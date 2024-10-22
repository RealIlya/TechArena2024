#include <algorithm>
#include <bitset>
#include <cmath>
#include <iostream>
#include <limits>
#include <map>
#include <queue>
#include <set>
#include <sstream>
#include <unordered_map>
#include <unordered_set>
#include <vector>

const int MAX_TABLES = 20;

struct Plan {
    double cost;
    double rows;
    std::string plan_str;

    Plan() : cost(std::numeric_limits<double>::max()), rows(0.0), plan_str("") {}
    Plan(double c, double r, const std::string& s) : cost(c), rows(r), plan_str(s) {}
};

struct JoinCondition {
    int left_table;
    char left_attr;
    int right_table;
    char right_attr;

    JoinCondition(int l_table, char l_attr, int r_table, char r_attr)
        : left_table(l_table), left_attr(l_attr), right_table(r_table), right_attr(r_attr) {}
};

class InputData {
   public:
    int num_tables;
    std::vector<double> table_rows;
    std::map<std::pair<int, char>, double> attr_cardinality;
    std::vector<std::pair<int, char>> scan_predicates;
    std::vector<JoinCondition> join_conditions;

    void read_input() {
        std::cin >> num_tables;
        table_rows.resize(num_tables + 1);  // 1-based indexing
        for (int i = 1; i <= num_tables; i++) {
            std::cin >> table_rows[i];
        }
        int num_attrs;
        std::cin >> num_attrs;
        for (int i = 0; i < num_attrs; i++) {
            int table_num;
            char attr;
            double card;
            std::cin >> table_num >> attr >> card;
            attr_cardinality[{table_num, attr}] = card;
        }
        int num_scan_preds;
        std::cin >> num_scan_preds;
        for (int i = 0; i < num_scan_preds; i++) {
            int table_num;
            char attr;
            std::cin >> table_num >> attr;
            scan_predicates.emplace_back(table_num, attr);
        }
        int num_join_preds;
        std::cin >> num_join_preds;
        for (int i = 0; i < num_join_preds; i++) {
            int table1, table2;
            char attr1, attr2;
            std::cin >> table1 >> table2 >> attr1 >> attr2;
            join_conditions.emplace_back(table1, attr1, table2, attr2);
        }
    }
};

class Task1Solver {
   public:
    explicit Task1Solver(const InputData& input) : data(input) {
        num_tables = data.num_tables;
    }

    void solve() {
        initialize_base_cases();
        dynamic_programming();
        // Output the result
        auto final_plan = dp[(1 << num_tables) - 1];
        std::cout << final_plan.plan_str << " " << final_plan.cost << std::endl;
    }

    std::unordered_map<int, Plan> dp;  // key: bitmask of tables
   private:
    const InputData& data;
    int num_tables;

    // Stores the best plan for a single table
    std::vector<Plan> base_plans;

    // Map to store join conditions between tables
    std::map<std::pair<int, int>, std::vector<JoinCondition>> join_map;

    void initialize_base_cases() {
        base_plans.resize(num_tables + 1);  // 1-based indexing
        for (int i = 1; i <= num_tables; i++) {
            double cost = data.table_rows[i];
            double rows = data.table_rows[i];
            std::stringstream ss;
            ss << i;
            // Apply scan predicates
            for (const auto& pred : data.scan_predicates) {
                if (pred.first == i) {
                    ss << pred.second;
                    double card = data.attr_cardinality.at({i, pred.second});
                    cost += data.table_rows[i];  // Cost of evaluating predicate
                    rows *= (1.0 / card);
                }
            }
            base_plans[i] = Plan(cost, rows, ss.str());
            dp[1 << (i - 1)] = base_plans[i];
        }
        // Build join map
        for (const auto& cond : data.join_conditions) {
            int t1 = cond.left_table;
            int t2 = cond.right_table;
            join_map[{t1, t2}].push_back(cond);
            join_map[{t2, t1}].push_back(cond);
        }
    }

    // динамически вычисляем маску таблицы
    void dynamic_programming() {
        int full_set = (1 << num_tables) - 1;
        for (int size = 2; size <= num_tables; size++) {
            for (int subset = 1; subset <= full_set; subset++) {
                if (__builtin_popcount(subset) != size) continue;
                dp_subset(subset);
            }
        }
    }

    void dp_subset(int subset) {
        Plan best_plan;
        for (int left = (subset - 1) & subset; left > 0; left = (left - 1) & subset) {
            int right = subset ^ left;
            auto it_left = dp.find(left);
            auto it_right = dp.find(right);
            if (it_left == dp.end() || it_right == dp.end()) continue;

            Plan left_plan = it_left->second;
            Plan right_plan = it_right->second;

            bool has_join_condition = false;
            std::vector<JoinCondition> applicable_conditions;

            // Check if there are join conditions between left and right
            for (int l = 0; l < num_tables; l++) {
                if (!(left & (1 << l))) continue;
                for (int r = 0; r < num_tables; r++) {
                    if (!(right & (1 << r))) continue;
                    int t1 = l + 1;
                    int t2 = r + 1;
                    auto it = join_map.find({t1, t2});
                    if (it != join_map.end()) {
                        has_join_condition = true;
                        applicable_conditions.insert(applicable_conditions.end(),
                                                     it->second.begin(), it->second.end());
                    }
                }
            }

            double join_cost;
            double result_rows;
            std::string join_str;
            if (has_join_condition) {
                // Try both NestLoop and HashJoin
                Plan nestloop_plan = compute_join(left_plan, right_plan, applicable_conditions, true);
                Plan hashjoin_plan = compute_join(left_plan, right_plan, applicable_conditions, false);
                if (nestloop_plan.cost < hashjoin_plan.cost) {
                    join_cost = nestloop_plan.cost;
                    result_rows = nestloop_plan.rows;
                    join_str = nestloop_plan.plan_str;
                } else {
                    join_cost = hashjoin_plan.cost;
                    result_rows = hashjoin_plan.rows;
                    join_str = hashjoin_plan.plan_str;
                }
            } else {
                // Cross join
                join_cost = left_plan.cost + right_plan.cost + left_plan.rows * right_plan.rows * 0.1;
                result_rows = left_plan.rows * right_plan.rows;
                std::stringstream ss;
                ss << "(" << left_plan.plan_str << " " << right_plan.plan_str << ")";
                join_str = ss.str();
            }
            if (join_cost < best_plan.cost) {
                best_plan.cost = join_cost;
                best_plan.rows = result_rows;
                best_plan.plan_str = join_str;
            }
        }
        if (best_plan.cost < std::numeric_limits<double>::max()) {
            dp[subset] = best_plan;
        }
    }

    Plan compute_join(const Plan& left_plan, const Plan& right_plan,
                      const std::vector<JoinCondition>& conditions, bool is_nestloop) {
        double cost;
        double result_rows;
        if (is_nestloop) {
            // NestLoop cost
            cost = left_plan.cost + right_plan.cost + left_plan.rows * right_plan.cost + left_plan.rows * right_plan.rows * 0.1;  // Output cost
        } else {
            // HashJoin cost
            cost = left_plan.cost + right_plan.cost + right_plan.rows * 1.5          // Build hash table
                   + left_plan.rows * 3.5 + left_plan.rows * right_plan.rows * 0.1;  // Output cost
        }
        // Estimate result rows
        result_rows = (left_plan.rows * right_plan.rows);
        for (const auto& cond : conditions) {
            double card_left = data.attr_cardinality.at({cond.left_table, cond.left_attr});
            double card_right = data.attr_cardinality.at({cond.right_table, cond.right_attr});
            double max_card = std::max(card_left, card_right);
            result_rows /= max_card;
        }
        // Build plan string
        std::stringstream ss;
        ss << "(" << left_plan.plan_str << " " << right_plan.plan_str;
        for (const auto& cond : conditions) {
            ss << " {" << cond.left_table << "." << cond.left_attr << " "
               << cond.right_table << "." << cond.right_attr << "}";
        }
        ss << ")";
        return Plan(cost, result_rows, ss.str());
    }
};

class Task2Solver {
   public:
    explicit Task2Solver(const InputData& input) : data(input) {
        num_tables = data.num_tables;
    }

    void solve() {
        compute_transitive_closure();
        identify_connected_components();
        solve_components();
        combine_components();
        // Output the result
        std::cout << final_plan.plan_str << " " << final_plan.cost << std::endl;
    }

   private:
    const InputData& data;
    int num_tables;
    std::unordered_map<int, Plan> dp;  // key: bitmask of tables
    std::vector<std::vector<int>> components;
    std::map<std::pair<int, int>, std::vector<JoinCondition>> join_map;
    std::unordered_map<int, std::unordered_set<int>> adjacency_list;
    Plan final_plan;

    void compute_transitive_closure() {
        // Build initial adjacency list
        for (const auto& cond : data.join_conditions) {
            int t1 = cond.left_table;
            int t2 = cond.right_table;
            adjacency_list[t1].insert(t2);
            adjacency_list[t2].insert(t1);
            join_map[{t1, t2}].push_back(cond);
            join_map[{t2, t1}].push_back(cond);
        }
        // Compute transitive closure using BFS
        // Not necessary here as we can infer joins during plan construction
    }

    void identify_connected_components() {
        std::vector<bool> visited(num_tables + 1, false);  // 1-based indexing
        for (int i = 1; i <= num_tables; i++) {
            if (!visited[i]) {
                std::vector<int> component;
                dfs(i, visited, component);
                components.push_back(component);
            }
        }
    }

    void dfs(int node, std::vector<bool>& visited, std::vector<int>& component) {
        visited[node] = true;
        component.push_back(node);
        for (int neighbor : adjacency_list[node]) {
            if (!visited[neighbor]) {
                dfs(neighbor, visited, component);
            }
        }
    }

    void solve_components() {
        std::vector<Plan> component_plans;
        for (const auto& comp : components) {
            InputData comp_data = extract_component_data(comp);
            Task1Solver solver(comp_data);
            solver.solve();
            Plan comp_plan = solver.dp[(1 << comp.size()) - 1];
            component_plans.push_back(comp_plan);
        }
        // Now combine component plans considering cross-joins
        // Use dynamic programming over components
        dp.clear();
        int num_components = components.size();
        int full_set = (1 << num_components) - 1;
        for (int i = 0; i < num_components; i++) {
            dp[1 << i] = component_plans[i];
        }
        for (int size = 2; size <= num_components; size++) {
            for (int subset = 1; subset <= full_set; subset++) {
                if (__builtin_popcount(subset) != size) continue;
                dp_components(subset);
            }
        }
        final_plan = dp[full_set];
    }

    void dp_components(int subset) {
        Plan best_plan;
        for (int left = (subset - 1) & subset; left > 0; left = (left - 1) & subset) {
            int right = subset ^ left;
            auto it_left = dp.find(left);
            auto it_right = dp.find(right);
            if (it_left == dp.end() || it_right == dp.end()) continue;

            Plan left_plan = it_left->second;
            Plan right_plan = it_right->second;

            // Cross join between components
            double join_cost = left_plan.cost + right_plan.cost + left_plan.rows * right_plan.rows * 0.1;  // Output cost
            double result_rows = left_plan.rows * right_plan.rows;
            std::stringstream ss;
            ss << "(" << left_plan.plan_str << " " << right_plan.plan_str << ")";
            if (join_cost < best_plan.cost) {
                best_plan.cost = join_cost;
                best_plan.rows = result_rows;
                best_plan.plan_str = ss.str();
            }
        }
        if (best_plan.cost < std::numeric_limits<double>::max()) {
            dp[subset] = best_plan;
        }
    }

    InputData extract_component_data(const std::vector<int>& comp) {
        InputData comp_data;
        comp_data.num_tables = comp.size();
        std::map<int, int> table_mapping;
        for (size_t i = 0; i < comp.size(); i++) {
            int old_table_num = comp[i];
            int new_table_num = i + 1;
            table_mapping[old_table_num] = new_table_num;
            comp_data.table_rows.push_back(data.table_rows[old_table_num]);
        }
        // Adjust attributes and predicates
        for (const auto& attr : data.attr_cardinality) {
            int table_num = attr.first.first;
            char attr_name = attr.first.second;
            if (table_mapping.count(table_num)) {
                int new_table_num = table_mapping[table_num];
                comp_data.attr_cardinality[{new_table_num, attr_name}] = attr.second;
            }
        }
        for (const auto& pred : data.scan_predicates) {
            int table_num = pred.first;
            char attr_name = pred.second;
            if (table_mapping.count(table_num)) {
                int new_table_num = table_mapping[table_num];
                comp_data.scan_predicates.emplace_back(new_table_num, attr_name);
            }
        }
        for (const auto& cond : data.join_conditions) {
            int t1 = cond.left_table;
            int t2 = cond.right_table;
            if (table_mapping.count(t1) && table_mapping.count(t2)) {
                int new_t1 = table_mapping[t1];
                int new_t2 = table_mapping[t2];
                comp_data.join_conditions.emplace_back(new_t1, cond.left_attr, new_t2, cond.right_attr);
            }
        }
        return comp_data;
    }

    void combine_components() {
        // Already combined in solve_components()
    }
};

int main() {
    InputData input_data;
    input_data.read_input();

    // Solve Task 1
    Task1Solver task1_solver(input_data);
    task1_solver.solve();

    // Solve Task 2
    // Task2Solver task2_solver(input_data);
    // task2_solver.solve();

    return 0;
}
