#include"front/semantic.h"
#include<iostream>
#include<cassert>
using ir::Instruction;
using ir::Function;
using ir::Operand;
using ir::Operator;

#define TODO assert(0 && "TODO");

// 把语法树的第index子节点，安全地转换成想要的类型，并且自动检查类型是否正确
#define GET_CHILD_PTR(node, type, index) auto node = dynamic_cast<type*>(root->children[index]); assert(node); 
// 获取index子节点, 并且进行递归分析
#define ANALYSIS(node, type, index) auto node = dynamic_cast<type*>(root->children[index]); assert(node); analysis##type(node, buffer);
// 让父节点自动继承子节点的这些关键信息。
#define COPY_EXP_NODE(from, to) to->is_computable = from->is_computable; to->v = from->v; to->t = from->t;

map<std::string, ir::Function*>* frontend::get_lib_funcs() {
    static map<std::string, ir::Function*> lib_funcs = {
        {"getint", new Function("getint", Type::Int)},
        {"getch", new Function("getch", Type::Int)},
        {"getfloat", new Function("getfloat", Type::Float)},
        {"getarray", new Function("getarray", {Operand("arr", Type::IntPtr)}, Type::Int)},
        {"getfarray", new Function("getfarray", {Operand("arr", Type::FloatPtr)}, Type::Int)},
        {"putint", new Function("putint", {Operand("i", Type::Int)}, Type::null)},
        {"putch", new Function("putch", {Operand("i", Type::Int)}, Type::null)},
        {"putfloat", new Function("putfloat", {Operand("f", Type::Float)}, Type::null)},
        {"putarray", new Function("putarray", {Operand("n", Type::Int), Operand("arr", Type::IntPtr)}, Type::null)},
        {"putfarray", new Function("putfarray", {Operand("n", Type::Int), Operand("arr", Type::FloatPtr)}, Type::null)},
    };
    return &lib_funcs;
}


// 类型转换
void frontend::Analyzer::type_transform(Operand& a, Operand& b, vector<Instruction*>& buffer){
    std::cout << "[DEBUG] type_transform called:" << std::endl;
    std::cout << "  Before transform:" << std::endl;
    std::cout << "    a: name=" << a.name << ", type=" << toString(a.type) << std::endl;
    std::cout << "    b: name=" << b.name << ", type=" << toString(b.type) << std::endl;

    if (a.type == Type::Int){
        if (b.type == Type::Float){     // Int-Float
            auto tmp_op = Operand("t" + std::to_string(tmp_cnt++), Type::Float);    // a转Float
            buffer.push_back(new Instruction(a, {}, tmp_op, Operator::cvt_i2f));
            a = tmp_op;   
        }else if (b.type == Type::FloatLiteral){    // Int-FloatLiteral
            auto tmp_op1 = Operand("t" + std::to_string(tmp_cnt++), Type::Float);    // a转Float
            buffer.push_back(new Instruction(a, {}, tmp_op1, Operator::cvt_i2f));

            auto tmp_op2 = Operand("t" + std::to_string(tmp_cnt++), Type::Float);    // b转Float
            buffer.push_back(new Instruction(b, {}, tmp_op2, Operator::fdef));
            
            a = tmp_op1;
            b = tmp_op2;
        }else if (b.type == Type::IntLiteral){      // Int-IntLiteral
            auto tmp_op = Operand("t" + std::to_string(tmp_cnt++), Type::Int);    // b转Int
            buffer.push_back(new Instruction(b, {}, tmp_op, Operator::def));

            b = tmp_op;
        }
    }else if (a.type == Type::IntLiteral){      // IntLiteral-Float
        if (b.type == Type::Float){
            auto tmp_op = Operand("t" + std::to_string(tmp_cnt++), Type::Float);    // a转Float
            buffer.push_back(new Instruction(Operand(a.name, Type::FloatLiteral), {}, tmp_op, Operator::fdef));
            
            a = tmp_op;

        }else if (b.type == Type::Int){     // IntLiteral-Int

            auto tmp_op = Operand("t" + std::to_string(tmp_cnt++), Type::Int);    // a转Int
            buffer.push_back(new Instruction(a, {}, tmp_op, Operator::def));

            a = tmp_op;
        }else if (b.type == Type::IntLiteral){      // IntLiteral-IntLiteral
            
            auto tmp_op1 = Operand("t" + std::to_string(tmp_cnt++), Type::Int);    // a转Int
            buffer.push_back(new Instruction(a, {}, tmp_op1, Operator::def));

            auto tmp_op2 = Operand("t" + std::to_string(tmp_cnt++), Type::Int);    // b转Int
            buffer.push_back(new Instruction(b, {}, tmp_op2, Operator::def));

            a = tmp_op1;
            b = tmp_op2;
        }
    }else if(a.type == Type::Float){    // Float-Int
        if (b.type == Type::Int){
            auto tmp_op = Operand("t" + std::to_string(tmp_cnt++), Type::Float);    // b转Float
            buffer.push_back(new Instruction(b, {}, tmp_op, Operator::cvt_i2f));

            b = tmp_op;
        }else if (b.type == Type::IntLiteral){  // Float-IntLiteral
            auto tmp_op = Operand("t" + std::to_string(tmp_cnt++), Type::Float);    // b转Float
            buffer.push_back(new Instruction(Operand(b.name, Type::FloatLiteral), {}, tmp_op, Operator::fdef));

            b = tmp_op;
        }else if (b.type == Type::FloatLiteral){  // Float-FloatLiteral
            auto tmp_op = Operand("t" + std::to_string(tmp_cnt++), Type::Float);    // b转Float
            buffer.push_back(new Instruction(b, {}, tmp_op, Operator::fdef));

            b = tmp_op;
        }
    }else if (a.type == Type::FloatLiteral){
        if (b.type == Type::Int){
            auto tmp_op1 = Operand("t" + std::to_string(tmp_cnt++), Type::Float);    // a转Float
            buffer.push_back(new Instruction(Operand(a.name, Type::FloatLiteral), {}, tmp_op1, Operator::fdef));

            auto tmp_op2 = Operand("t" + std::to_string(tmp_cnt++), Type::Float);    // b转Float
            buffer.push_back(new Instruction(b, {}, tmp_op2, Operator::cvt_i2f));

            a = tmp_op1;
            b = tmp_op2;
        }else if (b.type == Type::Float){
            auto tmp_op = Operand("t" + std::to_string(tmp_cnt++), Type::Float);    // a转Float
            buffer.push_back(new Instruction(Operand(a.name, Type::FloatLiteral), {}, tmp_op, Operator::fdef));
            
            a = tmp_op;
        }
    }

    std::cout << "  After transform:" << std::endl;
    std::cout << "    a: name=" << a.name << ", type=" << toString(a.type) << std::endl;
    std::cout << "    b: name=" << b.name << ", type=" << toString(b.type) << std::endl;
}


// 进入新作用域时, 向符号表中添加 ScopeInfo, 相当于压栈, 经过分析，作用域的类别没有用处
void frontend::SymbolTable::add_scope(Block* node) {

    ScopeInfo scope_info;   // 当前作用域
    scope_info.cnt = ++block_cnt;    // 当前作用域编号
    scope_stack.push_back(scope_info);  // 压入作用域

}


// 退出作用域时弹栈
void frontend::SymbolTable::exit_scope() {
    scope_stack.pop_back();
}


// 输入一个变量名, 返回其在当前作用域下重命名后的名字 (相当于加后缀)
string frontend::SymbolTable::get_scoped_name(string id) const {
    int cnt = scope_stack.back().cnt;  //当前作用域编号
    return id + "_" + std::to_string(cnt);
}


// 输入一个变量名, 在符号表中寻找最近的同名变量, 返回对应的 Operand(注意，此 Operand 的 name 是重命名后的)
Operand frontend::SymbolTable::get_operand(string id) const {
    map_str_ste temp;
    for (int i=scope_stack.size()-1; i>=0; i--){      // 倒着找 
        temp = scope_stack[i].table;     // 当前作用域的符号表
        if(temp.find(id) != temp.end()){     // 找到了
            return temp[id].operand;
        }
    }
    return Operand();
}


// 输入一个变量名, 在符号表中寻找最近的同名变量, 返回 STE
frontend::STE frontend::SymbolTable::get_ste(string id) const {
    map_str_ste temp;
    for (int i=scope_stack.size()-1; i>=0; i--){      // 倒着找 
        temp= scope_stack[i].table;     // 当前作用域的符号表
        if(temp.find(id) != temp.end()){     // 找到了
            return temp[id];
        }
    }    
    return frontend::STE();
}


// 初始化符号表
frontend::Analyzer::Analyzer(): tmp_cnt(0), symbol_table() {
    symbol_table.scope_stack.push_back({0, "global", map_str_ste()});    // 符号表创建全局作用域
}


ir::Program frontend::Analyzer::get_ir_program(CompUnit* root) {
    ir::Program buffer = ir::Program();
    Function* global_func = new Function("global", Type::null);

    symbol_table.functions.insert({"global", global_func});
    buffer.addFunction(*global_func);

    auto lib_funcs = *get_lib_funcs();
    for (auto it = lib_funcs.begin(); it != lib_funcs.end(); it++)
        symbol_table.functions[it->first] = it->second;

    analysisCompUnit(root, buffer);

    // 给全局函数插入全局return
    buffer.functions[0].addInst(new ir::Instruction({Operand("null", Type::null), Operand(), Operand(), Operator::_return}));

    // 登记global函数IR中的所有定义型变量到GVT
    for (const auto& inst : buffer.functions[0].InstVec) {
        // 仅登记有名字且不是null的变量
        if (inst->des.name != "" && inst->des.type != Type::null) {
            buffer.globalVal.push_back(ir::GlobalVal(inst->des));
        }
    }

    // 遍历symbol_table，登记main作用域的静态变量（如main中的数组等）
    // 假设main的作用域编号已知为main_scope_cnt
    for (const auto& scope : symbol_table.scope_stack) {
        if (scope.name == "fp" /* 或其它标识main作用域的条件 */) {
            for (const auto& it : scope.table) {
                const auto& op = it.second.operand;
                // 只登记数组或局部静态变量（如float*/int*等指针类型或全局静态变量）
                if (
                    (op.type == Type::FloatPtr || op.type == Type::IntPtr ||
                     op.type == Type::Float || op.type == Type::Int)
                    && op.name != "" && op.type != Type::null
                ) {
                    // 避免重复
                    bool exist = false;
                    for (const auto& gv : buffer.globalVal) {
                        if (gv.val.name == op.name) {
                            exist = true;
                            break;
                        }
                    }
                    if (!exist) buffer.globalVal.push_back(ir::GlobalVal(op));
                }
            }
        }
    }

    std::cout << buffer.draw();
    return buffer;
}


// CompUnit -> (Decl | FuncDef) [CompUnit]
void frontend::Analyzer::analysisCompUnit(CompUnit* root, ir::Program& buffer){
    if (root->children[0]->type == NodeType::DECL){     
        GET_CHILD_PTR(decl, Decl, 0);   
        assert(decl);
        analysisDecl(decl, buffer.functions.back().InstVec);    
    }else if (root->children[0]->type == NodeType::FUNCDEF){    
        if (buffer.functions.size() == 1){    
            auto global_ir = buffer.functions[0].InstVec;
            for (int i=0; i<(int)global_ir.size(); i++){   
                buffer.globalVal.push_back(ir::GlobalVal(global_ir[i]->des));  
            }
        }
        GET_CHILD_PTR(funcdef, FuncDef, 0);     
        assert(funcdef);
        auto tmp = ir::Function();  
        analysisFuncDef(funcdef, tmp);
        buffer.addFunction(tmp);    
        // 打印 main 函数所有涉及 t66 的 IR 指令及类型
        if (tmp.name == "main") {
            for (auto* inst : tmp.InstVec) {
                if (inst->des.name == "t66" || inst->op1.name == "t66" || inst->op2.name == "t66") {
                    std::cout << "[T66] " << inst->draw()
                              << " | des type: " << toString(inst->des.type)
                              << ", op1 type: " << toString(inst->op1.type)
                              << ", op2 type: " << toString(inst->op2.type)
                              << std::endl;
                }
            }
        }
    }
    if ((int)(int)root->children.size() == 2){
        ANALYSIS(compunit, CompUnit, 1);
    }
}


// FuncDef -> FuncType Ident '(' [FuncFParams] ')' Block
void frontend::Analyzer::analysisFuncDef(FuncDef* root, ir::Function& function){

    auto tk = dynamic_cast<Term*>(root->children[0]->children[0])->token.type;  
    root->t = tk == TokenType::VOIDTK ? Type::null : tk == TokenType::INTTK ? Type::Int :Type::Float;
    root->n = dynamic_cast<Term*>(root->children[1])->token.value;
    function.name = root->n;       
    function.returnType = root->t; 

    int cnt = ++symbol_table.block_cnt;
    symbol_table.scope_stack.push_back({cnt, "fp", map_str_ste()});   
    symbol_table.functions.insert({root->n, &function});            
    curr_function = &function;  

    if (function.name == "main"){   
        auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::null);
        auto global_callinst = new ir::CallInst(Operand("global", Type::null), vector<Operand>(), tmp);  
        curr_function->addInst(global_callinst);
    }

    auto paras = dynamic_cast<FuncFParams*>(root->children[3]);     
    if (paras){     // 如果函数参数列表存在
        analysisFuncFParams(paras, function);
        analysisBlock(dynamic_cast<Block*>(root->children[5]), function.InstVec);
    }else{
        analysisBlock(dynamic_cast<Block*>(root->children[4]), function.InstVec);
    }

    if (function.returnType == Type::null){     
        auto return_inst = new Instruction({Operand("null", Type::null), {}, {}, Operator::_return});
        curr_function->addInst(return_inst);
    }

    symbol_table.exit_scope();  
}


// Decl -> ConstDecl | VarDecl
void frontend::Analyzer::analysisDecl(Decl* root, vector<ir::Instruction*>& buffer){

    if (root->children[0]->type == NodeType::CONSTDECL){    // 常量
        ANALYSIS(constdecl, ConstDecl, 0);
    }else if (root->children[0]->type == NodeType::VARDECL){    // 变量
        ANALYSIS(vardecl, VarDecl, 0);
    }
}


// ConstDecl -> 'const' BType ConstDef { ',' ConstDef } ';'
void frontend::Analyzer::analysisConstDecl(ConstDecl* root, vector<ir::Instruction*>& buffer){
    ANALYSIS(btype, BType, 1);
    root->t = btype->t;   
    ANALYSIS(constdef1, ConstDef, 2);    
    int i = 3;
    while (dynamic_cast<Term*>(root->children[i])->token.type == TokenType::COMMA){
        ANALYSIS(constdef2, ConstDef, i+1);  
        i += 2;
    }
}


// BType -> 'int' | 'float'
void frontend::Analyzer::analysisBType(BType* root, vector<ir::Instruction*>& buffer){
    auto tk = dynamic_cast<Term*>(root->children[0])->token.type;  
    root->t = tk==TokenType::INTTK ? Type::Int : Type::Float;  
}


// ConstDef -> Ident { '[' ConstExp ']' } '=' ConstInitVal
// 该函数负责分析常量定义（包括普通常量和数组常量），并生成相应的IR指令
void frontend::Analyzer::analysisConstDef(ConstDef* root, vector<ir::Instruction*>& buffer){
    // 获取父节点ConstDecl的类型（int/float），即本常量的类型
    auto root_type = dynamic_cast<ConstDecl*>(root->parent)->t;  
    std::cout << "[DEBUG] analysisConstDef: root_type=" << toString(root_type) << std::endl;
    // 获取常量名（Term类型）
    GET_CHILD_PTR(identifier, Term, 0);
    string id = identifier->token.value;
    // 作用域内唯一命名，防止重名
    string new_name = symbol_table.get_scoped_name(id);
    root->arr_name = new_name;

    // 获取下一个孩子节点，用于判断是普通变量还是数组
    GET_CHILD_PTR(term, Term, 1);
    if (term->token.type == TokenType::ASSIGN) { // 普通常量定义
        ANALYSIS(constinitval, ConstInitVal, 2); // 分析初始值
        Operand des = Operand(new_name, root_type); // 目标操作数
        // 根据类型选用float定义还是int定义
        auto opcode = (root_type == Type::Float || root_type == Type::FloatLiteral) ? Operator::fdef : Operator::def;
        Operand op1 = Operand(constinitval->v, constinitval->t); // 初始值操作数

        // 类型转换处理，保证目标类型一致
        if (root_type == Type::Float) {
            if (constinitval->t == Type::Int) {
                // int -> float
                auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
                buffer.push_back(new Instruction(op1, {}, tmp, Operator::cvt_i2f));
                op1 = tmp;
            } else if (constinitval->t == Type::IntLiteral) {
                // 字面量int -> 字面量float
                std::string v = std::to_string((float)std::stoi(op1.name));
                v.erase(v.find_last_not_of('0') + 1, std::string::npos);
                if (v.back() == '.') v += "0";
                op1.name = v;
                op1.type = Type::FloatLiteral;
            } else if (constinitval->t == Type::FloatLiteral) {
                // 字面量float去除多余0并转正式float变量
                std::string v = op1.name;
                v.erase(v.find_last_not_of('0') + 1, std::string::npos);
                if (v.back() == '.') v += "0";
                op1.name = v;
                auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
                buffer.push_back(new Instruction(op1, {}, tmp, Operator::fdef));
                op1 = tmp;
            }
        } else {
            // root_type == Int
            assert(root_type == Type::Int);
            if (constinitval->t == Type::Float) {
                // float -> int
                auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
                buffer.push_back(new Instruction(op1, {}, tmp, Operator::cvt_f2i));
                op1 = tmp;
            } else if (constinitval->t == Type::FloatLiteral) {
                // 字面量float -> 字面量int
                op1.name = std::to_string((int)std::stof(op1.name));
                op1.type = Type::IntLiteral;
            }
        }
        // 生成定义指令
        if (opcode == Operator::fdef) {
            std::cout << "[DEBUG] fdef instruction: op1.name=" << op1.name << ", op1.type=" << toString(op1.type) << std::endl;
            assert(op1.type == Type::Float || op1.type == Type::FloatLiteral);
        }
        buffer.push_back(new Instruction(op1, Operand(), des, opcode));
        // 更新符号表：当前作用域插入该符号
        symbol_table.scope_stack.back().table.insert({id, {op1, {}}});
    }
    else if ((int)root->children.size() == 6) { // 一维数组定义
        ANALYSIS(constexp, ConstExp, 2); // 获取数组长度
        int array_size = std::stoi(constexp->v);
        STE arr_ste;
        arr_ste.dimension.push_back(array_size);
        ir::Type curr_type = root_type;
        // int数组/float数组分别为IntPtr/FloatPtr类型
        if (curr_type == ir::Type::Int) {
            curr_type = ir::Type::IntPtr;
        } else if (curr_type == ir::Type::Float) {
            curr_type = ir::Type::FloatPtr;
        }
        arr_ste.operand = ir::Operand(new_name, curr_type);
        symbol_table.scope_stack.back().table[id] = arr_ste;
        // 生成分配数组指令
        buffer.push_back(new Instruction({Operand(std::to_string(array_size), ir::Type::IntLiteral), {}, Operand(new_name, curr_type), Operator::alloc}));

        // 处理数组初值
        GET_CHILD_PTR(constinitval, ConstInitVal, 5);
        int cnt = 0;
        if (constinitval->children.size() == 2) { // 只有{}去初始化数组，默认全0
            for (int i = 0; i < array_size; i++) {
                if (arr_ste.operand.type == Type::FloatPtr) {
                    buffer.push_back(new Instruction({arr_ste.operand, Operand(std::to_string(i), Type::IntLiteral), Operand("0.0", Type::FloatLiteral), Operator::store}));
                } else {
                    buffer.push_back(new Instruction({arr_ste.operand, Operand(std::to_string(i), Type::IntLiteral), Operand("0", Type::IntLiteral), Operator::store}));
                }
            }
        } else {
            // 对每个元素逐一赋初值
            for (int i = 1; i < (int)constinitval->children.size()-1; i += 2, cnt++) {
                ConstInitVal* child = dynamic_cast<ConstInitVal*>(constinitval->children[i]);
                ConstExp* constexp = dynamic_cast<ConstExp*>(child->children[0]);
                analysisConstExp(constexp, buffer);
                std::string v = constexp->v;
                ir::Type t = constexp->t;
                if (arr_ste.operand.type == Type::FloatPtr) {
                    if (t == ir::Type::Int) {
                        // int -> float
                        Operand int_op(v, ir::Type::Int);
                        Operand float_tmp("t" + std::to_string(tmp_cnt++), ir::Type::Float);
                        buffer.push_back(new Instruction(int_op, {}, float_tmp, Operator::cvt_i2f));
                        buffer.push_back(new Instruction({arr_ste.operand, Operand(std::to_string(cnt), Type::IntLiteral), float_tmp, Operator::store}));
                        continue;
                    } else if (t == ir::Type::IntLiteral) {
                        // 字面量int -> 字面量float
                        v = std::to_string((float)std::stoi(v));
                        v.erase(v.find_last_not_of('0') + 1, std::string::npos);
                        if (v.back() == '.') v += "0";
                        t = ir::Type::FloatLiteral;
                    } else if (t == ir::Type::FloatLiteral) {
                        // 清理float字面量格式
                        v.erase(v.find_last_not_of('0') + 1, std::string::npos);
                        if (v.back() == '.') v += "0";
                    }
                    buffer.push_back(new Instruction({arr_ste.operand, Operand(std::to_string(cnt), Type::IntLiteral), Operand(v, t), Operator::store}));
                } else {
                    if (t == ir::Type::FloatLiteral) {
                        // 字面量float -> 字面量int
                        v = std::to_string((int)std::stof(v));
                        t = ir::Type::IntLiteral;
                    }
                    buffer.push_back(new Instruction({arr_ste.operand, Operand(std::to_string(cnt), Type::IntLiteral), Operand(v, t), Operator::store}));
                }
            }
            // 剩余元素补0
            for (; cnt < array_size; cnt++) {
                if (arr_ste.operand.type == Type::FloatPtr) {
                    buffer.push_back(new Instruction({arr_ste.operand, Operand(std::to_string(cnt), Type::IntLiteral), Operand("0.0", Type::FloatLiteral), Operator::store}));
                } else {
                    buffer.push_back(new Instruction({arr_ste.operand, Operand(std::to_string(cnt), Type::IntLiteral), Operand("0", Type::IntLiteral), Operator::store}));
                }
            }
        }
    }
    else if ((int)root->children.size() == 9) { // 二维数组定义
        ANALYSIS(constexp1, ConstExp, 2);
        ANALYSIS(constexp2, ConstExp, 5);
        int dim1 = std::stoi(constexp1->v);
        int dim2 = std::stoi(constexp2->v);
        int array_size = dim1 * dim2;
        STE arr_ste;
        arr_ste.dimension.push_back(dim1);
        arr_ste.dimension.push_back(dim2);
        ir::Type curr_type = root_type;
        if (curr_type == ir::Type::Int) {
            curr_type = ir::Type::IntPtr;
        } else if (curr_type == ir::Type::Float) {
            curr_type = ir::Type::FloatPtr;
        }
        arr_ste.operand = ir::Operand(new_name, curr_type);
        symbol_table.scope_stack.back().table[id] = arr_ste;
        // 分配二维数组空间（实际为一维展开）
        buffer.push_back(new Instruction({Operand(std::to_string(array_size), ir::Type::IntLiteral), {}, Operand(new_name, curr_type), Operator::alloc}));

        // 处理数组初值
        GET_CHILD_PTR(constinitval, ConstInitVal, 8);
        int cnt = 0;
        if (constinitval->children.size() == 2) { // 只有{}去初始化数组
            for (int i = 0; i < array_size; i++) {
                if (arr_ste.operand.type == Type::FloatPtr) {
                    buffer.push_back(new Instruction({arr_ste.operand, Operand(std::to_string(i), Type::IntLiteral), Operand("0.0", Type::FloatLiteral), Operator::store}));
                } else {
                    buffer.push_back(new Instruction({arr_ste.operand, Operand(std::to_string(i), Type::IntLiteral), Operand("0", Type::IntLiteral), Operator::store}));
                }
            }
        } else {
            // 对每个元素逐一赋初值
            for (int i = 1; i < (int)constinitval->children.size()-1; i += 2, cnt++) {
                ConstInitVal* child = dynamic_cast<ConstInitVal*>(constinitval->children[i]);
                ConstExp* constexp = dynamic_cast<ConstExp*>(child->children[0]);
                analysisConstExp(constexp, buffer);
                std::string v = constexp->v;
                ir::Type t = constexp->t;
                if (arr_ste.operand.type == Type::FloatPtr) {
                    if (t == ir::Type::Int) {
                        Operand int_op(v, ir::Type::Int);
                        Operand float_tmp("t" + std::to_string(tmp_cnt++), ir::Type::Float);
                        buffer.push_back(new Instruction(int_op, {}, float_tmp, Operator::cvt_i2f));
                        buffer.push_back(new Instruction({arr_ste.operand, Operand(std::to_string(cnt), Type::IntLiteral), float_tmp, Operator::store}));
                        continue;
                    } else if (t == ir::Type::IntLiteral) {
                        // 字面量int -> 字面量float
                        v = std::to_string((float)std::stoi(v));
                        v.erase(v.find_last_not_of('0') + 1, std::string::npos);
                        if (v.back() == '.') v += "0";
                        t = ir::Type::FloatLiteral;
                    } else if (t == ir::Type::FloatLiteral) {
                        // 清理float字面量格式
                        v.erase(v.find_last_not_of('0') + 1, std::string::npos);
                        if (v.back() == '.') v += "0";
                    }
                    buffer.push_back(new Instruction({arr_ste.operand, Operand(std::to_string(cnt), Type::IntLiteral), Operand(v, t), Operator::store}));
                } else {
                    if (t == ir::Type::FloatLiteral) {
                        // 字面量float -> 字面量int
                        v = std::to_string((int)std::stof(v));
                        t = ir::Type::IntLiteral;
                    }
                    buffer.push_back(new Instruction({arr_ste.operand, Operand(std::to_string(cnt), Type::IntLiteral), Operand(v, t), Operator::store}));
                }
            }
            // 剩余元素补0
            for (; cnt < array_size; cnt++) {
                if (arr_ste.operand.type == Type::FloatPtr) {
                    buffer.push_back(new Instruction({arr_ste.operand, Operand(std::to_string(cnt), Type::IntLiteral), Operand("0.0", Type::FloatLiteral), Operator::store}));
                } else {
                    buffer.push_back(new Instruction({arr_ste.operand, Operand(std::to_string(cnt), Type::IntLiteral), Operand("0", Type::IntLiteral), Operator::store}));
                }
            }
        }
    }
}

// ConstInitVal -> ConstExp | '{' [ ConstInitVal { ',' ConstInitVal } ] '}'
void frontend::Analyzer::analysisConstInitVal(ConstInitVal* root, vector<ir::Instruction*>& buffer){
    if (root->children[0]->type == NodeType::CONSTEXP){     
        ANALYSIS(constexp, ConstExp, 0);    
        root->v = constexp->v;
        root->t = constexp->t;
    }
}


// VarDecl -> BType VarDef { ',' VarDef } ';'
void frontend::Analyzer::analysisVarDecl(VarDecl* root, vector<ir::Instruction*>& buffer){
    ANALYSIS(btype, BType, 0);      
    root->t = btype->t;             
    ANALYSIS(vardef, VarDef, 1);    
    int i = 2;  
    while (i < (int)root->children.size()-1){
        ANALYSIS(vardef, VarDef, i+1);  
        i += 2;
    }
}


// VarDef -> Ident { '[' ConstExp ']' } [ '=' InitVal ]
// VarDef -> Ident { '[' ConstExp ']' } [ '=' InitVal ]
// 该函数负责分析变量定义（包括普通变量和数组变量），并生成相应的IR指令
void frontend::Analyzer::analysisVarDef(VarDef* root, vector<ir::Instruction*>& buffer){
    // 获取父节点VarDecl的类型（int/float），即本变量的类型
    auto root_type = dynamic_cast<VarDecl*>(root->parent)->t;
    std::cout << "[DEBUG] analysisVarDef: root_type=" << toString(root_type) << std::endl;
    // 获取变量名（Term类型）
    GET_CHILD_PTR(identifier, Term, 0);
    string id = identifier->token.value;
    // 作用域内唯一命名，防止重名
    string new_name = symbol_table.get_scoped_name(id);

    if ((int)root->children.size() == 1) { // 普通变量，没有赋值
        Operand des = Operand(new_name, root_type);
        // 根据类型选用float定义还是int定义
        auto opcode = (root_type == Type::Float || root_type == Type::FloatLiteral) ? Operator::fdef : Operator::def;
        if (root_type == Type::Float) {
            // float默认初始化为0.0
            buffer.push_back(new Instruction(Operand("0.0", Type::FloatLiteral), Operand(), des, opcode));
        } else {
            // int默认初始化为0
            buffer.push_back(new Instruction(Operand("0", Type::IntLiteral), Operand(), des, opcode));
        }
        // 更新符号表
        symbol_table.scope_stack.back().table.insert({id, {des, {}}});
    } else {
        GET_CHILD_PTR(term, Term, 1);
        if (term->token.type == TokenType::ASSIGN) { // 普通变量,有赋值
            ANALYSIS(initval, InitVal, 2);  // 分析初始值
            Operand des = Operand(new_name, root_type);
            auto opcode = (root_type == Type::Float || root_type == Type::FloatLiteral) ? Operator::fdef : Operator::def;
            Operand op1 = Operand(initval->v, initval->t); // 初始值操作数

            // 类型转换处理，保证目标类型一致
            if (root_type == Type::Float) {
                if (initval->t == Type::Int) {
                    // int -> float
                    auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
                    buffer.push_back(new Instruction(op1, {}, tmp, Operator::cvt_i2f));
                    op1 = tmp;
                } else if (initval->t == Type::IntLiteral) {
                    // 字面量int -> 字面量float
                    std::string v = std::to_string((float)std::stoi(op1.name));
                    v.erase(v.find_last_not_of('0') + 1, std::string::npos);
                    if (v.back() == '.') v += "0";
                    op1.name = v;
                    op1.type = Type::FloatLiteral;
                }
            } else {
                // root_type == Int
                assert(root_type == Type::Int);
                if (initval->t == Type::Float) {
                    // float -> int
                    auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
                    buffer.push_back(new Instruction(op1, {}, tmp, Operator::cvt_f2i));
                    op1 = tmp;
                } else if (initval->t == Type::FloatLiteral) {
                    // 字面量float -> 字面量int
                    op1.name = std::to_string((int)std::stof(op1.name));
                    op1.type = Type::IntLiteral;
                }
            }
            // 生成定义指令
            if (opcode == Operator::fdef) {
                std::cout << "[DEBUG] fdef instruction: op1.name=" << op1.name << ", op1.type=" << toString(op1.type) << std::endl;
                assert(op1.type == Type::Float || op1.type == Type::FloatLiteral);
            }
            buffer.push_back(new Instruction(op1, Operand(), des, opcode));
            // 更新符号表
            symbol_table.scope_stack.back().table.insert({id, {des, {}}});
        } else if (root->children.back()->type == NodeType::INITVAL) { // 数组,有赋值
            if ((int)root->children.size() == 6) { // 一维数组定义
                ANALYSIS(constexp, ConstExp, 2); // 获取数组长度
                int array_size = std::stoi(constexp->v);
                STE arr_ste;
                arr_ste.dimension.push_back(array_size);
                ir::Type curr_type = root_type;
                // int数组/float数组分别为IntPtr/FloatPtr类型
                if (curr_type == ir::Type::Int) {
                    curr_type = ir::Type::IntPtr;
                } else if (curr_type == ir::Type::Float) {
                    curr_type = ir::Type::FloatPtr;
                }
                arr_ste.operand = ir::Operand(new_name, curr_type);
                symbol_table.scope_stack.back().table[id] = arr_ste;
                // 生成分配数组指令
                buffer.push_back(new Instruction({Operand(std::to_string(array_size), ir::Type::IntLiteral), {}, Operand(new_name, curr_type), Operator::alloc}));

                GET_CHILD_PTR(initval, InitVal, 5);
                int cnt = 0;
                if (initval->children.size() == 2) { // 只有{}去初始化数组，默认全0
                    for (int i = 0; i < array_size; i++) {
                        if (arr_ste.operand.type == Type::FloatPtr) {
                            buffer.push_back(new Instruction({arr_ste.operand, Operand(std::to_string(i), Type::IntLiteral), Operand("0.0", Type::FloatLiteral), Operator::store}));
                        } else {
                            buffer.push_back(new Instruction({arr_ste.operand, Operand(std::to_string(i), Type::IntLiteral), Operand("0", Type::IntLiteral), Operator::store}));
                        }
                    }
                } else {
                    // 对每个元素逐一赋初值
                    for (int i = 1; i < (int)initval->children.size() - 1; i += 2, cnt++) {
                        InitVal* child = dynamic_cast<InitVal*>(initval->children[i]);
                        Exp* exp = dynamic_cast<Exp*>(child->children[0]);
                        analysisExp(exp, buffer);
                        std::string v = exp->v;
                        ir::Type t = exp->t;
                        if (arr_ste.operand.type == Type::FloatPtr) {
                            if (t == ir::Type::Int) {
                                Operand int_op(v, ir::Type::Int);
                                Operand float_tmp("t" + std::to_string(tmp_cnt++), ir::Type::Float);
                                buffer.push_back(new Instruction(int_op, {}, float_tmp, Operator::cvt_i2f));
                                buffer.push_back(new Instruction({arr_ste.operand, Operand(std::to_string(cnt), Type::IntLiteral), float_tmp, Operator::store}));
                                continue;
                            } else if (t == ir::Type::IntLiteral) {
                                // 字面量int -> 字面量float
                                v = std::to_string((float)std::stoi(v));
                                v.erase(v.find_last_not_of('0') + 1, std::string::npos);
                                if (v.back() == '.') v += "0";
                                t = ir::Type::FloatLiteral;
                            } else if (t == ir::Type::FloatLiteral) {
                                // 清理float字面量格式
                                v.erase(v.find_last_not_of('0') + 1, std::string::npos);
                                if (v.back() == '.') v += "0";
                            }
                            buffer.push_back(new Instruction({arr_ste.operand, Operand(std::to_string(cnt), Type::IntLiteral), Operand(v, t), Operator::store}));
                        } else {
                            if (t == ir::Type::FloatLiteral) {
                                // 字面量float -> 字面量int
                                v = std::to_string((int)std::stof(v));
                                t = ir::Type::IntLiteral;
                            }
                            buffer.push_back(new Instruction({arr_ste.operand, Operand(std::to_string(cnt), Type::IntLiteral), Operand(v, t), Operator::store}));
                        }
                    }
                    // 剩余元素补0
                    for (; cnt < array_size; cnt++) {
                        if (arr_ste.operand.type == Type::FloatPtr) {
                            buffer.push_back(new Instruction({arr_ste.operand, Operand(std::to_string(cnt), Type::IntLiteral), Operand("0.0", Type::FloatLiteral), Operator::store}));
                        } else {
                            buffer.push_back(new Instruction({arr_ste.operand, Operand(std::to_string(cnt), Type::IntLiteral), Operand("0", Type::IntLiteral), Operator::store}));
                        }
                    }
                }
            } else if ((int)root->children.size() == 9) { // 二维数组定义
                ANALYSIS(constexp1, ConstExp, 2);
                ANALYSIS(constexp2, ConstExp, 5);
                int dim1 = std::stoi(constexp1->v);
                int dim2 = std::stoi(constexp2->v);
                int array_size = dim1 * dim2;
                STE arr_ste;
                arr_ste.dimension.push_back(dim1);
                arr_ste.dimension.push_back(dim2);
                ir::Type curr_type = root_type;
                if (curr_type == ir::Type::Int) {
                    curr_type = ir::Type::IntPtr;
                } else if (curr_type == ir::Type::Float) {
                    curr_type = ir::Type::FloatPtr;
                }
                arr_ste.operand = ir::Operand(new_name, curr_type);
                symbol_table.scope_stack.back().table[id] = arr_ste;
                buffer.push_back(new Instruction({Operand(std::to_string(array_size), ir::Type::IntLiteral), {}, Operand(new_name, curr_type), Operator::alloc}));

                GET_CHILD_PTR(initval, InitVal, 8);
                int cnt = 0;
                if (initval->children.size() == 2) { // 只有{}去初始化数组
                    for (int i = 0; i < array_size; i++) {
                        if (arr_ste.operand.type == Type::FloatPtr) {
                            buffer.push_back(new Instruction({arr_ste.operand, Operand(std::to_string(i), Type::IntLiteral), Operand("0.0", Type::FloatLiteral), Operator::store}));
                        } else {
                            buffer.push_back(new Instruction({arr_ste.operand, Operand(std::to_string(i), Type::IntLiteral), Operand("0", Type::IntLiteral), Operator::store}));
                        }
                    }
                } else {
                    // 对每个元素逐一赋初值
                    for (int i = 1; i < (int)initval->children.size() - 1; i += 2, cnt++) {
                        InitVal* child = dynamic_cast<InitVal*>(initval->children[i]);
                        Exp* exp = dynamic_cast<Exp*>(child->children[0]);
                        analysisExp(exp, buffer);
                        std::string v = exp->v;
                        ir::Type t = exp->t;
                        if (arr_ste.operand.type == Type::FloatPtr) {
                            if (t == ir::Type::Int) {
                                Operand int_op(v, ir::Type::Int);
                                Operand float_tmp("t" + std::to_string(tmp_cnt++), ir::Type::Float);
                                buffer.push_back(new Instruction(int_op, {}, float_tmp, Operator::cvt_i2f));
                                buffer.push_back(new Instruction({arr_ste.operand, Operand(std::to_string(cnt), Type::IntLiteral), float_tmp, Operator::store}));
                                continue;
                            } else if (t == ir::Type::IntLiteral) {
                                v = std::to_string((float)std::stoi(v));
                                v.erase(v.find_last_not_of('0') + 1, std::string::npos);
                                if (v.back() == '.') v += "0";
                                t = ir::Type::FloatLiteral;
                            } else if (t == ir::Type::FloatLiteral) {
                                v.erase(v.find_last_not_of('0') + 1, std::string::npos);
                                if (v.back() == '.') v += "0";
                            }
                            buffer.push_back(new Instruction({arr_ste.operand, Operand(std::to_string(cnt), Type::IntLiteral), Operand(v, t), Operator::store}));
                        } else {
                            if (t == ir::Type::FloatLiteral) {
                                v = std::to_string((int)std::stof(v));
                                t = ir::Type::IntLiteral;
                            }
                            buffer.push_back(new Instruction({arr_ste.operand, Operand(std::to_string(cnt), Type::IntLiteral), Operand(v, t), Operator::store}));
                        }
                    }
                    // 剩余元素补0
                    for (; cnt < array_size; cnt++) {
                        if (arr_ste.operand.type == Type::FloatPtr) {
                            buffer.push_back(new Instruction({arr_ste.operand, Operand(std::to_string(cnt), Type::IntLiteral), Operand("0.0", Type::FloatLiteral), Operator::store}));
                        } else {
                            buffer.push_back(new Instruction({arr_ste.operand, Operand(std::to_string(cnt), Type::IntLiteral), Operand("0", Type::IntLiteral), Operator::store}));
                        }
                    }
                }
            }
        } else { // 数组,没有赋值
            if ((int)root->children.size() == 4) { // 一维数组定义
                ANALYSIS(constexp, ConstExp, 2);
                int array_size = std::stoi(constexp->v);
                STE arr_ste;
                arr_ste.dimension.push_back(array_size);
                ir::Type curr_type = root_type;
                if (curr_type == ir::Type::Int) {
                    curr_type = ir::Type::IntPtr;
                } else if (curr_type == ir::Type::Float) {
                    curr_type = ir::Type::FloatPtr;
                }
                arr_ste.operand = ir::Operand(new_name, curr_type);
                symbol_table.scope_stack.back().table[id] = arr_ste;
                buffer.push_back(new Instruction({Operand(std::to_string(array_size), ir::Type::IntLiteral), {}, Operand(new_name, curr_type), Operator::alloc}));

                // 默认全0初始化
                for (int i = 0; i < array_size; i++) {
                    if (arr_ste.operand.type == Type::FloatPtr) {
                        buffer.push_back(new Instruction({arr_ste.operand, Operand(std::to_string(i), Type::IntLiteral), Operand("0.0", Type::FloatLiteral), Operator::store}));
                    } else {
                        buffer.push_back(new Instruction({arr_ste.operand, Operand(std::to_string(i), Type::IntLiteral), Operand("0", Type::IntLiteral), Operator::store}));
                    }
                }
            } else if ((int)root->children.size() == 7) { // 二维数组定义
                ANALYSIS(constexp1, ConstExp, 2);
                ANALYSIS(constexp2, ConstExp, 5);
                int dim1 = std::stoi(constexp1->v);
                int dim2 = std::stoi(constexp2->v);
                int array_size = dim1 * dim2;
                STE arr_ste;
                arr_ste.dimension.push_back(dim1);
                arr_ste.dimension.push_back(dim2);
                ir::Type curr_type = root_type;
                if (curr_type == ir::Type::Int) {
                    curr_type = ir::Type::IntPtr;
                } else if (curr_type == ir::Type::Float) {
                    curr_type = ir::Type::FloatPtr;
                }
                arr_ste.operand = ir::Operand(new_name, curr_type);
                symbol_table.scope_stack.back().table[id] = arr_ste;
                buffer.push_back(new Instruction({Operand(std::to_string(array_size), ir::Type::IntLiteral), {}, Operand(new_name, curr_type), Operator::alloc}));

                // 默认全0初始化
                for (int i = 0; i < array_size; i++) {
                    if (arr_ste.operand.type == Type::FloatPtr) {
                        buffer.push_back(new Instruction({arr_ste.operand, Operand(std::to_string(i), Type::IntLiteral), Operand("0.0", Type::FloatLiteral), Operator::store}));
                    } else {
                        buffer.push_back(new Instruction({arr_ste.operand, Operand(std::to_string(i), Type::IntLiteral), Operand("0", Type::IntLiteral), Operator::store}));
                    }
                }
            }
        }
    }
}
// InitVal -> Exp | '{' [ InitVal { ',' InitVal } ] '}'
void frontend::Analyzer::analysisInitVal(InitVal* root, vector<ir::Instruction*>& buffer){

    if (root->children[0]->type == NodeType::EXP){  
        ANALYSIS(exp, Exp, 0);
        root->v = exp->v;
        root->t = exp->t;
    }
}


// FuncFParam -> BType Ident ['[' ']' { '[' Exp ']' }]
void frontend::Analyzer::analysisFuncFParam(FuncFParam* root, ir::Function& buffer){
    
    auto btype = dynamic_cast<BType*>(root->children[0]);
    assert(btype);
    analysisBType(btype, buffer.InstVec);
    std::string name = dynamic_cast<Term*>(root->children[1])->token.value; 
    if ((int)root->children.size() > 2){     

        auto type = (btype->t == Type::Int) ? Type::IntPtr : Type::FloatPtr;
        buffer.ParameterList.push_back(Operand(name, type));   
        symbol_table.scope_stack.back().table.insert({name, {Operand(name, type), {}}});

    }else{      
        buffer.ParameterList.push_back(Operand(name, btype->t));   
        symbol_table.scope_stack.back().table.insert({name, {Operand(name, btype->t), {}}});
    }
}


// FuncFParams -> FuncFParam { ',' FuncFParam }
void frontend::Analyzer::analysisFuncFParams(FuncFParams* root, ir::Function& buffer){
    if ((int)root->children.size() == 1){
        ANALYSIS(funcfparam, FuncFParam, 0);
    }else{
        ANALYSIS(funcfparam, FuncFParam, 0);
        int i = 1;
        while (i < (int)root->children.size()){
            ANALYSIS(funcfparam, FuncFParam, i+1);
            i += 2;
        }
    }
}


// Block -> '{' { BlockItem } '}'
void frontend::Analyzer::analysisBlock(Block* root, vector<ir::Instruction*>& buffer){
    symbol_table.add_scope(root);   
    if ((int)root->children.size() > 2){
        int i = 1;
        while (i < (int)root->children.size()-1){
            ANALYSIS(blockitem, BlockItem, i);
            i += 1;
        }
    }
    symbol_table.exit_scope();  
}


// BlockItem -> Decl | Stmt
void frontend::Analyzer::analysisBlockItem(BlockItem* root, vector<ir::Instruction*>& buffer){
    if (root->children[0]->type == NodeType::DECL){     
        ANALYSIS(decl, Decl, 0);
    }else if (root->children[0]->type == NodeType::STMT){   
        ANALYSIS(stmt, Stmt, 0);
    }
}


// Stmt -> LVal '=' Exp ';' | Block | 'if' '(' Cond ')' Stmt [ 'else' Stmt ] | 'while' '(' Cond ')' Stmt | 'break' ';' | 'continue' ';' | 'return' [Exp] ';' | [Exp] ';'
void frontend::Analyzer::analysisStmt(Stmt* root, vector<ir::Instruction*>& buffer){

    if (root->children[0]->type == NodeType::LVAL){     
        ANALYSIS(exp, Exp, 2);  
        ANALYSIS(lval, LVal, 0);    

    }else if (root->children[0]->type == NodeType::BLOCK){   

        ANALYSIS(block, Block, 0);

    }else if (root->children[0]->type == NodeType::EXP){    

        ANALYSIS(exp, Exp, 0);

    }else if (dynamic_cast<Term*>(root->children[0])->token.type == TokenType::IFTK){  
        // Stmt -> 'if' '(' Cond ')' Stmt [ 'else' Stmt ]
        auto tmp1 = vector<Instruction*>();
        GET_CHILD_PTR(cond, Cond, 2);
        analysisCond(cond, tmp1);    
        buffer.insert(buffer.end(), tmp1.begin(), tmp1.end());    

        // Convert float condition to int if needed
        Operand condOp = Operand(cond->v, cond->t);
        if (cond->t == Type::Float || cond->t == Type::FloatLiteral) {
            auto tmpInt = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
            buffer.push_back(new Instruction(condOp, {}, tmpInt, Operator::cvt_f2i));
            std::cout << "[GEN] cvt_f2i: " << tmpInt.name << ", type: " << toString(tmpInt.type) << std::endl;
            condOp = tmpInt;
        }

        buffer.push_back(new Instruction(condOp, Operand(), Operand("2",Type::IntLiteral), Operator::_goto));

        // 分析if的Stmt
        GET_CHILD_PTR(stmt1, Stmt, 4);   
        auto tmp2 = vector<Instruction*>();  
        analysisStmt(stmt1, tmp2);   

        if ((int)root->children.size() == 5){    
            buffer.push_back(new Instruction({Operand(), Operand(), Operand(std::to_string(tmp2.size()+1), Type::IntLiteral), Operator::_goto}));
            buffer.insert(buffer.end(), tmp2.begin(), tmp2.end());
            buffer.push_back(new Instruction({Operand(), Operand(), Operand(), Operator::__unuse__}));

        }else{      
            auto tmp3 = vector<Instruction*>();     
            GET_CHILD_PTR(stmt2, Stmt, 6);   
            analysisStmt(stmt2, tmp3);   
            tmp2.push_back(new Instruction({Operand(), Operand(), Operand(std::to_string(tmp3.size()+1), Type::IntLiteral), Operator::_goto}));
            buffer.push_back(new Instruction({Operand(), Operand(), Operand(std::to_string(tmp2.size()+1), Type::IntLiteral), Operator::_goto}));
            buffer.insert(buffer.end(), tmp2.begin(), tmp2.end());
            buffer.insert(buffer.end(), tmp3.begin(), tmp3.end());
            buffer.push_back(new Instruction({Operand(), Operand(), Operand(), Operator::__unuse__}));
        }
    }else if (dynamic_cast<Term*>(root->children[0])->token.type == TokenType::WHILETK){   // while块
        // Stmt -> 'while' '(' Cond ')' Stmt 
        GET_CHILD_PTR(cond, Cond, 2);
        auto tmp1 = vector<Instruction*>();  
        analysisCond(cond, tmp1);

        // Convert float condition to int if needed
        Operand condOp = Operand(cond->v, cond->t);
        if (cond->t == Type::Float || cond->t == Type::FloatLiteral) {
            auto tmpInt = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
            buffer.push_back(new Instruction(condOp, {}, tmpInt, Operator::cvt_f2i));
            std::cout << "[GEN] cvt_f2i: " << tmpInt.name << ", type: " << toString(tmpInt.type) << std::endl;
            condOp = tmpInt;
        }

        GET_CHILD_PTR(stmt, Stmt, 4);
        auto tmp2 = vector<Instruction*>();  
        analysisStmt(stmt, tmp2);
        tmp2.push_back(new Instruction({Operand("continue", Type::null), Operand(), Operand(), Operator::__unuse__}));

        for (int i=0; i<(int)tmp2.size(); i++){
            if (tmp2[i]->op == Operator::__unuse__ && tmp2[i]->op1.type == Type::null){
                if (tmp2[i]->op1.name == "break"){
                    tmp2[i] = new Instruction({Operand(), Operand(), Operand(std::to_string((int)tmp2.size()-i),Type::IntLiteral), Operator::_goto});
                }
                else if (tmp2[i]->op1.name == "continue"){
                    auto goto_inst = new Instruction({Operand(), Operand(), Operand(std::to_string(-(2+i+(int)tmp1.size())), Type::IntLiteral), Operator::_goto});
                    tmp2[i] = goto_inst;
                }
            }
        }

        buffer.insert(buffer.end(), tmp1.begin(), tmp1.end());
        buffer.push_back(new Instruction({condOp, Operand(), Operand("2",Type::IntLiteral), Operator::_goto}));
        buffer.push_back(new Instruction({Operand(), Operand(), Operand(std::to_string(tmp2.size()+1), Type::IntLiteral), Operator::_goto}));
        buffer.insert(buffer.end(), tmp2.begin(), tmp2.end());
        buffer.push_back(new Instruction(Operand(), Operand(), Operand(), Operator::__unuse__));

    }else if (dynamic_cast<Term*>(root->children[0])->token.type == TokenType::BREAKTK){   
        
        buffer.push_back(new Instruction({Operand("break", Type::null), Operand(), Operand(), Operator::__unuse__}));

    }else if (dynamic_cast<Term*>(root->children[0])->token.type == TokenType::CONTINUETK){    
        
        buffer.push_back(new Instruction({Operand("continue", Type::null), Operand(), Operand(), Operator::__unuse__}));
    
    }else if (dynamic_cast<Term*>(root->children[0])->token.type == TokenType::RETURNTK){  
        
        // stmt -> 'return' [Exp] ';'
        if ((int)root->children.size() == 2){
            Instruction* return_inst = new Instruction({Operand("null", Type::null), Operand(), Operand(), Operator::_return});
            buffer.push_back(return_inst);

        }else{
            // stmt -> 'return' Exp ';'
            auto tmp = vector<Instruction*>();
            GET_CHILD_PTR(exp, Exp, 1);
            analysisExp(exp, tmp);
            buffer.insert(buffer.end(), tmp.begin(), tmp.end());     

            // 根据函数返回类型进行返回
            if (curr_function->returnType == Type::Int)
            {
                // Int or IntLiteral
                if (exp->t == Type::Int || exp->t == Type::IntLiteral){
                    Instruction* rerurn_inst = new Instruction({Operand(exp->v, exp->t), Operand(), Operand(), Operator::_return});
                    buffer.push_back(rerurn_inst);  

                }
                // Float or FloatLiteral
                else if (exp->t == Type::FloatLiteral){
                    Operand literal_op(exp->v, Type::FloatLiteral);
                    auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
                    buffer.push_back(new Instruction(literal_op, {}, tmp, Operator::fdef));
                    buffer.push_back(new Instruction(tmp, {}, {}, Operator::_return));
                }
                else if (exp->t == Type::Float){
                    Operand tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
                    buffer.push_back(new Instruction(Operand(exp->v,Type::Float), Operand(), tmp, Operator::cvt_f2i));
                    buffer.push_back(new Instruction(tmp, Operand(), Operand(), Operator::_return));
                }
            }
            else if (curr_function->returnType == Type::Float)
            {
                // Float or FloatLiteral
                if (exp->t == Type::Float || exp->t == Type::FloatLiteral){
                    Instruction* retInst = new Instruction(Operand(exp->v,exp->t), Operand(), Operand(), Operator::_return);
                    buffer.push_back(retInst);
                }
                // Int or IntLiteral
                else if (exp->t == Type::IntLiteral){
                    float val = (float)std::stoi(exp->v);
                    Instruction* retInst = new Instruction(Operand(std::to_string(val),Type::FloatLiteral), Operand(), Operand(), Operator::_return);
                    buffer.push_back(retInst);
                }
                else if (exp->t == Type::Int){
                    Operand tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
                    Instruction* cvtInst = new Instruction(Operand(exp->v, exp->t), Operand(), tmp, Operator::cvt_i2f);
                    Instruction* retInst = new Instruction(tmp, Operand(), Operand(), Operator::_return);
                    buffer.push_back(cvtInst);
                    buffer.push_back(retInst);
                }
            }
        }
    }
}


// Exp -> AddExp
void frontend::Analyzer::analysisExp(Exp* root, vector<ir::Instruction*>& buffer){
    ANALYSIS(addexp, AddExp, 0);    
    COPY_EXP_NODE(addexp, root);
}


// Cond -> LOrExp
void frontend::Analyzer::analysisCond(Cond* root, vector<ir::Instruction*>& buffer){
    ANALYSIS(lorexp, LOrExp, 0);    
    COPY_EXP_NODE(lorexp, root);
}


// LVal -> Ident {'[' Exp ']'}
void frontend::Analyzer::analysisLVal(LVal* root, vector<ir::Instruction*>& buffer){
    auto tk = dynamic_cast<Term*>(root->children[0])->token;    
    auto op = symbol_table.get_operand(tk.value);   
    root->t = op.type;  

    if((int)root->children.size() == 1){     // LVal -> Ident
        root->v = op.name;
        root->is_computable = (root->t == Type::IntLiteral || root->t == Type::FloatLiteral);

        if (root->parent->type == NodeType::STMT){   // lval=exp
            auto exp_par = dynamic_cast<Exp*>(root->parent->children[2]);
            Operand value = Operand(exp_par->v, exp_par->t);
            Operand des = Operand(root->v, root->t);

            // 类型一致性处理
            if (root->t == Type::Float) {
                if (value.type == Type::Int) {
                    auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
                    buffer.push_back(new Instruction(value, {}, tmp, Operator::cvt_i2f));
                    value = tmp;
                } else if (value.type == Type::IntLiteral) {
                    std::string v = std::to_string((float)std::stoi(value.name));
                    v.erase(v.find_last_not_of('0') + 1, std::string::npos);
                    if (v.back() == '.') v += "0";
                    value.name = v;
                    value.type = Type::FloatLiteral;
                }
            } else if (root->t == Type::Int) {
                if (value.type == Type::Float) {
                    auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
                    buffer.push_back(new Instruction(value, {}, tmp, Operator::cvt_f2i));
                    value = tmp;
                } else if (value.type == Type::FloatLiteral) {
                    value.name = std::to_string((int)std::stof(value.name));
                    value.type = Type::IntLiteral;
                }
            }

            if (root->t == Type::Int){
                buffer.push_back(new Instruction({value, Operand(), des, Operator::mov}));
            }else{
                buffer.push_back(new Instruction({value, Operand(), des, Operator::fmov}));
            }
        }

    }else{      // LVal -> Ident {'[' Exp ']'}
        STE arr = symbol_table.get_ste(tk.value);
        vector<int> dimension = arr.dimension;  // 维度

        // Ident '[' Exp ']'
        if ((int)root->children.size() == 4){     // 一维数组
            ANALYSIS(exp, Exp, 2);
            //元素类型直接取数组指针类型
            Type t = (arr.operand.type == Type::IntPtr) ? Type::Int : Type::Float;
            root->t = t;
            Operand index = Operand(exp->v, exp->t);

            if (root->parent->type == NodeType::STMT){   // 赋值
                auto exp_par = dynamic_cast<Exp*>(root->parent->children[2]);
                Operand value = Operand(exp_par->v, exp_par->t);

                // 类型一致性处理
                if (arr.operand.type == Type::FloatPtr) {
                    if (value.type == Type::Int) {
                        auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
                        buffer.push_back(new Instruction(value, {}, tmp, Operator::cvt_i2f));
                        value = tmp;
                    } else if (value.type == Type::IntLiteral) {
                        std::string v = std::to_string((float)std::stoi(value.name));
                        v.erase(v.find_last_not_of('0') + 1, std::string::npos);
                        if (v.back() == '.') v += "0";
                        value.name = v;
                        value.type = Type::FloatLiteral;
                    }
                } else if (arr.operand.type == Type::IntPtr) {
                    if (value.type == Type::Float) {
                        auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
                        buffer.push_back(new Instruction(value, {}, tmp, Operator::cvt_f2i));
                        value = tmp;
                    } else if (value.type == Type::FloatLiteral) {
                        value.name = std::to_string((int)std::stof(value.name));
                        value.type = Type::IntLiteral;
                    }
                }

                buffer.push_back(new Instruction({arr.operand, index, value, Operator::store}));
                root->v = value.name;
            }else{      // 作为右值，取数操作
                Operand des = Operand("t" + std::to_string(tmp_cnt++), t);
                buffer.push_back(new Instruction({arr.operand, index, des, Operator::load}));
                root->v = des.name;
            }
        }else{      // 二维数组
            ANALYSIS(exp1, Exp, 2);
            ANALYSIS(exp2, Exp, 5);
            // 元素类型直接取数组指针类型
            Type t = (arr.operand.type == Type::IntPtr) ? Type::Int : Type::Float;
            root->t = t;
            if (exp1->is_computable && exp2->is_computable){    // 可以直接计算下标
                std::string i = std::to_string(std::stoi(exp1->v) * dimension[1] + std::stoi(exp2->v));
                Operand index = Operand(i, Type::IntLiteral);

                if (root->parent->type == NodeType::STMT){   // 赋值
                    auto exp_par = dynamic_cast<Exp*>(root->parent->children[2]);
                    Operand value = Operand(exp_par->v, exp_par->t);

                    // 类型一致性处理
                    if (arr.operand.type == Type::FloatPtr) {
                        if (value.type == Type::Int) {
                            auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
                            buffer.push_back(new Instruction(value, {}, tmp, Operator::cvt_i2f));
                            value = tmp;
                        } else if (value.type == Type::IntLiteral) {
                            std::string v = std::to_string((float)std::stoi(value.name));
                            v.erase(v.find_last_not_of('0') + 1, std::string::npos);
                            if (v.back() == '.') v += "0";
                            value.name = v;
                            value.type = Type::FloatLiteral;
                        }
                    } else if (arr.operand.type == Type::IntPtr) {
                        if (value.type == Type::Float) {
                            auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
                            buffer.push_back(new Instruction(value, {}, tmp, Operator::cvt_f2i));
                            value = tmp;
                        } else if (value.type == Type::FloatLiteral) {
                            value.name = std::to_string((int)std::stof(value.name));
                            value.type = Type::IntLiteral;
                        }
                    }

                    buffer.push_back(new Instruction({arr.operand, index, value, Operator::store}));
                    root->v = value.name;
                }else{
                    Operand des = Operand("t" + std::to_string(tmp_cnt++), t);
                    buffer.push_back(new Instruction({arr.operand, index, des, Operator::load}));
                    root->v = des.name;
                }
            }else{      // 下标不可直接计算
                auto op1 = Operand(exp1->v, exp1->t);
                auto op2 = Operand(std::to_string(dimension[1]), Type::IntLiteral);
                auto op3 = Operand(exp2->v, exp2->t);
                type_transform(op1, op2, buffer);
                auto tmp1 = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
                auto tmp2 = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
                buffer.push_back(new Instruction({op1, op2, tmp1, Operator::mul}));
                buffer.push_back(new Instruction({tmp1, op3, tmp2, Operator::add}));
                if (root->parent->type == NodeType::STMT){   // 赋值
                    auto exp_par = dynamic_cast<Exp*>(root->parent->children[2]);
                    Operand value = Operand(exp_par->v, exp_par->t);

                    // 类型一致性处理
                    if (arr.operand.type == Type::FloatPtr) {
                        if (value.type == Type::Int) {
                            auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
                            buffer.push_back(new Instruction(value, {}, tmp, Operator::cvt_i2f));
                            value = tmp;
                        } else if (value.type == Type::IntLiteral) {
                            std::string v = std::to_string((float)std::stoi(value.name));
                            v.erase(v.find_last_not_of('0') + 1, std::string::npos);
                            if (v.back() == '.') v += "0";
                            value.name = v;
                            value.type = Type::FloatLiteral;
                        }
                    } else if (arr.operand.type == Type::IntPtr) {
                        if (value.type == Type::Float) {
                            auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
                            buffer.push_back(new Instruction(value, {}, tmp, Operator::cvt_f2i));
                            value = tmp;
                        } else if (value.type == Type::FloatLiteral) {
                            value.name = std::to_string((int)std::stof(value.name));
                            value.type = Type::IntLiteral;
                        }
                    }

                    buffer.push_back(new Instruction({arr.operand, tmp2, value, Operator::store}));
                    root->v = value.name;
                }else{
                    Operand des = Operand("t" + std::to_string(tmp_cnt++), t);
                    buffer.push_back(new Instruction({arr.operand, tmp2, des, Operator::load}));
                    root->v = des.name;
                }
            }
        }
    }
}


// PrimaryExp -> '(' Exp ')' | LVal | Number
void frontend::Analyzer::analysisPrimaryExp(PrimaryExp* root, vector<ir::Instruction*>& buffer){
    if (root->children[0]->type == NodeType::TERMINAL){     
        ANALYSIS(exp, Exp, 1);  
        COPY_EXP_NODE(exp, root);

    }else if (root->children[0]->type == NodeType::LVAL){   
        ANALYSIS(lval, LVal, 0);    
        COPY_EXP_NODE(lval, root);

    }else{  
        root->is_computable = true; 
        auto number_tk = dynamic_cast<Term*>(root->children[0]->children[0])->token;  
        root->t = (number_tk.type==TokenType::INTLTR) ? Type::IntLiteral : Type::FloatLiteral;      
        if (root->t == Type::IntLiteral){
            root->v = number_tk.value;     
        }else{
            root->v = number_tk.value;
        }
    }
}


// UnaryExp -> PrimaryExp | Ident '(' [FuncRParams] ')' | UnaryOp UnaryExp
void frontend::Analyzer::analysisUnaryExp(UnaryExp* root, vector<ir::Instruction*>& buffer){
    if (root->children[0]->type == NodeType::PRIMARYEXP){   
        ANALYSIS(primaryexp, PrimaryExp, 0);
        COPY_EXP_NODE(primaryexp, root);    

    }else if (root->children[0]->type == NodeType::TERMINAL){   
        
        std::string func_name = dynamic_cast<Term*>(root->children[0])->token.value;   
        auto op1 = Operand(func_name, Type::null);  
        Type t = symbol_table.functions[func_name]->returnType;     
        auto des = Operand("t" + std::to_string(tmp_cnt++), t);     
        if ((int)root->children.size() == 3){    
            buffer.push_back(new ir::CallInst(op1, des));
        }else{
            auto callinst = new ir::CallInst(op1, vector<Operand>(), des);  
            GET_CHILD_PTR(funcrparams, FuncRParams, 2);     
            assert(funcrparams);
            analysisFuncRParams(funcrparams, buffer, *callinst);
            buffer.push_back(callinst);     
        }
        root->v = des.name;
        root->t = t;

    }else{      
        // UnaryExp -> UnaryOp UnaryExp
        auto tk = dynamic_cast<Term*>(root->children[0]->children[0])->token.type;
        ANALYSIS(unaryexp, UnaryExp, 1);    
        if (tk == TokenType::PLUS){     
            COPY_EXP_NODE(unaryexp, root);
        }else{      
            root->is_computable = unaryexp->is_computable;
            root->t = unaryexp->t;
            if (unaryexp->is_computable){   
                if (unaryexp->t == Type::IntLiteral){  
                    if (tk == TokenType::MINU){
                        root->v = std::to_string(- std::stoi(unaryexp->v));
                    }else{
                        root->v = std::to_string(! std::stoi(unaryexp->v));
                    }
                }else{  
                    if (tk == TokenType::MINU){
                        root->v = std::to_string(- std::stof(unaryexp->v));
                    }else{
                        root->v = std::to_string(! std::stof(unaryexp->v));
                    }
                }
            }else{  
                if (unaryexp->t == Type::Int){      
                    auto op1 = Operand(unaryexp->v, unaryexp->t);
                    auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
                    if (tk == TokenType::MINU){
                        auto tmp1 = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
                        buffer.push_back(new Instruction(Operand("0", Type::IntLiteral), Operand(), tmp, Operator::def));
                        buffer.push_back(new Instruction(tmp, op1, tmp1, Operator::sub));
                        root->v = tmp1.name;
                    }else{
                        buffer.push_back(new Instruction(op1, Operand(), tmp, Operator::_not));
                        root->v = tmp.name;
                    }
                }else{     
                    auto op1 = Operand(unaryexp->v, unaryexp->t);
                    auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
                    if (tk == TokenType::MINU){
                        auto tmp1 = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
                        buffer.push_back(new Instruction(Operand("0.0", Type::FloatLiteral), Operand(), tmp, Operator::fdef));
                        buffer.push_back(new Instruction(tmp, op1, tmp1, Operator::fsub));
                        root->v = tmp1.name;
                    }
                }
            }
        }
    }
}


// FuncRParams -> Exp { ',' Exp }
void frontend::Analyzer::analysisFuncRParams(FuncRParams* root, vector<ir::Instruction*>& buffer, ir::CallInst& callinst){
    ANALYSIS(exp1, Exp, 0);  
    Operand arg(exp1->v, exp1->t);
    if (arg.type == Type::FloatLiteral) {
        auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
        buffer.push_back(new Instruction(arg, {}, tmp, Operator::fdef));
        arg = tmp;
    }
    callinst.argumentList.push_back(arg);
    int i = 1;
    while (i < (int)root->children.size()){
        ANALYSIS(exp2, Exp, i+1);  
        callinst.argumentList.push_back(Operand(exp2->v, exp2->t));
        i += 2;
    }
}


// MulExp -> UnaryExp { ('*' | '/' | '%') UnaryExp }
void frontend::Analyzer::analysisMulExp(MulExp* root, vector<ir::Instruction*>& buffer){
    if ((int)root->children.size() == 1){
        ANALYSIS(unaryexp1, UnaryExp, 0);    
        COPY_EXP_NODE(unaryexp1, root);    
    }else if ((int)root->children.size() > 1){
        ANALYSIS(unaryexp1, UnaryExp, 0);   
        root->is_computable = unaryexp1->is_computable;
        root->t = unaryexp1->t;
        root->v = unaryexp1->v;
        int i = 1;
        while (i < (int)root->children.size()){
            auto tk = dynamic_cast<Term*>(root->children[i])->token.type;   
            ANALYSIS(unaryexp2, UnaryExp, i+1);     
            if(root->is_computable && unaryexp2->is_computable){    
                root->is_computable = true;
                if(root->t != unaryexp2->t){   
                    root->t = Type::FloatLiteral;
                }
                if(root->t == Type::IntLiteral){    
                    if (tk == TokenType::MULT){
                        root->v = std::to_string(std::stoi(root->v) * std::stoi(unaryexp2->v));
                    }else if (tk == TokenType::DIV){
                        root->v = std::to_string(std::stoi(root->v) / std::stoi(unaryexp2->v));
                    }else{
                        root->v = std::to_string(std::stoi(root->v) % std::stoi(unaryexp2->v));
                    }
                }else{      
                    if (tk == TokenType::MULT){
                        root->v = std::to_string(std::stof(root->v) * std::stof(unaryexp2->v));
                    }else if (tk == TokenType::DIV){
                        root->v = std::to_string(std::stof(root->v) / std::stof(unaryexp2->v));
                    }
                }
            }else{  
                root->is_computable = false;
                Operand op1 = Operand(root->v, root->t);
                Operand op2 = Operand(unaryexp2->v, unaryexp2->t);
                Operand tmp = Operand("t" + std::to_string(tmp_cnt++), root->t);
                if (tk == TokenType::MULT){
                    if (root->t == unaryexp2->t){   
                        if (tmp.type == Type::Int){
                            assert(op1.type == Type::Int || op1.type == Type::IntLiteral);
                            assert(op2.type == Type::Int || op2.type == Type::IntLiteral);
                            buffer.push_back(new Instruction({op1, op2, tmp, Operator::mul}));  
                        }else{
                            buffer.push_back(new Instruction({op1, op2, tmp, Operator::fmul}));  
                        }
                    }else{      
                        type_transform(op1, op2, buffer);
                        tmp.type = op1.type;     
                        if (tmp.type == Type::Int){
                            assert(op1.type == Type::Int || op1.type == Type::IntLiteral);
                            assert(op2.type == Type::Int || op2.type == Type::IntLiteral);
                            buffer.push_back(new Instruction({op1, op2, tmp, Operator::mul}));  
                        }else{
                            buffer.push_back(new Instruction({op1, op2, tmp, Operator::fmul}));  
                        }
                    }
                }else if (tk == TokenType::DIV){
                    if (root->t == unaryexp2->t){   
                        if (tmp.type == Type::Int){
                            assert(op1.type == Type::Int || op1.type == Type::IntLiteral);
                            assert(op2.type == Type::Int || op2.type == Type::IntLiteral);
                            buffer.push_back(new Instruction({op1, op2, tmp, Operator::div}));  
                        }else{
                            buffer.push_back(new Instruction({op1, op2, tmp, Operator::fdiv}));  
                        }
                    }else{
                        type_transform(op1, op2, buffer);
                        tmp.type = op1.type;
                        if(tmp.type == Type::Int){
                            assert(op1.type == Type::Int || op1.type == Type::IntLiteral);
                            assert(op2.type == Type::Int || op2.type == Type::IntLiteral);
                            buffer.push_back(new Instruction({op1, op2, tmp, Operator::div}));  
                        }else{
                            buffer.push_back(new Instruction({op1, op2, tmp, Operator::fdiv}));  
                        }
                    }
                }else{
                    assert(op1.type == Type::Int || op1.type == Type::IntLiteral);
                    assert(op2.type == Type::Int || op2.type == Type::IntLiteral);
                    buffer.push_back(new Instruction({op1, op2, tmp, Operator::mod}));  
                }
                root->v = tmp.name;     
                root->t = tmp.type;     
            }
            i += 2;
        }
    }
}


// AddExp -> MulExp { ('+' | '-') MulExp }
void frontend::Analyzer::analysisAddExp(AddExp* root, vector<ir::Instruction*>& buffer){
    if ((int)root->children.size() == 1){
        ANALYSIS(mulexp1, MulExp, 0);    
        COPY_EXP_NODE(mulexp1, root);    

    }else if ((int)root->children.size() > 1){  
        ANALYSIS(mulexp1, MulExp, 0);    
        root->is_computable = mulexp1->is_computable;
        root->t = mulexp1->t;
        root->v = mulexp1->v;
        int i = 1;
        while (i < (int)root->children.size()){
            auto tk = dynamic_cast<Term*>(root->children[i])->token.type;   
            ANALYSIS(mulexp2, MulExp, i+1);     
            if(root->is_computable && mulexp2->is_computable){    
                root->is_computable = true;
                if(root->t != mulexp2->t){   
                    root->t = Type::FloatLiteral;
                }

                if(root->t == Type::IntLiteral){    
                    if (tk == TokenType::PLUS){
                        root->v = std::to_string(std::stoi(root->v) + std::stoi(mulexp2->v));    
                    }else{  
                        root->v = std::to_string(std::stoi(root->v) - std::stoi(mulexp2->v));
                    }
                }else{     
                    if (tk == TokenType::PLUS){
                        root->v = std::to_string(std::stof(root->v) + std::stof(mulexp2->v));    
                    }else{  
                        root->v = std::to_string(std::stof(root->v) - std::stof(mulexp2->v));
                    }
                }
            }else{  
                root->is_computable = false;
                Operand op1 = Operand(root->v, root->t);
                Operand op2 = Operand(mulexp2->v, mulexp2->t);
                Operand tmp = Operand("t" + std::to_string(tmp_cnt++), root->t);
                if (!root->is_computable && !mulexp2->is_computable){   
                    if (tk == TokenType::PLUS){
                        if (root->t == mulexp2->t){   
                            if (tmp.type == Type::Int){
                                assert(op1.type == Type::Int || op1.type == Type::IntLiteral);
                                assert(op2.type == Type::Int || op2.type == Type::IntLiteral);
                                buffer.push_back(new Instruction({op1, op2, tmp, Operator::add}));  
                            }else{
                                buffer.push_back(new Instruction({op1, op2, tmp, Operator::fadd}));  
                            }
                        }else{  // 类型提升
                            type_transform(op1, op2, buffer);
                            tmp.type = op1.type;
                            if (tmp.type == Type::Int){
                                assert(op1.type == Type::Int || op1.type == Type::IntLiteral);
                                assert(op2.type == Type::Int || op2.type == Type::IntLiteral);
                                buffer.push_back(new Instruction({op1, op2, tmp, Operator::add}));  
                            }else{
                                buffer.push_back(new Instruction({op1, op2, tmp, Operator::fadd}));  
                            }
                        }
                    }else{
                        if (root->t == mulexp2->t){   
                            if (tmp.type == Type::Int){
                                assert(op1.type == Type::Int || op1.type == Type::IntLiteral);
                                assert(op2.type == Type::Int || op2.type == Type::IntLiteral);
                                buffer.push_back(new Instruction({op1, op2, tmp, Operator::sub}));  
                            }else{
                                buffer.push_back(new Instruction({op1, op2, tmp, Operator::fsub}));  
                            }
                        }else{  // 类型提升
                            type_transform(op1, op2, buffer);
                            tmp.type = op1.type;
                            if (tmp.type == Type::Int){      
                                assert(op1.type == Type::Int || op1.type == Type::IntLiteral);
                                assert(op2.type == Type::Int || op2.type == Type::IntLiteral);
                                buffer.push_back(new Instruction({op2, op1, tmp, Operator::sub}));  
                            }else{
                                buffer.push_back(new Instruction({op2, op1, tmp, Operator::fsub}));  
                            }
                        }
                    }
                }else{
                    if (tk == TokenType::PLUS){
                        if (root->t == Type::Int && mulexp2->t == Type::IntLiteral){    
                            tmp.type = Type::Int;
                            assert(op1.type == Type::Int || op1.type == Type::IntLiteral);
                            assert(op2.type == Type::Int || op2.type == Type::IntLiteral);
                            buffer.push_back(new Instruction({op1, op2, tmp, Operator::addi}));  
                        }else if (root->t == Type::IntLiteral && mulexp2->t == Type::Int){  
                            tmp.type = Type::Int;
                            assert(op2.type == Type::Int || op2.type == Type::IntLiteral);
                            assert(op1.type == Type::Int || op1.type == Type::IntLiteral);
                            buffer.push_back(new Instruction({op2, op1, tmp, Operator::addi}));  
                        }else{  // a+0.1, 0.1+a ...
                            tmp.type = Type::Float;
                            type_transform(op1, op2, buffer);
                            buffer.push_back(new Instruction({op1, op2, tmp, Operator::fadd}));  
                        }
                    }else{
                        if (root->t == Type::Int && mulexp2->t == Type::IntLiteral){    
                            tmp.type = Type::Int;
                            assert(op1.type == Type::Int || op1.type == Type::IntLiteral);
                            assert(op2.type == Type::Int || op2.type == Type::IntLiteral);
                            auto subi_inst = new Instruction({op1, op2, tmp, Operator::subi});
                            buffer.push_back(subi_inst);  

                        }else{  
                            type_transform(op1, op2, buffer);
                            tmp.type = op1.type;
                            if (tmp.type == Type::Int){      
                                assert(op2.type == Type::Int || op2.type == Type::IntLiteral);
                                assert(op1.type == Type::Int || op1.type == Type::IntLiteral);
                                buffer.push_back(new Instruction({op2, op1, tmp, Operator::sub}));  
                            }else{
                                buffer.push_back(new Instruction({op2, op1, tmp, Operator::fsub}));  
                            }
                        }
                    }
                }
                root->v = tmp.name;     
                root->t = tmp.type;     
            }
            i += 2;
        }
    }
}


// RelExp -> AddExp { ('<' | '>' | '<=' | '>=') AddExp }
void frontend::Analyzer::analysisRelExp(RelExp* root,vector<ir::Instruction*>& buffer){
     if ((int)root->children.size() == 1){    
        ANALYSIS(addexp, AddExp, 0);
        COPY_EXP_NODE(addexp, root);
        // Convert float to int for condition
        if (root->t == Type::Float || root->t == Type::FloatLiteral) {
            auto tmpInt = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
            buffer.push_back(new Instruction(Operand(root->v, root->t), {}, tmpInt, Operator::cvt_f2i));
            std::cout << "[GEN] cvt_f2i: " << tmpInt.name << ", type: " << toString(tmpInt.type) << std::endl;
            root->v = tmpInt.name;
            root->t = Type::Int;
        }
    }else{      
        // RelExp -> AddExp { ('<' | '>' | '<=' | '>=') AddExp }
        ANALYSIS(addexp1, AddExp, 0);    
        root->is_computable = addexp1->is_computable;
        root->t = addexp1->t;
        root->v = addexp1->v;

        int i = 1;
        while (i < (int)root->children.size()){
            ANALYSIS(addexp2, AddExp, i+1);     
            auto tk = dynamic_cast<Term*>(root->children[i])->token.type;   

            root->is_computable = false;    
            Operand op1 = Operand(root->v, root->t);
            Operand op2 = Operand(addexp2->v, addexp2->t);
            
            // Convert operands to same type before comparison
            if (op1.type == Type::Int && (op2.type == Type::Float || op2.type == Type::FloatLiteral)) {
                auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
                buffer.push_back(new Instruction(op1, {}, tmp, Operator::cvt_i2f));
                op1 = tmp;
            } else if (op2.type == Type::Int && (op1.type == Type::Float || op1.type == Type::FloatLiteral)) {
                auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
                buffer.push_back(new Instruction(op2, {}, tmp, Operator::cvt_i2f));
                op2 = tmp;
            }

            // 判断是否为浮点比较
            bool is_float = (op1.type == Type::Float || op1.type == Type::FloatLiteral || op2.type == Type::Float || op2.type == Type::FloatLiteral);
            Operand des = Operand("t" + std::to_string(tmp_cnt++), is_float ? Type::Float : Type::Int);

            if (tk == TokenType::LSS){
                if (!is_float){
                    buffer.push_back(new Instruction({op1, op2, des, Operator::lss}));
                }else{
                    assert(des.type == Type::Float);
                    buffer.push_back(new Instruction({op1, op2, des, Operator::flss}));
                }
            }
            else if (tk == TokenType::GTR){
                if (!is_float){
                    buffer.push_back(new Instruction({op1, op2, des, Operator::gtr}));
                }else{
                    assert(des.type == Type::Float);
                    buffer.push_back(new Instruction({op1, op2, des, Operator::fgtr}));
                }
            }
            else if (tk == TokenType::LEQ){
                if (!is_float){
                    buffer.push_back(new Instruction({op1, op2, des, Operator::leq}));
                }else{
                    assert(des.type == Type::Float);
                    buffer.push_back(new Instruction({op1, op2, des, Operator::fleq}));
                }
            }
            else{
                if (!is_float){
                    buffer.push_back(new Instruction({op1, op2, des, Operator::geq}));
                }else{
                    assert(des.type == Type::Float);
                    buffer.push_back(new Instruction({op1, op2, des, Operator::fgeq}));
                }
            }

            root->v = des.name;
            root->t = is_float ? Type::Float : Type::Int;
            i += 2;
        }
    }
}


// EqExp -> RelExp { ('==' | '!=') RelExp }
void frontend::Analyzer::analysisEqExp(EqExp* root,vector<ir::Instruction*>& buffer){
    if ((int)root->children.size() == 1){    
        ANALYSIS(relexp, RelExp, 0);     
        COPY_EXP_NODE(relexp, root);
    }else{      
        ANALYSIS(relexp1, RelExp, 0);     
        root->is_computable = relexp1->is_computable;
        root->v = relexp1->v;
        root->t = relexp1->t;

        int i = 1;
        while (i < (int)root->children.size()){
            ANALYSIS(relexp2, RelExp, i+1);     
            auto tk = dynamic_cast<Term*>(root->children[i])->token.type;  
            
            root->is_computable = false;
            Operand op1 = Operand(root->v, root->t);
            Operand op2 = Operand(relexp2->v, relexp2->t);
            
            if (tk == TokenType::EQL){ 
                // If first operand is integer type
                if (op1.type == Type::Int || op1.type == Type::IntLiteral){
                    // Convert second operand to int if needed
                    if (op2.type == Type::Float || op2.type == Type::FloatLiteral) {
                        auto tmpInt = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
                        buffer.push_back(new Instruction(op2, {}, tmpInt, Operator::cvt_f2i));
                        op2 = tmpInt;
                    }
                    assert((op2.type == ir::Type::Int || op2.type == ir::Type::IntLiteral) && "semantic.cpp: In analysisEqExp (EQL branch, op1 is Int/IntLiteral), op2 must be Int or IntLiteral after conversion.");
                    auto des = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
                    buffer.push_back(new Instruction({op1, op2, des, Operator::eq}));
                    root->v = des.name;
                } else {
                    // Float comparison
                    auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
                    buffer.push_back(new Instruction({op1, op2, tmp, Operator::feq}));
                    auto des = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
                    buffer.push_back(new Instruction({tmp, {}, des, Operator::cvt_f2i}));
                    root->v = des.name;
                }
            }else{     
                // If first operand is integer type
                if (op1.type == Type::Int || op1.type == Type::IntLiteral){
                    // Convert second operand to int if needed
                    if (op2.type == Type::Float || op2.type == Type::FloatLiteral) {
                        auto tmpInt = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
                        buffer.push_back(new Instruction(op2, {}, tmpInt, Operator::cvt_f2i));
                        op2 = tmpInt;
                    }
                    assert((op2.type == ir::Type::Int || op2.type == ir::Type::IntLiteral) && "semantic.cpp: In analysisEqExp (NEQ branch, op1 is Int/IntLiteral), op2 must be Int or IntLiteral after conversion.");
                    auto des = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
                    buffer.push_back(new Instruction({op1, op2, des, Operator::neq}));
                    root->v = des.name;
                } else {
                    // Float comparison
                    auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
                    buffer.push_back(new Instruction({op1, op2, tmp, Operator::fneq}));
                    auto des = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
                    buffer.push_back(new Instruction({tmp, {}, des, Operator::cvt_f2i}));
                    root->v = des.name;
                }
            }
            root->t = Type::Int;
            i += 2;
        }
    }
}


// LAndExp -> EqExp [ '&&' LAndExp ]
void frontend::Analyzer::analysisLAndExp(LAndExp* root, vector<ir::Instruction*>& buffer){
    if ((int)root->children.size() == 1){    
        ANALYSIS(eqexp, EqExp, 0);     
        COPY_EXP_NODE(eqexp, root);
        // Convert float to int for condition
        if (root->t == Type::Float || root->t == Type::FloatLiteral) {
            auto tmpInt = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
            buffer.push_back(new Instruction(Operand(root->v, root->t), {}, tmpInt, Operator::cvt_f2i));
            std::cout << "[GEN] cvt_f2i: " << tmpInt.name << ", type: " << toString(tmpInt.type) << std::endl;
            root->v = tmpInt.name;
            root->t = Type::Int;
        }
    }else{      
        // LAndExp -> EqExp '&&' LAndExp
        ANALYSIS(eqexp, EqExp, 0);  
        
        auto tmp = vector<ir::Instruction*>();  
        auto andexp = dynamic_cast<LAndExp*>(root->children[2]);  
        assert(andexp);
        analysisLAndExp(andexp, tmp);    
        
        root->t = Type::Int;    

        // Convert operands to int if needed
        Operand op1 = Operand(eqexp->v, eqexp->t);
        if (eqexp->t == Type::Float || eqexp->t == Type::FloatLiteral) {
            auto tmpInt = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
            buffer.push_back(new Instruction(op1, {}, tmpInt, Operator::cvt_f2i));
            std::cout << "[GEN] cvt_f2i: " << tmpInt.name << ", type: " << toString(tmpInt.type) << std::endl;
            op1 = tmpInt;
        }

        Operand op2 = Operand(andexp->v, andexp->t);
        if (andexp->t == Type::Float || andexp->t == Type::FloatLiteral) {
            auto tmpInt = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
            buffer.push_back(new Instruction(op2, {}, tmpInt, Operator::cvt_f2i));
            std::cout << "[GEN] cvt_f2i: " << tmpInt.name << ", type: " << toString(tmpInt.type) << std::endl;
            op2 = tmpInt;
        }

        Operand des = Operand("t" + std::to_string(tmp_cnt++), Type::Int);    
        Operand t1 = Operand("t" + std::to_string(tmp_cnt++), Type::Int);    
        
        buffer.push_back(new Instruction({op1, {}, t1, Operator::mov}));    
        buffer.push_back(new Instruction({t1, {}, {"2", Type::IntLiteral}, Operator::_goto}));  
        buffer.push_back(new Instruction({{}, {}, {std::to_string(tmp.size()+3), Type::IntLiteral}, Operator::_goto}));
        buffer.insert(buffer.end(), tmp.begin(), tmp.end());   
        buffer.push_back(new Instruction({op2, {}, des, Operator::mov}));   
        buffer.push_back(new Instruction({{}, {}, {"2", Type::IntLiteral}, Operator::_goto}));
        buffer.push_back(new Instruction({"0", Type::IntLiteral}, {}, des, Operator::mov));

        root->v = des.name;
    }
}

// LOrExp -> LAndExp [ '||' LOrExp ]
void frontend::Analyzer::analysisLOrExp(LOrExp* root, vector<ir::Instruction*>& buffer){
    if ((int)root->children.size() == 1){    
        ANALYSIS(landexp, LAndExp, 0);
        COPY_EXP_NODE(landexp, root);
        // Convert float to int for condition
        if (root->t == Type::Float || root->t == Type::FloatLiteral) {
            auto tmpInt = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
            buffer.push_back(new Instruction(Operand(root->v, root->t), {}, tmpInt, Operator::cvt_f2i));
            std::cout << "[GEN] cvt_f2i: " << tmpInt.name << ", type: " << toString(tmpInt.type) << std::endl;
            root->v = tmpInt.name;
            root->t = Type::Int;
        }
    }else{      
        // LOrExp -> LAndExp '||' LOrExp
        root->t = Type::Int;    
        ANALYSIS(andexp, LAndExp, 0);     

        auto tmp = vector<ir::Instruction*>();  
        auto orexp = dynamic_cast<LOrExp*>(root->children[2]);  
        assert(orexp);
        analysisLOrExp(orexp, tmp);    

        // Convert operands to int if needed
        Operand op1 = Operand(andexp->v, andexp->t);
        if (andexp->t == Type::Float || andexp->t == Type::FloatLiteral) {
            auto tmpInt = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
            buffer.push_back(new Instruction(op1, {}, tmpInt, Operator::cvt_f2i));
            std::cout << "[GEN] cvt_f2i: " << tmpInt.name << ", type: " << toString(tmpInt.type) << std::endl;
            op1 = tmpInt;
        }

        Operand op2 = Operand(orexp->v, orexp->t);
        if (orexp->t == Type::Float || orexp->t == Type::FloatLiteral) {
            auto tmpInt = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
            buffer.push_back(new Instruction(op2, {}, tmpInt, Operator::cvt_f2i));
            std::cout << "[GEN] cvt_f2i: " << tmpInt.name << ", type: " << toString(tmpInt.type) << std::endl;
            op2 = tmpInt;
        }

        Operand t1 = Operand("t" + std::to_string(tmp_cnt++), Type::Int);    
        Operand des = Operand("t" + std::to_string(tmp_cnt++), Type::Int);    
        
        buffer.push_back(new Instruction({op1, {}, t1, Operator::mov}));    
        buffer.push_back(new Instruction({t1, {}, {std::to_string(tmp.size()+3), Type::IntLiteral}, Operator::_goto}));    
        buffer.insert(buffer.end(), tmp.begin(), tmp.end());    
        buffer.push_back(new Instruction({op2, {}, des, Operator::mov}));  
        buffer.push_back(new Instruction({{}, {}, {"2", Type::IntLiteral}, Operator::_goto}));
        buffer.push_back(new Instruction({"1", Type::IntLiteral}, {}, des, Operator::mov));
        root->v = des.name;
    }
}


// ConstExp -> AddExp
void frontend::Analyzer::analysisConstExp(ConstExp* root, vector<ir::Instruction*>& buffer){
    ANALYSIS(addexp, AddExp, 0);    
    root->v = addexp->v;
    root->t = addexp->t;
}
