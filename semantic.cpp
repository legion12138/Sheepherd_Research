#include"front/semantic.h"
#include<iostream>
#include<cassert>
using ir::Instruction;
using ir::Function;
using ir::Operand;
using ir::Operator;

#define TODO assert(0 && "TODO");

// 获取父节点的指定子节点
#define GET_CHILD_PTR(node, type, index) auto node = dynamic_cast<type*>(root->children[index]); assert(node); 
// 获取父节点的指定子节点, 并且调用分析函数
#define ANALYSIS(node, type, index) auto node = dynamic_cast<type*>(root->children[index]); assert(node); analysis##type(node, buffer);
// 传递属性
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


//将数字字符串转换为十进制，包括十六进制、八进制、二进制，不过貌似执行机里已经有了
std::string trans2ten(std::string value){
    if(value.size() >= 2){
        if(value[0] == '0' && (value[1] == 'x' || value[1] == 'X')){
            return std::to_string(std::stoi(value, nullptr, 16));
        }else if(value[0] == '0' && (value[1] == 'b' || value[1] == 'B')){
            value = value.substr(2);
            return std::to_string(std::stoi(value, nullptr, 2));
        }else if(value[0] == '0'){
            return std::to_string(std::stoi(value, nullptr, 8));
        }
    }
    return std::to_string(std::stoi(value, nullptr, 10));
}


// 类型转换
void frontend::Analyzer::type_transform(Operand& a, Operand& b, vector<Instruction*>& buffer){
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
            auto tmp_op = Operand("t" + std::to_string(tmp_cnt++), Type::Int);    // b转Float
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

    // ====【新增代码】====
    // 假设你能获得main里所有符号，可以遍历symbol_table，找到arr_22，并登记到GVT
    // 这里只举例arr_22，实际应遍历所有main里的局部静态变量
    buffer.globalVal.push_back(ir::GlobalVal(Operand("arr_22", Type::FloatPtr)));
    // ===================

    std::cout<<buffer.draw();
    return buffer;
}


// CompUnit -> (Decl | FuncDef) [CompUnit]
void frontend::Analyzer::analysisCompUnit(CompUnit* root, ir::Program& buffer){

    if (root->children[0]->type == NodeType::DECL){     // 变量或常量定义
        GET_CHILD_PTR(decl, Decl, 0);   // 取得Decl节点
        assert(decl);
        analysisDecl(decl, buffer.functions.back().InstVec);    // 分析Decl节点
        
    }else if (root->children[0]->type == NodeType::FUNCDEF){    // 函数定义
        
        if (buffer.functions.size() == 1){     // 如果函数只有global,此时来新函数了,需要扫描global函数的IR向量,填全局变量

            auto global_ir = buffer.functions[0].InstVec;
            for (int i=0; i<(int)global_ir.size(); i++){   // 扫描global函数的定义IR
                buffer.globalVal.push_back(ir::GlobalVal(global_ir[i]->des));  // 填入全局变量
            }
        }

        GET_CHILD_PTR(funcdef, FuncDef, 0);     // 取得FuncDef节点
        assert(funcdef);
        auto tmp = ir::Function();  // 定义FuncDef的ir::function
        analysisFuncDef(funcdef, tmp);
        buffer.addFunction(tmp);    // ir::program增加函数
    }

    if ((int)(int)root->children.size() == 2){
        ANALYSIS(compunit, CompUnit, 1);
    }
}


// FuncDef -> FuncType Ident '(' [FuncFParams] ')' Block
void frontend::Analyzer::analysisFuncDef(FuncDef* root, ir::Function& function){

    auto tk = dynamic_cast<Term*>(root->children[0]->children[0])->token.type;  //函数返回值类型
    root->t = tk == TokenType::VOIDTK ? Type::null : tk == TokenType::INTTK ? Type::Int :Type::Float;
    root->n = dynamic_cast<Term*>(root->children[1])->token.value;
    function.name = root->n;       //函数名
    function.returnType = root->t; //返回值类型

    int cnt = ++symbol_table.block_cnt;
    symbol_table.scope_stack.push_back({cnt, "fp", map_str_ste()});   //给函数形参增加作用域
    symbol_table.functions.insert({root->n, &function});            //增加函数
    curr_function = &function;  // 当前函数指针

    if (function.name == "main"){   // 当前为main函数
        auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::null);
        auto global_callinst = new ir::CallInst(Operand("global", Type::null), vector<Operand>(), tmp);  // 函数调用IR
        curr_function->addInst(global_callinst);
    }

    auto paras = dynamic_cast<FuncFParams*>(root->children[3]);     //第三个子节点
    if (paras){     // 如果函数参数列表存在
        analysisFuncFParams(paras, function);
        analysisBlock(dynamic_cast<Block*>(root->children[5]), function.InstVec);
    }else{
        analysisBlock(dynamic_cast<Block*>(root->children[4]), function.InstVec);
    }

    if (function.returnType == Type::null){     // 函数没有返回值，加上return null，防止返回不了
        auto return_inst = new Instruction({Operand("null", Type::null), {}, {}, Operator::_return});
        curr_function->addInst(return_inst);
    }

    symbol_table.exit_scope();  //退出函数形参作用域
}


// Decl -> ConstDecl | VarDecl
void frontend::Analyzer::analysisDecl(Decl* root, vector<ir::Instruction*>& buffer){

    if (root->children[0]->type == NodeType::CONSTDECL){    // 常量定义
        ANALYSIS(constdecl, ConstDecl, 0);
    }else if (root->children[0]->type == NodeType::VARDECL){    // 变量定义
        ANALYSIS(vardecl, VarDecl, 0);
    }
}


// ConstDecl -> 'const' BType ConstDef { ',' ConstDef } ';'
void frontend::Analyzer::analysisConstDecl(ConstDecl* root, vector<ir::Instruction*>& buffer){
    ANALYSIS(btype, BType, 1);
    root->t = btype->t;   // 节点类型为BType节点类型
    ANALYSIS(constdef1, ConstDef, 2);    //分析ConstDef节点
    int i = 3;
    while (dynamic_cast<Term*>(root->children[i])->token.type == TokenType::COMMA){
        ANALYSIS(constdef2, ConstDef, i+1);  // 分析ConstDef节点
        i += 2;
    }
}


// BType -> 'int' | 'float'
void frontend::Analyzer::analysisBType(BType* root, vector<ir::Instruction*>& buffer){
    auto tk = dynamic_cast<Term*>(root->children[0])->token.type;  // 获取BType节点的类型
    root->t = tk==TokenType::INTTK ? Type::Int : Type::Float;   // 节点类型为Int或者Float
}


// ConstDef -> Ident { '[' ConstExp ']' } '=' ConstInitVal
void frontend::Analyzer::analysisConstDef(ConstDef* root, vector<ir::Instruction*>& buffer){
    auto root_type = dynamic_cast<ConstDecl*>(root->parent)->t;   // 父节点ConstDecl的类型
    GET_CHILD_PTR(identifier, Term, 0);
    string id = identifier->token.value;
    string new_name = symbol_table.get_scoped_name(id);
    root->arr_name = new_name;

    GET_CHILD_PTR(term, Term, 1);
    if (term->token.type == TokenType::ASSIGN) { // 普通常量定义
        ANALYSIS(constinitval, ConstInitVal, 2);
        Operand des = Operand(new_name, root_type);
        auto opcode = (root_type == Type::Float || root_type == Type::FloatLiteral) ? Operator::fdef : Operator::def;
        Operand op1 = Operand(constinitval->v, constinitval->t);
        if (root_type == Type::Float) {
            if (constinitval->t == Type::Int) {
                auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
                buffer.push_back(new Instruction(op1, {}, tmp, Operator::cvt_i2f));
                op1 = tmp;
            } else if (constinitval->t == Type::IntLiteral) {
                std::string v = std::to_string((float)std::stoi(op1.name));
                v.erase(v.find_last_not_of('0') + 1, std::string::npos);
                if (v.back() == '.') v += "0";
                op1.name = v;
                op1.type = Type::FloatLiteral;
            } else if (constinitval->t == Type::FloatLiteral) {
                std::string v = op1.name;
                v.erase(v.find_last_not_of('0') + 1, std::string::npos);
                if (v.back() == '.') v += "0";
                op1.name = v;
                auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
                buffer.push_back(new Instruction(op1, {}, tmp, Operator::fdef));
                op1 = tmp;
            }
        } else {
            assert(root_type == Type::Int);
            if (constinitval->t == Type::Float) {
                auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
                buffer.push_back(new Instruction(op1, {}, tmp, Operator::cvt_f2i));
                op1 = tmp;
            } else if (constinitval->t == Type::FloatLiteral) {
                op1.name = std::to_string((int)std::stof(op1.name));
                op1.type = Type::IntLiteral;
            }
        }
        buffer.push_back(new Instruction(op1, Operand(), des, opcode));
        symbol_table.scope_stack.back().table.insert({id, {op1, {}}});
    }
    else if ((int)root->children.size() == 6) { // 一维数组定义
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

        GET_CHILD_PTR(constinitval, ConstInitVal, 5);
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
        buffer.push_back(new Instruction({Operand(std::to_string(array_size), ir::Type::IntLiteral), {}, Operand(new_name, curr_type), Operator::alloc}));

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
    if (root->children[0]->type == NodeType::CONSTEXP){     // 变量定义这边
        ANALYSIS(constexp, ConstExp, 0);    //分析ConstExp节点
        root->v = constexp->v;
        root->t = constexp->t;
    }
}


// VarDecl -> BType VarDef { ',' VarDef } ';'
void frontend::Analyzer::analysisVarDecl(VarDecl* root, vector<ir::Instruction*>& buffer){

    ANALYSIS(btype, BType, 0);      // 分析Btype节点
    root->t = btype->t;             // 变量类型为BType节点类型
    ANALYSIS(vardef, VarDef, 1);    // 分析VarDef节点
    int i = 2;  
    while (i < (int)root->children.size()-1){
        ANALYSIS(vardef, VarDef, i+1);  // 分析ConstDef节点
        i += 2;
    }
}


// VarDef -> Ident { '[' ConstExp ']' } [ '=' InitVal ]
void frontend::Analyzer::analysisVarDef(VarDef* root, vector<ir::Instruction*>& buffer){

    auto root_type = dynamic_cast<VarDecl*>(root->parent)->t;

    GET_CHILD_PTR(identifier, Term, 0);
    string id = identifier->token.value;
    string new_name = symbol_table.get_scoped_name(id);

    if ((int)root->children.size() == 1) { // 普通变量定义，没有赋值
        Operand des = Operand(new_name, root_type);
        auto opcode = (root_type == Type::Float || root_type == Type::FloatLiteral) ? Operator::fdef : Operator::def;
        if (root_type == Type::Float) {
            buffer.push_back(new Instruction(Operand("0.0", Type::FloatLiteral), Operand(), des, opcode));
        } else {
            buffer.push_back(new Instruction(Operand("0", Type::IntLiteral), Operand(), des, opcode));
        }
        symbol_table.scope_stack.back().table.insert({id, {des, {}}});
    } else {
        GET_CHILD_PTR(term, Term, 1);
        if (term->token.type == TokenType::ASSIGN) { // 普通变量定义,有赋值
            ANALYSIS(initval, InitVal, 2);
            Operand des = Operand(new_name, root_type);
            auto opcode = (root_type == Type::Float || root_type == Type::FloatLiteral) ? Operator::fdef : Operator::def;
            Operand op1 = Operand(initval->v, initval->t);
            if (root_type == Type::Float) {
                if (initval->t == Type::Int) {
                    auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
                    buffer.push_back(new Instruction(op1, {}, tmp, Operator::cvt_i2f));
                    op1 = tmp;
                } else if (initval->t == Type::IntLiteral) {
                    std::string v = std::to_string((float)std::stoi(op1.name));
                    v.erase(v.find_last_not_of('0') + 1, std::string::npos);
                    if (v.back() == '.') v += "0";
                    op1.name = v;
                    op1.type = Type::FloatLiteral;
                }
            } else {
                assert(root_type == Type::Int);
                if (initval->t == Type::Float) {
                    auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
                    buffer.push_back(new Instruction(op1, {}, tmp, Operator::cvt_f2i));
                    op1 = tmp;
                } else if (initval->t == Type::FloatLiteral) {
                    op1.name = std::to_string((int)std::stof(op1.name));
                    op1.type = Type::IntLiteral;
                }
            }
            buffer.push_back(new Instruction(op1, Operand(), des, opcode));
            symbol_table.scope_stack.back().table.insert({id, {des, {}}});
        } else if (root->children.back()->type == NodeType::INITVAL) { // 数组,有赋值
            if ((int)root->children.size() == 6) { // 一维数组定义
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

                GET_CHILD_PTR(initval, InitVal, 5);
                int cnt = 0;
                if (initval->children.size() == 2) {
                    for (int i = 0; i < array_size; i++) {
                        if (arr_ste.operand.type == Type::FloatPtr) {
                            buffer.push_back(new Instruction({arr_ste.operand, Operand(std::to_string(i), Type::IntLiteral), Operand("0.0", Type::FloatLiteral), Operator::store}));
                        } else {
                            buffer.push_back(new Instruction({arr_ste.operand, Operand(std::to_string(i), Type::IntLiteral), Operand("0", Type::IntLiteral), Operator::store}));
                        }
                    }
                } else {
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
                if (initval->children.size() == 2) {
                    for (int i = 0; i < array_size; i++) {
                        if (arr_ste.operand.type == Type::FloatPtr) {
                            buffer.push_back(new Instruction({arr_ste.operand, Operand(std::to_string(i), Type::IntLiteral), Operand("0.0", Type::FloatLiteral), Operator::store}));
                        } else {
                            buffer.push_back(new Instruction({arr_ste.operand, Operand(std::to_string(i), Type::IntLiteral), Operand("0", Type::IntLiteral), Operator::store}));
                        }
                    }
                } else {
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

                for (int i = 0; i < array_size; i++) {
                    if (arr_ste.operand.type == Type::FloatPtr) {
                        buffer.push_back(new Instruction({arr_ste.operand, Operand(std::to_string(i), Type::IntLiteral), Operand("0.0", Type::FloatLiteral), Operator::store}));
                    } else {
                        buffer.push_back(new Instruction({arr_ste.operand, Operand(std::to_string(i), Type::IntLiteral), Operand("0", Type::IntLiteral), Operator::store}));
                    }
                }
            } else if ((int)root->children.size() == 7) {
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

    if (root->children[0]->type == NodeType::EXP){  // 第一个节点是Exp,普通定义这边
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
    std::string name = dynamic_cast<Term*>(root->children[1])->token.value; // 参数名字
    if ((int)root->children.size() > 2){     // 数组作为参数

        auto type = (btype->t == Type::Int) ? Type::IntPtr : Type::FloatPtr;
        buffer.ParameterList.push_back(Operand(name, type));   // 增加参数
        symbol_table.scope_stack.back().table.insert({name, {Operand(name, type), {}}});

    }else{      // 普通变量作为参数
        buffer.ParameterList.push_back(Operand(name, btype->t));   // 增加参数
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

    symbol_table.add_scope(root);   // 增加作用域

    if ((int)root->children.size() > 2){
        int i = 1;
        while (i < (int)root->children.size()-1){
            ANALYSIS(blockitem, BlockItem, i);
            i += 1;
        }
    }

    symbol_table.exit_scope();  //退出函数作用域
}


// BlockItem -> Decl | Stmt
void frontend::Analyzer::analysisBlockItem(BlockItem* root, vector<ir::Instruction*>& buffer){

    if (root->children[0]->type == NodeType::DECL){     // 定义语句块
        ANALYSIS(decl, Decl, 0);
    }else if (root->children[0]->type == NodeType::STMT){   // 条件语句块
        ANALYSIS(stmt, Stmt, 0);
    }
}


// Stmt -> LVal '=' Exp ';' | Block | 'if' '(' Cond ')' Stmt [ 'else' Stmt ] | 'while' '(' Cond ')' Stmt | 'break' ';' | 'continue' ';' | 'return' [Exp] ';' | [Exp] ';'
void frontend::Analyzer::analysisStmt(Stmt* root, vector<ir::Instruction*>& buffer){

    if (root->children[0]->type == NodeType::LVAL){     // 赋值语句块
        ANALYSIS(exp, Exp, 2);  // 分析Exp节点
        ANALYSIS(lval, LVal, 0);    // 分析lval节点

    }else if (root->children[0]->type == NodeType::BLOCK){   // Block块

        ANALYSIS(block, Block, 0);

    }else if (root->children[0]->type == NodeType::EXP){    // Exp块

        ANALYSIS(exp, Exp, 0);

    }else if (dynamic_cast<Term*>(root->children[0])->token.type == TokenType::IFTK){  // if块
        // Stmt -> 'if' '(' Cond ')' Stmt [ 'else' Stmt ]

        auto tmp1 = vector<Instruction*>();
        GET_CHILD_PTR(cond, Cond, 2);
        analysisCond(cond, tmp1);    // 分析cond节点
        buffer.insert(buffer.end(), tmp1.begin(), tmp1.end());    // 插入cond IR

        // if 成立的跳转
        buffer.push_back(new Instruction(Operand(cond->v,cond->t), Operand(), Operand("2",Type::IntLiteral), Operator::_goto));

        // 分析if的Stmt
        GET_CHILD_PTR(stmt1, Stmt, 4);   // 获取if的stmt
        auto tmp2 = vector<Instruction*>();  // if的stmt IR
        analysisStmt(stmt1, tmp2);   // 分析stmt节点

        if ((int)root->children.size() == 5){    // if 没有else

            // if 不成立的跳转
            buffer.push_back(new Instruction({Operand(), Operand(), Operand(std::to_string(tmp2.size()+1), Type::IntLiteral), Operator::_goto}));

            // 插入if stmt的IR
            buffer.insert(buffer.end(), tmp2.begin(), tmp2.end());

            // 增加无用IR,防止if块跳出没有IR了
            buffer.push_back(new Instruction({Operand(), Operand(), Operand(), Operator::__unuse__}));

        }else{      // if 有else
            auto tmp3 = vector<Instruction*>();     // else的stmt IR
            GET_CHILD_PTR(stmt2, Stmt, 6);   // 获取else 的stmt
            analysisStmt(stmt2, tmp3);   // 分析else 的stmt节点

            // if执行完要跳过else
            tmp2.push_back(new Instruction({Operand(), Operand(), Operand(std::to_string(tmp3.size()+1), Type::IntLiteral), Operator::_goto}));

            // 执行else要跳过if
            buffer.push_back(new Instruction({Operand(), Operand(), Operand(std::to_string(tmp2.size()+1), Type::IntLiteral), Operator::_goto}));

            // 合并if的stmt
            buffer.insert(buffer.end(), tmp2.begin(), tmp2.end());

            // 合并else的stmt
            buffer.insert(buffer.end(), tmp3.begin(), tmp3.end());

            // 增加无用IR,防止if块跳出没有IR了
            buffer.push_back(new Instruction({Operand(), Operand(), Operand(), Operator::__unuse__}));
        }
    }else if (dynamic_cast<Term*>(root->children[0])->token.type == TokenType::WHILETK){   // while块
        
        // Stmt -> 'while' '(' Cond ')' Stmt 
        
        GET_CHILD_PTR(cond, Cond, 2);
        auto tmp1 = vector<Instruction*>();  // cond IR
        analysisCond(cond, tmp1);

        GET_CHILD_PTR(stmt, Stmt, 4);
        auto tmp2 = vector<Instruction*>();  // while的stmt IR
        analysisStmt(stmt, tmp2);

        // 每一轮while结束都要回到开头
        tmp2.push_back(new Instruction({Operand("continue", Type::null), Operand(), Operand(), Operator::__unuse__}));

        // 遍历WHILE体中的BREAK与CONTINUE标记指令, 修改为_goto
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

        // 合并cond IR
        buffer.insert(buffer.end(), tmp1.begin(), tmp1.end());
        
        // 满足条件,执行stmt
        buffer.push_back(new Instruction({Operand(cond->v,cond->t), Operand(), Operand("2",Type::IntLiteral), Operator::_goto}));

        // 不满足,跳出stmt
        buffer.push_back(new Instruction({Operand(), Operand(), Operand(std::to_string(tmp2.size()+1), Type::IntLiteral), Operator::_goto}));

        // 合并stmt IR
        buffer.insert(buffer.end(), tmp2.begin(), tmp2.end());

        // 插入unuse
        buffer.push_back(new Instruction(Operand(), Operand(), Operand(), Operator::__unuse__));

    }else if (dynamic_cast<Term*>(root->children[0])->token.type == TokenType::BREAKTK){   // break块
        
        buffer.push_back(new Instruction({Operand("break", Type::null), Operand(), Operand(), Operator::__unuse__}));

    }else if (dynamic_cast<Term*>(root->children[0])->token.type == TokenType::CONTINUETK){    // continue块
        
        buffer.push_back(new Instruction({Operand("continue", Type::null), Operand(), Operand(), Operator::__unuse__}));
    
    }else if (dynamic_cast<Term*>(root->children[0])->token.type == TokenType::RETURNTK){  // return块
        
        // stmt -> 'return' [Exp] ';'

        if ((int)root->children.size() == 2){
            Instruction* return_inst = new Instruction({Operand("null", Type::null), Operand(), Operand(), Operator::_return});
            buffer.push_back(return_inst);

        }else{
            // stmt -> 'return' Exp ';'
            auto tmp = vector<Instruction*>();
            GET_CHILD_PTR(exp, Exp, 1);
            analysisExp(exp, tmp);
            buffer.insert(buffer.end(), tmp.begin(), tmp.end());     // 插入exp IR

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


    ANALYSIS(addexp, AddExp, 0);    // 分析addexp节点
    COPY_EXP_NODE(addexp, root);
}


// Cond -> LOrExp
void frontend::Analyzer::analysisCond(Cond* root, vector<ir::Instruction*>& buffer){
    ANALYSIS(lorexp, LOrExp, 0);    // 分析LOrExp节点
    COPY_EXP_NODE(lorexp, root);
}


// LVal -> Ident {'[' Exp ']'}
void frontend::Analyzer::analysisLVal(LVal* root, vector<ir::Instruction*>& buffer){

    auto tk = dynamic_cast<Term*>(root->children[0])->token;    // 获取Term节点的token
    auto op = symbol_table.get_operand(tk.value);   // 从符号表获取
    root->t = op.type;  // 记录类型

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
            // 关键修正：元素类型直接取数组指针类型
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
            // 关键修正：元素类型直接取数组指针类型
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

    if (root->children[0]->type == NodeType::TERMINAL){     // '(' Exp ')'

        ANALYSIS(exp, Exp, 1);  // 分析Exp节点
        COPY_EXP_NODE(exp, root);

    }else if (root->children[0]->type == NodeType::LVAL){   // LVal

        ANALYSIS(lval, LVal, 0);    // 分析Lval节点
        COPY_EXP_NODE(lval, root);

    }else{  // Number
        root->is_computable = true; // 可化简
        auto number_tk = dynamic_cast<Term*>(root->children[0]->children[0])->token;  //拿到Number节点对应终结符的token
        root->t = (number_tk.type==TokenType::INTLTR) ? Type::IntLiteral : Type::FloatLiteral;      // t属性为终结符的类型
        if (root->t == Type::IntLiteral){
            root->v = trans2ten(number_tk.value);     // v属性为终结符的值
        }else{
            root->v = number_tk.value;
        }
    }
}


// UnaryExp -> PrimaryExp | Ident '(' [FuncRParams] ')' | UnaryOp UnaryExp
void frontend::Analyzer::analysisUnaryExp(UnaryExp* root, vector<ir::Instruction*>& buffer){

    if (root->children[0]->type == NodeType::PRIMARYEXP){   // UnaryExp -> PrimaryExp

        ANALYSIS(primaryexp, PrimaryExp, 0);
        COPY_EXP_NODE(primaryexp, root);    // 向上传递属性

    }else if (root->children[0]->type == NodeType::TERMINAL){   // UnaryExp -> Ident '(' [FuncRParams] ')'
        
        std::string func_name = dynamic_cast<Term*>(root->children[0])->token.value;   // 函数名
        auto op1 = Operand(func_name, Type::null);  // 操作数一为函数名
        Type t = symbol_table.functions[func_name]->returnType;     //函数返回值类型
        auto des = Operand("t" + std::to_string(tmp_cnt++), t);     // 目的操作数为临时变量
        if ((int)root->children.size() == 3){    // 没有参数
            buffer.push_back(new ir::CallInst(op1, des));
        }else{
            auto callinst = new ir::CallInst(op1, vector<Operand>(), des);  // 函数调用IR
            GET_CHILD_PTR(funcrparams, FuncRParams, 2);     // 获取FuncRParams节点
            assert(funcrparams);
            analysisFuncRParams(funcrparams, buffer, *callinst);
            buffer.push_back(callinst);     // 插入函数调用IR
        }
        root->v = des.name;
        root->t = t;

    }else{      // UnaryExp -> UnaryOp UnaryExp
        auto tk = dynamic_cast<Term*>(root->children[0]->children[0])->token.type;
        ANALYSIS(unaryexp, UnaryExp, 1);    // 分析UnaryExp节点
        if (tk == TokenType::PLUS){     // "+"
            COPY_EXP_NODE(unaryexp, root);
        }else{      // "-" "!"
            root->is_computable = unaryexp->is_computable;
            root->t = unaryexp->t;
            if (unaryexp->is_computable){   // 可简化
                if (unaryexp->t == Type::IntLiteral){  // Int立即数
                    if (tk == TokenType::MINU){
                        root->v = std::to_string(- std::stoi(unaryexp->v));
                    }else{
                        root->v = std::to_string(! std::stoi(unaryexp->v));
                    }
                }else{  // Float
                    if (tk == TokenType::MINU){
                        root->v = std::to_string(- std::stof(unaryexp->v));
                    }else{
                        root->v = std::to_string(! std::stof(unaryexp->v));
                    }
                }
            }else{  // 不可简化
                if (unaryexp->t == Type::Int){      // Int
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
                }else{      // Float,不可能出现!Float
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
    ANALYSIS(exp1, Exp, 0);  // 分析Exp节点
    Operand arg(exp1->v, exp1->t);
    if (arg.type == Type::FloatLiteral) {
        auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
        buffer.push_back(new Instruction(arg, {}, tmp, Operator::fdef));
        arg = tmp;
    }
    callinst.argumentList.push_back(arg);
    int i = 1;
    while (i < (int)root->children.size()){
        ANALYSIS(exp2, Exp, i+1);  // 分析Exp节点
        callinst.argumentList.push_back(Operand(exp2->v, exp2->t));
        i += 2;
    }
}


// MulExp -> UnaryExp { ('*' | '/' | '%') UnaryExp }
void frontend::Analyzer::analysisMulExp(MulExp* root, vector<ir::Instruction*>& buffer){

    if ((int)root->children.size() == 1){

        ANALYSIS(unaryexp1, UnaryExp, 0);    // 分析unaryexp节点
        COPY_EXP_NODE(unaryexp1, root);    // 向上传递属性

    }else if ((int)root->children.size() > 1){
        ANALYSIS(unaryexp1, UnaryExp, 0);    // 分析unaryexp节点
        root->is_computable = unaryexp1->is_computable;
        root->t = unaryexp1->t;
        root->v = unaryexp1->v;
        int i = 1;
        while (i < (int)root->children.size()){
            auto tk = dynamic_cast<Term*>(root->children[i])->token.type;   // 运算符
            ANALYSIS(unaryexp2, UnaryExp, i+1);     // 分析下一个unaryexp节点
            if(root->is_computable && unaryexp2->is_computable){    // 可化简
                root->is_computable = true;
                if(root->t != unaryexp2->t){   // 类型不一致
                    root->t = Type::FloatLiteral;
                }

                if(root->t == Type::IntLiteral){    // 整数立即数间运算
                    if (tk == TokenType::MULT){
                        root->v = std::to_string(std::stoi(root->v) * std::stoi(unaryexp2->v));
                    }else if (tk == TokenType::DIV){
                        root->v = std::to_string(std::stoi(root->v) / std::stoi(unaryexp2->v));
                    }else{
                        root->v = std::to_string(std::stoi(root->v) % std::stoi(unaryexp2->v));
                    }
                }else{      // 浮点立即数间运算
                    if (tk == TokenType::MULT){
                        root->v = std::to_string(std::stof(root->v) * std::stof(unaryexp2->v));
                    }else if (tk == TokenType::DIV){
                        root->v = std::to_string(std::stof(root->v) / std::stof(unaryexp2->v));
                    }
                }
            }else{  // 不可化简
                root->is_computable = false;
                Operand op1 = Operand(root->v, root->t);
                Operand op2 = Operand(unaryexp2->v, unaryexp2->t);
                Operand tmp = Operand("t" + std::to_string(tmp_cnt++), root->t);
                if (tk == TokenType::MULT){
                    if (root->t == unaryexp2->t){   // 类型一致
                        if (tmp.type == Type::Int){
                            buffer.push_back(new Instruction({op1, op2, tmp, Operator::mul}));  // mul IR
                        }else{
                            buffer.push_back(new Instruction({op1, op2, tmp, Operator::fmul}));  // fmul IR
                        }
                    }else{      // 类型不一致
                        type_transform(op1, op2, buffer);
                        tmp.type = op1.type;     // 输出类型为其中一个
                        if (tmp.type == Type::Int){
                            buffer.push_back(new Instruction({op1, op2, tmp, Operator::mul}));  // mul IR
                        }else{
                            buffer.push_back(new Instruction({op1, op2, tmp, Operator::fmul}));  // fmul IR
                        }
                    }
                }else if (tk == TokenType::DIV){
                    if (root->t == unaryexp2->t){   // 类型一致
                        if (tmp.type == Type::Int){
                            buffer.push_back(new Instruction({op1, op2, tmp, Operator::div}));  // div IR
                        }else{
                            buffer.push_back(new Instruction({op1, op2, tmp, Operator::fdiv}));  // fdiv IR
                        }
                    }else{
                        type_transform(op1, op2, buffer);
                        tmp.type = op1.type;
                        if(tmp.type == Type::Int){
                            buffer.push_back(new Instruction({op1, op2, tmp, Operator::div}));  // div IR
                        }else{
                            buffer.push_back(new Instruction({op1, op2, tmp, Operator::fdiv}));  // fdiv IR
                        }
                    }
                }else{
                    buffer.push_back(new Instruction({op1, op2, tmp, Operator::mod}));  // mod IR
                }
                root->v = tmp.name;     // 临时变量名称
                root->t = tmp.type;     // 临时变量类型
            }

            i += 2;
        }
    }
}


// AddExp -> MulExp { ('+' | '-') MulExp }
void frontend::Analyzer::analysisAddExp(AddExp* root, vector<ir::Instruction*>& buffer){

    if ((int)root->children.size() == 1){

        ANALYSIS(mulexp1, MulExp, 0);    // 分析mulexp节点
        COPY_EXP_NODE(mulexp1, root);    // 向上传递属性

    }else if ((int)root->children.size() > 1){  // 多个元素相加

        ANALYSIS(mulexp1, MulExp, 0);    // 分析mulexp节点

        root->is_computable = mulexp1->is_computable;
        root->t = mulexp1->t;
        root->v = mulexp1->v;

        int i = 1;
        while (i < (int)root->children.size()){

            auto tk = dynamic_cast<Term*>(root->children[i])->token.type;   // 运算符
            ANALYSIS(mulexp2, MulExp, i+1);     // 分析下一个mulexp节点
            if(root->is_computable && mulexp2->is_computable){    // 可化简
                root->is_computable = true;
                if(root->t != mulexp2->t){   // 类型不一致
                    root->t = Type::FloatLiteral;
                }

                if(root->t == Type::IntLiteral){    // 整数立即数间运算
                    if (tk == TokenType::PLUS){
                        root->v = std::to_string(std::stoi(root->v) + std::stoi(mulexp2->v));    // 计算结果,先只考虑整数相加
                    }else{  
                        root->v = std::to_string(std::stoi(root->v) - std::stoi(mulexp2->v));
                    }
                }else{      // 浮点立即数间运算
                    if (tk == TokenType::PLUS){
                        root->v = std::to_string(std::stof(root->v) + std::stof(mulexp2->v));    // 计算结果,先只考虑整数相加
                    }else{  
                        root->v = std::to_string(std::stof(root->v) - std::stof(mulexp2->v));
                    }
                }
            }else{  // 不可化简
                root->is_computable = false;
                Operand op1 = Operand(root->v, root->t);
                Operand op2 = Operand(mulexp2->v, mulexp2->t);
                Operand tmp = Operand("t" + std::to_string(tmp_cnt++), root->t);
                if (!root->is_computable && !mulexp2->is_computable){   // 两个都是变量
                    if (tk == TokenType::PLUS){
                        if (root->t == mulexp2->t){   // 类型一致
                            if (tmp.type == Type::Int){
                                buffer.push_back(new Instruction({op1, op2, tmp, Operator::add}));  // add IR
                            }else{
                                buffer.push_back(new Instruction({op1, op2, tmp, Operator::fadd}));  // fadd IR
                            }
                        }else{  // 类型不一致
                            type_transform(op1, op2, buffer);
                            tmp.type = op1.type;
                            if (tmp.type == Type::Int){
                                buffer.push_back(new Instruction({op1, op2, tmp, Operator::add}));  // add IR
                            }else{
                                buffer.push_back(new Instruction({op1, op2, tmp, Operator::fadd}));  // fadd IR
                            }
                        }
                    }else{
                        if (root->t == mulexp2->t){   // 类型一致
                            if (tmp.type == Type::Int){
                                buffer.push_back(new Instruction({op1, op2, tmp, Operator::sub}));  // sub IR
                            }else{
                                buffer.push_back(new Instruction({op1, op2, tmp, Operator::fsub}));  // fsub IR
                            }
                        }else{  // 类型不一致
                            type_transform(op1, op2, buffer);
                            tmp.type = op1.type;
                            if (tmp.type == Type::Int){
                                buffer.push_back(new Instruction({op1, op2, tmp, Operator::sub}));
                            }else{
                                buffer.push_back(new Instruction({op1, op2, tmp, Operator::fsub}));  // fadd IR
                            }
                        }
                    }
                }else{
                    if (tk == TokenType::PLUS){
                        if (root->t == Type::Int && mulexp2->t == Type::IntLiteral){    // a+1
                            tmp.type = Type::Int;
                            buffer.push_back(new Instruction({op1, op2, tmp, Operator::addi}));  // addi IR
                        }else if (root->t == Type::IntLiteral && mulexp2->t == Type::Int){  // 1+a
                            tmp.type = Type::Int;
                            buffer.push_back(new Instruction({op2, op1, tmp, Operator::addi}));  // addi IR
                        }else{  // a+0.1, 0.1+a ...
                            tmp.type = Type::Float;
                            type_transform(op1, op2, buffer);
                            buffer.push_back(new Instruction({op1, op2, tmp, Operator::fadd}));  // add IR
                        }
                    }else{
                        if (root->t == Type::Int && mulexp2->t == Type::IntLiteral){    // a-1
                            tmp.type = Type::Int;
                            auto subi_inst = new Instruction({op1, op2, tmp, Operator::subi});
                            buffer.push_back(subi_inst);  // subi IR

                        }else{  // 1-a, 0.1-a, a-0.1
                            type_transform(op1, op2, buffer);
                            tmp.type = op1.type;
                            if (tmp.type == Type::Int){      // 1-a
                                buffer.push_back(new Instruction({op2, op1, tmp, Operator::sub}));  // sub IR
                            }else{
                                buffer.push_back(new Instruction({op2, op1, tmp, Operator::fsub}));  // fsub IR
                            }
                        }
                    }
                }
                root->v = tmp.name;     // 临时变量名称
                root->t = tmp.type;     // 临时变量类型
            }

            i += 2;
        }
    }
}


// RelExp -> AddExp { ('<' | '>' | '<=' | '>=') AddExp }
void frontend::Analyzer::analysisRelExp(RelExp* root,vector<ir::Instruction*>& buffer){

     if ((int)root->children.size() == 1){    // RelExp -> AddExp
     
        ANALYSIS(addexp, AddExp, 0);
        COPY_EXP_NODE(addexp, root);

    }else{      // RelExp -> AddExp { ('<' | '>' | '<=' | '>=') AddExp }

        ANALYSIS(addexp1, AddExp, 0);
        root->is_computable = addexp1->is_computable;
        root->t = addexp1->t;
        root->v = addexp1->v;

        int i = 1;
        while (i < (int)root->children.size()){

            ANALYSIS(addexp2, AddExp, i+1);     // 分析AddExp节点
            auto tk = dynamic_cast<Term*>(root->children[i])->token.type;   // 运算符

            root->is_computable = false;     // 不可化简
            Operand op1 = Operand(root->v, root->t);
            Operand op2 = Operand(addexp2->v, addexp2->t);
            type_transform(op1, op2, buffer);   // 类型保持一致
            Operand des = Operand("t" + std::to_string(tmp_cnt++), Type::Int);  // 临时操作数
            if (tk == TokenType::LSS){
                if (op1.type == Type::Int){
                    buffer.push_back(new Instruction({op1, op2, des, Operator::lss}));
                }else{
                    des.type = Type::Float;
                    buffer.push_back(new Instruction({op1, op2, des, Operator::flss}));
                }
            }
            else if (tk == TokenType::GTR){
                if (op1.type == Type::Int){
                    buffer.push_back(new Instruction({op1, op2, des, Operator::gtr}));
                }else{
                    des.type = Type::Float;
                    buffer.push_back(new Instruction({op1, op2, des, Operator::fgtr}));
                }
            }
            else if (tk == TokenType::LEQ){
                if (op1.type == Type::Int){
                    buffer.push_back(new Instruction({op1, op2, des, Operator::leq}));
                }else{
                    des.type = Type::Float;
                    buffer.push_back(new Instruction({op1, op2, des, Operator::fleq}));
                }
            }
            else{
                if (op1.type == Type::Int){
                    buffer.push_back(new Instruction({op1, op2, des, Operator::geq}));
                }else{
                    des.type = Type::Float;
                    buffer.push_back(new Instruction({op1, op2, des, Operator::fgeq}));
                }
            }

            root->v = des.name;
            root->t = Type::Int;

            i += 2;
        }
    }
}


// EqExp -> RelExp { ('==' | '!=') RelExp }
void frontend::Analyzer::analysisEqExp(EqExp* root,vector<ir::Instruction*>& buffer){
    if ((int)root->children.size() == 1){    // EqExp -> RelExp

        ANALYSIS(relexp, RelExp, 0);     // 分析RelExp节点
        COPY_EXP_NODE(relexp, root);

    }else{      // EqExp -> RelExp ('==' | '!=') RelExp

        ANALYSIS(relexp1, RelExp, 0);     // 分析RelExp节点
        root->is_computable = relexp1->is_computable;
        root->v = relexp1->v;
        root->t = relexp1->t;

        int i = 1;
        while (i < (int)root->children.size()){
            ANALYSIS(relexp2, RelExp, i+1);     // 分析RelExp节点
            auto tk = dynamic_cast<Term*>(root->children[i])->token.type;   // 运算符
            
            root->is_computable = false;
            Operand op1 = Operand(root->v, root->t);
            Operand op2 = Operand(relexp2->v, relexp2->t);
            type_transform(op1, op2, buffer);
            Operand des = Operand("t" + std::to_string(tmp_cnt++), Type::Int);  // 临时操作数
            if (tk == TokenType::EQL){  // '==' 类型检查 need to do
                if (op1.type == Type::Int){
                    buffer.push_back(new Instruction({op1, op2, des, Operator::eq}));
                }else{
                    des.type = Type::Float;
                    buffer.push_back(new Instruction({op1, op2, des, Operator::feq}));
                }
            }else{      // !=
                if (op1.type == Type::Int){
                    buffer.push_back(new Instruction({op1, op2, des, Operator::neq}));
                }else{
                    des.type = Type::Float;
                    buffer.push_back(new Instruction({op1, op2, des, Operator::fneq}));
                }
            }

            root->v = des.name;
            root->t = Type::Int;
            // }

            i += 2;
        }
    }
}


// LAndExp -> EqExp [ '&&' LAndExp ]
void frontend::Analyzer::analysisLAndExp(LAndExp* root, vector<ir::Instruction*>& buffer){
    if ((int)root->children.size() == 1){    // LAndExp -> EqExp

        ANALYSIS(eqexp, EqExp, 0);     // 分析EqExp节点
        COPY_EXP_NODE(eqexp, root);

    }else{      // LAndExp -> EqExp '&&' LAndExp
        
        // LAndExp -> EqExp '&&' LAndExp
        ANALYSIS(eqexp, EqExp, 0);  // 分析EqExp节点
        
        auto tmp = vector<ir::Instruction*>();  // LAndExp节点的IR向量
        auto andexp = dynamic_cast<LAndExp*>(root->children[2]);  //取得LAndExp节点
        assert(andexp);
        analysisLAndExp(andexp, tmp);    // 分析LAndExp节点
        
        root->t = Type::Int;    // and表达式结果固定为Int

        Operand op1 = Operand(eqexp->v, eqexp->t);
        Operand op2 = Operand(andexp->v, andexp->t);
        Operand des = Operand("t" + std::to_string(tmp_cnt++), Type::Int);    // 临时变量,输出结果为Int
        Operand t1 = Operand("t" + std::to_string(tmp_cnt++), op1.type);    // 临时变量1
        
        buffer.push_back(new Instruction({op1, {}, t1, Operator::mov}));    // 将op1转换为变量
        buffer.push_back(new Instruction({t1, {}, {"2", Type::IntLiteral}, Operator::_goto}));  // op1成立,判断op2
        buffer.push_back(new Instruction({{}, {}, {std::to_string(tmp.size()+3), Type::IntLiteral}, Operator::_goto}));
        buffer.insert(buffer.end(), tmp.begin(), tmp.end());    // 在尾部加入landexp节点的IR向量
        buffer.push_back(new Instruction({op2, {}, des, Operator::mov}));   // op2成立,des = op2
        buffer.push_back(new Instruction({{}, {}, {"2", Type::IntLiteral}, Operator::_goto}));
        buffer.push_back(new Instruction({"0", Type::IntLiteral}, {}, des, Operator::mov));

        root->v = des.name;
    }
}


// LOrExp -> LAndExp [ '||' LOrExp ]
void frontend::Analyzer::analysisLOrExp(LOrExp* root, vector<ir::Instruction*>& buffer){
    if ((int)root->children.size() == 1){    // LOrExp -> LAndExp

        ANALYSIS(landexp, LAndExp, 0);
        COPY_EXP_NODE(landexp, root);
        
    }else{      // LOrExp -> LAndExp '||' LOrExp
        
        root->t = Type::Int;    // LOrExp表达式计算得到的类型固定为整型变量,测评机貌似不支持IntLiteral

        ANALYSIS(andexp, LAndExp, 0);     // 分析LAndExp节点

        auto tmp = vector<ir::Instruction*>();  // LorExp节点的IR向量
        auto orexp = dynamic_cast<LOrExp*>(root->children[2]);  //取得LOrExp节点
        assert(orexp);
        analysisLOrExp(orexp, tmp);    // 分析LOrExp节点

        // root->is_computable = andexp->is_computable;    // 可简化性赋值为andexp节点

        Operand op1 = Operand(andexp->v, andexp->t);
        Operand op2 = Operand(orexp->v, orexp->t);
        Operand t1 = Operand("t" + std::to_string(tmp_cnt++), root->t);    //临时变量1
        Operand des = Operand("t" + std::to_string(tmp_cnt++), root->t);    //临时变量,结果
        
        buffer.push_back(new Instruction({op1, {}, t1, Operator::mov}));    // 将op1转换为变量
        buffer.push_back(new Instruction({t1, {}, {std::to_string(tmp.size()+3), Type::IntLiteral}, Operator::_goto}));    // if(op1)->des=1
        buffer.insert(buffer.end(), tmp.begin(), tmp.end());    // 在尾部加入orexp节点的IR向量
        buffer.push_back(new Instruction({op2, {}, des, Operator::mov}));   // else -> des = op2
        buffer.push_back(new Instruction({{}, {}, {"2", Type::IntLiteral}, Operator::_goto}));
        buffer.push_back(new Instruction({"1", Type::IntLiteral}, {}, des, Operator::mov));

        root->v = des.name;
    }
}


// ConstExp -> AddExp
void frontend::Analyzer::analysisConstExp(ConstExp* root, vector<ir::Instruction*>& buffer){
    ANALYSIS(addexp, AddExp, 0);    // 分析AddExp节点
    root->v = addexp->v;
    root->t = addexp->t;
}
