#include"front/semantic.h"
#include<iostream>
#include<cassert>
using ir::Instruction;
using ir::Function;
using ir::Operand;
using ir::Operator;

#define TODO assert(0 && "TODO");

// ��ȡ���ڵ��ָ���ӽڵ�
#define GET_CHILD_PTR(node, type, index) auto node = dynamic_cast<type*>(root->children[index]); assert(node); 
// ��ȡ���ڵ��ָ���ӽڵ�, ���ҵ��÷�������
#define ANALYSIS(node, type, index) auto node = dynamic_cast<type*>(root->children[index]); assert(node); analysis##type(node, buffer);
// ��������
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


//�������ַ���ת��Ϊʮ���ƣ�����ʮ�����ơ��˽��ơ������ƣ�����ò��ִ�л����Ѿ�����
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


// ����ת��
void frontend::Analyzer::type_transform(Operand& a, Operand& b, vector<Instruction*>& buffer){
    if (a.type == Type::Int){
        if (b.type == Type::Float){     // Int-Float
            auto tmp_op = Operand("t" + std::to_string(tmp_cnt++), Type::Float);    // aתFloat
            buffer.push_back(new Instruction(a, {}, tmp_op, Operator::cvt_i2f));
            a = tmp_op;   
        }else if (b.type == Type::FloatLiteral){    // Int-FloatLiteral
            auto tmp_op1 = Operand("t" + std::to_string(tmp_cnt++), Type::Float);    // aתFloat
            buffer.push_back(new Instruction(a, {}, tmp_op1, Operator::cvt_i2f));

            auto tmp_op2 = Operand("t" + std::to_string(tmp_cnt++), Type::Float);    // bתFloat
            buffer.push_back(new Instruction(b, {}, tmp_op2, Operator::fdef));
            
            a = tmp_op1;
            b = tmp_op2;
        }else if (b.type == Type::IntLiteral){      // Int-IntLiteral
            auto tmp_op = Operand("t" + std::to_string(tmp_cnt++), Type::Int);    // bתInt
            buffer.push_back(new Instruction(b, {}, tmp_op, Operator::def));

            b = tmp_op;
        }
    }else if (a.type == Type::IntLiteral){      // IntLiteral-Float
        if (b.type == Type::Float){
            auto tmp_op = Operand("t" + std::to_string(tmp_cnt++), Type::Float);    // aתFloat
            buffer.push_back(new Instruction(Operand(a.name, Type::FloatLiteral), {}, tmp_op, Operator::fdef));
            
            a = tmp_op;

        }else if (b.type == Type::Int){     // IntLiteral-Int

            auto tmp_op = Operand("t" + std::to_string(tmp_cnt++), Type::Int);    // aתInt
            buffer.push_back(new Instruction(a, {}, tmp_op, Operator::def));

            a = tmp_op;
        }else if (b.type == Type::IntLiteral){      // IntLiteral-IntLiteral
            
            auto tmp_op1 = Operand("t" + std::to_string(tmp_cnt++), Type::Int);    // aתInt
            buffer.push_back(new Instruction(a, {}, tmp_op1, Operator::def));

            auto tmp_op2 = Operand("t" + std::to_string(tmp_cnt++), Type::Int);    // bתInt
            buffer.push_back(new Instruction(b, {}, tmp_op2, Operator::def));

            a = tmp_op1;
            b = tmp_op2;
        }
    }else if(a.type == Type::Float){    // Float-Int
        if (b.type == Type::Int){
            auto tmp_op = Operand("t" + std::to_string(tmp_cnt++), Type::Float);    // bתFloat
            buffer.push_back(new Instruction(b, {}, tmp_op, Operator::cvt_i2f));

            b = tmp_op;
        }else if (b.type == Type::IntLiteral){  // Float-IntLiteral
            auto tmp_op = Operand("t" + std::to_string(tmp_cnt++), Type::Float);    // bתFloat
            buffer.push_back(new Instruction(Operand(b.name, Type::FloatLiteral), {}, tmp_op, Operator::fdef));

            b = tmp_op;
        }else if (b.type == Type::FloatLiteral){  // Float-FloatLiteral
            auto tmp_op = Operand("t" + std::to_string(tmp_cnt++), Type::Int);    // bתFloat
            buffer.push_back(new Instruction(b, {}, tmp_op, Operator::fdef));

            b = tmp_op;
        }
    }else if (a.type == Type::FloatLiteral){
        if (b.type == Type::Int){
            auto tmp_op1 = Operand("t" + std::to_string(tmp_cnt++), Type::Float);    // aתFloat
            buffer.push_back(new Instruction(Operand(a.name, Type::FloatLiteral), {}, tmp_op1, Operator::fdef));

            auto tmp_op2 = Operand("t" + std::to_string(tmp_cnt++), Type::Float);    // bתFloat
            buffer.push_back(new Instruction(b, {}, tmp_op2, Operator::cvt_i2f));

            a = tmp_op1;
            b = tmp_op2;
        }else if (b.type == Type::Float){
            auto tmp_op = Operand("t" + std::to_string(tmp_cnt++), Type::Float);    // aתFloat
            buffer.push_back(new Instruction(Operand(a.name, Type::FloatLiteral), {}, tmp_op, Operator::fdef));
            
            a = tmp_op;
        }
    }
}


// ������������ʱ, ����ű������ ScopeInfo, �൱��ѹջ, ��������������������û���ô�
void frontend::SymbolTable::add_scope(Block* node) {

    ScopeInfo scope_info;   // ��ǰ������
    scope_info.cnt = ++block_cnt;    // ��ǰ��������
    scope_stack.push_back(scope_info);  // ѹ��������

}


// �˳�������ʱ��ջ
void frontend::SymbolTable::exit_scope() {
    scope_stack.pop_back();
}


// ����һ��������, �������ڵ�ǰ��������������������� (�൱�ڼӺ�׺)
string frontend::SymbolTable::get_scoped_name(string id) const {
    int cnt = scope_stack.back().cnt;  //��ǰ��������
    return id + "_" + std::to_string(cnt);
}


// ����һ��������, �ڷ��ű���Ѱ�������ͬ������, ���ض�Ӧ�� Operand(ע�⣬�� Operand �� name �����������)
Operand frontend::SymbolTable::get_operand(string id) const {
    map_str_ste temp;
    for (int i=scope_stack.size()-1; i>=0; i--){      // ������ 
        temp = scope_stack[i].table;     // ��ǰ������ķ��ű�
        if(temp.find(id) != temp.end()){     // �ҵ���
            return temp[id].operand;
        }
    }
    return Operand();
}


// ����һ��������, �ڷ��ű���Ѱ�������ͬ������, ���� STE
frontend::STE frontend::SymbolTable::get_ste(string id) const {
    map_str_ste temp;
    for (int i=scope_stack.size()-1; i>=0; i--){      // ������ 
        temp= scope_stack[i].table;     // ��ǰ������ķ��ű�
        if(temp.find(id) != temp.end()){     // �ҵ���
            return temp[id];
        }
    }    
    return frontend::STE();
}


// ��ʼ�����ű�
frontend::Analyzer::Analyzer(): tmp_cnt(0), symbol_table() {
    symbol_table.scope_stack.push_back({0, "global", map_str_ste()});    // ���ű���ȫ��������
}


// ��ʼ��ȡir����
ir::Program frontend::Analyzer::get_ir_program(CompUnit* root) {
    ir::Program buffer = ir::Program();    // ��ʼ��program
    Function* global_func = new Function("global", Type::null);

    symbol_table.functions.insert({"global", global_func});  // ���ű����ȫ�ֺ���
    buffer.addFunction(*global_func);   // program����ȫ�ֺ���

    // ��ӿ⺯��
    auto lib_funcs = *get_lib_funcs();
    for (auto it = lib_funcs.begin(); it != lib_funcs.end(); it++)
        symbol_table.functions[it->first] = it->second;

    analysisCompUnit(root, buffer);

    // ��ȫ�ֺ�������ȫ��return
    buffer.functions[0].addInst(new ir::Instruction({Operand("null", Type::null), Operand(), Operand(), Operator::_return}));
    
    std::cout<<buffer.draw();     //��ӡprogram
    return buffer;
}


// CompUnit -> (Decl | FuncDef) [CompUnit]
void frontend::Analyzer::analysisCompUnit(CompUnit* root, ir::Program& buffer){

    if (root->children[0]->type == NodeType::DECL){     // ������������
        GET_CHILD_PTR(decl, Decl, 0);   // ȡ��Decl�ڵ�
        assert(decl);
        analysisDecl(decl, buffer.functions.back().InstVec);    // ����Decl�ڵ�
        
    }else if (root->children[0]->type == NodeType::FUNCDEF){    // ��������
        
        if (buffer.functions.size() == 1){     // �������ֻ��global,��ʱ���º�����,��Ҫɨ��global������IR����,��ȫ�ֱ���

            auto global_ir = buffer.functions[0].InstVec;
            for (int i=0; i<(int)global_ir.size(); i++){   // ɨ��global�����Ķ���IR
                buffer.globalVal.push_back(ir::GlobalVal(global_ir[i]->des));  // ����ȫ�ֱ���
            }
        }

        GET_CHILD_PTR(funcdef, FuncDef, 0);     // ȡ��FuncDef�ڵ�
        assert(funcdef);
        auto tmp = ir::Function();  // ����FuncDef��ir::function
        analysisFuncDef(funcdef, tmp);
        buffer.addFunction(tmp);    // ir::program���Ӻ���
    }

    if ((int)(int)root->children.size() == 2){
        ANALYSIS(compunit, CompUnit, 1);
    }
}


// FuncDef -> FuncType Ident '(' [FuncFParams] ')' Block
void frontend::Analyzer::analysisFuncDef(FuncDef* root, ir::Function& function){

    auto tk = dynamic_cast<Term*>(root->children[0]->children[0])->token.type;  //��������ֵ����
    root->t = tk == TokenType::VOIDTK ? Type::null : tk == TokenType::INTTK ? Type::Int :Type::Float;
    root->n = dynamic_cast<Term*>(root->children[1])->token.value;
    function.name = root->n;       //������
    function.returnType = root->t; //����ֵ����

    int cnt = ++symbol_table.block_cnt;
    symbol_table.scope_stack.push_back({cnt, "fp", map_str_ste()});   //�������β�����������
    symbol_table.functions.insert({root->n, &function});            //���Ӻ���
    curr_function = &function;  // ��ǰ����ָ��

    if (function.name == "main"){   // ��ǰΪmain����
        auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::null);
        auto global_callinst = new ir::CallInst(Operand("global", Type::null), vector<Operand>(), tmp);  // ��������IR
        curr_function->addInst(global_callinst);
    }

    auto paras = dynamic_cast<FuncFParams*>(root->children[3]);     //�������ӽڵ�
    if (paras){     // ������������б����
        analysisFuncFParams(paras, function);
        analysisBlock(dynamic_cast<Block*>(root->children[5]), function.InstVec);
    }else{
        analysisBlock(dynamic_cast<Block*>(root->children[4]), function.InstVec);
    }

    if (function.returnType == Type::null){     // ����û�з���ֵ������return null����ֹ���ز���
        auto return_inst = new Instruction({Operand("null", Type::null), {}, {}, Operator::_return});
        curr_function->addInst(return_inst);
    }

    symbol_table.exit_scope();  //�˳������β�������
}


// Decl -> ConstDecl | VarDecl
void frontend::Analyzer::analysisDecl(Decl* root, vector<ir::Instruction*>& buffer){

    if (root->children[0]->type == NodeType::CONSTDECL){    // ��������
        ANALYSIS(constdecl, ConstDecl, 0);
    }else if (root->children[0]->type == NodeType::VARDECL){    // ��������
        ANALYSIS(vardecl, VarDecl, 0);
    }
}


// ConstDecl -> 'const' BType ConstDef { ',' ConstDef } ';'
void frontend::Analyzer::analysisConstDecl(ConstDecl* root, vector<ir::Instruction*>& buffer){
    ANALYSIS(btype, BType, 1);
    root->t = btype->t;   // �ڵ�����ΪBType�ڵ�����
    ANALYSIS(constdef1, ConstDef, 2);    //����ConstDef�ڵ�
    int i = 3;
    while (dynamic_cast<Term*>(root->children[i])->token.type == TokenType::COMMA){
        ANALYSIS(constdef2, ConstDef, i+1);  // ����ConstDef�ڵ�
        i += 2;
    }
}


// BType -> 'int' | 'float'
void frontend::Analyzer::analysisBType(BType* root, vector<ir::Instruction*>& buffer){
    auto tk = dynamic_cast<Term*>(root->children[0])->token.type;  // ��ȡBType�ڵ������
    root->t = tk==TokenType::INTTK ? Type::Int : Type::Float;   // �ڵ�����ΪInt����Float
}


// ConstDef -> Ident { '[' ConstExp ']' } '=' ConstInitVal
void frontend::Analyzer::analysisConstDef(ConstDef* root, vector<ir::Instruction*>& buffer){
    auto root_type = dynamic_cast<ConstDecl*>(root->parent)->t;   // ���ڵ�ConstDecl������
    GET_CHILD_PTR(identifier, Term, 0);
    string id = identifier->token.value;    // ����ԭ��"a"
    string new_name = symbol_table.get_scoped_name(id);     // ���ű��������"a_g"
    root->arr_name = new_name;  // ���������

    GET_CHILD_PTR(term, Term, 1);   // ��ȡ�ڶ����ڵ�
    if (term->token.type == TokenType::ASSIGN){   //�ڶ����ڵ���=,��ͨ�ı�������
        ANALYSIS(constinitval, ConstInitVal, 2);    // ����ConstInitVal�ڵ�
        Operand des = Operand(new_name, root_type);     // Ŀ�������
        auto opcode = (root_type == Type::Float || root_type == Type::FloatLiteral) ? Operator::fdef : Operator::def;
        Operand op1 = Operand(constinitval->v, constinitval->t);    // ��һ������
        if (root_type == Type::Float){  // ���㳣������
            if (constinitval->t == Type::Int){  // ����ת��:Int->Float
                auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
                buffer.push_back(new Instruction(op1, {}, tmp, Operator::cvt_i2f));
                op1 = tmp;  // ���µ�һ������
            }else if (constinitval->t == Type::IntLiteral){     // ����ת��:IntLiteral->FloatLiteral
                op1.type = Type::FloatLiteral;
            } else if (constinitval->t==Type::FloatLiteral){
                auto tmp=Operand("t"+std::to_string(tmp_cnt++),Type::Float);
                buffer.push_back(new Instruction(op1,{},tmp,Operator::fdef));
                op1 = tmp;
            }
        }else{  // ���ͳ�������
            assert(root_type == Type::Int);
            if (constinitval->t == Type::Float){    // ����ת��:Float->Int
                auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
                buffer.push_back(new Instruction(op1, {}, tmp, Operator::cvt_f2i));
                op1 = tmp;
            }else if(constinitval->t == Type::FloatLiteral){    // ����ת��:FloatLiteral->IntLiteral
                op1.name = std::to_string((int)std::stof(op1.name));  // string->float->int->string
                op1.type = Type::IntLiteral;
            }
        }
        buffer.push_back(new Instruction(op1, Operand(), des, opcode));     // ��������IR
        symbol_table.scope_stack.back().table.insert({id, {op1, {}}});      // ��ǰ��������ű�������,��Ϊ��const����,���Դ���op1

    }else if ((int)root->children.size() == 6){   //һά���鶨��
        ANALYSIS(constexp, ConstExp, 2);    // ����ConstExp�ڵ�
        int array_size = std::stoi(constexp->v);    // ���鳤��
        STE arr_ste;    // ��ʱSTE
        arr_ste.dimension.push_back(array_size);  
        ir::Type curr_type = root_type;
        if (curr_type == ir::Type::Int){
            curr_type = ir::Type::IntPtr;
        }else if (curr_type == ir::Type::Float){
            curr_type = ir::Type::FloatPtr;
        }
        arr_ste.operand = ir::Operand(new_name, curr_type);
        symbol_table.scope_stack.back().table[id] = arr_ste;    // ������ű�
        buffer.push_back(new Instruction({Operand(std::to_string(array_size),ir::Type::IntLiteral), {}, Operand(new_name, curr_type), Operator::alloc}));

        // һά����ĳ�ʼ��
        GET_CHILD_PTR(constinitval, ConstInitVal, 5);
        if (constinitval->children.size() == 2){    // ֻ��{}ȥ��ʼ������
            for (int i = 0; i<array_size; i++){
                buffer.push_back(new Instruction({Operand(new_name, Type::IntPtr), Operand(std::to_string(i), Type::IntLiteral), Operand("0", Type::IntLiteral), Operator::store}));
            }
        }else{
            int cnt = 0;    // �����±�
            for (int i = 1; i< (int)constinitval->children.size()-1; i+=2, cnt++){     // ����'{' [ ConstInitVal { ',' ConstInitVal } ] '}'
                ConstInitVal* child = dynamic_cast<ConstInitVal*>(constinitval->children[i]);
                ConstExp* constexp = dynamic_cast<ConstExp*>(child->children[0]);
                analysisConstExp(constexp, buffer); // ����ConstExp�ڵ�
                buffer.push_back(new Instruction({Operand(new_name, Type::IntPtr), Operand(std::to_string(cnt), Type::IntLiteral), Operand(constexp->v, Type::IntLiteral), Operator::store}));
            }
        }
    // ConstDef -> Ident '[' ConstExp ']' '[' ConstExp ']' '=' ConstInitVal
    }else if ((int)root->children.size() == 9){  // ��ά���鶨��
        ANALYSIS(constexp1, ConstExp, 2);    // ����ConstExp�ڵ�
        ANALYSIS(constexp2, ConstExp, 5);    // ����ConstExp�ڵ�
        int array_size = std::stoi(constexp1->v) * std::stoi(constexp2->v);    // ���鳤��
        STE arr_ste;    // ��ʱSTE
        arr_ste.dimension.push_back(std::stoi(constexp1->v));   // ��һά
        arr_ste.dimension.push_back(std::stoi(constexp2->v));   // �ڶ�ά
        ir::Type curr_type = root_type;
        if (curr_type == ir::Type::Int){
            curr_type = ir::Type::IntPtr;
        }else if (curr_type == ir::Type::Float){
            curr_type = ir::Type::FloatPtr;
        }
        arr_ste.operand = ir::Operand(new_name, curr_type);
        symbol_table.scope_stack.back().table[id] = arr_ste;    // ������ű�
        buffer.push_back(new Instruction({Operand(std::to_string(array_size),ir::Type::IntLiteral), {}, Operand(new_name, curr_type), Operator::alloc}));
        
        // ��ά����ĳ�ʼ��
        GET_CHILD_PTR(constinitval, ConstInitVal, 8);
        if (constinitval->children.size() == 2){    // ֻ��{}ȥ��ʼ������
            for (int i = 0; i<array_size; i++){
                buffer.push_back(new Instruction({Operand(new_name, Type::IntPtr), Operand(std::to_string(i), Type::IntLiteral), Operand("0", Type::IntLiteral), Operator::store}));
            }
        }else{
            int cnt = 0;    // �����±�
            for (int i = 1; i< (int)constinitval->children.size()-1; i+=2, cnt++){     // ����'{' [ ConstInitVal { ',' ConstInitVal } ] '}'
                ConstInitVal* child = dynamic_cast<ConstInitVal*>(constinitval->children[i]);
                ConstExp* constexp = dynamic_cast<ConstExp*>(child->children[0]);
                analysisConstExp(constexp, buffer); // ����ConstExp�ڵ�
                buffer.push_back(new Instruction({Operand(new_name, Type::IntPtr), Operand(std::to_string(cnt), Type::IntLiteral), Operand(constexp->v, Type::IntLiteral), Operator::store}));
            }
        }
    }
}


// ConstInitVal -> ConstExp | '{' [ ConstInitVal { ',' ConstInitVal } ] '}'
void frontend::Analyzer::analysisConstInitVal(ConstInitVal* root, vector<ir::Instruction*>& buffer){
    if (root->children[0]->type == NodeType::CONSTEXP){     // �����������
        ANALYSIS(constexp, ConstExp, 0);    //����ConstExp�ڵ�
        root->v = constexp->v;
        root->t = constexp->t;
    }
}


// VarDecl -> BType VarDef { ',' VarDef } ';'
void frontend::Analyzer::analysisVarDecl(VarDecl* root, vector<ir::Instruction*>& buffer){

    ANALYSIS(btype, BType, 0);      // ����Btype�ڵ�
    root->t = btype->t;             // ��������ΪBType�ڵ�����
    ANALYSIS(vardef, VarDef, 1);    // ����VarDef�ڵ�
    int i = 2;  
    while (i < (int)root->children.size()-1){
        ANALYSIS(vardef, VarDef, i+1);  // ����ConstDef�ڵ�
        i += 2;
    }
}


// VarDef -> Ident { '[' ConstExp ']' } [ '=' InitVal ]
void frontend::Analyzer::analysisVarDef(VarDef* root, vector<ir::Instruction*>& buffer){

    auto root_type = dynamic_cast<VarDecl*>(root->parent)->t;   // ���ڵ�VarDecl������


    GET_CHILD_PTR(identifier, Term, 0);
    string id = identifier->token.value;    // ����ԭ��"a"


    string new_name = symbol_table.get_scoped_name(id);     // ���ű��������"a_g"
    if ((int)root->children.size() == 1){    // ��ͨ�������壬û�и�ֵ
        Operand des = Operand(new_name, root_type);     // Ŀ�������
        auto opcode = (root_type == Type::Float || root_type == Type::FloatLiteral) ? Operator::fdef : Operator::def;
        if (root_type == Type::Float){  // ����ΪFloat����
            buffer.push_back(new Instruction(Operand("0.0", Type::FloatLiteral), Operand(), des, opcode));
        }else{  // ����ΪInt����
            buffer.push_back(new Instruction(Operand("0", Type::IntLiteral), Operand(), des, opcode));
        }
        // symbol_table.scope_stack.back().table.insert({id, {op1, {}}});      // ��ǰ��������ű�������
        symbol_table.scope_stack.back().table.insert({id, {des, {}}});      // ��ǰ��������ű�������
    }else{
        GET_CHILD_PTR(term, Term, 1);   // ��ȡ�ڶ����ڵ�
        if (term->token.type == TokenType::ASSIGN){   //��ͨ��������,�и�ֵ
            ANALYSIS(initval, InitVal, 2);    // ����InitVal�ڵ�
            Operand des = Operand(new_name, root_type);     // Ŀ�������
            auto opcode = (root_type == Type::Float || root_type == Type::FloatLiteral) ? Operator::fdef : Operator::def;
            Operand op1 = Operand(initval->v, initval->t);    // ��һ������
            if (root_type == Type::Float){  // �����������
                if (initval->t == Type::Int){  // ����ת��:Int->Float
                    auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
                    buffer.push_back(new Instruction(op1, {}, tmp, Operator::cvt_i2f));
                    op1 = tmp;  // ���µ�һ������
                }else if (initval->t == Type::IntLiteral){     // ����ת��:IntLiteral->FloatLiteral
                    op1.type = Type::FloatLiteral;
                }
            }else{  // ���ͳ�������
                assert(root_type == Type::Int);
                if (initval->t == Type::Float){    // ����ת��:Float->Int
                    auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
                    buffer.push_back(new Instruction(op1, {}, tmp, Operator::cvt_f2i));
                    op1 = tmp;
                }else if(initval->t == Type::FloatLiteral){    // ����ת��:FloatLiteral->IntLiteral
                    op1.name = std::to_string((int)std::stof(op1.name));  // string->float->int->string
                    op1.type = Type::IntLiteral;
                }
            }
            buffer.push_back(new Instruction(op1, Operand(), des, opcode));     // ��������IR
            symbol_table.scope_stack.back().table.insert({id, {des, {}}});      // ��ǰ��������ű�������
        
        }else if(root->children.back()->type == NodeType::INITVAL){    // ����,�и�ֵ
            // VarDef -> Ident '[' ConstExp ']' '=' InitVal
            if ((int)root->children.size() == 6){   //һά���鶨��
                ANALYSIS(constexp, ConstExp, 2);    // ����ConstExp�ڵ�
                int array_size = std::stoi(constexp->v);    // ���鳤��
                STE arr_ste;    // ��ʱSTE
                arr_ste.dimension.push_back(array_size);  
                ir::Type curr_type = root_type;
                if (curr_type == ir::Type::Int){
                    curr_type = ir::Type::IntPtr;
                }else if (curr_type == ir::Type::Float){
                    curr_type = ir::Type::FloatPtr;
                }
                arr_ste.operand = ir::Operand(new_name, curr_type);
                symbol_table.scope_stack.back().table[id] = arr_ste;    // ������ű�
                buffer.push_back(new Instruction({Operand(std::to_string(array_size),ir::Type::IntLiteral), {}, Operand(new_name, curr_type), Operator::alloc}));

                // һά����ĳ�ʼ��
                GET_CHILD_PTR(initval, InitVal, 5);
                if (initval->children.size() == 2){    // ֻ��{}ȥ��ʼ������
                    for (int i = 0; i<array_size; i++){
                        buffer.push_back(new Instruction({Operand(new_name, Type::IntPtr), Operand(std::to_string(i), Type::IntLiteral), Operand("0", Type::IntLiteral), Operator::store}));
                    }
                }else{
                    int cnt = 0;    // �����±�
                    for (int i = 1; i< (int)initval->children.size()-1; i+=2, cnt++){     // ����'{' [ InitVal { ',' InitVal } ] '}'
                        InitVal* child = dynamic_cast<InitVal*>(initval->children[i]);
                        Exp* exp = dynamic_cast<Exp*>(child->children[0]);
                        analysisExp(exp, buffer); // ����Exp�ڵ�
                        buffer.push_back(new Instruction({Operand(new_name, Type::IntPtr), Operand(std::to_string(cnt), Type::IntLiteral), Operand(exp->v, Type::IntLiteral), Operator::store}));
                    }
                    // a[20]={1,2},���д�Ϻ�����ʼ��Ϊ0
                    for (;cnt<array_size;cnt++){
                        buffer.push_back(new Instruction({Operand(new_name, Type::IntPtr), Operand(std::to_string(cnt), Type::IntLiteral), Operand("0", Type::IntLiteral), Operator::store}));
                    }
                }
            // VarDef -> Ident '[' ConstExp ']' '[' ConstExp ']' '=' InitVal
            }else if ((int)root->children.size() == 9){  // ��ά���鶨��
                ANALYSIS(constexp1, ConstExp, 2);    // ����ConstExp�ڵ�
                ANALYSIS(constexp2, ConstExp, 5);    // ����ConstExp�ڵ�
                int array_size = std::stoi(constexp1->v) * std::stoi(constexp2->v);    // ���鳤��
                STE arr_ste;    // ��ʱSTE
                arr_ste.dimension.push_back(std::stoi(constexp1->v));   // ��һά
                arr_ste.dimension.push_back(std::stoi(constexp2->v));   // �ڶ�ά
                ir::Type curr_type = root_type;
                if (curr_type == ir::Type::Int){
                    curr_type = ir::Type::IntPtr;
                }else if (curr_type == ir::Type::Float){
                    curr_type = ir::Type::FloatPtr;
                }
                arr_ste.operand = ir::Operand(new_name, curr_type);
                symbol_table.scope_stack.back().table[id] = arr_ste;    // ������ű�
                buffer.push_back(new Instruction({Operand(std::to_string(array_size),ir::Type::IntLiteral), {}, Operand(new_name, curr_type), Operator::alloc}));
                
                // ��ά����ĳ�ʼ��
                GET_CHILD_PTR(initval, InitVal, 8);
                if (initval->children.size() == 2){    // ֻ��{}ȥ��ʼ������
                    for (int i = 0; i<array_size; i++){
                        buffer.push_back(new Instruction({Operand(new_name, Type::IntPtr), Operand(std::to_string(i), Type::IntLiteral), Operand("0", Type::IntLiteral), Operator::store}));
                    }
                }else{
                    int cnt = 0;    // �����±�
                    for (int i = 1; i< (int)initval->children.size()-1; i+=2, cnt++){     // ����'{' [ ConstInitVal { ',' ConstInitVal } ] '}'
                        InitVal* child = dynamic_cast<InitVal*>(initval->children[i]);
                        Exp* exp = dynamic_cast<Exp*>(child->children[0]);
                        analysisExp(exp, buffer); // ����Exp�ڵ�
                        buffer.push_back(new Instruction({Operand(new_name, Type::IntPtr), Operand(std::to_string(cnt), Type::IntLiteral), Operand(exp->v, Type::IntLiteral), Operator::store}));
                    }
                }
            }
        }else{  // ����,û�и�ֵ
            // VarDef -> Ident {'[' ConstExp ']'}
            if ((int)root->children.size() == 4){   //һά���鶨��
                ANALYSIS(constexp, ConstExp, 2);    // ����ConstExp�ڵ�
                int array_size = std::stoi(constexp->v);    // ���鳤��
                STE arr_ste;    // ��ʱSTE
                arr_ste.dimension.push_back(array_size);  
                ir::Type curr_type = root_type;
                if (curr_type == ir::Type::Int){
                    curr_type = ir::Type::IntPtr;
                }else if (curr_type == ir::Type::Float){
                    curr_type = ir::Type::FloatPtr;
                }
                arr_ste.operand = ir::Operand(new_name, curr_type);
                symbol_table.scope_stack.back().table[id] = arr_ste;    // ������ű�
                buffer.push_back(new Instruction({Operand(std::to_string(array_size),ir::Type::IntLiteral), {}, Operand(new_name, curr_type), Operator::alloc}));

                // һά����ĳ�ʼ��
                
                for (int i = 0; i<array_size; i++){
                    buffer.push_back(new Instruction({Operand(new_name, Type::IntPtr), Operand(std::to_string(i), Type::IntLiteral), Operand("0", Type::IntLiteral), Operator::store}));
                }
            // VarDef -> Ident '[' ConstExp ']' '[' ConstExp ']'
            }else if ((int)root->children.size() == 7){
                ANALYSIS(constexp1, ConstExp, 2);    // ����ConstExp�ڵ�
                ANALYSIS(constexp2, ConstExp, 5);    // ����ConstExp�ڵ�
                int array_size = std::stoi(constexp1->v) * std::stoi(constexp2->v);    // ���鳤��
                STE arr_ste;    // ��ʱSTE
                arr_ste.dimension.push_back(std::stoi(constexp1->v));   // ��һά
                arr_ste.dimension.push_back(std::stoi(constexp2->v));   // �ڶ�ά
                ir::Type curr_type = root_type;
                if (curr_type == ir::Type::Int){
                    curr_type = ir::Type::IntPtr;
                }else if (curr_type == ir::Type::Float){
                    curr_type = ir::Type::FloatPtr;
                }
                arr_ste.operand = ir::Operand(new_name, curr_type);
                symbol_table.scope_stack.back().table[id] = arr_ste;    // ������ű�
                buffer.push_back(new Instruction({Operand(std::to_string(array_size),ir::Type::IntLiteral), {}, Operand(new_name, curr_type), Operator::alloc}));
                
                // ��ά����ĳ�ʼ��
                for (int i = 0; i<array_size; i++){
                    buffer.push_back(new Instruction({Operand(new_name, Type::IntPtr), Operand(std::to_string(i), Type::IntLiteral), Operand("0", Type::IntLiteral), Operator::store}));
                }
            }
        }
    }
}


// InitVal -> Exp | '{' [ InitVal { ',' InitVal } ] '}'
void frontend::Analyzer::analysisInitVal(InitVal* root, vector<ir::Instruction*>& buffer){

    if (root->children[0]->type == NodeType::EXP){  // ��һ���ڵ���Exp,��ͨ�������
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
    std::string name = dynamic_cast<Term*>(root->children[1])->token.value; // ��������
    if ((int)root->children.size() > 2){     // ������Ϊ����

        auto type = (btype->t == Type::Int) ? Type::IntPtr : Type::FloatPtr;
        buffer.ParameterList.push_back(Operand(name, type));   // ���Ӳ���
        symbol_table.scope_stack.back().table.insert({name, {Operand(name, type), {}}});

    }else{      // ��ͨ������Ϊ����
        buffer.ParameterList.push_back(Operand(name, btype->t));   // ���Ӳ���
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

    symbol_table.add_scope(root);   // ����������

    if ((int)root->children.size() > 2){
        int i = 1;
        while (i < (int)root->children.size()-1){
            ANALYSIS(blockitem, BlockItem, i);
            i += 1;
        }
    }

    symbol_table.exit_scope();  //�˳�����������
}


// BlockItem -> Decl | Stmt
void frontend::Analyzer::analysisBlockItem(BlockItem* root, vector<ir::Instruction*>& buffer){

    if (root->children[0]->type == NodeType::DECL){     // ��������
        ANALYSIS(decl, Decl, 0);
    }else if (root->children[0]->type == NodeType::STMT){   // ��������
        ANALYSIS(stmt, Stmt, 0);
    }
}


// Stmt -> LVal '=' Exp ';' | Block | 'if' '(' Cond ')' Stmt [ 'else' Stmt ] | 'while' '(' Cond ')' Stmt | 'break' ';' | 'continue' ';' | 'return' [Exp] ';' | [Exp] ';'
void frontend::Analyzer::analysisStmt(Stmt* root, vector<ir::Instruction*>& buffer){

    if (root->children[0]->type == NodeType::LVAL){     // ��ֵ����
        ANALYSIS(exp, Exp, 2);  // ����Exp�ڵ�
        ANALYSIS(lval, LVal, 0);    // ����lval�ڵ�

    }else if (root->children[0]->type == NodeType::BLOCK){   // Block��

        ANALYSIS(block, Block, 0);

    }else if (root->children[0]->type == NodeType::EXP){    // Exp��

        ANALYSIS(exp, Exp, 0);

    }else if (dynamic_cast<Term*>(root->children[0])->token.type == TokenType::IFTK){  // if��
        // Stmt -> 'if' '(' Cond ')' Stmt [ 'else' Stmt ]

        auto tmp1 = vector<Instruction*>();
        GET_CHILD_PTR(cond, Cond, 2);
        analysisCond(cond, tmp1);    // ����cond�ڵ�
        buffer.insert(buffer.end(), tmp1.begin(), tmp1.end());    // ����cond IR

        // if ��������ת
        buffer.push_back(new Instruction(Operand(cond->v,cond->t), Operand(), Operand("2",Type::IntLiteral), Operator::_goto));

        // ����if��Stmt
        GET_CHILD_PTR(stmt1, Stmt, 4);   // ��ȡif��stmt
        auto tmp2 = vector<Instruction*>();  // if��stmt IR
        analysisStmt(stmt1, tmp2);   // ����stmt�ڵ�

        if ((int)root->children.size() == 5){    // if û��else

            // if ����������ת
            buffer.push_back(new Instruction({Operand(), Operand(), Operand(std::to_string(tmp2.size()+1), Type::IntLiteral), Operator::_goto}));

            // ����if stmt��IR
            buffer.insert(buffer.end(), tmp2.begin(), tmp2.end());

            // ��������IR,��ֹif������û��IR��
            buffer.push_back(new Instruction({Operand(), Operand(), Operand(), Operator::__unuse__}));

        }else{      // if ��else
            auto tmp3 = vector<Instruction*>();     // else��stmt IR
            GET_CHILD_PTR(stmt2, Stmt, 6);   // ��ȡelse ��stmt
            analysisStmt(stmt2, tmp3);   // ����else ��stmt�ڵ�

            // ifִ����Ҫ����else
            tmp2.push_back(new Instruction({Operand(), Operand(), Operand(std::to_string(tmp3.size()+1), Type::IntLiteral), Operator::_goto}));

            // ִ��elseҪ����if
            buffer.push_back(new Instruction({Operand(), Operand(), Operand(std::to_string(tmp2.size()+1), Type::IntLiteral), Operator::_goto}));

            // �ϲ�if��stmt
            buffer.insert(buffer.end(), tmp2.begin(), tmp2.end());

            // �ϲ�else��stmt
            buffer.insert(buffer.end(), tmp3.begin(), tmp3.end());

            // ��������IR,��ֹif������û��IR��
            buffer.push_back(new Instruction({Operand(), Operand(), Operand(), Operator::__unuse__}));
        }
    }else if (dynamic_cast<Term*>(root->children[0])->token.type == TokenType::WHILETK){   // while��
        
        // Stmt -> 'while' '(' Cond ')' Stmt 
        
        GET_CHILD_PTR(cond, Cond, 2);
        auto tmp1 = vector<Instruction*>();  // cond IR
        analysisCond(cond, tmp1);

        GET_CHILD_PTR(stmt, Stmt, 4);
        auto tmp2 = vector<Instruction*>();  // while��stmt IR
        analysisStmt(stmt, tmp2);

        // ÿһ��while������Ҫ�ص���ͷ
        tmp2.push_back(new Instruction({Operand("continue", Type::null), Operand(), Operand(), Operator::__unuse__}));

        // ����WHILE���е�BREAK��CONTINUE���ָ��, �޸�Ϊ_goto
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

        // �ϲ�cond IR
        buffer.insert(buffer.end(), tmp1.begin(), tmp1.end());
        
        // ��������,ִ��stmt
        buffer.push_back(new Instruction({Operand(cond->v,cond->t), Operand(), Operand("2",Type::IntLiteral), Operator::_goto}));

        // ������,����stmt
        buffer.push_back(new Instruction({Operand(), Operand(), Operand(std::to_string(tmp2.size()+1), Type::IntLiteral), Operator::_goto}));

        // �ϲ�stmt IR
        buffer.insert(buffer.end(), tmp2.begin(), tmp2.end());

        // ����unuse
        buffer.push_back(new Instruction(Operand(), Operand(), Operand(), Operator::__unuse__));

    }else if (dynamic_cast<Term*>(root->children[0])->token.type == TokenType::BREAKTK){   // break��
        
        buffer.push_back(new Instruction({Operand("break", Type::null), Operand(), Operand(), Operator::__unuse__}));

    }else if (dynamic_cast<Term*>(root->children[0])->token.type == TokenType::CONTINUETK){    // continue��
        
        buffer.push_back(new Instruction({Operand("continue", Type::null), Operand(), Operand(), Operator::__unuse__}));
    
    }else if (dynamic_cast<Term*>(root->children[0])->token.type == TokenType::RETURNTK){  // return��
        
        // stmt -> 'return' [Exp] ';'

        if ((int)root->children.size() == 2){
            Instruction* return_inst = new Instruction({Operand("null", Type::null), Operand(), Operand(), Operator::_return});
            buffer.push_back(return_inst);

        }else{
            // stmt -> 'return' Exp ';'
            auto tmp = vector<Instruction*>();
            GET_CHILD_PTR(exp, Exp, 1);
            analysisExp(exp, tmp);
            buffer.insert(buffer.end(), tmp.begin(), tmp.end());     // ����exp IR

            // ���ݺ����������ͽ��з���
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


    ANALYSIS(addexp, AddExp, 0);    // ����addexp�ڵ�
    COPY_EXP_NODE(addexp, root);
}


// Cond -> LOrExp
void frontend::Analyzer::analysisCond(Cond* root, vector<ir::Instruction*>& buffer){
    ANALYSIS(lorexp, LOrExp, 0);    // ����LOrExp�ڵ�
    COPY_EXP_NODE(lorexp, root);
}


// LVal -> Ident {'[' Exp ']'}
void frontend::Analyzer::analysisLVal(LVal* root, vector<ir::Instruction*>& buffer){

    auto tk = dynamic_cast<Term*>(root->children[0])->token;    // ��ȡTerm�ڵ��token


    auto op = symbol_table.get_operand(tk.value);   // �ӷ��ű�
    root->t = op.type;  // �ӷ��ű�����

    if((int)root->children.size() == 1){     // LVal -> Ident
        // root->v = tk.value;
        
        root->v = op.name;
        root->is_computable = (root->t == Type::IntLiteral || root->t == Type::FloatLiteral) ? true : false;
        //root->i = 0;

        if (root->parent->type == NodeType::STMT){   // ������lval=exp;
            auto exp_par = dynamic_cast<Exp*>(root->parent->children[2]);   // ��exp�ڵ�
            auto op1 = Operand(exp_par->v, exp_par->t);
            auto des = Operand(root->v, root->t);
            if (root->t == Type::Int){
                auto mov_inst = new Instruction({op1, Operand(), des, Operator::mov});
                buffer.push_back(mov_inst);    // �����ͱ�����ֵ
            }else{
                buffer.push_back(new Instruction({op1, Operand(), des, Operator::fmov}));    // �����������ֵ
            }
        }

    }else{      // LVal -> Ident {'[' Exp ']'}

        STE arr = symbol_table.get_ste(tk.value);
        vector<int> dimension = arr.dimension;  // ά��

        // Ident '[' Exp ']'
        if ((int)root->children.size() == 4){     // һά����

            ANALYSIS(exp, Exp, 2);
            Type t = (root->t == Type::IntPtr) ? Type::Int : Type::Float;
            root->t = t;
            Operand index = Operand(exp->v, exp->t);    // ȡ���±�
            if (root->parent->type == NodeType::STMT){   // Stmt->Lval=exp ��Ϊ��ֵ����ֵ����
                auto exp_par = dynamic_cast<Exp*>(root->parent->children[2]);   // ȡ������ֵ�ڵ�exp
                Operand des = Operand(exp_par->v, exp_par->t);
                buffer.push_back(new Instruction({arr.operand, index, des, Operator::store}));  // des�Ǵ����ֵ
                root->v = des.name;
            }else{      // ��Ϊ��ֵ��ȡ������
                Operand des = Operand("t" + std::to_string(tmp_cnt++), t);     // Ŀ�Ĳ�����Ϊ��ʱ����
                buffer.push_back(new Instruction({arr.operand, index, des, Operator::load}));  // ����ʱ�����ݴ棬�ٸ�ֵ
                root->v = des.name;
            }                   
        }else{      // ��ά����
            // Ident '[' Exp ']' '[' Exp ']'

            ANALYSIS(exp1, Exp, 2);
            ANALYSIS(exp2, Exp, 5);
            Type t = (root->t == Type::IntPtr) ? Type::Int : Type::Float;
            root->t = t;
            if (exp1->is_computable && exp2->is_computable){    // �ɼ�
                std::string i = std::to_string(std::stoi(exp1->v) * dimension[1] + std::stoi(exp2->v));
                Operand index = Operand(i, Type::IntLiteral);    // ȡ���±�
                if (root->parent->type == NodeType::STMT){   // Stmt->Lval=exp; ��Ϊ��ֵ����ֵ����
                    auto exp_par = dynamic_cast<Exp*>(root->parent->children[2]);   // ȡ������ֵ�ڵ�exp
                    Operand des = Operand(exp_par->v, exp_par->t);
                    buffer.push_back(new Instruction({arr.operand, index, des, Operator::store}));
                    root->v = des.name;
                }else{
                    Operand des = Operand("t" + std::to_string(tmp_cnt++), t);     // Ŀ�Ĳ�����Ϊ��ʱ����
                    buffer.push_back(new Instruction({arr.operand, index, des, Operator::load}));
                    root->v = des.name;
                }
            }else{      // ���ɼ�
                auto op1 = Operand(exp1->v, exp1->t);
                auto op2 = Operand(std::to_string(dimension[1]), Type::IntLiteral);
                auto op3 = Operand(exp2->v, exp2->t);
                type_transform(op1, op2, buffer);
                auto tmp1 = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
                auto tmp2 = Operand("t" + std::to_string(tmp_cnt++), Type::Int);
                buffer.push_back(new Instruction({op1, op2, tmp1, Operator::mul}));
                buffer.push_back(new Instruction({tmp1, op3, tmp2, Operator::add}));
                if (root->parent->type == NodeType::STMT){   // ��ֵ���
                    auto exp_par = dynamic_cast<Exp*>(root->parent->children[2]);   // ȡ������ֵ�ڵ�exp
                    Operand des = Operand(exp_par->v, exp_par->t);
                    buffer.push_back(new Instruction({arr.operand, tmp2, des, Operator::store}));
                    root->v = des.name;
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

        ANALYSIS(exp, Exp, 1);  // ����Exp�ڵ�
        COPY_EXP_NODE(exp, root);

    }else if (root->children[0]->type == NodeType::LVAL){   // LVal

        ANALYSIS(lval, LVal, 0);    // ����Lval�ڵ�
        COPY_EXP_NODE(lval, root);

    }else{  // Number
        root->is_computable = true; // �ɻ���
        auto number_tk = dynamic_cast<Term*>(root->children[0]->children[0])->token;  //�õ�Number�ڵ��Ӧ�ս����token
        root->t = (number_tk.type==TokenType::INTLTR) ? Type::IntLiteral : Type::FloatLiteral;      // t����Ϊ�ս��������
        if (root->t == Type::IntLiteral){
            root->v = trans2ten(number_tk.value);     // v����Ϊ�ս����ֵ
        }else{
            root->v = number_tk.value;
        }
    }
}


// UnaryExp -> PrimaryExp | Ident '(' [FuncRParams] ')' | UnaryOp UnaryExp
void frontend::Analyzer::analysisUnaryExp(UnaryExp* root, vector<ir::Instruction*>& buffer){

    if (root->children[0]->type == NodeType::PRIMARYEXP){   // UnaryExp -> PrimaryExp

        ANALYSIS(primaryexp, PrimaryExp, 0);
        COPY_EXP_NODE(primaryexp, root);    // ���ϴ�������

    }else if (root->children[0]->type == NodeType::TERMINAL){   // UnaryExp -> Ident '(' [FuncRParams] ')'
        
        std::string func_name = dynamic_cast<Term*>(root->children[0])->token.value;   // ������
        auto op1 = Operand(func_name, Type::null);  // ������һΪ������
        Type t = symbol_table.functions[func_name]->returnType;     //��������ֵ����
        auto des = Operand("t" + std::to_string(tmp_cnt++), t);     // Ŀ�Ĳ�����Ϊ��ʱ����
        if ((int)root->children.size() == 3){    // û�в���
            buffer.push_back(new ir::CallInst(op1, des));
        }else{
            auto callinst = new ir::CallInst(op1, vector<Operand>(), des);  // ��������IR
            GET_CHILD_PTR(funcrparams, FuncRParams, 2);     // ��ȡFuncRParams�ڵ�
            assert(funcrparams);
            analysisFuncRParams(funcrparams, buffer, *callinst);
            buffer.push_back(callinst);     // ���뺯������IR
        }
        root->v = des.name;
        root->t = t;

    }else{      // UnaryExp -> UnaryOp UnaryExp
        auto tk = dynamic_cast<Term*>(root->children[0]->children[0])->token.type;
        ANALYSIS(unaryexp, UnaryExp, 1);    // ����UnaryExp�ڵ�
        if (tk == TokenType::PLUS){     // "+"
            COPY_EXP_NODE(unaryexp, root);
        }else{      // "-" "!"
            root->is_computable = unaryexp->is_computable;
            root->t = unaryexp->t;
            if (unaryexp->is_computable){   // �ɼ�
                if (unaryexp->t == Type::IntLiteral){  // Int������
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
            }else{  // ���ɼ�
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
                }else{      // Float,�����ܳ���!Float
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
    ANALYSIS(exp1, Exp, 0);  // ����Exp�ڵ�
    Operand arg(exp1->v, exp1->t);
    if (arg.type == Type::FloatLiteral) {
        auto tmp = Operand("t" + std::to_string(tmp_cnt++), Type::Float);
        buffer.push_back(new Instruction(arg, {}, tmp, Operator::fdef));
        arg = tmp;
    }
    callinst.argumentList.push_back(arg);
    int i = 1;
    while (i < (int)root->children.size()){
        ANALYSIS(exp2, Exp, i+1);  // ����Exp�ڵ�
        callinst.argumentList.push_back(Operand(exp2->v, exp2->t));
        i += 2;
    }
}


// MulExp -> UnaryExp { ('*' | '/' | '%') UnaryExp }
void frontend::Analyzer::analysisMulExp(MulExp* root, vector<ir::Instruction*>& buffer){

    if ((int)root->children.size() == 1){

        ANALYSIS(unaryexp1, UnaryExp, 0);    // ����unaryexp�ڵ�
        COPY_EXP_NODE(unaryexp1, root);    // ���ϴ�������

    }else if ((int)root->children.size() > 1){
        ANALYSIS(unaryexp1, UnaryExp, 0);    // ����unaryexp�ڵ�
        root->is_computable = unaryexp1->is_computable;
        root->t = unaryexp1->t;
        root->v = unaryexp1->v;
        int i = 1;
        while (i < (int)root->children.size()){
            auto tk = dynamic_cast<Term*>(root->children[i])->token.type;   // �����
            ANALYSIS(unaryexp2, UnaryExp, i+1);     // ������һ��unaryexp�ڵ�
            if(root->is_computable && unaryexp2->is_computable){    // �ɻ���
                root->is_computable = true;
                if(root->t != unaryexp2->t){   // ���Ͳ�һ��
                    root->t = Type::FloatLiteral;
                }

                if(root->t == Type::IntLiteral){    // ����������������
                    if (tk == TokenType::MULT){
                        root->v = std::to_string(std::stoi(root->v) * std::stoi(unaryexp2->v));
                    }else if (tk == TokenType::DIV){
                        root->v = std::to_string(std::stoi(root->v) / std::stoi(unaryexp2->v));
                    }else{
                        root->v = std::to_string(std::stoi(root->v) % std::stoi(unaryexp2->v));
                    }
                }else{      // ����������������
                    if (tk == TokenType::MULT){
                        root->v = std::to_string(std::stof(root->v) * std::stof(unaryexp2->v));
                    }else if (tk == TokenType::DIV){
                        root->v = std::to_string(std::stof(root->v) / std::stof(unaryexp2->v));
                    }
                }
            }else{  // ���ɻ���
                root->is_computable = false;
                Operand op1 = Operand(root->v, root->t);
                Operand op2 = Operand(unaryexp2->v, unaryexp2->t);
                Operand tmp = Operand("t" + std::to_string(tmp_cnt++), root->t);
                if (tk == TokenType::MULT){
                    if (root->t == unaryexp2->t){   // ����һ��
                        if (tmp.type == Type::Int){
                            buffer.push_back(new Instruction({op1, op2, tmp, Operator::mul}));  // mul IR
                        }else{
                            buffer.push_back(new Instruction({op1, op2, tmp, Operator::fmul}));  // fmul IR
                        }
                    }else{      // ���Ͳ�һ��
                        type_transform(op1, op2, buffer);
                        tmp.type = op1.type;     // �������Ϊ����һ��
                        if (tmp.type == Type::Int){
                            buffer.push_back(new Instruction({op1, op2, tmp, Operator::mul}));  // mul IR
                        }else{
                            buffer.push_back(new Instruction({op1, op2, tmp, Operator::fmul}));  // fmul IR
                        }
                    }
                }else if (tk == TokenType::DIV){
                    if (root->t == unaryexp2->t){   // ����һ��
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
                root->v = tmp.name;     // ��ʱ��������
                root->t = tmp.type;     // ��ʱ��������
            }

            i += 2;
        }
    }
}


// AddExp -> MulExp { ('+' | '-') MulExp }
void frontend::Analyzer::analysisAddExp(AddExp* root, vector<ir::Instruction*>& buffer){

    if ((int)root->children.size() == 1){

        ANALYSIS(mulexp1, MulExp, 0);    // ����mulexp�ڵ�
        COPY_EXP_NODE(mulexp1, root);    // ���ϴ�������

    }else if ((int)root->children.size() > 1){  // ���Ԫ�����

        ANALYSIS(mulexp1, MulExp, 0);    // ����mulexp�ڵ�

        root->is_computable = mulexp1->is_computable;
        root->t = mulexp1->t;
        root->v = mulexp1->v;

        int i = 1;
        while (i < (int)root->children.size()){

            auto tk = dynamic_cast<Term*>(root->children[i])->token.type;   // �����
            ANALYSIS(mulexp2, MulExp, i+1);     // ������һ��mulexp�ڵ�
            if(root->is_computable && mulexp2->is_computable){    // �ɻ���
                root->is_computable = true;
                if(root->t != mulexp2->t){   // ���Ͳ�һ��
                    root->t = Type::FloatLiteral;
                }

                if(root->t == Type::IntLiteral){    // ����������������
                    if (tk == TokenType::PLUS){
                        root->v = std::to_string(std::stoi(root->v) + std::stoi(mulexp2->v));    // ������,��ֻ�����������
                    }else{  
                        root->v = std::to_string(std::stoi(root->v) - std::stoi(mulexp2->v));
                    }
                }else{      // ����������������
                    if (tk == TokenType::PLUS){
                        root->v = std::to_string(std::stof(root->v) + std::stof(mulexp2->v));    // ������,��ֻ�����������
                    }else{  
                        root->v = std::to_string(std::stof(root->v) - std::stof(mulexp2->v));
                    }
                }
            }else{  // ���ɻ���
                root->is_computable = false;
                Operand op1 = Operand(root->v, root->t);
                Operand op2 = Operand(mulexp2->v, mulexp2->t);
                Operand tmp = Operand("t" + std::to_string(tmp_cnt++), root->t);
                if (!root->is_computable && !mulexp2->is_computable){   // �������Ǳ���
                    if (tk == TokenType::PLUS){
                        if (root->t == mulexp2->t){   // ����һ��
                            if (tmp.type == Type::Int){
                                buffer.push_back(new Instruction({op1, op2, tmp, Operator::add}));  // add IR
                            }else{
                                buffer.push_back(new Instruction({op1, op2, tmp, Operator::fadd}));  // fadd IR
                            }
                        }else{  // ���Ͳ�һ��
                            type_transform(op1, op2, buffer);
                            tmp.type = op1.type;
                            if (tmp.type == Type::Int){
                                buffer.push_back(new Instruction({op1, op2, tmp, Operator::add}));  // add IR
                            }else{
                                buffer.push_back(new Instruction({op1, op2, tmp, Operator::fadd}));  // fadd IR
                            }
                        }
                    }else{
                        if (root->t == mulexp2->t){   // ����һ��
                            if (tmp.type == Type::Int){
                                buffer.push_back(new Instruction({op1, op2, tmp, Operator::sub}));  // sub IR
                            }else{
                                buffer.push_back(new Instruction({op1, op2, tmp, Operator::fsub}));  // fsub IR
                            }
                        }else{  // ���Ͳ�һ��
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
                root->v = tmp.name;     // ��ʱ��������
                root->t = tmp.type;     // ��ʱ��������
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

            ANALYSIS(addexp2, AddExp, i+1);     // ����AddExp�ڵ�
            auto tk = dynamic_cast<Term*>(root->children[i])->token.type;   // �����

            root->is_computable = false;     // ���ɻ���
            Operand op1 = Operand(root->v, root->t);
            Operand op2 = Operand(addexp2->v, addexp2->t);
            type_transform(op1, op2, buffer);   // ���ͱ���һ��
            Operand des = Operand("t" + std::to_string(tmp_cnt++), Type::Int);  // ��ʱ������
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

        ANALYSIS(relexp, RelExp, 0);     // ����RelExp�ڵ�
        COPY_EXP_NODE(relexp, root);

    }else{      // EqExp -> RelExp ('==' | '!=') RelExp

        ANALYSIS(relexp1, RelExp, 0);     // ����RelExp�ڵ�
        root->is_computable = relexp1->is_computable;
        root->v = relexp1->v;
        root->t = relexp1->t;

        int i = 1;
        while (i < (int)root->children.size()){
            ANALYSIS(relexp2, RelExp, i+1);     // ����RelExp�ڵ�
            auto tk = dynamic_cast<Term*>(root->children[i])->token.type;   // �����
            
            root->is_computable = false;
            Operand op1 = Operand(root->v, root->t);
            Operand op2 = Operand(relexp2->v, relexp2->t);
            type_transform(op1, op2, buffer);
            Operand des = Operand("t" + std::to_string(tmp_cnt++), Type::Int);  // ��ʱ������
            if (tk == TokenType::EQL){  // '==' ���ͼ�� need to do
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

        ANALYSIS(eqexp, EqExp, 0);     // ����EqExp�ڵ�
        COPY_EXP_NODE(eqexp, root);

    }else{      // LAndExp -> EqExp '&&' LAndExp
        
        // LAndExp -> EqExp '&&' LAndExp
        ANALYSIS(eqexp, EqExp, 0);  // ����EqExp�ڵ�
        
        auto tmp = vector<ir::Instruction*>();  // LAndExp�ڵ��IR����
        auto andexp = dynamic_cast<LAndExp*>(root->children[2]);  //ȡ��LAndExp�ڵ�
        assert(andexp);
        analysisLAndExp(andexp, tmp);    // ����LAndExp�ڵ�
        
        root->t = Type::Int;    // and���ʽ����̶�ΪInt

        Operand op1 = Operand(eqexp->v, eqexp->t);
        Operand op2 = Operand(andexp->v, andexp->t);
        Operand des = Operand("t" + std::to_string(tmp_cnt++), Type::Int);    // ��ʱ����,������ΪInt
        Operand t1 = Operand("t" + std::to_string(tmp_cnt++), op1.type);    // ��ʱ����1
        
        buffer.push_back(new Instruction({op1, {}, t1, Operator::mov}));    // ��op1ת��Ϊ����
        buffer.push_back(new Instruction({t1, {}, {"2", Type::IntLiteral}, Operator::_goto}));  // op1����,�ж�op2
        buffer.push_back(new Instruction({{}, {}, {std::to_string(tmp.size()+3), Type::IntLiteral}, Operator::_goto}));
        buffer.insert(buffer.end(), tmp.begin(), tmp.end());    // ��β������landexp�ڵ��IR����
        buffer.push_back(new Instruction({op2, {}, des, Operator::mov}));   // op2����,des = op2
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
        
        root->t = Type::Int;    // LOrExp���ʽ����õ������͹̶�Ϊ���ͱ���,������ò�Ʋ�֧��IntLiteral

        ANALYSIS(andexp, LAndExp, 0);     // ����LAndExp�ڵ�

        auto tmp = vector<ir::Instruction*>();  // LorExp�ڵ��IR����
        auto orexp = dynamic_cast<LOrExp*>(root->children[2]);  //ȡ��LOrExp�ڵ�
        assert(orexp);
        analysisLOrExp(orexp, tmp);    // ����LOrExp�ڵ�

        // root->is_computable = andexp->is_computable;    // �ɼ��Ը�ֵΪandexp�ڵ�

        Operand op1 = Operand(andexp->v, andexp->t);
        Operand op2 = Operand(orexp->v, orexp->t);
        Operand t1 = Operand("t" + std::to_string(tmp_cnt++), root->t);    //��ʱ����1
        Operand des = Operand("t" + std::to_string(tmp_cnt++), root->t);    //��ʱ����,���
        
        buffer.push_back(new Instruction({op1, {}, t1, Operator::mov}));    // ��op1ת��Ϊ����
        buffer.push_back(new Instruction({t1, {}, {std::to_string(tmp.size()+3), Type::IntLiteral}, Operator::_goto}));    // if(op1)->des=1
        buffer.insert(buffer.end(), tmp.begin(), tmp.end());    // ��β������orexp�ڵ��IR����
        buffer.push_back(new Instruction({op2, {}, des, Operator::mov}));   // else -> des = op2
        buffer.push_back(new Instruction({{}, {}, {"2", Type::IntLiteral}, Operator::_goto}));
        buffer.push_back(new Instruction({"1", Type::IntLiteral}, {}, des, Operator::mov));

        root->v = des.name;
    }
}


// ConstExp -> AddExp
void frontend::Analyzer::analysisConstExp(ConstExp* root, vector<ir::Instruction*>& buffer){
    ANALYSIS(addexp, AddExp, 0);    // ����AddExp�ڵ�
    root->v = addexp->v;
    root->t = addexp->t;
}