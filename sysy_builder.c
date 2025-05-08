#include "sysy_builder.hpp"
#include "logging.hpp"
#include <stack>
#include <cmath>

#define CONST_FP(num) ConstantFP::get((float)num, module.get())
#define CONST_INT(num) ConstantInt::get(num, module.get())
// types
Type *VOID_T;

Type *INT1_T;
Type *INT32_T;
Type *INT8_T;
Type *INT16_T;
Type *INT64_T;

Type *INT32PTR_T;
Type *FLOAT_T;
Type *FLOATPTR_T;

// 确保在运算过程中，左右操作数的类型一致，尤其是在整数和浮点数之间转换
// 返回值
// - true: 左右操作数均为int类型
// - false: 左右操作数均为float类型，或强制类型转换后都被转换成float类型
bool SysyBuilder::promote(Value **l_val_p, Value **r_val_p, const_val *l_num, const_val *r_num)
{
    bool is_int = false;
    auto &l_val = *l_val_p;
    auto &r_val = *r_val_p;
    if (l_val->get_type() == r_val->get_type())
    {
        is_int = l_val->get_type()->is_integer_type(); //如果左右操作数类型一致且都是int，则返回true
    }
    else//类型不一致时
    {
        if (l_val->get_type()->is_integer_type())//左值是int类型，右值是float类型，将左值转换成float类型
        {
            if (context.is_const_exp)
            {
                l_num->f_val = (float)l_num->i_val;
            }
            else if (scope.in_global())
                l_num->f_val = (float)l_num->i_val;
            else
                l_val = builder->create_sitofp(l_val, FLOAT_T);//使用sitofp指令转换
        }
        else//右值是int类型，左值是float类型，将右值转换成float类型
        {
            if (context.is_const_exp)
                r_num->f_val = (float)r_num->i_val;
            else if (scope.in_global())
                r_num->f_val = (float)r_num->i_val;
            else
                r_val = builder->create_sitofp(r_val, FLOAT_T);//使用sitofp指令转换
        }
    }
    return is_int;
}
/*
 * use SysyBuilder::Scope to construct scopes
 * scope.enter: enter a new scope
 * scope.exit: exit current scope
 * scope.push: add a new binding to current scope
 * scope.find: find and return the value bound to the name
 */
// Program -> CompUnit
// CompUnit -> (CompUnit) Decl | FuncDef
Value *SysyBuilder::visit(ASTProgram &node)
{
    //初始化类型信息，以便后续生成IR时获取
    VOID_T = module->get_void_type();
    INT1_T = module->get_int1_type();
    INT8_T = module->get_int8_type();
    INT16_T = module->get_int16_type();
    INT32_T = module->get_int32_type();
    INT64_T = module->get_int64_type();
    INT32PTR_T = module->get_int32_ptr_type();
    FLOAT_T = module->get_float_type();
    FLOATPTR_T = module->get_float_ptr_type();

    Value *ret_val = nullptr;
    for (auto &comp : node.compunits) // 遍历 CompUnit 节点,不过在ast.cpp中经过flatten操作后，这里其实会直接执行对应传入ASTDecl或ASTFuncDef的visit方法
    {
        ret_val = comp->accept(*this);
    }
    return ret_val;
}
// 函数定义
// FuncDef -> BType|void IDENT ( FuncFParams ) Block
// FuncDef -> BType|void IDENT () Block
// FuncFParams -> FuncFParam | FuncFParams , FuncFParam
Value *SysyBuilder::visit(ASTFuncDef &node)
{
    FunctionType *func_type = nullptr; //函数类型
    Type *ret_type = nullptr; //返回值类型
    std::vector<Type *> param_types; //函数参数类型
    // 返回类型确定
    if (node.type == TYPE_INT)
        ret_type = INT32_T;
    else if (node.type == TYPE_FLOAT)
        ret_type = FLOAT_T;
    else
        ret_type = VOID_T;
    // 参数类型确定
    for (auto &param : node.params)
    {
        if (param->type == TYPE_INT)
        {   
            if (param->isarray)//int型数组，类似int a[]([num])
            {   // 创建一个指向对应数组类型的指针而不保留数组类型参数
                auto temp = INT32_T;
                for (auto dim = param->array_lists.rbegin(); dim != param->array_lists.rend(); ++dim)
                {
                    auto num = *dim;
                    auto const_ori = num->is_const;
                    num->is_const = true;
                    num->accept(*this); // 这里递归计算数组的维度
                    num->is_const = const_ori;
                    temp = ArrayType::get(temp, context.val.i_val); // 基于当前的维度构造数组类型
                }
                temp = PointerType::get(temp); // 最终获得的是指向数组的指针
                param_types.push_back(temp); // 将该类型添加到参数类型列表中
            } 
            else{ //int型变量
                param_types.push_back(INT32_T);
            }
        }
        else // 同上，处理成一个 指向 float[num]的指针
        { 
            if (param->isarray) //float型数组，类似float a[]([num])
            {
                auto temp = FLOAT_T;
                for (auto dim = param->array_lists.rbegin(); dim != param->array_lists.rend(); ++dim)
                {
                    auto num = *dim;
                    auto const_ori = num->is_const;
                    num->is_const = true;
                    num->accept(*this); // 这里递归计算数组的维度
                    num->is_const = const_ori;
                    temp = ArrayType::get(temp, context.val.i_val); // 基于当前的维度构造数组类型
                }
                temp = PointerType::get(temp); // 最终获得的是指向数组的指针
                param_types.push_back(temp); // 将该类型添加到参数类型列表中
            }
            else{
                param_types.push_back(FLOAT_T);
            }
        }
    }
    func_type = FunctionType::get(ret_type, param_types); //上面处理好的返回值类型和参数类型
    auto func = Function::create(func_type, node.id, module.get());
    scope.push(node.id, func);//加入符号表
    context.func = func;// 将context变更为当前function
    // 以上是函数的声明，现在开始函数定义
    auto funBB = BasicBlock::create(module.get(), "entry", func); //函数入口基本块
    builder->set_insert_point(funBB); //进入函数所在基本块
    scope.enter();
    std::vector<Value *> args;
    for (auto &arg : func->get_args()) //获取形参
    {
        args.push_back(&arg);
    }
    for (size_t i = 0; i < node.params.size(); ++i)
    {
        // TODO:你需要处理函数参数，并把它们存入符号表scope
        // 提示：可以回顾预热实验中的fun_generator，前面已经获取了形参
        //      现在你需要先在栈上给它们开辟空间（alloca）
        //      再把前面获取的形参存储到对应位置（store）
        //      最后，为了后续函数体部分的基本块可以获取到这些参数，你需要把它们存入符号表（scope.push）
        //      需要考虑数组类型参数的存在

        // TODO--------------end
    }
    node.block->accept(*this);//递归处理函数体
    if (not builder->get_insert_block()->is_terminated()) // 基本块没有以跳转指令结尾的话自动添加一个return，这种情况下只使用默认的返回值
    {
        if (context.func->get_return_type()->is_void_type())
            builder->create_void_ret();
        else if (context.func->get_return_type()->is_float_type())
            builder->create_ret(CONST_FP(0.));
        else
            builder->create_ret(CONST_INT(0));
    }
    scope.exit();//退出函数所属作用域
    return nullptr;
}
// Decl -> ConstDecl | VarDecl
Value *SysyBuilder::visit(ASTDecl &node) //常量与变量声明语句
{
    if (node.is_const == true)
        context.is_const = true; //ConstDecl → 'const' BType ConstDef { ',' ConstDef } ';'
    else
        context.is_const = false; //VarDecl → BType VarDef { ',' VarDef } ';'
    context.type = node.type; //存储类型（也就是上面两个注释的产生式中的BType），以便后续递归处理ConstDef/VarDef时获取
    for (auto &def : node.def_lists) //递归处理其中的变量与常量定义（ASTDef）
    {
        def->accept(*this);
    }
    return nullptr;
}
// 根据传入的数组类型 array_type_t 和常量值 val，递归地处理数组类型，最终返回一个常量数组
Constant *SysyBuilder::get_const_array(Type *array_type_t, std::vector<const_val> val)
{
    if (array_type_t->is_array_type())
    {
        auto array_type = static_cast<ArrayType *>(array_type_t);
        auto dim = array_type->get_num_of_elements();
        std::vector<Constant *> temp;
        assert(val.size() % dim == 0);
        for (unsigned int i = 0; i < dim; i++)
        {
            temp.push_back(get_const_array(array_type->get_element_type(), std::vector<const_val>(val.begin() + i * val.size() / dim, val.begin() + (i + 1) * val.size() / dim)));
        }
        return ConstantArray::get(array_type, temp);
    }
    else if (array_type_t->is_int32_type())
    {
        assert(val.size() == 1);
        return ConstantInt::get(int(val[0].i_val), module.get());
    }
    else if (array_type_t->is_float_type())
    {
        assert(val.size() == 1);
        return ConstantFP::get(val[0].f_val, module.get());
    }
    else
    {
        assert(false);
    }
}
// 常量/变量声明中的ConstDef/VarDef
Value *SysyBuilder::visit(ASTDef &node)
{
    Type *var_type;
    auto current_type = context.type; //type在上一层（ASTDecl）处理的时候就存到context里了，因此可以直接获取
    if (current_type == TYPE_INT) // 确定常量/变量类型
    {
        var_type = module->get_int32_type();
    }
    else if (current_type == TYPE_FLOAT)
    {
        var_type = module->get_float_type();
    }
    else
    {
        std::cerr << "ASTDef" << std::endl;
        std::cerr << "Wrong variable type!" << std::endl;
        std::abort();
    }
    if (node.length == 0)// 非数组类型
    {
        if (scope.in_global())// 全局变量
        {
            if (node.initval_list == nullptr)// 无初始化值, 默认为0
            {
                Constant *initial_value;
                if (current_type == TYPE_INT)
                    initial_value = CONST_INT(0);
                else
                    initial_value = CONST_FP(0.);
                auto *var = GlobalVariable::create(node.id, module.get(), var_type, context.is_const, initial_value);//创建全局变量
                scope.push(node.id, var);
                if (node.is_const) // 对于常量，需要在全局作用域的const_map中记录其值
                    scope.push({node.id, std::vector<unsigned int>(0)}, {0});
            }
            else // 初始化不是0
            {
                node.initval_list->accept(*this);// 处理ASTInitval节点，以更新context中的val.i_val或者val.f_val
                Constant *initial_value;
                if (current_type == TYPE_INT)
                    initial_value = ConstantInt::get(int(context.val.i_val), module.get());
                else if (current_type == TYPE_FLOAT)
                    initial_value = ConstantFP::get(context.val.f_val, module.get());
                auto *var = GlobalVariable::create(node.id, module.get(), var_type, context.is_const, initial_value);
                scope.push(node.id, var);
                if (node.is_const)
                {
                    scope.push({node.id, std::vector<unsigned int>(0)}, context.val); //更新 const_map
                }
            }
        }
        else // 局部变量且非数组类型
        {
            //TODO:你需要补充局部变量的定义
            // 提示：需要考虑有无初始化值 
            //      初始化列表存储在node.initval_list 
            //      之后再给对应变量分配空间（create_alloca）
            //      如果有初始值还需要接着赋值（create_store）
            //      别忘记了把变量存进符号表（scope.push）

            //TODO--------------------------end
        }
    }
    else // 数组类型的变量
    {
        context.exp_lists.clear();// 清空上下文中用于表达维度的表达式列表
        unsigned int size = 1;
        for (auto exp : node.exp_lists)
        {
            context.exp_lists.push_back(*exp); // 将exp_lists顺序颠倒，比较后出现的数据在比较里边的层
        }
        ArrayType *array_type = nullptr;
        for (auto it = std::rbegin(context.exp_lists); it != std::rend(context.exp_lists); it++) //遍历每一维长度，构造多维ArrayType（最内层维度先处理）
        {
            it->accept(*this); // 求每一维度的长度
            size *= it->val.i_val; // 累乘计算总元素数
            int num = it->val.i_val; // 当前维度元素数
            if (array_type == nullptr)
                array_type = ArrayType::get(var_type, num); // 最内层
            else
                array_type = ArrayType::get(array_type, num); // 往外扩展一层
        }
        if (node.initval_list == nullptr) // 没有初始值
        {
            if (scope.in_global()) // 全局变量数组
            {
                Constant *zero = nullptr;
                if (current_type == TYPE_INT)
                    zero = ConstantZero::get(array_type, module.get());
                else
                    zero = ConstantZero::get(array_type, module.get());
                auto var = GlobalVariable::create(node.id, module.get(), array_type, node.is_const, zero);// 全都是零的数组
                scope.push(node.id, var);
            }
            else
            {
                auto var = builder->create_alloca(array_type); //局部变量数组分配空间
                scope.push(node.id, var);
            }
        }
        else // 数组变量 + 有初始化
        {
            if (scope.in_global())// 全局数组变量
            {
                auto ori_const = node.initval_list->is_const;
                node.initval_list->is_const = true; // 标记为常量初始化
                node.initval_list->accept(*this); // 访问初始值节点，填充 context.exp_uints
                node.initval_list->is_const = ori_const;
                auto initval = get_const_array(array_type, context.exp_uints); // 生成初始化数组所需的嵌套ConstantArray结构
                auto var = GlobalVariable::create(node.id, module.get(), array_type, node.is_const, initval); //创建全局变量数组
                scope.push(node.id, var);
                for (unsigned int i = 0; i < size; i++) 
                {
                    auto temp = i;
                    std::vector<unsigned int> now_dim;
                    for (auto dim = context.exp_lists.rbegin(); dim != context.exp_lists.rend(); ++dim) // 计算出每一维的索引（下标展开）
                    {
                        now_dim.insert(now_dim.begin(), temp % dim->val.i_val);
                        temp /= dim->val.i_val;
                    }
                    if (node.is_const)
                        scope.push({node.id, now_dim}, context.exp_uints[i]); // 如果是const，保存每一个数组下标对应的常量值到村到const_map
                }
            }
            // 局部数组变量，有初始化且非const
            else if (!node.is_const)
            {
                node.initval_list->accept(*this); //处理初始化列表
                auto initval = context.exp_vals; //获取处理好的初始化列表
                auto var = builder->create_alloca(array_type); //分配数组空间
                scope.push(node.id, var); //维护符号表
                Value *temp = var;
                int len = 1;
                for (auto i : context.exp_lists)// 计算数组长度（总元素数）
                {
                    len *= i.val.i_val;
                }
                // 初始化零值（使用 memset 调用），假设int a[10] = {1, 2};则后续部分都将自动初始化为0，而逐个赋0比较麻烦，这里就调用memset
                auto temp_dim = std::vector<Value *>(context.exp_lists.size() + 1, CONST_INT(0)); 
                temp = builder->create_gep(temp, temp_dim);
                if (current_type == TYPE_INT)
                {
                    auto mem_set = scope.find("memset_int");
                    auto call = builder->create_call(mem_set, {temp, CONST_INT(len)});
                    call->set_name("memset_int_call");
                }
                else
                {
                    auto mem_set = scope.find("memset_float");
                    auto call = builder->create_call(mem_set, {temp, CONST_INT(len)});
                    call->set_name("memset_float_call");
                }
                // 将初始值填入每一个具体位置
                for (auto val = 0u; val < initval.size(); val++)
                {
                    if (initval[val] == nullptr)
                        continue;
                    Value *iter = var;
                    auto temp = val;
                    std::vector<unsigned int> now_dim;
                    for (auto dim = context.exp_lists.rbegin(); dim != context.exp_lists.rend(); ++dim) // 计算当前元素的多维下标
                    {
                        now_dim.push_back(temp % dim->val.i_val);
                        temp /= dim->val.i_val;
                    }
                    std::vector<Value *> now_dim_v = {CONST_INT(0)};
                    for (auto dim = now_dim.rbegin(); dim != now_dim.rend(); ++dim)
                    {
                        now_dim_v.push_back(CONST_INT(int(*dim)));
                    }
                    iter = builder->create_gep(iter, now_dim_v);// 获取该下标的地址
                    // 类型转换：float转int，或int转float
                    if (current_type == TYPE_INT)
                    {
                        if (initval[val]->get_type()->is_float_type())
                            initval[val] = builder->create_fptosi(initval[val], INT32_T);
                    }
                    else if (current_type == TYPE_FLOAT)
                    {
                        if (initval[val]->get_type()->is_integer_type())
                            initval[val] = builder->create_sitofp(initval[val], FLOAT_T);
                    }
                    builder->create_store(initval[val], iter);// 存储初始化列表中的值到数组对应下标处
                }
            }
            else // const数组变量有初始化
            {
                //TODO:补全 const数组变量 + 有初始化 的处理逻辑
                //提示：可以仿照前面处理局部数组变量（有初始化且非const）的情况
                //     需要注意前面非const数组是直接builder->create_store(initval[val], iter);
                //     但const数组变量是需要将常量存入对应下标处的,e.g.  builder->create_store(ConstantInt::get(int(initval[val].i_val), module.get()), iter);
                //     最后将每个 now_dim 和常量值注册到 scope 中的 const_map 

                //TODO-------------------------end
            }
        }
    }
    return nullptr;
}
Value *SysyBuilder::visit(ASTInitVal &node)//初始化列表处理
{
    if (node.initval_list.size() == 0 && node.value != nullptr) // InitVal → Exp 形如int a = 5;中的=右边部分
    {
        auto value = node.value->accept(*this);//计算Exp的值
        if (context.type == TYPE_INT)
        {
            if (value->get_type()->is_float_type())
            {
                context.val.i_val = (int)context.val.f_val;
                if (!scope.in_global())
                {
                    value = builder->create_fptosi(value, INT32_T); //类型转换
                }
            }
        }
        else if (context.type == TYPE_FLOAT)
        {
            if (value->get_type()->is_integer_type())
            {
                context.val.f_val = (float)context.val.i_val;
                if (!scope.in_global())
                {
                    value = builder->create_sitofp(value, FLOAT_T);//类型转换
                }
            }
        }
        context.exp_vals = std::vector<Value *>(1, value); // 设置表达式值列表，后续用于数组等初始化处理
        if (node.is_const)
            context.exp_uints = std::vector<const_val>(1, context.val);// 如果是 const 初始值，还要保存常量值信息
    }
    else if (!node.is_const) //是初始化列表，且不是 const 情况（例如 int a[2] = {1, 2};）
    {
        auto exp_list = context.exp_lists;// 保存当前的维度信息
        assert(context.exp_lists[0].is_const);// 保证维度信息是常量
        unsigned int all_dim = 1;
        for (auto &exp : context.exp_lists) // 计算总大小（比如 int a[2][3] -> 6）
        {
            all_dim *= exp.val.i_val;
        }
        std::vector<Value *> exp_vals = std::vector<Value *>(0);// 存储所有初始化值
        auto now_dim = std::vector<unsigned int>(exp_list.size(), 0);// 当前维度计数器
        for (auto init : node.initval_list) // 遍历每一个初始化项
        {
            if (init->initval_list.size() == 0 && init->value != nullptr) //是表达式，不是嵌套的初始化列表
            {
                // Exp
                if (init->value != nullptr)
                {
                    auto value = init->value->accept(*this);
                    exp_vals.push_back(value);
                    now_dim.back()++;
                }
            }
            else //嵌套初始化列表（例如 {1, {2, 3}}）
            {
                // 更新多维数组的维度位置（计算“展开位置”）
                for (auto i = now_dim.size() - 1; i > 0; --i)
                {
                    now_dim[i - 1] += now_dim[i] / exp_list[i].val.i_val;
                    now_dim[i] %= exp_list[i].val.i_val;
                }

                context.exp_lists.erase(context.exp_lists.begin());// 修改上下文中的维度信息，递归处理子列表
                init->accept(*this);
                context.exp_lists = exp_list;// 恢复原维度

                for (auto &val : context.exp_vals)// 将递归结果加入当前列表
                {
                    exp_vals.push_back(val);
                }
                now_dim[0]++;
            }
        }
        exp_vals.resize(all_dim, nullptr);// 补齐初始化列表（数组可以部分初始化）
        context.exp_vals = exp_vals;
    }
    else //初始化列表，且是 const 初始化（例如 const int a[3] = {1, 2};）
    {
        auto exp_list = context.exp_lists;
        assert(context.exp_lists[0].is_const);
        unsigned int all_dim = 1;
        for (auto &exp : context.exp_lists)
        {
            all_dim *= exp.val.i_val;
        }
        std::vector<const_val> exp_uints = std::vector<const_val>(0);
        auto now_dim = std::vector<unsigned int>(exp_list.size(), 0);
        for (auto init : node.initval_list)
        {
            if (init->initval_list.size() == 0 && init->value != nullptr)
            {
                // Exp
                auto ori_const = init->value->is_const;
                init->value->is_const = true;
                auto value_exp = init->value->accept(*this);
                init->value->is_const = ori_const;
                auto value = init->value->val;
                if(value_exp->get_type()->is_integer_type()&&context.type==TYPE_FLOAT)//针对常量数组初始化的类型转换 
                {
                    value.f_val = static_cast<float>(value.i_val);
                }
                exp_uints.push_back(value);
                now_dim.back()++;
            }
            else
            {
                // initval
                for (auto i = now_dim.size() - 1; i > 0; --i)
                {
                    now_dim[i - 1] += now_dim[i] / exp_list[i].val.i_val;
                    now_dim[i] %= exp_list[i].val.i_val;
                }
                context.exp_lists.erase(context.exp_lists.begin());
                auto ori_const = init->is_const;
                init->is_const = true;
                init->accept(*this);
                init->is_const = ori_const;
                context.exp_lists = exp_list;

                for (auto &val : context.exp_uints)
                {
                    exp_uints.push_back(val);
                }
                now_dim[0]++;
            }
        }
        exp_uints.resize(all_dim, {0}); // 补齐未初始化的部分为0
        context.exp_uints = exp_uints;
    }
    return nullptr;
}

Value *SysyBuilder::visit(ASTParam &node)
{
    return nullptr;
}

Value *SysyBuilder::visit(ASTBlock &node)
{
    bool need_exit_scope = !context.pre_enter_scope;//针对函数block的特殊处理，保证函数参数和函数体在同一个作用域内
    if (context.pre_enter_scope) // 如果上文有进入作用域的标记，则不再进入新的作用域
        context.pre_enter_scope = false;
    else
        scope.enter();
    auto it_stmt = node.stmt_lists.begin();
    auto it_decl = node.decl_lists.begin();
    for (auto &it : node.list_type) // 遍历块中的元素，根据类型（声明或语句）分别处理
    {
        if (it == 0)// 0表示声明类型
        {
            (*it_decl)->accept(*this);
            it_decl++;
        }
        else // 1表示语句类型
        {
            (*it_stmt)->accept(*this);
            it_stmt++;
            if (builder->get_insert_block()->is_terminated()) // 如果当前基本块已经终止（语句为 return 或其他终止语句），则退出循环
                break;
        }
    }
    if (need_exit_scope)
    {
        scope.exit();
    }
    return nullptr;
}

Value *SysyBuilder::visit(ASTAssignStmt &node)//赋值语句
{
    auto *expr_result = node.expression->accept(*this);// 处理右侧表达式，获取其计算结果
    context.require_lvalue = true;// 设置标志，表示当前操作需要 lvalue（即左值），这是赋值操作所必需的
    auto *var_addr = node.var->accept(*this); // 处理左侧的变量，获取其地址（左值地址）
    if (var_addr->get_type()->get_pointer_element_type() != expr_result->get_type()) // 如果左侧变量的类型与右侧表达式的类型不同，则进行类型转换
    {
        if (expr_result->get_type() == INT32_T)
            expr_result = builder->create_sitofp(expr_result, FLOAT_T);
        else
            expr_result = builder->create_fptosi(expr_result, INT32_T);
    }
    builder->create_store(expr_result, var_addr);
    return expr_result;
}

Value *SysyBuilder::visit(ASTSelectionStmt &node)//if else语句
{   
    // 创建三个基本块：trueBB（条件成立时执行的块），falseBB（条件不成立时执行的块），nextBB（后续代码块）
    auto *trueBB = BasicBlock::create(module.get(), "", context.func);
    BasicBlock *falseBB{};
    if (node.else_stmt != nullptr)// 如果有 else 语句
        falseBB = BasicBlock::create(module.get(), "", context.func);
    auto *nextBB = BasicBlock::create(module.get(), "", context.func);
    // 入栈
    context.true_bb_stk.push(trueBB);
    if (node.else_stmt != nullptr)
        context.false_bb_stk.push(falseBB);
    else
        context.false_bb_stk.push(nextBB);
    // 访问条件表达式，计算条件判断结果
    node.cond->accept(*this);
    // trueBB 相关语句
    builder->set_insert_point(trueBB);//填充trueBB
    if (node.if_stmt != nullptr) // 如果有 if 语句（即 if(Cond) Stmt [ else Stmt ]中的第一个stmt ），继续解析，
        node.if_stmt->accept(*this);
    // 创建从 trueBB 跳转到 nextBB 的无条件跳转
    if (builder->get_insert_block()->empty()) // 如果当前插入块为空（没有指令）
    {
        if (builder->get_insert_block()->get_pre_basic_blocks().empty())// 如果没有前驱基本块
            builder->get_insert_block()->erase_from_parent();// 删除当前块
        else
        {
            if (not builder->get_insert_block()->is_terminated()) // 如果块没有终结指令（没有跳转或返回）
                builder->create_br(nextBB); // 创建跳转到 nextBB 的跳转指令
        }
    }
    else //当前块有指令
    {
        if (not builder->get_insert_block()->is_terminated())
            builder->create_br(nextBB);
    }
    if (node.else_stmt != nullptr) // 如果有 else 语句，处理 else 部分
    {
        builder->set_insert_point(falseBB);
        node.else_stmt->accept(*this);  // 处理 else 语句
        if (builder->get_insert_block()->empty()) // 如果当前插入块为空（没有指令），同上
        {
            if (builder->get_insert_block()->get_pre_basic_blocks().empty())
                builder->get_insert_block()->erase_from_parent();
            else
            {
                if (not builder->get_insert_block()->is_terminated())
                    builder->create_br(nextBB);
            }
        }
        else
        {
            if (not builder->get_insert_block()->is_terminated())
                builder->create_br(nextBB);
        }
    }
    builder->set_insert_point(nextBB);// 进入 nextBB，即条件判断后的代码块
    // 标号回填出栈
    context.true_bb_stk.pop();// 弹出 trueBB
    context.false_bb_stk.pop();// 弹出 falseBB（或 nextBB）
    return nullptr;
}

Value *SysyBuilder::visit(ASTIterationStmt &node) //while循环
{
    auto *condBB = BasicBlock::create(module.get(), "", context.func);
    if (not builder->get_insert_block()->is_terminated())
    {
        builder->create_br(condBB);
    }

    builder->set_insert_point(condBB);
    //TODO:你需要处理while循环的控制流部分
    //提示：
    //      可参考if else语句的实现 Value *SysyBuilder::visit(ASTSelectionStmt &node)
    //      不同的是while循环没有falseBB(条件错误时进入的基本块)，而是多了表示条件语句的condBB
    //      具体可回顾预热实验中while_generator.cpp的实现
    //      如果要处理while循环的条件语句，只需node.cond->accept(*this);
    //      处理循环体的话，只需node.stmt->accept(*this); 注意考虑循环体为空的情况(node.stmt == nullptr)

    //TODO-----------------------------------end
    return nullptr;
}

Value *SysyBuilder::visit(ASTBreak &node)//break语句
{
    auto *bb = context.next_bb_stk.top();
    auto *ret_val = builder->create_br(bb);//直接跳转到下一个基本块
    return ret_val;
}

Value *SysyBuilder::visit(ASTContinue &node)//continue语句
{
    //TODO:你需要处理continue语句
    //提示： 代码非常简单（只要2行）参考break语句的实现
    //      你只需要思考下一个基本块去哪获取（context.next_bb_stk？context.true_bb_stk？context.false_bb_stk？还是context.cond_bb_stk？）
    return nullptr;//这里是为了防止编译报错需要修改
    //TODO------------------------end
}

Value *SysyBuilder::visit(ASTReturnStmt &node)//return 语句
{
    if (node.expression == nullptr) //return ;的情况
    {
        builder->create_void_ret();// 创建返回类型为 void 的返回指令
    }
    else
    {
        auto *fun_ret_type = context.func->get_return_type(); // 获取函数的返回类型
        auto *ret_val = node.expression->accept(*this); // 访问返回语句中的表达式，计算其值
        if (fun_ret_type != ret_val->get_type()) // 如果返回值类型与函数的返回类型不匹配，则需要进行类型转换
        {
            if (fun_ret_type->is_integer_type())
            {
                ret_val = builder->create_fptosi(ret_val, INT32_T);
            }
            else
            {
                ret_val = builder->create_sitofp(ret_val, FLOAT_T);
            }
        }
        builder->create_ret(ret_val);
    }
    return nullptr;
}
// Exp -> AddExp
Value *SysyBuilder::visit(ASTExp &node)
{
    auto const_ori = node.is_const;
    if (node.is_const)
    {
        context.is_const_exp = true; // 如果当前节点是常量表达式，将上下文的 is_const_exp 设置为 true
    }
    auto *ret_val = node.add_exp->accept(*this); //处理AddExp
    if (ret_val != nullptr) // 如果返回值非空，则根据类型更新节点的常量值
    {
        if (ret_val->get_type()->is_integer_type())// 如果返回值类型是整数类型
        {
            node.val.i_val = context.val.i_val; // 将上下文中保存的整数值赋给节点的 i_val
        }
        else
            node.val.f_val = context.val.f_val; // 否则，如果返回值是浮点数类型，将上下文中保存的浮点值赋给节点的 f_val
    }
    node.is_const = const_ori;
    context.is_const_exp = false;
    return ret_val;
}
//  左值表达式 LVal → Ident { [ Exp ] }
Value *SysyBuilder::visit(ASTVar &node)
{
    // 在当前作用域找到var变量
    auto *var = scope.find(node.id);
    // 通过类型信息判断变量是否为整数、浮点数或指针类型
    auto is_int = var->get_type()->get_pointer_element_type()->is_integer_type();
    auto is_float = var->get_type()->get_pointer_element_type()->is_float_type();
    auto is_ptr = var->get_type()->get_pointer_element_type()->is_pointer_type();
    bool should_return_lvalue = context.require_lvalue; // 记录当前上下文是否要求返回左值
    Value *ret_val = nullptr;
    if (node.length == 0) // 普通变量（或多维数组的基地址）
    {
        if (should_return_lvalue) // 如果需要返回左值
        {
            ret_val = var; // 直接返回变量
            context.require_lvalue = false; // 重置左值要求
        }
        else
        {
            if (context.is_const_exp)// 对常量的引用
            {
                auto const_var = scope.find_const({node.id, {}});// 查找常量变量
                if (is_int) // 根据类型返回常量的值
                {
                    context.val.i_val = const_var.i_val; // 保存常量值
                    ret_val = CONST_INT((int)context.val.i_val); // 生成常量整数值
                }
                else if (is_float)
                {
                    context.val.f_val = const_var.f_val; // 保存常量值
                    ret_val = CONST_FP(context.val.f_val); // 生成常量浮点值
                }
            }
            else // 对变量的右值调用
            {
                if (is_int || is_float || is_ptr)
                {
                    ret_val = builder->create_load(var);
                }
                else
                {
                    ret_val = builder->create_gep(var, {CONST_INT(0), CONST_INT(0)});
                }
            }
        }
    }
    else // 如果变量是数组（有维度信息）
    {
        Value *temp_val = var; // 保存数组的基础地址
        if (!context.is_const_exp)
        {
            if (should_return_lvalue) 
            {
                context.require_lvalue = false;
            }
            if (is_int || is_float) // 对于整数或浮点类型
            {
                assert(node.array_lists.size() == 1); // 只有一个维度
                auto *val = node.array_lists[0]->accept(*this); // 访问数组维度表达式
                temp_val = builder->create_gep(temp_val, {val}); // 生成指针偏移
            }
            else 
            {
                if (temp_val->get_type()->get_pointer_element_type()->is_pointer_type())// 如果是指针类型，加载基础地址
                {
                    temp_val = builder->create_load(temp_val);
                    std::vector<Value *> args;
                    for (auto dim : node.array_lists)//处理每个维度
                    {
                        args.push_back(dim->accept(*this));
                    }
                    temp_val = builder->create_gep(temp_val, args);
                }
                else
                {
                    std::vector<Value *> args;
                    args.push_back(CONST_INT(0)); // 初始化偏移量
                    for (auto dim : node.array_lists)//处理每个维度
                    {
                        args.push_back(dim->accept(*this));
                    }
                    temp_val = builder->create_gep(temp_val, args);
                }
            }
            if (should_return_lvalue)
            {
                ret_val = temp_val;
                context.require_lvalue = false;
            }
            else
            {
                if (temp_val->get_type()->get_pointer_element_type()->is_array_type())// 如果数组元素类型是数组类型，生成一个指向元素的 GEP
                {
                    temp_val = builder->create_gep(temp_val, {CONST_INT(0), CONST_INT(0)});
                    ret_val = temp_val;
                }
                else
                    ret_val = builder->create_load(temp_val);
            }
        }
        else // 如果是常量表达式
        {
            if (should_return_lvalue)
            {
                context.require_lvalue = false;
            }
            std::vector<unsigned> num_list;
            for (auto dim : node.array_lists)
            {
                dim->accept(*this);
                num_list.push_back(context.val.i_val); // 将维度值存储在 num_list 中
            }
            auto const_var = scope.find_const({node.id, num_list});// 查找常量数组值
            if (is_int)
            {
                ret_val = CONST_INT((int)const_var.i_val);
                context.val.i_val = std::stoi(ret_val->print());
            }
            else if (is_float)
            {
                ret_val = CONST_FP(const_var.f_val);
                context.val.f_val = std::stof(ret_val->print());
            }
        }
    }
    return ret_val;
}

Value *SysyBuilder::visit(ASTNum &node)//Number
{
    if (node.type == TYPE_INT)
    {
        context.val.i_val = node.i_val; 
        return CONST_INT(node.i_val);
    }
    else
    {
        context.val.f_val = node.f_val; 
        return CONST_FP(node.f_val);
    }
}
//一元表达式 UnaryExp → PrimaryExp | Ident '(' [FuncRParams] ')'
//                   | UnaryOp UnaryExp
Value *SysyBuilder::visit(ASTUnaryExp &node)
{
    if (node.call_exp != nullptr)//函数调用 UnaryExp → Ident '(' [FuncRParams] ')'
    {
        Value *ret_val;
        if (!context.logic_op) //当前的UnaryExp处在一个逻辑反的上下文中
        {
            context.logic_op = true;//暂时设置 logic_op = true 避免函数调用的处理
            ret_val = node.call_exp->accept(*this);
            context.logic_op = false; //恢复逻辑反的上下文
        }
        else
            ret_val = node.call_exp->accept(*this);
        if (!context.logic_op)//处理逻辑反上下文
        {
            if (ret_val->get_type()->is_integer_type())
                ret_val = builder->create_icmp_eq(CONST_INT(0), ret_val);//返回反向布尔值
            else
                ret_val = builder->create_fcmp_eq(CONST_FP(0.), ret_val);
            ret_val = builder->create_zext(ret_val, INT32_T);
            context.logic_op = true;//消除了逻辑反上下文
        }
        return ret_val;
    }
    if (node.primary_exp != nullptr)//UnaryExp → PrimaryExp
    {
        Value *ret_val;
        if (!context.logic_op)
        {
            context.logic_op = true;
            ret_val = node.primary_exp->accept(*this);
            context.logic_op = false;
        }
        else
            ret_val = node.primary_exp->accept(*this);
        if (!context.logic_op)
        {
            if (ret_val->get_type()->is_integer_type())
                ret_val = builder->create_icmp_eq(CONST_INT(0), ret_val);
            else
                ret_val = builder->create_fcmp_eq(CONST_FP(0.), ret_val);
            ret_val = builder->create_zext(ret_val, INT32_T);
            context.logic_op = true;
        }
        return ret_val;
    }
    if (node.unary_exp != nullptr) //UnaryExp -> UnaryOp UnaryExp
    {
        if (node.unary_op == OP_MINUS)//UnaryOP -> -
        {
            Value *ret_val=nullptr;
            auto *exp_val = node.unary_exp->accept(*this);//处理后面的UnaryExp
            auto *type = exp_val->get_type();
            if (type->is_integer_type())// 如果是整数类型
            {
                context.val.i_val = -context.val.i_val;// 计算负值
                if (context.is_const_exp)
                    ret_val = CONST_INT((int)context.val.i_val);
                else if (scope.in_global())
                {
                    ret_val = CONST_INT((int)context.val.i_val);
                }
                else
                    ret_val = builder->create_isub(CONST_INT(0), exp_val);//非const的局部变量， 创建减法指令
            }
            else// 如果是浮点类型
            {
                context.val.f_val = -context.val.f_val;  // 计算负值
                if (context.is_const_exp)
                    ret_val = CONST_FP(context.val.f_val);
                else if (scope.in_global())
                    ret_val = CONST_FP(context.val.f_val);
                else
                {
                    ret_val = builder->create_fsub(CONST_FP(0.), exp_val);//非const的局部变量， 创建减法指令
                }
            }
            return ret_val;
        }
        else if (node.unary_op == OP_NOT)//UnaryOP -> !
        {
            context.logic_op = (!context.logic_op); // 将当前上下文的逻辑取反
        }
        else
        {
            ;//UnaryOP -> +
        }
        return node.unary_exp->accept(*this);
    }
    return nullptr;
}
//AddExp → MulExp | AddExp ('+' | '−') MulExp
Value *SysyBuilder::visit(ASTAddExp &node)
{
    if (node.add_exp == nullptr)//AddExp → MulExp
    {
        return node.mul_exp->accept(*this);//继续处理MulExp
    }
    //AddExp → AddExp ('+' | '−') MulExp
    const_val l_num, r_num;// 用于存储左右操作数的值
    auto *l_val = node.add_exp->accept(*this);//处理AddExp 左操作数
    if (l_val->get_type()->is_integer_type())
        l_num.i_val = context.val.i_val;
    else
        l_num.f_val = context.val.f_val;
    auto *r_val = node.mul_exp->accept(*this);//处理MulExp 右操作数
    if (r_val->get_type()->is_integer_type())
        r_num.i_val = context.val.i_val;
    else
        r_num.f_val = context.val.f_val;
    bool is_int = promote(&l_val, &r_val, &l_num, &r_num);// 调用 promote 函数进行类型提升，确保两个操作数的类型一致
    Value *ret_val = nullptr; // 存储最终的计算结果
    switch (node.op)
    {
    case OP_ADD://加法
        if (is_int)
        {
            context.val.i_val = l_num.i_val + r_num.i_val;// 计算整数相加的结果，方便上层获取
            if (context.is_const_exp)
                ret_val = CONST_INT((int)context.val.i_val);
            else
                ret_val = builder->create_iadd(l_val, r_val);
        }
        else
        {
            context.val.f_val = l_num.f_val + r_num.f_val; // 计算浮点数相加的结果，方便上层获取
            if (context.is_const_exp)
                ret_val = CONST_FP(context.val.f_val);
            else
                ret_val = builder->create_fadd(l_val, r_val);
        }
        break;
    case OP_SUB://减法
        if (is_int)
        {
            context.val.i_val = l_num.i_val - r_num.i_val;
            if (context.is_const_exp)
                ret_val = CONST_INT((int)context.val.i_val);
            else
                ret_val = builder->create_isub(l_val, r_val);
        }
        else
        {
            context.val.f_val = l_num.f_val - r_num.f_val;
            if (context.is_const_exp)
                ret_val = CONST_FP(context.val.f_val);
            else
                ret_val = builder->create_fsub(l_val, r_val);
        }
        break;
    }
    return ret_val;
}
// MulExp → UnaryExp | MulExp ('*' | '/' | '%') UnaryExp
Value *SysyBuilder::visit(ASTMulExp &node)
{
    if (node.mul_exp == nullptr)//MulExp → UnaryExp 
    {
        return node.unary_exp->accept(*this);
    }
    //MulExp → MulExp ('*' | '/' | '%') UnaryExp
    const_val l_num, r_num;//左右操作数
    auto *l_val = node.mul_exp->accept(*this);//处理MulExp 左操作数
    if (l_val->get_type()->is_integer_type())
        l_num.i_val = context.val.i_val;
    else
        l_num.f_val = context.val.f_val;
    auto *r_val = node.unary_exp->accept(*this);//处理UnaryExp 右操作数
    if (r_val->get_type()->is_integer_type())
        r_num.i_val = context.val.i_val;
    else
        r_num.f_val = context.val.f_val;
    bool is_int = promote(&l_val, &r_val, &l_num, &r_num);// 调用 promote 函数进行类型提升，确保两个操作数的类型一致
    Value *ret_val = nullptr;
    switch (node.op)
    {
    case OP_MUL:
        if (is_int)
        {
            context.val.i_val = l_num.i_val * r_num.i_val;
            if (context.is_const_exp)
                ret_val = CONST_INT((int)context.val.i_val);
            else
                ret_val = builder->create_imul(l_val, r_val);
        }
        else
        {
            context.val.f_val = l_num.f_val * r_num.f_val;
            if (context.is_const_exp)
                ret_val = CONST_FP(context.val.f_val);
            else
                ret_val = builder->create_fmul(l_val, r_val);
        }
        break;
    case OP_DIV:
        if (is_int)
        {
            if (r_num.i_val == 0) {
                std::abort();
            }
            context.val.i_val = l_num.i_val / r_num.i_val;
            if (context.is_const_exp)
                ret_val = CONST_INT((int)context.val.i_val);
            else
                ret_val = builder->create_isdiv(l_val, r_val);
        }
        else
        {
            context.val.f_val = l_num.f_val / r_num.f_val;
            if (context.is_const_exp)
                ret_val = CONST_FP(context.val.f_val);
            else
                ret_val = builder->create_fdiv(l_val, r_val);
        }
        break;
    case OP_MOD:
        if (is_int)
        {
            if (r_num.i_val == 0) {
                std::abort();
            }
            context.val.i_val = l_num.i_val % r_num.i_val;
            if (context.is_const_exp)
                ret_val = CONST_INT((int)context.val.i_val);
            else
                ret_val = builder->create_srem(l_val, r_val);
        }
        else
        {
            std::cerr << "浮点数没有取余操作（%）" << std::endl;
            std::abort();
        }
        break;
    }
    //TODO------------------------------end
    return ret_val;
}
// RelExp → AddExp | RelExp ('<' | '>' | '<=' | '>=') AddExp
Value *SysyBuilder::visit(ASTRelExp &node)
{
    if (node.rel_exp == nullptr)// RelExp → AddExp
    {
        auto *ret_val = node.add_exp->accept(*this);
        return ret_val;
    }
    // RelExp → RelExp ('<' | '>' | '<=' | '>=') AddExp
    const_val l_num, r_num;//存储左右操作数
    auto *l_val = node.rel_exp->accept(*this);//处理RelExp 左操作数
    if (l_val->get_type()->is_integer_type())
    {
        if (l_val->get_type()->is_int1_type())// 如果是布尔型（i1），则先进行零扩展为 i32
            l_val = builder->create_zext(l_val, INT32_T);
        l_num.i_val = context.val.i_val;// 从上下文中提取常量整型值（rel_exp的值）
    }
    else
    {
        l_num.f_val = context.val.f_val;
    }
    auto *r_val = node.add_exp->accept(*this);//处理AddExp 右操作数
    if (r_val->get_type()->is_integer_type())
    {
        if (r_val->get_type()->is_int1_type())// 如果是布尔型（i1），则先进行零扩展为 i32
            r_val = builder->create_zext(r_val, INT32_T);
        r_num.i_val = context.val.i_val;// 从上下文中提取常量整型值（add_exp的值）
    }
    else
        r_num.f_val = context.val.f_val;
    bool is_int = promote(&l_val, &r_val, &l_num, &r_num);//类型提升，转换成都是int或都是float
    Value *cmp; 
    switch (node.op)// 根据操作符生成对应的 IR 比较指令或常量计算
    {
    case OP_LT: // 小于 <
        if (is_int)//整型操作
        {
            context.val.i_val = (l_num.i_val < r_num.i_val); // 常量折叠：提前计算结果
            if (context.is_const_exp)  // 如果是常量表达式，构造常量；否则构造指令
                cmp = CONST_INT((int)context.val.i_val);
            else
                cmp = builder->create_icmp_lt(l_val, r_val);
        }
        else//浮点型型操作
        {
            context.val.i_val = (l_num.f_val < r_num.f_val);
            if (context.is_const_exp)
                cmp = CONST_FP(context.val.f_val);
            else
                cmp = builder->create_fcmp_lt(l_val, r_val);
        }
        break;
    case OP_LE:  // 小于等于 <=
        if (is_int)
        {
            context.val.i_val = (l_num.i_val <= r_num.i_val);
            if (context.is_const_exp)
                cmp = CONST_INT((int)context.val.i_val);
            else
                cmp = builder->create_icmp_le(l_val, r_val);
        }
        else
        {
            context.val.i_val = (l_num.f_val <= r_num.f_val);
            if (context.is_const_exp)
                cmp = CONST_FP(context.val.f_val);
            else
                cmp = builder->create_fcmp_le(l_val, r_val);
        }
        break;
    case OP_GT:// 大于 >
        if (is_int)
        {
            context.val.i_val = (l_num.i_val > r_num.i_val);
            if (context.is_const_exp)
                cmp = CONST_INT((int)context.val.i_val);
            else
                cmp = builder->create_icmp_gt(l_val, r_val);
        }
        else
        {
            context.val.i_val = (l_num.f_val > r_num.f_val);
            if (context.is_const_exp)
                cmp = CONST_FP(context.val.f_val);
            else
                cmp = builder->create_fcmp_gt(l_val, r_val);
        }
        break;
    case OP_GE: // 大于等于 >=
        if (is_int)
        {
            context.val.i_val = (l_num.i_val >= r_num.i_val);
            if (context.is_const_exp)
                cmp = CONST_INT((int)context.val.i_val);
            else
                cmp = builder->create_icmp_ge(l_val, r_val);
        }
        else
        {
            context.val.i_val = (l_num.f_val >= r_num.f_val);
            if (context.is_const_exp)
                cmp = CONST_FP(context.val.f_val);
            else
                cmp = builder->create_fcmp_ge(l_val, r_val);
        }
        break;
    }
    return cmp;
}
//EqExp → RelExp | EqExp ('==' | '!=') RelExp
Value *SysyBuilder::visit(ASTEqExp &node)
{
    if (node.eq_exp == nullptr)//EqExp → RelExp
    {
        auto *ret_val = node.rel_exp->accept(*this);
        return ret_val;
    }
    //EqExp → EqExp ('==' | '!=') RelExp
    const_val l_num, r_num;//存储左右操作数
    auto *l_val = node.eq_exp->accept(*this);//处理EqExp 左操作数
    if (l_val->get_type()->is_integer_type())
    {
        if (l_val->get_type()->is_int1_type())
            l_val = builder->create_zext(l_val, INT32_T);//零扩展（zext）为 int32（i32）
        l_num.i_val = context.val.i_val; // 从 context 中提取常量整数值（eq_exp的值）
    }
    else
        l_num.f_val = context.val.f_val;
    auto *r_val = node.rel_exp->accept(*this);//处理RelExp 右操作数
    if (r_val->get_type()->is_integer_type())
    {
        if (r_val->get_type()->is_int1_type())
            r_val = builder->create_zext(r_val, INT32_T);//零扩展（zext）为 int32（i32）
        r_num.i_val = context.val.i_val; // 从 context 中提取常量整数值（rel_exp的值）
    }
    else
        r_num.f_val = context.val.f_val;
    bool is_int = promote(&l_val, &r_val, &l_num, &r_num);//类型提升，转换成都是int或都是float
    Value *cmp;
    switch (node.op)// 根据当前等式操作类型（== 或 !=）生成 IR
    {
    case OP_EQ:// 等于 ==
        if (is_int)
        {
            context.val.i_val = (l_num.i_val == r_num.i_val);
            if (context.is_const_exp) // 如果是常量表达式，构造常量；否则构造指令
                cmp = CONST_INT((int)context.val.i_val);
            else
                cmp = builder->create_icmp_eq(l_val, r_val);
        }
        else
        {
            context.val.f_val = (l_num.f_val == r_num.f_val);
            if (context.is_const_exp)
                cmp = CONST_FP(context.val.f_val);
            else
                cmp = builder->create_fcmp_eq(l_val, r_val);
        }
        break;
    case OP_NEQ:// 不等于 !=
        if (is_int)
        {
            context.val.i_val = (l_num.i_val != r_num.i_val);
            if (context.is_const_exp)
                cmp = CONST_INT((int)context.val.i_val);
            else
                cmp = builder->create_icmp_ne(l_val, r_val);
        }
        else
        {
            context.val.i_val = (l_num.f_val != r_num.f_val);
            if (context.is_const_exp)
                cmp = CONST_FP(context.val.f_val);
            else
                cmp = builder->create_fcmp_ne(l_val, r_val);
        }
        break;
    }
    return cmp;
}
//LAndExp → EqExp | LAndExp '&&' EqExp
Value *SysyBuilder::visit(ASTLAndExp &node)
{
    Value *ret_val = nullptr;
    auto *true_bb = context.true_bb_stk.top();
    auto *false_bb = context.false_bb_stk.top();
    if (node.land_exp == nullptr)//LAndExp → EqExp
    {
        ret_val = node.eq_exp->accept(*this);
        if (ret_val->get_type()->is_int32_type())// 若返回值为 int32 类型，生成与 0 的比较，不等于 0 表示 true
            ret_val = builder->create_icmp_ne(CONST_INT(0), ret_val);
        else if (ret_val->get_type()->is_float_type()) // 若返回值为浮点类型，使用浮点不等于 0.0 来判断真假
            ret_val = builder->create_fcmp_ne(CONST_FP(0.), ret_val);
        ret_val = builder->create_cond_br(ret_val, true_bb, false_bb);
        return ret_val;// 返回的是分支跳转指令
    }
    // LAndExp -> LAndExp && EqExp
    auto *mid_bb = BasicBlock::create(module.get(), "", context.func);// 短路中间节点
    // 将中间块压入 true 分支栈，false 分支保持不变
    context.true_bb_stk.push(mid_bb);
    context.false_bb_stk.push(false_bb);
    // 递归处理左侧 LAndExp，逻辑上只要左边为 false 就可以直接跳 false_bb
    auto *l_val = node.land_exp->accept(*this);
    // 弹出栈，恢复现场
    context.true_bb_stk.pop();
    context.false_bb_stk.pop();
    if (not builder->get_insert_block()->is_terminated())// 如果左侧生成的 block 没有终止（还未跳转），则创建跳转指令
        builder->create_cond_br(l_val, mid_bb, false_bb);

    builder->set_insert_point(mid_bb);// 设置 IR 生成的插入点为中间块，表示左边 LAndExp为 true 的情况下进入右边判断
    auto *r_val = node.eq_exp->accept(*this);// 处理右侧 EqExp 
    if (r_val->get_type()->is_int32_type())
        r_val = builder->create_icmp_ne(CONST_INT(0), r_val);// 将 EqExp 的值转为布尔值：int32 类型不等于 0
    else if (r_val->get_type()->is_float_type())
        r_val = builder->create_fcmp_ne(CONST_FP(0.), r_val);// 或者浮点不等于 0.0
    builder->create_cond_br(r_val, true_bb, false_bb);// 若右边EqExp为 true 则跳转 true_bb，否则跳 false_bb
    return nullptr;
}
//Cond → LOrExp
//LOrExp → LAndExp | LOrExp '||' LAndExp
Value *SysyBuilder::visit(ASTLOrExp &node)//LOrExp是比LAndExp更上层的存在，因此创建跳转指令的工作只要交给LAndExp即可
{
    auto *true_bb = context.true_bb_stk.top();
    auto *false_bb = context.false_bb_stk.top();
    //LOrExp → LAndExp
    if (node.lor_exp == nullptr)// 这一层并没有||,但需要给下层传递truebb和falsebb
    {
        context.true_bb_stk.push(true_bb);
        context.false_bb_stk.push(false_bb);
        node.land_exp->accept(*this);
        context.true_bb_stk.pop();
        context.false_bb_stk.pop();
        return nullptr;
    }
    // 短路中间节点
    auto *mid_bb = BasicBlock::create(module.get(), "", context.func);
    // LOrExp -> LOrExp '||' LAndExp
    // 左侧布尔表达式LOrExp 
    context.true_bb_stk.push(true_bb);
    context.false_bb_stk.push(mid_bb);
    node.lor_exp->accept(*this);
    context.true_bb_stk.pop();
    context.false_bb_stk.pop();
    builder->set_insert_point(mid_bb);
    // 右侧布尔表达式LAndExp
    context.true_bb_stk.push(true_bb);
    context.false_bb_stk.push(false_bb);
    node.land_exp->accept(*this);
    context.true_bb_stk.pop();
    context.false_bb_stk.pop();
    return nullptr;
}

Value *SysyBuilder::visit(ASTCall &node)//函数调用
{
    auto *func = dynamic_cast<Function *>(scope.find(node.id));//从符号表中查找调用的函数名 node.id 并转型为 Function* 类型
    std::vector<Value *> args;//存放函数实参
    // 获取函数参数类型的起始迭代器，用于逐个参数与传入实参类型对比并处理类型转换
    auto param_type = func->get_function_type()->param_begin();
    for (auto &arg : node.args)//遍历函数调用的实参表达式列表
    { //FuncRParams → Exp { ',' Exp }
        auto *arg_val = arg->accept(*this);//处理每个Exp
        // 如果不是数组类型，并且当前参数类型与函数定义中的形参类型不匹配，则需要进行类型转换
        if (!arg_val->get_type()->is_array_type() && *param_type != arg_val->get_type())
        {
            if (arg_val->get_type()->is_pointer_type())//如果实参是指针类型（可能是传数组/指针参数），则直接加入 args，跳过类型转换
            {
                args.push_back(arg_val);
                param_type++;
                continue;
            }
            //整型浮点型类型转换
            if (arg_val->get_type()->is_integer_type())
                arg_val = builder->create_sitofp(arg_val, FLOAT_T);
            else
                arg_val = builder->create_fptosi(arg_val, INT32_T);
        }
        args.push_back(arg_val);//把处理后的实参 IR 值加入参数列表
        param_type++;//推进到下一个函数参数类型
    }
    auto *ret_val = builder->create_call(static_cast<Function *>(func), args);

    return ret_val;
}
