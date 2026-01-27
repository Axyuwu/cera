enum Type {}

enum ErrorHandling {
    HostUB,
    ProgramUB,
    ArithSaturating,
    ArithOverflowing,
    DivideToZero,
}

enum Constant {}

enum Expression {
    Mul {},
}

enum BlockID {
    Entry,
    Branch(usize),
    Exit,
}

enum ValueID {
    Constant(usize),
    Expression(usize),
    Pred(usize),
}

struct EntryBlock {
    args: Vec<Type>,
    succ: BlockID,
}

struct PredBlock {
    block_ids: Vec<BlockID>,
    value_ids_flat: Vec<ValueID>,
}

enum SuccBlock {
    Unconditional(BlockID),
    Conditional {
        condition: ValueID,
        table: Vec<BlockID>,
    },
}

struct BranchBlock {
    pred: PredBlock,
    expressions: Vec<Expression>,
    succ: SuccBlock,
}

struct ExitBlock {
    res: PredBlock,
}

struct Function {
    entry: EntryBlock,
    blocks: Vec<BranchBlock>,
    exit: ExitBlock,
}

struct CodegenUnit {
    constants: Vec<Constant>,
    functions: Vec<Function>,
}

struct LinkableBlob {}
