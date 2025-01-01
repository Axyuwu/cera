use cera_bytecode::{
    self,
    execution_engine::{EngineResult, EngineStack},
};

fn main() {
    let mut stack = EngineStack::<0x40>::new();
    dbg!(&stack);
    stack.push_value(&621u64).unwrap();
    dbg!(&stack);
    stack
        .push_stack_frame(0xF0F0F0F0u32, |proxy, _| -> EngineResult<()> {
            proxy.push_to_next(0..8)?;
            Ok(())
        })
        .unwrap()
        .unwrap();
    dbg!(&stack);
    stack.push_value(&0x5FF3ADu32).unwrap();
    dbg!(&stack);
    let (_, res): (u32, _) = unsafe { stack.pop_stack_frame([8..12].into_iter()) };
    res.unwrap();
    dbg!(&stack);
}
