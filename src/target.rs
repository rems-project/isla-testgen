pub trait Target {
    fn regs() -> Vec<String>;
}

pub struct Aarch64 {}

impl Target for Aarch64 {
    fn regs() -> Vec<String> {
        let mut regs: Vec<String> = (0..31).map(|r| format!("R{}", r)).collect();
        let mut other_regs = ["SP_EL0", "SP_EL1", "SP_EL2", "SP_EL3"].iter().map(|r| r.to_string()).collect();
        regs.append(&mut other_regs);
        regs
    }
}


pub struct Morello {}

impl Target for Morello {
    fn regs() -> Vec<String> {
        let mut regs: Vec<String> = (0..31).map(|r| format!("_R{:02}", r)).collect();
        let mut other_regs = ["SP_EL0", "SP_EL1", "SP_EL2", "SP_EL3"].iter().map(|r| r.to_string()).collect();
        regs.append(&mut other_regs);
        regs
    }
}
