import LspExperiments.Lsp

def hello := "world"

attribute [symm] Eq.symm

theorem foo (a : Nat) {b : Nat} : a + b = b + a := by
  have : 1 = 1 ∧ 2 = 2 := by
    constructor
    · symm
      rfl
    · symm
      rfl
  symm
  apply Nat.add_comm


