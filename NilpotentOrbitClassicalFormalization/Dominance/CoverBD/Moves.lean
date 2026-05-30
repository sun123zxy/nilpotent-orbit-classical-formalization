import NilpotentOrbitClassicalFormalization.Dominance.Classical

/-!
# B/D-type cover moves

This file states the five local row patterns appearing in the B/D-type
dominance cover characterization.
-/

namespace Nat.Partition

/-- `(2p + 1, 2q + 1) → (2p, 2q + 2)` with `p = q + 1`. -/
def IsBDMove₁ {N : ℕ} (lam mu : Nat.Partition N) : Prop :=
  ∃ s t : ℕ, s < t ∧
    Odd (lam.rowLen s) ∧ Odd (lam.rowLen t) ∧
    lam.rowLen s = lam.rowLen t + 2 ∧
    lam.rowLen s = mu.rowLen s + 1 ∧
    mu.rowLen t = lam.rowLen t + 1 ∧
    rowEqExcept₂ lam mu s t

/-- `(2p + 1, 2q + 1) → (2p - 1, 2q + 3)` with `p ≥ q + 2`. -/
def IsBDMove₂ {N : ℕ} (lam mu : Nat.Partition N) : Prop :=
  ∃ s t : ℕ, s < t ∧
    Odd (lam.rowLen s) ∧ Odd (lam.rowLen t) ∧
    lam.rowLen t + 4 ≤ lam.rowLen s ∧
    lam.rowLen s = mu.rowLen s + 2 ∧
    mu.rowLen t = lam.rowLen t + 2 ∧
    rowEqExcept₂ lam mu s t

/-- `(2p + 1, q, q) → (2p - 1, q + 1, q + 1)` with `q` even. -/
def IsBDMove₃ {N : ℕ} (lam mu : Nat.Partition N) : Prop :=
  ∃ s t : ℕ, s < t ∧
    Odd (lam.rowLen s) ∧ Even (lam.rowLen t) ∧
    lam.rowLen t = lam.rowLen (t + 1) ∧
    lam.rowLen t + 3 ≤ lam.rowLen s ∧
    lam.rowLen s = mu.rowLen s + 2 ∧
    mu.rowLen t = lam.rowLen t + 1 ∧
    mu.rowLen (t + 1) = lam.rowLen (t + 1) + 1 ∧
    rowEqExcept₃ lam mu s t (t + 1)

/-- `(p, p, 2q + 1) → (p - 1, p - 1, 2q + 3)` with `p` even. -/
def IsBDMove₄ {N : ℕ} (lam mu : Nat.Partition N) : Prop :=
  ∃ s t : ℕ, s + 1 < t ∧
    Even (lam.rowLen s) ∧
    lam.rowLen s = lam.rowLen (s + 1) ∧
    Odd (lam.rowLen t) ∧
    lam.rowLen t + 3 ≤ lam.rowLen s ∧
    lam.rowLen s = mu.rowLen s + 1 ∧
    lam.rowLen (s + 1) = mu.rowLen (s + 1) + 1 ∧
    mu.rowLen t = lam.rowLen t + 2 ∧
    rowEqExcept₃ lam mu s (s + 1) t

/-- `(p, p, q, q) → (p - 1, p - 1, q + 1, q + 1)` with `p`, `q` even. -/
def IsBDMove₅ {N : ℕ} (lam mu : Nat.Partition N) : Prop :=
  ∃ s t : ℕ, s + 1 < t ∧
    Even (lam.rowLen s) ∧
    lam.rowLen s = lam.rowLen (s + 1) ∧
    Even (lam.rowLen t) ∧
    lam.rowLen t = lam.rowLen (t + 1) ∧
    lam.rowLen t + 2 ≤ lam.rowLen s ∧
    lam.rowLen s = mu.rowLen s + 1 ∧
    lam.rowLen (s + 1) = mu.rowLen (s + 1) + 1 ∧
    mu.rowLen t = lam.rowLen t + 1 ∧
    mu.rowLen (t + 1) = lam.rowLen (t + 1) + 1 ∧
    rowEqExcept₄ lam mu s (s + 1) t (t + 1)

def IsBDMove {N : ℕ} (lam mu : BDPartition N) : Prop :=
  IsBDMove₁ (lam : Nat.Partition N) mu ∨
    IsBDMove₂ (lam : Nat.Partition N) mu ∨
    IsBDMove₃ (lam : Nat.Partition N) mu ∨
    IsBDMove₄ (lam : Nat.Partition N) mu ∨
    IsBDMove₅ (lam : Nat.Partition N) mu

end Nat.Partition
