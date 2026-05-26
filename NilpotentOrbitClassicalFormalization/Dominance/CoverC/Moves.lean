import NilpotentOrbitClassicalFormalization.Dominance.Classical

/-!
# C-type cover moves

This file states the five local row patterns appearing in the C-type dominance
cover characterization.
-/

namespace Nat.Partition

def rowEqExcept₂ {N : ℕ} (lam mu : Nat.Partition N) (a b : ℕ) : Prop :=
  ∀ k : ℕ, k ≠ a → k ≠ b → mu.rowLen k = lam.rowLen k

def rowEqExcept₃ {N : ℕ} (lam mu : Nat.Partition N) (a b c : ℕ) : Prop :=
  ∀ k : ℕ, k ≠ a → k ≠ b → k ≠ c → mu.rowLen k = lam.rowLen k

def rowEqExcept₄ {N : ℕ} (lam mu : Nat.Partition N) (a b c d : ℕ) : Prop :=
  ∀ k : ℕ, k ≠ a → k ≠ b → k ≠ c → k ≠ d → mu.rowLen k = lam.rowLen k

/-- `(2p, 2q) → (2p - 1, 2q + 1)` with `p = q + 1`. -/
def IsCMove₁ {N : ℕ} (lam mu : Nat.Partition N) : Prop :=
  ∃ s t : ℕ, s < t ∧
    Even (lam.rowLen s) ∧ Even (lam.rowLen t) ∧
    lam.rowLen s = lam.rowLen t + 2 ∧
    lam.rowLen s = mu.rowLen s + 1 ∧
    mu.rowLen t = lam.rowLen t + 1 ∧
    rowEqExcept₂ lam mu s t

/-- `(2p, 2q) → (2p - 2, 2q + 2)` with `p ≥ q + 2`. -/
def IsCMove₂ {N : ℕ} (lam mu : Nat.Partition N) : Prop :=
  ∃ s t : ℕ, s < t ∧
    Even (lam.rowLen s) ∧ Even (lam.rowLen t) ∧
    lam.rowLen t + 4 ≤ lam.rowLen s ∧
    lam.rowLen s = mu.rowLen s + 2 ∧
    mu.rowLen t = lam.rowLen t + 2 ∧
    rowEqExcept₂ lam mu s t

/-- `(2p, q, q) → (2p - 2, q + 1, q + 1)` with `q` odd. -/
def IsCMove₃ {N : ℕ} (lam mu : Nat.Partition N) : Prop :=
  ∃ s t : ℕ, s < t ∧
    Even (lam.rowLen s) ∧ Odd (lam.rowLen t) ∧
    lam.rowLen t = lam.rowLen (t + 1) ∧
    lam.rowLen t + 3 ≤ lam.rowLen s ∧
    lam.rowLen s = mu.rowLen s + 2 ∧
    mu.rowLen t = lam.rowLen t + 1 ∧
    mu.rowLen (t + 1) = lam.rowLen (t + 1) + 1 ∧
    rowEqExcept₃ lam mu s t (t + 1)

/-- `(p, p, 2q) → (p - 1, p - 1, 2q + 2)` with `p` odd. -/
def IsCMove₄ {N : ℕ} (lam mu : Nat.Partition N) : Prop :=
  ∃ s t : ℕ, s + 1 < t ∧
    Odd (lam.rowLen s) ∧
    lam.rowLen s = lam.rowLen (s + 1) ∧
    Even (lam.rowLen t) ∧
    lam.rowLen t + 3 ≤ lam.rowLen s ∧
    lam.rowLen s = mu.rowLen s + 1 ∧
    lam.rowLen (s + 1) = mu.rowLen (s + 1) + 1 ∧
    mu.rowLen t = lam.rowLen t + 2 ∧
    rowEqExcept₃ lam mu s (s + 1) t

/-- `(p, p, q, q) → (p - 1, p - 1, q + 1, q + 1)` with `p`, `q` odd. -/
def IsCMove₅ {N : ℕ} (lam mu : Nat.Partition N) : Prop :=
  ∃ s t : ℕ, s + 1 < t ∧
    Odd (lam.rowLen s) ∧
    lam.rowLen s = lam.rowLen (s + 1) ∧
    Odd (lam.rowLen t) ∧
    lam.rowLen t = lam.rowLen (t + 1) ∧
    lam.rowLen t + 2 ≤ lam.rowLen s ∧
    lam.rowLen s = mu.rowLen s + 1 ∧
    lam.rowLen (s + 1) = mu.rowLen (s + 1) + 1 ∧
    mu.rowLen t = lam.rowLen t + 1 ∧
    mu.rowLen (t + 1) = lam.rowLen (t + 1) + 1 ∧
    rowEqExcept₄ lam mu s (s + 1) t (t + 1)

def IsCMove {n : ℕ} (lam mu : CPartition n) : Prop :=
  IsCMove₁ (lam : Nat.Partition (2 * n)) mu ∨
    IsCMove₂ (lam : Nat.Partition (2 * n)) mu ∨
    IsCMove₃ (lam : Nat.Partition (2 * n)) mu ∨
    IsCMove₄ (lam : Nat.Partition (2 * n)) mu ∨
    IsCMove₅ (lam : Nat.Partition (2 * n)) mu

end Nat.Partition
