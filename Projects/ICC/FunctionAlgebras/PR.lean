import Notation

inductive PR : ℕ → Type u where
  | zero (k : ℕ) : PR k
  | succ : PR 1
  | pi (n : ℕ) (m : Fin n) : PR n
  | comp (m k : ℕ) (g : Fin k → PR m) (h : PR k) : PR m

def PR.elim (f : PR a) : (Fin a → ℕ) → ℕ := match f with
  | PR.zero k => λ_ ↦ 0
  | PR.succ => λx ↦ Nat.succ (x 0)
  | PR.pi _ m => λx ↦ x m
  | PR.comp _ _ g h => h.elim ∘ (λx ↦ λy ↦ (g y).elim x)
