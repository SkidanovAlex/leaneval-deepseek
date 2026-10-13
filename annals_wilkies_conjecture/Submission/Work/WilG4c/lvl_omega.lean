/-
  WilG4c — the levels of a cell are `Ω`-definable, with a sharp format.

  `lvl p N κ m` is the projection of `κ ⊆ ℝ^{p+N}` to the first `p+m` coordinates, so it is
  obtained from `κ` by iterating the projection axiom `SOMin.proj` exactly `N - m` times.
  Each projection step adds one to the format and keeps the degree, hence

      `κ ∈ S.Ω F D (p+N)  →  lvl p N κ m ∈ S.Ω (F + (N - m)) D (p + m)`   (`m ≤ N`).

  The proof is the descending induction on `m` from `N` (where `lvl p N κ N = κ`) using
  `lvl_succ`, `lvl p N κ m = projLast (lvl p N κ (m+1))`.  Note that the level argument in
  the induction hypothesis must be a *syntactic* `m+1`: the instance of `SOMin.proj` for the
  set `lvl p N κ (m+1) ⊆ ℝ^{p+(m+1)}` is found because `p + (m+1)` reduces to
  `Nat.succ (p+m)`.
-/
import Mathlib
import Submission.Work.WilG4c.CellParamDefs

set_option autoImplicit false

namespace Work.WilG4c

theorem lvl_omega (S : WilkiesDesign.SOMin) (p N : ℕ) :
    ∀ (F D : ℕ) (κ : Set (Fin (p+N) → ℝ)) (m : ℕ), m ≤ N →
      κ ∈ S.Ω F D (p+N) → Work.WilG4c.lvl p N κ m ∈ S.Ω (F + (N - m)) D (p + m) := by
  intro F D κ m hm hκ
  -- One projection step: a level `m+1` bound yields the level `m` bound, format `+1`.
  have step : ∀ m < N, lvl p N κ (m+1) ∈ S.Ω (F + (N - (m+1))) D (p + (m+1)) →
      lvl p N κ m ∈ S.Ω (F + (N - m)) D (p + m) := by
    intro m hm' h
    have h' := S.proj h
    have heq : F + (N - (m+1)) + 1 = F + (N - m) := by omega
    rw [lvl_succ κ hm']
    exact heq ▸ h'
  -- Descending induction on `N - m` (written as a recursion on the difference, which keeps
  -- the level argument of the induction hypothesis in the shape `m+1`).
  have key : ∀ k, ∀ m, N - m = k → m ≤ N →
      lvl p N κ m ∈ S.Ω (F + (N - m)) D (p + m) := by
    intro k
    induction k with
    | zero =>
      -- `N - m = 0` with `m ≤ N` forces `m = N`, where `lvl p N κ N = κ`.
      intro m hmk hmN
      have hm' : m = N := by omega
      subst hm'
      simpa [lvl_self, Nat.sub_self] using hκ
    | succ k ih =>
      intro m hmk hmN
      have hmN' : m < N := by omega
      have hmk' : N - (m+1) = k := by omega
      exact step m hmN' (ih (m+1) hmk' (by omega))
  exact key (N - m) m rfl hm

end Work.WilG4c
