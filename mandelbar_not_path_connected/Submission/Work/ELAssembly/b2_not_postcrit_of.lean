import Mathlib
import Submission.Work.ELAssembly.Defs
import Submission.Work.ELNest.Qp_shift
import Submission.Work.Landing.Rays

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedVariables false

/-!
# `b₂` is not postcritical (`Work.ELAssembly.AssemblyInputs.b2_not_postcrit`)

The branch point `b₂` of the equator-leak argument is a landing point of the ray of angle
`22/63` and a **fixed point of the holomorphic second return map** `Tsq c = (T_c)^[2]` of the
antiholomorphic quadratic `T_c(z) = z̄² + c`.  The critical orbit of `T_c` converges to the
parabolic point `z₁` (along the subsequence of index `5n`, i.e. under `F c = (Tsq c)^[5]`) and
never equals `z₁`.

The claim `b₂_not_postcrit` underlying the assembly is that this excludes the critical orbit
from ever hitting `b₂`:

`∀ n, (T_c)^[n] 0 ≠ b₂`.

The mechanism is purely combinatorial.  Write `f = Tsq c` and `g = T_c`; then `f = g^[2]` and
`g 0 = c` (so that `f^[n] c = g^[2n+1] 0` for every `n`).  If `g^[n] 0 = b₂`, then for every `k`
with `10k+1 ≥ n` we have

`f^[5k] c = g^[10k+1] 0 = g^[10k+1-n] b₂`,

and since `g^[2] b₂ = f b₂ = b₂`, the `g`-orbit of `b₂` is the two-cycle `b₂, g b₂`,
`b₂, g b₂, …`.  **Both** points `b₂` and `g b₂` are fixed by `f` (for the second:
`f (g b₂) = g^[2] (g b₂) = g^[3] b₂ = g (g^[2] b₂) = g b₂`).  Hence the subsequence
`k ↦ f^[5k] c` is *eventually constant*, so its limit is one of its values; but the
hypothesis says the limit `z₁` is not a value of the subsequence.  Contradiction.

The hypotheses `hN`, `hzero` and `hlands` (the orbit portrait and the landing of the angle
`22/63` at `b₂`) are not needed for this step: they are what *establishes* `hfix`/`b₂` in the
caller, and are kept in the statement so that the caller may pass them along.
-/

namespace Work.ELAssembly

open LeanEval.ComplexAnalysis (Tantibar)

/-- If `b` is a fixed point of `g^[2]`, then the `g`-orbit of `b` is the two-cycle `b, g b`:
every iterate of `b` is `b` or `g b`. -/
lemma b2_aux_iterate_or {g : ℂ → ℂ} {b : ℂ} (hbg : g^[2] b = b) :
    ∀ n : ℕ, g^[n] b = b ∨ g^[n] b = g b := by
  intro n
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
    rcases ih with h | h
    · exact Or.inr (by rw [Function.iterate_succ_apply', h])
    · exact Or.inl (by rw [Function.iterate_succ_apply', h]; exact hbg)

/-- **The combinatorial core of `b₂` non-postcritical.**  If `f = g^[2]`, `g 0 = c`, `b` is
fixed by `f`, and the `f`-orbit of `c` sampled at indices `5n` converges to `z` without ever
equalling `z`, then no `g`-iterate of `0` equals `b`. -/
lemma b2_aux_not_iterate {f g : ℂ → ℂ} {c z b : ℂ}
    (hfg : f = g^[2]) (hg0 : g 0 = c)
    (hcrit : Filter.Tendsto (fun n : ℕ => f^[5 * n] c) Filter.atTop (nhds z) ∧
      ∀ n : ℕ, f^[5 * n] c ≠ z)
    (hb : f b = b) : ∀ n : ℕ, g^[n] 0 ≠ b := by
  have hbg : g^[2] b = b := by rw [← hfg]; exact hb
  have hgbfix : f (g b) = g b := by
    rw [hfg]
    have h1 : g^[2] (g b) = g^[3] b := (Function.iterate_add_apply g 2 1 b).symm
    have h2 : g^[3] b = g b := by
      rw [show (3 : ℕ) = 1 + 2 from rfl, Function.iterate_add_apply, hbg, Function.iterate_one]
    rw [h1, h2]
  intro n hn
  -- `f^[5n] c = g^[10n+1] 0`, because `f^[j] = g^[2j]` and `g 0 = c`
  have hkey : f^[5 * n] c = g^[10 * n + 1] 0 := by
    rw [hfg, ← Function.iterate_mul]
    calc g^[2 * (5 * n)] c
        = g^[2 * (5 * n)] (g 0) := by rw [hg0]
      _ = g^[2 * (5 * n) + 1] 0 := (Function.iterate_add_apply g (2 * (5 * n)) 1 0).symm
      _ = g^[10 * n + 1] 0 := by rw [show 2 * (5 * n) + 1 = 10 * n + 1 from by ring]
  -- and `g^[10n+1] 0 = g^[9n+1] b₂`, since `10n+1 = (9n+1) + n` and `g^[n] 0 = b₂`
  have hstep : g^[10 * n + 1] 0 = g^[9 * n + 1] b := by
    rw [show 10 * n + 1 = (9 * n + 1) + n from by ring, Function.iterate_add_apply, hn]
  -- the value of the subsequence at `n` is `b₂` or `g b₂`
  have hval : f^[5 * n] c = g b ∨ f^[5 * n] c = b := by
    rw [hkey, hstep]
    rcases b2_aux_iterate_or hbg (9 * n) with h | h
    · left; rw [Function.iterate_succ_apply', h]
    · right; rw [Function.iterate_succ_apply', h]; exact hbg
  -- `f` fixes both `b₂` and `g b₂`, hence fixes `f^[5n] c`
  have hfixc : f (f^[5 * n] c) = f^[5 * n] c := by
    rcases hval with h | h
    · rw [h]; exact hgbfix
    · rw [h]; exact hb
  -- so the subsequence is eventually constant
  have htail : ∀ j : ℕ, n ≤ j → f^[5 * j] c = f^[5 * n] c := by
    intro j hj
    have h5 : 5 * n ≤ 5 * j := Nat.mul_le_mul_left 5 hj
    have h1 : f^[5 * j] c = f^[5 * j - 5 * n + 5 * n] c := by rw [Nat.sub_add_cancel h5]
    rw [h1, Function.iterate_add_apply, Function.iterate_fixed hfixc]
  have hconst : Filter.Tendsto (fun j : ℕ => f^[5 * j] c) Filter.atTop (nhds (f^[5 * n] c)) :=
    tendsto_atTop_of_eventually_const (u := fun j : ℕ => f^[5 * j] c) (x := f^[5 * n] c)
      (i₀ := n) (fun i hi => htail i hi)
  -- the limit is both `z` and the value `f^[5n] c`, which is excluded
  exact hcrit.2 n (tendsto_nhds_unique hcrit.1 hconst).symm

theorem b2_not_postcrit_of {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {z₁ b2 : ℂ} (hzero : ∀ θ : ℝ, θ ∈ Set.Ico 0 1 → (Work.EL.LandsN hN θ z₁ ↔ θ = Work.EL.alpha1 ∨ θ = Work.EL.alpha2)) (hcrit : Filter.Tendsto (fun n : ℕ => (Work.Landing.Tsq c)^[5 * n] c) Filter.atTop (nhds z₁) ∧ ∀ n : ℕ, (Work.Landing.Tsq c)^[5 * n] c ≠ z₁) (hfix : Work.Landing.Tsq c b2 = b2) (hlands : Work.EL.LandsN hN (22 / 63) b2) : ∀ n : ℕ, (LeanEval.ComplexAnalysis.Tantibar c)^[n] 0 ≠ b2 := by
  exact b2_aux_not_iterate (f := Work.Landing.Tsq c) (g := LeanEval.ComplexAnalysis.Tantibar c)
    (z := z₁) (b := b2) (Work.EL.Tsq_eq_comp c) (by simp [LeanEval.ComplexAnalysis.Tantibar])
    hcrit hfix

end Work.ELAssembly
