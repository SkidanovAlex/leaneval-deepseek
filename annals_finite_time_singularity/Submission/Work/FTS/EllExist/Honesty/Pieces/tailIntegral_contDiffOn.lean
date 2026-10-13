import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Submission.Work.FTS.PhiStar.Radial.hasDerivAt_integral_Ioi
import Submission.Work.FTS.PhiStar.Radial.integrableOn_Ioi_of_Ioi_Ioo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist.Honesty.Pieces

open scoped ContDiff

/-- The tail integral `u ↦ ∫ t in (u,∞), f t` of a function continuous and integrable on a
right neighbourhood of `z > 0` is differentiable at `z` with derivative `-f z`. -/
theorem tailIntegral_hasDerivAt {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ioi 0))
    (hint : MeasureTheory.IntegrableOn f (Set.Ioi 1)) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun u => ∫ t in Set.Ioi u, f t) (-(f z)) z := by
  have hhalf : (0 : ℝ) < z / 2 := by linarith
  have hsub : Set.Ioi (z / 2) ⊆ Set.Ioi (0 : ℝ) := fun x hx => by
    simp only [Set.mem_Ioi] at hx ⊢
    linarith
  exact Work.FTS.PhiStar.Radial.hasDerivAt_integral_Ioi (by linarith) (hcont.mono hsub)
    (Work.FTS.PhiStar.Radial.integrableOn_Ioi_of_Ioi_Ioo hhalf hcont hint)

/-- The derivative of the tail integral is `-f` on `(0,∞)`. -/
theorem tailIntegral_deriv_eq {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ioi 0))
    (hint : MeasureTheory.IntegrableOn f (Set.Ioi 1)) {z : ℝ} (hz : 0 < z) :
    deriv (fun u => ∫ t in Set.Ioi u, f t) z = -(f z) :=
  (tailIntegral_hasDerivAt hcont hint hz).deriv

/-- **One step of the induction**: if `f` is `C^m` on `(0,∞)` (with `m` a finite order) and
integrable on `(1,∞)`, then its tail integral is `C^{m+1}` on `(0,∞)`. -/
theorem tailIntegral_contDiffOn_succ {m : ℕ∞ω} (hm : m ≠ ⊤) {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Ioi 0)) (hint : MeasureTheory.IntegrableOn f (Set.Ioi 1))
    (hd : ContDiffOn ℝ m (fun z => -(f z)) (Set.Ioi 0)) :
    ContDiffOn ℝ (m + 1) (fun z => ∫ t in Set.Ioi z, f t) (Set.Ioi 0) := by
  refine (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ)
    (f := fun u => ∫ t in Set.Ioi u, f t) (s := Set.Ioi 0) (n := m) isOpen_Ioi).mpr
    ⟨?_, ?_, ?_⟩
  · exact fun z hz =>
      (tailIntegral_hasDerivAt hcont hint hz).differentiableAt.differentiableWithinAt
  · intro h
    exact absurd h hm
  · exact hd.congr fun z hz => tailIntegral_deriv_eq hcont hint hz

/-- **The tail integral of a `C^n` integrable function is `C^n`.**  This is the `Ioi z` half of the case-split needed by `Work.FTS.EllExist.Honesty.radGreen_contDiffOn`.

ROUTE (`hint` makes this unconditional: no junk case can arise).  Fix `z > 0`.  `f` is continuous
on `Ioi (z/2)` (`hf.continuousOn.mono`) and integrable there —
`Work.FTS.PhiStar.Radial.integrableOn_Ioi_of_Ioi_Ioo (z/2) hcont hint` (import it; it splits
`Ioi (z/2)` into `Ioc (z/2) 1` and `Ioi 1`; alternatively reprove: for `z/2 ≤ 1` the piece
`Icc (z/2) 1` is compact and `f` is continuous on it, for `1 ≤ z/2` use `Ioi (z/2) ⊆ Ioi 1`).  So
`Work.FTS.PhiStar.Radial.hasDerivAt_integral_Ioi (a := z/2) (z := z) (by linarith)` gives
`HasDerivAt (fun w => ∫ t in Set.Ioi w, f t) (-(f z)) z`.  Hence
`deriv (fun w => ∫ t in Set.Ioi w, f t)` agrees on `Ioi 0` with `fun w => -(f w)`, which is `C^n`
(`hf.neg.congr`), so `contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi` gives `C^{n+1}` (the
conjunct `↑n = ⊤ → AnalyticOn …` is vacuous), and `ContDiffOn.of_le` downgrades to `C^n`. -/
theorem tailIntegral_contDiffOn (n : ℕ) {f : ℝ → ℝ} (hf : ContDiffOn ℝ n f (Set.Ioi 0))
    (hint : MeasureTheory.IntegrableOn f (Set.Ioi 1)) :
    ContDiffOn ℝ n (fun z => ∫ t in Set.Ioi z, f t) (Set.Ioi 0) := by
  have hcont : ContinuousOn f (Set.Ioi 0) := hf.continuousOn
  rcases n with _ | m
  · -- `n = 0`: descend from the `C^1` statement given by the induction step at `m = 0`
    have h : ContDiffOn ℝ ((0 : ℕ∞ω) + 1) (fun z => ∫ t in Set.Ioi z, f t) (Set.Ioi 0) :=
      tailIntegral_contDiffOn_succ (m := (0 : ℕ∞ω)) (by simp) hcont hint (by simpa using hf.neg)
    exact h.of_le (by simp)
  · have hd : ContDiffOn ℝ ((m : ℕ) : ℕ∞ω) (fun z => -(f z)) (Set.Ioi 0) :=
      hf.neg.of_le (by exact_mod_cast Nat.le_succ m)
    have h : ContDiffOn ℝ (((m : ℕ) : ℕ∞ω) + 1) (fun z => ∫ t in Set.Ioi z, f t) (Set.Ioi 0) :=
      tailIntegral_contDiffOn_succ (m := ((m : ℕ) : ℕ∞ω)) (by simp) hcont hint hd
    simpa only [Nat.cast_succ] using h

end Work.FTS.EllExist.Honesty.Pieces
