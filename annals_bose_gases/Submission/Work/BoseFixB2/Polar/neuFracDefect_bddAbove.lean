import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.Polar.BoxAux
import Submission.Work.BoseFixB2.Polar.neuFracSmulAddDef
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Polar.neuFracDefect_bddAbove`

The quadratic defect

`R(t) = neuFracDefect ℓ a² u f g t = Q(t·f + g) − t²·Q(f) − Q(g)`,  `Q = neuFrac ℓ a² u`,

of the box Neumann-resolvent fraction `Q` along the line `t ↦ t·f + g` is bounded above on
the unit ball `|t| < 1`.

## The argument

Everything comes from the one-sided variational inequality

`Q(φ) ≤ ∫_Λ φ²`,  `Λ = lamBox ℓ u`,   (`neuFrac_le_integral_sq`, from the trial `g = 0`)

valid whenever `φ²` is integrable on the box — in particular for continuous `φ` (the box is
compact, `Aux.integrableOn_sq_of_continuous`).  Applying it to `φ = t·f + g` gives

`R(t) ≤ ∫_Λ (t·f + g)² − t²·Q(f) − Q(g)`.

Now, for `|t| ≤ 1`, the pointwise bound `|t·f z + g z| ≤ |f z| + |g z|` squares to

`∫_Λ (t·f + g)² ≤ ∫_Λ (|f| + |g|)²`   (`MeasureTheory.setIntegral_mono`,)

and the two remaining terms are handled by the trivial `−(t²·Q(f)) ≤ |Q(f)|` (because
`0 ≤ t² ≤ 1`) and `−Q(g) ≤ |Q(g)|`.  Hence

`R(t) ≤ ∫_Λ (|f| + |g|)² + |Q(f)| + |Q(g)|`

for every `|t| < 1`, which is the required uniform upper bound.

The real content of this file is therefore *only* the extraction of the one-sided variational
bound in its cleanest form and the elementary `t`-arithmetic; no resolvent machinery is used.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real ENNReal

namespace Work.BoseFixB2.Polar

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The one-sided variational bound for `neuFrac` at the trial `g = 0`**:
`neuFrac ℓ a² u φ ≤ ∫_Λ φ²`, `Λ = lamBox ℓ u`, as soon as `φ²` is integrable on the box.

This is FS's Dirichlet trial functional `T(φ,0) = ∫_Λ φ²` evaluated at the zero trial
(`Kinetic.trialVal_zero`), combined with the boundedness below of the trial set
(`BoxAux.neuFrac_le_trialVal_of_integrableOn`). -/
lemma neuFrac_le_integral_sq {ℓ a2 : ℝ} (ha2 : 0 ≤ a2) (u : EuclideanSpace ℝ (Fin 3))
    {φ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hφ : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) => (φ z) ^ 2)
      (MeasureTheory.volume.restrict (Work.BoseKinLoc.lamBox ℓ u))) :
    Work.BoseKinLoc.neuFrac ℓ a2 u φ
      ≤ ∫ z in Work.BoseKinLoc.lamBox ℓ u, (φ z) ^ 2 := by
  have h := neuFrac_le_trialVal_of_integrableOn (ℓ := ℓ) (a2 := a2) ha2 u hφ
    (g := fun _ : EuclideanSpace ℝ (Fin 3) => (0 : ℝ)) contDiff_const HasCompactSupport.zero
  rwa [Work.BoseKinLoc.Kinetic.trialVal_zero] at h

theorem neuFracDefect_bddAbove {ℓ a2 : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 < a2) (u : EuclideanSpace ℝ (Fin 3)) {f g : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) : ∃ M : ℝ, ∀ t : ℝ, |t| < 1 → neuFracDefect ℓ a2 u f g t ≤ M := by
  have ha2le : (0 : ℝ) ≤ a2 := le_of_lt ha2
  have hfc : Continuous f := hf.continuous
  have hgc : Continuous g := hg.continuous
  -- the square of `|f| + |g|` is integrable on the compact box
  have hIabs : MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) => (|f z| + |g z|) ^ 2)
      (MeasureTheory.volume.restrict (Work.BoseKinLoc.lamBox ℓ u)) :=
    integrableOn_sq_of_continuous hℓ u (hfc.abs.add hgc.abs)
  refine ⟨(∫ z in Work.BoseKinLoc.lamBox ℓ u, (|f z| + |g z|) ^ 2)
    + |Work.BoseKinLoc.neuFrac ℓ a2 u f| + |Work.BoseKinLoc.neuFrac ℓ a2 u g|, ?_⟩
  intro t ht
  -- `t ^ 2 ≤ 1` for `|t| < 1`
  have ht2 : t ^ 2 ≤ 1 := by
    have h1 : t < 1 := (abs_lt.mp ht).2
    have h2 : -1 < t := (abs_lt.mp ht).1
    have hpos : 0 < (1 - t) * (1 + t) :=
      mul_pos (by linarith) (by linarith)
    nlinarith [hpos]
  -- the state `t·f + g` is continuous, hence its square is integrable on the box
  have hφc : Continuous (fun z : EuclideanSpace ℝ (Fin 3) => t * f z + g z) :=
    (continuous_const.mul hfc).add hgc
  have hIφ : MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) => (t * f z + g z) ^ 2)
      (MeasureTheory.volume.restrict (Work.BoseKinLoc.lamBox ℓ u)) :=
    integrableOn_sq_of_continuous hℓ u hφc
  -- the variational bound at the state `t·f + g`
  have hQ : Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => t * f z + g z)
      ≤ ∫ z in Work.BoseKinLoc.lamBox ℓ u, (t * f z + g z) ^ 2 :=
    neuFrac_le_integral_sq ha2le u hIφ
  -- and the monotonicity `(t·f + g)² ≤ (|f| + |g|)²` on `|t| < 1`
  have hmono : (∫ z in Work.BoseKinLoc.lamBox ℓ u, (t * f z + g z) ^ 2)
      ≤ ∫ z in Work.BoseKinLoc.lamBox ℓ u, (|f z| + |g z|) ^ 2 := by
    refine MeasureTheory.setIntegral_mono hIφ hIabs ?_
    intro z
    change (t * f z + g z) ^ 2 ≤ (|f z| + |g z|) ^ 2
    have hpt : |t * f z + g z| ≤ |f z| + |g z| := by
      calc |t * f z + g z| ≤ |t * f z| + |g z| := abs_add_le _ _
        _ = |t| * |f z| + |g z| := by rw [abs_mul]
        _ ≤ 1 * |f z| + |g z| := by
              have := mul_le_mul_of_nonneg_right (le_of_lt ht) (abs_nonneg (f z))
              linarith
        _ = |f z| + |g z| := by rw [one_mul]
    have h2 : |(|f z| + |g z|)| = |f z| + |g z| :=
      abs_of_nonneg (add_nonneg (abs_nonneg (f z)) (abs_nonneg (g z)))
    rw [sq_le_sq, h2]
    exact hpt
  -- `−(t²·Q f) ≤ |Q f|`
  have hQf : -(t ^ 2 * Work.BoseKinLoc.neuFrac ℓ a2 u f)
      ≤ |Work.BoseKinLoc.neuFrac ℓ a2 u f| := by
    rw [show -(t ^ 2 * Work.BoseKinLoc.neuFrac ℓ a2 u f)
        = t ^ 2 * (-(Work.BoseKinLoc.neuFrac ℓ a2 u f)) by ring]
    calc t ^ 2 * (-(Work.BoseKinLoc.neuFrac ℓ a2 u f))
        ≤ t ^ 2 * |Work.BoseKinLoc.neuFrac ℓ a2 u f| :=
          mul_le_mul_of_nonneg_left (neg_le_abs _) (sq_nonneg t)
      _ ≤ 1 * |Work.BoseKinLoc.neuFrac ℓ a2 u f| :=
          mul_le_mul_of_nonneg_right ht2 (abs_nonneg _)
      _ = |Work.BoseKinLoc.neuFrac ℓ a2 u f| := one_mul _
  have hdef : neuFracDefect ℓ a2 u f g t
      = Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => t * f z + g z)
        - t ^ 2 * Work.BoseKinLoc.neuFrac ℓ a2 u f
        - Work.BoseKinLoc.neuFrac ℓ a2 u g := rfl
  rw [hdef]
  linarith [hQ, hmono, hQf, neg_le_abs (Work.BoseKinLoc.neuFrac ℓ a2 u g)]

end Work.BoseFixB2.Polar
