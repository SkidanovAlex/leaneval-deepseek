import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Kinetic.continuous_fibre_sq_diff`

The two-point fibre difference square

    `q ↦ ∫_{Λ} (Φ(kcInsN n i (ℓ q₁ + z, r₁)) − Φ(kcInsN n i (ℓ q₂ + z, r₂)))² dz`

is **continuous** on `(ℝ³ × X n) × (ℝ³ × X n)` for a smooth, compactly supported
`Φ : X (n+1) → ℝ`.

The proof is the parametric-integral theorem
`continuous_parametric_integral_of_continuous` (`Mathlib`): the integrand is
jointly continuous in `(q, z)` — the insertion `kcInsN n i` is continuous
coordinatewise (`kc_insN_apply_same` / `kc_insN_apply_succ`) and `Φ` is smooth —
and the domain `acube ℓ` is compact (`acube_compact`).  (Neither the support
hypothesis nor smoothness beyond continuity is needed; the hypotheses are part of
the requested interface.)
-/

noncomputable section

open MeasureTheory
open scoped Topology ENNReal

namespace Work.BoseKinLoc.Kinetic

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The coordinate insertion `p ↦ kcInsN n i p` is continuous on `ℝ³ × X n`
(coordinatewise from `kc_insN_apply_same`/`kc_insN_apply_succ`). -/
lemma continuous_kcInsN_pair {n : ℕ} (i : Fin (n + 1)) :
    Continuous (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
      Submission.BoseGases.kcInsN n i p) := by
  rw [continuous_pi_iff]
  intro j
  by_cases hj : j = i
  · subst j
    have hEq : (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        (Submission.BoseGases.kcInsN n i p) i) = fun p => p.1 := by
      funext p; exact Submission.BoseGases.kc_insN_apply_same n i p.1 p.2
    rw [hEq]; fun_prop
  · rcases Fin.exists_succAbove_eq hj with ⟨j', rfl⟩
    have hEq : (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        (Submission.BoseGases.kcInsN n i p) (i.succAbove j')) = fun p => p.2 j' := by
      funext p; exact Submission.BoseGases.kc_insN_apply_succ n i p.1 p.2 j'
    rw [hEq]; fun_prop

theorem continuous_fibre_sq_diff {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ}
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox (n + 1) ℓ) (i : Fin (n + 1)) :
    Continuous (fun q : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n)
        × (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) =>
      ∫ z in Submission.BoseGases.acube ℓ,
        (Φ (Submission.BoseGases.kcInsN n i (ℓ • q.1.1 + z, q.1.2))
          - Φ (Submission.BoseGases.kcInsN n i (ℓ • q.2.1 + z, q.2.2))) ^ 2) := by
  have hΦc : Continuous Φ := hΦ.continuous
  have hins : Continuous (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
      Submission.BoseGases.kcInsN n i p) := continuous_kcInsN_pair i
  have hmain : Continuous (Function.uncurry fun q : (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n)
        × (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n) =>
      fun z : EuclideanSpace ℝ (Fin 3) =>
        (Φ (Submission.BoseGases.kcInsN n i (ℓ • q.1.1 + z, q.1.2))
          - Φ (Submission.BoseGases.kcInsN n i (ℓ • q.2.1 + z, q.2.2))) ^ 2) := by
    have h1 : Continuous (fun u : ((EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n)
        × (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n)) × EuclideanSpace ℝ (Fin 3) =>
        Φ (Submission.BoseGases.kcInsN n i (ℓ • u.1.1.1 + u.2, u.1.1.2))) :=
      hΦc.comp (hins.comp (by fun_prop))
    have h2 : Continuous (fun u : ((EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n)
        × (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n)) × EuclideanSpace ℝ (Fin 3) =>
        Φ (Submission.BoseGases.kcInsN n i (ℓ • u.1.2.1 + u.2, u.1.2.2))) :=
      hΦc.comp (hins.comp (by fun_prop))
    have h3 : Continuous (fun u : ((EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n)
        × (EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n)) × EuclideanSpace ℝ (Fin 3) =>
        Φ (Submission.BoseGases.kcInsN n i (ℓ • u.1.1.1 + u.2, u.1.1.2))
          - Φ (Submission.BoseGases.kcInsN n i (ℓ • u.1.2.1 + u.2, u.1.2.2))) := h1.sub h2
    exact h3.pow 2
  simpa only [Function.uncurry] using
    continuous_parametric_integral_of_continuous
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))))
      hmain (Submission.BoseGases.acube_compact hℓ)

end Work.BoseKinLoc.Kinetic
