import Mathlib
import Submission.Work.Whitney.CutPush.projection_family_of_charts

/-!
# The collapse at the `ContinuousLinearMap` level

`CutPush/NOTES_STATE_S59.md` §13: the localised projection family averages the *continuous* linear
projections `Q i t`, so the collapse that identifies the average with one of them has to be stated for
`ContinuousLinearMap`s — otherwise every use has to fight the `ContinuousLinearMap → LinearMap`
coercion, which does not commute with the product or with finite sums for free.

* `eq_of_projection_range_eq_clm` — self-adjoint idempotent CLMs with the same range are equal;
* `sum_smul_projection_eq_of_common_range_clm` — an average `Σ i, ρ i • P i` of CLM projections whose
  *active* members share a range *is* that common projection.
-/

namespace Work.Whitney.CutPush

open scoped BigOperators

variable {m : ℕ}

/-- **Self-adjoint idempotent CLMs with the same range are equal.** -/
theorem eq_of_projection_range_eq_clm
    (P Q : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hP : P.comp P = P) (hQ : Q.comp Q = Q)
    (hPs : ∀ x y : EuclideanSpace ℝ (Fin m), inner ℝ (P x) y = inner ℝ x (P y))
    (hQs : ∀ x y : EuclideanSpace ℝ (Fin m), inner ℝ (Q x) y = inner ℝ x (Q y))
    (hr : LinearMap.range (P : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
      = LinearMap.range (Q : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) :
    P = Q := by
  have hPfix : ∀ z ∈ LinearMap.range (P : EuclideanSpace ℝ (Fin m) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin m)), P z = z := by
    rintro z ⟨w, rfl⟩
    have h := congrArg (fun f : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) => f w) hP
    simpa [ContinuousLinearMap.comp_apply] using h
  have hQfix : ∀ z ∈ LinearMap.range (Q : EuclideanSpace ℝ (Fin m) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin m)), Q z = z := by
    rintro z ⟨w, rfl⟩
    have h := congrArg (fun f : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) => f w) hQ
    simpa [ContinuousLinearMap.comp_apply] using h
  have hPQ : ∀ x, P (Q x) = Q x := fun x =>
    hPfix _ (hr ▸ LinearMap.mem_range_self (Q : EuclideanSpace ℝ (Fin m) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin m)) x)
  have hQP : ∀ x, Q (P x) = P x := fun x =>
    hQfix _ (hr.symm ▸ LinearMap.mem_range_self (P : EuclideanSpace ℝ (Fin m) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin m)) x)
  refine ContinuousLinearMap.ext fun x => ?_
  have key : ∀ y, inner ℝ (P x) y = inner ℝ (Q x) y := by
    intro y
    calc inner ℝ (P x) y = inner ℝ (Q (P x)) y := by rw [hQP x]
      _ = inner ℝ (P x) (Q y) := hQs (P x) y
      _ = inner ℝ x (P (Q y)) := hPs x (Q y)
      _ = inner ℝ x (Q y) := by rw [hPQ y]
      _ = inner ℝ (Q x) y := (hQs x y).symm
  have hzero : inner ℝ (P x - Q x) (P x - Q x) = 0 := by
    have h := key (P x - Q x)
    rw [inner_sub_left, h, sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hzero)

/-- **The collapse, at the level of `ContinuousLinearMap`s.** -/
theorem sum_smul_projection_eq_of_common_range_clm {ι : Type*} [Fintype ι]
    (P : ι → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (ρ : ι → ℝ) (hsum : ∑ i, ρ i = 1)
    (ι₀ : ι) (hι₀ : ρ ι₀ ≠ 0)
    (hP : ∀ i, ρ i ≠ 0 → (P i).comp (P i) = P i)
    (hPs : ∀ i, ρ i ≠ 0 → ∀ x y : EuclideanSpace ℝ (Fin m),
      inner ℝ (P i x) y = inner ℝ x (P i y))
    (hcommon : ∀ i, ρ i ≠ 0 → LinearMap.range (P i : EuclideanSpace ℝ (Fin m) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin m))
      = LinearMap.range (P ι₀ : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) :
    ∑ i, ρ i • P i = P ι₀ := by
  have hstep : ∀ i, ρ i • P i = ρ i • P ι₀ := by
    intro i
    by_cases hi : ρ i = 0
    · rw [hi]
      exact (zero_smul ℝ (P i)).trans (zero_smul ℝ (P ι₀)).symm
    · have heq : P i = P ι₀ :=
        eq_of_projection_range_eq_clm (P i) (P ι₀) (hP i hi) (hP ι₀ hι₀)
          (hPs i hi) (hPs ι₀ hι₀) (hcommon i hi)
      rw [heq]
  calc ∑ i, ρ i • P i = ∑ i, ρ i • P ι₀ := Finset.sum_congr rfl fun i _ => hstep i
    _ = (∑ i, ρ i) • P ι₀ := (Finset.sum_smul).symm
    _ = P ι₀ := by rw [hsum, one_smul]

end Work.Whitney.CutPush
