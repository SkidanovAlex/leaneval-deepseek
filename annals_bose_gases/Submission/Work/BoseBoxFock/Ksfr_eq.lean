import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.BoseBoxFock.fL_latticeSum_eq_complex
import Submission.Work.BoseBoxFock.pcfFrameDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open scoped BigOperators

/-! ## The `excited`-sum versus the `0`-punctured sum

`Work.BoseB7.excited M = univ.erase 0` (the excited modes: FS replaces `a₀` by the `c`-number `z`,
so the mode `0` is never summed over).  The two spellings used in the chapter — the `∈ excited`
sum and the `if · = 0 then 0 else ·` sum over all labels — agree, in any additive monoid. -/
lemma sum_excited_eq_sum_ite {M : Type*} [AddCommGroup M] [Fintype M] [DecidableEq M]
    (f : M → ℂ) :
    (∑ x ∈ Work.BoseB7.excited M, f x) = ∑ x : M, (if x = 0 then 0 else f x) := by
  rw [Work.BoseB7.excited, Finset.sum_erase_eq_sub (Finset.mem_univ (0 : M))]
  have hsing : (∑ x : M, (if x = 0 then f x else (0 : ℂ))) = f 0 := by
    rw [Finset.sum_ite_eq']; simp
  rw [← hsing, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : x = 0 <;> simp [h]

/-- **Evaluation of the `s`-frame** `Ksfr` (the `f_L`-weighted lattice sum): the periodised
multiplier kernel of `f(√−Δ/κ)`, in its complex-exponential (Poisson summation) form.

This is the finite-lattice (`Lab N`) identity `Work.BoseBoxFock.fL_latticeSum_eq_complex` with
the label `0` removed from the sum (it contributes `f_L(0) = f(0) = 1`, which is exactly the
`− 1` on the right-hand side). -/
theorem Ksfr_eq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {fc : Work.BoseBoxFix.LowCut} {μ : ℝ} {N : ℕ}
    (hℓ : 0 < Work.BoseBoxFock.ellH v μ)
    (hκ : 0 < ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
      * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
    (hN : 2 * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
      * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹ * Work.BoseBoxFock.ellH v μ
      / (2 * Real.pi) ≤ (N : ℝ)) (z : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseBoxFock.Ksfr v fc μ N z
      = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3 * (∑' d : Fin 3 → ℤ,
          ((((2 * Real.pi) ^ 3)⁻¹ : ℝ) : ℂ) * ∫ p : EuclideanSpace ℝ (Fin 3),
              Complex.exp (Complex.I * (inner ℝ p (z + Work.BoseBoxFock.ellH v μ
                • Work.BoseBoxFock.latVec d) : ℂ)) *
                (((fc.f (‖p‖ / ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                  * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹) : ℝ) : ℂ)))
        - 1 := by
  have h := Work.BoseBoxFock.fL_latticeSum_eq_complex (fc := fc)
    (κ := ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
      * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹) (ℓ := Work.BoseBoxFock.ellH v μ) hκ hℓ N hN z
  rw [Work.BoseBoxFock.Ksfr, sum_excited_eq_sum_ite]
  simp only [Work.BoseBoxFock.fLh]
  rw [h]

end Work.BoseBoxFock
