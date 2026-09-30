import Mathlib
import Submission.Work.BMF.kdr_defs
import Submission.Work.BMF.meanValueDefs
import Submission.Work.BMF.eC_integral_oneDim
import Submission.Work.BMF.eC_integral_unitBox
import Submission.Work.BMF.polySum_mul_conj_pow_expand
import Submission.Work.BMF.sum_ite_momMatch_eq_J

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open MeasureTheory Set
open scoped BigOperators

/-- **Mean-value identity for the box Weyl sum.**  For `s, k, X : ℕ`, the `2s`-th moment over the
unit cube of the box Weyl sum `polySum k α X = Σ_{1 ≤ h ≤ X} e(α₁ h + ⋯ + α_k h^k)` equals the
Vinogradov count `J_{s,k}(X)`, namely
`∫_{[0,1]^k} ‖polySum k α X‖^{2s} dα = J s k X`.

Route.  Expand `‖polySum k α X‖^{2s}` into the double sum over pairs
`(x, y) : (Fin s → Icc 1 X)²` of `e(α·(mom x - mom y))` using `‖z‖^{2s} = (z * conj z)^s`, then
integrate termwise (a finite sum; `unitBox k` has measure `1` since `volume_pi` on `Fin k → ℝ`
gives every coordinate measure `1`).  The integral of `e(α·v)` over the cube is `1` if `v = 0` and
`0` otherwise, being a product of the one-dimensional integrals `∫_0^1 e(t v_j) dt` with integer
`v_j`; and `mom x = mom y` is exactly the Vinogradov condition defining `J s k X`.  A torus route
is also available: `Submission.Vinogradov.vmvt_orthogonality_norm` gives the same identity on
`UnitAddTorus`, and `Work.BMF.meanValueDefs` relates the two Weyl sums. -/
theorem meanValue_polySum_J (s k X : ℕ) :
    (∫ α in unitBox k, ‖polySum k α (X : ℝ)‖ ^ (2 * (s : ℝ)))
      = LeanEval.NumberTheory.VinogradovMeanValue.J s k X := by
  -- `‖z‖^{2s} = (z * conj z)^s` as real numbers: the modulus is extracted into a `2s`-power,
  -- which is the `s`-th power of the squared modulus, and `z * conj z = ↑(normSq z)`.
  have hnorm : ∀ z : ℂ, ‖z‖ ^ (2 * (s : ℝ)) = Complex.normSq z ^ s := by
    intro z
    have hz : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
    calc ‖z‖ ^ (2 * (s : ℝ)) = (‖z‖ ^ (2 : ℝ)) ^ (s : ℝ) := Real.rpow_mul hz 2 (s : ℝ)
      _ = (‖z‖ ^ 2) ^ (s : ℝ) := by rw [Real.rpow_two]
      _ = (‖z‖ ^ 2) ^ s := Real.rpow_natCast _ s
      _ = Complex.normSq z ^ s := by rw [Complex.normSq_eq_norm_sq]
  have hreal : (∫ α in unitBox k, ‖polySum k α (X : ℝ)‖ ^ (2 * (s : ℝ)))
      = ∫ α in unitBox k, Complex.normSq (polySum k α (X : ℝ)) ^ s := by
    apply integral_congr_ae
    filter_upwards with α
    exact hnorm _
  -- Pass to the complex integral of `(z * conj z)^s`, using `∫ ↑f = ↑(∫ f)`.
  have hofreal : ((∫ α in unitBox k, Complex.normSq (polySum k α (X : ℝ)) ^ s : ℝ) : ℂ)
      = ∫ α in unitBox k, ((polySum k α (X : ℝ) * starRingEnd ℂ (polySum k α (X : ℝ)))^s) := by
    have h2' : ((∫ α in unitBox k, Complex.normSq (polySum k α (X : ℝ)) ^ s : ℝ) : ℂ)
        = ∫ α in unitBox k, ((Complex.normSq (polySum k α (X : ℝ)) ^ s : ℝ) : ℂ) :=
      (integral_ofReal (𝕜 := ℂ) (μ := volume.restrict (unitBox k))
        (f := fun α : Fin k → ℝ => Complex.normSq (polySum k α (X : ℝ)) ^ s)).symm
    have h2 : (∫ α in unitBox k, ((Complex.normSq (polySum k α (X : ℝ)) ^ s : ℝ) : ℂ))
        = ∫ α in unitBox k, ((polySum k α (X : ℝ) * starRingEnd ℂ (polySum k α (X : ℝ)))^s) := by
      apply integral_congr_ae
      filter_upwards with α
      rw [Complex.ofReal_pow, Complex.mul_conj]
    exact h2'.trans h2
  -- Expand into the double sum over pairs of tuples and integrate termwise.
  have hmain : (∫ α in unitBox k, ((polySum k α (X : ℝ) * starRingEnd ℂ (polySum k α (X : ℝ)))^s))
      = ((LeanEval.NumberTheory.VinogradovMeanValue.J s k X : ℝ) : ℂ) := by
    have hexp : (fun α : Fin k → ℝ =>
          (polySum k α (X : ℝ) * starRingEnd ℂ (polySum k α (X : ℝ)))^s)
        = fun α : Fin k → ℝ => ∑ p : (Fin s → Finset.Icc 1 X) × (Fin s → Finset.Icc 1 X),
            eC (∑ j : Fin k, α j * (((∑ i, (((p.1 i).1 : ℤ) ^ ((j : ℕ) + 1)))
              - (∑ i, (((p.2 i).1 : ℤ) ^ ((j : ℕ) + 1)))) : ℤ) : ℝ) := by
      funext α
      rw [polySum_mul_conj_pow_expand s k X α]
      apply Finset.sum_congr rfl
      intro p _
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      exact (Int.cast_sub _ _).symm
    rw [hexp]
    rw [integral_finsetSum
      (s := (Finset.univ : Finset ((Fin s → Finset.Icc 1 X) × (Fin s → Finset.Icc 1 X))))
      (f := fun p => fun α : Fin k → ℝ => eC (∑ j : Fin k, α j *
        (((∑ i, (((p.1 i).1 : ℤ) ^ ((j : ℕ) + 1)))
          - (∑ i, (((p.2 i).1 : ℤ) ^ ((j : ℕ) + 1)))) : ℤ) : ℝ))]
    · -- Each pair contributes the orthogonality integral, and the remaining sum is `J`.
      simp_rw [eC_integral_unitBox]
      exact sum_ite_momMatch_eq_J s k X
    · -- The integrands are continuous, hence integrable on the compact box.
      intro p hp
      have hc : Continuous (fun α : Fin k → ℝ => eC (∑ j : Fin k, α j *
          (((∑ i, (((p.1 i).1 : ℤ) ^ ((j : ℕ) + 1)))
            - (∑ i, (((p.2 i).1 : ℤ) ^ ((j : ℕ) + 1)))) : ℤ) : ℝ)) := by
        unfold eC
        fun_prop
      refine hc.continuousOn.integrableOn_compact ?_
      rw [unitBox]
      exact isCompact_univ_pi (fun _ => isCompact_Icc)
  have hfin : ((∫ α in unitBox k, ‖polySum k α (X : ℝ)‖ ^ (2 * (s : ℝ)) : ℝ) : ℂ)
      = ((LeanEval.NumberTheory.VinogradovMeanValue.J s k X : ℝ) : ℂ) := by
    rw [hreal, hofreal, hmain]
  exact Complex.ofReal_inj.mp hfin

end Work.BMF
