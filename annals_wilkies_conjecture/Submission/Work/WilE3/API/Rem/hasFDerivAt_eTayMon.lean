import Mathlib
import Submission.Work.WilE3.API.Rem.eTayBasic

namespace Work.WilE3.API.Rem

open ContinuousLinearMap

/-!
## The Fréchet derivative of a single Taylor monomial

For fixed `y` and multi-index `m`, `eTayMon y m x = ∏ j, (x j - y j) ^ (m j) / (m j)!` is a
product over the coordinates: one factor `z ↦ (z i - y i) ^ (m i) / (m i)!` per index `i`.  The
derivative at `x` is the sum, over `i`, of the product of the *other* factors times the
derivative of the `i`-th factor.  The two helper lemmas below supply the two ingredients:

* `hasFDerivAt_eTayMon_factor_aux` computes the derivative of a single factor, and
* `eTayMon_miS_mul_coeff_aux` identifies the resulting coefficient (product of the remaining
  factors times the scalar derivative of the `i`-th factor) with `eTayMon y (miS m i) x` when
  `m i > 0` and with `0` otherwise -- which is exactly the `i`-th coefficient of `eTayGrad`.
-/

/-- Derivative of the single Taylor factor `z ↦ (z i - y i) ^ (m i) / (m i)!` at `x`. -/
theorem hasFDerivAt_eTayMon_factor_aux {k : ℕ} (y x : Fin k → ℝ) (m : Fin k → ℕ) (i : Fin k) :
    HasFDerivAt (𝕜 := ℝ) (fun z : Fin k → ℝ => (z i - y i) ^ (m i) / ((m i).factorial : ℝ))
      (((m i : ℝ) * (x i - y i) ^ (m i - 1) / ((m i).factorial : ℝ)) •
        ContinuousLinearMap.proj (φ := fun _ : Fin k => ℝ) i) x := by
  have h1 : HasFDerivAt (𝕜 := ℝ) (fun z : Fin k → ℝ => (z i - y i) ^ (m i))
      (((m i : ℝ) * (x i - y i) ^ (m i - 1)) •
        ContinuousLinearMap.proj (φ := fun _ : Fin k => ℝ) i) x := by
    have h := ((hasFDerivAt_apply (𝕜 := ℝ) i x).sub_const (y i)).pow (m i)
    simpa [nsmul_eq_mul] using h
  have h2 := h1.mul_const (((m i).factorial : ℝ)⁻¹)
  have hfun : (fun z : Fin k → ℝ => (z i - y i) ^ (m i) * ((m i).factorial : ℝ)⁻¹)
      = (fun z : Fin k → ℝ => (z i - y i) ^ (m i) / ((m i).factorial : ℝ)) := by
    funext z; rw [div_eq_mul_inv]
  rw [hfun] at h2
  refine h2.congr_fderiv ?_
  rw [smul_smul]
  congr 1
  rw [div_eq_mul_inv]
  ring

/-- The coefficient of the `i`-th summand of the derivative of `eTayMon y m` at `x`:
the product of the factors with index `≠ i` times the scalar derivative
`m i · (x i - y i) ^ (m i - 1) / (m i)!` of the `i`-th factor equals `eTayMon y (miS m i) x`
for `m i > 0`, and `0` for `m i = 0`. -/
theorem eTayMon_miS_mul_coeff_aux {k : ℕ} (y x : Fin k → ℝ) (m : Fin k → ℕ) (i : Fin k) :
    (∏ j ∈ Finset.univ.erase i, ((x j - y j) ^ (m j) / ((m j).factorial : ℝ)))
      * ((m i : ℝ) * (x i - y i) ^ (m i - 1) / ((m i).factorial : ℝ))
    = (if 0 < m i then Work.WilE3.API.eTayMon y (Work.WilE3.API.miS m i) x else 0) := by
  set P := ∏ j ∈ Finset.univ.erase i, ((x j - y j) ^ (m j) / ((m j).factorial : ℝ)) with hP
  by_cases hmi : 0 < m i
  · rw [if_pos hmi]
    have hpred : m i = (m i - 1) + 1 := by omega
    have hfac : (m i).factorial = (m i) * (m i - 1).factorial := by
      conv_lhs => rw [hpred]
      rw [Nat.factorial_succ]
      congr 1
      omega
    have hcast : ((m i).factorial : ℝ) = (m i : ℝ) * ((m i - 1).factorial : ℝ) := by
      rw [hfac, Nat.cast_mul]
    have hne : (m i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hmi)
    have hmon : Work.WilE3.API.eTayMon y (Work.WilE3.API.miS m i) x
        = ((x i - y i) ^ (m i - 1) / ((m i - 1).factorial : ℝ)) * P := by
      rw [Work.WilE3.API.eTayMon, hP]
      rw [← Finset.mul_prod_erase Finset.univ
        (fun j => (x j - y j) ^ (Work.WilE3.API.miS m i j) /
          ((Work.WilE3.API.miS m i j).factorial : ℝ))
        (Finset.mem_univ i)]
      congr 1
      · rw [Work.WilE3.API.miS_apply, if_pos rfl]
      · apply Finset.prod_congr rfl
        intro j hj
        obtain ⟨hji, -⟩ := Finset.mem_erase.mp hj
        rw [Work.WilE3.API.miS_apply, if_neg hji, Nat.sub_zero]
    have hscal : (m i : ℝ) * (x i - y i) ^ (m i - 1) / ((m i).factorial : ℝ)
        = (x i - y i) ^ (m i - 1) / ((m i - 1).factorial : ℝ) := by
      rw [hcast]
      exact mul_div_mul_left _ _ hne
    rw [hmon, hscal]
    ring
  · rw [if_neg hmi]
    have h0 : m i = 0 := Nat.eq_zero_of_not_pos hmi
    rw [h0]
    simp

theorem hasFDerivAt_eTayMon {k : ℕ} (y x : Fin k → ℝ) (m : Fin k → ℕ) :
    HasFDerivAt (Work.WilE3.API.eTayMon y m) (Work.WilE3.API.eTayGrad y m x) x := by
  have hg : ∀ i : Fin k, HasFDerivAt (𝕜 := ℝ)
      (fun z : Fin k → ℝ => (z i - y i) ^ (m i) / ((m i).factorial : ℝ))
      (((m i : ℝ) * (x i - y i) ^ (m i - 1) / ((m i).factorial : ℝ)) •
        ContinuousLinearMap.proj (φ := fun _ : Fin k => ℝ) i) x :=
    fun i => hasFDerivAt_eTayMon_factor_aux y x m i
  have hprod := HasFDerivAt.finsetProd (u := Finset.univ)
    (g := fun i (z : Fin k → ℝ) => (z i - y i) ^ (m i) / ((m i).factorial : ℝ))
    (g' := fun i => ((m i : ℝ) * (x i - y i) ^ (m i - 1) / ((m i).factorial : ℝ)) •
      ContinuousLinearMap.proj (φ := fun _ : Fin k => ℝ) i)
    (x := x) (fun i _ => hg i)
  refine hprod.congr_fderiv ?_
  simp only [Work.WilE3.API.eTayGrad]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [smul_smul, eTayMon_miS_mul_coeff_aux y x m i]

end Work.WilE3.API.Rem
