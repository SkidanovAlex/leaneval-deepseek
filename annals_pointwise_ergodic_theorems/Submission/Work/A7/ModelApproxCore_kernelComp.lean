import Mathlib
import Submission.Work.A7.ModelApproxCore_aux.bilinOp_eq_tsum
import Submission.Work.A7.ModelApproxCore_aux.convOp_mul_tsum
import Submission.Work.A7.ModelApproxCore_aux.kernComp_eq_tsum
import Submission.Work.A7.ModelApproxCore_aux.norm_convOp_le
import Submission.Work.A7.ModelApproxCore_aux.summable_kernComp

/-
# The kernel form of the §6 functional calculus `B_{M·(ψ₁⊗ψ₂)}(u,v) = B_M(T_{ψ₁}u, T_{ψ₂}v)`

This module proves that the composition of the bilinear convolution operator `bilinOp K` (kernel
`K : ℤ → ℤ → ℂ`) on the left with the two *linear* convolution operators `convOp κ`, `convOp κ'`
is again a bilinear convolution operator, with the composed kernel
`kernComp K κ κ' a b = ∑' a' ∑' b' K (a - a') (b - b') κ a' κ' b'`:

  `bilinOp (kernComp K κ κ') u v = bilinOp K (convOp κ u) (convOp κ' v)`.

This is the identity used in §6 of Krause--Mirek--Tao to realise the functional calculus
`B_{M · (ψ₁ ⊗ ψ₂)}`, and it is a pure `tsum`-rearrangement: under the hypotheses
(`K ∈ ℓ¹(ℤ²)`, `κ, κ' ∈ ℓ¹(ℤ)`, `u, v` bounded) *both* sides are absolutely convergent, and both
are the same fourfold sum

  `∑' (a,b,c,d), K a b · κ c · κ' d · u (x - a - c) · v (x - b - d)`,

the left-hand side after the shear bijection `((a,b),(c,d)) ↦ ((a-c,b-d),(c,d))` of `(ℤ²)²`
(`shear` below, applied through `Equiv.tsum_eq`) and the right-hand side after the two
distributivity steps `tsum_mul_tsum_of_summable_norm` / `tsum_mul_left`.

The five elementary pieces are proved in `Submission/Work/A7/ModelApproxCore_aux/` and imported
here; what remains in this file is the summation bookkeeping (the shear bijection, the product
comparison `norm_bound_4`, and the assembly of the two chains).
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.A7

noncomputable section

open scoped BigOperators

/-- The shear bijection `((a,b),(c,d)) ↦ ((a-c, b-d),(c,d))` of `(ℤ × ℤ) × (ℤ × ℤ)`. -/
private def shear : (ℤ × ℤ) × (ℤ × ℤ) ≃ (ℤ × ℤ) × (ℤ × ℤ) where
  toFun q := ((q.1.1 - q.2.1, q.1.2 - q.2.2), q.2)
  invFun q := ((q.2.1 + q.1.1, q.2.2 + q.1.2), q.2)
  left_inv q := by obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := q; simp
  right_inv q := by obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := q; simp

/-! ## The main theorem -/

/-- Multiplication comparison for products of five nonnegative reals. -/
private lemma norm_bound_4 {A B C U V R S : ℝ} (hU : U ≤ R) (hV : V ≤ S)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (_ : 0 ≤ U) (hV0 : 0 ≤ V)
    (hR : 0 ≤ R) (_ : 0 ≤ S) : A * B * U * (C * V) ≤ A * (B * C * (R * S)) := by
  have h1 : U * (C * V) ≤ R * (C * S) :=
    mul_le_mul hU (mul_le_mul_of_nonneg_left hV hC) (mul_nonneg hC hV0) hR
  calc A * B * U * (C * V) = (A * B) * (U * (C * V)) := by ring
    _ ≤ (A * B) * (R * (C * S)) := mul_le_mul_of_nonneg_left h1 (mul_nonneg hA hB)
    _ = A * (B * C * (R * S)) := by ring


theorem ModelApproxCore_kernelComp {K : ℤ → ℤ → ℂ} {κ κ' : ℤ → ℂ} {u v : ℤ → ℂ} {Cu Cv : ℝ}
    (hK : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖) (hκ : Summable fun j : ℤ => ‖κ j‖)
    (hκ' : Summable fun j : ℤ => ‖κ' j‖) (hu : ∀ x, ‖u x‖ ≤ Cu) (hv : ∀ x, ‖v x‖ ≤ Cv) (x : ℤ) :
    Work.KMTAreas.A7.bilinOp (Work.KMTAreas.A7.kernComp K κ κ') u v x
      = Work.KMTAreas.A7.bilinOp K (Work.KMTAreas.A7.convOp κ u) (Work.KMTAreas.A7.convOp κ' v) x := by
  have hCu : ∀ y : ℤ, ‖u y‖ ≤ max Cu 0 := fun y => le_trans (hu y) (le_max_left _ _)
  have hCv : ∀ y : ℤ, ‖v y‖ ≤ max Cv 0 := fun y => le_trans (hv y) (le_max_left _ _)
  -- the common normal form of both sides
  set T : (ℤ × ℤ) × (ℤ × ℤ) → ℂ := fun q =>
    K q.1.1 q.1.2 * ((κ q.2.1 * u (x - q.1.1 - q.2.1)) * (κ' q.2.2 * v (x - q.1.2 - q.2.2))) with hT
  -- summability of the comparison kernel
  have hκκ' : Summable fun z : ℤ × ℤ => ‖κ z.1‖ * ‖κ' z.2‖ :=
    hκ.mul_of_nonneg hκ' (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hKK : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) =>
      ‖K q.1.1 q.1.2‖ * (‖κ q.2.1‖ * ‖κ' q.2.2‖) :=
    hK.mul_of_nonneg hκκ' (fun _ => norm_nonneg _)
      (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hGRcmp : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) =>
      ‖K q.1.1 q.1.2‖ * ((‖κ q.2.1‖ * ‖κ' q.2.2‖) * (max Cu 0 * max Cv 0)) := by
    have h := hKK.mul_right (max Cu 0 * max Cv 0)
    simpa only [mul_assoc] using h
  -- summability of the right-hand normal form
  have hGR : Summable T := by
    refine Summable.of_norm_bounded hGRcmp (fun q => ?_)
    have h1 : ‖u (x - q.1.1 - q.2.1)‖ ≤ max Cu 0 := hCu _
    have h2 : ‖v (x - q.1.2 - q.2.2)‖ ≤ max Cv 0 := hCv _
    simp only [hT, norm_mul]
    have h := norm_bound_4 (A := ‖K q.1.1 q.1.2‖) (B := ‖κ q.2.1‖) (C := ‖κ' q.2.2‖)
      (U := ‖u (x - q.1.1 - q.2.1)‖) (V := ‖v (x - q.1.2 - q.2.2)‖)
      (R := max Cu 0) (S := max Cv 0)
      h1 h2 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      (le_max_right _ _) (le_max_right _ _)
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h
  -- summability of the left-hand normal form
  have hGLcmp : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) =>
      ‖K (q.1.1 - q.2.1) (q.1.2 - q.2.2)‖ * ((‖κ q.2.1‖ * ‖κ' q.2.2‖) * (max Cu 0 * max Cv 0)) :=
    (Equiv.summable_iff (f := fun q : (ℤ × ℤ) × (ℤ × ℤ) =>
      ‖K q.1.1 q.1.2‖ * ((‖κ q.2.1‖ * ‖κ' q.2.2‖) * (max Cu 0 * max Cv 0))) shear).mpr hGRcmp
  have hGL : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) =>
      (K (q.1.1 - q.2.1) (q.1.2 - q.2.2) * κ q.2.1 * κ' q.2.2) * u (x - q.1.1)
        * v (x - q.1.2) := by
    refine Summable.of_norm_bounded hGLcmp (fun q => ?_)
    have h1 : ‖u (x - q.1.1)‖ ≤ max Cu 0 := hCu _
    have h2 : ‖v (x - q.1.2)‖ ≤ max Cv 0 := hCv _
    simp only [norm_mul]
    have h := norm_bound_4 (A := ‖K (q.1.1 - q.2.1) (q.1.2 - q.2.2)‖) (B := ‖κ q.2.1‖)
      (C := ‖κ' q.2.2‖) (U := ‖u (x - q.1.1)‖) (V := ‖v (x - q.1.2)‖)
      (R := max Cu 0) (S := max Cv 0)
      h1 h2 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      (le_max_right _ _) (le_max_right _ _)
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h
  -- pointwise identification of the left-hand normal form with `T ∘ shear`
  have hpoint : ∀ q : (ℤ × ℤ) × (ℤ × ℤ),
      (K (q.1.1 - q.2.1) (q.1.2 - q.2.2) * κ q.2.1 * κ' q.2.2) * u (x - q.1.1) * v (x - q.1.2)
        = T (shear q) := by
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩
    have h1 : x - (a - c) - c = x - a := by ring
    have h2 : x - (b - d) - d = x - b := by ring
    simp only [hT, shear, Equiv.coe_fn_mk]
    rw [h1, h2]
    ring
  have hRHS : Work.KMTAreas.A7.bilinOp K (Work.KMTAreas.A7.convOp κ u)
      (Work.KMTAreas.A7.convOp κ' v) x = ∑' q : (ℤ × ℤ) × (ℤ × ℤ), T q := by
    rw [ModelApproxCore_aux.bilinOp_eq_tsum hK (fun y => ModelApproxCore_aux.norm_convOp_le hκ hu y)
      (fun y => ModelApproxCore_aux.norm_convOp_le hκ' hv y)]
    trans ∑' p : ℤ × ℤ, ∑' z : ℤ × ℤ, T (p, z)
    · refine tsum_congr (fun p => ?_)
      have h1 : K p.1 p.2 * Work.KMTAreas.A7.convOp κ u (x - p.1)
            * Work.KMTAreas.A7.convOp κ' v (x - p.2)
          = K p.1 p.2 * (Work.KMTAreas.A7.convOp κ u (x - p.1)
            * Work.KMTAreas.A7.convOp κ' v (x - p.2)) := mul_assoc _ _ _
      rw [h1, ModelApproxCore_aux.convOp_mul_tsum hκ hκ' hu hv (x - p.1) (x - p.2)]
      exact (tsum_mul_left (f := fun z : ℤ × ℤ =>
        (κ z.1 * u (x - p.1 - z.1)) * (κ' z.2 * v (x - p.2 - z.2))) (a := K p.1 p.2)).symm
    · exact (Summable.tsum_prod hGR).symm
  have hLHS : Work.KMTAreas.A7.bilinOp (Work.KMTAreas.A7.kernComp K κ κ') u v x
      = ∑' q : (ℤ × ℤ) × (ℤ × ℤ), T q := by
    rw [ModelApproxCore_aux.bilinOp_eq_tsum (ModelApproxCore_aux.summable_kernComp hK hκ hκ') hCu hCv]
    trans ∑' p : ℤ × ℤ, ∑' z : ℤ × ℤ,
        (K (p.1 - z.1) (p.2 - z.2) * κ z.1 * κ' z.2) * u (x - p.1) * v (x - p.2)
    · refine tsum_congr (fun p => ?_)
      have h1 : (∑' z : ℤ × ℤ, K (p.1 - z.1) (p.2 - z.2) * κ z.1 * κ' z.2) * u (x - p.1)
          = ∑' z : ℤ × ℤ, (K (p.1 - z.1) (p.2 - z.2) * κ z.1 * κ' z.2) * u (x - p.1) :=
        (tsum_mul_right (f := fun z : ℤ × ℤ =>
          K (p.1 - z.1) (p.2 - z.2) * κ z.1 * κ' z.2) (a := u (x - p.1))).symm
      have h2 : (∑' z : ℤ × ℤ, (K (p.1 - z.1) (p.2 - z.2) * κ z.1 * κ' z.2) * u (x - p.1))
            * v (x - p.2)
          = ∑' z : ℤ × ℤ, (K (p.1 - z.1) (p.2 - z.2) * κ z.1 * κ' z.2) * u (x - p.1)
              * v (x - p.2) :=
        (tsum_mul_right (f := fun z : ℤ × ℤ =>
          (K (p.1 - z.1) (p.2 - z.2) * κ z.1 * κ' z.2) * u (x - p.1))
            (a := v (x - p.2))).symm
      rw [ModelApproxCore_aux.kernComp_eq_tsum hK hκ hκ' p.1 p.2, h1, h2]
    · calc ∑' p : ℤ × ℤ, ∑' z : ℤ × ℤ,
            (K (p.1 - z.1) (p.2 - z.2) * κ z.1 * κ' z.2) * u (x - p.1) * v (x - p.2)
          = ∑' q : (ℤ × ℤ) × (ℤ × ℤ),
              (K (q.1.1 - q.2.1) (q.1.2 - q.2.2) * κ q.2.1 * κ' q.2.2) * u (x - q.1.1)
                * v (x - q.1.2) := (Summable.tsum_prod hGL).symm
        _ = ∑' q : (ℤ × ℤ) × (ℤ × ℤ), T (shear q) := tsum_congr hpoint
        _ = ∑' q : (ℤ × ℤ) × (ℤ × ℤ), T q := Equiv.tsum_eq shear T
  rw [hLHS, hRHS]

end

end Work.A7
