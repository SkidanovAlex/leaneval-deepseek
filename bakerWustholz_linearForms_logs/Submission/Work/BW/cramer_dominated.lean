import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.det_cols_eq_sign_minorJ
import Submission.Work.BW.det_updateCol_eq_sign_minorJ
import Submission.Work.BW.hmax_move

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Matrix

namespace Work.BW

/-- Cramer domination on the ℝ-span of the rows of `M`: when `J` maximises `|Δ_J| ∏_{J} a`, every
coordinate of every vector in the span is dominated by the weighted sum over the coordinates in
`J`. -/
theorem cramer_dominated {r ρ : ℕ} (M : Fin ρ → Fin r → ℤ) (a : Fin r → ℝ) (ha : ∀ i, 0 < a i)
    (J : Finset (Fin r)) (hJ : J.card = ρ)
    (hmax : ∀ (J' : Finset (Fin r)) (hJ' : J'.card = ρ),
      |(minorJ M J' hJ' : ℝ)| * ∏ i ∈ J', a i ≤ |(minorJ M J hJ : ℝ)| * ∏ i ∈ J, a i)
    (hΔ : minorJ M J hJ ≠ 0) (q : Fin ρ → ℝ) (i : Fin r) :
    a i * |∑ k, q k * (M k i : ℝ)| ≤ ∑ i' ∈ J, a i' * |∑ k, q k * (M k i' : ℝ)| := by
  classical
  -- Write `M qᵀ` as the function `v` so that the goal only involves `v`.
  change a i * |(fun j : Fin r => ∑ k, q k * (M k j : ℝ)) i| ≤
    ∑ i' ∈ J, a i' * |(fun j : Fin r => ∑ k, q k * (M k j : ℝ)) i'|
  set v : Fin r → ℝ := fun j => ∑ k, q k * (M k j : ℝ) with hvdef
  by_cases hi : i ∈ J
  · -- If `i ∈ J`, the left hand side is one term of the sum.
    exact Finset.single_le_sum (fun i' _ => mul_nonneg (le_of_lt (ha i')) (abs_nonneg _)) hi
  · -- Otherwise, Cramer's rule expresses `v i` in the basis of the `J`-columns.
    let M' : Matrix (Fin ρ) (Fin ρ) ℤ := fun k b => M k (J.orderEmbOfFin hJ b)
    let A : Matrix (Fin ρ) (Fin ρ) ℝ := fun k b => (M k (J.orderEmbOfFin hJ b) : ℝ)
    let w : Fin ρ → ℝ := fun k => (M k i : ℝ)
    -- `A` is the `J`-column submatrix of `M`, and `A.det = Δ_J`.
    have hAdet : A.det = ((minorJ M J hJ : ℤ) : ℝ) := by
      have h2 : A = (Int.castRingHom ℝ).mapMatrix M' := rfl
      rw [h2, (RingHom.map_det (Int.castRingHom ℝ) M').symm]
      rfl
    have hAne : A.det ≠ 0 := by
      rw [hAdet, Int.cast_ne_zero]
      exact hΔ
    have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hAne
    -- `x` solves `A x = w`, so `v i = ∑_b u_b x_b` with `u = Aᵀ q`.
    set x : Fin ρ → ℝ := A⁻¹ *ᵥ w with hxdef
    set u : Fin ρ → ℝ := fun b => ∑ k, q k * A k b with hudef
    have hAx : A *ᵥ x = w := by
      rw [hxdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hunit, Matrix.one_mulVec]
    have hu_v : ∀ b, u b = v (J.orderEmbOfFin hJ b) := by
      intro b
      rw [hudef, hvdef]
    -- The Cramer identity `v i = ∑_b u_b x_b`.
    have hkey : v i = ∑ b, u b * x b := by
      have h1 : v i = ∑ k, q k * w k := by rw [hvdef]
      have h2 : ∑ b, u b * x b = ∑ k, q k * w k := by
        calc ∑ b, u b * x b
            = ∑ b, (∑ k, q k * A k b) * x b := by rw [hudef]
          _ = ∑ b, ∑ k, (q k * A k b) * x b := by simp only [Finset.sum_mul]
          _ = ∑ k, ∑ b, (q k * A k b) * x b := Finset.sum_comm
          _ = ∑ k, q k * ∑ b, A k b * x b := by
                apply Finset.sum_congr rfl; intro k _
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl; intro b _
                ring
          _ = ∑ k, q k * (A *ᵥ x) k := by
                apply Finset.sum_congr rfl; intro k _
                rw [Matrix.mulVec_apply]
                simp [dotProduct, Matrix.row_apply]
          _ = ∑ k, q k * w k := by rw [hAx]
      rw [h1, h2]
    have habs : |∑ b, u b * x b| ≤ ∑ b, |u b| * |x b| := by
      calc |∑ b, u b * x b| ≤ ∑ b, |u b * x b| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ b, |u b| * |x b| := by simp only [abs_mul]
    -- Each Cramer coefficient is dominated: `a i |x b| ≤ a c_b`, `c_b = J.orderEmbOfFin hJ b`.
    have per_b (b : Fin ρ) : a i * |x b| ≤ a (J.orderEmbOfFin hJ b) := by
      obtain ⟨hcard, ε, hε, hdet⟩ := det_updateCol_eq_sign_minorJ M hJ hi b
      have hCramer : A.det * x b = (Matrix.updateCol A b w).det := by
        have h := congr_fun (Matrix.det_smul_inv_mulVec_eq_cramer A w hunit) b
        rw [← hxdef, Matrix.cramer_apply] at h
        simpa [Pi.smul_apply, smul_eq_mul] using h
      have hmul : A.det * x b
          = ε * ((minorJ M (insert i (J.erase (J.orderEmbOfFin hJ b))) hcard : ℤ) : ℝ) := by
        rw [hCramer]
        exact hdet
      have hεabs : |ε| = 1 := by rcases hε with h | h <;> simp [h]
      have habs' : |A.det| * |x b|
          = |((minorJ M (insert i (J.erase (J.orderEmbOfFin hJ b))) hcard : ℤ) : ℝ)| := by
        have h := congrArg abs hmul
        rw [abs_mul, abs_mul, hεabs, one_mul] at h
        exact h
      have hmove := hmax_move M a ha J hJ hmax hi (Finset.orderEmbOfFin_mem J hJ b) hcard
      rw [← habs', ← hAdet] at hmove
      have hpos : 0 < |A.det| := abs_pos.mpr hAne
      have h2 : (a i * |x b|) * |A.det| ≤ a (J.orderEmbOfFin hJ b) * |A.det| := by
        nlinarith [hmove]
      exact le_of_mul_le_mul_right h2 hpos
    have hbound : a i * |v i| ≤ ∑ b, a (J.orderEmbOfFin hJ b) * |u b| := by
      rw [hkey]
      calc a i * |∑ b, u b * x b|
          ≤ a i * ∑ b, |u b| * |x b| := mul_le_mul_of_nonneg_left habs (le_of_lt (ha i))
        _ = ∑ b, a i * (|u b| * |x b|) := by rw [Finset.mul_sum]
        _ ≤ ∑ b, a (J.orderEmbOfFin hJ b) * |u b| := by
              apply Finset.sum_le_sum; intro b _
              calc a i * (|u b| * |x b|) = (a i * |x b|) * |u b| := by ring
                _ ≤ a (J.orderEmbOfFin hJ b) * |u b| :=
                    mul_le_mul_of_nonneg_right (per_b b) (abs_nonneg _)
    have hsum : (∑ b, a (J.orderEmbOfFin hJ b) * |u b|)
        = ∑ i' ∈ J, a i' * |v i'| := by
      conv_rhs => rw [← Finset.map_orderEmbOfFin_univ J hJ]
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl; intro b _
      rw [hu_v b]
      rfl
    calc a i * |v i| ≤ ∑ b, a (J.orderEmbOfFin hJ b) * |u b| := hbound
      _ = ∑ i' ∈ J, a i' * |v i'| := hsum

end Work.BW
