import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

/-- **Second-order Taylor expansion of the analytic germ `f` with a `z ^ 3` remainder.**

If `f` is analytic at `0` with `f 0 = 0` and `f'(0) = 1`, then on a full neighbourhood of `0`
(globally, in fact) `f z = z + (f''(0)/2) z^2 + z^3 G z` for a germ `G` analytic at `0`. -/
lemma taylor3 {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0) (hf1 : deriv f 0 = 1) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧
      ∀ z, f z = z + (iteratedDeriv 2 f 0 / 2) * z^2 + z^3 * G z := by
  obtain ⟨G, hGa, hG⟩ := hf.exists_eq_sum_add_pow_mul 3
  refine ⟨G, hGa, fun z => ?_⟩
  rw [hG z]
  have hsum : (∑ i ∈ Finset.range 3, (z ^ i / ↑i.factorial) • iteratedDeriv i f 0)
      = z + (iteratedDeriv 2 f 0 / 2) * z^2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    simp only [iteratedDeriv_zero, hf0, iteratedDeriv_one, hf1]
    simp
    ring
  rw [hsum, smul_eq_mul]

/-- **The algebraic identity** behind the second-order expansion of `1/(z u(z²))`.

If `U ^ 2 = 1 + A z^2 + z^4 W` (this is what the functional equation `u(w)^2 w = f(w)`
produces at `w = z^2`), then the discrepancy between `(z U)⁻¹` and its first-order
approximation `1/z - (A/2) z` equals `z⁻¹` times an explicit expression that is `O(z^4)`. -/
lemma inv_sqrt_identity (U z A W : ℂ) (hz : z ≠ 0) (hU : U ≠ 0)
    (hrel : U^2 = 1 + A*z^2 + z^4*W) :
    (z * U)⁻¹ - (1/z - (A/2)*z) = (1/z) * ((3/2)*(U-1)^2 - (U-1)^3/U - z^4 * W/2) := by
  field_simp
  linear_combination (-U) * hrel

/-- **The quantitative bound.**  Under the algebraic relation `U ^ 2 = 1 + A z^2 + z^4 W`,
with `‖U - 1‖ ≤ 1/2` (so `U` is invertible with `‖U‖ ≥ 1/2`), `‖W‖ ≤ B` and `‖z‖ ≤ 1`,
the second-order remainder of `(z U)⁻¹` near `1/z - (A/2) z` is `O(‖z‖^2)`. -/
lemma key_bound (U z A W : ℂ) (B : ℝ)
    (hz : 0 < ‖z‖) (hz1 : ‖z‖ ≤ 1)
    (hU1 : ‖U - 1‖ ≤ 1/2)
    (hW : ‖W‖ ≤ B) (hB : 0 ≤ B)
    (hrel : U^2 = 1 + A*z^2 + z^4*W) :
    ‖(z * U)⁻¹ - (1/z - (A/2)*z)‖
      ≤ ((3/2)*(‖A‖+B)^2 + 2*(‖A‖+B)^3 + B/2) * ‖z‖^2 := by
  have hK : 0 ≤ ‖A‖ + B := add_nonneg (norm_nonneg A) hB
  have hz4le : ‖z‖^4 ≤ ‖z‖^2 := pow_le_pow_of_le_one (norm_nonneg z) hz1 (by norm_num)
  have hz6le : ‖z‖^6 ≤ ‖z‖^4 := pow_le_pow_of_le_one (norm_nonneg z) hz1 (by norm_num)
  have hnormU : (1:ℝ)/2 ≤ ‖U‖ := by
    have h1 : ‖U - (U - 1)‖ ≤ ‖U‖ + ‖U - 1‖ := norm_sub_le U (U - 1)
    have h2 : U - (U - 1) = 1 := by ring
    rw [h2, norm_one] at h1
    linarith
  have hU_ne : U ≠ 0 := by
    intro h; rw [h, norm_zero] at hnormU; norm_num at hnormU
  have hz_ne : z ≠ 0 := norm_pos_iff.mp hz
  have hprod : (U - 1)*(2 + (U - 1)) = A*z^2 + z^4*W := by
    have h : U^2 - 1 = A*z^2 + z^4*W := by linear_combination hrel
    linear_combination h
  have h2s : (3:ℝ)/2 ≤ ‖2 + (U - 1)‖ := by
    have h := norm_sub_norm_le (2:ℂ) (-(U - 1))
    rw [show (2:ℂ) - -(U-1) = 2 + (U-1) by ring, norm_neg, Complex.norm_ofNat] at h
    linarith
  have hKz : 0 ≤ (‖A‖ + B) * ‖z‖^2 := mul_nonneg hK (sq_nonneg _)
  have hprod_norm : ‖U - 1‖ * ‖2 + (U - 1)‖ ≤ (‖A‖ + B) * ‖z‖^2 := by
    rw [← norm_mul, hprod]
    calc ‖A*z^2 + z^4*W‖ ≤ ‖A*z^2‖ + ‖z^4*W‖ := norm_add_le _ _
      _ = ‖A‖*‖z‖^2 + ‖z‖^4*‖W‖ := by simp only [norm_mul, norm_pow]
      _ ≤ ‖A‖*‖z‖^2 + ‖z‖^2*B :=
          add_le_add le_rfl (mul_le_mul hz4le hW (norm_nonneg W) (by positivity))
      _ = (‖A‖ + B) * ‖z‖^2 := by ring
  have hsK : ‖U - 1‖ ≤ (‖A‖ + B) * ‖z‖^2 := by
    have h1 : ‖U - 1‖ * (3/2) ≤ (‖A‖ + B) * ‖z‖^2 := by
      calc ‖U - 1‖ * (3/2) ≤ ‖U - 1‖ * ‖2 + (U-1)‖ :=
            mul_le_mul_of_nonneg_left h2s (norm_nonneg _)
        _ ≤ (‖A‖ + B) * ‖z‖^2 := hprod_norm
    have h2 : ‖U - 1‖ ≤ ((‖A‖ + B) * ‖z‖^2) / (3/2) := by
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 3/2)]; linarith
    have h3 : ((‖A‖ + B) * ‖z‖^2) / (3/2) ≤ (‖A‖ + B) * ‖z‖^2 := by
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 3/2)]; nlinarith
    linarith
  have hnormUinv : ‖U‖⁻¹ ≤ 2 := by
    have hUp : 0 < ‖U‖ := by linarith
    rw [inv_eq_one_div, div_le_iff₀ hUp]; linarith
  have hT1 : ‖(3/2:ℂ)*(U-1)^2‖ ≤ (3/2)*(‖A‖+B)^2*‖z‖^4 := by
    rw [norm_mul, norm_pow]
    have h32 : ‖(3/2:ℂ)‖ = (3/2:ℝ) := by norm_num
    rw [h32]
    have hsq : ‖U-1‖^2 ≤ ((‖A‖+B)*‖z‖^2)^2 := pow_le_pow_left₀ (norm_nonneg _) hsK 2
    calc (3/2) * ‖U-1‖^2 ≤ (3/2) * ((‖A‖+B)*‖z‖^2)^2 :=
          mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ = (3/2)*(‖A‖+B)^2*‖z‖^4 := by ring
  have hT2 : ‖(U-1)^3/U‖ ≤ 2*(‖A‖+B)^3*‖z‖^4 := by
    have hmain : ‖(U-1)^3/U‖ ≤ 2*(‖A‖+B)^3*‖z‖^6 := by
      rw [norm_div, norm_pow, div_eq_mul_inv]
      have hnum : ‖U-1‖^3 ≤ ((‖A‖+B)*‖z‖^2)^3 := pow_le_pow_left₀ (norm_nonneg _) hsK 3
      calc ‖U-1‖^3 * ‖U‖⁻¹ ≤ ((‖A‖+B)*‖z‖^2)^3 * 2 :=
            mul_le_mul hnum hnormUinv (inv_nonneg.mpr (norm_nonneg _)) (pow_nonneg hKz 3)
        _ = 2*(‖A‖+B)^3*‖z‖^6 := by ring
    calc ‖(U-1)^3/U‖ ≤ 2*(‖A‖+B)^3*‖z‖^6 := hmain
      _ ≤ 2*(‖A‖+B)^3*‖z‖^4 :=
          mul_le_mul_of_nonneg_left hz6le (mul_nonneg (by norm_num) (pow_nonneg hK 3))
  have hT3 : ‖z^4*W/2‖ ≤ B*‖z‖^4/2 := by
    rw [norm_div, norm_mul, norm_pow]
    rw [Complex.norm_ofNat]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    calc ‖z‖^4 * ‖W‖ ≤ ‖z‖^4 * B := mul_le_mul_of_nonneg_left hW (pow_nonneg (norm_nonneg z) 4)
      _ = B * ‖z‖^4 := by ring
  have hE : ‖(3/2)*(U-1)^2 - (U-1)^3/U - z^4*W/2‖
      ≤ ((3/2)*(‖A‖+B)^2 + 2*(‖A‖+B)^3 + B/2) * ‖z‖^4 := by
    calc ‖(3/2)*(U-1)^2 - (U-1)^3/U - z^4*W/2‖
        ≤ ‖(3/2)*(U-1)^2 - (U-1)^3/U‖ + ‖z^4*W/2‖ := norm_sub_le _ _
      _ ≤ (‖(3/2)*(U-1)^2‖ + ‖(U-1)^3/U‖) + ‖z^4*W/2‖ := by
            have := norm_sub_le ((3/2)*(U-1)^2) ((U-1)^3/U); linarith
      _ ≤ ((3/2)*(‖A‖+B)^2*‖z‖^4 + 2*(‖A‖+B)^3*‖z‖^4) + B*‖z‖^4/2 := by
            linarith [hT1, hT2, hT3]
      _ = ((3/2)*(‖A‖+B)^2 + 2*(‖A‖+B)^3 + B/2) * ‖z‖^4 := by ring
  have hC0 : 0 ≤ (3/2)*(‖A‖+B)^2 + 2*(‖A‖+B)^3 + B/2 := by
    have h1 : 0 ≤ (3/2)*(‖A‖+B)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
    have h2 : 0 ≤ 2*(‖A‖+B)^3 := mul_nonneg (by norm_num) (pow_nonneg hK 3)
    have h3 : 0 ≤ B/2 := by linarith
    linarith
  rw [inv_sqrt_identity U z A W hz_ne hU_ne hrel]
  calc ‖(1/z) * ((3/2)*(U-1)^2 - (U-1)^3/U - z^4*W/2)‖
      = ‖z‖⁻¹ * ‖(3/2)*(U-1)^2 - (U-1)^3/U - z^4*W/2‖ := by rw [norm_mul, one_div, norm_inv]
    _ ≤ ‖z‖⁻¹ * (((3/2)*(‖A‖+B)^2 + 2*(‖A‖+B)^3 + B/2) * ‖z‖^4) :=
          mul_le_mul_of_nonneg_left hE (inv_nonneg.mpr (norm_nonneg z))
    _ = ((3/2)*(‖A‖+B)^2 + 2*(‖A‖+B)^3 + B/2) * ‖z‖^3 := by
          field_simp
    _ ≤ ((3/2)*(‖A‖+B)^2 + 2*(‖A‖+B)^3 + B/2) * ‖z‖^2 := by
          apply mul_le_mul_of_nonneg_left _ hC0
          have : ‖z‖^3 ≤ ‖z‖^2 := pow_le_pow_of_le_one (norm_nonneg z) hz1 (by norm_num)
          linarith

/-- **Approximate square-root inverse.**

Let `f` be an analytic germ at `0` with `f 0 = 0`, `f'(0) = 1`, and let `u` be an analytic
germ at `0` with `u 0 = 1` satisfying `u(w)^2 · w = f(w)` on the unit disc.  Then
`(z u(z²))⁻¹` differs from its first-order expansion `1/z - (f''(0)/4) z` by at most a constant
times `‖z‖²` near `z = 0`. -/
theorem approxInvSqrt (f u : ℂ → ℂ) (hu : AnalyticAt ℂ u 0) (hf : AnalyticAt ℂ f 0)
    (hu0 : u 0 = 1) (hf0 : f 0 = 0) (hf1 : deriv f 0 = 1)
    (hueq : ∀ w ∈ Metric.ball 0 1, u w ^ 2 * w = f w) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < δ →
      ‖(z * u (z ^ 2))⁻¹ - (1 / z + (-(iteratedDeriv 2 f 0) / 4) * z)‖ ≤ C * ‖z‖ ^ 2 := by
  obtain ⟨G, hGa, hG⟩ := taylor3 hf hf0 hf1
  set B : ℝ := ‖G 0‖ + 1 with hBdef
  have hB : 0 ≤ B := by rw [hBdef]; positivity
  obtain ⟨δG, hδGpos, hGbd⟩ : ∃ δG : ℝ, 0 < δG ∧ ∀ w : ℂ, ‖w‖ < δG → ‖G w‖ ≤ B := by
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp hGa.continuousAt 1 one_pos
    refine ⟨δ, hδ, fun w hw => ?_⟩
    have h1 : dist (G w) (G 0) < 1 := hδ' (by simpa [dist_eq_norm] using hw)
    rw [dist_eq_norm] at h1
    have h2 : ‖G w‖ ≤ ‖G w - G 0‖ + ‖G 0‖ := by
      calc ‖G w‖ = ‖(G w - G 0) + G 0‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    rw [hBdef]
    linarith
  obtain ⟨δu, hδupos, hubd⟩ : ∃ δu : ℝ, 0 < δu ∧ ∀ w : ℂ, ‖w‖ < δu → ‖u w - 1‖ ≤ 1/2 := by
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp hu.continuousAt (1/2) (by norm_num)
    refine ⟨δ, hδ, fun w hw => ?_⟩
    have h1 : dist (u w) (u 0) < 1/2 := hδ' (by simpa [dist_eq_norm] using hw)
    rw [hu0, dist_eq_norm] at h1
    linarith
  refine ⟨(3/2)*(‖iteratedDeriv 2 f 0/2‖+B)^2 + 2*(‖iteratedDeriv 2 f 0/2‖+B)^3 + B/2,
    min 1 (min δG δu), lt_min one_pos (lt_min hδGpos hδupos), ?_⟩
  intro z hz hzlt
  have hz_lt_one : ‖z‖ < 1 := lt_of_lt_of_le hzlt (min_le_left _ _)
  have hz1 : ‖z‖ ≤ 1 := le_of_lt hz_lt_one
  have hltδG : ‖z‖ < δG := lt_of_lt_of_le hzlt (le_trans (min_le_right _ _) (min_le_left _ _))
  have hltδu : ‖z‖ < δu := lt_of_lt_of_le hzlt (le_trans (min_le_right _ _) (min_le_right _ _))
  have hz2G : ‖z^2‖ < δG := by rw [norm_pow]; nlinarith [norm_nonneg z, hz1]
  have hz2u : ‖z^2‖ < δu := by rw [norm_pow]; nlinarith [norm_nonneg z, hz1]
  have hwball : z^2 ∈ Metric.ball 0 1 := by
    rw [Metric.mem_ball, dist_zero_right, norm_pow]
    nlinarith [norm_nonneg z]
  have hz_ne : z ≠ 0 := norm_pos_iff.mp hz
  have hz2_ne : z^2 ≠ 0 := pow_ne_zero 2 hz_ne
  have hrel : (u (z^2))^2 = 1 + (iteratedDeriv 2 f 0 / 2)*z^2 + z^4 * G (z^2) := by
    have h1 : u (z^2)^2 * z^2 = f (z^2) := hueq (z^2) hwball
    have h2 : f (z^2) = z^2 + (iteratedDeriv 2 f 0/2)*(z^2)^2 + (z^2)^3 * G (z^2) := hG (z^2)
    have : (u (z^2))^2 * z^2 = (1 + (iteratedDeriv 2 f 0 / 2)*z^2 + z^4 * G (z^2)) * z^2 := by
      rw [h1, h2]; ring
    exact mul_right_cancel₀ hz2_ne this
  have hU1 : ‖u (z^2) - 1‖ ≤ 1/2 := hubd (z^2) hz2u
  have hW : ‖G (z^2)‖ ≤ B := hGbd (z^2) hz2G
  have hkey := key_bound (u (z^2)) z (iteratedDeriv 2 f 0 / 2) (G (z^2)) B hz hz1 hU1 hW hB hrel
  have hrewrite : (1 / z + (-(iteratedDeriv 2 f 0) / 4) * z)
      = (1 / z - ((iteratedDeriv 2 f 0) / 2 / 2) * z) := by ring
  rw [hrewrite]
  exact hkey

end Work.LandLeaves
