import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.LatVec
import Submission.Work.BoseBoxFock.chiScale_image_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.kernelImage_le`

**The lemma.**  Let `0 < ℓ`, `0 ≤ R ≤ ℓ/2`, `W : ℝ³ → ℂ` with `‖W x‖ ≤ CW` and
`tsupport W ⊆ ball 0 R`.  Then for every `K : ℕ` there is `C ≥ 0`, *independent of `W`*, with

    ‖χ_ℓ(w) χ_ℓ(z) Σ_{m ≠ 0} W(w − z + ℓ m)‖ ≤ C (R/ℓ)^K CW        (all z w),

where `χ_ℓ = chiScale ℓ` is the corpus bump scaled to the ball of radius `ℓ/2` and
`m` runs over the nonzero integer vectors of `ℤ³` (`latVec`).

**Why it is true.**  Only the images `m ∈ {−1,0,1}³` can contribute: if some coordinate
satisfies `|m_i| ≥ 2`, then `‖ℓ • latVec m‖ ≥ 2ℓ`, while `χ_ℓ(w) ≠ 0` and `χ_ℓ(z) ≠ 0`
force `‖w‖, ‖z‖ < ℓ/2`, so `‖w − z + ℓ • latVec m‖ ≥ 2ℓ − ℓ = ℓ > R`, hence the point is
outside the support of `W` and the term vanishes.  So the sum is a finite sum of at most
`27` terms.

For a contributing `m ≠ 0` the point `w − z + ℓ • latVec m` lies in the support of `W`, so
`‖w − z − ℓ • latVec (−m)‖ < R`, i.e. `w` and `z` are `R`-close *along the lattice* — exactly
the hypothesis of the corpus lemma `chiScale_image_le`, which gives

    χ_ℓ(w) χ_ℓ(z) ≤ C₀ (R/ℓ)^K

thanks to the flatness of `χ` at the boundary of its support
(`Work.BoseFixB1.chi_boundary_taylor`).  Multiplying by `‖W‖ ≤ CW` and summing the `27`
terms gives the claim.

Everything here is elementary; the only analytic input is the PROVED
`Work.BoseBoxFock.chiScale_image_le`.
-/

namespace Work.BoseBoxFock

open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The lattice vector is additive under negation. -/
lemma latVec_neg (m : Fin 3 → ℤ) : latVec (-m) = -latVec m := by
  ext i
  simp [latVec]

/-- `chiScale ℓ x ≠ 0` forces `‖x‖ < ℓ/2`: the bump is supported in the open ball of radius
`ℓ/2`. -/
private lemma norm_lt_of_chiScale_ne_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {x : ℝ³}
    (hx : chiScale ℓ x ≠ 0) : ‖x‖ < ℓ / 2 := by
  have h1 : chi ((ℓ⁻¹ : ℝ) • x) ≠ 0 := by simpa only [chiScale] using hx
  have h2 : ‖(ℓ⁻¹ : ℝ) • x‖ < 1 / 2 := by
    by_contra hcon
    exact h1 (chi_eq_zero_of_half_le_norm _ (le_of_not_gt hcon))
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ), inv_mul_eq_div] at h2
  have h3 := (div_lt_iff₀ hℓ).mp h2
  linarith

/-- **Separation at the lattice scale.**  If `m` has a coordinate of absolute value at least
`2`, then for `w, z` in the support of `chiScale ℓ` the point `w − z + ℓ • latVec m` is at
distance `> R` from the origin (whenever `R ≤ ℓ/2`), hence outside the support of `W`. -/
private lemma latVec_far {ℓ R : ℝ} (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ / 2) {m : Fin 3 → ℤ}
    (hm : ∃ i, (2 : ℤ) ≤ |m i|) {w z : ℝ³} (hw : chiScale ℓ w ≠ 0)
    (hz : chiScale ℓ z ≠ 0) : R < ‖w - z + ℓ • latVec m‖ := by
  obtain ⟨i, hi⟩ := hm
  have hlat : (2 : ℝ) ≤ ‖latVec m‖ := by
    have h1 : ‖(latVec m).ofLp i‖ ≤ ‖latVec m‖ := PiLp.norm_apply_le (latVec m) i
    rw [latVec_apply, Real.norm_eq_abs] at h1
    have h2 : (2 : ℝ) ≤ |((m i : ℤ) : ℝ)| := by exact_mod_cast hi
    linarith
  have hw' : ‖w‖ < ℓ / 2 := norm_lt_of_chiScale_ne_zero hℓ hw
  have hz' : ‖z‖ < ℓ / 2 := norm_lt_of_chiScale_ne_zero hℓ hz
  have hlat2 : (2 : ℝ) * ℓ ≤ ‖ℓ • latVec m‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hℓ]
    have := mul_le_mul_of_nonneg_left hlat hℓ.le
    linarith
  have hsub : ‖w - z‖ < ℓ := by
    have := norm_sub_le w z
    linarith
  have hkey : ‖ℓ • latVec m‖ - ‖w - z‖ ≤ ‖w - z + ℓ • latVec m‖ := by
    have h6 := abs_norm_sub_norm_le (ℓ • latVec m) (w - z + ℓ • latVec m)
    have hsub6 : ℓ • latVec m - (w - z + ℓ • latVec m) = -(w - z) := by abel
    rw [hsub6, norm_neg] at h6
    have h7 := (abs_le.mp h6).2
    linarith
  linarith

/-- A function supported in `ball 0 R` vanishes outside that ball. -/
private lemma eq_zero_of_far {W : ℝ³ → ℂ} {R : ℝ}
    (hWs : tsupport W ⊆ Metric.ball (0 : ℝ³) R) {u : ℝ³} (hu : R ≤ ‖u‖) : W u = 0 := by
  by_contra hcon
  have hmem : u ∈ tsupport W := subset_tsupport W (Function.mem_support.mpr hcon)
  have h := hWs hmem
  rw [Metric.mem_ball, dist_eq_norm, sub_zero] at h
  linarith

theorem kernelImage_le {ℓ R CW : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R) (hRℓ : R ≤ ℓ / 2) (hCW : 0 ≤ CW)
    {W : EuclideanSpace ℝ (Fin 3) → ℂ} (hWb : ∀ x, ‖W x‖ ≤ CW)
    (hWs : tsupport W ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z w : EuclideanSpace ℝ (Fin 3),
      ‖((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)
          * ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ)
          * (∑' m : Fin 3 → ℤ, if m = 0 then (0 : ℂ)
              else W (w - z + ℓ • Work.BoseBoxFock.latVec m))‖
      ≤ C * (R / ℓ) ^ K * CW := by
  obtain ⟨C₀, hC₀nn, hC₀⟩ := chiScale_image_le hℓ hR (by linarith) K
  refine ⟨27 * C₀, by positivity, fun z w => ?_⟩
  have hχw : 0 ≤ chiScale ℓ w := chi_nonneg _
  have hχz : 0 ≤ chiScale ℓ z := chi_nonneg _
  have hKnn : 0 ≤ (R / ℓ) ^ K := pow_nonneg (div_nonneg hR hℓ.le) K
  set B : ℝ := C₀ * (R / ℓ) ^ K * CW with hB
  have hBnn : 0 ≤ B := by
    rw [hB]
    exact mul_nonneg (mul_nonneg hC₀nn hKnn) hCW
  -- the finite set of possibly contributing lattice vectors
  set S : Finset (Fin 3 → ℤ) := Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-1 : ℤ) 1)
    with hS
  have hS0 : (0 : Fin 3 → ℤ) ∈ S := by
    rw [hS, Fintype.mem_piFinset]
    intro i
    simp
  have hScard : (S.card : ℝ) ≤ 27 := by
    have h : S.card = 27 := by
      rw [hS]
      decide
    rw [h]
    norm_num
  -- per-term bound
  have hper : ∀ m : Fin 3 → ℤ, m ≠ 0 →
      ‖((chiScale ℓ w : ℝ) : ℂ) * ((chiScale ℓ z : ℝ) : ℂ)
        * W (w - z + ℓ • latVec m)‖ ≤ B := by
    intro m hm
    by_cases hW0 : W (w - z + ℓ • latVec m) = 0
    · rw [hW0, mul_zero, norm_zero]
      exact hBnn
    · have hlt : ‖w - z + ℓ • latVec m‖ < R := by
        by_contra hcon
        exact hW0 (eq_zero_of_far hWs (le_of_not_gt hcon))
      have hclose : chiScale ℓ w * chiScale ℓ z ≤ C₀ * (R / ℓ) ^ K := by
        have hwz : ‖z - w - ℓ • latVec m‖ ≤ R := by
          have h1 : z - w - ℓ • latVec m = -(w - z + ℓ • latVec m) := by abel
          rw [h1, norm_neg]
          exact hlt.le
        have h := hC₀ z w ⟨m, hm, hwz⟩
        calc chiScale ℓ w * chiScale ℓ z = chiScale ℓ z * chiScale ℓ w := mul_comm _ _
          _ ≤ C₀ * (R / ℓ) ^ K := h
      calc ‖((chiScale ℓ w : ℝ) : ℂ) * ((chiScale ℓ z : ℝ) : ℂ)
            * W (w - z + ℓ • latVec m)‖
          = chiScale ℓ w * chiScale ℓ z * ‖W (w - z + ℓ • latVec m)‖ := by
            rw [norm_mul, norm_mul, Complex.norm_of_nonneg hχw, Complex.norm_of_nonneg hχz]
        _ ≤ (C₀ * (R / ℓ) ^ K) * CW :=
            mul_le_mul hclose (hWb _) (norm_nonneg _) (mul_nonneg hC₀nn hKnn)
        _ = B := by rw [hB]
  -- the summand vanishes outside `S`
  have hsupp : ∀ m : Fin 3 → ℤ, m ∉ S →
      ((chiScale ℓ w : ℝ) : ℂ) * ((chiScale ℓ z : ℝ) : ℂ)
        * (if m = 0 then (0 : ℂ) else W (w - z + ℓ • latVec m)) = 0 := by
    intro m hmS
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hmS hS0
    rw [if_neg hm0]
    by_cases hχw0 : chiScale ℓ w = 0
    · rw [hχw0]
      simp
    by_cases hχz0 : chiScale ℓ z = 0
    · rw [hχz0]
      simp
    have hmem : ∃ i, (2 : ℤ) ≤ |m i| := by
      have hnot : ¬ ∀ i : Fin 3, m i ∈ Finset.Icc (-1 : ℤ) 1 := fun h =>
        hmS (by rw [hS, Fintype.mem_piFinset]; exact h)
      push Not at hnot
      obtain ⟨i, hi⟩ := hnot
      refine ⟨i, ?_⟩
      have h2 : ¬ (-(1 : ℤ) ≤ m i ∧ m i ≤ 1) := by simpa only [Finset.mem_Icc] using hi
      have hlt : m i < -1 ∨ 1 < m i := by omega
      rcases hlt with hh | hh
      · exact le_trans (by omega : (2 : ℤ) ≤ -(m i)) (neg_le_abs (m i))
      · exact le_trans (by omega : (2 : ℤ) ≤ m i) (le_abs_self (m i))
    rw [eq_zero_of_far hWs (le_of_lt (latVec_far hℓ hRℓ hmem hχw0 hχz0)), mul_zero]
  -- pull the prefactor into the sum, then evaluate the finitely supported sum
  have hpull : ((chiScale ℓ w : ℝ) : ℂ) * ((chiScale ℓ z : ℝ) : ℂ)
        * (∑' m : Fin 3 → ℤ, (if m = 0 then (0 : ℂ) else W (w - z + ℓ • latVec m)))
      = ∑ m ∈ S, ((chiScale ℓ w : ℝ) : ℂ) * ((chiScale ℓ z : ℝ) : ℂ)
          * (if m = 0 then (0 : ℂ) else W (w - z + ℓ • latVec m)) := by
    rw [← tsum_mul_left]
    exact tsum_eq_sum hsupp
  rw [hpull]
  calc ‖∑ m ∈ S, ((chiScale ℓ w : ℝ) : ℂ) * ((chiScale ℓ z : ℝ) : ℂ)
        * (if m = 0 then (0 : ℂ) else W (w - z + ℓ • latVec m))‖
      ≤ ∑ m ∈ S, ‖((chiScale ℓ w : ℝ) : ℂ) * ((chiScale ℓ z : ℝ) : ℂ)
        * (if m = 0 then (0 : ℂ) else W (w - z + ℓ • latVec m))‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ S, B := by
        refine Finset.sum_le_sum (fun m hmS => ?_)
        by_cases hm0 : m = 0
        · rw [if_pos hm0, mul_zero, norm_zero]
          exact hBnn
        · rw [if_neg hm0]
          exact hper m hm0
    _ = (S.card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 27 * B := mul_le_mul_of_nonneg_right hScard hBnn
    _ = 27 * C₀ * (R / ℓ) ^ K * CW := by rw [hB]; ring

end Work.BoseBoxFock
