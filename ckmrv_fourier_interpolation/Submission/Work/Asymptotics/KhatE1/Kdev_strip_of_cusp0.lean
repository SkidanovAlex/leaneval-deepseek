import Mathlib
import Submission.Work.Asymptotics.KhatE1Defs
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.KhatE1.STPure
import Submission.Work.Asymptotics.Compact.gfun_eq

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

/-- On the funnel, `scale (S • τ) ≤ 3 * (scale τ) ^ 2`.  (A crude upper bound, dual to
`E_scale_S_le`; only the existence of a polynomial bound is used downstream.) -/
lemma funnel_scale_S_le (τ : ℍ) (hτ : Work.Asymptotics.Funnel τ) :
    Work.Kernels.scale (ModularGroup.S • τ) ≤ 3 * (Work.Kernels.scale τ) ^ 2 := by
  have hj : Work.Kernels.jFun ModularGroup.S (τ : ℂ) = (τ : ℂ) := by
    rw [Work.Kernels.jFun_apply]; simp
  have himS : (ModularGroup.S • τ).im = τ.im / ‖(τ : ℂ)‖ ^ 2 := by
    rw [Work.Kernels.im_smul_eq, hj]
  have hnormS : ‖((ModularGroup.S • τ : ℍ) : ℂ)‖ = (‖(τ : ℂ)‖)⁻¹ := by
    rw [Work.Kernels.S_smul_coe, norm_neg, norm_inv]
  have himpos : (0 : ℝ) < τ.im := τ.im_pos
  have him1 : (1 : ℝ) ≤ τ.im := by have := hτ.2; linarith
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hspos : (0 : ℝ) < Work.Kernels.scale τ := Work.Kernels.scale_pos τ
  have hnsq : ‖(τ : ℂ)‖ ^ 2 = τ.re ^ 2 + τ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  have hs : Work.Kernels.scale τ = 1 + (τ.im)⁻¹ + ‖(τ : ℂ)‖ := rfl
  have hsS : Work.Kernels.scale (ModularGroup.S • τ)
      = 1 + ((ModularGroup.S • τ).im)⁻¹ + ‖((ModularGroup.S • τ : ℍ) : ℂ)‖ := rfl
  have hnorm_le : ‖(τ : ℂ)‖ ≤ Work.Kernels.scale τ := Work.Kernels.coe_norm_le_scale τ
  -- `‖τ‖² / Im τ ≤ (scale τ)²`
  have h2 : ‖(τ : ℂ)‖ ^ 2 / τ.im ≤ (Work.Kernels.scale τ) ^ 2 := by
    rw [div_le_iff₀ himpos]
    have hb2 : ‖(τ : ℂ)‖ ≤ τ.im * Work.Kernels.scale τ := by nlinarith [hnorm_le, him1, hs1]
    have h3 : ‖(τ : ℂ)‖ * ‖(τ : ℂ)‖
        ≤ (Work.Kernels.scale τ) * (τ.im * Work.Kernels.scale τ) :=
      mul_le_mul hnorm_le hb2 (norm_nonneg _) (by positivity)
    nlinarith [h3, hnorm_le, hspos, himpos]
  have hinvS : ((ModularGroup.S • τ).im)⁻¹ ≤ (Work.Kernels.scale τ) ^ 2 := by
    rw [himS, inv_div]; exact h2
  have hnormS_le : ‖((ModularGroup.S • τ : ℍ) : ℂ)‖ ≤ Work.Kernels.scale τ := by
    rw [hnormS]
    exact le_trans (inv_anti₀ himpos (Work.Kernels.im_le_coe_norm τ))
      (Work.Kernels.inv_im_le_scale τ)
  have hs2 : (1 : ℝ) ≤ (Work.Kernels.scale τ) ^ 2 := one_le_pow₀ hs1
  rw [hsS, hs]
  nlinarith [hinvS, hnormS_le, hs1, hs2, hspos]

/-- **`S`-transport reduction.**  A sharp cusp-0 estimate for `K - 𝒢` on the tile `E = KEpsilon`,
uniform in a `z`-condition `P z t` (e.g. `(z : ℂ) = t * I`, or `0 ≤ z.re ∧ z.re ≤ 1 ∧ z.im = t`)
implies the corresponding sharp estimate for the deviation `Kdev = K̂ - (𝒢₊ - 𝒢₋)/2` on the
funnel, by the `S`-transport in the `τ` variable:
`Kdev(τ,z) = -τ^{-d/2} (K(w,z) - (𝒢₊ + 𝒢₋)/2)|_{w = S τ}`. -/
theorem strip_sharp_of_cusp0_gen (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (P : ℍ → ℝ → Prop)
    (h : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w z : UpperHalfPlane) (t : ℝ), w ∈ Work.Asymptotics.KEpsilon →
        (ModularGroup.S • w).im + 1 ≤ t → P z t →
        ‖Work.Kernels.Kfun ℓ d w z
            - (Work.Asymptotics.Compact.Gplus d w z
                + Work.Asymptotics.Compact.Gminus d ℓ w z) / 2‖
          ≤ C * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖ * (Work.Kernels.scale w) ^ N
              * (1 + t) ^ M * Real.exp (-(Real.pi * t))) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t → P z t →
        ‖Work.Asymptotics.Kdev ℓ d τ z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(Real.pi * t)) := by
  obtain ⟨C, N, M, hC, hN, hM, hh⟩ := h
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (d : ℤ) / 2 = (k : ℤ) := by
    rcases hd with rfl | rfl
    · exact ⟨4, by norm_num⟩
    · exact ⟨12, by norm_num⟩
  refine ⟨C * 3 ^ N + 1, 2 * N, M, by positivity, by linarith, hM, ?_⟩
  intro τ z t hτ ht hP
  set w : ℍ := ModularGroup.S • τ with hwdef
  have hw : w ∈ Work.Asymptotics.KEpsilon := by
    rw [hwdef]
    exact Work.Asymptotics.S_smul_mem_KEpsilon hτ.1 hτ.2
  have hSw : ModularGroup.S • w = τ := by
    rw [hwdef]
    exact Work.Asymptotics.S_smul_S_smul τ
  have hthr : (ModularGroup.S • w).im + 1 ≤ t := by rw [hSw]; exact ht
  have hb := hh w z t hw hthr hP
  have hbτ : ‖Work.Kernels.Kfun ℓ d (ModularGroup.S • τ) z
        - (Work.Asymptotics.Compact.Gplus d (ModularGroup.S • τ) z
            + Work.Asymptotics.Compact.Gminus d ℓ (ModularGroup.S • τ) z) / 2‖
      ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale (ModularGroup.S • τ)) ^ N
          * (1 + t) ^ M * Real.exp (-(Real.pi * t)) := by
    rw [hwdef] at hb
    rw [Work.Asymptotics.S_smul_S_smul τ] at hb
    exact hb
  have hsum : Work.Asymptotics.Compact.Gfun d ℓ (ModularGroup.S • τ) z
      = (Work.Asymptotics.Compact.Gplus d (ModularGroup.S • τ) z
          + Work.Asymptotics.Compact.Gminus d ℓ (ModularGroup.S • τ) z) / 2 := by
    have h1 := Work.Asymptotics.Compact.gfun_eq ℓ d hd (ModularGroup.S • τ) z
    rw [h1]; ring
  have hkz : (τ : ℂ) ^ (-((d : ℤ) / 2)) * (τ : ℂ) ^ ((d : ℤ) / 2) = 1 := by
    rw [← zpow_add₀ τ.ne_zero]; simp
  have hdev : Work.Asymptotics.Kdev ℓ d τ z
      = - (τ : ℂ) ^ (-((d : ℤ) / 2))
          * (Work.Kernels.Kfun ℓ d (ModularGroup.S • τ) z
              - Work.Asymptotics.Compact.Gfun d ℓ (ModularGroup.S • τ) z) := by
    have hK := Work.Asymptotics.KhatE1.STPure.Khat_eq_neg_slash_pointwise ℓ d hd τ z
    have hgs := Work.Asymptotics.KhatE1.STPure.Gfun_S_smul ℓ d hd τ z
    have hGp : (Work.Asymptotics.Compact.Gplus d τ z
          - Work.Asymptotics.Compact.Gminus d ℓ τ z) / 2
        = - (τ : ℂ) ^ (-((d : ℤ) / 2))
            * Work.Asymptotics.Compact.Gfun d ℓ (ModularGroup.S • τ) z := by
      have h1 : Work.Asymptotics.Compact.Gfun d ℓ (ModularGroup.S • τ) z
          = - (τ : ℂ) ^ ((d : ℤ) / 2)
              * ((Work.Asymptotics.Compact.Gplus d τ z
                  - Work.Asymptotics.Compact.Gminus d ℓ τ z) / 2) := by
        rw [hgs]; ring
      rw [h1, show - (τ : ℂ) ^ (-((d : ℤ) / 2))
            * (- (τ : ℂ) ^ ((d : ℤ) / 2)
              * ((Work.Asymptotics.Compact.Gplus d τ z
                  - Work.Asymptotics.Compact.Gminus d ℓ τ z) / 2))
          = ((τ : ℂ) ^ (-((d : ℤ) / 2)) * (τ : ℂ) ^ ((d : ℤ) / 2))
              * ((Work.Asymptotics.Compact.Gplus d τ z
                  - Work.Asymptotics.Compact.Gminus d ℓ τ z) / 2) from by ring]
      rw [hkz]; ring
    rw [Work.Asymptotics.Kdev, hK, hGp]
    ring
  have hcoe : ‖(τ : ℂ) ^ (-((d : ℤ) / 2))‖ ≤ 1 := by
    have h2 : (1 : ℝ) ≤ ‖(τ : ℂ)‖ := by
      have h3 : (2 : ℝ) ≤ τ.im := hτ.2
      linarith [Work.Kernels.im_le_coe_norm τ]
    have h1 : (1 : ℝ) ≤ ‖(τ : ℂ)‖ ^ k := one_le_pow₀ h2
    have hkk : (τ : ℂ) ^ (-((d : ℤ) / 2)) = ((τ : ℂ) ^ k)⁻¹ := by
      rw [zpow_neg, hk, zpow_natCast]
    rw [hkk, norm_inv, norm_pow]
    exact inv_le_one_of_one_le₀ h1
  have hw0 : (0 : ℝ) < Work.Kernels.scale w := Work.Kernels.scale_pos w
  have hsc : (Work.Kernels.scale w) ^ N ≤ (3 : ℝ) ^ N * (Work.Kernels.scale τ) ^ (2 * N) := by
    have hle : Work.Kernels.scale w ≤ 3 * (Work.Kernels.scale τ) ^ 2 := by
      rw [hwdef]; exact funnel_scale_S_le τ hτ
    have h0 : (0 : ℝ) ≤ 3 := by norm_num
    calc (Work.Kernels.scale w) ^ N ≤ (3 * (Work.Kernels.scale τ) ^ 2) ^ N :=
          Real.rpow_le_rpow (le_of_lt hw0) hle hN
      _ = (3 : ℝ) ^ N * ((Work.Kernels.scale τ) ^ 2) ^ N :=
          Real.mul_rpow h0 (by positivity)
      _ = (3 : ℝ) ^ N * (Work.Kernels.scale τ) ^ (2 * N) := by
          rw [show (((Work.Kernels.scale τ) ^ 2 : ℝ)) = (Work.Kernels.scale τ) ^ ((2 : ℕ) : ℝ) by
                rw [Real.rpow_natCast],
            Real.rpow_mul (le_of_lt (Work.Kernels.scale_pos τ))]
          norm_num
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  have hsN : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ (2 * N) :=
    Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos τ)) (2 * N)
  have ht1 : (0 : ℝ) ≤ 1 + t := by
    have h3 : (2 : ℝ) ≤ τ.im := hτ.2
    linarith
  have htM : (0 : ℝ) ≤ (1 + t) ^ M := Real.rpow_nonneg ht1 M
  have he0 : (0 : ℝ) ≤ Real.exp (-(Real.pi * t)) := Real.exp_nonneg _
  have hKN : (0 : ℝ) ≤ (3 : ℝ) ^ N := Real.rpow_nonneg (by norm_num) N
  calc ‖Work.Asymptotics.Kdev ℓ d τ z‖
      = ‖(τ : ℂ) ^ (-((d : ℤ) / 2))‖
          * ‖Work.Kernels.Kfun ℓ d (ModularGroup.S • τ) z
              - Work.Asymptotics.Compact.Gfun d ℓ (ModularGroup.S • τ) z‖ := by
        rw [hdev, norm_mul, norm_neg]
    _ = ‖(τ : ℂ) ^ (-((d : ℤ) / 2))‖
          * ‖Work.Kernels.Kfun ℓ d (ModularGroup.S • τ) z
              - (Work.Asymptotics.Compact.Gplus d (ModularGroup.S • τ) z
                  + Work.Asymptotics.Compact.Gminus d ℓ (ModularGroup.S • τ) z) / 2‖ := by
        rw [hsum]
    _ ≤ 1 * (C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale (ModularGroup.S • τ)) ^ N
          * (1 + t) ^ M * Real.exp (-(Real.pi * t))) :=
        mul_le_mul hcoe hbτ (norm_nonneg _) (by norm_num)
    _ = C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale w) ^ N
          * (1 + t) ^ M * Real.exp (-(Real.pi * t)) := by rw [hwdef]; ring
    _ ≤ C * ‖Work.Kernels.qParamFun τ‖ * ((3 : ℝ) ^ N * (Work.Kernels.scale τ) ^ (2 * N))
          * (1 + t) ^ M * Real.exp (-(Real.pi * t)) := by
        have h4 : (0 : ℝ) ≤ C * ‖Work.Kernels.qParamFun τ‖ := mul_nonneg hC.le hq0
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsc h4) htM) he0
    _ ≤ (C * 3 ^ N + 1) * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (2 * N)
          * (1 + t) ^ M * Real.exp (-(Real.pi * t)) := by
        have h3 : (0 : ℝ) ≤ C * 3 ^ N := mul_nonneg hC.le hKN
        have h5 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (2 * N)
              * (1 + t) ^ M * Real.exp (-(Real.pi * t)) := by positivity
        nlinarith [h3, h5]

/-- The strip form (used to reduce `Kdev_strip_sharp` to the cusp-0 strip estimate). -/
theorem strip_sharp_of_cusp0 (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (h : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w z : UpperHalfPlane) (t : ℝ), w ∈ Work.Asymptotics.KEpsilon →
        (ModularGroup.S • w).im + 1 ≤ t → 0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖Work.Kernels.Kfun ℓ d w z
            - (Work.Asymptotics.Compact.Gplus d w z
                + Work.Asymptotics.Compact.Gminus d ℓ w z) / 2‖
          ≤ C * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖ * (Work.Kernels.scale w) ^ N
              * (1 + t) ^ M * Real.exp (-(Real.pi * t))) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖Work.Asymptotics.Kdev ℓ d τ z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(Real.pi * t)) := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  obtain ⟨C', N', M', hC', hN', hM', hbd⟩ :=
    strip_sharp_of_cusp0_gen ℓ d hd (fun z t => 0 ≤ z.re ∧ z.re ≤ 1 ∧ z.im = t)
      ⟨C, N, M, hC, hN, hM, fun w z t hw ht hP => hb w z t hw ht hP.1 hP.2.1 hP.2.2⟩
  exact ⟨C', N', M', hC', hN', hM',
    fun τ z t hτ ht h1 h2 h3 => hbd τ z t hτ ht ⟨h1, h2, h3⟩⟩

/-- The axis form (used to reduce the funnel-axis bound to the cusp-0 axis estimate). -/
theorem axis_sharp_of_cusp0 (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (h : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w z : UpperHalfPlane) (t : ℝ), w ∈ Work.Asymptotics.KEpsilon →
        (ModularGroup.S • w).im + 1 ≤ t → (z : ℂ) = (t : ℂ) * Complex.I →
        ‖Work.Kernels.Kfun ℓ d w z
            - (Work.Asymptotics.Compact.Gplus d w z
                + Work.Asymptotics.Compact.Gminus d ℓ w z) / 2‖
          ≤ C * ‖Work.Kernels.qParamFun (ModularGroup.S • w)‖ * (Work.Kernels.scale w) ^ N
              * (1 + t) ^ M * Real.exp (-(Real.pi * t))) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        (z : ℂ) = (t : ℂ) * Complex.I →
        ‖Work.Asymptotics.Kdev ℓ d τ z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(Real.pi * t)) := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  obtain ⟨C', N', M', hC', hN', hM', hbd⟩ :=
    strip_sharp_of_cusp0_gen ℓ d hd (fun z t => (z : ℂ) = (t : ℂ) * Complex.I)
      ⟨C, N, M, hC, hN, hM, fun w z t hw ht hP => hb w z t hw ht hP⟩
  exact ⟨C', N', M', hC', hN', hM', fun τ z t hτ ht hz => hbd τ z t hτ ht hz⟩

end Work.Asymptotics.KhatE1
