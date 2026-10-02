import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open Filter Asymptotics Set
open scoped Topology

/-- Pointwise second-order bound for the expansion of `‖1 + z‖` near `0`:
for `‖z‖ ≤ 1/2`, the modulus `‖1 + z‖` differs from `1 + z.re` by at most `2 ‖z‖^2`. -/
lemma norm_oneAdd_sub_one_sub_re_le (z : ℂ) (hz : ‖z‖ ≤ 1 / 2) :
    |‖1 + z‖ - 1 - z.re| ≤ 2 * ‖z‖ ^ 2 := by
  have hsq : ‖1 + z‖ ^ 2 = (1 + z.re) ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
    ring
  have hzre : -(1 / 2 : ℝ) ≤ z.re := (abs_le.mp (le_trans (Complex.abs_re_le_norm z) hz)).1
  have hqnn : 0 ≤ 1 + z.re := by linarith
  have hznn2 : (0 : ℝ) ≤ ‖z‖ ^ 2 := sq_nonneg _
  have him2 : z.im ^ 2 ≤ ‖z‖ ^ 2 := by
    have h := Complex.abs_im_le_norm z
    rw [← sq_abs z.im]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have hle2 : 1 + z.re ≤ ‖1 + z‖ := by
    have himnn : (0 : ℝ) ≤ z.im ^ 2 := sq_nonneg _
    have hsq2 : (1 + z.re) ^ 2 ≤ ‖1 + z‖ ^ 2 := by rw [hsq]; linarith
    have h := sq_le_sq.mp hsq2
    rwa [abs_of_nonneg hqnn, abs_of_nonneg (norm_nonneg _)] at h
  have hle3 : ‖1 + z‖ ≤ 1 + z.re + 2 * ‖z‖ ^ 2 := by
    have hkey : ‖1 + z‖ ^ 2 ≤ (1 + z.re + 2 * ‖z‖ ^ 2) ^ 2 := by
      rw [hsq]
      nlinarith [hz, hqnn, him2, hznn2, sq_nonneg (‖z‖ ^ 2)]
    have h := sq_le_sq.mp hkey
    rwa [abs_of_nonneg (norm_nonneg _),
      abs_of_nonneg (by linarith : 0 ≤ 1 + z.re + 2 * ‖z‖ ^ 2)] at h
  rw [show ‖1 + z‖ - 1 - z.re = ‖1 + z‖ - (1 + z.re) by ring,
    abs_of_nonneg (by linarith : 0 ≤ ‖1 + z‖ - (1 + z.re))]
  linarith

/-- From the first-order expansion of `F` at `0` with multiplier `lam` of modulus one, deduce the
first-order expansion of the modulus ratio `‖F w‖ / ‖w‖`: the correction term at order `n ≥ 1` is
`Re ((c / lam) * w ^ n)`.
Hint: write `F w = lam * w * (1 + u w)` with `u w = (c/lam) * w^n + o(w^n)`, then use
`‖1 + u‖ = 1 + u.re + O(‖u‖^2)` (from `Complex.normSq`), and `‖u‖^2 = O(‖w‖^(2n)) = o(‖w‖^n)`. -/
theorem tendsto_normRatio_sub {F : ℂ → ℂ} {lam c : ℂ} {n : ℕ} (hn : 1 ≤ n) (hlam : ‖lam‖ = 1)
    (h : Asymptotics.IsLittleO (𝓝 0) (fun w : ℂ => F w - lam * w - c * w ^ (n + 1)) (fun w : ℂ => w ^ (n + 1))) :
    Filter.Tendsto (fun w : ℂ => (‖F w‖ / ‖w‖ - 1 - ((c / lam) * w ^ n).re) / ‖w‖ ^ n) (𝓝[≠] 0) (𝓝 0) := by
  have hlam0 : lam ≠ 0 := by rintro rfl; simp at hlam
  obtain ⟨ψ, hψ, hφψ⟩ := h.exists_eq_mul
  let U : ℂ → ℂ := fun w => ((c + ψ w) / lam) * w ^ n
  let r : ℂ → ℂ := fun w => (1 / lam) * (ψ w * w ^ n)
  let D : ℂ → ℝ := fun w => ‖w‖ ^ n
  have hψn : Tendsto (fun w : ℂ => ‖ψ w‖) (𝓝 0) (𝓝 0) := by simpa using hψ.norm
  -- `w ↦ ψ w * w^n` is little-o of `w^n`
  have hψ0 : (fun w : ℂ => ψ w * w ^ n) =o[𝓝 0] (fun w : ℂ => w ^ n) := by
    rw [isLittleO_iff]
    intro e he
    filter_upwards [(tendsto_order.1 hψn).2 e he] with w hw
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (le_of_lt hw) (norm_nonneg _)
  have hr : r =o[𝓝 0] (fun w : ℂ => w ^ n) := hψ0.const_mul_left (1 / lam)
  have hrU : ∀ w, U w = (c / lam) * w ^ n + (1 / lam) * (ψ w * w ^ n) := by
    intro w; simp only [U]; field_simp
  -- the real part of `r`
  have hR : (fun w : ℂ => (r w).re) =o[𝓝 0] D := by
    have hRn : (fun w : ℂ => (r w).re) =o[𝓝 0] (fun w : ℂ => w ^ n) := by
      rw [isLittleO_iff] at hr ⊢
      intro e he
      filter_upwards [hr he] with w hw
      rw [Real.norm_eq_abs]
      calc |(r w).re| ≤ ‖r w‖ := Complex.abs_re_le_norm _
        _ ≤ e * ‖w ^ n‖ := hw
    simpa only [D, norm_pow] using hRn.norm_right
  -- `U = O(w^n)`
  have hbO : (fun w : ℂ => (c / lam) * w ^ n) =O[𝓝 0] (fun w : ℂ => w ^ n) :=
    IsBigO.of_bound ‖c / lam‖ (Eventually.of_forall fun w => by rw [norm_mul])
  have hUO : U =O[𝓝 0] (fun w : ℂ => w ^ n) := by
    refine (hbO.add hr.isBigO).congr' ?_ EventuallyEq.rfl
    exact Eventually.of_forall fun w => (hrU w).symm
  have hU0 : Tendsto U (𝓝 0) (𝓝 0) := by
    refine hUO.trans_tendsto ?_
    simpa only [zero_pow (show n ≠ 0 by omega)] using (continuous_pow n).tendsto (0 : ℂ)
  -- `w^{2n} = o (‖w‖^n)`
  have hpowD : (fun w : ℂ => w ^ (2 * n)) =o[𝓝 0] D := by
    have h := (isLittleO_pow_pow (𝕜 := ℂ) (m := n) (n := 2 * n) (by omega)).norm_right
    simpa only [D, norm_pow] using h
  -- `‖U w‖^2 = o (‖w‖^n)`
  have hU2 : (fun w : ℂ => ‖U w‖ ^ 2) =o[𝓝 0] D := by
    have hp0 : (fun w : ℂ => U w ^ 2) =O[𝓝 0] (fun w : ℂ => (w ^ n) ^ 2) := hUO.pow 2
    have h2 : (fun w : ℂ => (w ^ n) ^ 2) = (fun w : ℂ => w ^ (2 * n)) := by
      funext w; rw [← pow_mul, Nat.mul_comm]
    rw [h2] at hp0
    have hres : (fun w : ℂ => U w ^ 2) =o[𝓝 0] D := hp0.trans_isLittleO hpowD
    simpa only [norm_pow] using hres.norm_left
  -- pointwise expansion of `‖1 + U w‖`
  have hP : (fun w : ℂ => ‖1 + U w‖ - 1 - (U w).re) =O[𝓝 0] (fun w : ℂ => ‖U w‖ ^ 2) := by
    refine IsBigO.of_bound 2 ?_
    have hUn : Tendsto (fun w : ℂ => ‖U w‖) (𝓝 0) (𝓝 (0 : ℝ)) := by simpa using hU0.norm
    have hsmall : ∀ᶠ w in 𝓝 0, ‖U w‖ ≤ 1 / 2 :=
      ((tendsto_order.1 hUn).2 (1 / 2) (by norm_num)).mono fun w hw => le_of_lt hw
    filter_upwards [hsmall] with w hw
    simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖U w‖))]
    exact norm_oneAdd_sub_one_sub_re_le (U w) hw
  have hP' : (fun w : ℂ => ‖1 + U w‖ - 1 - (U w).re) =o[𝓝 0] D := hP.trans_isLittleO hU2
  have hPR : (fun w : ℂ => (‖1 + U w‖ - 1 - (U w).re) + (r w).re) =o[𝓝 0] D := hP'.add hR
  -- `F w = lam * w * (1 + U w)` eventually
  have hF : ∀ᶠ w in 𝓝 0, F w = lam * w * (1 + U w) := by
    filter_upwards [hφψ] with w hw
    simp only [Pi.mul_apply] at hw
    have h1 : F w = lam * w + c * w ^ (n + 1) + ψ w * w ^ (n + 1) := by
      rw [← hw]; ring
    rw [h1]
    simp only [U]
    field_simp
    ring
  -- eventual agreement of the target function with `P + R`
  have hfeq : (fun w : ℂ => (‖F w‖ / ‖w‖ - 1 - ((c / lam) * w ^ n).re)) =ᶠ[𝓝[≠] 0]
      (fun w : ℂ => (‖1 + U w‖ - 1 - (U w).re) + (r w).re) := by
    have hF' : ∀ᶠ w in 𝓝[≠] 0, F w = lam * w * (1 + U w) := hF.filter_mono nhdsWithin_le_nhds
    have hw0 : ∀ᶠ w : ℂ in 𝓝[≠] 0, w ≠ 0 := self_mem_nhdsWithin
    filter_upwards [hF', hw0] with w hFw hwne
    rw [hFw]
    have hwn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hwne
    have hrr : r w = U w - (c / lam) * w ^ n := by
      simp only [U, r]; field_simp; ring
    rw [norm_mul, norm_mul, hlam, one_mul, mul_div_cancel_left₀ _ hwn, hrr, Complex.sub_re]
    ring
  have hPRsub : (fun w : ℂ => (‖1 + U w‖ - 1 - (U w).re) + (r w).re) =o[𝓝[≠] 0] D :=
    hPR.mono nhdsWithin_le_nhds
  have hf : (fun w : ℂ => (‖F w‖ / ‖w‖ - 1 - ((c / lam) * w ^ n).re)) =o[𝓝[≠] 0] D :=
    hPRsub.congr' hfeq.symm EventuallyEq.rfl
  simpa only [D] using hf.tendsto_div_nhds_zero

end Work.LandLeaves
