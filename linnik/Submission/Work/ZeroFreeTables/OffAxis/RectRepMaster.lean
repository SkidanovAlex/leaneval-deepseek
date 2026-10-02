import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.RectRepDefs
import Submission.Work.ZeroFreeTables.P9.prim.masterP3_assembly
import Submission.Work.ZeroFreeTables.OffAxis.RepHMaster
import Submission.Work.ZeroFreeTables.OffAxis.pointEngine_prim_gen
import Submission.Work.ZeroFreeTables.P9.P3NearSumL_eq_nearP3sum
import Submission.Work.ZeroFreeTables.lam0w.Bounds

open DirichletCharacter Complex
open scoped Classical BigOperators

namespace Work.ZeroFreeTables.OffAxis

/-!
# ZeroFreeTables/OffAxis/RectRepMaster

The `P₃`-master bound at the **wide** height range `|Im s| ≤ 10·log q` (HB §9 at a repeated
zero, in the form needed by the rectangle/off-axis engine).

The engine `OffAxis.pointEngine_prim_gen` produces, for a primitive non-principal `χ`, a point
`s = 1 + a/L` and the log-derivative input in the `nearInvSum` form,

`Σ(s,χ) ≤ -nearP3sum + α·c + (α²/L²)·((1+4/δ²)·J + Ct) + (2/3)(α³/L³)·((2/δ)(1+4/δ²)·J + Ct)`

with `α = a + λ₁` and `J = P9.invSqSum N χ s`, and it carries **no** height restriction on `s`.
Everything that a height restriction would have supplied is confined to two places:

* the log-derivative slot, where `WideLogDerivHyp χ δ L c` is stated exactly on the strip and the
  height range `|Im s| ≤ 10L` used here (`invNearSum = nearInvSum` is the height-free bridge
  `P9.invNearSum_eq_tsum_gen`), and
* the far-zero sum `J = invSqSum`, bounded here by `CJ·(L+2)` on the wide range
  `‖s‖ ≤ 10L + 2` (`invSqSum_wide_scale`, from the proved uniform bound
  `lam0w.invSqSum_uniform`), the `log(2 + ‖s‖)` factor being absorbed into `L + 2`.

The residual quadratic and cubic error terms are then absorbed into `α·e` by
`err_absorb_wide` once `L ≥ 2(a+M)²((1+4/δ²)CJ + Ct)/(a·e)`-ish, which is what `L₀` encodes.
-/

/-! ## The wide-scale inverse-square zero-sum bound -/

/-- On the wide range `1 ≤ L`, `log N ≤ L`, `‖s‖ ≤ 10L + 2`, the multiplicity-weighted
inverse-square zero sum is `O(L)`: `invSqSum N χ s ≤ CJ (L + 2)` with `CJ` uniform in
`N`, `χ`, `s` and `L`. -/
theorem invSqSum_wide_scale :
    ∃ CJ : ℝ, 0 < CJ ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
      (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {s : ℂ} {L : ℝ}, 1 ≤ L →
      Real.log (N : ℝ) ≤ L → ‖s‖ ≤ 10 * L + 2 →
      Work.ZeroFreeTables.P9.invSqSum N χ s ≤ CJ * (L + 2) := by
  obtain ⟨C, hCpos, hC⟩ := Work.ZeroFreeTables.lam0w.invSqSum_uniform
  refine ⟨11 * C, by positivity, ?_⟩
  intro N _ χ hχ hprim s L hL1 hlogN hnorm
  have h1 := hC χ hχ hprim s
  have hlog2 : Real.log (2 + ‖s‖) ≤ 10 * L + 3 := by
    have hpos : (0 : ℝ) < 2 + ‖s‖ := by positivity
    calc Real.log (2 + ‖s‖) ≤ (2 + ‖s‖) - 1 := Real.log_le_sub_one_of_pos hpos
      _ ≤ (10 * L + 4) - 1 := by linarith only [hnorm]
      _ = 10 * L + 3 := by ring
  calc Work.ZeroFreeTables.P9.invSqSum N χ s
      ≤ C * (Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2) := h1
    _ ≤ C * (L + (10 * L + 3) + 2) := mul_le_mul_of_nonneg_left (by linarith only [hlogN, hlog2]) hCpos.le
    _ ≤ 11 * C * (L + 2) := by linarith only [hCpos, hL1]

/-! ## Absorbing the two error terms into `α·e` -/

/-- Elementary error bookkeeping: given the far-zero bound `J ≤ C(L+2)`, the parity bound
`0 ≤ Ct` and the threshold condition `K ≤ A·e·L` with
`K = 2·Amax²·(k2 C + Ct) + (4/3)·Amax³·(k3 C + Ct)`, the residual quadratic plus cubic
error terms at scale `L` are at most `A·e`. -/
theorem err_absorb_wide {A Amax k2 k3 C Ct J L e : ℝ}
    (hA : 0 ≤ A) (hAle : A ≤ Amax) (hAmax : 0 ≤ Amax) (hk2 : 0 ≤ k2) (hk3 : 0 ≤ k3)
    (hC : 0 ≤ C) (hCt : 0 ≤ Ct) (hJ : J ≤ C * (L + 2))
    (hL2 : 2 ≤ L) (hLpos : 0 < L)
    (hK : 2 * Amax ^ 2 * (k2 * C + Ct) + (4 / 3) * Amax ^ 3 * (k3 * C + Ct) ≤ A * e * L) :
    (A / L) ^ 2 * (k2 * J + Ct) + (2 / 3) * (A / L) ^ 3 * (k3 * J + Ct) ≤ A * e := by
  have hB2 : k2 * J + Ct ≤ (k2 * C + Ct) * (L + 2) := by
    have h1 : k2 * J ≤ k2 * (C * (L + 2)) := mul_le_mul_of_nonneg_left hJ hk2
    have h2 : Ct ≤ Ct * (L + 2) := le_mul_of_one_le_right hCt (by linarith only [hL2])
    have heq : (k2 * C + Ct) * (L + 2) = k2 * (C * (L + 2)) + Ct * (L + 2) := by ring
    linarith only [h1, h2, heq.le]
  have hB3 : k3 * J + Ct ≤ (k3 * C + Ct) * (L + 2) := by
    have h1 : k3 * J ≤ k3 * (C * (L + 2)) := mul_le_mul_of_nonneg_left hJ hk3
    have h2 : Ct ≤ Ct * (L + 2) := le_mul_of_one_le_right hCt (by linarith only [hL2])
    have heq : (k3 * C + Ct) * (L + 2) = k3 * (C * (L + 2)) + Ct * (L + 2) := by ring
    linarith only [h1, h2, heq.le]
  have h2n : 0 ≤ k2 * C := mul_nonneg hk2 hC
  have h3n : 0 ≤ k3 * C := mul_nonneg hk3 hC
  have hP2 : 0 ≤ (k2 * C + Ct) * (L + 2) := mul_nonneg (by linarith only [hCt, h2n]) (by linarith only [hL2])
  have hP3 : 0 ≤ (k3 * C + Ct) * (L + 2) := mul_nonneg (by linarith only [hCt, h3n]) (by linarith only [hL2])
  have hL2' : (L + 2) / L ^ 2 ≤ 2 / L := by
    rw [div_le_div_iff₀ (pow_pos hLpos 2) hLpos]; nlinarith only [hL2]
  have hL3' : (L + 2) / L ^ 3 ≤ 2 / L := by
    rw [div_le_div_iff₀ (pow_pos hLpos 3) hLpos]; nlinarith only [hL2, sq_nonneg L]
  have hnum2 : A ^ 2 ≤ Amax ^ 2 := pow_le_pow_left₀ hA hAle 2
  have hnum3 : A ^ 3 ≤ Amax ^ 3 := pow_le_pow_left₀ hA hAle 3
  have hA2eq : (A / L) ^ 2 = A ^ 2 / L ^ 2 := by rw [div_pow]
  have hA3eq : (A / L) ^ 3 = A ^ 3 / L ^ 3 := by rw [div_pow]
  have hA2nn : 0 ≤ A ^ 2 / L ^ 2 := by positivity
  have hA3nn : 0 ≤ (2 / 3) * (A ^ 3 / L ^ 3) := by positivity
  have herr2 : (A / L) ^ 2 * (k2 * J + Ct) ≤ Amax ^ 2 * (k2 * C + Ct) * (2 / L) := by
    rw [hA2eq]
    calc A ^ 2 / L ^ 2 * (k2 * J + Ct)
        ≤ A ^ 2 / L ^ 2 * ((k2 * C + Ct) * (L + 2)) := mul_le_mul_of_nonneg_left hB2 hA2nn
      _ ≤ Amax ^ 2 / L ^ 2 * ((k2 * C + Ct) * (L + 2)) := by
          apply mul_le_mul_of_nonneg_right _ hP2
          exact div_le_div_of_nonneg_right hnum2 (pow_pos hLpos 2).le
      _ = Amax ^ 2 * (k2 * C + Ct) * ((L + 2) / L ^ 2) := by ring
      _ ≤ Amax ^ 2 * (k2 * C + Ct) * (2 / L) :=
          mul_le_mul_of_nonneg_left hL2' (mul_nonneg (pow_nonneg hAmax 2) (by linarith only [hCt, h2n]))
  have herr3 : (2 / 3) * (A / L) ^ 3 * (k3 * J + Ct)
      ≤ (2 / 3) * Amax ^ 3 * (k3 * C + Ct) * (2 / L) := by
    rw [hA3eq]
    calc (2 / 3) * (A ^ 3 / L ^ 3) * (k3 * J + Ct)
        ≤ (2 / 3) * (A ^ 3 / L ^ 3) * ((k3 * C + Ct) * (L + 2)) :=
          mul_le_mul_of_nonneg_left hB3 hA3nn
      _ ≤ (2 / 3) * (Amax ^ 3 / L ^ 3) * ((k3 * C + Ct) * (L + 2)) := by
          apply mul_le_mul_of_nonneg_right _ hP3
          exact mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hnum3 (pow_pos hLpos 3).le) (by norm_num)
      _ = (2 / 3) * Amax ^ 3 * (k3 * C + Ct) * ((L + 2) / L ^ 3) := by ring
      _ ≤ (2 / 3) * Amax ^ 3 * (k3 * C + Ct) * (2 / L) :=
          mul_le_mul_of_nonneg_left hL3'
            (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hAmax 3)) (by linarith only [hCt, h3n]))
  have hsum : Amax ^ 2 * (k2 * C + Ct) * (2 / L)
        + (2 / 3) * Amax ^ 3 * (k3 * C + Ct) * (2 / L)
      = (2 * Amax ^ 2 * (k2 * C + Ct) + (4 / 3) * Amax ^ 3 * (k3 * C + Ct)) / L := by ring
  have hKL : (2 * Amax ^ 2 * (k2 * C + Ct) + (4 / 3) * Amax ^ 3 * (k3 * C + Ct)) / L
      ≤ A * e := by
    rw [div_le_iff₀ hLpos]; linarith only [hK]
  linarith only [herr2, herr3, hsum, hKL]

/-! ## The master bound -/

set_option maxHeartbeats 1000000 in
theorem RectRepMaster {a δ c e M : ℝ} (ha : 0 < a) (hδ0 : 0 < δ) (hδ1 : δ < 1) (he : 0 < e) :
    ∃ L₀ : ℝ, ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
      (hprim : χ.IsPrimitive) {L lam₁ : ℝ}, L₀ ≤ L → Real.log (N : ℝ) ≤ L → 0 ≤ lam₁ →
      lam₁ ≤ M → Work.ZeroFreeTables.OffAxis.WideLogDerivHyp χ δ L c →
      ∀ s : ℂ, s.re = 1 + a / L → |s.im| ≤ 10 * L →
        Work.ZeroFreeTables.SigmaP3L N L χ s a lam₁
          ≤ -Work.ZeroFreeTables.P3NearSumL N L χ s a lam₁ δ + (a + lam₁) * (c + e) := by
  obtain ⟨CJ, hCJpos, hCJ⟩ := invSqSum_wide_scale
  obtain ⟨Ct, hCtpos, hCt⟩ := Work.ZeroFreeTables.lam0w.paritySumBound
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 2 * (a + M) ^ 2 * ((1 + 4 / δ ^ 2) * CJ + Ct)
    + (4 / 3) * (a + M) ^ 3 * ((2 / δ) * (1 + 4 / δ ^ 2) * CJ + Ct) := ⟨_, rfl⟩
  refine ⟨max 4 (max (a + 2) (max (2 * a / δ)
    (max (Real.exp (max a a⁻¹) + 4) (K / (a * e))))), ?_⟩
  intro N _ χ hχ hprim L lam₁ hL hlogN hlam₁ hM hyp s hsre hsim
  -- ## the scale conditions carried by `L₀ ≤ L`
  have hX : max (a + 2) (max (2 * a / δ) (max (Real.exp (max a a⁻¹) + 4) (K / (a * e)))) ≤ L :=
    le_trans (le_max_right 4 _) hL
  have hY : max (2 * a / δ) (max (Real.exp (max a a⁻¹) + 4) (K / (a * e))) ≤ L :=
    le_trans (le_max_right (a + 2) _) hX
  have hZ : max (Real.exp (max a a⁻¹) + 4) (K / (a * e)) ≤ L :=
    le_trans (le_max_right (2 * a / δ) _) hY
  have hLge4 : 4 ≤ L := le_trans (le_max_left 4 _) hL
  have hLge2 : 2 ≤ L := by linarith only [hδ0, hδ1, hLge4]
  have hLpos : 0 < L := by linarith only [hδ0, hδ1, hLge4]
  have hLge1 : 1 ≤ L := by linarith only [hδ0, hδ1, hLge4]
  have ha2 : a + 2 ≤ L := le_trans (le_max_left (a + 2) _) hX
  have haL : a ≤ L := by linarith only [hδ0, hδ1, ha2]
  have h2aδ : 2 * a ≤ δ * L := by
    have h := le_trans (le_max_left (2 * a / δ) _) hY
    rw [div_le_iff₀ hδ0] at h
    linarith only [h]
  have hlogL_ge : max a a⁻¹ ≤ Real.log L := by
    have hexp : Real.exp (max a a⁻¹) ≤ L := by linarith only [le_trans (le_max_left _ _) hZ, hδ0, hδ1, hZ]
    have h := Real.log_le_log (Real.exp_pos (max a a⁻¹)) hexp
    rwa [Real.log_exp] at h
  have hmpos : 0 < max a a⁻¹ := lt_of_lt_of_le ha (le_max_left a a⁻¹)
  have hlogL_pos : 0 < Real.log L := lt_of_lt_of_le hmpos hlogL_ge
  have hKe : K ≤ a * e * L := by
    have h := le_trans (le_max_right _ _) hZ
    rw [div_le_iff₀ (mul_pos ha he)] at h
    calc K ≤ L * (a * e) := h
      _ = a * e * L := by ring
  -- ## the point `s` lies in the strip of `WideLogDerivHyp`
  have hs1 : 1 + 1 / (L * Real.log L) ≤ s.re := by
    rw [hsre]
    have h1 : 1 ≤ a * Real.log L := by
      have h := mul_le_mul_of_nonneg_left (le_trans (le_max_right a a⁻¹) hlogL_ge) (le_of_lt ha)
      rwa [mul_inv_cancel₀ (ne_of_gt ha)] at h
    have h2 : 1 / (L * Real.log L) ≤ a / L := by
      rw [div_le_div_iff₀ (by positivity : 0 < L * Real.log L) hLpos]
      nlinarith only [h1, hLpos, hδ0, hδ1, hLge4]
    linarith only [h2]
  have hs2 : s.re ≤ 1 + Real.log L / L := by
    rw [hsre]
    have h2 : a ≤ Real.log L := le_trans (le_max_left a a⁻¹) hlogL_ge
    have h3 : a / L ≤ Real.log L / L := by
      rw [div_le_div_iff₀ hLpos hLpos]
      nlinarith only [h2, hLpos, hδ0, hδ1, hLge4]
    linarith only [h3]
  -- ## the log-derivative slot, in the `nearInvSum` form required by the engine
  have hlog : (-logDeriv (DirichletCharacter.LFunction χ) s).re
      + Work.ZeroFreeTables.P9.nearInvSum N χ s δ ≤ c * L := by
    have hw := hyp s hs1 hs2 hsim
    have hb := Work.ZeroFreeTables.P9.invNearSum_eq_tsum_gen χ hχ hprim s hδ0 (le_of_lt hδ1)
    rw [← hb]
    exact hw
  -- ## the parity series
  obtain ⟨par, hpar0, hpar1⟩ : ∃ par : ℕ, (χ.Even → par = 0) ∧ (χ.Odd → par = 1) := by
    rcases χ.even_or_odd with hE | hO
    · exact ⟨0, fun _ => rfl, fun hO => absurd hO hE.not_odd⟩
    · exact ⟨1, fun hE => absurd hE hO.not_even, fun _ => rfl⟩
  have hpar_le : par ≤ 1 := by
    rcases χ.even_or_odd with hE | hO
    · rw [hpar0 hE]; exact zero_le_one
    · rw [hpar1 hO]
  have hs_gt : 1 < s.re := by
    have : 0 < a / L := div_pos ha hLpos
    rw [hsre]; linarith only [this]
  obtain ⟨hS2, hS3⟩ := hCt par hpar_le s hs_gt
  -- ## the pointwise engine
  have hpe := Work.ZeroFreeTables.OffAxis.pointEngine_prim_gen χ hχ hprim ha hlam₁ hδ0 hδ1
    (lt_of_lt_of_le one_lt_two hLge2) h2aδ hsre hlog par hpar0 hpar1 hS2 hS3
  have hbridge3 :=
    Work.ZeroFreeTables.P9.P3NearSumL_eq_nearP3sum (s := s) (δ := δ) χ hχ hprim hδ0
      (le_of_lt hδ1) a lam₁ L
  rw [← hbridge3] at hpe
  -- ## the far-zero sum on the wide range
  have hnorm : ‖s‖ ≤ 10 * L + 2 := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    have hre_nonneg : 0 ≤ s.re := by
      have : (0 : ℝ) ≤ a / L := div_nonneg ha.le hLpos.le
      rw [hsre]; linarith only [hδ0, hδ1, hsre, hs_gt]
    have habs : |s.re| = s.re := abs_of_nonneg hre_nonneg
    have hdiv : a / L ≤ 1 := (div_le_one hLpos).mpr haL
    calc ‖s‖ ≤ |s.re| + |s.im| := h
      _ = s.re + |s.im| := by rw [habs]
      _ = 1 + a / L + |s.im| := by rw [hsre]
      _ ≤ 1 + 1 + 10 * L := by linarith only [hsim, hdiv]
      _ = 10 * L + 2 := by ring
  have hJ := hCJ (s := s) (L := L) χ hχ hprim hLge1 hlogN hnorm
  -- ## absorbing the error
  have hA0 : 0 ≤ a + lam₁ := by linarith only [ha, hlam₁]
  have hAmax : 0 ≤ a + M := by linarith only [ha, hlam₁, hM]
  have hAle : a + lam₁ ≤ a + M := by linarith only [hM]
  have hk2 : (0 : ℝ) ≤ 1 + 4 / δ ^ 2 := by
    have : (0 : ℝ) ≤ 4 / δ ^ 2 := div_nonneg (by norm_num) (sq_nonneg δ)
    linarith only [hδ0, hδ1, this]
  have hk3 : (0 : ℝ) ≤ (2 / δ) * (1 + 4 / δ ^ 2) := by positivity
  have hKbig : K ≤ (a + lam₁) * e * L := by
    have h1 : a ≤ a + lam₁ := le_add_of_nonneg_right hlam₁
    have h2 : a * e ≤ (a + lam₁) * e := mul_le_mul_of_nonneg_right h1 he.le
    have h3 : a * e * L ≤ (a + lam₁) * e * L := mul_le_mul_of_nonneg_right h2 hLpos.le
    exact le_trans hKe h3
  have herr := err_absorb_wide (A := a + lam₁) (Amax := a + M) (k2 := 1 + 4 / δ ^ 2)
    (k3 := (2 / δ) * (1 + 4 / δ ^ 2)) (C := CJ) (Ct := Ct)
    (J := Work.ZeroFreeTables.P9.invSqSum N χ s) (L := L) (e := e)
    hA0 hAle hAmax hk2 hk3 hCJpos.le hCtpos.le hJ hLge2 hLpos
    (by rw [← hKdef]; exact hKbig)
  have herr' : ((a + lam₁) ^ 2 / L ^ 2)
        * ((1 + 4 / δ ^ 2) * Work.ZeroFreeTables.P9.invSqSum N χ s + Ct)
      + (2 / 3) * ((a + lam₁) ^ 3 / L ^ 3)
        * ((2 / δ) * (1 + 4 / δ ^ 2) * Work.ZeroFreeTables.P9.invSqSum N χ s + Ct)
      ≤ (a + lam₁) * e := by
    rw [show (a + lam₁) ^ 2 / L ^ 2 = ((a + lam₁) / L) ^ 2 from by rw [div_pow],
      show (a + lam₁) ^ 3 / L ^ 3 = ((a + lam₁) / L) ^ 3 from by rw [div_pow]]
    exact herr
  have hce : (a + lam₁) * c + (a + lam₁) * e = (a + lam₁) * (c + e) := by ring
  linarith [hpe, herr', hce]

end Work.ZeroFreeTables.OffAxis
