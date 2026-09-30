import Mathlib
import Submission.Work.BMF.mr_core_defs
import Submission.Work.BMF.halasz_complex
import Submission.Work.BMF.mr_direct.halasz_twisted
import Submission.Work.BMF.mr_direct.window_M_le
import Submission.Work.BMF.mr_direct.dist_scale_transfer_wide
import Submission.Work.BMF.mr_core.dirPolyD_abel_le
import Submission.Work.BMF.mr_core.exists_B_C_le
import Submission.Work.BMF.mr_core.rpow_eighth_le_ceil_sub_one

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The "small `T`" case of the critical regime

`Work.BMF.mr_core.smallT_le`: the case `Y/H ≤ T ≤ 3` of the Matomäki–Radziwiłł input
`Work.BMF.CoreInput`, in the Dirichlet-polynomial form.

Since `T ≤ 3` and `T ≥ Y/H`, the whole activity sits at frequencies `|t| ≤ 2T ≤ 6` and the
window ratio is `ρ = Y/H ≤ 3`, so `ρ ≍ 1`.  The trivial (diagonal) mean value bound is not small
enough; the saving comes from the pretentious hypothesis `𝔻(g, n^{iu}; Y) ≥ B` for
`|u| ≤ C·Y/H`, which is fed to Halász's theorem as follows.

* `C` is taken of size `≳ 1/ε`, so that the whole frequency window `|t| ≤ 2T` together with the
  Halász window `T₀ := C·ρ/4` of the twisted function stays inside `|u| ≤ C·Y/H`.
* the twisted Halász theorem `mr_direct.halasz_twisted` bounds the prefix sums
  `Σ_{n ≤ k} g n · n^{-it}` by `C_h · k · ((1+M)e^{-M} + 1/√T₀)`, and
  `mr_direct.window_M_le` replaces `M` (the infimum of the shifted distance) by `M₀ = B²/2`.
* `mr_direct.dist_scale_transfer_wide` transfers the distance hypothesis from the single scale
  `Y` to every scale in `[Y^{1/8}, 16Y]`, which covers the Halász scales `k ≥ ⌈Y⌉₊ - 1` and the
  scale-transfer requirement `M₀ = B²/2` (it loses the factor `2` in the exponent).
* `mr_core.dirPolyD_abel_le` converts those prefix bounds into a bound for
  `dirPolyD g Y t = Σ_{Y ≤ n ≤ 3Y} g n · n^{-(1+it)}` (Abel summation with weight `1/n`).
* the resulting pointwise bound `‖dirPolyD g Y t‖ ≤ κ'` on `|t| ≤ 2T` is integrated, and
  `mr_core.exists_B_C_le` chooses `B, C` with `12 κ'² ≤ ε/8`.
-/

namespace Work.BMF.mr_core

open MeasureTheory intervalIntegral

open scoped BigOperators

theorem smallT_le (ε : ℝ) (hε : 0 < ε) :
    ∃ B C X₀ : ℝ, 0 < B ∧ 0 < C ∧ 1 ≤ X₀ ∧
      ∀ (g : ℕ → ℂ) (Y H T : ℝ), X₀ ≤ Y →
        g 1 = 1 →
        (∀ m n : ℕ, m.Coprime n → g (m * n) = g m * g n) → (∀ n, ‖g n‖ ≤ 1) →
        1 ≤ Y / H → H ≤ Y →
        (∀ u : ℝ, |u| ≤ C * Y / H →
          B ≤ BoundedMultiplicativeFunctions.𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * u)) Y) →
        Y / H ≤ T → T ≤ 3 →
        (Y / H) / T * (∫ t in -(2 * T)..(2 * T), ‖Work.BMF.dirPolyD g Y t‖ ^ 2) ≤ ε / 8 := by
  obtain ⟨Ch, hChpos, hhal⟩ := Work.BMF.mr_direct.halasz_twisted
  obtain ⟨B, C, hB8, hC12, hBC⟩ := exists_B_C_le Ch ε hChpos hε
  refine ⟨B, C, (16:ℝ)^8, by linarith, by linarith, by norm_num, ?_⟩
  intro g Y H T hY hg1 hgmult hgb hρ1 hHY hdist hρT hT3
  set ρ : ℝ := Y / H with hρdef
  have hρ1' : 1 ≤ ρ := hρ1
  have hρ3 : ρ ≤ 3 := le_trans hρT hT3
  have hTpos : 0 < T := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hρ1') hρT
  -- the Halász window of the twisted function
  set T₀ : ℝ := C * ρ / 4 with hT₀def
  have hT₀ge : 3 ≤ T₀ := by rw [hT₀def]; nlinarith
  have hT₀1 : 1 ≤ T₀ := le_trans (by norm_num) hT₀ge
  -- the pretentious parameter, halved: the scale transfer `dist_scale_transfer_wide` costs a factor 2
  set M₀ : ℝ := B ^ 2 / 2 with hM₀def
  have hM₀pos : 0 < M₀ := by rw [hM₀def]; nlinarith
  set κ' : ℝ := 9 * Ch * ((1 + M₀) * Real.exp (-M₀) + 2 / Real.sqrt C) with hκ'def
  have hκ'nn : 0 ≤ κ' := by rw [hκ'def]; positivity
  have hκ'le : κ' ≤ Real.sqrt (ε / 384) := by rw [hκ'def, hM₀def]; exact hBC
  have hCYH : C * Y / H = C * ρ := by rw [hρdef]; ring
  have hdistspec : ∀ u : ℝ, |u| ≤ C * ρ →
      B ≤ BoundedMultiplicativeFunctions.𝔻 g (fun n ↦ (n:ℂ) ^ (Complex.I * u)) Y :=
    fun u hu => hdist u (hCYH ▸ hu)
  have hY169 : (16:ℝ)^8 ≤ Y := hY
  have hρnn : 0 ≤ ρ := le_trans zero_le_one hρ1'
  have h4T₀ : 4 * T₀ = C * ρ := by rw [hT₀def]; ring
  -- ### pointwise bound on the whole frequency range `|t| ≤ 2T`
  have hpoint : ∀ t : ℝ, |t| ≤ 2 * T → ‖Work.BMF.dirPolyD g Y t‖ ≤ κ' := by
    intro t ht
    have htT₀ : |t| ≤ 2 * T₀ := by
      have h1 : |t| ≤ 6 := by linarith [abs_nonneg t]
      have h2 : (6:ℝ) ≤ 2 * T₀ := by rw [hT₀def]; nlinarith
      linarith
    set κ : ℝ := Ch * ((1 + M₀) * Real.exp (-M₀) + 1 / Real.sqrt T₀) with hκdef
    -- prefix bounds from the twisted Halász theorem
    have hpre : ∀ k : ℕ, ⌈Y⌉₊ - 1 ≤ k → k ≤ ⌊3 * Y⌋₊ →
        ‖∑ j ∈ Finset.Icc 1 k, g j * (j : ℂ) ^ (-(Complex.I * t))‖ ≤ κ * (k : ℝ) := by
      intro k hk1 hk2
      have hkR2 : (2:ℝ) ≤ (k:ℝ) := by
        have hc16 : 16 ≤ ⌈Y⌉₊ := by
          have h := Nat.ceil_mono (show (16:ℝ) ≤ Y by linarith)
          simpa using h
        have : 15 ≤ k := by omega
        exact_mod_cast (le_trans (by norm_num : (2:ℕ) ≤ 15) this)
      have hhal' := hhal g hg1 hgmult hgb (k:ℝ) T₀ t hkR2 hT₀1
      dsimp only at hhal'
      rw [Nat.floor_natCast] at hhal'
      -- the distance hypothesis at the scale `k`, via the scale transfer from scale `Y`
      have hDk : ∀ w : ℝ, |w| ≤ 4 * T₀ →
          M₀ ≤ BoundedMultiplicativeFunctions.𝔻 g (fun n ↦ (n:ℂ) ^ (Complex.I * w)) (k:ℝ) ^ 2 := by
        intro w hw
        have hw' : |w| ≤ C * ρ := by rw [← h4T₀]; exact hw
        have hkw : (k:ℝ) ≤ 16 * Y := by
          have h1 : (k:ℝ) ≤ ((⌊3 * Y⌋₊ : ℕ) : ℝ) := by exact_mod_cast hk2
          have h2 : ((⌊3 * Y⌋₊ : ℕ) : ℝ) ≤ 3 * Y := Nat.floor_le (by linarith : (0:ℝ) ≤ 3 * Y)
          linarith [hY169]
        have hklow : Y ^ (1/8:ℝ) ≤ (k:ℝ) := by
          have h1 := rpow_eighth_le_ceil_sub_one Y hY169
          have h2 : ((⌈Y⌉₊ - 1 : ℕ) : ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1
          linarith
        have hres := Work.BMF.mr_direct.dist_scale_transfer_wide g hgb B (C*ρ) Y hB8 hY169
          hdistspec (k:ℝ) hklow hkw w hw'
        calc M₀ = B^2/2 := hM₀def
          _ = (Real.sqrt (B^2/2))^2 := (Real.sq_sqrt (by positivity)).symm
          _ ≤ (BoundedMultiplicativeFunctions.𝔻 g (fun n ↦ (n:ℂ) ^ (Complex.I * w)) (k:ℝ))^2 :=
              pow_le_pow_left₀ (Real.sqrt_nonneg _) hres 2
      have hMle := Work.BMF.mr_direct.window_M_le g M₀ T₀ t (k:ℝ) hM₀pos htT₀ hDk
      have hChk : (0:ℝ) ≤ Ch * (k:ℝ) := by positivity
      calc ‖∑ j ∈ Finset.Icc 1 k, g j * (j : ℂ) ^ (-(Complex.I * t))‖
          ≤ Ch * (k:ℝ) * ((1 + ⨅ (u : {u : ℝ // |u| ≤ 2 * T₀}),
              BoundedMultiplicativeFunctions.𝔻 g
                (fun n ↦ (n : ℂ) ^ (Complex.I * (t + u.1))) (k:ℝ) ^ 2) *
              Real.exp (-(⨅ (u : {u : ℝ // |u| ≤ 2 * T₀}),
              BoundedMultiplicativeFunctions.𝔻 g
                (fun n ↦ (n : ℂ) ^ (Complex.I * (t + u.1))) (k:ℝ) ^ 2)) + 1 / Real.sqrt T₀) := hhal'
        _ ≤ Ch * (k:ℝ) * ((1 + M₀) * Real.exp (-M₀) + 1 / Real.sqrt T₀) := by
            apply mul_le_mul_of_nonneg_left _ hChk
            linarith [hMle]
        _ = κ * (k:ℝ) := by rw [hκdef]; ring
    -- the Abel step
    have hsqrtT₀ : 1 / Real.sqrt T₀ ≤ 2 / Real.sqrt C := by
      have hCρ4 : C / 4 ≤ T₀ := by rw [hT₀def]; nlinarith
      have h1 : Real.sqrt (C/4) ≤ Real.sqrt T₀ := Real.sqrt_le_sqrt hCρ4
      have h2 : Real.sqrt (C/4) = Real.sqrt C / 2 := by
        rw [Real.sqrt_div (by positivity), show Real.sqrt (4:ℝ) = 2 from by
          rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
      rw [h2] at h1
      have h3 := one_div_le_one_div_of_le (by positivity : 0 < Real.sqrt C / 2) h1
      rw [one_div_div] at h3
      exact h3
    calc ‖Work.BMF.dirPolyD g Y t‖ ≤ 9 * κ := dirPolyD_abel_le g Y κ t (by linarith : 16 ≤ Y) hpre
      _ ≤ 9 * (Ch * ((1 + M₀) * Real.exp (-M₀) + 2 / Real.sqrt C)) := by
          have hstep : Ch * ((1 + M₀) * Real.exp (-M₀) + 1 / Real.sqrt T₀) ≤
              Ch * ((1 + M₀) * Real.exp (-M₀) + 2 / Real.sqrt C) :=
            mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hChpos)
          have hstep2 := mul_le_mul_of_nonneg_left hstep (by norm_num : (0:ℝ) ≤ 9)
          linarith [hstep2]
      _ = κ' := by rw [hκ'def]; ring
  -- ### integration
  have hI : ∫ t in -(2*T)..(2*T), ‖Work.BMF.dirPolyD g Y t‖ ^ 2 ≤ 4 * T * κ'^2 := by
    have hnn : 0 ≤ ∫ t in -(2*T)..(2*T), ‖Work.BMF.dirPolyD g Y t‖^2 :=
      intervalIntegral.integral_nonneg (by linarith [hTpos]) (fun u _ => by positivity)
    have habs : ‖∫ t in -(2*T)..(2*T), ‖Work.BMF.dirPolyD g Y t‖^2‖ ≤
        κ'^2 * |2*T - (-(2*T))| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => ?_)
      have hle : -(2*T) ≤ 2*T := by linarith [hTpos]
      rw [Set.uIoc_of_le hle, Set.mem_Ioc] at hx
      have habs' : |x| ≤ 2*T := abs_le.mpr ⟨le_of_lt hx.1, hx.2⟩
      have hbound := hpoint x habs'
      rw [Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ ‖Work.BMF.dirPolyD g Y x‖^2)]
      exact pow_le_pow_left₀ (norm_nonneg _) hbound 2
    rw [Real.norm_of_nonneg hnn] at habs
    have h4T : |2*T - (-(2*T))| = 4*T := by
      rw [abs_of_nonneg (by linarith [hTpos])]; ring
    rw [h4T] at habs
    linarith [habs]
  have h12 : 12 * κ'^2 ≤ ε / 8 := by
    have hsq : κ'^2 ≤ ε/384 := by
      calc κ'^2 ≤ (Real.sqrt (ε/384))^2 := pow_le_pow_left₀ hκ'nn hκ'le 2
        _ = ε/384 := Real.sq_sqrt (by positivity)
    linarith
  calc (Y / H) / T * (∫ t in -(2*T)..(2*T), ‖Work.BMF.dirPolyD g Y t‖^2)
      = (ρ / T) * (∫ t in -(2*T)..(2*T), ‖Work.BMF.dirPolyD g Y t‖^2) := by rw [hρdef]
    _ ≤ (ρ / T) * (4*T*κ'^2) := by
        apply mul_le_mul_of_nonneg_left hI
        exact div_nonneg hρnn (le_of_lt hTpos)
    _ = 4 * ρ * κ'^2 := by field_simp
    _ ≤ 12 * κ'^2 := by nlinarith [hρ3, hκ'nn]
    _ ≤ ε / 8 := h12

end Work.BMF.mr_core
