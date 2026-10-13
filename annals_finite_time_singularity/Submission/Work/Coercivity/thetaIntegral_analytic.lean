import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.ConvergenceOnBall
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Coercivity.uniform_geometric_bound_of_local
import Submission.Work.Coercivity.hasSum_setIntegral_tsum

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped NNReal ENNReal Topology Real
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option linter.unusedSimpArgs false
set_option autoImplicit false

set_option quotPrecheck false

/-- The angular interval `[0, π/2]`. -/
local notation "Iθ" => Set.Icc (0:ℝ) (Real.pi / 2)

local notation "U" => Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (-1) (Real.pi / 2 + 1) : Set ℝ)

/-- Cauchy-type bound for the coefficients of the origin-changed series. -/
theorem changeOriginCoeff_le {q : FormalMultilinearSeries ℝ (ℝ × ℝ) ℝ} {M s ρ : ℝ≥0}
    (hM : 0 < M) (hs : 0 < s) (hρ : 0 < ρ) (h8 : 8 * ρ ≤ s)
    (hbd : ∀ n, ‖q n‖₊ ≤ M / s ^ n) {a : ℝ × ℝ} (ha : ‖a‖₊ ≤ ρ) (k : ℕ) :
    ‖q.changeOrigin a k‖₊ ≤ 4 * M / ρ ^ k := by
  have hsnn : (s : ℝ≥0) ≠ 0 := ne_of_gt hs
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hρR : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ
  have h4ρ : 4 * ρ ≤ s :=
    le_trans (mul_le_mul_of_nonneg_right (by norm_num : (4:ℝ≥0) ≤ 8) (le_of_lt hρ)) h8
  have h4ρR : 4 * (ρ : ℝ) ≤ (s : ℝ) := by exact_mod_cast h4ρ
  -- radius bound
  have hsq : (s : ℝ≥0∞) ≤ q.radius := by
    refine FormalMultilinearSeries.le_radius_of_bound q (M : ℝ) (fun n => ?_)
    have h1 : (‖q n‖₊ : ℝ) ≤ (M : ℝ) / (s : ℝ) ^ n := by
      have h2 := NNReal.coe_le_coe.mpr (hbd n)
      simpa [NNReal.coe_div, NNReal.coe_pow] using h2
    calc ‖q n‖ * (s : ℝ) ^ n = (‖q n‖₊ : ℝ) * (s : ℝ) ^ n := by rw [coe_nnnorm]
      _ ≤ ((M : ℝ) / (s : ℝ) ^ n) * (s : ℝ) ^ n := by gcongr
      _ = (M : ℝ) := by
        rw [div_mul_cancel₀]
        positivity
  have hast : ‖a‖₊ < s := by
    have hlt : ρ < 8 * ρ := by
      calc ρ = 1 * ρ := (one_mul ρ).symm
        _ < 8 * ρ := mul_lt_mul_of_pos_right (by norm_num) hρ
    exact lt_of_le_of_lt ha (lt_of_lt_of_le hlt h8)
  have harad : (‖a‖₊ : ℝ≥0∞) < q.radius :=
    lt_of_lt_of_le (ENNReal.coe_lt_coe.mpr hast) hsq
  set c : ℕ → ℝ≥0 := fun l => ‖q (k + l)‖₊ * ‖a‖₊ ^ l with hc_def
  have hsumm : Summable fun z : (l : ℕ) × {s : Finset (Fin (k + l)) // s.card = l} => c z.1 :=
    q.changeOriginSeries_summable_aux₂ (r := ‖a‖₊) harad k
  have hkey : ‖q.changeOrigin a k‖₊ ≤
      ∑' z : (l : ℕ) × {s : Finset (Fin (k + l)) // s.card = l}, c z.1 :=
    q.nnnorm_changeOrigin_le k harad
  -- real-number auxiliary inequality
  have hreal : ∀ l : ℕ, (2:ℝ) ^ (k + l) * ((M:ℝ) / (s:ℝ) ^ (k + l) * (ρ:ℝ) ^ l)
      ≤ ((2:ℝ) ^ k * (M:ℝ) / (s:ℝ) ^ k) * ((1:ℝ)/2) ^ l := by
    intro l
    have hsplit : (2:ℝ) ^ (k + l) * ((M:ℝ) / s ^ (k + l) * ρ ^ l)
        = ((2:ℝ) ^ k * M / s ^ k) * ((2:ℝ) ^ l * ρ ^ l / s ^ l) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, pow_add, pow_add, mul_inv_rev]
      ring
    rw [hsplit]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [show ((1:ℝ)/2) ^ l = 1 / 2 ^ l by rw [div_pow]; norm_num]
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    calc (2:ℝ) ^ l * ρ ^ l * 2 ^ l = ((2:ℝ) * ρ * 2) ^ l := by rw [← mul_pow, ← mul_pow]
      _ = ((4:ℝ) * ρ) ^ l := by rw [show (2:ℝ) * ρ * 2 = 4 * ρ by ring]
      _ ≤ s ^ l := pow_le_pow_left₀ (by positivity) h4ρR l
  -- NNReal termwise inequality
  have haux : ∀ l : ℕ, (2:ℝ≥0) ^ (k + l) * c l
      ≤ ((2:ℝ≥0) ^ k * M / s ^ k) * (1/2) ^ l := by
    intro l
    have hcl : c l ≤ M / s ^ (k + l) * ρ ^ l := by
      rw [hc_def]
      have h1 : ‖q (k+l)‖₊ ≤ M / s ^ (k + l) := hbd (k + l)
      have h2 : ‖a‖₊ ^ l ≤ ρ ^ l := by gcongr
      calc ‖q (k + l)‖₊ * ‖a‖₊ ^ l ≤ (M / s ^ (k + l)) * ρ ^ l := by gcongr
        _ = M / s ^ (k + l) * ρ ^ l := rfl
    refine le_trans (mul_le_mul_of_nonneg_left hcl (by positivity)) ?_
    rw [← NNReal.coe_le_coe]
    push_cast
    exact hreal l
  -- final NNReal inequality
  have hnn : ((2:ℝ≥0) ^ k * M / s ^ k) * 2 ≤ 4 * M / ρ ^ k := by
    rw [← NNReal.coe_le_coe]
    push_cast
    have hp2R : 2 * (ρ : ℝ) ≤ (s : ℝ) := by
      have hp2 : 2 * ρ ≤ s :=
        le_trans (mul_le_mul_of_nonneg_right (by norm_num : (2:ℝ≥0) ≤ 8) (le_of_lt hρ)) h8
      exact_mod_cast hp2
    have hkey2 : (2:ℝ) ^ k * (ρ:ℝ) ^ k ≤ (s:ℝ) ^ k := by
      calc (2:ℝ) ^ k * ρ ^ k = (2 * ρ) ^ k := by rw [mul_pow]
        _ ≤ s ^ k := pow_le_pow_left₀ (by positivity) hp2R k
    rw [show ((2:ℝ) ^ k * M / s ^ k) * 2 = (2:ℝ) ^ (k+1) * M / s ^ k by rw [pow_succ]; ring,
        div_le_div_iff₀ (by positivity) (by positivity)]
    calc (2:ℝ) ^ (k + 1) * M * ρ ^ k = 2 * M * ((2:ℝ) ^ k * ρ ^ k) := by rw [pow_succ]; ring
      _ ≤ 2 * M * s ^ k := by gcongr
      _ ≤ 4 * M * s ^ k := by gcongr; norm_num
  -- the ENNReal chain
  have hchain : (∑' z : (l : ℕ) × {s : Finset (Fin (k + l)) // s.card = l},
      (↑(c z.1) : ℝ≥0∞)) ≤ (4 * M / ρ ^ k : ℝ≥0) := by
    have hstep1 : (∑' z : (l : ℕ) × {s : Finset (Fin (k + l)) // s.card = l},
        (↑(c z.1) : ℝ≥0∞))
        = ∑' l : ℕ, (Fintype.card {s : Finset (Fin (k + l)) // s.card = l} : ℝ≥0∞) *
            (↑(c l) : ℝ≥0∞) := by
      rw [ENNReal.tsum_sigma']
      apply tsum_congr; intro l
      rw [tsum_fintype]
      have hcc : ∀ b : {s : Finset (Fin (k + l)) // s.card = l},
          (↑(c (⟨l, b⟩ : (m : ℕ) × {s : Finset (Fin (k + m)) // s.card = m}).1) : ℝ≥0∞)
            = (↑(c l) : ℝ≥0∞) := fun b => rfl
      rw [Finset.sum_congr rfl (fun b _ => hcc b), Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    rw [hstep1]
    have hcard : ∀ l : ℕ,
        Fintype.card {s : Finset (Fin (k + l)) // s.card = l} ≤ 2 ^ (k + l) := by
      intro l
      calc Fintype.card {s : Finset (Fin (k + l)) // s.card = l}
          ≤ Fintype.card (Finset (Fin (k + l))) := Fintype.card_subtype_le _
        _ = 2 ^ (k + l) := by rw [Fintype.card_finset, Fintype.card_fin]
    calc ∑' l : ℕ, (Fintype.card {s : Finset (Fin (k + l)) // s.card = l} : ℝ≥0∞) *
            (↑(c l) : ℝ≥0∞)
        ≤ ∑' l : ℕ, (2 : ℝ≥0∞) ^ (k + l) * (↑(c l) : ℝ≥0∞) := by
          apply ENNReal.tsum_le_tsum; intro l
          gcongr
          exact_mod_cast hcard l
      _ ≤ ∑' l : ℕ, ((2 : ℝ≥0∞) ^ k * (M : ℝ≥0∞) / (s : ℝ≥0∞) ^ k) *
            ((1/2 : ℝ≥0∞) ^ l) := by
          apply ENNReal.tsum_le_tsum; intro l
          have e1 : (2 : ℝ≥0∞) ^ (k + l) * (↑(c l) : ℝ≥0∞)
              = ↑((2:ℝ≥0) ^ (k + l) * c l) := by
            simp only [hc_def]
            push_cast
            ring
          have e2 : ((2 : ℝ≥0∞) ^ k * (M : ℝ≥0∞) / (s : ℝ≥0∞) ^ k) * ((1/2 : ℝ≥0∞) ^ l)
              = ↑(((2:ℝ≥0) ^ k * M / s ^ k) * (1/2) ^ l) := by
            rw [ENNReal.coe_mul, ENNReal.coe_div (pow_ne_zero _ hsnn), ENNReal.coe_pow,
              ENNReal.coe_pow]
            norm_num
          rw [e1, e2]
          exact ENNReal.coe_le_coe.mpr (haux l)
      _ = ((2 : ℝ≥0∞) ^ k * (M : ℝ≥0∞) / (s : ℝ≥0∞) ^ k) *
            ∑' l : ℕ, ((1/2 : ℝ≥0∞) ^ l) := ENNReal.tsum_mul_left
      _ = ((2 : ℝ≥0∞) ^ k * (M : ℝ≥0∞) / (s : ℝ≥0∞) ^ k) * 2 := by
          rw [ENNReal.tsum_geometric]
          norm_num
      _ ≤ (4 * M / ρ ^ k : ℝ≥0) := by
          have e3 : ((2 : ℝ≥0∞) ^ k * (M : ℝ≥0∞) / (s : ℝ≥0∞) ^ k) * 2
              = ↑(((2:ℝ≥0) ^ k * M / s ^ k) * 2) := by
            rw [ENNReal.coe_mul, ENNReal.coe_div (pow_ne_zero _ hsnn), ENNReal.coe_pow]
            norm_num
          rw [e3]
          exact ENNReal.coe_le_coe.mpr hnn
  have hgoal : (‖q.changeOrigin a k‖₊ : ℝ≥0∞) ≤ (4 * M / ρ ^ k : ℝ≥0) := by
    calc (↑(‖q.changeOrigin a k‖₊) : ℝ≥0∞)
        ≤ ↑(∑' z : (l : ℕ) × {s : Finset (Fin (k + l)) // s.card = l}, c z.1) := by
          exact_mod_cast hkey
      _ = ∑' z : (l : ℕ) × {s : Finset (Fin (k + l)) // s.card = l},
              (↑(c z.1) : ℝ≥0∞) := ENNReal.coe_tsum hsumm
      _ ≤ _ := hchain
  exact ENNReal.coe_le_coe.mp hgoal



/-- The `k`-th derivative of a slice in the `z`-direction is the `k`-th iterated Fréchet derivative
of the two-variable function along the direction `(1,0)`. -/
theorem iteratedDeriv_slice_eq {F : ℝ → ℝ → ℝ} {z₀ θ : ℝ} {k : ℕ}
    (hF : AnalyticAt ℝ (Function.uncurry F) (z₀, θ)) :
    iteratedDeriv k (fun z => F z θ) z₀
      = iteratedFDeriv ℝ k (Function.uncurry F) (z₀, θ) (fun _ => ((1 : ℝ), (0 : ℝ))) := by
  obtain ⟨u, hu, huan⟩ := hF.exists_mem_nhds_analyticOnNhd
  obtain ⟨u', hu'u, hu'open, hu'mem⟩ := mem_nhds_iff.mp hu
  have huo : AnalyticOn ℝ (Function.uncurry F) u' := (huan.mono hu'u).analyticOn
  have hcont : ContDiffOn ℝ ⊤ (Function.uncurry F) u' := huo.contDiffOn hu'open.uniqueDiffOn
  set c : ℝ × ℝ := ((0 : ℝ), θ) with hc_def
  set L : ℝ →L[ℝ] ℝ × ℝ := ContinuousLinearMap.inl ℝ ℝ ℝ with hL_def
  set g : ℝ × ℝ → ℝ := fun y => Function.uncurry F (y + c) with hg_def
  set v : Set (ℝ × ℝ) := (fun y : ℝ × ℝ => y + c) ⁻¹' u' with hv_def
  have hvopen : IsOpen v := by
    rw [hv_def]
    exact (Homeomorph.addRight c).isOpen_preimage.mpr hu'open
  have hgcont : ContDiffOn ℝ ⊤ g v := by
    rw [hg_def]
    refine ContDiffOn.comp hcont ?_ ?_
    · exact contDiffOn_id.add contDiffOn_const
    · intro y hy; exact hy
  have hzv : L z₀ ∈ v := by
    rw [hv_def, Set.mem_preimage, hL_def, ContinuousLinearMap.inl_apply, hc_def,
      Prod.mk_add_mk, zero_add, add_zero]
    exact hu'mem
  have hz0v : z₀ ∈ L ⁻¹' v := by rw [Set.mem_preimage]; exact hzv
  have hLvopen : IsOpen (L ⁻¹' v) := hvopen.preimage L.continuous
  have hmain := ContinuousLinearMap.iteratedFDerivWithin_comp_right L hgcont
      hvopen.uniqueDiffOn hLvopen.uniqueDiffOn hzv (le_top : ((k : ℕ∞) : WithTop ℕ∞) ≤ ⊤)
  have e1 : iteratedFDerivWithin ℝ k (g ∘ L) (L ⁻¹' v) z₀ = iteratedFDeriv ℝ k (g ∘ L) z₀ :=
    iteratedFDerivWithin_of_isOpen k hLvopen hz0v
  have e2 : iteratedFDerivWithin ℝ k g v (L z₀) = iteratedFDeriv ℝ k g (L z₀) :=
    iteratedFDerivWithin_of_isOpen k hvopen hzv
  have e3 : iteratedFDeriv ℝ k g (L z₀)
      = iteratedFDeriv ℝ k (Function.uncurry F) (L z₀ + c) :=
    iteratedFDeriv_comp_add_right k c (L z₀)
  have hz : L z₀ + c = (z₀, θ) := by
    rw [hL_def, ContinuousLinearMap.inl_apply, hc_def, Prod.mk_add_mk, zero_add, add_zero]
  have hL1 : (fun _ : Fin k => L (1 : ℝ)) = (fun _ => ((1 : ℝ), (0 : ℝ))) := by
    funext i; rw [hL_def, ContinuousLinearMap.inl_apply]
  have hslice : (fun z : ℝ => F z θ) = g ∘ L := by
    funext z
    simp only [Function.comp_apply, hg_def, hL_def, hc_def, ContinuousLinearMap.inl_apply,
      Prod.mk_add_mk, zero_add, add_zero, Function.uncurry_apply_pair]
  rw [iteratedDeriv_eq_iteratedFDeriv]
  rw [hslice, ← e1, hmain, ContinuousMultilinearMap.compContinuousLinearMap_apply, e2, e3, hz, hL1]



/-- Local Cauchy-type bound for the `z`-derivatives of the slices of a two-variable analytic
function, uniform in `θ` near `θ₀`. -/
theorem slice_bound_local {F : ℝ → ℝ → ℝ} {z₀ θ₀ : ℝ}
    (hF : AnalyticAt ℝ (Function.uncurry F) (z₀, θ₀)) :
    ∃ ε > 0, ∃ C > 0, ∃ σ > 0, ∀ k : ℕ, ∀ θ : ℝ, |θ - θ₀| < ε →
      ‖iteratedFDeriv ℝ k (Function.uncurry F) (z₀, θ) (fun _ => ((1 : ℝ), (0 : ℝ)))‖
        ≤ C * (k.factorial : ℝ) / σ ^ k := by
  obtain ⟨q, r, hq⟩ := hF
  obtain ⟨s, hs0', hsr⟩ := (ENNReal.lt_iff_exists_nnreal_btwn (a := (0 : ℝ≥0∞)) (b := r)).mp hq.r_pos
  have hs0 : 0 < s := ENNReal.coe_pos.mp hs0'
  obtain ⟨M, hMpos, hMac⟩ := q.norm_le_div_pow_of_pos_of_lt_radius hs0
    (lt_of_lt_of_le hsr hq.r_le)
  set M' : ℝ≥0 := ⟨M, le_of_lt hMpos⟩ with hM'_def
  have hbd : ∀ n, ‖q n‖₊ ≤ M' / s ^ n := by
    intro n
    rw [← NNReal.coe_le_coe]
    have h := hMac n
    simp only [hM'_def, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_mk, coe_nnnorm]
    exact h
  set σ : ℝ≥0 := s / 16 with hσ_def
  have hσpos : 0 < σ := by
    rw [hσ_def]; positivity
  have h8σ : 8 * σ ≤ s := by
    rw [hσ_def]
    rw [← NNReal.coe_le_coe]
    push_cast
    nlinarith [hs0]
  have hσs : σ < s := by
    have : σ ≤ s / 2 := by rw [hσ_def, ← NNReal.coe_le_coe]; push_cast; nlinarith [hs0]
    have : (0:ℝ≥0) < s / 2 := by positivity
    linarith
  have hM'pos : 0 < M' := by
    rw [hM'_def]; exact_mod_cast hMpos
  refine ⟨σ, hσpos, (4 : ℝ≥0) * M', by positivity, σ, hσpos, fun k θ hθ => ?_⟩
  set a : ℝ × ℝ := ((0 : ℝ), θ - θ₀) with ha_def
  have ha : ‖a‖₊ ≤ σ := by
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    rw [ha_def, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _), Real.norm_eq_abs]
    exact hθ.le
  have hcoef : ‖q.changeOrigin a k‖₊ ≤ 4 * M' / σ ^ k :=
    changeOriginCoeff_le (by positivity) hs0 hσpos h8σ hbd ha k
  have harad : (‖a‖₊ : ℝ≥0∞) < r := by
    have h1 : (‖a‖₊ : ℝ≥0∞) ≤ (σ : ℝ≥0∞) := by exact_mod_cast ha
    have h2 : (σ : ℝ≥0∞) < (s : ℝ≥0∞) := ENNReal.coe_lt_coe.mpr hσs
    exact lt_of_le_of_lt h1 (lt_trans h2 hsr)
  have hca : HasFPowerSeriesOnBall (Function.uncurry F) (q.changeOrigin a)
      ((z₀, θ₀) + a) (r - ↑‖a‖₊) := hq.changeOrigin harad
  have hfs := hca.factorial_smul ((1 : ℝ), (0 : ℝ)) k
  have hza : (z₀, θ₀) + a = (z₀, θ) := by
    rw [ha_def, Prod.mk_add_mk, add_zero, add_sub_cancel]
  rw [hza] at hfs
  rw [← hfs, nsmul_eq_mul, norm_mul]
  have hkfac : ‖(k.factorial : ℝ)‖ = (k.factorial : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  rw [hkfac]
  have hop : ‖(q.changeOrigin a k) (fun _ => ((1 : ℝ), (0 : ℝ)))‖ ≤ ‖q.changeOrigin a k‖ := by
    have h := (q.changeOrigin a k).le_opNorm (fun _ : Fin k => ((1 : ℝ), (0 : ℝ)))
    have h1 : (∏ i : Fin k, ‖((1 : ℝ), (0 : ℝ))‖) = 1 := by
      simp [Prod.norm_def]
    rwa [h1, mul_one] at h
  have hcoefR : ((4 : ℝ≥0) * M' / σ ^ k : ℝ≥0) = (4 * (M' : ℝ) / (σ : ℝ) ^ k) := by
    push_cast; ring
  calc (k.factorial : ℝ) * ‖(q.changeOrigin a k) (fun _ => ((1 : ℝ), (0 : ℝ)))‖
      ≤ (k.factorial : ℝ) * ‖q.changeOrigin a k‖ :=
        mul_le_mul_of_nonneg_left hop (Nat.cast_nonneg _)
    _ = (k.factorial : ℝ) * (‖q.changeOrigin a k‖₊ : ℝ) := by rw [coe_nnnorm]
    _ ≤ (k.factorial : ℝ) * ((4 : ℝ≥0) * M' / σ ^ k : ℝ≥0) := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        exact_mod_cast hcoef
    _ = ((4 : ℝ≥0) * M' : ℝ) * (k.factorial : ℝ) / (σ : ℝ) ^ k := by
        push_cast; ring



/-- Note: `ContDiffOn ℝ ⊤` is the real-analytic order `ω`, not `C^∞`. -/
theorem thetaIntegral_analytic (F : ℝ → ℝ → ℝ)
    (hF : ContDiffOn ℝ ⊤ (Function.uncurry F) (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1))) :
    AnalyticOn ℝ (fun z => ∫ θ in Set.Icc 0 (Real.pi / 2), F z θ) (Set.Ioi 0) := by
  intro z₀ hz₀
  have hz₀' : 0 < z₀ := hz₀
  have hFa : AnalyticOn ℝ (Function.uncurry F) U := hF.analyticOn
  have hUopen : IsOpen (U : Set (ℝ × ℝ)) := isOpen_Ioi.prod isOpen_Ioo
  have hmemU : ∀ θ ∈ (Iθ : Set ℝ), (z₀, θ) ∈ (U : Set (ℝ × ℝ)) := by
    rintro θ ⟨h0, hpi⟩
    exact ⟨hz₀, by linarith, by linarith [Real.pi_pos]⟩
  have hAn : ∀ θ ∈ (Iθ : Set ℝ), AnalyticAt ℝ (Function.uncurry F) (z₀, θ) :=
    fun θ hθ => hFa.analyticAt (hUopen.mem_nhds (hmemU θ hθ))
  -- the coefficient family
  set A : ℕ → ℝ → ℝ := fun k θ => iteratedFDeriv ℝ k (Function.uncurry F) (z₀, θ)
      (fun _ => ((1 : ℝ), (0 : ℝ))) / (k.factorial : ℝ) with hA_def
  have hAeq : ∀ k θ, A k θ = iteratedFDeriv ℝ k (Function.uncurry F) (z₀, θ)
      (fun _ => ((1 : ℝ), (0 : ℝ))) / (k.factorial : ℝ) := fun k θ => rfl
  -- local geometric bounds
  have hloc : ∀ θ ∈ (Iθ : Set ℝ), ∃ ε > 0, ∃ C > 0, ∃ s > 0,
      ∀ k, ∀ θ' ∈ Set.Ioo (θ - ε) (θ + ε), |A k θ'| ≤ C / s ^ k := by
    intro θ hθ
    obtain ⟨ε, hε, C, hC, σ, hσ, hb⟩ := slice_bound_local (hAn θ hθ)
    refine ⟨ε, hε, C, hC, σ, hσ, fun k θ' hθ' => ?_⟩
    have habs : |θ' - θ| < ε := by
      rw [abs_lt]; exact ⟨by linarith [hθ'.1], by linarith [hθ'.2]⟩
    have h1 : ‖iteratedFDeriv ℝ k (Function.uncurry F) (z₀, θ')
        (fun _ => ((1 : ℝ), (0 : ℝ)))‖ ≤ C * (k.factorial : ℝ) / σ ^ k := hb k θ' habs
    rw [Real.norm_eq_abs] at h1
    rw [hAeq, abs_div, abs_of_pos (by positivity : (0:ℝ) < (k.factorial : ℝ))]
    rw [div_le_div_iff₀ (by positivity) (pow_pos hσ k)]
    calc |iteratedFDeriv ℝ k (Function.uncurry F) (z₀, θ') (fun _ => ((1 : ℝ), (0 : ℝ)))|
          * σ ^ k
        ≤ (C * (k.factorial : ℝ) / σ ^ k) * σ ^ k := by gcongr
      _ = C * (k.factorial : ℝ) := by
          rw [div_mul_cancel₀]
          positivity
  obtain ⟨C₀, hC₀, σ, hσ, hbnd⟩ := uniform_geometric_bound_of_local isCompact_Icc hloc
  -- continuity of the coefficient functions
  have hcontA : ∀ k, ContinuousOn (A k) (Iθ : Set ℝ) := by
    intro k
    have hc : ContinuousOn (iteratedFDeriv ℝ k (Function.uncurry F)) (U : Set (ℝ × ℝ)) :=
      ContinuousOn.continuousOn_iteratedFDeriv hF hUopen le_top
    have h2 : ContinuousOn (fun θ : ℝ => iteratedFDeriv ℝ k (Function.uncurry F) (z₀, θ))
        (Iθ : Set ℝ) :=
      ContinuousOn.comp hc (continuous_const.prodMk continuous_id).continuousOn
        (fun θ hθ => hmemU θ hθ)
    have hev : Continuous (fun q : ContinuousMultilinearMap ℝ (fun _ : Fin k => ℝ × ℝ) ℝ =>
        q (fun _ => ((1 : ℝ), (0 : ℝ)))) :=
      continuous_eval.comp (continuous_id.prodMk continuous_const)
    have h3 : ContinuousOn (fun θ : ℝ => (iteratedFDeriv ℝ k (Function.uncurry F) (z₀, θ))
        (fun _ => ((1 : ℝ), (0 : ℝ))) / (k.factorial : ℝ)) (Iθ : Set ℝ) :=
      (hev.comp_continuousOn h2).div_const _
    exact h3.congr (fun θ _ => (hAeq k θ).symm)
  -- the radius
  set ρ : ℝ≥0 := ⟨min (σ / 2) (z₀ / 2),
    le_of_lt (lt_min (by linarith) (by linarith))⟩ with hρ_def
  have hρpos : 0 < ρ := by
    rw [hρ_def]
    exact_mod_cast (lt_min (by linarith : (0:ℝ) < σ / 2) (by linarith : (0:ℝ) < z₀ / 2))
  have hρσ : (ρ : ℝ) < σ := by
    have h1 : (ρ : ℝ) ≤ σ / 2 := by rw [hρ_def]; exact min_le_left _ _
    linarith
  have hρz : (ρ : ℝ) ≤ z₀ / 2 := by
    rw [hρ_def]; exact min_le_right _ _
  -- each slice is analytic on the closed ball
  have hslice_an : ∀ θ ∈ (Iθ : Set ℝ),
      AnalyticOn ℝ (fun z => F z θ) (Metric.eball z₀ (ρ : ℝ≥0∞)) := by
    intro θ hθ
    have h1 : AnalyticOn ℝ (fun z : ℝ => F z θ) (Set.Ioi (0 : ℝ)) := by
      have hcomp : AnalyticOn ℝ (fun z : ℝ => (Function.uncurry F) (z, θ)) (Set.Ioi (0 : ℝ)) :=
        hFa.comp (analyticOn_id.prod analyticOn_const)
          (fun z hz => ⟨hz, by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩)
      simpa [Function.uncurry] using hcomp
    refine h1.mono ?_
    intro z hz
    have h2 : edist z z₀ < (ρ : ℝ≥0∞) := Metric.mem_eball.mp hz
    rw [edist_dist, Real.dist_eq] at h2
    rw [← ENNReal.ofReal_coe_nnreal] at h2
    have h3 : |z - z₀| < (ρ : ℝ) :=
      (ENNReal.ofReal_lt_ofReal_iff (by positivity : (0:ℝ) < (ρ:ℝ))).mp h2
    show (0:ℝ) < z
    linarith [(abs_lt.mp h3).1, hρz, hz₀']
  -- the power series of each slice
  have hslice_ps : ∀ θ ∈ (Iθ : Set ℝ), HasFPowerSeriesOnBall (fun z => F z θ)
      (FormalMultilinearSeries.ofScalars ℝ (fun k => A k θ)) z₀ (ρ : ℝ≥0∞) := by
    intro θ hθ
    have hcoeff : (fun k => iteratedDeriv k (fun z => F z θ) z₀ / (k.factorial : ℝ))
        = fun k => A k θ := by
      funext k
      rw [iteratedDeriv_slice_eq (hAn θ hθ), hAeq]
    have hcn : ∀ n, |iteratedDeriv n (fun z => F z θ) z₀ / (n.factorial : ℝ)| = |A n θ| := by
      intro n
      rw [iteratedDeriv_slice_eq (hAn θ hθ), hAeq n θ]
    have hle : (ρ : ℝ≥0∞) ≤ (FormalMultilinearSeries.ofScalars ℝ
        (fun k => iteratedDeriv k (fun z => F z θ) z₀ / (k.factorial : ℝ))).radius := by
      refine FormalMultilinearSeries.le_radius_of_bound _ C₀ (fun n => ?_)
      rw [FormalMultilinearSeries.ofScalars_norm, Real.norm_eq_abs, hcn]
      calc |A n θ| * (ρ : ℝ) ^ n ≤ (C₀ / σ ^ n) * (ρ : ℝ) ^ n := by
            gcongr
            exact hbnd n θ hθ
        _ ≤ C₀ := by
            rw [div_mul_eq_mul_div, div_le_iff₀ (pow_pos hσ n)]
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hρσ.le n) hC₀.le
    have hps := AnalyticOn.hasFPowerSeriesOnSubball (x := z₀) (r := (ρ : ℝ≥0∞))
      (ENNReal.coe_pos.mpr hρpos) (hslice_an θ hθ) hle
    rw [hcoeff] at hps
    exact hps
  -- the integral of the Fubini step
  let c : ℕ → ℝ := fun k => ∫ θ in (Iθ : Set ℝ), A k θ
  have hmain : HasFPowerSeriesOnBall (fun z => ∫ θ in (Iθ : Set ℝ), F z θ)
      (FormalMultilinearSeries.ofScalars ℝ c) z₀ (ρ : ℝ≥0∞) := by
    refine ⟨?_, ENNReal.coe_pos.mpr hρpos, ?_⟩
    · -- radius: the coefficients are bounded by `(π/2) C₀ / σ^n`
      refine FormalMultilinearSeries.le_radius_of_bound _ (Real.pi / 2 * C₀) (fun n => ?_)
      rw [FormalMultilinearSeries.ofScalars_norm, Real.norm_eq_abs]
      have hb : |c n| ≤ Real.pi / 2 * C₀ / σ ^ n := by
        have h1 : |c n| ≤ ∫ θ in (Iθ : Set ℝ), |A n θ| := by
          have := norm_integral_le_integral_norm (f := fun θ => A n θ)
            (μ := volume.restrict (Iθ : Set ℝ))
          simpa [c, Real.norm_eq_abs] using this
        have h2 : ∫ θ in (Iθ : Set ℝ), |A n θ| ≤ ∫ θ in (Iθ : Set ℝ), (C₀ / σ ^ n) := by
          refine integral_mono_ae ((hcontA n).abs.integrableOn_Icc)
            (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)) ?_
          filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
          exact hbnd n θ hθ
        have h3 : ∫ θ in (Iθ : Set ℝ), (C₀ / σ ^ n) = Real.pi / 2 * (C₀ / σ ^ n) := by
          rw [setIntegral_const, smul_eq_mul]
          show (volume (Iθ : Set ℝ)).toReal * (C₀ / σ ^ n) = Real.pi / 2 * (C₀ / σ ^ n)
          rw [Real.volume_Icc, ENNReal.toReal_ofReal (by have h := Real.pi_pos; linarith)]
          ring
        rw [h3] at h2
        calc |c n| ≤ ∫ θ in (Iθ : Set ℝ), |A n θ| := h1
          _ ≤ Real.pi / 2 * (C₀ / σ ^ n) := h2
          _ = Real.pi / 2 * C₀ / σ ^ n := by ring
      calc |c n| * (ρ : ℝ) ^ n ≤ (Real.pi / 2 * C₀ / σ ^ n) * (ρ : ℝ) ^ n := by gcongr
        _ ≤ Real.pi / 2 * C₀ := by
            rw [div_mul_eq_mul_div, div_le_iff₀ (pow_pos hσ n)]
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hρσ.le n)
              (by positivity)
    · -- the power series expansion
      intro y hy
      have hy' : |y| < (ρ : ℝ) := by
        have h2 : edist y 0 < (ρ : ℝ≥0∞) := Metric.mem_eball.mp hy
        rw [edist_dist, Real.dist_eq, sub_zero] at h2
        rw [← ENNReal.ofReal_coe_nnreal] at h2
        exact (ENNReal.ofReal_lt_ofReal_iff (by positivity : (0:ℝ) < (ρ:ℝ))).mp h2
      have hyσ : |y| < σ := lt_of_lt_of_le hy' hρσ.le
      have hD := hasSum_setIntegral_tsum hC₀ hσ measurableSet_Icc
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) hcontA
        (fun k θ hθ => hbnd k θ hθ) hyσ
      have hyρ : y ∈ Metric.eball (0:ℝ) (ρ : ℝ≥0∞) := by
        rw [Metric.mem_eball, edist_dist, Real.dist_eq, sub_zero]
        rw [← ENNReal.ofReal_coe_nnreal]
        exact (ENNReal.ofReal_lt_ofReal_iff (by positivity : (0:ℝ) < (ρ:ℝ))).mpr hy'
      have hcongr : (∫ θ in (Iθ : Set ℝ), ∑' k, A k θ * y ^ k)
          = ∫ θ in (Iθ : Set ℝ), F (z₀ + y) θ := by
        have hh : ∀ θ : ℝ, (∑' b : ℕ,
            (FormalMultilinearSeries.ofScalars ℝ (fun k => A k θ) b) (fun _ => y))
            = ∑' k, A k θ * y ^ k := by
          intro θ
          refine tsum_congr (fun n => ?_)
          rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
        simp only [← hh]
        refine integral_congr_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
        exact ((hslice_ps θ hθ).hasSum hyρ).tsum_eq
      rw [hcongr] at hD
      have hL : (fun n : ℕ => (FormalMultilinearSeries.ofScalars ℝ c) n (fun _ => y))
          = fun k : ℕ => (∫ θ in (Iθ : Set ℝ), A k θ) * y ^ k := by
        funext n
        rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
      rw [hL]
      exact hD
  exact hmain.analyticAt.analyticWithinAt

/-- The `C^ω` form of `thetaIntegral_analytic` (on the open set `Ioi 0`, `ContDiffOn ℝ ⊤` is
exactly analyticity).  This is the statement needed by the `ContDiffOn`-shaped consumers; it is a
one-line consequence of the analytic version. -/
theorem thetaIntegral_contDiffOn (F : ℝ → ℝ → ℝ)
    (hF : ContDiffOn ℝ ⊤ (Function.uncurry F) (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1))) :
    ContDiffOn ℝ ⊤ (fun z => ∫ θ in Set.Icc 0 (Real.pi / 2), F z θ) (Set.Ioi 0) :=
  (thetaIntegral_analytic F hF).contDiffOn isOpen_Ioi.uniqueDiffOn

end Work.Coercivity
