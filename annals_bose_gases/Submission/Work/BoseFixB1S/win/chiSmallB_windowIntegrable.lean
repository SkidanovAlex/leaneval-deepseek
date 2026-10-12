import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseFixB1B.pairRung.boxWinModeRGen_one
import Submission.Work.BoseFixB1B.pairRung.winModeContentLeWord
import Submission.Work.BoseFixB1B.wMR_memLp_one_contDiff
import Submission.Work.BoseFixB1S.win.chiSmallB_kinFT_decay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.win.chiSmallB_windowIntegrable`

`q`-integrability of the two genuine windowed mode contents of the sliding small box
`A = dlBox ℓ d u` at the *cosine-`M`-th-power* cutoff `χ = chiSmallB M ℓ d u`:

    Integrable (q ↦ boxWinModePGen ℓ |A| A χ Ψ q) ∧ Integrable (q ↦ boxWinModeRGen ℓ |A| A χ Ψ q).

## Why the existing `pairRung.winModeIntegrableBox` does not apply verbatim

`Work.BoseFixB1B.pairRung.winModeIntegrableBox` proves exactly this pair of statements, but under
the hypothesis `ContDiff ℝ ⊤ χ` (**smooth** window).  The sliding cutoff
`chiSmallB M ℓ d u x = χ(x/ℓ)·χ_M(x/(ℓd) − u)` is a product of the corpus bump `χ` at the big-box
scale and the cosine-`M`-th-power bump `χ_M` at the small-box scale; `χ_M` is only
`C^{M−1}` (`Work.BoseFixB1S.win.contDiff_chiSmall`), so `ContDiff ℝ ⊤ (chiSmallB …)` is simply
**false** for every `M`.  With the present hypothesis `5 ≤ M` the cutoff is `C⁴ ⊇ C³`.

The P-half of `winModeIntegrableBox` rests on the uniform `(1+‖p‖)⁻³` decay of the windowed
amplitude `tBamp χ p Φ i x` (`Work.SmallBoxTBWord.tBamp_decay`), whose only genuinely smooth input
is `Work.SmallBoxTBWord.chi_support_and_deriv_bound` — that lemma needs `χ` only up to order `3`
(the Fourier-decay engine `Commons.Analysis.Fourier.fourier_decay_mul_update` is stated for
`ContDiff ℝ 3`).  We therefore re-prove the two decay lemmas with the hypothesis weakened to
`ContDiff ℝ 3` and re-run the P-half.  The R-half already needs only `Continuous χ`
(`Work.BoseFixB1B.wMR_memLp_one_contDiff`, `…pairRung.boxWinModeRGen_one`).

## Contents

* `chi3_support_and_deriv_bound` — the `C³` support/derivative input;
* `tBamp_decay_three` — the `(1+‖p‖)⁻³` decay of the windowed amplitude for a `C³` window;
* `boxWinModePGen_decay_three`, `boxWinModePGen_integrable_three` — the P-half;
* `boxWinModeRGen_integrable_three` — the R-half (continuous window);
* `contDiff_three_chiSmallB`, `hcs_chiSmallB_priv`,
  `support_chiSmallB_subset_dlBox` — the `chiSmallB` facts;
* `chiSmallB_windowIntegrable` — the target.
-/

noncomputable section

open MeasureTheory Filter Metric
open scoped Topology Real BigOperators ENNReal ContDiff

namespace Work.BoseFixB1S.win

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-! ## 1. Elementary analytic helpers -/

/-- The norm of a real number inside `ℂ` is its absolute value. -/
private lemma norm_ofReal_abs (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by simp

/-- `(D / r³)² = D² r^{-6}` (in the real-power convention used for the decay constant). -/
private lemma div_cube_sq_eq_rpow (r : ℝ) (hr : 0 < r) (D : ℝ) :
    (D / r ^ 3) ^ 2 = D ^ 2 * r ^ (-(6 : ℝ)) := by
  rw [Real.rpow_neg hr.le, Real.rpow_ofNat, div_pow, div_eq_mul_inv]
  ring

/-- The single term of the final arithmetic: two copies of `(c·(D/r³))²·V` make `2c²VD²r^{-6}`. -/
private lemma two_mul_sq_div_cube (c Vab D r : ℝ) (hr : 0 < r) :
    (c * (D / r ^ 3)) ^ 2 * Vab + (c * (D / r ^ 3)) ^ 2 * Vab
      = (2 * c ^ 2 * Vab * D ^ 2) * r ^ (-(6 : ℝ)) := by
  have h2 : (c * (D / r ^ 3)) ^ 2 = c ^ 2 * D ^ 2 * r ^ (-(6 : ℝ)) := by
    rw [mul_pow, div_cube_sq_eq_rpow r hr D]
    ring
  rw [h2]
  ring

/-- A vector of `ℝ³` all of whose coordinates are bounded by `C` has norm at most `√3·C`. -/
private lemma norm_le_of_coord_abs_le {C : ℝ} (hC : 0 ≤ C) {y : E3}
    (hy : ∀ k : Fin 3, |y k| ≤ C) : ‖y‖ ≤ Real.sqrt 3 * C := by
  have hb : 0 ≤ Real.sqrt 3 * C := by positivity
  apply le_of_sq_le_sq
  · rw [EuclideanSpace.real_norm_sq_eq]
    calc ∑ k : Fin 3, (y k) ^ 2 ≤ ∑ _k : Fin 3, C ^ 2 := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          exact sq_le_sq.mpr (by simpa [abs_of_nonneg hC] using hy k)
      _ = 3 * C ^ 2 := by norm_num
      _ = (Real.sqrt 3 * C) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  · exact hb

/-- Absorption of the `(2π)` scaling of the Fourier variable:
`K·(1+r/c)⁻³ ≤ K·c³/(1+r)³` for `K ≥ 0`, `c ≥ 1`, `r ≥ 0`. -/
private lemma zpow_neg_three_le (K c r : ℝ) (hK : 0 ≤ K) (hc : 1 ≤ c) (hr : 0 ≤ r) :
    K * (1 + r / c) ^ (-(3:ℤ)) ≤ K * c ^ 3 / (1 + r) ^ 3 := by
  have hcpos : 0 < c := lt_of_lt_of_le one_pos hc
  have h1r : 0 ≤ 1 + r := by linarith
  have hbase : 0 < 1 + r / c := by positivity
  have hdiv : 1 + r / c = (c + r) / c := by field_simp
  have hexp : (1 + r / c) ^ 3 = (c + r) ^ 3 / c ^ 3 := by rw [hdiv, div_pow]
  have hle : (1 + r) ^ 3 / c ^ 3 ≤ (1 + r / c) ^ 3 := by
    rw [hexp]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ h1r (by linarith) 3) (by positivity)
  have hpos1 : 0 < (1 + r / c) ^ 3 := pow_pos hbase 3
  have hpos2 : 0 < (1 + r) ^ 3 / c ^ 3 := by positivity
  have hinv : ((1 + r / c) ^ 3)⁻¹ ≤ c ^ 3 / (1 + r) ^ 3 := by
    have h := (inv_le_inv₀ hpos1 hpos2).mpr hle
    rwa [inv_div] at h
  have hzpow : (1 + r / c) ^ (-(3:ℤ)) = ((1 + r / c) ^ 3)⁻¹ := by simp [zpow_neg]
  rw [hzpow]
  simpa [mul_div_assoc] using mul_le_mul_of_nonneg_left hinv hK

/-! ## 2. The `C³` support/derivative input -/

/-- The `C³`-version of `Work.SmallBoxTBWord.chi_support_and_deriv_bound`: the support of a
compactly supported `C³` function `χ : ℝ³ → ℝ` is contained in a ball `B(0,R)`, and the iterated
Fréchet derivatives of its complexification up to order `3` are globally bounded by a
nonnegative sequence `G`. -/
lemma chi3_support_and_deriv_bound {χ : E3 → ℝ} (hχ : ContDiff ℝ 3 χ)
    (hcs : HasCompactSupport χ) :
    ∃ R : ℝ, 0 < R ∧ tsupport χ ⊆ Metric.closedBall (0 : E3) R ∧
      ∃ G : ℕ → ℝ, (∀ k, 0 ≤ G k) ∧
        ∀ k ≤ 3, ∀ z : E3, ‖iteratedFDeriv ℝ k (fun z : E3 => (χ z : ℂ)) z‖ ≤ G k := by
  obtain ⟨r, hr⟩ := hcs.isBounded.subset_closedBall (0 : E3)
  have hRpos : 0 < max r 1 := lt_of_lt_of_le zero_lt_one (le_max_right r 1)
  have hsupp : tsupport χ ⊆ Metric.closedBall (0 : E3) (max r 1) :=
    hr.trans (Metric.closedBall_subset_closedBall (le_max_left r 1))
  have hfc : ContDiff ℝ 3 (fun z : E3 => (χ z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hχ
  have hfk : HasCompactSupport (fun z : E3 => (χ z : ℂ)) := by
    have key := hcs.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
    have h : (fun z : E3 => (χ z : ℂ)) = (fun x : ℝ => (x : ℂ)) ∘ χ := by ext z; rfl
    rwa [h]
  refine ⟨max r 1, hRpos, hsupp, ?_⟩
  have hsingle : ∀ k : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      (k ≤ 3 → ∀ z : E3, ‖iteratedFDeriv ℝ k (fun z : E3 => (χ z : ℂ)) z‖ ≤ B) := by
    intro k
    by_cases hk : k ≤ 3
    · have hkcd : ContDiff ℝ k (fun z : E3 => (χ z : ℂ)) := hfc.of_le (by exact_mod_cast hk)
      have hcont : Continuous (fun x : E3 => iteratedFDeriv ℝ k (fun z : E3 => (χ z : ℂ)) x) :=
        hkcd.continuous_iteratedFDeriv'
      have hcpt : HasCompactSupport (fun x : E3 =>
          iteratedFDeriv ℝ k (fun z : E3 => (χ z : ℂ)) x) :=
        HasCompactSupport.iteratedFDeriv (𝕜 := ℝ) hfk k
      obtain ⟨C, hCpos, hCle⟩ := (hcpt.isCompact_range hcont).isBounded.subset_closedBall_lt 0 0
      refine ⟨C, le_of_lt hCpos, fun _ z => ?_⟩
      have hz := hCle ⟨z, rfl⟩
      rwa [Metric.mem_closedBall, dist_zero_right] at hz
    · exact ⟨0, le_refl 0, fun h => absurd h hk⟩
  choose G hG0 hG using hsingle
  exact ⟨G, hG0, fun k hk z => hG k hk z⟩

/-! ## 3. The uniform `(1+‖p‖)⁻³` decay of the windowed amplitude at a `C³` window -/

theorem tBamp_decay_three {N : ℕ} {a : ℝ} (ha : 0 < a) {χ : E3 → ℝ} (hχ : ContDiff ℝ 3 χ)
    (hcs : HasCompactSupport χ) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Submission.BoseGases.X N), x ∈ Submission.BoseGases.abox N a →
      ∀ (i : Fin N) (p : E3), ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ≤ C / (1 + ‖p‖) ^ 3 := by
  obtain ⟨R0, hR0pos, hR0supp, G, hGnn, hGbd⟩ := chi3_support_and_deriv_bound hχ hcs
  set R : ℝ := max R0 1 with hRdef
  set S : ℝ := max R (3 * a) with hSdef
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hRS : R ≤ S := le_max_left _ _
  have hSnn : 0 ≤ S := le_of_lt (lt_of_lt_of_le hRpos hRS)
  obtain ⟨Cd, hCd0, hCd⟩ := Commons.Analysis.Fourier.fourier_decay_mul_update N R S hRpos hRS
  obtain ⟨M, hMnn, hMbd⟩ := Work.SmallBoxTBWord.complexified_iteratedFDeriv_bound (N := N) hSnn hΦ
  refine ⟨Cd * (1 + ∑ k ∈ Finset.range 4, |G k|) * (1 + ∑ k ∈ Finset.range 4, |M k|) * (2*π)^3,
    by positivity, ?_⟩
  intro x hx i p
  have hxS : ∀ j : Fin N, ‖x j‖ ≤ S := by
    intro j
    have hmem : x j ∈ Submission.BoseGases.acube a := hx j
    rw [Submission.BoseGases.mem_acube_iff] at hmem
    have habs : ∀ k : Fin 3, |(x j) k| ≤ a / 2 := by
      intro k
      rw [abs_le]
      exact ⟨by linarith [(hmem k).1], (hmem k).2⟩
    have h1 : ‖x j‖ ≤ Real.sqrt 3 * (a / 2) := norm_le_of_coord_abs_le (by positivity) habs
    have h2 : Real.sqrt 3 * (a / 2) ≤ 3 * a := by
      have hs : Real.sqrt 3 ≤ 3 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg 3]
      nlinarith
    linarith [h1, h2, le_max_right R (3 * a)]
  have hchi3 : ContDiff ℝ 3 (fun z : E3 => (χ z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hχ
  have hPhi3 : ContDiff ℝ 3 (fun y : Submission.BoseGases.X N => (Φ y : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hΦ.of_le (WithTop.coe_le_coe.mpr le_top))
  have hgsupp : ∀ z : E3, (fun z : E3 => (χ z : ℂ)) z ≠ 0 → ‖z‖ ≤ R := by
    intro z hz
    have hzmem : z ∈ tsupport χ := subset_tsupport χ (by simpa using hz)
    have h1 : z ∈ Metric.closedBall (0 : E3) R0 := hR0supp hzmem
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h1
    exact le_trans h1 (le_max_left _ _)
  have hdec := hCd (fun z : E3 => (χ z : ℂ)) G hchi3 hgsupp hGbd
      (fun y : Submission.BoseGases.X N => (Φ y : ℂ)) M hPhi3 hMbd x hxS i ((2*π)⁻¹ • p)
  have hconv : Work.SmallBoxTBWord.tBamp χ p Φ i x = Submission.BoseGases.kinFT
      (fun z : E3 => (χ z : ℂ) * (Φ (Function.update x i z) : ℂ)) p := by
    rw [Work.SmallBoxTBWord.tBamp, Submission.BoseGases.kinFT]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    ring
  rw [hconv, Work.SmallBoxBridge.Resolve.kinFT_eq_fourier]
  refine hdec.trans ?_
  have hnorm_xi : ‖(2 * π)⁻¹ • p‖ = ‖p‖ / (2 * π) := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ (2*π)⁻¹), inv_mul_eq_div]
  rw [hnorm_xi]
  have hK : 0 ≤ Cd * (1 + ∑ k ∈ Finset.range 4, |G k|) * (1 + ∑ k ∈ Finset.range 4, |M k|) :=
    mul_nonneg (mul_nonneg hCd0 (by positivity)) (by positivity)
  have := zpow_neg_three_le
    (Cd * (1 + ∑ k ∈ Finset.range 4, |G k|) * (1 + ∑ k ∈ Finset.range 4, |M k|))
    (2*π) ‖p‖ hK (by linarith [Real.pi_gt_three]) (norm_nonneg p)
  simpa using this

/-! ## 4. The P-half: uniform `(1+‖q‖)⁻⁶` decay and integrability -/

/-- `(1+‖q‖)⁻⁶` decay of the genuine windowed `q`-diagonal content at a `C³` window
(the `ContDiff ℝ 3`-relaxation of `Work.BoseFixB1B.pairRung.boxWinModePGen_decayBox`). -/
theorem boxWinModePGen_decay_three {n : ℕ} {a volA : ℝ} {Ac : Set E3} {χ : E3 → ℝ}
    {Ψ : Submission.BoseGases.X n → ℝ}
    (ha : 0 < a) (hAcm : MeasurableSet Ac) (hAcsub : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal) (hvolpos : 0 < volA)
    (hχc : ContDiff ℝ 3 χ) (hχs : HasCompactSupport χ)
    (hχsupp : ∀ z, z ∉ Ac → χ z = 0)
    (hΨc : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ q : E3,
      Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q ≤ K * (1 + ‖q‖) ^ (-(6 : ℝ)) := by
  classical
  -- a bound for `Ψ` on the box
  obtain ⟨Cψ, hCψ0, hCψ⟩ :=
    Work.BoseFixB1.exists_bound_abox_pos (N := n) (ℓ := a) ha hΨc.continuous
  -- the two Fourier decay constants (`Ψ` and the constant state `1`)
  obtain ⟨C₁, hC₁0, hC₁⟩ := tBamp_decay_three (N := n) (a := a) ha hχc hχs hΨc
  obtain ⟨C₂, hC₂0, hC₂⟩ := tBamp_decay_three (N := n) (a := a) ha hχc hχs
    (Φ := fun _ : Submission.BoseGases.X n => (1 : ℝ)) contDiff_const
  set D : ℝ := C₁ + Cψ * C₂ with hDdef
  have hD0 : 0 ≤ D := by
    rw [hDdef]
    exact add_nonneg hC₁0 (mul_nonneg hCψ0 hC₂0)
  -- ## the box mean is bounded by `Cψ` on the box
  have hboxP : ∀ (i : Fin n) (x : Submission.BoseGases.X n),
      x ∈ Submission.BoseGases.abox n a →
      |Work.SmallBoxTBWord.boxP volA Ac i Ψ (Function.update x i (0 : E3))| ≤ Cψ := by
    intro i x hx
    have hIntEq : (∫ z in Ac, Ψ (Function.update (Function.update x i (0 : E3)) i z))
        = ∫ z in Ac, Ψ (Function.update x i z) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with z
      rw [Function.update_idem]
    have hrepr : Work.SmallBoxTBWord.boxP volA Ac i Ψ (Function.update x i (0 : E3))
        = volA⁻¹ * ∫ z in Ac, Ψ (Function.update x i z) := by
      rw [Work.SmallBoxTBWord.boxP, one_div, hIntEq]
    rw [hrepr, abs_mul, abs_of_nonneg (inv_nonneg.mpr hvolpos.le)]
    have hint : |∫ z in Ac, Ψ (Function.update x i z)| ≤ Cψ * volA := by
      have hfin : (volume : Measure E3) Ac < ⊤ :=
        lt_of_le_of_lt (measure_mono hAcsub) (Submission.BoseGases.acube_lt_top a ha.le)
      have hb : ∀ z ∈ Ac, ‖Ψ (Function.update x i z)‖ ≤ Cψ := by
        intro z hz
        rw [Real.norm_eq_abs]
        exact hCψ _ (Submission.BoseGases.update_mem_abox i hx (hAcsub hz))
      have h1 := norm_setIntegral_le_of_norm_le_const hfin hb
      rw [Real.norm_eq_abs, MeasureTheory.Measure.real_def, ← hvol] at h1
      exact h1
    calc volA⁻¹ * |∫ z in Ac, Ψ (Function.update x i z)| ≤ volA⁻¹ * (Cψ * volA) :=
          mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hvolpos.le)
      _ = Cψ := by
          rw [inv_mul_eq_iff_eq_mul₀ (ne_of_gt hvolpos)]
          ring
  -- ## the box-projected windowed amplitude decays like `(1+‖q‖)^{-3}`
  have hdecQ : ∀ (x : Submission.BoseGases.X n), x ∈ Submission.BoseGases.abox n a →
      ∀ (i : Fin n) (q : E3),
      ‖Work.SmallBoxTBWord.tBamp χ q (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖
        ≤ D / (1 + ‖q‖) ^ 3 := by
    intro x hx i q
    rw [Work.BoseBox.tBamp_boxQInd_eq_sub Ψ i q x (0 : E3) hχsupp hχc.continuous hχs
      hΨc.continuous]
    have h1 := hC₁ x hx i q
    have h2 := hC₂ x hx i q
    have h3 := hboxP i x hx
    calc ‖Work.SmallBoxTBWord.tBamp χ q Ψ i x
          - ((Work.SmallBoxTBWord.boxP volA Ac i Ψ (Function.update x i (0 : E3)) : ℝ) : ℂ)
            * Work.SmallBoxTBWord.tBamp χ q (fun _ : Submission.BoseGases.X n => (1 : ℝ)) i x‖
        ≤ ‖Work.SmallBoxTBWord.tBamp χ q Ψ i x‖
          + ‖((Work.SmallBoxTBWord.boxP volA Ac i Ψ (Function.update x i (0 : E3)) : ℝ) : ℂ)
            * Work.SmallBoxTBWord.tBamp χ q (fun _ : Submission.BoseGases.X n => (1 : ℝ)) i x‖ :=
          norm_sub_le _ _
      _ = ‖Work.SmallBoxTBWord.tBamp χ q Ψ i x‖
          + |Work.SmallBoxTBWord.boxP volA Ac i Ψ (Function.update x i (0 : E3))|
            * ‖Work.SmallBoxTBWord.tBamp χ q
                (fun _ : Submission.BoseGases.X n => (1 : ℝ)) i x‖ := by
          rw [norm_mul, norm_ofReal_abs]
      _ ≤ C₁ / (1 + ‖q‖) ^ 3 + Cψ * (C₂ / (1 + ‖q‖) ^ 3) :=
          add_le_add h1 (mul_le_mul h3 h2 (norm_nonneg _) hCψ0)
      _ = D / (1 + ‖q‖) ^ 3 := by
          rw [hDdef, ← mul_div_assoc, ← add_div]
  -- ## the two real slot amplitudes inherit the bound
  have hslotRe : ∀ (q : E3) (x : Submission.BoseGases.X n),
      x ∈ Submission.BoseGases.abox n a → ∀ i : Fin n,
      |∫ z in Ac, Work.BoseFixB1.boxWinModeReGen volA Ac χ q z * Ψ (Function.update x i z)|
        ≤ D / (1 + ‖q‖) ^ 3 := by
    intro q x hx i
    have hns := Work.BoseFixB1.tBamp_boxQInd_normSq (n := n) (a := a) (volA := volA) ha hvolpos
      hAcm hAcsub hχc.continuous hχs hΨc.continuous i hx q
    have hB0 : (0 : ℝ) ≤ D / (1 + ‖q‖) ^ 3 := div_nonneg hD0 (by positivity)
    have hsplit : (∫ z in Ac, Work.BoseFixB1.boxWinModeReGen volA Ac χ q z
          * Ψ (Function.update x i z)) ^ 2
        ≤ ‖Work.SmallBoxTBWord.tBamp χ q (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2 := by
      rw [hns]
      exact le_add_of_nonneg_right (sq_nonneg _)
    have hsq : (∫ z in Ac, Work.BoseFixB1.boxWinModeReGen volA Ac χ q z
          * Ψ (Function.update x i z)) ^ 2 ≤ (D / (1 + ‖q‖) ^ 3) ^ 2 :=
      le_trans hsplit (pow_le_pow_left₀ (norm_nonneg _) (hdecQ x hx i q) 2)
    have h2 := sq_le_sq.mp hsq
    rwa [abs_of_nonneg hB0] at h2
  have hslotIm : ∀ (q : E3) (x : Submission.BoseGases.X n),
      x ∈ Submission.BoseGases.abox n a → ∀ i : Fin n,
      |∫ z in Ac, Work.BoseFixB1.boxWinModeImGen volA Ac χ q z * Ψ (Function.update x i z)|
        ≤ D / (1 + ‖q‖) ^ 3 := by
    intro q x hx i
    have hns := Work.BoseFixB1.tBamp_boxQInd_normSq (n := n) (a := a) (volA := volA) ha hvolpos
      hAcm hAcsub hχc.continuous hχs hΨc.continuous i hx q
    have hB0 : (0 : ℝ) ≤ D / (1 + ‖q‖) ^ 3 := div_nonneg hD0 (by positivity)
    have hsplit : (∫ z in Ac, Work.BoseFixB1.boxWinModeImGen volA Ac χ q z
          * Ψ (Function.update x i z)) ^ 2
        ≤ ‖Work.SmallBoxTBWord.tBamp χ q (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2 := by
      rw [hns]
      exact le_add_of_nonneg_left (sq_nonneg _)
    have hsq : (∫ z in Ac, Work.BoseFixB1.boxWinModeImGen volA Ac χ q z
          * Ψ (Function.update x i z)) ^ 2 ≤ (D / (1 + ‖q‖) ^ 3) ^ 2 :=
      le_trans hsplit (pow_le_pow_left₀ (norm_nonneg _) (hdecQ x hx i q) 2)
    have h2 := sq_le_sq.mp hsq
    rwa [abs_of_nonneg hB0] at h2
  -- ## the `τ`-amplitude bound
  have hann : ∀ (q : E3) (g : E3 → ℝ),
      (∀ (x : Submission.BoseGases.X n), x ∈ Submission.BoseGases.abox n a → ∀ i : Fin n,
        |∫ z in Ac, g z * Ψ (Function.update x i z)| ≤ D / (1 + ‖q‖) ^ 3) →
      ∀ x ∈ Submission.BoseGases.abox n a,
        |Work.BoseFixB1.boxTauAnnGen volA Ac g Ψ x|
          ≤ (Real.sqrt volA)⁻¹ * (n : ℝ) * (D / (1 + ‖q‖) ^ 3) := by
    intro q g hg x hx
    set B : ℝ := D / (1 + ‖q‖) ^ 3 with hBdef
    have hsum : |∑ i : Fin n, Ac.indicator (fun _ => (1 : ℝ)) (x i)
          * (∫ z in Ac, g z * Ψ (Function.update x i z))| ≤ (n : ℝ) * B := by
      calc |∑ i : Fin n, Ac.indicator (fun _ => (1 : ℝ)) (x i)
            * (∫ z in Ac, g z * Ψ (Function.update x i z))|
          ≤ ∑ i : Fin n, |Ac.indicator (fun _ => (1 : ℝ)) (x i)
              * (∫ z in Ac, g z * Ψ (Function.update x i z))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin n, B := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            rw [abs_mul]
            have hind : |Ac.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
              by_cases hxi : x i ∈ Ac
              · rw [Set.indicator_of_mem hxi]
                norm_num
              · rw [Set.indicator_of_notMem hxi]
                norm_num
            calc |Ac.indicator (fun _ => (1 : ℝ)) (x i)|
                  * |∫ z in Ac, g z * Ψ (Function.update x i z)|
                ≤ 1 * B := mul_le_mul hind (hg x hx i) (abs_nonneg _) (by norm_num)
              _ = B := one_mul B
        _ = (n : ℝ) * B := by rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    rw [Work.BoseFixB1.boxTauAnnGen, abs_mul,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg volA))]
    calc (Real.sqrt volA)⁻¹ * |∑ i : Fin n, Ac.indicator (fun _ => (1 : ℝ)) (x i)
          * (∫ z in Ac, g z * Ψ (Function.update x i z))|
        ≤ (Real.sqrt volA)⁻¹ * ((n : ℝ) * B) :=
          mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Real.sqrt_nonneg volA))
      _ = (Real.sqrt volA)⁻¹ * (n : ℝ) * (D / (1 + ‖q‖) ^ 3) := by
          rw [hBdef]
          ring
  -- ## the box integral of the square of the `τ`-amplitude
  have hInt : ∀ (q : E3) (g : E3 → ℝ),
      (∀ x ∈ Submission.BoseGases.abox n a,
        |Work.BoseFixB1.boxTauAnnGen volA Ac g Ψ x|
          ≤ (Real.sqrt volA)⁻¹ * (n : ℝ) * (D / (1 + ‖q‖) ^ 3)) →
      (∫ x in Submission.BoseGases.abox n a,
          (Work.BoseFixB1.boxTauAnnGen volA Ac g Ψ x) ^ 2)
        ≤ ((Real.sqrt volA)⁻¹ * (n : ℝ) * (D / (1 + ‖q‖) ^ 3)) ^ 2
          * (MeasureTheory.volume (Submission.BoseGases.abox n a)).toReal := by
    intro q g hg
    haveI : IsFiniteMeasure ((MeasureTheory.volume : MeasureTheory.Measure
        (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n a)) :=
      ⟨by rw [Measure.restrict_apply_univ]
          exact Submission.BoseGases.abox_lt_top n a ha.le⟩
    calc (∫ x in Submission.BoseGases.abox n a,
            (Work.BoseFixB1.boxTauAnnGen volA Ac g Ψ x) ^ 2)
        ≤ ∫ _x in Submission.BoseGases.abox n a,
            ((Real.sqrt volA)⁻¹ * (n : ℝ) * (D / (1 + ‖q‖) ^ 3)) ^ 2 := by
          refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _)
            (integrable_const _) ?_
          refine (ae_restrict_iff' (Submission.BoseGases.abox_measurable n a)).mpr
            (Eventually.of_forall fun x hx => ?_)
          have hle : |Work.BoseFixB1.boxTauAnnGen volA Ac g Ψ x| ^ 2
              ≤ ((Real.sqrt volA)⁻¹ * (n : ℝ) * (D / (1 + ‖q‖) ^ 3)) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) (hg x hx) 2
          simpa only [sq_abs] using hle
      _ = ((Real.sqrt volA)⁻¹ * (n : ℝ) * (D / (1 + ‖q‖) ^ 3)) ^ 2
            * (MeasureTheory.volume (Submission.BoseGases.abox n a)).toReal := by
          rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def, smul_eq_mul,
            mul_comm]
  -- ## assembly and the constant
  set Vab : ℝ := (MeasureTheory.volume (Submission.BoseGases.abox n a)).toReal with hVabdef
  have hVab0 : 0 ≤ Vab := by
    rw [hVabdef]
    exact ENNReal.toReal_nonneg
  refine ⟨2 * ((Real.sqrt volA)⁻¹ * (n : ℝ)) ^ 2 * Vab * D ^ 2, ?_, ?_⟩
  · refine mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg _)) hVab0)
      (sq_nonneg _)
  · intro q
    have hbRe := hInt q (Work.BoseFixB1.boxWinModeReGen volA Ac χ q)
      (fun x hx => hann q _ (fun x hx i => hslotRe q x hx i) x hx)
    have hbIm := hInt q (Work.BoseFixB1.boxWinModeImGen volA Ac χ q)
      (fun x hx => hann q _ (fun x hx i => hslotIm q x hx i) x hx)
    rw [Work.BoseFixB1.boxWinModePGen, Work.BoseFixB1.boxModePGen, Work.BoseFixB1.boxModePGen]
    calc (∫ x in Submission.BoseGases.abox n a, (Work.BoseFixB1.boxTauAnnGen volA Ac
              (Work.BoseFixB1.boxWinModeReGen volA Ac χ q) Ψ x) ^ 2)
          + (∫ x in Submission.BoseGases.abox n a, (Work.BoseFixB1.boxTauAnnGen volA Ac
              (Work.BoseFixB1.boxWinModeImGen volA Ac χ q) Ψ x) ^ 2)
        ≤ ((Real.sqrt volA)⁻¹ * (n : ℝ) * (D / (1 + ‖q‖) ^ 3)) ^ 2 * Vab
          + ((Real.sqrt volA)⁻¹ * (n : ℝ) * (D / (1 + ‖q‖) ^ 3)) ^ 2 * Vab :=
          add_le_add hbRe hbIm
      _ = (2 * ((Real.sqrt volA)⁻¹ * (n : ℝ)) ^ 2 * Vab * D ^ 2) * (1 + ‖q‖) ^ (-(6 : ℝ)) :=
          two_mul_sq_div_cube ((Real.sqrt volA)⁻¹ * (n : ℝ)) Vab D (1 + ‖q‖) (by positivity)

/-- Integrability of the genuine windowed `q`-diagonal content at a `C³` window. -/
theorem boxWinModePGen_integrable_three {n : ℕ} {a volA : ℝ} {Ac : Set E3} {χ : E3 → ℝ}
    {Ψ : Submission.BoseGases.X n → ℝ}
    (ha : 0 < a) (hAcm : MeasurableSet Ac) (hAcsub : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal) (hvolpos : 0 < volA)
    (hχc : ContDiff ℝ 3 χ) (hχs : HasCompactSupport χ)
    (hχsupp : ∀ z, z ∉ Ac → χ z = 0)
    (hΨc : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    MeasureTheory.Integrable (fun q : E3 => Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q) := by
  obtain ⟨K, _hK0, hK⟩ :=
    boxWinModePGen_decay_three ha hAcm hAcsub hvol hvolpos hχc hχs hχsupp hΨc
  refine Integrable.mono' (g := fun q : E3 => K * (1 + ‖q‖) ^ (-(6 : ℝ))) ?_ ?_ ?_
  · exact (integrable_one_add_norm (E := E3) (μ := (volume : Measure E3)) (r := 6)
      (by rw [finrank_euclideanSpace, Fintype.card_fin]; norm_num)).const_mul K
  · exact Work.BoseFixB1B.pairRung.aeStronglyMeasurable_boxWinModePGen hAcm hχc.continuous
      hΨc.continuous
  · filter_upwards with q
    have hP0 : 0 ≤ Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q := by
      rw [Work.BoseFixB1.boxWinModePGen, Work.BoseFixB1.boxModePGen, Work.BoseFixB1.boxModePGen]
      exact add_nonneg (integral_nonneg fun x => sq_nonneg _)
        (integral_nonneg fun x => sq_nonneg _)
    rw [Real.norm_of_nonneg hP0]
    exact hK q

/-- Integrability of the genuine windowed `q`-pairing content at a *continuous* window
(this half of `Work.BoseFixB1B.pairRung.winModeIntegrableBox` never needed smoothness). -/
theorem boxWinModeRGen_integrable_three {n : ℕ} {a volA : ℝ} {Ac : Set E3} {χ : E3 → ℝ}
    {Ψ : Submission.BoseGases.X n → ℝ}
    (ha : 0 < a) (hAcm : MeasurableSet Ac) (hAcsub : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal) (hvolpos : 0 < volA)
    (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    (hχsupp : ∀ z, z ∉ Ac → χ z = 0)
    (hΨc : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    MeasureTheory.Integrable (fun q : E3 => Work.BoseFixB1.boxWinModeRGen a volA Ac χ Ψ q) := by
  rcases n with _ | m
  · -- `n = 0`: the slot sums are empty
    have h0 : ∀ q : E3, Work.BoseFixB1.boxWinModeRGen a volA Ac χ Ψ q = 0 := by
      intro q
      simp [Work.BoseFixB1.boxWinModeRGen, Work.BoseFixB1.boxModeRGen,
        Work.BoseFixB1.boxTauAnnGen, Work.BoseFixB1.boxTauDagGen]
    rw [funext h0]
    simp
  · rcases m with _ | k
    · -- `n = 1`: the content vanishes identically
      have h0 := Work.BoseFixB1B.pairRung.boxWinModeRGen_one ha hAcm hAcsub hvol hvolpos hχc
        hχs hχsupp hΨc.continuous
      have h0' : (fun q : E3 => Work.BoseFixB1.boxWinModeRGen a volA Ac χ Ψ q)
          = fun _ : E3 => (0 : ℝ) := funext (fun q => congrFun h0 q)
      rw [h0']
      simp
    · -- `n = k + 2`: the pair-content theorem
      exact MeasureTheory.memLp_one_iff_integrable.mp
        (Work.BoseFixB1B.wMR_memLp_one_contDiff (N := k) hAcm ha hAcsub hvol hvolpos
          hχc hχs hχsupp hΨc)

/-! ## 5. Facts about the sliding cosine-`M` cutoff `chiSmallB` -/

/-- `chiSmallB M ℓ d u` is `C³` for `M ≥ 4` (the small-box factor is `C^{M−1}`, the big-box
factor is the smooth corpus bump). -/
lemma contDiff_three_chiSmallB {M : ℕ} (hM : 4 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : E3) : ContDiff ℝ 3 (Submission.BoseGases.chiSmallB M ℓ d u) := by
  have hsmall : ContDiff ℝ 3 (Submission.BoseGases.chiSmall M) :=
    contDiff_chiSmall 3 M (by omega)
  have haff : ContDiff ℝ 3 (fun x : E3 => (ℓ * d)⁻¹ • x - u) := by
    have h1 : ContDiff ℝ 3 (fun x : E3 => (ℓ * d)⁻¹ • x) :=
      ContinuousLinearMap.contDiff ((ℓ * d)⁻¹ • ContinuousLinearMap.id ℝ E3)
    exact h1.sub contDiff_const
  have h2 : ContDiff ℝ 3
      (fun x : E3 => Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) :=
    hsmall.comp haff
  have hchi : ContDiff ℝ 3 Submission.BoseGases.chi :=
    Submission.BoseGases.chi_contDiff.of_le (WithTop.coe_le_coe.mpr le_top)
  have h3 : ContDiff ℝ 3 (fun x : E3 => Submission.BoseGases.chiScale ℓ x) := by
    have hlin : ContDiff ℝ 3 (fun x : E3 => (ℓ⁻¹) • x) :=
      ContinuousLinearMap.contDiff ((ℓ⁻¹) • ContinuousLinearMap.id ℝ E3)
    have heq : (fun x : E3 => Submission.BoseGases.chiScale ℓ x)
        = fun x : E3 => Submission.BoseGases.chi ((ℓ⁻¹) • x) := rfl
    rw [heq]
    exact hchi.comp hlin
  exact h3.mul h2

/-- `chiSmallB M ℓ d u` has compact support (`M ≥ 1`): its support is contained in the preimage of
the unit ball under `x ↦ (ℓd)⁻¹ • x − u`, hence in a closed ball. -/
private lemma hcs_chiSmallB_priv {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : E3) : HasCompactSupport (Submission.BoseGases.chiSmallB M ℓ d u) := by
  have hc : 0 < ℓ * d := mul_pos hℓ hd
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : E3) (ℓ * d * (1 + ‖u‖))) ?_
  intro x hx
  rw [Function.mem_support] at hx
  have h2 : Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u) ≠ 0 := by
    intro h
    exact hx (by dsimp [Submission.BoseGases.chiSmallB]; rw [h, mul_zero])
  have h3 : ‖(ℓ * d)⁻¹ • x - u‖ ≤ 1 := chiSmall_support_norm_le hM h2
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  have h4 : ‖(ℓ * d)⁻¹ • x‖ ≤ 1 + ‖u‖ := by
    have h5 : (ℓ * d)⁻¹ • x - u + u = (ℓ * d)⁻¹ • x := by abel
    calc ‖(ℓ * d)⁻¹ • x‖ = ‖(ℓ * d)⁻¹ • x - u + u‖ := by rw [h5]
      _ ≤ ‖(ℓ * d)⁻¹ • x - u‖ + ‖u‖ := norm_add_le _ _
      _ ≤ 1 + ‖u‖ := by linarith
  have h6 : ‖x‖ = (ℓ * d) * ‖(ℓ * d)⁻¹ • x‖ := by
    have h7 : (ℓ * d) • ((ℓ * d)⁻¹ • x) = x := by
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hc), one_smul]
    have hnorm := congrArg Norm.norm h7
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hc)] at hnorm
    exact hnorm.symm
  rw [h6]
  calc (ℓ * d) * ‖(ℓ * d)⁻¹ • x‖ ≤ (ℓ * d) * (1 + ‖u‖) :=
        mul_le_mul_of_nonneg_left h4 (le_of_lt hc)
    _ = ℓ * d * (1 + ‖u‖) := by ring

/-- The support of `chiSmallB M ℓ d u` lies in the sliding small box `dlBox ℓ d u`. -/
lemma support_chiSmallB_subset_dlBox {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : E3) : Function.support (fun x : E3 => Submission.BoseGases.chiSmallB M ℓ d u x) ⊆
      Submission.BoseGases.dlBox ℓ d u := by
  intro x hx
  rw [Function.mem_support] at hx
  rw [Submission.BoseGases.mem_dlBox_iff]
  constructor
  · rw [Submission.BoseGases.mem_acube_iff]
    intro m
    rw [Set.mem_Icc]
    obtain ⟨h1, h2⟩ := abs_le.mp (Submission.BoseGases.chiSmallB_support_big_box hM hℓ hx m)
    exact ⟨by linarith, by linarith⟩
  · rw [Submission.BoseGases.mem_acube_iff]
    intro m
    rw [Set.mem_Icc]
    obtain ⟨h1, h2⟩ := abs_le.mp (Submission.BoseGases.chiSmallB_support_small_box_dist hM hℓ hd hx m)
    exact ⟨by linarith, by linarith⟩

/-! ## 6. The target -/

theorem chiSmallB_windowIntegrable {n : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hd1 : d ≤ 1)
    {M : ℕ} (hM : 5 ≤ M) (u : EuclideanSpace ℝ (Fin 3))
    (hVpos : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨc : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) => Work.BoseFixB1.boxWinModePGen ℓ
        (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
        (Submission.BoseGases.chiSmallB M ℓ d u) Ψ q) ∧
    MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) => Work.BoseFixB1.boxWinModeRGen ℓ
        (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
        (Submission.BoseGases.chiSmallB M ℓ d u) Ψ q) := by
  have hM1 : 1 ≤ M := by omega
  have hM4 : 4 ≤ M := by omega
  have hAcm : MeasurableSet (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAcsub : Submission.BoseGases.dlBox ℓ d u ⊆ Submission.BoseGases.acube ℓ :=
    Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hvol : Work.SmallBoxSliding.boxMass ℓ d u
      = (MeasureTheory.volume (Submission.BoseGases.dlBox ℓ d u)).toReal := by
    rw [Work.SmallBoxSliding.boxMass_eq_measureReal ℓ d u, MeasureTheory.Measure.real_def]
  have hχc3 : ContDiff ℝ 3 (Submission.BoseGases.chiSmallB M ℓ d u) :=
    contDiff_three_chiSmallB hM4 hℓ hd u
  have hχs : HasCompactSupport (Submission.BoseGases.chiSmallB M ℓ d u) :=
    hcs_chiSmallB_priv hM1 hℓ hd u
  have hχsupp : ∀ z, z ∉ Submission.BoseGases.dlBox ℓ d u →
      Submission.BoseGases.chiSmallB M ℓ d u z = 0 := by
    intro z hz
    by_contra h
    exact hz (support_chiSmallB_subset_dlBox hM1 hℓ hd u (Function.mem_support.mpr h))
  exact ⟨boxWinModePGen_integrable_three hℓ hAcm hAcsub hvol hVpos hχc3 hχs hχsupp hΨc,
    boxWinModeRGen_integrable_three hℓ hAcm hAcsub hvol hVpos hχc3.continuous hχs hχsupp hΨc⟩

end Work.BoseFixB1S.win
