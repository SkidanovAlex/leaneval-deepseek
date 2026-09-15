import Mathlib
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Commons.NumberTheory.Zeta.psi_sub_id_powLog_real
import Submission.Commons.Analysis.Asymptotics.poly_mul_exp_neg_sqrtLog_le

open Complex Filter Metric Set MeasureTheory
open scoped Real Topology BigOperators Interval

namespace Commons.NumberTheory.Zeta

set_option maxHeartbeats 0

/-!
# The Chebyshev `ψ` de la Vallée Poussin error term `x·exp(−c√(log x))`

The public commons lemma `Commons.NumberTheory.Zeta.psi_sub_id_powLog_real` proves
`|ψ(x) − x| ≤ x/(log x)^A` for every `A > 0`; it is *derived from* the stronger
exponential error term `|ψ(x) − x| ≤ x·exp(−c√(log x))` (de la Vallée Poussin),
whose proof lives inside that file but was left `private` and hence is not
exported.  This file re-establishes the exponential form directly from the
public truncated-Perron / zero-free-region interface, so that it can be used by
everyone (e.g. by the character-twisted PNT estimates).

Everything below the header is the explicit de la Vallée Poussin engine: the
contour integral for the truncated Perron formula on a deformation of the line
`Re s = 1 + 1/log x` down to the zero-free edge `Re s = 1 − c/(2(log T + 3) + 2)`
at height `T = exp(√(log x))`, with the three boundary integrals estimated by the
zero-free-region bounds on `ζ'/ζ`.
-/

/-! ## Basic helpers -/

private lemma engM_pos (x : ℝ) : 0 < Real.log (engT x + 3) + 1 := by
  have h : (1 : ℝ) < engT x + 3 := by linarith [engT_pos x]
  have := Real.log_pos h
  linarith

private lemma engDelta_nonneg {x c : ℝ} (hc : 0 < c) : 0 ≤ engDelta x c := by
  dsimp [engDelta]
  exact div_nonneg (le_of_lt hc) (by linarith [engM_pos x])

private lemma engDelta_pos {x c : ℝ} (hc : 0 < c) : 0 < engDelta x c := by
  dsimp [engDelta]
  have h : 0 < Real.log (engT x + 3) + 1 := engM_pos x
  positivity

private lemma perronRe_gt_one {x : ℝ} (hx : 1 < x) : 1 < perronRe x := by
  dsimp [perronRe]
  have h : 0 < 1 / Real.log x := by
    have := Real.log_pos hx
    positivity
  linarith

private lemma perronRe_le_two_of_three {x : ℝ} (hx : 3 ≤ x) : perronRe x ≤ 2 := by
  dsimp [perronRe]
  have hx1 : 1 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos hx1
  have hlog : 1 ≤ Real.log x := by
    have h3 : (1 : ℝ) ≤ Real.log 3 :=
      (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 3)).2 (le_of_lt Real.exp_one_lt_three)
    exact le_trans h3 (Real.log_le_log (by norm_num) hx)
  have hd : 1 / Real.log x ≤ 1 := (div_le_one hlogpos).2 hlog
  linarith

private lemma zeta1_eq_sub_mul_zeta {s : ℂ} (hs : s ≠ 1) :
    riemannZeta₁ s = (s - 1) * riemannZeta s := by
  rw [riemannZeta₁, riemannZeta_eq_inv_sub_add hs]
  field_simp

private lemma zeta_ne_zero_of_zeta1_ne_zero {s : ℂ} (h1 : riemannZeta₁ s ≠ 0)
    (hs1 : s ≠ 1) : riemannZeta s ≠ 0 := by
  rw [zeta1_eq_sub_mul_zeta hs1] at h1
  exact fun h => h1 (by rw [h, mul_zero])

private lemma zeta1_ne_zero_of_zeta_ne_zero {s : ℂ} (h : riemannZeta s ≠ 0)
    (hs1 : s ≠ 1) : riemannZeta₁ s ≠ 0 := by
  rw [zeta1_eq_sub_mul_zeta hs1]
  exact mul_ne_zero (sub_ne_zero.mpr hs1) h

private lemma psiIntF_continuousAt_of_zeta_ne_zero {x : ℝ} (hx : 0 < x) {s : ℂ}
    (hsRe : 0 < s.re) (hs1 : s ≠ 1) (hζ : riemannZeta s ≠ 0) :
    ContinuousAt (psiIntF x) s := by
  have hderAn : AnalyticOnNhd ℂ (deriv riemannZeta) ({1}ᶜ : Set ℂ) :=
    AnalyticOnNhd.deriv analyticOn_riemannZeta
  have hc1 : ContinuousAt (fun w : ℂ => -(deriv riemannZeta w) / riemannZeta w) s := by
    have hcd : ContinuousAt (fun w : ℂ => deriv riemannZeta w) s :=
      hderAn.continuousOn.continuousAt (isOpen_compl_singleton.mem_nhds hs1)
    have hcz : ContinuousAt riemannZeta s :=
      analyticOn_riemannZeta.continuousOn.continuousAt (isOpen_compl_singleton.mem_nhds hs1)
    exact (hcd.neg).div hcz hζ
  have hcp : ContinuousAt (fun w : ℂ => (x : ℂ) ^ w) s := by
    have heq : (fun w : ℂ => (x : ℂ) ^ w) = fun w : ℂ => Complex.exp ((Real.log x : ℂ) * w) := by
      funext w; exact cpow_eq_exp_log_mul hx w
    rw [heq]; fun_prop
  have hs0 : s ≠ 0 := by intro h; rw [h] at hsRe; simp at hsRe
  have hm : ContinuousAt (fun w : ℂ => (-(deriv riemannZeta w) / riemannZeta w) * (x : ℂ) ^ w) s :=
    hc1.mul hcp
  have htotal : ContinuousAt
      (fun w : ℂ => ((-(deriv riemannZeta w) / riemannZeta w) * (x : ℂ) ^ w) / w) s :=
    hm.div continuousAt_id hs0
  change ContinuousAt (fun w : ℂ => -(deriv riemannZeta w) / riemannZeta w * (x : ℂ) ^ w / w) s
  exact htotal

private lemma psiIntF_integrable_horiz {x r a b : ℝ} (hx : 0 < x) (hr : r ≠ 0)
    (hpos : ∀ u : ℝ, u ∈ Set.uIcc a b → 0 < u)
    (hζ : ∀ u : ℝ, u ∈ Set.uIcc a b → riemannZeta ((u : ℂ) + (r : ℂ) * Complex.I) ≠ 0) :
    IntervalIntegrable (fun u : ℝ => ‖psiIntF x ((u : ℂ) + (r : ℂ) * Complex.I)‖) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.norm
  intro u0 hu0
  have hcφ : ContinuousAt (fun u : ℝ => (u : ℂ) + (r : ℂ) * Complex.I) u0 := by fun_prop
  have hsRe : 0 < ((u0 : ℂ) + (r : ℂ) * Complex.I).re := by simpa using hpos u0 hu0
  have hs1 : (u0 : ℂ) + (r : ℂ) * Complex.I ≠ 1 := by
    intro h
    have him : ((u0 : ℂ) + (r : ℂ) * Complex.I).im = 0 := by rw [h]; simp
    simp at him
    exact hr him
  have hcont := psiIntF_continuousAt_of_zeta_ne_zero hx hsRe hs1 (hζ u0 hu0)
  exact (ContinuousAt.comp (g := psiIntF x)
    (f := fun u : ℝ => (u : ℂ) + (r : ℂ) * Complex.I) hcont hcφ).continuousWithinAt

private lemma psiIntF_integrable_vert {x σ₁ c d : ℝ} (hx : 0 < x) (hσ1pos : 0 < σ₁)
    (hσ1ne : σ₁ ≠ 1)
    (hζ : ∀ t : ℝ, t ∈ Set.uIcc c d → riemannZeta ((σ₁ : ℂ) + (t : ℂ) * Complex.I) ≠ 0) :
    IntervalIntegrable (fun t : ℝ => ‖psiIntF x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖) volume c d := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.norm
  intro t0 ht0
  have hcφ : ContinuousAt (fun t : ℝ => (σ₁ : ℂ) + (t : ℂ) * Complex.I) t0 := by fun_prop
  have hsRe : 0 < ((σ₁ : ℂ) + (t0 : ℂ) * Complex.I).re := by simpa using hσ1pos
  have hs1 : (σ₁ : ℂ) + (t0 : ℂ) * Complex.I ≠ 1 := by
    intro h
    have hre : ((σ₁ : ℂ) + (t0 : ℂ) * Complex.I).re = 1 := by rw [h]; simp
    simp at hre
    exact hσ1ne hre
  have hcont := psiIntF_continuousAt_of_zeta_ne_zero hx hsRe hs1 (hζ t0 ht0)
  exact (ContinuousAt.comp (g := psiIntF x)
    (f := fun t : ℝ => (σ₁ : ℂ) + (t : ℂ) * Complex.I) hcont hcφ).continuousWithinAt

/-! ## The zero-free rectangle -/

private lemma rect_zeta1_ne_zero_engine {x c ε₀ : ℝ} (hx : 3 ≤ x) (hc : 0 < c)
    (hδ : engDelta x c ≤ 1 / 2) (hε : engDelta x c ≤ ε₀)
    (hZF : ∀ t : ℝ, 1 ≤ |t| → ∀ σ : ℝ, 1 - c / Real.log (|t| + 3) ≤ σ →
      riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) ≠ 0)
    (hNA : ∀ (t σ : ℝ), |t| ≤ 4 → 1 - ε₀ ≤ σ → σ ≤ 2 →
      riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) ≠ 0) :
    (Set.uIcc (engSigma x c) (perronRe x) ×ℂ Set.uIcc (-(engT x)) (engT x)) ⊆
      {s : ℂ | (0 : ℝ) < s.re ∧ riemannZeta₁ s ≠ 0} := by
  intro s hs
  rw [Complex.mem_reProdIm] at hs
  obtain ⟨hsre, hsim⟩ := hs
  have hper2 : perronRe x ≤ 2 := perronRe_le_two_of_three hx
  have hσle : engSigma x c ≤ perronRe x := by
    have h1 : engSigma x c ≤ 1 := by
      dsimp [engSigma]
      have hdn : 0 ≤ engDelta x c := engDelta_nonneg hc
      linarith
    have h2 : 1 < perronRe x := perronRe_gt_one (by linarith : 1 < x)
    linarith
  rw [Set.uIcc_of_le hσle] at hsre
  dsimp [engSigma, engDelta] at hsre
  dsimp [engDelta] at hδ hε
  have hTm : -(engT x) ≤ engT x := by linarith [engT_pos x]
  rw [Set.uIcc_of_le hTm] at hsim
  constructor
  · have := hsre.1
    linarith [hδ]
  · by_cases hs1 : s = 1
    · rw [hs1, riemannZeta₁_one]; exact one_ne_zero
    · apply zeta1_ne_zero_of_zeta_ne_zero _ hs1
      have hdecomp : ((s.re : ℂ) + Complex.I * (s.im : ℂ)) = s := by
        rw [mul_comm]; exact Complex.re_add_im s
      have hre2 : s.re ≤ 2 := le_trans hsre.2 hper2
      by_cases hre1 : 1 ≤ s.re
      · rw [← hdecomp]
        exact riemannZeta_ne_zero_of_one_le_re (by simpa using hre1)
      · push Not at hre1
        by_cases him4 : |s.im| ≤ 4
        · rw [← hdecomp]
          exact hNA s.im s.re him4 (by linarith [hsre.1, hε]) hre2
        · push Not at him4
          have him1 : 1 ≤ |s.im| := by linarith
          have hre' : 1 - c / Real.log (|s.im| + 3) ≤ s.re := by
            have hlogT : 0 < Real.log (engT x + 3) := by
              have : (1 : ℝ) < engT x + 3 := by linarith [engT_pos x]
              exact Real.log_pos this
            have hlogim_pos : 0 < Real.log (|s.im| + 3) := by
              have : (1 : ℝ) < |s.im| + 3 := by linarith [abs_nonneg s.im]
              exact Real.log_pos this
            have himle : |s.im| ≤ engT x := abs_le.mpr ⟨hsim.1, hsim.2⟩
            have hlogle : Real.log (|s.im| + 3) ≤ Real.log (engT x + 3) :=
              Real.log_le_log (by linarith [abs_nonneg s.im]) (by linarith)
            have h3 : c / (2 * (Real.log (engT x + 3) + 1)) ≤ c / Real.log (engT x + 3) := by
              rw [div_le_div_iff₀ (by linarith : (0:ℝ) < 2 * (Real.log (engT x + 3) + 1)) hlogT]
              nlinarith
            have h4 : c / Real.log (engT x + 3) ≤ c / Real.log (|s.im| + 3) :=
              div_le_div_of_nonneg_left (le_of_lt hc) hlogim_pos hlogle
            linarith [hsre.1]
          rw [← hdecomp]
          exact hZF s.im him1 s.re hre'

/-! ## Integrability of the edge integrals -/

private lemma engSigma_le_perronRe {x c : ℝ} (hx : 1 < x) (hc : 0 < c) :
    engSigma x c ≤ perronRe x := by
  have h1 : engSigma x c ≤ 1 := by
    dsimp [engSigma]
    linarith [engDelta_nonneg (x := x) hc]
  linarith [perronRe_gt_one hx]

private lemma mem_rect_horiz {x c T u : ℝ} (hu : u ∈ Set.uIcc (engSigma x c) (perronRe x))
    (hT : T ∈ Set.uIcc (-(engT x)) (engT x)) :
    (u : ℂ) + (T : ℂ) * Complex.I ∈
      Set.uIcc (engSigma x c) (perronRe x) ×ℂ Set.uIcc (-(engT x)) (engT x) := by
  rw [Complex.mem_reProdIm]
  exact ⟨by simpa using hu, by simpa using hT⟩

private lemma mem_rect_vert {x c σ t : ℝ} (hσ : σ ∈ Set.uIcc (engSigma x c) (perronRe x))
    (ht : t ∈ Set.uIcc (-(engT x)) (engT x)) :
    (σ : ℂ) + (t : ℂ) * Complex.I ∈
      Set.uIcc (engSigma x c) (perronRe x) ×ℂ Set.uIcc (-(engT x)) (engT x) := by
  rw [Complex.mem_reProdIm]
  exact ⟨by simpa using hσ, by simpa using ht⟩

private lemma engT_mem_uIcc (x : ℝ) : engT x ∈ Set.uIcc (-(engT x)) (engT x) := by
  rw [Set.uIcc_of_le (by linarith [engT_pos x])]
  exact ⟨by linarith [engT_pos x], le_rfl⟩

private lemma neg_engT_mem_uIcc (x : ℝ) : -(engT x) ∈ Set.uIcc (-(engT x)) (engT x) := by
  rw [Set.uIcc_of_le (by linarith [engT_pos x])]
  exact ⟨le_rfl, by linarith [engT_pos x]⟩

private lemma engSigma_mem_uIcc {x c : ℝ} (hx : 1 < x) (hc : 0 < c) :
    engSigma x c ∈ Set.uIcc (engSigma x c) (perronRe x) := by
  rw [Set.uIcc_of_le (engSigma_le_perronRe hx hc)]
  exact ⟨le_rfl, engSigma_le_perronRe hx hc⟩

private lemma engine_edge_integrable {x c : ℝ} (hx : 3 ≤ x) (hc : 0 < c)
    (hδ : engDelta x c < 1)
    (hrect : (Set.uIcc (engSigma x c) (perronRe x) ×ℂ Set.uIcc (-(engT x)) (engT x)) ⊆
      {s : ℂ | (0 : ℝ) < s.re ∧ riemannZeta₁ s ≠ 0}) :
    IntervalIntegrable (fun u : ℝ => ‖psiIntF x ((u : ℂ) + (engT x : ℂ) * Complex.I)‖)
        volume (engSigma x c) (perronRe x) ∧
    IntervalIntegrable (fun u : ℝ => ‖psiIntF x ((u : ℂ) + (((-engT x : ℝ) : ℂ)) * Complex.I)‖)
        volume (engSigma x c) (perronRe x) ∧
    IntervalIntegrable (fun t : ℝ => ‖psiIntF x ((engSigma x c : ℂ) + (t : ℂ) * Complex.I)‖)
        volume (-(engT x)) (engT x) := by
  have hxpos : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hσpos : 0 < engSigma x c := by
    dsimp [engSigma]; linarith
  have hσne : engSigma x c ≠ 1 := by
    dsimp [engSigma]; linarith [engDelta_pos (x := x) hc]
  have hTnz : engT x ≠ 0 := ne_of_gt (engT_pos x)
  have hneghTnz : -engT x ≠ 0 := neg_ne_zero.mpr hTnz
  -- zeta nonzero helper
  have hζ : ∀ (σ : ℝ) (t : ℝ), σ ∈ Set.uIcc (engSigma x c) (perronRe x) →
      t ∈ Set.uIcc (-(engT x)) (engT x) →
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro σ t hσ ht
    have hmem := mem_rect_vert hσ ht
    have h1' : riemannZeta₁ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := (hrect hmem).2
    by_cases hs1 : ((σ : ℂ) + (t : ℂ) * Complex.I) = 1
    · rw [hs1]; exact riemannZeta_one_ne_zero
    · exact zeta_ne_zero_of_zeta1_ne_zero h1' hs1
  refine ⟨?_, ?_, ?_⟩
  · refine psiIntF_integrable_horiz hxpos hTnz ?_ ?_
    · intro u hu
      have hmem := mem_rect_horiz hu (engT_mem_uIcc x)
      have := (hrect hmem).1
      simpa using this
    · intro u hu
      exact hζ u (engT x) hu (engT_mem_uIcc x)
  · refine psiIntF_integrable_horiz hxpos hneghTnz ?_ ?_
    · intro u hu
      have hmem := mem_rect_horiz hu (neg_engT_mem_uIcc x)
      have := (hrect hmem).1
      simpa using this
    · intro u hu
      exact hζ u (-engT x) hu (neg_engT_mem_uIcc x)
  · refine psiIntF_integrable_vert hxpos hσpos hσne ?_
    intro t ht
    exact hζ (engSigma x c) t (engSigma_mem_uIcc hx1 hc) ht

/-! ## M1/M2 data in engine shape -/

private lemma hM2_datum {C₂ δ₂ : ℝ}
    (hM2 : ∀ (t σ : ℝ), |t| ≤ 2 → σ ≠ 1 → (1 - δ₂) ≤ σ → σ ≤ 2 →
      ‖(deriv riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)))) /
          riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)))‖ ≤
        C₂ + 1 / ‖(((σ : ℂ) + Complex.I * (t : ℂ))) - 1‖) :
    ∀ (t σ : ℝ), |t| ≤ 2 → σ ≠ 1 → (1 - δ₂) ≤ σ → σ ≤ 2 →
      logDerivZ (((σ : ℂ) + (t : ℂ) * Complex.I)) ≤
        C₂ + 1 / ‖(((σ : ℂ) + (t : ℂ) * Complex.I)) - 1‖ := by
  intro t σ ht hs hlo hhi
  have h := hM2 t σ ht hs hlo hhi
  have harg : ((σ : ℂ) + (t : ℂ) * Complex.I) = ((σ : ℂ) + Complex.I * (t : ℂ)) := by ring
  rw [harg]
  simpa [logDerivZ] using h

private lemma hM1_datum {c₁ C₁ : ℝ} (hc₁ : 0 < c₁) (hC₁ : 0 ≤ C₁)
    (hLD : ∀ t : ℝ, 1 ≤ |t| → ∀ σ : ℝ, 1 - c₁ / Real.log (|t| + 3) ≤ σ → σ ≤ 2 →
      ‖(deriv riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)))) /
          riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)))‖ ≤
        C₁ * (Real.log (|t| + 3) + 1) ^ 4) :
    ∀ t : ℝ, 1 ≤ |t| → ∀ σ : ℝ, 1 - c₁ / (Real.log (|t| + 3) + 1) ≤ σ → σ ≤ 2 →
      logDerivZ (((σ : ℂ) + (t : ℂ) * Complex.I)) ≤ C₁ * (Real.log (|t| + 3) + 1) ^ 5 := by
  intro t ht σ hσ hσ2
  have hLpos : 0 < Real.log (|t| + 3) := Real.log_pos (by linarith [abs_nonneg t])
  have hσ' : 1 - c₁ / Real.log (|t| + 3) ≤ σ := by
    have hle : c₁ / (Real.log (|t| + 3) + 1) ≤ c₁ / Real.log (|t| + 3) := by
      rw [div_le_div_iff₀ (by linarith : (0:ℝ) < Real.log (|t| + 3) + 1) hLpos]
      nlinarith
    linarith
  have h := hLD t ht σ hσ' hσ2
  have hpow : (Real.log (|t| + 3) + 1) ^ 4 ≤ (Real.log (|t| + 3) + 1) ^ 5 := by
    have h1 : (1 : ℝ) ≤ Real.log (|t| + 3) + 1 := by linarith
    calc (Real.log (|t| + 3) + 1) ^ 4 = (Real.log (|t| + 3) + 1) ^ 4 * 1 := by ring
      _ ≤ (Real.log (|t| + 3) + 1) ^ 4 * (Real.log (|t| + 3) + 1) :=
          mul_le_mul_of_nonneg_left h1 (pow_nonneg (by linarith) 4)
      _ = (Real.log (|t| + 3) + 1) ^ 5 := by ring
  have harg : ((σ : ℂ) + (t : ℂ) * Complex.I) = ((σ : ℂ) + Complex.I * (t : ℂ)) := by ring
  rw [harg, logDerivZ]
  exact le_trans h (mul_le_mul_of_nonneg_left hpow hC₁)

/-! ## Elementary transcription lemmas for the exponential bound -/

private lemma rpow_perronRe_eq {x : ℝ} (hx : 0 < x) (hL : Real.log x ≠ 0) :
    x ^ perronRe x = x * Real.exp 1 := by
  rw [Real.rpow_def_of_pos hx]
  have h : Real.log x * perronRe x = Real.log x + 1 := by
    dsimp [perronRe]
    rw [mul_add, mul_one, mul_one_div, div_self hL]
  rw [h, Real.exp_add, Real.exp_log hx]

private lemma rpow_engSigma_eq {x c : ℝ} (hx : 0 < x) :
    x ^ (engSigma x c) = x * Real.exp (-(engDelta x c * Real.log x)) := by
  have he : engSigma x c = 1 - engDelta x c := rfl
  rw [he, Real.rpow_sub hx, Real.rpow_one, Real.rpow_def_of_pos hx]
  have harg : Real.log x * engDelta x c = engDelta x c * Real.log x := by ring
  rw [harg, div_eq_mul_inv, ← Real.exp_neg]

private lemma engM_pow5_le {x : ℝ} (hL1 : 1 ≤ Real.log x)
    (hM3 : Real.log (engT x + 3) + 1 ≤ 3 * Real.sqrt (Real.log x)) :
    (Real.log (engT x + 3) + 1) ^ 5 ≤ 243 * (Real.log x) ^ 3 := by
  have hLpos : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hL1
  have hMnn : 0 ≤ Real.log (engT x + 3) + 1 := le_of_lt (engM_pos x)
  have h1 : (Real.log (engT x + 3) + 1) ^ 5 ≤ (3 * Real.sqrt (Real.log x)) ^ 5 :=
    pow_le_pow_left₀ hMnn hM3 5
  have h2 : (3 * Real.sqrt (Real.log x)) ^ 5 = 243 * (Real.sqrt (Real.log x)) ^ 5 := by ring
  have hs := Real.sq_sqrt (le_of_lt hLpos)
  have hs1 : 1 ≤ Real.sqrt (Real.log x) := Real.one_le_sqrt.mpr hL1
  have hsle : Real.sqrt (Real.log x) ≤ Real.log x := by nlinarith
  have h3 : (Real.sqrt (Real.log x)) ^ 5 ≤ (Real.log x) ^ 3 := by
    have h4 : (Real.sqrt (Real.log x)) ^ 5
        = (Real.sqrt (Real.log x)) ^ 2 * ((Real.sqrt (Real.log x)) ^ 2 * Real.sqrt (Real.log x)) := by
      ring
    calc (Real.sqrt (Real.log x)) ^ 5
        = Real.log x * (Real.log x * Real.sqrt (Real.log x)) := by rw [h4, hs]
      _ ≤ Real.log x * (Real.log x * Real.log x) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsle (le_of_lt hLpos)) (le_of_lt hLpos)
      _ = (Real.log x) ^ 3 := by ring
  calc (Real.log (engT x + 3) + 1) ^ 5 ≤ (3 * Real.sqrt (Real.log x)) ^ 5 := h1
    _ = 243 * (Real.sqrt (Real.log x)) ^ 5 := h2
    _ ≤ 243 * (Real.log x) ^ 3 := mul_le_mul_of_nonneg_left h3 (by norm_num)

private lemma engDelta_mul_log_ge {x c : ℝ} (hc : 0 < c) (hL1 : 1 ≤ Real.log x)
    (hM3 : Real.log (engT x + 3) + 1 ≤ 3 * Real.sqrt (Real.log x)) :
    (c / 6) * Real.sqrt (Real.log x) ≤ engDelta x c * Real.log x := by
  have hLpos : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hL1
  have hsqLpos : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.mpr hLpos
  have hMpos : 0 < Real.log (engT x + 3) + 1 := engM_pos x
  have hsqL2 : Real.sqrt (Real.log x) ^ 2 = Real.log x := Real.sq_sqrt (le_of_lt hLpos)
  have hδeq : engDelta x c = c / (2 * (Real.log (engT x + 3) + 1)) := rfl
  have hsqL2' : Real.log x = Real.sqrt (Real.log x) ^ 2 := hsqL2.symm
  rw [hδeq]
  conv_rhs => rw [hsqL2']
  rw [show c / (2 * (Real.log (engT x + 3) + 1)) * Real.sqrt (Real.log x) ^ 2
      = c * Real.sqrt (Real.log x) ^ 2 / (2 * (Real.log (engT x + 3) + 1)) by ring]
  rw [le_div_iff₀ (by linarith : (0:ℝ) < 2 * (Real.log (engT x + 3) + 1))]
  have hnn : 0 ≤ (c / 3) * Real.sqrt (Real.log x) :=
    mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hprod : (c / 3) * Real.sqrt (Real.log x) * (Real.log (engT x + 3) + 1)
      ≤ (c / 3) * Real.sqrt (Real.log x) * (3 * Real.sqrt (Real.log x)) :=
    mul_le_mul_of_nonneg_left hM3 hnn
  nlinarith [hprod, hsqLpos]

private lemma engDelta_inv_le {x c : ℝ} (hc : 0 < c)
    (hM3 : Real.log (engT x + 3) + 1 ≤ 3 * Real.sqrt (Real.log x)) :
    1 / (1 - engSigma x c) ≤ 6 * Real.sqrt (Real.log x) / c := by
  have h1 : 1 - engSigma x c = engDelta x c := by dsimp [engSigma]; ring
  rw [h1]
  have hδeq : engDelta x c = c / (2 * (Real.log (engT x + 3) + 1)) := rfl
  rw [hδeq, one_div, inv_div]
  apply div_le_div_of_nonneg_right _ (le_of_lt hc)
  linarith [hM3]

private lemma log_engT_div_two_le (x : ℝ) :
    Real.log (engT x / 2) ≤ Real.sqrt (Real.log x) := by
  have hTpos : 0 < engT x := engT_pos x
  have h1 : Real.log (engT x / 2) ≤ Real.log (engT x) :=
    Real.log_le_log (by linarith) (by linarith)
  rw [engT, Real.log_exp] at h1
  exact h1

private lemma engSigma_ge_half {x c : ℝ} (hδh : engDelta x c ≤ 1 / 2) :
    1 / 2 ≤ engSigma x c := by
  dsimp [engSigma]
  linarith

private lemma perronRe_sub_engSigma_le_two {x c : ℝ} (hL1 : 1 ≤ Real.log x)
    (hδh : engDelta x c ≤ 1 / 2) :
    perronRe x - engSigma x c ≤ 2 := by
  have hLpos : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hL1
  have hd : 1 / Real.log x ≤ 1 := (div_le_one hLpos).2 hL1
  dsimp [perronRe, engSigma]
  linarith

/-! ## Eventual size facts -/

private lemma engT_tendsto_atTop : Tendsto (fun x : ℝ => engT x) atTop atTop :=
  Real.tendsto_exp_atTop.comp (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)

private lemma engT_eventually_ge (B : ℝ) : ∀ᶠ x : ℝ in atTop, B ≤ engT x :=
  engT_tendsto_atTop.eventually (eventually_ge_atTop B)

private lemma engDelta_eventually_le {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    ∀ᶠ x : ℝ in atTop, engDelta x c ≤ d := by
  filter_upwards [engT_eventually_ge (Real.exp (c / (2 * d)) + 3)] with x hx
  have h1 : Real.exp (c / (2 * d)) ≤ engT x + 3 := by linarith
  have h2 : c / (2 * d) ≤ Real.log (engT x + 3) :=
    (Real.le_log_iff_exp_le (by linarith [engT_pos x])).2 h1
  have hM : 0 < Real.log (engT x + 3) + 1 := engM_pos x
  have h3 : c ≤ Real.log (engT x + 3) * (2 * d) := by
    have h4 := mul_le_mul_of_nonneg_right h2 (by linarith : (0:ℝ) ≤ 2 * d)
    rwa [div_mul_cancel₀ _ (by positivity : (2:ℝ) * d ≠ 0)] at h4
  rw [engDelta]
  rw [div_le_iff₀ (by linarith : (0:ℝ) < 2 * (Real.log (engT x + 3) + 1))]
  nlinarith [h3, hM]

private lemma engM_eventually_le :
    ∀ᶠ x : ℝ in atTop, Real.log (engT x + 3) + 1 ≤ 3 * Real.sqrt (Real.log x) := by
  filter_upwards [engT_eventually_ge 3, Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hT3 hL1
  have hsq1 : 1 ≤ Real.sqrt (Real.log x) := Real.one_le_sqrt.mpr hL1
  have hlog2 : Real.log 2 ≤ Real.sqrt (Real.log x) := by
    have h : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
    linarith
  have hTpos : 0 < engT x := engT_pos x
  have h1 : Real.log (engT x + 3) ≤ Real.log (engT x * 2) :=
    Real.log_le_log (by linarith) (by linarith)
  rw [Real.log_mul (ne_of_gt hTpos) (by norm_num : (2:ℝ) ≠ 0)] at h1
  have h2 : Real.log (engT x) = Real.sqrt (Real.log x) := by rw [engT, Real.log_exp]
  rw [h2] at h1
  linarith

/-! ## The perronEdgeSum bound -/

private lemma perronEdgeSum_eventually_le {c₁ C₁ C₂ cf : ℝ} (hc₁ : 0 < c₁) (hC₁ : 0 ≤ C₁)
    (hC₂ : 0 ≤ C₂) (hcf : 0 < cf) (hcf1 : cf ≤ c₁ / 12) (hcf2 : cf ≤ 1 / 2) :
    ∀ᶠ x : ℝ in atTop,
      perronEdgeSum x (engT x) (engSigma x c₁) C₁ C₂ ≤
        5 * x * Real.exp (-cf * Real.sqrt (Real.log x)) := by
  have hx3 : ∀ᶠ x : ℝ in atTop, 3 ≤ x := eventually_ge_atTop 3
  have hL1 : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x := Real.tendsto_log_atTop.eventually_ge_atTop 1
  have hT2 : ∀ᶠ x : ℝ in atTop, 2 ≤ engT x := engT_eventually_ge 2
  have hδh : ∀ᶠ x : ℝ in atTop, engDelta x c₁ ≤ 1 / 2 :=
    engDelta_eventually_le hc₁ (by norm_num)
  have hP1 : ∀ᶠ x : ℝ in atTop,
      486 * Real.exp 1 * C₁ * (Real.log x) ^ 3 * Real.exp (-Real.sqrt (Real.log x)) ≤
        Real.exp (-(1 / 2) * Real.sqrt (Real.log x)) := by
    have h := Commons.Analysis.Asymptotics.poly_mul_exp_neg_sqrtLog_le 1 one_pos 3
      (486 * Real.exp 1 * C₁) (by positivity)
    filter_upwards [h] with x hx
    simpa using hx
  have hP2 : ∀ᶠ x : ℝ in atTop,
      243 * C₁ * (Real.log x) ^ 4 * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x)) ≤
        Real.exp (-(c₁ / 12) * Real.sqrt (Real.log x)) := by
    have h := Commons.Analysis.Asymptotics.poly_mul_exp_neg_sqrtLog_le (c₁ / 6) (by positivity) 4
      (243 * C₁) (by positivity)
    filter_upwards [h] with x hx
    have hx' : 243 * C₁ * (Real.log x) ^ 4 * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x)) ≤
        Real.exp (-((c₁ / 6) / 2) * Real.sqrt (Real.log x)) := by simpa using hx
    have heq : (c₁ / 6) / 2 = c₁ / 12 := by ring
    rw [heq] at hx'
    exact hx'
  have hP3 : ∀ᶠ x : ℝ in atTop,
      16 * (C₂ + 6 / c₁ + 1) * (Real.log x) * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x)) ≤
        Real.exp (-(c₁ / 12) * Real.sqrt (Real.log x)) := by
    have h := Commons.Analysis.Asymptotics.poly_mul_exp_neg_sqrtLog_le (c₁ / 6) (by positivity) 1
      (16 * (C₂ + 6 / c₁ + 1)) (by positivity)
    filter_upwards [h] with x hx
    have hx' : 16 * (C₂ + 6 / c₁ + 1) * (Real.log x) ^ 1 *
        Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x)) ≤
        Real.exp (-((c₁ / 6) / 2) * Real.sqrt (Real.log x)) := by simpa using hx
    have heq : (c₁ / 6) / 2 = c₁ / 12 := by ring
    rw [heq] at hx'
    simpa using hx'
  filter_upwards [hx3, hL1, hT2, engM_eventually_le, hδh, hP1, hP2, hP3]
    with x hx3 hL1 hT2 hM3 hδh hP1 hP2 hP3
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hL1
  have hLnn : 0 ≤ Real.log x := le_of_lt hLpos
  have hsqLnn : 0 ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
  have hTinv : (engT x)⁻¹ = Real.exp (-Real.sqrt (Real.log x)) := by rw [engT, ← Real.exp_neg]
  have hrpow1 : x ^ perronRe x = x * Real.exp 1 := rpow_perronRe_eq hxpos (ne_of_gt hLpos)
  have hrpowsig := rpow_engSigma_eq (x := x) (c := c₁) hxpos
  have hM5 := engM_pow5_le hL1 hM3
  have hδmul := engDelta_mul_log_ge hc₁ hL1 hM3
  have hδinv := engDelta_inv_le hc₁ hM3
  have hlogT2 := log_engT_div_two_le x
  have hσhalf := engSigma_ge_half (x := x) (c := c₁) hδh
  have hσpos : 0 < engSigma x c₁ := by linarith
  have hdiff := perronRe_sub_engSigma_le_two hL1 hδh
  have hδle : Real.exp (-(engDelta x c₁ * Real.log x)) ≤
      Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x)) :=
    Real.exp_le_exp.mpr (by linarith [hδmul])
  have hexp12 : Real.exp (-(c₁ / 12) * Real.sqrt (Real.log x)) ≤
      Real.exp (-cf * Real.sqrt (Real.log x)) :=
    Real.exp_le_exp.mpr (by nlinarith [hcf1, hsqLnn])
  have hexp2 : Real.exp (-(1 / 2) * Real.sqrt (Real.log x)) ≤
      Real.exp (-cf * Real.sqrt (Real.log x)) :=
    Real.exp_le_exp.mpr (by nlinarith [hcf2, hsqLnn])
  have hMnn : 0 ≤ Real.log (engT x + 3) + 1 := le_of_lt (engM_pos x)
  have hxe : 0 ≤ x * Real.exp 1 := mul_nonneg (le_of_lt hxpos) (le_of_lt (Real.exp_pos 1))
  have hdiffnn : 0 ≤ perronRe x - engSigma x c₁ := by
    have h1 : engSigma x c₁ ≤ 1 := by dsimp [engSigma]; linarith [engDelta_nonneg (x := x) hc₁]
    linarith [perronRe_gt_one (by linarith : 1 < x)]
  have hK : C₂ + 6 * Real.sqrt (Real.log x) / c₁ ≤ 2 * (C₂ + 6 / c₁ + 1) * Real.log x := by
    have h1 : 6 * Real.sqrt (Real.log x) / c₁ = (6 / c₁) * Real.sqrt (Real.log x) := by ring
    rw [h1]
    have h4 : Real.sqrt (Real.log x) ≤ Real.log x := by
      nlinarith [Real.sq_sqrt (le_of_lt hLpos), Real.one_le_sqrt.mpr hL1]
    have hKnn : 0 ≤ C₂ + 6 / c₁ + 1 := by
      have h0 : 0 ≤ 6 / c₁ := div_nonneg (by norm_num) (le_of_lt hc₁)
      linarith
    have h2 : (6 / c₁) * Real.sqrt (Real.log x) ≤ (C₂ + 6 / c₁ + 1) * Real.log x := by
      have h3 : 6 / c₁ ≤ C₂ + 6 / c₁ + 1 := by linarith [hC₂]
      calc (6 / c₁) * Real.sqrt (Real.log x) ≤ (C₂ + 6 / c₁ + 1) * Real.sqrt (Real.log x) :=
            mul_le_mul_of_nonneg_right h3 hsqLnn
        _ ≤ (C₂ + 6 / c₁ + 1) * Real.log x := mul_le_mul_of_nonneg_left h4 hKnn
    have h5 : C₂ ≤ (C₂ + 6 / c₁ + 1) * Real.log x := by
      have h6 : C₂ ≤ C₂ + 6 / c₁ + 1 := by
        have h0 : 0 ≤ 6 / c₁ := div_nonneg (by norm_num) (le_of_lt hc₁)
        linarith
      calc C₂ = C₂ * 1 := by ring
        _ ≤ (C₂ + 6 / c₁ + 1) * 1 := mul_le_mul_of_nonneg_right h6 (by norm_num)
        _ ≤ (C₂ + 6 / c₁ + 1) * Real.log x := mul_le_mul_of_nonneg_left hL1 hKnn
    linarith
  have hA : C₁ * (Real.log (engT x + 3) + 1) ^ 5 * x ^ perronRe x *
        (perronRe x - engSigma x c₁) / engT x
      ≤ x * Real.exp (-cf * Real.sqrt (Real.log x)) := by
    have hnum : C₁ * (Real.log (engT x + 3) + 1) ^ 5 * x ^ perronRe x *
        (perronRe x - engSigma x c₁) ≤ C₁ * (243 * (Real.log x) ^ 3) * (x * Real.exp 1) * 2 := by
      rw [hrpow1]
      have hb1 : C₁ * (Real.log (engT x + 3) + 1) ^ 5 * (x * Real.exp 1) ≤
          C₁ * (243 * (Real.log x) ^ 3) * (x * Real.exp 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM5 hC₁) hxe
      exact mul_le_mul hb1 hdiff hdiffnn
        (mul_nonneg (mul_nonneg hC₁ (mul_nonneg (by norm_num) (pow_nonneg hLnn 3))) hxe)
    have h1 : C₁ * (Real.log (engT x + 3) + 1) ^ 5 * x ^ perronRe x *
        (perronRe x - engSigma x c₁) / engT x
        ≤ (C₁ * (243 * (Real.log x) ^ 3) * (x * Real.exp 1) * 2) / engT x :=
      div_le_div_of_nonneg_right hnum (le_of_lt (engT_pos x))
    have h2 : (C₁ * (243 * (Real.log x) ^ 3) * (x * Real.exp 1) * 2) / engT x
        = x * (486 * Real.exp 1 * C₁ * (Real.log x) ^ 3 *
            Real.exp (-Real.sqrt (Real.log x))) := by
      rw [div_eq_mul_inv, hTinv]; ring
    rw [h2] at h1
    have hP1' : 486 * Real.exp 1 * C₁ * (Real.log x) ^ 3 * Real.exp (-Real.sqrt (Real.log x))
        ≤ Real.exp (-cf * Real.sqrt (Real.log x)) := le_trans hP1 hexp2
    exact le_trans h1 (mul_le_mul_of_nonneg_left hP1' (le_of_lt hxpos))
  have hB : 4 * (C₂ + 1 / (1 - engSigma x c₁)) * x ^ (engSigma x c₁) / engSigma x c₁
      ≤ x * Real.exp (-cf * Real.sqrt (Real.log x)) := by
    have hnum : 4 * (C₂ + 1 / (1 - engSigma x c₁)) * x ^ (engSigma x c₁)
        ≤ 4 * (C₂ + 6 * Real.sqrt (Real.log x) / c₁) *
            (x * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x))) := by
      rw [hrpowsig]
      have hsum : C₂ + 1 / (1 - engSigma x c₁) ≤ C₂ + 6 * Real.sqrt (Real.log x) / c₁ := by
        linarith [hδinv]
      have h1 : 4 * (C₂ + 1 / (1 - engSigma x c₁)) ≤
          4 * (C₂ + 6 * Real.sqrt (Real.log x) / c₁) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
      have h2 : x * Real.exp (-(engDelta x c₁ * Real.log x)) ≤
          x * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x)) :=
        mul_le_mul_of_nonneg_left hδle (le_of_lt hxpos)
      exact mul_le_mul h1 h2 (by positivity) (by positivity)
    have hdiv : 4 * (C₂ + 1 / (1 - engSigma x c₁)) * x ^ (engSigma x c₁) / engSigma x c₁
        ≤ 8 * (C₂ + 6 * Real.sqrt (Real.log x) / c₁) *
            (x * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x))) := by
      have h1 := div_le_div_of_nonneg_right hnum (le_of_lt hσpos)
      have h2 : 4 * (C₂ + 6 * Real.sqrt (Real.log x) / c₁) *
            (x * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x))) / engSigma x c₁
          = 4 * (C₂ + 6 * Real.sqrt (Real.log x) / c₁) *
            (x * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x))) * (1 / engSigma x c₁) := by
        rw [div_eq_mul_inv, one_div]
      rw [h2] at h1
      refine le_trans h1 ?_
      have hinv : 1 / engSigma x c₁ ≤ 2 := by rw [div_le_iff₀ hσpos]; linarith [hσhalf]
      have h3 := mul_le_mul_of_nonneg_left hinv (by positivity : (0:ℝ) ≤ 4 *
        (C₂ + 6 * Real.sqrt (Real.log x) / c₁) *
        (x * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x))))
      linarith [h3]
    have h16 : 8 * (C₂ + 6 * Real.sqrt (Real.log x) / c₁) ≤
        16 * (C₂ + 6 / c₁ + 1) * (Real.log x) := by
      have hh := mul_le_mul_of_nonneg_left hK (by norm_num : (0:ℝ) ≤ 8)
      linarith [hh]
    have hfin : 8 * (C₂ + 6 * Real.sqrt (Real.log x) / c₁) *
          (x * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x)))
        ≤ x * Real.exp (-cf * Real.sqrt (Real.log x)) := by
      have h1 : 8 * (C₂ + 6 * Real.sqrt (Real.log x) / c₁) *
            (x * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x)))
          ≤ 16 * (C₂ + 6 / c₁ + 1) * (Real.log x) *
            (x * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x))) :=
        mul_le_mul_of_nonneg_right h16 (by positivity)
      refine le_trans h1 ?_
      rw [show 16 * (C₂ + 6 / c₁ + 1) * (Real.log x) *
            (x * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x)))
          = x * (16 * (C₂ + 6 / c₁ + 1) * (Real.log x) *
            Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x))) by ring]
      exact mul_le_mul_of_nonneg_left (le_trans hP3 hexp12) (le_of_lt hxpos)
    linarith
  have hC : C₁ * x ^ (engSigma x c₁) * (Real.log (engT x + 3) + 1) ^ 5 *
        Real.log (engT x / 2)
      ≤ x * Real.exp (-cf * Real.sqrt (Real.log x)) := by
    rw [hrpowsig]
    have hnum : C₁ * (x * Real.exp (-(engDelta x c₁ * Real.log x))) *
        (Real.log (engT x + 3) + 1) ^ 5 * Real.log (engT x / 2)
        ≤ C₁ * (x * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x))) *
            (243 * (Real.log x) ^ 3) * Real.sqrt (Real.log x) := by
      have hY : C₁ * (x * Real.exp (-(engDelta x c₁ * Real.log x))) ≤
          C₁ * (x * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hδle (le_of_lt hxpos)) hC₁
      have hLognn : 0 ≤ Real.log (engT x / 2) := Real.log_nonneg (by linarith : (1:ℝ) ≤ engT x / 2)
      have hX'nn : 0 ≤ C₁ * (x * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x))) :=
        mul_nonneg hC₁ (mul_nonneg (le_of_lt hxpos) (le_of_lt (Real.exp_pos _)))
      exact mul_le_mul (mul_le_mul hY hM5 (pow_nonneg hMnn 5) hX'nn) hlogT2 hLognn
        (mul_nonneg hX'nn (mul_nonneg (by norm_num) (pow_nonneg hLnn 3)))
    have h3 : Real.sqrt (Real.log x) ≤ Real.log x := by
      nlinarith [Real.sq_sqrt (le_of_lt hLpos), Real.one_le_sqrt.mpr hL1]
    have hmid : C₁ * (x * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x))) *
        (243 * (Real.log x) ^ 3) * Real.sqrt (Real.log x)
        ≤ x * (243 * C₁ * (Real.log x) ^ 4 *
            Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x))) := by
      have h4 : (Real.log x) ^ 3 * Real.sqrt (Real.log x) ≤ (Real.log x) ^ 4 := by
        calc (Real.log x) ^ 3 * Real.sqrt (Real.log x) ≤ (Real.log x) ^ 3 * Real.log x :=
              mul_le_mul_of_nonneg_left h3 (pow_nonneg hLnn 3)
          _ = (Real.log x) ^ 4 := by ring
      have hnn : 0 ≤ C₁ * (x * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x))) * 243 :=
        mul_nonneg (mul_nonneg hC₁ (mul_nonneg (le_of_lt hxpos) (le_of_lt (Real.exp_pos _))))
          (by norm_num)
      have h5 := mul_le_mul_of_nonneg_left h4 hnn
      calc C₁ * (x * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x))) *
            (243 * (Real.log x) ^ 3) * Real.sqrt (Real.log x)
          = (C₁ * (x * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x))) * 243) *
              ((Real.log x) ^ 3 * Real.sqrt (Real.log x)) := by ring
        _ ≤ (C₁ * (x * Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x))) * 243) *
              (Real.log x) ^ 4 := h5
        _ = x * (243 * C₁ * (Real.log x) ^ 4 *
              Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x))) := by ring
    have h6 : x * (243 * C₁ * (Real.log x) ^ 4 *
          Real.exp (-(c₁ / 6) * Real.sqrt (Real.log x)))
        ≤ x * Real.exp (-cf * Real.sqrt (Real.log x)) :=
      mul_le_mul_of_nonneg_left (le_trans hP2 hexp12) (le_of_lt hxpos)
    linarith
  rw [perronEdgeSum]
  linarith

/-! ## const_mul_log absorption -/

private lemma const_mul_log_le_mul_exp_neg_sqrtLog (a : ℝ) (ha : 0 < a) (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ x : ℝ in atTop,
      C * Real.log x ≤ x * Real.exp (-a * Real.sqrt (Real.log x)) := by
  rcases eq_or_lt_of_le hC with hC0 | hCpos
  · rw [← hC0]
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
    simp only [zero_mul]
    exact mul_nonneg (le_of_lt hxpos) (le_of_lt (Real.exp_pos _))
  · set b₀ : ℝ := max 1 (max (2 * a) (max 8 (2 * Real.sqrt (2 * max (Real.log C) 0)))) with hb₀def
    have hb₀ge1 : 1 ≤ b₀ := by
      rw [hb₀def]; exact le_max_left 1 (max (2 * a) (max 8 (2 * Real.sqrt (2 * max (Real.log C) 0))))
    have hb₀ge2a : 2 * a ≤ b₀ := by
      rw [hb₀def]
      exact le_trans (le_max_left (2 * a) (max 8 (2 * Real.sqrt (2 * max (Real.log C) 0))))
        (le_max_right 1 (max (2 * a) (max 8 (2 * Real.sqrt (2 * max (Real.log C) 0)))))
    have hb₀pos : 0 < b₀ := lt_of_lt_of_le zero_lt_one hb₀ge1
    refine Filter.eventually_atTop.2 ⟨Real.exp (b₀ ^ 2), ?_⟩
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
    have hLge : b₀ ^ 2 ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).2 hx
    have hLnonneg : 0 ≤ Real.log x := le_trans (sq_nonneg b₀) hLge
    set b : ℝ := Real.sqrt (Real.log x) with hbdef
    have hbsq : b ^ 2 = Real.log x := Real.sq_sqrt hLnonneg
    have hbnonneg : 0 ≤ b := Real.sqrt_nonneg _
    have hbge : b₀ ≤ b := by
      rw [hbdef, ← Real.sqrt_sq (le_of_lt hb₀pos)]
      exact Real.sqrt_le_sqrt hLge
    have hbge1 : 1 ≤ b := le_trans hb₀ge1 hbge
    have hbge2a : 2 * a ≤ b := le_trans hb₀ge2a hbge
    have hbge8 : 8 ≤ b := by
      have h8 : 8 ≤ b₀ := by
        rw [hb₀def]
        exact le_trans (le_trans (le_max_left 8 (2 * Real.sqrt (2 * max (Real.log C) 0)))
            (le_max_right (2 * a) (max 8 (2 * Real.sqrt (2 * max (Real.log C) 0)))))
          (le_max_right 1 (max (2 * a) (max 8 (2 * Real.sqrt (2 * max (Real.log C) 0)))))
      linarith
    have hbgeT : 2 * Real.sqrt (2 * max (Real.log C) 0) ≤ b := by
      have h8 : 2 * Real.sqrt (2 * max (Real.log C) 0) ≤ b₀ := by
        rw [hb₀def]
        exact le_trans (le_trans (le_max_right 8 (2 * Real.sqrt (2 * max (Real.log C) 0)))
            (le_max_right (2 * a) (max 8 (2 * Real.sqrt (2 * max (Real.log C) 0)))))
          (le_max_right 1 (max (2 * a) (max 8 (2 * Real.sqrt (2 * max (Real.log C) 0)))))
      linarith
    have hbpos : 0 < b := lt_of_lt_of_le zero_lt_one hbge1
    have hlogC : Real.log C ≤ b ^ 2 / 8 := by
      have hs : Real.sqrt (2 * max (Real.log C) 0) ≤ b / 2 := by linarith
      have hTnn : (0:ℝ) ≤ 2 * max (Real.log C) 0 := by
        have : (0:ℝ) ≤ max (Real.log C) 0 := le_max_right _ _
        linarith
      have hsq : 2 * max (Real.log C) 0 ≤ (b / 2) ^ 2 := by
        have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
        rwa [Real.sq_sqrt hTnn] at h
      have hmax : max (Real.log C) 0 ≤ b ^ 2 / 8 := by nlinarith
      exact le_trans (le_max_left _ _) hmax
    have hlogb : 2 * Real.log b ≤ 3 * b ^ 2 / 8 := by
      have h1 : Real.log b ≤ b := Real.log_le_self (le_of_lt hbpos)
      have h2 : b ≤ 3 * b ^ 2 / 16 := by nlinarith
      linarith
    have hkey : C * b ^ 2 * Real.exp (a * b) ≤ Real.exp (b ^ 2) := by
      have hb2pos : 0 < b ^ 2 := pow_pos hbpos 2
      have expand : C * b ^ 2 ≤ Real.exp (b ^ 2 / 2) := by
        rw [← Real.log_le_log_iff (mul_pos hCpos hb2pos) (Real.exp_pos _), Real.log_exp,
          Real.log_mul (ne_of_gt hCpos) (ne_of_gt hb2pos), Real.log_pow]
        push_cast
        linarith
      have expab : Real.exp (a * b) ≤ Real.exp (b ^ 2 / 2) := by
        apply Real.exp_le_exp.mpr; nlinarith [hbge2a]
      calc C * b ^ 2 * Real.exp (a * b) = (C * b ^ 2) * Real.exp (a * b) := by ring
        _ ≤ Real.exp (b ^ 2 / 2) * Real.exp (b ^ 2 / 2) :=
            mul_le_mul expand expab (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _))
        _ = Real.exp (b ^ 2) := by rw [← Real.exp_add]; ring_nf
    have hfinal : C * Real.log x * Real.exp (a * Real.sqrt (Real.log x)) ≤ x := by
      calc C * Real.log x * Real.exp (a * Real.sqrt (Real.log x))
          = C * b ^ 2 * Real.exp (a * b) := by
            rw [show Real.sqrt (Real.log x) = b from hbdef.symm, ← hbsq]
        _ ≤ Real.exp (b ^ 2) := hkey
        _ = x := by rw [hbsq]; exact Real.exp_log hxpos
    have hexpneg : x * Real.exp (-a * Real.sqrt (Real.log x)) =
        x / Real.exp (a * Real.sqrt (Real.log x)) := by
      rw [show -a * Real.sqrt (Real.log x) = -(a * Real.sqrt (Real.log x)) by ring,
        Real.exp_neg, div_eq_mul_inv]
    rw [hexpneg, le_div_iff₀ (Real.exp_pos _)]
    exact hfinal

/-! ## Truncation absorption -/

private lemma trunc_eventually_le {Ctr cf : ℝ} (hCtr : 0 ≤ Ctr) (hcf : 0 < cf)
    (hcf2 : cf ≤ 1 / 2) :
    ∀ᶠ x : ℝ in atTop,
      Ctr * (x * (Real.log x) ^ 2 / engT x + Real.log x) ≤
        2 * x * Real.exp (-cf * Real.sqrt (Real.log x)) := by
  have hP : ∀ᶠ x : ℝ in atTop,
      Ctr * (Real.log x) ^ 2 * Real.exp (-Real.sqrt (Real.log x)) ≤
        Real.exp (-(1 / 2) * Real.sqrt (Real.log x)) := by
    have h := Commons.Analysis.Asymptotics.poly_mul_exp_neg_sqrtLog_le 1 one_pos 2 Ctr hCtr
    filter_upwards [h] with x hx
    simpa using hx
  have hC := const_mul_log_le_mul_exp_neg_sqrtLog cf hcf Ctr hCtr
  filter_upwards [hP, hC, eventually_ge_atTop (1 : ℝ)] with x hP hC hx1
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hsqLnn : 0 ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
  have hTinv : (engT x)⁻¹ = Real.exp (-Real.sqrt (Real.log x)) := by rw [engT, ← Real.exp_neg]
  have h2 : Real.exp (-(1 / 2) * Real.sqrt (Real.log x)) ≤
      Real.exp (-cf * Real.sqrt (Real.log x)) :=
    Real.exp_le_exp.mpr (by nlinarith [hcf2, hsqLnn])
  have hA : Ctr * (x * (Real.log x) ^ 2 / engT x)
      ≤ x * Real.exp (-cf * Real.sqrt (Real.log x)) := by
    have heq : Ctr * (x * (Real.log x) ^ 2 / engT x)
        = (Ctr * (Real.log x) ^ 2 * Real.exp (-Real.sqrt (Real.log x))) * x := by
      rw [div_eq_mul_inv, hTinv]; ring
    rw [heq]
    calc (Ctr * (Real.log x) ^ 2 * Real.exp (-Real.sqrt (Real.log x))) * x
        ≤ Real.exp (-(1 / 2) * Real.sqrt (Real.log x)) * x :=
          mul_le_mul_of_nonneg_right hP (le_of_lt hxpos)
      _ ≤ Real.exp (-cf * Real.sqrt (Real.log x)) * x :=
          mul_le_mul_of_nonneg_right h2 (le_of_lt hxpos)
      _ = x * Real.exp (-cf * Real.sqrt (Real.log x)) := by ring
  linarith

/-! ## The engine with exponential error -/

private lemma psi_sub_id_engine_exp :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      |Chebyshev.psi x - x| ≤ x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c₁, C₁, hc₁, hC₁pos, hZF1, hLD1⟩ := zeta_zeroFreeRegion_logDeriv_bound
  obtain ⟨C₂, δ₂, hC₂pos, hδ₂pos, hM2⟩ := zeta_logDeriv_near_axis_bound
  obtain ⟨ε₀, hε₀pos, hNA⟩ := zeta_zeroFree_near_axis
  obtain ⟨Ctr, hCtrpos, htrunc⟩ := psi_sub_perronZeta_bound
  set cf : ℝ := min c₁ 1 / 32 with hcfdef
  have hcfpos : 0 < cf := by rw [hcfdef]; positivity
  have hcf1 : cf ≤ c₁ / 12 := by
    rw [hcfdef]
    have h1 : min c₁ 1 ≤ c₁ := min_le_left _ _
    nlinarith [hc₁, h1]
  have hcf2 : cf ≤ 1 / 2 := by
    rw [hcfdef]
    have h1 : min c₁ 1 ≤ 1 := min_le_right _ _
    nlinarith [h1]
  have hC₁ : 0 ≤ C₁ := le_of_lt hC₁pos
  have hM1D := hM1_datum (c₁ := c₁) (C₁ := C₁) hc₁ hC₁ hLD1
  have hM2D := hM2_datum (C₂ := C₂) (δ₂ := δ₂) hM2
  have hx3 : ∀ᶠ x : ℝ in atTop, 3 ≤ x := eventually_ge_atTop 3
  have hL1 : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x := Real.tendsto_log_atTop.eventually_ge_atTop 1
  have hT2 : ∀ᶠ x : ℝ in atTop, 2 ≤ engT x := engT_eventually_ge 2
  have hδδ : ∀ᶠ x : ℝ in atTop, engDelta x c₁ ≤ δ₂ := engDelta_eventually_le hc₁ hδ₂pos
  have hδε : ∀ᶠ x : ℝ in atTop, engDelta x c₁ ≤ ε₀ := engDelta_eventually_le hc₁ hε₀pos
  have hδh : ∀ᶠ x : ℝ in atTop, engDelta x c₁ ≤ 1 / 2 :=
    engDelta_eventually_le hc₁ (by norm_num)
  have hrectEv : ∀ᶠ x : ℝ in atTop,
      (Set.uIcc (engSigma x c₁) (perronRe x) ×ℂ Set.uIcc (-(engT x)) (engT x)) ⊆
        {s : ℂ | (0 : ℝ) < s.re ∧ riemannZeta₁ s ≠ 0} := by
    filter_upwards [hx3, hδh, hδε] with x hx3 hδh hδε
    exact rect_zeta1_ne_zero_engine hx3 hc₁ hδh hδε hZF1 hNA
  have hintEv : ∀ᶠ x : ℝ in atTop,
      IntervalIntegrable (fun u : ℝ => ‖psiIntF x ((u : ℂ) + (engT x : ℂ) * Complex.I)‖)
          volume (engSigma x c₁) (perronRe x) ∧
      IntervalIntegrable (fun u : ℝ => ‖psiIntF x ((u : ℂ) + (((-engT x : ℝ) : ℂ)) * Complex.I)‖)
          volume (engSigma x c₁) (perronRe x) ∧
      IntervalIntegrable (fun t : ℝ => ‖psiIntF x ((engSigma x c₁ : ℂ) + (t : ℂ) * Complex.I)‖)
          volume (-(engT x)) (engT x) := by
    filter_upwards [hx3, hδh, hrectEv] with x hx3 hδh hrect
    exact engine_edge_integrable hx3 hc₁ (by linarith) hrect
  have htruncEv := trunc_eventually_le (Ctr := Ctr) (cf := cf) (le_of_lt hCtrpos) hcfpos hcf2
  have hpeS := perronEdgeSum_eventually_le (c₁ := c₁) (C₁ := C₁) (C₂ := C₂) (cf := cf)
    hc₁ hC₁ (le_of_lt hC₂pos) hcfpos hcf1 hcf2
  have h7 : ∀ᶠ x : ℝ in atTop,
      7 * Real.exp (-cf * Real.sqrt (Real.log x)) ≤ Real.exp (-(cf / 2) * Real.sqrt (Real.log x)) := by
    have h := Commons.Analysis.Asymptotics.poly_mul_exp_neg_sqrtLog_le cf hcfpos 0 7 (by norm_num)
    filter_upwards [h] with x hx
    simpa using hx
  refine ⟨cf / 2, by positivity, ?_⟩
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (show ∀ᶠ x : ℝ in atTop,
      |Chebyshev.psi x - x| ≤ x * Real.exp (-(cf / 2) * Real.sqrt (Real.log x)) from by
    filter_upwards [hx3, hL1, hT2, hδδ, hδε, hδh, hrectEv, hintEv, htruncEv, hpeS, h7]
      with x hx3 hL1 hT2 hδδ hδε hδh hrect hint htruncB hpeSB h7B
    obtain ⟨hIntTop, hIntBot, hIntL⟩ := hint
    have hper2 : perronRe x ≤ 2 := perronRe_le_two_of_three hx3
    have hper1 : 1 < perronRe x := perronRe_gt_one (by linarith : 1 < x)
    have hxpos : 0 < x := by linarith
    have hσpos : 0 < engSigma x c₁ := by dsimp [engSigma]; linarith [engDelta_pos (x := x) hc₁]
    have hδ1 : 0 < 1 - engSigma x c₁ := by dsimp [engSigma]; linarith [engDelta_pos (x := x) hc₁]
    have hHT : (1 : ℝ) ≤ engT x := le_trans (by norm_num) hT2
    have hTopB := hTopB_engine (x := x) (c := c₁) (C := C₁) (H := 1) hx3 hper2
      (le_of_lt hc₁) hHT hM1D
    have hBotB := hBotB_engine (x := x) (c := c₁) (C := C₁) (H := 1) hx3 hper2
      (le_of_lt hc₁) hHT hM1D
    have hNear := hNear_engine (x := x) (c := c₁) (C₂ := C₂) (δ₂ := δ₂) hc₁ hδδ hM2D
    have hFarPos := hFarPos_engine (x := x) (c := c₁) (C := C₁) (H := 1) hx3
      (le_of_lt hc₁) (by norm_num) hT2 hM1D
    have hFarNeg := hFarNeg_engine (x := x) (c := c₁) (C := C₁) (H := 1) hx3
      (le_of_lt hc₁) (by norm_num) hT2 hM1D
    have hE := psi_sub_id_le_engine (x := x) (T := engT x) (σ₁ := engSigma x c₁)
      hx3 hT2 hσpos hδ1 hper1 hrect hC₁ (le_of_lt hC₂pos) htrunc hTopB hBotB hNear hFarPos hFarNeg
      hIntTop hIntBot hIntL
    have hcoef : 0 ≤ 1 / (2 * Real.pi) := by positivity
    have h2' := mul_le_mul_of_nonneg_left hpeSB hcoef
    have hle1 : 1 / (2 * Real.pi) ≤ 1 := by
      rw [div_le_one (by positivity : (0:ℝ) < 2 * Real.pi)]
      linarith [Real.pi_gt_three]
    have h2'' : (1 / (2 * Real.pi)) * (5 * x * Real.exp (-cf * Real.sqrt (Real.log x)))
        ≤ 5 * x * Real.exp (-cf * Real.sqrt (Real.log x)) := by
      have hnn : 0 ≤ 5 * x * Real.exp (-cf * Real.sqrt (Real.log x)) := by positivity
      have hh := mul_le_mul_of_nonneg_right hle1 hnn
      rwa [one_mul] at hh
    have hcomb : (1 / (2 * Real.pi)) * perronEdgeSum x (engT x) (engSigma x c₁) C₁ C₂
        ≤ 5 * x * Real.exp (-cf * Real.sqrt (Real.log x)) := le_trans h2' h2''
    calc |Chebyshev.psi x - x|
        ≤ Ctr * (x * (Real.log x) ^ 2 / engT x + Real.log x) +
            (1 / (2 * Real.pi)) * perronEdgeSum x (engT x) (engSigma x c₁) C₁ C₂ := hE
      _ ≤ 2 * x * Real.exp (-cf * Real.sqrt (Real.log x)) +
            5 * x * Real.exp (-cf * Real.sqrt (Real.log x)) := by linarith [htruncB, hcomb]
      _ = (7 * Real.exp (-cf * Real.sqrt (Real.log x))) * x := by ring
      _ ≤ Real.exp (-(cf / 2) * Real.sqrt (Real.log x)) * x :=
          mul_le_mul_of_nonneg_right h7B (le_of_lt hxpos)
      _ = x * Real.exp (-(cf / 2) * Real.sqrt (Real.log x)) := by ring)
  exact ⟨x₀, hx₀⟩

/-! ## The exponential error term -/

theorem chebyshev_psi_sub_id_exp :
    ∃ c x₀ : ℝ, 0 < c ∧ ∀ x : ℝ, x₀ ≤ x →
      |Chebyshev.psi x - x| ≤ x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c, hc, x₀, hx₀⟩ := psi_sub_id_engine_exp
  exact ⟨c, x₀, hc, hx₀⟩

/-! ## The same bound uniformly for all `x ≥ 2`

The formulation with a threshold `x₀` is inconvenient for the PNT-in-arithmetic-
progressions main term, where one needs the error term valid for *every* `x ≥ 2`
(with a larger constant).  For `x ≤ x₀` the crude Chebyshev bound
`ψ(x) ≤ (log 4 + 4)·x` supplies this; the exponentially small factor is bounded
below on the finite range `[2, x₀]` by its value at `x₀`. -/

theorem chebyshev_psi_sub_id_exp_uniform :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |Chebyshev.psi x - x| ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  -- the theorem's existential is `∃ c, ∃ x₀, 0 < c ∧ …`, so peel `c, x₀` first
  obtain ⟨c, x₀, hc, hx₀⟩ := chebyshev_psi_sub_id_exp
  set y₀ : ℝ := max x₀ 2 with hy₀
  have hy₀2 : (2 : ℝ) ≤ y₀ := le_max_right _ _
  have hy₀pos : 0 < y₀ := by linarith
  have hlogy₀ : 0 < Real.log y₀ := Real.log_pos (by linarith)
  set C : ℝ := max 1 ((Real.log 4 + 5) * Real.exp (c * Real.sqrt (Real.log y₀))) with hC
  have hCge1 : (1 : ℝ) ≤ C := le_max_left _ _
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hCge1
  refine ⟨c, C, hc, hCpos, ?_⟩
  intro x hx2
  have hxpos : 0 < x := by linarith
  have hApos : 0 < Real.log 4 + 5 := by
    have h4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
    linarith
  rcases lt_or_ge x y₀ with hxy | hyx
  · -- finite range `2 ≤ x ≤ y₀`: use the crude Chebyshev bound
    have hpsi : Chebyshev.psi x ≤ (Real.log 4 + 4) * x :=
      Chebyshev.psi_le_const_mul_self (by linarith)
    have hpsinonneg : 0 ≤ Chebyshev.psi x := Chebyshev.psi_nonneg x
    have habs : |Chebyshev.psi x - x| ≤ (Real.log 4 + 5) * x := by
      rw [abs_le]
      constructor <;> nlinarith
    have hlogmono : Real.log x ≤ Real.log y₀ := Real.log_le_log hxpos (le_of_lt hxy)
    have hsq : Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log y₀) := Real.sqrt_le_sqrt hlogmono
    have hmono : c * Real.sqrt (Real.log x) ≤ c * Real.sqrt (Real.log y₀) :=
      mul_le_mul_of_nonneg_left hsq (le_of_lt hc)
    -- `(log 4 + 5) · e^{c√(log y₀)} · e^{-c√(log x)} ≥ log 4 + 5`
    have hprod : (Real.log 4 + 5) ≤
        ((Real.log 4 + 5) * Real.exp (c * Real.sqrt (Real.log y₀))) *
          Real.exp (-c * Real.sqrt (Real.log x)) := by
      have hge : 1 ≤ Real.exp (c * Real.sqrt (Real.log y₀) + -c * Real.sqrt (Real.log x)) := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by linarith)
      have heq : ((Real.log 4 + 5) * Real.exp (c * Real.sqrt (Real.log y₀))) *
          Real.exp (-c * Real.sqrt (Real.log x)) =
          (Real.log 4 + 5) *
            Real.exp (c * Real.sqrt (Real.log y₀) + -c * Real.sqrt (Real.log x)) := by
        rw [mul_assoc, ← Real.exp_add]
      rw [heq]
      calc (Real.log 4 + 5) = (Real.log 4 + 5) * 1 := by ring
        _ ≤ (Real.log 4 + 5) *
              Real.exp (c * Real.sqrt (Real.log y₀) + -c * Real.sqrt (Real.log x)) :=
            mul_le_mul_of_nonneg_left hge (le_of_lt hApos)
    have hkey : Real.log 4 + 5 ≤ C * Real.exp (-c * Real.sqrt (Real.log x)) := by
      refine le_trans hprod ?_
      have hCge : ((Real.log 4 + 5) * Real.exp (c * Real.sqrt (Real.log y₀))) ≤ C :=
        le_max_right _ _
      exact mul_le_mul_of_nonneg_right hCge (Real.exp_nonneg _)
    calc |Chebyshev.psi x - x| ≤ (Real.log 4 + 5) * x := habs
      _ ≤ (C * Real.exp (-c * Real.sqrt (Real.log x))) * x :=
          mul_le_mul_of_nonneg_right hkey (le_of_lt hxpos)
      _ = C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by ring
  · -- large range `y₀ ≤ x`: the thresholded estimate applies, `C ≥ 1`
    have hx₀le : x₀ ≤ x := le_trans (le_max_left _ _) hyx
    have hbig := hx₀ x hx₀le
    have hexpnn : 0 ≤ Real.exp (-c * Real.sqrt (Real.log x)) := Real.exp_nonneg _
    have hxle : x ≤ C * x := by
      have := mul_le_mul_of_nonneg_right hCge1 (le_of_lt hxpos)
      rwa [one_mul] at this
    calc |Chebyshev.psi x - x| ≤ x * Real.exp (-c * Real.sqrt (Real.log x)) := hbig
      _ ≤ (C * x) * Real.exp (-c * Real.sqrt (Real.log x)) :=
          mul_le_mul_of_nonneg_right hxle hexpnn
      _ = C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by ring


end Commons.NumberTheory.Zeta
