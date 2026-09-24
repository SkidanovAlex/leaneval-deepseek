import Mathlib
import Submission.Work.GM.Affine.WinMass_fejer_defs
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.WinMass_basic
import Submission.Work.GM.Affine.integrable_Fhat_sq
import Submission.Work.GM.Affine.smoothed_psiSmooth_fourier
import Submission.Work.GM.Affine.Gfun_sq_ge_coherence

/-!
# `Work.GM.Affine.WinMass_core_of_fejer_route`

Assembly of the target window bound from the six analytic inputs of the "Fejér route"
(`WINMASS_ROUTE.md`): the Fejér majorant (`hF`), the near/lattice estimate (`hN`), the far tail
from the decay hypothesis (`hTl`), the `L²` contraction of the smoothing (`hL2`), the crude
always-valid bound (`hCr`) and the small-`M₂` bound (`hSm`).

The near/far split is taken at `|x| = T^{δ/2} T / M₂`, so that the constant `K = T^{δ/2}` of `hN`
satisfies `K² = T^δ`; the `T^δ`-loss of the near part is exactly the `T^δ` of the target.  The
tail bound contributes the second term `M₂² M₃ ∫f²`, and the two "cheap" cases (`M₂ < 1`, or `M₂ ≥ 1`
with either `M₂ ≤ 2C₀` or `T` below a fixed threshold depending on `C₀`, `δ`) are handled by `hSm`
and `hCr`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.GM.Affine

noncomputable section

/-- `fejerK M₃` is continuous. -/
lemma fejerK_continuous_asm (M₃ : ℝ) : Continuous (fun x : ℝ => fejerK M₃ x) := by
  rw [show (fun x : ℝ => fejerK M₃ x) = fun x : ℝ => 1 + 2 * ∑ k ∈ Finset.Icc 1 (fejerN M₃ - 1),
      (1 - (k : ℝ) / (fejerN M₃)) * Real.cos (2 * Real.pi * (k : ℝ) * x) from rfl]
  refine Continuous.add continuous_const (Continuous.mul continuous_const ?_)
  exact continuous_finsetSum _ (fun k _ =>
    Continuous.mul continuous_const (Real.continuous_cos.comp (by fun_prop)))

/-- `|fejerK M₃ x| ≤ 2 * fejerN M₃`. -/
lemma fejerK_abs_le_asm (M₃ x : ℝ) : |fejerK M₃ x| ≤ 2 * (fejerN M₃ : ℝ) := by
  have hN1 : 1 ≤ fejerN M₃ := fejerN_pos M₃
  have hNpos : (0 : ℝ) < (fejerN M₃ : ℝ) := by exact_mod_cast hN1
  have hterm : ∀ k ∈ Finset.Icc 1 (fejerN M₃ - 1),
      |(1 - (k : ℝ) / (fejerN M₃)) * Real.cos (2 * Real.pi * (k : ℝ) * x)| ≤ 1 := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk2 : (k : ℝ) ≤ (fejerN M₃ : ℝ) := by
      have : k ≤ fejerN M₃ := by omega
      exact_mod_cast this
    have hkn : 0 ≤ (k : ℝ) / (fejerN M₃) := div_nonneg (by positivity) hNpos.le
    have hkn1 : (k : ℝ) / (fejerN M₃) ≤ 1 := (div_le_one hNpos).mpr hk2
    have h1 : |1 - (k : ℝ) / (fejerN M₃)| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    rw [abs_mul]
    calc |1 - (k : ℝ) / (fejerN M₃)| * |Real.cos (2 * Real.pi * (k : ℝ) * x)|
        ≤ 1 * 1 := mul_le_mul h1 (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one
      _ = 1 := by ring
  have hsumabs : |∑ k ∈ Finset.Icc 1 (fejerN M₃ - 1),
        (1 - (k : ℝ) / (fejerN M₃)) * Real.cos (2 * Real.pi * (k : ℝ) * x)|
      ≤ ((Finset.Icc 1 (fejerN M₃ - 1)).card : ℝ) := by
    calc |∑ k ∈ Finset.Icc 1 (fejerN M₃ - 1),
          (1 - (k : ℝ) / (fejerN M₃)) * Real.cos (2 * Real.pi * (k : ℝ) * x)|
        ≤ ∑ k ∈ Finset.Icc 1 (fejerN M₃ - 1),
            |(1 - (k : ℝ) / (fejerN M₃)) * Real.cos (2 * Real.pi * (k : ℝ) * x)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ Finset.Icc 1 (fejerN M₃ - 1), (1 : ℝ) := Finset.sum_le_sum hterm
      _ = ((Finset.Icc 1 (fejerN M₃ - 1)).card : ℝ) := by simp
  have hcard : ((Finset.Icc 1 (fejerN M₃ - 1)).card : ℝ) ≤ (fejerN M₃ : ℝ) - 1 := by
    have h1 : (Finset.Icc 1 (fejerN M₃ - 1)).card = fejerN M₃ - 1 := by
      rw [Nat.card_Icc]; omega
    rw [h1, Nat.cast_sub hN1]
    norm_num
  have hdef : fejerK M₃ x = 1 + 2 * (∑ k ∈ Finset.Icc 1 (fejerN M₃ - 1),
      (1 - (k : ℝ) / (fejerN M₃)) * Real.cos (2 * Real.pi * (k : ℝ) * x)) := rfl
  rw [hdef]
  calc |1 + 2 * (∑ k ∈ Finset.Icc 1 (fejerN M₃ - 1),
        (1 - (k : ℝ) / (fejerN M₃)) * Real.cos (2 * Real.pi * (k : ℝ) * x))|
      ≤ 1 + |2 * (∑ k ∈ Finset.Icc 1 (fejerN M₃ - 1),
        (1 - (k : ℝ) / (fejerN M₃)) * Real.cos (2 * Real.pi * (k : ℝ) * x))| := by
        have h := abs_add_le (1 : ℝ) (2 * (∑ k ∈ Finset.Icc 1 (fejerN M₃ - 1),
          (1 - (k : ℝ) / (fejerN M₃)) * Real.cos (2 * Real.pi * (k : ℝ) * x)))
        simpa using h
    _ = 1 + 2 * |∑ k ∈ Finset.Icc 1 (fejerN M₃ - 1),
        (1 - (k : ℝ) / (fejerN M₃)) * Real.cos (2 * Real.pi * (k : ℝ) * x)| := by
        rw [abs_mul]; norm_num
    _ ≤ 1 + 2 * ((fejerN M₃ : ℝ) - 1) := by linarith [hsumabs, hcard]
    _ ≤ 2 * (fejerN M₃ : ℝ) := by linarith

/-- `f̃ = smoothed psiSmooth T f` is nonnegative when `f` is. -/
lemma smoothed_psiSmooth_nonneg_asm {T : ℝ} (hT : 0 < T) {f : ℝ → ℝ} (hfnn : ∀ u, 0 ≤ f u)
    (u : ℝ) : 0 ≤ smoothed psiSmooth T f u := by
  rw [smoothed]
  exact mul_nonneg hT.le (integral_nonneg (fun v => mul_nonneg (psiSmooth_nonneg _) (hfnn v)))

/-- `‖Bsum f M₂ ·‖²` is integrable for `f` continuous with `SuppHyp C₀ f`. -/
lemma integrable_normSq_Bsum_asm {C₀ : ℝ} (hC₀ : 1 ≤ C₀) {f : ℝ → ℝ} (hf : Continuous f)
    (hSupp : SuppHyp C₀ f) {M₂ : ℝ} (hM₂ : 0 < M₂) :
    Integrable (fun x : ℝ => ‖Bsum f M₂ x‖ ^ 2) := by
  have hHcont : Continuous (Hprof f M₂) := Hprof_continuous hf M₂
  have hHcs : HasCompactSupport (Hprof f M₂) := Hprof_hasCompactSupport hSupp hC₀ hM₂.le
  have h := integrable_Fhat_sq hHcont hHcs
  refine h.congr (Filter.Eventually.of_forall (fun x => ?_))
  show (‖Fhat (Hprof f M₂) x‖ : ℝ) ^ 2 = ‖Bsum f M₂ x‖ ^ 2
  rw [Bsum_eq_Fhat_Hprof hf hSupp hC₀ hM₂ x]

/-- `HasCompactSupport f` from `SuppHyp C₀ f`. -/
lemma hcs_of_suppHyp_asm {C₀ : ℝ} {f : ℝ → ℝ} (h : SuppHyp C₀ f) : HasCompactSupport f :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (fun u hu => by
    rw [Function.mem_support] at hu
    exact h u hu)

theorem WinMass_core_of_fejer_route {C₀ T₀ C₃ : ℝ} (hC₀ : 1 ≤ C₀) (hT₀ : 1 ≤ T₀)
    (hC₃ : 1 ≤ C₃) (c : ℕ → ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hF : ∃ C : ℝ, 0 < C ∧
      ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        ∀ M₂ : ℝ, 0 ≤ M₂ → ∀ M₃ : ℝ, 1 ≤ M₃ →
          WinMass f M₂ M₃ ≤ C * ∫ x : ℝ, ‖Bsum f M₂ x‖ ^ 2 * fejerK M₃ x)
    (hN : ∃ C : ℝ, 0 < C ∧
      ∀ K T M₂ : ℝ, 1 ≤ T → 8 ≤ K → 2 * C₀ ≤ M₂ → 2 * C₀ ≤ T →
        ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
          ∀ M₃ : ℝ, 1 ≤ M₃ →
            (∫ x in Set.Icc (-(K * T / M₂)) (K * T / M₂),
                ‖Bsum f M₂ x‖ ^ 2 * fejerK M₃ x)
              ≤ C * K ^ 2 * M₂ *
                  ∫ u : ℝ, smoothed psiSmooth T f u * Gfun C₀ T M₂ f u)
    (hTl : ∃ C : ℝ, 0 < C ∧
      ∀ T : ℝ, 1 ≤ T → 2 * C₀ ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) →
        SuppHyp C₀ f →
        ∀ Λ : ℝ, 0 < Λ →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
        ∀ M₂ : ℝ, 1 ≤ M₂ → M₂ ≤ T ^ 4 → ∀ M₃ : ℝ, 1 ≤ M₃ →
          (∫ x in {x : ℝ | T ^ (δ / 2) * T / M₂ < |x|},
              ‖Bsum f M₂ x‖ ^ 2 * fejerK M₃ x)
            ≤ C * M₂ ^ 2 * M₃ * ∫ u, (f u) ^ 2)
    (hL2 : ∀ T : ℝ, 0 < T → ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f →
      (∫ u, (smoothed psiSmooth T f u) ^ 2) ≤ ∫ u, (f u) ^ 2)
    (hCr : ∃ C : ℝ, 0 < C ∧
      ∀ M₂ M₃ : ℝ, 1 ≤ M₃ → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        WinMass f M₂ M₃ ≤ C * (max M₂ 1) ^ 3 * M₃ * ∫ u, (f u) ^ 2)
    (hSm : ∀ M₂ M₃ : ℝ, 0 < M₂ → 1 ≤ M₃ → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) →
      HasCompactSupport f → SuppHyp C₀ f → M₂ < 1 →
        WinMass f M₂ M₃ ≤ 20 * M₂ ^ 2 * M₃ * ∫ u, (f u) ^ 2) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        ∀ Λ : ℝ, 0 < Λ →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
        ∀ Mbig M₂ M₃ : ℝ,
        1 ≤ Mbig → Mbig ≤ T ^ 4 → 1 ≤ M₃ → M₃ ≤ C₃ * Mbig → 0 < M₂ → M₂ ≤ Mbig →
        WinMass f M₂ M₃ ≤
          C' * T ^ δ * (M₂ * (∫ u, (f u) ^ 2) ^ (1/2:ℝ) *
              (∫ u, (Gfun C₀ T M₂ f u) ^ 2) ^ (1/2:ℝ) +
            M₂ ^ 2 * M₃ * ∫ u, (f u) ^ 2) := by
  obtain ⟨CF, hCFpos, hFw⟩ := hF
  obtain ⟨CN, hCNpos, hNw⟩ := hN
  obtain ⟨CTl, hCTlpos, hTlw⟩ := hTl
  obtain ⟨CCr, hCCrpos, hCrw⟩ := hCr
  have hT₀pos : (0 : ℝ) < T₀ := lt_of_lt_of_le zero_lt_one hT₀
  have hC₀pos : (0 : ℝ) < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  -- the threshold `T₁` (above which the `T^{δ/2}`-window argument applies)
  set T₁ : ℝ := max (max T₀ (2 * C₀)) (max 1 ((8 : ℝ) ^ (2 / δ))) with hT₁def
  have hT₁T₀ : T₀ ≤ T₁ := by
    rw [hT₁def]
    exact le_trans (le_max_left T₀ (2 * C₀))
      (le_max_left (max T₀ (2 * C₀)) (max 1 ((8 : ℝ) ^ (2 / δ))))
  have hT₁2C₀ : 2 * C₀ ≤ T₁ := by
    rw [hT₁def]
    exact le_trans (le_max_right T₀ (2 * C₀))
      (le_max_left (max T₀ (2 * C₀)) (max 1 ((8 : ℝ) ^ (2 / δ))))
  have hT₁8 : (8 : ℝ) ^ (2 / δ) ≤ T₁ := by
    rw [hT₁def]
    exact le_trans (le_max_right 1 ((8 : ℝ) ^ (2 / δ)))
      (le_max_right (max T₀ (2 * C₀)) (max 1 ((8 : ℝ) ^ (2 / δ))))
  -- the crude bound for the "cheap" cases
  set Θ : ℝ := max (2 * C₀) (T₁ ^ 4) with hΘdef
  have hΘ1 : 1 ≤ Θ := by
    rw [hΘdef]
    have h : (1 : ℝ) ≤ 2 * C₀ := by linarith
    exact le_trans h (le_max_left (2 * C₀) (T₁ ^ 4))
  have hΘpos : 0 < Θ := lt_of_lt_of_le zero_lt_one hΘ1
  -- the final constant
  set Cval : ℝ := CCr * Θ + 20 + CF * (CN + CTl) + 1 with hCvaldef
  have hCvalpos : 0 < Cval := by
    rw [hCvaldef]
    have h1 : 0 < CCr * Θ := mul_pos hCCrpos hΘpos
    have h2 : 0 ≤ CF * (CN + CTl) := mul_nonneg hCFpos.le (add_nonneg hCNpos.le hCTlpos.le)
    linarith
  refine ⟨Cval, hCvalpos, ?_⟩
  intro T hTT₀ f hf hfnn hSupp Λ hΛ hdec hΛbd Mbig M₂ M₃ hMbig1 hMbigT4 hM₃ hM₃le hM₂pos hM₂Mbig
  have hTpos : 0 < T := lt_of_lt_of_le hT₀pos hTT₀
  have hT1 : 1 ≤ T := le_trans hT₀ hTT₀
  have hTδnn : 0 ≤ T ^ δ := Real.rpow_nonneg hTpos.le δ
  have hTδ1 : 1 ≤ T ^ δ := Real.one_le_rpow hT1 hδ.le
  have hfcs : HasCompactSupport f := hcs_of_suppHyp_asm hSupp
  have hAnn : 0 ≤ ∫ u, (f u) ^ 2 := integral_nonneg (fun u => sq_nonneg _)
  have hBnn : 0 ≤ ∫ u, (Gfun C₀ T M₂ f u) ^ 2 := integral_nonneg (fun u => sq_nonneg _)
  have hAs : 0 ≤ (∫ u, (f u) ^ 2) ^ (1/2:ℝ) := Real.rpow_nonneg hAnn _
  have hBs : 0 ≤ (∫ u, (Gfun C₀ T M₂ f u) ^ 2) ^ (1/2:ℝ) := Real.rpow_nonneg hBnn _
  have hprod1 : 0 ≤ M₂ * (∫ u, (f u) ^ 2) ^ (1/2:ℝ) * (∫ u, (Gfun C₀ T M₂ f u) ^ 2) ^ (1/2:ℝ) :=
    mul_nonneg (mul_nonneg hM₂pos.le hAs) hBs
  have hprod2 : 0 ≤ M₂ ^ 2 * M₃ * ∫ u, (f u) ^ 2 :=
    mul_nonneg (mul_nonneg (pow_nonneg hM₂pos.le 2) (by linarith)) hAnn
  set br : ℝ := M₂ * (∫ u, (f u) ^ 2) ^ (1/2:ℝ) *
      (∫ u, (Gfun C₀ T M₂ f u) ^ 2) ^ (1/2:ℝ) + M₂ ^ 2 * M₃ * ∫ u, (f u) ^ 2 with hbrdef
  have hbrnn : 0 ≤ br := by rw [hbrdef]; linarith
  have hbr2 : M₂ ^ 2 * M₃ * ∫ u, (f u) ^ 2 ≤ br := by
    rw [hbrdef]; exact le_add_of_nonneg_left hprod1
  have hbr1 : M₂ * (∫ u, (f u) ^ 2) ^ (1/2:ℝ) * (∫ u, (Gfun C₀ T M₂ f u) ^ 2) ^ (1/2:ℝ) ≤ br := by
    rw [hbrdef]; exact le_add_of_nonneg_right hprod2
  -- scaling by `T ^ δ ≥ 1`
  have hscale : ∀ X : ℝ, 0 ≤ X → X ≤ T ^ δ * X := by
    intro X hX
    have h := mul_le_mul_of_nonneg_right hTδ1 hX
    simpa using h
  have hconst_mul : ∀ K : ℝ, K ≤ Cval → K * (T ^ δ * br) ≤ Cval * T ^ δ * br := by
    intro K hK
    calc K * (T ^ δ * br) ≤ Cval * (T ^ δ * br) :=
          mul_le_mul_of_nonneg_right hK (mul_nonneg hTδnn hbrnn)
      _ = Cval * T ^ δ * br := by ring
  have hCval20 : (20 : ℝ) ≤ Cval := by
    rw [hCvaldef]
    have h1 : 0 ≤ CCr * Θ := le_of_lt (mul_pos hCCrpos hΘpos)
    have h2 : 0 ≤ CF * (CN + CTl) := mul_nonneg hCFpos.le (add_nonneg hCNpos.le hCTlpos.le)
    linarith
  have hCvalCheap : CCr * Θ ≤ Cval := by
    rw [hCvaldef]
    have h1 : 0 ≤ CCr * Θ := le_of_lt (mul_pos hCCrpos hΘpos)
    have h2 : 0 ≤ CF * (CN + CTl) := mul_nonneg hCFpos.le (add_nonneg hCNpos.le hCTlpos.le)
    linarith
  have hCvalMain : CF * (CN + CTl) ≤ Cval := by
    rw [hCvaldef]
    have h1 : 0 ≤ CCr * Θ := le_of_lt (mul_pos hCCrpos hΘpos)
    have h2 : 0 ≤ CF * (CN + CTl) := mul_nonneg hCFpos.le (add_nonneg hCNpos.le hCTlpos.le)
    linarith
  -- the `M₂²M₃∫f²` term is dominated by `T^δ * br`
  have hmid : M₂ ^ 2 * M₃ * (∫ u, (f u) ^ 2) ≤ T ^ δ * br := by
    have h1 := hscale (M₂ ^ 2 * M₃ * (∫ u, (f u) ^ 2)) hprod2
    exact h1.trans (mul_le_mul_of_nonneg_left hbr2 hTδnn)
  by_cases hM₂lt : M₂ < 1
  · -- the degenerate range `M₂ < 1`
    have hsm := hSm M₂ M₃ hM₂pos hM₃ f hf hfnn hfcs hSupp hM₂lt
    have hstep : WinMass f M₂ M₃ ≤ 20 * (T ^ δ * br) := by
      have h1 : WinMass f M₂ M₃ ≤ 20 * (M₂ ^ 2 * M₃ * (∫ u, (f u) ^ 2)) := by
        rw [show (20 : ℝ) * M₂ ^ 2 * M₃ * (∫ u, (f u) ^ 2)
            = 20 * (M₂ ^ 2 * M₃ * (∫ u, (f u) ^ 2)) from by ring] at hsm
        exact hsm
      have h2 : 20 * (M₂ ^ 2 * M₃ * (∫ u, (f u) ^ 2)) ≤ 20 * (T ^ δ * br) :=
        mul_le_mul_of_nonneg_left hmid (by norm_num)
      exact h1.trans h2
    exact hstep.trans (hconst_mul 20 hCval20)
  · have hM₂1 : 1 ≤ M₂ := not_lt.mp hM₂lt
    by_cases hcheap : M₂ ≤ 2 * C₀ ∨ T < T₁
    · -- `M₂ ≤ 2C₀`, or `T` below the threshold: the crude bound
      have hcr := hCrw M₂ M₃ hM₃ f hf hfnn hSupp
      have hmax : max M₂ 1 = M₂ := max_eq_left hM₂1
      rw [hmax] at hcr
      have hM₂Θ : M₂ ≤ Θ := by
        rcases hcheap with h | h
        · rw [hΘdef]
          exact le_trans h (le_max_left (2 * C₀) (T₁ ^ 4))
        · rw [hΘdef]
          have h1 : M₂ ≤ T ^ 4 := le_trans hM₂Mbig hMbigT4
          have h2 : T ^ 4 ≤ T₁ ^ 4 := pow_le_pow_left₀ hTpos.le (le_of_lt h) 4
          exact le_trans h1 (le_trans h2 (le_max_right (2 * C₀) (T₁ ^ 4)))
      have hcube : M₂ ^ 3 ≤ Θ * M₂ ^ 2 := by
        have h2 : (0 : ℝ) ≤ M₂ ^ 2 := pow_nonneg hM₂pos.le 2
        calc M₂ ^ 3 = M₂ ^ 2 * M₂ := by ring
          _ ≤ M₂ ^ 2 * Θ := mul_le_mul_of_nonneg_left hM₂Θ h2
          _ = Θ * M₂ ^ 2 := by ring
      have hstep : WinMass f M₂ M₃ ≤ (CCr * Θ) * (T ^ δ * br) := by
        have hA : WinMass f M₂ M₃ ≤ CCr * Θ * M₂ ^ 2 * M₃ * (∫ u, (f u) ^ 2) := by
          have hb : M₂ ^ 3 * M₃ ≤ (Θ * M₂ ^ 2) * M₃ :=
            mul_le_mul_of_nonneg_right hcube (by linarith : (0 : ℝ) ≤ M₃)
          have hc : (M₂ ^ 3 * M₃) * (∫ u, (f u) ^ 2)
              ≤ ((Θ * M₂ ^ 2) * M₃) * (∫ u, (f u) ^ 2) :=
            mul_le_mul_of_nonneg_right hb hAnn
          have hd : CCr * ((M₂ ^ 3 * M₃) * (∫ u, (f u) ^ 2))
              ≤ CCr * (((Θ * M₂ ^ 2) * M₃) * (∫ u, (f u) ^ 2)) :=
            mul_le_mul_of_nonneg_left hc hCCrpos.le
          refine hcr.trans ?_
          calc CCr * M₂ ^ 3 * M₃ * (∫ u, (f u) ^ 2)
              = CCr * ((M₂ ^ 3 * M₃) * (∫ u, (f u) ^ 2)) := by ring
            _ ≤ CCr * (((Θ * M₂ ^ 2) * M₃) * (∫ u, (f u) ^ 2)) := hd
            _ = CCr * Θ * M₂ ^ 2 * M₃ * (∫ u, (f u) ^ 2) := by ring
        have hB : CCr * Θ * M₂ ^ 2 * M₃ * (∫ u, (f u) ^ 2) ≤ CCr * Θ * (T ^ δ * br) := by
          calc CCr * Θ * M₂ ^ 2 * M₃ * (∫ u, (f u) ^ 2)
              = CCr * Θ * (M₂ ^ 2 * M₃ * (∫ u, (f u) ^ 2)) := by ring
            _ ≤ CCr * Θ * (T ^ δ * br) :=
                mul_le_mul_of_nonneg_left hmid (mul_nonneg hCCrpos.le hΘpos.le)
        exact hA.trans hB
      exact hstep.trans (hconst_mul (CCr * Θ) hCvalCheap)
    · -- the main case: `M₂ > 2C₀` and `T ≥ T₁`
      have hM₂gt : 2 * C₀ < M₂ := not_le.mp (fun h => hcheap (Or.inl h))
      have hTT₁ : T₁ ≤ T := not_lt.mp (fun h => hcheap (Or.inr h))
      have hM₂1' : 1 ≤ M₂ := by linarith
      have h2C₀T : 2 * C₀ ≤ T := le_trans hT₁2C₀ hTT₁
      have hM₂T4 : M₂ ≤ T ^ 4 := le_trans hM₂Mbig hMbigT4
      have hK8 : 8 ≤ T ^ (δ / 2) := by
        have h1 : (8 : ℝ) ^ (2 / δ) ≤ T := le_trans hT₁8 hTT₁
        have h2 : ((8 : ℝ) ^ (2 / δ)) ^ (δ / 2) ≤ T ^ (δ / 2) :=
          Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) h1 (by positivity)
        have h3 : ((8 : ℝ) ^ (2 / δ)) ^ (δ / 2) = 8 := by
          rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 8)]
          have h4 : (2 / δ) * (δ / 2) = 1 := by field_simp
          rw [h4, Real.rpow_one]
        linarith
      have hK2 : (T ^ (δ / 2)) ^ 2 = T ^ δ := by
        rw [← Real.rpow_ofNat (T ^ (δ / 2)) 2, ← Real.rpow_mul hTpos.le (δ / 2) 2]
        have h4 : δ / 2 * 2 = δ := by ring
        rw [h4]
      -- facts about the smoothing
      have hsmcont : Continuous (smoothed psiSmooth T f) :=
        (smoothed_psiSmooth_fourier hTpos hf hfcs).1
      have hsmcs : HasCompactSupport (smoothed psiSmooth T f) :=
        (smoothed_psiSmooth_fourier hTpos hf hfcs).2.1
      have hsmnn : ∀ u : ℝ, 0 ≤ smoothed psiSmooth T f u :=
        fun u => smoothed_psiSmooth_nonneg_asm hTpos hfnn u
      -- facts about `Gfun`
      have hGcont : Continuous (fun u : ℝ => Gfun C₀ T M₂ f u) := by
        rw [show (fun u : ℝ => Gfun C₀ T M₂ f u) = fun u : ℝ =>
            ∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂,
              ∑ j ∈ Finset.Icc (-⌊2 * C₀ * M₂⌋) ⌊2 * C₀ * M₂⌋,
                smoothed psiSmooth T f (((m₂ : ℝ) * u + (j : ℝ)) / (m₂' : ℝ)) from
          funext (fun u => by rw [Gfun])]
        refine continuous_finsetSum _ (fun m₂ _ => continuous_finsetSum _ (fun m₂' _ =>
          continuous_finsetSum _ (fun j _ => ?_)))
        exact hsmcont.comp (((continuous_const.mul continuous_id).add continuous_const).div_const _)
      have hGcs : HasCompactSupport (fun u : ℝ => Gfun C₀ T M₂ f u) :=
        HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-(2 * C₀ + 1)) (4 * C₀ + 1))
          isCompact_Icc (fun u hu =>
            Gfun_supp_subset hC₀ hT1 hM₂1' hSupp u (Function.mem_support.mp hu))
      have hGnn : ∀ u : ℝ, 0 ≤ Gfun C₀ T M₂ f u := by
        intro u
        rw [show Gfun C₀ T M₂ f u = ∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂,
            ∑ j ∈ Finset.Icc (-⌊2 * C₀ * M₂⌋) ⌊2 * C₀ * M₂⌋,
              smoothed psiSmooth T f (((m₂ : ℝ) * u + (j : ℝ)) / (m₂' : ℝ)) from by rw [Gfun]]
        exact Finset.sum_nonneg (fun m₂ _ => Finset.sum_nonneg (fun m₂' _ =>
          Finset.sum_nonneg (fun j _ => hsmnn _)))
      -- Cauchy--Schwarz
      have hCS : (∫ u, smoothed psiSmooth T f u * Gfun C₀ T M₂ f u)
          ≤ (∫ u, (f u) ^ 2) ^ (1/2:ℝ) * (∫ u, (Gfun C₀ T M₂ f u) ^ 2) ^ (1/2:ℝ) := by
        have h1 := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) (p := 2) (q := 2)
          (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
          (Filter.Eventually.of_forall hsmnn) (Filter.Eventually.of_forall hGnn)
          (hsmcont.memLp_of_hasCompactSupport hsmcs)
          (hGcont.memLp_of_hasCompactSupport hGcs)
        simp only [Real.rpow_ofNat] at h1
        refine h1.trans ?_
        have hL2' : (∫ u, (smoothed psiSmooth T f u) ^ 2) ≤ ∫ u, (f u) ^ 2 := hL2 T hTpos f hf hfcs
        have hle : (∫ u, (smoothed psiSmooth T f u) ^ 2) ^ (1/2:ℝ)
            ≤ (∫ u, (f u) ^ 2) ^ (1/2:ℝ) :=
          Real.rpow_le_rpow (integral_nonneg (fun u => sq_nonneg _)) hL2' (by norm_num)
        exact mul_le_mul_of_nonneg_right hle hBs
      -- integrability of the Fejér integrand, and the near/far split
      have hBint : Integrable (fun x : ℝ => ‖Bsum f M₂ x‖ ^ 2) :=
        integrable_normSq_Bsum_asm hC₀ hf hSupp hM₂pos
      have hKbdd : ∀ᵐ x ∂volume, ‖fejerK M₃ x‖ ≤ 2 * (fejerN M₃ : ℝ) :=
        Filter.Eventually.of_forall (fun x => by
          rw [Real.norm_eq_abs]; exact fejerK_abs_le_asm M₃ x)
      have hgint : Integrable (fun x : ℝ => ‖Bsum f M₂ x‖ ^ 2 * fejerK M₃ x) := by
        have h := hBint.bdd_mul (fejerK_continuous_asm M₃).aestronglyMeasurable hKbdd
        refine h.congr (Filter.Eventually.of_forall (fun x => ?_))
        ring
      have hSmeas : MeasurableSet {x : ℝ | |x| ≤ T ^ (δ / 2) * T / M₂} :=
        measurableSet_le continuous_abs.measurable measurable_const
      have hsplit : (∫ x : ℝ, ‖Bsum f M₂ x‖ ^ 2 * fejerK M₃ x)
          = (∫ x in {x : ℝ | |x| ≤ T ^ (δ / 2) * T / M₂}, ‖Bsum f M₂ x‖ ^ 2 * fejerK M₃ x)
            + (∫ x in ({x : ℝ | |x| ≤ T ^ (δ / 2) * T / M₂})ᶜ,
                ‖Bsum f M₂ x‖ ^ 2 * fejerK M₃ x) :=
        (MeasureTheory.integral_add_compl hSmeas hgint).symm
      -- the near part
      have hnear : (∫ x in {x : ℝ | |x| ≤ T ^ (δ / 2) * T / M₂},
            ‖Bsum f M₂ x‖ ^ 2 * fejerK M₃ x) ≤ CN * T ^ δ * br := by
        have hset : {x : ℝ | |x| ≤ T ^ (δ / 2) * T / M₂}
            = Set.Icc (-(T ^ (δ / 2) * T / M₂)) (T ^ (δ / 2) * T / M₂) := by
          ext x
          simp only [Set.mem_setOf_eq, Set.mem_Icc, abs_le]
        rw [hset]
        have hnear0 := hNw (T ^ (δ / 2)) T M₂ hT1 hK8 (le_of_lt hM₂gt) h2C₀T f hf hfnn hSupp M₃ hM₃
        rw [hK2] at hnear0
        refine hnear0.trans ?_
        have h1 : M₂ * (∫ u, smoothed psiSmooth T f u * Gfun C₀ T M₂ f u) ≤ br := by
          have h2 : M₂ * (∫ u, smoothed psiSmooth T f u * Gfun C₀ T M₂ f u)
              ≤ M₂ * ((∫ u, (f u) ^ 2) ^ (1/2:ℝ) *
                  (∫ u, (Gfun C₀ T M₂ f u) ^ 2) ^ (1/2:ℝ)) :=
            mul_le_mul_of_nonneg_left hCS hM₂pos.le
          have h3 : M₂ * ((∫ u, (f u) ^ 2) ^ (1/2:ℝ) *
                (∫ u, (Gfun C₀ T M₂ f u) ^ 2) ^ (1/2:ℝ)) ≤ br := by
            rw [hbrdef]
            rw [show M₂ * ((∫ u, (f u) ^ 2) ^ (1/2:ℝ) *
                (∫ u, (Gfun C₀ T M₂ f u) ^ 2) ^ (1/2:ℝ))
                = M₂ * (∫ u, (f u) ^ 2) ^ (1/2:ℝ) *
                  (∫ u, (Gfun C₀ T M₂ f u) ^ 2) ^ (1/2:ℝ) from by ring]
            exact le_add_of_nonneg_right hprod2
          exact h2.trans h3
        calc CN * T ^ δ * M₂ * (∫ u, smoothed psiSmooth T f u * Gfun C₀ T M₂ f u)
            = CN * T ^ δ * (M₂ * (∫ u, smoothed psiSmooth T f u * Gfun C₀ T M₂ f u)) := by ring
          _ ≤ CN * T ^ δ * br := mul_le_mul_of_nonneg_left h1 (mul_nonneg hCNpos.le hTδnn)
      -- the far part (tail)
      have hfar : (∫ x in ({x : ℝ | |x| ≤ T ^ (δ / 2) * T / M₂})ᶜ,
            ‖Bsum f M₂ x‖ ^ 2 * fejerK M₃ x) ≤ CTl * T ^ δ * br := by
        have hset : ({x : ℝ | |x| ≤ T ^ (δ / 2) * T / M₂})ᶜ
            = {x : ℝ | T ^ (δ / 2) * T / M₂ < |x|} := by
          ext x
          simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
        rw [hset]
        have hfar0 := hTlw T hT1 h2C₀T f hf hfnn hSupp Λ hΛ hdec hΛbd M₂ hM₂1' hM₂T4 M₃ hM₃
        refine hfar0.trans ?_
        calc CTl * M₂ ^ 2 * M₃ * (∫ u, (f u) ^ 2)
            = CTl * (M₂ ^ 2 * M₃ * (∫ u, (f u) ^ 2)) := by ring
          _ ≤ CTl * (T ^ δ * br) := mul_le_mul_of_nonneg_left hmid hCTlpos.le
          _ = CTl * T ^ δ * br := by ring
      -- assembly
      have hwhole := hFw f hf hfnn hSupp M₂ hM₂pos.le M₃ hM₃
      rw [hsplit] at hwhole
      have hsum : (∫ x in {x : ℝ | |x| ≤ T ^ (δ / 2) * T / M₂},
              ‖Bsum f M₂ x‖ ^ 2 * fejerK M₃ x)
            + (∫ x in ({x : ℝ | |x| ≤ T ^ (δ / 2) * T / M₂})ᶜ,
                ‖Bsum f M₂ x‖ ^ 2 * fejerK M₃ x)
          ≤ CN * T ^ δ * br + CTl * T ^ δ * br := add_le_add hnear hfar
      have hwhole' : WinMass f M₂ M₃ ≤ CF * (CN * T ^ δ * br + CTl * T ^ δ * br) :=
        hwhole.trans (mul_le_mul_of_nonneg_left hsum hCFpos.le)
      have hfin : CF * (CN * T ^ δ * br + CTl * T ^ δ * br) = CF * (CN + CTl) * T ^ δ * br := by
        ring
      rw [hfin] at hwhole'
      exact hwhole'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCvalMain hTδnn) hbrnn)

end

end Work.GM.Affine
