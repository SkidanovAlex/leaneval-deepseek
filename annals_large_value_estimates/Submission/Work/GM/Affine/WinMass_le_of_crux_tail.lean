import Mathlib
import Submission.Work.GM.Affine.WinMass_basic
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.region_II_defs
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.Gfun_sq_ge_coherence

/-!
# `Work.GM.Affine.WinMass_le_of_crux_tail`

Assembly of the region-II window mass from the two analytic inputs of GM §9:

* `hcrux` (the "spike window" bound, `Work.GM.Affine.Hsum_spike_window`) controls the
  `psi1`-weighted sum `∑_ℓ psi1 1 (M₂ℓ/(K T)) ∫_{[-2,2]} ‖H_ℓ‖²` over *all* ℓ; since
  `psi1 1 (x) = 1` for `|x| ≤ 1`, this covers the "near" range `|ℓ| ≤ K T / M₂`;
* `htail` (the "large `ℓ`" bound, `Work.GM.Affine.WinMass_tail_finset_le`) controls any finite
  set of ℓ with `|ℓ| > K T / M₂`.

Here we show that the two together bound the full window mass `WinMass f M₂ M₃`:

`WinMass f M₂ M₃ ≤ C T^δ M₂ √(∫f²) √(∫Gfun²)`.

The proof chooses `K = 8`, splits an arbitrary finite set of ℓ into the near part
(`|ℓ| ≤ 8T/M₂`) and the far part (`|ℓ| > 8T/M₂`), and then passes to the sum over all ℓ using
the `ENNReal` supremum description of a sum of non-negative terms — no summability of the
window masses is needed, because a non-summable non-negative family has real `tsum = 0`
(the Lean convention), for which the claim is trivial.

In the head part the Cauchy–Schwarz inequality `∫ f · Gfun ≤ √(∫f²) √(∫Gfun²)`
(`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`, `p = q = 2`) replaces the `∫ f Gfun` of
the crux by the two `L²` norms of the target.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.GM.Affine

noncomputable section

/-! ## Elementary facts about `Gfun` -/

private lemma Gfun_continuous' {C₀ T M₂ : ℝ} {f : ℝ → ℝ} (hT : 0 < T) (hf : Continuous f)
    (hfcs : HasCompactSupport f) :
    Continuous (fun u : ℝ => Gfun C₀ T M₂ f u) := by
  have hsmcont : Continuous (smoothed psiSmooth T f) :=
    (smoothed_psiSmooth_fourier hT hf hfcs).1
  rw [show (fun u : ℝ => Gfun C₀ T M₂ f u) = fun u : ℝ =>
      ∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂, ∑ j ∈ Finset.Icc (-⌊2 * C₀ * M₂⌋) ⌊2 * C₀ * M₂⌋,
        smoothed psiSmooth T f (((m₂ : ℝ) * u + (j : ℝ)) / (m₂' : ℝ)) from
    funext (fun u => by rw [Gfun])]
  refine continuous_finsetSum _ (fun m₂ _ => continuous_finsetSum _ (fun m₂' _ =>
    continuous_finsetSum _ (fun j _ => ?_)))
  exact hsmcont.comp (((continuous_const.mul continuous_id).add continuous_const).div_const _)

private lemma Gfun_hasCompactSupport' {C₀ T M₂ : ℝ} (hC₀ : 1 ≤ C₀) (hT : 1 ≤ T) (hM₂ : 1 ≤ M₂)
    {f : ℝ → ℝ} (hSupp : SuppHyp C₀ f) :
    HasCompactSupport (fun u : ℝ => Gfun C₀ T M₂ f u) :=
  HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-(2 * C₀ + 1)) (4 * C₀ + 1))
    isCompact_Icc (fun u hu => Gfun_supp_subset hC₀ hT hM₂ hSupp u hu)

private lemma Gfun_nonneg' {T : ℝ} (hT : 0 < T) {f : ℝ → ℝ} (hfnn : ∀ u, 0 ≤ f u) (C₀ M₂ : ℝ) :
    ∀ u, 0 ≤ Gfun C₀ T M₂ f u := by
  intro u
  rw [show Gfun C₀ T M₂ f u = ∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂,
      ∑ j ∈ Finset.Icc (-⌊2 * C₀ * M₂⌋) ⌊2 * C₀ * M₂⌋,
        smoothed psiSmooth T f (((m₂ : ℝ) * u + (j : ℝ)) / (m₂' : ℝ)) from by rw [Gfun]]
  exact Finset.sum_nonneg (fun m₂ _ => Finset.sum_nonneg (fun m₂' _ =>
    Finset.sum_nonneg (fun j _ => smoothed_psiSmooth_nonneg hT hfnn _)))

theorem WinMass_le_of_crux_tail {C₀ : ℝ} (hC₀ : 1 ≤ C₀) (c : ℕ → ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hcrux : ∃ C : ℝ, 0 < C ∧
      ∀ T : ℝ, 1 ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        ∀ M₂ M₃ K : ℝ, 1 ≤ M₂ → 1 ≤ M₃ → 8 ≤ K →
          (∑' ℓ : ℤ, (psi1 1 ((M₂ * (ℓ : ℝ)) / (K * T)) : ℝ) *
              ∫ τ in Set.Icc (-2 : ℝ) 2, ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2)
            ≤ C * T ^ δ * K * M₂ * (∫ u, f u * Gfun C₀ T M₂ f u))
    (htail : ∃ C : ℝ, 0 < C ∧
      ∀ T : ℝ, 1 ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        ∀ Λ : ℝ, 0 < Λ →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
        ∀ M₂ M₃ K : ℝ, 1 ≤ M₂ → 1 ≤ M₃ → M₂ ≤ T ^ 4 → 8 ≤ K →
        ∀ s : Finset ℤ, (∀ ℓ ∈ s, K * T / M₂ < |(ℓ : ℝ)|) →
          (∑ ℓ ∈ s, ∫ τ in Set.Icc (-2 : ℝ) 2, ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2)
            ≤ C * T ^ δ * M₂ * Real.sqrt (∫ u, (f u) ^ 2) *
                Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ T : ℝ, 1 ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        ∀ Λ : ℝ, 0 < Λ →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
        ∀ Mbig M₂ M₃ : ℝ, 1 ≤ Mbig → Mbig ≤ T ^ 4 → 1 ≤ M₃ → M₃ ≤ Mbig →
        1 ≤ M₂ → M₂ ≤ Mbig →
        WinMass f M₂ M₃ ≤
          C * T ^ δ * M₂ * Real.sqrt (∫ u, (f u) ^ 2) *
            Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2) := by
  obtain ⟨C₁, hC₁pos, hcrux'⟩ := hcrux
  obtain ⟨C₂, hC₂pos, htail'⟩ := htail
  refine ⟨8 * C₁ + C₂, by positivity, ?_⟩
  intro T hT f hf hfnn hSupp Λ hΛ hdecay hΛbd Mbig M₂ M₃ hMbig hMbigT hM₃ hM₃M hM₂ hM₂M
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hTδnn : 0 ≤ T ^ δ := Real.rpow_nonneg hTpos.le δ
  have hM₂pos : 0 < M₂ := lt_of_lt_of_le zero_lt_one hM₂
  have hM₂T4 : M₂ ≤ T ^ 4 := le_trans hM₂M hMbigT
  set SX : ℝ := Real.sqrt (∫ u, (f u) ^ 2) with hSXdef
  set SG : ℝ := Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2) with hSGdef
  set P : ℝ := M₂ * SX * SG with hPdef
  have hSXnn : 0 ≤ SX := by rw [hSXdef]; exact Real.sqrt_nonneg _
  have hSGnn : 0 ≤ SG := by rw [hSGdef]; exact Real.sqrt_nonneg _
  have hPnn : 0 ≤ P := by rw [hPdef]; positivity
  have hBnn : 0 ≤ (8 * C₁ + C₂) * T ^ δ * P := by positivity
  have hfcs : HasCompactSupport f := hasCompactSupport_of_suppHyp hC₀ hSupp
  have hGcont : Continuous (fun u : ℝ => Gfun C₀ T M₂ f u) := Gfun_continuous' hTpos hf hfcs
  have hGcs : HasCompactSupport (fun u : ℝ => Gfun C₀ T M₂ f u) :=
    Gfun_hasCompactSupport' hC₀ hT hM₂ hSupp
  have hGnn : ∀ u, 0 ≤ Gfun C₀ T M₂ f u := Gfun_nonneg' hTpos hfnn C₀ M₂
  -- Cauchy--Schwarz: `∫ f · Gfun ≤ √(∫f²) √(∫Gfun²)`
  have hCS : ∫ u, f u * Gfun C₀ T M₂ f u ≤ SX * SG := by
    rw [hSXdef, hSGdef]
    have hfm : MemLp f (ENNReal.ofReal (2:ℝ)) volume := hf.memLp_of_hasCompactSupport hfcs
    have hgm : MemLp (fun u : ℝ => Gfun C₀ T M₂ f u) (ENNReal.ofReal (2:ℝ)) volume :=
      hGcont.memLp_of_hasCompactSupport hGcs
    have h := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) (p := 2) (q := 2)
      (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
      (Filter.Eventually.of_forall hfnn) (Filter.Eventually.of_forall hGnn) hfm hgm
    simp only [Real.rpow_ofNat] at h
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h
    exact h
  set A : ℤ → ℝ := fun ℓ => ∫ τ in Set.Icc (-2:ℝ) 2, ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 with hAdef
  have hAnn : ∀ ℓ : ℤ, 0 ≤ A ℓ := fun ℓ =>
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun τ _ => sq_nonneg _)
  have hWinMass : WinMass f M₂ M₃ = ∑' ℓ : ℤ, A ℓ := rfl
  have hbound : WinMass f M₂ M₃ ≤ (8 * C₁ + C₂) * T ^ δ * P := by
    by_cases hsum : Summable A
    · -- the weighted family is summable by comparison with `A`
      have hWA : Summable (fun ℓ : ℤ => (psi1 1 ((M₂ * (ℓ : ℝ)) / (8 * T)) : ℝ) * A ℓ) :=
        Summable.of_nonneg_of_le (fun ℓ => mul_nonneg (psi1_nonneg 1 _) (hAnn ℓ))
          (fun ℓ => mul_le_of_le_one_left (hAnn ℓ) (psi1_le_one 1 _)) hsum
      -- the head bound from the crux hypothesis, with `K = 8`
      have hhead_tsum : (∑' ℓ : ℤ, (psi1 1 ((M₂ * (ℓ : ℝ)) / (8 * T)) : ℝ) * A ℓ)
          ≤ 8 * C₁ * T ^ δ * P := by
        have hcr := hcrux' T hT f hf hfnn hSupp M₂ M₃ 8 hM₂ hM₃ (by norm_num : (8:ℝ) ≤ 8)
        have h1 : (∑' ℓ : ℤ, (psi1 1 ((M₂ * (ℓ : ℝ)) / (8 * T)) : ℝ) * A ℓ)
            ≤ C₁ * T ^ δ * 8 * M₂ * (∫ u, f u * Gfun C₀ T M₂ f u) := by
          simpa only [hAdef] using hcr
        calc (∑' ℓ : ℤ, (psi1 1 ((M₂ * (ℓ : ℝ)) / (8 * T)) : ℝ) * A ℓ)
            ≤ C₁ * T ^ δ * 8 * M₂ * (∫ u, f u * Gfun C₀ T M₂ f u) := h1
          _ ≤ C₁ * T ^ δ * 8 * M₂ * (SX * SG) := mul_le_mul_of_nonneg_left hCS (by positivity)
          _ = 8 * C₁ * T ^ δ * P := by rw [hPdef]; ring
      -- finite-set bound: near part by the crux weight, far part by the tail hypothesis
      have hfin : ∀ s : Finset ℤ, ∑ ℓ ∈ s, A ℓ ≤ (8 * C₁ + C₂) * T ^ δ * P := by
        intro s
        have hsplit : ∑ ℓ ∈ s, A ℓ
            = (∑ ℓ ∈ s.filter (fun ℓ : ℤ => |(ℓ:ℝ)| ≤ 8 * T / M₂), A ℓ)
              + ∑ ℓ ∈ s.filter (fun ℓ : ℤ => ¬ (|(ℓ:ℝ)| ≤ 8 * T / M₂)), A ℓ :=
          (Finset.sum_filter_add_sum_filter_not s (fun ℓ : ℤ => |(ℓ:ℝ)| ≤ 8 * T / M₂) A).symm
        have hhead_le : (∑ ℓ ∈ s.filter (fun ℓ : ℤ => |(ℓ:ℝ)| ≤ 8 * T / M₂), A ℓ)
            ≤ ∑ ℓ ∈ s, (psi1 1 ((M₂ * (ℓ : ℝ)) / (8 * T)) : ℝ) * A ℓ := by
          have h1 : (∑ ℓ ∈ s.filter (fun ℓ : ℤ => |(ℓ:ℝ)| ≤ 8 * T / M₂), A ℓ)
              = ∑ ℓ ∈ s.filter (fun ℓ : ℤ => |(ℓ:ℝ)| ≤ 8 * T / M₂),
                  (psi1 1 ((M₂ * (ℓ : ℝ)) / (8 * T)) : ℝ) * A ℓ := by
            refine Finset.sum_congr rfl (fun ℓ hℓ => ?_)
            have hℓp : |(ℓ:ℝ)| ≤ 8 * T / M₂ := (Finset.mem_filter.mp hℓ).2
            have h8T : (0:ℝ) < 8 * T := by linarith
            have hle : M₂ * |(ℓ:ℝ)| ≤ 8 * T := by
              have h := mul_le_mul_of_nonneg_left hℓp hM₂pos.le
              rwa [mul_div_cancel₀ (8 * T) (ne_of_gt hM₂pos)] at h
            have hw : (psi1 1 ((M₂ * (ℓ : ℝ)) / (8 * T)) : ℝ) = 1 := by
              apply psi1_eq_one
              rw [abs_div, abs_mul, abs_of_pos hM₂pos, abs_of_pos h8T]
              rw [div_le_one h8T]
              exact hle
            rw [hw, one_mul]
          rw [h1]
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun ℓ _ _ => mul_nonneg (psi1_nonneg 1 _) (hAnn ℓ))
        have htail_le : (∑ ℓ ∈ s.filter (fun ℓ : ℤ => ¬ (|(ℓ:ℝ)| ≤ 8 * T / M₂)), A ℓ)
            ≤ C₂ * T ^ δ * P := by
          have habs : ∀ ℓ ∈ s.filter (fun ℓ : ℤ => ¬ (|(ℓ:ℝ)| ≤ 8 * T / M₂)),
              (8:ℝ) * T / M₂ < |(ℓ:ℝ)| :=
            fun ℓ hℓ => not_le.mp (Finset.mem_filter.mp hℓ).2
          have h := htail' T hT f hf hfnn hSupp Λ hΛ hdecay hΛbd M₂ M₃ 8 hM₂ hM₃ hM₂T4
            (by norm_num : (8:ℝ) ≤ 8) (s.filter (fun ℓ : ℤ => ¬ (|(ℓ:ℝ)| ≤ 8 * T / M₂))) habs
          rw [← hAdef] at h
          calc (∑ ℓ ∈ s.filter (fun ℓ : ℤ => ¬ (|(ℓ:ℝ)| ≤ 8 * T / M₂)), A ℓ)
              ≤ C₂ * T ^ δ * M₂ * Real.sqrt (∫ u, (f u) ^ 2) *
                  Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2) := h
            _ = C₂ * T ^ δ * P := by rw [hPdef, hSXdef, hSGdef]; ring
        calc ∑ ℓ ∈ s, A ℓ
            = (∑ ℓ ∈ s.filter (fun ℓ : ℤ => |(ℓ:ℝ)| ≤ 8 * T / M₂), A ℓ)
              + ∑ ℓ ∈ s.filter (fun ℓ : ℤ => ¬ (|(ℓ:ℝ)| ≤ 8 * T / M₂)), A ℓ := hsplit
          _ ≤ (∑ ℓ ∈ s, (psi1 1 ((M₂ * (ℓ : ℝ)) / (8 * T)) : ℝ) * A ℓ) + C₂ * T ^ δ * P :=
              add_le_add hhead_le htail_le
          _ ≤ (∑' ℓ : ℤ, (psi1 1 ((M₂ * (ℓ : ℝ)) / (8 * T)) : ℝ) * A ℓ) + C₂ * T ^ δ * P :=
              add_le_add (hWA.sum_le_tsum s (fun ℓ _ => mul_nonneg (psi1_nonneg 1 _) (hAnn ℓ)))
                le_rfl
          _ ≤ 8 * C₁ * T ^ δ * P + C₂ * T ^ δ * P := add_le_add hhead_tsum le_rfl
          _ = (8 * C₁ + C₂) * T ^ δ * P := by ring
      -- pass from finite sets to the (possibly divergent) sum over all of `ℤ`
      have hmain : ENNReal.ofReal (WinMass f M₂ M₃)
          ≤ ENNReal.ofReal ((8 * C₁ + C₂) * T ^ δ * P) := by
        rw [hWinMass, ENNReal.ofReal_tsum_of_nonneg (fun ℓ => hAnn ℓ) hsum,
          ENNReal.tsum_eq_iSup_sum]
        refine iSup_le fun s => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg (fun ℓ _ => hAnn ℓ)]
        exact (ENNReal.ofReal_le_ofReal_iff hBnn).mpr (hfin s)
      exact (ENNReal.ofReal_le_ofReal_iff hBnn).mp hmain
    · -- if the window masses are not summable their `ℝ`-valued sum is `0`
      have hzero : WinMass f M₂ M₃ = 0 := by
        rw [hWinMass]; exact tsum_eq_zero_of_not_summable hsum
      rw [hzero]
      exact hBnn
  calc WinMass f M₂ M₃ ≤ (8 * C₁ + C₂) * T ^ δ * P := hbound
    _ = (8 * C₁ + C₂) * T ^ δ * M₂ * Real.sqrt (∫ u, (f u) ^ 2) *
          Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2) := by rw [hPdef, hSXdef, hSGdef]; ring

end

end Work.GM.Affine
