import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.mr_direct_defs
import Submission.Work.BMF.mr_direct_range_defs
import Submission.Work.BMF.mr_direct.badDefs
import Submission.Work.BMF.mr_direct.goodSet_bound_range3
import Submission.Work.BMF.mr_direct.goodSet_E1_bound
import Submission.Work.BMF.mr_direct.badGoodArith
import Submission.Work.BMF.mr_direct.badParamsBounds
import Submission.Work.BMF.mr_direct.remPointwiseRange
import Submission.Work.BMF.mr_direct.primeRecipsWindowLE
import Submission.Work.BMF.mr_direct.dist_scale_transfer_wide

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.BMF.mr_direct

open MeasureTheory intervalIntegral
open scoped BigOperators
open BoundedMultiplicativeFunctions

noncomputable section

/-!
# Helpers for the bad-set analysis of the `k = 0` core

This module collects the elementary, already proved ingredients that the bad-set half
`Work.BMF.mr_direct.badSetCore` of the `E_2` decomposition needs:

* `intervalIntegral_le_setIntegral_add` and `setIntegral_eq_add_of_union` — splitting an integral
  at a measurable set and over a disjoint measurable partition;
* `badSetRS_integral_le` — the trivial bound on the `T_S` part of a bad set;
* `remPolyR_badSet_le` — the *pointwise* bound `norm (R_{j,K}(1+it)) <= Delta` on the bad set at
  the bad-set parameters, obtained from `remPointwiseRange` and one application of
  `dist_scale_transfer_wide`;
* `goodSet_part_small_bad` — the good-set half of the decomposition at the bad-set parameters,
  which together with the bad-set half gives `CoreInput`.
-/

theorem intervalIntegral_le_setIntegral_add (f : ℝ → ℝ) (S : ℝ) (G U : Set ℝ)
    (hf : Continuous f) (hfnn : ∀ x, 0 ≤ f x) (hS : 0 ≤ S) (hG : MeasurableSet G)
    (hGsub : G ⊆ Set.Icc (-S) S) (hUsub : U ⊆ Set.Icc (-S) S)
    (hUG : Set.Icc (-S) S \ G ⊆ U) :
    (∫ t in (-S)..S, f t) ≤ (∫ t in G, f t) + (∫ t in U, f t) := by
  have hne : -S ≤ S := by linarith
  rw [intervalIntegral.integral_of_le hne, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hIccInt : MeasureTheory.IntegrableOn f (Set.Icc (-S) S) := hf.integrableOn_Icc
  have hGInt : MeasureTheory.IntegrableOn f G := hIccInt.mono_set hGsub
  have hCInt : MeasureTheory.IntegrableOn f (Set.Icc (-S) S \ G) :=
    hIccInt.mono_set Set.sdiff_subset
  have hUInt : MeasureTheory.IntegrableOn f U := hIccInt.mono_set hUsub
  have hunion : Set.Icc (-S) S = G ∪ (Set.Icc (-S) S \ G) := by
    ext x
    constructor
    · intro hx
      by_cases h : x ∈ G
      · exact Or.inl h
      · exact Or.inr ⟨hx, h⟩
    · rintro (hx | hx)
      · exact hGsub hx
      · exact hx.1
  have hdisj : Disjoint G (Set.Icc (-S) S \ G) :=
    Set.disjoint_left.mpr fun _ hx hx' => hx'.2 hx
  rw [hunion, MeasureTheory.setIntegral_union hdisj (measurableSet_Icc.diff hG) hGInt hCInt]
  refine add_le_add le_rfl ?_
  refine MeasureTheory.setIntegral_mono_set hUInt ?_ ?_
  · exact Filter.Eventually.of_forall (fun x => hfnn x)
  · exact Filter.Eventually.of_forall (fun x hx => hUG hx)

/-- **Pointwise smallness of the remainder polynomial on the whole frequency range.**  At the
bad-set parameters the whole range `|t| ≤ C·(Y/H)/2` (in particular every `|t| ≤ 2T`, by the
hypothesis `4T ≤ C·(Y/H)`) lies inside the Halász window `|u| ≤ C·Y/H` of the statement, so the
range-general remainder bound `Work.BMF.mr_direct.remPointwiseRange` applies at *every* such `t`:
`‖R_{j,K}(1+it)‖ ≤ Δ` with
`Δ = Cw·(log Q/log P)·((1+B₂²)·e^{-B₂²/4} + 1/√(C·(Y/H)/4))`, `B₂ = √(B²/2)`.  In particular it
applies on the whole bad region `Icc (-(2T)) (2T) \ goodSetR`, not only on `badSetR g K (2T) j`.

Only *one* application of the scale transfer `Work.BMF.mr_direct.dist_scale_transfer_wide` is
needed: it gives `𝔻 g (n^{iu}; x) ≥ B₂` for every `x ∈ [Y^{1/8}, 16Y]`, and the hypothesis
`Y^{1/8} ≤ (Y/Q)^{1/4}/16` (`Q = badQ Y`, the largest prime scale) places the scales
`[X^{1/4}/16, 16X]`, `X = Y e^{-j/K} ∈ [Y/Q, Y]`, inside that window. -/
lemma remPolyR_pointwise_le (Cw : ℝ)
    (hCw : ∀ (B : ℝ), 1 ≤ B →
      ∀ (g : ℕ → ℂ) (P Q X X₁ X₂ T₀ t : ℝ),
        g 1 = 1 → (∀ m n : ℕ, m.Coprime n → g (m * n) = g m * g n) →
        (∀ n, ‖g n‖ ≤ 1) → 2 ≤ P → P ≤ Q → 16 ≤ X → X / 4 ≤ X₁ → X₁ ≤ X₂ →
        X₂ ≤ 4 * X → 1 ≤ T₀ →
        (∀ (x : ℝ), X ^ (1/4:ℝ) / 16 ≤ x → x ≤ 16 * X → ∀ u : ℝ, |u| ≤ 4 * T₀ →
          B ≤ BoundedMultiplicativeFunctions.𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * u)) x) →
        (∑ p ∈ Work.BMF.primesIn P Q, 1 / (p : ℝ)) ≤ B ^ 2 / 8 →
        |t| ≤ 2 * T₀ →
        ‖∑ m ∈ Work.BMF.natIcc X₁ X₂,
            g m * (((Work.BMF.mrDirect.omegaCount P Q m : ℕ) + 1 : ℕ) : ℂ)⁻¹ *
              (m : ℂ) ^ (-(1 + Complex.I * t))‖
          ≤ Cw * (Real.log Q / Real.log P) *
              ((1 + B ^ 2) * Real.exp (-(B ^ 2 / 4)) + 1 / Real.sqrt T₀))
    (g : ℕ → ℂ) (a Y H T B C : ℝ) (j : ℕ) (K : ℝ)
    (hg1 : g 1 = 1) (hgmul : ∀ m n : ℕ, m.Coprime n → g (m * n) = g m * g n)
    (hgb : ∀ n, ‖g n‖ ≤ 1)
    (hHpos : 0 < H) (hHY : H ≤ Y) (hC4 : 4 ≤ C) (hYbig : 16 ^ 8 ≤ Y)
    (hB8 : (8 : ℝ) ≤ B)
    (hY16 : 16 ≤ Y) (hYQ16 : (16 : ℝ) ≤ Y / Work.BMF.mr_direct.badQ Y)
    (hloglog : 1 < Real.log (Real.log Y))
    (hscale : Y ^ ((1 : ℝ) / 8) ≤ (Y / Work.BMF.mr_direct.badQ Y) ^ ((1 : ℝ) / 4) / 16)
    (hT4 : 4 * T ≤ C * (Y / H))
    (hdist : ∀ u : ℝ, |u| ≤ C * (Y / H) →
      B ≤ BoundedMultiplicativeFunctions.𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * u)) Y)
    (hSie : (∑ p ∈ Work.BMF.primesIn (Work.BMF.mr_direct.badP a Y)
        (Work.BMF.mr_direct.badQ Y), 1 / (p : ℝ)) ≤ (Real.sqrt (B ^ 2 / 2)) ^ 2 / 8)
    (hP2 : 2 ≤ Work.BMF.mr_direct.badP a Y)
    (hPQ : Work.BMF.mr_direct.badP a Y ≤ Work.BMF.mr_direct.badQ Y)
    (hj : j ∈ Work.BMF.mrDirect.indexSet K (Work.BMF.mr_direct.badP a Y)
      (Work.BMF.mr_direct.badQ Y)) (hK : 2 ≤ K) :

    ∀ t : ℝ, |t| ≤ 2 * (C * (Y / H) / 4) →  ‖Work.BMF.mrDirect.remPolyR g (Work.BMF.mr_direct.badP a Y)
          (Work.BMF.mr_direct.badQ Y) K Y (3 * Y) j t‖
        ≤ Cw * (Real.log (Work.BMF.mr_direct.badQ Y) / Real.log (Work.BMF.mr_direct.badP a Y)) *
            ((1 + (Real.sqrt (B ^ 2 / 2)) ^ 2) * Real.exp (-((Real.sqrt (B ^ 2 / 2)) ^ 2 / 4)) +
              1 / Real.sqrt (C * (Y / H) / 4)) := by
  intro t htabs
  have hYpos : 0 < Y := by linarith
  have hKpos : 0 < K := by linarith
  have hQpos : 0 < Work.BMF.mr_direct.badQ Y := Real.exp_pos _
  have hPpos : 0 < Work.BMF.mr_direct.badP a Y := Real.rpow_pos_of_pos hQpos a
  have hρpos : 0 < Y / H := div_pos hYpos hHpos
  have hlogYpos : 0 < Real.log Y := Real.log_pos (by linarith)
  have hloglogpos : 0 < Real.log (Real.log Y) := by linarith
  have hlogQ : Real.log (Work.BMF.mr_direct.badQ Y)
      = Real.log Y / Real.log (Real.log Y) := by
    rw [Work.BMF.mr_direct.badQ, Real.log_exp]
  have hlogQpos : 0 < Real.log (Work.BMF.mr_direct.badQ Y) := by
    rw [hlogQ]; exact div_pos hlogYpos hloglogpos
  -- `j / K ≤ log Q`
  have hjmem : j ∈ Finset.Icc ⌊K * Real.log (Work.BMF.mr_direct.badP a Y)⌋₊
      ⌊K * Real.log (Work.BMF.mr_direct.badQ Y)⌋₊ := by
    simpa only [Work.BMF.mrDirect.indexSet] using hj
  have hjle : (j : ℝ) ≤ K * Real.log (Work.BMF.mr_direct.badQ Y) := by
    have h1 : j ≤ ⌊K * Real.log (Work.BMF.mr_direct.badQ Y)⌋₊ := (Finset.mem_Icc.mp hjmem).2
    have h2 : (j : ℝ) ≤ ((⌊K * Real.log (Work.BMF.mr_direct.badQ Y)⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast h1
    have h3 : ((⌊K * Real.log (Work.BMF.mr_direct.badQ Y)⌋₊ : ℕ) : ℝ)
        ≤ K * Real.log (Work.BMF.mr_direct.badQ Y) :=
      Nat.floor_le (by positivity)
    linarith
  -- `exp (-1/K) ≥ 1/4`
  have hexp4 : (1 : ℝ) / 4 ≤ Real.exp (-(1 / K)) := by
    have hlog4 : (1 : ℝ) / 2 ≤ Real.log 4 := by
      have h2 := Real.log_two_gt_d9
      have h4 : Real.log (2 : ℝ) ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
      linarith
    have h1K : 1 / K ≤ Real.log 4 := by
      have h2 : 1 / K ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hK
      linarith
    have h := Real.exp_le_exp.mpr (neg_le_neg h1K)
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)] at h
    simpa using h
  have hexpK1 : Real.exp (-(j : ℝ) / K) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg j)) hKpos.le
  have hexp_ge : (1 / Work.BMF.mr_direct.badQ Y) ≤ Real.exp (-(j : ℝ) / K) := by
    have h2 : (j : ℝ) / K ≤ Real.log (Work.BMF.mr_direct.badQ Y) := by
      rw [div_le_iff₀ hKpos]; linarith
    have h1 : -Real.log (Work.BMF.mr_direct.badQ Y) ≤ (-(j : ℝ)) / K := by
      have h3 : (-(j : ℝ)) / K = -((j : ℝ) / K) := by ring
      rw [h3]; linarith
    have h := Real.exp_le_exp.mpr h1
    rw [Real.exp_neg, Real.exp_log hQpos] at h
    rw [one_div]
    exact h
  set X : ℝ := Y * Real.exp (-(j : ℝ) / K) with hXdef
  set X₁ : ℝ := Y * Real.exp (-((j : ℝ) + 1) / K) with hX₁def
  set X₂ : ℝ := 3 * Y * Real.exp (-(j : ℝ) / K) with hX₂def
  have hXpos : 0 < X := by rw [hXdef]; positivity
  have hXleY : X ≤ Y := by
    rw [hXdef]
    calc Y * Real.exp (-(j : ℝ) / K) ≤ Y * 1 :=
          mul_le_mul_of_nonneg_left hexpK1 hYpos.le
      _ = Y := mul_one Y
  have hXge : Y / Work.BMF.mr_direct.badQ Y ≤ X := by
    rw [hXdef]
    calc Y / Work.BMF.mr_direct.badQ Y = Y * (1 / Work.BMF.mr_direct.badQ Y) := by ring
      _ ≤ Y * Real.exp (-(j : ℝ) / K) := mul_le_mul_of_nonneg_left hexp_ge hYpos.le
  have hX16 : 16 ≤ X := le_trans hYQ16 hXge
  have hX₁pos : 0 < X₁ := by rw [hX₁def]; positivity
  have hXq : X / 4 ≤ X₁ := by
    have hsplit : Real.exp (-((j : ℝ) + 1) / K)
        = Real.exp (-(j : ℝ) / K) * Real.exp (-(1 / K)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hXdef, hX₁def, hsplit, div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
    have hYe : 0 < Y * Real.exp (-(j : ℝ) / K) := by positivity
    have hmult := mul_le_mul_of_nonneg_left hexp4 hYe.le
    linarith [hmult]
  have hX12 : X₁ ≤ X₂ := by
    rw [hX₁def, hX₂def]
    have h1 : Real.exp (-((j : ℝ) + 1) / K) ≤ Real.exp (-(j : ℝ) / K) := by
      apply Real.exp_le_exp.mpr
      apply div_le_div_of_nonneg_right _ hKpos.le
      push_cast
      linarith
    calc Y * Real.exp (-((j : ℝ) + 1) / K) ≤ Y * Real.exp (-(j : ℝ) / K) :=
          mul_le_mul_of_nonneg_left h1 hYpos.le
      _ ≤ 3 * Y * Real.exp (-(j : ℝ) / K) := by
          have := Real.exp_pos (-(j : ℝ) / K); nlinarith [hYpos]
  have hX24 : X₂ ≤ 4 * X := by
    rw [hX₂def, hXdef]
    have := Real.exp_pos (-(j : ℝ) / K)
    nlinarith [hYpos]
  have hT0 : (1 : ℝ) ≤ C * (Y / H) / 4 := by
    have hρ1 : 1 ≤ Y / H := (one_le_div hHpos).mpr hHY
    nlinarith
  have hB2ge : (1 : ℝ) ≤ Real.sqrt (B ^ 2 / 2) := by
    have h2 : (1 : ℝ) ≤ B ^ 2 / 2 := by nlinarith
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (B ^ 2 / 2) := Real.sqrt_le_sqrt h2
  have htr := Work.BMF.mr_direct.dist_scale_transfer_wide g hgb B (C * (Y / H)) Y hB8 hYbig hdist
  have hdist' : ∀ x : ℝ, X ^ ((1 : ℝ) / 4) / 16 ≤ x → x ≤ 16 * X →
      ∀ u : ℝ, |u| ≤ 4 * (C * (Y / H) / 4) →
      Real.sqrt (B ^ 2 / 2) ≤ BoundedMultiplicativeFunctions.𝔻 g
        (fun n ↦ (n : ℂ) ^ (Complex.I * u)) x := by
    intro x hx1 hx2 u hu
    have hxlow : Y ^ ((1 : ℝ) / 8) ≤ x := by
      refine le_trans (le_trans hscale ?_) hx1
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact Real.rpow_le_rpow (le_of_lt (div_pos hYpos hQpos)) hXge (by norm_num)
    have hxupp : x ≤ 16 * Y := le_trans hx2 (by nlinarith [hXleY])
    have hu' : |u| ≤ C * (Y / H) := by linarith [hu]
    exact htr x hxlow hxupp u hu'
  have hmain := hCw (Real.sqrt (B ^ 2 / 2)) hB2ge g (Work.BMF.mr_direct.badP a Y)
    (Work.BMF.mr_direct.badQ Y) X X₁ X₂ (C * (Y / H) / 4) t
    hg1 hgmul hgb hP2 hPQ hX16 hXq hX12 hX24 hT0 hdist' hSie htabs
  rw [Work.BMF.mrDirect.remPolyR, ← hX₁def, ← hX₂def]
  exact hmain
/-! ## The `T_S` part of the bad set -/

/-- Additivity of the set integral over a disjoint measurable decomposition `U = A ∪ B`, for a
continuous `f` and `U` bounded. -/

lemma setIntegral_eq_add_of_union {f : ℝ → ℝ} (hf : Continuous f) {S : ℝ} {U A B : Set ℝ}
    (hU : U ⊆ Set.Icc (-S) S) (hA : MeasurableSet A) (hAm : A ⊆ U)
    (hB : MeasurableSet B) (hBm : B ⊆ U) (hUAB : U = A ∪ B) (hdisj : Disjoint A B) :
    (∫ t in U, f t) = (∫ t in A, f t) + (∫ t in B, f t) := by
  have hUInt : MeasureTheory.IntegrableOn f U :=
    (hf.integrableOn_Icc (a := -S) (b := S)).mono_set hU
  have hAInt : MeasureTheory.IntegrableOn f A := hUInt.mono_set hAm
  have hBInt : MeasureTheory.IntegrableOn f B := hUInt.mono_set hBm
  rw [hUAB, MeasureTheory.setIntegral_union hdisj hB hAInt hBInt]

/-- The `T_S` part of the bad set: there `‖Q_{j,K}‖ < Θ`, so the whole integral is at most
`(2S+1)Θ²` (the measure of the interval times the trivial pointwise bound). -/
lemma badSetRS_integral_le (g : ℕ → ℂ) (K S Θ : ℝ) (j : ℕ) (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    (∫ t in Work.BMF.mr_direct.badSetRS g K S Θ j,
        ‖Work.BMF.mrDirect.primePoly g K j t‖ ^ 2) ≤ (2 * S + 1) * Θ ^ 2 := by
  set A : Set ℝ := Work.BMF.mr_direct.badSetRS g K S Θ j with hAdef
  have hAmeas : MeasurableSet A := Work.BMF.mr_direct.measurableSet_badSetRS g K S Θ j
  have hAsub : A ⊆ Set.Icc (-S) S := fun t ht => ht.1.1
  have hIccInt : MeasureTheory.IntegrableOn
      (fun t : ℝ => ‖Work.BMF.mrDirect.primePoly g K j t‖ ^ 2) (Set.Icc (-S) S) :=
    ((Work.BMF.mr_direct.continuous_primePoly g K j).norm.pow 2).integrableOn_Icc
  have hAInt : MeasureTheory.IntegrableOn
      (fun t : ℝ => ‖Work.BMF.mrDirect.primePoly g K j t‖ ^ 2) A :=
    hIccInt.mono_set hAsub
  have hcInt : MeasureTheory.IntegrableOn (fun _ : ℝ => Θ ^ 2) A :=
    continuous_const.integrableOn_Icc.mono_set hAsub
  have hpoint : ∀ t ∈ A, ‖Work.BMF.mrDirect.primePoly g K j t‖ ^ 2 ≤ Θ ^ 2 := by
    intro t ht
    exact pow_le_pow_left₀ (norm_nonneg _) ht.2.le 2
  have h1 : (∫ t in A, ‖Work.BMF.mrDirect.primePoly g K j t‖ ^ 2) ≤ ∫ t in A, Θ ^ 2 :=
    MeasureTheory.setIntegral_mono_on hAInt hcInt hAmeas hpoint
  have h2 : (∫ t in A, (Θ ^ 2 : ℝ)) = (MeasureTheory.volume.real A) * Θ ^ 2 := by
    rw [MeasureTheory.setIntegral_const]
    simp [smul_eq_mul]
  have h3 : MeasureTheory.volume.real A ≤ MeasureTheory.volume.real (Set.Icc (-S) S) :=
    MeasureTheory.measureReal_mono hAsub (by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top)
  have h4 : MeasureTheory.volume.real (Set.Icc (-S) S) = 2 * S := by
    rw [MeasureTheory.measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    ring
  have h5 : (2 * S) * Θ ^ 2 ≤ (2 * S + 1) * Θ ^ 2 := by
    have h6 : (0 : ℝ) ≤ Θ ^ 2 := sq_nonneg Θ
    nlinarith
  calc (∫ t in A, ‖Work.BMF.mrDirect.primePoly g K j t‖ ^ 2)
      ≤ ∫ t in A, Θ ^ 2 := h1
    _ = (MeasureTheory.volume.real A) * Θ ^ 2 := h2
    _ ≤ (2 * S) * Θ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg Θ)
        linarith [le_trans h3 (le_of_eq h4)]
    _ ≤ (2 * S + 1) * Θ ^ 2 := h5

/-! ## The good-set half of the `E_2` decomposition -/

/-- **Good-set half** of the `E_2` (bad-set-parameter) decomposition: the contribution of the
good set `goodSetR g K P Q (2T)` to the decomposition inequality is at most `ε`, at the
parameters `P = badP a Y`, `Q = badQ Y` and any constant resolution `K ≥ 3`.

The proof instantiates the general-range good-set bound
`Work.BMF.mr_direct.goodSet_bound_range3` with `α = 1/4`, `X₁ = Y`, `X₂ = 3Y`, `S = 2T`, and
then uses `2ρ/S ≤ 1` and the arithmetic of `Work.BMF.mr_direct.badGoodArith`. -/
theorem goodSet_part_small_bad (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (ε : ℝ) (hε : 0 < ε)
    (c : ℝ) (hc : 0 < c) (a : ℝ) (ha : 0 < a) (ha2 : a ≤ 1 / 2)
    (K : ℝ) (hK : 3 ≤ K) :
    ∃ X₀ : ℝ, 1 ≤ X₀ ∧ ∀ (Y H T : ℝ) (g : ℕ → ℂ),
      X₀ ≤ Y → Y ^ θ ≤ H → H ≤ Y → 2 * (Y / H) ≤ 2 * T → (∀ n, ‖g n‖ ≤ 1) →
      c * (2 * (Y / H) / (2 * T)) *
        (K * Real.log (Work.BMF.mr_direct.badQ Y / Work.BMF.mr_direct.badP a Y) *
          (∑ j ∈ Work.BMF.mrDirect.indexSet K (Work.BMF.mr_direct.badP a Y)
              (Work.BMF.mr_direct.badQ Y),
            ∫ t in Work.BMF.goodSetR g K (Work.BMF.mr_direct.badP a Y)
                (Work.BMF.mr_direct.badQ Y) (2 * T),
              ‖Work.BMF.mrDirect.primePoly g K j t *
               Work.BMF.mrDirect.remPolyR g (Work.BMF.mr_direct.badP a Y)
                 (Work.BMF.mr_direct.badQ Y) K Y (3 * Y) j t‖ ^ 2))
        ≤ ε := by
  obtain ⟨C₂, hC₂pos, hgsb⟩ := Work.BMF.mr_direct.goodSet_bound_range3
  obtain ⟨Xa, hXa1, har⟩ :=
    Work.BMF.mr_direct.badGoodArith θ hθ₀ hθ₁ a ε (5 * (c * C₂)) K ha ha2 hε
      (by positivity) hK
  obtain ⟨Xp, hXp1, hp⟩ := Work.BMF.mr_direct.badParamsBounds 1 one_pos a ha ha2
  refine ⟨max (max Xa Xp) 16, le_trans hXa1 (le_trans (le_max_left Xa Xp) (le_max_left _ _)), ?_⟩
  intro Y H T g hY hYθ hHY hT2 hg
  have hXaY : Xa ≤ Y := le_trans (le_max_left Xa Xp) (le_trans (le_max_left _ _) hY)
  have hXpY : Xp ≤ Y := le_trans (le_max_right Xa Xp) (le_trans (le_max_left _ _) hY)
  have hY16 : (16 : ℝ) ≤ Y := le_trans (le_max_right _ _) hY
  obtain ⟨_hY16', _hlogY1, _hloglogY1, hP2, hPQ, hQ1, _hlogQlogY, _hPinv⟩ := hp Y hXpY
  have hY1 : (1 : ℝ) ≤ Y := by linarith
  have hYpos : 0 < Y := by linarith
  have hYθpos : 0 < Y ^ θ := Real.rpow_pos_of_pos hYpos θ
  have hHpos : 0 < H := lt_of_lt_of_le hYθpos hYθ
  have hρpos : 0 < Y / H := div_pos hYpos hHpos
  have hTpos : 0 < T := by linarith
  have hSnn : (0 : ℝ) ≤ 2 * T := by linarith
  set P : ℝ := Work.BMF.mr_direct.badP a Y with hPdef
  set Q : ℝ := Work.BMF.mr_direct.badQ Y with hQdef
  have hPpos : 0 < P := by linarith
  have hQpos : 0 < Q := by linarith
  have hlogPpos : 0 < Real.log P := Real.log_pos (by linarith : 1 < P)
  have hlogQpos : 0 < Real.log Q := Real.log_pos (by linarith : 1 < Q)
  -- the good-set bound at `α = 1/4`
  have hgood := hgsb Y (3 * Y) K P Q (2 * T) (1 / 4) g g
    (Work.BMF.goodSetR g K P Q (2 * T))
    hY1 (by linarith) (by linarith) hK hP2 hPQ hSnn (by norm_num) (by norm_num)
    hg hg (fun t ht => ht.1) (fun t ht j hj => ht.2 j hj)
  -- the ratio `log(Q/P)/log(P) = (1-a)/a`
  have hlogP : Real.log P = a * Real.log Q := by
    rw [hPdef, hQdef, Work.BMF.mr_direct.badP]
    exact Real.log_rpow (Real.exp_pos _) a
  have hLnn : 0 ≤ Real.log (Q / P) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hPpos]
    have hPQ1 : P ≤ Q := hPQ
    linarith
  have hρTn : (2 * (Y / H) / (2 * T)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  have hQnn : (0 : ℝ) ≤ Q ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (le_of_lt hQpos) _
  have hPnn : (0 : ℝ) ≤ P ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (le_of_lt hPpos) _
  have hexp1 : (1 : ℝ) - 2 * ((1 : ℝ) / 4) = 1 / 2 := by norm_num
  have hexp2 : -(2 * ((1 : ℝ) / 4)) = -(1 / 2 : ℝ) := by norm_num
  have hcoef5 : (1 : ℝ) + 1 / ((1 : ℝ) / 4) = 5 := by norm_num
  have h3Y : (3 : ℝ) * Y / Y = 3 := by field_simp
  rw [hexp1, hexp2, hcoef5, h3Y] at hgood
  have hYT : (2 * (Y / H) / (2 * T)) * ((2 * T) / Y * Q ^ ((1 : ℝ) / 2)) =
      2 * Q ^ ((1 : ℝ) / 2) / H := by
    rw [← mul_assoc,
      show (2 * (Y / H) / (2 * T)) * ((2 * T) / Y) = 2 / H by field_simp]
    ring
  have hkey : (2 * (Y / H) / (2 * T)) *
        ((2 * T) / Y * Q ^ ((1 : ℝ) / 2) + 3 * P ^ (-(1 / 2 : ℝ)))
      ≤ 2 * Q ^ ((1 : ℝ) / 2) / H + 3 * P ^ (-(1 / 2 : ℝ)) := by
    have h3 : (2 * (Y / H) / (2 * T)) * 3 ≤ 3 := by nlinarith [hρTn]
    have := mul_le_mul_of_nonneg_right h3 hPnn
    rw [mul_add, hYT]
    linarith
  have hscale : 0 ≤ 5 * (c * C₂) * (K + 1) ^ 3 * (Real.log (Q / P) + 1) ^ 2 := by positivity
  have hstep : c * (2 * (Y / H) / (2 * T)) *
      (K * Real.log (Q / P) *
        (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
          ∫ t in Work.BMF.goodSetR g K P Q (2 * T),
            ‖Work.BMF.mrDirect.primePoly g K j t *
             Work.BMF.mrDirect.remPolyR g P Q K Y (3 * Y) j t‖ ^ 2))
      ≤ 5 * (c * C₂) * (K + 1) ^ 3 * (Real.log (Q / P) + 1) ^ 2 *
          (2 * Q ^ ((1 : ℝ) / 2) / H + 3 * P ^ (-(1 / 2 : ℝ))) := by
    have hcoef : (0 : ℝ) ≤ c * (2 * (Y / H) / (2 * T)) := by positivity
    calc c * (2 * (Y / H) / (2 * T)) *
          (K * Real.log (Q / P) *
            (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
              ∫ t in Work.BMF.goodSetR g K P Q (2 * T),
                ‖Work.BMF.mrDirect.primePoly g K j t *
                 Work.BMF.mrDirect.remPolyR g P Q K Y (3 * Y) j t‖ ^ 2))
        ≤ c * (2 * (Y / H) / (2 * T)) *
            (C₂ * 5 * (K + 1) ^ 3 * (Real.log (Q / P) + 1) ^ 2 *
              ((2 * T) / Y * Q ^ ((1 : ℝ) / 2) + 3 * P ^ (-(1 / 2 : ℝ)))) :=
          mul_le_mul_of_nonneg_left hgood hcoef
      _ = 5 * (c * C₂) * (K + 1) ^ 3 * (Real.log (Q / P) + 1) ^ 2 *
            ((2 * (Y / H) / (2 * T)) *
              ((2 * T) / Y * Q ^ ((1 : ℝ) / 2) + 3 * P ^ (-(1 / 2 : ℝ)))) := by ring
      _ ≤ 5 * (c * C₂) * (K + 1) ^ 3 * (Real.log (Q / P) + 1) ^ 2 *
            (2 * Q ^ ((1 : ℝ) / 2) / H + 3 * P ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hkey hscale
  have hfin := har Y H hXaY hYθ hHY
  rw [← hPdef, ← hQdef] at hfin
  exact le_trans hstep hfin

end

end Work.BMF.mr_direct
