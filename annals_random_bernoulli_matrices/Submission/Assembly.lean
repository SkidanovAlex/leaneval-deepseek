import Mathlib
import Submission.NetAssemble
import Submission.IncompSide
import Submission.NormalCompress
import Submission.NetUniform
import Submission.GeoBridge
import Submission.Helpers
import Submission.Commons.Analysis.Real.mul_nat_mul_pow_le_one
import Submission.Commons.Analysis.Real.mul_pow_le_one
import Submission.Commons.Probability.Bernoulli.map_affine
import Submission.Commons.Probability.Bernoulli.rademacher_det_lower

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3000000

noncomputable section

universe u

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Measure Filter unitInterval

namespace Submission.Assembly

attribute [local instance] Classical.propDecidable

open Submission.Section5D (Acoord holeN)
open Submission.IncompReduction (normalLe shiftMatrix)
open Submission.NetArgument (Dset slopeOk qSum cSlope)
open Commons.LinearAlgebra.Net (sqNorm compressible)

/-- A law on Bernoulli entries on a nonempty index type is a probability measure. -/
lemma isProbabilityMeasure_of_hasLaw {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    {n : ℕ} (hn : 1 ≤ n) {p : I} {B : Ω → Matrix (Fin n) (Fin n) ℝ}
    (hBlaw : ∀ i j : Fin n, HasLaw (B · i j) (bernoulliMeasure 1 0 p) P) :
    IsProbabilityMeasure P := by
  haveI : IsProbabilityMeasure (bernoulliMeasure (1:ℝ) (0:ℝ) p) := inferInstance
  have hi : Fin n := ⟨0, by omega⟩
  have hl := hBlaw hi hi
  have h1 : (P.map (fun ω => B ω hi hi)) Set.univ = P Set.univ :=
    Measure.map_apply_of_aemeasurable hl.aemeasurable MeasurableSet.univ
  have h2 : (P.map (fun ω => B ω hi hi)) Set.univ = 1 := by
    rw [hl.map_eq]; exact measure_univ
  exact ⟨by rw [← h1, h2]⟩

/-- A law on Bernoulli-like entries (`μ` a probability measure) gives a probability measure. -/
lemma isProbabilityMeasure_of_hasLaw_gen {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    {n : ℕ} (hn : 1 ≤ n) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {B : Ω → Matrix (Fin n) (Fin n) ℝ}
    (hBlaw : ∀ i j : Fin n, HasLaw (B · i j) μ P) : IsProbabilityMeasure P := by
  have hi : Fin n := ⟨0, by omega⟩
  have hl := hBlaw hi hi
  have h1 : (P.map (fun ω => B ω hi hi)) Set.univ = P Set.univ :=
    Measure.map_apply_of_aemeasurable hl.aemeasurable MeasurableSet.univ
  have h2 : (P.map (fun ω => B ω hi hi)) Set.univ = 1 := by
    rw [hl.map_eq]; exact measure_univ
  exact ⟨by rw [← h1, h2]⟩

/-- `c * exp(-M) ≤ K` for `M` large. -/
lemma exists_exp_neg_mul_le {c : ℝ} (hc : 0 ≤ c) {K : ℝ} (hK : 0 < K) :
    ∃ M : ℝ, 1 ≤ M ∧ c * Real.exp (-M) ≤ K := by
  rcases eq_or_lt_of_le hc with h | h
  · exact ⟨1, le_refl 1, by rw [show c = 0 by linarith, zero_mul]; exact hK.le⟩
  refine ⟨max 1 (Real.log (c / K) + 1), le_max_left _ _, ?_⟩
  have h1 : Real.exp (-(max 1 (Real.log (c / K) + 1))) ≤ Real.exp (-(Real.log (c / K) + 1)) :=
    Real.exp_le_exp.mpr (by linarith [le_max_right (1:ℝ) (Real.log (c / K) + 1)])
  have h2 : Real.exp (-(Real.log (c / K) + 1)) = K / (c * Real.exp 1) := by
    have hcK : 0 < c / K := by positivity
    rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_log hcK, Real.exp_neg]
    field_simp
  calc c * Real.exp (-(max 1 (Real.log (c / K) + 1)))
      ≤ c * Real.exp (-(Real.log (c / K) + 1)) := mul_le_mul_of_nonneg_left h1 hc
    _ = c * (K / (c * Real.exp 1)) := by rw [h2]
    _ = K / Real.exp 1 := by field_simp
    _ ≤ K := by
        rw [div_le_iff₀ (Real.exp_pos 1)]
        nlinarith [Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1), hK]


/-- The spectral event with a *universal* constant `C`. -/
lemma spectral_event_exists {n : ℕ} (hn1 : 1 ≤ n) {p : I} {C : ℝ} (hC1 : 1 ≤ C)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hBmeas : ∀ i j : Fin n, Measurable (fun ω => B ω i j))
    (hBind : ProbabilityTheory.iIndepFun (fun x : Fin n × Fin n => (B · x.1 x.2)) P)
    (hBlaw : ∀ i j : Fin n, HasLaw (B · i j) (bernoulliMeasure 1 0 p) P)
    (hBpt : ∀ (i j : Fin n) (ω : Ω), |B ω i j - (p : ℝ)| ≤ 1)
    (hrect : ∀ (n : ℕ), 1 ≤ n → ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (A : Ω → Fin (n - 1) → Fin n → ℝ),
      (∀ k j, Measurable (fun ω => A ω k j)) →
      (ProbabilityTheory.iIndepFun (fun kj : Fin (n - 1) × Fin n => (A · kj.1 kj.2)) P) →
      (∀ (k : Fin (n - 1)) (j : Fin n) (ω : Ω), |A ω k j| ≤ 1) →
      (∀ k j, ∫ ω, A ω k j ∂P = 0) →
      ∃ G : Set Ω, MeasurableSet G ∧ P.real G ≥ 1 - Real.exp (-(1 : ℝ) * (n : ℝ)) ∧
        G ⊆ {ω : Ω | ∀ x : Fin n → ℝ,
          (∑ k : Fin (n - 1), ((∑ j : Fin n, A ω k j * x j)) ^ 2)
            ≤ (C * 1 * Real.sqrt (n : ℝ)) ^ 2 * (∑ i : Fin n, (x i) ^ 2)}) :
    ∃ G : Set Ω, MeasurableSet G ∧ P.real G ≥ 1 - Real.exp (-(1 : ℝ) * (n : ℝ)) ∧
      G ⊆ {ω : Ω | ∀ v : Fin n → ℝ,
        (∑ k : Fin (n - 1),
            ((∑ i : Fin n, (B ω i (Submission.GeoBridge.emb k) - (p : ℝ)) * v i)) ^ 2)
          ≤ (C * Real.sqrt (n : ℝ)) ^ 2 * (∑ i : Fin n, (v i) ^ 2)} := by
  have hAmeas : ∀ k : Fin (n - 1), ∀ j : Fin n,
      Measurable (fun ω : Ω => B ω j (Submission.GeoBridge.emb k) - (p : ℝ)) :=
    fun k j => (hBmeas j (Submission.GeoBridge.emb k)).sub measurable_const
  have hAind : ProbabilityTheory.iIndepFun
      (fun kj : Fin (n - 1) × Fin n =>
        fun ω : Ω => B ω kj.2 (Submission.GeoBridge.emb kj.1) - (p : ℝ)) P := by
    have hg : Function.Injective
        (fun kj : Fin (n - 1) × Fin n => (kj.2, Submission.GeoBridge.emb kj.1)) := by
      intro a b h
      have h1 : a.2 = b.2 := congrArg Prod.fst h
      have h2 : Submission.GeoBridge.emb a.1 = Submission.GeoBridge.emb b.1 :=
        congrArg Prod.snd h
      have h3 : a.1 = b.1 := Submission.GeoBridge.emb_injective h2
      exact Prod.ext h3 h1
    have hpre := ProbabilityTheory.iIndepFun.precomp
      (f := fun x : Fin n × Fin n => (B · x.1 x.2))
      (g := fun kj : Fin (n - 1) × Fin n => (kj.2, Submission.GeoBridge.emb kj.1)) hg hBind
    have hcomp := ProbabilityTheory.iIndepFun.comp hpre
      (fun _ : Fin (n - 1) × Fin n => fun t : ℝ => t - (p : ℝ)) (fun _ => by fun_prop)
    have hfun : (fun kj : Fin (n - 1) × Fin n =>
        ((fun t : ℝ => t - (p : ℝ)) ∘
          (fun ω : Ω => B ω kj.2 (Submission.GeoBridge.emb kj.1))))
      = (fun kj : Fin (n - 1) × Fin n => fun ω : Ω =>
          B ω kj.2 (Submission.GeoBridge.emb kj.1) - (p : ℝ)) := by
      funext kj ω
      simp [Function.comp_apply]
    rwa [hfun] at hcomp
  have hAb : ∀ (k : Fin (n - 1)) (j : Fin n) (ω : Ω),
      |B ω j (Submission.GeoBridge.emb k) - (p : ℝ)| ≤ 1 :=
    fun k j ω => hBpt j (Submission.GeoBridge.emb k) ω
  have hAm : ∀ (k : Fin (n - 1)) (j : Fin n),
      ∫ ω, (B ω j (Submission.GeoBridge.emb k) - (p : ℝ)) ∂P = 0 := by
    intro k j
    have h1 : ∫ ω, B ω j (Submission.GeoBridge.emb k) ∂P = (p : ℝ) :=
      Submission.CompressProp.bernoulli_integral P (hBlaw j (Submission.GeoBridge.emb k))
    have hint : Integrable (fun ω : Ω => B ω j (Submission.GeoBridge.emb k)) P :=
      Integrable.of_bound (hBmeas j (Submission.GeoBridge.emb k)).aestronglyMeasurable 2
        (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_le]
          have hp01 : (0 : ℝ) ≤ (p : ℝ) := p.2.1
          have hp12 : (p : ℝ) ≤ 1 := p.2.2
          have := hBpt j (Submission.GeoBridge.emb k) ω
          rw [abs_le] at this
          constructor <;> linarith [this.1, this.2])
    rw [integral_sub hint (integrable_const ((p : ℝ))), h1]
    simp
  obtain ⟨G, hGmeas, hGprob, hGsub⟩ := hrect n hn1 P
    (fun ω k j => B ω j (Submission.GeoBridge.emb k) - (p : ℝ)) hAmeas hAind hAb hAm
  exact ⟨G, hGmeas, hGprob, fun ω hω => by simpa using hGsub hω⟩


/-- **Theorem A** in the `∃N ∃C` form (law-only hypotheses). -/
theorem theorem_A_bound {p : I} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ C : ℝ, 0 < C ∧
      ∀ n ≥ N, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (B : Ω → Matrix (Fin n) (Fin n) ℝ)
        (hBind : ProbabilityTheory.iIndepFun (fun x : Fin n × Fin n => (B · x.1 x.2)) P)
        (hBlaw : ∀ i j : Fin n, HasLaw (B · i j) (bernoulliMeasure 1 0 p) P),
        ∀ s : ℝ, -1 ≤ s → s ≤ 0 → ∀ t : ℝ, 0 < t →
          P.real {ω : Ω | RandomBernoulliMatrices.σ_min
              (B ω + Matrix.of (fun _ _ : Fin n => s)) ≤ t / Real.sqrt (n : ℝ)}
            ≤ (1 - (p : ℝ) + ε) ^ n + C * t := by
  classical
  by_cases htriv : 1 ≤ 1 - (p : ℝ) + ε
  · refine ⟨2, by norm_num, 1, one_pos, ?_⟩
    intro n hn Ω _ P B hBind hBlaw s hs1 hs2 t ht
    have hn1 : 1 ≤ n := le_trans (by norm_num) hn
    haveI := isProbabilityMeasure_of_hasLaw P hn1 hBlaw
    calc P.real {ω : Ω | RandomBernoulliMatrices.σ_min
            (B ω + Matrix.of (fun _ _ : Fin n => s)) ≤ t / Real.sqrt (n : ℝ)}
        ≤ 1 := MeasureTheory.measureReal_le_one
      _ ≤ (1 - (p : ℝ) + ε) ^ n := one_le_pow₀ htriv
      _ ≤ (1 - (p : ℝ) + ε) ^ n + 1 * t := by linarith [ht.le]
  push_neg at htriv
  -- parameters
  set ee : ℝ := min (ε / 4) ((p : ℝ) / 2) with hee_def
  have hee0 : 0 < ee := lt_min (by linarith) (by linarith)
  have hee_lt_p : ee < (p : ℝ) := by
    rw [hee_def]
    calc min (ε / 4) ((p : ℝ) / 2) ≤ (p : ℝ) / 2 := min_le_right _ _
      _ < (p : ℝ) := by linarith
  have hee_le : ee ≤ ε / 4 := by rw [hee_def]; exact min_le_left _ _
  set a : ℝ := 1 - (p : ℝ) + ee with ha_def
  have ha0 : 0 < a := by rw [ha_def]; linarith
  have hahalf : 1 / 2 ≤ a := by rw [ha_def]; linarith
  have ha1 : a < 1 := by rw [ha_def]; linarith
  -- constants
  obtain ⟨n₁, hn₁2, γ₀, hγ₀, δ₁, hδ₁0, hδ₁1, ν₁, hν₁0, hν₁1, hinc⟩ :=
    Submission.IncompSide.sigma_min_le_normal_bound hp₀ hp₁ hee0
  obtain ⟨n₂, hn₂2, δ₂, hδ₂0, hδ₂1, ν₂, hν₂0, hν₂1, hcomp₂⟩ :=
    Submission.NormalCompress.normal_compressible_le hp₀ hp₁ hee0
  set δ : ℝ := min δ₂ (1 / 2) with hδ_def
  set ν : ℝ := min ν₂ 1 with hν_def
  have hδ0 : 0 < δ := lt_min hδ₂0 (by norm_num)
  have hδ12 : δ ≤ 1 / 2 := min_le_right _ _
  have hδ_le : δ ≤ δ₂ := min_le_left _ _
  have hν0 : 0 < ν := lt_min hν₂0 (by norm_num)
  have hν1 : ν ≤ 1 := min_le_right _ _
  have hν_le : ν ≤ ν₂ := min_le_left _ _
  obtain ⟨K, L₀, hK0, hL₀1, hthr⟩ :=
    Submission.Threshold.threshold_le_K_div_sqrt_of_incompressible hp₀ hp₁ hδ0 hν0
  obtain ⟨CPerm, hCP1, hperm⟩ :=
    Submission.NetUniform.cor_permutations_uniform hδ0 hδ12 hν0 hν1
  obtain ⟨LAC, hLACpos, KA, hKA1, hDset⟩ :=
    Submission.NetAssemble.Dset_card_le_M hp₀ hp₁ hee0 hee_lt_p hδ0 hδ12 hν0 hν1
  obtain ⟨C, hC1, hrect⟩ :=
    Commons.Probability.RandomMatrix.rect_spectral_measurable 1 (by norm_num) 1 (by norm_num)
  set Θ : ℝ := 2 * (Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) with hΘ_def
  have hΘ1 : 1 ≤ Θ := by
    rw [hΘ_def]; have := Real.sqrt_nonneg (2 * C ^ 2 + 24 / 11); linarith
  obtain ⟨Ct, hCt0, hTens⟩ := Commons.Probability.Independence.tensorization_linear hΘ1
  set Ctt : ℝ := max Ct 1 with hCtt_def
  have hCtt1 : 1 ≤ Ctt := le_max_right _ _
  have hCtt0 : 0 < Ctt := lt_of_lt_of_le one_pos hCtt1
  have hCt_le : Ct ≤ Ctt := le_max_left _ _
  have hTens' : ∀ {m : ℕ} {Ω' : Type u} [MeasurableSpace Ω'] (P' : Measure Ω')
      [IsProbabilityMeasure P'] {ξ : Fin m → Ω' → ℝ} (hξ : ProbabilityTheory.iIndepFun ξ P')
      {K' ε₀ ε' : ℝ} (hK' : 0 < K') (hε₀ : 0 < ε₀) (h1 : ε₀ ≤ ε') (h2 : ε' ≤ Θ * ε₀)
      (hsmall : ∀ k : Fin m, ∀ tt : ℝ, ε₀ ≤ tt → P'.real {x | |ξ k x| ≤ tt} ≤ K' * tt),
      P'.real {x | (∑ k, (ξ k x) ^ 2) ≤ ε' ^ 2 * (m : ℝ)} ≤ (Ctt * K' * ε') ^ m := by
    intro m Ω' _ P' _ ξ hξ K' ε₀ ε' hK' hε₀ h1 h2 hsmall
    refine le_trans (hTens (P := P') hξ hK' hε₀ h1 h2 hsmall) ?_
    apply pow_le_pow_left₀ (mul_nonneg (mul_nonneg hCt0.le hK'.le) (le_trans hε₀.le h1))
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCt_le hK'.le)
      (le_trans hε₀.le h1)
  set L : ℝ := max (max L₀ 1) (256 * LAC / ν) with hL_def
  have hL1 : 1 ≤ L :=
    le_trans (le_max_right L₀ 1) (le_max_left (max L₀ 1) (256 * LAC / ν))
  have hLL₀ : L₀ ≤ L :=
    le_trans (le_max_left L₀ 1) (le_max_left (max L₀ 1) (256 * LAC / ν))
  have hLAC_le : LAC ≤ L * ν / 256 := by
    have h1 : 256 * LAC / ν ≤ L := le_max_right (max L₀ 1) (256 * LAC / ν)
    have h2 : 256 * LAC ≤ L * ν := by
      rw [div_le_iff₀ hν0] at h1; linarith [h1]
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 256)]
    linarith [h2]
  set Kspv : ℝ := Submission.NetAssemble.Ksp C Ctt with hKspv_def
  have hKspv0 : 0 < Kspv := by
    rw [hKspv_def]; exact Submission.NetAssemble.Ksp_pos hC1 hCtt0
  obtain ⟨M, hM1, hMle⟩ := exists_exp_neg_mul_le
    (c := CPerm * KA * Kspv * L * ν / a) (by positivity) (K := 1 / 16) (by norm_num)
  have hQ1 : CPerm * Real.exp (-M) * KA * Kspv * L * ν / a ≤ 1 / 16 := by
    have h2 : (CPerm * KA * Kspv * L * ν / a) * Real.exp (-M)
        = CPerm * Real.exp (-M) * KA * Kspv * L * ν / a := by ring
    rw [← h2]; exact hMle
  obtain ⟨nD, hDn⟩ := hDset M hM1
  -- absorption constants
  set K₀ : ℝ := 1 + (2 / (ν₁ ^ 2 * δ₁)) * (6 * L * ν + 1 + 4 * K / (Kspv * ν)) with hK₀_def
  set C₁ : ℝ := (4 / (ν₁ ^ 3 * δ₁)) * (3 * L + 1 / (Kspv * ν)) with hC₁_def
  have hC₁0 : 0 < C₁ := by
    rw [hC₁_def]
    refine mul_pos (div_pos (by norm_num) (by positivity)) ?_
    have h1 : 0 < 1 / (Kspv * ν) := div_pos one_pos (by positivity)
    have h2 : 0 < 3 * L := by linarith
    linarith
  have hK₀0 : 0 < K₀ := by
    rw [hK₀_def]
    have h1 : 0 < 1 / (Kspv * ν) := div_pos one_pos (by positivity)
    have h2 : 0 < 6 * L * ν := by positivity
    have h3 : 0 < 4 * K / (Kspv * ν) := div_pos (by linarith) (by positivity)
    have h4 : 0 < (2 / (ν₁ ^ 2 * δ₁)) * (6 * L * ν + 1 + 4 * K / (Kspv * ν)) :=
      mul_pos (div_pos (by norm_num) (by positivity))
        (by linarith : 0 < 6 * L * ν + 1 + 4 * K / (Kspv * ν))
    linarith
  -- the remaining "n large" bounds
  obtain ⟨n16, hn16⟩ := Commons.Analysis.Real.mul_nat_mul_pow_le_one
    (s := (1:ℝ)/16) (by norm_num) (by norm_num) (c := 2) (by norm_num)
  obtain ⟨ne, hne⟩ := Commons.Analysis.Real.mul_nat_mul_pow_le_one
    (s := Real.exp (-1)) (Real.exp_pos _) (Real.exp_lt_one_iff.mpr (by norm_num))
    (c := 2) (by norm_num)
  obtain ⟨na, hna⟩ := Commons.Analysis.Real.mul_nat_mul_pow_le_one
    (s := a) ha0 ha1 (c := 2) (by norm_num)
  obtain ⟨nu, hnu⟩ := Commons.Analysis.Real.mul_pow_le_one
    (s := (1:ℝ)/2) (by norm_num) (by norm_num) (c := 2 * K / ν) (by positivity)
  have hab_lt : a / (1 - (p : ℝ) + ε) < 1 := by
    rw [div_lt_one (by linarith)]
    rw [ha_def]; linarith
  have hab0 : 0 < a / (1 - (p : ℝ) + ε) := div_pos ha0 (by linarith)
  obtain ⟨nabs, hnabs⟩ := Commons.Analysis.Real.mul_pow_le_one
    (s := a / (1 - (p : ℝ) + ε)) hab0 hab_lt (c := K₀) hK₀0.le
  set Nbig : ℕ := max (max (max n₁ n₂) (max nD 2))
      (max (max (max n16 ne) (max na nu))
        (max nabs (max (max (max (Nat.ceil ((2 * K / ν) ^ 2)) (Nat.ceil (Kspv / 4)))
          (Nat.ceil (1 / δ))) (max (Nat.ceil (1 / (C₁ * γ₀))) 1)))) with hNbig_def
  have hNbig1 : 1 ≤ Nbig := by
    rw [hNbig_def]
    refine le_trans (le_max_right (Nat.ceil (1 / (C₁ * γ₀))) 1) ?_
    refine le_trans (le_max_right (max (max (Nat.ceil ((2 * K / ν) ^ 2)) (Nat.ceil (Kspv / 4)))
      (Nat.ceil (1 / δ))) (max (Nat.ceil (1 / (C₁ * γ₀))) 1)) ?_
    refine le_trans (le_max_right nabs (max (max (max (Nat.ceil ((2 * K / ν) ^ 2))
      (Nat.ceil (Kspv / 4))) (Nat.ceil (1 / δ))) (max (Nat.ceil (1 / (C₁ * γ₀))) 1))) ?_
    refine le_trans (le_max_right (max (max n16 ne) (max na nu))
      (max nabs (max (max (max (Nat.ceil ((2 * K / ν) ^ 2)) (Nat.ceil (Kspv / 4)))
        (Nat.ceil (1 / δ))) (max (Nat.ceil (1 / (C₁ * γ₀))) 1)))) ?_
    exact le_max_right (max (max n₁ n₂) (max nD 2)) _
  refine ⟨Nbig, hNbig1, C₁, hC₁0, ?_⟩
  intro n hn Ω _ P B hBind hBlaw s hs1 hs2 t ht
  rw [hNbig_def] at hn
  simp only [max_le_iff] at hn
  obtain ⟨⟨⟨hnn₁, hnn₂⟩, ⟨hnnD, hn2⟩⟩, ⟨⟨hn16', hne'⟩, ⟨hnna', hnu'⟩⟩, hnabs',
    ⟨⟨hncd1, hncd2⟩, hnδ'⟩, ⟨hng, hn1⟩⟩ := hn
  have hn16'' : 2 * (n:ℝ) * (1/16)^n ≤ 1 := hn16 n hn16'
  have hne'' : 2 * (n:ℝ) * (Real.exp (-1))^n ≤ 1 := hne n hne'
  have hna'' : 2 * (n:ℝ) * a^n ≤ 1 := hna n hnna'
  have hnu'' : (2 * K / ν) * ((1:ℝ)/2)^n ≤ 1 := hnu n hnu'
  have hnabs'' : K₀ * (a / (1 - (p : ℝ) + ε))^n ≤ 1 := hnabs n hnabs'
  have hnKsq : (2 * K / ν) ^ 2 ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil ((2 * K / ν) ^ 2)) (by exact_mod_cast hncd1)
  have hn4 : (Kspv / 4) ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil (Kspv / 4)) (by exact_mod_cast hncd2)
  have hnδ'' : (1 / δ) ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil (1 / δ)) (by exact_mod_cast hnδ')
  have hnγ'' : (1 / (C₁ * γ₀)) ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil (1 / (C₁ * γ₀))) (by exact_mod_cast hng)
  have hnK : K / Real.sqrt (n : ℝ) ≤ ν / 2 := by
    have h2 : 2 * K / ν ≤ Real.sqrt (n : ℝ) := by
      have h3 : (2 * K / ν) ^ 2 ≤ (Real.sqrt (n:ℝ))^2 := by
        rw [Real.sq_sqrt (by positivity)]; exact hnKsq
      have h4 := sq_le_sq.mp h3
      rwa [abs_of_nonneg (by positivity), abs_of_nonneg (Real.sqrt_nonneg _)] at h4
    have h5 : K ≤ ν / 2 * Real.sqrt (n:ℝ) := by
      have h6 := mul_le_mul_of_nonneg_right h2 (by positivity : (0:ℝ) ≤ ν / 2)
      have he : (2 * K / ν) * (ν / 2) = K := by field_simp
      rw [he] at h6
      linarith [h6]
    rw [div_le_iff₀ (Real.sqrt_pos.2 (by positivity))]
    linarith [h5]
  have hnδ : 1 ≤ δ * (n : ℝ) := by
    rw [div_le_iff₀ hδ0] at hnδ''
    linarith
  have hnabs2 : K₀ * a ^ n ≤ (1 - (p : ℝ) + ε) ^ n := by
    have h := hnabs''
    rw [div_pow] at h
    rw [← mul_div_assoc] at h
    rw [div_le_one (pow_pos (by linarith [p.2.2] : (0:ℝ) < 1 - (p:ℝ) + ε) n)] at h
    linarith [h]
  have hnKγ : 1 ≤ C₁ * (γ₀ * (n : ℝ)) := by
    rw [div_le_iff₀ (mul_pos hC₁0 hγ₀)] at hnγ''
    linarith
  have hn1 : 1 ≤ n := by omega
  haveI := isProbabilityMeasure_of_hasLaw P hn1 hBlaw
  have hhnne : 2 * (n:ℝ) * Real.exp (-(n:ℝ)) ≤ 1 := by
    have heq : Real.exp (-(n:ℝ)) = (Real.exp (-1))^n := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [heq]; exact hne''
  -- clamp
  obtain ⟨Bc, hcm, hcind, hclaw, hcpt, hcae⟩ :=
    Submission.GeoBridge.exists_measurable_clamped_matrix (P := P) B hBind hBlaw
  -- spectral event
  obtain ⟨G, hGmeas, hGprob, hGsub⟩ := spectral_event_exists hn1 hC1 P Bc hcm hcind hclaw hcpt
    hrect
  -- the per-vector estimate
  have hper : ∀ T : ℝ, 0 < T → T ≤ ν / 2 → ∀ y : Fin n → ℤ, slopeOk p s L T y →
      P.real {ω : Ω | (∑ k : Fin (n - 1),
          (Submission.NetArgument.qSum (Bc ω) s y k) ^ 2)
            ≤ ((Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * (n : ℝ)) ^ 2}
        ≤ (Ctt * (Submission.NetArgument.cSlope * L * T / Real.sqrt (n : ℝ))
            * (((Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * (n : ℝ))
                / Real.sqrt ((n - 1 : ℕ) : ℝ))) ^ (n - 1) := by
    intro T hT0 hTν y hslope
    obtain ⟨_, hε₀, h1, h2⟩ := Submission.NetProb.R_pos_and_bounds hn2 hC1
    have hκ : 0 < Submission.NetArgument.cSlope * L * T / Real.sqrt (n : ℝ) := by
      have hc : 0 < Submission.NetArgument.cSlope := Submission.NetAssemble.cSlope_pos
      have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by positivity)
      positivity
    exact Submission.NetProb.qsum_sq_bound_tens hn2 P hslope hcm hcind hclaw hTens'
      hκ hε₀ h1 h2
  by_cases hcase : t ≤ γ₀ * (n : ℝ)
  · have hu0 : 0 < t / Real.sqrt (n : ℝ) := div_pos ht (Real.sqrt_pos.2 (by positivity))
    have hule : t / Real.sqrt (n : ℝ) ≤ γ₀ * Real.sqrt (n : ℝ) := by
      rw [div_le_iff₀ (Real.sqrt_pos.2 (by positivity))]
      have hsq : Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ) = (n:ℝ) := by
        rw [← sq, Real.sq_sqrt (by positivity)]
      have he : γ₀ * Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ)
          = γ₀ * (Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ)) := by ring
      rw [he, hsq]
      exact hcase
    obtain ⟨PiSet, hPiCard, hPiProp⟩ := hperm n hn2 hnδ
    have hbound : P.real {ω : Ω | RandomBernoulliMatrices.σ_min
          (B ω + Matrix.of (fun _ _ : Fin n => s)) ≤ t / Real.sqrt (n : ℝ)}
        ≤ K₀ * a ^ n + C₁ * t := by
      have hstepA := hinc n hn2 hnn₁ P B hBind hBlaw s (t / Real.sqrt (n:ℝ)) hu0 hule
      have hstepB : P.real {ω : Ω | normalLe (le_trans (by norm_num : (1:ℕ) ≤ 2) hn2)
            (shiftMatrix s (B ω)) (2 * (t / Real.sqrt (n:ℝ)) * Real.sqrt (n:ℝ) / ν₁)}
          ≤ (6 * L * ν + 1 + 4 * K / (Kspv * ν)) * a ^ n
            + (3 * L + 1 / (Kspv * ν)) * (2 * (t / Real.sqrt (n:ℝ)) * Real.sqrt (n:ℝ) / ν₁) := by
        have hnet := Submission.NetAssemble.net_normal_bound hn2 hp₀ hp₁
          (by linarith [p.2.2]) hδ0 hδ12 hν0 hν1 hM1 hCP1 hKA1 ha0 ha1 hahalf hL1 hLAC_le
          hK0 (by rw [abs_le]; exact ⟨by linarith, by linarith⟩)
          (by rw [abs_le]; constructor <;> linarith [hs1, hs2, p.2.1, p.2.2])
          hC1 hCtt0 hCtt1 (by simpa [hKspv_def] using hQ1) PiSet hPiCard
          (fun T th hT0 hTν hth0 hthT1 hthT2 y hy hnc w hw =>
            hPiProp hT0 hTν hy hnc hth0 hthT1 hthT2 w hw)
          (fun x hx hnc => hthr n hn1 x hx hnc L hLL₀)
          P Bc hcm hcind hclaw hcpt hper
          (fun T hT0 hTν hcap => by
            rw [ha_def] at hcap
            exact hDn n hnnD T hT0 hTν hcap s L)
          hGmeas hGprob hGsub
          (by
            rw [ha_def]
            have hc2 : P.real {ω : Ω | compressible δ₂ ν₂
                (fun j => (Submission.IncompReduction.nVec (shiftMatrix s (Bc ω))).ofLp j)}
                ≤ (1 - (p : ℝ) + ee) ^ n := hcomp₂ n hn2 hnn₂ P Bc hcind hclaw s
            refine le_trans ?_ hc2
            exact MeasureTheory.measureReal_mono
              (fun ω hω => Submission.NormalCompress.compressible_mono _ hδ_le hν_le hν0.le hω)
              (measure_ne_top P _))
          hnK
          (by
            have h := hnu''
            rw [one_div_pow] at h
            rw [mul_one_div] at h
            exact (div_le_one (by positivity : (0:ℝ) < (2:ℝ)^n)).mp h)
          hn16'' hhnne hna''
          (r := 2 * (t / Real.sqrt (n:ℝ)) * Real.sqrt (n:ℝ) / ν₁)
          (by
            have h2 : (0:ℝ) < 2 := by norm_num
            have hs' : (0:ℝ) < Real.sqrt (n:ℝ) := Real.sqrt_pos.2 (by positivity)
            exact div_pos (mul_pos (mul_pos h2 hu0) hs') hν₁0)
        have hae' : ∀ i j : Fin n, (fun ω => B ω i j) =ᵐ[P] (fun ω => Bc ω i j) :=
          fun i j => (hcae i j).symm
        have htr := Submission.GeoBridge.measureReal_matrix_event_eq_of_ae P B Bc hae'
          {M : Matrix (Fin n) (Fin n) ℝ | normalLe (le_trans (by norm_num : (1:ℕ) ≤ 2) hn2)
            (shiftMatrix s M) (2 * (t / Real.sqrt (n:ℝ)) * Real.sqrt (n:ℝ) / ν₁)}
        simp only [Set.mem_setOf_eq] at htr
        rw [htr]
        exact hnet
      have hr : 2 * (t / Real.sqrt (n:ℝ)) * Real.sqrt (n:ℝ) / ν₁ = 2 * t / ν₁ := by
        have hs : Real.sqrt (n:ℝ) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
        field_simp
      have hfin : P.real {ω : Ω | RandomBernoulliMatrices.σ_min
            (B ω + Matrix.of (fun _ _ : Fin n => s)) ≤ t / Real.sqrt (n : ℝ)}
          ≤ a ^ n + (2 / (ν₁ ^ 2 * δ₁)) * ((6 * L * ν + 1 + 4 * K / (Kspv * ν)) * a ^ n
              + (3 * L + 1 / (Kspv * ν)) * (2 * t / ν₁)) := by
        rw [hr] at hstepB
        refine le_trans hstepA ?_
        rw [hr]
        exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hstepB (by positivity))
      have hcompl : a ^ n + (2 / (ν₁ ^ 2 * δ₁)) * ((6 * L * ν + 1 + 4 * K / (Kspv * ν)) * a ^ n
              + (3 * L + 1 / (Kspv * ν)) * (2 * t / ν₁))
          = K₀ * a ^ n + C₁ * t := by
        rw [hK₀_def, hC₁_def]; ring
      rw [hcompl] at hfin
      exact hfin
    refine le_trans hbound ?_
    linarith [hnabs2]
  · push_neg at hcase
    have h1 : 1 ≤ C₁ * t := by
      have hb : (0:ℝ) < γ₀ * (n:ℝ) := mul_pos hγ₀ (by positivity)
      nlinarith [hnKγ, hb, hcase, hC₁0]
    calc P.real {ω : Ω | RandomBernoulliMatrices.σ_min
            (B ω + Matrix.of (fun _ _ : Fin n => s)) ≤ t / Real.sqrt (n : ℝ)}
        ≤ 1 := MeasureTheory.measureReal_le_one
      _ ≤ (1 - (p : ℝ) + ε) ^ n + C₁ * t := by
          have h2 : (0:ℝ) ≤ (1 - (p:ℝ) + ε)^n :=
            pow_nonneg (by linarith [p.2.2] : (0:ℝ) ≤ 1 - (p:ℝ) + ε) n
          linarith [h1, h2]


/-- General product formula for independent families. -/
lemma measureReal_iInter_eq_prod_gen {Ω : Type u} [MeasurableSpace Ω] {ι : Type*} [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P] {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)] {f : (i : ι) → Ω → β i}
    (hf : ProbabilityTheory.iIndepFun f P) (s : (i : ι) → Set (β i))
    (hs : ∀ i, MeasurableSet (s i)) :
    P.real (⋂ i, f i ⁻¹' s i) = ∏ i, P.real (f i ⁻¹' s i) := by
  have h1 : P (⋂ i, f i ⁻¹' s i) = ∏ i, P (f i ⁻¹' s i) :=
    hf.meas_iInter (fun i => MeasurableSpace.measurableSet_comap.2 ⟨s i, hs i, rfl⟩)
  rw [Measure.real_def, h1, ENNReal.toReal_prod]
  exact Finset.prod_congr rfl (fun i _ => rfl)

/-- Real-valued product formula for independent families. -/
lemma measureReal_iInter_eq_prod {Ω : Type u} [MeasurableSpace Ω] {ι : Type*} [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P] {f : ι → Ω → ℝ} (hf : ProbabilityTheory.iIndepFun f P)
    (hfmeas : ∀ i, Measurable (f i)) (t : ι → Set ℝ) (ht : ∀ i, MeasurableSet (t i)) :
    P.real (⋂ i, f i ⁻¹' t i) = ∏ i, P.real (f i ⁻¹' t i) := by
  have h1 : P (⋂ i, f i ⁻¹' t i) = ∏ i, P (f i ⁻¹' t i) :=
    hf.meas_iInter (fun i => MeasurableSpace.measurableSet_comap.2 ⟨t i, ht i, rfl⟩)
  rw [Measure.real_def, h1, ENNReal.toReal_prod]
  exact Finset.prod_congr rfl (fun i _ => rfl)

/-- Squeeze lemma converting uniform upper/lower `n`-th-power bounds into the
`(a + o(1))^n` form. -/
lemma asymptotic_squeeze {Q : ℕ → ℝ} {a : ℝ} (ha0 : 0 ≤ a) (N₀ : ℕ)
    (hQ0 : ∀ n ≥ 1, 0 ≤ Q n)
    (hlow : ∀ n ≥ N₀, a ^ n ≤ Q n)
    (hup : ∀ ε > 0, ∃ N, ∀ n ≥ N, Q n ≤ (a + ε) ^ n) :
    ∃ o : ℕ → ℝ, o =o[Filter.atTop] (1 : ℕ → ℝ) ∧ ∀ n > 0, Q n = (a + o n) ^ n := by
  let o : ℕ → ℝ := fun n => if n = 0 then 0 else Q n ^ ((1 : ℝ) / n) - a
  have ho_def : ∀ n, n ≠ 0 → o n = Q n ^ ((1 : ℝ) / n) - a := by
    intro n hn; dsimp only [o]; rw [if_neg hn]
  refine ⟨o, ?_, ?_⟩
  · rw [Asymptotics.isLittleO_iff]
    intro c hc
    obtain ⟨N, hN⟩ := hup (c / 2) (by linarith)
    rw [Filter.eventually_atTop]
    refine ⟨max (max N N₀) 1, fun n hn => ?_⟩
    have hn1 : 1 ≤ n := le_trans (le_max_right (max N N₀) 1) hn
    have hnN : N ≤ n := le_trans (le_max_left N N₀) (le_trans (le_max_left (max N N₀) 1) hn)
    have hnN₀ : N₀ ≤ n := le_trans (le_max_right N N₀) (le_trans (le_max_left (max N N₀) 1) hn)
    have hn0 : n ≠ 0 := by omega
    have hQnn : 0 ≤ Q n := le_trans (pow_nonneg ha0 n) (hlow n hnN₀)
    have hlow' : a ≤ Q n ^ ((1 : ℝ) / n) := by
      have h1 : a ^ n ≤ Q n := hlow n hnN₀
      have h2 : (a ^ n : ℝ) ^ ((1 : ℝ) / n) ≤ Q n ^ ((1 : ℝ) / n) :=
        Real.rpow_le_rpow (pow_nonneg ha0 n) h1 (by positivity)
      have h3 : (a ^ n : ℝ) ^ ((1 : ℝ) / n) = a := by
        rw [← Real.rpow_natCast a n, ← Real.rpow_mul ha0, one_div,
          mul_inv_cancel₀ (by exact_mod_cast hn0), Real.rpow_one]
      rwa [h3] at h2
    have hup' : Q n ^ ((1 : ℝ) / n) ≤ a + c / 2 := by
      have h1 : Q n ≤ (a + c / 2) ^ n := hN n hnN
      have h2 : Q n ^ ((1 : ℝ) / n) ≤ ((a + c / 2) ^ n) ^ ((1 : ℝ) / n) :=
        Real.rpow_le_rpow hQnn h1 (by positivity)
      have h3 : ((a + c / 2) ^ n) ^ ((1 : ℝ) / n) = a + c / 2 := by
        rw [← Real.rpow_natCast (a + c / 2) n, ← Real.rpow_mul (by linarith), one_div,
          mul_inv_cancel₀ (by exact_mod_cast hn0), Real.rpow_one]
      rwa [h3] at h2
    have hnn : 0 ≤ o n := by rw [ho_def n hn0]; linarith
    have hle : o n ≤ c := by rw [ho_def n hn0]; linarith
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have h1 : ‖(1 : ℕ → ℝ) n‖ = 1 := by simp
    rw [h1, mul_one]
    exact hle
  · intro n hn
    have hn0 : n ≠ 0 := by omega
    have hQnn : 0 ≤ Q n := hQ0 n (by omega)
    rw [ho_def n hn0]
    have h1 : a + (Q n ^ ((1 : ℝ) / n) - a) = Q n ^ ((1 : ℝ) / n) := by ring
    rw [h1, ← Real.rpow_natCast (Q n ^ ((1 : ℝ) / n)) n, ← Real.rpow_mul hQnn, one_div,
      inv_mul_cancel₀ (by exact_mod_cast hn0), Real.rpow_one]

/-- Lower bound on the singular probability for a Bernoulli family: the first
column is zero with probability `(1−p)^n`. -/
lemma det_zero_lower_bernoulli {p : I} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ} (hn : 1 ≤ n)
    (B : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hBind : ProbabilityTheory.iIndepFun (fun x : Fin n × Fin n => (B · x.1 x.2)) P)
    (hBlaw : ∀ i j : Fin n, HasLaw (B · i j) (bernoulliMeasure 1 0 p) P) :
    (1 - (p : ℝ)) ^ n ≤ P.real {ω | (B ω).det = 0} := by
  haveI hprob : IsProbabilityMeasure P := isProbabilityMeasure_of_hasLaw P hn hBlaw
  obtain ⟨Bc, hcm, hcind, hclaw, hcpt, hcae⟩ :=
    Submission.GeoBridge.exists_measurable_clamped_matrix (P := P) B hBind hBlaw
  have h0 : Fin n := ⟨0, by omega⟩
  have h0ind : ProbabilityTheory.iIndepFun (fun i : Fin n => fun ω => Bc ω i h0) P := by
    have hg : Function.Injective (fun i : Fin n => (i, h0)) := fun a b h => congrArg Prod.fst h
    have h := ProbabilityTheory.iIndepFun.precomp
      (f := fun x : Fin n × Fin n => (Bc · x.1 x.2)) (g := fun i : Fin n => (i, h0)) hg hcind
    simpa using h
  have h0meas : ∀ i : Fin n, Measurable (fun ω => Bc ω i h0) := fun i => hcm i h0
  have hprod := measureReal_iInter_eq_prod h0ind h0meas (fun _ => ({0} : Set ℝ))
    (fun _ => measurableSet_singleton 0)
  have hterm : ∀ i : Fin n, P.real ((fun ω => Bc ω i h0) ⁻¹' ({0} : Set ℝ)) = 1 - (p : ℝ) := by
    intro i
    have h1 : P.real ((fun ω => Bc ω i h0) ⁻¹' ({0} : Set ℝ))
        = (P.map (fun ω => Bc ω i h0)).real ({0} : Set ℝ) := by
      rw [Measure.real_def, Measure.real_def,
        Measure.map_apply (hcm i h0) (measurableSet_singleton 0)]
    rw [h1, (hclaw i h0).map_eq]
    exact bernoulliMeasure_real_apply_of_notMem_of_mem p (measurableSet_singleton 0)
      (by simp) (by simp)
  have hPeq : P.real (⋂ i : Fin n, (fun ω => Bc ω i h0) ⁻¹' ({0} : Set ℝ))
      = (1 - (p : ℝ)) ^ n := by
    rw [hprod]
    rw [Finset.prod_congr rfl (fun i _ => hterm i)]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsub : (⋂ i : Fin n, (fun ω => Bc ω i h0) ⁻¹' ({0} : Set ℝ))
      ⊆ {ω | (Bc ω).det = 0} := by
    intro ω hω
    exact Matrix.det_eq_zero_of_column_eq_zero h0 (fun i => Set.mem_iInter.mp hω i)
  have hae' : ∀ i j : Fin n, (fun ω => B ω i j) =ᵐ[P] (fun ω => Bc ω i j) :=
    fun i j => (hcae i j).symm
  have htr := Submission.GeoBridge.measureReal_matrix_event_eq_of_ae P B Bc hae'
    {M : Matrix (Fin n) (Fin n) ℝ | M.det = 0}
  simp only [Set.mem_setOf_eq] at htr
  rw [htr]
  calc (1 - (p : ℝ)) ^ n = P.real (⋂ i : Fin n, (fun ω => Bc ω i h0) ⁻¹' ({0} : Set ℝ)) :=
        hPeq.symm
    _ ≤ P.real {ω | (Bc ω).det = 0} :=
        MeasureTheory.measureReal_mono hsub (measure_ne_top _ _)


/-- Upper bound on the singular probability of a shifted Bernoulli family. -/
lemma det_shifted_upper {p : I} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {s : ℝ} (hs1 : -1 ≤ s) (hs2 : s ≤ 0)
    {Ω : ℕ → Type u} [mΩ : ∀ n, MeasurableSpace (Ω n)] {P : (n : ℕ) → Measure (Ω n)}
    {B : (n : ℕ) → Ω n → Matrix (Fin n) (Fin n) ℝ}
    (B_indep : ∀ n, ProbabilityTheory.iIndepFun
      (fun x : Fin n × Fin n => (B n · x.1 x.2)) (P n))
    (B_bernoulli : ∀ n i j, HasLaw (B n · i j) (bernoulliMeasure 1 0 p) (P n)) :
    ∀ ε' > 0, ∃ N, ∀ n ≥ N,
      (P n).real {ω | (B n ω + Matrix.of (fun _ _ : Fin n => s)).det = 0}
        ≤ (1 - (p : ℝ) + ε') ^ n := by
  intro ε' hε'
  obtain ⟨N, hN1, C, hC, hb⟩ := theorem_A_bound hp₀ hp₁ hε'
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right N 1) hn
  have hnN : N ≤ n := le_trans (le_max_left N 1) hn
  haveI : IsProbabilityMeasure (P n) := isProbabilityMeasure_of_hasLaw (P n) hn1 (B_bernoulli n)
  refine Submission.Helpers.le_of_forall_pos_le_mul_add hC (fun t ht => ?_)
  have hb' := hb n hnN (Ω n) (P n) (B n) (B_indep n) (B_bernoulli n) s hs1 hs2 t ht
  have hsub : {ω : Ω n | (B n ω + Matrix.of (fun _ _ : Fin n => s)).det = 0} ⊆
      {ω : Ω n | RandomBernoulliMatrices.σ_min
          (B n ω + Matrix.of (fun _ _ : Fin n => s)) ≤ t / Real.sqrt (n : ℝ)} :=
    fun ω hω => Submission.Helpers.sigma_min_le_of_det_eq_zero _ (by positivity) hω
  exact le_trans (MeasureTheory.measureReal_mono hsub (measure_ne_top _ _)) hb'

/-- The Bernoulli singular-probability asymptotic. -/
theorem corollary_1_bound {p : I} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {Ω : ℕ → Type u} [mΩ : ∀ n, MeasurableSpace (Ω n)] {P : (n : ℕ) → Measure (Ω n)}
    {B : (n : ℕ) → Ω n → Matrix (Fin n) (Fin n) ℝ}
    (B_indep : ∀ n, ProbabilityTheory.iIndepFun
      (fun x : Fin n × Fin n => (B n · x.1 x.2)) (P n))
    (B_bernoulli : ∀ n i j, HasLaw (B n · i j) (bernoulliMeasure 1 0 p) (P n)) :
    ∃ o : ℕ → ℝ, o =o[Filter.atTop] (1 : ℕ → ℝ) ∧
      ∀ n > 0, (P n).real {ω | (B n ω).det = 0} = (1 - (p : ℝ) + o n) ^ n := by
  have ha0 : 0 ≤ 1 - (p : ℝ) := by linarith [p.2.2]
  have hup : ∀ ε' > 0, ∃ N, ∀ n ≥ N,
      (P n).real {ω | (B n ω).det = 0} ≤ (1 - (p : ℝ) + ε') ^ n := by
    intro ε' hε'
    obtain ⟨N, hN⟩ := det_shifted_upper hp₀ hp₁ (by norm_num : (-1:ℝ) ≤ 0) (le_refl (0:ℝ))
      B_indep B_bernoulli ε' hε'
    refine ⟨N, fun n hn => ?_⟩
    have h0 : Matrix.of (fun _ _ : Fin n => (0 : ℝ)) = 0 := by
      ext i j; exact rfl
    have he : {ω : Ω n | (B n ω).det = 0}
        = {ω : Ω n | (B n ω + Matrix.of (fun _ _ : Fin n => (0:ℝ))).det = 0} := by
      ext ω
      simp only [Set.mem_setOf_eq, h0, add_zero]
    rw [he]
    exact hN n hn
  have hlow : ∀ n ≥ 1, (1 - (p : ℝ)) ^ n ≤ (P n).real {ω | (B n ω).det = 0} :=
    fun n hn => det_zero_lower_bernoulli hp₀ hp₁ (P n) hn (B n) (B_indep n) (B_bernoulli n)
  exact asymptotic_squeeze ha0 1 (fun n _ => by
    rw [Measure.real_def]; exact ENNReal.toReal_nonneg) hlow hup


/-- Affine transformation of a Bernoulli law. -/
lemma hasLaw_affine {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {x y : ℝ} {p : I} (h : HasLaw X (bernoulliMeasure x y p) P) {a b : ℝ} (ha : a ≠ 0) :
    HasLaw (fun ω => a * X ω + b) (bernoulliMeasure (a * x + b) (a * y + b) p) P := by
  have hfmeas : Measurable (fun t : ℝ => a * t + b) := by fun_prop
  refine ⟨hfmeas.comp_aemeasurable h.aemeasurable, ?_⟩
  have hg := h.aemeasurable
  have hcomp : P.map (fun ω => a * X ω + b) = (P.map X).map (fun t : ℝ => a * t + b) := by
    have hae : (fun ω => a * X ω + b)
        =ᵐ[P] (fun ω => a * AEMeasurable.mk X hg ω + b) :=
      hg.ae_eq_mk.mono (fun ω hω => by simp only [hω])
    rw [Measure.map_congr hae]
    have h2 : (fun ω => a * AEMeasurable.mk X hg ω + b)
        = (fun t : ℝ => a * t + b) ∘ (AEMeasurable.mk X hg) := rfl
    rw [h2, ← Measure.map_map hfmeas hg.measurable_mk, Measure.map_congr hg.ae_eq_mk]
  rw [hcomp, h.map_eq, Commons.Probability.Bernoulli.map_affine ha]

/-- The Rademacher singular-probability asymptotic. -/
theorem corollary_2_bound {Ω : ℕ → Type u} (mΩ : ∀ n, MeasurableSpace (Ω n))
    {P : (n : ℕ) → Measure (Ω n)}
    {M : (n : ℕ) → Ω n → Matrix (Fin n) (Fin n) ℝ}
    (M_indep : ∀ n, ProbabilityTheory.iIndepFun
      (fun x : Fin n × Fin n => (M n · x.1 x.2)) (P n))
    (M_rademacher : ∀ n i j, HasLaw (M n · i j)
      RandomBernoulliMatrices.rademacherMeasure (P n)) :
    ∃ o : ℕ → ℝ, o =o[Filter.atTop] (1 : ℕ → ℝ) ∧
      ∀ n > 0, (P n).real {ω | (M n ω).det = 0} = (1 / 2 + o n) ^ n := by
  classical
  let p2 : I := ⟨1 / 2, by norm_num⟩
  have hp2 : (p2 : ℝ) = 1 / 2 := rfl
  have hrad : RandomBernoulliMatrices.rademacherMeasure = bernoulliMeasure 1 (-1) p2 := rfl
  let X : (n : ℕ) → Ω n → Matrix (Fin n) (Fin n) ℝ :=
    fun n ω => (1 / 2 : ℝ) • (M n ω + Matrix.of (fun _ _ : Fin n => (1 : ℝ)))
  have hXind : ∀ n, ProbabilityTheory.iIndepFun
      (fun x : Fin n × Fin n => (X n · x.1 x.2)) (P n) := by
    intro n
    have hfmeas : Measurable (fun t : ℝ => (1 / 2) * t + 1 / 2) := by fun_prop
    have h := ProbabilityTheory.iIndepFun.comp (M_indep n)
      (fun _ : Fin n × Fin n => fun t : ℝ => (1 / 2) * t + 1 / 2) (fun _ => hfmeas)
    have heq : (fun x : Fin n × Fin n => (X n · x.1 x.2))
        = (fun p : Fin n × Fin n =>
            (fun t : ℝ => (1 / 2) * t + 1 / 2) ∘ (M n · p.1 p.2)) := by
      funext p ω
      simp only [Function.comp_apply]
      dsimp only [X]
      simp only [Matrix.smul_apply]
      change (1/2) * (M n ω p.1 p.2 + 1) = (1/2) * (M n ω p.1 p.2) + 1/2
      ring
    rwa [heq]
  have hXlaw : ∀ n i j, HasLaw (X n · i j) (bernoulliMeasure 1 0 p2) (P n) := by
    intro n i j
    have h1 : (fun ω => X n ω i j) = (fun ω => (1/2) * (M n ω i j) + 1/2) := by
      funext ω
      dsimp only [X]
      simp only [Matrix.smul_apply]
      change (1/2) * (M n ω i j + 1) = (1/2) * (M n ω i j) + 1/2
      ring
    rw [h1]
    have h := hasLaw_affine (P := P n) (X := fun ω => M n ω i j)
      (x := (1:ℝ)) (y := (-1:ℝ)) (p := p2) (by rw [← hrad]; exact M_rademacher n i j)
      (a := 1/2) (b := 1/2) (by norm_num)
    have he : bernoulliMeasure ((1/2 : ℝ) * 1 + 1/2) ((1/2 : ℝ) * (-1) + 1/2) p2
        = bernoulliMeasure 1 0 p2 := by
      rw [show (1/2 : ℝ) * 1 + 1/2 = 1 by norm_num,
        show (1/2 : ℝ) * (-1) + 1/2 = 0 by norm_num]
    rwa [he] at h
  have hshift : ∀ n (ω : Ω n),
      X n ω + Matrix.of (fun _ _ : Fin n => (-(1/2))) = (1/2 : ℝ) • (M n ω) := by
    intro n ω
    ext i j
    dsimp only [X]
    simp only [Matrix.smul_apply]
    change (1/2) * (M n ω i j + 1) + -(1/2) = (1/2) * (M n ω i j)
    ring
  have hdetiff : ∀ n (A : Matrix (Fin n) (Fin n) ℝ), ((1/2 : ℝ) • A).det = 0 ↔ A.det = 0 := by
    intro n A
    rw [Matrix.det_smul, Fintype.card_fin]
    constructor
    · intro h
      exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero n (by norm_num : (1/2 : ℝ) ≠ 0))
    · intro h; rw [h, mul_zero]
  have hev : ∀ n, {ω : Ω n | (M n ω).det = 0}
      = {ω : Ω n | (X n ω + Matrix.of (fun _ _ : Fin n => (-(1/2)))).det = 0} := by
    intro n
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [hshift n ω]
    exact (hdetiff n (M n ω)).symm
  have hp2_0 : 0 < (p2 : ℝ) := by rw [hp2]; norm_num
  have hp2_1 : (p2 : ℝ) ≤ 1 / 2 := by rw [hp2]
  have hup : ∀ ε > 0, ∃ N, ∀ n ≥ N,
      (P n).real {ω | (M n ω).det = 0} ≤ (1 / 2 + ε) ^ n := by
    intro ε hε
    obtain ⟨N, hN⟩ := det_shifted_upper hp2_0 hp2_1 (by norm_num : (-1:ℝ) ≤ -(1/2))
      (by norm_num : (-(1/2):ℝ) ≤ 0) hXind hXlaw ε hε
    refine ⟨N, fun n hn => ?_⟩
    have h := hN n hn
    rw [← hev n] at h
    rwa [show (1 : ℝ) - (p2 : ℝ) + ε = 1 / 2 + ε by rw [hp2]; ring] at h
  refine asymptotic_squeeze (a := 1/2) (by norm_num) 2 (fun n _ => by
      rw [Measure.real_def]; exact ENNReal.toReal_nonneg) (fun n hn => ?_) hup
  haveI : IsProbabilityMeasure (P n) :=
    isProbabilityMeasure_of_hasLaw_gen (P n) (B := M n)
      (μ := bernoulliMeasure 1 (-1) p2) (n := n) (hn := le_trans (by norm_num) hn)
      (fun i j => by rw [← hrad]; exact M_rademacher n i j)
  exact Commons.Probability.Bernoulli.rademacher_det_lower (by omega) (P n) (M n)
    (M_indep n) (fun i j => by rw [← hrad]; exact M_rademacher n i j)

end Submission.Assembly
