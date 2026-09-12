import Mathlib
import Submission.NetChain
import Submission.NormalCompress
import Submission.CompressProp
import Submission.Commons.Probability.RandomMatrix.rect_spectral_measurable

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3000000

noncomputable section

universe u

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Measure Filter unitInterval

namespace Submission.NetProb

attribute [local instance] Classical.propDecidable

open Submission.Admissible
open Submission.MagicVector
open Submission.IncompReduction
open Submission.NormalVectorMatrix (colVec colVec_coeff)
open Submission.Section5D (Acoord holeN)
open Commons.LinearAlgebra.Net (sqNorm compressible)

/-- The spectral event for the transposed first `n−1` columns of `B + s·J`. -/
theorem rect_spectral_exists {n : ℕ} (hn1 : 1 ≤ n) {p : unitInterval}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hBmeas : ∀ i j : Fin n, Measurable (fun ω => B ω i j))
    (hBind : ProbabilityTheory.iIndepFun (fun x : Fin n × Fin n => (B · x.1 x.2)) P)
    (hBlaw : ∀ i j : Fin n, HasLaw (B · i j) (bernoulliMeasure 1 0 p) P)
    (hBpt : ∀ (i j : Fin n) (ω : Ω), |B ω i j - (p : ℝ)| ≤ 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ G : Set Ω, MeasurableSet G ∧ P.real G ≥ 1 - Real.exp (-(1 : ℝ) * (n : ℝ)) ∧
      G ⊆ {ω : Ω | ∀ v : Fin n → ℝ,
        (∑ k : Fin (n - 1),
            ((∑ i : Fin n, (B ω i (Submission.GeoBridge.emb k) - (p : ℝ)) * v i)) ^ 2)
          ≤ (C * Real.sqrt (n : ℝ)) ^ 2 * (∑ i : Fin n, (v i) ^ 2)} := by
  obtain ⟨C, hC1, hG⟩ := Commons.Probability.RandomMatrix.rect_spectral_measurable 1 (by norm_num) 1
    (by norm_num)
  refine ⟨C, hC1, ?_⟩
  have hAmeas : ∀ k : Fin (n - 1), ∀ j : Fin n,
      Measurable (fun ω : Ω => B ω j (Submission.GeoBridge.emb k) - (p : ℝ)) := by
    intro k j
    exact (hBmeas j (Submission.GeoBridge.emb k)).sub measurable_const
  have hAind : ProbabilityTheory.iIndepFun
      (fun kj : Fin (n - 1) × Fin n => fun ω : Ω => B ω kj.2 (Submission.GeoBridge.emb kj.1) - (p : ℝ)) P := by
    have hg : Function.Injective
        (fun kj : Fin (n - 1) × Fin n => (kj.2, Submission.GeoBridge.emb kj.1)) := by
      intro a b h
      have h1 : a.2 = b.2 := congrArg Prod.fst h
      have h2 : Submission.GeoBridge.emb a.1 = Submission.GeoBridge.emb b.1 := congrArg Prod.snd h
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
      |B ω j (Submission.GeoBridge.emb k) - (p : ℝ)| ≤ 1 := by
    intro k j ω
    exact hBpt j (Submission.GeoBridge.emb k) ω
  have hAm : ∀ (k : Fin (n - 1)) (j : Fin n), ∫ ω, (B ω j (Submission.GeoBridge.emb k) - (p : ℝ)) ∂P = 0 := by
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
  obtain ⟨G, hGmeas, hGprob, hGsub⟩ := hG n hn1 P
    (fun ω k j => B ω j (Submission.GeoBridge.emb k) - (p : ℝ)) hAmeas hAind hAb hAm
  exact ⟨G, hGmeas, hGprob, fun ω hω => by simpa using hGsub hω⟩

/-- Per-vector bound with the tensorization input passed explicitly. -/
lemma qsum_sq_bound_tens {n : ℕ} (hn2 : 2 ≤ n) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {p : unitInterval} {s L T Θ R Ct : ℝ}
    {y : Fin n → ℤ} (hslope : Submission.NetArgument.slopeOk p s L T y)
    {C : Ω → Matrix (Fin n) (Fin n) ℝ}
    (hCmeas : ∀ i j : Fin n, Measurable (fun ω => C ω i j))
    (hCind : ProbabilityTheory.iIndepFun (fun x : Fin n × Fin n => (C · x.1 x.2)) P)
    (hClaw : ∀ i j : Fin n, HasLaw (C · i j) (bernoulliMeasure 1 0 p) P)
    (hTens : ∀ {m : ℕ} {Ω' : Type u} [MeasurableSpace Ω'] (P' : Measure Ω')
      [IsProbabilityMeasure P'] {ξ : Fin m → Ω' → ℝ} (hξ : ProbabilityTheory.iIndepFun ξ P')
      {K ε₀ ε : ℝ} (hK : 0 < K) (hε₀ : 0 < ε₀) (h1 : ε₀ ≤ ε) (h2 : ε ≤ Θ * ε₀)
      (hsmall : ∀ k : Fin m, ∀ t : ℝ, ε₀ ≤ t → P'.real {x | |ξ k x| ≤ t} ≤ K * t),
      P'.real {x | (∑ k, (ξ k x) ^ 2) ≤ ε ^ 2 * (m : ℝ)} ≤ (Ct * K * ε) ^ m)
    (hK : 0 < Submission.NetArgument.cSlope * L * T / Real.sqrt (n : ℝ))
    (hε₀ : 0 < R / Real.sqrt ((n - 1 : ℕ) : ℝ))
    (h1 : Real.sqrt (n : ℝ) ≤ R / Real.sqrt ((n - 1 : ℕ) : ℝ))
    (h2 : R / Real.sqrt ((n - 1 : ℕ) : ℝ) ≤ Θ * Real.sqrt (n : ℝ)) :
    P.real {ω : Ω | (∑ k : Fin (n - 1), (Submission.NetArgument.qSum (C ω) s y k) ^ 2) ≤ R ^ 2}
      ≤ (Ct * (Submission.NetArgument.cSlope * L * T / Real.sqrt (n : ℝ))
          * (R / Real.sqrt ((n - 1 : ℕ) : ℝ))) ^ (n - 1) := by
  have hnm1 : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
    have : 1 ≤ n - 1 := by omega
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one this)
  have hsqrt_m : Real.sqrt (((n - 1 : ℕ) : ℝ)) ^ 2 = ((n - 1 : ℕ) : ℝ) :=
    Real.sq_sqrt (le_of_lt hnm1)
  have hεsq : (R / Real.sqrt ((n - 1 : ℕ) : ℝ)) ^ 2 * ((n - 1 : ℕ) : ℝ) = R ^ 2 := by
    rw [div_pow, hsqrt_m]
    field_simp
  have hsmall : ∀ k : Fin (n - 1), ∀ t : ℝ, Real.sqrt (n : ℝ) ≤ t →
      P.real {x : Ω | |(fun k' : Fin (n - 1) => fun ω : Ω =>
          Submission.NetArgument.qSum (C ω) s y k') k x| ≤ t}
        ≤ (Submission.NetArgument.cSlope * L * T / Real.sqrt (n : ℝ)) * t := by
    intro k t ht
    exact Submission.NetArgument.qSum_smallball P hslope hCmeas hCind hClaw ht
  have hmain := hTens P (Submission.NetArgument.qSum_iIndepFun (s := s) (y := y) P hCmeas hCind)
    hK (Real.sqrt_pos.2 (by exact_mod_cast (by omega : 1 ≤ n))) h1 h2 hsmall
  rw [hεsq] at hmain
  exact hmain

/-- **Annulus probability bound**: the probability that the random normal is
incompressible with threshold in `(T/2, T]` and the last-column inner product
is small is bounded by `e^{−n}` plus the net contribution. -/
theorem net_annulus_bound_core {n : ℕ} (hn2 : 2 ≤ n) {p : unitInterval}
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) ≤ 1 / 2) (hp1' : (p : ℝ) < 1)
    {δ ν T s L LAC : ℝ} (hδ0 : 0 < δ) (hδ12 : δ ≤ 1 / 2) (hν0 : 0 < ν) (hν1 : ν ≤ 1)
    (hT0 : 0 < T) (hTν : T ≤ ν / 2) (hL1 : 1 ≤ L) (hLAC : LAC ≤ L * ν / 256)
    (hs : |s| ≤ 1) (hsp : |s + (p : ℝ)| ≤ 1)
    (PiSet : Finset (Equiv.Perm (Fin n)))
    (hPi : ∀ (y : Fin n → ℝ), sqNorm y = 1 → ¬ compressible δ ν y →
      ∀ (th : ℝ), 0 < th → T / 2 ≤ th → th ≤ T → ∀ (w : Fin n → ℤ),
        (∀ i : Fin n, |(Real.sqrt (n : ℝ) / th) * y i - (w i : ℝ)| ≤ 1) →
        ∃ π ∈ PiSet, ∀ i : Fin n, w (π i) ∈ Acoord n δ ν T i)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hBmeas : ∀ i j : Fin n, Measurable (fun ω => B ω i j))
    (hBind : ProbabilityTheory.iIndepFun (fun x : Fin n × Fin n => (B · x.1 x.2)) P)
    (hBlaw : ∀ i j : Fin n, HasLaw (B · i j) (bernoulliMeasure 1 0 p) P)
    (hBpt : ∀ (i j : Fin n) (ω : Ω), |B ω i j - (p : ℝ)| ≤ 1)
    {C : ℝ} (hC1 : 1 ≤ C) {G : Set Ω} (hGmeas : MeasurableSet G)
    (hGprob : P.real G ≥ 1 - Real.exp (-(1 : ℝ) * (n : ℝ)))
    (hGsub : G ⊆ {ω : Ω | ∀ v : Fin n → ℝ,
        (∑ k : Fin (n - 1),
            ((∑ i : Fin n, (B ω i (Submission.GeoBridge.emb k) - (p : ℝ)) * v i)) ^ 2)
          ≤ (C * Real.sqrt (n : ℝ)) ^ 2 * (∑ i : Fin n, (v i) ^ 2)})
    {Ct : ℝ} (hCtpos : 0 < Ct)
    (hper : ∀ y : Fin n → ℤ, Submission.NetArgument.slopeOk p s L T y →
      P.real {ω : Ω | (∑ k : Fin (n - 1),
          (Submission.NetArgument.qSum (B ω) s y k) ^ 2)
            ≤ ((Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * (n : ℝ)) ^ 2}
        ≤ (Ct * (Submission.NetArgument.cSlope * L * T / Real.sqrt (n : ℝ))
            * (((Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * (n : ℝ))
                / Real.sqrt ((n - 1 : ℕ) : ℝ))) ^ (n - 1)) :
      P.real {ω : Ω |
          ¬ compressible δ ν (Submission.NormalSplit.yfnOf s (B ω))
            ∧ T / 2 < Submission.Threshold.threshold p
                (Submission.NormalSplit.yfnOf s (B ω)) L
            ∧ Submission.Threshold.threshold p
                (Submission.NormalSplit.yfnOf s (B ω)) L ≤ T}
        ≤ Real.exp (-(1 : ℝ) * (n : ℝ))
          + ((PiSet.card
              * (Submission.NetArgument.Dset p s L T LAC (holeN ν T)
                  (Acoord n δ ν T)).card : ℕ) : ℝ)
            * (Ct * (Submission.NetArgument.cSlope * L * T / Real.sqrt (n : ℝ))
                * (((Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * (n : ℝ))
                    / Real.sqrt ((n - 1 : ℕ) : ℝ))) ^ (n - 1) := by
  have hn1 : 1 ≤ n := by omega
  set R : ℝ := (Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * (n : ℝ) with hRdef
  set Θ : ℝ := 2 * (Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) with hΘdef
  have hCnn : (0 : ℝ) ≤ C := by linarith
  have hs0 : (0 : ℝ) ≤ 2 * C ^ 2 + 24 / 11 := by positivity
  have hr0 : (0 : ℝ) ≤ Real.sqrt (2 * C ^ 2 + 24 / 11) := Real.sqrt_nonneg _
  have hRpos : 0 < R := by
    rw [hRdef]
    have : (0 : ℝ) < Real.sqrt (2 * C ^ 2 + 24 / 11) + 1 := by linarith
    positivity
  have hΘ1 : 1 ≤ Θ := by
    rw [hΘdef]
    linarith
  have hnm1 : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
    have h1 : 1 ≤ n - 1 := by omega
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one h1)
  have hκ : (0 : ℝ) < Submission.NetArgument.cSlope * L * T / Real.sqrt (n : ℝ) := by
    have h1 : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn1)
    have h2 : (0 : ℝ) < Submission.NetArgument.cSlope := by
      rw [Submission.NetArgument.cSlope]; norm_num
    positivity
  have hεpos : 0 < R / Real.sqrt ((n - 1 : ℕ) : ℝ) := div_pos hRpos (Real.sqrt_pos.2 hnm1)
  have hnn : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
    have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    rw [this]; linarith
  have hmulsqrt : Real.sqrt (n : ℝ) * Real.sqrt ((n - 1 : ℕ) : ℝ)
      = Real.sqrt ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) :=
    (Real.sqrt_mul (show (0 : ℝ) ≤ (n : ℝ) by positivity) ((n - 1 : ℕ) : ℝ)).symm
  have hle1 : Real.sqrt (n : ℝ) ≤ R / Real.sqrt ((n - 1 : ℕ) : ℝ) := by
    rw [hRdef, le_div_iff₀ (Real.sqrt_pos.2 hnm1)]
    have h4 : (1 : ℝ) ≤ Real.sqrt (2 * C ^ 2 + 24 / 11) + 1 := by linarith
    calc Real.sqrt (n : ℝ) * Real.sqrt ((n - 1 : ℕ) : ℝ)
        = Real.sqrt ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) := hmulsqrt
      _ ≤ Real.sqrt ((n : ℝ) * (n : ℝ)) := Real.sqrt_le_sqrt (by nlinarith [hnn])
      _ = (n : ℝ) := Real.sqrt_mul_self (by positivity)
      _ ≤ (Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * (n : ℝ) := by
          have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
          calc (n : ℝ) = 1 * (n : ℝ) := (one_mul _).symm
            _ ≤ (Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * (n : ℝ) :=
                mul_le_mul_of_nonneg_right h4 hn0
  have hle2 : R / Real.sqrt ((n - 1 : ℕ) : ℝ) ≤ Θ * Real.sqrt (n : ℝ) := by
    rw [hRdef, hΘdef, div_le_iff₀ (Real.sqrt_pos.2 hnm1)]
    have h2 : (n : ℝ) ≤ 2 * Real.sqrt ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) := by
      have hn2' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      have h3 : (n : ℝ) / 2 ≤ Real.sqrt ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) := by
        rw [Real.le_sqrt (by positivity) (by positivity)]
        have hle : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
        rw [hle]
        nlinarith [hn2']
      linarith
    have h3 : Real.sqrt ((n : ℝ) * ((n - 1 : ℕ) : ℝ))
        = Real.sqrt (n : ℝ) * Real.sqrt ((n - 1 : ℕ) : ℝ) :=
      Real.sqrt_mul (by positivity) _
    rw [h3] at h2
    have h4 : (0 : ℝ) ≤ Real.sqrt (2 * C ^ 2 + 24 / 11) + 1 := by linarith [hr0]
    calc (Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * (n : ℝ)
        ≤ (Real.sqrt (2 * C ^ 2 + 24 / 11) + 1)
            * (2 * (Real.sqrt (n : ℝ) * Real.sqrt ((n - 1 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left h2 h4
      _ = 2 * (Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * Real.sqrt (n : ℝ)
            * Real.sqrt ((n - 1 : ℕ) : ℝ) := by ring
  -- the net
  have hperz : ∀ z ∈ Submission.NetChain.NetT p s L T LAC (holeN ν T) (Acoord n δ ν T) PiSet,
      P.real {ω : Ω | (∑ k : Fin (n - 1),
          (Submission.NetArgument.qSum (B ω) s z k) ^ 2) ≤ R ^ 2}
        ≤ (Ct * (Submission.NetArgument.cSlope * L * T / Real.sqrt (n : ℝ))
            * (R / Real.sqrt ((n - 1 : ℕ) : ℝ))) ^ (n - 1) := by
    intro z hz
    have hzslope : Submission.NetArgument.slopeOk p s L T z := by
      obtain ⟨π, _hπ, hd⟩ := (Submission.NetChain.mem_NetT).mp hz
      have h1 : Submission.NetArgument.slopeOk p s L T (fun i : Fin n => z (π i)) :=
        (Submission.NetArgument.mem_Dset.mp hd).2
      exact (Submission.NetArgument.slopeOk_comp_perm π p s L T z).mp h1
    have hzz := hper z hzslope
    rw [hRdef] at hzz ⊢
    exact hzz
  -- set algebra
  set Ann : Set Ω := {ω : Ω |
      ¬ compressible δ ν (Submission.NormalSplit.yfnOf s (B ω))
        ∧ T / 2 < Submission.Threshold.threshold p
            (Submission.NormalSplit.yfnOf s (B ω)) L
        ∧ Submission.Threshold.threshold p
            (Submission.NormalSplit.yfnOf s (B ω)) L ≤ T} with hAnn
  set E : Set Ω := {ω : Ω | ∃ z ∈ Submission.NetChain.NetT p s L T LAC (holeN ν T)
      (Acoord n δ ν T) PiSet,
      (∑ k : Fin (n - 1), (Submission.NetArgument.qSum (B ω) s z k) ^ 2) ≤ R ^ 2} with hE
  have hsub : Ann ∩ G ⊆ E := by
    intro ω hω
    exact Submission.NetChain.chain_subset hn2 hp1' hδ0 hδ12 hν0 hν1 hT0 hTν hL1 hLAC
      hs hsp (PiSet := PiSet) hPi B hGsub hω
  have hAnn1 : P.real (Ann ∩ G) ≤ P.real E :=
    MeasureTheory.measureReal_mono hsub (measure_ne_top P _)
  have hEunion : E = ⋃ z ∈ Submission.NetChain.NetT p s L T LAC (holeN ν T)
      (Acoord n δ ν T) PiSet,
      {ω : Ω | (∑ k : Fin (n - 1), (Submission.NetArgument.qSum (B ω) s z k) ^ 2) ≤ R ^ 2} := by
    rw [hE]
    ext ω
    simp [Set.mem_iUnion, Set.mem_setOf_eq]
  have hAnn2 : P.real E ≤ ∑ z ∈ Submission.NetChain.NetT p s L T LAC (holeN ν T)
      (Acoord n δ ν T) PiSet,
      P.real {ω : Ω | (∑ k : Fin (n - 1), (Submission.NetArgument.qSum (B ω) s z k) ^ 2) ≤ R ^ 2} := by
    rw [hEunion]
    exact MeasureTheory.measureReal_biUnion_finset_le _ _
  have hAnn3 : (∑ z ∈ Submission.NetChain.NetT p s L T LAC (holeN ν T) (Acoord n δ ν T) PiSet,
      P.real {ω : Ω | (∑ k : Fin (n - 1), (Submission.NetArgument.qSum (B ω) s z k) ^ 2) ≤ R ^ 2})
      ≤ ((Submission.NetChain.NetT p s L T LAC (holeN ν T) (Acoord n δ ν T) PiSet).card : ℝ)
        * (Ct * (Submission.NetArgument.cSlope * L * T / Real.sqrt (n : ℝ))
            * (R / Real.sqrt ((n - 1 : ℕ) : ℝ))) ^ (n - 1) := by
    calc _ ≤ ∑ _z ∈ Submission.NetChain.NetT p s L T LAC (holeN ν T) (Acoord n δ ν T) PiSet,
          (Ct * (Submission.NetArgument.cSlope * L * T / Real.sqrt (n : ℝ))
            * (R / Real.sqrt ((n - 1 : ℕ) : ℝ))) ^ (n - 1) :=
          Finset.sum_le_sum hperz
      _ = ((Submission.NetChain.NetT p s L T LAC (holeN ν T) (Acoord n δ ν T) PiSet).card : ℝ)
            * (Ct * (Submission.NetArgument.cSlope * L * T / Real.sqrt (n : ℝ))
              * (R / Real.sqrt ((n - 1 : ℕ) : ℝ))) ^ (n - 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hcardN : ((Submission.NetChain.NetT p s L T LAC (holeN ν T) (Acoord n δ ν T) PiSet).card : ℝ)
      ≤ ((PiSet.card * (Submission.NetArgument.Dset p s L T LAC (holeN ν T)
          (Acoord n δ ν T)).card : ℕ) : ℝ) := by
    exact_mod_cast Submission.NetChain.NetT_card_le p s L T LAC (holeN ν T)
      (Acoord n δ ν T) PiSet
  have hpow0 : (0 : ℝ) ≤ (Ct * (Submission.NetArgument.cSlope * L * T / Real.sqrt (n : ℝ))
      * (R / Real.sqrt ((n - 1 : ℕ) : ℝ))) ^ (n - 1) := by positivity
  have hAnn4 : P.real E ≤ ((PiSet.card * (Submission.NetArgument.Dset p s L T LAC (holeN ν T)
      (Acoord n δ ν T)).card : ℕ) : ℝ)
      * (Ct * (Submission.NetArgument.cSlope * L * T / Real.sqrt (n : ℝ))
          * (R / Real.sqrt ((n - 1 : ℕ) : ℝ))) ^ (n - 1) :=
    le_trans hAnn2 (le_trans hAnn3 (mul_le_mul_of_nonneg_right hcardN hpow0))
  -- complement of the spectral event
  have hcompl : P.real (Ann ∩ Gᶜ) ≤ Real.exp (-(1 : ℝ) * (n : ℝ)) := by
    have h1 : P.real (Ann ∩ Gᶜ) ≤ P.real Gᶜ :=
      MeasureTheory.measureReal_mono (Set.inter_subset_right) (measure_ne_top P _)
    have h2 : P.real Gᶜ = 1 - P.real G := by
      rw [MeasureTheory.measureReal_compl hGmeas]
      congr 1
      rw [Measure.real_def, measure_univ, ENNReal.toReal_one]
    have h3 : P.real Gᶜ ≤ Real.exp (-(1 : ℝ) * (n : ℝ)) := by
      rw [h2]
      linarith [hGprob]
    linarith
  have hsplit : P.real Ann ≤ P.real (Ann ∩ G) + P.real (Ann ∩ Gᶜ) := by
    have h : Ann = (Ann ∩ G) ∪ (Ann ∩ Gᶜ) := by
      ext ω
      by_cases hω : ω ∈ G <;> simp [hω]
    calc P.real Ann = P.real ((Ann ∩ G) ∪ (Ann ∩ Gᶜ)) := by conv_lhs => rw [h]
      _ ≤ P.real (Ann ∩ G) + P.real (Ann ∩ Gᶜ) := MeasureTheory.measureReal_union_le _ _
  rw [hAnn]
  linarith [hsplit, hAnn1, hAnn4, hcompl]

/-- Arithmetic bounds for `R := (√(2C²+24/11)+1)·n`. -/
lemma R_pos_and_bounds {n : ℕ} (hn2 : 2 ≤ n) {C : ℝ} (hC1 : 1 ≤ C) :
    0 < (Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * (n : ℝ) ∧
    0 < ((Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * (n : ℝ)) / Real.sqrt ((n - 1 : ℕ) : ℝ) ∧
    Real.sqrt (n : ℝ) ≤ ((Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * (n : ℝ))
        / Real.sqrt ((n - 1 : ℕ) : ℝ) ∧
    ((Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * (n : ℝ)) / Real.sqrt ((n - 1 : ℕ) : ℝ)
      ≤ 2 * (Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * Real.sqrt (n : ℝ) := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hr0 : (0 : ℝ) ≤ Real.sqrt (2 * C ^ 2 + 24 / 11) := Real.sqrt_nonneg _
  have h5 : (0 : ℝ) < Real.sqrt (2 * C ^ 2 + 24 / 11) + 1 := by linarith
  have hnm1 : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
    have h1 : 1 ≤ n - 1 := by omega
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one h1)
  have hnn : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
    have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    rw [this]; linarith
  have hmulsqrt : Real.sqrt (n : ℝ) * Real.sqrt ((n - 1 : ℕ) : ℝ)
      = Real.sqrt ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) :=
    (Real.sqrt_mul (show (0 : ℝ) ≤ (n : ℝ) by positivity) ((n - 1 : ℕ) : ℝ)).symm
  have hle1 : Real.sqrt (n : ℝ) ≤ ((Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * (n : ℝ))
      / Real.sqrt ((n - 1 : ℕ) : ℝ) := by
    rw [le_div_iff₀ (Real.sqrt_pos.2 hnm1)]
    have h4 : (1 : ℝ) ≤ Real.sqrt (2 * C ^ 2 + 24 / 11) + 1 := by linarith
    calc Real.sqrt (n : ℝ) * Real.sqrt ((n - 1 : ℕ) : ℝ)
        = Real.sqrt ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) := hmulsqrt
      _ ≤ Real.sqrt ((n : ℝ) * (n : ℝ)) := Real.sqrt_le_sqrt (by nlinarith [hnn])
      _ = (n : ℝ) := Real.sqrt_mul_self (by positivity)
      _ ≤ (Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * (n : ℝ) := by
          calc (n : ℝ) = 1 * (n : ℝ) := (one_mul _).symm
            _ ≤ (Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * (n : ℝ) :=
                mul_le_mul_of_nonneg_right h4 (le_of_lt hn0)
  have hle2 : ((Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * (n : ℝ))
      / Real.sqrt ((n - 1 : ℕ) : ℝ) ≤ 2 * (Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * Real.sqrt (n : ℝ) := by
    rw [div_le_iff₀ (Real.sqrt_pos.2 hnm1)]
    have h2 : (n : ℝ) ≤ 2 * Real.sqrt ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) := by
      have hn2' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      have h3 : (n : ℝ) / 2 ≤ Real.sqrt ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) := by
        rw [Real.le_sqrt (by positivity) (by positivity)]
        have hle : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
        rw [hle]
        nlinarith [hn2']
      linarith
    have h3 : Real.sqrt ((n : ℝ) * ((n - 1 : ℕ) : ℝ))
        = Real.sqrt (n : ℝ) * Real.sqrt ((n - 1 : ℕ) : ℝ) :=
      Real.sqrt_mul (by positivity) _
    rw [h3] at h2
    calc (Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * (n : ℝ)
        ≤ (Real.sqrt (2 * C ^ 2 + 24 / 11) + 1)
            * (2 * (Real.sqrt (n : ℝ) * Real.sqrt ((n - 1 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left h2 (le_of_lt h5)
      _ = 2 * (Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * Real.sqrt (n : ℝ)
            * Real.sqrt ((n - 1 : ℕ) : ℝ) := by ring
  exact ⟨mul_pos h5 hn0, div_pos (mul_pos h5 hn0) (Real.sqrt_pos.2 hnm1), hle1, hle2⟩

/-- **Annulus probability bound** (existence form of the constants). -/
theorem net_annulus_bound {n : ℕ} (hn2 : 2 ≤ n) {p : unitInterval}
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) ≤ 1 / 2) (hp1' : (p : ℝ) < 1)
    {δ ν T s L LAC : ℝ} (hδ0 : 0 < δ) (hδ12 : δ ≤ 1 / 2) (hν0 : 0 < ν) (hν1 : ν ≤ 1)
    (hT0 : 0 < T) (hTν : T ≤ ν / 2) (hL1 : 1 ≤ L) (hLAC : LAC ≤ L * ν / 256)
    (hs : |s| ≤ 1) (hsp : |s + (p : ℝ)| ≤ 1)
    (PiSet : Finset (Equiv.Perm (Fin n)))
    (hPi : ∀ (y : Fin n → ℝ), sqNorm y = 1 → ¬ compressible δ ν y →
      ∀ (th : ℝ), 0 < th → T / 2 ≤ th → th ≤ T → ∀ (w : Fin n → ℤ),
        (∀ i : Fin n, |(Real.sqrt (n : ℝ) / th) * y i - (w i : ℝ)| ≤ 1) →
        ∃ π ∈ PiSet, ∀ i : Fin n, w (π i) ∈ Acoord n δ ν T i)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hBmeas : ∀ i j : Fin n, Measurable (fun ω => B ω i j))
    (hBind : ProbabilityTheory.iIndepFun (fun x : Fin n × Fin n => (B · x.1 x.2)) P)
    (hBlaw : ∀ i j : Fin n, HasLaw (B · i j) (bernoulliMeasure 1 0 p) P)
    (hBpt : ∀ (i j : Fin n) (ω : Ω), |B ω i j - (p : ℝ)| ≤ 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ Ct : ℝ, 0 < Ct ∧
      P.real {ω : Ω |
          ¬ compressible δ ν (Submission.NormalSplit.yfnOf s (B ω))
            ∧ T / 2 < Submission.Threshold.threshold p
                (Submission.NormalSplit.yfnOf s (B ω)) L
            ∧ Submission.Threshold.threshold p
                (Submission.NormalSplit.yfnOf s (B ω)) L ≤ T}
        ≤ Real.exp (-(1 : ℝ) * (n : ℝ))
          + ((PiSet.card
              * (Submission.NetArgument.Dset p s L T LAC (holeN ν T)
                  (Acoord n δ ν T)).card : ℕ) : ℝ)
            * (Ct * (Submission.NetArgument.cSlope * L * T / Real.sqrt (n : ℝ))
                * (((Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * (n : ℝ))
                    / Real.sqrt ((n - 1 : ℕ) : ℝ))) ^ (n - 1) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨C, hC1, G, hGmeas, hGprob, hGsub⟩ :=
    rect_spectral_exists hn1 P B hBmeas hBind hBlaw hBpt
  obtain ⟨_hRpos, hεpos, hle1, hle2⟩ := R_pos_and_bounds hn2 hC1
  set Θ : ℝ := 2 * (Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) with hΘdef
  have hΘ1 : 1 ≤ Θ := by
    rw [hΘdef]
    linarith [Real.sqrt_nonneg (2 * C ^ 2 + 24 / 11)]
  rcases Commons.Probability.Independence.tensorization_linear hΘ1 with ⟨Ct, hCtpos, hTens⟩
  refine ⟨C, hC1, Ct, hCtpos, ?_⟩
  have hκ : 0 < Submission.NetArgument.cSlope * L * T / Real.sqrt (n : ℝ) := by
    have h1 : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn1)
    have h2 : (0 : ℝ) < Submission.NetArgument.cSlope := by
      rw [Submission.NetArgument.cSlope]; norm_num
    positivity
  refine net_annulus_bound_core hn2 hp0 hp1 hp1' hδ0 hδ12 hν0 hν1 hT0 hTν hL1 hLAC hs hsp
    PiSet hPi P B hBmeas hBind hBlaw hBpt hC1 hGmeas hGprob hGsub hCtpos ?_
  intro y hslope
  have h2' : ((Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * (n : ℝ)) / Real.sqrt ((n - 1 : ℕ) : ℝ)
      ≤ Θ * Real.sqrt (n : ℝ) := by
    rw [hΘdef]
    exact hle2
  exact qsum_sq_bound_tens hn2 P hslope hBmeas hBind hBlaw hTens hκ hεpos hle1 h2'

end Submission.NetProb
