import Mathlib
import Submission.NetProb
import Submission.NetFiber
import Submission.NetUniform
import Submission.NormalCompress
import Submission.IncompSide
import Submission.NormalSplit
import Submission.GeoBridge
import Submission.Helpers

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3000000

noncomputable section

universe u

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Measure Filter unitInterval

namespace Submission.NetAssemble

attribute [local instance] Classical.propDecidable

open Submission.Section5D (Acoord holeN keepMag)
open Submission.IncompReduction (normalLe shiftMatrix)
open Submission.NetArgument (Dset slopeOk qSum cSlope)
open Commons.LinearAlgebra.Net (sqNorm compressible)

/-!
# Assembly of Theorem A from the net argument

This module performs the annulus summation of the net argument, producing the
bound `P{normalLe r} ≤ (1−p+ε)^n + C·r`, and then combines it with the
incompressible-side decomposition to obtain Theorem A.
-/

/-- The spectral/net constant multiplying `L·T`. -/
noncomputable def Ksp (C Ct : ℝ) : ℝ :=
  Ct * Submission.NetArgument.cSlope * 2 * (Real.sqrt (2 * C ^ 2 + 24 / 11) + 1)

lemma cSlope_pos : 0 < Submission.NetArgument.cSlope := by
  rw [Submission.NetArgument.cSlope]; norm_num

lemma Ksp_pos {C Ct : ℝ} (hC1 : 1 ≤ C) (hCt : 0 < Ct) : 0 < Ksp C Ct := by
  have h1 : 0 < Real.sqrt (2 * C ^ 2 + 24 / 11) + 1 := by
    have := Real.sqrt_nonneg (2 * C ^ 2 + 24 / 11); linarith
  have h2 := cSlope_pos
  unfold Ksp
  exact mul_pos (mul_pos (mul_pos hCt h2) (by norm_num)) h1

/-- The per-annulus spectral factor raised to `n−1` is bounded by `(Ksp·L·T)^{n−1}`. -/
lemma chi_pow_le {n : ℕ} (hn2 : 2 ≤ n) {C : ℝ} (hC1 : 1 ≤ C) {Ct : ℝ} (hCt : 0 < Ct)
    {L T : ℝ} (hL1 : 1 ≤ L) (hT0 : 0 < T) :
    (Ct * (Submission.NetArgument.cSlope * L * T / Real.sqrt (n : ℝ))
        * (((Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * (n : ℝ))
            / Real.sqrt ((n - 1 : ℕ) : ℝ))) ^ (n - 1)
      ≤ (Ksp C Ct * L * T) ^ (n - 1) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨_, _, _, hle2⟩ := Submission.NetProb.R_pos_and_bounds hn2 hC1
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn1)
  have hc : 0 < Submission.NetArgument.cSlope := cSlope_pos
  have hdiv : 0 ≤ Submission.NetArgument.cSlope * L * T / Real.sqrt (n : ℝ) := by positivity
  have ha : 0 ≤ Ct * (Submission.NetArgument.cSlope * L * T / Real.sqrt (n : ℝ)) :=
    mul_nonneg hCt.le hdiv
  have hbase : Ct * (Submission.NetArgument.cSlope * L * T / Real.sqrt (n : ℝ))
        * (((Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * (n : ℝ)) / Real.sqrt ((n - 1 : ℕ) : ℝ))
      ≤ Ksp C Ct * L * T := by
    have h := mul_le_mul_of_nonneg_left hle2 ha
    refine le_trans h (le_of_eq ?_)
    rw [Ksp]
    have hne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt hs
    field_simp
  have hxnonneg : 0 ≤ ((Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * (n : ℝ))
      / Real.sqrt ((n - 1 : ℕ) : ℝ) := by
    have h1 : 0 < Real.sqrt (2 * C ^ 2 + 24 / 11) + 1 := by
      have := Real.sqrt_nonneg (2 * C ^ 2 + 24 / 11); linarith
    have h2 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have h3 : 0 < ((n - 1 : ℕ) : ℝ) := by
      have h : 1 ≤ n - 1 := by omega
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one h)
    positivity
  exact pow_le_pow_left₀ (mul_nonneg ha hxnonneg) hbase (n - 1)


/-- Dyadic threshold scale `T_j = K/(√n · 2^j)`. -/
noncomputable def Tj (K : ℝ) (n j : ℕ) : ℝ := K / (Real.sqrt (n : ℝ) * (2 : ℝ) ^ j)

lemma Tj_pos {K : ℝ} (hK : 0 < K) {n : ℕ} (hn1 : 1 ≤ n) (j : ℕ) : 0 < Tj K n j := by
  unfold Tj
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn1)
  positivity

lemma Tj_zero (K : ℝ) (n : ℕ) : Tj K n 0 = K / Real.sqrt (n : ℝ) := by
  unfold Tj; simp

lemma Tj_succ (K : ℝ) (n j : ℕ) : Tj K n (j + 1) = Tj K n j / 2 := by
  unfold Tj
  rw [pow_succ]
  have h2 : (2 : ℝ) ^ j ≠ 0 := by positivity
  field_simp

lemma Tj_anti {K : ℝ} (hK : 0 < K) {n : ℕ} (hn1 : 1 ≤ n) {i j : ℕ} (hij : i ≤ j) :
    Tj K n j ≤ Tj K n i := by
  unfold Tj
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn1)
  have h2 : (2 : ℝ) ^ i ≤ (2 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) hij
  have hpos : 0 < (2 : ℝ) ^ i := by positivity
  gcongr

lemma Tj_le_zero {K : ℝ} (hK : 0 < K) {n : ℕ} (hn1 : 1 ≤ n) (j : ℕ) :
    Tj K n j ≤ K / Real.sqrt (n : ℝ) := by
  rw [← Tj_zero K n]
  exact Tj_anti hK hn1 (Nat.zero_le j)

/-- **Single-annulus bound**: on the annulus `(T/2, T]` of threshold values, the
`normalLe`∩incompressible probability is bounded by the fibre factor times the
net bound. -/
theorem annulus_combined {n : ℕ} (hn2 : 2 ≤ n) {p : I}
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) ≤ 1 / 2) (hp1' : (p : ℝ) < 1)
    {δ ν : ℝ} (hδ0 : 0 < δ) (hδ12 : δ ≤ 1 / 2) (hν0 : 0 < ν) (hν1 : ν ≤ 1)
    {M LAC CPerm KA a s L T : ℝ}
    (hM : 1 ≤ M) (hCP1 : 1 ≤ CPerm) (hKA1 : 1 ≤ KA) (ha0 : 0 < a)
    (hL1 : 1 ≤ L) (hT0 : 0 < T) (hTν : T ≤ ν / 2) (hLAC : LAC ≤ L * ν / 256)
    (hs : |s| ≤ 1) (hsp : |s + (p : ℝ)| ≤ 1)
    {C : ℝ} (hC1 : 1 ≤ C) {Ct : ℝ} (hCt : 0 < Ct)
    (PiSet : Finset (Equiv.Perm (Fin n))) (hPiCard : (PiSet.card : ℝ) ≤ CPerm ^ n)
    (hPi : ∀ (y : Fin n → ℝ), sqNorm y = 1 → ¬ compressible δ ν y →
      ∀ (th : ℝ), 0 < th → T / 2 ≤ th → th ≤ T → ∀ (w : Fin n → ℤ),
        (∀ i : Fin n, |(Real.sqrt (n : ℝ) / th) * y i - (w i : ℝ)| ≤ 1) →
        ∃ π ∈ PiSet, ∀ i : Fin n, w (π i) ∈ Acoord n δ ν T i)
    (hDcard : ((Dset p s L T LAC (holeN ν T) (Acoord n δ ν T)).card : ℝ)
      ≤ Real.exp (-M * (n : ℝ)) * (KA * (holeN ν T : ℝ)) ^ n)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → Matrix (Fin n) (Fin n) ℝ) (hBmeas : ∀ i j : Fin n, Measurable (fun ω => B ω i j))
    (hBind : ProbabilityTheory.iIndepFun (fun x : Fin n × Fin n => (B · x.1 x.2)) P)
    (hBlaw : ∀ i j : Fin n, HasLaw (B · i j) (bernoulliMeasure 1 0 p) P)
    (hBpt : ∀ (i j : Fin n) (ω : Ω), |B ω i j - (p : ℝ)| ≤ 1)
    {G : Set Ω} (hGmeas : MeasurableSet G)
    (hGprob : P.real G ≥ 1 - Real.exp (-(1 : ℝ) * (n : ℝ)))
    (hGsub : G ⊆ {ω : Ω | ∀ v : Fin n → ℝ,
        (∑ k : Fin (n - 1),
            ((∑ i : Fin n, (B ω i (Submission.GeoBridge.emb k) - (p : ℝ)) * v i)) ^ 2)
          ≤ (C * Real.sqrt (n : ℝ)) ^ 2 * (∑ i : Fin n, (v i) ^ 2)})
    (hper : ∀ y : Fin n → ℤ, Submission.NetArgument.slopeOk p s L T y →
      P.real {ω : Ω | (∑ k : Fin (n - 1),
          (Submission.NetArgument.qSum (B ω) s y k) ^ 2)
            ≤ ((Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * (n : ℝ)) ^ 2}
        ≤ (Ct * (Submission.NetArgument.cSlope * L * T / Real.sqrt (n : ℝ))
            * (((Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * (n : ℝ))
                / Real.sqrt ((n - 1 : ℕ) : ℝ))) ^ (n - 1))
    (hcomp : P.real {ω : Ω | compressible δ ν (Submission.NormalSplit.yfnOf s (B ω))}
      ≤ a ^ n)
    {r : ℝ} (hr : 0 < r) :
    P.real {ω : Ω | normalLe (show 1 ≤ n by omega) (shiftMatrix s (B ω)) r ∧
        ¬ compressible δ ν (Submission.NormalSplit.yfnOf s (B ω)) ∧
        T / 2 < Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ∧
        Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ≤ T}
      ≤ (L * max (2 * T) r) *
        (Real.exp (-(1 : ℝ) * (n : ℝ))
          + CPerm ^ n * (Real.exp (-M * (n : ℝ)) * (KA * (holeN ν T : ℝ)) ^ n
              * (Ksp C Ct * L * T) ^ (n - 1))
          + a ^ n) := by
  have hn1 : 1 ≤ n := by omega
  have hfib := Submission.NetFiber.fiber_bound_annulus P hn1 B hBind hBlaw
    (s := s) (L := L) (T := T) (r := r) hL1 hT0 hr
  have hnet := Submission.NetProb.net_annulus_bound_core hn2 hp0 hp1 hp1' hδ0 hδ12 hν0 hν1
    hT0 hTν hL1 hLAC hs hsp PiSet hPi P B hBmeas hBind hBlaw hBpt hC1 hGmeas hGprob hGsub
    hCt hper
  -- the net RHS is bounded by e^{-n} + CPerm^n * (exp(-Mn) (KA N)^n (Ksp L T)^{n-1})
  have hCPnn : (0 : ℝ) ≤ CPerm ^ n := pow_nonneg (le_trans zero_le_one hCP1) n
  have hKAn : (0 : ℝ) ≤ KA ^ n := pow_nonneg (le_trans zero_le_one hKA1) n
  have hexpnn : (0 : ℝ) ≤ Real.exp (-(1 : ℝ) * (n : ℝ)) := Real.exp_nonneg _
  have hexpn : (0 : ℝ) ≤ Real.exp (-M * (n : ℝ)) := Real.exp_nonneg _
  have hχ := chi_pow_le hn2 hC1 hCt hL1 hT0
  have hRnn : (0 : ℝ) ≤ ((Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * (n : ℝ))
      / Real.sqrt ((n - 1 : ℕ) : ℝ) := by
    have h1 : 0 < Real.sqrt (2 * C ^ 2 + 24 / 11) + 1 := by
      have := Real.sqrt_nonneg (2 * C ^ 2 + 24 / 11); linarith
    have h2 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have h3 : 0 < ((n - 1 : ℕ) : ℝ) := by
      have h : 1 ≤ n - 1 := by omega
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one h)
    exact div_nonneg (mul_nonneg (le_of_lt h1) (le_of_lt h2)) (Real.sqrt_nonneg _)
  have hbase_nn : (0 : ℝ) ≤ Ct * (Submission.NetArgument.cSlope * L * T / Real.sqrt (n : ℝ))
      * (((Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * (n : ℝ))
          / Real.sqrt ((n - 1 : ℕ) : ℝ)) := by
    have h4 : (0 : ℝ) ≤ Submission.NetArgument.cSlope * L * T / Real.sqrt (n : ℝ) := by
      have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn1)
      exact div_nonneg (by have := cSlope_pos; positivity) (Real.sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hCt.le h4) hRnn
  have hχnn : (0 : ℝ) ≤ (Ct * (Submission.NetArgument.cSlope * L * T / Real.sqrt (n : ℝ))
      * (((Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * (n : ℝ))
          / Real.sqrt ((n - 1 : ℕ) : ℝ))) ^ (n - 1) := pow_nonneg hbase_nn _
  have hNnn : (0 : ℝ) ≤ (holeN ν T : ℝ) := Nat.cast_nonneg _
  have hKspnn : (0 : ℝ) ≤ Ksp C Ct * L * T :=
    le_of_lt (mul_pos (mul_pos (Ksp_pos hC1 hCt) (by linarith)) hT0)
  have hKspn : (0 : ℝ) ≤ (Ksp C Ct * L * T) ^ (n - 1) := pow_nonneg hKspnn _
  have hDsnn : (0 : ℝ) ≤ (((Dset p s L T LAC (holeN ν T) (Acoord n δ ν T)).card : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  have hmid_nn : (0 : ℝ) ≤ Real.exp (-M * (n : ℝ)) * (KA * (holeN ν T : ℝ)) ^ n :=
    mul_nonneg hexpn (pow_nonneg (mul_nonneg (le_trans zero_le_one hKA1) hNnn) n)
  -- monotone numerator estimate
  have hnum : ((PiSet.card * (Dset p s L T LAC (holeN ν T) (Acoord n δ ν T)).card : ℕ) : ℝ)
        * (Ct * (Submission.NetArgument.cSlope * L * T / Real.sqrt (n : ℝ))
            * (((Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * (n : ℝ))
                / Real.sqrt ((n - 1 : ℕ) : ℝ))) ^ (n - 1)
      ≤ CPerm ^ n * (Real.exp (-M * (n : ℝ)) * (KA * (holeN ν T : ℝ)) ^ n
            * (Ksp C Ct * L * T) ^ (n - 1)) := by
    have h1 : ((PiSet.card * (Dset p s L T LAC (holeN ν T) (Acoord n δ ν T)).card : ℕ) : ℝ)
        ≤ CPerm ^ n * (Real.exp (-M * (n : ℝ)) * (KA * (holeN ν T : ℝ)) ^ n) := by
      rw [Nat.cast_mul]
      exact mul_le_mul hPiCard hDcard hDsnn hCPnn
    have h2 := mul_le_mul_of_nonneg_right h1 hχnn
    have h3 : (CPerm ^ n * (Real.exp (-M * (n : ℝ)) * (KA * (holeN ν T : ℝ)) ^ n))
          * (Ct * (Submission.NetArgument.cSlope * L * T / Real.sqrt (n : ℝ))
              * (((Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * (n : ℝ))
                  / Real.sqrt ((n - 1 : ℕ) : ℝ))) ^ (n - 1)
        ≤ CPerm ^ n * (Real.exp (-M * (n : ℝ)) * (KA * (holeN ν T : ℝ)) ^ n
              * (Ksp C Ct * L * T) ^ (n - 1)) := by
      have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hχ hmid_nn) hCPnn
      calc (CPerm ^ n * (Real.exp (-M * (n : ℝ)) * (KA * (holeN ν T : ℝ)) ^ n))
            * (Ct * (Submission.NetArgument.cSlope * L * T / Real.sqrt (n : ℝ))
                * (((Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * (n : ℝ))
                    / Real.sqrt ((n - 1 : ℕ) : ℝ))) ^ (n - 1)
          = CPerm ^ n * ((Real.exp (-M * (n : ℝ)) * (KA * (holeN ν T : ℝ)) ^ n)
              * (Ct * (Submission.NetArgument.cSlope * L * T / Real.sqrt (n : ℝ))
                  * (((Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * (n : ℝ))
                      / Real.sqrt ((n - 1 : ℕ) : ℝ))) ^ (n - 1)) := by ring
        _ ≤ CPerm ^ n * ((Real.exp (-M * (n : ℝ)) * (KA * (holeN ν T : ℝ)) ^ n)
              * (Ksp C Ct * L * T) ^ (n - 1)) := h
        _ = CPerm ^ n * (Real.exp (-M * (n : ℝ)) * (KA * (holeN ν T : ℝ)) ^ n
              * (Ksp C Ct * L * T) ^ (n - 1)) := by ring
    exact le_trans h2 h3
  have hnet' : P.real {ω : Ω | ¬ compressible δ ν (Submission.NormalSplit.yfnOf s (B ω)) ∧
        T / 2 < Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ∧
        Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ≤ T}
      ≤ Real.exp (-(1 : ℝ) * (n : ℝ))
          + CPerm ^ n * (Real.exp (-M * (n : ℝ)) * (KA * (holeN ν T : ℝ)) ^ n
              * (Ksp C Ct * L * T) ^ (n - 1)) :=
    le_trans hnet (add_le_add (le_refl _) hnum)
  -- the annulus probability
  have hAnn : P.real {ω : Ω |
        T / 2 < Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ∧
        Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ≤ T}
      ≤ Real.exp (-(1 : ℝ) * (n : ℝ))
          + CPerm ^ n * (Real.exp (-M * (n : ℝ)) * (KA * (holeN ν T : ℝ)) ^ n
              * (Ksp C Ct * L * T) ^ (n - 1)) + a ^ n := by
    have hsubAnn : {ω : Ω |
          T / 2 < Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ∧
          Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ≤ T}
        ⊆ {ω : Ω | ¬ compressible δ ν (Submission.NormalSplit.yfnOf s (B ω)) ∧
            T / 2 < Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ∧
            Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ≤ T}
          ∪ {ω : Ω | compressible δ ν (Submission.NormalSplit.yfnOf s (B ω))} := by
      intro ω hω
      by_cases hc : compressible δ ν (Submission.NormalSplit.yfnOf s (B ω))
      · exact Or.inr hc
      · exact Or.inl ⟨hc, hω⟩
    have h1 := MeasureTheory.measureReal_mono hsubAnn (measure_ne_top P _)
    have h2 := MeasureTheory.measureReal_union_le
      ({ω : Ω | ¬ compressible δ ν (Submission.NormalSplit.yfnOf s (B ω)) ∧
            T / 2 < Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ∧
            Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ≤ T})
      ({ω : Ω | compressible δ ν (Submission.NormalSplit.yfnOf s (B ω))}) (μ := P)
    linarith [h1, h2, hnet', hcomp]
  -- combine
  have hsub : {ω : Ω | normalLe (show 1 ≤ n by omega) (shiftMatrix s (B ω)) r ∧
        ¬ compressible δ ν (Submission.NormalSplit.yfnOf s (B ω)) ∧
        T / 2 < Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ∧
        Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ≤ T}
      ⊆ {ω : Ω |
        T / 2 < Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ∧
        Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ≤ T} := by
    intro ω hω
    exact hω.2.2
  have hfin : P.real {ω : Ω | normalLe (show 1 ≤ n by omega) (shiftMatrix s (B ω)) r ∧
        ¬ compressible δ ν (Submission.NormalSplit.yfnOf s (B ω)) ∧
        T / 2 < Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ∧
        Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ≤ T}
      ≤ (L * max (2 * T) r) * P.real {ω : Ω |
        T / 2 < Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ∧
        Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ≤ T} := by
    calc P.real {ω : Ω | normalLe (show 1 ≤ n by omega) (shiftMatrix s (B ω)) r ∧
        ¬ compressible δ ν (Submission.NormalSplit.yfnOf s (B ω)) ∧
        T / 2 < Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ∧
        Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ≤ T}
        ≤ P.real {ω : Ω | normalLe (show 1 ≤ n by omega) (shiftMatrix s (B ω)) r ∧
            T / 2 < Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ∧
            Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ≤ T} := by
          exact MeasureTheory.measureReal_mono (fun ω hω => ⟨hω.1, hω.2.2⟩) (measure_ne_top P _)
      _ ≤ (L * max (2 * T) r) * P.real {ω : Ω |
            T / 2 < Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ∧
            Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ≤ T} := hfib
  have hLmax0 : 0 ≤ L * max (2 * T) r := by
    have h2T : T ≤ 2 * T := by linarith
    have : 0 ≤ max (2 * T) r := le_trans (le_trans hT0.le h2T) (le_max_left _ _)
    exact mul_nonneg (by linarith) this
  calc P.real {ω : Ω | normalLe (show 1 ≤ n by omega) (shiftMatrix s (B ω)) r ∧
        ¬ compressible δ ν (Submission.NormalSplit.yfnOf s (B ω)) ∧
        T / 2 < Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ∧
        Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ≤ T}
      ≤ (L * max (2 * T) r) * P.real {ω : Ω |
        T / 2 < Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ∧
        Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ≤ T} := hfin
    _ ≤ (L * max (2 * T) r) *
        (Real.exp (-(1 : ℝ) * (n : ℝ))
          + CPerm ^ n * (Real.exp (-M * (n : ℝ)) * (KA * (holeN ν T : ℝ)) ^ n
              * (Ksp C Ct * L * T) ^ (n - 1))
          + a ^ n) := mul_le_mul_of_nonneg_left hAnn hLmax0


/-- `Dset` cardinality bound with `LAC` and `K_A` chosen independently of `M`. -/
theorem Dset_card_le_M {p : I} {ε : ℝ} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    (hε₀ : 0 < ε) (hεp : ε < (p : ℝ))
    {δ ν : ℝ} (hδ0 : 0 < δ) (hδ12 : δ ≤ 1 / 2) (hν0 : 0 < ν) (hν1 : ν ≤ 1) :
    ∃ LAC : ℝ, 0 < LAC ∧ ∃ K_A : ℝ, 1 ≤ K_A ∧
      ∀ (M : ℝ), 1 ≤ M → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ T : ℝ, 0 < T → T ≤ ν / 2 →
        ((holeN ν T : ℝ) * (1 - (p : ℝ) + ε) ^ n ≤ 1) → ∀ (s L : ℝ),
          ((Dset p s L T LAC (holeN ν T) (Acoord n δ ν T)).card : ℝ)
            ≤ Real.exp (-M * (n : ℝ)) * (K_A * (holeN ν T : ℝ)) ^ n := by
  rcases Submission.CorAc2.cor_anticoncentration hp₀ hp₁ hδ0 hδ12 hε₀ hεp with
    ⟨LAC, hLACpos, hbody⟩
  rcases Submission.Section5D.Acoord_hrad hδ0 hδ12 hν0 hν1 with ⟨nrad, hnrad1, hradb⟩
  rcases Submission.Section5D.Acoord_prod_bound hδ0 hδ12 hν0 hν1 with
    ⟨KA, hKA1, nprod, hnprod1, hprodb⟩
  refine ⟨LAC, hLACpos, KA, hKA1, ?_⟩
  intro M hM
  rcases hbody M hM with ⟨η, nAC, hη, hnAC1, hAC⟩
  refine ⟨max (max nAC nrad) nprod, ?_⟩
  intro n hn T hT0 hTν hNa s L
  have ha0 : 0 < 1 - (p : ℝ) + ε := by
    have := p.2.2; linarith
  have hNa' : (holeN ν T : ℝ) ≤ (1 / (1 - (p : ℝ) + ε)) ^ n := by
    rw [one_div, inv_pow, inv_eq_one_div]
    exact (le_div_iff₀ (pow_pos ha0 n)).mpr hNa
  have hnAC : nAC ≤ n := le_trans (le_trans (le_max_left nAC nrad) (le_max_left _ _)) hn
  have hnrad : nrad ≤ n := le_trans (le_trans (le_max_right nAC nrad) (le_max_left _ _)) hn
  have hnprod : nprod ≤ n := le_trans (le_max_right _ _) hn
  have hN1 : 1 ≤ holeN ν T := Submission.Section5D.holeN_ge_one hT0 hν0 hTν
  have hAdm : Submission.Admissible.Admissible (holeN ν T) n n δ (Acoord n δ ν T) :=
    Submission.Section5D.Acoord_admissible hδ0 hδ12 hν0 hν1 n T hT0 hTν
  have hrad : ∀ j : Fin n, ∀ a : ℤ, a ∈ Acoord n δ ν T j →
      |a| ≤ ((n * holeN ν T : ℕ) : ℤ) := by
    intro j a ha
    exact hradb n hnrad T hT0 hTν j a ha
  have hsym : ∀ j : Fin n, ∀ a : ℤ, a ∈ Acoord n δ ν T j → -a ∈ Acoord n δ ν T j :=
    fun j a ha => Submission.Section5D.Acoord_symm ha
  have hcf := hAC n hnAC (holeN ν T) hN1 hNa' (Acoord n δ ν T) hAdm hrad hsym
  have hcard : ((Dset p s L T LAC (holeN ν T) (Acoord n δ ν T)).card : ℝ)
      ≤ (Submission.CorAc2.cfCount LAC (holeN ν T) n p (Acoord n δ ν T) : ℝ) := by
    exact_mod_cast Submission.NetArgument.Dset_card_le_cfCount p s L T LAC (holeN ν T)
      (Acoord n δ ν T)
  have hprod := hprodb n hnprod T hT0 hTν
  have hexp0 : (0 : ℝ) ≤ Real.exp (-M * (n : ℝ)) := le_of_lt (Real.exp_pos _)
  calc ((Dset p s L T LAC (holeN ν T) (Acoord n δ ν T)).card : ℝ)
      ≤ (Submission.CorAc2.cfCount LAC (holeN ν T) n p (Acoord n δ ν T) : ℝ) := hcard
    _ ≤ Real.exp (-M * (n : ℝ))
          * (∏ j : Fin n, (((Acoord n δ ν T j).card : ℕ) : ℝ)) := hcf
    _ ≤ Real.exp (-M * (n : ℝ)) * (KA * (holeN ν T : ℝ)) ^ n :=
        mul_le_mul_of_nonneg_left hprod hexp0


/-- The index at which the `Dset` cap is first exceeded, with its defining bounds. -/
lemma exists_J {n : ℕ} (hn2 : 2 ≤ n) {ν a K : ℝ} (hν0 : 0 < ν) (ha0 : 0 < a)
    (hahalf : 1 / 2 ≤ a) (hK : 0 < K) (hn2pow : 2 * K / ν ≤ (2 : ℝ) ^ n) :
    ∃ J : ℕ, (∀ j, j < J → (holeN ν (Tj K n j) : ℝ) * a ^ n ≤ 1) ∧
      (1 < (holeN ν (Tj K n J) : ℝ) * a ^ n) ∧ J ≤ 2 * n := by
  have hn1 : 1 ≤ n := by omega
  have hwit : 1 < (holeN ν (Tj K n (2 * n)) : ℝ) * a ^ n := by
    have hTval : Tj K n (2 * n) = K / (Real.sqrt (n : ℝ) * (4 : ℝ) ^ n) := by
      unfold Tj
      rw [show (2 : ℝ) ^ (2 * n) = (4 : ℝ) ^ n by
        rw [pow_mul, show (2 : ℝ) ^ 2 = 4 by norm_num]]
    have hνT : ν / Tj K n (2 * n) = ν * Real.sqrt (n : ℝ) * (4 : ℝ) ^ n / K := by
      rw [hTval]; field_simp
    have h2K : (2 : ℝ) * K ≤ (2 : ℝ) ^ n * ν := (div_le_iff₀ hν0).mp hn2pow
    have hA : (2 : ℝ) ≤ ν * (2 : ℝ) ^ n / K := by
      rw [le_div_iff₀ hK]; linarith [h2K]
    have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]; exact_mod_cast hn1
    have h2n1 : (2 : ℝ) ≤ (2 : ℝ) ^ n := by
      calc (2 : ℝ) = (2 : ℝ) ^ 1 := by norm_num
        _ ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hn1
    have h4n : ν * (4 : ℝ) ^ n / K = (ν * (2 : ℝ) ^ n / K) * (2 : ℝ) ^ n := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]; ring
    have hle : (2 : ℝ) + (2 : ℝ) ^ n ≤ ν * Real.sqrt (n : ℝ) * (4 : ℝ) ^ n / K := by
      rw [show ν * Real.sqrt (n : ℝ) * (4 : ℝ) ^ n / K
          = Real.sqrt (n : ℝ) * (ν * (4 : ℝ) ^ n / K) by ring, h4n]
      have h5 : (2 : ℝ) * (2 : ℝ) ^ n ≤ (ν * (2 : ℝ) ^ n / K) * (2 : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right hA (by positivity)
      have h6 : (2 : ℝ) + (2 : ℝ) ^ n ≤ (2 : ℝ) * (2 : ℝ) ^ n := by nlinarith
      have h7 : (1 : ℝ) * ((ν * (2 : ℝ) ^ n / K) * (2 : ℝ) ^ n)
          ≤ Real.sqrt (n : ℝ) * ((ν * (2 : ℝ) ^ n / K) * (2 : ℝ) ^ n) := by
        have h8 : (0 : ℝ) ≤ (ν * (2 : ℝ) ^ n / K) * (2 : ℝ) ^ n := by positivity
        linarith [mul_le_mul_of_nonneg_right hsqrt1 h8]
      linarith [h5, h6, h7]
    have hm : 2 + 2 ^ n ≤ ⌊ν / Tj K n (2 * n)⌋₊ := by
      apply Nat.le_floor
      rw [hνT]
      rw [show ((2 + 2 ^ n : ℕ) : ℝ) = 2 + (2 : ℝ) ^ n by push_cast; ring]
      exact hle
    have hm1 : 1 ≤ ⌊ν / Tj K n (2 * n)⌋₊ := by
      have h2npos : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
      omega
    have hh : (1 + 2 ^ n : ℕ) ≤ holeN ν (Tj K n (2 * n)) := by
      unfold holeN
      omega
    have hcast : ((1 + 2 ^ n : ℕ) : ℝ) = 1 + (2 : ℝ) ^ n := by push_cast; ring
    have hge : (1 + (2 : ℝ) ^ n) ≤ (holeN ν (Tj K n (2 * n)) : ℝ) := by
      rw [← hcast]; exact_mod_cast hh
    have hprod : (1 + (2 : ℝ) ^ n) * a ^ n ≤ (holeN ν (Tj K n (2 * n)) : ℝ) * a ^ n :=
      mul_le_mul_of_nonneg_right hge (pow_nonneg ha0.le n)
    have hgt : 1 < (1 + (2 : ℝ) ^ n) * a ^ n := by
      have h2a : (1 : ℝ) ≤ 2 * a := by linarith
      have h2an : (1 : ℝ) ≤ (2 * a) ^ n := one_le_pow₀ h2a
      have han : 0 < a ^ n := pow_pos ha0 n
      rw [add_mul, ← mul_pow]
      linarith
    linarith [hprod, hgt]
  let J : ℕ := Nat.find (p := fun j => 1 < (holeN ν (Tj K n j) : ℝ) * a ^ n) ⟨2 * n, hwit⟩
  have hJmin : 1 < (holeN ν (Tj K n J) : ℝ) * a ^ n := by
    dsimp only [J]
    exact Nat.find_spec (p := fun j => 1 < (holeN ν (Tj K n j) : ℝ) * a ^ n) ⟨2 * n, hwit⟩
  have hJcap : ∀ j, j < J → (holeN ν (Tj K n j) : ℝ) * a ^ n ≤ 1 := by
    intro j hj
    dsimp only [J] at hj
    exact not_lt.mp (Nat.find_min (p := fun j => 1 < (holeN ν (Tj K n j) : ℝ) * a ^ n)
      ⟨2 * n, hwit⟩ hj)
  have hJle : J ≤ 2 * n := by
    dsimp only [J]
    exact Nat.find_le (p := fun j => 1 < (holeN ν (Tj K n j) : ℝ) * a ^ n) hwit
  exact ⟨J, hJcap, hJmin, hJle⟩

/-- `holeN ν T · T ≤ ν` for every `T > 0`. -/
lemma holeN_mul_le {ν T : ℝ} (hν0 : 0 ≤ ν) (hT : 0 < T) :
    (holeN ν T : ℝ) * T ≤ ν := by
  have h1 : (holeN ν T : ℝ) ≤ (⌊ν / T⌋₊ : ℝ) := by
    unfold holeN
    exact_mod_cast Nat.sub_le ⌊ν / T⌋₊ 1
  have h2 : (⌊ν / T⌋₊ : ℝ) ≤ ν / T := Nat.floor_le (div_nonneg hν0 hT.le)
  calc (holeN ν T : ℝ) * T ≤ (ν / T) * T := mul_le_mul_of_nonneg_right (le_trans h1 h2) hT.le
    _ = ν := by field_simp


/-- The exponential scale `exp(−n)` is below `a^n` when `a ≥ 1/2`. -/
lemma exp_neg_le_pow {n : ℕ} {a : ℝ} (ha : 1 / 2 ≤ a) :
    Real.exp (-(n : ℝ)) ≤ a ^ n := by
  have he : Real.exp (-1) ≤ 1 / 2 := by
    have h1 : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
    have h2 : 1 / Real.exp 1 < 1 / (2 : ℝ) := one_div_lt_one_div_of_lt (by norm_num) h1
    rw [Real.exp_neg, inv_eq_one_div]
    exact le_of_lt h2
  have hea : Real.exp (-1) ≤ a := le_trans he ha
  have hexp : Real.exp (-(n : ℝ)) = Real.exp (-1) ^ n := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hexp]
  exact pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) hea n


/-- `L·max(2T, r) ≤ L·2T + L·r` for positive data. -/
lemma Lmax_le {L T r : ℝ} (hL : 0 ≤ L) (hT : 0 < T) (hr : 0 < r) :
    L * max (2 * T) r ≤ L * 2 * T + L * r := by
  have hmax : max (2 * T) r ≤ 2 * T + r := by
    rw [max_le_iff]; exact ⟨by linarith, by linarith⟩
  calc L * max (2 * T) r ≤ L * (2 * T + r) := mul_le_mul_of_nonneg_left hmax hL
    _ = L * 2 * T + L * r := by ring

/-- `x^(n−1) = x^n / x` for `x > 0`, `n ≥ 1`. -/
lemma pow_pred_eq_div {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 1 ≤ n) :
    x ^ (n - 1) = x ^ n / x := by
  rw [eq_div_iff hx.ne']
  have h1 : n - 1 + 1 = n := Nat.sub_add_cancel hn
  conv_rhs => rw [← h1, pow_succ]

/-- **Uniform bound on the net term.**  Under the `Dset` cap `N·a^n ≤ 1` and
`N·T ≤ ν`, the per-annulus net term is at most `(1/16)^n/(QL·ν)`, uniformly in
the annulus. -/
lemma Fj_le {n : ℕ} (hn1 : 1 ≤ n) {ν a QL CPerm M KA : ℝ}
    (hν0 : 0 < ν) (ha0 : 0 < a) (hQL : 0 < QL) (hCP1 : 1 ≤ CPerm) (hKA1 : 1 ≤ KA)
    (hM : 1 ≤ M) (hQ : CPerm * Real.exp (-M) * KA * QL * ν / a ≤ 1 / 16)
    {N T : ℝ} (hN0 : 0 ≤ N) (hT0 : 0 < T) (hNT : N * T ≤ ν) (hNcap : N * a ^ n ≤ 1) :
    CPerm ^ n * (Real.exp (-M * (n : ℝ)) * (KA * N) ^ n * (QL * T) ^ (n - 1))
      ≤ (1 / 16) ^ n / (QL * ν) := by
  have hB : 0 ≤ CPerm * Real.exp (-M) * KA := by
    have h1 : 0 < Real.exp (-M) := Real.exp_pos _
    have : (0:ℝ) ≤ CPerm := by linarith
    have : (0:ℝ) ≤ KA := by linarith
    positivity
  have hstep1 : N ^ n * T ^ (n - 1) = N * (N * T) ^ (n - 1) := by
    rw [mul_pow]
    have hpow : N ^ n = N ^ (n - 1) * N := by
      conv_lhs => rw [← Nat.sub_add_cancel hn1]
      rw [pow_succ]
    rw [hpow]; ring
  have hexpM : Real.exp (-M * (n : ℝ)) = Real.exp (-M) ^ n := by
    rw [show -M * (n : ℝ) = (n : ℝ) * (-M) by ring, Real.exp_nat_mul]
  have hA : CPerm ^ n * (Real.exp (-M * (n : ℝ)) * (KA * N) ^ n * (QL * T) ^ (n - 1))
      = (CPerm * Real.exp (-M) * KA) ^ n * QL ^ (n - 1) * (N ^ n * T ^ (n - 1)) := by
    rw [hexpM, mul_pow, mul_pow]
    ring
  rw [hA, hstep1]
  have hNν : N * ν ^ (n - 1) ≤ ν ^ (n - 1) / a ^ n := by
    rw [le_div_iff₀ (pow_pos ha0 n)]
    calc N * ν ^ (n - 1) * a ^ n = ν ^ (n - 1) * (N * a ^ n) := by ring
      _ ≤ ν ^ (n - 1) * 1 := mul_le_mul_of_nonneg_left hNcap (pow_nonneg hν0.le (n-1))
      _ = ν ^ (n - 1) := by ring
  have hpowN : (0:ℝ) ≤ N * (N * T) ^ (n - 1) :=
    mul_nonneg hN0 (pow_nonneg (mul_nonneg hN0 hT0.le) (n-1))
  have hQLν : (0:ℝ) < QL * ν := mul_pos hQL hν0
  calc (CPerm * Real.exp (-M) * KA) ^ n * QL ^ (n - 1) * (N * (N * T) ^ (n - 1))
      ≤ (CPerm * Real.exp (-M) * KA) ^ n * QL ^ (n - 1) * (N * ν ^ (n - 1)) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hN0 hT0.le) hNT (n-1)) hN0
        · positivity
    _ ≤ (CPerm * Real.exp (-M) * KA) ^ n * QL ^ (n - 1) * (ν ^ (n - 1) / a ^ n) := by
        apply mul_le_mul_of_nonneg_left hNν
        positivity
    _ = (CPerm * Real.exp (-M) * KA * QL * ν / a) ^ n / (QL * ν) := by
        have hpow : ∀ x : ℝ, 0 < x → x ^ (n - 1) = x ^ n / x :=
          fun x hx => pow_pred_eq_div hx hn1
        rw [hpow QL hQL, hpow ν hν0]
        rw [div_pow]
        rw [show CPerm * Real.exp (-M) * KA * QL * ν
              = (CPerm * Real.exp (-M) * KA) * (QL * ν) by ring, mul_pow]
        field_simp
        ring
    _ ≤ (1 / 16) ^ n / (QL * ν) :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hQ n) hQLν.le


/-- **Main summation theorem of the net argument.**  Summing the per-annulus
bounds and the tail yields
`P{normalLe r} ≤ (6Lν+1)·a^n + (1/16)^n + 4L·r`. -/
theorem net_normal_bound {n : ℕ} (hn2 : 2 ≤ n) {p : I}
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) ≤ 1 / 2) (hp1' : (p : ℝ) < 1)
    {δ ν : ℝ} (hδ0 : 0 < δ) (hδ12 : δ ≤ 1 / 2) (hν0 : 0 < ν) (hν1 : ν ≤ 1)
    {M LAC CPerm KA a s L K : ℝ}
    (hM : 1 ≤ M) (hCP1 : 1 ≤ CPerm) (hKA1 : 1 ≤ KA)
    (ha0 : 0 < a) (ha1 : a < 1) (hahalf : 1 / 2 ≤ a)
    (hL1 : 1 ≤ L) (hLAC : LAC ≤ L * ν / 256)
    (hK : 0 < K)
    (hs : |s| ≤ 1) (hsp : |s + (p : ℝ)| ≤ 1)
    {C : ℝ} (hC1 : 1 ≤ C) {Ct : ℝ} (hCt : 0 < Ct) (hCt1 : 1 ≤ Ct)
    (hQ1 : CPerm * Real.exp (-M) * KA * Ksp C Ct * L * ν / a ≤ 1 / 16)
    (PiSet : Finset (Equiv.Perm (Fin n))) (hPiCard : (PiSet.card : ℝ) ≤ CPerm ^ n)
    (hPi : ∀ (T th : ℝ), 0 < T → T ≤ ν / 2 → 0 < th → T / 2 ≤ th → th ≤ T →
      ∀ (y : Fin n → ℝ), sqNorm y = 1 → ¬ compressible δ ν y → ∀ (w : Fin n → ℤ),
        (∀ i : Fin n, |(Real.sqrt (n : ℝ) / th) * y i - (w i : ℝ)| ≤ 1) →
        ∃ π ∈ PiSet, ∀ i : Fin n, w (π i) ∈ Acoord n δ ν T i)
    (hKthr : ∀ x : Fin n → ℝ, sqNorm x = 1 → ¬ compressible δ ν x →
      Submission.Threshold.threshold p x L ≤ K / Real.sqrt (n : ℝ))
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → Matrix (Fin n) (Fin n) ℝ) (hBmeas : ∀ i j : Fin n, Measurable (fun ω => B ω i j))
    (hBind : ProbabilityTheory.iIndepFun (fun x : Fin n × Fin n => (B · x.1 x.2)) P)
    (hBlaw : ∀ i j : Fin n, HasLaw (B · i j) (bernoulliMeasure 1 0 p) P)
    (hBpt : ∀ (i j : Fin n) (ω : Ω), |B ω i j - (p : ℝ)| ≤ 1)
    (hper : ∀ T : ℝ, 0 < T → T ≤ ν / 2 → ∀ y : Fin n → ℤ, slopeOk p s L T y →
      P.real {ω : Ω | (∑ k : Fin (n - 1),
          (Submission.NetArgument.qSum (B ω) s y k) ^ 2)
            ≤ ((Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * (n : ℝ)) ^ 2}
        ≤ (Ct * (Submission.NetArgument.cSlope * L * T / Real.sqrt (n : ℝ))
            * (((Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) * (n : ℝ))
                / Real.sqrt ((n - 1 : ℕ) : ℝ))) ^ (n - 1))
    (hD : ∀ T : ℝ, 0 < T → T ≤ ν / 2 → (holeN ν T : ℝ) * a ^ n ≤ 1 →
      ((Dset p s L T LAC (holeN ν T) (Acoord n δ ν T)).card : ℝ)
        ≤ Real.exp (-M * (n : ℝ)) * (KA * (holeN ν T : ℝ)) ^ n)
    {G : Set Ω} (hGmeas : MeasurableSet G)
    (hGprob : P.real G ≥ 1 - Real.exp (-(1 : ℝ) * (n : ℝ)))
    (hGsub : G ⊆ {ω : Ω | ∀ v : Fin n → ℝ,
        (∑ k : Fin (n - 1),
            ((∑ i : Fin n, (B ω i (Submission.GeoBridge.emb k) - (p : ℝ)) * v i)) ^ 2)
          ≤ (C * Real.sqrt (n : ℝ)) ^ 2 * (∑ i : Fin n, (v i) ^ 2)})
    (hcomp : P.real {ω : Ω | compressible δ ν (Submission.NormalSplit.yfnOf s (B ω))}
      ≤ a ^ n)
    (hnK : K / Real.sqrt (n : ℝ) ≤ ν / 2)
    (hn2pow : 2 * K / ν ≤ (2 : ℝ) ^ n)
    (hn16 : 2 * (n : ℝ) * (1 / 16) ^ n ≤ 1)
    (hne : 2 * (n : ℝ) * Real.exp (-(n : ℝ)) ≤ 1)
    (hna : 2 * (n : ℝ) * a ^ n ≤ 1)
    {r : ℝ} (hr : 0 < r) :
    P.real {ω : Ω | normalLe (show 1 ≤ n by omega) (shiftMatrix s (B ω)) r}
      ≤ (6 * L * ν + 1 + 4 * K / (Ksp C Ct * ν)) * a ^ n
        + (3 * L + 1 / (Ksp C Ct * ν)) * r := by
  have hn1 : 1 ≤ n := by omega
  have hsN : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn1)
  have hsR : 0 ≤ Real.sqrt (n : ℝ) := hsN.le
  have hTN : K / Real.sqrt (n : ℝ) ≤ ν / 2 := hnK
  have hKN0 : 0 ≤ K / Real.sqrt (n : ℝ) := div_nonneg hK.le hsR
  have hL0 : (0 : ℝ) ≤ L := by linarith
  have hKsp0 : 0 < Ksp C Ct := Ksp_pos hC1 hCt
  have hKspLν0 : 0 < Ksp C Ct * L * ν := by positivity
  obtain ⟨J, hJcap, hJmin, hJle⟩ := exists_J hn2 hν0 ha0 hahalf hK hn2pow
  set E := Real.exp (-(1 : ℝ) * (n : ℝ)) with hEdef
  set C16 := (1 / 16) ^ n / (Ksp C Ct * L * ν) with hC16def
  have hE0 : 0 ≤ E := by rw [hEdef]; exact Real.exp_nonneg _
  have hEa : E ≤ a ^ n := by
    rw [hEdef]
    have heq : Real.exp (-(1 : ℝ) * (n : ℝ)) = Real.exp (-(n : ℝ)) := by congr 1; ring
    rw [heq]; exact exp_neg_le_pow hahalf
  have hC160 : 0 ≤ C16 := by
    rw [hC16def]
    exact div_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 1/16) n) hKspLν0.le
  have hne' : 2 * (n : ℝ) * E ≤ 1 := by
    rw [hEdef]
    have heq : Real.exp (-(1 : ℝ) * (n : ℝ)) = Real.exp (-(n : ℝ)) := by congr 1; ring
    rw [heq]; exact hne
  have hKsp1 : (1 : ℝ) ≤ Ksp C Ct := by
    rw [Ksp]
    have h10 : (1 : ℝ) ≤ Real.sqrt (2 * C ^ 2 + 24 / 11) + 1 := by
      have := Real.sqrt_nonneg (2 * C ^ 2 + 24 / 11); linarith
    have h11 : (1 : ℝ) ≤ Submission.NetArgument.cSlope := by
      rw [Submission.NetArgument.cSlope]; norm_num
    have h12 : (1 : ℝ) ≤ Ct * Submission.NetArgument.cSlope :=
      one_le_mul_of_one_le_of_one_le hCt1 h11
    have h13 : (1 : ℝ) ≤ Ct * Submission.NetArgument.cSlope * 2 := by linarith
    have h14 : (1 : ℝ) ≤ (Ct * Submission.NetArgument.cSlope * 2)
        * (Real.sqrt (2 * C ^ 2 + 24 / 11) + 1) :=
      one_le_mul_of_one_le_of_one_le h13 h10
    linarith [h14]
  have hTjpos : ∀ j, 0 < Tj K n j := fun j => Tj_pos hK hn1 j
  have hTjle : ∀ j ≤ J, Tj K n j ≤ ν / 2 := by
    intro j _
    calc Tj K n j ≤ Tj K n 0 := Tj_anti hK hn1 (Nat.zero_le j)
      _ = K / Real.sqrt (n : ℝ) := Tj_zero K n
      _ ≤ ν / 2 := hTN
  have hTJle : Tj K n J ≤ ν * a ^ n := by
    have h1 := holeN_mul_le (ν := ν) (T := Tj K n J) hν0.le (hTjpos J)
    have h2 : ((holeN ν (Tj K n J) : ℝ) * a ^ n) * Tj K n J ≤ ν * a ^ n := by
      calc ((holeN ν (Tj K n J) : ℝ) * a ^ n) * Tj K n J
          = ((holeN ν (Tj K n J) : ℝ) * Tj K n J) * a ^ n := by ring
        _ ≤ ν * a ^ n := mul_le_mul_of_nonneg_right h1 (pow_nonneg ha0.le n)
    have hstep : Tj K n J < ((holeN ν (Tj K n J) : ℝ) * a ^ n) * Tj K n J := by
      calc Tj K n J = 1 * Tj K n J := (one_mul _).symm
        _ < ((holeN ν (Tj K n J) : ℝ) * a ^ n) * Tj K n J :=
            mul_lt_mul_of_pos_right hJmin (hTjpos J)
    exact le_of_lt (lt_of_lt_of_le hstep h2)
  -- geometric bound on the scales
  have hTjform : ∀ j, Tj K n j = (K / Real.sqrt (n : ℝ)) * ((1 : ℝ) / 2) ^ j := by
    intro j
    unfold Tj
    rw [one_div_pow]
    field_simp
  have hgeo2 : ∑ j ∈ Finset.range J, ((1 : ℝ) / 2) ^ j ≤ 2 := by
    have hsummable : Summable (fun j : ℕ => ((1 : ℝ) / 2) ^ j) :=
      summable_geometric_of_norm_lt_one (by norm_num : ‖((1 : ℝ) / 2)‖ < 1)
    have htsum : ∑' j : ℕ, ((1 : ℝ) / 2) ^ j = 2 := by
      rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖((1 : ℝ) / 2)‖ < 1)]
      norm_num
    have h := hsummable.sum_le_tsum (Finset.range J) (fun i _ => by positivity)
    rw [htsum] at h
    exact h
  have hTjsum : ∑ j ∈ Finset.range J, Tj K n j ≤ 2 * (K / Real.sqrt (n : ℝ)) := by
    calc ∑ j ∈ Finset.range J, Tj K n j
        = (K / Real.sqrt (n : ℝ)) * ∑ j ∈ Finset.range J, ((1 : ℝ) / 2) ^ j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => hTjform j)
      _ ≤ (K / Real.sqrt (n : ℝ)) * 2 := mul_le_mul_of_nonneg_left hgeo2 hKN0
      _ = 2 * (K / Real.sqrt (n : ℝ)) := by ring
  have hsum2L : ∑ j ∈ Finset.range J, L * 2 * Tj K n j ≤ 4 * L * (K / Real.sqrt (n : ℝ)) := by
    have h1 : ∑ j ∈ Finset.range J, L * 2 * Tj K n j
        = L * 2 * ∑ j ∈ Finset.range J, Tj K n j := by rw [Finset.mul_sum]
    rw [h1]
    calc L * 2 * ∑ j ∈ Finset.range J, Tj K n j ≤ L * 2 * (2 * (K / Real.sqrt (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hTjsum (by linarith)
      _ = 4 * L * (K / Real.sqrt (n : ℝ)) := by ring
  have hsum2L0 : (0 : ℝ) ≤ ∑ j ∈ Finset.range J, L * 2 * Tj K n j :=
    Finset.sum_nonneg (fun j _ => by have := hTjpos j; nlinarith [hL0])
  -- per-annulus bounds
  have hann : ∀ j ∈ Finset.range J,
      P.real {ω : Ω | normalLe hn1 (shiftMatrix s (B ω)) r ∧
        ¬ compressible δ ν (Submission.NormalSplit.yfnOf s (B ω)) ∧
        Tj K n (j + 1) < Submission.Threshold.threshold p
            (Submission.NormalSplit.yfnOf s (B ω)) L ∧
        Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ≤ Tj K n j}
      ≤ (L * max (2 * Tj K n j) r) * (E + C16 + a ^ n) := by
    intro j hj
    have hjJ : j < J := Finset.mem_range.mp hj
    have hTj0 : 0 < Tj K n j := hTjpos j
    have hTjν : Tj K n j ≤ ν / 2 := hTjle j (le_of_lt hjJ)
    have hNcap : (holeN ν (Tj K n j) : ℝ) * a ^ n ≤ 1 := hJcap j hjJ
    have hDc := hD (Tj K n j) hTj0 hTjν hNcap
    have hperj := hper (Tj K n j) hTj0 hTjν
    have hann0 := annulus_combined hn2 hp0 hp1 hp1' hδ0 hδ12 hν0 hν1 hM hCP1 hKA1 ha0
      hL1 hTj0 hTjν hLAC hs hsp hC1 hCt PiSet hPiCard
      (fun y hy hnc th hth0 hthh hthT w hw =>
        hPi (Tj K n j) th hTj0 hTjν hth0 hthh hthT y hy hnc w hw)
      hDc P B hBmeas hBind hBlaw hBpt hGmeas hGprob hGsub hperj hcomp hr
    have hQL0 : 0 < Ksp C Ct * L := by positivity
    have hQ1' : CPerm * Real.exp (-M) * KA * (Ksp C Ct * L) * ν / a ≤ 1 / 16 := by
      rw [show CPerm * Real.exp (-M) * KA * (Ksp C Ct * L) * ν / a
          = CPerm * Real.exp (-M) * KA * Ksp C Ct * L * ν / a by ring]
      exact hQ1
    have hFj := Fj_le (QL := Ksp C Ct * L) hn1 hν0 ha0 hQL0 hCP1 hKA1 hM hQ1'
      (N := ((holeN ν (Tj K n j) : ℕ) : ℝ)) (T := Tj K n j)
      (by positivity) hTj0 (holeN_mul_le hν0.le hTj0) hNcap
    have hEq : {ω : Ω | normalLe hn1 (shiftMatrix s (B ω)) r ∧
        ¬ compressible δ ν (Submission.NormalSplit.yfnOf s (B ω)) ∧
        Tj K n (j + 1) < Submission.Threshold.threshold p
            (Submission.NormalSplit.yfnOf s (B ω)) L ∧
        Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ≤ Tj K n j}
      = {ω : Ω | normalLe hn1 (shiftMatrix s (B ω)) r ∧
        ¬ compressible δ ν (Submission.NormalSplit.yfnOf s (B ω)) ∧
        Tj K n j / 2 < Submission.Threshold.threshold p
            (Submission.NormalSplit.yfnOf s (B ω)) L ∧
        Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ≤ Tj K n j} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      rw [Tj_succ]
    rw [hEq]
    have hLmax0 : 0 ≤ L * max (2 * Tj K n j) r :=
      mul_nonneg hL0 (le_trans (by linarith [hTj0]) (le_max_left _ _))
    have hFjC : CPerm ^ n * (Real.exp (-M * (n : ℝ))
        * (KA * (holeN ν (Tj K n j) : ℝ)) ^ n
        * (Ksp C Ct * L * Tj K n j) ^ (n - 1)) ≤ C16 := by
      rw [hC16def]; exact hFj
    refine le_trans hann0 (mul_le_mul_of_nonneg_left ?_ hLmax0)
    linarith [hFjC]
  -- the set decomposition
  have hset : {ω : Ω | normalLe hn1 (shiftMatrix s (B ω)) r ∧
        ¬ compressible δ ν (Submission.NormalSplit.yfnOf s (B ω))}
      ⊆ {ω : Ω | normalLe hn1 (shiftMatrix s (B ω)) r ∧
          Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ≤ Tj K n J}
        ∪ ⋃ j ∈ Finset.range J, {ω : Ω | normalLe hn1 (shiftMatrix s (B ω)) r ∧
            ¬ compressible δ ν (Submission.NormalSplit.yfnOf s (B ω)) ∧
            Tj K n (j + 1) < Submission.Threshold.threshold p
                (Submission.NormalSplit.yfnOf s (B ω)) L ∧
            Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ≤ Tj K n j} := by
    intro ω hω
    obtain ⟨hnl, hnc⟩ := hω
    have hsq : sqNorm (Submission.NormalSplit.yfnOf s (B ω)) = 1 :=
      Submission.GeoBridge.sqNorm_ofLp_of_unit
        (Submission.IncompReduction.nVec_unit hn1 (shiftMatrix s (B ω)))
    have hthrK : Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L
        ≤ K / Real.sqrt (n : ℝ) := hKthr _ hsq hnc
    by_cases hcase : Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L
        ≤ Tj K n J
    · exact Or.inl ⟨hnl, hcase⟩
    · have hcase' : Tj K n J < Submission.Threshold.threshold p
          (Submission.NormalSplit.yfnOf s (B ω)) L := not_le.mp hcase
      have hthr0 : Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L
          ≤ Tj K n 0 := by rw [Tj_zero]; exact hthrK
      have hwitJ : Tj K n (J + 1) < Submission.Threshold.threshold p
          (Submission.NormalSplit.yfnOf s (B ω)) L := by
        rw [Tj_succ]; linarith [hcase', hTjpos J]
      have hexj : ∃ k : ℕ, Tj K n (k + 1) < Submission.Threshold.threshold p
          (Submission.NormalSplit.yfnOf s (B ω)) L := ⟨J, hwitJ⟩
      let j0 : ℕ := Nat.find hexj
      have hj0p : Tj K n (j0 + 1) < Submission.Threshold.threshold p
          (Submission.NormalSplit.yfnOf s (B ω)) L := by
        dsimp only [j0]; exact Nat.find_spec hexj
      have hj0leJ : j0 ≤ J := by
        dsimp only [j0]; exact Nat.find_le (h := hexj) hwitJ
      have hj0thr : Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L
          ≤ Tj K n j0 := by
        rcases Nat.eq_zero_or_pos j0 with h0 | hpos
        · rw [h0]; exact hthr0
        · have hnot : ¬ (Tj K n j0 < Submission.Threshold.threshold p
              (Submission.NormalSplit.yfnOf s (B ω)) L) := by
            have hmin := Nat.find_min hexj (show j0 - 1 < Nat.find hexj by omega)
            simpa [Nat.sub_add_cancel hpos] using hmin
          exact not_lt.mp hnot
      have hj0lt : j0 < J := by
        rcases Nat.eq_zero_or_pos J with h0 | hpos
        · rw [h0] at hcase'; rw [Tj_zero] at hcase'
          exact absurd hcase' (not_lt.mpr hthrK)
        · by_contra hcon
          push_neg at hcon
          have heq : j0 = J := le_antisymm hj0leJ hcon
          rw [heq] at hj0thr
          linarith [hj0thr, hcase']
      refine Or.inr ?_
      simp only [Set.mem_iUnion, exists_prop]
      exact ⟨j0, Finset.mem_range.mpr hj0lt, hnl, hnc, hj0p, hj0thr⟩
  -- tail bound
  have htail : P.real {ω : Ω | normalLe hn1 (shiftMatrix s (B ω)) r ∧
        Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ≤ Tj K n J}
      ≤ 2 * L * ν * a ^ n + L * r := by
    have h1 := Submission.NormalSplit.normal_fiber_bound P hn1 B hBind hBlaw
      (s := s) (L := L) (S := Tj K n J) (r := r) hL1 (hTjpos J) hr
    have h2 : P.real {ω : Ω | Submission.Threshold.threshold p
        (Submission.NormalSplit.yfnOf s (B ω)) L ≤ Tj K n J} ≤ 1 :=
      MeasureTheory.measureReal_le_one
    have h3 : L * max (2 * Tj K n J) r ≤ 2 * L * ν * a ^ n + L * r := by
      calc L * max (2 * Tj K n J) r ≤ L * 2 * Tj K n J + L * r :=
            Lmax_le hL0 (hTjpos J) hr
        _ ≤ 2 * L * ν * a ^ n + L * r := by
            have h9 : 2 * L * Tj K n J ≤ 2 * L * (ν * a ^ n) :=
              mul_le_mul_of_nonneg_left hTJle (by linarith)
            linarith [h9]
        _ ≤ 2 * L * ν * a ^ n + L * r := by
            have h9 : 2 * L * Tj K n J ≤ 2 * L * (ν * a ^ n) :=
              mul_le_mul_of_nonneg_left hTJle (by linarith)
            linarith [h9]
    have hLmax0 : 0 ≤ L * max (2 * Tj K n J) r :=
      mul_nonneg hL0 (le_trans (by linarith [hTjpos J]) (le_max_left _ _))
    calc P.real {ω : Ω | normalLe hn1 (shiftMatrix s (B ω)) r ∧
          Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ≤ Tj K n J}
        ≤ (L * max (2 * Tj K n J) r) * P.real {ω : Ω | Submission.Threshold.threshold p
            (Submission.NormalSplit.yfnOf s (B ω)) L ≤ Tj K n J} := h1
      _ ≤ (L * max (2 * Tj K n J) r) * 1 := mul_le_mul_of_nonneg_left h2 hLmax0
      _ ≤ 2 * L * ν * a ^ n + L * r := by rw [mul_one]; exact h3
  -- bound the annulus sum
  have hsumUp : ∑ j ∈ Finset.range J, P.real {ω : Ω | normalLe hn1 (shiftMatrix s (B ω)) r ∧
        ¬ compressible δ ν (Submission.NormalSplit.yfnOf s (B ω)) ∧
        Tj K n (j + 1) < Submission.Threshold.threshold p
            (Submission.NormalSplit.yfnOf s (B ω)) L ∧
        Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ≤ Tj K n j}
      ≤ (4 * L * ν + 4 * K / (Ksp C Ct * ν)) * a ^ n
        + (2 * L + 1 / (Ksp C Ct * ν)) * r := by
    have hstep1 : ∑ j ∈ Finset.range J, P.real {ω : Ω | normalLe hn1 (shiftMatrix s (B ω)) r ∧
        ¬ compressible δ ν (Submission.NormalSplit.yfnOf s (B ω)) ∧
        Tj K n (j + 1) < Submission.Threshold.threshold p
            (Submission.NormalSplit.yfnOf s (B ω)) L ∧
        Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ≤ Tj K n j}
        ≤ ∑ j ∈ Finset.range J, (L * 2 * Tj K n j + L * r) * (E + C16 + a ^ n) := by
      apply Finset.sum_le_sum
      intro j hj
      have h := hann j hj
      have hX0 : 0 ≤ E + C16 + a ^ n := by linarith [hE0, hC160, pow_nonneg ha0.le n]
      have hmax : L * max (2 * Tj K n j) r ≤ L * 2 * Tj K n j + L * r :=
        Lmax_le hL0 (hTjpos j) hr
      exact le_trans h (mul_le_mul_of_nonneg_right hmax hX0)
    refine le_trans hstep1 ?_
    have hsummand : ∀ j : ℕ, (L * 2 * Tj K n j + L * r) * (E + C16 + a ^ n)
        = L * 2 * Tj K n j * E + L * 2 * Tj K n j * C16 + L * 2 * Tj K n j * a ^ n
          + (L * r * E + L * r * C16 + L * r * a ^ n) := fun j => by ring
    have hsplit : ∑ j ∈ Finset.range J, (L * 2 * Tj K n j + L * r) * (E + C16 + a ^ n)
        = ((∑ j ∈ Finset.range J, L * 2 * Tj K n j * E)
            + (∑ j ∈ Finset.range J, L * 2 * Tj K n j * C16)
            + (∑ j ∈ Finset.range J, L * 2 * Tj K n j * a ^ n))
          + ((∑ j ∈ Finset.range J, L * r * E)
            + (∑ j ∈ Finset.range J, L * r * C16)
            + (∑ j ∈ Finset.range J, L * r * a ^ n)) := by
      simp only [hsummand]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [hsplit]
    have hSE : ∑ j ∈ Finset.range J, L * 2 * Tj K n j * E
        = (∑ j ∈ Finset.range J, L * 2 * Tj K n j) * E := (Finset.sum_mul _ _ _).symm
    have hSC : ∑ j ∈ Finset.range J, L * 2 * Tj K n j * C16
        = (∑ j ∈ Finset.range J, L * 2 * Tj K n j) * C16 := (Finset.sum_mul _ _ _).symm
    have hSA : ∑ j ∈ Finset.range J, L * 2 * Tj K n j * a ^ n
        = (∑ j ∈ Finset.range J, L * 2 * Tj K n j) * a ^ n := (Finset.sum_mul _ _ _).symm
    rw [hSE, hSC, hSA]
    -- bound the three "scale" sums
    have hb1 : (∑ j ∈ Finset.range J, L * 2 * Tj K n j) * E ≤ 2 * L * ν * a ^ n := by
      have h4 : (∑ j ∈ Finset.range J, L * 2 * Tj K n j) * E
          ≤ (4 * L * (K / Real.sqrt (n : ℝ))) * E :=
        mul_le_mul_of_nonneg_right hsum2L hE0
      have h5 : (4 * L * (K / Real.sqrt (n : ℝ))) * E
          ≤ (4 * L * (K / Real.sqrt (n : ℝ))) * a ^ n :=
        mul_le_mul_of_nonneg_left hEa (by positivity)
      have h6 : (4 * L * (K / Real.sqrt (n : ℝ))) * a ^ n ≤ 2 * L * ν * a ^ n := by
        have h7 : 4 * L * (K / Real.sqrt (n : ℝ)) ≤ 4 * L * (ν / 2) :=
          mul_le_mul_of_nonneg_left hTN (by linarith)
        calc (4 * L * (K / Real.sqrt (n : ℝ))) * a ^ n ≤ (4 * L * (ν / 2)) * a ^ n :=
              mul_le_mul_of_nonneg_right h7 (pow_nonneg ha0.le n)
          _ = 2 * L * ν * a ^ n := by ring
      linarith
    have hb2 : (∑ j ∈ Finset.range J, L * 2 * Tj K n j) * C16
        ≤ (4 * K / (Ksp C Ct * ν)) * a ^ n := by
      have h4 : (∑ j ∈ Finset.range J, L * 2 * Tj K n j) * C16
          ≤ (4 * L * (K / Real.sqrt (n : ℝ))) * C16 :=
        mul_le_mul_of_nonneg_right hsum2L hC160
      have halg : (4 * L * (K / Real.sqrt (n : ℝ))) * C16
          = (4 * K / (Ksp C Ct * ν)) * ((1 / Real.sqrt (n : ℝ)) * (1 / 16) ^ n) := by
        rw [hC16def]
        field_simp
      have h8 : (1 / Real.sqrt (n : ℝ)) ≤ 1 := by
        rw [div_le_one hsN]
        rw [Real.le_sqrt (by norm_num) (by positivity)]
        exact_mod_cast hn1
      have h9 : (0 : ℝ) ≤ (4 * K) / (Ksp C Ct * ν) :=
        div_nonneg (by positivity) (by positivity)
      have h10 : ((1 / Real.sqrt (n : ℝ)) * (1 / 16) ^ n) ≤ a ^ n := by
        calc (1 / Real.sqrt (n : ℝ)) * (1 / 16) ^ n ≤ 1 * (1 / 16) ^ n :=
              mul_le_mul_of_nonneg_right h8 (pow_nonneg (by norm_num) n)
          _ ≤ a ^ n := by
              rw [one_mul]
              exact pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/16)
                (le_trans (by norm_num : (1:ℝ)/16 ≤ 1/2) hahalf) n
      calc (∑ j ∈ Finset.range J, L * 2 * Tj K n j) * C16
          ≤ (4 * L * (K / Real.sqrt (n : ℝ))) * C16 := h4
        _ = (4 * K / (Ksp C Ct * ν)) * ((1 / Real.sqrt (n : ℝ)) * (1 / 16) ^ n) := halg
        _ ≤ (4 * K / (Ksp C Ct * ν)) * a ^ n := mul_le_mul_of_nonneg_left h10 h9
    have hb3 : (∑ j ∈ Finset.range J, L * 2 * Tj K n j) * a ^ n ≤ 2 * L * ν * a ^ n := by
      have h4 : (∑ j ∈ Finset.range J, L * 2 * Tj K n j) * a ^ n
          ≤ (4 * L * (K / Real.sqrt (n : ℝ))) * a ^ n :=
        mul_le_mul_of_nonneg_right hsum2L (pow_nonneg ha0.le n)
      have h7 : 4 * L * (K / Real.sqrt (n : ℝ)) ≤ 4 * L * (ν / 2) :=
        mul_le_mul_of_nonneg_left hTN (by linarith)
      have h8 : (4 * L * (K / Real.sqrt (n : ℝ))) * a ^ n ≤ (4 * L * (ν / 2)) * a ^ n :=
        mul_le_mul_of_nonneg_right h7 (pow_nonneg ha0.le n)
      have h9 : (4 * L * (ν / 2)) * a ^ n = 2 * L * ν * a ^ n := by ring
      linarith
    -- bound the "r" sums
    have hJ2n : (J : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hJle
    have hb4 : ∑ j ∈ Finset.range J, L * r * E ≤ L * r := by
      have h4 : ∑ j ∈ Finset.range J, L * r * E = (J : ℝ) * (L * r * E) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
      rw [h4]
      have h5 : (J : ℝ) * (L * r * E) ≤ (2 * (n : ℝ)) * (L * r * E) :=
        mul_le_mul_of_nonneg_right hJ2n (by positivity)
      have h7 : (2 * (n : ℝ)) * (L * r * E) ≤ L * r := by
        have h8 : (2 * (n : ℝ)) * (L * r * E) = (L * r) * ((2 * (n : ℝ)) * E) := by ring
        rw [h8]
        calc (L * r) * ((2 * (n : ℝ)) * E) ≤ (L * r) * 1 :=
              mul_le_mul_of_nonneg_left hne' (mul_nonneg hL0 hr.le)
          _ = L * r := by ring
      linarith
    have hb5 : ∑ j ∈ Finset.range J, L * r * C16 ≤ (1 / (Ksp C Ct * ν)) * r := by
      have h4 : ∑ j ∈ Finset.range J, L * r * C16 = (J : ℝ) * (L * r * C16) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
      rw [h4]
      have h5 : (J : ℝ) * (L * r * C16) ≤ (2 * (n : ℝ)) * (L * r * C16) :=
        mul_le_mul_of_nonneg_right hJ2n (by positivity)
      have h6 : (2 * (n : ℝ)) * (L * r * C16)
          = (2 * (n : ℝ) * (1 / 16) ^ n) * ((1 / (Ksp C Ct * ν)) * r) := by
        rw [hC16def]
        field_simp
      rw [h6] at h5
      have h7 : (2 * (n : ℝ) * (1 / 16) ^ n) * ((1 / (Ksp C Ct * ν)) * r)
          ≤ 1 * ((1 / (Ksp C Ct * ν)) * r) :=
        mul_le_mul_of_nonneg_right hn16 (by positivity)
      linarith
    have hb6 : ∑ j ∈ Finset.range J, L * r * a ^ n ≤ L * r := by
      have h4 : ∑ j ∈ Finset.range J, L * r * a ^ n = (J : ℝ) * (L * r * a ^ n) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
      rw [h4]
      have h5 : (J : ℝ) * (L * r * a ^ n) ≤ (2 * (n : ℝ)) * (L * r * a ^ n) :=
        mul_le_mul_of_nonneg_right hJ2n (by positivity)
      have h7 : (2 * (n : ℝ)) * (L * r * a ^ n) ≤ L * r := by
        have h8 : (2 * (n : ℝ)) * (L * r * a ^ n) = (L * r) * ((2 * (n : ℝ)) * a ^ n) := by ring
        rw [h8]
        calc (L * r) * ((2 * (n : ℝ)) * a ^ n) ≤ (L * r) * 1 :=
              mul_le_mul_of_nonneg_left hna (mul_nonneg hL0 hr.le)
          _ = L * r := by ring
      linarith
    linarith [hb1, hb2, hb3, hb4, hb5, hb6]
  -- combine everything
  have hmain : P.real {ω : Ω | normalLe hn1 (shiftMatrix s (B ω)) r ∧
        ¬ compressible δ ν (Submission.NormalSplit.yfnOf s (B ω))}
      ≤ (6 * L * ν + 4 * K / (Ksp C Ct * ν)) * a ^ n
        + (3 * L + 1 / (Ksp C Ct * ν)) * r := by
    have h1 := MeasureTheory.measureReal_mono hset (measure_ne_top P _)
    have h2 := MeasureTheory.measureReal_union_le
      ({ω : Ω | normalLe hn1 (shiftMatrix s (B ω)) r ∧
          Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ≤ Tj K n J})
      (⋃ j ∈ Finset.range J, {ω : Ω | normalLe hn1 (shiftMatrix s (B ω)) r ∧
            ¬ compressible δ ν (Submission.NormalSplit.yfnOf s (B ω)) ∧
            Tj K n (j + 1) < Submission.Threshold.threshold p
                (Submission.NormalSplit.yfnOf s (B ω)) L ∧
            Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ≤ Tj K n j})
      (μ := P)
    have h3 : P.real (⋃ j ∈ Finset.range J, {ω : Ω | normalLe hn1 (shiftMatrix s (B ω)) r ∧
            ¬ compressible δ ν (Submission.NormalSplit.yfnOf s (B ω)) ∧
            Tj K n (j + 1) < Submission.Threshold.threshold p
                (Submission.NormalSplit.yfnOf s (B ω)) L ∧
            Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ≤ Tj K n j})
        ≤ ∑ j ∈ Finset.range J, P.real {ω : Ω | normalLe hn1 (shiftMatrix s (B ω)) r ∧
            ¬ compressible δ ν (Submission.NormalSplit.yfnOf s (B ω)) ∧
            Tj K n (j + 1) < Submission.Threshold.threshold p
                (Submission.NormalSplit.yfnOf s (B ω)) L ∧
            Submission.Threshold.threshold p (Submission.NormalSplit.yfnOf s (B ω)) L ≤ Tj K n j} :=
      MeasureTheory.measureReal_biUnion_finset_le _ _
    linarith [h1, h2, h3, htail, hsumUp]
  have hmain2 : P.real {ω : Ω | normalLe hn1 (shiftMatrix s (B ω)) r}
      ≤ a ^ n + ((6 * L * ν + 4 * K / (Ksp C Ct * ν)) * a ^ n
          + (3 * L + 1 / (Ksp C Ct * ν)) * r) := by
    have hsub : {ω : Ω | normalLe hn1 (shiftMatrix s (B ω)) r}
        ⊆ {ω : Ω | compressible δ ν (Submission.NormalSplit.yfnOf s (B ω))}
          ∪ {ω : Ω | normalLe hn1 (shiftMatrix s (B ω)) r ∧
              ¬ compressible δ ν (Submission.NormalSplit.yfnOf s (B ω))} := by
      intro ω hω
      by_cases hc : compressible δ ν (Submission.NormalSplit.yfnOf s (B ω))
      · exact Or.inl hc
      · exact Or.inr ⟨hω, hc⟩
    have h1 := MeasureTheory.measureReal_mono hsub (measure_ne_top P _)
    have h2 := MeasureTheory.measureReal_union_le
      ({ω : Ω | compressible δ ν (Submission.NormalSplit.yfnOf s (B ω))})
      ({ω : Ω | normalLe hn1 (shiftMatrix s (B ω)) r ∧
          ¬ compressible δ ν (Submission.NormalSplit.yfnOf s (B ω))}) (μ := P)
    linarith [h1, h2, hmain, hcomp]
  refine le_trans hmain2 (le_of_eq ?_)
  ring

end Submission.NetAssemble
