import Mathlib
import Submission.Work.KMTAreas.A7.randSymbG_telescope
import Submission.Work.KMTAreas.A7.randSymbG_mikhlin
import Submission.Work.KMTAreas.A7.randSymbG_support_le
import Submission.Work.KMTAreas.A7.narrow_of_core
import Submission.Work.KMTAreas.A7.randSymbNarrow
import Submission.Work.KMTAreas.A7.isLqMultiplierBound_of_mikhlin
import Submission.Work.KMTAreas.A7.eLpNorm_iwConv_le_of_IWLqBound
import Submission.Work.KMTPlan.A6.L_le_of_threshold_fail
import Submission.Work.KMTAreas.A4.offYoung
import Submission.Work.KMTAreas.A7.integral_norm_sum_bumps_le
import Submission.Work.KMTAreas.A7.randSymbCrudeAux
import Submission.Work.KMTAreas.A7.randSymb_eq_activeSum
import Submission.Work.KMTAreas.A7.tsum_norm_iwKernel_le
import Submission.Work.KMTPlan.A6.MdlKerVarphitildeNt

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier
open Work.KMTContract Work.Analysis.EndVar

/-! ## Helper lemmas for `randSymb_Tle_g_bound` -/

/-- **Monotonicity of `GoodMajorArcs` in the arithmetic constant.** -/
lemma gGoodMajorArcs_mono_const {ρ Cρ Cρ' : ℝ} (h : Cρ' ≤ Cρ) {l : ℕ} {k : ℤ}
    (hgood : GoodMajorArcs ρ Cρ l k) : GoodMajorArcs ρ Cρ' l k := by
  unfold GoodMajorArcs at hgood ⊢
  have h2 : (0 : ℝ) ≤ 2 ^ (ρ * (l : ℝ)) := Real.rpow_nonneg (by norm_num) _
  nlinarith [mul_le_mul_of_nonneg_right h h2]

/-- A `Λ`-lacunary sequence with `Λ > 1` and `1 ≤ a n` is monotone. -/
lemma gMonotone_of_lacunary {Λ : NNReal} {a : ℕ → NNReal} (hΛ : 1 < Λ)
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) : Monotone a := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  have hpos : (0 : NNReal) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
  have h1 : Λ * a n < a (n + 1) := by
    have h2 : Λ < a (n + 1) / a n := ha n
    rwa [lt_div_iff₀ hpos] at h2
  have h3 : a n ≤ Λ * a n := by nlinarith [ha1 n, hΛ]
  exact le_trans h3 h1.le

/-- The loss scale `lmaxR l₁ l₂ k₁ k₂` is the natural number `Lnat l₁ l₂ k₁ k₂`. -/
lemma gLmaxR_eq_Lnat (l₁ l₂ k₁ k₂ : ℕ) :
    lmaxR l₁ l₂ k₁ k₂ = ((Lnat l₁ l₂ k₁ k₂ : ℕ) : ℝ) := by
  have h : Work.Analysis.EndVar.lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) = (Lnat l₁ l₂ k₁ k₂ : ℤ) := by
    simp only [Work.Analysis.EndVar.lmax, Lnat]
    omega
  rw [lmaxR, h]
  push_cast
  ring

/-- **The `g`-side threshold support bound.**  If an admissible scale `N = ⌊a n⌋` satisfies the
height condition `Lnat l₁ l₂ k₁ k₂ ≤ heightScale C₀ N`, then the threshold hypothesis
`k₂ + Cρ 2^{ρl₂} + 2 ≤ 2^{L/C₀ - 2}` forces the `g`-side bump at that scale to be supported in the
arc `ℝ_{≤⌊-Cρ' 2^{ρl₂}⌋}` (where `Cρ' = max 1 (Cρ/d)` is the safe normalisation of the arithmetic
constant by the degree `d = deg P`).  This is the `g`-side counterpart of the `f`-side
`exp_le_floor_of_inIndexSet`. -/
lemma gSupport_threshold (ρ Cρ Cs : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (hd : 1 ≤ P.natDegree) {l₁ l₂ k₁ k₂ : ℕ} {a : ℕ → NNReal} {n : ℕ}
    (hCs : Cρ / (P.natDegree : ℝ) ≤ Cs)
    (hindex : inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n)))
    (hthr : (k₂ : ℝ) + Cs * 2 ^ (ρ * (l₂ : ℝ)) + 2 ≤
      (2 : ℝ) ^ (((Lnat l₁ l₂ k₁ k₂ : ℕ) : ℝ) / (C₀ : ℝ) - 2)) :
    (2 : ℝ) ^ ((P.natDegree : ℤ) * ((k₂ : ℤ) - logN (Nat.floor (a n)))) ≤
      (2 : ℝ) ^ (⌊-Cρ * 2 ^ (ρ * (l₂ : ℝ))⌋) := by
  have hLh : Lnat l₁ l₂ k₁ k₂ ≤ heightScale C₀ (Nat.floor (a n)) := by
    have h1 : max (l₁ : ℤ) (l₂ : ℤ) ≤ (heightScale C₀ (Nat.floor (a n)) : ℤ) := hindex.1
    have h2 : (k₁ : ℤ) ≤ (heightScale C₀ (Nat.floor (a n)) : ℤ) := hindex.2.1
    have h3 : (k₂ : ℤ) ≤ (heightScale C₀ (Nat.floor (a n)) : ℤ) := hindex.2.2
    show max (max l₁ l₂) (max k₁ k₂) ≤ heightScale C₀ (Nat.floor (a n))
    omega
  have hkey : (k₂ : ℝ) + Cs * 2 ^ (ρ * (l₂ : ℝ)) ≤ (logN (Nat.floor (a n)) : ℝ) := by
    have h := two_rpow_div_sub_two_le C₀ (Lnat l₁ l₂ k₁ k₂) (Nat.floor (a n)) hC₀ hLh
    linarith
  have hfloor : (k₂ : ℤ) - logN (Nat.floor (a n)) ≤
      ⌊-(Cs * 2 ^ (ρ * (l₂ : ℝ)))⌋ :=
    int_sub_le_floor_neg (N := Nat.floor (a n)) (k := k₂) hkey
  have hdpos : (0 : ℝ) < (P.natDegree : ℝ) :=
    by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hmul0 : (P.natDegree : ℤ) * ((k₂ : ℤ) - logN (Nat.floor (a n))) ≤
      (P.natDegree : ℤ) * ⌊-(Cs * 2 ^ (ρ * (l₂ : ℝ)))⌋ :=
    mul_le_mul_of_nonneg_left hfloor (Int.ofNat_nonneg _)
  have hreal : ((P.natDegree : ℝ)) * (⌊-(Cs * 2 ^ (ρ * (l₂ : ℝ)))⌋ : ℝ)
      ≤ -Cρ * 2 ^ (ρ * (l₂ : ℝ)) := by
    have hdnn : (0 : ℝ) ≤ (P.natDegree : ℝ) := Nat.cast_nonneg _
    have hle : ((⌊-(Cs * 2 ^ (ρ * (l₂ : ℝ)))⌋ : ℤ) : ℝ) ≤ -(Cs * 2 ^ (ρ * (l₂ : ℝ))) :=
      Int.floor_le _
    have h1 : Cρ ≤ (P.natDegree : ℝ) * Cs := by
      calc Cρ = (P.natDegree : ℝ) * (Cρ / (P.natDegree : ℝ)) := by
            field_simp
        _ ≤ (P.natDegree : ℝ) * Cs := mul_le_mul_of_nonneg_left hCs hdnn
    have h2 : (0 : ℝ) ≤ 2 ^ (ρ * (l₂ : ℝ)) := Real.rpow_nonneg (by norm_num) _
    have hstep := mul_le_mul_of_nonneg_left hle hdnn
    nlinarith [hstep, h1, h2, hdnn]
  have hint : (P.natDegree : ℤ) * ((k₂ : ℤ) - logN (Nat.floor (a n))) ≤
      ⌊-Cρ * 2 ^ (ρ * (l₂ : ℝ))⌋ := by
    rw [Int.le_floor]
    have hcast : (((P.natDegree : ℤ) * ⌊-(Cs * 2 ^ (ρ * (l₂ : ℝ)))⌋ : ℤ) : ℝ)
        = (P.natDegree : ℝ) * ((⌊-(Cs * 2 ^ (ρ * (l₂ : ℝ)))⌋ : ℤ) : ℝ) := by
      push_cast
      ring
    have h1 : (((P.natDegree : ℤ) * ((k₂ : ℤ) - logN (Nat.floor (a n))) : ℤ) : ℝ) ≤
        (((P.natDegree : ℤ) * ⌊-(Cs * 2 ^ (ρ * (l₂ : ℝ)))⌋ : ℤ) : ℝ) := by
      exact_mod_cast hmul0
    rw [hcast] at h1
    linarith [hreal]
  exact zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hint

/-- **The Mikhlin bound for the randomised `g`-side cut-off**, packaged with the `Λ`-dependent
constant: for each lacunarity parameter `Λ > 1` there is `Kg ≥ 0` such that the telescoped
randomised symbol satisfies the Mikhlin conditions with constant `Kg (1 + 2^{d k₂})²`, uniformly
in the lacunary sequence, the truncation `K` and the signs. -/
lemma gRandSymb_mikhlin_hex (P : Polynomial ℤ) :
    ∀ Λ : NNReal, 1 < Λ → ∃ Kg : ℝ, 0 < Kg ∧
      ∀ (ρ' : ℝ) (C₀' : ℕ) (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a)
        (ha1 : ∀ n : ℕ, 1 ≤ a n) (l₁ l₂ k₁ : ℕ) (k₂ : ℕ) (t : ℝ)
        (ht : t ∈ Set.Icc (1/2 : ℝ) 1) (K : ℕ) (ε : ℕ → ℂ), (∀ n : ℕ, ‖ε n‖ ≤ 1) →
        MikhlinBound (randSymb (smallSymbG ρ' P C₀' a l₁ l₂ k₁ k₂ t) ε K)
          (Kg * (1 + (2 : ℝ) ^ (P.natDegree * k₂)) ^ 2) := by
  intro Λ hΛ
  obtain ⟨C, hC, hb⟩ := randSymbG_mikhlin P P.natDegree le_rfl Λ hΛ
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro ρ' C₀' a ha ha1 l₁ l₂ k₁ k₂ t ht K ε hε
  have hmono : Monotone a := gMonotone_of_lacunary hΛ ha ha1
  obtain ⟨hid, hc4⟩ := randSymbG_telescope ρ' P C₀' a l₁ l₂ k₁ k₂ t ε hε hmono K
  rw [hid]
  obtain ⟨h0, h1, h2, h3⟩ :=
    hb k₂ t ht a ha ha1 K (randSymbGCoef ρ' C₀' a l₁ l₂ k₁ k₂ ε K) hc4
  have hle : C * (1 + (2 : ℝ) ^ (P.natDegree * k₂)) ^ 2
      ≤ max C 1 * (1 + (2 : ℝ) ^ (P.natDegree * k₂)) ^ 2 :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  exact ⟨le_trans h0 hle, fun ξ => le_trans (h1 ξ) hle, fun ξ => le_trans (h2 ξ) hle,
    fun ξ => le_trans (h3 ξ) hle⟩

/-! ## The randomised `g`-side cut-off as a Schwartz function -/

/-- The `g`-side bump `φ̃_N` is smooth to all orders. -/
lemma gContDiff_varphitildeN_all (d N k₂ : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (varphitildeN d N k₂) := by
  unfold varphitildeN
  by_cases h : k₂ = 0
  · rw [if_pos h]
    exact contDiff_kmtEta_all.comp (contDiff_const.mul contDiff_id)
  · rw [if_neg h]
    exact (contDiff_kmtEta_all.comp (contDiff_const.mul contDiff_id)).sub
      (contDiff_kmtEta_all.comp (contDiff_const.mul contDiff_id))

/-- The modulated `g`-side bump `φ̃_{N,t}` is smooth to all orders. -/
lemma gContDiff_varphitildeNt_all (P : Polynomial ℤ) (d N k₂ : ℕ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (varphitildeNt P d N k₂ t) := by
  rw [show varphitildeNt P d N k₂ t
      = fun ξ : ℝ => varphitildeN d N k₂ ξ * ee (PevalR P ((N : ℝ) * t) * ξ) from rfl]
  exact (gContDiff_varphitildeN_all d N k₂).mul (contDiff_ee_all (PevalR P ((N : ℝ) * t)))

/-- The modulated `g`-side bump has compact support (the modulation is nowhere zero). -/
lemma gHasCompactSupport_varphitildeNt (P : Polynomial ℤ) (d N k₂ : ℕ) (t : ℝ) :
    HasCompactSupport (varphitildeNt P d N k₂ t) := by
  rw [show varphitildeNt P d N k₂ t
      = fun ξ : ℝ => varphitildeN d N k₂ ξ * ee (PevalR P ((N : ℝ) * t) * ξ) from rfl]
  exact (hasCompactSupport_varphitildeN d N k₂).mul_right

/-- The modulated `g`-side bump as a Schwartz function. -/
noncomputable def gVarphitildeNtSch (P : Polynomial ℤ) (d N k₂ : ℕ) (t : ℝ) :
    SchwartzMap ℝ ℂ :=
  (gHasCompactSupport_varphitildeNt P d N k₂ t).toSchwartzMap
    (gContDiff_varphitildeNt_all P d N k₂ t)

lemma gVarphitildeNtSch_coe (P : Polynomial ℤ) (d N k₂ : ℕ) (t : ℝ) :
    (gVarphitildeNtSch P d N k₂ t : ℝ → ℂ) = varphitildeNt P d N k₂ t :=
  funext fun ξ => HasCompactSupport.toSchwartzMap_toFun
    (gHasCompactSupport_varphitildeNt P d N k₂ t)
    (gContDiff_varphitildeNt_all P d N k₂ t) ξ

/-- The `m`-th member of the `g`-side family `smallSymbG`, as a Schwartz function. -/
noncomputable def smallSymbGSch (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₁ l₂ k₁ k₂ m : ℕ) (t : ℝ) : SchwartzMap ℝ ℂ :=
  if randAct ρ C₀ a l₁ l₂ k₁ k₂ m then
    gVarphitildeNtSch P P.natDegree (Nat.floor (a m)) k₂ t else 0

lemma smallSymbGSch_coe (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₁ l₂ k₁ k₂ m : ℕ) (t : ℝ) :
    (smallSymbGSch ρ P C₀ a l₁ l₂ k₁ k₂ m t : ℝ → ℂ)
      = smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t m := by
  unfold smallSymbGSch
  rw [smallSymbG_apply]
  by_cases h : randAct ρ C₀ a l₁ l₂ k₁ k₂ m
  · rw [if_pos h, if_pos h]
    exact gVarphitildeNtSch_coe P P.natDegree (Nat.floor (a m)) k₂ t
  · rw [if_neg h, if_neg h]
    funext ξ
    simp

/-- **The randomised `g`-side cut-off is a Schwartz function.** -/
theorem gRandSymb_schwartz (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (ε : ℕ → ℂ) (K : ℕ) :
    ∃ Φ : SchwartzMap ℝ ℂ,
      (Φ : ℝ → ℂ) = randSymb (smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε K := by
  refine ⟨∑ n ∈ Finset.range K, ε n • (smallSymbGSch ρ P C₀ a l₁ l₂ k₁ k₂ (n + 1) t
      - smallSymbGSch ρ P C₀ a l₁ l₂ k₁ k₂ n t), ?_⟩
  funext ξ
  simp [randSymb, smallSymbGSch_coe]

end

end Work.KMTAreas.A7
