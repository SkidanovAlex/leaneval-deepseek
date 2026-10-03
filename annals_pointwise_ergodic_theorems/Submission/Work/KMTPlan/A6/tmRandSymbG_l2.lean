import Mathlib
import Submission.Work.KMTPlan.A6.LowSmallAux
import Submission.Work.KMTPlan.A6.lowSmallSet_conv
import Submission.Work.KMTAreas.A7.varphitildeNt_support_all
import Submission.Work.KMTAreas.A7.abs_PevalR_mul_le
import Submission.Work.KMTPlan.A6.tmRandSymb_l2
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.KMTContract Work.Analysis.EndVar

local notation "Circ" => Work.Analysis.IonescuWainger.Circle


/-- **`η(u) - η(v)` is bounded by `1`**, `η` being `[0,1]`-valued. -/
theorem kmtEta_sub_le_one (u v : ℝ) :
    ‖Work.KMTContract.kmtEta u - Work.KMTContract.kmtEta v‖ ≤ 1 := by
  simp only [Work.KMTContract.kmtEta, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_le]
  constructor
  · have h1 := Work.KMTContract.kmtEta_nonneg u
    have h2 := Work.KMTContract.kmtEta_le_one v
    linarith
  · have h1 := Work.KMTContract.kmtEta_le_one u
    have h2 := Work.KMTContract.kmtEta_nonneg v
    linarith

theorem varphitildeN_norm_le_one (d N k₂ : ℕ) (ξ : ℝ) :
    ‖Work.KMTAreas.A7.varphitildeN d N k₂ ξ‖ ≤ 1 := by
  by_cases hk : k₂ = 0
  · simp only [Work.KMTAreas.A7.varphitildeN, if_pos hk]
    exact Work.KMTContract.norm_kmtEta_le _
  · simp only [Work.KMTAreas.A7.varphitildeN, if_neg hk]
    exact kmtEta_sub_le_one _ _

theorem varphitildeNt_norm_le_one (P : Polynomial ℤ) (d N k₂ : ℕ) (t ξ : ℝ) :
    ‖Work.KMTAreas.A7.varphitildeNt P d N k₂ t ξ‖ ≤ 1 := by
  rw [show Work.KMTAreas.A7.varphitildeNt P d N k₂ t ξ
      = Work.KMTAreas.A7.varphitildeN d N k₂ ξ
        * Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((N : ℝ) * t) * ξ) from rfl,
    norm_mul, Work.KMTAreas.A7.norm_ee_eq_one, mul_one]
  exact varphitildeN_norm_le_one d N k₂ ξ

/-- The second `η`-argument of `φ̃_N` in terms of the first: `2^{d(Log N - k₂)+d} = 2^d · 2^{d(Log N - k₂)}`. -/
theorem rpow_shift_d (d N k₂ : ℕ) :
    (2 : ℝ) ^ ((d : ℝ) * ((logN N : ℝ) - (k₂ : ℝ) + 1))
      = (2 : ℝ) ^ d * (2 : ℝ) ^ ((d : ℝ) * ((logN N : ℝ) - (k₂ : ℝ))) := by
  rw [show (d : ℝ) * ((logN N : ℝ) - (k₂ : ℝ) + 1)
      = (d : ℝ) * ((logN N : ℝ) - (k₂ : ℝ)) + (d : ℝ) by ring,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast, mul_comm]

/-- **The two-sided support of the `d`-fold bump `φ̃_N` at heights `k₂ ≥ 1`.**
A nonzero value of `φ̃_N(ξ)` forces `2^{-(d+1)} < 2^{d(Log N - k₂)}|ξ| < 1`. -/
theorem varphitildeN_annulus {d N k₂ : ℕ} (hd : 1 ≤ d) (hk₂ : 1 ≤ k₂) {ξ : ℝ}
    (h : Work.KMTAreas.A7.varphitildeN d N k₂ ξ ≠ 0) :
    (2 : ℝ) ^ (-((d : ℝ) + 1))
        < (2 : ℝ) ^ ((d : ℝ) * ((logN N : ℝ) - (k₂ : ℝ))) * |ξ| ∧
      (2 : ℝ) ^ ((d : ℝ) * ((logN N : ℝ) - (k₂ : ℝ))) * |ξ| < 1 := by
  have hk2ne : k₂ ≠ 0 := by omega
  set A : ℝ := (2 : ℝ) ^ ((d : ℝ) * ((logN N : ℝ) - (k₂ : ℝ))) with hA
  have hApos : 0 < A := Real.rpow_pos_of_pos (by norm_num) _
  have h2dpos : 0 < (2 : ℝ) ^ d := by positivity
  have h2d1 : (1 : ℝ) ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  have hpow := rpow_shift_d d N k₂
  rw [Work.KMTAreas.A7.varphitildeN, if_neg hk2ne, hpow] at h
  have hbor : Work.KMTContract.kmtEta (A * ξ) ≠ 0
      ∨ Work.KMTContract.kmtEta ((2 : ℝ) ^ d * A * ξ) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h (by rw [hc.1, hc.2, sub_zero])
  have hcancel : (2 : ℝ) ^ d * (2 : ℝ) ^ (-((d : ℝ) + 1)) = 1 / 2 := by
    rw [← Real.rpow_natCast (2 : ℝ) d, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [show ((d : ℝ) + (-((d : ℝ) + 1)) : ℝ) = -1 by ring, Real.rpow_neg_one]
    norm_num
  constructor
  · by_contra hcon
    push Not at hcon
    have hsmall : |A * ξ| ≤ 1 / 2 := by
      rw [abs_mul, abs_of_pos hApos]
      have h2 : (2 : ℝ) ^ (-((d : ℝ) + 1)) ≤ 1 / 2 := by
        have hle : -((d : ℝ) + 1) ≤ (-1 : ℝ) := by
          have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
          linarith
        calc (2 : ℝ) ^ (-((d : ℝ) + 1)) ≤ (2 : ℝ) ^ (-1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
          _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
      linarith [abs_nonneg ξ]
    have hsmall2 : |(2 : ℝ) ^ d * A * ξ| ≤ 1 / 2 := by
      rw [abs_mul, abs_mul, abs_of_pos h2dpos, abs_of_pos hApos]
      have h2 : A * |ξ| ≤ (2 : ℝ) ^ (-((d : ℝ) + 1)) := hcon
      have h3 : (2 : ℝ) ^ d * (A * |ξ|) ≤ (2 : ℝ) ^ d * (2 : ℝ) ^ (-((d : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left h2 h2dpos.le
      rw [hcancel] at h3
      linarith
    have h1' : Work.KMTContract.kmtEta (A * ξ) = 1 := Work.KMTContract.kmtEta_one hsmall
    have h2' : Work.KMTContract.kmtEta ((2 : ℝ) ^ d * A * ξ) = 1 :=
      Work.KMTContract.kmtEta_one hsmall2
    exact h (by rw [h1', h2', sub_self])
  · rcases hbor with h0 | h0
    · have hlt : ¬ (1 ≤ |A * ξ|) := fun hc => h0 (Work.KMTContract.kmtEta_zero hc)
      have h2 : |A * ξ| < 1 := lt_of_not_ge hlt
      rwa [abs_mul, abs_of_pos hApos] at h2
    · have hlt : ¬ (1 ≤ |(2 : ℝ) ^ d * A * ξ|) := fun hc => h0 (Work.KMTContract.kmtEta_zero hc)
      have h2 : |(2 : ℝ) ^ d * A * ξ| < 1 := lt_of_not_ge hlt
      rw [abs_mul, abs_mul, abs_of_pos h2dpos, abs_of_pos hApos] at h2
      have h3 : A * |ξ| ≤ (2 : ℝ) ^ d * (A * |ξ|) := by
        calc A * |ξ| = 1 * (A * |ξ|) := (one_mul _).symm
          _ ≤ (2 : ℝ) ^ d * (A * |ξ|) := mul_le_mul_of_nonneg_right h2d1 (by positivity)
      linarith

/-- **Level comparison for the `d`-fold bump.**  Two nonzero values of `φ̃_{N}` at the same height
`k₂ ≥ 1` force the two `Log`-levels to be within `1` of each other. -/
theorem level_close_G {d : ℕ} (hd : 1 ≤ d) {k₂ : ℕ} (hk₂ : 1 ≤ k₂) {ξ : ℝ} (hξ : 0 < |ξ|)
    {N₁ N₂ : ℕ} (h1 : Work.KMTAreas.A7.varphitildeN d N₁ k₂ ξ ≠ 0)
    (h2 : Work.KMTAreas.A7.varphitildeN d N₂ k₂ ξ ≠ 0) :
    |logN N₁ - logN N₂| ≤ 1 := by
  obtain ⟨l₁, u₁⟩ := varphitildeN_annulus hd hk₂ h1
  obtain ⟨l₂, u₂⟩ := varphitildeN_annulus hd hk₂ h2
  set A₁ : ℝ := (2 : ℝ) ^ ((d : ℝ) * ((logN N₁ : ℝ) - (k₂ : ℝ))) with hA₁
  set A₂ : ℝ := (2 : ℝ) ^ ((d : ℝ) * ((logN N₂ : ℝ) - (k₂ : ℝ))) with hA₂
  have hA₁pos : 0 < A₁ := Real.rpow_pos_of_pos (by norm_num) _
  have hA₂pos : 0 < A₂ := Real.rpow_pos_of_pos (by norm_num) _
  have hr₁ : (2 : ℝ) ^ (-((d : ℝ) + 1)) < A₁ * |ξ| := l₁
  have hu₁ : A₁ * |ξ| < 1 := u₁
  have hr₂ : (2 : ℝ) ^ (-((d : ℝ) + 1)) < A₂ * |ξ| := l₂
  have hu₂ : A₂ * |ξ| < 1 := u₂
  have hratio : (A₁ * |ξ|) / (A₂ * |ξ|)
      = (2 : ℝ) ^ ((d : ℝ) * ((logN N₁ : ℝ) - (logN N₂ : ℝ))) := by
    rw [hA₁, hA₂, mul_div_mul_right _ _ (ne_of_gt hξ),
      ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hlo : (2 : ℝ) ^ (-((d : ℝ) + 1)) < (A₁ * |ξ|) / (A₂ * |ξ|) := by
    rw [lt_div_iff₀ (by positivity : 0 < A₂ * |ξ|)]
    have hpos : 0 < (2 : ℝ) ^ (-((d : ℝ) + 1)) := Real.rpow_pos_of_pos (by norm_num) _
    have h1 : (2 : ℝ) ^ (-((d : ℝ) + 1)) * (A₂ * |ξ|) < (2 : ℝ) ^ (-((d : ℝ) + 1)) := by
      calc (2 : ℝ) ^ (-((d : ℝ) + 1)) * (A₂ * |ξ|)
          < (2 : ℝ) ^ (-((d : ℝ) + 1)) * 1 := mul_lt_mul_of_pos_left hu₂ hpos
        _ = (2 : ℝ) ^ (-((d : ℝ) + 1)) := mul_one _
    linarith [h1, hr₁]
  have hhi : (A₁ * |ξ|) / (A₂ * |ξ|) < (2 : ℝ) ^ ((d : ℝ) + 1) := by
    rw [div_lt_iff₀ (by positivity : 0 < A₂ * |ξ|)]
    have hpos : 0 < (2 : ℝ) ^ (-((d : ℝ) + 1)) := Real.rpow_pos_of_pos (by norm_num) _
    have h2d : (2 : ℝ) ^ ((d : ℝ) + 1) * (2 : ℝ) ^ (-((d : ℝ) + 1)) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      rw [show ((d : ℝ) + 1 + -((d : ℝ) + 1) : ℝ) = 0 by ring, Real.rpow_zero]
    nlinarith [hu₁, hr₂, hpos, h2d, mul_pos (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) ((d:ℝ)+1)) (by positivity : 0 < A₂ * |ξ|)]
  rw [hratio] at hlo hhi
  have hlt : (logN N₁ : ℝ) - (logN N₂ : ℝ) < 1 + 1 / (d : ℝ) := by
    have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
    have h1' : ((d : ℝ) * ((logN N₁ : ℝ) - (logN N₂ : ℝ))) < (d : ℝ) + 1 :=
      (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp hhi
    have := (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp hlo
    have h2' : -((d : ℝ) + 1) < (d : ℝ) * ((logN N₁ : ℝ) - (logN N₂ : ℝ)) := this
    rw [show (1 : ℝ) + 1 / (d : ℝ) = ((d : ℝ) + 1) / (d : ℝ) by
        rw [add_div, div_self (ne_of_gt hdpos)]]
    rw [lt_div_iff₀ hdpos]
    linarith [h1']
  have hgt : (-2 : ℝ) < (logN N₁ : ℝ) - (logN N₂ : ℝ) := by
    have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have h2' : -((d : ℝ) + 1) < (d : ℝ) * ((logN N₁ : ℝ) - (logN N₂ : ℝ)) :=
      (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp hlo
    have hdiv : (-((d : ℝ) + 1)) / (d : ℝ) < (logN N₁ : ℝ) - (logN N₂ : ℝ) := by
      rw [div_lt_iff₀ hdpos]; linarith [h2']
    have hle : (-2 : ℝ) ≤ (-((d : ℝ) + 1)) / (d : ℝ) := by
      rw [neg_div, neg_le_neg_iff]
      rw [div_le_iff₀ hdpos]
      linarith [hd1]
    linarith [hdiv, hle]
  have hle2 : (1 : ℝ) + 1 / (d : ℝ) ≤ 2 := by
    have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have : 1 / (d : ℝ) ≤ 1 := by
      rw [div_le_one hdpos]; exact hd1
    linarith
  have hcast : ((logN N₁ - logN N₂ : ℤ) : ℝ) = (logN N₁ : ℝ) - (logN N₂ : ℝ) := by push_cast; ring
  have hlt' : ((logN N₁ - logN N₂ : ℤ) : ℝ) < 2 := by
    rw [hcast]; linarith
  have hgt' : (-2 : ℝ) < ((logN N₁ - logN N₂ : ℤ) : ℝ) := by
    rw [hcast]
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
    have hq : 0 ≤ 1 / (d : ℝ) := by positivity
    linarith
  rw [abs_le]
  constructor
  · have : (-2 : ℤ) < logN N₁ - logN N₂ := by exact_mod_cast hgt'
    omega
  · have : logN N₁ - logN N₂ < (2 : ℤ) := by exact_mod_cast hlt'
    omega


/-- The unclamped `g`-side bump family at height `k₂` along the lacunary scale `⌊a n⌋`. -/
noncomputable abbrev Gfam (P : Polynomial ℤ) (a : ℕ → NNReal) (k₂ : ℕ) (t : ℝ) : ℕ → ℝ → ℂ :=
  fun n ξ => Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t ξ

/-- **The randomised `g`-side symbol at heights `k₂ ≥ 1` is uniformly bounded.**  A nonzero value
of `φ̃_{N}` at height `k₂ ≥ 1` forces `Log N` into a window of length `≤ 1 + 1/d ≤ 1.5` around
`k₂ - log₂|ξ|/d`; by lacunarity at most `M Λ` scales share a level, so at most `3 M Λ` summands of
the randomised sum are nonzero, each of modulus `≤ 2`. -/
theorem randSymbG_TV_kpos (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℕ → NNReal) (k₂ : ℕ) (t x : ℝ) (K : ℕ),
      1 ≤ k₂ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      t ∈ Set.Icc (1 / 2 : ℝ) 1 →
      ∑ n ∈ Finset.range K, ‖Gfam P a k₂ t (n + 1) x - Gfam P a k₂ t n x‖ ≤ C := by
  obtain ⟨Mlev, hMlev⟩ := lacunaryLevel
  refine ⟨6 * (Mlev Λ : ℝ), by positivity, ?_⟩
  intro a k₂ t x K hk₂ hLac ha1 ht
  have hd1 : 1 ≤ P.natDegree := by omega
  have hzero : ∀ N : ℕ, Work.KMTAreas.A7.varphitildeN P.natDegree N k₂ 0 = 0 := by
    intro N
    have hk2ne : k₂ ≠ 0 := by omega
    simp only [Work.KMTAreas.A7.varphitildeN, if_neg hk2ne]
    simp [Work.KMTContract.kmtEta_one (by norm_num : |(0 : ℝ)| ≤ 1 / 2)]
  set S : Finset ℕ := (Finset.range (K + 1)).filter (fun n => Gfam P a k₂ t n x ≠ 0) with hS
  -- the cardinality bound
  have hcard : S.card ≤ 3 * Mlev Λ := by
    by_cases hne : S.Nonempty
    · obtain ⟨n₀, hn₀⟩ := hne
      have hn₀U : Gfam P a k₂ t n₀ x ≠ 0 := (Finset.mem_filter.mp hn₀).2
      have hx0 : x ≠ 0 := by
        intro hx0
        have hgoal : Gfam P a k₂ t n₀ x = 0 := by
          rw [show Gfam P a k₂ t n₀ x
              = Work.KMTAreas.A7.varphitildeN P.natDegree (Nat.floor (a n₀)) k₂ x
                * Work.KMTAreas.A7.ee
                    (Work.KMTAreas.A7.PevalR P ((Nat.floor (a n₀) : ℝ) * t) * x) from rfl,
            hx0, hzero (Nat.floor (a n₀)), zero_mul]
        exact hn₀U hgoal
      have hxpos : 0 < |x| := abs_pos.mpr hx0
      set j₀ : ℤ := logN (Nat.floor (a n₀)) with hj₀
      have hsub : S ⊆ (Finset.Icc (j₀ - 1) (j₀ + 1)).biUnion (fun j =>
            ((Finset.range (K + 1)).filter (fun n => logN (Nat.floor (a n)) = j))) := by
        intro n hn
        have hnU : Gfam P a k₂ t n x ≠ 0 := (Finset.mem_filter.mp hn).2
        have h1 : Work.KMTAreas.A7.varphitildeN P.natDegree (Nat.floor (a n)) k₂ x ≠ 0 := by
          intro h0
          exact hnU (by
            rw [show Gfam P a k₂ t n x
                = Work.KMTAreas.A7.varphitildeN P.natDegree (Nat.floor (a n)) k₂ x
                  * Work.KMTAreas.A7.ee
                      (Work.KMTAreas.A7.PevalR P ((Nat.floor (a n) : ℝ) * t) * x) from rfl,
              h0, zero_mul])
        have h2 : Work.KMTAreas.A7.varphitildeN P.natDegree (Nat.floor (a n₀)) k₂ x ≠ 0 := by
          intro h0
          exact hn₀U (by
            rw [show Gfam P a k₂ t n₀ x
                = Work.KMTAreas.A7.varphitildeN P.natDegree (Nat.floor (a n₀)) k₂ x
                  * Work.KMTAreas.A7.ee
                      (Work.KMTAreas.A7.PevalR P ((Nat.floor (a n₀) : ℝ) * t) * x) from rfl,
              h0, zero_mul])
        have hlev := level_close_G hd1 hk₂ hxpos h1 h2
        refine Finset.mem_biUnion.mpr ⟨logN (Nat.floor (a n)), ?_, ?_⟩
        · rw [Finset.mem_Icc]
          rw [abs_le] at hlev
          obtain ⟨hlev1, hlev2⟩ := hlev
          constructor <;> omega
        · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).1, rfl⟩
      calc S.card
          ≤ ((Finset.Icc (j₀ - 1) (j₀ + 1)).biUnion (fun j =>
              ((Finset.range (K + 1)).filter (fun n => logN (Nat.floor (a n)) = j)))).card :=
            Finset.card_le_card hsub
        _ ≤ ∑ j ∈ Finset.Icc (j₀ - 1) (j₀ + 1),
              ((Finset.range (K + 1)).filter (fun n => logN (Nat.floor (a n)) = j)).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ _j ∈ Finset.Icc (j₀ - 1) (j₀ + 1), Mlev Λ :=
            Finset.sum_le_sum (fun j _ => hMlev a Λ hΛ hLac ha1 j (Finset.range (K + 1)))
        _ ≤ 3 * Mlev Λ := by
            rw [Finset.sum_const, smul_eq_mul]
            have h3 : (Finset.Icc (j₀ - 1) (j₀ + 1)).card ≤ 3 := by
              rw [Int.card_Icc]
              have hthis : ((j₀ + 1) + 1 - (j₀ - 1) : ℤ) = 3 := by ring
              rw [hthis]
              simp
            exact Nat.mul_le_mul_right _ h3
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp
  -- the total-variation bound
  have hsum : ∑ n ∈ Finset.range K, ‖Gfam P a k₂ t (n + 1) x - Gfam P a k₂ t n x‖
      ≤ 2 * (S.card : ℝ) := by
    have hbd : ∀ n : ℕ, ‖Gfam P a k₂ t n x‖ ≤ 1 :=
      fun n => varphitildeNt_norm_le_one P P.natDegree (Nat.floor (a n)) k₂ t x
    have hstep2 : ∑ n ∈ Finset.range K, ‖Gfam P a k₂ t (n + 1) x - Gfam P a k₂ t n x‖
        ≤ 2 * (S.card : ℝ) := by
      have h1 : ∑ n ∈ Finset.range K, ‖Gfam P a k₂ t (n + 1) x - Gfam P a k₂ t n x‖
          ≤ ∑ n ∈ Finset.range K, (‖Gfam P a k₂ t (n + 1) x‖ + ‖Gfam P a k₂ t n x‖) :=
        Finset.sum_le_sum (fun n _ => norm_sub_le _ _)
      have h2 : ∑ n ∈ Finset.range K, (‖Gfam P a k₂ t (n + 1) x‖ + ‖Gfam P a k₂ t n x‖)
          ≤ 2 * ∑ n ∈ Finset.range (K + 1), ‖Gfam P a k₂ t n x‖ := by
        have hA : ∑ n ∈ Finset.range K, ‖Gfam P a k₂ t (n + 1) x‖
            ≤ ∑ n ∈ Finset.range (K + 1), ‖Gfam P a k₂ t n x‖ := by
          rw [Finset.sum_range_succ']
          exact le_add_of_nonneg_right (norm_nonneg _)
        have hB : ∑ n ∈ Finset.range K, ‖Gfam P a k₂ t n x‖
            ≤ ∑ n ∈ Finset.range (K + 1), ‖Gfam P a k₂ t n x‖ := by
          rw [Finset.sum_range_succ]
          exact le_add_of_nonneg_right (norm_nonneg _)
        rw [Finset.sum_add_distrib]
        linarith
      have h3 : ∑ n ∈ Finset.range (K + 1), ‖Gfam P a k₂ t n x‖ ≤ (S.card : ℝ) := by
        calc ∑ n ∈ Finset.range (K + 1), ‖Gfam P a k₂ t n x‖
            ≤ ∑ n ∈ Finset.range (K + 1),
                (if Gfam P a k₂ t n x ≠ 0 then (1 : ℝ) else 0) := by
              refine Finset.sum_le_sum (fun n _ => ?_)
              by_cases h : Gfam P a k₂ t n x = 0
              · rw [h]; simp
              · rw [if_pos h]; exact hbd n
          _ = ∑ n ∈ S, (1 : ℝ) := by
              rw [Finset.sum_filter]
          _ = (S.card : ℝ) := by
              rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      linarith [h1, h2, h3]
    exact hstep2
  have hcardR : (S.card : ℝ) ≤ 3 * (Mlev Λ : ℝ) := by exact_mod_cast hcard
  linarith [hsum, hcardR]


/-- `(a-b) a^d ≤ a^{d+1} - b^{d+1}` for `0 ≤ b ≤ a`. -/
theorem sub_mul_pow_le_pow_sub_succ (d : ℕ) {a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) :
    (a - b) * a ^ d ≤ a ^ (d + 1) - b ^ (d + 1) := by
  induction d with
  | zero => simp
  | succ k ih =>
    have ih' : (a - b) * a ^ k ≤ a ^ (k + 1) - b ^ (k + 1) := ih
    have hfac : a ^ (k + 2) - b ^ (k + 2)
        = a * (a ^ (k + 1) - b ^ (k + 1)) + (a - b) * b ^ (k + 1) := by
      rw [show k + 2 = k + 1 + 1 by ring, pow_succ, pow_succ]
      ring
    have h4 : 0 ≤ a - b := sub_nonneg.mpr hba
    have h5 : 0 ≤ b ^ (k + 1) := pow_nonneg hb _
    have h6 : a * ((a - b) * a ^ k) ≤ a * (a ^ (k + 1) - b ^ (k + 1)) :=
      mul_le_mul_of_nonneg_left ih' (le_trans hb hba)
    have h7 : a * ((a - b) * a ^ k) = (a - b) * a ^ (k + 1) := by
      rw [pow_succ]; ring
    rw [hfac]
    nlinarith [h6, h7, mul_nonneg h4 h5]

/-- The polynomial coefficient weight `d · ∑|c_i|` of the difference bound. -/
noncomputable abbrev Gmom (P : Polynomial ℤ) : ℝ :=
  (P.natDegree : ℝ) * ∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)|

/-- The `d`-fold scaled height `2^{d·Log N}` at the lacunary scale `⌊a m⌋`. -/
noncomputable abbrev GZ (P : Polynomial ℤ) (a : ℕ → NNReal) (m : ℕ) : ℝ :=
  (2 : ℝ) ^ ((P.natDegree : ℝ) * ((logN (Nat.floor (a m)) : ℤ) : ℝ))

/-- The polynomial height `(1 + ⌊a m⌋)^d`. -/
noncomputable abbrev Gg (P : Polynomial ℤ) (a : ℕ → NNReal) (m : ℕ) : ℝ :=
  (1 + (Nat.floor (a m) : ℝ)) ^ P.natDegree

/-- **Difference bound for the evaluation of a polynomial.**  For `0 ≤ N ≤ N'` and `0 ≤ t ≤ 1`,
`|P(N't) - P(Nt)| ≤ (d ∑_i |c_i|) · ((1+N')^d - (1+N)^d)`. -/
theorem abs_PevalR_sub_le (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) {N N' : ℕ} (hNN : N ≤ N')
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |Work.KMTAreas.A7.PevalR P ((N' : ℝ) * t) - Work.KMTAreas.A7.PevalR P ((N : ℝ) * t)|
      ≤ Gmom P * ((1 + (N' : ℝ)) ^ P.natDegree - (1 + (N : ℝ)) ^ P.natDegree) := by
  classical
  have hN'N : (N : ℝ) ≤ (N' : ℝ) := by exact_mod_cast hNN
  set Q : Polynomial ℝ := P.map (Int.castRingHom ℝ) with hQ
  have hcoeff : ∀ i, Q.coeff i = (P.coeff i : ℝ) := by
    intro i; rw [hQ, Polynomial.coeff_map]; rfl
  have hdegQ : Q.natDegree ≤ P.natDegree := by rw [hQ]; exact Polynomial.natDegree_map_le
  have heval : ∀ y : ℝ, Work.KMTAreas.A7.PevalR P y
      = ∑ i ∈ Finset.range (P.natDegree + 1), (P.coeff i : ℝ) * y ^ i := by
    intro y
    have h1 : Work.KMTAreas.A7.PevalR P y = Q.eval y := by rw [hQ]; rfl
    rw [h1, Polynomial.eval_eq_sum_range' (by omega : Q.natDegree < P.natDegree + 1)]
    exact Finset.sum_congr rfl (fun i _ => by rw [hcoeff])
  have hmax : max |(N' : ℝ) * t| |(N : ℝ) * t| ≤ 1 + (N' : ℝ) := by
    refine max_le ?_ ?_
    · rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg N') ht0)]
      calc (N' : ℝ) * t ≤ (N' : ℝ) * 1 := mul_le_mul_of_nonneg_left ht1 (Nat.cast_nonneg N')
        _ = (N' : ℝ) := mul_one _
        _ ≤ 1 + (N' : ℝ) := le_add_of_nonneg_left (by norm_num)
    · rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg N) ht0)]
      calc (N : ℝ) * t ≤ (N : ℝ) * 1 := mul_le_mul_of_nonneg_left ht1 (Nat.cast_nonneg N)
        _ = (N : ℝ) := mul_one _
        _ ≤ (N' : ℝ) := hN'N
        _ ≤ 1 + (N' : ℝ) := le_add_of_nonneg_left (by norm_num)
  have hgap : |(N' : ℝ) * t - (N : ℝ) * t| = ((N' : ℝ) - (N : ℝ)) * t := by
    have h6 : (0 : ℝ) ≤ (N' : ℝ) - (N : ℝ) := by linarith
    rw [← sub_mul, abs_of_nonneg (mul_nonneg h6 ht0)]
  have hbase1 : (1 : ℝ) ≤ 1 + (N' : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg N')
  have hbase_nonneg : (0 : ℝ) ≤ max |(N' : ℝ) * t| |(N : ℝ) * t| :=
    le_max_of_le_left (abs_nonneg _)
  rw [heval, heval, ← Finset.sum_sub_distrib]
  have hterm : ∀ i ∈ Finset.range (P.natDegree + 1),
      |(P.coeff i : ℝ) * ((N' : ℝ) * t) ^ i - (P.coeff i : ℝ) * ((N : ℝ) * t) ^ i|
        ≤ |(P.coeff i : ℝ)| * (((N' : ℝ) - (N : ℝ)) * (P.natDegree : ℝ)
            * (1 + (N' : ℝ)) ^ (P.natDegree - 1)) := by
    intro i hi
    have hi_d : i ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h6 : (0 : ℝ) ≤ (N' : ℝ) - (N : ℝ) := by linarith
    rw [← mul_sub, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have h1 := abs_pow_sub_pow_le (a := (N' : ℝ) * t) (b := (N : ℝ) * t) i
    rw [hgap] at h1
    have h2 : max |(N' : ℝ) * t| |(N : ℝ) * t| ^ (i - 1) ≤ (1 + (N' : ℝ)) ^ (P.natDegree - 1) := by
      have h3 : max |(N' : ℝ) * t| |(N : ℝ) * t| ^ (i - 1) ≤ (1 + (N' : ℝ)) ^ (i - 1) :=
        pow_le_pow_left₀ hbase_nonneg hmax (i - 1)
      have h4 : (1 + (N' : ℝ)) ^ (i - 1) ≤ (1 + (N' : ℝ)) ^ (P.natDegree - 1) :=
        pow_le_pow_right₀ hbase1 (Nat.sub_le_sub_right hi_d 1)
      linarith
    have h5 : (i : ℝ) * max |(N' : ℝ) * t| |(N : ℝ) * t| ^ (i - 1)
        ≤ (P.natDegree : ℝ) * (1 + (N' : ℝ)) ^ (P.natDegree - 1) := by
      have h7 : (i : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hi_d
      have h8 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      have h9 : (0 : ℝ) ≤ max |(N' : ℝ) * t| |(N : ℝ) * t| := hbase_nonneg
      have h10 : (0 : ℝ) ≤ (1 + (N' : ℝ)) ^ (P.natDegree - 1) := by positivity
      have h11 : (0 : ℝ) ≤ (P.natDegree : ℝ) := Nat.cast_nonneg _
      nlinarith [h7, h8, h9, h10, h2, h11]
    have hbase_pow : (0 : ℝ) ≤ max |(N' : ℝ) * t| |(N : ℝ) * t| ^ (i - 1) :=
      pow_nonneg hbase_nonneg _
    calc |((N' : ℝ) * t) ^ i - ((N : ℝ) * t) ^ i|
        ≤ ((N' : ℝ) - (N : ℝ)) * t * (i : ℝ)
            * max |(N' : ℝ) * t| |(N : ℝ) * t| ^ (i - 1) := h1
      _ = ((N' : ℝ) - (N : ℝ)) * t
            * ((i : ℝ) * max |(N' : ℝ) * t| |(N : ℝ) * t| ^ (i - 1)) := by ring
      _ ≤ ((N' : ℝ) - (N : ℝ)) * 1
            * ((P.natDegree : ℝ) * (1 + (N' : ℝ)) ^ (P.natDegree - 1)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left ht1 h6) h5
            (mul_nonneg (Nat.cast_nonneg i) hbase_pow) (mul_nonneg h6 (by norm_num))
      _ = ((N' : ℝ) - (N : ℝ)) * (P.natDegree : ℝ)
            * (1 + (N' : ℝ)) ^ (P.natDegree - 1) := by ring
  calc |∑ i ∈ Finset.range (P.natDegree + 1),
        ((P.coeff i : ℝ) * ((N' : ℝ) * t) ^ i - (P.coeff i : ℝ) * ((N : ℝ) * t) ^ i)|
      ≤ ∑ i ∈ Finset.range (P.natDegree + 1),
          |(P.coeff i : ℝ) * ((N' : ℝ) * t) ^ i - (P.coeff i : ℝ) * ((N : ℝ) * t) ^ i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (P.natDegree + 1),
          |(P.coeff i : ℝ)| * (((N' : ℝ) - (N : ℝ)) * (P.natDegree : ℝ)
            * (1 + (N' : ℝ)) ^ (P.natDegree - 1)) := Finset.sum_le_sum hterm
    _ = (∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)|)
          * (((N' : ℝ) - (N : ℝ)) * (P.natDegree : ℝ)
            * (1 + (N' : ℝ)) ^ (P.natDegree - 1)) := by rw [Finset.sum_mul]
    _ ≤ (∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)|)
          * ((P.natDegree : ℝ) * ((1 + (N' : ℝ)) ^ P.natDegree
              - (1 + (N : ℝ)) ^ P.natDegree)) := by
        have hS0 : (0 : ℝ) ≤ ∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)| :=
          Finset.sum_nonneg (fun i _ => abs_nonneg _)
        have h6 : (0 : ℝ) ≤ (N' : ℝ) - (N : ℝ) := by linarith
        have hb_nonneg : (0 : ℝ) ≤ 1 + (N : ℝ) := by positivity
        have h10 := sub_mul_pow_le_pow_sub_succ (P.natDegree - 1)
          (a := 1 + (N' : ℝ)) (b := 1 + (N : ℝ)) hb_nonneg (by linarith)
        have h11 : (P.natDegree - 1) + 1 = P.natDegree := Nat.sub_add_cancel hd
        rw [h11] at h10
        have h12 : (1 + (N' : ℝ)) - (1 + (N : ℝ)) = (N' : ℝ) - (N : ℝ) := by ring
        rw [h12] at h10
        refine mul_le_mul_of_nonneg_left ?_ hS0
        nlinarith [h10, h6]
    _ = Gmom P * ((1 + (N' : ℝ)) ^ P.natDegree - (1 + (N : ℝ)) ^ P.natDegree) := by
        rw [Gmom]; ring


/-- The product form of the `k₂ = 0` slice: `η(2^{d·Log N} x) · e(P(Nt) x)`. -/
noncomputable abbrev Gph (P : Polynomial ℤ) (a : ℕ → NNReal) (t x : ℝ) (m : ℕ) : ℂ :=
  Work.KMTContract.kmtEta (GZ P a m * x)
    * Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a m) : ℝ) * t) * x)

/-- At the bottom height `k₂ = 0` the `d`-fold bump is a single cutoff, so the slice reduces to the
product form `Gph`. -/
theorem Gfam_zero_eq_Gph (P : Polynomial ℤ) (a : ℕ → NNReal) (t x : ℝ) (m : ℕ) :
    Gfam P a 0 t m x = Gph P a t x m := by
  have h : Work.KMTAreas.A7.varphitildeN P.natDegree (Nat.floor (a m)) 0
      = fun ξ : ℝ => Work.KMTContract.kmtEta (GZ P a m * ξ) := by
    funext ξ
    rw [Work.KMTAreas.A7.varphitildeN]
    rw [if_pos rfl]
  simp only [Gfam, Gph, Work.KMTAreas.A7.varphitildeNt, h]

/-- **The randomised `g`-side symbol at the bottom height `k₂ = 0` is uniformly bounded.**
Here the bump is the *single* cutoff `η(2^{d Log N}·)`, whose support is a half-line of scales, so
the counting argument of the `k₂ ≥ 1` case is unavailable.  Instead one splits the sum at the
"crossing" index where `2^{d Log N}|x|` reaches `1`:

* before the crossing, both the amplitude difference (Lipschitz of `η`, telescoping in `2^{d Log N}`)
  and the phase difference (the polynomial difference bound `abs_PevalR_sub_le`, telescoping in
  `(1+N)^d`) are controlled by the *values* of the two monotone sequences at the crossing, each of
  which is `≲ 1` there;
* at the crossing at most one summand survives, and it is `≤ 2`. -/
theorem randSymbG_TV_k0 (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (Λ : NNReal) (hΛ : 1 < Λ) (Lη : ℝ) (hLη : 0 < Lη)
    (hη : ∀ u v : ℝ, ‖Work.KMTContract.kmtEta u - Work.KMTContract.kmtEta v‖ ≤ Lη * |u - v|) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℕ → NNReal) (t x : ℝ) (K : ℕ),
      PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      t ∈ Set.Icc (1 / 2 : ℝ) 1 →
      ∑ n ∈ Finset.range K, ‖Gfam P a 0 t (n + 1) x - Gfam P a 0 t n x‖ ≤ C := by
  classical
  have hd1 : 1 ≤ P.natDegree := by omega
  have hGmom0 : 0 ≤ Gmom P := by
    rw [Gmom]
    exact mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun i _ => abs_nonneg _))
  have h3pow : (0 : ℝ) ≤ (3 : ℝ) ^ P.natDegree := by positivity
  refine ⟨Lη + 2 * Real.pi * Gmom P * (3 : ℝ) ^ P.natDegree + 3, ?_, ?_⟩
  · have h1 : 0 ≤ 2 * Real.pi * Gmom P * (3 : ℝ) ^ P.natDegree :=
      mul_nonneg (mul_nonneg (by positivity) hGmom0) h3pow
    linarith [hLη.le, h1]
  intro a t x K hLac ha1 ht
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have ht1 : t ≤ 1 := ht.2
  have hNmono : Monotone (fun m : ℕ => Nat.floor (a m)) := lacunary_floor_mono Λ hΛ hLac
  have hZmono : Monotone (GZ P a) := by
    intro i j hij
    have h1 : logN (Nat.floor (a i)) ≤ logN (Nat.floor (a j)) :=
      Work.KMTPlan.A6.logN_mono (hNmono hij)
    have h2 : ((logN (Nat.floor (a i)) : ℤ) : ℝ) ≤ ((logN (Nat.floor (a j)) : ℤ) : ℝ) := by
      exact_mod_cast h1
    have h3 : (P.natDegree : ℝ) * ((logN (Nat.floor (a i)) : ℤ) : ℝ)
        ≤ (P.natDegree : ℝ) * ((logN (Nat.floor (a j)) : ℤ) : ℝ) :=
      mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
    exact (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr h3
  have hZnn : ∀ m, 0 ≤ GZ P a m := fun m => Real.rpow_nonneg (by norm_num) _
  -- the two monotone dominanting sequences
  have hgmono : Monotone (Gg P a) := by
    intro i j hij
    have h1 : (1 + (Nat.floor (a i) : ℝ)) ≤ (1 + (Nat.floor (a j) : ℝ)) := by
      have := hNmono hij
      have : (Nat.floor (a i) : ℝ) ≤ (Nat.floor (a j) : ℝ) := by exact_mod_cast this
      linarith
    exact pow_le_pow_left₀ (by positivity) h1 _
  have hgnn : ∀ m, 0 ≤ Gg P a m := fun m => by rw [Gg]; positivity
  have hdec : ∀ n : ℕ, ‖Gph P a t x (n + 1) - Gph P a t x n‖
      ≤ ‖Work.KMTContract.kmtEta (GZ P a (n + 1) * x) - Work.KMTContract.kmtEta (GZ P a n * x)‖
        + ‖Work.KMTContract.kmtEta (GZ P a n * x)‖
          * ‖Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a (n + 1)) : ℝ) * t) * x)
             - Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a n) : ℝ) * t) * x)‖ := by
    intro n
    have halg : Gph P a t x (n + 1) - Gph P a t x n
        = (Work.KMTContract.kmtEta (GZ P a (n + 1) * x) - Work.KMTContract.kmtEta (GZ P a n * x))
            * Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a (n + 1)) : ℝ) * t) * x)
          + Work.KMTContract.kmtEta (GZ P a n * x)
            * (Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a (n + 1)) : ℝ) * t) * x)
               - Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a n) : ℝ) * t) * x)) := by
      simp only [Gph]; ring
    rw [halg]
    calc ‖(Work.KMTContract.kmtEta (GZ P a (n + 1) * x) - Work.KMTContract.kmtEta (GZ P a n * x))
              * Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a (n + 1)) : ℝ) * t) * x)
            + Work.KMTContract.kmtEta (GZ P a n * x)
              * (Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a (n + 1)) : ℝ) * t) * x)
                 - Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a n) : ℝ) * t) * x))‖
        ≤ ‖(Work.KMTContract.kmtEta (GZ P a (n + 1) * x) - Work.KMTContract.kmtEta (GZ P a n * x))
              * Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a (n + 1)) : ℝ) * t) * x)‖
            + ‖Work.KMTContract.kmtEta (GZ P a n * x)
              * (Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a (n + 1)) : ℝ) * t) * x)
                 - Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a n) : ℝ) * t) * x))‖ :=
          norm_add_le _ _
      _ = _ := by rw [norm_mul, norm_mul, Work.KMTAreas.A7.norm_ee_eq_one, mul_one]
  -- ======= step 2: the cut at the crossing =======
  set Acut : Finset ℕ := (Finset.range K).filter (fun n => GZ P a (n + 1) * |x| < 1) with hAcut
  set Cr : Finset ℕ := ((Finset.range K).filter (fun n => n ∉ Acut)).filter
      (fun n => GZ P a n * |x| < 1) with hCr
  have hCrsub : Cr ⊆ (Finset.range K).filter (fun n => n ∉ Acut) :=
    fun n hn => Finset.mem_of_mem_filter n hn
  have hCrK : ∀ n ∈ Cr, n ∈ Finset.range K := fun n hn => (Finset.mem_filter.mp (hCrsub hn)).1
  have hCrA : ∀ n ∈ Cr, n ∉ Acut := fun n hn => (Finset.mem_filter.mp (hCrsub hn)).2
  have hCrz : ∀ n ∈ Cr, GZ P a n * |x| < 1 := fun n hn => (Finset.mem_filter.mp hn).2
  have hCrcard : Cr.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro m hm m' hm'
    by_contra hne2
    have hmA : m ∉ Acut := hCrA m hm
    have hmz : GZ P a m * |x| < 1 := hCrz m hm
    have hm'A : m' ∉ Acut := hCrA m' hm'
    have hm'z : GZ P a m' * |x| < 1 := hCrz m' hm'
    have hmK : m ∈ Finset.range K := hCrK m hm
    have hm'K : m' ∈ Finset.range K := hCrK m' hm'
    have hm1 : 1 ≤ GZ P a (m + 1) * |x| := by
      refine not_lt.mp fun hc => hmA ?_
      rw [hAcut]; exact Finset.mem_filter.mpr ⟨hmK, hc⟩
    have hm'1 : 1 ≤ GZ P a (m' + 1) * |x| := by
      refine not_lt.mp fun hc => hm'A ?_
      rw [hAcut]; exact Finset.mem_filter.mpr ⟨hm'K, hc⟩
    rcases lt_or_gt_of_ne hne2 with hlt | hlt
    · have h1 : GZ P a (m + 1) ≤ GZ P a m' := hZmono (by omega)
      have h2 : GZ P a (m + 1) * |x| ≤ GZ P a m' * |x| :=
        mul_le_mul_of_nonneg_right h1 (abs_nonneg x)
      linarith
    · have h1 : GZ P a (m' + 1) ≤ GZ P a m := hZmono (by omega)
      have h2 : GZ P a (m' + 1) * |x| ≤ GZ P a m * |x| :=
        mul_le_mul_of_nonneg_right h1 (abs_nonneg x)
      linarith
  -- telescoping bounds over Acut
  have hMdata : ∀ (hne : Acut.Nonempty), ∃ M₀ : ℕ, M₀ ∈ Acut ∧ (∀ m ∈ Acut, m ≤ M₀) ∧
      GZ P a (M₀ + 1) * |x| < 1 := by
    intro hne
    refine ⟨Acut.max' hne, Finset.max'_mem Acut hne, fun m hm => Finset.le_max' Acut m hm, ?_⟩
    exact (Finset.mem_filter.mp (Finset.max'_mem Acut hne)).2
  have htelZ : ∑ n ∈ Acut, (GZ P a (n + 1) - GZ P a n) * |x| ≤ 1 := by
    by_cases hne : Acut.Nonempty
    · obtain ⟨M₀, hM₀mem, hM₀ub, hM₀key⟩ := hMdata hne
      have hsub : Acut ⊆ Finset.range (M₀ + 1) :=
        fun m hm => Finset.mem_range.mpr (Nat.lt_succ_of_le (hM₀ub m hm))
      calc ∑ n ∈ Acut, (GZ P a (n + 1) - GZ P a n) * |x|
          ≤ ∑ n ∈ Finset.range (M₀ + 1), (GZ P a (n + 1) - GZ P a n) * |x| :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by
              have := hZmono (Nat.le_succ n)
              nlinarith [abs_nonneg x])
        _ = (GZ P a (M₀ + 1) - GZ P a 0) * |x| := by
            rw [← Finset.sum_mul, Finset.sum_range_sub (f := GZ P a)]
        _ ≤ 1 := by nlinarith [hM₀key, abs_nonneg x, hZnn 0]
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
      norm_num
  have htelg : ∑ n ∈ Acut, (Gg P a (n + 1) - Gg P a n) * |x| ≤ (3 : ℝ) ^ P.natDegree := by
    by_cases hne : Acut.Nonempty
    · obtain ⟨M₀, hM₀mem, hM₀ub, hM₀key⟩ := hMdata hne
      have hsub : Acut ⊆ Finset.range (M₀ + 1) :=
        fun m hm => Finset.mem_range.mpr (Nat.lt_succ_of_le (hM₀ub m hm))
      have hM₀big : Gg P a (M₀ + 1) ≤ (3 : ℝ) ^ P.natDegree * GZ P a (M₀ + 1) := by
        have hNlt := nat_lt_two_mul_two_pow_logN (Nat.floor (a (M₀ + 1)))
        have hlog0 : (0 : ℝ) ≤ ((logN (Nat.floor (a (M₀ + 1))) : ℤ) : ℝ) := by
          exact_mod_cast Work.Analysis.EndVar.logN_nonneg (Nat.floor (a (M₀ + 1)))
        have h2a : (1 : ℝ) ≤ (2 : ℝ) ^ ((logN (Nat.floor (a (M₀ + 1))) : ℤ) : ℝ) :=
          Real.one_le_rpow (by norm_num) hlog0
        have hNle : (1 + (Nat.floor (a (M₀ + 1)) : ℝ))
            ≤ 3 * (2 : ℝ) ^ ((logN (Nat.floor (a (M₀ + 1))) : ℤ) : ℝ) := by linarith
        have hpow : (3 * (2 : ℝ) ^ ((logN (Nat.floor (a (M₀ + 1))) : ℤ) : ℝ)) ^ P.natDegree
            = (3 : ℝ) ^ P.natDegree * GZ P a (M₀ + 1) := by
          rw [mul_pow, GZ]
          congr 1
          rw [← Real.rpow_natCast ((2 : ℝ) ^ ((logN (Nat.floor (a (M₀ + 1))) : ℤ) : ℝ))
                P.natDegree,
            ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          congr 1
          ring
        rw [Gg, ← hpow]
        exact pow_le_pow_left₀ (by positivity) hNle _
      calc ∑ n ∈ Acut, (Gg P a (n + 1) - Gg P a n) * |x|
          ≤ ∑ n ∈ Finset.range (M₀ + 1), (Gg P a (n + 1) - Gg P a n) * |x| :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by
              have := hgmono (Nat.le_succ n)
              nlinarith [abs_nonneg x])
        _ = (Gg P a (M₀ + 1) - Gg P a 0) * |x| := by
            rw [← Finset.sum_mul, Finset.sum_range_sub (f := Gg P a)]
        _ ≤ Gg P a (M₀ + 1) * |x| := by nlinarith [abs_nonneg x, hgnn 0]
        _ ≤ (3 : ℝ) ^ P.natDegree * GZ P a (M₀ + 1) * |x| :=
            mul_le_mul_of_nonneg_right hM₀big (abs_nonneg x)
        _ = (3 : ℝ) ^ P.natDegree * (GZ P a (M₀ + 1) * |x|) := by ring
        _ ≤ (3 : ℝ) ^ P.natDegree := by nlinarith [hM₀key, h3pow]
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
      exact h3pow
  -- ======= the two sums =======
  have hA : ∑ n ∈ Finset.range K,
      ‖Work.KMTContract.kmtEta (GZ P a (n + 1) * x) - Work.KMTContract.kmtEta (GZ P a n * x)‖
      ≤ Lη + 1 := by
    have hon : ∑ n ∈ Acut,
        ‖Work.KMTContract.kmtEta (GZ P a (n + 1) * x) - Work.KMTContract.kmtEta (GZ P a n * x)‖
        ≤ Lη := by
      calc ∑ n ∈ Acut, ‖Work.KMTContract.kmtEta (GZ P a (n + 1) * x)
              - Work.KMTContract.kmtEta (GZ P a n * x)‖
          ≤ ∑ n ∈ Acut, Lη * ((GZ P a (n + 1) - GZ P a n) * |x|) := by
            refine Finset.sum_le_sum (fun n _ => ?_)
            have hlip := hη (GZ P a (n + 1) * x) (GZ P a n * x)
            have habs : |GZ P a (n + 1) * x - GZ P a n * x|
                = (GZ P a (n + 1) - GZ P a n) * |x| := by
              rw [← sub_mul, abs_mul,
                abs_of_nonneg (sub_nonneg.mpr (hZmono (Nat.le_succ n)))]
            rwa [habs] at hlip
        _ = Lη * ∑ n ∈ Acut, (GZ P a (n + 1) - GZ P a n) * |x| := by
            rw [Finset.mul_sum]
        _ ≤ Lη * 1 := mul_le_mul_of_nonneg_left htelZ hLη.le
        _ = Lη := mul_one Lη
    have hoff : ∑ n ∈ (Finset.range K).filter (fun n => n ∉ Acut),
        ‖Work.KMTContract.kmtEta (GZ P a (n + 1) * x) - Work.KMTContract.kmtEta (GZ P a n * x)‖
        ≤ 1 := by
      have heq : ∑ n ∈ Cr,
            ‖Work.KMTContract.kmtEta (GZ P a (n + 1) * x) - Work.KMTContract.kmtEta (GZ P a n * x)‖
          = ∑ n ∈ (Finset.range K).filter (fun n => n ∉ Acut),
            ‖Work.KMTContract.kmtEta (GZ P a (n + 1) * x) - Work.KMTContract.kmtEta (GZ P a n * x)‖ := by
        refine Finset.sum_subset hCrsub (fun n hn hnotin => ?_)
        have hnK : n ∈ Finset.range K := (Finset.mem_filter.mp hn).1
        have hnA : n ∉ Acut := (Finset.mem_filter.mp hn).2
        have h1 : ¬ (GZ P a n * |x| < 1) := fun hc =>
          hnotin (Finset.mem_filter.mpr ⟨hn, hc⟩)
        have h2 : 1 ≤ GZ P a n * |x| := not_lt.mp h1
        have h3 : Work.KMTContract.kmtEta (GZ P a n * x) = 0 :=
          Work.KMTContract.kmtEta_zero (by rw [abs_mul, abs_of_nonneg (hZnn n)]; exact h2)
        have h4 : 1 ≤ GZ P a (n + 1) * |x| := by
          refine not_lt.mp fun hc => hnA ?_
          rw [hAcut]; exact Finset.mem_filter.mpr ⟨hnK, hc⟩
        have h5 : Work.KMTContract.kmtEta (GZ P a (n + 1) * x) = 0 :=
          Work.KMTContract.kmtEta_zero (by rw [abs_mul, abs_of_nonneg (hZnn (n + 1))]; exact h4)
        rw [h3, h5, sub_zero, norm_zero]
      rw [← heq]
      calc ∑ n ∈ Cr, ‖Work.KMTContract.kmtEta (GZ P a (n + 1) * x)
              - Work.KMTContract.kmtEta (GZ P a n * x)‖
          ≤ ∑ _n ∈ Cr, (1 : ℝ) :=
            Finset.sum_le_sum (fun n _ => kmtEta_sub_le_one _ _)
        _ = (Cr.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ 1 := by exact_mod_cast hCrcard
    have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.range K)
      (p := fun n => n ∈ Acut)
      (f := fun n => ‖Work.KMTContract.kmtEta (GZ P a (n + 1) * x)
        - Work.KMTContract.kmtEta (GZ P a n * x)‖)
    have hAeq : (Finset.range K).filter (fun n => n ∈ Acut) = Acut := by
      refine Finset.ext (fun n => ?_)
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨(Finset.mem_filter.mp h).1, h⟩⟩
    rw [hAeq] at hsplit
    linarith [hsplit, hon, hoff]
  have hB : ∑ n ∈ Finset.range K,
      ‖Work.KMTContract.kmtEta (GZ P a n * x)‖
        * ‖Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a (n + 1)) : ℝ) * t) * x)
           - Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a n) : ℝ) * t) * x)‖
      ≤ 2 * Real.pi * Gmom P * (3 : ℝ) ^ P.natDegree + 2 := by
    have hon : ∑ n ∈ Acut,
        ‖Work.KMTContract.kmtEta (GZ P a n * x)‖
          * ‖Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a (n + 1)) : ℝ) * t) * x)
             - Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a n) : ℝ) * t) * x)‖
        ≤ 2 * Real.pi * Gmom P * (3 : ℝ) ^ P.natDegree := by
      calc ∑ n ∈ Acut, ‖Work.KMTContract.kmtEta (GZ P a n * x)‖
            * ‖Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a (n + 1)) : ℝ) * t) * x)
               - Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a n) : ℝ) * t) * x)‖
          ≤ ∑ n ∈ Acut, 2 * Real.pi * Gmom P * ((Gg P a (n + 1) - Gg P a n) * |x|) := by
            refine Finset.sum_le_sum (fun n _ => ?_)
            have h1 : ‖Work.KMTContract.kmtEta (GZ P a n * x)‖ ≤ 1 :=
              Work.KMTContract.norm_kmtEta_le _
            have h2 : ‖Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a (n + 1)) : ℝ) * t) * x)
                  - Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a n) : ℝ) * t) * x)‖
                ≤ 2 * Real.pi * |Work.KMTAreas.A7.PevalR P ((Nat.floor (a (n + 1)) : ℝ) * t) * x
                    - Work.KMTAreas.A7.PevalR P ((Nat.floor (a n) : ℝ) * t) * x| :=
              ee_sub_le _ _
            have h3 : |Work.KMTAreas.A7.PevalR P ((Nat.floor (a (n + 1)) : ℝ) * t) * x
                  - Work.KMTAreas.A7.PevalR P ((Nat.floor (a n) : ℝ) * t) * x|
                = |Work.KMTAreas.A7.PevalR P ((Nat.floor (a (n + 1)) : ℝ) * t)
                    - Work.KMTAreas.A7.PevalR P ((Nat.floor (a n) : ℝ) * t)| * |x| := by
              rw [← sub_mul, abs_mul]
            have h4 := abs_PevalR_sub_le P hd1 (hNmono (Nat.le_succ n)) ht0 ht1
            have h5 : |Work.KMTAreas.A7.PevalR P ((Nat.floor (a (n + 1)) : ℝ) * t)
                  - Work.KMTAreas.A7.PevalR P ((Nat.floor (a n) : ℝ) * t)| * |x|
                ≤ Gmom P * ((Gg P a (n + 1) - Gg P a n) * |x|) := by
              have h6 : (1 + (Nat.floor (a (n + 1)) : ℝ)) ^ P.natDegree
                  - (1 + (Nat.floor (a n) : ℝ)) ^ P.natDegree
                  = Gg P a (n + 1) - Gg P a n := by rw [Gg, Gg]
              rw [h6] at h4
              rw [← mul_assoc]
              exact mul_le_mul_of_nonneg_right h4 (abs_nonneg x)
            have h7 : 0 ≤ Gmom P * ((Gg P a (n + 1) - Gg P a n) * |x|) :=
              mul_nonneg hGmom0 (mul_nonneg (sub_nonneg.mpr (hgmono (Nat.le_succ n))) (abs_nonneg x))
            have h8 : 0 ≤ 2 * Real.pi := by positivity
            calc ‖Work.KMTContract.kmtEta (GZ P a n * x)‖
                  * ‖Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a (n + 1)) : ℝ) * t) * x)
                     - Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a n) : ℝ) * t) * x)‖
                ≤ 1 * (2 * Real.pi * |Work.KMTAreas.A7.PevalR P ((Nat.floor (a (n + 1)) : ℝ) * t) * x
                    - Work.KMTAreas.A7.PevalR P ((Nat.floor (a n) : ℝ) * t) * x|) :=
                  mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
              _ = 2 * Real.pi * |Work.KMTAreas.A7.PevalR P ((Nat.floor (a (n + 1)) : ℝ) * t) * x
                    - Work.KMTAreas.A7.PevalR P ((Nat.floor (a n) : ℝ) * t) * x| := one_mul _
              _ = 2 * Real.pi * (|Work.KMTAreas.A7.PevalR P ((Nat.floor (a (n + 1)) : ℝ) * t)
                    - Work.KMTAreas.A7.PevalR P ((Nat.floor (a n) : ℝ) * t)| * |x|) := by rw [h3]
              _ ≤ 2 * Real.pi * (Gmom P * ((Gg P a (n + 1) - Gg P a n) * |x|)) := by
                  exact mul_le_mul_of_nonneg_left h5 h8
              _ = 2 * Real.pi * Gmom P * ((Gg P a (n + 1) - Gg P a n) * |x|) := by ring
        _ = 2 * Real.pi * Gmom P * ∑ n ∈ Acut, (Gg P a (n + 1) - Gg P a n) * |x| := by
            rw [Finset.mul_sum]
        _ ≤ 2 * Real.pi * Gmom P * (3 : ℝ) ^ P.natDegree :=
            mul_le_mul_of_nonneg_left htelg (by positivity)
    have hoff : ∑ n ∈ (Finset.range K).filter (fun n => n ∉ Acut),
        ‖Work.KMTContract.kmtEta (GZ P a n * x)‖
          * ‖Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a (n + 1)) : ℝ) * t) * x)
             - Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a n) : ℝ) * t) * x)‖
        ≤ 2 := by
      have heq : ∑ n ∈ Cr,
            ‖Work.KMTContract.kmtEta (GZ P a n * x)‖
              * ‖Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a (n + 1)) : ℝ) * t) * x)
                 - Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a n) : ℝ) * t) * x)‖
          = ∑ n ∈ (Finset.range K).filter (fun n => n ∉ Acut),
            ‖Work.KMTContract.kmtEta (GZ P a n * x)‖
              * ‖Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a (n + 1)) : ℝ) * t) * x)
                 - Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a n) : ℝ) * t) * x)‖ := by
        refine Finset.sum_subset hCrsub (fun n hn hnotin => ?_)
        have hA' : n ∉ Acut := (Finset.mem_filter.mp hn).2
        have h1 : ¬ (GZ P a n * |x| < 1) := fun hc => hnotin (Finset.mem_filter.mpr ⟨hn, hc⟩)
        have h2 : 1 ≤ GZ P a n * |x| := not_lt.mp h1
        have h3 : Work.KMTContract.kmtEta (GZ P a n * x) = 0 :=
          Work.KMTContract.kmtEta_zero (by rw [abs_mul, abs_of_nonneg (hZnn n)]; exact h2)
        rw [h3, norm_zero, zero_mul]
      rw [← heq]
      calc ∑ n ∈ Cr, ‖Work.KMTContract.kmtEta (GZ P a n * x)‖
              * ‖Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a (n + 1)) : ℝ) * t) * x)
                 - Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a n) : ℝ) * t) * x)‖
          ≤ ∑ _n ∈ Cr, (2 : ℝ) := by
            refine Finset.sum_le_sum (fun n _ => ?_)
            have h1 : ‖Work.KMTContract.kmtEta (GZ P a n * x)‖ ≤ 1 :=
              Work.KMTContract.norm_kmtEta_le _
            have h2 : ‖Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a (n + 1)) : ℝ) * t) * x)
                  - Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a n) : ℝ) * t) * x)‖
                ≤ 2 := by
              calc ‖Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a (n + 1)) : ℝ) * t) * x)
                    - Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a n) : ℝ) * t) * x)‖
                  ≤ ‖Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a (n + 1)) : ℝ) * t) * x)‖
                    + ‖Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a n) : ℝ) * t) * x)‖ :=
                    norm_sub_le _ _
                _ = 1 + 1 := by rw [Work.KMTAreas.A7.norm_ee_eq_one, Work.KMTAreas.A7.norm_ee_eq_one]
                _ = 2 := by norm_num
            calc _ ≤ 1 * 2 := mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
              _ = 2 := one_mul _
        _ = (Cr.card : ℝ) * 2 := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 2 := by
            have hc : (Cr.card : ℝ) ≤ 1 := by exact_mod_cast hCrcard
            nlinarith
    have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.range K)
      (p := fun n => n ∈ Acut)
      (f := fun n => ‖Work.KMTContract.kmtEta (GZ P a n * x)‖
        * ‖Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a (n + 1)) : ℝ) * t) * x)
           - Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a n) : ℝ) * t) * x)‖)
    have hAeq : (Finset.range K).filter (fun n => n ∈ Acut) = Acut := by
      refine Finset.ext (fun n => ?_)
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨(Finset.mem_filter.mp h).1, h⟩⟩
    rw [hAeq] at hsplit
    linarith [hsplit, hon, hoff]
  -- ======= conclude =======
  have hTV : ∑ n ∈ Finset.range K, ‖Gph P a t x (n + 1) - Gph P a t x n‖
      ≤ Lη + 2 * Real.pi * Gmom P * (3 : ℝ) ^ P.natDegree + 3 := by
    calc ∑ n ∈ Finset.range K, ‖Gph P a t x (n + 1) - Gph P a t x n‖
        ≤ ∑ n ∈ Finset.range K,
            (‖Work.KMTContract.kmtEta (GZ P a (n + 1) * x) - Work.KMTContract.kmtEta (GZ P a n * x)‖
              + ‖Work.KMTContract.kmtEta (GZ P a n * x)‖
                * ‖Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a (n + 1)) : ℝ) * t) * x)
                   - Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a n) : ℝ) * t) * x)‖) :=
          Finset.sum_le_sum (fun n _ => hdec n)
      _ = (∑ n ∈ Finset.range K,
              ‖Work.KMTContract.kmtEta (GZ P a (n + 1) * x) - Work.KMTContract.kmtEta (GZ P a n * x)‖)
            + ∑ n ∈ Finset.range K, ‖Work.KMTContract.kmtEta (GZ P a n * x)‖
                * ‖Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a (n + 1)) : ℝ) * t) * x)
                   - Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((Nat.floor (a n) : ℝ) * t) * x)‖ :=
          Finset.sum_add_distrib
      _ ≤ (Lη + 1) + (2 * Real.pi * Gmom P * (3 : ℝ) ^ P.natDegree + 2) := add_le_add hA hB
      _ = Lη + 2 * Real.pi * Gmom P * (3 : ℝ) ^ P.natDegree + 3 := by ring
  exact hTV

/-- **Clamping a bump family on an order-convex index set costs at most `2`.**  If `T` is
order-convex, then `c n = if n ∈ T then d n else 0` differs from `d` only at the (at most two)
boundary indices of `T`, so the total variation of `c` exceeds that of `d` by at most `2`, and the
randomised symbol of `c` is bounded by `Cv + 2`. -/
theorem randSymb_clamped_le {T : Set ℕ} [DecidablePred (· ∈ T)]
    (hT : ∀ {n j m : ℕ}, n ≤ j → j ≤ m → n ∈ T → m ∈ T → j ∈ T)
    {ψ : ℕ → ℝ → ℂ} {ε : ℕ → ℂ} {K : ℕ} {x : ℝ} {Cv : ℝ}
    (hψ : ∀ n, ‖ψ n x‖ ≤ 1)
    (hvar : ∑ n ∈ Finset.range K, ‖ψ (n + 1) x - ψ n x‖ ≤ Cv)
    (hε : ∀ n, ‖ε n‖ ≤ 1) :
    ‖Work.KMTAreas.A7.randSymb (fun n ξ => if n ∈ T then ψ n ξ else 0) ε K x‖ ≤ Cv + 2 := by
  classical
  set d : ℕ → ℂ := fun n => ψ n x with hd
  set c : ℕ → ℂ := fun n => if n ∈ T then d n else 0 with hc
  have hsym : (Work.KMTAreas.A7.randSymb (fun n ξ => if n ∈ T then ψ n ξ else 0) ε K) x
      = ∑ n ∈ Finset.range K, ε n * (c (n + 1) - c n) := by
    simp only [Work.KMTAreas.A7.randSymb]
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
  have hterm : ∀ n : ℕ, ‖c (n + 1) - c n‖ ≤ ‖d (n + 1) - d n‖ +
      (if (n ∈ T ↔ n + 1 ∈ T) then 0 else 1 : ℝ) := by
    intro n
    have hdn : ‖d n‖ ≤ 1 := hψ n
    have hdn1 : ‖d (n + 1)‖ ≤ 1 := hψ (n + 1)
    by_cases h1 : n ∈ T <;> by_cases h2 : n + 1 ∈ T
    · have hc1 : c n = d n := by simp [hc, h1]
      have hc2 : c (n + 1) = d (n + 1) := by simp [hc, h2]
      have hij : (n ∈ T ↔ n + 1 ∈ T) := ⟨fun _ => h2, fun _ => h1⟩
      rw [hc1, hc2, if_pos hij]; simp
    · have hc1 : c n = d n := by simp [hc, h1]
      have hc2 : c (n + 1) = 0 := by simp [hc, h2]
      have hij : ¬ (n ∈ T ↔ n + 1 ∈ T) := fun hh => h2 (hh.mp h1)
      rw [hc1, hc2, if_neg hij]
      simp only [zero_sub, norm_neg]
      linarith [norm_nonneg (d (n + 1) - d n)]
    · have hc1 : c n = 0 := by simp [hc, h1]
      have hc2 : c (n + 1) = d (n + 1) := by simp [hc, h2]
      have hij : ¬ (n ∈ T ↔ n + 1 ∈ T) := fun hh => h1 (hh.mpr h2)
      rw [hc1, hc2, if_neg hij]
      simp only [sub_zero]
      linarith [norm_nonneg (d (n + 1) - d n)]
    · have hc1 : c n = 0 := by simp [hc, h1]
      have hc2 : c (n + 1) = 0 := by simp [hc, h2]
      have hij : (n ∈ T ↔ n + 1 ∈ T) := ⟨fun hh => absurd hh h1, fun hh => absurd hh h2⟩
      rw [hc1, hc2, if_pos hij]; simp
  have hjump : ∑ n ∈ Finset.range K, (if (n ∈ T ↔ n + 1 ∈ T) then (0 : ℝ) else 1)
      = (((Finset.range K).filter (fun n => ¬ (n ∈ T ↔ n + 1 ∈ T))).card : ℝ) := by
    have h1 : ∀ n : ℕ, (if (n ∈ T ↔ n + 1 ∈ T) then (0 : ℝ) else 1)
        = ((if ¬ (n ∈ T ↔ n + 1 ∈ T) then (1 : ℕ) else 0 : ℕ) : ℝ) := by
      intro n
      by_cases h : (n ∈ T ↔ n + 1 ∈ T) <;> simp [h]
    rw [Finset.sum_congr rfl (fun n _ => h1 n), ← Nat.cast_sum, Finset.sum_boole]
    simp
  have hcard : (((Finset.range K).filter (fun n => ¬ (n ∈ T ↔ n + 1 ∈ T))).card : ℝ) ≤ 2 := by
    have h := card_jump_le_two hT K
    exact_mod_cast h
  have hd_eq : (∑ n ∈ Finset.range K, ‖d (n + 1) - d n‖)
      = ∑ n ∈ Finset.range K, ‖ψ (n + 1) x - ψ n x‖ := by simp only [hd]
  calc ‖(Work.KMTAreas.A7.randSymb (fun n ξ => if n ∈ T then ψ n ξ else 0) ε K) x‖
      = ‖∑ n ∈ Finset.range K, ε n * (c (n + 1) - c n)‖ := by rw [hsym]
    _ ≤ ∑ n ∈ Finset.range K, ‖c (n + 1) - c n‖ := by
        refine le_trans (norm_sum_le _ _) ?_
        refine Finset.sum_le_sum fun n _ => ?_
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hε n)
    _ ≤ ∑ n ∈ Finset.range K,
          (‖d (n + 1) - d n‖ + (if (n ∈ T ↔ n + 1 ∈ T) then 0 else 1 : ℝ)) :=
        Finset.sum_le_sum fun n _ => hterm n
    _ = (∑ n ∈ Finset.range K, ‖d (n + 1) - d n‖)
          + ∑ n ∈ Finset.range K, (if (n ∈ T ↔ n + 1 ∈ T) then 0 else 1 : ℝ) :=
        Finset.sum_add_distrib
    _ ≤ Cv + 2 := by
        rw [hd_eq, hjump]
        linarith [hvar, hcard]

/-- **The randomised `g`-side symbol of the low case is uniformly bounded**, in the form needed by
the assembly: a constant depending only on the lacunarity `Λ` (and on `P`) bounds
`‖randSymb (lowSymbG ...) ε K x‖` for every admissible scale, height, modulation `t`, truncation
`K`, sign sequence `ε` and every `x : ℝ`. -/
theorem randSymbG_sup_le (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (C₀ : ℕ) (Λ : NNReal)
    (hΛ : 1 < Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : ℝ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ) (ε : ℕ → ℂ),
      PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      (∀ n, ‖ε n‖ ≤ 1) → t ∈ Set.Icc (1 / 2 : ℝ) 1 →
      ∀ x : ℝ, ‖Work.KMTAreas.A7.randSymb (lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε K x‖ ≤ C := by
  classical
  obtain ⟨Lη, hLη, hη⟩ := kmtEta_lipschitz
  obtain ⟨C₁, hC₁0, hC₁⟩ := randSymbG_TV_kpos P hd Λ hΛ
  obtain ⟨C₂, hC₂0, hC₂⟩ := randSymbG_TV_k0 P hd Λ hΛ Lη hLη hη
  refine ⟨max C₁ C₂ + 2, by linarith [le_max_left C₁ C₂], ?_⟩
  intro ρ a l₁ l₂ k₁ k₂ K t ε hLac ha1 hε ht x
  have hvar : ∑ n ∈ Finset.range K, ‖Gfam P a k₂ t (n + 1) x - Gfam P a k₂ t n x‖
      ≤ max C₁ C₂ := by
    rcases eq_or_ne k₂ 0 with hk | hk
    · subst hk
      exact le_trans (hC₂ a t x K hLac ha1 ht) (le_max_right _ _)
    · exact le_trans (hC₁ a k₂ t x K (by omega) hLac ha1 ht) (le_max_left _ _)
  have hψ : ∀ n : ℕ, ‖(fun m ξ => Gfam P a k₂ t m ξ) n x‖ ≤ 1 :=
    fun n => varphitildeNt_norm_le_one P P.natDegree (Nat.floor (a n)) k₂ t x
  have hbound := randSymb_clamped_le
    (T := {n : ℕ | n ≠ 0 ∧ lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n})
    (hT := by
      intro n j m hnj hjm hn hm
      have hn' : n ≠ 0 ∧ lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n := hn
      have hm' : m ≠ 0 ∧ lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ m := hm
      refine ⟨?_, lowSmallSet_conv Λ hΛ hLac hnj hjm hn'.2 hm'.2⟩
      omega)
    (ψ := fun m ξ => Gfam P a k₂ t m ξ) (ε := ε) (K := K) (x := x) (Cv := max C₁ C₂)
    hψ hvar hε
  have hcongr : (fun n ξ => if n ∈ {n : ℕ | n ≠ 0 ∧ lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n}
        then (fun m ξ => Gfam P a k₂ t m ξ) n ξ else 0)
      = lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t := by
    funext n ξ
    simp only [lowSymbG, Gfam, Set.mem_setOf_eq]
    by_cases h0 : n = 0
    · simp [h0]
    · by_cases hls : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n <;> simp [h0, hls]
  rw [hcongr] at hbound
  exact hbound

/-- **Narrowness of the `d`-fold bump on the index set of the low case.**  On the index set
`I^{max(l₁,l₂),k₁,k₂}` and under the threshold hypothesis on `k₂`, a nonzero value of the `g`-side
bump forces `|ξ| ≤ 2^{⌊-Cρ 2^{ρl₂}⌋}`. -/
theorem narrow_of_index_G (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (ρ Cρ : ℝ) (hCρ : 0 < Cρ)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    {l₁ l₂ k₁ k₂ : ℕ} {a : ℕ → NNReal} {n : ℕ} {t : ℝ}
    (hindex : Work.Analysis.EndVar.inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ)
      (Nat.floor (a n)))
    (hthr : (k₂ : ℝ) + Cρ * (2 : ℝ) ^ (ρ * (l₂ : ℝ)) + 2 ≤
      (2 : ℝ) ^ (((lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ) / (C₀ : ℝ) - 2)) :
    ∀ ξ : ℝ, Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t ξ ≠ 0 →
      |ξ| ≤ (2 : ℝ) ^ (⌊-Cρ * (2 : ℝ) ^ (ρ * (l₂ : ℝ))⌋ : ℤ) := by
  have hLh : lcL l₁ l₂ k₁ k₂ ≤ heightScale C₀ (Nat.floor (a n)) := by
    have h1 : max (l₁ : ℤ) (l₂ : ℤ) ≤ (heightScale C₀ (Nat.floor (a n)) : ℤ) := hindex.1
    have h2 : (k₁ : ℤ) ≤ (heightScale C₀ (Nat.floor (a n)) : ℤ) := hindex.2.1
    have h3 : (k₂ : ℤ) ≤ (heightScale C₀ (Nat.floor (a n)) : ℤ) := hindex.2.2
    have h1' : (max l₁ l₂ : ℤ) ≤ (heightScale C₀ (Nat.floor (a n)) : ℤ) := h1
    rw [lcL]
    omega
  have hkey : (k₂ : ℝ) + Cρ * (2 : ℝ) ^ (ρ * (l₂ : ℝ)) ≤ (logN (Nat.floor (a n)) : ℝ) := by
    have h := Work.KMTAreas.A7.two_rpow_div_sub_two_le C₀ (lcL l₁ l₂ k₁ k₂)
      (Nat.floor (a n)) hC₀ hLh
    linarith
  have hfloor : (k₂ : ℤ) - logN (Nat.floor (a n)) ≤ ⌊-Cρ * (2 : ℝ) ^ (ρ * (l₂ : ℝ))⌋ := by
    have h := Work.KMTAreas.A7.int_sub_le_floor_neg (N := Nat.floor (a n)) (k := k₂)
      (x := Cρ * (2 : ℝ) ^ (ρ * (l₂ : ℝ))) hkey
    have hx : -(Cρ * (2 : ℝ) ^ (ρ * (l₂ : ℝ))) = -Cρ * (2 : ℝ) ^ (ρ * (l₂ : ℝ)) := by ring
    rwa [hx] at h
  -- the threshold bound is strictly negative, so the level difference is `≤ 0`
  have hneg : -Cρ * (2 : ℝ) ^ (ρ * (l₂ : ℝ)) < 0 := by
    have h2p : (0 : ℝ) < (2 : ℝ) ^ (ρ * (l₂ : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    nlinarith
  have hm0 : ((k₂ : ℤ) - logN (Nat.floor (a n))) ≤ 0 := by
    have hfl : ((⌊-Cρ * (2 : ℝ) ^ (ρ * (l₂ : ℝ))⌋ : ℤ) : ℝ)
        ≤ -Cρ * (2 : ℝ) ^ (ρ * (l₂ : ℝ)) := Int.floor_le _
    have hflt : ((⌊-Cρ * (2 : ℝ) ^ (ρ * (l₂ : ℝ))⌋ : ℤ) : ℝ) < 0 := lt_of_le_of_lt hfl hneg
    have h2 : (⌊-Cρ * (2 : ℝ) ^ (ρ * (l₂ : ℝ))⌋ : ℤ) < 0 := by exact_mod_cast hflt
    omega
  have hd1 : (1 : ℤ) ≤ (P.natDegree : ℤ) := by
    have : (1 : ℕ) ≤ P.natDegree := by omega
    exact_mod_cast this
  have hint : (P.natDegree : ℤ) * ((k₂ : ℤ) - logN (Nat.floor (a n)))
      ≤ ⌊-Cρ * (2 : ℝ) ^ (ρ * (l₂ : ℝ))⌋ := by
    have hmulR : (((P.natDegree : ℤ) * ((k₂ : ℤ) - logN (Nat.floor (a n))) : ℤ) : ℝ)
        ≤ (((k₂ : ℤ) - logN (Nat.floor (a n))) : ℝ) := by
      have hdR : (1 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd1
      have hmR : (((k₂ : ℤ) - logN (Nat.floor (a n))) : ℝ) ≤ 0 := by exact_mod_cast hm0
      push_cast
      nlinarith [hdR, hmR]
    have hstep : (((P.natDegree : ℤ) * ((k₂ : ℤ) - logN (Nat.floor (a n))) : ℤ) : ℝ)
        ≤ ((⌊-Cρ * (2 : ℝ) ^ (ρ * (l₂ : ℝ))⌋ : ℤ) : ℝ) := by
      have hfl : (((k₂ : ℤ) - logN (Nat.floor (a n))) : ℝ)
          ≤ ((⌊-Cρ * (2 : ℝ) ^ (ρ * (l₂ : ℝ))⌋ : ℤ) : ℝ) := by exact_mod_cast hfloor
      linarith [hmulR, hfl]
    exact_mod_cast hstep
  intro ξ hξ
  calc |ξ| ≤ (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - (logN (Nat.floor (a n)) : ℝ))) :=
        Work.KMTAreas.A7.varphitildeNt_support_all P P.natDegree (Nat.floor (a n)) k₂ t ξ hξ
    _ = (2 : ℝ) ^ (((P.natDegree : ℤ) * ((k₂ : ℤ) - logN (Nat.floor (a n))) : ℤ)) := by
        rw [← Real.rpow_intCast]
        congr 1
        push_cast
        ring
    _ ≤ (2 : ℝ) ^ (⌊-Cρ * (2 : ℝ) ^ (ρ * (l₂ : ℝ))⌋ : ℤ) :=
        zpow_le_zpow_right₀ (by norm_num) hint

/-- The modulated `d`-fold bump is continuous. -/
theorem continuous_varphitildeNt (P : Polynomial ℤ) (d N k₂ : ℕ) (t : ℝ) :
    Continuous (Work.KMTAreas.A7.varphitildeNt P d N k₂ t) := by
  have hcd : ContDiff ℝ 2 (Work.KMTAreas.A7.varphitildeN d N k₂) := by
    rw [Work.KMTAreas.A7.varphitildeN]
    split_ifs with hk
    · exact (Work.KMTAreas.A7.contDiff_kmtEta 2).comp (contDiff_const.mul contDiff_id)
    · exact ((Work.KMTAreas.A7.contDiff_kmtEta 2).comp (contDiff_const.mul contDiff_id)).sub
        ((Work.KMTAreas.A7.contDiff_kmtEta 2).comp (contDiff_const.mul contDiff_id))
  rw [show Work.KMTAreas.A7.varphitildeNt P d N k₂ t
      = fun ξ : ℝ => Work.KMTAreas.A7.varphitildeN d N k₂ ξ
          * Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((N : ℝ) * t) * ξ) from rfl]
  exact (hcd.mul (Work.KMTAreas.A7.contDiff_ee_const_mul 2
    (Work.KMTAreas.A7.PevalR P ((N : ℝ) * t)))).continuous

/-- Every member of the `g`-side bump family `lowSymbG` is measurable. -/
theorem measurable_lowSymbG (P : Polynomial ℤ) (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (m : ℕ) :
    Measurable (fun ξ : ℝ => lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t m ξ) := by
  by_cases h0 : m = 0
  · simp only [lowSymbG, h0, if_true]; exact measurable_const
  · simp only [lowSymbG, if_neg h0]
    by_cases hls : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ m
    · simp only [if_pos hls]
      exact (continuous_varphitildeNt P P.natDegree (Nat.floor (a m)) k₂ t).measurable
    · simp only [if_neg hls]; exact measurable_const

/-- The support of a member of `lowSymbG`: an admissible index and a nonzero bump. -/
theorem support_of_lowSymbG {ρ : ℝ} {P : Polynomial ℤ} {C₀ : ℕ} {a : ℕ → NNReal}
    {l₁ l₂ k₁ k₂ n : ℕ} {t x : ℝ}
    (h : lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t n x ≠ 0) :
    n ≠ 0 ∧ lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n ∧
      Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t x ≠ 0 := by
  by_cases h0 : n = 0
  · simp only [lowSymbG, if_pos h0] at h
    exact absurd rfl h
  · simp only [lowSymbG, if_neg h0] at h
    by_cases hls : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n
    · simp only [if_pos hls] at h
      exact ⟨h0, hls, h⟩
    · simp only [if_neg hls] at h
      exact absurd rfl h

/-- **The support of the randomised `g`-side symbol**: the values of
`randSymb (lowSymbG …) ε K` are confined to the arc `|x| ≤ 2^{d k₂}`. -/
theorem lowSymbG_support (P : Polynomial ℤ) (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ) (ε : ℕ → ℂ) :
    ∀ x : ℝ, Work.KMTAreas.A7.randSymb (lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε K x ≠ 0 →
      |x| ≤ (2 : ℝ) ^ (((P.natDegree * k₂ : ℕ)) : ℤ) := by
  intro x hx
  obtain ⟨n, -, hn⟩ := exists_ne_zero_of_randSymb_ne_zero hx
  obtain ⟨-, -, hbump⟩ := support_of_lowSymbG (h := hn)
  have hsupp := Work.KMTAreas.A7.varphitildeNt_support_all P P.natDegree (Nat.floor (a n)) k₂ t x hbump
  have hlog0 : (0 : ℝ) ≤ (logN (Nat.floor (a n)) : ℝ) := by
    exact_mod_cast Work.Analysis.EndVar.logN_nonneg (Nat.floor (a n))
  have hexp : (P.natDegree : ℝ) * ((k₂ : ℝ) - (logN (Nat.floor (a n)) : ℝ))
      ≤ (((P.natDegree * k₂ : ℕ)) : ℝ) := by
    have hdn : (0 : ℝ) ≤ (P.natDegree : ℝ) := Nat.cast_nonneg _
    push_cast
    nlinarith [hdn, hlog0]
  calc |x| ≤ (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - (logN (Nat.floor (a n)) : ℝ))) := hsupp
    _ ≤ (2 : ℝ) ^ ((((P.natDegree * k₂ : ℕ)) : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = (2 : ℝ) ^ (((P.natDegree * k₂ : ℕ)) : ℤ) := by
        rw [Work.KMTPlan.A6.two_zpow_eq_rpow]

/-- **The `ℓ²` bound for the exact-height multiplier with the randomised `g`-side symbol**
(the `g`-side mirror of `Work.KMTPlan.A6.tmRandSymb_l2`).

The two cases of the symbol bound are the narrow (`hthr` holds, non-aliasing collapses the IW
symbol to a single term) and the crude (`hthr` fails, whence `lcL ≤ L0` and the frequency set is
finite) case; the pointwise bound on the randomised symbol is `randSymbG_sup_le`. -/
theorem tmRandSymbG_l2_main (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) :
    ∃ ρ₀ : Real, 0 < ρ₀ ∧ ∀ ρ : Real, 0 < ρ → ρ ≤ ρ₀ → ∃ C : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (t : Real) (ε : ℕ → Complex)
        (g : ℤ → Complex),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        (∀ n, ‖ε n‖ ≤ 1) → t ∈ Set.Icc (1 / 2 : Real) 1 →
        MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
        MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ l₂
            (Work.KMTAreas.A7.randSymb
              (Work.KMTPlan.A6.lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε K) g)
          2 MeasureTheory.Measure.count
        ≤ (C Λ : ENNReal) * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  refine ⟨min 1 (1 / (2 * (C₀ : ℝ))), lt_min zero_lt_one (by positivity), ?_⟩
  intro ρ hρ hρρ₀
  have hρ1 : ρ ≤ 1 := le_trans hρρ₀ (min_le_left _ _)
  have hρC₀ : ρ * (C₀ : ℝ) ≤ 1 / 2 := by
    have h := le_trans hρρ₀ (min_le_right _ _)
    have h2 : ρ * (2 * (C₀ : ℝ)) ≤ 1 :=
      (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (C₀ : ℝ))).mp h
    nlinarith
  obtain ⟨Crho, hCrhoP, hNA, _⟩ := hA1 ρ hρ hρ1
  obtain ⟨L0, hL0⟩ := L_le_of_threshold_fail ρ hρ C₀ hC₀ (max Crho 2)
    (le_trans (by norm_num : (1 : ℝ) ≤ 2) (le_max_right _ _)) hρC₀
  obtain ⟨Cc, hCcP, hCc⟩ := iw_height_card_le (ρ := ρ) hρ
  have hcrux : ∀ Lam : NNReal, 1 < Lam → ∃ C : ℝ, 0 < C ∧
      ∀ (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ) (ε : ℕ → ℂ),
        PointwiseErgodicTheorems.Lacunary Lam a → (∀ n, 1 ≤ a n) → (∀ n, ‖ε n‖ ≤ 1) →
        t ∈ Set.Icc (1 / 2 : ℝ) 1 → ∀ x : ℝ,
          ‖Work.KMTAreas.A7.randSymb (lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε K x‖ ≤ C :=
    fun Lam hLam => by
      obtain ⟨C, hC, hb⟩ := randSymbG_sup_le P hd C₀ Lam hLam
      exact ⟨C, hC, fun a l₁ l₂ k₁ k₂ K t ε hLac ha1 hε ht =>
        hb ρ a l₁ l₂ k₁ k₂ K t ε hLac ha1 hε ht⟩
  let cpsi : NNReal → ℝ := fun Lam => if h : 1 < Lam then Classical.choose (hcrux Lam h) else 1
  have hcpsiP : ∀ Lam : NNReal, 1 < Lam → 0 < cpsi Lam := by
    intro Lam hLam
    simp only [cpsi, dif_pos hLam]
    exact (Classical.choose_spec (hcrux Lam hLam)).1
  have hcpsiB : ∀ (Lam : NNReal) (hLam : 1 < Lam) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ K : ℕ)
      (t : ℝ) (ε : ℕ → ℂ),
      PointwiseErgodicTheorems.Lacunary Lam a → (∀ n, 1 ≤ a n) → (∀ n, ‖ε n‖ ≤ 1) →
      t ∈ Set.Icc (1 / 2 : ℝ) 1 → ∀ x : ℝ,
        ‖Work.KMTAreas.A7.randSymb (lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε K x‖ ≤ cpsi Lam := by
    intro Lam hLam a l₁ l₂ k₁ k₂ K t ε hLac ha1 hε ht
    simp only [cpsi, dif_pos hLam]
    exact (Classical.choose_spec (hcrux Lam hLam)).2 a l₁ l₂ k₁ k₂ K t ε hLac ha1 hε ht
  let Kf : ℝ := max 1 (Cc * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (L0 : ℝ))) *
    (2 * ((2 ^ (P.natDegree * L0) : ℕ) : ℝ) + 4))
  have hKf1 : 1 ≤ Kf := le_max_left _ _
  refine ⟨fun Lam => Real.toNNReal (Kf * cpsi Lam + 1), ?_⟩
  intro a Lam l₁ l₂ k₁ k₂ K t ε g hLam hLac ha1 hε ht hg
  let psig : ℕ → ℝ → ℂ := lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t
  have hpsiran : ∀ x : ℝ, ‖Work.KMTAreas.A7.randSymb psig ε K x‖ ≤ cpsi Lam :=
    hcpsiB Lam hLam a l₁ l₂ k₁ k₂ K t ε hLac ha1 hε ht
  have hmeaspsig : ∀ m : ℕ, Measurable (psig m) :=
    fun m => measurable_lowSymbG P ρ C₀ a l₁ l₂ k₁ k₂ t m
  have hmeas : Measurable (Work.KMTAreas.A7.randSymb psig ε K) := by
    unfold Work.KMTAreas.A7.randSymb
    refine Finset.measurable_sum _ (fun n _ => ?_)
    exact Measurable.const_mul (Measurable.sub (hmeaspsig (n + 1)) (hmeaspsig n)) (ε n)
  have hsupparc : ∀ x : ℝ, Work.KMTAreas.A7.randSymb psig ε K x ≠ 0 →
      x ∈ realArc ((((P.natDegree * k₂ : ℕ)) : ℕ) : ℤ) := by
    intro x hx
    have h := lowSymbG_support P ρ C₀ a l₁ l₂ k₁ k₂ K t ε x (by simpa only [psig] using hx)
    rw [realArc, Set.mem_Icc]
    exact abs_le.mp h
  have hsym : ∀ ξ : Circ, ‖iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l₂)
      (periodize (Work.KMTAreas.A7.randSymb psig ε K)) ξ‖ ≤ Kf * cpsi Lam + 1 := by
    intro ξ
    by_cases hthr : (k₂ : ℝ) + (max Crho 2) * (2 : ℝ) ^ (ρ * (l₂ : ℝ)) + 2 ≤
        (2 : ℝ) ^ (((lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ) / (C₀ : ℝ) - 2)
    · set k : ℤ := ⌊-(max Crho 2) * (2 : ℝ) ^ (ρ * (l₂ : ℝ))⌋ with hk
      have hsuppn : ∀ x : ℝ, Work.KMTAreas.A7.randSymb psig ε K x ≠ 0 → x ∈ realArc k := by
        intro x hx
        obtain ⟨n, _, hn⟩ := exists_ne_zero_of_randSymb_ne_zero hx
        obtain ⟨-, hls, hbump⟩ := support_of_lowSymbG (h := hn)
        have hindex := (lowSmallSet_iff.mp hls).1
        have hle := narrow_of_index_G P hd ρ (max Crho 2) (by positivity) C₀ hC₀ hindex hthr
          x hbump
        rw [realArc, Set.mem_Icc]
        exact abs_le.mp hle
      have hgood : GoodMajorArcs ρ (max Crho 2) l₂ k := by
        show (k : ℝ) ≤ -(max Crho 2) * (2 : ℝ) ^ (ρ * (l₂ : ℝ))
        exact Int.floor_le _
      have hgood' : GoodMajorArcs ρ Crho l₂ k := by
        have h1 : Crho * (2 : ℝ) ^ (ρ * (l₂ : ℝ)) ≤
            (max Crho 2) * (2 : ℝ) ^ (ρ * (l₂ : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        have hg : (k : ℝ) ≤ -(max Crho 2) * (2 : ℝ) ^ (ρ * (l₂ : ℝ)) := hgood
        show (k : ℝ) ≤ -Crho * (2 : ℝ) ^ (ρ * (l₂ : ℝ))
        linarith
      have hNA' : NonAliasing k (Work.KMTAreas.A7.diffFreqs ρ l₂) :=
        nonAliasing_mono (hNA l₂ k hgood') (tmDiffFreqs_subset ρ l₂)
      have h2 : (2 : ℝ) ^ (k + 1) < 1 :=
        Work.Analysis.IWMultiplier.two_pow_succ_lt_one_of_goodMajorArcs hgood (le_max_right _ _) hρ
      have hper : ∀ ξ : Circ, ‖periodize (Work.KMTAreas.A7.randSymb psig ε K) ξ‖ ≤ cpsi Lam :=
        fun ξ => Work.Analysis.IWMultiplier.periodize_norm_le h2 hsuppn (fun x => hpsiran x) ξ
      have hSIA : SupportedInArc k (periodize (Work.KMTAreas.A7.randSymb psig ε K)) :=
        supportedInArc_periodize' hsuppn
      have hb := norm_iwSymbolSet_le_of_nonAliasing hNA' hSIA (le_of_lt (hcpsiP Lam hLam)) hper ξ
      have hK : cpsi Lam ≤ Kf * cpsi Lam + 1 := by nlinarith [hKf1, hcpsiP Lam hLam]
      exact le_trans hb hK
    · have hk2L : k₂ ≤ lcL l₁ l₂ k₁ k₂ := by rw [lcL]; omega
      have hl2L : l₂ ≤ lcL l₁ l₂ k₁ k₂ := by rw [lcL]; omega
      have hL : lcL l₁ l₂ k₁ k₂ ≤ L0 := hL0 (lcL l₁ l₂ k₁ k₂) k₂ l₂ hk2L hl2L hthr
      have hk2 : k₂ ≤ L0 := le_trans hk2L hL
      have hl2 : l₂ ≤ L0 := le_trans hl2L hL
      have hper : ∀ ξ : Circ, ‖periodize (Work.KMTAreas.A7.randSymb psig ε K) ξ‖
          ≤ (2 * ((2 ^ (P.natDegree * L0) : ℕ) : ℝ) + 4) * cpsi Lam := by
        intro ξ
        refine norm_periodize_le (phi := Work.KMTAreas.A7.randSymb psig ε K)
          (R := (2 : ℝ) ^ (((P.natDegree * k₂ : ℕ)) : ℤ)) (C := cpsi Lam)
          (2 ^ (P.natDegree * L0)) ?_ ?_ (fun x => hpsiran x) ξ
        · rw [zpow_natCast]
          have hle : P.natDegree * k₂ ≤ P.natDegree * L0 := Nat.mul_le_mul_left _ hk2
          calc (2 : ℝ) ^ (P.natDegree * k₂) ≤ (2 : ℝ) ^ (P.natDegree * L0) :=
                pow_le_pow_right₀ (by norm_num) hle
            _ = ((2 ^ (P.natDegree * L0) : ℕ) : ℝ) := by push_cast; ring
        · intro x hx
          by_contra hne
          have hmem := hsupparc x hne
          rw [realArc, Set.mem_Icc] at hmem
          have habs : |x| ≤ (2 : ℝ) ^ (((P.natDegree * k₂ : ℕ)) : ℤ) := abs_le.mpr hmem
          rw [zpow_natCast] at habs hx
          linarith
      have hcard : ((Work.KMTAreas.A7.diffFreqs ρ l₂).card : ℝ) ≤
          Cc * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (L0 : ℝ))) := by
        have hsub : (Work.KMTAreas.A7.diffFreqs ρ l₂).card ≤ (iwArithFreqs ρ l₂).card :=
          Finset.card_le_card (tmDiffFreqs_subset ρ l₂)
        have h1 : ((iwArithFreqs ρ l₂).card : ℝ) ≤ Cc * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l₂ : ℝ))) :=
          hCc l₂
        have h2 : (2 : ℝ) ^ (ρ * (l₂ : ℝ)) ≤ (2 : ℝ) ^ (ρ * (L0 : ℝ)) :=
          (Real.rpow_le_rpow_left_iff (show (1 : ℝ) < 2 by norm_num)).mpr (by
            have : (l₂ : ℝ) ≤ (L0 : ℝ) := by exact_mod_cast hl2
            nlinarith [hρ.le])
        have h3 : (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l₂ : ℝ))) ≤ (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (L0 : ℝ))) :=
          (Real.rpow_le_rpow_left_iff (show (1 : ℝ) < 2 by norm_num)).mpr h2
        calc ((Work.KMTAreas.A7.diffFreqs ρ l₂).card : ℝ)
            ≤ ((iwArithFreqs ρ l₂).card : ℝ) := by exact_mod_cast hsub
          _ ≤ Cc * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l₂ : ℝ))) := h1
          _ ≤ Cc * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (L0 : ℝ))) := mul_le_mul_of_nonneg_left h3 hCcP.le
      have hb := norm_iwSymbolSet_le (Work.KMTAreas.A7.diffFreqs ρ l₂)
        (C := (2 * ((2 ^ (P.natDegree * L0) : ℕ) : ℝ) + 4) * cpsi Lam) hper ξ
      have hKf : Cc * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (L0 : ℝ))) *
          (2 * ((2 ^ (P.natDegree * L0) : ℕ) : ℝ) + 4) ≤ Kf := le_max_right _ _
      calc ‖iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l₂)
              (periodize (Work.KMTAreas.A7.randSymb psig ε K)) ξ‖
          ≤ ((Work.KMTAreas.A7.diffFreqs ρ l₂).card : ℝ) *
              ((2 * ((2 ^ (P.natDegree * L0) : ℕ) : ℝ) + 4) * cpsi Lam) := hb
        _ ≤ (Cc * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (L0 : ℝ)))) *
              ((2 * ((2 ^ (P.natDegree * L0) : ℕ) : ℝ) + 4) * cpsi Lam) := by
            apply mul_le_mul_of_nonneg_right hcard
            exact mul_nonneg (by positivity) (hcpsiP Lam hLam).le
        _ = (Cc * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (L0 : ℝ))) *
              (2 * ((2 ^ (P.natDegree * L0) : ℕ) : ℝ) + 4)) * cpsi Lam := by ring
        _ ≤ Kf * cpsi Lam := mul_le_mul_of_nonneg_right hKf (hcpsiP Lam hLam).le
        _ ≤ Kf * cpsi Lam + 1 := by linarith
  have hPhi : MemLp (iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l₂)
      (periodize (Work.KMTAreas.A7.randSymb psig ε K))) ⊤ circleMeasure :=
    Work.Analysis.IWMultiplier.memLp_iwSymbolSet _
      (Work.Analysis.IonescuWainger.memLp_periodize (φ := Work.KMTAreas.A7.randSymb psig ε K)
        (R := (2 : ℝ) ^ (((P.natDegree * k₂ : ℕ)) : ℤ)) (C := cpsi Lam) hmeas
        (zpow_nonneg (by norm_num) _)
        (fun x hx => by
          by_contra hne
          have hmem := hsupparc x hne
          rw [realArc, Set.mem_Icc] at hmem
          have habs : |x| ≤ (2 : ℝ) ^ (((P.natDegree * k₂ : ℕ)) : ℤ) := abs_le.mpr hmem
          rw [zpow_natCast] at habs hx
          linarith)
        (fun x => hpsiran x))
  have hmain := eLpNorm_iwConv_two_le_of_symbol_bound (Work.KMTAreas.A7.diffFreqs ρ l₂)
    (periodize (Work.KMTAreas.A7.randSymb psig ε K)) (Kf * cpsi Lam + 1)
    (by nlinarith [hcpsiP Lam hLam, hKf1]) hsym hPhi g hg
  change MeasureTheory.eLpNorm (Work.Analysis.IWMultiplier.iwConv (Work.KMTAreas.A7.diffFreqs ρ l₂)
      (periodize (Work.KMTAreas.A7.randSymb psig ε K)) g) 2 MeasureTheory.Measure.count
      ≤ ((Real.toNNReal (Kf * cpsi Lam + 1) : NNReal) : ENNReal)
          * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count
  exact hmain


/-- **The `ℓ²` bound for the exact-height multiplier with the randomised `g`-side symbol**
(Krause--Mirek--Tao, the `g`-side companion of the `ℓ²` bound for the randomised
cut-offs). -/
theorem tmRandSymbG_l2 (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) :
    ∃ ρ₀ : Real, 0 < ρ₀ ∧ ∀ ρ : Real, 0 < ρ → ρ ≤ ρ₀ → ∃ C : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (t : Real) (ε : ℕ → Complex)
        (g : ℤ → Complex),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        (∀ n, ‖ε n‖ ≤ 1) → t ∈ Set.Icc (1 / 2 : Real) 1 →
        MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
        MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ l₂
            (Work.KMTAreas.A7.randSymb
              (Work.KMTPlan.A6.lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε K) g)
          2 MeasureTheory.Measure.count
        ≤ (C Λ : ENNReal) * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count :=
  tmRandSymbG_l2_main P hd hA1 C₀ hC₀

end
end Work.KMTPlan.A6
