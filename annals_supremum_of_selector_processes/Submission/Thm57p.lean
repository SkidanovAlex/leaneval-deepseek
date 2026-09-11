import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.SelCore
import Submission.Deep
import Submission.Chain12
import Submission.Ratio
import Submission.BinomOne
import Submission.Binom
import Submission.Binom2
import Submission.BinomMed
import Submission.DeepThm

/-!
# 5.7' (real form) for sup-type processes.

Assembled from:
  - Chain12.thm57gen  (deep theorem: 10^{-11} ≤ uniform average over w0-subsets,
                       w0 = wSize J0 n p, J0 = 10^{20})
  - Ratio.sizeAvg_ratio   (uniform N-subset average ≥ (N/w0)·(w0-subset average))
  - Binom2.binom_ge_uniform / BinomOne.binom_ge_one (binomial vs uniform)
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Classical
open MeasureTheory ProbabilityTheory Measure unitInterval Finset
open scoped NNReal ENNReal BigOperators

namespace Submission

open _root_.SupremumOfSelectorProcesses

namespace Thm57p

open Frame
open Sel
open Sel.Deep
open Sel.Deep.Sys
open Chain12

variable {X : Type*} [Fintype X]

/-- deep parameter -/
noncomputable def J0 : ℕ := 10 ^ 20

/-- the final 5.7' constant -/
noncomputable def c0 : ℝ := ((10 : ℝ) ^ 11)⁻¹ * ((4 : ℝ) * (J0 : ℝ))⁻¹

/-- Sys.avgOver equals Binom.sizeAvg -/
lemma avgOver_eq_sizeAvg (v : Set X → ℝ) (w : ℕ) (hw : w ≤ Fintype.card X) :
    Sys.avgOver v w = Binom.sizeAvg v w := by
  classical
  rw [DeepThm.avgOver_eq v w hw]
  rw [show Binom.sizeAvg v w = Binom2.sizeAvg v w by rfl]
  rw [Binom2.sizeAvg_eq v w hw]
  rfl

/-- monotone sup-type function -/
lemma supFW_monotone {lam : Set X → X → ℝ} {F : Set (Set X)}
    (hnonneg : ∀ S ∈ F, ∀ i ∈ S, 0 ≤ lam S i) : Monotone (fun W : Set X => supFW lam F W) := by
  intro W W' hWW'
  exact Chain12.supFW_mono hnonneg hWW'

/-- nonneg sup-type function -/
lemma supFW_nonneg_all {lam : Set X → X → ℝ} {F : Set (Set X)}
    (hnonneg : ∀ S ∈ F, ∀ i ∈ S, 0 ≤ lam S i) : ∀ W : Set X, 0 ≤ supFW lam F W := by
  intro W
  exact Chain12.supFW_nonneg hnonneg W

/-- floor toNat = floor (when x ≥ 0) -/
lemma floor_toNat_eq (x : ℝ) (hx0 : 0 ≤ x) : (⌊x⌋.toNat : ℝ) = (⌊x⌋ : ℝ) := by
  classical
  have h1 : (⌊x⌋.toNat : ℤ) = ⌊x⌋ := Int.toNat_of_nonneg (Int.floor_nonneg.mpr hx0)
  exact_mod_cast h1

/-- floor toNat ≤ x -/
lemma floor_toNat_le_real (x : ℝ) (hx0 : 0 ≤ x) : (⌊x⌋.toNat : ℝ) ≤ x := by
  classical
  rw [floor_toNat_eq x hx0]
  exact Int.floor_le x

/-- 1 ≤ ⌊x⌋.toNat when 1 ≤ x -/
lemma one_le_floor_toNat (x : ℝ) (hx0 : 0 ≤ x) (hx1 : (1 : ℝ) ≤ x) :
    (1 : ℕ) ≤ ⌊x⌋.toNat := by
  classical
  have hfl : (1 : ℤ) ≤ ⌊x⌋ := by
    have h := Int.floor_le_floor hx1
    simpa using h
  have hto : (⌊x⌋.toNat : ℤ) = ⌊x⌋ := Int.toNat_of_nonneg (Int.floor_nonneg.mpr hx0)
  have hle : (1 : ℤ) ≤ (⌊x⌋.toNat : ℤ) := by simpa [hto] using hfl
  exact_mod_cast hle

/-- floor bound: for x ≥ 0, x - 1 ≤ ⌊x⌋.toNat -/
lemma floor_sub_one (x : ℝ) (hx0 : 0 ≤ x) : x - 1 ≤ (⌊x⌋.toNat : ℝ) := by
  classical
  have hxgt : x - 1 < (⌊x⌋ : ℝ) := by
    have h : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
    linarith
  rw [floor_toNat_eq x hx0]
  exact le_of_lt hxgt

/-- if np ≥ 1 then np ≤ 2·⌊np⌋.toNat -/
lemma np_le_two_floor (p : ℝ) (hp0 : 0 ≤ p) (n : ℕ) (hnp1 : (1 : ℝ) ≤ (n : ℝ) * p) :
    (n : ℝ) * p ≤ 2 * (⌊(n : ℝ) * p⌋.toNat : ℝ) := by
  classical
  set y : ℝ := (n : ℝ) * p with hy
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hy1 : 1 ≤ y := by rw [hy]; exact hnp1
  by_cases hbig : 2 ≤ y
  · have hxsub : y - 1 ≤ (⌊y⌋.toNat : ℝ) := floor_sub_one y hy0
    have hhalf : y / 2 ≤ y - 1 := by nlinarith
    have hle : y / 2 ≤ (⌊y⌋.toNat : ℝ) := le_trans hhalf hxsub
    nlinarith
  · have h1 : (1 : ℝ) ≤ (⌊y⌋.toNat : ℝ) := by exact_mod_cast one_le_floor_toNat y hy0 hy1
    have hylt : y < 2 := lt_of_not_ge hbig
    nlinarith

/-- w0 (deep size) is bounded by J0·np -/
lemma w0_le_J0np (p : ℝ) (hp0 : 0 ≤ p) (n : ℕ) :
    (Sys.wSize J0 n p : ℝ) ≤ (J0 : ℝ) * (n : ℝ) * p := by
  classical
  unfold Sys.wSize
  rw [Nat.cast_min]
  have hf : (⌊(J0 : ℝ) * (n : ℝ) * p⌋.toNat : ℝ) ≤ (J0 : ℝ) * (n : ℝ) * p := by
    exact floor_toNat_le_real ((J0 : ℝ) * (n : ℝ) * p) (by positivity)
  exact le_trans (min_le_right (n : ℝ) (⌊(J0 : ℝ) * (n : ℝ) * p⌋.toNat : ℝ)) hf

/-- w0 ≥ 1 when np ≥ 1/2 -/
lemma w0_ge_one (p : ℝ) (hp0 : 0 < p) (n : ℕ) (hn : (1 : ℕ) ≤ n)
    (hnp : (1 / 2 : ℝ) ≤ (n : ℝ) * p) : 1 ≤ Sys.wSize J0 n p := by
  classical
  unfold Sys.wSize
  have hJ2 : (2 : ℝ) ≤ (J0 : ℝ) := by norm_num [J0]
  have hJnp : (1 : ℝ) ≤ (J0 : ℝ) * (n : ℝ) * p := by
    have hnp0 : 0 ≤ (n : ℝ) * p := by positivity
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    nlinarith
  have hf1 : (1 : ℝ) ≤ (⌊(J0 : ℝ) * (n : ℝ) * p⌋.toNat : ℝ) := by
    exact_mod_cast one_le_floor_toNat ((J0 : ℝ) * (n : ℝ) * p) (by positivity) hJnp
  have hf1nat : (1 : ℕ) ≤ ⌊(J0 : ℝ) * (n : ℝ) * p⌋.toNat := by exact_mod_cast hf1
  exact le_min hn hf1nat

/-- the family has no empty member under total-weight hypothesis -/
lemma not_mem_empty {lam : Set X → X → ℝ} {F : Set (Set X)}
    (htot1 : ∀ S ∈ F, 1 ≤ Sys.wtot lam S) : (∅ : Set X) ∉ F := by
  classical
  intro hmem
  have htot := htot1 ∅ hmem
  have hz : Sys.wtot lam (∅ : Set X) = 0 := by
    simp [Sys.wtot]
  rw [hz] at htot
  norm_num at htot

/-- if r·A ≤ w·B with 0 < w and 0 ≤ r then (r/w)·A ≤ B -/
lemma div_ratio (A B r w : ℝ) (hw : 0 < w) (hr : 0 ≤ r) (h : r * A ≤ w * B) :
    (r / w) * A ≤ B := by
  have hw' : w ≠ 0 := ne_of_gt hw
  calc
    (r / w) * A = (r * A) / w := by ring
    _ ≤ (w * B) / w := by exact div_le_div_of_nonneg_right h (le_of_lt hw)
    _ = B := by field_simp [hw']

/-- 5.7' (real form): if 𝓕 with total weight ≥ 1 is not p-small then
    the binomial sum of the sup-process is ≥ c0. -/
theorem thm57p (p : ℝ) (F : Set (Set X)) (lam : Set X → X → ℝ)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hnonneg : ∀ S ∈ F, ∀ i ∈ S, 0 ≤ lam S i)
    (htot1 : ∀ S ∈ F, 1 ≤ Sys.wtot lam S)
    (hnot : ¬ pSmall p F) :
    c0 ≤ Binom.binomSum p (fun W : Set X => supFW lam F W) := by
  classical
  set n : ℕ := Fintype.card X with hn
  have hnotmem : (∅ : Set X) ∉ F := not_mem_empty htot1
  have hnpgt : (2 : ℝ)⁻¹ < (n : ℝ) * p := by
    simpa [hn] using (pSmall.not_of_np (p := p) (𝓕 := F) hnot hnotmem)
  have hnp12 : (1 / 2 : ℝ) ≤ (n : ℝ) * p := by
    have hlt : (1 / 2 : ℝ) < (n : ℝ) * p := by
      norm_num at hnpgt
      exact hnpgt
    exact le_of_lt hlt
  have hn1 : (1 : ℕ) ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    have : (1 / 2 : ℝ) ≤ (0 : ℝ) := by simpa [hn0] using hnp12
    norm_num at this
  let w0 : ℕ := Sys.wSize J0 n p
  have hw0le : w0 ≤ n := by
    dsimp [w0]
    unfold Sys.wSize
    exact min_le_left n _
  have hw0n : w0 ≤ Fintype.card X := by
    rw [← hn]
    exact hw0le
  have hw0pos : 0 < w0 := by
    exact w0_ge_one p hp0 n hn1 hnp12
  have hJ0 : 10 ^ 20 ≤ J0 := by norm_num [J0]
  have hdeep := Chain12.thm57gen p J0 F lam hJ0 hp0 hp1 hnonneg htot1 hnot
  have hdeepAvg : ((10 : ℝ) ^ 11)⁻¹ ≤ Binom.sizeAvg (supFW lam F) w0 := by
    have hsz : Sys.wSize J0 (Fintype.card X) p = w0 := rfl
    have hconv : Sys.avgOver (supFW lam F) (Sys.wSize J0 (Fintype.card X) p)
        ≤ Binom.sizeAvg (supFW lam F) w0 := by
      rw [hsz]
      rw [avgOver_eq_sizeAvg (supFW lam F) w0 hw0n]
    exact le_trans hdeep hconv
  let g : Set X → ℝ := fun W : Set X => supFW lam F W
  have hg0 : ∀ T : Set X, 0 ≤ g T := by
    intro T; exact supFW_nonneg_all hnonneg T
  have hgmono : Monotone g := by
    intro W W' hW
    exact supFW_monotone hnonneg hW
  by_cases hbig : (1 : ℝ) ≤ (n : ℝ) * p
  · -- case A: np ≥ 1
    let N : ℕ := ⌊(n : ℝ) * p⌋.toNat
    have hNn : N ≤ n := by
      have hNle : (N : ℝ) ≤ (n : ℝ) * p := by
        dsimp [N]
        exact floor_toNat_le_real ((n : ℝ) * p) (by positivity)
      have hnlt : (n : ℝ) * p < (n : ℝ) := by
        have hn0 : 0 ≤ (n : ℝ) := by positivity
        nlinarith
      have hNlt : (N : ℝ) < (n : ℝ) := lt_of_le_of_lt hNle hnlt
      have hNltn : N < n := by exact_mod_cast hNlt
      exact le_of_lt hNltn
    have hN0 : 0 < N := by
      have hfl : (1 : ℤ) ≤ ⌊(n : ℝ) * p⌋ := by
        have h := Int.floor_le_floor hbig
        simpa using h
      have hx0 : 0 ≤ (n : ℝ) * p := by positivity
      have hto : (⌊(n : ℝ) * p⌋.toNat : ℤ) = ⌊(n : ℝ) * p⌋ :=
        Int.toNat_of_nonneg (Int.floor_nonneg.mpr hx0)
      have hle : (1 : ℤ) ≤ (⌊(n : ℝ) * p⌋.toNat : ℤ) := by simpa [hto] using hfl
      have h1nat : (1 : ℕ) ≤ ⌊(n : ℝ) * p⌋.toNat := by exact_mod_cast hle
      exact h1nat
    have hNw : N ≤ w0 := by
      change ⌊(n : ℝ) * p⌋.toNat ≤ min n ⌊(J0 : ℝ) * (n : ℝ) * p⌋.toNat
      have hNf : ⌊(n : ℝ) * p⌋.toNat ≤ ⌊(J0 : ℝ) * (n : ℝ) * p⌋.toNat := by
        have hJ : (1 : ℝ) ≤ (J0 : ℝ) := by norm_num [J0]
        have hnp0 : 0 ≤ (n : ℝ) * p := by positivity
        have hle : (n : ℝ) * p ≤ (J0 : ℝ) * (n : ℝ) * p := by nlinarith
        have hfl : ⌊(n : ℝ) * p⌋ ≤ ⌊(J0 : ℝ) * (n : ℝ) * p⌋ := Int.floor_mono hle
        have h1 : 0 ≤ ⌊(n : ℝ) * p⌋ := Int.floor_nonneg.mpr hnp0
        have h2 : (⌊(n : ℝ) * p⌋.toNat : ℤ) = ⌊(n : ℝ) * p⌋ := Int.toNat_of_nonneg h1
        have h3 : 0 ≤ ⌊(J0 : ℝ) * (n : ℝ) * p⌋ :=
          Int.floor_nonneg.mpr (by positivity)
        have h4 : (⌊(J0 : ℝ) * (n : ℝ) * p⌋.toNat : ℤ) = ⌊(J0 : ℝ) * (n : ℝ) * p⌋ :=
          Int.toNat_of_nonneg h3
        have hle' : (⌊(n : ℝ) * p⌋.toNat : ℤ) ≤ (⌊(J0 : ℝ) * (n : ℝ) * p⌋.toNat : ℤ) := by
          rw [h2, h4]
          exact hfl
        exact_mod_cast hle'
      exact le_min hNn hNf
    have hratio := Ratio.sizeAvg_ratio (lam := lam) (F := F) hnonneg N w0 hN0 hNw hw0n
    have hNposR : 0 < (N : ℝ) := by exact_mod_cast hN0
    have hw0posR : 0 < (w0 : ℝ) := by exact_mod_cast hw0pos
    have hratio_g : (N : ℝ) * Binom.sizeAvg g w0 ≤ (w0 : ℝ) * Binom.sizeAvg g N := by
      simpa [g] using hratio
    have hdiv : (N : ℝ) / (w0 : ℝ) * Binom.sizeAvg g w0 ≤ Binom.sizeAvg g N :=
      div_ratio (Binom.sizeAvg g w0) (Binom.sizeAvg g N) (N : ℝ) (w0 : ℝ) hw0posR
        (le_of_lt hNposR) hratio_g
    have hmult : (N : ℝ) / (w0 : ℝ) * ((10 : ℝ) ^ 11)⁻¹ ≤
        (N : ℝ) / (w0 : ℝ) * Binom.sizeAvg g w0 := by
      exact mul_le_mul_of_nonneg_left hdeepAvg (by positivity)
    have hNw0 : (N : ℝ) / (w0 : ℝ) * ((10 : ℝ) ^ 11)⁻¹ ≤ Binom.sizeAvg g N :=
      le_trans hmult hdiv
    have hNb : (1 : ℝ) / (2 * (J0 : ℝ)) ≤ (N : ℝ) / (w0 : ℝ) := by
      have hle : (w0 : ℝ) ≤ 2 * (J0 : ℝ) * (N : ℝ) := by
        have h1 := w0_le_J0np p (le_of_lt hp0) n
        have h2 := np_le_two_floor p (le_of_lt hp0) n hbig
        nlinarith
      have hJpos : 0 < 2 * (J0 : ℝ) := by positivity
      rw [div_le_div_iff₀ hJpos hw0posR]
      nlinarith
    have hUni := Binom2.binom_ge_uniform p hp0 hp1 N (by rfl : N = ⌊(Fintype.card X : ℝ) * p⌋.toNat) g hg0 hgmono
    have hAne : ((10 : ℝ) ^ 11) ≠ 0 := by positivity
    have hJne : (J0 : ℝ) ≠ 0 := by positivity
    have heq0 : c0 = (1 / 2 : ℝ) * (1 / (2 * (J0 : ℝ))) * ((10 : ℝ) ^ 11)⁻¹ := by
      dsimp [c0]
      field_simp [hJne, hAne]
      ring
    have hc0 : c0 ≤ (1 / 2 : ℝ) * Binom.sizeAvg g N := by
      have hstep1 : (1 / 2 : ℝ) * Binom.sizeAvg g N ≥
          (1 / 2 : ℝ) * ((N : ℝ) / (w0 : ℝ)) * ((10 : ℝ) ^ 11)⁻¹ := by
        have hm : (1 / 2 : ℝ) * (((N : ℝ) / (w0 : ℝ)) * ((10 : ℝ) ^ 11)⁻¹) ≤
            (1 / 2 : ℝ) * Binom.sizeAvg g N := by
          exact mul_le_mul_of_nonneg_left hNw0 (by norm_num)
        calc
          (1 / 2 : ℝ) * ((N : ℝ) / (w0 : ℝ)) * ((10 : ℝ) ^ 11)⁻¹
              = (1 / 2 : ℝ) * (((N : ℝ) / (w0 : ℝ)) * ((10 : ℝ) ^ 11)⁻¹) := by ring_nf
          _ ≤ (1 / 2 : ℝ) * Binom.sizeAvg g N := hm
      have hstep0 : c0 ≤ (1 / 2 : ℝ) * ((N : ℝ) / (w0 : ℝ)) * ((10 : ℝ) ^ 11)⁻¹ := by
        rw [heq0]
        have hc : 0 ≤ (1 / 2 : ℝ) * ((10 : ℝ) ^ 11)⁻¹ := by positivity
        have hm := mul_le_mul_of_nonneg_left hNb hc
        calc
          (1 / 2 : ℝ) * (1 / (2 * (J0 : ℝ))) * ((10 : ℝ) ^ 11)⁻¹
              = ((1 / 2 : ℝ) * ((10 : ℝ) ^ 11)⁻¹) * (1 / (2 * (J0 : ℝ))) := by ring_nf
          _ ≤ ((1 / 2 : ℝ) * ((10 : ℝ) ^ 11)⁻¹) * ((N : ℝ) / (w0 : ℝ)) := hm
          _ = (1 / 2 : ℝ) * ((N : ℝ) / (w0 : ℝ)) * ((10 : ℝ) ^ 11)⁻¹ := by ring_nf
      exact le_trans hstep0 hstep1
    calc
      c0 ≤ (1 / 2 : ℝ) * Binom.sizeAvg g N := hc0
      _ ≤ Binom2.binomSum p g := by simpa [Binom2.sizeAvg] using hUni
  · -- case B: np < 1
    have hnp1 : (n : ℝ) * p < 1 := lt_of_not_ge hbig
    have hw0leJ : (w0 : ℝ) ≤ (J0 : ℝ) := by
      have h1 := w0_le_J0np p (le_of_lt hp0) n
      have hJ : 0 < (J0 : ℝ) := by positivity
      nlinarith
    have hOne := BinomOne.binom_ge_one p hp0 hp1 hnp12 g hg0 hgmono
    have hw0posR : 0 < (w0 : ℝ) := by exact_mod_cast hw0pos
    have hratio1 := Ratio.sizeAvg_ratio (lam := lam) (F := F) hnonneg 1 w0
      (by norm_num : 0 < 1) hw0pos hw0n
    have hratio1g : Binom.sizeAvg g w0 ≤ (w0 : ℝ) * Binom.sizeAvg g 1 := by
      simpa [g] using hratio1
    have hdiv1 : (1 : ℝ) / (w0 : ℝ) * Binom.sizeAvg g w0 ≤ Binom.sizeAvg g 1 :=
      div_ratio (Binom.sizeAvg g w0) (Binom.sizeAvg g 1) 1 (w0 : ℝ) hw0posR (by norm_num)
        (by simpa using hratio1g)
    have hmult1 : (1 : ℝ) / (w0 : ℝ) * ((10 : ℝ) ^ 11)⁻¹ ≤
        (1 : ℝ) / (w0 : ℝ) * Binom.sizeAvg g w0 := by
      exact mul_le_mul_of_nonneg_left hdeepAvg (by positivity)
    have hRatio1 : (1 : ℝ) / (w0 : ℝ) * ((10 : ℝ) ^ 11)⁻¹ ≤ Binom.sizeAvg g 1 :=
      le_trans hmult1 hdiv1
    have h1b : (1 : ℝ) / (J0 : ℝ) ≤ (1 : ℝ) / (w0 : ℝ) :=
      one_div_le_one_div_of_le hw0posR hw0leJ
    have hAne : ((10 : ℝ) ^ 11) ≠ 0 := by positivity
    have hJne : (J0 : ℝ) ≠ 0 := by positivity
    have heq0B : c0 = (1 / 4 : ℝ) * (1 / (J0 : ℝ)) * ((10 : ℝ) ^ 11)⁻¹ := by
      dsimp [c0]
      field_simp [hJne, hAne]
    have hc0 : c0 ≤ (1 / 4 : ℝ) * ((1 : ℝ) / (w0 : ℝ)) * ((10 : ℝ) ^ 11)⁻¹ := by
      rw [heq0B]
      have hc : 0 ≤ (1 / 4 : ℝ) * ((10 : ℝ) ^ 11)⁻¹ := by positivity
      have hm := mul_le_mul_of_nonneg_left h1b hc
      calc
        (1 / 4 : ℝ) * (1 / (J0 : ℝ)) * ((10 : ℝ) ^ 11)⁻¹
            = ((1 / 4 : ℝ) * ((10 : ℝ) ^ 11)⁻¹) * (1 / (J0 : ℝ)) := by ring_nf
        _ ≤ ((1 / 4 : ℝ) * ((10 : ℝ) ^ 11)⁻¹) * (1 / (w0 : ℝ)) := hm
        _ = (1 / 4 : ℝ) * (1 / (w0 : ℝ)) * ((10 : ℝ) ^ 11)⁻¹ := by ring_nf
    calc
      c0 ≤ (1 / 4 : ℝ) * ((1 : ℝ) / (w0 : ℝ)) * ((10 : ℝ) ^ 11)⁻¹ := hc0
      _ ≤ (1 / 4 : ℝ) * Binom.sizeAvg g 1 := by
            have hm : (1 / 4 : ℝ) * (((1 : ℝ) / (w0 : ℝ)) * ((10 : ℝ) ^ 11)⁻¹) ≤
                (1 / 4 : ℝ) * Binom.sizeAvg g 1 := by
              exact mul_le_mul_of_nonneg_left hRatio1 (by norm_num)
            calc
              (1 / 4 : ℝ) * ((1 : ℝ) / (w0 : ℝ)) * ((10 : ℝ) ^ 11)⁻¹
                  = (1 / 4 : ℝ) * (((1 : ℝ) / (w0 : ℝ)) * ((10 : ℝ) ^ 11)⁻¹) := by ring_nf
              _ ≤ (1 / 4 : ℝ) * Binom.sizeAvg g 1 := hm
      _ ≤ Binom2.binomSum p g := by simpa [Binom2.sizeAvg, Binom2.binomSum] using hOne

end Thm57p
end Submission
