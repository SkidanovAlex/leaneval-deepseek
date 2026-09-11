import Mathlib
import Submission.Deep
import Submission.DeepCore
import Submission.Levels1
import Submission.LevelFinal
import Submission.CountLemmas

/-!
# Shared infrastructure for the fixed-U step (Rao coding lemma)

All definitions and helper lemmas for `Submission.Sun.fixed_U_step` live here
(instead of directly in `FixedU.lean`) so that auxiliary modules (children
working on the case analyses) can import them without importing the main
theorem.
-/
open Finset
open scoped BigOperators
open Real

namespace Submission.Sun

variable {α : Type*} [DecidableEq α]

/-! ## Basic facts about `χ`, `V`-subsets and cardinalities -/

lemma chi_subset_sdiff {S : Finset (Finset α)} {X U A : Finset α}
    (hA : A ∈ S) (hU : U ⊆ X) (hA1 : A ⊆ X) : chi S U A ⊆ X \ U := by
  intro x hx
  have hxbest : x ∈ best S U A := (Finset.mem_sdiff.mp hx).1
  have hnotU : x ∉ U := (Finset.mem_sdiff.mp hx).2
  have hxUn : x ∈ A ∪ U := best_subset_union (S:=S) (U:=U) (A:=A) hA hxbest
  have hxX : x ∈ X := by
    rcases Finset.mem_union.mp hxUn with hxA | hxU
    · exact hA1 hxA
    · exact hU hxU
  exact Finset.mem_sdiff.mpr ⟨hxX, hnotU⟩

lemma chi_card_le_k'' {S : Finset (Finset α)} {U A : Finset α} {k : ℕ}
    (hA : A ∈ S) (huni : ∀ A ∈ S, A.card = k) :
    (chi S U A).card ≤ k := by
  have hc : (chi S U A).card ≤ (A \ U).card := chi_card_le_self (S:=S) (U:=U) (A:=A) hA
  have hcard : (A \ U).card ≤ A.card := by
    exact Finset.card_le_card (by intro x hx; exact (Finset.mem_sdiff.mp hx).1)
  exact le_trans hc (le_trans hcard (le_of_eq (huni A hA)))

/-- members V of the v-subsets of X\U -/
lemma mem_cardSubsets_sdiff {X U V : Finset α} {v : ℕ} (hV : V ∈ cardSubsets (X \ U) v) :
    V ⊆ X ∧ V ⊆ X \ U ∧ V.card = v ∧ Disjoint U V := by
  have hV' : V ⊆ X \ U ∧ V.card = v := by
    simpa [cardSubsets] using (Finset.mem_powersetCard.mp hV)
  refine ⟨?_, hV'.1, hV'.2, ?_⟩
  · exact hV'.1.trans Finset.sdiff_subset
  · exact (Finset.subset_sdiff.mp hV'.1).2.symm

/-- t ≤ s: |χ(A,U∪V)| ≤ |χ(A,U)| -/
lemma chi_ext_le_fix {S : Finset (Finset α)} {X U V A : Finset α} {v : ℕ} (hA : A ∈ S)
    (hV : V ∈ cardSubsets (X \ U) v) :
    (chi S (U ∪ V) A).card ≤ (chi S U A).card := by
  exact chi_card_mono (S:=S) (U:=U) (W:=U ∪ V) (A:=A) hA (Finset.subset_union_left)

/-- χ(A,U∪V) ⊆ X\U -/
lemma chi_ext_subset_sdiff {S : Finset (Finset α)} {X U V A : Finset α} {v : ℕ} (hA : A ∈ S)
    (hV : V ∈ cardSubsets (X \ U) v) (hU : U ⊆ X) (hA1 : A ⊆ X) :
    chi S (U ∪ V) A ⊆ X \ U := by
  have hUV : U ∪ V ⊆ X := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxU | hxV
    · exact hU hxU
    · exact (mem_cardSubsets_sdiff hV).1 hxV
  have h1 : chi S (U ∪ V) A ⊆ X \ (U ∪ V) :=
    chi_subset_sdiff (S:=S) (X:=X) (U:=U ∪ V) (A:=A) hA hUV hA1
  intro x hx
  have hx' := h1 hx
  exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx').1,
    fun hxU => (Finset.mem_sdiff.mp hx').2 (Finset.mem_union_left V hxU)⟩

/-- if no member of S in U then all remainders have cardinal ≥ 1 -/
lemma s_pos {S : Finset (Finset α)} {U A : Finset α} (hA : A ∈ S)
    (hU : ¬ ∃ A' ∈ S, A' ⊆ U) : 1 ≤ (chi S U A).card := by
  have h : 0 < (chi S U A).card := by
    have hz : (chi S U A).card ≠ 0 := by
      intro h0
      exact hU ((chi_card_zero_iff (S:=S) (U:=U) (A:=A) hA).1 h0)
    omega
  omega

/-- S nonempty from |S| ≥ r^k -/
lemma S_ne_of_Sr' {S : Finset (Finset α)} {k : ℕ} {r : ℝ} (hk : 1 ≤ k) (hr1 : 1 ≤ r)
    (hSr : (S.card : ℝ) ≥ r ^ k) : S.Nonempty := by
  have h1 : (1 : ℝ) ≤ r ^ k := by
    exact one_le_pow₀ hr1
  have hpos : 0 < S.card := by
    have hcard : (1 : ℝ) ≤ (S.card : ℝ) := by nlinarith
    exact_mod_cast (by nlinarith : (0 : ℝ) < (S.card : ℝ))
  exact Finset.card_pos.mp hpos

/-- X\U cardinal: N = X.card - U.card -/
lemma card_sdiff_of_subset' {X U : Finset α} (hU : U ⊆ X) :
    (X \ U).card = X.card - U.card :=
  Finset.card_sdiff_of_subset hU

/-! ## The fixed-U-step context as derived hypotheses -/

/-- canonical remainder-candidate member whose remainder ⊆ B0 (minimizing |χ|) -/
noncomputable def remCand (S : Finset (Finset α)) (U B0 : Finset α) : Finset (Finset α) :=
  S.filter (fun y : Finset α => chi S U y ⊆ B0)

/-- canonical member of S with remainder inside B0, minimizing remainder size -/
noncomputable def remMin (S : Finset (Finset α)) (U B0 : Finset α) : Finset α :=
  if h : (remCand S U B0).Nonempty then
    Classical.choose (Finset.exists_min_image (remCand S U B0)
      (fun y : Finset α => (chi S U y).card) h)
  else ∅

lemma remMin_spec {S : Finset (Finset α)} {U B0 : Finset α}
    (h : (remCand S U B0).Nonempty) :
    remMin S U B0 ∈ remCand S U B0 ∧
      ∀ y ∈ remCand S U B0, (chi S U (remMin S U B0)).card ≤ (chi S U y).card := by
  unfold remMin
  rw [dif_pos h]
  exact Classical.choose_spec
    (Finset.exists_min_image (remCand S U B0) (fun y : Finset α => (chi S U y).card) h)

lemma remMin_mem_S {S : Finset (Finset α)} {U B0 A : Finset α} (hA : A ∈ S)
    (hR : chi S U A ⊆ B0) : remMin S U B0 ∈ S := by
  have hnon : (remCand S U B0).Nonempty := ⟨A, by simp [remCand, hA, hR]⟩
  exact (Finset.mem_filter.mp (remMin_spec hnon).1).1

lemma remMin_rem_subset {S : Finset (Finset α)} {U B0 A : Finset α} (hA : A ∈ S)
    (hR : chi S U A ⊆ B0) : chi S U (remMin S U B0) ⊆ B0 := by
  have hnon : (remCand S U B0).Nonempty := ⟨A, by simp [remCand, hA, hR]⟩
  exact (Finset.mem_filter.mp (remMin_spec hnon).1).2

lemma remMin_rem_le {S : Finset (Finset α)} {U B0 A : Finset α} (hA : A ∈ S)
    (hR : chi S U A ⊆ B0) :
    (chi S U (remMin S U B0)).card ≤ (chi S U A).card := by
  have hnon : (remCand S U B0).Nonempty := ⟨A, by simp [remCand, hA, hR]⟩
  exact (remMin_spec hnon).2 A (by simp [remCand, hA, hR])

end Submission.Sun

namespace Submission.Sun

variable {α : Type*} [DecidableEq α]

/-! ## Vocabulary of the fixed-U proof -/

/-- v-subsets of X\U together with members A ∈ S -/
noncomputable def pairSet (X : Finset α) (S : Finset (Finset α)) (U : Finset α) (v : ℕ) :
    Finset (Finset α × Finset α) :=
  (cardSubsets (X \ U) v).product S

/-- s(A) := |χ(A,U)| -/
noncomputable def sVal (S : Finset (Finset α)) (U A : Finset α) : ℕ := (chi S U A).card

/-- t(A,V) := |χ(A,U∪V)| -/
noncomputable def tVal (S : Finset (Finset α)) (U V A : Finset α) : ℕ :=
  (chi S (U ∪ V) A).card

/-- φ(s,t) with the ambient ground size X.card -/
noncomputable def phiVal (r : ℝ) (k : ℕ) (X : Finset α) (v s t : ℕ) : ℝ :=
  phi r k X.card v s t

/-- case 1: for every t-subset C of χ(A,U), few candidates -/
def case1p (S : Finset (Finset α)) (X U V A : Finset α) (r : ℝ) (k v : ℕ) : Prop :=
  0 < tVal S U V A ∧
  ∀ C : Finset α, C ⊆ chi S U A → C.card = tVal S U V A →
    (((tau S U C (V ∪ chi S U A) (sVal S U A)).card : ℝ) ≤
      phiVal r k X v (sVal S U A) (tVal S U V A))

/-- case 2: some t-subset of χ(A,U) admits many candidates -/
def case2p (S : Finset (Finset α)) (X U V A : Finset α) (r : ℝ) (k v : ℕ) : Prop :=
  ∃ C : Finset α, C ⊆ chi S U A ∧ C.card = tVal S U V A ∧
    phiVal r k X v (sVal S U A) (tVal S U V A) <
      ((tau S U C (V ∪ chi S U A) (sVal S U A)).card : ℝ)

/-- case-1 pairs in the (s,t)-fiber -/
noncomputable def case1Fiber (X : Finset α) (S : Finset (Finset α)) (U : Finset α) (v : ℕ) (r : ℝ) (k s t : ℕ) :
    Finset (Finset α × Finset α) := by
  classical
  exact (pairSet X S U v).filter
    (fun (V,A) => sVal S U A = s ∧ tVal S U V A = t ∧ case1p S X U V A r k v)

/-- case-2 pairs in the (s,t)-fiber -/
noncomputable def case2Fiber (X : Finset α) (S : Finset (Finset α)) (U : Finset α) (v : ℕ) (r : ℝ) (k s t : ℕ) :
    Finset (Finset α × Finset α) := by
  classical
  exact (pairSet X S U v).filter
    (fun (V,A) => sVal S U A = s ∧ tVal S U V A = t ∧ case2p S X U V A r k v)

/-- pairs with t=0 (V kills the remainder) -/
noncomputable def zeroFiber (X : Finset α) (S : Finset (Finset α)) (U : Finset α) (v : ℕ) : Finset (Finset α × Finset α) := by
  classical
  exact (pairSet X S U v).filter (fun (V,A) => tVal S U V A = 0)

/-- subsets of X\U of sizes v, v+1, …, v+s -/
def bigB0 (X U : Finset α) (v s : ℕ) : Finset (Finset α) := by
  classical
  exact (Finset.range (s + 1)).biUnion (fun j : ℕ => cardSubsets (X \ U) (v + j))

/-- possible B0-values for a fixed s: subsets of X\U of size in [v, v+s];
    their number is ≤ Σ_j C(N, v+j) -/
lemma card_bigB0_le (X U : Finset α) (v s : ℕ) :
    (bigB0 X U v s).card ≤ ∑ j ∈ Finset.range (s + 1), (cardSubsets (X \ U) (v + j)).card := by
  classical
  calc
    (bigB0 X U v s).card ≤ ∑ j ∈ Finset.range (s + 1), (cardSubsets (X \ U) (v + j)).card := by
      simpa [bigB0] using Finset.card_biUnion_le

/-- n := X.card; N := |X\U|; derived bounds -/
lemma N_bound_8 {X U : Finset α} (hU : U ⊆ X) (h8u : 8 * U.card ≤ X.card) :
    (X.card : ℝ) / 8 ≤ ((X \ U).card : ℝ) := by
  have hN : (X \ U).card = X.card - U.card := Finset.card_sdiff_of_subset hU
  have hu_le_n : U.card ≤ X.card := by omega
  have hcast : ((X.card - U.card : ℕ) : ℝ) = (X.card : ℝ) - (U.card : ℝ) := by
    exact Nat.cast_sub hu_le_n
  rw [hN, hcast]
  have huR : (U.card : ℝ) ≤ (X.card : ℝ) / 8 := by
    have h8 := (by exact_mod_cast h8u : (8 : ℝ) * (U.card : ℝ) ≤ (X.card : ℝ))
    linarith
  have hn0 : 0 ≤ (X.card : ℝ) := by positivity
  nlinarith

lemma N_bound_2v {X U : Finset α} {v : ℕ} (hU : U ⊆ X)
    (huv2 : U.card + 2 * v ≤ X.card) : 2 * v ≤ (X \ U).card := by
  have hN : (X \ U).card = X.card - U.card := Finset.card_sdiff_of_subset hU
  rw [hN]
  omega

/-- v ≤ |X\U| -/
lemma N_bound_v {X U : Finset α} {v : ℕ} (hU : U ⊆ X)
    (huv : U.card + v ≤ X.card) : v ≤ (X \ U).card := by
  have hN : (X \ U).card = X.card - U.card := Finset.card_sdiff_of_subset hU
  rw [hN]
  omega

/-- X.card > 0 (since 6k ≤ n, k ≥ 2) -/
lemma X_card_pos {X : Finset α} {k : ℕ} (hk : 2 ≤ k) (hn6 : 6 * k ≤ X.card) :
    0 < X.card := by omega

/-- |X\U| > 0 -/
lemma N_pos {X U : Finset α} {v : ℕ} (hv : 0 < v) (hle : v ≤ (X \ U).card) :
    0 < (X \ U).card := by omega

/-- X\U ⊆ X -/
lemma sdiff_subset (X U : Finset α) : X \ U ⊆ X := Finset.sdiff_subset

/-- (X\U).card ≤ X.card -/
lemma sdiff_card_le (X U : Finset α) : (X \ U).card ≤ X.card :=
  Finset.card_le_card Finset.sdiff_subset


/-! ## Real estimates (log / exp / geometric bounds) -/

lemma log2_ge_69 : (69 : ℝ) / 100 ≤ Real.log 2 := by
  have h : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith

lemma log2_le_7 : Real.log 2 ≤ (7 : ℝ) / 10 := by
  have h : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  norm_num at h
  linarith

lemma exp26_le_two39 : Real.exp 26 ≤ (2 : ℝ) ^ 39 := by
  have h26 : (26 : ℝ) ≤ Real.log ((2 : ℝ) ^ 39) := by
    rw [Real.log_pow]
    have h2 := log2_ge_69
    calc (26 : ℝ) ≤ (39 : ℝ) * (69 / 100 : ℝ) := by norm_num
      _ ≤ (39 : ℝ) * Real.log 2 := by nlinarith [h2]
  calc
    Real.exp 26 ≤ Real.exp (Real.log ((2 : ℝ) ^ 39)) := Real.exp_le_exp.mpr h26
    _ = (2 : ℝ) ^ 39 := Real.exp_log (by positivity)

lemma exp26_over_kap : Real.exp 26 * ((2 : ℝ) ^ 40)⁻¹ ≤ (1 / 2 : ℝ) := by
  have hz : (2 : ℝ) ^ 40 ≠ 0 := by positivity
  calc
    Real.exp 26 * ((2 : ℝ) ^ 40)⁻¹ ≤ (2 : ℝ) ^ 39 * ((2 : ℝ) ^ 40)⁻¹ := by
      exact mul_le_mul_of_nonneg_right exp26_le_two39 (by positivity)
    _ = (1 / 2 : ℝ) := by field_simp [hz]

lemma exp20_ge_two20 : (2 : ℝ) ^ 20 ≤ Real.exp 20 := by
  have hlog : Real.log ((2 : ℝ) ^ 20) ≤ 20 := by
    rw [Real.log_pow]
    have hl := log2_le_7
    calc
      ((20 : ℕ) : ℝ) * Real.log 2 ≤ ((20 : ℕ) : ℝ) * (7 / 10 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hl (by norm_num)
      _ = (14 : ℝ) := by norm_num
      _ ≤ (20 : ℝ) := by norm_num
  calc
    (2 : ℝ) ^ 20 = Real.exp (Real.log ((2 : ℝ) ^ 20)) := (Real.exp_log (by positivity : 0 < (2 : ℝ) ^ 20)).symm
    _ ≤ Real.exp 20 := Real.exp_le_exp.mpr hlog

lemma exp_neg20_two18_le_quarter : Real.exp (-20) * (2 : ℝ) ^ 18 ≤ (1 / 4 : ℝ) := by
  have hm : (2 : ℝ) ^ 20 = (2 : ℝ) ^ 18 * (2 : ℝ) ^ 2 := by
    rw [show 20 = 18 + 2 by norm_num, pow_add]
  have h4 : (2 : ℝ) ^ 2 = 4 := by norm_num
  have hfin : (2 : ℝ) ^ 20 / 4 = (2 : ℝ) ^ 18 := by
    rw [hm, h4]
    field_simp
  calc
    Real.exp (-20) * (2 : ℝ) ^ 18 = (2 : ℝ) ^ 18 / Real.exp 20 := by
      rw [Real.exp_neg]
      field_simp
    _ ≤ (1 / 4 : ℝ) := by
      have hpos : 0 < Real.exp 20 := by positivity
      rw [div_le_iff₀ hpos]
      rw [hfin.symm]
      rw [show (1 / 4 : ℝ) * Real.exp 20 = Real.exp 20 / 4 by ring]
      exact div_le_div_of_nonneg_right exp20_ge_two20 (by norm_num : 0 ≤ (4 : ℝ))

lemma exp26_n_over_rv_half {X : Finset α} {v : ℕ} {r : ℝ} (hr1 : 1 ≤ r) (hv : 0 < v)
    (hkap : (kap * (X.card : ℝ)) / r ≤ (v : ℝ)) (hXpos : 0 < X.card) :
    Real.exp 26 * (X.card : ℝ) / ((v : ℝ) * r) ≤ (1 / 2 : ℝ) := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr1
  have hn0 : 0 < (X.card : ℝ) := by exact_mod_cast hXpos
  have hmain : (kap : ℝ) ≤ ((v : ℝ) * r) / (X.card : ℝ) := by
    have h1 : (kap : ℝ) * (X.card : ℝ) ≤ r * (v : ℝ) := by
      have h1' : (kap * (X.card : ℝ)) / r ≤ (v : ℝ) := hkap
      rw [div_le_iff₀ hr0] at h1'
      nlinarith
    rw [le_div_iff₀ hn0]
    nlinarith
  have hkap0 : 0 < (kap : ℝ) := by unfold kap; positivity
  have hrvpos : 0 < ((v : ℝ) * r) / (X.card : ℝ) := by positivity
  have hle : (((v : ℝ) * r) / (X.card : ℝ))⁻¹ ≤ (kap : ℝ)⁻¹ :=
    (inv_le_inv₀ hrvpos hkap0).mpr hmain
  have hnrv : (X.card : ℝ) / ((v : ℝ) * r) ≤ (kap : ℝ)⁻¹ := by
    have heq : (((v : ℝ) * r) / (X.card : ℝ))⁻¹ = (X.card : ℝ) / ((v : ℝ) * r) := by
      field_simp
    simpa [heq] using hle
  have hkapinv : (kap : ℝ)⁻¹ = ((2 : ℝ) ^ 40)⁻¹ := by
    unfold kap
    ring
  calc
    Real.exp 26 * (X.card : ℝ) / ((v : ℝ) * r) = Real.exp 26 * ((X.card : ℝ) / ((v : ℝ) * r)) := by ring
    _ ≤ Real.exp 26 * (kap : ℝ)⁻¹ := by
      exact mul_le_mul_of_nonneg_left hnrv (by positivity)
    _ = Real.exp 26 * (((2 : ℝ) ^ 40)⁻¹) := by rw [hkapinv]
    _ ≤ (1 / 2 : ℝ) := exp26_over_kap

lemma exp6_le_two14 : Real.exp 6 ≤ (2 : ℝ) ^ 14 := by
  have h6 : (6 : ℝ) ≤ Real.log ((2 : ℝ) ^ 14) := by
    rw [Real.log_pow]
    have h2 := log2_ge_69
    calc (6 : ℝ) ≤ (14 : ℝ) * (69 / 100 : ℝ) := by norm_num
      _ ≤ (14 : ℝ) * Real.log 2 := by nlinarith [h2]
  calc
    Real.exp 6 ≤ Real.exp (Real.log ((2 : ℝ) ^ 14)) := Real.exp_le_exp.mpr h6
    _ = (2 : ℝ) ^ 14 := Real.exp_log (by positivity)

lemma exp_neg20_le_one : Real.exp (-20) ≤ 1 := by
  calc
    Real.exp (-20) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by norm_num : (-20 : ℝ) ≤ 0)
    _ = 1 := Real.exp_zero

lemma four_plus_exp26_exp_neg20_le : (4 + Real.exp 26) * Real.exp (-20) ≤ (2 : ℝ) ^ 15 := by
  have h25 : (2 : ℝ) ^ 25 ≤ Real.exp 20 := by
    have hlog : Real.log ((2 : ℝ) ^ 25) ≤ 20 := by
      rw [Real.log_pow]
      have hl := log2_le_7
      calc
        ((25 : ℕ) : ℝ) * Real.log 2 ≤ ((25 : ℕ) : ℝ) * (7 / 10 : ℝ) := by
          exact mul_le_mul_of_nonneg_left hl (by norm_num)
        _ = (175 / 10 : ℝ) := by norm_num
        _ ≤ (20 : ℝ) := by norm_num
    calc
      (2 : ℝ) ^ 25 = Real.exp (Real.log ((2 : ℝ) ^ 25)) := (Real.exp_log (by positivity : 0 < (2 : ℝ) ^ 25)).symm
      _ ≤ Real.exp 20 := Real.exp_le_exp.mpr hlog
  have hE : Real.exp (-20) ≤ ((2 : ℝ) ^ 25)⁻¹ := by
    have hpos1 : 0 < Real.exp 20 := by positivity
    have hpos2 : 0 < (2 : ℝ) ^ 25 := by positivity
    calc
      Real.exp (-20) = (Real.exp 20)⁻¹ := by rw [Real.exp_neg]
      _ ≤ ((2 : ℝ) ^ 25)⁻¹ := by
        exact (inv_le_inv₀ hpos1 hpos2).mpr h25
  have h1 : Real.exp 26 * Real.exp (-20) ≤ (2 : ℝ) ^ 14 := by
    have hz : (2 : ℝ) ^ 25 ≠ 0 := by positivity
    calc
      Real.exp 26 * Real.exp (-20) ≤ (2 : ℝ) ^ 39 * Real.exp (-20) := by
        exact mul_le_mul_of_nonneg_right exp26_le_two39 (by positivity)
      _ ≤ (2 : ℝ) ^ 39 * ((2 : ℝ) ^ 25)⁻¹ := by
        exact mul_le_mul_of_nonneg_left hE (by positivity)
      _ = (2 : ℝ) ^ 14 := by
        have hm : (2 : ℝ) ^ 39 = (2 : ℝ) ^ 14 * (2 : ℝ) ^ 25 := by
          rw [show 39 = 14 + 25 by norm_num, pow_add]
        rw [hm]
        field_simp [hz]
  have h4 : (4 : ℝ) * Real.exp (-20) ≤ (2 : ℝ) ^ 14 := by
    have h14 : (4 : ℝ) ≤ (2 : ℝ) ^ 14 := by norm_num
    calc
      (4 : ℝ) * Real.exp (-20) ≤ (4 : ℝ) * 1 := by
        exact mul_le_mul_of_nonneg_left exp_neg20_le_one (by norm_num)
      _ = 4 := by ring
      _ ≤ (2 : ℝ) ^ 14 := h14
  calc
    (4 + Real.exp 26) * Real.exp (-20) = 4 * Real.exp (-20) + Real.exp 26 * Real.exp (-20) := by ring
    _ ≤ (2 : ℝ) ^ 14 + (2 : ℝ) ^ 14 := by exact add_le_add h4 h1
    _ = (2 : ℝ) ^ 15 := by
      have : (2 : ℝ) ^ 14 + (2 : ℝ) ^ 14 = 2 * (2 : ℝ) ^ 14 := by ring
      rw [this, pow_succ]
      norm_num

lemma x2_ratio_le_half {F : ℝ} (hF : F ≤ 4) (hF0 : 0 ≤ F) :
    (F + Real.exp 26) * Real.exp (-20) / (2 : ℝ) ^ 16 ≤ (1 / 2 : ℝ) := by
  have hmain : (4 + Real.exp 26) * Real.exp (-20) ≤ (2 : ℝ) ^ 15 := four_plus_exp26_exp_neg20_le
  have hle : (F + Real.exp 26) * Real.exp (-20) ≤ (2 : ℝ) ^ 15 := by
    have hpos : 0 ≤ Real.exp (-20) := by positivity
    have h2 : (F + Real.exp 26) ≤ (4 + Real.exp 26) := by
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hF (Real.exp 26)
    exact le_trans (mul_le_mul_of_nonneg_right h2 hpos) hmain
  have hz : (2 : ℝ) ^ 16 ≠ 0 := by positivity
  calc
    (F + Real.exp 26) * Real.exp (-20) / (2 : ℝ) ^ 16 ≤ (2 : ℝ) ^ 15 / (2 : ℝ) ^ 16 := by
      exact div_le_div_of_nonneg_right hle (by positivity)
    _ = (1 / 2 : ℝ) := by
      rw [show (2 : ℝ) ^ 16 = (2 : ℝ) ^ 15 * (2 : ℝ) by
        rw [show 16 = 15 + 1 by norm_num, pow_succ]]
      field_simp



/-! ## small summation bounds used by the fixed-U assembly -/

/-- for s ≥ 1, s+1 ≤ 2^s -/
lemma succ_le_two_pow {s : ℕ} (hs : 1 ≤ s) : s + 1 ≤ 2 ^ s := by
  induction' s with s ih
  · omega
  · by_cases hs0 : s = 0
    · subst s
      norm_num
    · have h1 : 1 ≤ s := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hs0)
      have ih' : s + 1 ≤ 2 ^ s := ih h1
      have h2s : 2 ^ (s + 1) = 2 * 2 ^ s := by
        rw [pow_succ]
        ring
      calc
        (s + 1) + 1 ≤ 2 * (s + 1) := by omega
        _ ≤ 2 * (2 ^ s) := by
          exact Nat.mul_le_mul_left 2 ih'
        _ = 2 ^ (s + 1) := h2s.symm

lemma sum_half_Icc (k : ℕ) : (∑ t ∈ Finset.Icc 1 k, (1 / 2 : ℝ) ^ t) = 1 - (1 / 2 : ℝ) ^ k := by
  classical
  induction k with
  | zero => simp
  | succ k ih =>
      have hsum := Finset.sum_Icc_succ_top (a := 1) (b := k) (by omega : 1 ≤ k + 1)
        (fun t : ℕ => (1 / 2 : ℝ) ^ t)
      rw [hsum, ih]
      have hp : (1 / 2 : ℝ) ^ (k + 1) = (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ k := by
        rw [pow_succ]
        ring
      rw [hp]
      ring

lemma sum_half_Icc_le_one (k : ℕ) : (∑ s ∈ Finset.Icc 1 k, (1 / 2 : ℝ) ^ s) ≤ 1 := by
  rw [sum_half_Icc]
  have hpos : 0 ≤ (1 / 2 : ℝ) ^ k := by positivity
  nlinarith

lemma sum_q_Icc_le_one {s : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) :
    (∑ t ∈ Finset.Icc 1 s, q ^ t) ≤ 1 := by
  calc
    (∑ t ∈ Finset.Icc 1 s, q ^ t) ≤ (∑ t ∈ Finset.Icc 1 s, (1 / 2 : ℝ) ^ t) := by
          apply Finset.sum_le_sum
          intro t ht
          exact pow_le_pow_left₀ hq0 hq t
    _ ≤ 1 := sum_half_Icc_le_one s

/-- C(N, v+j) ≤ C(N,v)·(N/v)^j with real N/v -/
lemma choose_add_le_real {N v j : ℕ} (hv : 0 < v) (hvN : v ≤ N) :
    ((N.choose (v + j) : ℕ) : ℝ) ≤ (N.choose v : ℝ) * (((N : ℝ) / (v : ℝ)) ^ j) := by
  by_cases hj : v + j ≤ N
  · have hnat := CountLemmas.choose_ratio_le (N := N) (v := v) (j := j) hv (by omega)
    have hfloor : (((N / v : ℕ) : ℝ)) ≤ (N : ℝ) / (v : ℝ) := by
      rw [le_div_iff₀ (by exact_mod_cast hv : 0 < (v : ℝ))]
      have hd : ((((N / v) * v : ℕ) : ℝ) ≤ (N : ℝ)) := by
        exact_mod_cast (Nat.div_mul_le_self N v)
      simpa [Nat.cast_mul] using hd
    have hpowmono : ((((N / v : ℕ) : ℝ)) ^ j) ≤ ((N : ℝ) / (v : ℝ)) ^ j := by
      exact pow_le_pow_left₀ (by positivity) hfloor j
    calc
      ((N.choose (v + j) : ℕ) : ℝ) ≤ ((N.choose v * (N / v) ^ j : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = (N.choose v : ℝ) * ((((N / v : ℕ) : ℝ)) ^ j) := by norm_num
      _ ≤ (N.choose v : ℝ) * (((N : ℝ) / (v : ℝ)) ^ j) := by
        exact mul_le_mul_of_nonneg_left hpowmono (by positivity)
  · have hzero : N.choose (v + j) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have hpos : 0 ≤ (N.choose v : ℝ) * (((N : ℝ) / (v : ℝ)) ^ j) := by positivity
    rw [hzero]
    simpa using hpos

/-- |bigB0(v,s)| ≤ (s+1)·C(N,v)·(N/v)^s (real, N := |X\U|) -/
lemma bigB0_real_le {X U : Finset α} {v s : ℕ} (hv : 0 < v) (hvN : v ≤ (X \ U).card) :
    ((bigB0 X U v s).card : ℝ) ≤
      ((s + 1 : ℕ) : ℝ) * ((X \ U).card.choose v : ℝ) *
        (((X \ U).card : ℝ) / (v : ℝ)) ^ s := by
  have hsum := card_bigB0_le X U v s
  have hle : ∀ j ∈ Finset.range (s + 1),
      ((cardSubsets (X \ U) (v + j)).card : ℝ) ≤
        ((X \ U).card.choose v : ℝ) * (((X \ U).card : ℝ) / (v : ℝ)) ^ s := by
    intro j hj
    have hjv : v ≤ (X \ U).card := hvN
    have hratio : j ≤ s := by
      have : j < s + 1 := Finset.mem_range.mp hj
      omega
    have h1 := choose_add_le_real (N := (X \ U).card) (v := v) (j := j) hv hjv
    -- C(N, v+j) ≤ C(N,v)·(N/v)^j ≤ C(N,v)·(N/v)^s
    have hpow : (((X \ U).card : ℝ) / (v : ℝ)) ^ j ≤ (((X \ U).card : ℝ) / (v : ℝ)) ^ s := by
      have hNv1 : (1 : ℝ) ≤ ((X \ U).card : ℝ) / (v : ℝ) := by
        have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
        have hcast : (v : ℝ) ≤ ((X \ U).card : ℝ) := by exact_mod_cast hjv
        rw [le_div_iff₀ hvR]
        nlinarith
      have hNv0 : 0 ≤ ((X \ U).card : ℝ) / (v : ℝ) := by positivity
      exact pow_le_pow_right₀ hNv1 hratio
    rw [card_cardSubsets]
    have h2 := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ ((X \ U).card.choose v : ℝ))
    -- exact chain: C(N,v+j) ≤ C(N,v)(N/v)^j ≤ C(N,v)(N/v)^s
    calc
      ((X \ U).card.choose (v + j) : ℝ) ≤ ((X \ U).card.choose v : ℝ) * (((X \ U).card : ℝ) / (v : ℝ)) ^ j := by
        simpa [Nat.add_comm] using h1
      _ ≤ ((X \ U).card.choose v : ℝ) * (((X \ U).card : ℝ) / (v : ℝ)) ^ s := by
        exact h2
  calc
    ((bigB0 X U v s).card : ℝ) ≤ ∑ j ∈ Finset.range (s + 1), ((cardSubsets (X \ U) (v + j)).card : ℝ) := by
        have h2 : (((∑ j ∈ Finset.range (s + 1), (cardSubsets (X \ U) (v + j)).card : ℕ) : ℝ)) =
            ∑ j ∈ Finset.range (s + 1), (((cardSubsets (X \ U) (v + j)).card : ℕ) : ℝ) := by simp
        exact (le_trans (by exact_mod_cast hsum) (le_of_eq h2))
    _ ≤ ∑ j ∈ Finset.range (s + 1), (((X \ U).card.choose v : ℝ) * (((X \ U).card : ℝ) / (v : ℝ)) ^ s) := by
        exact Finset.sum_le_sum hle
    _ = ((s + 1 : ℕ) : ℝ) * (((X \ U).card.choose v : ℝ) * (((X \ U).card : ℝ) / (v : ℝ)) ^ s) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        simp
    _ ≤ ((s + 1 : ℕ) : ℝ) * ((X \ U).card.choose v : ℝ) * (((X \ U).card : ℝ) / (v : ℝ)) ^ s := by
        exact le_of_eq (by ring)



/-- (s+1)·(1/4)^s ≤ (1/2)^s for s ≥ 1 -/
lemma succ_fourth_pow_le {s : ℕ} (hs : 1 ≤ s) :
    ((s + 1 : ℕ) : ℝ) * (1 / 4 : ℝ) ^ s ≤ (1 / 2 : ℝ) ^ s := by
  have hsuc := succ_le_two_pow hs
  have h4 : (4 : ℝ) = (2 : ℝ) * (2 : ℝ) := by norm_num
  have hpow2 : (1 / 4 : ℝ) ^ s = (1 / 2 : ℝ) ^ s * (1 / 2 : ℝ) ^ s := by
    rw [show (1 / 4 : ℝ) = (1 / 2 : ℝ) * (1 / 2 : ℝ) by norm_num]
    rw [mul_pow]
  have hpos : 0 ≤ (1 / 2 : ℝ) ^ s := by positivity
  have hc : ((s + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ s := by exact_mod_cast hsuc
  calc
    ((s + 1 : ℕ) : ℝ) * (1 / 4 : ℝ) ^ s = ((s + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ s * (1 / 2 : ℝ) ^ s) := by rw [hpow2]
    _ ≤ (2 : ℝ) ^ s * ((1 / 2 : ℝ) ^ s * (1 / 2 : ℝ) ^ s) := by
        exact mul_le_mul_of_nonneg_right hc (by positivity)
    _ = (1 / 2 : ℝ) ^ s := by
        have hprod : (2 : ℝ) ^ s * (1 / 2 : ℝ) ^ s = 1 := by
          rw [← mul_pow]
          norm_num
        rw [← mul_assoc, hprod]
        ring

/-- Σ_{s∈Icc 1 k} (s+1)·(1/4)^s ≤ 1 -/
lemma sum_succ_fourth_le_one (k : ℕ) : (∑ s ∈ Finset.Icc 1 k, ((s + 1 : ℕ) : ℝ) * (1 / 4 : ℝ) ^ s) ≤ 1 := by
  calc
    (∑ s ∈ Finset.Icc 1 k, ((s + 1 : ℕ) : ℝ) * (1 / 4 : ℝ) ^ s)
        ≤ (∑ s ∈ Finset.Icc 1 k, (1 / 2 : ℝ) ^ s) := by
          apply Finset.sum_le_sum
          intro s hs
          have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
          exact succ_fourth_pow_le hs1
    _ ≤ 1 := sum_half_Icc_le_one k

/-- index pairs (s,t) with 1 ≤ s ≤ k, 1 ≤ t ≤ s -/
def idxSet (k : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 k) ×ˢ (Finset.Icc 1 k)).filter (fun (s,t) => t ≤ s)

lemma mem_idxSet_iff {k s t : ℕ} : (s, t) ∈ idxSet k ↔ 1 ≤ s ∧ s ≤ k ∧ 1 ≤ t ∧ t ≤ s := by
  classical
  rw [idxSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  simp
  omega

/-- exp(26·t − 20·s) for a fibre index (s,t) -/
noncomputable def wfib (j : ℕ × ℕ) : ℝ :=
  Real.exp ((26 : ℝ) * (j.2 : ℝ) - (20 : ℝ) * (j.1 : ℝ))


/-- exp(b·t − a·s) with a = 20, b = 26 -/
noncomputable def wgt (S : Finset (Finset α)) (U V A : Finset α) : ℝ :=
  Real.exp ((26 : ℝ) * (tVal S U V A : ℝ) - (20 : ℝ) * (sVal S U A : ℝ))

/-- weights depend only on the fibre: wgt(p) = wfib (sVal A, tVal V A) -/
lemma wgt_eq_wfib (S : Finset (Finset α)) (U V A : Finset α) :
    wgt S U V A = wfib (sVal S U A, tVal S U V A) := by
  simp [wgt, wfib]



/-- 7·n ≤ 8·|X\U| from 8u ≤ n -/
lemma N_ge_7n8 {X U : Finset α} (hU : U ⊆ X) (h8u : 8 * U.card ≤ X.card) :
    (7 * X.card : ℕ) ≤ 8 * (X \ U).card := by
  have hN : (X \ U).card = X.card - U.card := Finset.card_sdiff_of_subset hU
  rw [hN]
  omega

/-- (n/N)·(1 + N/(vr)) ≤ 4 in the fixed-U environment -/
lemma F_le_four {X U : Finset α} {v : ℕ} {r : ℝ} (hU : U ⊆ X) (h8u : 8 * U.card ≤ X.card)
    (hr1 : 1 ≤ r) (hv : 0 < v) (hn : 0 < X.card)
    (huv : U.card + v ≤ X.card)
    (hkap : (kap * (X.card : ℝ)) / r ≤ (v : ℝ)) :
    ((X.card : ℝ) / ((X \ U).card : ℝ)) *
        (1 + ((X \ U).card : ℝ) / ((v : ℝ) * r)) ≤ 4 := by
  have hNpos : 0 < (X \ U).card := by
    have hvn : v ≤ (X \ U).card := N_bound_v (X := X) (U := U) (v := v) hU huv
    omega
  have hN0 : 0 < ((X \ U).card : ℝ) := by exact_mod_cast hNpos
  have h7 : (7 : ℝ) * (X.card : ℝ) ≤ 8 * ((X \ U).card : ℝ) := by
    have hnat : (7 * X.card : ℕ) ≤ 8 * (X \ U).card := N_ge_7n8 hU h8u
    exact_mod_cast hnat
  have hnN : (X.card : ℝ) / ((X \ U).card : ℝ) ≤ (8 : ℝ) / 7 := by
    rw [div_le_iff₀ hN0]
    nlinarith
  have hmain : (kap : ℝ) ≤ ((v : ℝ) * r) / (X.card : ℝ) := by
    have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr1
    have h1 : (kap : ℝ) * (X.card : ℝ) ≤ r * (v : ℝ) := by
      have h1' : (kap * (X.card : ℝ)) / r ≤ (v : ℝ) := hkap
      rw [div_le_iff₀ hr0] at h1'
      nlinarith
    rw [le_div_iff₀ (by positivity : 0 < (X.card : ℝ))]
    nlinarith
  have hNr : ((X \ U).card : ℝ) / ((v : ℝ) * r) ≤ 1 := by
    have h0 : 0 < ((v : ℝ) * r) := by positivity
    rw [div_le_iff₀ h0]
    -- (X\U).card ≤ vr : from vr ≥ kap·n ≥ n ≥ N
    have hkap1 : (1 : ℝ) ≤ (kap : ℝ) := by unfold kap; norm_num
    have hNle : ((X \ U).card : ℝ) ≤ (X.card : ℝ) := by
      exact_mod_cast (sdiff_card_le X U)
    have hmain' : (kap : ℝ) ≤ ((v : ℝ) * r) / (X.card : ℝ) := hmain
    have hcap : (1 : ℝ) ≤ ((v : ℝ) * r) / (X.card : ℝ) := le_trans hkap1 hmain'
    have hn0 : 0 < (X.card : ℝ) := by exact_mod_cast hn
    rw [le_div_iff₀ hn0] at hcap
    nlinarith
  have hprod : ((X.card : ℝ) / ((X \ U).card : ℝ)) * (1 + ((X \ U).card : ℝ) / ((v : ℝ) * r))
      ≤ (8 / 7 : ℝ) * 2 := by
    have hpos1 : 0 ≤ (X.card : ℝ) / ((X \ U).card : ℝ) := by positivity
    have hpos2 : 0 ≤ 1 + ((X \ U).card : ℝ) / ((v : ℝ) * r) := by positivity
    nlinarith
  nlinarith



/-! ## exp-Jensen and the final contraction -/

/-- exp(mean) ≤ mean of exp over a nonempty finite set -/
lemma exp_avg_le_sum_div {ι : Type*} [DecidableEq ι] (t : Finset ι) (x : ι → ℝ) (ht : 0 < t.card) :
    Real.exp ((∑ i ∈ t, x i) / (t.card : ℝ)) ≤ (∑ i ∈ t, Real.exp (x i)) / (t.card : ℝ) := by
  classical
  let n : ℝ := (t.card : ℝ)
  have hn0 : n ≠ 0 := by
    dsimp [n]
    exact_mod_cast (ne_of_gt ht)
  have hw0 : ∀ i ∈ t, (0 : ℝ) ≤ 1 / n := by
    intro i hi
    positivity
  have hw1 : (∑ i ∈ t, (1 / n : ℝ)) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    dsimp [n]
    field_simp
  have hc := ConvexOn.map_sum_le (s := Set.univ) (f := fun y : ℝ => Real.exp y) (t := t)
    (w := fun _ : ι => (1 / n : ℝ)) (p := fun i : ι => x i)
    convexOn_exp hw0 hw1 (by intro i hi; trivial)
  have hc' : Real.exp (∑ i ∈ t, (1 / n : ℝ) * x i) ≤ ∑ i ∈ t, (1 / n : ℝ) * Real.exp (x i) := by
    simpa [nsmul_eq_mul] using hc
  have hL : (∑ i ∈ t, (1 / n : ℝ) * x i) = (∑ i ∈ t, x i) / n := by
    rw [← Finset.mul_sum]
    field_simp [hn0]
  have hR : (∑ i ∈ t, (1 / n : ℝ) * Real.exp (x i)) = (∑ i ∈ t, Real.exp (x i)) / n := by
    rw [← Finset.mul_sum]
    field_simp [hn0]
  rw [hL, hR] at hc'
  dsimp [n] at hc' ⊢
  exact hc'

/-- ln 4 ≤ 1.4 -/
lemma log4_le_7_5 : Real.log 4 ≤ (7 : ℝ) / 5 := by
  have hl := log2_le_7
  calc
    Real.log 4 = Real.log ((2 : ℝ) ^ 2) := by norm_num
    _ = 2 * Real.log 2 := by
      rw [Real.log_pow]
      norm_num
    _ ≤ 2 * ((7 : ℝ) / 10) := by
      exact mul_le_mul_of_nonneg_left hl (by norm_num)
    _ = (7 : ℝ) / 5 := by ring

/-- (a/b)·efix + lnK/b ≤ (5/6)·efix for K ≤ 4 and efix ≥ 1 -/
lemma finish_factor {efix K : ℝ} (hK : 0 < K) (hK4 : K ≤ 4) (he : 1 ≤ efix) :
    (10 / 13 : ℝ) * efix + Real.log K / 26 ≤ (5 / 6 : ℝ) * efix := by
  have hlog : Real.log K ≤ (7 : ℝ) / 5 := le_trans (Real.log_le_log hK hK4) log4_le_7_5
  have hE : 0 ≤ efix := by linarith
  nlinarith


/-- sum of a constant over a Finset is card·c -/
lemma sum_const_real {β : Type*} (s : Finset β) (c : ℝ) :
    s.sum (fun _ : β => c) = (s.card : ℝ) * c := by
  rw [Finset.sum_const, nsmul_eq_mul]

end Submission.Sun
