import Mathlib
import Submission.SunBasic
import Submission.Deep2
import Submission.Binom
import Submission.Deep
import Submission.LevelFinal
import Submission.LogLemmas

set_option maxHeartbeats 800000

/-!
# `spread_disjoint`: r-spread families contain many disjoint sets

This is the last ingredient in the Finset chain (see `Upper.lean`). A k-uniform
`r`-spread family with `r ≥ Cmain·p·log(2k)` contains `p` pairwise-disjoint
members.  We obtain it by colouring the ground set with many colours and applying
`rao_petal` (which in turn relies on `fixed_U_step`) to each colour class.
-/
open Finset
open scoped BigOperators
open Real

namespace Submission.Sun

variable {α : Type*} [DecidableEq α]

/-- constant for the disjoint-sets lemma (moved here from Upper.lean so that this
module can be imported by Upper without an import cycle) -/
noncomputable def Cmain : ℝ := 2 ^ 70



variable {α : Type*} [DecidableEq α]

abbrev Colourings (X : Finset α) (ℓ : ℕ) := {x : α // x ∈ X} → Fin ℓ
abbrev FreeCols (ℓ : ℕ) (j : Fin ℓ) := {y : Fin ℓ // y ≠ j}
abbrev Comp (X W : Finset α) := {x : α // x ∈ X \ W}

def cls (X : Finset α) {ℓ : ℕ} (u : Colourings X ℓ) (j : Fin ℓ) : Finset α :=
  (X.attach.filter (fun x => u x = j)).image (fun x => x.1)

lemma cls_subset (X : Finset α) {ℓ : ℕ} (u : Colourings X ℓ) (j : Fin ℓ) :
    cls X u j ⊆ X := by
  intro x hx
  rw [cls, mem_image] at hx
  rcases hx with ⟨y, hy, rfl⟩
  exact y.2

lemma mem_cls {X : Finset α} {ℓ : ℕ} (u : Colourings X ℓ) (j : Fin ℓ) {x : α} (hx : x ∈ X) :
    x ∈ cls X u j ↔ u ⟨x, hx⟩ = j := by
  unfold cls
  rw [mem_image]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hyf := (Finset.mem_filter.mp hy).2
    have hxy : (⟨x, hx⟩ : {y : α // y ∈ X}) = y := Subtype.ext hyx.symm
    simpa [hxy] using hyf
  · intro h
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    simp [h]

/-- classes of different colours are disjoint -/
lemma disjoint_cls (X : Finset α) {ℓ : ℕ} (u : Colourings X ℓ) {j j' : Fin ℓ} (hjj : j ≠ j') :
    Disjoint (cls X u j) (cls X u j') := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  have hc : u ⟨x, (cls_subset X u j hx)⟩ = j := (mem_cls u j (hx := cls_subset X u j hx)).1 hx
  have hc' : u ⟨x, (cls_subset X u j' hx')⟩ = j' := (mem_cls u j' (hx := cls_subset X u j' hx')).1 hx'
  have h2 : u ⟨x, (cls_subset X u j' hx')⟩ = j := by
    calc
      u ⟨x, (cls_subset X u j' hx')⟩ = u ⟨x, (cls_subset X u j hx)⟩ := congrArg u (Subtype.ext rfl)
      _ = j := hc
  exact hjj (h2.symm.trans hc')

noncomputable def fromFree (X : Finset α) {ℓ : ℕ} (j : Fin ℓ) (W : Finset α)
    (d : Comp X W → FreeCols ℓ j) : Colourings X ℓ :=
  fun y => if h : y.1 ∈ W then j else (d ⟨y.1, Finset.mem_sdiff.mpr ⟨y.2, h⟩⟩).1

lemma cls_fromFree (X : Finset α) {ℓ : ℕ} (j : Fin ℓ) (W : Finset α) (hW : W ⊆ X)
    (d : Comp X W → FreeCols ℓ j) : cls X (fromFree X j W d) j = W := by
  apply Finset.ext
  intro x
  constructor
  · intro hx
    have hxX : x ∈ X := cls_subset X (fromFree X j W d) j hx
    have hc : fromFree X j W d ⟨x, hxX⟩ = j := (mem_cls (fromFree X j W d) j (hx := hxX)).1 hx
    by_contra hxW
    have hval : fromFree X j W d ⟨x, hxX⟩ = (d ⟨x, Finset.mem_sdiff.mpr ⟨hxX, hxW⟩⟩).1 := by
      simp [fromFree, hxW]
    rw [hval] at hc
    exact (d ⟨x, Finset.mem_sdiff.mpr ⟨hxX, hxW⟩⟩).2 hc
  · intro hx
    have hxX : x ∈ X := hW hx
    have hc : fromFree X j W d ⟨x, hxX⟩ = j := by
      simp [fromFree, hx]
    exact (mem_cls (fromFree X j W d) j (hx := hxX)).2 hc

noncomputable def toFree (X : Finset α) {ℓ : ℕ} (j : Fin ℓ) (W : Finset α) (hW : W ⊆ X)
    (u : Colourings X ℓ) (hu : cls X u j = W) : Comp X W → FreeCols ℓ j :=
  fun x => ⟨u ⟨x.1, (Finset.mem_sdiff.mp x.2).1⟩, by
    intro hc
    have hxcls : x.1 ∈ cls X u j := (mem_cls u j (hx := (Finset.mem_sdiff.mp x.2).1)).2 hc
    have hxW : x.1 ∈ W := by
      rw [hu] at hxcls
      exact hxcls
    exact (Finset.mem_sdiff.mp x.2).2 hxW⟩

lemma fromFree_toFree (X : Finset α) {ℓ : ℕ} (j : Fin ℓ) (W : Finset α) (hW : W ⊆ X)
    (u : Colourings X ℓ) (hu : cls X u j = W) :
    fromFree X j W (toFree X j W hW u hu) = u := by
  funext y
  by_cases hy : y.1 ∈ W
  · have hcls : y.1 ∈ cls X u j := by
      rw [hu]
      exact hy
    have hyj : u ⟨y.1, y.2⟩ = j := (mem_cls u j (hx := y.2)).1 hcls
    simp [fromFree, hy, hyj]
  · have hmem : y.1 ∈ X \ W := Finset.mem_sdiff.mpr ⟨y.2, hy⟩
    have htoFree : (toFree X j W hW u hu ⟨y.1, hmem⟩).1 = u y := by
      simp [toFree]
    simp [fromFree, hy, htoFree]

lemma toFree_fromFree (X : Finset α) {ℓ : ℕ} (j : Fin ℓ) (W : Finset α) (hW : W ⊆ X)
    (d : Comp X W → FreeCols ℓ j) :
    toFree X j W hW (fromFree X j W d) (cls_fromFree X j W hW d) = d := by
  funext x
  apply Subtype.ext
  have hxnotW : x.1 ∉ W := (Finset.mem_sdiff.mp x.2).2
  have hval : fromFree X j W d ⟨x.1, (Finset.mem_sdiff.mp x.2).1⟩ = (d x).1 := by
    simp [fromFree, hxnotW]
  simpa [toFree, hxnotW] using hval

noncomputable def colourEquiv (X : Finset α) {ℓ : ℕ} (j : Fin ℓ) (W : Finset α) (hW : W ⊆ X) :
    {u : Colourings X ℓ // cls X u j = W} ≃ (Comp X W → FreeCols ℓ j) where
  toFun u := toFree X j W hW u.1 u.2
  invFun d := ⟨fromFree X j W d, cls_fromFree X j W hW d⟩
  left_inv u := by
    apply Subtype.ext
    exact fromFree_toFree X j W hW u.1 u.2
  right_inv d := toFree_fromFree X j W hW d

/-- number of colourings whose `j`-class equals W -/
lemma fibre_card (X : Finset α) {ℓ : ℕ} (j : Fin ℓ) (W : Finset α) (hW : W ⊆ X) :
    Fintype.card {u : Colourings X ℓ // cls X u j = W} = (ℓ - 1) ^ (X.card - W.card) := by
  rw [Fintype.card_congr (colourEquiv X j W hW)]
  rw [Fintype.card_fun]
  have hfree : Fintype.card (FreeCols ℓ j) = ℓ - 1 := by
    have h2 : Fintype.card {y : Fin ℓ // y ≠ j} = Fintype.card (Fin ℓ) - Fintype.card {y : Fin ℓ // y = j} := by
      simpa [Ne] using (Fintype.card_subtype_compl (p := fun y : Fin ℓ => y = j))
    rw [h2]
    simp
  have hcomp : Fintype.card (Comp X W) = X.card - W.card := by
    rw [Fintype.card_coe, Finset.card_sdiff_of_subset hW]
  rw [hfree, hcomp]

/-- colouring space cardinality -/
lemma colouring_card (X : Finset α) (ℓ : ℕ) : Fintype.card (Colourings X ℓ) = ℓ ^ X.card := by
  rw [Fintype.card_fun]
  simp [Fintype.card_coe]

/-- weight of a subset (real): t^(n-|W|) -/
def weight (X : Finset α) (ℓ : ℕ) (W : Finset α) : ℝ :=
  ((ℓ - 1 : ℕ) : ℝ) ^ (X.card - W.card)

/-- summing a function of the class over all colourings = weighted sum over subsets -/
lemma sum_colour_by_class (X : Finset α) {ℓ : ℕ} (j : Fin ℓ) (f : Finset α → ℝ) :
    (∑ u : Colourings X ℓ, f (cls X u j)) = ∑ W ∈ X.powerset, weight X ℓ W * f W := by
  classical
  let C : Finset (Colourings X ℓ) := Finset.univ
  have hCsum : (∑ u : Colourings X ℓ, f (cls X u j)) = C.sum (fun u => f (cls X u j)) := by
    rfl
  have hfib := Finset.sum_fiberwise_of_maps_to (s := C) (t := X.powerset)
      (g := fun u : Colourings X ℓ => cls X u j)
      (f := fun u : Colourings X ℓ => f (cls X u j))
      (by intro u hu; exact Finset.mem_powerset.mpr (cls_subset X u j))
  rw [hCsum]
  rw [← hfib]
  apply Finset.sum_congr rfl
  intro W hW
  have hWsub : W ⊆ X := Finset.mem_powerset.mp hW
  calc
    (C.filter (fun u : Colourings X ℓ => cls X u j = W)).sum (fun u => f (cls X u j))
        = (C.filter (fun u : Colourings X ℓ => cls X u j = W)).sum (fun u => f W) := by
            refine Finset.sum_congr rfl ?_
            intro u hu
            have huW : cls X u j = W := (Finset.mem_filter.mp hu).2
            simp [huW]
    _ = (((C).filter (fun u : Colourings X ℓ => cls X u j = W)).card : ℝ) * f W := by
            rw [Finset.sum_const]
            simp [nsmul_eq_mul]
    _ = weight X ℓ W * f W := by
            have hfs : (C.filter (fun u : Colourings X ℓ => cls X u j = W)).card
                = (ℓ - 1) ^ (X.card - W.card) := by
                dsimp [C]
                rw [← fibre_card X j W hWsub]
                rw [Fintype.card_subtype]
            unfold weight
            rw [hfs]
            norm_num

/-- total measure = ℓ^n -/
lemma measure_all {X : Finset α} {ℓ : ℕ} (j : Fin ℓ) :
    (∑ W ∈ X.powerset, weight X ℓ W) = (ℓ : ℝ) ^ X.card := by
  have h1 := sum_colour_by_class X j (fun _ => (1 : ℝ))
  have hleft : (∑ u : Colourings X ℓ, (1 : ℝ)) = (Fintype.card (Colourings X ℓ) : ℝ) := by
    simp
  have hcard : (Fintype.card (Colourings X ℓ) : ℝ) = (ℓ : ℝ) ^ X.card := by
    rw [colouring_card]
    rw [Nat.cast_pow]
  calc
    (∑ W ∈ X.powerset, weight X ℓ W) = ∑ W ∈ X.powerset, weight X ℓ W * (1 : ℝ) := by simp
    _ = (∑ u : Colourings X ℓ, (1 : ℝ)) := by
        rw [h1]
    _ = (ℓ : ℝ) ^ X.card := by rw [hleft, hcard]

/-- (ℓ^n)·(1/ℓ)^m·(1-1/ℓ)^{n-m} = (ℓ-1)^{n-m}, for naturals n ≥ m -/
lemma pow_id {ℓ : ℝ} (hℓ : ℓ ≠ 0) {n m : ℕ} (hm : m ≤ n) :
    ℓ ^ n * (1 / ℓ) ^ m * (1 - 1 / ℓ) ^ (n - m) = (ℓ - 1) ^ (n - m) := by
  have hmain : ℓ ^ n * (1 / ℓ) ^ m = ℓ ^ (n - m) := by
    calc
      ℓ ^ n * (1 / ℓ) ^ m = ℓ ^ n * (ℓ⁻¹) ^ m := by rw [one_div]
      _ = ℓ ^ n * (ℓ ^ m)⁻¹ := by rw [inv_pow]
      _ = ℓ ^ (n - m) := by rw [← pow_sub₀ ℓ hℓ hm]
  calc
    ℓ ^ n * (1 / ℓ) ^ m * (1 - 1 / ℓ) ^ (n - m)
        = ℓ ^ (n - m) * (1 - 1 / ℓ) ^ (n - m) := by rw [hmain]
    _ = ℓ ^ (n - m) * ((ℓ - 1) / ℓ) ^ (n - m) := by
            congr 1
            field_simp [hℓ]
    _ = ℓ ^ (n - m) * ((ℓ - 1) ^ (n - m) / ℓ ^ (n - m)) := by rw [div_pow]
    _ = (ℓ - 1) ^ (n - m) := by
            field_simp [pow_ne_zero (n - m) hℓ]

/-- with a natural number base ℓ ≥ 1 -/
lemma pow_id_nat {ℓ : ℕ} (hℓ1 : 1 ≤ ℓ) {n m : ℕ} (hm : m ≤ n) :
    (ℓ : ℝ) ^ n * (1 / (ℓ : ℝ)) ^ m * (1 - 1 / (ℓ : ℝ)) ^ (n - m) = ((ℓ - 1 : ℕ) : ℝ) ^ (n - m) := by
  have hℓne : (ℓ : ℝ) ≠ 0 := by exact_mod_cast (by omega : ℓ ≠ 0)
  have hcast : (ℓ : ℝ) - 1 = ((ℓ - 1 : ℕ) : ℝ) := by
    have : ((ℓ - 1 : ℕ) : ℝ) + 1 = (ℓ : ℝ) := by exact_mod_cast (Nat.sub_add_cancel hℓ1)
    linarith
  rw [← hcast]
  exact pow_id hℓne hm

open Submission.Binom

/-- `binomLe N q M` regrouped by exact weight -/
lemma binomLe_eq_range_sum (N : ℕ) (q : ℝ) (M : ℕ) :
    binomLe N q M = ∑ m ∈ Finset.range (M + 1), (N.choose m : ℝ) * q ^ m * (1 - q) ^ (N - m) := by
  classical
  have hterm_sum : ∀ x : Words N,
      (if wt x ≤ M then q ^ (wt x) * (1 - q) ^ (N - wt x) else 0)
        = ∑ m ∈ Finset.range (M + 1), (if wt x = m then q ^ (wt x) * (1 - q) ^ (N - wt x) else 0) := by
    intro x
    by_cases hxM : wt x ≤ M
    · have hxr : wt x ∈ Finset.range (M + 1) := by simp [hxM]
      have hR : (∑ m ∈ Finset.range (M + 1), (if wt x = m then q ^ (wt x) * (1 - q) ^ (N - wt x) else 0))
          = q ^ (wt x) * (1 - q) ^ (N - wt x) := by
            rw [Finset.sum_ite_eq (Finset.range (M+1)) (wt x) (fun m => q ^ (wt x) * (1-q)^(N - wt x))]
            simp [hxr]
      simp [hxM, hR]
    · have hxr : wt x ∉ Finset.range (M + 1) := by simp [hxM]
      have hR : (∑ m ∈ Finset.range (M + 1), (if wt x = m then q ^ (wt x) * (1 - q) ^ (N - wt x) else 0)) = 0 := by
            rw [Finset.sum_ite_eq (Finset.range (M+1)) (wt x) (fun m => q ^ (wt x) * (1-q)^(N - wt x))]
            simp [hxr]
      simp [hxM, hR]
  calc
    binomLe N q M = ∑ x : Words N, ∑ m ∈ Finset.range (M + 1), (if wt x = m then q ^ (wt x) * (1 - q) ^ (N - wt x) else 0) := by
        unfold binomLe
        refine Finset.sum_congr rfl ?_
        intro x hx
        exact hterm_sum x
    _ = ∑ m ∈ Finset.range (M + 1), ∑ x : Words N, (if wt x = m then q ^ (wt x) * (1 - q) ^ (N - wt x) else 0) := by
        rw [Finset.sum_comm]
    _ = ∑ m ∈ Finset.range (M + 1), (N.choose m : ℝ) * q ^ m * (1 - q) ^ (N - m) := by
        apply Finset.sum_congr rfl
        intro m hm
        have hterm : (∑ x : Words N, (if wt x = m then q ^ (wt x) * (1 - q) ^ (N - wt x) else 0))
            = (∑ x : Words N, (if wt x = m then q ^ m * (1 - q) ^ (N - m) else 0)) := by
              apply Finset.sum_congr rfl
              intro x hx
              by_cases hxm : wt x = m
              · rw [hxm]
              · simp [hxm]
        rw [hterm]
        exact binomEq_eq_choose N m q

/-- lower tail as real weighted binomial sum at threshold -/
lemma binom_tail_choose {N : ℕ} {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    {M : ℕ} (hM : (M : ℝ) ≤ (N : ℝ) * q / 2) :
    (∑ m ∈ Finset.range (M + 1), (N.choose m : ℝ) * q ^ m * (1 - q) ^ (N - m)) ≤
      Real.exp (-((N : ℝ) * q) / 8) := by
  rw [← binomLe_eq_range_sum N q M]
  exact binomial_lower_tail hq0 hq1 hM

/-- split subset-sum over sizes ≤ M into a sum over sizes -/
lemma sum_card_le_eq_range (X : Finset α) (M : ℕ) (f : Finset α → ℝ) :
    (∑ W ∈ X.powerset with W.card ≤ M, f W) = ∑ m ∈ Finset.range (M + 1), ∑ W ∈ X.powersetCard m, f W := by
  classical
  have hdisj : (↑(Finset.range (M + 1)) : Set ℕ).PairwiseDisjoint (fun m => X.powersetCard m) := by
    intro m hm m' hm' hmm'
    exact Finset.pairwise_disjoint_powersetCard X hmm'
  have hsplit : (X.powerset.filter (fun W => W.card ≤ M)) =
      (Finset.range (M + 1)).biUnion (fun m => X.powersetCard m) := by
    ext W
    constructor
    · intro hW
      have hW1 := (Finset.mem_filter.mp hW).1
      have hW2 := (Finset.mem_filter.mp hW).2
      rw [Finset.mem_biUnion]
      refine ⟨W.card, Finset.mem_range.mpr (by omega), ?_⟩
      exact Finset.mem_powersetCard.mpr ⟨Finset.mem_powerset.mp hW1, rfl⟩
    · intro hW
      rw [Finset.mem_biUnion] at hW
      rcases hW with ⟨m, hm, hWm⟩
      have hW' := Finset.mem_powersetCard.mp hWm
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_powerset.mpr hW'.1, by
        have h2 := Finset.mem_range.mp hm
        omega⟩
  calc
    (∑ W ∈ X.powerset with W.card ≤ M, f W)
        = ∑ W ∈ (Finset.range (M + 1)).biUnion (fun m => X.powersetCard m), f W := by rw [hsplit]
    _ = ∑ m ∈ Finset.range (M + 1), ∑ W ∈ X.powersetCard m, f W := by
            rw [Finset.sum_biUnion hdisj]

lemma sum_weight_card (X : Finset α) (ℓ : ℕ) (m : ℕ) (hm : m ≤ X.card) :
    (∑ W ∈ X.powersetCard m, weight X ℓ W) =
      (X.card.choose m : ℝ) * ((ℓ - 1 : ℕ) : ℝ) ^ (X.card - m) := by
  have hWcard : ∀ W ∈ X.powersetCard m, X.card - W.card = X.card - m := by
    intro W hW
    have hc := (Finset.mem_powersetCard.mp hW).2
    rw [hc]
  calc
    (∑ W ∈ X.powersetCard m, weight X ℓ W)
        = ∑ W ∈ X.powersetCard m, ((ℓ - 1 : ℕ) : ℝ) ^ (X.card - m) := by
            refine Finset.sum_congr rfl ?_
            intro W hW
            unfold weight
            rw [hWcard W hW]
    _ = ((X.powersetCard m).card : ℝ) * ((ℓ - 1 : ℕ) : ℝ) ^ (X.card - m) := by
            rw [Finset.sum_const]
            simp [nsmul_eq_mul]
    _ = (X.card.choose m : ℝ) * ((ℓ - 1 : ℕ) : ℝ) ^ (X.card - m) := by
            rw [Finset.card_powersetCard]

/-- measure of subsets of size ≤ M is at most the exponential tail bound -/
lemma measure_small_le {X : Finset α} {ℓ M : ℕ} (hℓ1 : 1 ≤ ℓ)
    (hM : (M : ℝ) ≤ (X.card : ℝ) / (ℓ : ℝ) / 2) :
    (∑ W ∈ X.powerset with W.card ≤ M, weight X ℓ W) ≤
      ((ℓ : ℝ) ^ X.card) * Real.exp (-((X.card : ℝ) / (ℓ : ℝ)) / 8) := by
  classical
  have hq0 : (0 : ℝ) < 1 / (ℓ : ℝ) := by positivity
  have hq1 : (1 / (ℓ : ℝ)) ≤ 1 := by
    have hℓR : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ1
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (ℓ : ℝ))]
    simpa using hℓR
  have hM' : (M : ℝ) ≤ (X.card : ℝ) * (1 / (ℓ : ℝ)) / 2 := by
    calc
      (M : ℝ) ≤ (X.card : ℝ) / (ℓ : ℝ) / 2 := hM
      _ = (X.card : ℝ) * (1 / (ℓ : ℝ)) / 2 := by ring
  have hMleN : M ≤ X.card := by
    have hM2 : (M : ℝ) ≤ (X.card : ℝ) := by
      have h1 : (1 / (ℓ : ℝ)) ≤ 1 := hq1
      have hn0 : 0 ≤ (X.card : ℝ) := by positivity
      calc
        (M : ℝ) ≤ (X.card : ℝ) * (1 / (ℓ : ℝ)) / 2 := hM'
        _ ≤ (X.card : ℝ) := by nlinarith
    exact_mod_cast hM2
  calc
    (∑ W ∈ X.powerset with W.card ≤ M, weight X ℓ W)
        = ∑ m ∈ Finset.range (M + 1), ∑ W ∈ X.powersetCard m, weight X ℓ W := by
            exact sum_card_le_eq_range X M (fun W => weight X ℓ W)
    _ = ∑ m ∈ Finset.range (M + 1), (X.card.choose m : ℝ) * ((ℓ - 1 : ℕ) : ℝ) ^ (X.card - m) := by
            apply Finset.sum_congr rfl
            intro m hm
            exact sum_weight_card X ℓ m (by
              have hmM : m ≤ M := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
              exact le_trans hmM hMleN)
    _ = ((ℓ : ℝ) ^ X.card) * (∑ m ∈ Finset.range (M + 1), (X.card.choose m : ℝ) * (1 / (ℓ : ℝ)) ^ m * (1 - 1 / (ℓ : ℝ)) ^ (X.card - m)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro m hm
            have hmM : m ≤ M := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
            have hmn : m ≤ X.card := le_trans hmM hMleN
            have hp := pow_id_nat (ℓ := ℓ) hℓ1 hmn
            calc
              (X.card.choose m : ℝ) * ((ℓ - 1 : ℕ) : ℝ) ^ (X.card - m)
                  = (X.card.choose m : ℝ) * ((ℓ : ℝ) ^ X.card * (1 / (ℓ : ℝ)) ^ m * (1 - 1 / (ℓ : ℝ)) ^ (X.card - m)) := by
                      congr 1
                      rw [← hp]
              _ = ((ℓ : ℝ) ^ X.card) * ((X.card.choose m : ℝ) * (1 / (ℓ : ℝ)) ^ m * (1 - 1 / (ℓ : ℝ)) ^ (X.card - m)) := by ring
    _ ≤ ((ℓ : ℝ) ^ X.card) * Real.exp (-((X.card : ℝ) / (ℓ : ℝ)) / 8) := by
            have hpos : 0 ≤ (ℓ : ℝ) ^ X.card := by positivity
            have htail := binom_tail_choose (N := X.card) (q := 1 / (ℓ : ℝ)) hq0 hq1 (M := M) hM'
            have htail' : (∑ m ∈ Finset.range (M + 1), (X.card.choose m : ℝ) * (1 / (ℓ : ℝ)) ^ m * (1 - 1 / (ℓ : ℝ)) ^ (X.card - m)) ≤
                Real.exp (-((X.card : ℝ) / (ℓ : ℝ)) / 8) := by
              have hEq : -((X.card : ℝ) * (1 / (ℓ : ℝ))) / 8 = -((X.card : ℝ) / (ℓ : ℝ)) / 8 := by ring
              rw [← hEq]
              exact htail
            exact mul_le_mul_of_nonneg_left htail' hpos


/-- three-way split of the total measure -/
lemma measure_split {X : Finset α} {ℓ m0 : ℕ} (P : Finset α → Prop) [DecidablePred P] :
    (∑ W ∈ X.powerset, weight X ℓ W) =
      (∑ W ∈ X.powerset with W.card < m0, weight X ℓ W)
      + (∑ W ∈ X.powerset with m0 ≤ W.card ∧ ¬ P W, weight X ℓ W)
      + (∑ W ∈ X.powerset with m0 ≤ W.card ∧ P W, weight X ℓ W) := by
  classical
  have h1 : (∑ W ∈ X.powerset with W.card < m0, weight X ℓ W)
      = ∑ W ∈ X.powerset, (if W.card < m0 then weight X ℓ W else 0) := by
        rw [Finset.sum_filter]
  have h2 : (∑ W ∈ X.powerset with m0 ≤ W.card ∧ ¬ P W, weight X ℓ W)
      = ∑ W ∈ X.powerset, (if m0 ≤ W.card ∧ ¬ P W then weight X ℓ W else 0) := by
        rw [Finset.sum_filter]
  have h3 : (∑ W ∈ X.powerset with m0 ≤ W.card ∧ P W, weight X ℓ W)
      = ∑ W ∈ X.powerset, (if m0 ≤ W.card ∧ P W then weight X ℓ W else 0) := by
        rw [Finset.sum_filter]
  calc
    (∑ W ∈ X.powerset, weight X ℓ W)
        = ∑ W ∈ X.powerset, ((if W.card < m0 then weight X ℓ W else 0)
            + (if m0 ≤ W.card ∧ ¬ P W then weight X ℓ W else 0)
            + (if m0 ≤ W.card ∧ P W then weight X ℓ W else 0)) := by
            refine Finset.sum_congr rfl ?_
            intro W hW
            by_cases h : W.card < m0
            · have hnge : ¬ m0 ≤ W.card := by omega
              simp [h, hnge]
            · have hge : m0 ≤ W.card := le_of_not_gt h
              by_cases hP : P W
              · simp [h, hge, hP]
              · simp [h, hge, hP]
    _ = (∑ W ∈ X.powerset, (if W.card < m0 then weight X ℓ W else 0))
        + (∑ W ∈ X.powerset, (if m0 ≤ W.card ∧ ¬ P W then weight X ℓ W else 0))
        + (∑ W ∈ X.powerset, (if m0 ≤ W.card ∧ P W then weight X ℓ W else 0)) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = (∑ W ∈ X.powerset with W.card < m0, weight X ℓ W)
        + (∑ W ∈ X.powerset with m0 ≤ W.card ∧ ¬ P W, weight X ℓ W)
        + (∑ W ∈ X.powerset with m0 ≤ W.card ∧ P W, weight X ℓ W) := by
            rw [h1, h2, h3]

/-- a subset-sum with `m0 ≤ card` splits into per-size sums -/
lemma sum_filter_card_ge (X : Finset α) (m0 : ℕ) (Q : Finset α → Prop) [DecidablePred Q]
    (f : Finset α → ℝ) :
    (∑ W ∈ X.powerset with m0 ≤ W.card ∧ Q W, f W) =
      ∑ m ∈ (Finset.range (X.card + 1)).filter (fun m => m0 ≤ m),
        ∑ W ∈ X.powersetCard m with Q W, f W := by
  classical
  have hdisj : (↑((Finset.range (X.card + 1)).filter (fun m => m0 ≤ m)) : Set ℕ).PairwiseDisjoint
      (fun m => (X.powersetCard m).filter (fun W => Q W)) := by
    intro m hm m' hm' hmm'
    exact (Finset.pairwise_disjoint_powersetCard X hmm').mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hsplit : (X.powerset.filter (fun W => m0 ≤ W.card ∧ Q W)) =
      ((Finset.range (X.card + 1)).filter (fun m => m0 ≤ m)).biUnion
        (fun m => (X.powersetCard m).filter (fun W => Q W)) := by
    ext W
    constructor
    · intro hW
      have hW1 := (Finset.mem_filter.mp hW).1
      have hW2 := (Finset.mem_filter.mp hW).2
      have hWsub : W ⊆ X := Finset.mem_powerset.mp hW1
      rw [Finset.mem_biUnion]
      refine ⟨W.card, ?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_range.mpr (by
          have : W.card ≤ X.card := Finset.card_le_card hWsub
          omega), hW2.1⟩
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_powersetCard.mpr ⟨hWsub, rfl⟩, hW2.2⟩
    · intro hW
      rw [Finset.mem_biUnion] at hW
      rcases hW with ⟨m, hm, hWm⟩
      have hm' := Finset.mem_filter.mp hm
      have hWm1 := Finset.mem_filter.mp hWm
      have hW' := Finset.mem_powersetCard.mp hWm1.1
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_powerset.mpr hW'.1, ?_⟩
      have hm0 : m0 ≤ W.card := by rw [hW'.2]; exact hm'.2
      exact ⟨hm0, hWm1.2⟩
  calc
    (∑ W ∈ X.powerset with m0 ≤ W.card ∧ Q W, f W)
        = ∑ W ∈ ((Finset.range (X.card + 1)).filter (fun m => m0 ≤ m)).biUnion
            (fun m => (X.powersetCard m).filter (fun W => Q W)), f W := by
            change (∑ W ∈ (X.powerset.filter (fun W => m0 ≤ W.card ∧ Q W)), f W) = _
            rw [hsplit]
    _ = ∑ m ∈ (Finset.range (X.card + 1)).filter (fun m => m0 ≤ m),
        ∑ W ∈ (X.powersetCard m).filter (fun W => Q W), f W := by
            rw [Finset.sum_biUnion hdisj]
    _ = ∑ m ∈ (Finset.range (X.card + 1)).filter (fun m => m0 ≤ m),
        ∑ W ∈ X.powersetCard m with Q W, f W := by rfl

lemma measure_all_by_size {X : Finset α} {ℓ : ℕ} (j : Fin ℓ) :
    (∑ m ∈ Finset.range (X.card + 1), (X.card.choose m : ℝ) * ((ℓ - 1 : ℕ) : ℝ) ^ (X.card - m))
      = (ℓ : ℝ) ^ X.card := by
  classical
  have h1 : (∑ m ∈ Finset.range (X.card + 1), ∑ W ∈ X.powersetCard m, weight X ℓ W)
      = (∑ W ∈ X.powerset, weight X ℓ W) := by
    have hdisj : (↑(Finset.range (X.card + 1)) : Set ℕ).PairwiseDisjoint (fun m => X.powersetCard m) := by
      intro m hm m' hm' hmm'
      exact Finset.pairwise_disjoint_powersetCard X hmm'
    have hsplit : X.powerset = (Finset.range (X.card + 1)).biUnion (fun m => X.powersetCard m) := by
      ext W
      constructor
      · intro hW
        rw [Finset.mem_biUnion]
        refine ⟨W.card, ?_, ?_⟩
        · exact Finset.mem_range.mpr (by
            have : W.card ≤ X.card := Finset.card_le_card (Finset.mem_powerset.mp hW)
            omega)
        · exact Finset.mem_powersetCard.mpr ⟨Finset.mem_powerset.mp hW, rfl⟩
      · intro hW
        rw [Finset.mem_biUnion] at hW
        rcases hW with ⟨m, hm, hWm⟩
        exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hWm).1
    calc
      (∑ m ∈ Finset.range (X.card + 1), ∑ W ∈ X.powersetCard m, weight X ℓ W)
          = ∑ W ∈ (Finset.range (X.card + 1)).biUnion (fun m => X.powersetCard m), weight X ℓ W := by
              rw [Finset.sum_biUnion hdisj]
      _ = (∑ W ∈ X.powerset, weight X ℓ W) := by rw [hsplit]
  have h2 : (∑ m ∈ Finset.range (X.card + 1), ∑ W ∈ X.powersetCard m, weight X ℓ W)
      = ∑ m ∈ Finset.range (X.card + 1), (X.card.choose m : ℝ) * ((ℓ - 1 : ℕ) : ℝ) ^ (X.card - m) := by
      apply Finset.sum_congr rfl
      intro m hm
      exact sum_weight_card X ℓ m (Nat.le_of_lt_succ (Finset.mem_range.mp hm))
  calc
    (∑ m ∈ Finset.range (X.card + 1), (X.card.choose m : ℝ) * ((ℓ - 1 : ℕ) : ℝ) ^ (X.card - m))
        = (∑ m ∈ Finset.range (X.card + 1), ∑ W ∈ X.powersetCard m, weight X ℓ W) := h2.symm
    _ = (∑ W ∈ X.powerset, weight X ℓ W) := h1
    _ = (ℓ : ℝ) ^ X.card := measure_all (X := X) (ℓ := ℓ) j

/-- total weight of subsets satisfying `m0 ≤ card` and `Q` is at most ε·ℓ^n when per-size
    bad counts are ≤ ε·choose -/
lemma measure_P_le_pow {X : Finset α} {ℓ m0 : ℕ} {ε : ℝ} (hℓ1 : 1 ≤ ℓ) (hε0 : 0 ≤ ε)
    (Q : Finset α → Prop) [DecidablePred Q]
    (hsize : ∀ m, m0 ≤ m → m ≤ X.card →
       (((X.powersetCard m).filter (fun W : Finset α => Q W)).card : ℝ) ≤ ε * (X.card.choose m : ℝ)) :
    (∑ W ∈ X.powerset with m0 ≤ W.card ∧ Q W, weight X ℓ W) ≤ ε * (ℓ : ℝ) ^ X.card := by
  classical
  have ht0 : (0 : ℝ) ≤ ((ℓ - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 ≤ ℓ - 1)
  have hj0 : Fin ℓ := ⟨0, by omega⟩
  calc
    (∑ W ∈ X.powerset with m0 ≤ W.card ∧ Q W, weight X ℓ W)
        = ∑ m ∈ (Finset.range (X.card + 1)).filter (fun m => m0 ≤ m),
            ∑ W ∈ X.powersetCard m with Q W, weight X ℓ W := by
            exact sum_filter_card_ge X m0 Q (fun W => weight X ℓ W)
    _ ≤ ∑ m ∈ (Finset.range (X.card + 1)).filter (fun m => m0 ≤ m),
            ε * (X.card.choose m : ℝ) * ((ℓ - 1 : ℕ) : ℝ) ^ (X.card - m) := by
            apply Finset.sum_le_sum
            intro m hm
            have hm' := Finset.mem_filter.mp hm
            have hmN : m ≤ X.card := by
              have : m < X.card + 1 := Finset.mem_range.mp hm'.1
              omega
            have hsize_m := hsize m hm'.2 hmN
            have hinner : (∑ W ∈ X.powersetCard m with Q W, weight X ℓ W)
                  = (((X.powersetCard m).filter (fun W => Q W)).card : ℝ) * ((ℓ - 1 : ℕ) : ℝ) ^ (X.card - m) := by
                      have hWcard : ∀ W ∈ (X.powersetCard m).filter (fun W => Q W), X.card - W.card = X.card - m := by
                        intro W hW
                        have hc := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hW).1).2
                        rw [hc]
                      calc
                        (∑ W ∈ X.powersetCard m with Q W, weight X ℓ W)
                            = ∑ W ∈ (X.powersetCard m).filter (fun W => Q W), ((ℓ - 1 : ℕ) : ℝ) ^ (X.card - W.card) := by rfl
                        _ = ∑ W ∈ (X.powersetCard m).filter (fun W => Q W), ((ℓ - 1 : ℕ) : ℝ) ^ (X.card - m) := by
                                refine Finset.sum_congr rfl ?_
                                intro W hW
                                rw [hWcard W hW]
                        _ = (((X.powersetCard m).filter (fun W => Q W)).card : ℝ) * ((ℓ - 1 : ℕ) : ℝ) ^ (X.card - m) := by
                                rw [Finset.sum_const]
                                simp [nsmul_eq_mul]
            have hpow : 0 ≤ ((ℓ - 1 : ℕ) : ℝ) ^ (X.card - m) := pow_nonneg ht0 (X.card - m)
            have hle2 : (((X.powersetCard m).filter (fun W => Q W)).card : ℝ) * ((ℓ - 1 : ℕ) : ℝ) ^ (X.card - m)
                  ≤ ε * (X.card.choose m : ℝ) * ((ℓ - 1 : ℕ) : ℝ) ^ (X.card - m) := by
                      exact (mul_le_mul_of_nonneg_right hsize_m hpow).trans_eq (by ring)
            exact le_trans (le_of_eq hinner) hle2
    _ = ε * (∑ m ∈ (Finset.range (X.card + 1)).filter (fun m => m0 ≤ m),
            (X.card.choose m : ℝ) * ((ℓ - 1 : ℕ) : ℝ) ^ (X.card - m)) := by
            calc
              (∑ m ∈ (Finset.range (X.card + 1)).filter (fun m => m0 ≤ m),
                  ε * (X.card.choose m : ℝ) * ((ℓ - 1 : ℕ) : ℝ) ^ (X.card - m))
                  = ∑ m ∈ (Finset.range (X.card + 1)).filter (fun m => m0 ≤ m),
                      ε * ((X.card.choose m : ℝ) * ((ℓ - 1 : ℕ) : ℝ) ^ (X.card - m)) := by
                      refine Finset.sum_congr rfl ?_
                      intro m hm
                      ring
              _ = ε * (∑ m ∈ (Finset.range (X.card + 1)).filter (fun m => m0 ≤ m),
                      (X.card.choose m : ℝ) * ((ℓ - 1 : ℕ) : ℝ) ^ (X.card - m)) := by
                      rw [Finset.mul_sum]
    _ ≤ ε * (∑ m ∈ Finset.range (X.card + 1), (X.card.choose m : ℝ) * ((ℓ - 1 : ℕ) : ℝ) ^ (X.card - m)) := by
            have hsub : (Finset.range (X.card + 1)).filter (fun m => m0 ≤ m) ⊆ Finset.range (X.card + 1) := by
              intro m hm; exact (Finset.mem_filter.mp hm).1
            have hterm0 : ∀ m ∈ Finset.range (X.card + 1), m ∉ (Finset.range (X.card + 1)).filter (fun m => m0 ≤ m) → 0 ≤ (X.card.choose m : ℝ) * ((ℓ - 1 : ℕ) : ℝ) ^ (X.card - m) := by
              intro m hm _
              have h1 : 0 ≤ (X.card.choose m : ℝ) := by positivity
              exact mul_nonneg h1 (pow_nonneg ht0 _)
            have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub hterm0
            exact mul_le_mul_of_nonneg_left hle hε0
    _ = ε * (ℓ : ℝ) ^ X.card := by
            rw [measure_all_by_size (X := X) (ℓ := ℓ) hj0]




/-- a subset W contains a member of S -/
def hasMem (S : Finset (Finset α)) (W : Finset α) : Prop := ∃ A ∈ S, A ⊆ W

/-- (1/2) ≤ log 2 -/
lemma log2_ge_half : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have h1 : Real.log (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have hsub : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    have h2 : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
    rw [h2, Real.log_inv (2 : ℝ)]
  linarith

/-- 0 < log(2·k) for k ≥ 1 -/
lemma log_two_k_pos_ge {k : ℕ} (hk : 1 ≤ k) : (0 : ℝ) < Real.log (2 * (k : ℝ)) := by
  have hk2 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h4 : (0 : ℝ) < 2 * (k : ℝ) := by nlinarith
  have h4' : (1 : ℝ) < 2 * (k : ℝ) := by nlinarith
  exact Real.log_pos h4'

/-- log(2k) ≥ log 2 for k ≥ 1 -/
lemma log_two_k_ge_log_two {k : ℕ} (hk : 1 ≤ k) :
    Real.log 2 ≤ Real.log (2 * (k : ℝ)) := by
  have hpos2 : (0 : ℝ) < 2 := by norm_num
  have hposk : (0 : ℝ) < 2 * (k : ℝ) := by
    have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    positivity
  have hle : (2 : ℝ) ≤ 2 * (k : ℝ) := by
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    nlinarith
  exact Real.log_le_log hpos2 hle

/-- log(32k) ≤ 16·log(2k) for k ≥ 1 -/
lemma log_32k_le_16_log_2k {k : ℕ} (hk : 1 ≤ k) :
    Real.log (32 * (k : ℝ)) ≤ 16 * Real.log (2 * (k : ℝ)) := by
  have hpos1 : (0 : ℝ) < 32 * (k : ℝ) := by
    have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    positivity
  have hpos2 : (0 : ℝ) < 2 * (k : ℝ) := by
    have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    positivity
  -- 32k ≤ (2k)^16
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk15 : (1 : ℝ) ≤ (k : ℝ) ^ 15 := one_le_pow₀ (n := 15) hk1
  have hk16 : (k : ℝ) ≤ (k : ℝ) ^ 16 := by
    calc
      (k : ℝ) = (k : ℝ) * 1 := by ring
      _ ≤ (k : ℝ) * (k : ℝ) ^ 15 := by
        exact mul_le_mul_of_nonneg_left hk15 (by positivity)
      _ = (k : ℝ) ^ 16 := by ring
  have hle : (32 * (k : ℝ)) ≤ (2 * (k : ℝ)) ^ 16 := by
    rw [mul_pow]
    nlinarith
  have hlogle : Real.log (32 * (k : ℝ)) ≤ Real.log ((2 * (k : ℝ)) ^ 16) :=
    Real.log_le_log hpos1 hle
  rw [Real.log_pow] at hlogle
  exact hlogle

/-- lemma main' : spread families contain p disjoint sets -/
theorem spread_disjoint {X : Finset α} {S : Finset (Finset α)} {k p : ℕ} {r : ℝ}
    (hk : 2 ≤ k) (hp : 2 ≤ p)
    (hS : ∀ A ∈ S, A ⊆ X) (huni : ∀ A ∈ S, A.card = k)
    (hspread : ∀ T : Finset α, T ⊆ X → T.Nonempty →
      (#(S.filter (fun A : Finset α => T ⊆ A)) : ℝ) ≤ r ^ (k - T.card))
    (hSr : (S.card : ℝ) ≥ r ^ k)
    (hr1 : 1 ≤ r) (hrn : r ≤ (X.card : ℝ))
    (hn6 : 6 * k ≤ X.card)
    (hrbig : Cmain * (p : ℝ) * Real.log (2 * (k : ℝ)) ≤ r) :
    ∃ T : Finset (Finset α), T ⊆ S ∧ T.card = p ∧
      (∀ A ∈ T, ∀ B ∈ T, A ≠ B → Disjoint A B) := by

  classical
  let ℓ : ℕ := 32 * p
  let q : ℝ := 1 / (ℓ : ℝ)
  let γ : ℝ := 1 / (2 * (ℓ : ℝ))
  let m0 : ℕ := Nat.ceil (γ * (X.card : ℝ))
  -- basic constants
  have hℓ2 : 2 ≤ ℓ := by
    dsimp [ℓ]
    omega
  have hℓ0 : 0 < ℓ := by omega
  have hℓ1 : 1 ≤ ℓ := by omega
  have hℓR : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ1
  have hℓne : (ℓ : ℝ) ≠ 0 := by exact_mod_cast (by omega : ℓ ≠ 0)
  have hγ0 : (0 : ℝ) < γ := by
    dsimp [γ, ℓ]
    positivity
  have hγle : γ ≤ 1 / 32 := by
    dsimp [γ]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) * (ℓ : ℝ))]
    have h16 : (16 : ℝ) ≤ (ℓ : ℝ) := by
      dsimp [ℓ]
      exact_mod_cast (by omega : (16 : ℕ) ≤ 32 * p)
    nlinarith
  have h12 : (12 : ℝ) ≤ (X.card : ℝ) := Xcard_ge_12 (X := X) (k := k) hk hn6
  have hnpos : (0 : ℝ) < (X.card : ℝ) := by nlinarith
  have hγnpos : (0 : ℝ) < γ * (X.card : ℝ) := mul_pos hγ0 hnpos
  have hm0pos : 0 < m0 := by
    dsimp [m0]
    exact (Nat.ceil_pos).2 hγnpos
  have hm0le_n : m0 ≤ X.card := by
    simpa [m0] using (ceil_gamma_le_n (γ := γ) (n := X.card) hγ0 hγle h12)
  have hMc : (m0 : ℝ) - 1 ≤ γ * (X.card : ℝ) := by
    have hceil : (m0 : ℝ) < γ * (X.card : ℝ) + 1 := by
      simpa [m0] using (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ γ * (X.card : ℝ) by positivity))
    linarith
  have hMthm : ((m0 - 1 : ℕ) : ℝ) ≤ (X.card : ℝ) / (ℓ : ℝ) / 2 := by
    have h1 : ((m0 - 1 : ℕ) : ℝ) = (m0 : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ m0)]
      norm_num
    have h3 : γ * (X.card : ℝ) = (X.card : ℝ) / (ℓ : ℝ) / 2 := by
      dsimp [γ]
      field_simp [hℓne]
    rw [h1]
    rw [← h3]
    exact hMc
  -- log(2k) positive and ≥ log 2
  have hk1 : 1 ≤ k := by omega
  have hlogk : (0 : ℝ) < Real.log (2 * (k : ℝ)) := log_two_k_pos_ge hk1
  have hlog2le : Real.log 2 ≤ Real.log (2 * (k : ℝ)) := log_two_k_ge_log_two hk1
  have hlog2pos : (0 : ℝ) < Real.log 2 := by
    exact Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog2ge : (1 / 2 : ℝ) ≤ Real.log 2 := log2_ge_half
  -- r ≥ Cmain·p·log2 (real), and n ≥ that
  have hbigr : (2 ^ 70 : ℝ) * (p : ℝ) * Real.log 2 ≤ r := by
    have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
    have hmul1 : (p : ℝ) * Real.log 2 ≤ (p : ℝ) * Real.log (2 * (k : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hlog2le hp0
    have hmul2 : (2 ^ 70 : ℝ) * ((p : ℝ) * Real.log 2) ≤ (2 ^ 70 : ℝ) * ((p : ℝ) * Real.log (2 * (k : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hmul1 (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 70)
    calc
      (2 ^ 70 : ℝ) * (p : ℝ) * Real.log 2 = (2 ^ 70 : ℝ) * ((p : ℝ) * Real.log 2) := by ring
      _ ≤ (2 ^ 70 : ℝ) * ((p : ℝ) * Real.log (2 * (k : ℝ))) := hmul2
      _ = Cmain * (p : ℝ) * Real.log (2 * (k : ℝ)) := by unfold Cmain; ring
      _ ≤ r := by simpa using hrbig
  have hbiglog2 : (2 ^ 70 : ℝ) * (p : ℝ) * Real.log 2 ≤ (X.card : ℝ) := le_trans hbigr hrn
  -- exp tail bound: exp(-(n/ℓ)/8) ≤ 1/2
  have htailineq : Real.log 2 ≤ ((X.card : ℝ) / (ℓ : ℝ)) / 8 := by
    have hA : (2 ^ 62 : ℝ) * (ℓ : ℝ) * Real.log 2 ≤ (X.card : ℝ) := by
      calc
        (2 ^ 62 : ℝ) * (ℓ : ℝ) * Real.log 2 = (2 ^ 67 : ℝ) * (p : ℝ) * Real.log 2 := by
            dsimp [ℓ]
            norm_num
            ring
        _ ≤ (2 ^ 70 : ℝ) * (p : ℝ) * Real.log 2 := by
            have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
            have hlog0 : (0 : ℝ) ≤ Real.log 2 := le_of_lt hlog2pos
            nlinarith [mul_le_mul_of_nonneg_left (by norm_num : (2 : ℝ) ^ 67 ≤ (2 : ℝ) ^ 70) (mul_nonneg hp0 hlog0)]
        _ ≤ (X.card : ℝ) := hbiglog2
    -- X.card ≥ 8·ℓ·log2 → (X.card/ℓ)/8 ≥ log2
    have h8 : (8 : ℝ) * (ℓ : ℝ) * Real.log 2 ≤ (2 ^ 62 : ℝ) * (ℓ : ℝ) * Real.log 2 := by
      have hℓ0' : (0 : ℝ) ≤ (ℓ : ℝ) := le_of_lt (by positivity : (0 : ℝ) < (ℓ : ℝ))
      have hlog0 : (0 : ℝ) ≤ Real.log 2 := le_of_lt hlog2pos
      nlinarith [mul_le_mul_of_nonneg_left (by norm_num : (8 : ℝ) ≤ (2 : ℝ) ^ 62) (mul_nonneg hℓ0' hlog0)]
    have hmain8 : (8 : ℝ) * (ℓ : ℝ) * Real.log 2 ≤ (X.card : ℝ) := le_trans h8 hA
    have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by positivity
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
    rw [le_div_iff₀ hℓpos]
    nlinarith
  have hExp : Real.exp (-((X.card : ℝ) / (ℓ : ℝ)) / 8) ≤ 1 / 2 := by
    have hle : -((X.card : ℝ) / (ℓ : ℝ)) / 8 ≤ -Real.log 2 := by linarith
    have h1 := (Real.exp_le_exp).2 hle
    -- exp(-log 2) = 1/2
    calc
      Real.exp (-((X.card : ℝ) / (ℓ : ℝ)) / 8) ≤ Real.exp (-Real.log 2) := h1
      _ = 1 / 2 := by
        rw [Real.exp_neg]
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        norm_num
  -- log(32k) ≤ 16 log(2k)
  have hlog32 : Real.log (32 * (k : ℝ)) ≤ 16 * Real.log (2 * (k : ℝ)) := log_32k_le_16_log_2k hk1
  -- kap ≤ r
  have hrkap : kap ≤ r := by
    have h1 : (kap : ℝ) ≤ (2 ^ 70 : ℝ) * (p : ℝ) * Real.log 2 := by
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := hlog2ge
      have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
      unfold kap
      nlinarith
    exact le_trans h1 hbigr
  -- ===== per-size bound from rao_petal =====
  have hpetal_bound : Bpetal / γ * Real.log (2 * (k : ℝ) / (1 / 16 : ℝ)) ≤ r := by
    have harg : 2 * (k : ℝ) / (1 / 16 : ℝ) = 32 * (k : ℝ) := by norm_num; ring
    have hB : Bpetal / γ = (2 ^ 66 : ℝ) * (p : ℝ) := by
      unfold Bpetal γ ℓ
      have hp0 : (0 : ℝ) < (p : ℝ) := by positivity
      field_simp [hp0.ne']
      norm_num
    have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
    have hlelog := mul_le_mul_of_nonneg_left hlog32 (mul_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 66) hp0)
    calc
      Bpetal / γ * Real.log (2 * (k : ℝ) / (1 / 16 : ℝ))
          = (2 ^ 66 : ℝ) * (p : ℝ) * Real.log (32 * (k : ℝ)) := by rw [hB, harg]
      _ ≤ (2 ^ 66 : ℝ) * (p : ℝ) * (16 * Real.log (2 * (k : ℝ))) := by
            have hp0' : (0 : ℝ) ≤ (p : ℝ) := by positivity
            exact mul_le_mul_of_nonneg_left hlog32 (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 66 * (p : ℝ))
      _ = (2 ^ 70 : ℝ) * (p : ℝ) * Real.log (2 * (k : ℝ)) := by ring
      _ = Cmain * (p : ℝ) * Real.log (2 * (k : ℝ)) := by unfold Cmain; ring
      _ ≤ r := by simpa using hrbig
  have hpetal_cond : ∀ m : ℕ, m0 ≤ m → m ≤ X.card → Echi S X m ≤ (1 / 16 : ℝ) := by
    intro m hm0m hmn
    apply rao_petal (X := X) (S := S) (k := k) (r := r) (γ := γ) (ε := (1 / 16 : ℝ)) (m := m)
      hk hS huni hspread hSr hr1 hrn hn6 hrkap hγ0 hγle
      (by
        have h1 : γ * (X.card : ℝ) ≤ (m0 : ℝ) := by
          dsimp [m0]
          exact_mod_cast (Nat.le_ceil (γ * (X.card : ℝ)))
        have h2 : (m0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm0m
        nlinarith)
      hmn (by norm_num) (by norm_num) hpetal_bound
  have hSne : S.Nonempty := S_ne_of_Sr (k := k) (r := r) (by omega) hr1 hSr
  have hbad_size : ∀ m : ℕ, m0 ≤ m → m ≤ X.card →
      (((X.powersetCard m).filter (fun W : Finset α => ¬ hasMem S W)).card : ℝ) ≤ (1 / 16 : ℝ) * (X.card.choose m : ℝ) := by
    intro m hm0m hmn
    have hpet := hpetal_cond m hm0m hmn
    have hle := Echi_lower_contains (S := S) (X := X) m hSne hmn
    have hle' : (((X.powersetCard m).filter (fun W : Finset α => ¬ hasMem S W)).card : ℝ)
        ≤ ((X.powersetCard m).card : ℝ) * Echi S X m := by
          simpa [hasMem, cardSubsets] using hle
    calc
      (((X.powersetCard m).filter (fun W : Finset α => ¬ hasMem S W)).card : ℝ)
          ≤ ((X.powersetCard m).card : ℝ) * Echi S X m := hle'
      _ ≤ ((X.powersetCard m).card : ℝ) * (1 / 16 : ℝ) := by
            exact mul_le_mul_of_nonneg_left hpet (by positivity)
      _ = (1 / 16 : ℝ) * (X.card.choose m : ℝ) := by
            rw [Finset.card_powersetCard]
            ring
  -- μsmall and μbad and μall and μgood bounds
  have hsmall' : (∑ W ∈ X.powerset with W.card < m0, weight X ℓ W) ≤
      ((ℓ : ℝ) ^ X.card) * Real.exp (-((X.card : ℝ) / (ℓ : ℝ)) / 8) := by
    have hM := measure_small_le (X := X) (ℓ := ℓ) (M := m0 - 1) hℓ1 hMthm
    have hconv : (∑ W ∈ X.powerset with W.card < m0, weight X ℓ W)
        = ∑ W ∈ X.powerset with W.card ≤ m0 - 1, weight X ℓ W := by
      have hfilt : X.powerset.filter (fun W => W.card < m0) = X.powerset.filter (fun W => W.card ≤ m0 - 1) := by
        ext W
        constructor
        · intro hW
          rw [Finset.mem_filter] at hW ⊢
          exact ⟨hW.1, by omega⟩
        · intro hW
          rw [Finset.mem_filter] at hW ⊢
          exact ⟨hW.1, by omega⟩
      rw [hfilt]
    calc
      (∑ W ∈ X.powerset with W.card < m0, weight X ℓ W)
          = ∑ W ∈ X.powerset with W.card ≤ m0 - 1, weight X ℓ W := hconv
      _ ≤ ((ℓ : ℝ) ^ X.card) * Real.exp (-((X.card : ℝ) / (ℓ : ℝ)) / 8) := hM
  have hsmall : (∑ W ∈ X.powerset with W.card < m0, weight X ℓ W) ≤ ((ℓ : ℝ) ^ X.card) / 2 := by
    calc
      (∑ W ∈ X.powerset with W.card < m0, weight X ℓ W)
          ≤ ((ℓ : ℝ) ^ X.card) * Real.exp (-((X.card : ℝ) / (ℓ : ℝ)) / 8) := hsmall'
      _ ≤ ((ℓ : ℝ) ^ X.card) * (1 / 2) := by
            exact mul_le_mul_of_nonneg_left hExp (by positivity)
      _ = ((ℓ : ℝ) ^ X.card) / 2 := by ring
  have hbad : (∑ W ∈ X.powerset with m0 ≤ W.card ∧ ¬ hasMem S W, weight X ℓ W) ≤
      (1 / 16 : ℝ) * (ℓ : ℝ) ^ X.card := by
    exact measure_P_le_pow (X := X) (ℓ := ℓ) (m0 := m0) (ε := (1 / 16 : ℝ)) hℓ1 (by norm_num)
      (fun W => ¬ hasMem S W) hbad_size
  let j0 : Fin ℓ := ⟨0, by omega⟩
  have hμall : (∑ W ∈ X.powerset, weight X ℓ W) = (ℓ : ℝ) ^ X.card := measure_all (X := X) (ℓ := ℓ) j0
  have hgood : (7 / 16 : ℝ) * (ℓ : ℝ) ^ X.card ≤
      ∑ W ∈ X.powerset with m0 ≤ W.card ∧ hasMem S W, weight X ℓ W := by
    have hsplit := measure_split (X := X) (ℓ := ℓ) (m0 := m0) (fun W => hasMem S W)
    nlinarith [hsplit, hμall, hsmall, hbad]
  -- ===== colouring-side of the good measure =====
  let goodProp : Finset α → Prop := fun W => m0 ≤ W.card ∧ hasMem S W
  let goodInd : Finset α → ℝ := fun W => if goodProp W then 1 else 0
  let gsum : ℝ := ∑ W ∈ X.powerset with goodProp W, weight X ℓ W
  have hgood' : (7 / 16 : ℝ) * (ℓ : ℝ) ^ X.card ≤ gsum := by
    simpa [gsum, goodProp] using hgood
  have hgmeas (j : Fin ℓ) : (∑ u : Colourings X ℓ, goodInd (cls X u j)) = gsum := by
    calc
      (∑ u : Colourings X ℓ, goodInd (cls X u j)) = ∑ W ∈ X.powerset, weight X ℓ W * goodInd W := by
            exact sum_colour_by_class X j goodInd
      _ = ∑ W ∈ X.powerset, (if goodProp W then weight X ℓ W else 0) := by
            refine Finset.sum_congr rfl ?_
            intro W hW
            by_cases h : goodProp W
            · simp [h, goodInd]
            · simp [h, goodInd]
      _ = gsum := by
            unfold gsum
            rw [← Finset.sum_filter]
  let gc (u : Colourings X ℓ) : ℕ := (Finset.univ.filter (fun j : Fin ℓ => goodProp (cls X u j))).card
  have hboole (u : Colourings X ℓ) :
      (∑ j : Fin ℓ, goodInd (cls X u j)) = (gc u : ℝ) := by
    unfold gc goodInd goodProp
    change (∑ j ∈ (Finset.univ : Finset (Fin ℓ)), (if goodProp (cls X u j) then (1 : ℝ) else 0))
        = ((Finset.univ.filter (fun j => goodProp (cls X u j))).card : ℝ)
    simpa using (Finset.sum_boole (fun j => goodProp (cls X u j)) (Finset.univ : Finset (Fin ℓ)))
  let TOT : ℝ := ∑ u : Colourings X ℓ, ∑ j : Fin ℓ, goodInd (cls X u j)
  have hTOT_gc : TOT = ∑ u : Colourings X ℓ, (gc u : ℝ) := by
    unfold TOT
    refine Finset.sum_congr rfl ?_
    intro u hu
    exact hboole u
  have hTOT_lower : (14 * (p : ℝ)) * (ℓ : ℝ) ^ X.card ≤ TOT := by
    have hswap : TOT = ∑ j : Fin ℓ, ∑ u : Colourings X ℓ, goodInd (cls X u j) := by
      unfold TOT
      change (∑ u ∈ (Finset.univ : Finset (Colourings X ℓ)), ∑ j ∈ (Finset.univ : Finset (Fin ℓ)), goodInd (cls X u j))
          = (∑ j ∈ (Finset.univ : Finset (Fin ℓ)), ∑ u ∈ (Finset.univ : Finset (Colourings X ℓ)), goodInd (cls X u j))
      rw [Finset.sum_comm]
    calc
      TOT = ∑ j : Fin ℓ, ∑ u : Colourings X ℓ, goodInd (cls X u j) := hswap
      _ = ∑ j : Fin ℓ, gsum := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            exact hgmeas j
      _ = ((Fintype.card (Fin ℓ) : ℝ)) * gsum := by
            change (∑ j ∈ (Finset.univ : Finset (Fin ℓ)), gsum) = (Fintype.card (Fin ℓ) : ℝ) * gsum
            rw [Finset.sum_const]
            simp
      _ = (ℓ : ℝ) * gsum := by
            rw [Fintype.card_fin]
      _ = (32 * (p : ℝ)) * gsum := by
            have hℓcast : (ℓ : ℝ) = (32 : ℝ) * (p : ℝ) := by
              dsimp [ℓ]
              rw [Nat.cast_mul]
              norm_num
            rw [hℓcast]
      _ ≥ (14 * (p : ℝ)) * (ℓ : ℝ) ^ X.card := by
            -- (32p)·gsum ≥ (32p)·(7/16)·ℓ^n = 14p·ℓ^n
            have hm := mul_le_mul_of_nonneg_left hgood' (by positivity : (0 : ℝ) ≤ (32 * (p : ℝ)))
            have hring : (14 * (p : ℝ)) * (ℓ : ℝ) ^ X.card = (32 * (p : ℝ)) * ((7 / 16 : ℝ) * (ℓ : ℝ) ^ X.card) := by ring
            rw [hring]
            exact hm
  -- ===== some colouring has ≥ p good classes =====
  have hcol : ∃ u : Colourings X ℓ, p ≤ gc u := by
    by_contra hno
    have hno' : ∀ u : Colourings X ℓ, gc u ≤ p - 1 := by
      intro u
      by_contra hgt
      have hge : p ≤ gc u := by omega
      exact hno ⟨u, hge⟩
    have hupper : TOT ≤ ((p : ℝ) - 1) * (ℓ : ℝ) ^ X.card := by
      calc
        TOT = ∑ u : Colourings X ℓ, (gc u : ℝ) := hTOT_gc
        _ ≤ ∑ u : Colourings X ℓ, ((p : ℝ) - 1) := by
              refine Finset.sum_le_sum ?_
              intro u hu
              have hgc := hno' u
              have hp1 : 1 ≤ p := by omega
              have hcast' : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
                have h1 : ((p - 1 : ℕ) : ℝ) + 1 = (p : ℝ) := by exact_mod_cast (Nat.sub_add_cancel hp1)
                linarith
              rw [← hcast']
              exact_mod_cast hgc
        _ = (Fintype.card (Colourings X ℓ) : ℝ) * ((p : ℝ) - 1) := by
              have hcardsum : (∑ u : Colourings X ℓ, ((p : ℝ) - 1)) = (Fintype.card (Colourings X ℓ) : ℝ) * ((p : ℝ) - 1) := by
                simp [nsmul_eq_mul, Finset.card_univ, Finset.sum_const]
                ring
              exact hcardsum
        _ = (ℓ : ℝ) ^ X.card * ((p : ℝ) - 1) := by
              rw [colouring_card]
              rw [Nat.cast_pow]
        _ = ((p : ℝ) - 1) * (ℓ : ℝ) ^ X.card := by ring
    have hleX : (14 * (p : ℝ)) * (ℓ : ℝ) ^ X.card ≤ ((p : ℝ) - 1) * (ℓ : ℝ) ^ X.card := le_trans hTOT_lower hupper
    have hpos : (0 : ℝ) < (ℓ : ℝ) ^ X.card := by positivity
    have hle : (14 * (p : ℝ)) ≤ (p : ℝ) - 1 := by
      exact le_of_mul_le_mul_right hleX hpos
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    nlinarith
  rcases hcol with ⟨u, hge⟩
  -- ===== extract p good colours and build T =====
  have hcard_g : p ≤ (Finset.univ.filter (fun j : Fin ℓ => goodProp (cls X u j))).card := by
    simpa [gc] using hge
  rcases Finset.exists_subset_card_eq hcard_g with ⟨G, hGsub, hGcard⟩
  let pick : Fin ℓ → Finset α :=
    fun j => if hj : goodProp (cls X u j) then Classical.choose hj.2 else ∅
  have hgoodG {j : Fin ℓ} (hj : j ∈ G) : goodProp (cls X u j) := by
    exact (Finset.mem_filter.mp (hGsub hj)).2
  have hpick_mem {j : Fin ℓ} (hgood : goodProp (cls X u j)) : pick j ∈ S := by
    unfold pick
    rw [dif_pos hgood]
    exact (Classical.choose_spec hgood.2).1
  have hpick_sub {j : Fin ℓ} (hgood : goodProp (cls X u j)) : pick j ⊆ cls X u j := by
    unfold pick
    rw [dif_pos hgood]
    exact (Classical.choose_spec hgood.2).2
  have hinj : Set.InjOn pick (↑G : Set (Fin ℓ)) := by
    intro j hjG j' hj'G hjj
    by_contra hne
    have hgood : goodProp (cls X u j) := hgoodG hjG
    have hgood' : goodProp (cls X u j') := hgoodG hj'G
    have hdisj : Disjoint (cls X u j) (cls X u j') := disjoint_cls X u hne
    have hA : pick j ∈ S := hpick_mem hgood
    have hA1 : pick j ⊆ cls X u j := hpick_sub hgood
    have hA2 : pick j' ⊆ cls X u j' := hpick_sub hgood'
    have hA1' : pick j ⊆ cls X u j' := by
      rw [hjj]
      exact hA2
    have hcardk : (pick j).card = k := huni (pick j) hA
    have hnon : (pick j).Nonempty := by
      have hk1 : 1 ≤ k := by omega
      have hpos : 0 < (pick j).card := by omega
      exact Finset.card_pos.mp hpos
    rcases hnon with ⟨x, hx⟩
    have hx1 : x ∈ cls X u j := hA1 hx
    have hx2 : x ∈ cls X u j' := hA1' hx
    exact (Finset.disjoint_left.mp hdisj) hx1 hx2
  let T : Finset (Finset α) := G.image pick
  refine ⟨T, ?_, ?_, ?_⟩
  · -- T ⊆ S
    intro A hA
    dsimp [T] at hA
    rw [Finset.mem_image] at hA
    rcases hA with ⟨j, hj, rfl⟩
    exact hpick_mem (hgoodG hj)
  · -- T.card = p
    dsimp [T]
    have hcardimg : (G.image pick).card = G.card := Finset.card_image_of_injOn hinj
    rw [hcardimg, hGcard]
  · -- pairwise disjoint
    intro A hA B hB hAB
    dsimp [T] at hA hB
    rw [Finset.mem_image] at hA hB
    rcases hA with ⟨j, hj, rfl⟩
    rcases hB with ⟨j', hj', rfl⟩
    have hgood : goodProp (cls X u j) := hgoodG hj
    have hgood' : goodProp (cls X u j') := hgoodG hj'
    have hne : j ≠ j' := by
      intro hjj
      subst j'
      exact hAB rfl
    have hdisj : Disjoint (cls X u j) (cls X u j') := disjoint_cls X u hne
    exact hdisj.mono (hpick_sub hgood) (hpick_sub hgood')


end Submission.Sun
