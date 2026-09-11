import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.SelCore

/-!
# The deep fragment argument (Theorem 5.7'' of Park--Pham).

A member `S ∈ 𝓕` of the family carries a level function `lv S : X → ℕ`, meaningful on `S`.
Elements at level `j` have weight `q^{-j}`, `q = 100`. All levels are ≤ τ.
-/

set_option autoImplicit false
open Classical
open MeasureTheory ProbabilityTheory Measure unitInterval Finset
open scoped NNReal ENNReal BigOperators

namespace Submission

open _root_.SupremumOfSelectorProcesses

namespace Sel

open Frame

namespace Deep

/-- base `q = 100` -/
abbrev q : ℕ := 100

lemma q_pos : 0 < (q : ℝ) := by norm_num [q]
lemma q_ge_one : 1 ≤ (q : ℝ) := by norm_num [q]
lemma q_ne_zero : (q : ℝ) ≠ 0 := by positivity

/-- weight `q^{-j}` of one element at level `j`. -/
noncomputable def wlev (j : ℕ) : ℝ := ((q : ℝ) ^ j)⁻¹

lemma wlev_pos (j : ℕ) : 0 < wlev j := by unfold wlev; positivity
lemma wlev_nonneg (j : ℕ) : 0 ≤ wlev j := le_of_lt (wlev_pos j)

lemma wlev_succ (j : ℕ) : wlev (j + 1) = (q : ℝ)⁻¹ * wlev j := by
  rw [wlev, wlev, pow_succ]
  field_simp [q_ne_zero]

lemma wlev_le_of_le {j k : ℕ} (hjk : j ≤ k) : wlev k ≤ wlev j := by
  unfold wlev
  rw [← one_div, ← one_div]
  exact one_div_le_one_div_of_le (a := (q : ℝ) ^ j) (b := (q : ℝ) ^ k)
    (pow_pos q_pos j) (pow_le_pow_right₀ q_ge_one hjk)

/-- A "system": family 𝓕 of subsets with a level function per member. -/
structure Sys (X : Type*) where
  τ : ℕ
  lv : Set X → X → ℕ
  F : Set (Set X)

namespace Sys
variable {X : Type*} [Fintype X]

/-- levels are bounded by τ on every member -/
def LevelBounded (N : Sys X) : Prop := ∀ S ∈ N.F, ∀ i ∈ S, N.lv S i ≤ N.τ

/-- elements of S at level j -/
def levelSet (N : Sys X) (S : Set X) (j : ℕ) : Set X := {i | i ∈ S ∧ N.lv S i = j}

lemma levelSet_subset (N : Sys X) (S : Set X) (j : ℕ) : N.levelSet S j ⊆ S := by
  intro i hi; exact hi.1

lemma mem_levelSet (N : Sys X) {S : Set X} {i : X} {j : ℕ} :
    i ∈ N.levelSet S j ↔ i ∈ S ∧ N.lv S i = j := Iff.rfl

lemma levelSet_disjoint (N : Sys X) (S : Set X) {j k : ℕ} (hjk : j ≠ k) :
    Disjoint (N.levelSet S j) (N.levelSet S k) := by
  rw [Set.disjoint_left]
  intro i hi hk
  apply hjk
  calc
    j = N.lv S i := hi.2.symm
    _ = k := hk.2

lemma levelSet_eq_empty_of_gt (N : Sys X) {S : Set X} (h : ∀ i ∈ S, N.lv S i ≤ N.τ) {j : ℕ}
    (hj : N.τ < j) : N.levelSet S j = ∅ := by
  ext i
  constructor
  · intro hi
    have hlv : N.lv S i ≤ N.τ := h i hi.1
    have : N.lv S i = j := hi.2
    omega
  · intro hi; simp at hi

/-- level profile count -/
noncomputable def sCount (N : Sys X) (S : Set X) (j : ℕ) : ℕ := (N.levelSet S j).ncard

/-- prefix count n_b = Σ_{j ≤ b} s_j -/
noncomputable def prefixCount (N : Sys X) (S : Set X) (b : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (b + 1), N.sCount S j

/-- weight (sum over levels b+1..τ) of the elements of A∩S -/
noncomputable def weightAbove (N : Sys X) (S : Set X) (A : Set X) (b : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc (b + 1) N.τ, ((A ∩ N.levelSet S j).ncard : ℝ) * wlev j

/-- weight of A∩S over all levels 0..τ -/
noncomputable def weight (N : Sys X) (S : Set X) (A : Set X) : ℝ :=
  ∑ j ∈ Finset.range (N.τ + 1), ((A ∩ N.levelSet S j).ncard : ℝ) * wlev j

/-- total weight of all of S -/
noncomputable def totalWeight (N : Sys X) (S : Set X) : ℝ := N.weight S S

/-- S.ncard = S.toFinset.card -/
lemma ncard_eq_toFinset_card' (A : Set X) : A.ncard = A.toFinset.card := by
  rw [Set.ncard_eq_toFinset_card]
  congr 1
  apply Finset.ext
  intro x
  simp

/-- union of the level sets of S with index ≤ b -/
def unionBelow (N : Sys X) (S : Set X) (b : ℕ) : Set X :=
  {x | ∃ j, j ≤ b ∧ x ∈ N.levelSet S j}

lemma mem_unionBelow (N : Sys X) {S : Set X} {b : ℕ} {x : X} :
    x ∈ N.unionBelow S b ↔ ∃ j, j ≤ b ∧ x ∈ N.levelSet S j := Iff.rfl

lemma unionBelow_subset (N : Sys X) {S : Set X} {b : ℕ} : N.unionBelow S b ⊆ S := by
  rintro x ⟨j, hj, hx⟩
  exact hx.1

lemma unionBelow_mono (N : Sys X) (S : Set X) {b b' : ℕ} (h : b ≤ b') :
    N.unionBelow S b ⊆ N.unionBelow S b' := by
  rintro x ⟨j, hj, hx⟩
  exact ⟨j, le_trans hj h, hx⟩

/-- prefixCount S b = |unionBelow S b| -/
lemma prefixCount_eq_card_below (N : Sys X) (S : Set X) (b : ℕ) :
    N.prefixCount S b = (N.unionBelow S b).ncard := by
  classical
  have hsconv : ∀ j, (N.levelSet S j).ncard = (N.levelSet S j).toFinset.card := by
    intro j; exact ncard_eq_toFinset_card' (N.levelSet S j)
  have hcard := Finset.card_biUnion (s := Finset.range (b + 1))
    (t := fun j : ℕ => (N.levelSet S j).toFinset) (by
      intro j hj k hk hjk
      apply Finset.disjoint_left.mpr
      intro x hx1 hx2
      apply hjk
      calc
        j = N.lv S x := by exact ((Set.mem_toFinset).1 hx1).2.symm
        _ = k := ((Set.mem_toFinset).1 hx2).2)
  unfold Sys.prefixCount Sys.sCount
  calc
    (∑ j ∈ Finset.range (b + 1), (N.levelSet S j).ncard)
        = ∑ j ∈ Finset.range (b + 1), ((N.levelSet S j).toFinset).card := by
          exact Finset.sum_congr rfl (by intro j hj; exact hsconv j)
    _ = (Finset.biUnion (Finset.range (b + 1))
          (fun j : ℕ => (N.levelSet S j).toFinset)).card := hcard.symm
    _ = (N.unionBelow S b).toFinset.card := by
          congr 1
          apply Finset.ext
          intro x
          constructor
          · intro hx
            rcases (Finset.mem_biUnion.mp hx) with ⟨j, hj, hxj⟩
            exact (Set.mem_toFinset).2 ⟨j, (by simpa using hj), (Set.mem_toFinset).1 hxj⟩
          · intro hx
            rcases (Set.mem_toFinset).1 hx with ⟨j, hj, hxj⟩
            exact (Finset.mem_biUnion.mpr ⟨j, (by simpa using hj), (Set.mem_toFinset).2 hxj⟩)
    _ = (N.unionBelow S b).ncard := (ncard_eq_toFinset_card' (N.unionBelow S b)).symm

/-- n_τ = |S| when levels are bounded -/
lemma prefixCount_eq_card (N : Sys X) (S : Set X) (hB : N.LevelBounded) (hS : S ∈ N.F) :
    N.prefixCount S N.τ = S.ncard := by
  classical
  have hsub : N.unionBelow S N.τ = S := by
    apply Set.ext
    intro x
    rw [Sys.mem_unionBelow]
    constructor
    · rintro ⟨j, hj, hxj⟩; exact hxj.1
    · intro hxS
      exact ⟨N.lv S x, hB S hS x hxS, ⟨hxS, rfl⟩⟩
  calc
    N.prefixCount S N.τ = (N.unionBelow S N.τ).ncard := N.prefixCount_eq_card_below S N.τ
    _ = S.ncard := by rw [hsub]

/-- partial profile equality up to level b: level-set COUNTS agree (as in the paper, S' ∈ F_{s_b}) -/
def ProfileEq (N : Sys X) (S S' : Set X) (b : ℕ) : Prop :=
  ∀ j, j ≤ b → N.sCount S j = N.sCount S' j

/-- 𝓕_{𝓼_b}: members with the same partial profile as S, up to level b -/
def FPartial (N : Sys X) (S : Set X) (b : ℕ) : Set (Set X) :=
  {S' | S' ∈ N.F ∧ ProfileEq N S S' b}

/-- The paper's fragment relation: U is an (S,W)-fragment with index b, witnessed by S'. -/
def IsFragment (N : Sys X) (S : Set X) (W U : Set X) (b : ℕ) (S' : Set X) : Prop :=
  S' ∈ N.FPartial S b ∧
  U ⊆ S ∧ Disjoint U W ∧
  (∀ j ≤ b, N.levelSet S' j ⊆ W ∪ U) ∧
  N.weightAbove S' (W ∪ U) b ≥ (100 : ℝ)⁻¹ *
    (N.weightAbove S' S' b - wlev b * ((N.prefixCount S b : ℝ) - (U.ncard : ℝ)))

/-- existence of a fragment with index b -/
def HasFragmentAt (N : Sys X) (S : Set X) (W U : Set X) (b : ℕ) : Prop :=
  ∃ S', N.IsFragment S W U b S'

/-- n_τ ≥ |S∖W| -/
lemma prefixCount_ge_sdiff (N : Sys X) (S : Set X) (W : Set X) (hB : N.LevelBounded)
    (hS : S ∈ N.F) :
    ((N.prefixCount S N.τ : ℝ) - ((S \ W).ncard : ℝ)) ≥ 0 := by
  rw [N.prefixCount_eq_card S hB hS]
  have hle : (S \ W).ncard ≤ S.ncard := Set.ncard_le_ncard (by simp)
  exact sub_nonneg.mpr (by exact_mod_cast hle)

/-- S∖W is a fragment of (S,W) with index τ, witnessed by S itself. -/
lemma sdiff_isFragment (N : Sys X) (S : Set X) (W : Set X) (hS : S ∈ N.F)
    (hB : N.LevelBounded) :
    N.IsFragment S W (S \ W) N.τ S := by
  constructor
  · constructor <;> simp [Sys.FPartial, Sys.ProfileEq, hS]
  · constructor
    · simp
    · constructor
      · exact Set.disjoint_sdiff_left
      · constructor
        · intro j hj i hi
          by_cases hw : i ∈ W
          · exact Or.inl hw
          · exact Or.inr ⟨hi.1, hw⟩
        · have h0 : N.weightAbove S (W ∪ (S \ W)) N.τ = 0 := by
            simp [Sys.weightAbove]
          rw [h0]
          have hnonneg : 0 ≤ ((N.prefixCount S N.τ : ℝ) - ((S \ W).ncard : ℝ)) :=
            N.prefixCount_ge_sdiff S W hB hS
          have hA : N.weightAbove S S N.τ = 0 := by simp [Sys.weightAbove]
          rw [hA]
          have hwx : 0 ≤ wlev N.τ * ((N.prefixCount S N.τ : ℝ) - ((S \ W).ncard : ℝ)) :=
            mul_nonneg (wlev_nonneg N.τ) hnonneg
          nlinarith

/-- The min index of fragments of (S, W): least n with a fragment of (S,W) at index n. -/
noncomputable def MinIndex (N : Sys X) (S : Set X) (W : Set X) (hS : S ∈ N.F)
    (hB : N.LevelBounded) : ℕ := by
  classical
  exact Nat.find (⟨N.τ, S \ W, S, N.sdiff_isFragment S W hS hB⟩ : ∃ n U S', N.IsFragment S W U n S')

lemma minIndex_spec (N : Sys X) (S : Set X) (W : Set X) (hS : S ∈ N.F)
    (hB : N.LevelBounded) :
    ∃ U S', N.IsFragment S W U (N.MinIndex S W hS hB) S' := by
  classical
  exact Nat.find_spec (⟨N.τ, S \ W, S, N.sdiff_isFragment S W hS hB⟩ :
    ∃ n U S', N.IsFragment S W U n S')

/-- minimality of MinIndex -/
lemma minIndex_min (N : Sys X) (S : Set X) (W : Set X) (hS : S ∈ N.F)
    (hB : N.LevelBounded) {b : ℕ} (U' : Set X) (S'' : Set X)
    (hfr : N.IsFragment S W U' b S'') :
    N.MinIndex S W hS hB ≤ b := by
  classical
  exact Nat.find_min' (⟨N.τ, S \ W, S, N.sdiff_isFragment S W hS hB⟩ :
    ∃ n U S', N.IsFragment S W U n S') ⟨U', S'', hfr⟩

/-- U is a minimum fragment of (S,W) with index b -/
def MinFragmentAt (N : Sys X) (S : Set X) (W U : Set X) (b : ℕ) (hS : S ∈ N.F)
    (hB : N.LevelBounded) : Prop :=
  b = N.MinIndex S W hS hB ∧ N.HasFragmentAt S W U b ∧
    ∀ U', N.HasFragmentAt S W U' b → U.ncard ≤ U'.ncard

/-- U is a minimum fragment of (S,W) (some index) -/
def MinFragment (N : Sys X) (S : Set X) (W U : Set X) (hS : S ∈ N.F)
    (hB : N.LevelBounded) : Prop :=
  ∃ b, N.MinFragmentAt S W U b hS hB

/-- there exists a minimum fragment of (S,W) at the minimum index -/
lemma exists_min_fragment (N : Sys X) (S : Set X) (W : Set X) (hS : S ∈ N.F)
    (hB : N.LevelBounded) :
    ∃ U : Set X, N.MinFragmentAt S W U (N.MinIndex S W hS hB) hS hB := by
  classical
  rcases N.minIndex_spec S W hS hB with ⟨U₀, S₀, hfr₀⟩
  let b0 : ℕ := N.MinIndex S W hS hB
  let cand : Finset (Set X) := Finset.univ.filter (fun U : Set X => N.HasFragmentAt S W U b0)
  have hne : cand.Nonempty := by
    refine ⟨U₀, ?_⟩
    rw [Finset.mem_filter]
    constructor
    · simp
    · change ∃ S', N.IsFragment S W U₀ b0 S'
      exact ⟨S₀, hfr₀⟩
  let m : ℕ := (cand.image (fun U : Set X => U.ncard)).min' (by
    exact Finset.image_nonempty.2 hne)
  have hm : m ∈ cand.image (fun U : Set X => U.ncard) := Finset.min'_mem _ _
  rcases (Finset.mem_image).1 hm with ⟨U, hU, hUm⟩
  refine ⟨U, ?_⟩
  constructor
  · rfl
  · constructor
    · exact (by simpa [cand] using hU)
    · intro U' hU'
      have hmem' : U'.ncard ∈ cand.image (fun U : Set X => U.ncard) := by
        refine (Finset.mem_image).2 ⟨U', ?_, rfl⟩
        simpa [cand] using hU'
      calc
        U.ncard = m := hUm
        _ ≤ U'.ncard := Finset.min'_le (cand.image (fun U : Set X => U.ncard)) U'.ncard hmem'

/-- a chosen minimum fragment of (S,W) -/
noncomputable def minFrag (N : Sys X) (S : Set X) (W : Set X) (hS : S ∈ N.F)
    (hB : N.LevelBounded) : Set X :=
  Classical.choose (N.exists_min_fragment S W hS hB)

/-- the chosen fragment is a minimum fragment at the minimum index -/
lemma minFrag_spec (N : Sys X) (S : Set X) (W : Set X) (hS : S ∈ N.F)
    (hB : N.LevelBounded) :
    N.MinFragmentAt S W (N.minFrag S W hS hB) (N.MinIndex S W hS hB) hS hB :=
  Classical.choose_spec (N.exists_min_fragment S W hS hB)

/-- minFrag ⊆ S -/
lemma minFrag_subset (N : Sys X) (S : Set X) (W : Set X) (hS : S ∈ N.F)
    (hB : N.LevelBounded) : N.minFrag S W hS hB ⊆ S := by
  rcases (N.minFrag_spec S W hS hB).2.1 with ⟨S', hfr⟩
  exact hfr.2.1

/-- minFrag is a fragment at the min index -/
lemma minFrag_isFragment (N : Sys X) (S : Set X) (W : Set X) (hS : S ∈ N.F)
    (hB : N.LevelBounded) :
    ∃ S', N.IsFragment S W (N.minFrag S W hS hB) (N.MinIndex S W hS hB) S' :=
  (N.minFrag_spec S W hS hB).2.1

/-- a total version of minFrag (∅ if S ∉ F) -/
noncomputable def minFragW (N : Sys X) (W : Set X) (S : Set X)
    (hB : N.LevelBounded) : Set X := by
  classical
  exact if hS : S ∈ N.F then N.minFrag S W hS hB else ∅

/-- the cover of W as a Finset: {minFrag(S,W) : S ∈ F} -/
noncomputable def coverFinset (N : Sys X) (W : Set X) (hB : N.LevelBounded) : Finset (Set X) :=
  N.F.toFinset.image (fun S : Set X => N.minFragW W S hB)

/-- the Finset cover covers F -/
lemma coverFinset_cover (N : Sys X) (W : Set X) (hB : N.LevelBounded) :
    ∀ S ∈ N.F, ∃ U ∈ N.coverFinset W hB, U ⊆ S := by
  intro S hS
  refine ⟨N.minFrag S W hS hB, ?_, N.minFrag_subset S W hS hB⟩
  unfold Sys.coverFinset Sys.minFragW
  refine (Finset.mem_image).2 ⟨S, (Set.mem_toFinset).2 hS, ?_⟩
  simp [Sys.minFrag, hS]

/-- value of the random-set process: sup_{S ∈ 𝓕} of the weight of W∩S -/
noncomputable def procVal (N : Sys X) (W : Set X) : ℝ :=
  famSup (fun S : Set X => N.weight S (W ∩ S)) N.F

/-- good/bad random sets (for threshold θ) -/
def Good (N : Sys X) (θ : ℝ) (W : Set X) : Prop := θ ≤ N.procVal W
def Bad (N : Sys X) (θ : ℝ) (W : Set X) : Prop := N.procVal W < θ

/-- weight of the intersection A ∩ levelSet S j -/
noncomputable def lvlWeight (N : Sys X) (S : Set X) (A : Set X) (j : ℕ) : ℝ :=
  ((A ∩ N.levelSet S j).ncard : ℝ) * wlev j

/-! ## profiles, bounds, uniform averages -/

/-- number of w-subsets -/
noncomputable def numSubsets (n w : ℕ) : ℕ := n.choose w

/-- average of v over the subsets of X of size w (0 if none) -/
noncomputable def avgOver (v : Set X → ℝ) (w : ℕ) : ℝ := by
  classical
  let s : Finset (Set X) := Finset.univ.filter (fun W : Set X => W.ncard = w)
  exact if h : s.Nonempty then (∑ W ∈ s, v W) / (s.card : ℝ) else 0

/-- w = min n ⌊J·n·p⌋ -/
noncomputable def wSize (J n : ℕ) (p : ℝ) : ℕ := min n ⌊(J : ℝ) * (n : ℝ) * p⌋.toNat

/-- legal lower bound for level j -/
noncomputable def legalLower (j : ℕ) : ℝ :=
  max 1 (((q : ℝ) ^ j) / ((q : ℝ) ^ 4 * ((j + 1 : ℝ) ^ 2)))

/-- power of q predicate -/
def IsQPower (m : ℕ) : Prop := ∃ k : ℕ, m = (q : ℕ) ^ k

/-- a single profile entry is legal -/
def LegalEntry (s j : ℕ) : Prop :=
  s = 0 ∨ (IsQPower s ∧ (legalLower j : ℝ) ≤ (s : ℝ) ∧ (s : ℝ) < 2 * (q : ℝ) ^ j)

/-- profile of a member is legal -/
def LegalProfile (N : Sys X) (S : Set X) : Prop :=
  ∀ j : ℕ, j ≤ N.τ → LegalEntry (N.sCount S j) j

/-- every member has total weight ≥ 10^{-8} -/
def TotBound (N : Sys X) : Prop := ∀ S ∈ N.F, (((10 : ℝ) ^ 8)⁻¹) ≤ N.totalWeight S

/-- every member has a legal profile -/
def FLegal (N : Sys X) : Prop := ∀ S ∈ N.F, N.LegalProfile S

/-- all levels bounded (alias) -/
def FBounded (N : Sys X) : Prop := ∀ S ∈ N.F, ∀ i ∈ S, N.lv S i ≤ N.τ

/-- total real weight of S under a general weight function -/
noncomputable def wtot {X : Type*} [Fintype X] (lam : Set X → X → ℝ) (S : Set X) : ℝ := by
  classical
  exact (S.toFinset).sum (fun i : X => lam S i)

end Sys

end Deep
end Sel
end Submission
