import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.Prob
import Submission.PVCore

open ProbabilityTheory MeasureTheory unitInterval Set
open scoped ENNReal NNReal BigOperators unitInterval ProbabilityTheory
open FractionalExpectationThresholds
open Submission.PVC

attribute [local instance] Classical.propDecidable

/-!
# Basic API for covers, costs and fragments

All statements are about a finite universe `X`; families are sets of subsets of `X`.
Prove each of the lemmas below.  You may add private helper lemmas.
-/

namespace Submission
namespace PVAPI

universe u
variable {X : Type u} [Fintype X]

/-- membership in the upward closure. -/
lemma mem_Up {H : Set (Set X)} {Y : Set X} : Y ∈ Up H ↔ ∃ S ∈ H, S ⊆ Y := by rfl

/-- the upward closure is an upper set. -/
lemma Up_upper (H : Set (Set X)) : IsUpperSet (Up H) := by
  intro A B hAB hA
  rcases hA with ⟨S, hS, hSA⟩
  exact ⟨S, hS, le_trans hSA hAB⟩

/-- upward closure is monotone in the family. -/
lemma Up_mono {H₁ H₂ : Set (Set X)} (h : H₁ ⊆ H₂) : Up H₁ ⊆ Up H₂ := by
  intro Y hY
  rcases hY with ⟨S, hS, hSY⟩
  exact ⟨S, h hS, hSY⟩

/-- the empty family has empty upward closure. -/
lemma Up_empty : Up (∅ : Set (Set X)) = ∅ := by
  ext Y
  simp [Up]

/-- each member lies in the upward closure of its family. -/
lemma self_mem_Up {H : Set (Set X)} {S : Set X} (hS : S ∈ H) : S ∈ Up H := by
  exact (mem_Up.mpr ⟨S, hS, subset_rfl⟩)

/-- `G` covers `H` iff `H ⊆ Up G`. -/
lemma covers_iff_subset_Up {G H : Set (Set X)} : Covers G H ↔ H ⊆ Up G := by
  constructor
  · intro hC Y hY
    exact (mem_Up.mpr (hC Y hY))
  · intro hSub Y hY
    exact (mem_Up.mp (hSub hY))

/-- cost is nonnegative when `q` is. -/
lemma ecost_nonneg {q : ℝ} (hq : 0 ≤ q) (G : Set (Set X)) : 0 ≤ ecost q G := by
  unfold ecost
  exact Finset.sum_nonneg (by
    intro S hS
    by_cases hSG : S ∈ G <;> simp [hSG, pow_nonneg hq])

/-- cost is monotone in the family when `q ≥ 0`. -/
lemma ecost_mono {q : ℝ} (hq : 0 ≤ q) {G₁ G₂ : Set (Set X)} (h : G₁ ⊆ G₂) :
    ecost q G₁ ≤ ecost q G₂ := by
  unfold ecost
  apply Finset.sum_le_sum
  intro S hS
  by_cases h1 : S ∈ G₁
  · have h2 : S ∈ G₂ := h h1
    simp [h1, h2]
  · by_cases h2 : S ∈ G₂
    · simp [h1, h2, pow_nonneg hq]
    · simp [h1, h2]

/-- cost of the union is at most the sum of the costs. -/
lemma ecost_union_le {q : ℝ} (hq : 0 ≤ q) (G₁ G₂ : Set (Set X)) :
    ecost q (G₁ ∪ G₂) ≤ ecost q G₁ + ecost q G₂ := by
  unfold ecost
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro S hS
  by_cases h1 : S ∈ G₁
  · by_cases h2 : S ∈ G₂
    · have h3 : S ∈ G₁ ∪ G₂ := by simp [h1]
      simp [h1, h2, h3]
      linarith [pow_nonneg hq (S.ncard)]
    · have h3 : S ∈ G₁ ∪ G₂ := by simp [h1]
      simp [h1, h2, h3]
  · by_cases h2 : S ∈ G₂
    · have h3 : S ∈ G₁ ∪ G₂ := by simp [h2]
      simp [h1, h2, h3]
    · simp [h1, h2]

/-- cost of the empty family is zero. -/
lemma ecost_empty (q : ℝ) : ecost q (∅ : Set (Set X)) = 0 := by
  unfold ecost
  simp

/-- cost of a singleton is the monomial. -/
lemma ecost_singleton (q : ℝ) (S : Set X) : ecost q ({S} : Set (Set X)) = q ^ S.ncard := by
  classical
  calc
    ecost q ({S} : Set (Set X)) = ∑ T : Set X, if T = S then q ^ T.ncard else 0 := by
      unfold ecost
      apply Finset.sum_congr rfl
      intro T hT
      by_cases h : T = S <;> simp [h, Set.mem_singleton_iff]
    _ = q ^ S.ncard := by
      rw [Finset.sum_ite_eq' (s := (Finset.univ : Finset (Set X))) (a := S)
        (b := fun T : Set X => q ^ T.ncard)]
      simp

/-- cost of a family inside a singleton. -/
lemma ecost_le_singleton {q : ℝ} (hq : 0 ≤ q) {G : Set (Set X)} {S : Set X} (h : G ⊆ {S}) :
    ecost q G ≤ q ^ S.ncard := by
  calc
    ecost q G ≤ ecost q ({S} : Set (Set X)) := ecost_mono hq h
    _ = q ^ S.ncard := ecost_singleton q S

/-- a family covers itself. -/
lemma covers_self (H : Set (Set X)) : Covers H H := by
  intro S hS
  exact ⟨S, hS, subset_rfl⟩

/-- a subfamily covers the superfamily. -/
lemma covers_of_subset {G₁ G₂ : Set (Set X)} (h : G₂ ⊆ G₁) : Covers G₁ G₂ := by
  intro S hS
  exact ⟨S, h hS, subset_rfl⟩

/-- finiteness of the set of achievable cover-costs of a family. -/
private lemma finite_cover_costs (q : ℝ) (H : Set (Set X)) :
    ({a : ℝ | ∃ G : Set (Set X), Covers G H ∧ ecost q G = a}).Finite := by
  classical
  let s : Set ℝ := {a | ∃ G : Set (Set X), Covers G H ∧ ecost q G = a}
  change s.Finite
  have hsub : s ⊆ Set.range (fun G : Set (Set X) => ecost q G) := by
    intro a ha
    rcases ha with ⟨G, hC, ha'⟩
    exact ⟨G, ha'⟩
  exact (Set.finite_range (fun G : Set (Set X) => ecost q G)).subset hsub

/-- the minimal cover cost is at most the cost of any cover. -/
lemma ccost_le_ecost {q : ℝ} {G H : Set (Set X)} (h : Covers G H) : ccost q H ≤ ecost q G := by
  classical
  unfold ccost
  let s : Set ℝ := {a | ∃ G' : Set (Set X), Covers G' H ∧ ecost q G' = a}
  change sInf s ≤ ecost q G
  exact csInf_le (finite_cover_costs q H).bddBelow ⟨G, h, rfl⟩

/-- minimal cover cost is monotone in the family (for `0 ≤ q ≤ 1` if needed). -/
lemma ccost_mono {q : ℝ} {H₁ H₂ : Set (Set X)} (h : H₁ ⊆ H₂) : ccost q H₁ ≤ ccost q H₂ := by
  classical
  unfold ccost
  let s1 : Set ℝ := {a | ∃ G : Set (Set X), Covers G H₁ ∧ ecost q G = a}
  let s2 : Set ℝ := {a | ∃ G : Set (Set X), Covers G H₂ ∧ ecost q G = a}
  change sInf s1 ≤ sInf s2
  have hsub : s2 ⊆ s1 := by
    intro a ha
    rcases ha with ⟨G, hC, ha'⟩
    refine ⟨G, ?_, ha'⟩
    intro S hS
    exact hC S (h hS)
  have hnon : s2.Nonempty := by
    refine ⟨ecost q H₂, H₂, covers_self H₂, rfl⟩
  exact csInf_le_csInf (s := s2) (t := s1) (finite_cover_costs q H₁).bddBelow hnon hsub

/-- if every cover of `H` has cost at least `c`, then `c ≤ ccost q H`. -/
lemma ccost_ge_of_forall_covers {q c : ℝ} {H : Set (Set X)}
    (h : ∀ G : Set (Set X), Covers G H → c ≤ ecost q G) : c ≤ ccost q H := by
  classical
  unfold ccost
  let s : Set ℝ := {a | ∃ G : Set (Set X), Covers G H ∧ ecost q G = a}
  change c ≤ sInf s
  apply le_csInf
  · refine ⟨ecost q H, H, covers_self H, rfl⟩
  · intro a ha
    rcases ha with ⟨G, hC, ha'⟩
    rw [← ha']
    exact h G hC

/-- membership in fragments. -/
lemma mem_Frag {H : Set (Set X)} {W : Set X} {F : Set X} :
    F ∈ Frag H W ↔ ∃ S ∈ H, F = S \ W := by rfl

/-- fragments are monotone in the family. -/
lemma Frag_mono {H₁ H₂ : Set (Set X)} {W : Set X} (h : H₁ ⊆ H₂) : Frag H₁ W ⊆ Frag H₂ W := by
  intro F hF
  rcases (mem_Frag.mp hF) with ⟨S, hS, hF'⟩
  exact (mem_Frag.mpr ⟨S, h hS, hF'⟩)

/-- every minimal fragment is a fragment. -/
lemma FStar_subset_Frag {H : Set (Set X)} {W : Set X} : FStar H W ⊆ Frag H W := by
  intro F hF
  exact hF.1

/-- large fragments are minimal fragments. -/
lemma Lm_subset_FStar {H : Set (Set X)} {W : Set X} {m : ℕ} : Lm H W m ⊆ FStar H W := by
  intro F hF
  exact hF.1

/-- small fragments are minimal fragments. -/
lemma Sm_subset_FStar {H : Set (Set X)} {W : Set X} {m : ℕ} : Sm H W m ⊆ FStar H W := by
  intro F hF
  exact hF.1

/-- a minimal fragment contains no other fragment strictly. -/
lemma IsMinFrag.minimal {H : Set (Set X)} {W : Set X} {F G : Set X} (hF : IsMinFrag H W F)
    (hG : G ∈ Frag H W) (hGF : G ⊆ F) : G = F := hF.2 G hG hGF

/-- a fragment of a member of `H` is a subset of that member. -/
lemma frag_subset_mem {H : Set (Set X)} {W F : Set X} (hF : F ∈ Frag H W) :
    ∃ S ∈ H, F ⊆ S := by
  rcases (mem_Frag.mp hF) with ⟨S, hS, hF'⟩
  refine ⟨S, hS, ?_⟩
  rw [hF']
  exact Set.sdiff_subset

/-- minimal fragments partition into large and small. -/
lemma FStar_eq_union {H : Set (Set X)} {W : Set X} {m : ℕ} :
    FStar H W = Lm H W m ∪ Sm H W m := by
  ext F
  constructor
  · intro hF
    by_cases hm : m ≤ F.ncard
    · exact Or.inl ⟨hF, hm⟩
    · exact Or.inr ⟨hF, Nat.lt_of_not_ge hm⟩
  · intro hF
    rcases hF with hL | hS
    · exact hL.1
    · exact hS.1

/-- if `F ∈ Sm H W m` then `F.ncard < m`. -/
lemma Sm_mem_ncard_lt {H : Set (Set X)} {W : Set X} {m : ℕ} {F : Set X} (hF : F ∈ Sm H W m) :
    F.ncard < m := hF.2

/-- small fragments are small: a subset of the underlying member. -/
lemma Sm_mem_frag {H : Set (Set X)} {W : Set X} {m : ℕ} {F : Set X} (hF : F ∈ Sm H W m) :
    F ∈ Frag H W := FStar_subset_Frag (Sm_subset_FStar hF)

/-- for any member `S` of `H`, there is a minimal fragment contained in `S ∖ W`. -/
lemma exists_minFrag_subset {H : Set (Set X)} {W S : Set X} (hS : S ∈ H) :
    ∃ F, IsMinFrag H W F ∧ F ⊆ S \ W := by
  classical
  let C : Finset (Set X) := Finset.univ.filter (fun F : Set X => F ∈ Frag H W ∧ F ⊆ S \ W)
  have hSC : S \ W ∈ C := by
    rw [Finset.mem_filter]
    constructor
    · simp
    · constructor
      · exact mem_Frag.mpr ⟨S, hS, rfl⟩
      · exact subset_rfl
  obtain ⟨M, hMC, hmin⟩ := Finset.exists_min_image C (fun F : Set X => F.ncard) ⟨S \ W, hSC⟩
  have hM : M ∈ Frag H W ∧ M ⊆ S \ W := (Finset.mem_filter.mp hMC).2
  refine ⟨M, ?_, hM.2⟩
  constructor
  · exact hM.1
  · intro G hG hGM
    have hGC : G ∈ C := by
      rw [Finset.mem_filter]
      exact ⟨by simp, hG, subset_trans hGM hM.2⟩
    have h1 : M.ncard ≤ G.ncard := hmin G hGC
    exact Set.eq_of_subset_of_ncard_le hGM h1

/-- if `G` covers all minimal fragments of `H` relative to `W`, then `G` covers `H`. -/
lemma Covers_of_covers_FStar {G H : Set (Set X)} {W : Set X} (h : Covers G (FStar H W)) :
    Covers G H := by
  intro S hS
  rcases exists_minFrag_subset (H := H) (W := W) (S := S) hS with ⟨F, hFmin, hFsub⟩
  have hFStar : F ∈ FStar H W := hFmin
  rcases h F hFStar with ⟨T, hTG, hTF⟩
  refine ⟨T, hTG, ?_⟩
  exact subset_trans hTF (subset_trans hFsub Set.sdiff_subset)

/-- if `G` covers `H` and also covers `L`, it covers `H ∪ L`. -/
lemma Covers_union {G H L : Set (Set X)} (hH : Covers G H) (hL : Covers G L) :
    Covers G (H ∪ L) := by
  intro S hS
  rcases hS with hSH | hSL
  · exact hH S hSH
  · exact hL S hSL

/-- minimal cover cost is bounded below by cost of a subfamily restriction argument.
Given `Covers G (FStar H W) → Covers G H`, we get `ccost q H ≤ ccost q (FStar H W)`. -/
lemma ccost_le_ccost_FStar {q : ℝ} {H : Set (Set X)} {W : Set X} :
    ccost q H ≤ ccost q (FStar H W) := by
  classical
  unfold ccost
  let sH : Set ℝ := {a | ∃ G : Set (Set X), Covers G H ∧ ecost q G = a}
  let sF : Set ℝ := {a | ∃ G : Set (Set X), Covers G (FStar H W) ∧ ecost q G = a}
  change sInf sH ≤ sInf sF
  have hsub : sF ⊆ sH := by
    intro a ha
    rcases ha with ⟨G, hC, ha'⟩
    refine ⟨G, ?_, ha'⟩
    exact Covers_of_covers_FStar (G := G) (H := H) (W := W) hC
  have hnon : sF.Nonempty := by
    refine ⟨ecost q (FStar H W), FStar H W, covers_self (FStar H W), rfl⟩
  exact csInf_le_csInf (s := sF) (t := sH) (finite_cover_costs q H).bddBelow hnon hsub

/-- if `∅ ∈ Sm H W m` (i.e. an empty minimal fragment) then `W` contains a member of `H`. -/
lemma hit_of_empty_frag {H : Set (Set X)} {W : Set X} {m : ℕ}
    (hemp : (∅ : Set X) ∈ Sm H W m) : ∃ S ∈ H, S ⊆ W := by
  classical
  have hsm : IsMinFrag H W (∅ : Set X) ∧ (∅ : Set X).ncard < m := by
    simpa [Sm] using hemp
  rcases (mem_Frag.mp hsm.1.1) with ⟨S, hS, hFW⟩
  refine ⟨S, hS, ?_⟩
  exact (Set.sdiff_eq_empty.mp hFW.symm)

/-- subadditivity of the minimal cover cost (for `0 ≤ q`). -/
lemma ccost_subadd {q : ℝ} (hq : 0 ≤ q) (H₁ H₂ : Set (Set X)) :
    ccost q (H₁ ∪ H₂) ≤ ccost q H₁ + ccost q H₂ := by
  classical
  let S₁ : Set ℝ := {a | ∃ G : Set (Set X), Covers G H₁ ∧ ecost q G = a}
  let S₂ : Set ℝ := {a | ∃ G : Set (Set X), Covers G H₂ ∧ ecost q G = a}
  have hcore : ∀ a ∈ S₁, ∀ b ∈ S₂, ccost q (H₁ ∪ H₂) ≤ a + b := by
    intro a ha b hb
    rcases ha with ⟨G₁, hC₁, rfl⟩
    rcases hb with ⟨G₂, hC₂, rfl⟩
    have hC₁' : Covers (G₁ ∪ G₂) H₁ := by
      intro S hS
      rcases hC₁ S hS with ⟨T, hT, hTS⟩
      exact ⟨T, Or.inl hT, hTS⟩
    have hC₂' : Covers (G₁ ∪ G₂) H₂ := by
      intro S hS
      rcases hC₂ S hS with ⟨T, hT, hTS⟩
      exact ⟨T, Or.inr hT, hTS⟩
    have hC : Covers (G₁ ∪ G₂) (H₁ ∪ H₂) := Covers_union hC₁' hC₂'
    calc
      ccost q (H₁ ∪ H₂) ≤ ecost q (G₁ ∪ G₂) := ccost_le_ecost hC
      _ ≤ ecost q G₁ + ecost q G₂ := ecost_union_le hq G₁ G₂
  have hstep2 : ∀ a ∈ S₁, ∀ b ∈ S₂, ccost q (H₁ ∪ H₂) - a ≤ b := by
    intro a ha b hb
    have h := hcore a ha b hb
    linarith
  have hstep1 : ∀ a ∈ S₁, ccost q (H₁ ∪ H₂) - a ≤ sInf S₂ := by
    intro a ha
    apply le_csInf
    · exact ⟨ecost q H₂, H₂, covers_self H₂, rfl⟩
    · intro b hb
      exact hstep2 a ha b hb
  have hfin : ccost q (H₁ ∪ H₂) - sInf S₂ ≤ sInf S₁ := by
    apply le_csInf
    · exact ⟨ecost q H₁, H₁, covers_self H₁, rfl⟩
    · intro a ha
      have h := hstep1 a ha
      linarith
  change ccost q (H₁ ∪ H₂) ≤ sInf S₁ + sInf S₂
  linarith

/-- minimal cover cost of the empty family is zero (for `0 ≤ q`). -/
lemma ccost_empty {q : ℝ} (hq : 0 ≤ q) : ccost q (∅ : Set (Set X)) = 0 := by
  classical
  unfold ccost
  apply le_antisymm
  · apply csInf_le (finite_cover_costs q (∅ : Set (Set X))).bddBelow
    refine ⟨(∅ : Set (Set X)), ?_, ?_⟩
    · intro S hS
      simp at hS
    · simp [ecost]
  · apply le_csInf
    · refine ⟨0, (∅ : Set (Set X)), ?_, ?_⟩
      · intro S hS
        simp at hS
      · simp [ecost]
    · intro a ha
      rcases ha with ⟨G, hC, rfl⟩
      exact ecost_nonneg hq G

/-- if `∅ ∈ H` then every cover has cost at least `1`, so the minimal cost is at least 1
(for `0 ≤ q`). -/
lemma ccost_ge_one_of_mem_empty {q : ℝ} (hq : 0 ≤ q) {H : Set (Set X)} (hemp : (∅ : Set X) ∈ H) :
    1 ≤ ccost q H := by
  apply ccost_ge_of_forall_covers
  intro G hG
  rcases hG (∅ : Set X) hemp with ⟨T, hT, hTempty⟩
  have hT0 : T = ∅ := by
    apply Subset.antisymm hTempty
    intro x hx
    simp at hx
  have hmem0 : (∅ : Set X) ∈ G := by simpa [hT0] using hT
  unfold ecost
  simpa [hmem0] using (Finset.single_le_sum
    (s := (Finset.univ : Finset (Set X)))
    (f := fun S : Set X => if S ∈ G then q ^ S.ncard else 0)
    (by intro S hS; by_cases hGS : S ∈ G <;> simp [hGS, pow_nonneg hq])
    (Finset.mem_univ (∅ : Set X)))

end PVAPI
end Submission
