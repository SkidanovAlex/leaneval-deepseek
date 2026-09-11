import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.SelCore
import Submission.Deep
import Submission.Multi
import Submission.MultiDeep

/-!
# Multiset deep fragments: partial profiles, fragments, min fragments, cover, procVal.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
open Classical
open MeasureTheory ProbabilityTheory Measure unitInterval Finset
open scoped NNReal ENNReal BigOperators

namespace Submission

open _root_.SupremumOfSelectorProcesses

namespace Multi

open Sel.Deep

variable {X : Type*} [Fintype X]

namespace MSys

/-- supremum of v over the members of the finite family (0 if empty) -/
noncomputable def mSup (v : (X → ℕ) → ℝ) (N : MSys X) : ℝ := by
  classical
  let l : Finset ℝ := N.Fl.image v
  exact if h : l.Nonempty then l.max' h else 0

lemma le_mSup {v : (X → ℕ) → ℝ} (N : MSys X) {S : X → ℕ} (hS : S ∈ N.F) :
    v S ≤ mSup v N := by
  classical
  unfold mSup
  have hS' : S ∈ N.Fl := by simpa using hS
  by_cases h : (N.Fl.image v).Nonempty
  · simp [h]
    exact Finset.le_max' (N.Fl.image v) (v S) (Finset.mem_image.mpr ⟨S, hS', rfl⟩)
  · exfalso
    exact h ⟨v S, Finset.mem_image.mpr ⟨S, hS', rfl⟩⟩

lemma mSup_le_of_forall {v : (X → ℕ) → ℝ} (N : MSys X) {c : ℝ}
    (h : ∀ S ∈ N.F, v S ≤ c) (hc : 0 ≤ c) : mSup v N ≤ c := by
  classical
  unfold mSup
  by_cases hne : (N.Fl.image v).Nonempty
  · have hm : (N.Fl.image v).max' hne ≤ c := by
      apply Finset.max'_le (N.Fl.image v) hne c
      intro y hy
      rcases (Finset.mem_image).1 hy with ⟨S, hS, rfl⟩
      exact h S (by simpa using hS)
    simpa [hne] using hm
  · simp [hne, hc]

lemma mSup_nonneg (N : MSys X) (v : (X → ℕ) → ℝ)
    (hv : ∀ S ∈ N.F, 0 ≤ v S) : 0 ≤ mSup v N := by
  classical
  by_cases hne : N.Fl.Nonempty
  · rcases hne with ⟨S, hS⟩
    exact le_trans (hv S (by simpa using hS)) (le_mSup (v := v) N (by simpa using hS))
  · have hN : N.Fl = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    unfold mSup
    have hl : (N.Fl.image v) = ∅ := by simp [hN]
    by_cases h2 : (N.Fl.image v).Nonempty
    · exact False.elim ((Finset.not_nonempty_iff_eq_empty.mpr hl) h2)
    · simp [h2]

lemma mSup_mono {v w : (X → ℕ) → ℝ} (N : MSys X)
    (h : ∀ S ∈ N.F, v S ≤ w S) (hv : ∀ S ∈ N.F, 0 ≤ v S) : mSup v N ≤ mSup w N := by
  classical
  refine mSup_le_of_forall (v := v) N (c := mSup w N) (fun S hS => ?_) ?_
  · exact (h S hS).trans (le_mSup (v := w) N hS)
  · exact mSup_nonneg N w (fun S hS => (hv S hS).trans (h S hS))

lemma mSup_congr {v w : (X → ℕ) → ℝ} (N : MSys X)
    (h : ∀ S ∈ N.F, v S = w S) : mSup v N = mSup w N := by
  classical
  unfold mSup
  have him : N.Fl.image v = N.Fl.image w := by
    apply Finset.image_congr
    intro S hS
    exact h S (by simpa using hS)
  by_cases h1 : (N.Fl.image v).Nonempty
  · have h2 : (N.Fl.image w).Nonempty := by simpa [him] using h1
    simp [h1, h2, him]
  · have h2 : ¬ (N.Fl.image w).Nonempty := by
      intro hw
      exact h1 (by simpa [him] using hw)
    simp [h1, h2]

/-- partial profile equality up to level b: level-counts agree -/
def ProfileEq (N : MSys X) (S S' : X → ℕ) (b : ℕ) : Prop :=
  ∀ j : ℕ, j ≤ b → N.sCount S j = N.sCount S' j

lemma ProfileEq_refl (N : MSys X) (S : X → ℕ) (b : ℕ) : N.ProfileEq S S b := fun j hj => rfl

/-- 𝓕_{𝓼_b}: members with the same partial profile as S up to level b -/
def FPartialM (N : MSys X) (S : X → ℕ) (b : ℕ) : Set (X → ℕ) :=
  {S' | S' ∈ N.F ∧ N.ProfileEq S S' b}

lemma mem_FPartialM (N : MSys X) {S S' : X → ℕ} {b : ℕ} :
    S' ∈ N.FPartialM S b ↔ S' ∈ N.F ∧ N.ProfileEq S S' b := Iff.rfl

/-- partial-profile members are members -/
lemma FPartialM_mem_F {N : MSys X} {S S' : X → ℕ} {b : ℕ}
    (h : S' ∈ N.FPartialM S b) : S' ∈ N.F := h.1

/-- prefix counts agree on partial-profile members -/
lemma prefixCount_eq_of_FPartial (N : MSys X) {S S' : X → ℕ} {b : ℕ}
    (h : S' ∈ N.FPartialM S b) (c : ℕ) (hc : c ≤ b) :
    N.prefixCount S c = N.prefixCount S' c := by
  unfold prefixCount
  apply Finset.sum_congr rfl
  intro j hj
  exact h.2 j (le_trans (by simpa using hj) hc)

/-- (S,W)-fragment with index b (b ∈ 0..τ), witnessed by S' -/
def IsFragmentM (N : MSys X) (S W U : X → ℕ) (b : ℕ) (S' : X → ℕ) : Prop :=
  S' ∈ N.FPartialM S b ∧
  subM U (subMM S W) ∧
  (∀ j, j ≤ b → subM (N.levM S' j) (addM W U)) ∧
  N.weightAboveM S' (addM W U) b ≥ (100 : ℝ)⁻¹ *
    (N.weightAboveM S' S' b - wlev b * ((N.prefixCount S b : ℝ) - (sizeM U : ℝ)))

lemma IsFragmentM_wit (N : MSys X) {S W U : X → ℕ} {b : ℕ} {S' : X → ℕ}
    (h : N.IsFragmentM S W U b S') : S' ∈ N.FPartialM S b := h.1
lemma IsFragmentM_subM (N : MSys X) {S W U : X → ℕ} {b : ℕ} {S' : X → ℕ}
    (h : N.IsFragmentM S W U b S') : subM U (subMM S W) := h.2.1
lemma IsFragmentM_levM (N : MSys X) {S W U : X → ℕ} {b : ℕ} {S' : X → ℕ}
    (h : N.IsFragmentM S W U b S') : ∀ j, j ≤ b → subM (N.levM S' j) (addM W U) := h.2.2.1
lemma IsFragmentM_weight (N : MSys X) {S W U : X → ℕ} {b : ℕ} {S' : X → ℕ}
    (h : N.IsFragmentM S W U b S') :
    N.weightAboveM S' (addM W U) b ≥ (100 : ℝ)⁻¹ *
      (N.weightAboveM S' S' b - wlev b * ((N.prefixCount S b : ℝ) - (sizeM U : ℝ))) :=
  h.2.2.2

/-- existence of a fragment with index b -/
def HasFragmentAtM (N : MSys X) (S W U : X → ℕ) (b : ℕ) : Prop :=
  ∃ S', N.IsFragmentM S W U b S'

/-- prefixCount S τ ≥ |S∖W| -/
lemma prefixCount_ge_sdiff (N : MSys X) (S W : X → ℕ) (hS : S ∈ N.F)
    (hB : N.LevelBounded) :
    ((N.prefixCount S N.τ : ℝ) - (sizeM (subMM S W) : ℝ)) ≥ 0 := by
  rw [N.prefixCount_eq_sizeM S (hB S hS)]
  have hle : sizeM (subMM S W) ≤ sizeM S := sizeM_subMM_le S W
  exact sub_nonneg.mpr (by exact_mod_cast hle)

/-- S∖W is an (S,W)-fragment at index τ, witnessed by S -/
lemma sdiff_isFragmentM (N : MSys X) (S W : X → ℕ) (hS : S ∈ N.F)
    (hB : N.LevelBounded) :
    N.IsFragmentM S W (subMM S W) N.τ S := by
  constructor
  · constructor
    · exact hS
    · exact N.ProfileEq_refl S N.τ
  · constructor
    · exact subM_refl (subMM S W)
    · constructor
      · intro j hj x
        unfold levM addM subMM
        by_cases h : N.lv S x = j <;> simp [h]
        omega
      · have h0 : N.weightAboveM S (addM W (subMM S W)) N.τ = 0 := by
          exact N.weightAboveM_eq_zero_of_b_ge S (addM W (subMM S W)) N.τ (le_rfl)
        rw [h0]
        have hnonneg : 0 ≤ ((N.prefixCount S N.τ : ℝ) - (sizeM (subMM S W) : ℝ)) :=
          N.prefixCount_ge_sdiff S W hS hB
        have hA : N.weightAboveM S S N.τ = 0 := by
          exact N.weightAboveM_eq_zero_of_b_ge S S N.τ (le_rfl)
        rw [hA]
        have hwx : 0 ≤ wlev N.τ * ((N.prefixCount S N.τ : ℝ) - (sizeM (subMM S W) : ℝ)) :=
          mul_nonneg (wlev_nonneg N.τ) hnonneg
        nlinarith

/-- The min index of fragments of (S,W): least n with a fragment of (S,W) at index n -/
noncomputable def MinIndexM (N : MSys X) (S : X → ℕ) (W : X → ℕ) (hS : S ∈ N.F)
    (hB : N.LevelBounded) : ℕ := by
  classical
  exact Nat.find (⟨N.τ, subMM S W, S, N.sdiff_isFragmentM S W hS hB⟩ :
    ∃ n U S', N.IsFragmentM S W U n S')

lemma minIndexM_spec (N : MSys X) (S : X → ℕ) (W : X → ℕ) (hS : S ∈ N.F)
    (hB : N.LevelBounded) :
    ∃ U S', N.IsFragmentM S W U (N.MinIndexM S W hS hB) S' := by
  classical
  exact Nat.find_spec (⟨N.τ, subMM S W, S, N.sdiff_isFragmentM S W hS hB⟩ :
    ∃ n U S', N.IsFragmentM S W U n S')

/-- minimality of MinIndexM -/
lemma minIndexM_min (N : MSys X) (S : X → ℕ) (W : X → ℕ) (hS : S ∈ N.F)
    (hB : N.LevelBounded) {b : ℕ} (U' : X → ℕ) (S'' : X → ℕ)
    (hfr : N.IsFragmentM S W U' b S'') :
    N.MinIndexM S W hS hB ≤ b := by
  classical
  exact Nat.find_min' (⟨N.τ, subMM S W, S, N.sdiff_isFragmentM S W hS hB⟩ :
    ∃ n U S', N.IsFragmentM S W U n S') ⟨U', S'', hfr⟩

/-- U is a minimum fragment of (S,W) with index b -/
def MinFragmentAtM (N : MSys X) (S W U : X → ℕ) (b : ℕ) (hS : S ∈ N.F)
    (hB : N.LevelBounded) : Prop :=
  b = N.MinIndexM S W hS hB ∧ N.HasFragmentAtM S W U b ∧
    ∀ U', N.HasFragmentAtM S W U' b → sizeM U ≤ sizeM U'

/-- existence of a minimum fragment at the minimum index -/
lemma exists_min_fragmentM (N : MSys X) (S : X → ℕ) (W : X → ℕ) (hS : S ∈ N.F)
    (hB : N.LevelBounded) :
    ∃ U : X → ℕ, N.MinFragmentAtM S W U (N.MinIndexM S W hS hB) hS hB := by
  classical
  rcases N.minIndexM_spec S W hS hB with ⟨U₀, S₀, hfr₀⟩
  let b0 : ℕ := N.MinIndexM S W hS hB
  have hU0b : N.HasFragmentAtM S W U₀ b0 := ⟨S₀, hfr₀⟩
  have hU0le : sizeM U₀ ≤ sizeM S := by
    exact le_trans (sizeM_mono (IsFragmentM_subM (N := N) hfr₀)) (sizeM_subMM_le S W)
  let cand : Finset ℕ := (Finset.range (sizeM S + 1)).filter
    (fun k => ∃ U, N.HasFragmentAtM S W U b0 ∧ sizeM U = k)
  have hne : cand.Nonempty := by
    refine ⟨sizeM U₀, ?_⟩
    rw [Finset.mem_filter]
    constructor
    · exact Finset.mem_range.mpr (by omega)
    · exact ⟨U₀, hU0b, rfl⟩
  let m : ℕ := cand.min' hne
  have hm : m ∈ cand := Finset.min'_mem cand hne
  rcases (Finset.mem_filter).1 hm with ⟨hmr, hw⟩
  rcases hw with ⟨U, hU, hUm⟩
  refine ⟨U, ?_⟩
  constructor
  · rfl
  · constructor
    · exact hU
    · intro U' hU'
      have hU'le : sizeM U' ≤ sizeM S := by
        rcases hU' with ⟨S'', hfr'⟩
        exact le_trans (sizeM_mono (IsFragmentM_subM (N := N) hfr')) (sizeM_subMM_le S W)
      have hmem' : sizeM U' ∈ cand := by
        rw [Finset.mem_filter]
        constructor
        · exact Finset.mem_range.mpr (by omega)
        · exact ⟨U', hU', rfl⟩
      calc
        sizeM U = m := hUm
        _ ≤ sizeM U' := Finset.min'_le cand (sizeM U') hmem'

/-- chosen minimum fragment of (S,W) -/
noncomputable def minFragM (N : MSys X) (S : X → ℕ) (W : X → ℕ) (hS : S ∈ N.F)
    (hB : N.LevelBounded) : X → ℕ :=
  Classical.choose (N.exists_min_fragmentM S W hS hB)

lemma minFragM_spec (N : MSys X) (S : X → ℕ) (W : X → ℕ) (hS : S ∈ N.F)
    (hB : N.LevelBounded) :
    N.MinFragmentAtM S W (N.minFragM S W hS hB) (N.MinIndexM S W hS hB) hS hB :=
  Classical.choose_spec (N.exists_min_fragmentM S W hS hB)

/-- minFrag ⊆ S∖W, in particular ⊆ S -/
lemma minFragM_subM_sdiff (N : MSys X) (S : X → ℕ) (W : X → ℕ) (hS : S ∈ N.F)
    (hB : N.LevelBounded) : subM (N.minFragM S W hS hB) (subMM S W) := by
  rcases (N.minFragM_spec S W hS hB).2.1 with ⟨S', hfr⟩
  exact hfr.2.1

lemma minFragM_subM_S (N : MSys X) (S : X → ℕ) (W : X → ℕ) (hS : S ∈ N.F)
    (hB : N.LevelBounded) : subM (N.minFragM S W hS hB) S := by
  exact subM_trans (N.minFragM_subM_sdiff S W hS hB) (subM_subMM (m := S) (m' := W))

/-- minFrag is a fragment at the min index -/
lemma minFragM_isFragmentM (N : MSys X) (S : X → ℕ) (W : X → ℕ) (hS : S ∈ N.F)
    (hB : N.LevelBounded) :
    ∃ S', N.IsFragmentM S W (N.minFragM S W hS hB) (N.MinIndexM S W hS hB) S' :=
  (N.minFragM_spec S W hS hB).2.1

/-- value of the random-multiset process: sup_{S∈F} of the weight of W∧S -/
noncomputable def procValM (N : MSys X) (W : X → ℕ) : ℝ :=
  mSup (fun S : X → ℕ => N.weightM S W) N

/-- good/bad multisets (threshold θ) -/
def GoodM (N : MSys X) (θ : ℝ) (W : X → ℕ) : Prop := θ ≤ N.procValM W
def BadM (N : MSys X) (θ : ℝ) (W : X → ℕ) : Prop := N.procValM W < θ

/-- total weight ≥ 10^{-8} for every member -/
def TotBoundM (N : MSys X) : Prop := ∀ S ∈ N.F, ((10 : ℝ) ^ 8)⁻¹ ≤ N.totalWeightM S

/-- every member has a legal profile -/
def FLegalM (N : MSys X) : Prop := ∀ S ∈ N.F, ∀ j : ℕ, j ≤ N.τ → Sel.Deep.Sys.LegalEntry (N.sCount S j) j

/-- every member has every level bounded -/
def FBoundedM (N : MSys X) : Prop := ∀ S ∈ N.F, ∀ x : X, N.lv S x ≤ N.τ

/-- the cover of W as a Finset: {minFragM(S,W) : S ∈ F} -/
noncomputable def coverFinsetM (N : MSys X) (W : X → ℕ) (hB : N.LevelBounded) : Finset (X → ℕ) :=
  N.Fl.image (fun S : X → ℕ => if hS : S ∈ N.F then N.minFragM S W hS hB else fun _ => 0)

/-- the Finset cover covers F -/
lemma coverFinsetM_cover (N : MSys X) (W : X → ℕ) (hB : N.LevelBounded) :
    ∀ S ∈ N.F, ∃ U ∈ N.coverFinsetM W hB, subM U S := by
  intro S hS
  refine ⟨N.minFragM S W hS hB, ?_, N.minFragM_subM_S S W hS hB⟩
  unfold coverFinsetM
  refine (Finset.mem_image).2 ⟨S, by simpa using hS, ?_⟩
  simp [hS]

/-- total cost of the min-fragment cover of W -/
noncomputable def coverCostM (N : MSys X) (c : ℝ) (p : X → ℝ) (W : X → ℕ)
    (hB : N.LevelBounded) : ℝ :=
  mTotalCost c p (N.coverFinsetM W hB)

end MSys

end Multi
end Submission
