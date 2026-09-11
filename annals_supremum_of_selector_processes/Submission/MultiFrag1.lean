import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.SelCore
import Submission.Deep
import Submission.Multi
import Submission.MultiDeep
import Submission.MultiDeep2

/-!
# Multiset fragment structure (obs.T-multi and consequences)
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

/-- countAt is unchanged by removing a loose copy of x from U (per-coordinate) -/
lemma countAt_addM_eraseOne_tight (N : MSys X) {S' W U : X → ℕ} {j : ℕ} (x : X)
    (hx : S' x ≤ W x + U x - 1) :
    N.countAt S' (addM W U) j = N.countAt S' (addM W (eraseOne U x)) j := by
  classical
  unfold countAt
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hyx : y = x
  · subst y
    have hmin : min (W x + U x) (S' x) = min (W x + (U x - 1)) (S' x) := by omega
    by_cases hlv : N.lv S' x = j <;> simp [hlv, hmin, eraseOne, addM]
  · have hE : eraseOne U x y = U y := eraseOne_other U (x := x) hyx
    simp [hE, addM]

/-- removing a loose copy of x keeps the weight inequality (with |U'| = t − 1) -/
lemma eraseOne_weight_tight (N : MSys X) {S W U S' : X → ℕ} {b : ℕ} (x : X)
    (hxU : 1 ≤ U x)
    (h2 : N.weightAboveM S' (addM W U) b ≥ (100 : ℝ)⁻¹ *
        (N.weightAboveM S' S' b - wlev b * ((N.prefixCount S b : ℝ) - (sizeM U : ℝ))))
    (hx : S' x ≤ W x + U x - 1) :
    N.weightAboveM S' (addM W (eraseOne U x)) b ≥ (100 : ℝ)⁻¹ *
        (N.weightAboveM S' S' b - wlev b * ((N.prefixCount S b : ℝ) - (sizeM (eraseOne U x) : ℝ))) := by
  classical
  have hEq : N.weightAboveM S' (addM W U) b = N.weightAboveM S' (addM W (eraseOne U x)) b := by
    apply N.weightAboveM_congr_of_countAt
    intro j
    exact countAt_addM_eraseOne_tight N (S' := S') (W := W) (U := U) (j := j) x hx
  have hsU : (sizeM (eraseOne U x) : ℝ) + 1 = (sizeM U : ℝ) := by
    exact_mod_cast (sizeM_eraseOne_add U x hxU)
  have htarget : (100 : ℝ)⁻¹ * (N.weightAboveM S' S' b - wlev b *
        ((N.prefixCount S b : ℝ) - (sizeM (eraseOne U x) : ℝ))) ≤
      (100 : ℝ)⁻¹ * (N.weightAboveM S' S' b - wlev b * ((N.prefixCount S b : ℝ) - (sizeM U : ℝ))) := by
    have hsub2 : (N.prefixCount S b : ℝ) - (sizeM (eraseOne U x) : ℝ) =
        (N.prefixCount S b : ℝ) - (sizeM U : ℝ) + 1 := by
      linarith
    rw [hsub2]
    have hw0 : 0 ≤ wlev b := wlev_nonneg b
    nlinarith
  rw [← hEq]
  exact le_trans htarget h2

/-- feasibility of S' for (S, W + U) at level b (fragment without the U ⊆ S∖W clause) -/
def FeasibleM (N : MSys X) (S W U : X → ℕ) (b : ℕ) (S' : X → ℕ) : Prop :=
  S' ∈ N.FPartialM S b ∧
  (∀ j, j ≤ b → subM (N.levM S' j) (addM W U)) ∧
  N.weightAboveM S' (addM W U) b ≥ (100 : ℝ)⁻¹ *
    (N.weightAboveM S' S' b - wlev b * ((N.prefixCount S b : ℝ) - (sizeM U : ℝ)))

lemma IsFragmentM_feasible (N : MSys X) {S W U : X → ℕ} {b : ℕ} {S' : X → ℕ}
    (h : N.IsFragmentM S W U b S') : N.FeasibleM S W U b S' := by
  rcases h with ⟨h1, h2, h3, h4⟩
  exact ⟨h1, h3, h4⟩

/-- removing a loose copy of x preserves feasibility -/
lemma feasible_eraseOne_tight (N : MSys X) {S W U S' : X → ℕ} {b : ℕ}
    (hfe : N.FeasibleM S W U b S') (x : X) (hxU : 1 ≤ U x) (hx : S' x ≤ W x + U x - 1) :
    N.FeasibleM S W (eraseOne U x) b S' := by
  classical
  rcases hfe with ⟨hF, h1, h2⟩
  constructor
  · exact hF
  · constructor
    · intro j hj y
      by_cases hy : y = x
      · subst y
        have h1' := h1 j hj x
        have hle0 : N.levM S' j x ≤ S' x := N.levM_subM S' j x
        calc
          N.levM S' j x ≤ S' x := hle0
          _ ≤ W x + U x - 1 := hx
          _ = W x + (U x - 1) := by omega
          _ = addM W (eraseOne U x) x := by simp [eraseOne, addM]
      · have hU' : eraseOne U x y = U y := eraseOne_other U (x := x) hy
        simpa [hU', addM] using (h1 j hj y)
    · exact eraseOne_weight_tight N x hxU h2 hx

/-- removing a loose copy of x preserves the fragment -/
lemma isFragmentM_eraseOne_tight (N : MSys X) {S W U S' : X → ℕ} {b : ℕ}
    (hfr : N.IsFragmentM S W U b S') (x : X) (hxU : 1 ≤ U x) (hx : S' x ≤ W x + U x - 1) :
    N.IsFragmentM S W (eraseOne U x) b S' := by
  classical
  rcases hfr with ⟨hF, hUsub, h1, h2⟩
  constructor
  · exact hF
  · constructor
    · intro y
      by_cases hy : y = x
      · subst y
        have hU := hUsub x
        unfold subMM at hU
        rw [eraseOne_self]
        rw [subMM]
        exact le_trans (Nat.sub_le (U x) 1) hU
      · have hE : eraseOne U x y = U y := eraseOne_other U (x := x) hy
        simpa [hE] using hUsub y
    · constructor
      · intro j hj y
        by_cases hy : y = x
        · subst y
          have h1' := h1 j hj x
          have hle0 : N.levM S' j x ≤ S' x := N.levM_subM S' j x
          calc
            N.levM S' j x ≤ S' x := hle0
            _ ≤ W x + U x - 1 := hx
            _ = W x + (U x - 1) := by omega
            _ = addM W (eraseOne U x) x := by simp [eraseOne, addM]
        · have hU' : eraseOne U x y = U y := eraseOne_other U (x := x) hy
          simpa [hU', addM] using (h1 j hj y)
      · exact eraseOne_weight_tight N x hxU h2 hx

/-! ## erasure when x is not in the prefix of S' (levels ≤ b) -/

/-- fragment2 inequality after a lossy erasure (loss ≤ wlev(b+1)) -/
lemma frag_weightM_erase (N : MSys X) {S S' W U : X → ℕ} {b : ℕ} (x : X) (hxU : 1 ≤ U x)
    (hfr2 : N.weightAboveM S' (addM W U) b ≥ (100 : ℝ)⁻¹ *
        (N.weightAboveM S' S' b - wlev b * ((N.prefixCount S b : ℝ) - (sizeM U : ℝ))))
    (hloss : N.weightAboveM S' (addM W U) b - N.weightAboveM S' (addM W (eraseOne U x)) b ≤ wlev (b + 1)) :
    N.weightAboveM S' (addM W (eraseOne U x)) b ≥ (100 : ℝ)⁻¹ *
        (N.weightAboveM S' S' b - wlev b * ((N.prefixCount S b : ℝ) - (sizeM (eraseOne U x) : ℝ))) := by
  classical
  have hs : sizeM (eraseOne U x) + 1 = sizeM U := sizeM_eraseOne_add U x hxU
  have hws : wlev (b + 1) = (100 : ℝ)⁻¹ * wlev b := by
    rw [wlev_succ]
    norm_num
  have hsub : (N.prefixCount S b : ℝ) - (sizeM (eraseOne U x) : ℝ) =
      (N.prefixCount S b : ℝ) - (sizeM U : ℝ) + 1 := by
    have hsR : (sizeM (eraseOne U x) : ℝ) + 1 = (sizeM U : ℝ) := by exact_mod_cast hs
    linarith
  have hA : (100 : ℝ)⁻¹ * (N.weightAboveM S' S' b - wlev b *
        ((N.prefixCount S b : ℝ) - (sizeM U : ℝ))) - wlev (b + 1) ≤
      N.weightAboveM S' (addM W U) b - wlev (b + 1) := by
    exact sub_le_sub_right hfr2 (wlev (b + 1))
  have hB : N.weightAboveM S' (addM W U) b - wlev (b + 1) ≤
      N.weightAboveM S' (addM W (eraseOne U x)) b := by
    linarith
  calc
    N.weightAboveM S' (addM W (eraseOne U x)) b ≥
        (100 : ℝ)⁻¹ * (N.weightAboveM S' S' b - wlev b *
          ((N.prefixCount S b : ℝ) - (sizeM U : ℝ))) - wlev (b + 1) := by
          exact le_trans hA hB
    _ = (100 : ℝ)⁻¹ * (N.weightAboveM S' S' b - wlev b *
          ((N.prefixCount S b : ℝ) - (sizeM (eraseOne U x) : ℝ))) := by
          rw [hws, hsub]
          ring

/-- addM distributes over eraseOne when the erased copy exists -/
lemma eraseOne_addM (W U : X → ℕ) (x : X) (hx : 1 ≤ U x) :
    eraseOne (addM W U) x = addM W (eraseOne U x) := by
  funext y
  by_cases hy : y = x
  · subst y
    simp [eraseOne, addM]
    omega
  · simp [eraseOne, addM, hy]

/-- erase a copy of x whose level is above b: the fragment is preserved -/
lemma isFragmentM_eraseOne_high (N : MSys X) {S W U S' : X → ℕ} {b : ℕ}
    (hfr : N.IsFragmentM S W U b S') (x : X) (hxU : 1 ≤ U x) (j0 : ℕ)
    (hxlev : N.lv S' x = j0) (hbj : b < j0) :
    N.IsFragmentM S W (eraseOne U x) b S' := by
  classical
  rcases hfr with ⟨hF, hUsub, h1, h2⟩
  constructor
  · exact hF
  · constructor
    · intro y
      by_cases hy : y = x
      · subst y
        have hU := hUsub x
        unfold subMM at hU
        rw [eraseOne_self]
        rw [subMM]
        exact le_trans (Nat.sub_le (U x) 1) hU
      · have hE : eraseOne U x y = U y := eraseOne_other U (x := x) hy
        simpa [hE] using hUsub y
    · constructor
      · intro j hj y
        by_cases hy : y = x
        · subst y
          have hnot : N.lv S' x ≠ j := by omega
          have hz : N.levM S' j x = 0 := levM_eq_zero_of_lv_ne N S' j hnot
          rw [hz]
          exact Nat.zero_le _
        · have hU' : eraseOne U x y = U y := eraseOne_other U (x := x) hy
          simpa [hU', addM] using (h1 j hj y)
      · have hE : eraseOne (addM W U) x = addM W (eraseOne U x) := eraseOne_addM W U x hxU
        have hloss0 : N.weightAboveM S' (addM W U) b ≤
            N.weightAboveM S' (eraseOne (addM W U) x) b + wlev j0 :=
          N.weightAboveM_eraseOne_le (S' := S') (A := addM W U) (b := b) (j0 := j0) x hxlev
        have hw : wlev j0 ≤ wlev (b + 1) := wlev_le_of_le (by omega)
        have hloss : N.weightAboveM S' (addM W U) b - N.weightAboveM S' (addM W (eraseOne U x)) b ≤ wlev (b + 1) := by
          rw [hE] at hloss0
          linarith
        exact frag_weightM_erase N x hxU h2 hloss

/-! ## min-fragment consequences -/

/-- prefixM S' b ⊆ W + U from fragment1 -/
lemma prefixM_subM_addM_of_fragment1 (N : MSys X) {S' W U : X → ℕ} {b : ℕ}
    (h1 : ∀ j, j ≤ b → subM (N.levM S' j) (addM W U)) :
    subM (N.prefixM S' b) (addM W U) := by
  intro x
  by_cases hb : N.lv S' x ≤ b
  · rw [prefixM_pointwise]
    have hsub := h1 (N.lv S' x) hb x
    have hz : N.levM S' (N.lv S' x) x = S' x := by rw [levM_pos_of_lv_eq N S' (N.lv S' x) rfl]
    simp [hb, hz] at hsub ⊢
    exact hsub
  · rw [prefixM_pointwise]
    simp [hb]

/-- a min fragment at index b, witnessed by S', is ⊆ S'∖W (pointwise) -/
lemma minFragM_subM_sdiff_of_witness (N : MSys X) (S W U : X → ℕ) (b : ℕ) (hS : S ∈ N.F)
    (hB : N.LevelBounded) (hmin : N.MinFragmentAtM S W U b hS hB) {S' : X → ℕ}
    (hfr : N.IsFragmentM S W U b S') : subM U (subMM S' W) := by
  classical
  intro x
  by_contra hx
  have hgt : (S' x - W x) + 1 ≤ U x := by
    have hlt : S' x - W x < U x := Nat.lt_of_not_ge hx
    omega
  have hloose : S' x ≤ W x + U x - 1 := by
    have h1 : S' x ≤ W x + (U x) := by omega
    -- from hgt: if S'x ≥ Wx: ...
    by_cases hw : S' x ≤ W x
    · have : 1 ≤ U x := by omega
      omega
    · have hw' : W x < S' x := Nat.lt_of_not_ge hw
      have : S' x - W x + 1 ≤ U x := hgt
      omega
  have hxU : 1 ≤ U x := by omega
  have hfrx : N.IsFragmentM S W (eraseOne U x) b S' := N.isFragmentM_eraseOne_tight hfr x hxU hloose
  have hU' : N.HasFragmentAtM S W (eraseOne U x) b := ⟨S', hfrx⟩
  have hle := hmin.2.2 (eraseOne U x) hU'
  have hs : sizeM U = sizeM (eraseOne U x) + 1 := (sizeM_eraseOne_add U x hxU).symm
  omega

/-- obs.max: for a min fragment at b witnessed by S', W x < S' x when U x > 0 -/
lemma obsMaxM (N : MSys X) (S W U : X → ℕ) (b : ℕ) (hS : S ∈ N.F)
    (hB : N.LevelBounded) (hmin : N.MinFragmentAtM S W U b hS hB) {S' : X → ℕ}
    (hfr : N.IsFragmentM S W U b S') {x : X} (hxU : 0 < U x) : W x < S' x := by
  have hsub := N.minFragM_subM_sdiff_of_witness S W U b hS hB hmin hfr x
  have hle : U x ≤ S' x - W x := hsub
  have hs : 1 ≤ S' x - W x := le_trans (Nat.succ_le_of_lt hxU) hle
  have hs' : W x + 1 ≤ S' x := by
    by_cases hw : W x ≤ S' x
    · have hadd : W x + (S' x - W x) = S' x := Nat.add_sub_of_le hw
      have hw1 : W x + 1 ≤ W x + (S' x - W x) := Nat.add_le_add_left hs (W x)
      rwa [hadd] at hw1
    · have hgt : S' x < W x := Nat.lt_of_not_ge hw
      have hsub0 : S' x - W x = 0 := by omega
      omega
  exact Nat.lt_of_succ_le hs'

/-- elements of a min fragment at index b have level ≤ b in the witness -/
lemma level_le_b_of_minFragM (N : MSys X) (S W U : X → ℕ) (b : ℕ) (hS : S ∈ N.F)
    (hB : N.LevelBounded) (hmin : N.MinFragmentAtM S W U b hS hB) {S' : X → ℕ}
    (hfr : N.IsFragmentM S W U b S') {x : X} (hxU : 0 < U x) : N.lv S' x ≤ b := by
  classical
  by_contra hnot
  have hbj : b < N.lv S' x := Nat.lt_of_not_ge hnot
  have hfrx : N.IsFragmentM S W (eraseOne U x) b S' :=
    N.isFragmentM_eraseOne_high hfr x hxU (N.lv S' x) rfl hbj
  have hU' : N.HasFragmentAtM S W (eraseOne U x) b := ⟨S', hfrx⟩
  have hle := hmin.2.2 (eraseOne U x) hU'
  have hs : sizeM U = sizeM (eraseOne U x) + 1 := (sizeM_eraseOne_add U x hxU).symm
  omega

/-- U ⊆ prefixM S' b for a min fragment -/
lemma minFragM_subM_prefixM (N : MSys X) (S W U : X → ℕ) (b : ℕ) (hS : S ∈ N.F)
    (hB : N.LevelBounded) (hmin : N.MinFragmentAtM S W U b hS hB) {S' : X → ℕ}
    (hfr : N.IsFragmentM S W U b S') : subM U (N.prefixM S' b) := by
  intro x
  by_cases hUx : U x = 0
  · simp [hUx]
  · have hxU : 0 < U x := Nat.pos_of_ne_zero hUx
    have hlv : N.lv S' x ≤ b := N.level_le_b_of_minFragM S W U b hS hB hmin hfr hxU
    rw [prefixM_pointwise]
    have hsub := N.minFragM_subM_sdiff_of_witness S W U b hS hB hmin hfr x
    have hle : U x ≤ S' x - W x := hsub
    have hle' : U x ≤ S' x := by omega
    simp [hlv, hle']

/-- reverse inclusion in obs.T: (∨_{j≤b}S'_j)∖W ⊆ U -/
lemma prefixM_sdiff_subM_U (N : MSys X) {S W U S' : X → ℕ} {b : ℕ}
    (hfr : N.IsFragmentM S W U b S') : subM (subMM (N.prefixM S' b) W) U := by
  intro x
  by_cases hx0 : subMM (N.prefixM S' b) W x = 0
  · simp [hx0]
  · have hpos : 0 < subMM (N.prefixM S' b) W x := Nat.pos_of_ne_zero hx0
    have hpre : N.prefixM S' b x ≤ W x + U x := by
      have hpre1 := N.prefixM_subM_addM_of_fragment1 (hfr.2.2.1)
      exact hpre1 x
    unfold subMM at hpos
    have hwle : W x ≤ N.prefixM S' b x := by omega
    have hsub := Nat.sub_le_sub_right hpre (W x)
    have hconv : W x + U x - W x = U x := by omega
    rwa [hconv] at hsub

/-- U ⊆ (∨_{j≤b}S'_j)∖W for a min fragment (obs.T inclusion) -/
lemma U_subM_prefixM_sdiff (N : MSys X) (S W U : X → ℕ) (b : ℕ) (hS : S ∈ N.F)
    (hB : N.LevelBounded) (hmin : N.MinFragmentAtM S W U b hS hB) {S' : X → ℕ}
    (hfr : N.IsFragmentM S W U b S') : subM U (subMM (N.prefixM S' b) W) := by
  intro x
  by_cases hUx : U x = 0
  · simp [hUx]
  · have hxU : 0 < U x := Nat.pos_of_ne_zero hUx
    have hlv : N.lv S' x ≤ b := N.level_le_b_of_minFragM S W U b hS hB hmin hfr hxU
    have hsub := N.minFragM_subM_sdiff_of_witness S W U b hS hB hmin hfr x
    have hle : U x ≤ S' x - W x := hsub
    have hpre : N.prefixM S' b x = S' x := by
      rw [prefixM_pointwise]
      simp [hlv]
    unfold subMM
    rw [hpre]
    omega

/-- obs.T: U = prefixM S' b ∖ W -/
lemma obsTM (N : MSys X) (S W U : X → ℕ) (b : ℕ) (hS : S ∈ N.F)
    (hB : N.LevelBounded) (hmin : N.MinFragmentAtM S W U b hS hB) {S' : X → ℕ}
    (hfr : N.IsFragmentM S W U b S') : subMM (N.prefixM S' b) W = U := by
  exact subM_antisymm (N.prefixM_sdiff_subM_U hfr)
    (N.U_subM_prefixM_sdiff S W U b hS hB hmin hfr)

/-- t ≤ n_b for a min fragment (obs.T consequence) -/
lemma t_le_nbM (N : MSys X) (S W U : X → ℕ) (b : ℕ) (hS : S ∈ N.F)
    (hB : N.LevelBounded) (hmin : N.MinFragmentAtM S W U b hS hB) {S' : X → ℕ}
    (hfr : N.IsFragmentM S W U b S') : sizeM U ≤ N.prefixCount S b := by
  have h1 : subM U (N.prefixM S' b) := N.minFragM_subM_prefixM S W U b hS hB hmin hfr
  have h2 : sizeM U ≤ sizeM (N.prefixM S' b) := sizeM_mono h1
  have h3 : sizeM (N.prefixM S' b) = N.prefixCount S' b := N.sizeM_prefixM S' b
  have h4 : N.prefixCount S' b = N.prefixCount S b := by
    exact (N.prefixCount_eq_of_FPartial (IsFragmentM_wit (N := N) hfr) b le_rfl).symm
  rw [h3, h4] at h2
  exact h2

end MSys

end Multi
end Submission
