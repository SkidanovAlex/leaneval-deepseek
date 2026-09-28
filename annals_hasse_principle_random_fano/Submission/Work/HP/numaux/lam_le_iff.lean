import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.numaux.Defs
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.MDBasic.finite_sets

/-!
# `lam L j ≤ x` iff `x` admits `j` independent lattice vectors of norm at most `x`

The `j`-th successive minimum `lam L j` is defined as the infimum of the radii `r` for
which there are `j` linearly independent vectors of `L` all of Euclidean norm at most `r`.
Because `L ⊆ ℤ^ι` is an integral lattice, the lattice points in a ball are *finite*, so
this infimum is attained: there really are `j` independent lattice vectors whose norms are
all at most `lam L j`.  Consequently, whenever `lam L j ≤ x` we can exhibit such a family
with the sharper bound `x`.

The finiteness input (`Work.HP.MDBasic.finite_eNorm_le`) is proved in a sibling file; the
attainment argument is reproduced here so that this file can be imported alongside the
other `numaux` files, which rely on the `orthLat` of `Submission.Work.HP.numaux.Defs`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Finset

namespace Work.HP.numaux

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The successive minimum `lam L j` is attained: for `j ≤ rk L` there are `j` linearly
independent vectors of `L` all of norm at most `lam L j`. -/
lemma lam_attained (L : Submodule ℤ (ι → ℤ)) {j : ℕ} (hj : j ≤ rk L) :
    ∃ f : Fin j → (ι → ℤ), (∀ k, f k ∈ L) ∧ LinearIndependent ℤ f ∧
      ∀ k, eNorm (f k) ≤ lam L j := by
  classical
  by_cases hj0 : j = 0
  · subst hj0
    exact ⟨fun k => k.elim0, fun k => k.elim0, linearIndependent_empty_type, fun k => k.elim0⟩
  · have hj1 : 0 < j := Nat.pos_of_ne_zero hj0
    obtain ⟨g₀, hg₀L, hg₀I, hg₀b⟩ :=
      lam_witness L hj (ρ := lam L j + 1) (by linarith)
    -- the witnesses whose norms are all at most `lam L j + 1`
    let T : Set (Fin j → (ι → ℤ)) :=
      {f | (∀ k, f k ∈ L) ∧ LinearIndependent ℤ f ∧ ∀ k, eNorm (f k) ≤ lam L j + 1}
    -- the maximal norm of such a witness
    let M : (Fin j → (ι → ℤ)) → ℝ :=
      fun f => Finset.univ.sup' ⟨⟨0, hj1⟩, Finset.mem_univ _⟩ fun k => eNorm (f k)
    have hTfin : T.Finite := by
      refine (Set.Finite.pi (fun _ => Work.HP.MDBasic.finite_eNorm_le (lam L j + 1))).subset ?_
      intro f hf
      rw [Set.mem_pi]
      intro k _
      exact hf.2.2 k
    have hTne : T.Nonempty := ⟨g₀, hg₀L, hg₀I, hg₀b⟩
    obtain ⟨t₀, ht₀T, ht₀min⟩ := Set.exists_min_image T M hTfin hTne
    have hMle : M t₀ ≤ lam L j + 1 := Finset.sup'_le _ _ fun k _ => ht₀T.2.2 k
    -- the minimising maximal norm is exactly `lam L j`
    have hbound : M t₀ ≤ lam L j := by
      by_contra hc
      push Not at hc
      have hrhoM : (lam L j + M t₀) / 2 < M t₀ := by linarith
      have hlamrho : lam L j < (lam L j + M t₀) / 2 := by linarith
      obtain ⟨h, hhL, hhI, hhb⟩ :=
        lam_witness L hj (ρ := (lam L j + M t₀) / 2) hlamrho
      have hhT : h ∈ T := ⟨hhL, hhI, fun k => le_of_lt ((hhb k).trans_lt (hrhoM.trans_le hMle))⟩
      have hlt : M h < M t₀ := lt_of_le_of_lt (Finset.sup'_le _ _ fun k _ => hhb k) hrhoM
      exact absurd (ht₀min h hhT) (not_le.mpr hlt)
    exact ⟨t₀, ht₀T.1, ht₀T.2.1,
      fun k => (Finset.le_sup' (fun k => eNorm (t₀ k)) (Finset.mem_univ k)).trans hbound⟩

/-- `lam L j ≤ x` is exactly the property that `x` admits `j` linearly independent vectors
of `L` of norm at most `x`. -/
theorem lam_le_iff {ι : Type} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ (ι → ℤ)) (j : ℕ) (x : ℝ)
    (hj : j ≤ rk L) (hx : lam L j ≤ x) :
    ∃ f : Fin j → (ι → ℤ), (∀ k, f k ∈ L) ∧ LinearIndependent ℤ f ∧
      ∀ k, eNorm (f k) ≤ x := by
  obtain ⟨f, hfL, hfI, hfb⟩ := lam_attained L hj
  exact ⟨f, hfL, hfI, fun k => (hfb k).trans hx⟩

end Work.HP.numaux
