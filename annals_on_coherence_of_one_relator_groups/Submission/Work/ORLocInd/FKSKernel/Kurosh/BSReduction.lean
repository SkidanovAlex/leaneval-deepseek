import Mathlib
import Submission.Work.ORLocInd.FKSKernel.Kurosh.BSWalk
import Submission.Work.ORLocInd.FKSKernel.Kurosh.exists_closed_pathWord_of_generator
import Submission.Work.ORLocInd.FKSKernel.Kurosh.exists_shorten_of_backtrack
import Submission.Work.ORLocInd.FKSKernel.Kurosh.exists_concat
import Submission.Work.ORLocInd.FKSKernel.Kurosh.exists_inv

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.ORLocInd.FKSKernel.Kurosh

open Work.ORBassSerre
open Work.ORBassSerre.Action

open Quiver

/-!
# Reduction of an element of `Γ` to a reduced closed path word

This file assembles the pieces of the walk proof of the injectivity of the canonical map
`Φ : Γ →* G` of `BSPresentation`:

* every element of `Γ` is the `elt` of a closed path word based at the root (using that the
  generators are represented by closed path words and that concatenation and inversion of path words
  are available),
* any path word can be replaced by a *reduced* one with the same `elt` and the same endpoints
  (using `exists_shorten_of_backtrack` and induction on the length),
* hence `Φ` is injective, by the walk lemma `elt_eq_one_of_reduced_closed`.

Since the reduction below needs an edge orbit to build path words (the `stepE` field of a path word
is a total function `ℕ → orbitE G V`), the statements carry the hypothesis
`[Nonempty (orbitE G V)]`.  The degenerate case in which there are no arrows at all is treated
separately (`isFinitelyPresented_of_isEmpty_total`).
-/

universe u v

variable {G : Type*} {V : Type*} [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction G V] [Work.ORBassSerre.GraphAction G V]

namespace TreeDatum


namespace PathWord

variable {d : TreeDatum G V} [Nonempty (Work.ORBassSerre.orbitE G V)]

/-- The one-vertex path word at the root, with all letters trivial: it represents `1`. -/
noncomputable def oneWord : PathWord d where
  len := 0
  orb := fun _ => d.root
  letter := fun _ => ⟨d.root, 1⟩
  letter_orbit := fun _ _ => rfl
  stepE := fun _ => Classical.arbitrary (Work.ORBassSerre.orbitE G V)
  stepB := fun _ => true
  step_src := fun k hk => absurd hk (Nat.not_lt_zero k)
  step_tgt := fun k hk => absurd hk (Nat.not_lt_zero k)

@[simp] theorem oneWord_len : (oneWord (d := d)).len = 0 := rfl

theorem oneWord_elt (D : PresData d) : (oneWord (d := d)).elt D = 1 := by
  rw [elt, oneWord_len, tpre_zero, one_mul]
  show Letter.gam (d := d) ⟨d.root, (1 : ↥(d.vgroup d.root))⟩ D = 1
  rw [Letter.gam, map_one]

theorem oneWord_orb (k : ℕ) : (oneWord (d := d)).orb k = d.root := rfl

/-- **Reduction to a reduced path word.**  Every path word can be replaced by a reduced one with the
same `elt` in `Gamma d D` and the same two endpoints, and with no more steps. -/
theorem exists_reduced (D : PresData d) (W : PathWord d) :
    ∃ W' : PathWord d, W'.len ≤ W.len ∧ W'.Reduced ∧ W'.elt D = W.elt D ∧
      W'.orb 0 = W.orb 0 ∧ W'.orb W'.len = W.orb W.len := by
  classical
  suffices h : ∀ n, ∀ W : PathWord d, W.len = n →
      ∃ W' : PathWord d, W'.len ≤ W.len ∧ W'.Reduced ∧ W'.elt D = W.elt D ∧
        W'.orb 0 = W.orb 0 ∧ W'.orb W'.len = W.orb W.len by
    exact h W.len W rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro W hn
    by_cases hred : W.Reduced
    · exact ⟨W, le_rfl, hred, rfl, rfl, rfl⟩
    · rw [PathWord.Reduced] at hred
      push Not at hred
      obtain ⟨k, hk, hback⟩ := hred
      obtain ⟨W₁, hlen, helt, h0, hL⟩ :=
        exists_shorten_of_backtrack (d := d) D W hk hback
      obtain ⟨W₂, hle, hred₂, helt₂, h0₂, hL₂⟩ := ih W₁.len (by omega) W₁ rfl
      exact ⟨W₂, by omega, hred₂, by rw [helt₂, helt], by rw [h0₂, h0], by rw [hL₂, hL]⟩

/-- **Every generator of `Γ` is the `elt` of a closed path word based at the root.** -/
theorem generator_mem (D : PresData d) (y : PresGen d D) :
    ∃ W : PathWord d, W.orb 0 = d.root ∧ W.Closed ∧ W.elt D = PresentedGroup.of y :=
  exists_closed_pathWord_of_generator D y

/-- **Every element of `Γ` is the `elt` of a closed path word based at the root.** -/
theorem exists_closed_root (D : PresData d) (γ : Gamma d D) :
    ∃ W : PathWord d, W.orb 0 = d.root ∧ W.Closed ∧ W.elt D = γ := by
  classical
  set H : Subgroup (Gamma d D) :=
    { carrier := {γ | ∃ W : PathWord d, W.orb 0 = d.root ∧ W.Closed ∧ W.elt D = γ}
      one_mem' := ⟨oneWord, oneWord_orb 0, by rw [PathWord.Closed]; rw [oneWord_orb, oneWord_orb],
        oneWord_elt D⟩
      mul_mem' := by
        rintro a b ⟨W₁, h1, hc1, he1⟩ ⟨W₂, h2, hc2, he2⟩
        have hlink : W₁.orb W₁.len = W₂.orb 0 := by
          have hc1' : W₁.orb W₁.len = W₁.orb 0 := hc1
          rw [hc1', h1, h2]
        obtain ⟨W, hlen, h0, hL, helt⟩ := exists_concat W₁ W₂ hlink
        refine ⟨W, by rw [h0, h1], ?_, ?_⟩
        · rw [PathWord.Closed]
          have hc2' : W₂.orb W₂.len = W₂.orb 0 := hc2
          rw [hL, hc2', h2, ← h1, h0]
        · rw [helt, he1, he2]
      inv_mem' := by
        rintro a ⟨W, h0, hc, he⟩
        obtain ⟨W', hlen, h0', hL', helt⟩ := exists_inv W
        refine ⟨W', ?_, ?_, ?_⟩
        · rw [h0']
          have hc' : W.orb W.len = W.orb 0 := hc
          rw [hc', h0]
        · rw [PathWord.Closed]
          have h0'' : W'.orb 0 = d.root := by rw [h0', hc, h0]
          have hL'' : W'.orb W'.len = d.root := by rw [hL', h0]
          rw [hL'', h0'']
        · rw [helt, he] } with hH
  have hle : H = ⊤ := by
    rw [eq_top_iff, ← PresentedGroup.closure_range_of (rels d D)]
    refine (Subgroup.closure_le (K := H)).mpr ?_
    rintro x ⟨y, rfl⟩
    exact generator_mem D y
  have : γ ∈ H := by rw [hle]; exact Subgroup.mem_top γ
  exact this

/-- **Every element of `Γ` is the `elt` of a reduced closed path word based at the root.** -/
theorem exists_reduced_closed_root (D : PresData d) (γ : Gamma d D) :
    ∃ W : PathWord d, W.Reduced ∧ W.Closed ∧ W.elt D = γ := by
  obtain ⟨W, h0, hc, he⟩ := exists_closed_root (d := d) D γ
  obtain ⟨W', _, hred, helt, h0', hL'⟩ := exists_reduced D W
  refine ⟨W', hred, ?_, by rw [helt, he]⟩
  rw [PathWord.Closed]
  have hc' : W.orb W.len = W.orb 0 := hc
  rw [hL', hc', ← h0']

/-- **The canonical map `Φ : Γ →* G` is injective.**  If `Φ γ = 1`, write `γ` as the `elt` of a
reduced closed path word; the walk lemma forces that word to be trivial, so `γ = 1`. -/
theorem Φ_injective (D : PresData d) (hT : Work.ORBassSerre.IsTree V) :
    Function.Injective (d.Φ D) := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  obtain ⟨W, hred, hc, he⟩ := exists_reduced_closed_root (d := d) D γ
  rw [← he]
  exact elt_eq_one_of_reduced_closed D hT W hred hc (by rw [he]; exact hγ)

end PathWord

end TreeDatum

end Work.ORLocInd.FKSKernel.Kurosh
