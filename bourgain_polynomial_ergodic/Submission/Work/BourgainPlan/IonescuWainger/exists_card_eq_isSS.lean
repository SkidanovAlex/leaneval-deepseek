import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.SunflowerSSDefs

/-!
# Extracting a sub-tuple of a family `g` that is an `IsSS` sunflower

Given a family `g : Fin n → Finset α` and an injective family `A : Fin r → Finset α` every member of
which occurs in the range of `g`, this file shows that some `r`-element subfamily of the `g i`
(the subfamily being selected by a set `I ⊆ Fin n` of indices, enumerated in increasing order via
`Finset.orderIsoOfFin`) is an `IsSS` sunflower whenever `A` is.

This is the passage, used in the proof of the Ionescu–Wainger multiplier theorem (Tao's §3
`sunflower-sec` / `sunsquare`), from the combinatorial hypothesis "there are `r` pairwise distinct
`k`-sets forming a sunflower" to the statement "one can *choose* `r` of the given sets so that they
form a sunflower" — the point being that the sums of `sunflower_square_function` run over tuples
`X : Fin r → Finset α` drawn from a fixed ambient family, and one needs the sunflower witness to be
visible in that family.

The proof is a pure reindexing: choose, for each `i : Fin r`, some index `f i : Fin n` with
`g (f i) = A i` (possible by `hocc`); injectivity of `A` makes `f` injective, so its image `I` has
`r` elements and `i ↦ g (I.orderIsoOfFin hI i)` is exactly `A` composed with a permutation of
`Fin r`; now use `IsSS.comp_perm`.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

theorem exists_card_eq_isSS {α : Type*} [Fintype α] [DecidableEq α]
    {n r k : ℕ} (g : Fin n → Finset α) (A : Fin r → Finset α)
    (hA : Work.BourgainPlan.IonescuWainger.IsSS k A) (hinj : Function.Injective A)
    (hocc : ∀ i, A i ∈ Finset.univ.image g) :
    ∃ (I : Finset (Fin n)) (hI : I.card = r),
      Work.BourgainPlan.IonescuWainger.IsSS k (fun i : Fin r => g ↑(I.orderIsoOfFin hI i)) := by
  classical
  -- Choose, for every `i`, an index of `g` carrying the value `A i`.
  have hex : ∀ i : Fin r, ∃ j : Fin n, g j = A i := fun i => by
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp (hocc i)
    exact ⟨j, hj⟩
  let f : Fin r → Fin n := fun i => (hex i).choose
  have hf : ∀ i, g (f i) = A i := fun i => (hex i).choose_spec
  -- `A` injective makes `f` injective.
  have hfinj : Function.Injective f := by
    intro i j hij
    exact hinj (by rw [← hf i, ← hf j, hij])
  let I : Finset (Fin n) := Finset.univ.image f
  have hI : I.card = r := by
    rw [Finset.card_image_of_injective Finset.univ hfinj, Finset.card_univ, Fintype.card_fin]
  -- The increasing enumeration of `I` is `f` composed with a permutation of `Fin r`.
  let e : Fin r ≃o I := I.orderIsoOfFin hI
  let fI : Fin r → I := fun i => ⟨f i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  have hfI_inj : Function.Injective fI := fun i j h => hfinj (congrArg Subtype.val h)
  have hfI_surj : Function.Surjective fI := by
    intro y
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp y.2
    exact ⟨j, Subtype.ext hj⟩
  let fIe : Fin r ≃ I := Equiv.ofBijective fI ⟨hfI_inj, hfI_surj⟩
  let σ : Equiv.Perm (Fin r) := (e : Fin r ≃ I).trans fIe.symm
  have hσ : ∀ i : Fin r, f (σ i) = ↑(e i) := by
    intro i
    have h1 : fIe (σ i) = e i := by
      show fIe (fIe.symm (e i)) = e i
      exact Equiv.apply_symm_apply fIe (e i)
    exact congrArg Subtype.val h1
  -- Hence the selected subfamily is `A ∘ σ`, an `IsSS` sunflower by `IsSS.comp_perm`.
  have hfun : (fun i : Fin r => g ↑(e i)) = A ∘ σ := by
    funext i
    show g ↑(e i) = A (σ i)
    rw [← hf (σ i), hσ i]
  have hgoal : IsSS k (fun i : Fin r => g ↑(I.orderIsoOfFin hI i)) := by
    have : (fun i : Fin r => g ↑(I.orderIsoOfFin hI i)) = A ∘ σ := hfun
    rw [this]
    exact hA.comp_perm σ
  exact ⟨I, hI, hgoal⟩

end Work.BourgainPlan.IonescuWainger
