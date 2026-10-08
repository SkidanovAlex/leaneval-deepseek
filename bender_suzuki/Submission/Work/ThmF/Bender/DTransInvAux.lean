import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.Bender.Basic
import Submission.Work.ThmF.Bender.twoInvolutionsOdd
import Submission.Work.ThmF.Bender.existsInvolutionConjugating

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Auxiliary lemmas for Peterfalvi I, Ch. I §2 Prop. 2 (b)

The vocabulary and the elementary facts about conjugating involutions used by
`Submission.Work.ThmF.Bender.DTransitiveInv` (and by the two counting lemmas delegated for it):

* `InvOut H` : the involutions of `G` outside `H`;
* `InvHt H t` : the involutions of `G` transforming `H` into the conjugate `H^t` (i.e. the
  involutions of the coset `Ht`);
* `conj_notMem_of_notMem` : conjugating an involution of `H` by an involution outside `H` keeps
  it outside `H` (Ch. I §1 (2));
* `exists_conj_involution_of_notMem` : each involution outside `H` is conjugate to each
  involution of `H` by an involution (Ch. I §2 Prop. 1 (a));
* `existsUnique_conj_involution` : that conjugating involution is unique (Ch. I §2 Prop. 1 (a)),
  proved by the pigeonhole principle for the map `u ↦ u * s * u⁻¹` of the finite set `InvOut H`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.Bender

open LeanEval.GroupTheory.Defs Submission.Blueprint

variable {G : Type*} [Group G] [Finite G]

/-- The involutions of `G` lying outside the subgroup `H`. -/
def InvOut (H : Subgroup G) : Set G := {u : G | orderOf u = 2 ∧ u ∉ H}

/-- The involutions of `G` transforming `H` into a fixed conjugate `H^t`, i.e. the involutions
of the coset `Ht` (they are exactly the involutions `u` with `H^u = H^t`). -/
def InvHt (H : Subgroup G) (t : G) : Set G :=
  {u : G | orderOf u = 2 ∧ Submission.Blueprint.conj u H = Submission.Blueprint.conj t H}

omit [Finite G] in
lemma orderOf_conj_eq (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
    MulEquiv.orderOf_eq (MulAut.conj g) x

/-- Conjugation by an involution outside `H` sends the involutions of `H` outside `H`
(Peterfalvi I, Ch. I §1 (2): an involution of `H` lies in a unique conjugate of `H`). -/
lemma conj_notMem_of_notMem {H : Subgroup G} (hH : IsStronglyEmbedded H) {s x : G}
    (hs : s ∈ H) (hs2 : orderOf s = 2) (hx : x ∉ H) (hx2 : orderOf x = 2) :
    x * s * x⁻¹ ∉ H := by
  intro hmem
  have hw2 : orderOf (x * s * x⁻¹) = 2 := by rw [orderOf_conj_eq, hs2]
  have hconj : x * s * x⁻¹ ∈ Submission.Blueprint.conj x H := by
    rw [Work.Models.mem_conj_iff]
    have h : x⁻¹ * (x * s * x⁻¹) * x = s := by group
    rw [h]; exact hs
  have h := Work.ThmF.conj_eq_self_of_involution_mem hH hmem hw2 hconj
  exact hx ((Work.ThmF.conj_eq_iff_mem hH x).mp h)

/-- Given an involution `s ∈ H` and an involution `w ∉ H`, some involution conjugates `s` to
`w` (Peterfalvi I, Ch. I §2 Prop. 1 (a)). -/
lemma exists_conj_involution_of_notMem {H : Subgroup G} (hH : IsStronglyEmbedded H) {s w : G}
    (hs : s ∈ H) (hs2 : orderOf s = 2) (hw2 : orderOf w = 2) (hw : w ∉ H) :
    ∃ u : G, orderOf u = 2 ∧ u * s * u⁻¹ = w :=
  existsInvolutionConjugating hs2 hw2 (twoInvolutionsOdd hH hs hs2 hw2 hw)

/-- Peterfalvi I, Ch. I §2 Prop. 1 (a): if `s ∈ H` and `t ∉ H` are involutions, there is a
*unique* involution `u` with `u * s * u⁻¹ = t`.  This is the uniqueness of the conjugating
involution, proved by counting: `u ↦ u * s * u⁻¹` is a bijection of the finite set of
involutions outside `H`. -/
theorem existsUnique_conj_involution {H : Subgroup G} (hH : IsStronglyEmbedded H) {s t : G}
    (hs : s ∈ H) (hs2 : orderOf s = 2) (ht2 : orderOf t = 2) (htH : t ∉ H) :
    ∃! u : G, orderOf u = 2 ∧ u * s * u⁻¹ = t := by
  obtain ⟨u₀, hu₀2, hu₀⟩ := exists_conj_involution_of_notMem hH hs hs2 ht2 htH
  refine ⟨u₀, ⟨hu₀2, hu₀⟩, ?_⟩
  intro u' hu'
  obtain ⟨hu'2, hu'⟩ := hu'
  set S : Set G := InvOut H with hS
  have hmap : ∀ u : ↥S, ((u : G) * s * (u : G)⁻¹) ∈ S := by
    intro u
    exact ⟨by rw [orderOf_conj_eq, hs2], conj_notMem_of_notMem hH hs hs2 u.2.2 u.2.1⟩
  let F : ↥S → ↥S := fun u => ⟨(u : G) * s * (u : G)⁻¹, hmap u⟩
  have hFsurj : Function.Surjective F := by
    intro v
    obtain ⟨u, hu2, huc⟩ := exists_conj_involution_of_notMem hH hs hs2 v.2.1 v.2.2
    have hu_notin : u ∉ H := fun h => v.2.2 (huc ▸ H.mul_mem (H.mul_mem h hs) (H.inv_mem h))
    exact ⟨⟨u, hu2, hu_notin⟩, by ext; exact huc⟩
  have hFinj : Function.Injective F := Finite.injective_iff_surjective.mpr hFsurj
  have hu₀_notin : u₀ ∉ H := fun h => htH (hu₀ ▸ H.mul_mem (H.mul_mem h hs) (H.inv_mem h))
  have hu'_notin : u' ∉ H := fun h => htH (hu' ▸ H.mul_mem (H.mul_mem h hs) (H.inv_mem h))
  have h1 : (⟨u₀, hu₀2, hu₀_notin⟩ : ↥S) = ⟨u', hu'2, hu'_notin⟩ := by
    apply hFinj
    ext
    show (u₀ : G) * s * (u₀ : G)⁻¹ = (u' : G) * s * (u' : G)⁻¹
    rw [hu₀, hu']
  exact (Subtype.ext_iff.mp h1).symm

end Work.ThmF.Bender
