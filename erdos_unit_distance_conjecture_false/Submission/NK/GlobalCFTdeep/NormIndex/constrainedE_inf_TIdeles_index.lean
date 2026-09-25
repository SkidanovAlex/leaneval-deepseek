import Mathlib
import Submission.NK.GlobalCFTdeep.NormIndex.Defs

/-!
# The index of the constrained idèles inside the `S`-idèles

For a number field `K`, a finite set `S` of places and subgroups `A v ≤ K_vˣ` (`v ∈ S`), the
subgroup `constrainedE S A ≤ 𝕀 K` (local condition `A v` at `v ∈ S`, local units outside `S`)
is contained in the `S`-idèles `𝕀_{K,S}` (local units outside `S`), and this file computes its
index:

`[𝕀_{K,S} : 𝕀_{K,S} ∩ E] = ∏_{v ∈ S} [K_vˣ : A v]`.

The reason is that the projection `𝕀_{K,S} → ∏_{v ∈ S} K_vˣ` is onto — an idèle can be
prescribed arbitrarily at the finitely many places of `S` and taken to be `1` elsewhere — and
`constrainedE S A` is exactly the preimage of the product of the `A v`; the kernel of the
projection consists of idèles which are local units outside `S`, hence lies in `constrainedE S A`.
The product formula for the index is `index_pi_dependent`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep.NormIndex

open NK.GlobalCFT

/-- **The index of a product of subgroups.**  For a finite index type `ι` and a dependent family
of groups `G i`, the index of `∏ i, H i` in `∏ i, G i` is the product of the indices.  This is
`Subgroup.index_pi` without the restriction that all the groups `G i` be the same. -/
theorem index_pi_dependent {ι : Type*} [Fintype ι] {G : ι → Type*} [∀ i, Group (G i)]
    (H : ∀ i, Subgroup (G i)) :
    (Subgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  simp_rw [Subgroup.index, ← Nat.card_pi]
  refine Nat.card_congr
    ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

variable {K : Type} [Field K] [NumberField K]

/-- The projection of the `S`-idèles onto the coordinates at the places of `S`. -/
def tIdelesProj (S : Finset (Place K)) :
    ↥(TIdeles (L := K) (S : Set (Place K))) →* ((v : S) → (Place.localField K v)ˣ) where
  toFun x v := x.1 v.1
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem tIdelesProj_apply (S : Finset (Place K))
    (x : ↥(TIdeles (L := K) (S : Set (Place K)))) (v : S) :
    tIdelesProj S x v = x.1 v.1 := rfl

/-- **The projection `𝕀_{K,S} → ∏_{v ∈ S} K_vˣ` is onto**: an idèle may be prescribed at the
finitely many places of `S` and taken to be `1` at every place outside `S`. -/
theorem tIdelesProj_surjective (S : Finset (Place K)) :
    Function.Surjective (tIdelesProj (K := K) S) := by
  classical
  intro y
  let xfun : (v : Place K) → (Place.localField K v)ˣ :=
    fun v => if h : v ∈ S then y ⟨v, h⟩ else 1
  have hxfun : ∀ v, v ∉ S → xfun v ∈ Place.localUnits K v := by
    intro v hv
    show (if h : v ∈ S then y ⟨v, h⟩ else 1) ∈ Place.localUnits K v
    rw [dif_neg hv]
    exact Subgroup.one_mem _
  have hxev : ∀ᶠ v in Filter.cofinite, xfun v ∈ Place.localUnits K v := by
    rw [Filter.eventually_cofinite]
    refine Set.Finite.subset S.finite_toSet ?_
    intro v hv
    by_contra hvS
    exact hv (hxfun v hvS)
  let x : Idele K := RestrictedProduct.mk xfun hxev
  have hxU : x ∈ TIdeles (L := K) (S : Set (Place K)) := by
    rw [mem_TIdeles]
    intro v hv
    show x v ∈ Place.localUnits K v
    rw [show x v = xfun v from rfl]
    exact hxfun v hv
  refine ⟨⟨x, hxU⟩, ?_⟩
  funext v
  show x v.1 = y v
  have hxv : xfun v.1 = y v := by
    show (if h : v.1 ∈ S then y ⟨v.1, h⟩ else 1) = y v
    rw [dif_pos v.2]
  rw [show x v.1 = xfun v.1 from rfl, hxv]

theorem constrainedE_inf_TIdeles_index {K : Type} [Field K] [NumberField K] (S : Finset (NK.GlobalCFT.Place K)) (A : (v : S) → Subgroup ((NK.GlobalCFT.Place.localField K v)ˣ)) : ((NK.GlobalCFTdeep.constrainedE S A ⊓ NK.GlobalCFTdeep.TIdeles (L := K) (S : Set (NK.GlobalCFT.Place K))).subgroupOf (NK.GlobalCFTdeep.TIdeles (L := K) (S : Set (NK.GlobalCFT.Place K)))).index = ∏ v : S, (A v).index := by
  classical
  -- The intersection with the `S`-idèles is the preimage of the product of the `A v` under the
  -- projection to the coordinates at `S`.
  have hsub : (constrainedE S A ⊓ TIdeles (L := K) (S : Set (Place K))).subgroupOf
      (TIdeles (L := K) (S : Set (Place K))) =
      (Subgroup.pi Set.univ A).comap (tIdelesProj (K := K) S) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_constrainedE, mem_TIdeles,
      Subgroup.mem_comap, Subgroup.mem_pi, Set.mem_univ, true_implies, tIdelesProj_apply]
    constructor
    · rintro ⟨⟨h1, -⟩, -⟩ v
      exact h1 v
    · intro h
      exact ⟨⟨fun v => h v, fun v hv => (mem_TIdeles.mp x.2) v hv⟩,
        fun v hv => (mem_TIdeles.mp x.2) v hv⟩
  rw [hsub, (Subgroup.pi Set.univ A).index_comap_of_surjective
    (tIdelesProj_surjective (K := K) S), index_pi_dependent]

end NK.GlobalCFTdeep.NormIndex
