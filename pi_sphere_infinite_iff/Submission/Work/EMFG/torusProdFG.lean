import Mathlib
import Submission.Work.PiS.Interfaces
import Submission.Work.EMFG.basic
import Submission.Work.EMFG.torusFGandEM
import Submission.Work.EMFG.finiteCoverFG

/-!
# EMFG — a product with the torus has finitely generated homology

`Work.EMFG.fgUpTo_prod_torus`: if `H_k(Y;ℤ)` is finitely generated for every `k`, then so is
`H_k((S¹)^r × Y;ℤ)`.

This is the tool that turns a good model of `K(A,1)` for the torsion part of a finitely generated
abelian group into a good model for the whole group: for `A ≅ ℤ^r × F` one takes `(S¹)^r × L` with
`L` a model of `K(F,1)`.

The proof covers `(S¹)^r × Y` by the products of the four open semicircles of the circle's good
cover with `Y` (`Work.EMFG.torusPatch`).  A nonempty finite intersection is
`(⋂ patches) × Y` with `⋂ patches` contractible, and a product of a contractible space with `Y` is
homotopy equivalent to `Y`, so `H_*` of every intersection is finitely generated; the general
finite-cover finiteness `Work.EMFG.finiteCoverFG` finishes.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped Topology
open CategoryTheory CategoryTheory.Limits

namespace Work.EMFG

noncomputable section

/-- The product of a contractible space with `Y` is homotopy equivalent to `Y` (projection). -/
def homotopyEquivProdOfContractible (C : Type) [TopologicalSpace C] [ContractibleSpace C]
    (Y : Type) [TopologicalSpace Y] : ContinuousMap.HomotopyEquiv (C × Y) Y where
  toFun := ContinuousMap.snd
  invFun := (ContinuousMap.const Y (Classical.arbitrary C)).prodMk (ContinuousMap.id Y)
  left_inv := by
    obtain ⟨c, H⟩ := (contractible_iff_id_nullhomotopic C).mp ‹ContractibleSpace C›
    -- a homotopy between the two constant maps, from a path
    have hpath : ContinuousMap.Homotopic (ContinuousMap.const C (Classical.arbitrary C))
        (ContinuousMap.const C c) := by
      obtain ⟨γ⟩ := PathConnectedSpace.joined (Classical.arbitrary C) c
      refine ⟨ContinuousMap.Homotopy.mk
        (⟨fun p : unitInterval × C => γ p.1, by fun_prop⟩ : C(unitInterval × C, C)) ?_ ?_⟩
      · intro x; exact γ.source
      · intro x; exact γ.target
    refine (hpath.prodMap (ContinuousMap.Homotopic.refl (ContinuousMap.id Y))).trans ?_
    exact ⟨ContinuousMap.Homotopy.prodMap H.symm.some
      (ContinuousMap.Homotopy.refl (ContinuousMap.id Y))⟩
  right_inv := ⟨ContinuousMap.Homotopy.refl (ContinuousMap.id Y)⟩

/-- `H_k` of a product with a contractible factor is finitely generated if `H_k(Y;ℤ)` is. -/
theorem fgUpTo_prod_contractible (C : Type) [TopologicalSpace C] [ContractibleSpace C]
    {Y : Type} [TopologicalSpace Y] (hY : ∀ k : ℕ, Module.Finite ℤ (Work.PiS.HZ Y k))
    (N : ℕ) : Work.PiS.FGUpTo (C × Y) N :=
  fgUpTo_of_homotopyEquiv (homotopyEquivProdOfContractible C Y).symm fun _ _ => hY _

/-- `{p : X × Y | p.1 ∈ A}` is homeomorphic to `↥A × Y`. -/
def subtypeProdHomeo (X : Type) [TopologicalSpace X] (Y : Type) [TopologicalSpace Y]
    (A : Set X) : ↥{p : X × Y | p.1 ∈ A} ≃ₜ ↥A × Y where
  toFun p := (⟨p.1.1, p.2⟩, p.1.2)
  invFun q := ⟨(q.1.1, q.2), q.1.2⟩
  left_inv p := by ext <;> rfl
  right_inv q := by ext <;> rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- **Finitely generated homology of a product with a torus.** -/
theorem fgUpTo_prod_torus {Y : Type} [TopologicalSpace Y]
    (hY : ∀ k : ℕ, Module.Finite ℤ (Work.PiS.HZ Y k)) (r N : ℕ) :
    Work.PiS.FGUpTo ((Fin r → Work.Serre.Sph 1) × Y) N := by
  classical
  obtain ⟨hgood, hcov⟩ := torusPatch_isGoodFam r
  let U : (Fin r → Fin 4) → Set ((Fin r → Work.Serre.Sph 1) × Y) :=
    fun η => {p | p.1 ∈ torusPatch r η}
  have hopen : ∀ η, IsOpen (U η) := fun η => (hgood.1 η).preimage continuous_fst
  have hcovU : (⋃ η, U η) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro p
    rw [Set.mem_iUnion]
    have h1 : p.1 ∈ (⋃ η, torusPatch r η) := by rw [hcov]; exact Set.mem_univ _
    obtain ⟨η, hη⟩ := Set.mem_iUnion.mp h1
    exact ⟨η, hη⟩
  -- a finite intersection of the cover pieces, as a set of the ambient product
  have hset : ∀ S : Finset (Fin r → Fin 4),
      (⋂ η ∈ S, U η) = {p : (Fin r → Work.Serre.Sph 1) × Y |
        p.1 ∈ ⋂ η ∈ S, torusPatch r η} := by
    intro S
    ext p
    simp only [U, Set.mem_iInter, Set.mem_setOf_eq]
  have hfg : ∀ (S : Finset (Fin r → Fin 4)), S.Nonempty → ∀ k : ℕ,
      Module.Finite ℤ ((Work.Cohomology.singularChains ℤ
        (TopCat.of ↥(⋂ η ∈ S, U η))).homology k) := by
    intro S hS k
    -- the finiteness for the *set-defined* intersection …
    have hmain : ∀ k : ℕ, Module.Finite ℤ
        ((Work.Cohomology.singularChains ℤ (TopCat.of ↥{p : (Fin r → Work.Serre.Sph 1) × Y |
          p.1 ∈ ⋂ η ∈ S, torusPatch r η})).homology k) := by
      intro k
      by_cases hne : (⋂ η ∈ S, torusPatch r η).Nonempty
      · obtain ⟨η₀, hη₀⟩ := hS
        have heq : (⋂ i : ↥S, torusPatch r (i : Fin r → Fin 4))
            = ⋂ η ∈ S, torusPatch r η := by
          ext p
          simp only [Set.mem_iInter, Subtype.forall]
        have hcontrA : ContractibleSpace
            ↥(⋂ i : ↥S, torusPatch r (i : Fin r → Fin 4)) :=
          hgood.2 ↥S (fun i : ↥S => (i : Fin r → Fin 4)) ⟨η₀, hη₀⟩ (by
            rw [← heq] at hne
            simpa using hne)
        haveI hA : ContractibleSpace
            ↥(⋂ i : ↥S, torusPatch r (i : Fin r → Fin 4)) := hcontrA
        haveI hB : ContractibleSpace ↥(⋂ η ∈ S, torusPatch r η) :=
          (Homeomorph.setCongr heq.symm).contractibleSpace
        exact fgUpTo_of_homeomorph (subtypeProdHomeo _ _ _).symm
          (fgUpTo_prod_contractible ↥(⋂ η ∈ S, torusPatch r η) hY k) k le_rfl
      · haveI hE1 : IsEmpty ↥(⋂ η ∈ S, torusPatch r η) :=
          ⟨fun x => hne ⟨x.1, x.2⟩⟩
        haveI hE2 : IsEmpty ↥{p : (Fin r → Work.Serre.Sph 1) × Y |
            p.1 ∈ ⋂ η ∈ S, torusPatch r η} :=
          ⟨fun p => hne ⟨p.1.1, p.2⟩⟩
        exact Work.ThomBordism.fgch_moduleFinite_of_isZero
          (Work.ThomBordism.fgch_isZero_homology_of_isEmpty
            (TopCat.of ↥{p : (Fin r → Work.Serre.Sph 1) × Y |
              p.1 ∈ ⋂ η ∈ S, torusPatch r η}) k)
    exact fgUpTo_of_homeomorph (Homeomorph.setCongr (hset S)).symm
      (fun k _ => hmain k) k le_rfl
  intro k hk
  exact finiteCoverFG U hopen hcovU hfg k

end

end Work.EMFG
