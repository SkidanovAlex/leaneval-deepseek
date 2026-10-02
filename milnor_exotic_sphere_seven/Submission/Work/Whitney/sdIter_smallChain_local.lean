import Mathlib
import Submission.Work.Cohomology.SmallChains
import Submission.Work.Cohomology.SmallChainsIsoAux
import Submission.Work.Cohomology.Sd_isSmallChain
import Submission.Work.Whitney.sdIter_small_of_range

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# The subdivision refines an open cover of the *support* of a chain

`Work.Cohomology.exists_iter_small_chain` proves that for an open cover `X = U ∪ V` of the *whole*
space, some iterate of the barycentric subdivision sends **any** chain into the small chains
`IsSmallChain U V`.  Its hypothesis `U ∪ V = univ` is consumed exactly once, in the Lebesgue-number
step: only the simplices whose image lies in the cover need to be refined.

This file records the **localised** chain-level form, which is what the rank-one model product
formula needs (the `A+C`-cycle of `NOTES_rankOneSusp`).  The hypothesis is that every simplex of the
chain `c` lies in `U ∪ V` (i.e. `c` is a chain of the small complex of the pair `(U ∪ V, ∅)`); the
conclusion is that a high enough iterate of the subdivision is `(U,V)`-small.

The input is the *simplex-level* localised Lebesgue statement
`Work.Whitney.sdIter_small_of_range`; here it is upgraded to chains by the directed-limit argument of
`exists_iter_small_chain` together with the fact that the generators of the small complex of
`(U ∪ V, ∅)` are exactly the generators of the singular chains of simplices lying in `U ∪ V`.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable {X : TopCat}

/-- **A submodule of the simplicial chains of an arbitrary simplicial set which contains every
generator is everything.**  This is `Work.Cohomology.mem_of_gen` with the topological space
replaced by an arbitrary simplicial set (needed below for the small complex, which is a simplicial
set but not the singular complex of a space). -/
theorem mem_of_genSSet (Y : SSet) (n : ℕ)
    (P : Submodule ℤ ↥((Y.chainComplex (ModuleCat.of ℤ ℤ)).X n))
    (hgen : ∀ σ : Y _⦋n⦌, genSSet Y n σ ∈ P) : P = ⊤ := by
  letI : Module ℤ (↥((Y.chainComplex (ModuleCat.of ℤ ℤ)).X n) ⧸ P) := Submodule.Quotient.module P
  let q : (Y.chainComplex (ModuleCat.of ℤ ℤ)).X n ⟶
      ModuleCat.of ℤ (↥((Y.chainComplex (ModuleCat.of ℤ ℤ)).X n) ⧸ P) :=
    ModuleCat.ofHom (Submodule.mkQ P)
  have hleg : ∀ σ : Y _⦋n⦌, Y.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ ≫ q = 0 := by
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply]
    show Submodule.Quotient.mk (genSSet Y n σ) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact hgen σ
  have hq : q = 0 := by
    apply SSet.chainComplex_hom_ext (X := Y) (R := ModuleCat.of ℤ ℤ) (n := n)
    intro σ
    simpa using hleg σ
  refine Submodule.eq_top_iff'.mpr fun c => ?_
  have h2 : ModuleCat.Hom.hom q c = ModuleCat.Hom.hom (0 : (Y.chainComplex (ModuleCat.of ℤ ℤ)).X n ⟶
      ModuleCat.of ℤ (↥((Y.chainComplex (ModuleCat.of ℤ ℤ)).X n) ⧸ P)) c := by rw [hq]
  rw [ModuleCat.hom_zero, LinearMap.zero_apply] at h2
  have h3 : ModuleCat.Hom.hom q = Submodule.mkQ P := rfl
  rw [h3, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h2
  exact h2

/-- **The localised small-chains theorem.**  For an open pair `(U,V)` and a singular `n`-chain `c`
all of whose simplices lie in `U ∪ V`, some iterate of the barycentric subdivision is
`(U,V)`-small. -/
theorem exists_iter_small_chain_of_smallSupport (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (n : ℕ) (c : (singularChains ℤ X).X n) (hc : IsSmallChain (U ∪ V) ∅ c) :
    ∃ N, IsSmallChain U V ((sdChainMapIter X N).f n c) := by
  classical
  let P : Submodule ℤ ↥((singularChains ℤ X).X n) :=
    ⨆ N, Submodule.comap (ModuleCat.Hom.hom ((sdChainMapIter X N).f n))
      (smallChainSubmodule U V n)
  have hgen : ∀ (σ : Simplex X n), IsSmall (U ∪ V) (∅ : Set X) σ → gen X n σ ∈ P := by
    intro σ hσ
    have hrange : Set.range (fun z : (Delta n : TopCat) => sdMap n σ z) ⊆ U ∪ V := by
      rcases (isSmall_iff (U := U ∪ V) (V := (∅ : Set X)) σ).mp hσ with h | h
      · exact h
      · exfalso
        rcases Set.range_nonempty (fun z : (Delta n : TopCat) => sdMap n σ z) with ⟨y, hy⟩
        simpa using h hy
    obtain ⟨N, hN⟩ := Work.Whitney.sdIter_small_of_range U V hU hV n σ hrange
    exact le_iSup (fun N => Submodule.comap (ModuleCat.Hom.hom ((sdChainMapIter X N).f n))
      (smallChainSubmodule U V n)) N hN
  have hcP : c ∈ P := by
    obtain ⟨c', hc'⟩ := hc
    let Q : Submodule ℤ ↥((smallChains (U ∪ V) (∅ : Set X)).X n) :=
      Submodule.comap ((smallToSing (U ∪ V) (∅ : Set X)).f n).hom P
    have hQ : Q = ⊤ := by
      refine mem_of_genSSet (smallSSet (U ∪ V) (∅ : Set X)) n Q ?_
      intro σ
      show ((smallToSing (U ∪ V) (∅ : Set X)).f n).hom
        (genSSet (smallSSet (U ∪ V) (∅ : Set X)) n σ) ∈ P
      rw [smallToSing_gen (U := U ∪ V) (V := (∅ : Set X)) σ]
      exact hgen σ.1 σ.2
    have : c' ∈ Q := by rw [hQ]; exact Submodule.mem_top
    have h2 : ((smallToSing (U ∪ V) (∅ : Set X)).f n).hom c' ∈ P := this
    rwa [hc'] at h2
  have hdir : Directed (· ≤ ·)
      (fun N => Submodule.comap (ModuleCat.Hom.hom ((sdChainMapIter X N).f n))
        (smallChainSubmodule U V n)) := by
    intro N M
    refine ⟨N + M, ?_, ?_⟩
    · rintro x hx
      rw [Submodule.mem_comap] at hx ⊢
      rw [sdChainMapIter_f_apply X N M n x]
      exact iter_sd_small U V M hx
    · rintro x hx
      rw [Submodule.mem_comap] at hx ⊢
      rw [show N + M = M + N from Nat.add_comm N M, sdChainMapIter_f_apply X M N n x]
      exact iter_sd_small U V N hx
  rw [Submodule.mem_iSup_of_directed _ hdir] at hcP
  exact hcP

end

end Work.Cohomology

/-! ## Axiom check -/

#print axioms Work.Cohomology.mem_of_genSSet
#print axioms Work.Cohomology.exists_iter_small_chain_of_smallSupport
