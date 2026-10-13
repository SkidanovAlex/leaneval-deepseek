import Mathlib
import Submission.Work.DSMap.Map
import Submission.Work.DSG2.Defs
import Submission.Work.DSG2.Basic
import Submission.Work.DSG2.Setup
import Submission.Work.DSG2.denseAffineCover
import Submission.Work.DSG2.finiteTypeSections_u
import Submission.Work.DSG2.exists_segre_product_u
import Submission.Work.DSG2.SegreProduct
import Submission.Work.DSG2.segreEmbedding_u
import Submission.Work.DSG2.padSurjMvPolynomial
import Submission.Work.DSG2.immersionPSpaceOfSurj

/-!
# DSG2: existence of the Chow data

`Work.DSG2.nonempty_chowSetup`: for `A` Noetherian, `X : Scheme.{u}` proper over `Spec A` and
`X` nonempty, the Chow data `Work.DSG2.ChowSetup A X f` exists.

The construction is the classical one (EGA II 5.6.1, Stacks 0200):

1. a finite affine open cover `U : Fin m → X.affineOpens` with `⋂ U i` dense (`denseAffineCover`),
   and `m > 0` because `X` is nonempty;
2. a common `N` and surjections `A[x₀,…,x_N] ↠ Γ(X, U i)` (finite typeness of the sections plus
   `Work.DSG2.padSurjMvPolynomial`), giving immersions `j i : U i ⟶ ℙ^N_A`
   (`Work.DSG2.immersionPSpaceOfSurj`);
3. the `m`-fold product `∏ᵢ ℙ^N_A` with its closed immersion into a projective space
   (`Work.DSG2.nonempty_segreProductData`, from the two-factor Segre embedding
   `Work.DSG2.hasSegre`);
4. the product map `jU : U0 = ⋂ U i ⟶ P` of the restrictions of the `j i`, from the universal
   property of the product.
-/

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace Work.DSG2

open LeanEval.AlgebraicGeometry.DirectSummand

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The Chow data exists over a Noetherian base, for nonempty `X`. -/
theorem nonempty_chowSetup (A : Type u) [CommRing A] [IsNoetherianRing A] (X : Scheme.{u})
    (f : X ⟶ Spec (.of A)) [IsProper f] (hX : Nonempty X) :
    Nonempty (ChowSetup A X f) := by
  classical
  haveI : IsNoetherian X := isNoetherian_of_isProper f
  obtain ⟨m, U, hUcover, hU0dense⟩ := denseAffineCover (X := X)
  -- the cover is nonempty, because `X` is
  have hm : 0 < m := by
    by_contra h
    obtain rfl : m = 0 := Nat.eq_zero_of_not_pos h
    have hbot : (⊥ : X.Opens) = ⊤ := by
      simpa [iSup_of_empty] using hUcover
    obtain ⟨x⟩ := hX
    have : x ∈ (⊥ : X.Opens) := hbot ▸ (show x ∈ (⊤ : X.Opens) from trivial)
    simpa using this
  -- a presentation of each `Γ(X, U i)` by a polynomial ring
  have key : ∀ i : Fin m,
      ∃ (n : ℕ) (ψ : MvPolynomial (Fin n) A →+* Γ(X, ((U i : X.Opens))))
        (_ : Function.Surjective ψ),
        ψ.comp MvPolynomial.C = sectionAlgebra f ((U i : X.Opens)) := by
    intro i
    letI : Algebra A Γ(X, ((U i : X.Opens))) := (sectionAlgebra f _).toAlgebra
    have halg : Algebra.FiniteType A Γ(X, ((U i : X.Opens))) :=
      finiteTypeSections_u f _ (U i).2
    obtain ⟨n, ψ, hψ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp halg
    refine ⟨n, ψ.toRingHom, hψ, ?_⟩
    ext a
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe]
    rw [← MvPolynomial.algebraMap_eq, ← RingHom.algebraMap_toAlgebra (sectionAlgebra f _)]
    exact AlgHom.commutes ψ a
  choose n ψ hψ hψC using key
  -- a common number of variables
  set N : ℕ := Finset.sup Finset.univ n with hN
  have hnN : ∀ i, n i ≤ N := fun i => Finset.le_sup (Finset.mem_univ i)
  have key2 : ∀ i : Fin m,
      ∃ ψ' : MvPolynomial (Fin N) A →+* Γ(X, ((U i : X.Opens))),
        Function.Surjective ψ' ∧
          ψ'.comp MvPolynomial.C = sectionAlgebra f ((U i : X.Opens)) :=
    fun i => padSurjMvPolynomial (sectionAlgebra f _) (hnN i) (ψ i) (hψ i) (hψC i)
  choose ψ' hψ' hψ'C using key2
  -- the local immersions into `ℙ^N_A`
  have hj : ∀ i : Fin m,
      ∃ i' : (((U i : X.Opens)) : Scheme.{u}) ⟶ DSMap.PSpace A N,
        IsImmersion i' ∧
          i' ≫ DSMap.PSpace.toSpec A N = ((U i : X.Opens)).ι ≫ f :=
    fun i => immersionPSpaceOfSurj A f ((U i : X.Opens)) (U i).2 N (ψ' i) (hψ' i) (hψ'C i)
  choose j hjImm hjComp using hj
  -- the ambient product
  obtain ⟨SP⟩ := nonempty_segreProductData A N m hm (hasSegre A)
  -- the product map `jU : U0 ⟶ P`
  set U0 : X.Opens := ⨅ i, ((U i : X.Opens)) with hU0
  have hU0le : ∀ i, U0 ≤ ((U i : X.Opens)) := fun i => iInf_le _ i
  have hU0dense' : Dense (U0 : Set X) := hU0dense
  have hq : ∀ i : Fin m,
      (X.homOfLE (hU0le i) ≫ j i) ≫ DSMap.PSpace.toSpec A N = U0.ι ≫ f := by
    intro i
    rw [Category.assoc, hjComp i, ← Category.assoc, Scheme.homOfLE_ι]
  obtain ⟨jU, hjUπ, hjUproj⟩ := SP.liftSpec (U0 : Scheme.{u})
    (fun i => X.homOfLE (hU0le i) ≫ j i) (U0.ι ≫ f) hq
  exact ⟨{
    hNoeth := ‹IsNoetherian X›
    m := m
    hm := hm
    U := U
    hUcover := hUcover
    U0 := U0
    hU0le := hU0le
    hU0dense := hU0dense'
    N := N
    j := j
    hjImm := hjImm
    hjComp := hjComp
    P := SP.P
    πP := SP.π
    p := SP.p
    pComp := SP.proj_compat
    pProper := SP.proj_proper
    πP_proper := SP.struct_proper
    lift := SP.liftSpec
    M := SP.N
    iP := SP.i
    iP_closed := SP.isClosed_proj
    iP_comp := SP.struct_compat
    jU := jU
    jU_proj := hjUproj
    jU_π := hjUπ }⟩

end Work.DSG2
