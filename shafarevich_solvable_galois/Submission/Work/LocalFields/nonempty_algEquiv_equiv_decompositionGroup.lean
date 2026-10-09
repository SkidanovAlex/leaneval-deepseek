import Mathlib
import Submission.Work.LocalFields.Basic
import Submission.Work.LocalFields.Decomposition
import Submission.Work.LocalFields.card_decompositionGroup_le_card_algEquiv
import Submission.Work.LocalFields.card_algEquiv_le_card_decompositionGroup
import Submission.Work.LocalFields.finrank_completion_eq_card_decompositionGroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

open scoped NumberField Valued WithZero Pointwise

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- **The group of `K_v`-linear automorphisms of `L_w` is the decomposition group.**

For a finite Galois extension `L/K` of number fields, a finite prime `v` of `K`, a finite prime
`w` of `L` lying over `v`, and *any* `K_v`-algebra structure on `L_w` which is compatible with the
`K`-structure and whose scalar multiplication is continuous, the group `L_w ≃ₐ[K_v] L_w` of
`K_v`-algebra automorphisms of the completion `L_w` is isomorphic to the decomposition group
`D_w ≤ Gal(L/K)`.

This is the classical "`D_w` is the local Galois group" statement; the proof only has to combine
the two already-proved cardinality inequalities with the canonical monoid hom, as follows.

Proof sketch.  Write `Aut := L_w ≃ₐ[K_v] L_w`.
* `Work.LocalFields.card_decompositionGroup_le_card_algEquiv v w` (hypotheses as here) gives
  `Nat.card D_w ≤ Nat.card Aut`, via the injective map `τ ↦ Work.LocalFields.localAlgEquiv v w τ τ.2`.
* `Work.LocalFields.card_algEquiv_le_card_decompositionGroup v w` gives
  `Nat.card Aut ≤ Nat.card D_w`, via an injective map `Aut → D_w`.
  Hence `Nat.card Aut = Nat.card D_w` (`le_antisymm`).
* Build a `MonoidHom` `σL : Aut →* D_w` out of the restriction map used in the second of these
  files: for `σ : Aut`, `σ ↦ σ.restrictScalars K` (a monoid hom `Aut →* Gal(L_w/K)`),
  then `AlgEquiv.restrictNormalHom (F := K) (K₁ := L_w) φ.fieldRange` where
  `φ : L →ₐ[K] L_w := IsScalarTower.toAlgHom K L L_w` (a monoid hom, available in Mathlib, using
  `[Normal K φ.fieldRange]` obtained from `Normal.of_algEquiv (AlgHom.equivFieldRange φ)` and the
  Galois-ness of `L/K`), and finally conjugation by `AlgHom.equivFieldRange φ` to land in
  `Gal(L/K)`; use `MonoidHom.codRestrict` with the proof that the image lies in `D_w`
  (copy the argument from `card_algEquiv_le_card_decompositionGroup`, which uses
  `mem_decompositionGroup_of_valuation_le_one` and `mapsTo_integer_of_algEquiv`).
* This `σL` is injective (the argument at the end of `card_algEquiv_le_card_decompositionGroup`:
  a `K_v`-algebra automorphism of `L_w` trivial on the dense subfield `φ.fieldRange` is trivial,
  using `Algebra.adjoin` and closedness of finite-dimensional subspaces).
* With `Nat.card Aut = Nat.card D_w`, injectivity gives bijectivity
  (`Nat.bijective_iff_injective_and_card`), and `MulEquiv.ofBijective σL hσL` is the desired
  isomorphism (its `.symm` is fine too). -/
theorem nonempty_algEquiv_equiv_decompositionGroup {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : Work.LocalFields.FinitePrime K) (w : Work.LocalFields.FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal]
    [Algebra (Work.LocalFields.Completion K v) (Work.LocalFields.Completion L w)]
    [ContinuousSMul (Work.LocalFields.Completion K v) (Work.LocalFields.Completion L w)]
    [IsScalarTower K (Work.LocalFields.Completion K v) (Work.LocalFields.Completion L w)] :
    Nonempty (((Work.LocalFields.Completion L w) ≃ₐ[Work.LocalFields.Completion K v]
        (Work.LocalFields.Completion L w)) ≃* Work.LocalFields.decompositionGroup K w) := by
  let φ : L →ₐ[K] (Work.LocalFields.Completion L w) := IsScalarTower.toAlgHom K L _
  have hφ_apply : ∀ y : L, φ y = algebraMap L (Work.LocalFields.Completion L w) y := fun y => rfl
  haveI hnormal : Normal K φ.fieldRange := Normal.of_algEquiv (AlgHom.equivFieldRange φ)
  -- the monoid homomorphisms making up the canonical restriction map `Aut →* Gal(L/K)`
  let α : (Work.LocalFields.Completion L w ≃ₐ[K] Work.LocalFields.Completion L w)
      →* Gal(φ.fieldRange/K) :=
    AlgEquiv.restrictNormalHom (F := K) (K₁ := Work.LocalFields.Completion L w) φ.fieldRange
  let conjHom : (φ.fieldRange ≃ₐ[K] φ.fieldRange) →* (L ≃ₐ[K] L) :=
    { toFun := fun u => (AlgHom.equivFieldRange φ).trans (u.trans (AlgHom.equivFieldRange φ).symm)
      map_one' := by ext x; simp
      map_mul' := by intro u v; ext x; simp [AlgEquiv.trans_apply, AlgEquiv.mul_apply] }
  let σL : ((Work.LocalFields.Completion L w) ≃ₐ[Work.LocalFields.Completion K v]
      (Work.LocalFields.Completion L w)) →* Gal(L/K) :=
    conjHom.comp (α.comp (AlgEquiv.restrictScalarsHom K))
  -- `σL σ` is characterised by acting as `σ` on the dense image of `L`
  have hcomm : ∀ (σ : (Work.LocalFields.Completion L w) ≃ₐ[Work.LocalFields.Completion K v]
      (Work.LocalFields.Completion L w)) (x : L),
      σ (algebraMap L (Work.LocalFields.Completion L w) x) =
        algebraMap L (Work.LocalFields.Completion L w) (σL σ x) := by
    intro σ x
    have h1 : σL σ x = (AlgHom.equivFieldRange φ).symm
        ((α (AlgEquiv.restrictScalars K σ)) ((AlgHom.equivFieldRange φ) x)) := rfl
    rw [h1]
    have hφsymm : ∀ y : φ.fieldRange,
        algebraMap L (Work.LocalFields.Completion L w) ((AlgHom.equivFieldRange φ).symm y)
          = (y : Work.LocalFields.Completion L w) := by
      intro y
      have h := congrArg (fun z : φ.fieldRange => (z : Work.LocalFields.Completion L w))
        (AlgEquiv.apply_symm_apply (AlgHom.equivFieldRange φ) y)
      rw [AlgHom.equivFieldRange_apply_coe, hφ_apply] at h
      exact h
    rw [hφsymm]
    rw [show (((α (AlgEquiv.restrictScalars K σ)) ((AlgHom.equivFieldRange φ) x)) :
        Work.LocalFields.Completion L w)
        = (algebraMap ↥(φ.fieldRange) (Work.LocalFields.Completion L w))
            ((AlgEquiv.restrictNormal (AlgEquiv.restrictScalars K σ) φ.fieldRange)
              ((AlgHom.equivFieldRange φ) x)) from rfl]
    rw [AlgEquiv.restrictNormal_commutes]
    rw [show (algebraMap ↥(φ.fieldRange) (Work.LocalFields.Completion L w))
          ((AlgHom.equivFieldRange φ) x)
        = algebraMap L (Work.LocalFields.Completion L w) x from by
      simpa [AlgHom.equivFieldRange_apply_coe] using hφ_apply x]
    rfl
  -- `σL σ` preserves the `w`-adic unit ball
  have hle : ∀ (σ : (Work.LocalFields.Completion L w) ≃ₐ[Work.LocalFields.Completion K v]
      (Work.LocalFields.Completion L w)) (x : L),
      w.valuation L x ≤ 1 ↔ w.valuation L (σL σ x) ≤ 1 := by
    intro σ x
    have hz : ∀ z : Work.LocalFields.Completion L w, Valued.v (σ z) ≤ 1 ↔ Valued.v z ≤ 1 := by
      intro z
      constructor
      · intro hz
        have h1 : σ.symm (σ z) ∈ (𝒪[Work.LocalFields.Completion L w] :
            Set (Work.LocalFields.Completion L w)) :=
          Work.LocalFields.mapsTo_integer_of_algEquiv σ.symm hz
        rwa [σ.symm_apply_apply] at h1
      · intro hz
        exact Work.LocalFields.mapsTo_integer_of_algEquiv σ hz
    have hval : ∀ y : L, Valued.v ((y : Work.LocalFields.Completion L w)) = w.valuation L y :=
      fun y => IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe L w y
    rw [← hval x, ← hval (σL σ x)]
    rw [show (((σL σ x : L)) : Work.LocalFields.Completion L w)
        = σ ((x : L) : Work.LocalFields.Completion L w) from (hcomm σ x).symm]
    exact (hz ((x : L) : Work.LocalFields.Completion L w)).symm
  -- hence the image of `σL` lies in the decomposition group
  have hD : ∀ σ, σL σ ∈ Work.LocalFields.decompositionGroup K w := fun σ =>
    Work.LocalFields.mem_decompositionGroup_of_valuation_le_one v w (σL σ) (hle σ)
  -- and `σL` is injective, because `L` is dense in `L_w`
  have hinj : Function.Injective σL := by
    intro σ τ hστ
    have hgen : Algebra.adjoin (Work.LocalFields.Completion K v)
        (Set.range (algebraMap L (Work.LocalFields.Completion L w))) = ⊤ := by
      set S := Algebra.adjoin (Work.LocalFields.Completion K v)
        (Set.range (algebraMap L (Work.LocalFields.Completion L w)))
      have hclosed : IsClosed (S : Set (Work.LocalFields.Completion L w)) := by
        haveI : FiniteDimensional (Work.LocalFields.Completion K v) ↥(S.toSubmodule) :=
          Submodule.finiteDimensional_of_le (le_top)
        exact Submodule.closed_of_finiteDimensional S.toSubmodule
      have hdense : DenseRange (algebraMap L (Work.LocalFields.Completion L w)) :=
        IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap L w
      have hrange : Set.range (algebraMap L (Work.LocalFields.Completion L w)) ⊆
          (S : Set (Work.LocalFields.Completion L w)) := Algebra.subset_adjoin
      have huniv : (Set.univ : Set (Work.LocalFields.Completion L w)) ⊆
          (S : Set (Work.LocalFields.Completion L w)) := by
        have hd : closure (Set.range (algebraMap L (Work.LocalFields.Completion L w))) = Set.univ :=
          hdense.closure_range
        rw [← hd]
        exact closure_minimal hrange hclosed
      exact Algebra.eq_top_iff.mpr (fun z => huniv (Set.mem_univ z))
    have hAlg : σ.toAlgHom = τ.toAlgHom := by
      refine AlgHom.ext_of_adjoin_eq_top hgen (fun x hx => ?_)
      obtain ⟨y, rfl⟩ := hx
      change σ (algebraMap L (Work.LocalFields.Completion L w) y) =
        τ (algebraMap L (Work.LocalFields.Completion L w) y)
      rw [hcomm σ y, hcomm τ y, hστ]
    exact AlgEquiv.ext (fun z => congrFun (congrArg DFunLike.coe hAlg) z)
  let σL' : ((Work.LocalFields.Completion L w) ≃ₐ[Work.LocalFields.Completion K v]
      (Work.LocalFields.Completion L w)) →* Work.LocalFields.decompositionGroup K w :=
    σL.codRestrict (Work.LocalFields.decompositionGroup K w).toSubmonoid hD
  have hinj' : Function.Injective σL' := by
    intro a b hab
    exact hinj (Subtype.ext_iff.mp hab)
  -- the two cardinality inequalities
  have hDle : Nat.card (Work.LocalFields.decompositionGroup K w) ≤
      Nat.card ((Work.LocalFields.Completion L w) ≃ₐ[Work.LocalFields.Completion K v]
        (Work.LocalFields.Completion L w)) :=
    Work.LocalFields.card_decompositionGroup_le_card_algEquiv v w
  have hleD : Nat.card ((Work.LocalFields.Completion L w) ≃ₐ[Work.LocalFields.Completion K v]
        (Work.LocalFields.Completion L w)) ≤ Nat.card (Work.LocalFields.decompositionGroup K w) :=
    Work.LocalFields.card_algEquiv_le_card_decompositionGroup v w
  have hcard : Nat.card ((Work.LocalFields.Completion L w) ≃ₐ[Work.LocalFields.Completion K v]
        (Work.LocalFields.Completion L w)) = Nat.card (Work.LocalFields.decompositionGroup K w) :=
    le_antisymm hleD hDle
  have hbij : Function.Bijective σL' :=
    (Nat.bijective_iff_injective_and_card σL').mpr ⟨hinj', hcard⟩
  exact ⟨MulEquiv.ofBijective σL' hbij⟩

end Work.LocalFields
