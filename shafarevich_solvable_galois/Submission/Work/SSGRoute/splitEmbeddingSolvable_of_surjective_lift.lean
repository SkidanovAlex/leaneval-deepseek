import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.AbsoluteGalois.Basic
import Submission.Work.AbsoluteGalois.fixedField_ker_autEquiv
import Submission.Work.AbsoluteGalois.isOpen_ker_iff_continuous
import Submission.Work.GenericKernelReduction.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-!
A continuous open-kernel surjection `f : G_ℚ ↠ N ⋊[Φ] Gal(L/ℚ)` whose composite with
`SemidirectProduct.rightHom` is the restriction map to `L` solves the split embedding problem
`1 → N → N ⋊[Φ] Gal(L/ℚ) → Gal(L/ℚ) → 1` over `ℚ`.

Suggested route: let `M := IntermediateField.fixedField f.ker`; `M/ℚ` is finite Galois
(`InfiniteGalois.isOpen_iff_finite`, `IsGalois.of_fixedField_normal_subgroup`) and
`Work.AbsoluteGalois.fixedField_ker_autEquiv` gives
`e : N ⋊[Φ] (L ≃ₐ[ℚ] L) ≃* (M ≃ₐ[ℚ] M)` with `e (f σ) x = σ x`.  The hypothesis `hproj` gives
`f.ker ≤ (Work.AbsoluteGalois.restrictHom L).ker = L.fixingSubgroup`
(`MonoidHom.mem_ker`, `Work.AbsoluteGalois.restrictHom_ker`), hence `L ≤ M`
(`IntermediateField.le_iff_le`).  Conclude by unfolding
`Work.Fitting.SplitEmbeddingSolvable` with `L' := ↥M`, the `Algebra ↥L ↥M` structure induced by the
inclusion `IntermediateField.inclusion`, `FiniteDimensional ↥L ↥M`/`IsGalois ↥L ↥M` from the tower,
and `e` as the required isomorphism: for `g = f σ` use `e (f σ) x = σ x` on the one hand and
`(restrictHom L) σ = SemidirectProduct.rightHom (f σ)` with
`AlgEquiv.restrictNormalHom_apply` on the other.  Use `namespace Work.SSGRoute`.
-/

-- `Field.absoluteGaloisGroup ℚ` is a `def`, so many of the group/field instances in play below
-- are only *definitionally* equal to those of `GalQ = ℚ̄ ≃ₐ[ℚ] ℚ̄`; full definitional unfolding
-- during elaboration makes the transport transparent to `isDefEq`.
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

theorem splitEmbeddingSolvable_of_surjective_lift
    (L : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ L] [IsGalois ℚ L] [Normal ℚ L]
    {N : Type} [Group N] [Finite N] {Φ : (L ≃ₐ[ℚ] L) →* MulAut N}
    (f : SSGRoute.GalQ →* N ⋊[Φ] (L ≃ₐ[ℚ] L))
    (hsurj : Function.Surjective f)
    (hopen : IsOpen (f.ker : Set SSGRoute.GalQ))
    (hproj : ∀ σ : SSGRoute.GalQ, SemidirectProduct.rightHom (f σ) = AlgEquiv.restrictNormalHom L σ) :
    Work.Fitting.SplitEmbeddingSolvable L N Φ := by
  classical
  -- `ker f` is open, hence closed, so the infinite Galois correspondence applies to it
  have hclosed : IsClosed (f.ker : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :=
    Subgroup.isClosed_of_isOpen f.ker hopen
  -- the fixed field of `ker f`
  let M : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.fixedField f.ker
  have hfix : M.fixingSubgroup = f.ker := by
    have h := InfiniteGalois.fixingSubgroup_fixedField (k := ℚ) (K := AlgebraicClosure ℚ)
      (⟨f.ker, hclosed⟩ : ClosedSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    simpa [M] using h
  -- the isomorphism `N ⋊[Φ] Gal(L/ℚ) ≃* Gal(M/ℚ)`, acting by restriction of absolute automorphisms
  obtain ⟨e, he⟩ := Work.AbsoluteGalois.fixedField_ker_autEquiv
    (N ⋊[Φ] (L ≃ₐ[ℚ] L)) f hopen hsurj
  -- `M/ℚ` is finite (the kernel is open) and Galois (it is a normal subgroup that is closed)
  have hfdM : FiniteDimensional ℚ M := by
    refine (InfiniteGalois.isOpen_iff_finite (k := ℚ) (K := AlgebraicClosure ℚ) M).mp ?_
    rw [hfix]
    exact hopen
  have hgalM : IsGalois ℚ M := by
    exact IsGalois.of_fixedField_normal_subgroup f.ker (hn := MonoidHom.normal_ker f)
  -- `ker f ≤ L.fixingSubgroup`, because `f` projects onto the restriction map to `L`
  have hker_le : f.ker ≤ L.fixingSubgroup := by
    rw [← Work.AbsoluteGalois.restrictHom_ker L]
    intro σ hσ
    rw [MonoidHom.mem_ker, Work.AbsoluteGalois.restrictHom_def, ← hproj σ,
      MonoidHom.mem_ker.mp hσ, map_one]
  -- hence `L ≤ M` by the Galois correspondence
  have hLM : L ≤ M := by
    have h := (IntermediateField.le_iff_le (F := ℚ) (E := AlgebraicClosure ℚ) f.ker L).mpr hker_le
    simpa [M] using h
  -- the `↥L`-algebra structure on `↥M` induced by the inclusion `L ≤ M`
  let algLM : Algebra ↥L ↥M := (IntermediateField.inclusion hLM).toRingHom.toAlgebra
  letI : Algebra ↥L ↥M := algLM
  haveI hSTLM : IsScalarTower ℚ ↥L ↥M := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    simp
  haveI hfdLM : FiniteDimensional ↥L ↥M := FiniteDimensional.right ℚ ↥L ↥M
  haveI hgalLM : IsGalois ↥L ↥M := IsGalois.tower_top_of_isGalois ℚ ↥L ↥M
  -- it suffices to solve the problem inside the fixed algebraic closure
  refine Work.GenericKernelReduction.splitEmbeddingSolvable_of_inClosure ?_
  refine ⟨M, hLM, hfdM, hgalM, algLM, hSTLM, hfdLM, hgalLM, e, ?_⟩
  intro g x
  obtain ⟨σ, rfl⟩ := hsurj g
  apply Subtype.ext
  have hcoef : ∀ y : ↥L, (algebraMap ↥L ↥M y : AlgebraicClosure ℚ) = (y : AlgebraicClosure ℚ) :=
    fun y => rfl
  calc ((e (f σ)) ((algebraMap ↥L ↥M) x) : AlgebraicClosure ℚ)
      = ((e (f σ)) ⟨(x : AlgebraicClosure ℚ), hLM x.2⟩ : AlgebraicClosure ℚ) :=
        congrArg (fun z : ↥M => ((e (f σ)) z : AlgebraicClosure ℚ)) (Subtype.ext (hcoef x))
    _ = σ (x : AlgebraicClosure ℚ) := he σ ⟨(x : AlgebraicClosure ℚ), hLM x.2⟩
    _ = (((AlgEquiv.restrictNormalHom L) σ) x : AlgebraicClosure ℚ) :=
        (AlgEquiv.restrictNormalHom_apply L σ x).symm
    _ = (((SemidirectProduct.rightHom (f σ)) x) : AlgebraicClosure ℚ) := by rw [hproj σ]
    _ = ((algebraMap ↥L ↥M) ((SemidirectProduct.rightHom (f σ)) x) : AlgebraicClosure ℚ) :=
        (hcoef _).symm

end Work.SSGRoute
