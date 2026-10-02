import Mathlib
import Submission.Work.ThomBordism.KeyLocal.tubeSets
import Submission.Work.ThomBordism.relKronH_surjective
import Submission.Work.PTGeometric.isOrientFamily_eq_smul_of_connected
import Submission.Work.Orient.Bridge
import Submission.Work.Cohomology.relChains_free

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# An admissible degree-`8` class at a point of a closed oriented `8`-manifold

The target of this file, `Work.ThomBordism.KeyLocal.exists_admissible`, produces for every point `x`
of a `Man8` a relative cohomology class
`o ∈ H^8(V, V∖{x};ℤ)` which is **dual** to the local fundamental class
`locClass (TopCat.of V.pt) 8 V.c x ∈ H_8(V, V∖{x};ℤ)`:

  `⟨o, locClass x⟩ = 1`.

## Where this comes from

The relative Kronecker pairing `Work.Tubular.relKronH X A n : H^n(X,A;ℤ) →ₗ (H_n(X,A;ℤ) →ₗ ℤ)` is
**surjective** whenever the relative chains are degreewise free
(`Work.ThomBordism.relKronH_surjective`, and `Work.Cohomology.relChains_free` always applies) — this
is the surjectivity half of the universal coefficient theorem.  So it suffices to exhibit a *functional*
on `H_n(X,A;ℤ)` taking the value `1` at the local class.  The local homology of a charted space at a
point is infinite cyclic (`Work.PTGeometric.nonempty_locH_iso_int`, no compactness needed), and the
fundamental-class field `Man8.c_fund` says that the local class is a *cyclic generator* of it
(`Work.Cohomology.relLocClass_point_span`).  A cyclic generator `u` of a `ℤ`-module `A ≃ₗ[ℤ] ℤ`
carries a functional `φ` with `φ u = 1` (`exists_dual_apply_one` below: transport `1` back along the
isomorphism and multiply by the resulting scalar), and a preimage of `φ` under the surjective pairing
is the required `o`.

Note that the class `o` produced this way need not be *explicit* — the statement is an existence
statement, and the surjectivity route is exactly what makes it cheap and orientation-independent.
-/

namespace Work.ThomBordism.KeyLocal

noncomputable section

/-- **A functional taking the value `1` at a cyclic generator.**  If `A` is a `ℤ`-module isomorphic
to `ℤ` and `u` generates `A` cyclically (`Submodule.span ℤ {u} = ⊤`), then there is a `ℤ`-linear
functional `φ` on `A` with `φ u = 1`.

Indeed `e u` is a unit of `ℤ`: `e.symm 1 = c • u` for some `c`, and applying the isomorphism `e`
gives `c • e u = 1`, so `IsUnit (e u)`; hence `c • e` is the required functional. -/
theorem exists_dual_apply_one {A : Type*} [AddCommGroup A] [Module ℤ A] (e : A ≃ₗ[ℤ] ℤ)
    {u : A} (hu : Submodule.span ℤ ({u} : Set A) = ⊤) :
    ∃ φ : A →ₗ[ℤ] ℤ, φ u = 1 := by
  have hmem : e.symm 1 ∈ Submodule.span ℤ ({u} : Set A) := by
    rw [hu]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have h : c • e u = 1 := by
    have h1 := congrArg (fun w => e w) hc
    rw [e.apply_symm_apply] at h1
    rw [← h1]
    exact (LinearMap.map_smul (e : A →ₗ[ℤ] ℤ) c u).symm
  exact ⟨c • (e : A →ₗ[ℤ] ℤ), by rw [LinearMap.smul_apply]; exact h⟩

/-- **An admissible class at a point.**  For every point `x` of a closed oriented smooth
`8`-manifold `V` there is a relative cohomology class `o ∈ H^8(V, V∖{x};ℤ)` pairing to `1` against
the local fundamental class of `V` at `x`. -/
theorem exists_admissible {V : Work.ThomBordism.Man8} (x : V.pt) :
    ∃ o : Work.Thom.RelCoh ℤ 8 (TopCat.of V.pt) (Work.ThomBordism.FrameSigns.punct V x),
      Work.Tubular.relKronH (TopCat.of V.pt) (Work.ThomBordism.FrameSigns.punct V x) 8 o
        (Work.Orient.locClass (TopCat.of V.pt) 8 V.c x) = 1 := by
  classical
  -- the local homology at `x` is infinite cyclic
  obtain ⟨ee⟩ := Work.PTGeometric.nonempty_locH_iso_int 8 (by norm_num) (TopCat.of V.pt) x
  let e : Work.Orient.LocH (TopCat.of V.pt) 8 x ≃ₗ[ℤ] ℤ := ee.toLinearEquiv
  -- the local fundamental class generates it
  have hu : Submodule.span ℤ
      ({Work.Orient.locClass (TopCat.of V.pt) 8 V.c x} :
        Set (Work.Orient.LocH (TopCat.of V.pt) 8 x)) = ⊤ :=
    Work.Cohomology.relLocClass_point_span (TopCat.of V.pt) 8 V.c (fun y => V.c_fund y) x
  -- hence there is a functional taking the value `1` there
  obtain ⟨φ, hφ⟩ := exists_dual_apply_one e hu
  -- and the relative Kronecker pairing is surjective onto all functionals
  have hsurj : Function.Surjective
      (Work.Tubular.relKronH (TopCat.of V.pt) (Work.ThomBordism.FrameSigns.punct V x) 8) :=
    Work.ThomBordism.relKronH_surjective _ _ 8
      (fun m => Work.Cohomology.relChains_free _ _ m)
  obtain ⟨o, ho⟩ := hsurj φ
  refine ⟨o, ?_⟩
  rw [ho]
  exact hφ

end

end Work.ThomBordism.KeyLocal
