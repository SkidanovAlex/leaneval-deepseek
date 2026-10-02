import Mathlib
import Submission.Work.ThomBordism.orientedFibreGen
import Submission.Work.Tubular.LocalDegree
import Submission.Work.Thom.ThomClass
import Submission.Work.ThomBordism.exists_nonTorsion_H8
import Submission.Work.ThomBordism.relKronH_surjective
import Submission.Work.Cohomology.kronH_isIso
import Submission.Work.Cohomology.kronH_kernel_eq_torsion
import Submission.Work.Orient.Closed

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

namespace Work.ThomBordism

noncomputable section

open CategoryTheory AlgebraicTopology

/-!
# The Kronecker pairing with the fundamental class is nonzero on the normal total space

The target `Work.ThomBordism.exists_kronH_zeroSection_fund_ne_zero` says that the functional

  `x ↦ ⟨(zeroSection E)^* x, V.c⟩`,   `x ∈ H⁸(ν; ℤ)`,

on the degree-`8` cohomology of the normal total space `ν = NormalTotal E` of an embedding
`E : V ↪ ℝ^{8+k}` of a connected closed oriented smooth `8`-manifold is not identically zero.

This is a purely homological statement, and the two sides of it are:

* the **projection** `NormalTotal.proj : ν → V` is a continuous retraction (its composite with the
  zero section is the identity of `V`), so pulling a class back from `V` along `proj` and then along
  the zero section gives the class back;
* `H⁸(V; ℤ)` contains a class pairing nontrivially with the fundamental class `V.c`.

The second point is the only substantive one.  It is the same local-degree computation as
`Work.ThomBordism.exists_nonTorsion_H8`, stopped one step earlier: the localisation at a point is an
isomorphism onto `ℤ`, its value on `V.c` generates (because `V.c` is a fundamental class), hence is
nonzero, and `Work.Cohomology.exists_cochain_of_functional` turns the resulting functional on
`H₈(V; ℤ)` into a cocycle.
-/

/-- The projection `ν → V` of the normal total space, as a continuous map. -/
def normalProjTotal {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) :
    C(Work.Tubular.NormalTotal E, V.pt) :=
  ⟨Work.Tubular.NormalTotal.proj, Work.Tubular.NormalTotal.continuous_proj E⟩

/-- The projection of the normal total space is a retraction of the zero section. -/
theorem normalProjTotal_comp_zeroSection {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) :
    (normalProjTotal E).comp (Work.Tubular.zeroSectionNormal E) = ContinuousMap.id V.pt :=
  rfl

/-- **`H⁸` of a connected closed oriented `8`-manifold contains a class pairing nontrivially with
the fundamental class.** -/
theorem exists_fundPairing_ne_zero (V : Work.ThomBordism.Man8) [ConnectedSpace V.pt] :
    ∃ u : (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj (TopCat.of V.pt))).homology 8,
      Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8 u V.c ≠ 0 := by
  classical
  set X : SSet := TopCat.toSSet.obj (TopCat.of V.pt) with hX
  have hc : Work.Orient.IsFundClass (TopCat.of V.pt) 8 V.c := fun x => V.c_fund x
  obtain ⟨x⟩ := (inferInstance : Nonempty V.pt)
  obtain ⟨e⟩ := Work.ThomBordism.RelH_point_iso 8 (by norm_num) (TopCat.of V.pt) x
  -- the localisation at `x`
  let loc : (Work.Cohomology.chainC ℤ X).homology 8 →ₗ[ℤ]
      ↥(Work.ThomBordism.RelH (TopCat.of V.pt) 8 ({x} : Set V.pt)) :=
    (HomologicalComplex.homologyMap
      (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of V.pt)
        {y : V.pt | y ≠ x})) 8).hom
  have hloc : loc V.c = Work.Orient.locClass (TopCat.of V.pt) 8 V.c x := rfl
  -- the local generator is non-zero, since the local group is `ℤ` and it generates
  have hgen : loc V.c ≠ 0 := by
    intro h0
    have hz : Submodule.span ℤ
        ({(0 : ↥(Work.ThomBordism.RelH (TopCat.of V.pt) 8 ({x} : Set V.pt)))} :
          Set ↥(Work.ThomBordism.RelH (TopCat.of V.pt) 8 ({x} : Set V.pt))) = ⊤ := by
      rw [show (0 : ↥(Work.ThomBordism.RelH (TopCat.of V.pt) 8 ({x} : Set V.pt)))
          = loc V.c from h0.symm]
      rw [hloc]
      exact hc x
    have hbot : Submodule.span ℤ
        ({(0 : ↥(Work.ThomBordism.RelH (TopCat.of V.pt) 8 ({x} : Set V.pt)))} :
          Set ↥(Work.ThomBordism.RelH (TopCat.of V.pt) 8 ({x} : Set V.pt))) = ⊥ :=
      Submodule.span_singleton_eq_bot.mpr rfl
    have hsub : Subsingleton ↥(Work.ThomBordism.RelH (TopCat.of V.pt) 8 ({x} : Set V.pt)) := by
      refine ⟨fun a b => ?_⟩
      have htop : (⊤ : Submodule ℤ ↥(Work.ThomBordism.RelH (TopCat.of V.pt) 8 ({x} : Set V.pt)))
          = ⊥ := by rw [← hz, hbot]
      have ha : a = 0 := by
        have hmem : a ∈ (⊥ : Submodule ℤ
            ↥(Work.ThomBordism.RelH (TopCat.of V.pt) 8 ({x} : Set V.pt))) := by
          rw [← htop]; trivial
        simpa using hmem
      have hb : b = 0 := by
        have hmem : b ∈ (⊥ : Submodule ℤ
            ↥(Work.ThomBordism.RelH (TopCat.of V.pt) 8 ({x} : Set V.pt))) := by
          rw [← htop]; trivial
        simpa using hmem
      rw [ha, hb]
    have hsurj : Function.Surjective (e.hom.hom : ↥(Work.ThomBordism.RelH (TopCat.of V.pt) 8
        ({x} : Set V.pt)) → ℤ) := (ConcreteCategory.bijective_of_isIso e.hom).2
    have : Subsingleton ℤ := ⟨fun a b => by
      obtain ⟨p, rfl⟩ := hsurj a
      obtain ⟨q, rfl⟩ := hsurj b
      rw [Subsingleton.elim p q]⟩
    exact absurd (Subsingleton.elim (0 : ℤ) 1) (by norm_num)
  -- the functional `H₈ → ℤ` evaluating the local class at `x` in the model `ℤ`
  have hφ : (e.hom.hom.comp loc) V.c ≠ 0 := by
    intro h0
    refine hgen ((ConcreteCategory.bijective_of_isIso e.hom).1 ?_)
    rw [LinearMap.comp_apply] at h0
    rw [h0, map_zero]
  -- a cycle representing `V.c`
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective
    ((Work.Cohomology.chainC ℤ X).homologyπ 8)).mp inferInstance V.c
  -- a cocycle evaluating non-trivially on `z`
  obtain ⟨α, hα, hval⟩ :=
    Work.Cohomology.exists_cochain_of_functional X 8 (e.hom.hom.comp loc) z
  refine ⟨Work.Cohomology.cohomologyClassOf ℤ X α hα, ?_⟩
  have h1 : Work.Cohomology.kronH ℤ X 8 (Work.Cohomology.cohomologyClassOf ℤ X α hα)
      V.c ≠ 0 := by
    rw [← hz, Work.Cohomology.kronH_apply ℤ X α hα z, hval, hz]
    exact hφ
  exact h1

/-- **The Kronecker pairing of the pullback along the zero section of the normal total space with
the fundamental class is not identically zero**: there is a degree-`8` class on `ν = NormalTotal E`
whose pullback along `x ↦ (x,0)` pairs nontrivially with `V.c`.

The class is the pullback along the projection `ν → V` of the class produced by
`Work.ThomBordism.exists_fundPairing_ne_zero`; the projection is a retraction of the zero section,
so the two pullbacks cancel. -/
theorem exists_kronH_zeroSection_fund_ne_zero {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
    {k : ℕ} (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) :
    ∃ x : Work.Thom.Coh ℤ 8 (TopCat.of (Work.Tubular.NormalTotal E)),
      Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
        ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom x) V.c ≠ 0 := by
  classical
  obtain ⟨u, hu⟩ := exists_fundPairing_ne_zero V
  refine ⟨(Work.Thom.CohMap (normalProjTotal E) ℤ 8).hom u, ?_⟩
  have hcoe : (Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom
      ((Work.Thom.CohMap (normalProjTotal E) ℤ 8).hom u) = u := by
    rw [Work.Thom.CohMap_comp_apply (Work.Tubular.zeroSectionNormal E) (normalProjTotal E) ℤ 8 u,
      normalProjTotal_comp_zeroSection, Work.Thom.CohMap_id]
    rfl
  rw [hcoe]
  exact hu

end

end Work.ThomBordism
