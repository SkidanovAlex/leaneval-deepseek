import Mathlib
import Submission.Work.ThomBordism.Interface
import Submission.Work.Orient.Closed
import Submission.Work.Cohomology.kronH_kernel_eq_torsion

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

namespace Work.ThomBordism

noncomputable section

open CategoryTheory AlgebraicTopology

/-- `H⁸` of a closed oriented `8`-manifold has an element of infinite order. -/
theorem exists_nonTorsion_H8 (V : Work.ThomBordism.Man8) [PathConnectedSpace V.pt] :
    ∃ u : (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj (TopCat.of V.pt))).homology 8,
      ∀ N : ℕ, 0 < N → (N : ℤ) • u ≠ 0 := by
  classical
  have : ConnectedSpace V.pt := inferInstance
  set X : SSet := TopCat.toSSet.obj (TopCat.of V.pt) with hX
  -- the fundamental class generates `H₈`
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
    haveI : Subsingleton ℤ := ⟨fun a b => by
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
    Work.Cohomology.exists_cochain_of_functional X 8 (e.hom.hom.comp loc : _ →ₗ[ℤ] ℤ) z
  refine ⟨Work.Cohomology.cohomologyClassOf ℤ X α hα, ?_⟩
  intro N hN hNu
  have h1 : Work.Cohomology.kronH ℤ X 8 (Work.Cohomology.cohomologyClassOf ℤ X α hα)
      ((Work.Cohomology.chainC ℤ X).homologyπ 8 z) ≠ 0 := by
    rw [Work.Cohomology.kronH_apply ℤ X α hα z, hval, hz]
    exact hφ
  have hNu' : N • (Work.Cohomology.cohomologyClassOf ℤ X α hα) = 0 := by
    rw [← natCast_zsmul]
    exact hNu
  have h2 : N • (Work.Cohomology.kronH ℤ X 8 (Work.Cohomology.cohomologyClassOf ℤ X α hα)) = 0 := by
    rw [← map_nsmul, hNu', map_zero]
  have h3 : (N • (Work.Cohomology.kronH ℤ X 8 (Work.Cohomology.cohomologyClassOf ℤ X α hα)))
      ((Work.Cohomology.chainC ℤ X).homologyπ 8 z) = 0 := by
    have h4 := congrArg (fun f : (Work.Cohomology.chainC ℤ X).homology 8 →ₗ[ℤ] ℤ =>
      f ((Work.Cohomology.chainC ℤ X).homologyπ 8 z)) h2
    simpa using h4
  rw [LinearMap.smul_apply] at h3
  exact h1 (nsmul_right_injective (M := ℤ) hN.ne' h3)

end

end Work.ThomBordism
