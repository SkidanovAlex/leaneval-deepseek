import Submission.Work.Tubular.modelClass_fibre_span_top

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

/-!
# The punctured model Thom class restricts to a generator on every fibre

The companion of `Submission/Work/Tubular/modelClass_fibre_span_top.lean` for the *punctured* model
class `Work.Thom.Mpun n B`, the class of the pair `(B × ℝⁿ, B × (ℝⁿ∖0))` obtained from `Mn n B` by
the isomorphism of relative cohomology induced by the inclusion of the sphere-bundle pair into the
punctured pair (`Work.Thom.Mpun_spec`, `Work.Thom.Mpun_isModel`, `Work.Thom.Mpun_natural`).  The
proof is the same argument with `Sph ↦ Punct` and `Mn ↦ Mpun`; nothing new is needed, because the
two model classes satisfy the same two structural lemmas.

The punctured model `Mpun` is the local model out of which the Thom class of a bundle is glued
(`Work.Thom.localThomOfChart` is by construction the pullback of `Mpun` along a chart), so this is
the input of item 3 of the chapter (the fibrewise-generator property of the Thom class).
-/

open CategoryTheory Limits
open scoped Topology

namespace Work.Tubular

noncomputable section

/-- **The punctured model class restricts to a generator on every fibre.** -/
theorem modelClassPunct_fibre_span_top (n : ℕ) (B : Type) [TopologicalSpace B] (b : B) :
    Submodule.span ℤ
      {((Work.Thom.relCohMap (Work.Thom.baseIncl B ({b} : Set B) n)
          (Work.Thom.Punct ({b} : Set B) n) (Work.Thom.Punct B n)
          (fun p hp => hp) ℤ n).hom (Work.Thom.Mpun n B))}
      = ⊤ := by
  rw [Work.Thom.Mpun_natural n B ({b} : Set B)]
  refine Submodule.eq_top_iff'.mpr fun y => ?_
  rw [Submodule.mem_span_singleton]
  obtain ⟨x, hx⟩ := (Work.Thom.Mpun_isModel n ↥({b} : Set B) 0).2
    ((Nat.zero_add n).symm ▸ y : Work.Thom.RelCoh ℤ (0 + n)
      (↥({b} : Set B) × EuclideanSpace ℝ (Fin n)) (Work.Thom.Punct (↥({b} : Set B)) n))
  obtain ⟨m, hm⟩ := Work.Cohomology.exists_smul_oneH (TopCat.of ↥({b} : Set B)) x
  have hbase : (Work.Thom.mixedCupC ℤ (Work.Thom.Punct (↥({b} : Set B)) n) 0 n)
      ((Work.Thom.CohMap (Work.Thom.projFstA ↥({b} : Set B) n) ℤ 0).hom
        (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥({b} : Set B)))))
      (Work.Thom.Mpun n ↥({b} : Set B))
      = (Nat.zero_add n).symm ▸ Work.Thom.Mpun n ↥({b} : Set B) := by
    rw [Work.Thom.CohMap_oneH, Work.Thom.mixedCupC_eq_mixedCup, Work.Thom.mixedCup_oneH_zero]
  have hchain : (Work.Thom.mixedCupC ℤ (Work.Thom.Punct (↥({b} : Set B)) n) 0 n)
      ((Work.Thom.CohMap (Work.Thom.projFstA ↥({b} : Set B) n) ℤ 0).hom
        (m • Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥({b} : Set B)))))
      (Work.Thom.Mpun n ↥({b} : Set B))
      = m • ((Nat.zero_add n).symm ▸ Work.Thom.Mpun n ↥({b} : Set B)) := by
    rw [map_zsmul, map_zsmul, ← hbase]
    rfl
  have hfx : (Work.Thom.mixedCupC ℤ (Work.Thom.Punct (↥({b} : Set B)) n) 0 n)
      ((Work.Thom.CohMap (Work.Thom.projFstA ↥({b} : Set B) n) ℤ 0).hom x)
      (Work.Thom.Mpun n ↥({b} : Set B))
      = m • ((Nat.zero_add n).symm ▸ Work.Thom.Mpun n ↥({b} : Set B)) := by
    rw [hm]
    exact hchain
  have hy := hx.symm.trans hfx
  have h5 := congrArg (fun w => (Nat.zero_add n) ▸ w) hy
  rw [relCoh_cast_symm_cast, relCoh_cast_zsmul, relCoh_cast_symm_cast] at h5
  exact ⟨m, (int_smul_eq_zsmul (inferInstance : Module ℤ (Work.Thom.RelCoh ℤ n
    (↥({b} : Set B) × EuclideanSpace ℝ (Fin n)) (Work.Thom.Punct (↥({b} : Set B)) n))) m
      (Work.Thom.Mpun n ↥({b} : Set B))).trans h5.symm⟩

end

end Work.Tubular
