import Mathlib
import Submission.Work.Cohomology.KroneckerH
import Submission.Work.Cohomology.kronH_isIso
import Submission.Work.Cohomology.free_submodule_of_free_int
import Submission.Work.Cohomology.free_of_chain_retractions
import Submission.Work.Cohomology.uctDual_evaluation

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

attribute [local instance 5000] Submodule.module
attribute [local instance 5000] Submodule.Quotient.module

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- The `n`-chains of a simplicial set, with coefficients in `ℤ`, form a free `ℤ`-module: they are
the coproduct of copies of `ℤ` indexed by the `n`-simplices. -/
theorem chainC_X_free (X : SSet) (m : ℕ) :
    Module.Free ℤ ↥((Work.Cohomology.chainC ℤ X).X m) := by
  classical
  exact Module.Free.of_equiv'
    (Module.Free.directSum ℤ (fun _ : X _⦋m⦌ => ℤ))
    ((ModuleCat.coprodIsoDirectSum (fun _ : X _⦋m⦌ => ModuleCat.of ℤ ℤ)).toLinearEquiv).symm

/-- **A finitely generated abelian group is separated by its dual outside its torsion subgroup**:
an element of infinite order is detected by some `ℤ`-linear functional.

This goes through the classical structure of finitely generated modules over a PID: the quotient
`M ⧸ torsion M` is finitely generated and torsion-free, hence free, and on a free module a nonzero
element is detected by a coordinate functional. -/
theorem exists_linearMap_ne_zero_of_not_torsion {M : Type*} [AddCommGroup M] [Module ℤ M]
    [Module.Finite ℤ M] (x : M) (hx : ∀ N : ℕ, 0 < N → (N : ℕ) • x ≠ 0) :
    ∃ f : M →ₗ[ℤ] ℤ, f x ≠ 0 := by
  haveI : Module.Finite ℤ (M ⧸ Submodule.torsion ℤ M) := inferInstance
  haveI : Module.IsTorsionFree ℤ (M ⧸ Submodule.torsion ℤ M) := inferInstance
  haveI : Module.Free ℤ (M ⧸ Submodule.torsion ℤ M) := Module.free_of_finite_type_torsion_free'
  have hx' : x ∉ Submodule.torsion ℤ M := by
    rw [Submodule.mem_torsion_iff]
    rintro ⟨a, ha⟩
    refine hx _ (Int.natAbs_pos.mpr (nonZeroDivisors.coe_ne_zero a)) ?_
    rw [@Submonoid.smul_def ℤ M _ (DistribMulAction.toDistribSMul.toSMul)
      (nonZeroDivisors ℤ) a x] at ha
    rcases Int.natAbs_eq a.val with hn | hn
    · rw [hn] at ha
      rwa [Nat.cast_smul_eq_nsmul] at ha
    · rw [hn] at ha
      rw [neg_smul, neg_eq_zero] at ha
      rwa [Nat.cast_smul_eq_nsmul] at ha
  let b := Module.Free.chooseBasis ℤ (M ⧸ Submodule.torsion ℤ M)
  have hxbar : (Submodule.torsion ℤ M).mkQ x ≠ 0 := by
    intro h
    apply hx'
    have h2 : x ∈ (Submodule.torsion ℤ M).mkQ.ker := by
      rw [LinearMap.mem_ker]
      exact h
    rwa [Submodule.ker_mkQ] at h2
  have hb : b.repr ((Submodule.torsion ℤ M).mkQ x) ≠ 0 := fun h =>
    hxbar (b.repr.injective (by rw [h, map_zero]))
  obtain ⟨i, hi⟩ : ∃ i, b.repr ((Submodule.torsion ℤ M).mkQ x) i ≠ 0 := by
    by_contra h
    push Not at h
    exact hb (Finsupp.ext h)
  refine ⟨(Finsupp.lapply i).comp (b.repr.toLinearMap.comp (Submodule.torsion ℤ M).mkQ), ?_⟩
  simpa using hi

/-- **Every functional on the homology of a simplicial set is realised by a cocycle.**  For
`φ : Hₙ(X;ℤ) →ₗ ℤ` and a cycle `z`, there is a cocycle `α` whose value on `z` is `φ` of the class
of `z`.

The cocycle is produced by extending `φ` (pulled back to the cycles along `Zₙ ↠ Hₙ`) to all of
`Cₙ`: `Cₙ` retracts onto its cycles because `im d ⊆ C_{n-1}` is free, hence projective
(`exists_retraction_cycles`). -/
theorem exists_cochain_of_functional (X : SSet) (n : ℕ)
    (φ : ↥((Work.Cohomology.chainC ℤ X).homology n) →ₗ[ℤ] ℤ)
    (z : (Work.Cohomology.chainC ℤ X).cycles n) :
    ∃ α : (Work.Cohomology.chainC ℤ X).X n →ₗ[ℤ] ℤ,
      Work.Cohomology.cochainDiff ℤ X α = 0 ∧
        α (((Work.Cohomology.chainC ℤ X).iCycles n).hom z) =
          φ (((Work.Cohomology.chainC ℤ X).homologyπ n).hom z) := by
  have hproj : Module.Projective ℤ ↥(uctR (chainC ℤ X) n) := by
    haveI : Module.Free ℤ ↥((chainC ℤ X).X (n - 1)) := chainC_X_free X (n - 1)
    haveI : Module.Free ℤ ↥(uctR (chainC ℤ X) n) :=
      Module.Free.of_module_eq (free_submodule_of_free_int (uctR (chainC ℤ X) n))
    exact Module.Projective.of_free (R := ℤ) (P := ↥(uctR (chainC ℤ X) n))
  obtain ⟨ρ, hρ⟩ := exists_retraction_cycles (chainC ℤ X) n hproj
  let e := uctIsoToLinearEquiv (homologyZIso (chainC ℤ X) n)
  let ψ : (↥(uctZ (chainC ℤ X) n) ⧸ uctH (chainC ℤ X) n) →ₗ[ℤ] ℤ :=
    φ.comp e.symm.toLinearMap
  let g : ↥(uctZ (chainC ℤ X) n) →ₗ[ℤ] ℤ := ψ.comp (uctH (chainC ℤ X) n).mkQ
  refine ⟨g.comp ρ, ?_, ?_⟩
  · apply LinearMap.ext
    intro c
    show g (ρ (((chainC ℤ X).d (n + 1) n).hom c)) = 0
    have hmem : (((chainC ℤ X).d (n + 1) n).hom c) ∈ uctZ (chainC ℤ X) n := by
      show ((chainC ℤ X).d n (n - 1)).hom (((chainC ℤ X).d (n + 1) n).hom c) = 0
      have h := congrArg ModuleCat.Hom.hom
        (HomologicalComplex.d_comp_d (chainC ℤ X) (n + 1) n (n - 1))
      simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
      exact LinearMap.congr_fun h c
    have hρ' : ρ (((chainC ℤ X).d (n + 1) n).hom c) =
        (⟨(((chainC ℤ X).d (n + 1) n).hom c), hmem⟩ : ↥(uctZ (chainC ℤ X) n)) := by
      have h := LinearMap.congr_fun hρ
        (⟨(((chainC ℤ X).d (n + 1) n).hom c), hmem⟩ : ↥(uctZ (chainC ℤ X) n))
      simpa using h
    rw [hρ']
    show ψ ((uctH (chainC ℤ X) n).mkQ
      (⟨(((chainC ℤ X).d (n + 1) n).hom c), hmem⟩ : ↥(uctZ (chainC ℤ X) n))) = 0
    have hHmem : (⟨(((chainC ℤ X).d (n + 1) n).hom c), hmem⟩ : ↥(uctZ (chainC ℤ X) n))
        ∈ uctH (chainC ℤ X) n := by
      rw [mem_uctH]
      exact ⟨c, rfl⟩
    rw [show (uctH (chainC ℤ X) n).mkQ
        (⟨(((chainC ℤ X).d (n + 1) n).hom c), hmem⟩ : ↥(uctZ (chainC ℤ X) n)) = 0 from by
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact hHmem]
    rw [map_zero]
  · have hmemz : (((chainC ℤ X).iCycles n).hom z) ∈ uctZ (chainC ℤ X) n := by
      show ((chainC ℤ X).d n (n - 1)).hom (((chainC ℤ X).iCycles n).hom z) = 0
      have h := congrArg ModuleCat.Hom.hom
        (HomologicalComplex.iCycles_d (chainC ℤ X) n (n - 1))
      simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
      exact LinearMap.congr_fun h z
    have hρz : ρ (((chainC ℤ X).iCycles n).hom z) =
        (⟨(((chainC ℤ X).iCycles n).hom z), hmemz⟩ : ↥(uctZ (chainC ℤ X) n)) := by
      have h := LinearMap.congr_fun hρ
        (⟨(((chainC ℤ X).iCycles n).hom z), hmemz⟩ : ↥(uctZ (chainC ℤ X) n))
      simpa using h
    show g (ρ (((chainC ℤ X).iCycles n).hom z)) =
      φ (((chainC ℤ X).homologyπ n).hom z)
    rw [hρz]
    have hmk : (uctH (chainC ℤ X) n).mkQ
          (⟨(((chainC ℤ X).iCycles n).hom z), hmemz⟩ : ↥(uctZ (chainC ℤ X) n))
        = (uctH (chainC ℤ X) n).mkQ ((cycIsoZ (chainC ℤ X) n).hom z) := by
      congr 1
      exact Subtype.ext (cycIsoZ_hom_val (chainC ℤ X) n z).symm
    show ψ ((uctH (chainC ℤ X) n).mkQ
      (⟨(((chainC ℤ X).iCycles n).hom z), hmemz⟩ : ↥(uctZ (chainC ℤ X) n))) =
      φ (((chainC ℤ X).homologyπ n).hom z)
    rw [hmk]
    have he : e (((chainC ℤ X).homologyπ n) z)
        = (uctH (chainC ℤ X) n).mkQ ((cycIsoZ (chainC ℤ X) n).hom z) := by
      rw [uctIsoToLinearEquiv_apply]
      exact homologyZIso_apply (chainC ℤ X) n z
    show φ (e.symm ((uctH (chainC ℤ X) n).mkQ ((cycIsoZ (chainC ℤ X) n).hom z))) =
      φ (((chainC ℤ X).homologyπ n).hom z)
    rw [← he, LinearEquiv.symm_apply_apply]

theorem kronH_kernel_eq_torsion (X : SSet) (hfin : ∀ n : ℕ, Module.Finite ℤ ((Work.Cohomology.chainC ℤ X).homology n)) (n : ℕ) : ∀ y : (Work.Cohomology.chainC ℤ X).homology n, (∀ a : (Work.Cohomology.cochainC ℤ X).homology n, Work.Cohomology.kronH ℤ X n a y = 0) ↔ ∃ N : ℕ, 0 < N ∧ (N : ℤ) • y = 0 := by
  intro y
  constructor
  · intro h
    by_contra hnt
    have hx : ∀ N : ℕ, 0 < N → (N : ℕ) • y ≠ 0 := by
      intro N hN hN0
      exact hnt ⟨N, hN, by rw [natCast_zsmul]; exact hN0⟩
    obtain ⟨f, hf⟩ := exists_linearMap_ne_zero_of_not_torsion y hx
    obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective ((Work.Cohomology.chainC ℤ X).homologyπ n)).mp
      inferInstance y
    obtain ⟨α, hα, hval⟩ := exists_cochain_of_functional X n f z
    have hz0 : Work.Cohomology.kronH ℤ X n (Work.Cohomology.cohomologyClassOf ℤ X α hα) y = 0 :=
      h _
    rw [← hz, Work.Cohomology.kronH_apply ℤ X α hα z, hval, hz] at hz0
    exact hf hz0
  · rintro ⟨N, hN, hNy⟩ a
    have hNy' : N • y = 0 := by rw [← natCast_zsmul]; exact hNy
    have hz : N • (Work.Cohomology.kronH ℤ X n a y) = 0 := by
      rw [← map_nsmul, hNy', map_zero]
    exact nsmul_right_injective (M := ℤ) hN.ne' (by simpa using hz)

end

end Work.Cohomology
