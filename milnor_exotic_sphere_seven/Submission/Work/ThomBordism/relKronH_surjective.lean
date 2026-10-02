import Mathlib
import Submission.Work.Tubular.relKronecker_chain
import Submission.Work.Tubular.RelAPI
import Submission.Work.Cohomology.relChains_free
import Submission.Work.Cohomology.uctDual
import Submission.Work.Cohomology.uctDual_evaluation
import Submission.Work.Cohomology.relChainsProjective
import Submission.Work.Cohomology.free_submodule_of_free_int

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The relative Kronecker pairing is surjective

`Work.Tubular.relKronH X A n : H^n(X,A;ℤ) →ₗ[ℤ] (H_n(X,A;ℤ) →ₗ[ℤ] ℤ)` is the relative Kronecker
pairing (the relative counterpart of `Work.Cohomology.kronH`), computed on the classes of a relative
cocycle `α` and of a relative cycle `cc` by evaluating `α` on a lift of `cc`
(`Work.Tubular.relKronH_apply_of_relDualProj`).

Here we prove that it is **surjective** whenever the relative chains `C_m(X,A)` are degreewise free
(which they always are, `Work.Cohomology.relChains_free`): this is the surjectivity half of the
universal coefficient theorem.  The proof is that of the absolute statement
(`Work.ThomBordism.kronH_surjective`, `Submission/Work/ThomBordism/evaluation_kernel_torsion_of_pd.lean`),
run for the relative chain complex.

A functional `χ` on `H_n(X,A;ℤ)` is first pulled back to the concrete quotient `Z_n ⧸ B_n` and then
to the cycles `Z_n ⊆ C_n(X,A)`.  Since `Z_n` retracts onto `C_n(X,A)` — the image of the differential
`d_{n+1}` is a subgroup of the free module `C_n(X,A)`, hence free and hence projective
(`Work.Cohomology.free_submodule_of_free_int`, `Work.Cohomology.exists_retraction_cycles`) — the
functional extends to a functional `w` on `C_n(X,A)` which kills the boundaries.  Under the
identification of the relative cochains with the dual of the relative chains
(`Work.Cohomology.relDualEquiv`) the functional `w` corresponds to a relative cochain `α` vanishing
on the chains of `A` whose coboundary is zero: the class of `α` pairs with `χ`.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

attribute [local instance 5000] Submodule.module
attribute [local instance 5000] Submodule.Quotient.module

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

namespace Work.ThomBordism

open Work.Cohomology

noncomputable section

/-- **The relative Kronecker pairing is surjective.**  Every `ℤ`-linear functional on the relative
homology `H_n(X,A;ℤ)` is the pairing with some relative cohomology class, provided the relative
chains are degreewise free. -/
theorem relKronH_surjective (X : TopCat) (A : Set X) (n : ℕ)
    (hfree : ∀ m, Module.Free ℤ ↥((Work.Cohomology.relChains X A).X m)) :
    Function.Surjective (Work.Tubular.relKronH X A n) := by
  intro χ
  -- the image of the differential is a subgroup of the free module `C_n(X,A)`, hence free
  haveI : Module.Free ℤ ↥((relChains X A).X (n - 1)) := hfree (n - 1)
  haveI : Module.Free ℤ ↥(uctR (relChains X A) n) := by
    rw [show Submodule.module (uctR (relChains X A) n)
      = AddCommGroup.toIntModule ↥(uctR (relChains X A) n) from Subsingleton.elim _ _]
    exact free_submodule_of_free_int _
  have hproj : Module.Projective ℤ ↥(uctR (relChains X A) n) := inferInstance
  obtain ⟨ρ, hρ⟩ := exists_retraction_cycles (relChains X A) n hproj
  -- the functional on `Z_n ⧸ B_n`, pulled back to `Z_n`, extended to `C_n(X,A)`
  let χ' : (↥(uctZ (relChains X A) n) ⧸ uctH (relChains X A) n) →ₗ[ℤ] ℤ :=
    χ.comp (homologyZIso (relChains X A) n).inv.hom
  let χt : ↥(uctZ (relChains X A) n) →ₗ[ℤ] ℤ := χ'.comp (uctH (relChains X A) n).mkQ
  let w : ↥((relChains X A).X n) →ₗ[ℤ] ℤ := χt.comp ρ
  -- `w` kills the boundaries
  have hw : ∀ y : ↥((relChains X A).X (n + 1)),
      w (((relChains X A).d (n + 1) n).hom y) = 0 := by
    intro y
    have hcyc : ((relChains X A).d (n + 1) n).hom y ∈ uctZ (relChains X A) n := by
      rw [uctZ, LinearMap.mem_ker]
      have h := congrArg (fun (g : (relChains X A).X (n + 1) ⟶ (relChains X A).X (n - 1)) =>
        ModuleCat.Hom.hom g y) (HomologicalComplex.d_comp_d (relChains X A) (n + 1) n (n - 1))
      exact h
    have hfix : ρ (((relChains X A).d (n + 1) n).hom y) = ⟨_, hcyc⟩ := by
      have h := LinearMap.congr_fun hρ (⟨_, hcyc⟩ : ↥(uctZ (relChains X A) n))
      simpa using h
    have hker : (⟨_, hcyc⟩ : ↥(uctZ (relChains X A) n)) ∈ uctH (relChains X A) n :=
      (mem_uctH _ n _).mpr ⟨y, rfl⟩
    show w (((relChains X A).d (n + 1) n).hom y) = 0
    simp only [w, LinearMap.comp_apply]
    rw [hfix]
    simp only [χt, χ', LinearMap.comp_apply]
    rw [show (uctH (relChains X A) n).mkQ (⟨_, hcyc⟩ : ↥(uctZ (relChains X A) n)) = 0 from by
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]; exact hker]
    simp
  -- the relative cochain associated with `w`
  have hα : relDiffLM ℤ X A n (relDualEquiv X A n w) = 0 := by
    have hmap : relDualLM X (n + 1) (relDiffLM ℤ X A n (relDualEquiv X A n w)).1
        = (relDualLM X n (relDualEquiv X A n w).1).comp
            ((singularChains ℤ X).d (n + 1) n).hom :=
      relDualDiff_apply_coe X A n (relDualEquiv X A n w)
    have hzero : relDualLM X (n + 1) (relDiffLM ℤ X A n (relDualEquiv X A n w)).1 = 0 := by
      rw [hmap, relDualEquiv_apply_coe X A n w]
      rw [LinearMap.comp_assoc, ← relDualProj_comm_lm X A n, ← LinearMap.comp_assoc,
        show w.comp ((relChains X A).d (n + 1) n).hom = 0 from LinearMap.ext hw]
      simp
    apply Subtype.ext
    exact hzero
  refine ⟨relClassOf ℤ X A (relDualEquiv X A n w) hα, ?_⟩
  apply LinearMap.ext
  intro b
  obtain ⟨cc, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((relChains X A).homologyπ n)).mp inferInstance b
  obtain ⟨zhat, hzhat⟩ := relDualProj_surjective X A n (((relChains X A).iCycles n) cc)
  rw [Work.Tubular.relKronH_apply_of_relDualProj n (relDualEquiv X A n w) hα cc zhat hzhat]
  change relDualLM X n (relDualEquiv X A n w).1 zhat = χ (((relChains X A).homologyπ n).hom cc)
  rw [show relDualLM X n (relDualEquiv X A n w).1 = w.comp (relDualProj X A n).hom from
    relDualEquiv_apply_coe X A n w]
  rw [LinearMap.comp_apply, hzhat]
  have hcyc : ((relChains X A).iCycles n).hom cc ∈ uctZ (relChains X A) n := by
    rw [uctZ, LinearMap.mem_ker]
    have h : ModuleCat.Hom.hom ((relChains X A).iCycles n ≫ (relChains X A).d n (n - 1)) cc = 0 := by
      rw [HomologicalComplex.iCycles_d, ModuleCat.hom_zero, LinearMap.zero_apply]
    rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h
  have hfix : ρ (((relChains X A).iCycles n).hom cc) = ⟨_, hcyc⟩ := by
    have h := LinearMap.congr_fun hρ (⟨_, hcyc⟩ : ↥(uctZ (relChains X A) n))
    simpa using h
  show w (((relChains X A).iCycles n).hom cc) = χ (((relChains X A).homologyπ n).hom cc)
  simp only [w, LinearMap.comp_apply]
  rw [hfix]
  simp only [χt, χ', LinearMap.comp_apply]
  have hh : (homologyZIso (relChains X A) n).inv.hom
        ((uctH (relChains X A) n).mkQ ((cycIsoZ (relChains X A) n).hom cc))
      = (((relChains X A).homologyπ n).hom cc) := by
    rw [← homologyZIso_apply _ n cc]
    exact CategoryTheory.Iso.hom_inv_id_apply _ _
  have hv : ((cycIsoZ (relChains X A) n).hom cc : ↥((relChains X A).X n))
      = ((relChains X A).iCycles n).hom cc := cycIsoZ_hom_val _ n cc
  rw [show (⟨_, hcyc⟩ : ↥(uctZ (relChains X A) n)) = (cycIsoZ (relChains X A) n).hom cc from
    Subtype.ext hv.symm, hh]

end

end Work.ThomBordism
