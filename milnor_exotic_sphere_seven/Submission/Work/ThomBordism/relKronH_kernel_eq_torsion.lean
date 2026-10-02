import Mathlib
import Submission.Work.Tubular.relKronecker_chain
import Submission.Work.Tubular.RelAPI
import Submission.Work.Cohomology.kronH_kernel_eq_torsion
import Submission.Work.Tubular.exists_relKronH_eval_iso
import Submission.Work.Cohomology.uctDual
import Submission.Work.Cohomology.uctDual_evaluation
import Submission.Work.Cohomology.relChains_free
import Submission.Work.ThomBordism.chain_extends_up_to_smul
import Submission.Work.ThomBordism.exists_smul_extends_of_finite_quotient

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The kernel of the relative Kronecker pairing is the torsion subgroup

`Work.Tubular.relKronH X A n : H^n(X,A;ℤ) →ₗ[ℤ] (H_n(X,A;ℤ) →ₗ[ℤ] ℤ)` is the relative Kronecker
pairing.  The classical universal coefficient theorem for the (degreewise free) relative chain
complex `C_*(X,A)` reads

`H^n(X,A;ℤ) ≅ Hom(H_n(X,A;ℤ), ℤ) ⊕ Ext(H_{n-1}(X,A;ℤ), ℤ)`,

the Kronecker pairing being the projection onto the first summand; as `Ext` of a finitely generated
group is its torsion subgroup, the pairing kills exactly the torsion classes of `H^n(X,A;ℤ)`
(provided `H_{n-1}(X,A;ℤ)` is finitely generated, so that the `Ext`-term is a finite group).  The
main theorem `Work.ThomBordism.relKronH_kernel_eq_torsion` states the consequence that is used in
the chapters above: a class of infinite order is detected by some relative homology class.

## Proof

A class of `H^n(X,A;ℤ)` is represented by a relative cocycle `φ`; transported along
`Work.Cohomology.relDualEquiv` it is a functional `ψ` on the relative `n`-chains.  If it is killed by
the pairing then `ψ` vanishes on all relative `n`-cycles (`relKronH_relClass_apply_cycle`), hence
factors through the boundaries `B_{n-1} ⊆ Z_{n-1} ⊆ C_{n-1}`.  As `Z_{n-1}/B_{n-1} = H_{n-1}(X,A;ℤ)`
is finitely generated, some positive multiple of that functional on `B_{n-1}` extends to `C_{n-1}`
— this is `Work.ThomBordism.chain_extends_up_to_smul`, whose arithmetic input is the purely
algebraic `Work.ThomBordism.exists_smul_extends_of_finite_quotient` — so a positive multiple of `φ`
is a coboundary and the class is torsion (`smul_homologypi_cycles_eq_zero` turns the coboundary
relation into the vanishing of the multiple of the class).

## Main result

* `Work.ThomBordism.relKronH_kernel_eq_torsion`
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

attribute [local instance 5000] Submodule.module
attribute [local instance 5000] Submodule.Quotient.module
attribute [local instance 100] ZSMul.toSMul

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.ThomBordism

open Work.Cohomology
open Work.Tubular

noncomputable section

/-! ## The pairing of a cocycle with a cycle -/

/-- **The relative Kronecker pairing is computed on cycles.**  For a relative cocycle `φ` and a
relative cycle `cc`, the value of the pairing of their classes is the evaluation of the functional
on the relative chains corresponding to `φ` (the inverse image under `relDualEquiv`) on the cycle
`cc`. -/
lemma relKronH_relClass_apply_cycle (X : TopCat) (A : Set X) (n : ℕ)
    (φ : ↥(relKern ℤ X A n)) (hφ : relDiffLM ℤ X A n φ = 0)
    (cc : (relChains X A).cycles n) :
    Work.Tubular.relKronH X A n (relClassOf ℤ X A φ hφ)
        ((relChains X A).homologyπ n cc)
      = ((relDualEquiv X A n).symm φ) ((relChains X A).iCycles n cc) := by
  obtain ⟨z, hz⟩ := relDualProj_surjective X A n ((relChains X A).iCycles n cc)
  rw [Work.Tubular.relKronH_apply_of_relDualProj n φ hφ cc z hz, ← hz, ← LinearMap.comp_apply,
    relDualEquiv_symm_comp X A n φ]
  rfl

/-! ## A multiple of a cycle that is a boundary dies in homology -/

/-- **If a multiple `N • z` of a cycle is a boundary, then `N • [z] = 0` in homology.** -/
lemma smul_homologypi_cycles_eq_zero (D : CochainComplex (ModuleCat ℤ) ℕ) (m : ℕ)
    (z : D.cycles (m + 1)) (x : ↥(D.X m)) (N : ℕ)
    (hx : (D.d m (m + 1)).hom x = (N : ℤ) • ((D.iCycles (m + 1)).hom z)) :
    (N : ℤ) • ((D.homologyπ (m + 1)).hom z) = 0 := by
  have h1 : (N : ℤ) • z = D.toCycles m (m + 1) x := by
    apply (ModuleCat.mono_iff_injective (D.iCycles (m + 1))).mp inferInstance
    have hti : (D.iCycles (m + 1)).hom ((D.toCycles m (m + 1)).hom x)
        = (D.d m (m + 1)).hom x := by
      have h := ConcreteCategory.congr_hom (HomologicalComplex.toCycles_i D m (m + 1)) x
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
    simp only [map_smul]
    rw [hti, hx]
  have hzero : (D.homologyπ (m + 1)).hom (D.toCycles m (m + 1) x) = 0 := by
    have h := ConcreteCategory.congr_hom
      (HomologicalComplex.toCycles_comp_homologyπ D m (m + 1)) x
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_zero, LinearMap.comp_apply,
      LinearMap.zero_apply] using h
  rw [← map_smul, h1, hzero]

/-! ## The main theorem -/

/-- A non-torsion relative cohomology class of a pair is detected by some relative homology class,
provided the homology one degree below is finitely generated.  This is the kernel of the relative
Kronecker pairing being the torsion subgroup: the classical universal coefficient theorem
`H^n ≅ Hom(H_n,ℤ) ⊕ Ext(H_{n-1},ℤ)` for the relative chain complex, the Kronecker pairing being the
projection onto the first summand, with `Ext` of a finitely generated group torsion.

Available in the workspace: the absolute analogue `Work.Cohomology.kronH_kernel_eq_torsion`, and the
free case `Work.Tubular.exists_relKronH_eval_iso`; missing is the `Ext` term.

Route.  `relChains X A` is degreewise free (`Work.Cohomology.relChainsProjective`).  A cocycle `α̃`
in the kernel kills all cycles, hence factors as `C_n ↠ C_n/Z_n ≅ B_{n-1} → ℤ`; multiplying by
`N = |Ext(H_{n-1},ℤ)|` (finite, as `H_{n-1}` is finitely generated) extends that functional to
`C_{n-1}`, so `N · [α̃] = 0`: every element of the kernel is torsion.  Conversely a torsion class is
killed by the pairing (a coboundary pairs to zero with every cycle).  A non-torsion `α` therefore has
non-zero image under `relKronH`, giving `β`. -/
theorem relKronH_kernel_eq_torsion {X : TopCat} {A : Set X} {n : ℕ}
    (hfin : Module.Finite ℤ ((Work.Cohomology.relChains X A).homology (n - 1)))
    (α : (Work.Cohomology.relComplex ℤ X A).homology n)
    (hnt : ∀ N : ℕ, 0 < N → (N : ℤ) • α ≠ 0) :
    ∃ β : (Work.Cohomology.relChains X A).homology n,
      Work.Tubular.relKronH X A n α β ≠ 0 := by
  by_contra hcon
  simp only [not_exists, ne_eq, not_not] at hcon
  rcases n with _ | m
  · -- ## `n = 0`: every `0`-chain is a cycle, so a functional killing the cycles vanishes
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
      ((relComplex ℤ X A).homologyπ 0)).mp inferInstance α
    set ψ : ↥((relChains X A).X 0) →ₗ[ℤ] ℤ :=
      (relDualEquiv X A 0).symm (relOfCycle X A 0 z) with hψdef
    have hkill : ∀ cc : (relChains X A).cycles 0,
        ψ ((relChains X A).iCycles 0 cc) = 0 := by
      intro cc
      have h1 : Work.Tubular.relKronH X A 0
          (relClassOf ℤ X A (relOfCycle X A 0 z) (relDiffLM_relOfCycle X A 0 z))
          ((relChains X A).homologyπ 0 cc) = 0 := by
        rw [relClassOf_relOfCycle X A 0 z]
        exact hcon _
      rw [relKronH_relClass_apply_cycle X A 0 (relOfCycle X A 0 z)
        (relDiffLM_relOfCycle X A 0 z) cc] at h1
      simpa only [hψdef] using h1
    have hkillZ : ∀ u : ↥(uctZ (relChains X A) 0),
        ψ ((u : ↥(uctZ (relChains X A) 0)) : ↥((relChains X A).X 0)) = 0 := by
      intro u
      set cc : (relChains X A).cycles 0 := (cycIsoZ (relChains X A) 0).inv u with hcc
      have hzu : (cycIsoZ (relChains X A) 0).hom cc = u := by
        rw [hcc]; exact Iso.inv_hom_id_apply _ _
      have hval := cycIsoZ_hom_val (relChains X A) 0 cc
      rw [hzu] at hval
      have hzi : ((relChains X A).iCycles 0) cc
          = ((u : ↥(uctZ (relChains X A) 0)) : ↥((relChains X A).X 0)) := hval.symm
      rw [← hzi]
      exact hkill cc
    have hψ0 : ψ = 0 := by
      ext x
      have hx : x ∈ uctZ (relChains X A) 0 := by
        rw [uctZ, LinearMap.mem_ker,
          show (relChains X A).d 0 (0 - 1) = 0 from
            HomologicalComplex.shape _ 0 0 (by simp [ComplexShape.down])]
        simp
      exact hkillZ ⟨x, hx⟩
    have hφ0 : relOfCycle X A 0 z = 0 := by
      have h2 : (relDualEquiv X A 0) ψ = 0 := by rw [hψ0, map_zero]
      rwa [hψdef, LinearEquiv.apply_symm_apply] at h2
    have hz0 : z = 0 := by
      apply (ModuleCat.mono_iff_injective ((relComplex ℤ X A).iCycles 0)).mp inferInstance
      rw [show ((relComplex ℤ X A).iCycles 0) z = relOfCycle X A 0 z from rfl, hφ0, map_zero]
    have hzero : (1 : ℤ) • ((relComplex ℤ X A).homologyπ 0).hom z = 0 := by
      rw [hz0, map_zero, smul_zero]
    exact (hnt 1 (by norm_num)) hzero
  · -- ## `n = m + 1`: the extension of the functional on the boundaries
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
      ((relComplex ℤ X A).homologyπ (m + 1))).mp inferInstance α
    set ψ : ↥((relChains X A).X (m + 1)) →ₗ[ℤ] ℤ :=
      (relDualEquiv X A (m + 1)).symm (relOfCycle X A (m + 1) z) with hψdef
    have hkill : ∀ cc : (relChains X A).cycles (m + 1),
        ψ ((relChains X A).iCycles (m + 1) cc) = 0 := by
      intro cc
      have h1 : Work.Tubular.relKronH X A (m + 1)
          (relClassOf ℤ X A (relOfCycle X A (m + 1) z) (relDiffLM_relOfCycle X A (m + 1) z))
          ((relChains X A).homologyπ (m + 1) cc) = 0 := by
        rw [relClassOf_relOfCycle X A (m + 1) z]
        exact hcon _
      rw [relKronH_relClass_apply_cycle X A (m + 1) (relOfCycle X A (m + 1) z)
        (relDiffLM_relOfCycle X A (m + 1) z) cc] at h1
      simpa only [hψdef] using h1
    have hkillZ : ∀ u : ↥(uctZ (relChains X A) (m + 1)),
        ψ ((u : ↥(uctZ (relChains X A) (m + 1))) : ↥((relChains X A).X (m + 1))) = 0 := by
      intro u
      set cc : (relChains X A).cycles (m + 1) := (cycIsoZ (relChains X A) (m + 1)).inv u with hcc
      have hzu : (cycIsoZ (relChains X A) (m + 1)).hom cc = u := by
        rw [hcc]; exact Iso.inv_hom_id_apply _ _
      have hval := cycIsoZ_hom_val (relChains X A) (m + 1) cc
      rw [hzu] at hval
      have hzi : ((relChains X A).iCycles (m + 1)) cc
          = ((u : ↥(uctZ (relChains X A) (m + 1))) : ↥((relChains X A).X (m + 1))) := hval.symm
      rw [← hzi]
      exact hkill cc
    have hψker : ∀ z' : ↥((relChains X A).X (m + 1)),
        ((relChains X A).d (m + 1) m).hom z' = 0 → ψ z' = 0 := by
      intro z' hz'
      exact hkillZ ⟨z', LinearMap.mem_ker.mpr hz'⟩
    -- the extension of functionals on the boundaries to the cycles, up to a multiple
    have hA : ∀ f : ↥(uctH (relChains X A) m) →ₗ[ℤ] ℤ, ∃ N : ℕ, 0 < N ∧
        ∃ g : ↥(uctZ (relChains X A) m) →ₗ[ℤ] ℤ,
          ∀ b : ↥(uctH (relChains X A) m), g ↑b = (N : ℤ) • f b := by
      intro f
      exact exists_smul_extends_of_finite_quotient (uctH (relChains X A) m)
        (by
          -- the two `ℤ`-module structures on the quotient differ (`Submodule.Quotient.module` and
          -- the canonical one), but there is only one such structure on a fixed abelian group
          rw [show AddCommGroup.toIntModule (↥(uctZ (relChains X A) m) ⧸ uctH (relChains X A) m)
              = Submodule.Quotient.module (uctH (relChains X A) m) from Subsingleton.elim _ _]
          haveI : Module.Finite ℤ ↥((relChains X A).homology m) := hfin
          exact Module.Finite.equiv (uctIsoToLinearEquiv (homologyZIso (relChains X A) m))) f
    obtain ⟨N, hN, F, hF⟩ := chain_extends_up_to_smul (relChains X A)
      (fun k => relChains_free X A k) m hA ψ hψker
    -- the cochain of degree `m` whose coboundary is `N • φ`
    set Φ : ↥(relKern ℤ X A m) := relDualEquiv X A m F with hΦdef
    have hΦdiff : ((relComplex ℤ X A).d m (m + 1)).hom Φ
        = (N : ℤ) • ((relComplex ℤ X A).iCycles (m + 1)).hom z := by
      have hcomm : ((relComplex ℤ X A).d m (m + 1)).hom.comp ((relDualIso X A m).hom.hom)
          = ((relDualIso X A (m + 1)).hom.hom).comp
            (((dualComplex ℤ (relChains X A)).d m (m + 1)).hom) := by
        have h := congrArg (fun (g : (dualComplex ℤ (relChains X A)).X m ⟶
            (relComplex ℤ X A).X (m + 1)) => ModuleCat.Hom.hom g) (relDualIso_comm X A m)
        simpa only [ModuleCat.hom_comp] using h
      have h1 := LinearMap.congr_fun hcomm F
      simp only [LinearMap.comp_apply] at h1
      rw [hΦdef]
      rw [show (relDualEquiv X A m) F = (relDualIso X A m).hom.hom F from rfl, h1]
      rw [show ((dualComplex ℤ (relChains X A)).d m (m + 1)).hom F
          = F.comp ((relChains X A).d (m + 1) m).hom from uct_d_apply (relChains X A) m F,
        hF, map_smul]
      congr 1
      rw [hψdef]
      rw [show (relDualIso X A (m + 1)).hom.hom
            ((relDualEquiv X A (m + 1)).symm (relOfCycle X A (m + 1) z))
          = (relDualEquiv X A (m + 1))
              ((relDualEquiv X A (m + 1)).symm (relOfCycle X A (m + 1) z)) from rfl,
        LinearEquiv.apply_symm_apply]
      rfl
    exact (hnt N hN) (smul_homologypi_cycles_eq_zero (relComplex ℤ X A) m z Φ N hΦdiff)

end

end Work.ThomBordism
