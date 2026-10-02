import Mathlib
import Submission.Work.Cohomology.singularCohomology_zero
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.cupNaturalH
import Submission.Work.Cohomology.Pullback
import Submission.Work.Cohomology.h0Evaluation
import Submission.Work.Cohomology.pi0Projection
import Submission.Work.Cohomology.pi0Proj_sgen_of_mem
import Submission.Work.Cohomology.pi0Proj_sgen_of_not_mem
import Submission.Work.Cohomology.cokernelIsoInt

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The cokernel of `H⁰(Y; ℤ) → H⁰(Z; ℤ)` for a space `Z` with exactly two path components

Let `Z` be a topological space with exactly two path components (there are points `a b : Z` such
that every point of `Z` is joinable to `a` or to `b`, while `a` and `b` are not joinable to each
other), let `Y` be path connected and let `f : Z ⟶ Y` be continuous.  Then

`f* : H⁰(Y; ℤ) ⟶ H⁰(Z; ℤ)`

has cokernel `ℤ`.

This is the degree-zero part of "`H⁰` is the ring of locally constant functions": a degree-zero
cocycle on `Z` is constant on the generators lying in a single path component, so it is determined
by its two values at the two components.  The functional

`Φ : H⁰(Z;ℤ) →ₗ[ℤ] ℤ,  x ↦ x(s_a) - x(s_b)`

(where `s_a`, `s_b` are the `0`-simplices given by `a` and `b`) is surjective — the indicator of
one of the components is a cocycle, `Work.Cohomology.pi0Proj` — and its kernel is exactly the
image of `f*`: a cocycle on `Y` is constant on the generators of `Y` because `Y` is path connected,
so `f*` lands in `ker Φ`, while a cocycle of `Z` killed by `Φ` is constant on `Z` and hence the
pullback of a multiple of the augmentation of `Y`.  The first isomorphism theorem in the form
`Work.Cohomology.cokernelIsoInt` then computes the cokernel.

The lemmas about constancy of a `0`-cocycle on the elements of a path component are proved here
(`tcc_sgen_congr_of_pi0`, `tcc_sgen_congr_of_joined`) so that the file only depends on the stable
parts of the library.
-/

open CategoryTheory AlgebraicTopology Limits Simplicial
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-! ## Constancy of `0`-cocycles on path components -/

/-- A linear functional on the `0`-chains of `X` which kills the differential `d₁` takes the same
value on all `0`-simplices representing the same path component. -/
theorem tcc_sgen_congr_of_pi0 {X : TopCat}
    (f : (singularChains ℤ X).X 0 →ₗ[ℤ] ℤ)
    (hf : f.comp ((singularChains ℤ X).d 1 0).hom = 0)
    {s s' : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk 0))}
    (h : SSet.π₀.mk s = SSet.π₀.mk s') :
    f (sgen ℤ X s) = f (sgen ℤ X s') := by
  have hmem : (singularChains ℤ X).d 1 0 ≫ ModuleCat.ofHom f = 0 := by
    apply ModuleCat.hom_ext
    rw [ModuleCat.hom_comp, ModuleCat.hom_zero, ModuleCat.hom_ofHom]
    exact hf
  have hmem' : ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).d 1 0
      ≫ ModuleCat.ofHom f = 0 := by
    rw [show ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).d 1 0 =
      (singularChains ℤ X).d 1 0 from rfl]
    exact hmem
  obtain ⟨hh, hfac⟩ := CokernelCofork.IsColimit.desc'
    (SSet.isColimitCokernelCoforkChainComplexDOneZero (TopCat.toSSet.obj X) (ModuleCat.of ℤ ℤ))
    (ModuleCat.ofHom f) hmem'
  have key : ∀ s, f (sgen ℤ X s) =
      ModuleCat.Hom.hom hh
        (ModuleCat.Hom.hom (Sigma.ι
          (fun _ : SSet.π₀ (TopCat.toSSet.obj X) => ModuleCat.of ℤ ℤ)
          (SSet.π₀.mk s)) 1) := by
    intro s
    rw [show f (sgen ℤ X s) = ModuleCat.Hom.hom
        (SSet.ιChainComplex (TopCat.toSSet.obj X) (R := ModuleCat.of ℤ ℤ) s
          ≫ ModuleCat.ofHom f) 1 from by
      rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
      rfl]
    rw [← hfac, CokernelCofork.π_ofπ]
    rw [← Category.assoc, SSet.π₀.comp_fromChainComplexXZero]
    rw [ModuleCat.hom_comp, LinearMap.comp_apply]
    rfl
  rw [key s, key s', h]

/-- A linear functional on the `0`-chains of `X` which kills the differential `d₁` takes the same
value at two points joined by a path. -/
theorem tcc_sgen_congr_of_joined {X : TopCat}
    (f : (singularChains ℤ X).X 0 →ₗ[ℤ] ℤ)
    (hf : f.comp ((singularChains ℤ X).d 1 0).hom = 0)
    {x y : X} (h : Joined x y) :
    f (sgen ℤ X ((TopCat.toSSetObj₀Equiv (X := X)).symm x))
      = f (sgen ℤ X ((TopCat.toSSetObj₀Equiv (X := X)).symm y)) := by
  refine tcc_sgen_congr_of_pi0 f hf ?_
  rw [← TopCat.zerothHomotopyEquiv_mk x, ← TopCat.zerothHomotopyEquiv_mk y,
    TopCat.zerothHomotopyEquiv, Equiv.coe_fn_mk]
  exact congrArg _ (ZerothHomotopy.sound h.somePath)

/-! ## Elementary bridges -/

/-- `sgen` and `h0Gen` are the same generator of the degree-zero chains. -/
theorem tcc_sgen_eq_gen (T : TopCat)
    (s : (TopCat.toSSet.obj T).obj (Opposite.op (SimplexCategory.mk 0))) :
    sgen ℤ T s = h0Gen (TopCat.toSSet.obj T) s := rfl

/-- The hypothesis of the constancy lemmas, in the form in which it is available. -/
theorem tcc_comp_eq_zero_of_cochainDiff (T : TopCat) (β : Cochain ℤ (TopCat.toSSet.obj T) 0)
    (hβ : cochainDiff ℤ (TopCat.toSSet.obj T) β = 0) :
    β.comp ((singularChains ℤ T).d 1 0).hom = 0 := hβ

/-- Two points which are not joined by a path lie in different path components. -/
theorem tcc_pi0_mk_symm_ne_of_not_joined {Z : TopCat} {a b : Z} (h : ¬ Joined a b) :
    SSet.π₀.mk ((TopCat.toSSetObj₀Equiv (X := Z)).symm a) ≠
      SSet.π₀.mk ((TopCat.toSSetObj₀Equiv (X := Z)).symm b) := by
  intro hh
  have h2 : ZerothHomotopy.mk a = ZerothHomotopy.mk b := by
    have hcongr := congrArg (TopCat.zerothHomotopyEquiv (X := Z)).symm hh
    rwa [TopCat.zerothHomotopyEquiv_symm_mk, TopCat.zerothHomotopyEquiv_symm_mk,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hcongr
  exact h (Quotient.exact h2)

/-- The "difference of the evaluations at the two components" functional on `H⁰(Z; ℤ)`. -/
def tccCokerPhi (Z : TopCat)
    (sA sB : (TopCat.toSSet.obj Z).obj (Opposite.op (SimplexCategory.mk 0))) :
    singularCohomology ℤ 0 Z →ₗ[ℤ] ℤ :=
  h0Ev (TopCat.toSSet.obj Z) sA - h0Ev (TopCat.toSSet.obj Z) sB

/-- A cocycle of `Z` which is constant on the two components is the pullback along `f` of a
multiple of the augmentation of `Y`. -/
theorem tcc_exists_preimage_of_constant (Y Z : TopCat) [PathConnectedSpace Y] (f : Z ⟶ Y)
    (sA : (TopCat.toSSet.obj Z).obj (Opposite.op (SimplexCategory.mk 0)))
    (α : Cochain ℤ (TopCat.toSSet.obj Z) 0) (hα : cochainDiff ℤ (TopCat.toSSet.obj Z) α = 0)
    (hconst : ∀ σ : (TopCat.toSSet.obj Z).obj (Opposite.op (SimplexCategory.mk 0)),
      α (h0Gen (TopCat.toSSet.obj Z) σ) = α (h0Gen (TopCat.toSSet.obj Z) sA)) :
    ∃ y : singularCohomology ℤ 0 Y,
      (singularCohomologyMap ℤ Z Y f 0).hom y
        = cohomologyClassOf ℤ (TopCat.toSSet.obj Z) α hα := by
  classical
  let γ : Cochain ℤ (TopCat.toSSet.obj Y) 0 :=
    (α (h0Gen (TopCat.toSSet.obj Z) sA)) • unitCochain ℤ (TopCat.toSSet.obj Y)
  have hγ : cochainDiff ℤ (TopCat.toSSet.obj Y) γ = 0 := by
    have hlin : cochainDiff ℤ (TopCat.toSSet.obj Y) γ
        = (α (h0Gen (TopCat.toSSet.obj Z) sA)) •
            cochainDiff ℤ (TopCat.toSSet.obj Y) (unitCochain ℤ (TopCat.toSSet.obj Y)) := by
      rw [show γ = (α (h0Gen (TopCat.toSSet.obj Z) sA)) •
          unitCochain ℤ (TopCat.toSSet.obj Y) from rfl,
        ← cochainDiffLM_apply ℤ (TopCat.toSSet.obj Y) 0
          ((α (h0Gen (TopCat.toSSet.obj Z) sA)) •
            unitCochain ℤ (TopCat.toSSet.obj Y)),
        map_smul, cochainDiffLM_apply]
    rw [hlin, cochainDiff_unitCochain, smul_zero]
  refine ⟨cohomologyClassOf ℤ (TopCat.toSSet.obj Y) γ hγ, ?_⟩
  have hpbα : ((SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℤ ℤ)).f 0).hom.dualMap γ
      = α := by
    apply genEval_ext
    intro σ
    rw [genEval_dualMap ℤ (TopCat.toSSet.map f) γ σ]
    show genEval ℤ (TopCat.toSSet.obj Y) γ
        ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk 0)) σ)
      = genEval ℤ (TopCat.toSSet.obj Z) α σ
    rw [show genEval ℤ (TopCat.toSSet.obj Y) γ
          ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk 0)) σ)
        = γ (h0Gen (TopCat.toSSet.obj Y)
            ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk 0)) σ)) from rfl,
      show genEval ℤ (TopCat.toSSet.obj Z) α σ = α (h0Gen (TopCat.toSSet.obj Z) σ) from rfl]
    rw [show γ (h0Gen (TopCat.toSSet.obj Y)
          ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk 0)) σ))
        = (α (h0Gen (TopCat.toSSet.obj Z) sA)) •
            (unitCochain ℤ (TopCat.toSSet.obj Y))
              (h0Gen (TopCat.toSSet.obj Y)
                ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk 0)) σ)) from rfl,
      smul_eq_mul,
      show (unitCochain ℤ (TopCat.toSSet.obj Y))
          (h0Gen (TopCat.toSSet.obj Y)
            ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk 0)) σ)) = 1 from
        genEval_unitCochain ℤ (TopCat.toSSet.obj Y) _, mul_one]
    exact (hconst σ).symm
  rw [show (singularCohomologyMap ℤ Z Y f 0).hom
      (cohomologyClassOf ℤ (TopCat.toSSet.obj Y) γ hγ)
      = cohomologyClassOf ℤ (TopCat.toSSet.obj Z)
          (((SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℤ ℤ)).f 0).hom.dualMap γ)
          (cochainDiff_dualMap_chainComplexMap ℤ (TopCat.toSSet.map f) γ hγ) from
      singularCohomologyMap_classOf ℤ f γ hγ]
  exact cohomologyClassOf_congr ℤ (TopCat.toSSet.obj Z) hpbα _ hα

theorem twoComponentCokernel (Y Z : TopCat) [PathConnectedSpace Y] (f : Z ⟶ Y)
    (hZ : ∃ a b : Z, (∀ z : Z, Joined z a ∨ Joined z b) ∧ ¬ Joined a b) :
    Nonempty (CategoryTheory.Limits.cokernel
      (Work.Cohomology.singularCohomologyMap ℤ Z Y f 0) ≅ ModuleCat.of ℤ ℤ) := by
  classical
  obtain ⟨a, b, hcover, hnab⟩ := hZ
  let sA : (TopCat.toSSet.obj Z).obj (Opposite.op (SimplexCategory.mk 0)) :=
    (TopCat.toSSetObj₀Equiv (X := Z)).symm a
  let sB : (TopCat.toSSet.obj Z).obj (Opposite.op (SimplexCategory.mk 0)) :=
    (TopCat.toSSetObj₀Equiv (X := Z)).symm b
  have hneq : SSet.π₀.mk sA ≠ SSet.π₀.mk sB := tcc_pi0_mk_symm_ne_of_not_joined hnab
  -- **Step 1.** `Φ` is surjective.
  have hone : tccCokerPhi Z sA sB (cohomologyClassOf ℤ (TopCat.toSSet.obj Z)
      (pi0Proj Z (SSet.π₀.mk sA)) (pi0Proj_cocycle Z (SSet.π₀.mk sA))) = 1 := by
    rw [show tccCokerPhi Z sA sB (cohomologyClassOf ℤ (TopCat.toSSet.obj Z)
          (pi0Proj Z (SSet.π₀.mk sA)) (pi0Proj_cocycle Z (SSet.π₀.mk sA)))
        = h0Ev (TopCat.toSSet.obj Z) sA (cohomologyClassOf ℤ (TopCat.toSSet.obj Z)
            (pi0Proj Z (SSet.π₀.mk sA)) (pi0Proj_cocycle Z (SSet.π₀.mk sA)))
          - h0Ev (TopCat.toSSet.obj Z) sB (cohomologyClassOf ℤ (TopCat.toSSet.obj Z)
            (pi0Proj Z (SSet.π₀.mk sA)) (pi0Proj_cocycle Z (SSet.π₀.mk sA))) from rfl,
      h0Ev_classOf (TopCat.toSSet.obj Z) sA (pi0Proj Z (SSet.π₀.mk sA))
        (pi0Proj_cocycle Z (SSet.π₀.mk sA)),
      h0Ev_classOf (TopCat.toSSet.obj Z) sB (pi0Proj Z (SSet.π₀.mk sA))
        (pi0Proj_cocycle Z (SSet.π₀.mk sA)),
      show h0Gen (TopCat.toSSet.obj Z) sA = sgen ℤ Z sA from rfl,
      pi0Proj_sgen_of_mem Z (SSet.π₀.mk sA) sA rfl,
      show h0Gen (TopCat.toSSet.obj Z) sB = sgen ℤ Z sB from rfl,
      pi0Proj_sgen_of_not_mem Z (SSet.π₀.mk sA) sB hneq.symm, sub_zero]
  have hsurj : Function.Surjective (tccCokerPhi Z sA sB) := by
    intro n
    have hmem : n ∈ LinearMap.range (tccCokerPhi Z sA sB) := by
      have h1 : (1 : ℤ) ∈ LinearMap.range (tccCokerPhi Z sA sB) :=
        ⟨_, hone⟩
      have h2 := Submodule.smul_mem (LinearMap.range (tccCokerPhi Z sA sB)) n h1
      simpa using h2
    exact hmem
  -- **Step 2.** `range f* ⊆ ker Φ`: the pullback of a class of `Y` is a constant cocycle.
  have hrange_le : LinearMap.range (singularCohomologyMap ℤ Z Y f 0).hom ≤
      LinearMap.ker (tccCokerPhi Z sA sB) := by
    rintro x ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    obtain ⟨β, hβ, hy⟩ := exists_cohomologyClassOf ℤ (TopCat.toSSet.obj Y) 0 y
    rw [← hy]
    let pb : Cochain ℤ (TopCat.toSSet.obj Z) 0 :=
      ((SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℤ ℤ)).f 0).hom.dualMap β
    have hpb : cochainDiff ℤ (TopCat.toSSet.obj Z) pb = 0 :=
      cochainDiff_dualMap_chainComplexMap ℤ (TopCat.toSSet.map f) β hβ
    rw [show (singularCohomologyMap ℤ Z Y f 0).hom
        (cohomologyClassOf ℤ (TopCat.toSSet.obj Y) β hβ)
        = cohomologyClassOf ℤ (TopCat.toSSet.obj Z) pb hpb from
        singularCohomologyMap_classOf ℤ f β hβ]
    have hvalA : pb (h0Gen (TopCat.toSSet.obj Z) sA)
        = β (h0Gen (TopCat.toSSet.obj Y)
            ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk 0)) sA)) := by
      simpa only [pb, h0Gen, genEval] using genEval_dualMap ℤ (TopCat.toSSet.map f) β sA
    have hvalB : pb (h0Gen (TopCat.toSSet.obj Z) sB)
        = β (h0Gen (TopCat.toSSet.obj Y)
            ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk 0)) sB)) := by
      simpa only [pb, h0Gen, genEval] using genEval_dualMap ℤ (TopCat.toSSet.map f) β sB
    have hconst : ∀ σ : (TopCat.toSSet.obj Y).obj (Opposite.op (SimplexCategory.mk 0)),
        β (h0Gen (TopCat.toSSet.obj Y) σ)
          = β (h0Gen (TopCat.toSSet.obj Y) (baseSimplex Y)) := by
      intro σ
      exact eval_constancy ℤ Y β (tcc_comp_eq_zero_of_cochainDiff Y β hβ) σ
    rw [show tccCokerPhi Z sA sB (cohomologyClassOf ℤ (TopCat.toSSet.obj Z) pb hpb)
        = h0Ev (TopCat.toSSet.obj Z) sA (cohomologyClassOf ℤ (TopCat.toSSet.obj Z) pb hpb)
          - h0Ev (TopCat.toSSet.obj Z) sB (cohomologyClassOf ℤ (TopCat.toSSet.obj Z) pb hpb)
        from rfl,
      h0Ev_classOf (TopCat.toSSet.obj Z) sA pb hpb,
      h0Ev_classOf (TopCat.toSSet.obj Z) sB pb hpb, hvalA, hvalB,
      hconst ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk 0)) sA),
      hconst ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk 0)) sB), sub_self]
  -- **Step 3.** `ker Φ ⊆ range f*`.
  have hker_le : LinearMap.ker (tccCokerPhi Z sA sB) ≤
      LinearMap.range (singularCohomologyMap ℤ Z Y f 0).hom := by
    intro x hx
    rw [LinearMap.mem_ker] at hx
    let α : Cochain ℤ (TopCat.toSSet.obj Z) 0 :=
      ModuleCat.Hom.hom ((SSetCochainComplex ℤ (TopCat.toSSet.obj Z)).iCycles 0)
        ((h0CycIso (TopCat.toSSet.obj Z)).hom x)
    have hα : cochainDiff ℤ (TopCat.toSSet.obj Z) α = 0 :=
      cochainDiff_iCycles ℤ (TopCat.toSSet.obj Z) 0 _
    have hxclass : x = cohomologyClassOf ℤ (TopCat.toSSet.obj Z) α hα :=
      (h0ClassOf_iCycles (TopCat.toSSet.obj Z) x).symm
    -- the two components carry the same value, because `Φ x = 0`
    have heq : α (h0Gen (TopCat.toSSet.obj Z) sA) = α (h0Gen (TopCat.toSSet.obj Z) sB) := by
      have h := hx
      rw [hxclass] at h
      rw [show tccCokerPhi Z sA sB (cohomologyClassOf ℤ (TopCat.toSSet.obj Z) α hα)
          = h0Ev (TopCat.toSSet.obj Z) sA (cohomologyClassOf ℤ (TopCat.toSSet.obj Z) α hα)
            - h0Ev (TopCat.toSSet.obj Z) sB (cohomologyClassOf ℤ (TopCat.toSSet.obj Z) α hα)
          from rfl,
        h0Ev_classOf (TopCat.toSSet.obj Z) sA α hα,
        h0Ev_classOf (TopCat.toSSet.obj Z) sB α hα] at h
      exact sub_eq_zero.mp h
    -- hence `α` is constant on all generators
    have hconstα : ∀ σ : (TopCat.toSSet.obj Z).obj (Opposite.op (SimplexCategory.mk 0)),
        α (h0Gen (TopCat.toSSet.obj Z) σ) = α (h0Gen (TopCat.toSSet.obj Z) sA) := by
      intro σ
      rcases hcover (TopCat.toSSetObj₀Equiv (X := Z) σ) with hj | hj
      · have h1 := tcc_sgen_congr_of_joined α (tcc_comp_eq_zero_of_cochainDiff Z α hα) hj
        rw [Equiv.symm_apply_apply] at h1
        rw [← tcc_sgen_eq_gen Z σ, ← tcc_sgen_eq_gen Z sA]
        exact h1
      · have h1 := tcc_sgen_congr_of_joined α (tcc_comp_eq_zero_of_cochainDiff Z α hα) hj
        rw [Equiv.symm_apply_apply] at h1
        have h2 : α (h0Gen (TopCat.toSSet.obj Z) σ) = α (h0Gen (TopCat.toSSet.obj Z) sB) := by
          rw [← tcc_sgen_eq_gen Z σ, ← tcc_sgen_eq_gen Z sB]
          exact h1
        rw [h2, heq]
    obtain ⟨y, hy⟩ := tcc_exists_preimage_of_constant Y Z f sA α hα hconstα
    exact ⟨y, by rw [hxclass]; exact hy⟩
  exact cokernelIsoInt (singularCohomologyMap ℤ Z Y f 0) (ModuleCat.ofHom (tccCokerPhi Z sA sB))
    hsurj (le_antisymm hrange_le hker_le)

end

end Work.Cohomology
