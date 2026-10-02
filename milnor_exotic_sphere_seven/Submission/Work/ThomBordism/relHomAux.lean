import Mathlib
import Submission.Work.Cohomology.uctDual
import Submission.Work.Cohomology.uctDual_evaluation
import Submission.Work.Cohomology.free_submodule_of_free_int
import Submission.Work.Cohomology.RatModZ
import Submission.Work.ThomBordism.kerRangeDual

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary material for the integral homology/cohomology comparison

This file collects the definitions and elementary lemmas used in
`Submission/Work/ThomBordism/relHomologyIntOfCoh.lean`, the proof that a finitely generated
relative homology group `Hₙ(X,A)` is `ℤ` as soon as `Hⁿ(X,A;ℤ) ≅ ℤ` and `Hⁿ⁺¹(X,A;ℤ) = 0`.

Everything is stated for an abstract chain complex `E` of `ℤ`-modules with free components; the
application to `E = relChains X A` happens in the target file.

## Main definitions

* `eMap`, `eCoh` — the evaluation map `Hⁿ(dualComplex ℤ E) ⟶ Hom(Zₙ ⧸ Bₙ, ℤ)`, in the shape
  `Hⁿ ⟶ Hom(Zₙ ⧸ Bₙ, ℤ)` of the concrete cycles and boundaries.

## Main results

* `free_uctZ`, `free_uctB`, `free_uctH`, `projective_uctR` — freeness/projectivity of the
  cycles, boundaries and the modules they generate, for a complex with free components;
* `exists_retract_cycles'` — `Eₙ` retracts onto its cycles;
* `eCoh_surjective` — the evaluation map is surjective;
* `forall_extends_of_isZero_dual` — vanishing of `Hⁿ⁺¹` of the dual complex implies that every
  functional on the boundaries `Bₙ` extends to `Eₙ`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

attribute [local instance 5000] Submodule.module
attribute [local instance 5000] Submodule.Quotient.module
attribute [local instance 100] ZSMul.toSMul

open CategoryTheory CategoryTheory.Limits

namespace Work.ThomBordism

open Work.Cohomology

noncomputable section

/-! ## Freeness and projectivity of cycles and boundaries -/

universe u

/-- A submodule of a free `ℤ`-module is free. -/
theorem free_submodule_int {M : Type u} [AddCommGroup M] [Module ℤ M] [Module.Free ℤ M]
    (N : Submodule ℤ M) : Module.Free ℤ ↥N := by
  rw [show Submodule.module N = AddCommGroup.toIntModule ↥N from Subsingleton.elim _ _]
  exact free_submodule_of_free_int N

/-- The cycles of a chain complex with free components are free. -/
theorem free_uctZ (E : ChainComplex (ModuleCat ℤ) ℕ)
    (hfree : ∀ k, Module.Free ℤ ↥(E.X k)) (n : ℕ) : Module.Free ℤ ↥(uctZ E n) := by
  haveI : Module.Free ℤ ↥(E.X n) := hfree n
  exact free_submodule_int (uctZ E n)

/-- The boundaries of a chain complex with free components are free. -/
theorem free_uctB (E : ChainComplex (ModuleCat ℤ) ℕ)
    (hfree : ∀ k, Module.Free ℤ ↥(E.X k)) (n : ℕ) : Module.Free ℤ ↥(uctB E n) := by
  haveI : Module.Free ℤ ↥(E.X n) := hfree n
  exact free_submodule_int (uctB E n)

/-- The boundaries, viewed inside the cycles, form a free module. -/
theorem free_uctH (E : ChainComplex (ModuleCat ℤ) ℕ)
    (hfree : ∀ k, Module.Free ℤ ↥(E.X k)) (n : ℕ) : Module.Free ℤ ↥(uctH E n) := by
  haveI : Module.Free ℤ ↥(uctZ E n) := free_uctZ E hfree n
  exact free_submodule_int (uctH E n)

/-- The image of the differential is projective. -/
theorem projective_uctR (E : ChainComplex (ModuleCat ℤ) ℕ)
    (hfree : ∀ k, Module.Free ℤ ↥(E.X k)) (m : ℕ) : Module.Projective ℤ ↥(uctR E m) := by
  haveI : Module.Free ℤ ↥(uctR E m) := by
    rcases m with _ | k
    · rw [uctR_zero]
      exact free_submodule_int (⊥ : Submodule ℤ ↥(E.X (0 - 1)))
    · rw [uctR_apply]
      exact free_uctB E hfree k
  exact inferInstance

/-- `Eₙ` retracts onto its cycles when the components of `E` are free. -/
theorem exists_retract_cycles (E : ChainComplex (ModuleCat ℤ) ℕ)
    (hfree : ∀ k, Module.Free ℤ ↥(E.X k)) (n : ℕ) :
    ∃ ρ : ↥(E.X n) →ₗ[ℤ] ↥(uctZ E n), ρ ∘ₗ (uctZ E n).subtype = LinearMap.id :=
  exists_retraction_cycles E n (projective_uctR E hfree n)

/-! ## The evaluation map `Hⁿ ⟶ Hom(Zₙ ⧸ Bₙ, ℤ)` -/

/-- The comparison map `uctPsi` kills the image of the previous differential. -/
theorem uctPre_le_ker_uctPsi (E : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    uctPre E n ≤ LinearMap.ker (uctPsi E n) := by
  intro y hy
  rw [LinearMap.mem_ker]
  obtain ⟨g, hg⟩ := hy
  have hval : ((dualComplex ℤ E).d (n - 1) n).hom g = y.1 := by
    have h := congrArg (fun (m : ↥(LinearMap.ker ((dualComplex ℤ E).d n (n + 1)).hom)) =>
      (m : ↥((dualComplex ℤ E).X n))) hg
    rwa [LinearMap.codRestrict_apply] at h
  apply LinearMap.ext
  intro w
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (uctH E n) w
  rw [uctPsi_apply]
  show (dval E n (y : ↥((dualComplex ℤ E).X n))) (x : ↥(E.X n)) = 0
  rw [← hval, uct_d_pred_apply]
  rw [show dval E n (dval E (n - 1) g ∘ₗ (E.d n (n - 1)).hom)
      = (dval E (n - 1) g) ∘ₗ (E.d n (n - 1)).hom from rfl]
  rw [LinearMap.comp_apply]
  rw [show ((E.d n (n - 1)).hom) (x : ↥(E.X n)) = 0 from LinearMap.mem_ker.mp x.2]
  rw [map_zero]

/-- The evaluation map on the quotient `ker dⁿ ⧸ im dⁿ⁻¹`. -/
def eMap (E : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    (↥(LinearMap.ker ((dualComplex ℤ E).d n (n + 1)).hom) ⧸ uctPre E n) →ₗ[ℤ]
      (Module.Dual ℤ (↥(uctZ E n) ⧸ uctH E n)) :=
  (uctPre E n).liftQ (uctPsi E n) (uctPre_le_ker_uctPsi E n)

/-- **The evaluation map** `Hⁿ(dualComplex ℤ E) ⟶ Hom(Zₙ ⧸ Bₙ, ℤ)`. -/
def eCoh (E : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    ↥((dualComplex ℤ E).homology n) →ₗ[ℤ]
      (Module.Dual ℤ (↥(uctZ E n) ⧸ uctH E n)) :=
  (eMap E n).comp (uctIsoToLinearEquiv (homologyDualIso E n)).toLinearMap

/-- The computation rule for the evaluation map on representatives. -/
theorem eCoh_mkQ (E : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ)
    (f : ↥(LinearMap.ker ((dualComplex ℤ E).d n (n + 1)).hom)) :
    eCoh E n ((uctIsoToLinearEquiv (homologyDualIso E n)).symm ((uctPre E n).mkQ f))
      = uctPsi E n f := by
  rw [eCoh, eMap, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]
  exact Submodule.liftQ_apply (uctPre E n) (uctPsi E n) (h := uctPre_le_ker_uctPsi E n) f

/-- **The evaluation map is surjective.** -/
theorem eCoh_surjective (E : ChainComplex (ModuleCat ℤ) ℕ)
    (hfree : ∀ k, Module.Free ℤ ↥(E.X k)) (n : ℕ) : Function.Surjective (eCoh E n) := by
  obtain ⟨ρ, hρ⟩ := exists_retract_cycles E hfree n
  have hsurj := uctPsi_surj E n ⟨ρ, hρ⟩
  intro χ
  obtain ⟨f, hf⟩ := hsurj χ
  exact ⟨(uctIsoToLinearEquiv (homologyDualIso E n)).symm ((uctPre E n).mkQ f),
    by rw [eCoh_mkQ, hf]⟩

/-- The boundaries, viewed inside the cycles, are linearly equivalent to the boundaries viewed
inside the chains. -/
def uctH_uctB_iso (E : ChainComplex (ModuleCat ℤ) ℕ) (m : ℕ) :
    ↥(uctH E m) ≃ₗ[ℤ] ↥(uctB E m) where
  toFun x := ⟨((x.1 : ↥(uctZ E m)) : ↥(E.X m)), (mem_uctH E m x.1).mp x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun y := ⟨⟨(y.1 : ↥(E.X m)), uctB_le_uctZ E m y.2⟩, (mem_uctH E m _).mpr y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! ## Vanishing of `Hⁿ⁺¹` and extension of functionals -/

/-- Exactness of the dual complex at `n + 1`, in the index shape needed below. -/
theorem kerRangeDual_succ (E : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ)
    (h : IsZero ((dualComplex ℤ E).homology (n + 1))) :
    LinearMap.ker ((dualComplex ℤ E).d (n + 1) (n + 2)).hom =
      LinearMap.range ((dualComplex ℤ E).d n (n + 1)).hom := by
  have h0 := kerRangeDual E (n + 1) h
  have h1 : n + 1 - 1 = n := by omega
  have h2 : n + 1 + 1 = n + 2 := by omega
  rw [h1, h2] at h0
  exact h0

/-- **Vanishing of `Hⁿ⁺¹` of the dual complex makes every functional on the boundaries extend.** -/
theorem forall_extends_of_isZero_dual (E : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ)
    (h : IsZero ((dualComplex ℤ E).homology (n + 1))) :
    ∀ φ : ↥(uctB E n) →ₗ[ℤ] ℤ, ∃ ψ : ↥(E.X n) →ₗ[ℤ] ℤ,
      ψ.comp (uctB E n).subtype = φ := by
  intro φ
  have hker := kerRangeDual_succ E n h
  -- the boundary projection `Eₙ₊₁ → Bₙ`
  let dB : ↥(E.X (n + 1)) →ₗ[ℤ] ↥(uctB E n) :=
    { toFun := fun x => ⟨((E.d (n + 1) n).hom) x, ⟨x, rfl⟩⟩
      map_add' := fun a b => Subtype.ext (by simp)
      map_smul' := fun a b => Subtype.ext (by simp) }
  have hdB : ∀ x, (dB x : ↥(E.X n)) = ((E.d (n + 1) n).hom) x := fun x => rfl
  -- the functional `φ ∘ ∂ₙ₊₁` on `Eₙ₊₁`; it is a cocycle
  let f : ↥((dualComplex ℤ E).X (n + 1)) := φ.comp dB
  have hfker : f ∈ LinearMap.ker ((dualComplex ℤ E).d (n + 1) (n + 2)).hom := by
    rw [LinearMap.mem_ker, uct_d_apply]
    apply LinearMap.ext
    intro y
    rw [LinearMap.comp_apply, LinearMap.zero_apply]
    have hcomp : ((E.d (n + 1) n).hom) (((E.d (n + 2) (n + 1)).hom) y) = 0 := by
      have hc := congrArg ModuleCat.Hom.hom (HomologicalComplex.d_comp_d E (n + 2) (n + 1) n)
      rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at hc
      exact LinearMap.congr_fun hc y
    have hzero : dB (((E.d (n + 2) (n + 1)).hom) y) = 0 :=
      Subtype.ext (by rw [hdB]; exact hcomp)
    show φ (dB (((E.d (n + 2) (n + 1)).hom) y)) = 0
    rw [hzero, map_zero]
  rw [hker] at hfker
  obtain ⟨g, hg⟩ := hfker
  refine ⟨dval E n g, ?_⟩
  apply LinearMap.ext
  intro b
  obtain ⟨x, hx⟩ := b.2
  have hb : b = dB x := Subtype.ext (by rw [hdB]; exact hx.symm)
  have h2 : (dval E n g) (((E.d (n + 1) n).hom) x) = φ (dB x) := by
    have h := LinearMap.congr_fun hg x
    rw [uct_d_apply, LinearMap.comp_apply] at h
    exact h
  rw [LinearMap.comp_apply, hb]
  rw [show (uctB E n).subtype (dB x) = ((E.d (n + 1) n).hom) x from hdB x]
  exact h2

end

end Work.ThomBordism
