import Mathlib
import Submission.Work.Cohomology.uctDefs
import Submission.Work.Cohomology.free_submodule_of_free_int
import Submission.Work.ThomBordism.relHomAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Extending a functional on the boundaries to the chains, up to a multiple

Let `C` be a chain complex of `ℤ`-modules with free components and let `ψ : C_{m+1} →ₗ[ℤ] ℤ` be a
functional killing the `(m+1)`-cycles.  Then some positive multiple `N • ψ` is induced by a
functional on `C_m`:

`∃ N > 0, ∃ F : C_m →ₗ[ℤ] ℤ, F ∘ ∂_{m+1} = N • ψ`.

**Proof.** `ψ` kills `ker ∂_{m+1}`, hence factors through the boundaries
`B_m = im ∂_{m+1} ⊆ Z_m ⊆ C_m`, giving `φ : B_m →ₗ[ℤ] ℤ` with `φ ∘ ∂_{m+1} = ψ`.  The hypothesis
`hA` extends `φ`, up to a positive multiple `N`, to a functional `g` on the cycles `Z_m`.  Finally
`Z_m = ker ∂_m` is a *direct summand* of `C_m`: since `im ∂_m ⊆ C_{m-1}` is free (a submodule of a
free `ℤ`-module), it is projective, so `C_m ↠ im ∂_m` splits and `C_m` retracts onto `Z_m`
(`Work.ThomBordism.exists_retract_cycles`).  Composing `g` with that retraction gives the required
`F`.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

attribute [local instance 5000] Submodule.module
attribute [local instance 5000] Submodule.Quotient.module

open CategoryTheory CategoryTheory.Limits

namespace Work.ThomBordism

open Work.Cohomology

noncomputable section

/-- The functional on the range of `f` induced by a functional on the source which kills `ker f`.

Concretely: `ker f` is the kernel of the canonical surjection `M ↠ range f`, so a functional on `M`
vanishing on `ker f` induces a functional on `range f`. -/
noncomputable def rangeLift {R : Type*} [Ring R] {M N N' : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup N'] [Module R M] [Module R N] [Module R N']
    (f : M →ₗ[R] N) (ψ : M →ₗ[R] N') (h : LinearMap.ker f ≤ LinearMap.ker ψ) :
    ↥(LinearMap.range f) →ₗ[R] N' :=
  (Submodule.liftQ (LinearMap.ker f) ψ h).comp (LinearMap.quotKerEquivRange f).symm.toLinearMap

/-- The computation rule for `rangeLift`. -/
theorem rangeLift_apply {R : Type*} [Ring R] {M N N' : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup N'] [Module R M] [Module R N] [Module R N']
    (f : M →ₗ[R] N) (ψ : M →ₗ[R] N') (h : LinearMap.ker f ≤ LinearMap.ker ψ) (x : M) :
    rangeLift f ψ h ⟨f x, ⟨x, rfl⟩⟩ = ψ x := by
  show (Submodule.liftQ (LinearMap.ker f) ψ h)
    ((LinearMap.quotKerEquivRange f).symm ⟨f x, ⟨x, rfl⟩⟩) = ψ x
  rw [LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]

theorem chain_extends_up_to_smul (C : ChainComplex (ModuleCat ℤ) ℕ)
    (hfree : ∀ k, Module.Free ℤ ↥(C.X k)) (m : ℕ)
    (hA : ∀ f : ↥(Work.Cohomology.uctH C m) →ₗ[ℤ] ℤ, ∃ N : ℕ, 0 < N ∧
      ∃ g : ↥(Work.Cohomology.uctZ C m) →ₗ[ℤ] ℤ,
        ∀ b : ↥(Work.Cohomology.uctH C m), g ↑b = (N : ℤ) • f b)
    (ψ : ↥(C.X (m + 1)) →ₗ[ℤ] ℤ)
    (hψ : ∀ z : ↥(C.X (m + 1)), (C.d (m + 1) m).hom z = 0 → ψ z = 0) :
    ∃ N : ℕ, 0 < N ∧ ∃ F : ↥(C.X m) →ₗ[ℤ] ℤ,
      F ∘ₗ (C.d (m + 1) m).hom = (N : ℤ) • ψ := by
  -- the `(m+1)`-boundaries, as elements of the cycles
  have hcyc : ∀ x : ↥(C.X (m + 1)), (C.d (m + 1) m).hom x ∈ uctZ C m := fun x => by
    rw [uctZ, LinearMap.mem_ker]
    have h := congrArg ModuleCat.Hom.hom (HomologicalComplex.d_comp_d C (m + 1) m (m - 1))
    simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
    exact LinearMap.congr_fun h x
  have hmem : ∀ x : ↥(C.X (m + 1)),
      (⟨(C.d (m + 1) m).hom x, hcyc x⟩ : ↥(uctZ C m)) ∈ uctH C m :=
    fun x => (mem_uctH C m ⟨(C.d (m + 1) m).hom x, hcyc x⟩).mpr ⟨x, rfl⟩
  -- `ψ` vanishes on the kernel of the differential, so it factors through the boundaries
  have hker : LinearMap.ker (C.d (m + 1) m).hom ≤ LinearMap.ker ψ := fun z hz =>
    hψ z ((LinearMap.mem_ker).mp hz)
  -- the boundaries inside the cycles, as a map of the cycles
  let eH : ↥(uctH C m) →ₗ[ℤ] ↥(uctB C m) :=
    { toFun := fun b => ⟨(b.1 : ↥(C.X m)), (mem_uctH C m b.1).mp b.2⟩
      map_add' := fun a b => Subtype.ext rfl
      map_smul' := fun c b => Subtype.ext rfl }
  -- the functional on the boundaries induced by `ψ`
  let φ : ↥(uctH C m) →ₗ[ℤ] ℤ :=
    (rangeLift (C.d (m + 1) m).hom ψ hker).comp eH
  have key : ∀ x : ↥(C.X (m + 1)),
      φ ⟨⟨(C.d (m + 1) m).hom x, hcyc x⟩, hmem x⟩ = ψ x := by
    intro x
    have h1 : eH ⟨⟨(C.d (m + 1) m).hom x, hcyc x⟩, hmem x⟩
        = (⟨(C.d (m + 1) m).hom x, ⟨x, rfl⟩⟩ : ↥(LinearMap.range (C.d (m + 1) m).hom)) :=
      Subtype.ext rfl
    show (rangeLift (C.d (m + 1) m).hom ψ hker)
      (eH ⟨⟨(C.d (m + 1) m).hom x, hcyc x⟩, hmem x⟩) = ψ x
    rw [h1]
    exact rangeLift_apply _ _ _ x
  -- extend the functional on the boundaries to the cycles, up to a multiple
  obtain ⟨N, hN, g, hg⟩ := hA φ
  -- the cycles are a direct summand of the chains
  obtain ⟨ρ, hρ⟩ := exists_retract_cycles C hfree m
  refine ⟨N, hN, g.comp ρ, ?_⟩
  apply LinearMap.ext
  intro x
  have hρx : ρ ((C.d (m + 1) m).hom x)
      = (⟨(C.d (m + 1) m).hom x, hcyc x⟩ : ↥(uctZ C m)) := by
    have h := LinearMap.congr_fun hρ (⟨(C.d (m + 1) m).hom x, hcyc x⟩ : ↥(uctZ C m))
    simpa using h
  show g (ρ ((C.d (m + 1) m).hom x)) = (N : ℤ) • ψ x
  rw [hρx]
  have h2 := hg (⟨⟨(C.d (m + 1) m).hom x, hcyc x⟩, hmem x⟩ : ↥(uctH C m))
  rw [h2, key x]

end

end Work.ThomBordism
