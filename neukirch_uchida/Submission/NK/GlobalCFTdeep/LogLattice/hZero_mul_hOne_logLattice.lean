import Mathlib
import Submission.NK.GlobalCFTdeep.LogLattice.LogLatticeMain
import Submission.NK.GlobalCFTdeep.Herbrand.Mul
import Submission.NK.GlobalCFTdeep.Herbrand.FiniteIndex
import Submission.NK.GlobalCFTdeep.LogLattice.finite_ker_logVecLin
import Submission.NK.GlobalCFTdeep.Herbrand.finite_tateCohomology_of_moduleFinite
import Submission.NK.GlobalCFTdeep.Herbrand.FiberUnitsLocal

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct IsMulCommutative
open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep.LogLattice

open NK.GlobalCFT NK.GlobalCFTdeep

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **Pointwise `Gal(L/K)`-equivariance of the log map** on the `T`-units: the log vector of
`σ • a` is the permuted log vector of `a`. -/
private lemma logVecLin_tUnitsRep_ρ_apply (T : Set (Place L)) [Fintype ↥T]
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (σ : L ≃ₐ[K] L) (a : Additive (TUnits T)) (w : ↥T) :
    logVecLin T ((tUnitsRep (L := L) T hT).ρ σ a) w =
      logVecLin T a ⟨σ⁻¹ • (w : Place L), hT σ⁻¹ w.2⟩ := by
  letI : MulDistribMulAction (L ≃ₐ[K] L) (TUnits T) :=
    stableMulDistribMulAction (L ≃ₐ[K] L) (TUnits T) (fun σ x hx => smul_mem_TUnits hT hx)
  have hρ : (tUnitsRep (L := L) T hT).ρ σ a = Additive.ofMul (σ • Additive.toMul a) := rfl
  rw [hρ]
  show logVec T (((σ • Additive.toMul a : TUnits T)) : Lˣ) w =
    logVec T (((Additive.toMul a : TUnits T)) : Lˣ) ⟨σ⁻¹ • (w : Place L), hT σ⁻¹ w.2⟩
  rw [show (((σ • Additive.toMul a : TUnits T)) : Lˣ) =
    σ • (((Additive.toMul a : TUnits T)) : Lˣ) from rfl]
  exact logVec_smul_apply T hT σ (((Additive.toMul a : TUnits T)) : Lˣ) w

/-- **The relation `h(U(T)) = h(M')` for the log map.**  The log map
`logVecLin T : Additive (TUnits T) →ₗ[ℤ] ↥T → ℝ` has image `M' = logLattice T` and finite kernel
`μ(L) = ker (logVecLin T)` (`NK.GlobalCFTdeep.LogLattice.finite_ker_logVecLin`, which needs
`hTinf`: every infinite place lies in `T`).  Hence the exact sequence of `ℤ[Gal(L/K)]`-modules

  `0 → μ(L) → U(T) → M' → 0`

gives, since the Herbrand quotient of the finite module `μ(L)` is `1`,

  `hZero U(T) · hOne M' = hZero M' · hOne U(T)`.

## Proof sketch

Build the short complex of `Rep ℤ G`-modules with `X₁ := repOfStableAddSubgroup μ hμ` (the kernel,
made `G`-stable using the equivariance `NK.GlobalCFTdeep.LogLattice.logVec_smul_apply`),
`X₂ := tUnitsRep T hT`, `X₃ := logLatticeRep T hT`, the inclusion and the log map (both
`Rep.ofHom`-morphisms); its short-exactness follows from
`Commons.RepresentationTheory.GroupCohomology.shortExact_of_mono_epi_elementwise` together with
`Rep.mono_iff_injective`/`Rep.epi_iff_surjective` and the definition of `logLattice` as the range of
the log map.  Then the raw long-exact-sequence identity `hZero_mul_hOne_of_shortExact` (see
`Herbrand/Mul.lean`), together with `hZero_eq_hOne_of_finite` for the finite module `μ` and the
positivity of `hOne μ` (a finite nonempty group's cohomology has positive cardinality), cancels the
`μ`-terms and gives the displayed identity.

Note that the *finite* module here is `X₁`, so neither `herbrandEq_iff_of_finite_quotient` nor
`herbrandEq_iff_of_shortExact_finite` (which require `X₃` finite) applies directly: use
`hZero_mul_hOne_of_shortExact` and cancel. -/
theorem hZero_mul_hOne_logLattice {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (T : Set (NK.GlobalCFT.Place L)) [Fintype ↥T]
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : NK.GlobalCFT.Place L⦄, w ∈ T → σ • w ∈ T)
    (hTinf : ∀ w : NK.GlobalCFT.Place L, w.IsInfinite → w ∈ T)
    [IsCyclic (L ≃ₐ[K] L)] :
    NK.GlobalCFTdeep.hZero (NK.GlobalCFTdeep.tUnitsRep (L := L) T hT) *
        NK.GlobalCFTdeep.hOne (NK.GlobalCFTdeep.logLatticeRep (L := L) T hT) =
      NK.GlobalCFTdeep.hZero (NK.GlobalCFTdeep.logLatticeRep (L := L) T hT) *
        NK.GlobalCFTdeep.hOne (NK.GlobalCFTdeep.tUnitsRep (L := L) T hT) := by
  classical
  letI : CommGroup (L ≃ₐ[K] L) := IsCyclic.commGroup
  letI : MulDistribMulAction (L ≃ₐ[K] L) (TUnits T) :=
    stableMulDistribMulAction (L ≃ₐ[K] L) (TUnits T) (fun σ x hx => smul_mem_TUnits hT hx)
  -- The kernel `μ = ker (logVecLin T)`, as a `Gal(L/K)`-stable additive subgroup of `U(T)`.
  let μa : AddSubgroup (Additive (TUnits T)) := (LinearMap.ker (logVecLin T)).toAddSubgroup
  have hμ : ∀ (g : L ≃ₐ[K] L) {x : Additive (TUnits T)}, x ∈ μa → g • x ∈ μa := by
    intro g x hx
    have hx' : logVecLin T x = 0 := hx
    have h1 : logVecLin T ((tUnitsRep (L := L) T hT).ρ g x) = 0 := by
      funext w
      rw [logVecLin_tUnitsRep_ρ_apply T hT g x w, hx']
      rfl
    show logVecLin T (g • x) = 0
    rw [show g • x = (tUnitsRep (L := L) T hT).ρ g x from rfl]
    exact h1
  let X₁ : Rep ℤ (L ≃ₐ[K] L) := repOfStableAddSubgroup μa hμ
  -- The inclusion `μ ↪ U(T)`.
  let f : X₁ ⟶ tUnitsRep (L := L) T hT :=
    Rep.ofHom
      { toFun := fun x => (x : Additive (TUnits T))
        map_add' := fun a b => rfl
        map_smul' := fun n a => rfl
        isIntertwining' := fun σ => by
          apply LinearMap.ext
          intro x
          rfl }
  -- The log map `U(T) ↠ M'`.
  let φ : Additive (TUnits T) →ₗ[ℤ] ↥(logLattice T) :=
    { toFun := fun a => ⟨logVecLin T a, mem_logLattice.mpr ⟨a, rfl⟩⟩
      map_add' := fun a b => by ext w; simp
      map_smul' := fun n a => by ext w; simp }
  have hφint : ∀ (σ : L ≃ₐ[K] L),
      φ ∘ₗ (tUnitsRep (L := L) T hT).ρ σ = (logLatticeRep (L := L) T hT).ρ σ ∘ₗ φ := by
    intro σ
    apply LinearMap.ext
    intro a
    letI : DistribMulAction (L ≃ₐ[K] L) (↥T → ℝ) := permAction T hT ℝ
    apply Subtype.ext
    change logVecLin T ((tUnitsRep (L := L) T hT).ρ σ a) = _
    funext w
    change logVecLin T ((tUnitsRep (L := L) T hT).ρ σ a) w =
      logVecLin T a ⟨σ⁻¹ • (w : Place L), hT σ⁻¹ w.2⟩
    exact logVecLin_tUnitsRep_ρ_apply T hT σ a w
  let g : tUnitsRep (L := L) T hT ⟶ logLatticeRep (L := L) T hT :=
    Rep.ofHom { φ with isIntertwining' := hφint }
  -- The short complex `0 → μ → U(T) → M' → 0`.
  let S : ShortComplex (Rep ℤ (L ≃ₐ[K] L)) :=
    ShortComplex.mk f g (by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      change logVecLin T ((x : ↥μa).1) = 0
      exact (x : ↥μa).2)
  have hS : S.ShortExact := by
    refine Commons.RepresentationTheory.GroupCohomology.shortExact_of_mono_epi_elementwise S
      ((Rep.mono_iff_injective S.f).2 ?_) ((Rep.epi_iff_surjective S.g).2 ?_) ?_
    · intro a b hab
      exact Subtype.ext hab
    · intro y
      obtain ⟨a, ha⟩ := mem_logLattice.mp y.2
      exact ⟨a, Subtype.ext ha⟩
    · intro x hx
      have hx' : logVecLin T x = 0 := by
        have hxφ : φ x = 0 := hx
        have h2 := congrArg (fun y : ↥(logLattice T) => (y : ↥T → ℝ)) hxφ
        simpa [φ] using h2
      exact ⟨⟨x, hx'⟩, rfl⟩
  -- Finiteness of the three modules
  haveI hX₁fin : Finite X₁.V := by
    show Finite ↥(LinearMap.ker (logVecLin T))
    exact finite_ker_logVecLin (K := K) T hTinf
  haveI hX₂fin : Module.Finite ℤ (tUnitsRep (L := L) T hT).V :=
    (Herbrand.finrank_tUnits (L := L) T hTinf).1
  haveI hX₃fin : Module.Finite ℤ (logLatticeRep (L := L) T hT).V :=
    finite_logLattice T hTinf
  haveI hX₁modfin : Module.Finite ℤ X₁.V := by
    have := hX₁fin
    exact Module.Finite.of_finite
  haveI hμ0 : Finite ↥(tateCohomology S.X₁ 0) :=
    (Herbrand.finite_tateCohomology_of_moduleFinite S.X₁).1
  haveI hμ1 : Finite ↥(tateCohomology S.X₁ 1) :=
    (Herbrand.finite_tateCohomology_of_moduleFinite S.X₁).2
  haveI hU0 : Finite ↥(tateCohomology S.X₂ 0) :=
    (Herbrand.finite_tateCohomology_of_moduleFinite S.X₂).1
  haveI hU1 : Finite ↥(tateCohomology S.X₂ 1) :=
    (Herbrand.finite_tateCohomology_of_moduleFinite S.X₂).2
  haveI hM0 : Finite ↥(tateCohomology S.X₃ 0) :=
    (Herbrand.finite_tateCohomology_of_moduleFinite S.X₃).1
  haveI hM1 : Finite ↥(tateCohomology S.X₃ 1) :=
    (Herbrand.finite_tateCohomology_of_moduleFinite S.X₃).2
  -- Herbrand's lemma for the finite kernel, and positivity of `hOne`
  have hfinμ : hZero S.X₁ = hOne S.X₁ := Herbrand.hZero_eq_hOne_of_finite S.X₁
  have hposμ : 0 < hOne S.X₁ := Nat.card_pos
  have hMult := hZero_mul_hOne_of_shortExact S hS
  rw [hfinμ] at hMult
  have key : hZero S.X₂ * hOne S.X₃ = hZero S.X₃ * hOne S.X₂ := by
    apply Nat.mul_left_cancel hposμ
    calc hOne S.X₁ * (hZero S.X₂ * hOne S.X₃)
        = hZero S.X₂ * hOne S.X₁ * hOne S.X₃ := by ring
      _ = hOne S.X₁ * hZero S.X₃ * hOne S.X₂ := hMult
      _ = hOne S.X₁ * (hZero S.X₃ * hOne S.X₂) := by ring
  exact key

end NK.GlobalCFTdeep.LogLattice
