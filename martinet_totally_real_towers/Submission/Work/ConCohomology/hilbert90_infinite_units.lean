/-
Copyright: the martinet_totally_real_towers team.

# Hilbert 90 for the units of an infinite Galois extension

This module proves Noether's generalization of Hilbert's Theorem 90 for an arbitrary (possibly
infinite) Galois extension `L/K`, in the shape needed by this chapter: every *locally constant*
`1`-cocycle `a : Gal(L/K) → Additive Lˣ` (with the inhomogeneous cocycle condition
`a (σ * τ) = a σ + σ • a τ` of `Defs`) is a coboundary `a = d⁰ β`.

## The argument

Local constancy of `a` at the identity produces, via
`InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois`, a finite Galois intermediate field
`M` with `K ⊆ M ⊆ L` whose fixing subgroup is killed by `a`
(`σ ∈ Gal(L/M) ⟹ a σ = 0`).  Because `M/K` is Galois the fixing subgroup is the kernel of the
restriction map `φ : Gal(L/K) →* Gal(M/K)` (`FiniteGaloisIntermediateField.mem_fixingSubgroup_iff`),
and the cocycle identity then shows

* `a` is constant on the fibres of `φ` (`hdescent`),
* every value `a σ` is fixed by `Gal(L/M)` (`hsmul_fix`), hence lies in `M` (`hmem`) by the
  infinite Galois correspondence (`InfiniteGalois.fixedField_fixingSubgroup`).

Choosing once and for all lifts `χ.liftNormal L` of `χ : Gal(M/K)` we may therefore descend `a` to
a cocycle `b` on the finite group `Gal(M/K)` with coefficients in `Mˣ`; that `b` is a cocycle is
the content of `hb`, and it is proved by pushing the identity back along the inclusion
`ι : Mˣ → Lˣ` (`hι_inj`), which is Galois-equivariant (`hι_smul`).  Hilbert 90 for the finite
extension `M/K` (`Work.ConCohomology.hilbert90_finite_units`) exhibits `β : Mˣ` with
`b χ = χ • β - β`, and since `σ` and `(φ σ).liftNormal L` act the same way on `Mˣ` one gets
`a σ = σ • β - β` in `Lˣ`, i.e. `a = d⁰ β`.

The whole chapter is written with `Additive Lˣ` coefficients; the proof above computes with the
multiplicative notation (`.toMul`) to avoid the `Additive`/multiplicative coercions.
-/

import Mathlib
import Submission.Work.ConCohomology.GaloisUnits
import Submission.Work.ConCohomology.hilbert90_finite_units

namespace Work.ConCohomology

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
-- The instance search for the action of `Gal(↥M/K)` on the units of the intermediate field `↥M`
-- (a `MulDistribMulAction` coming from `AlgEquiv.applyMulSemiringAction`) does terminate but needs
-- more than the default budget, because `↥M` is an `IntermediateField`.
set_option synthInstance.maxHeartbeats 400000

/-- **Noether's generalization of Hilbert's Theorem 90 for an infinite Galois extension.**
Every locally constant `1`-cocycle `Gal(L/K) → Lˣ` (written additively) is a coboundary. -/
theorem hilbert90_infinite_units {K L : Type*} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (a : Gal(L/K) → Additive Lˣ) (ha : IsCocycle1 a)
    (hc : IsLocallyConstant a) : ∃ β : Additive Lˣ, a = d0Fun (G := Gal(L/K)) β := by
  -- `a` is a cocycle; the multiplicative normalization of the cocycle identity.
  have hac : ∀ σ τ : Gal(L/K), (a (σ * τ)).toMul = (a σ).toMul * (σ • (a τ).toMul) := by
    intro σ τ
    have h' := congrArg Additive.toMul (ha σ τ)
    simpa only [toMul_add, toMul_smul_additiveUnits] using h'
  -- the value of a cocycle at `1` is `0`
  have ha1 : a 1 = 0 := by
    have h := ha 1 1
    simp only [one_mul, one_smul] at h
    have h2 : a 1 + a 1 = a 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h2
  -- local constancy: an open normal subgroup killed by `a`
  obtain ⟨M, hMfix⟩ : ∃ M : FiniteGaloisIntermediateField K L,
      ∀ σ : Gal(L/K), σ ∈ M.fixingSubgroup → a σ = 0 := by
    obtain ⟨U, hUo, hU1, hUc⟩ := (IsLocallyConstant.iff_exists_open a).mp hc 1
    have hU : U ∈ nhds (1 : Gal(L/K)) := hUo.mem_nhds hU1
    rw [InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois] at hU
    obtain ⟨M, hM⟩ := hU
    exact ⟨M, fun σ hσ => by rw [hUc σ (hM hσ), ha1]⟩
  -- restriction to the finite quotient `Gal(M/K)`
  let φ : Gal(L/K) →* Gal(↥M/K) := AlgEquiv.restrictNormalHom (↥M)
  have hφfix : ∀ σ : Gal(L/K), σ ∈ M.fixingSubgroup ↔ φ σ = 1 := fun σ =>
    (FiniteGaloisIntermediateField.mem_fixingSubgroup_iff σ M)
  -- `a` is constant on the fibres of `φ`
  have hdescent : ∀ σ τ : Gal(L/K), φ σ = φ τ → a σ = a τ := by
    intro σ τ h
    have hker : σ⁻¹ * τ ∈ M.fixingSubgroup := by
      rw [hφfix, map_mul, map_inv, h]; simp
    have hσ := ha σ (σ⁻¹ * τ)
    rw [hMfix _ hker, smul_zero, add_zero] at hσ
    have heq : σ * (σ⁻¹ * τ) = τ := by group
    rw [heq] at hσ
    exact hσ.symm
  have hdescent_mul : ∀ σ τ : Gal(L/K), φ σ = φ τ → (a σ).toMul = (a τ).toMul :=
    fun σ τ h => congrArg Additive.toMul (hdescent σ τ h)
  -- the values of `a` are fixed by `Gal(L/M)`
  have hsmul_fix : ∀ (h : Gal(L/K)), h ∈ M.fixingSubgroup → ∀ σ : Gal(L/K), h • a σ = a σ := by
    intro h hh σ
    have h1 : a (h * σ) = h • a σ := by
      have hc1 := ha h σ
      rw [hMfix h hh, zero_add] at hc1
      exact hc1
    have hconj : σ⁻¹ * h * σ ∈ M.fixingSubgroup := by
      rw [hφfix, map_mul, map_mul, map_inv, (hφfix h).mp hh]; simp
    have h2 : a (σ * (σ⁻¹ * h * σ)) = a σ := by
      have hc2 := ha σ (σ⁻¹ * h * σ)
      rw [hMfix _ hconj, smul_zero, add_zero] at hc2
      exact hc2
    have heq : h * σ = σ * (σ⁻¹ * h * σ) := by group
    rw [heq] at h1
    rw [← h1, h2]
  -- hence every value of `a` lies in `M`
  have hmem : ∀ σ : Gal(L/K), ((a σ).toMul : L) ∈ (M : IntermediateField K L) := by
    intro σ
    have hfixfield : ((a σ).toMul : L) ∈
        IntermediateField.fixedField (M : IntermediateField K L).fixingSubgroup := by
      rw [IntermediateField.mem_fixedField_iff]
      intro h hh
      have h3 := congrArg Additive.toMul (hsmul_fix h hh σ)
      rw [toMul_smul_additiveUnits] at h3
      have h4 := congrArg (fun y : Lˣ => (y : L)) h3
      rwa [AlgEquiv.smul_units_def, Units.coe_map] at h4
    rwa [InfiniteGalois.fixedField_fixingSubgroup (M : IntermediateField K L)] at hfixfield
  -- a chosen lift of an automorphism of `M` restricts back to it
  have hφlift : ∀ χ : Gal(↥M/K), φ (χ.liftNormal L) = χ := fun χ =>
    AlgEquiv.restrict_liftNormal L χ
  -- the descended cocycle `b`, with coefficients in `Mˣ`
  have hne : ∀ χ : Gal(↥M/K),
      (⟨(a (χ.liftNormal L)).toMul, hmem (χ.liftNormal L)⟩ : ↥M) ≠ 0 := by
    intro χ hzero
    have h1 := congrArg (fun y : ↥M => (y : L)) hzero
    have h0 : ((a (χ.liftNormal L)).toMul : L) = 0 := h1
    exact (a (χ.liftNormal L)).ne_zero h0
  let b : Gal(↥M/K) → Additive (↥M)ˣ := fun χ =>
    Additive.ofMul (Units.mk0 ⟨(a (χ.liftNormal L)).toMul, hmem (χ.liftNormal L)⟩ (hne χ))
  have hbval : ∀ χ : Gal(↥M/K), (b χ).toMul =
      Units.mk0 ⟨(a (χ.liftNormal L)).toMul, hmem (χ.liftNormal L)⟩ (hne χ) := fun χ => rfl
  have hbcoe : ∀ χ : Gal(↥M/K),
      (algebraMap ↥M L) ((b χ).toMul : ↥M) = ((a (χ.liftNormal L)).toMul : L) := by
    intro χ
    rw [hbval χ, Units.val_mk0]
    rfl
  -- the inclusion `Mˣ → Lˣ`
  let ι : (↥M)ˣ →* Lˣ := Units.map (algebraMap ↥M L).toMonoidHom
  have hιcoe : ∀ u : (↥M)ˣ, (ι u : L) = (algebraMap ↥M L) (u : ↥M) := by
    intro u
    dsimp only [ι]
    exact Units.coe_map _ u
  have haimg : ∀ χ : Gal(↥M/K), ι ((b χ).toMul) = (a (χ.liftNormal L)).toMul := by
    intro χ
    apply Units.ext
    show (ι ((b χ).toMul) : L) = ((a (χ.liftNormal L)).toMul : L)
    rw [hιcoe, hbcoe χ]
  have hι_inj : Function.Injective ι := by
    intro u v huv
    have h := congrArg (fun w : Lˣ => (w : L)) huv
    rw [hιcoe, hιcoe] at h
    exact Units.ext (Subtype.val_injective h)
  -- the inclusion is equivariant for the two Galois actions
  have hι_val : ∀ (σ : Gal(L/K)) (x : ↥M), σ ((x : L)) = (((φ σ) x : ↥M) : L) := by
    intro σ x
    exact (AlgEquiv.restrictNormal_apply (M : IntermediateField K L) σ x).symm
  have hι_smul : ∀ (σ : Gal(L/K)) (u : (↥M)ˣ), ι ((φ σ) • u) = σ • ι u := by
    intro σ u
    apply Units.ext
    show (ι ((φ σ) • u) : L) = (σ • ι u : L)
    rw [hιcoe, AlgEquiv.smul_units_def, Units.coe_map, hιcoe]
    exact (hι_val σ ↑u).symm
  have hι_smulχ : ∀ (χ : Gal(↥M/K)) (u : (↥M)ˣ), ι (χ • u) = (χ.liftNormal L) • ι u := by
    intro χ u
    have h := hι_smul (χ.liftNormal L) u
    rwa [show φ (χ.liftNormal L) = χ from hφlift χ] at h
  -- `b` is a `1`-cocycle
  have hb : IsCocycle1 b := by
    intro χ₁ χ₂
    have hφ12 : φ ((χ₁ * χ₂).liftNormal L) = φ ((χ₁.liftNormal L) * (χ₂.liftNormal L)) := by
      rw [map_mul, hφlift, hφlift, hφlift]
    apply Additive.toMul.injective
    apply hι_inj
    rw [show (b χ₁ + χ₁ • b χ₂).toMul = (b χ₁).toMul * (χ₁ • (b χ₂)).toMul from rfl]
    rw [toMul_smul_additiveUnits]
    rw [map_mul, hι_smulχ χ₁ (b χ₂).toMul, haimg χ₁, haimg χ₂, haimg (χ₁ * χ₂)]
    rw [hdescent_mul ((χ₁ * χ₂).liftNormal L) ((χ₁.liftNormal L) * (χ₂.liftNormal L)) hφ12]
    exact hac (χ₁.liftNormal L) (χ₂.liftNormal L)
  -- Hilbert 90 for the finite extension `M/K`
  obtain ⟨β, hβ⟩ := hilbert90_finite_units b hb
  -- assembly: `β`, viewed in `Lˣ`, is the required coboundary
  refine ⟨Additive.ofMul (ι β.toMul), ?_⟩
  funext σ
  apply Additive.toMul.injective
  have ha_b : (a σ).toMul = ι ((b (φ σ)).toMul) := by
    rw [hdescent_mul σ ((φ σ).liftNormal L) (by rw [hφlift (φ σ)])]
    exact (haimg (φ σ)).symm
  change Additive.toMul (a σ) = Additive.toMul (σ • Additive.ofMul (ι β.toMul))
      / Additive.toMul (Additive.ofMul (ι β.toMul))
  rw [toMul_smul_additiveUnits]
  change Additive.toMul (a σ) = σ • (ι β.toMul) / (ι β.toMul)
  rw [ha_b]
  rw [show b (φ σ) = d0Fun β (φ σ) from congrFun hβ (φ σ)]
  rw [show (d0Fun β (φ σ)).toMul = ((φ σ) • β.toMul) / β.toMul from by
        rw [d0Fun_apply, toMul_sub, toMul_smul_additiveUnits]]
  rw [map_div, hι_smul σ β.toMul]

end Work.ConCohomology
