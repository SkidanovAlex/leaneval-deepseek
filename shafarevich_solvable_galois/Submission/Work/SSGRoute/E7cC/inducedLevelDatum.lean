import Mathlib.RepresentationTheory.Coinduced
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.Work.SSGRoute.Sha2Lib.coind_cocycle_value
import Submission.Work.SSGRoute.e7comega_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The induced-module level datum of the unramified detector (node C6)

`Ind_{D_w}^{G₀} 𝔽_p` (`G₀ = Gal(K/k)`, `D_w = decompK w ≤ G₀`) is realised here as the `𝔽_p`-valued
functions on `G₀` that are constant on the cosets of `D_w`, i.e. invariant under *right*
multiplication by `D_w` (`f (γ * δ) = f γ`), with the left-translation `G₀`-action
`(σ · f) τ = f (σ⁻¹ τ)` — which preserves that submodule for *every* `D_w ≤ G₀` (no normality).

This is the module in which `Sha2Lib.isUnramifiedDetector_of_induced` works
(`M = Ind_{D_w}^{G} res_{D_w} M`) and the shape of `N = Gal(L/K)` produced by the *conjugates* of a
cyclic degree-`p` extension `K₁/K` of `K` in which `q` is unramified and inert
(`Sha2Lib.exists_unramified_inert_cyclic_level`, proved).

* `indDatum` is the submodule, `indDatumBase` the basis vector at the trivial coset (the indicator
  of `D_w`), i.e. the element `e_{D_w}` of the level statement
  `Work.SSGRoute.E7cC.exists_level_induced_unramifiedDetector`.

**Convention note** (found by the reviewers of the first draft of the level statement): the carrier
must be the *right*-invariant functions.  With the left-invariant carrier (`f (δ * γ) = f γ`) the
left-translation action is well defined only when `D_w ◁ G₀`, and the equivariance clause of the
level statement would then *force* `D_w ◁ G₀`, making the statement false for `k = ℚ`,
`K` = the splitting field of `X³ − 2`, `D_w = ℤ/2 ⋬ S₃`. -/

namespace Work.SSGRoute.E7cC

open CategoryTheory SSGRoute.PTExt

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-- **`Ind_{D_w}^{G₀} 𝔽_p`**: the `𝔽_p`-valued functions on `G₀` constant on the cosets of the
decomposition group `D_w = decompK w`, i.e. invariant under right multiplication by `D_w`. -/
noncomputable def indDatum (p : ℕ) (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) : AddSubgroup ((K ≃ₐ[k] K) → ZMod p) :=
  { carrier := {f | ∀ δ ∈ SSGRoute.PTExt.decompK (k := k) (K := K) w,
      ∀ γ : K ≃ₐ[k] K, f (γ * δ) = f γ}
    zero_mem' := by
      intro δ _ γ
      rfl
    add_mem' := by
      intro f g hf hg δ hδ γ
      simp only [Pi.add_apply, hf δ hδ γ, hg δ hδ γ]
    neg_mem' := by
      intro f hf δ hδ γ
      simp only [Pi.neg_apply, hf δ hδ γ] }

/-- The basis vector of `Ind_{D_w}^{G₀} 𝔽_p` at the **trivial coset**: the indicator of `D_w`.
This is the element denoted `e_{D_w}` in the level statement: the coordinate whose value under a
`G₀`-equivariant `φ : Ind_{D_w}^{G₀}𝔽_p → M` is a `D_w`-fixed vector of `M`. -/
noncomputable def indDatumBase (p : ℕ) (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) : ↥(indDatum p k K w) := by
  classical
  refine ⟨fun γ => if γ ∈ SSGRoute.PTExt.decompK (k := k) (K := K) w then 1 else 0, ?_⟩
  intro δ hδ γ
  by_cases h : γ * δ ∈ SSGRoute.PTExt.decompK (k := k) (K := K) w
  · have hγ : γ ∈ SSGRoute.PTExt.decompK (k := k) (K := K) w := by
      have h1 := (SSGRoute.PTExt.decompK (k := k) (K := K) w).mul_mem h
        ((SSGRoute.PTExt.decompK (k := k) (K := K) w).inv_mem hδ)
      simpa using h1
    simp only [if_pos h, if_pos hγ]
  · have hγ : γ ∉ SSGRoute.PTExt.decompK (k := k) (K := K) w := fun hc =>
      h ((SSGRoute.PTExt.decompK (k := k) (K := K) w).mul_mem hc hδ)
    simp only [if_neg h, if_neg hγ]

/-- **The coset-sum value rule for trivial coefficients** — the first line of the detection formula
(7.1) of `E7cC/NOTE_C6_session17_level_via_weakApproximation.md` §7.

`Sha2Lib.coind_cocycle_value` computes the value of a `1`-cocycle of the *coinduced* module at a
conjugate `φ δ = x⁻¹ * γ * x` up to two correction terms involving the values at `x`; for a trivial
coefficient module the corrections cancel and the value is literally the value of the *conjugate*
cocycle at the identity:

    (h γ).1 (x⁻¹) = (h (φ δ)).1 1 ,      φ δ = x⁻¹ * γ * x .

With `y := fun δ => (h (φ δ)).1 1` this is the rule `h(γ)(x) = y(x⁻¹ γ x)` of §7. -/
theorem coind_cocycle_value_trivial {k : Type} [CommRing k] {D Γ : Type} [Group D] [Group Γ]
    (φ : D →* Γ) (V : Rep.{0} k D) [V.IsTrivial]
    (h : Γ → (Rep.coind φ V).V)
    (hc : h ∈ (groupCohomology.cocycles₁ (Rep.coind φ V) : Set (Γ → (Rep.coind φ V).V)))
    (γ x : Γ) (δ : D) (hδ : φ δ = x⁻¹ * γ * x) :
    (h γ).1 (x⁻¹) = (h (φ δ)).1 1 := by
  rw [Work.SSGRoute.Sha2Lib.coind_cocycle_value φ V h hc γ x δ hδ]
  rw [Representation.isTrivial_apply]
  abel

/-- **The defect form of the Shapiro value rule** — the link the detection sum (7.1) consumes.

`Sha2Lib.coind_cocycle_value` says that the value of the coinduced `1`-cocycle at a conjugate
`φ δ = x⁻¹ * γ * x` differs from the value of the *conjugate* cocycle at the identity by a defect,
and the defect is `(1 - V.ρ δ)` applied to the coordinate `(h x).1 (x⁻¹)`:

    (h γ).1 (x⁻¹) - (h (φ δ)).1 1 = (1 - V.ρ δ) ((h x).1 (x⁻¹)) .

It is this defect that is summed against the coordinate functionals `ν_x` in
`E7cC/NOTE_C6_session17_level_via_weakApproximation.md` §7, and it is where the coefficient module
`A = res_{D_w}M` enters (the trivial-coefficient case `E7cC.coind_cocycle_value_trivial` is the
vanishing of the defect). -/
theorem coind_cocycle_value_defect {k : Type} [CommRing k] {D Γ : Type} [Group D] [Group Γ]
    (φ : D →* Γ) (V : Rep.{0} k D)
    (h : Γ → (Rep.coind φ V).V)
    (hc : h ∈ (groupCohomology.cocycles₁ (Rep.coind φ V) : Set (Γ → (Rep.coind φ V).V)))
    (γ x : Γ) (δ : D) (hδ : φ δ = x⁻¹ * γ * x) :
    (h γ).1 (x⁻¹) - (h (φ δ)).1 1 = (h x).1 (x⁻¹) - (V.ρ δ) ((h x).1 (x⁻¹)) := by
  rw [Work.SSGRoute.Sha2Lib.coind_cocycle_value φ V h hc γ x δ hδ]
  abel

/-- **The restriction `D̃ → D_w` of the decomposition group.**

For the level `L` of the detector and the place `w`, `D̃ = (decompK w).comap (galRes k K L)` is the
preimage in `Gal(L/k)` of the decomposition group `D_w = decompK w`; its elements act on
`K`-coefficient modules `A : Rep Coeff (decompK w)` through this restriction.  It is the auxiliary map
needed to state the base-change-of-induction isomorphism (24.1) of
`E7cC/NOTE_C6_session17_level_via_weakApproximation.md` §24, whose right-hand coefficient module must
be a representation of `D̃` (with codomain `decompK w`, *not* `↥L ≃ₐ[k] ↥L`). -/
noncomputable def dtildeToDw (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (L : IntermediateField K Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L] :
    ((SSGRoute.PTExt.decompK (k := k) (K := K) w).comap (SSGRoute.PTExt.galRes k K ↥L)) →*
      SSGRoute.PTExt.decompK (k := k) (K := K) w where
  toFun γ := ⟨SSGRoute.PTExt.galRes k K ↥L (γ : ↥L ≃ₐ[k] ↥L), Subgroup.mem_comap.mp γ.property⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (SSGRoute.PTExt.galRes k K ↥L)
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (SSGRoute.PTExt.galRes k K ↥L) (x : ↥L ≃ₐ[k] ↥L) (y : ↥L ≃ₐ[k] ↥L)

end Work.SSGRoute.E7cC
