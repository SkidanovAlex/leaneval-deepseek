import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.place_basics
import Submission.Work.SSGRoute.corestriction_hom_on_fixingSubgroup
import Submission.Work.SSGRoute.corestriction_vanishes_on_inertia
import Submission.Work.SSGRoute.isLocConstOn_corestriction
import Submission.Work.SSGRoute.exists_corestriction
import Submission.Work.SSGRoute.odd_involution_coboundary
import Submission.Work.SSGRoute.decomp_mod_inertia_cyclic
import Submission.Work.SSGRoute.exists_cyclic_quotient_subgroup_vanishing
import Submission.Work.SSGRoute.exists_cyclic_quotient_subgroup_of_cyclic_image
import Submission.Work.SSGRoute.PT.pairAlgebra
import Submission.Work.SSGRoute.ZConstruction.Reduction
import Submission.NK.Reconstruct.denseChebotarev
import Submission.NK.Reconstruct.restrictNormalHom_smul_valuationSubringAtPrime
import Submission.NeukirchUchida.PrimeCorrespondence
import Submission.NeukirchUchida.Local.Transitivity
import Submission.NeukirchUchida.Local.PlaceFromValuation
import Submission.NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely
import Submission.Work.SSGRoute.levelInertia_defs
import Submission.Work.SSGRoute.inertiaAtLevelDefs
import Submission.Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
import Submission.Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one
import Submission.Commons.RingTheory.Valuation.comap_valuationSubringAtPrime
import Submission.Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
import Submission.Commons.NumberTheory.NumberField.Valuation.centralizer_stabilizer_valuationSubring_sepClosure
import Submission.Work.SSGRoute.exists_levelSub_le_of_isOpen
import Submission.Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
import Submission.NK.ResidueFrob.primeOfLevel_liesOver
import Submission.NK.Chebotarev.FrobRestriction
import Submission.NK.Chebotarev.FrobeniusOne
import Submission.NK.Chebotarev.IsFrobAtStabilizes
import Submission.Work.SSGRoute.ZVocab
import Submission.Work.SSGRoute.ZPlace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `Solves` bundle and the reduction principles for Theorem 13

`Solves` packages the five clauses of the conclusion of Schmidt–Wingberg Theorem 13 for a
fixed witness `x`, so that the reduction principles (`solves_of_pullback`, `solves_of_surjection`,
`solves_of_prod_fst`) can be stated and proved once.  Moved here, below the node
`Work.SSGRoute.shafarevich_theorem13`, verbatim, so that the modules that consume `Solves`
(in particular `Submission/Work/SSGRoute/coind_module.lean`) can also live below the node.
-/

namespace Work.SSGRoute

open _root_.SSGRoute
open scoped Pointwise

/-- **The conclusion of Schmidt–Wingberg's Theorem 13 for a fixed witness `x`**, i.e. the bundle of
the five clauses of the theorem's conclusion (for the datum `y` and the section `sec`).  Packaging
the bundle makes the *reduction principles* for Theorem 13 statable and provable once. -/
def Solves (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    {E : Type} [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E]
    (S : Finset (ValuationSubring Ω)) (sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω))
    (y x : (Ω ≃ₐ[k] Ω) → E) : Prop :=
  IsCocycleOn (res k K) ⊤ x ∧ IsLocConstOn ⊤ x ∧
  (∀ A ∈ S, IsSplitIn k K A →
    IsCoboundaryOn (res k K) (decomp k A)
      (fun δ => x δ - ∑ s : K ≃ₐ[k] K, s • y ((sec s)⁻¹ * δ * sec s))) ∧
  (∀ A ∈ S, ¬ IsSplitIn k K A →
    IsCoboundaryOn (res k K) (decomp k A) x) ∧
  (∀ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 →
    IsCoboundaryOn (res k K) (Subgroup.zpowers c) x) ∧
  (∀ B : ValuationSubring Ω, IsFinPlace k B →
    (∀ A ∈ S, ¬ IsConjPlace k A B) → ¬ IsSplitIn k Λ B →
    ∀ σ : Ω ≃ₐ[k] Ω, IsInertia k B σ → x σ = 0) ∧
  ∀ B : ValuationSubring Ω, IsFinPlace k B → (∀ A ∈ S, ¬ IsConjPlace k A B) →
    ∃ U : Subgroup (Ω ≃ₐ[k] Ω),
      (∃ V : Subgroup (Ω ≃ₐ[k] Ω),
        IsOpen (V : Set (Ω ≃ₐ[k] Ω)) ∧ U = V ⊓ decomp k B) ∧
      (∀ δ ∈ decomp k B, ∀ u ∈ U, δ * u * δ⁻¹ ∈ U) ∧
      (∃ g ∈ decomp k B,
        ∀ δ ∈ decomp k B, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ U) ∧
      IsCoboundaryOn (res k K) U x

/-- **Pull-back (retraction) principle for Theorem 13.**

Let `π : E' →ₗ E` be `Gal(K|k)`-equivariant from a module `E'` onto `E`, and let `y'` be a datum in
`E'` which is admissible for Theorem 13 (additive and locally constant on `G_K`, and satisfying the
four vanishing conditions) and which *lifts* the given datum `y`, i.e. `π (y' σ) = y σ` for every
`σ`.  If Theorem 13's conclusion holds for `y'` with coefficients in `E'`, then it holds for `y` with
coefficients in `E`: the witness `x := π ∘ x'` satisfies every clause, because `π` preserves the
cocycle identity, local constancy and coboundaries, sends `0` to `0`, and commutes with the
corestriction sum (by equivariance) and with the values of `y'` (by the lift condition). -/
theorem solves_of_pullback (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [Field Ω]
    [Algebra k Ω] (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ]
    {E : Type} [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E]
    {E' : Type} [AddCommGroup E'] [Module (ZMod p) E'] [DistribMulAction (K ≃ₐ[k] K) E']
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E']
    (π : E' →ₗ[ZMod p] E) (hπ : ∀ (g : K ≃ₐ[k] K) (e' : E'), π (g • e') = g • π e')
    (S : Finset (ValuationSubring Ω))
    (y : (Ω ≃ₐ[k] Ω) → E) (y' : (Ω ≃ₐ[k] Ω) → E')
    (sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω))
    (hπy : ∀ σ, π (y' σ) = y σ)
    (h : ∃ x' : (Ω ≃ₐ[k] Ω) → E', Solves p k Ω K Λ S sec y' x') :
    ∃ x : (Ω ≃ₐ[k] Ω) → E, Solves p k Ω K Λ S sec y x := by
  classical
  obtain ⟨x', hx'⟩ := h
  obtain ⟨hx'1, hx'2, hx'3, hx'4, hx'5, hx'6, hx'7⟩ := hx'
  have hπsum : ∀ (f : (K ≃ₐ[k] K) → E'),
      π (∑ s : K ≃ₐ[k] K, s • f s) = ∑ s : K ≃ₐ[k] K, s • π (f s) := by
    intro f
    rw [map_sum]
    exact Finset.sum_congr rfl (fun s _ => hπ s (f s))
  have key : ∀ (m : E') (δ : Ω ≃ₐ[k] Ω),
      π (res k K δ • m - m) = res k K δ • π m - π m := by
    intro m δ
    rw [map_sub, hπ]
  refine ⟨fun δ => π (x' δ), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg h hh
    show π (x' (g * h)) = π (x' g) + res k K g • π (x' h)
    rw [hx'1 g hg h hh, map_add, hπ]
  · obtain ⟨U, hU, hcU⟩ := hx'2
    exact ⟨U, hU, fun g hg u hu hgu => by
      show π (x' (g * u)) = π (x' g)
      rw [hcU g hg u hu hgu]⟩
  · intro A hA hsp
    obtain ⟨m, hm⟩ := hx'3 A hA hsp
    refine ⟨π m, fun δ hδ => ?_⟩
    have hsum : (∑ s : K ≃ₐ[k] K, s • y ((sec s)⁻¹ * δ * sec s))
        = ∑ s : K ≃ₐ[k] K, s • π (y' ((sec s)⁻¹ * δ * sec s)) := by
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [hπy]
    have hcongr := congrArg π (hm δ hδ)
    rw [map_sub, hπsum (fun s : K ≃ₐ[k] K => y' ((sec s)⁻¹ * δ * sec s)), key m δ,
      ← hsum] at hcongr
    exact hcongr
  · intro A hA hns
    obtain ⟨m, hm⟩ := hx'4 A hA hns
    refine ⟨π m, fun δ hδ => ?_⟩
    show π (x' δ) = res k K δ • π m - π m
    have hcongr : π (x' δ) = π (res k K δ • m - m) := by rw [hm δ hδ]
    rw [key] at hcongr
    exact hcongr
  · intro c hc2
    obtain ⟨m, hm⟩ := hx'5 c hc2
    refine ⟨π m, fun δ hδ => ?_⟩
    show π (x' δ) = res k K δ • π m - π m
    have hcongr : π (x' δ) = π (res k K δ • m - m) := by rw [hm δ hδ]
    rw [key] at hcongr
    exact hcongr
  · intro B hB hconj hns σ hσ
    show π (x' σ) = 0
    rw [hx'6 B hB hconj hns σ hσ, map_zero]
  · intro B hB hconj
    obtain ⟨U, hUform, hUnorm, hUcyc, hUcob⟩ := hx'7 B hB hconj
    refine ⟨U, hUform, hUnorm, hUcyc, ?_⟩
    obtain ⟨m, hm⟩ := hUcob
    refine ⟨π m, fun δ hδ => ?_⟩
    show π (x' δ) = res k K δ • π m - π m
    have hcongr : π (x' δ) = π (res k K δ • m - m) := by rw [hm δ hδ]
    rw [key] at hcongr
    exact hcongr

/-- **Enlargement (retraction) principle for Theorem 13.**

If `π : E' →ₗ E` is `Gal(K|k)`-equivariant and surjective, and Theorem 13's conclusion holds for
*every* admissible datum with coefficients in `E'`, then it holds for the given datum `y` with
coefficients in `E`.  Indeed, if `s` is any additive section of `π` then `y' := s ∘ y` is admissible,
and `x := π ∘ x'` inherits every clause:

* the cocycle identity and local constancy are preserved by the additive equivariant map `π`;
* the coboundary clauses are preserved because `π` of a coboundary witness is a coboundary witness;
* the two "`= 0`" clauses are preserved because `π 0 = 0`;
* the corestriction sum commutes with `π` because `π` is equivariant.

Consequently the theorem for a general coefficient module follows from the theorem for any module
surjecting onto it — for instance from the *co-induced* module `Maps(Gal(K|k), E) = E ⊗ 𝔽_p[G]`,
which is the shape of the coefficient module arising in the application (the graded pieces of the
Shafarevich construction are free `𝔽_p[Gal(K|k)]`-modules). -/
theorem solves_of_surjection (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [Field Ω]
    [Algebra k Ω] (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ]
    {E : Type} [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E]
    {E' : Type} [AddCommGroup E'] [Module (ZMod p) E'] [DistribMulAction (K ≃ₐ[k] K) E']
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E']
    (π : E' →ₗ[ZMod p] E) (hπ : ∀ (g : K ≃ₐ[k] K) (e' : E'), π (g • e') = g • π e')
    (hsurj : Function.Surjective π)
    (S : Finset (ValuationSubring Ω))
    (y : (Ω ≃ₐ[k] Ω) → E)
    (sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω))
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, IsFinPlace k B →
      (∀ A ∈ S, ¬ IsConjPlace k A B) → ¬ IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S, IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S, IsConjPlace k A B) →
      (¬ IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (hE' : ∀ (y' : (Ω ≃ₐ[k] Ω) → E'),
      (∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y' (g * h) = y' g + y' h) →
      IsLocConstOn K.fixingSubgroup y' →
      (∀ B : ValuationSubring Ω, IsFinPlace k B →
        (∀ A ∈ S, ¬ IsConjPlace k A B) → ¬ IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → y' σ = 0) →
      (∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S, IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → y' σ = 0) →
      (∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S, IsConjPlace k A B) →
        (¬ IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ decomp k B → y' σ = 0) →
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y' c = 0) →
      ∃ x' : (Ω ≃ₐ[k] Ω) → E', Solves p k Ω K Λ S sec y' x') :
    ∃ x : (Ω ≃ₐ[k] Ω) → E, Solves p k Ω K Λ S sec y x := by
  classical
  obtain ⟨s, hs⟩ : ∃ s : E →ₗ[ZMod p] E', π.comp s = LinearMap.id :=
    LinearMap.exists_rightInverse_of_surjective π (LinearMap.range_eq_top.mpr hsurj)
  have hs' : ∀ e : E, π (s e) = e := fun e => by
    have h := LinearMap.congr_fun hs e
    simpa using h
  let y' : (Ω ≃ₐ[k] Ω) → E' := fun σ => s (y σ)
  have hy' : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y' (g * h) = y' g + y' h := by
    intro g hg h hh
    show s (y (g * h)) = s (y g) + s (y h)
    rw [hy g hg h hh, map_add]
  have hyc' : IsLocConstOn K.fixingSubgroup y' := by
    obtain ⟨U, hU, hcU⟩ := hyc
    exact ⟨U, hU, fun g hg u hu hgu => by
      show s (y (g * u)) = s (y g)
      rw [hcU g hg u hu hgu]⟩
  have hyS' : ∀ B : ValuationSubring Ω, IsFinPlace k B →
      (∀ A ∈ S, ¬ IsConjPlace k A B) → ¬ IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → y' σ = 0 := by
    intro B hB hc hs σ hσ hI
    show s (y σ) = 0
    rw [hyS B hB hc hs σ hσ hI, map_zero]
  have hyT' : ∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S, IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → y' σ = 0 := by
    intro B hB hc σ hσ hI
    show s (y σ) = 0
    rw [hyT B hB hc σ hσ hI, map_zero]
  have hy0' : ∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S, IsConjPlace k A B) →
      (¬ IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ decomp k B → y' σ = 0 := by
    intro B hB hc hd σ hσ hD
    show s (y σ) = 0
    rw [hy0 B hB hc hd σ hσ hD, map_zero]
  have hyinf' : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y' c = 0 := by
    intro c hc hc2
    show s (y c) = 0
    rw [hyinf c hc hc2, map_zero]
  exact solves_of_pullback p k Ω K Λ π hπ S y y' sec (fun σ => hs' (y σ))
    (hE' y' hy' hyc' hyS' hyT' hy0' hyinf')
/-- **Enlargement along a direct summand: `Solves` for `E ⊕ F` gives `Solves` for `E`.**

The datum `(y, 0)` on `E × F` is admissible whenever `y` is, and `Prod.fst : E × F →ₗ E` is
`Gal(K|k)`-equivariant and onto, so `solves_of_pullback` applies.  This is the statement-level form
of the reduction of finding 1: the conclusion of Theorem 13 for a coefficient module `E` follows from
the conclusion for `E ⊕ F` for *any* `F`, so it is enough to prove it for the self-dual module
`E ⊕ E^∨(1)` (where the paper's §4 verification of condition (b) is available), for the co-induced
module `E ⊗ 𝔽_p[Gal(K|k)]` (the shape of the coefficient module of the application), or for
`E ⊕ μ_p^N`. -/
theorem solves_of_prod_fst (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [Field Ω]
    [Algebra k Ω] (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ]
    {E : Type} [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E]
    {F : Type} [AddCommGroup F] [Module (ZMod p) F] [DistribMulAction (K ≃ₐ[k] K) F]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) F]
    (S : Finset (ValuationSubring Ω)) (y : (Ω ≃ₐ[k] Ω) → E)
    (sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω))
    (h : ∃ x' : (Ω ≃ₐ[k] Ω) → E × F,
        Solves p k Ω K Λ S sec (fun σ => (y σ, 0)) x') :
    ∃ x : (Ω ≃ₐ[k] Ω) → E, Solves p k Ω K Λ S sec y x :=
  solves_of_pullback p k Ω K Λ (LinearMap.fst (ZMod p) E F)
    (fun g e' => Prod.smul_fst g e') S y (fun σ => (y σ, 0)) sec (fun σ => rfl) h

end Work.SSGRoute
