import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.adicCompletionMap_comp
import Submission.Commons.NumberTheory.NumberField.Completion.adicCompletionMap_injective
import Submission.Commons.NumberTheory.NumberField.Completion.decompositionSubgroup_adicCompletionIntegers_eq_top
import Submission.Commons.NumberTheory.NumberField.Completion.exists_galois_unramified_tower_with_subfield
import Submission.Commons.NumberTheory.NumberField.Completion.finite_groupCohomology_two_units_adicCompletion_of_isGalois
import Submission.Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.isCyclic_algEquiv_adicCompletion_of_ramificationIdx_eq_one
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_algEquiv_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_groupCohomology_two_units_eq_card_of_cyclic_arbitrary_base
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_groupCohomology_two_units_le_finrank_of_abelian
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_groupCohomology_two_units_topAlgEquiv
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_adicCompletion_eq_mul_of_exists_open_subgroup_units_tate_trivial
import Submission.Commons.NumberTheory.NumberField.Completion.norm_units_surjective_of_ramificationIdx_eq_one
import Submission.Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow
import Submission.Commons.NumberTheory.NumberField.Completion.val_norm_units_adicCompletion_eq_pow_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
import Submission.Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
import Submission.Commons.RepresentationTheory.GroupCohomology.H2_inflation_injective_of_subsingleton_H1
import Submission.Commons.RepresentationTheory.GroupCohomology.H2_inflation_restriction_comp_zero
import Submission.Commons.RepresentationTheory.GroupCohomology.H2_inflation_restriction_exact_of_subsingleton_H1
import Submission.Commons.RepresentationTheory.GroupCohomology.groupCohomology_two_int_iso_one_qmodz
import Submission.Commons.RepresentationTheory.GroupCohomology.isZero_iff_subsingleton_moduleCat
import Submission.Commons.RepresentationTheory.GroupCohomology.mono_map_of_isZero_kernel
import Submission.Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_two_eq_natCard_tateCohomology_zero_of_cyclic
import Submission.Commons.RepresentationTheory.GroupCohomology.natCard_nsmul_H2_eq_zero
import Submission.Commons.RepresentationTheory.GroupCohomology.natCard_quotientToInvariants_le_of_twist
import Submission.Commons.RepresentationTheory.GroupCohomology.res_comp_inf_eq_zero_of_ord
import Submission.Commons.RepresentationTheory.TateCohomology.natCard_tateCohomology_zero_units
import Submission.Commons.RepresentationTheory.TateCohomology.tateCohomology_zero_iso
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
/-!
# The first inequality of local class field theory for the units: the number-field case

For number fields `L ⊆ L'` with `L'/L` Galois and places `q' | q`, the local degree is bounded
by the order of the second cohomology of the units of the local field:

  `[L'_{q'} : L_q] ≤ # H²(Gal(L'_{q'}/L_q), (L'_{q'})ˣ)`.

This is the base form of the *first inequality* of local class field theory
(Milne, *CFT*, III.2.2), and the long-standing crux of this workspace: local class field theory
gives equality, so the statement cannot be obtained from formal group cohomology alone.

## Proof

Put `e₀ = e(q'|q)`, `f₀ = f(q'|q)` (so `[L'_{q'} : L_q] = e₀ f₀`) and `F = L_q`, `E = L'_{q'}`.
The published tower lemma `exists_galois_unramified_tower_with_subfield` supplies a Galois
extension `L'' ⊇ L' ⊇ L` and a subfield `L₁ ⊆ L''` with places `q'' | q' | q`, `q₁ | q` such
that `e(q''|q') = 1`, `f(q''|q') = e₀`, `e(q₁|q) = 1`, `f(q₁|q) = e₀ f₀`.  Writing
`M = L''_{q''}`, `K' = L₁_{q₁}`, `Γ = Gal(M/F)`, `N = Gal(M/E)` and `Δ = Gal(M/K')`, the twist is
the following diagram of subgroups, where every vertical arrow is *injective*:

  `H²(Γ⧸Δ, M^Δ) --Inf_Δ--> H²(Γ, Mˣ) <--Inf_N-- H²(Γ⧸N, M^N)`

* `H²(Γ⧸Δ, M^Δ) = H²(Gal(K'/F), K'ˣ) ≅ ℤ/(e₀f₀)`: `K'/F` is unramified of degree `e₀f₀`, hence
  cyclic, and the cyclic norm-index theorem for units gives `#H² = e₀ f₀`.
* `Inf_Δ` and `Inf_N` are injective (Hilbert 90 for the units: `H¹` vanishes for every subgroup),
  and `ker(Res_N) = range(Inf_N)` (Hilbert 90 + exactness of the inflation–restriction sequence in
  degree two).
* **The crux** `Res_N ∘ Inf_Δ = 0`: `Res_N ∘ Inf_Δ` is the map induced by the inclusion
  `ι : (M^Δ)ˣ ↪ Mˣ`.  On `Mˣ` we have the valuation `ord₂ = v_M`, on `(M^Δ)ˣ ≅ (K')ˣ` the
  valuation `ord₁ = v_{K'}`, and `ι ≫ ord₂ = e₀ • ord₁` is the standard identity
  `v_M(α) = e(M/K') · v_{K'}(α)` for `α ∈ K'` (`unitsValLog_algebraMap`), together with
  `e(M/K') = e₀`.  Since `map(id) ord₂` is a *mono* on `H²` (its kernel is `H²(N, O_Mˣ) = 0`
  because `M/E` is unramified, from the short exact sequence `1 → O_Mˣ → Mˣ → ℤ → 1`) and
  `Nat.card N = e₀` kills `e₀ • H²(N, ℤ)`, the map induced by `ι` vanishes; this is the published
  combinatorial lemma `res_comp_inf_eq_zero_of_ord`.
* Hence `range(Inf_Δ) ⊆ range(Inf_N)` and, both inflation maps being injective,
  `#H²(Γ⧸Δ, M^Δ) ≤ #H²(Γ⧸N, M^N)` (`natCard_quotientToInvariants_le_of_twist`).
* Finally `H²(Γ⧸N, M^N) ≅ H²(Gal(E/F), Eˣ)` by Galois descent and transport along `φ : E ↪ M`.

Putting everything together, `[L'_{q'} : L_q] = e₀ f₀ = #H²(Γ⧸Δ, M^Δ) ≤ #H²(Gal(E/F), Eˣ)`.

The file also contains, in the section `IntegersUnitsUnramified`, the unramified input
`H²(Gal(L_q/K_Q), O_{L_q}ˣ) = 0` (the `mono` hypothesis above) together with its supporting
representation-theoretic constructions.
-/

open scoped NumberField
open CategoryTheory Representation
open IsDedekindDomain

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace Commons.NumberTheory.NumberField.Completion

section IntegersUnitsUnramified

variable {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

noncomputable def geIntegersUnitsAction
    (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    MulSemiringAction (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      ↥(q.adicCompletionIntegers L) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  let A : ValuationSubring (q.adicCompletion L) := q.adicCompletionIntegers L
  have htop : A.decompositionSubgroup (Q.adicCompletion K) = ⊤ :=
    decompositionSubgroup_adicCompletionIntegers_eq_top Q q hq
  let e : (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) ≃*
      ↥(A.decompositionSubgroup (Q.adicCompletion K)) :=
    (Subgroup.topEquiv.symm).trans (MulEquiv.subgroupCongr htop.symm)
  exact
    { smul := fun γ x => e γ • x
      one_smul := fun x => by show e 1 • x = x; rw [map_one]; exact one_smul _ x
      mul_smul := fun γ δ x => by
        show e (γ * δ) • x = e γ • (e δ • x); rw [map_mul]; exact mul_smul _ _ _
      smul_add := fun γ x y => by
        show e γ • (x + y) = e γ • x + e γ • y; exact smul_add _ _ _
      smul_zero := fun γ => by show e γ • (0 : ↥A) = 0; exact smul_zero _
      smul_one := fun γ => by show e γ • (1 : ↥A) = 1; exact smul_one _
      smul_mul := fun γ x y => by
        show e γ • (x * y) = e γ • x * e γ • y; exact smul_mul' _ _ _ }

noncomputable def geIntegersUnitsUnitsAction
    (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    MulDistribMulAction (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (q.adicCompletionIntegers L)ˣ := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  letI : MulSemiringAction (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      ↥(q.adicCompletionIntegers L) := geIntegersUnitsAction Q q hq
  let ψ : (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) →*
      RingAut ↥(q.adicCompletionIntegers L) := MulSemiringAction.toRingAut _ _
  exact
    { smul := fun γ u => Units.map (ψ γ).toMonoidHom u
      one_smul := fun u => by
        show Units.map ((ψ 1).toMonoidHom) u = u
        rw [map_one]; rfl
      mul_smul := fun γ δ u => by
        show Units.map (ψ (γ * δ)).toMonoidHom u
          = Units.map (ψ γ).toMonoidHom (Units.map (ψ δ).toMonoidHom u)
        rw [map_mul]; rfl
      smul_mul := fun γ u v => by
        show Units.map (ψ γ).toMonoidHom (u * v)
          = Units.map (ψ γ).toMonoidHom u * Units.map (ψ γ).toMonoidHom v
        exact map_mul _ _ _
      smul_one := fun γ => by
        show Units.map (ψ γ).toMonoidHom (1 : (q.adicCompletionIntegers L)ˣ) = 1
        exact map_one _ }

noncomputable def geIntegersUnitsRep
    (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    Representation ℤ (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (Additive (q.adicCompletionIntegers L)ˣ) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  letI : MulDistribMulAction (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (q.adicCompletionIntegers L)ˣ := geIntegersUnitsUnitsAction Q q hq
  exact Representation.ofMulDistribMulAction _ _

/-- The action of `Γ` on `Oˣ` is the Galois action. -/
theorem geIntegersUnitsRep_apply_coe
    (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∀ (γ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (u : (q.adicCompletionIntegers L)ˣ),
      ((Additive.toMul ((geIntegersUnitsRep Q q hq) γ (Additive.ofMul u)) :
          (q.adicCompletionIntegers L)ˣ) : q.adicCompletion L)
        = γ ((u : (q.adicCompletionIntegers L)ˣ) : q.adicCompletion L) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  intro γ u
  rfl


/-- The norm of the `Oˣ`-representation, as a product over `Γ`. -/
theorem geIntegersUnitsRep_norm_apply
    (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    letI : MulDistribMulAction (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (q.adicCompletionIntegers L)ˣ := geIntegersUnitsUnitsAction Q q hq
    letI : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
      module_finite_adicCompletion Q q hq
    letI : Fintype (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
      AlgEquiv.fintype (Q.adicCompletion K) (q.adicCompletion L)
    ∀ u : (q.adicCompletionIntegers L)ˣ,
      (geIntegersUnitsRep Q q hq).norm (Additive.ofMul u)
        = Additive.ofMul (∏ γ : (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L),
            γ • u) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  letI : MulDistribMulAction (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (q.adicCompletionIntegers L)ˣ := geIntegersUnitsUnitsAction Q q hq
  intro u
  letI : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    module_finite_adicCompletion Q q hq
  letI : Fintype (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
    AlgEquiv.fintype (Q.adicCompletion K) (q.adicCompletion L)
  exact Representation.norm_ofMulDistribMulAction_eq (Additive.ofMul u)

/-- The norm of the `Oˣ`-representation is the field norm. -/
theorem geIntegersUnitsRep_norm_coe
    (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    letI : MulDistribMulAction (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (q.adicCompletionIntegers L)ˣ := geIntegersUnitsUnitsAction Q q hq
    letI : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
      module_finite_adicCompletion Q q hq
    letI : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
      isGalois_adicCompletion Q q hq
    letI : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
      module_finite_adicCompletion Q q hq
    letI : Fintype (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
      AlgEquiv.fintype (Q.adicCompletion K) (q.adicCompletion L)
    ∀ u : (q.adicCompletionIntegers L)ˣ,
      ((Additive.toMul ((geIntegersUnitsRep Q q hq).norm (Additive.ofMul u)) :
          (q.adicCompletionIntegers L)ˣ) : q.adicCompletion L)
        = algebraMap (Q.adicCompletion K) (q.adicCompletion L)
            (Algebra.norm (Q.adicCompletion K) ((u : (q.adicCompletionIntegers L)ˣ) :
              q.adicCompletion L)) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  letI : MulDistribMulAction (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (q.adicCompletionIntegers L)ˣ := geIntegersUnitsUnitsAction Q q hq
  intro u
  letI : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    module_finite_adicCompletion Q q hq
  letI : IsGalois (Q.adicCompletion K) (q.adicCompletion L) := isGalois_adicCompletion Q q hq
  letI : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    module_finite_adicCompletion Q q hq
  letI : Fintype (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
    AlgEquiv.fintype (Q.adicCompletion K) (q.adicCompletion L)
  have h1 : (geIntegersUnitsRep Q q hq).norm (Additive.ofMul u)
      = Additive.ofMul (∏ γ : (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L),
          γ • u) :=
    Representation.norm_ofMulDistribMulAction_eq (Additive.ofMul u)
  have h2 : Additive.toMul (Additive.ofMul
      (∏ γ : (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L), γ • u))
      = (∏ γ : (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L), γ • u) := rfl
  rw [h1, h2]
  have hsplit : (((∏ γ : (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L), γ • u) :
      (q.adicCompletionIntegers L)ˣ) : q.adicCompletion L)
      = ∏ γ : (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L),
        (((γ • u : (q.adicCompletionIntegers L)ˣ) : q.adicCompletionIntegers L) :
          q.adicCompletion L) := by
    simp
  have hcoe : (((∏ γ : (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L), γ • u) :
      (q.adicCompletionIntegers L)ˣ) : q.adicCompletion L)
      = ∏ γ : (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L),
        γ ((u : (q.adicCompletionIntegers L)ˣ) : q.adicCompletion L) := by
    rw [hsplit]
    exact Finset.prod_congr rfl fun γ _ => geIntegersUnitsRep_apply_coe Q q hq γ u
  rw [hcoe, ← Algebra.norm_eq_prod_automorphisms]


/-! ## The vanishing of `H²` of the units of the ring of integers -/

open Representation

/-- In `WithZero (Multiplicative ℤ)` an `n`-th power (`n ≠ 0`) is `1` only if the element is `1`. -/
private theorem geWithZero_pow_eq_one {a : WithZero (Multiplicative ℤ)} {n : ℕ} (hn : n ≠ 0)
    (h : a ^ n = 1) : a = 1 := by
  rcases lt_trichotomy a 1 with hlt | heq | hgt
  · have h' := pow_lt_one₀ zero_le hlt hn
    rw [h] at h'
    exact absurd h' (lt_irrefl 1)
  · exact heq
  · have h' := one_lt_pow₀ hgt hn
    rw [h] at h'
    exact absurd h' (lt_irrefl 1)

/-- **Every `Γ`-invariant unit of `O_{L_q}` is a norm** (for `e(q|Q) = 1`). -/
theorem geMem_range_norm_of_mem_invariants
    (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (h1 : q.asIdeal.ramificationIdx (𝓞 K) = 1) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    letI : MulDistribMulAction (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (q.adicCompletionIntegers L)ˣ := geIntegersUnitsUnitsAction Q q hq
    letI : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
      module_finite_adicCompletion Q q hq
    letI : IsGalois (Q.adicCompletion K) (q.adicCompletion L) := isGalois_adicCompletion Q q hq
    letI : Fintype (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
      AlgEquiv.fintype (Q.adicCompletion K) (q.adicCompletion L)
    ∀ x : (q.adicCompletionIntegers L)ˣ,
      Additive.ofMul x ∈ (geIntegersUnitsRep Q q hq).invariants →
      Additive.ofMul x ∈ LinearMap.range (geIntegersUnitsRep Q q hq).norm := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  letI : MulDistribMulAction (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (q.adicCompletionIntegers L)ˣ := geIntegersUnitsUnitsAction Q q hq
  intro x hx
  letI : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    module_finite_adicCompletion Q q hq
  letI : IsGalois (Q.adicCompletion K) (q.adicCompletion L) := isGalois_adicCompletion Q q hq
  letI : Fintype (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
    AlgEquiv.fintype (Q.adicCompletion K) (q.adicCompletion L)
  have hfix : ∀ γ : (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L),
      (geIntegersUnitsRep Q q hq) γ (Additive.ofMul x) = Additive.ofMul x :=
    (Representation.mem_invariants (geIntegersUnitsRep Q q hq) (Additive.ofMul x)).mp hx
  have hfixL : ∀ γ : (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L),
      γ (((x : (q.adicCompletionIntegers L)ˣ) : q.adicCompletion L)) =
        ((x : (q.adicCompletionIntegers L)ˣ) : q.adicCompletion L) := by
    intro γ
    have h2 := geIntegersUnitsRep_apply_coe Q q hq γ x
    rw [show Additive.toMul ((geIntegersUnitsRep Q q hq) γ (Additive.ofMul x)) = x from
      congrArg Additive.toMul (hfix γ)] at h2
    exact h2.symm
  have hbot : ((x : (q.adicCompletionIntegers L)ˣ) : q.adicCompletion L) ∈
      (⊥ : IntermediateField (Q.adicCompletion K) (q.adicCompletion L)) :=
    (IsGalois.mem_bot_iff_fixed (F := Q.adicCompletion K) (E := q.adicCompletion L)
      ((x : (q.adicCompletionIntegers L)ˣ) : q.adicCompletion L)).mpr hfixL
  rw [IntermediateField.mem_bot] at hbot
  obtain ⟨y, hy⟩ := hbot
  have hxl0 : ((x : (q.adicCompletionIntegers L)ˣ) : q.adicCompletion L) ≠ 0 :=
    fun h => (x : (q.adicCompletionIntegers L)ˣ).ne_zero (Subtype.ext h)
  have hy0 : y ≠ 0 := fun h => hxl0 (by rw [← hy, h, map_zero])
  have hxval : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
      (((x : (q.adicCompletionIntegers L)ˣ) : q.adicCompletion L)) = 1 :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
      (R := 𝓞 L) (K := L) (v := q) (a := (x : q.adicCompletionIntegers L))).mp x.isUnit
  have hyval : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) y = 1 := by
    have hp := val_adicCompletionMap_eq_pow Q q hq y
    rw [h1, pow_one] at hp
    have hxv : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        (Commons.RingTheory.Henselian.adicCompletionMap Q q hq y) = 1 := by
      change Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        (algebraMap (Q.adicCompletion K) (q.adicCompletion L) y) = 1
      rw [hy]
      exact hxval
    rw [hxv] at hp
    exact hp.symm
  obtain ⟨u, hu⟩ := norm_units_surjective_of_ramificationIdx_eq_one Q q hq h1 y hyval
  have hdeg : Module.finrank (Q.adicCompletion K) (q.adicCompletion L) ≠ 0 := by
    haveI : Module.Finite (Q.adicCompletion K) (q.adicCompletion L) :=
      module_finite_adicCompletion Q q hq
    exact (Module.finrank_pos (R := Q.adicCompletion K) (M := q.adicCompletion L)).ne'
  have hmapy : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
      (algebraMap (Q.adicCompletion K) (q.adicCompletion L) y) = 1 := by
    rw [hy]
    exact hxval
  have huval : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) u = 1 := by
    have hp := val_norm_adicCompletion_eq_pow Q q hq u
    rw [hu, hmapy] at hp
    exact geWithZero_pow_eq_one hdeg hp.symm
  have humem : u ∈ q.adicCompletionIntegers L := by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    rw [huval]
  have hunit : IsUnit (⟨u, humem⟩ : q.adicCompletionIntegers L) := by
    rw [IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    exact huval
  let w : (q.adicCompletionIntegers L)ˣ := hunit.unit
  have hwcoe : ((w : (q.adicCompletionIntegers L)ˣ) : q.adicCompletion L) = u :=
    congrArg (fun z : q.adicCompletionIntegers L => (z : q.adicCompletion L))
      (IsUnit.unit_spec hunit)
  refine ⟨Additive.ofMul w, ?_⟩
  have hnorm : (geIntegersUnitsRep Q q hq).norm (Additive.ofMul w)
      = Additive.ofMul (∏ γ : (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L),
          γ • w) :=
    Representation.norm_ofMulDistribMulAction_eq (Additive.ofMul w)
  rw [hnorm]
  congr 1
  refine Units.ext (Subtype.ext ?_)
  have hsplit : (((∏ γ : (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L), γ • w) :
      (q.adicCompletionIntegers L)ˣ) : q.adicCompletion L)
      = ∏ γ : (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L),
        (((γ • w : (q.adicCompletionIntegers L)ˣ) : q.adicCompletionIntegers L) :
          q.adicCompletion L) := by
    simp
  rw [hsplit]
  have hstep : ∀ γ : (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L),
      (((γ • w : (q.adicCompletionIntegers L)ˣ) : q.adicCompletionIntegers L) :
          q.adicCompletion L) = γ u := by
    intro γ
    have h2 := geIntegersUnitsRep_apply_coe Q q hq γ w
    rw [show Additive.toMul ((geIntegersUnitsRep Q q hq) γ (Additive.ofMul w)) = γ • w
      from rfl] at h2
    rw [h2, hwcoe]
  rw [Finset.prod_congr rfl (fun γ _ => hstep γ)]
  rw [← Algebra.norm_eq_prod_automorphisms, hu, hy]


/-- **`H²` of the units of the ring of integers vanishes for unramified extensions.**

For an unramified finite Galois extension `L_q / K_Q` (`e(q|Q) = 1`), the second cohomology of the
units of the ring of integers is trivial.  Equivalently the norm `N : O_{L_q}ˣ → O_{K_Q}ˣ` is
surjective.  This is the atomic input of the unramified twist (Milne, *CFT* III.2). -/
theorem geSubsingleton_groupCohomology_two_integersUnits
    (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (h1 : q.asIdeal.ramificationIdx (𝓞 K) = 1) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    letI : MulDistribMulAction (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (q.adicCompletionIntegers L)ˣ := geIntegersUnitsUnitsAction Q q hq
    letI : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
      module_finite_adicCompletion Q q hq
    letI : IsGalois (Q.adicCompletion K) (q.adicCompletion L) := isGalois_adicCompletion Q q hq
    letI : Fintype (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
      AlgEquiv.fintype (Q.adicCompletion K) (q.adicCompletion L)
    Subsingleton (groupCohomology (Rep.of (geIntegersUnitsRep Q q hq)) 2) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  letI : MulDistribMulAction (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (q.adicCompletionIntegers L)ˣ := geIntegersUnitsUnitsAction Q q hq
  letI : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    module_finite_adicCompletion Q q hq
  letI : IsGalois (Q.adicCompletion K) (q.adicCompletion L) := isGalois_adicCompletion Q q hq
  letI : Fintype (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
    AlgEquiv.fintype (Q.adicCompletion K) (q.adicCompletion L)
  haveI hcyc : IsCyclic (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
    isCyclic_algEquiv_adicCompletion_of_ramificationIdx_eq_one Q q hq h1
  letI : CommGroup (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
    IsCyclic.commGroup
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator
    (α := q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
  -- every invariant unit is a norm
  have htop : (LinearMap.range (geIntegersUnitsRep Q q hq).norm).comap
      (geIntegersUnitsRep Q q hq).invariants.subtype = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro v
    rw [Submodule.mem_comap]
    exact geMem_range_norm_of_mem_invariants Q q hq h1 (Additive.toMul v.1) (by simpa using v.2)
  haveI : Subsingleton ((geIntegersUnitsRep Q q hq).invariants ⧸
      (LinearMap.range (geIntegersUnitsRep Q q hq).norm).comap
        (geIntegersUnitsRep Q q hq).invariants.subtype) := by
    rw [htop]
    infer_instance
  -- hence `Ĥ⁰` is trivial
  obtain ⟨e⟩ := Commons.RepresentationTheory.TateCohomology.tateCohomology_zero_iso
    (geIntegersUnitsRep Q q hq)
  haveI hsub : Subsingleton (tateCohomology (Rep.of (geIntegersUnitsRep Q q hq)) 0) :=
    ⟨fun a b => e.injective (Subsingleton.elim (e a) (e b))⟩
  -- and `|H²| = |Ĥ⁰|` by cyclic periodicity
  have hper :=
    Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_two_eq_natCard_tateCohomology_zero_of_cyclic
      g hg (Rep.of (geIntegersUnitsRep Q q hq))
  have hcard : Nat.card (tateCohomology (Rep.of (geIntegersUnitsRep Q q hq)) 0) = 1 :=
    Nat.card_unique
  have htwo : Nat.card (groupCohomology (Rep.of (geIntegersUnitsRep Q q hq)) 2) = 1 := by
    rw [hper, hcard]
  exact (Nat.card_eq_one_iff_unique.mp htwo).1


/-! The arithmetic face of the result above — surjectivity of the norm on the units of the ring of
integers — is published in the commons as
`Commons.NumberTheory.NumberField.Completion.norm_adicCompletionIntegers_surjective_of_ramificationIdx_eq_one`
(so the duplicate is omitted here to avoid a name clash). -/



end IntegersUnitsUnramified

section ShortComplexHelpers

open CategoryTheory

private lemma infNatTrans_app_apply {k : Type} [CommRing k] {G : Type} [Group G]
    (S : Subgroup G) [S.Normal] (n : ℕ) (A : Rep k G) :
    (groupCohomology.infNatTrans k S n).app A
      = groupCohomology.map (QuotientGroup.mk' S) (Rep.ofHom (A.ρ.quotientToInvariants_lift S)) n :=
  rfl

private lemma resNatTrans_app_apply {k : Type} [CommRing k] {G : Type} [Group G]
    (S : Subgroup G) [S.Normal] (n : ℕ) (A : Rep k G) :
    (groupCohomology.resNatTrans k (G := S) (H := G) S.subtype n).app A
      = groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) n :=
  rfl

end ShortComplexHelpers

theorem ge_finrank_adicCompletion_of_galois
    {L : Type} [Field L] [NumberField L] {L' : Type} [Field L'] [NumberField L']
    [Algebra L L'] [FiniteDimensional L L'] [IsGalois L L']
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L'))
    (hq : q'.asIdeal.LiesOver q.asIdeal) :
    letI : Algebra (q.adicCompletion L) (q'.adicCompletion L') :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q q' hq)
    Module.finrank (q.adicCompletion L) (q'.adicCompletion L') ≤
      Nat.card (groupCohomology
        (Rep.ofAlgebraAutOnUnits (q.adicCompletion L) (q'.adicCompletion L')) 2) := by
  letI : Algebra (q.adicCompletion L) (q'.adicCompletion L') :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q q' hq)
  set e0 : ℕ := q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers L) with he0
  set f0 : ℕ := q'.asIdeal.inertiaDeg (NumberField.RingOfIntegers L) with hf0
  set N0 : ℕ := Nat.card (NumberField.RingOfIntegers L ⧸ q.asIdeal) with hN0
  have hresL' : Nat.card (NumberField.RingOfIntegers L' ⧸ q'.asIdeal) = N0 ^ f0 := by
    rw [hN0, hf0]
    exact Commons.NumberTheory.NumberField.natCard_residue_eq_pow_inertiaDeg q q' hq
  have he0pos : 0 < e0 := by
    rw [he0]
    exact Ideal.ramificationIdx_pos (NumberField.RingOfIntegers L) q'.asIdeal
  have hf0pos : 0 < f0 := by
    rw [hf0]
    exact Ideal.inertiaDeg_pos q'.asIdeal (NumberField.RingOfIntegers L)
  have hfin : Module.finrank (q.adicCompletion L) (q'.adicCompletion L') = e0 * f0 := by
    rw [he0, hf0]
    exact (Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
      q q' hq).symm
  -- the unramified twist
  obtain ⟨L'', hL''f, hL''n, hAlgL, hAlgL', hST, hfdL, hfdL', hgalL, hgalL', q'', hq''lies, he'', hf'',
      L₁, hL₁f, hL₁n, hAlg₁, hfd₁, hgal₁, hAlg₁'', hST₁, hfd₁'', hgal₁'', q₁, hq₁lies, hq₁lies'',
      he₁, hf₁⟩ :=
    exists_galois_unramified_tower_with_subfield (L := L) (L' := L') q q' hq e0 he0pos
  letI : Field L'' := hL''f
  letI : NumberField L'' := hL''n
  letI : Algebra L L'' := hAlgL
  letI : Algebra L' L'' := hAlgL'
  letI : IsScalarTower L L' L'' := hST
  letI : FiniteDimensional L L'' := hfdL
  letI : FiniteDimensional L' L'' := hfdL'
  letI : IsGalois L L'' := hgalL
  letI : IsGalois L' L'' := hgalL'
  letI : Field L₁ := hL₁f
  letI : NumberField L₁ := hL₁n
  letI : Algebra L L₁ := hAlg₁
  letI : FiniteDimensional L L₁ := hfd₁
  letI : IsGalois L L₁ := hgal₁
  letI : Algebra L₁ L'' := hAlg₁''
  letI : IsScalarTower L L₁ L'' := hST₁
  letI : FiniteDimensional L₁ L'' := hfd₁''
  letI : IsGalois L₁ L'' := hgal₁''
  have hq''' : q''.asIdeal.LiesOver q.asIdeal :=
    Ideal.LiesOver.trans q''.asIdeal q'.asIdeal q.asIdeal
  have hf₁' : q₁.asIdeal.inertiaDeg (NumberField.RingOfIntegers L) = e0 * f0 := by
    rw [hf₁, hf0]
  -- algebra structures on the completions
  letI : Algebra (q.adicCompletion L) (q''.adicCompletion L'') :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q q'' hq''')
  letI : Algebra (q.adicCompletion L) (q₁.adicCompletion L₁) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q q₁ hq₁lies)
  letI : Algebra (q'.adicCompletion L') (q''.adicCompletion L'') :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q' q'' hq''lies)
  letI : Algebra (q₁.adicCompletion L₁) (q''.adicCompletion L'') :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₁ q'' hq₁lies'')
  -- the embeddings of the two subfields
  have hφcomp : (Commons.RingTheory.Henselian.adicCompletionMap q' q'' hq''lies).comp
      (Commons.RingTheory.Henselian.adicCompletionMap q q' hq) =
      Commons.RingTheory.Henselian.adicCompletionMap q q'' hq''' :=
    Commons.NumberTheory.NumberField.Completion.adicCompletionMap_comp q q' q'' hq hq''lies hq'''
  have hψcomp : (Commons.RingTheory.Henselian.adicCompletionMap q₁ q'' hq₁lies'').comp
      (Commons.RingTheory.Henselian.adicCompletionMap q q₁ hq₁lies) =
      Commons.RingTheory.Henselian.adicCompletionMap q q'' hq''' :=
    Commons.NumberTheory.NumberField.Completion.adicCompletionMap_comp q q₁ q'' hq₁lies hq₁lies'' hq'''
  let φ : (q'.adicCompletion L') →ₐ[q.adicCompletion L] (q''.adicCompletion L'') :=
    { toRingHom := Commons.RingTheory.Henselian.adicCompletionMap q' q'' hq''lies
      commutes' := fun x => by
        rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
        exact congrFun (congrArg DFunLike.coe hφcomp) x }
  let ψ : (q₁.adicCompletion L₁) →ₐ[q.adicCompletion L] (q''.adicCompletion L'') :=
    { toRingHom := Commons.RingTheory.Henselian.adicCompletionMap q₁ q'' hq₁lies''
      commutes' := fun x => by
        rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
        exact congrFun (congrArg DFunLike.coe hψcomp) x }
  have hφinj : Function.Injective φ := by
    have h := Commons.NumberTheory.NumberField.Completion.adicCompletionMap_injective q' q'' hq''lies
    intro a b hab
    exact h hab
  have hψinj : Function.Injective ψ := by
    have h := Commons.NumberTheory.NumberField.Completion.adicCompletionMap_injective q₁ q'' hq₁lies''
    intro a b hab
    exact h hab
  -- Galois / finiteness instances on the completions
  haveI hgalE : IsGalois (q.adicCompletion L) (q'.adicCompletion L') :=
    isGalois_adicCompletion q q' hq
  haveI hfdE : FiniteDimensional (q.adicCompletion L) (q'.adicCompletion L') :=
    module_finite_adicCompletion q q' hq
  haveI hgalM : IsGalois (q.adicCompletion L) (q''.adicCompletion L'') :=
    isGalois_adicCompletion q q'' hq'''
  haveI hfdM : FiniteDimensional (q.adicCompletion L) (q''.adicCompletion L'') :=
    module_finite_adicCompletion q q'' hq'''
  haveI hgalFn : IsGalois (q.adicCompletion L) (q₁.adicCompletion L₁) :=
    isGalois_adicCompletion q q₁ hq₁lies
  haveI hfdFn : FiniteDimensional (q.adicCompletion L) (q₁.adicCompletion L₁) :=
    module_finite_adicCompletion q q₁ hq₁lies
  haveI hgalRφ : IsGalois (q.adicCompletion L) ↥φ.fieldRange :=
    IsGalois.of_algEquiv (AlgEquiv.ofInjective φ hφinj)
  haveI hgalRψ : IsGalois (q.adicCompletion L) ↥ψ.fieldRange :=
    IsGalois.of_algEquiv (AlgEquiv.ofInjective ψ hψinj)
  -- the two normal subgroups
  let N : Subgroup (q''.adicCompletion L'' ≃ₐ[q.adicCompletion L] q''.adicCompletion L'') :=
    IntermediateField.fixingSubgroup φ.fieldRange
  let Δ : Subgroup (q''.adicCompletion L'' ≃ₐ[q.adicCompletion L] q''.adicCompletion L'') :=
    IntermediateField.fixingSubgroup ψ.fieldRange
  haveI hNnorm : N.Normal := by
    show (IntermediateField.fixingSubgroup φ.fieldRange).Normal
    infer_instance
  haveI hΔnorm : Δ.Normal := by
    show (IntermediateField.fixingSubgroup ψ.fieldRange).Normal
    infer_instance
  have hNfix : IntermediateField.fixedField N = φ.fieldRange := by
    show IntermediateField.fixedField (IntermediateField.fixingSubgroup φ.fieldRange) = φ.fieldRange
    exact IsGalois.fixedField_fixingSubgroup φ.fieldRange
  have hΔfix : IntermediateField.fixedField Δ = ψ.fieldRange := by
    show IntermediateField.fixedField (IntermediateField.fixingSubgroup ψ.fieldRange) = ψ.fieldRange
    exact IsGalois.fixedField_fixingSubgroup ψ.fieldRange
  -- cyclicity of the Galois group of the unramified subextension
  have hcycFn : IsCyclic (q₁.adicCompletion L₁ ≃ₐ[q.adicCompletion L] q₁.adicCompletion L₁) :=
    isCyclic_algEquiv_adicCompletion_of_ramificationIdx_eq_one q q₁ hq₁lies he₁
  haveI hcycRψ : IsCyclic (↥ψ.fieldRange ≃ₐ[q.adicCompletion L] ↥ψ.fieldRange) :=
    (AlgEquiv.autCongr (AlgEquiv.ofInjective ψ hψinj)).isCyclic.mp hcycFn
  have hfinFnRange : Module.finrank (q.adicCompletion L) ↥ψ.fieldRange =
      Module.finrank (q.adicCompletion L) (q₁.adicCompletion L₁) :=
    (AlgEquiv.ofInjective ψ hψinj).toLinearEquiv.finrank_eq.symm
  have hfinFn : Module.finrank (q.adicCompletion L) (q₁.adicCompletion L₁) = e0 * f0 := by
    have h := Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
      q q₁ hq₁lies
    rw [he₁, one_mul, hf₁'] at h
    exact h.symm
  have hΔcard : Nat.card (groupCohomology
      ((Rep.ofAlgebraAutOnUnits (q.adicCompletion L) (q''.adicCompletion L'')).quotientToInvariants Δ) 2)
      = e0 * f0 := by
    rw [NatCardP9.natCard_groupCohomology_two_quotientToInvariants_units Δ]
    rw [hΔfix]
    rw [natCard_groupCohomology_two_units_eq_card_of_cyclic_arbitrary_base (Q := q)
      (B := q.adicCompletion L) (E := ↥ψ.fieldRange)]
    rw [IsGalois.card_aut_eq_finrank]
    rw [hfinFnRange, hfinFn]
  -- ============ Hilbert 90 for the two subgroups ============
  haveI h1subΔ : Subsingleton (groupCohomology
      (Rep.res Δ.subtype (Rep.ofAlgebraAutOnUnits (q.adicCompletion L) (q''.adicCompletion L''))) 1) := by
    rw [NatCardP9.res_subtype_eq_res_subgroupEquivAlgEquiv Δ]
    exact (NatCardP9.subsingleton_groupCohomology_res_mulEquiv
      (IntermediateField.subgroupEquivAlgEquiv Δ)
      (Rep.ofAlgebraAutOnUnits ↥(IntermediateField.fixedField Δ) (q''.adicCompletion L'')) 1).mpr
      inferInstance
  haveI h1subN : Subsingleton (groupCohomology
      (Rep.res N.subtype (Rep.ofAlgebraAutOnUnits (q.adicCompletion L) (q''.adicCompletion L''))) 1) := by
    rw [NatCardP9.res_subtype_eq_res_subgroupEquivAlgEquiv N]
    exact (NatCardP9.subsingleton_groupCohomology_res_mulEquiv
      (IntermediateField.subgroupEquivAlgEquiv N)
      (Rep.ofAlgebraAutOnUnits ↥(IntermediateField.fixedField N) (q''.adicCompletion L'')) 1).mpr
      inferInstance
  let A : Rep ℤ (q''.adicCompletion L'' ≃ₐ[q.adicCompletion L] q''.adicCompletion L'') :=
    Rep.ofAlgebraAutOnUnits (q.adicCompletion L) (q''.adicCompletion L'')
  -- ============ scalar towers on the completions ============
  haveI hSTφ : IsScalarTower (q.adicCompletion L) (q'.adicCompletion L') (q''.adicCompletion L'') :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
      exact (congrFun (congrArg DFunLike.coe hφcomp) x).symm)
  haveI hSTψ : IsScalarTower (q.adicCompletion L) (q₁.adicCompletion L₁) (q''.adicCompletion L'') :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
      exact (congrFun (congrArg DFunLike.coe hψcomp) x).symm)
  haveI hSTE : IsScalarTower (q'.adicCompletion L') (q''.adicCompletion L'')
      (q''.adicCompletion L'') := inferInstance
  -- ============ `[M : E] = e0` and `[M : Fn] = e0` ============
  have hfinEM : Module.finrank (q'.adicCompletion L') (q''.adicCompletion L'') = e0 := by
    have h := Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
      q' q'' hq''lies
    rw [he'', one_mul, hf''] at h
    exact h.symm
  haveI hfreeE : Module.Free (q.adicCompletion L) (q'.adicCompletion L') :=
    Module.Free.of_divisionRing _ _
  haveI hfreeM : Module.Free (q'.adicCompletion L') (q''.adicCompletion L'') :=
    Module.Free.of_divisionRing _ _
  haveI hfreeM2 : Module.Free (q.adicCompletion L) (q''.adicCompletion L'') :=
    Module.Free.of_divisionRing _ _
  haveI hfreeFn : Module.Free (q₁.adicCompletion L₁) (q''.adicCompletion L'') :=
    Module.Free.of_divisionRing _ _
  have hfinFM : Module.finrank (q.adicCompletion L) (q''.adicCompletion L'') = e0 * f0 * e0 := by
    rw [← Module.finrank_mul_finrank (q.adicCompletion L) (q'.adicCompletion L')
      (q''.adicCompletion L''), hfin, hfinEM]
  have hfinFFn : Module.finrank (q.adicCompletion L) (q₁.adicCompletion L₁) = e0 * f0 := by
    have h := Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
      q q₁ hq₁lies
    rw [he₁, one_mul, hf₁'] at h
    exact h.symm
  have hfinFnM : Module.finrank (q₁.adicCompletion L₁) (q''.adicCompletion L'') = e0 := by
    have h := Module.finrank_mul_finrank (q.adicCompletion L) (q₁.adicCompletion L₁)
      (q''.adicCompletion L'')
    rw [hfinFFn, hfinFM] at h
    have hne : 0 < e0 * f0 := Nat.mul_pos he0pos hf0pos
    refine Nat.eq_of_mul_eq_mul_left hne ?_
    rw [h]
  -- ============ `f(q''|q₁) = 1` ============
  have hcard : Nat.card (𝓞 L'' ⧸ q''.asIdeal) = Nat.card (𝓞 L₁ ⧸ q₁.asIdeal) := by
    have h1 := Commons.NumberTheory.NumberField.natCard_residue_eq_pow_inertiaDeg q' q'' hq''lies
    have h2 := Commons.NumberTheory.NumberField.natCard_residue_eq_pow_inertiaDeg q q'' hq'''
    have h3 := Commons.NumberTheory.NumberField.natCard_residue_eq_pow_inertiaDeg q q₁ hq₁lies
    have h4 : Nat.card (𝓞 L'' ⧸ q''.asIdeal) = N0 ^ (f0 * e0) := by
      rw [h1, hf'', hresL', ← pow_mul]
    have h5 : Nat.card (𝓞 L₁ ⧸ q₁.asIdeal) = N0 ^ (e0 * f0) := by
      rw [h3, ← hN0, hf₁']
    rw [h4, h5, mul_comm]
  haveI hfinL₁q₁ : Finite (𝓞 L₁ ⧸ q₁.asIdeal) :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum q₁
  haveI hftL₁q₁ : Fintype (𝓞 L₁ ⧸ q₁.asIdeal) := Fintype.ofFinite _
  haveI hfinL''q'' : Finite (𝓞 L'' ⧸ q''.asIdeal) :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum q''
  haveI hftL''q'' : Fintype (𝓞 L'' ⧸ q''.asIdeal) := Fintype.ofFinite _
  have hfq''q₁ : q''.asIdeal.inertiaDeg (𝓞 L₁) = 1 := by
    haveI hlies : q''.asIdeal.LiesOver q₁.asIdeal := hq₁lies''
    haveI : q₁.asIdeal.IsMaximal := inferInstance
    haveI : q''.asIdeal.IsMaximal := inferInstance
    haveI hfieldL₁ : Field (𝓞 L₁ ⧸ q₁.asIdeal) := Ideal.Quotient.field q₁.asIdeal
    haveI hfieldL'' : Field (𝓞 L'' ⧸ q''.asIdeal) := Ideal.Quotient.field q''.asIdeal
    have hdeg : q''.asIdeal.inertiaDeg (𝓞 L₁) =
        Module.finrank (𝓞 L₁ ⧸ q₁.asIdeal) (𝓞 L'' ⧸ q''.asIdeal) :=
      Ideal.inertiaDeg_eq_of_isMaximal q₁.asIdeal q''.asIdeal
    have hcard2 : Nat.card (𝓞 L'' ⧸ q''.asIdeal) =
        Nat.card (𝓞 L₁ ⧸ q₁.asIdeal) ^ q''.asIdeal.inertiaDeg (𝓞 L₁) :=
      Commons.NumberTheory.NumberField.natCard_residue_eq_pow_inertiaDeg q₁ q'' hq₁lies''
    have hbase : 2 ≤ Nat.card (𝓞 L₁ ⧸ q₁.asIdeal) := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    have hmain : Nat.card (𝓞 L₁ ⧸ q₁.asIdeal) ^ q''.asIdeal.inertiaDeg (𝓞 L₁) =
        Nat.card (𝓞 L₁ ⧸ q₁.asIdeal) ^ 1 := by
      rw [← hcard2, hcard, pow_one]
    exact Nat.pow_right_injective hbase hmain
  -- ============ `e(q''|q₁) = e0` ============
  have herq''q₁ : q''.asIdeal.ramificationIdx (𝓞 L₁) = e0 := by
    have h := Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
      q₁ q'' hq₁lies''
    rw [hfq''q₁, mul_one] at h
    exact h.trans hfinFnM
  -- ============ the valuation maps ============
  have hvalFnEv : ∀ (σ : q''.adicCompletion L'' ≃ₐ[q.adicCompletion L] q''.adicCompletion L'')
      (u : (q''.adicCompletion L'')ˣ),
      unitsValLog (q''.adicCompletion L'') (σ • u) = unitsValLog (q''.adicCompletion L'') u :=
    unitsValLog_smul q q'' hq'''
  let valHom : Additive (q''.adicCompletion L'')ˣ →+ ℤ :=
  { toFun := fun x => Multiplicative.toAdd
      (unitsValLog (q''.adicCompletion L'') (Additive.toMul x))
    map_zero' := by
      show Multiplicative.toAdd (unitsValLog _ (Additive.toMul (0 : Additive (q''.adicCompletion L'')ˣ))) = 0
      rw [show Additive.toMul (0 : Additive (q''.adicCompletion L'')ˣ) = 1 from rfl, map_one]
      rfl
    map_add' := fun x y => by
      show Multiplicative.toAdd (unitsValLog _ (Additive.toMul (x + y)))
        = Multiplicative.toAdd (unitsValLog _ (Additive.toMul x))
          + Multiplicative.toAdd (unitsValLog _ (Additive.toMul y))
      rw [show Additive.toMul (x + y) = Additive.toMul x * Additive.toMul y from rfl, map_mul]
      rfl }
  let valLin : Additive (q''.adicCompletion L'')ˣ →ₗ[ℤ] ℤ := valHom.toIntLinearMap
  have hvalLin_nat : ∀ (g : N) (x : Additive (q''.adicCompletion L'')ˣ),
      valLin (Additive.ofMul ((N.subtype g) • (Additive.toMul (α := (q''.adicCompletion L'')ˣ) x)))
        = valLin x := by
    intro g x
    change Multiplicative.toAdd (unitsValLog (q''.adicCompletion L'')
        (Additive.toMul (α := (q''.adicCompletion L'')ˣ)
          (Additive.ofMul (α := (q''.adicCompletion L'')ˣ)
            ((N.subtype g) • (Additive.toMul (α := (q''.adicCompletion L'')ˣ) x)))))
      = Multiplicative.toAdd (unitsValLog (q''.adicCompletion L'')
          (Additive.toMul (α := (q''.adicCompletion L'')ˣ) x))
    rw [toMul_ofMul, hvalFnEv (N.subtype g)
      (Additive.toMul (α := (q''.adicCompletion L'')ˣ) x)]
  let ord₂ : Rep.res (MonoidHom.id N) (Rep.res N.subtype A) ⟶ Rep.trivial ℤ N ℤ :=
    Rep.ofHom ⟨valLin, fun g => by
      apply LinearMap.ext
      intro x
      set y : Additive (q''.adicCompletion L'')ˣ := x with hy
      have hρ : A.ρ (N.subtype g) y
          = Additive.ofMul (α := (q''.adicCompletion L'')ˣ)
              ((N.subtype g) • (Additive.toMul (α := (q''.adicCompletion L'')ˣ) y)) :=
        Rep.ofMulDistribMulAction_ρ_apply_apply (N.subtype g) y
      show valLin (A.ρ (N.subtype g) y) = valLin y
      rw [hρ]
      exact hvalLin_nat g y⟩
  have hord₂surj : Function.Surjective ord₂.hom := by
    intro z
    obtain ⟨w, hw⟩ := unitsValLog_adicCompletion_surjective L'' q'' z
    refine ⟨Additive.ofMul w, ?_⟩
    show valHom (Additive.ofMul w) = z
    show Multiplicative.toAdd (unitsValLog _ (Additive.toMul (Additive.ofMul w))) = z
    rw [toMul_ofMul]
    exact congrArg Multiplicative.toAdd hw
  -- ============ the inclusion of the invariants `(M^Δ)ˣ ↪ Mˣ` ============
  let φq := Rep.ofHom (A.ρ.quotientToInvariants_lift Δ)
  let ι : Rep.res ((QuotientGroup.mk' Δ).comp N.subtype) (A.quotientToInvariants Δ)
      ⟶ Rep.res N.subtype A :=
    (Rep.resFunctor N.subtype).map φq
  -- ============ hfac ============
  have hφq_eq : φq = Rep.ofHom (A.ρ.quotientToInvariants_lift Δ) := rfl
  have hfac : CategoryTheory.CategoryStruct.comp ((groupCohomology.infNatTrans ℤ Δ 2).app A)
      ((groupCohomology.resNatTrans ℤ (G := N)
        (H := q''.adicCompletion L'' ≃ₐ[q.adicCompletion L] q''.adicCompletion L'') N.subtype 2).app A)
      = groupCohomology.map ((QuotientGroup.mk' Δ).comp N.subtype) ι 2 := by
    have hinf : (groupCohomology.infNatTrans ℤ Δ 2).app A
        = groupCohomology.map (QuotientGroup.mk' Δ) φq 2 := by
      rw [hφq_eq]
      exact infNatTrans_app_apply Δ 2 A
    have hres : (groupCohomology.resNatTrans ℤ (G := N)
        (H := q''.adicCompletion L'' ≃ₐ[q.adicCompletion L] q''.adicCompletion L'') N.subtype 2).app A
        = groupCohomology.map N.subtype (𝟙 (Rep.res N.subtype A)) 2 := resNatTrans_app_apply N 2 A
    rw [hinf, hres, show ι = Rep.resMap N.subtype φq from rfl]
    have h := groupCohomology.map_comp (A := A.quotientToInvariants Δ) (B := A)
      (C := Rep.res N.subtype A) (f := QuotientGroup.mk' Δ) (g := N.subtype)
      φq (𝟙 (Rep.res N.subtype A)) 2
    rw [Category.comp_id] at h
    exact h.symm
  -- ============ the crux `Res_N ∘ Inf_Δ = 0` ============
  have hcrux : CategoryTheory.CategoryStruct.comp ((groupCohomology.infNatTrans ℤ Δ 2).app A)
      ((groupCohomology.resNatTrans ℤ (G := N)
        (H := q''.adicCompletion L'' ≃ₐ[q.adicCompletion L] q''.adicCompletion L'') N.subtype 2).app A)
      = 0 := by
    have hE0ne : (e0 : ℤ) ≠ 0 := by exact_mod_cast he0pos.ne'
    haveI hfdMc : FiniteDimensional (q'.adicCompletion L') (q''.adicCompletion L'') :=
      module_finite_adicCompletion q' q'' hq''lies
    haveI hgalMc : IsGalois (q'.adicCompletion L') (q''.adicCompletion L'') :=
      isGalois_adicCompletion q' q'' hq''lies
    -- (1) the identification of the two Galois groups of `M` over the two images of `E`
    have hφrange : ∀ x : q'.adicCompletion L', (φ x : q''.adicCompletion L'') ∈ φ.fieldRange :=
      fun x => ⟨x, rfl⟩
    let eN : N ≃* (q''.adicCompletion L'' ≃ₐ[q'.adicCompletion L'] q''.adicCompletion L'') :=
      { toFun := fun g => AlgEquiv.ofRingEquiv (f := (N.subtype g).toRingEquiv) (fun x => by
          show (N.subtype g) (algebraMap (q'.adicCompletion L') (q''.adicCompletion L'') x)
            = algebraMap (q'.adicCompletion L') (q''.adicCompletion L'') x
          exact (IntermediateField.mem_fixingSubgroup_iff φ.fieldRange (N.subtype g)).mp g.2
            (φ x) (hφrange x))
        invFun := fun σ => ⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (fun x => by
          rw [IsScalarTower.algebraMap_apply (q.adicCompletion L) (q'.adicCompletion L')
            (q''.adicCompletion L'')]
          exact σ.commutes (algebraMap (q.adicCompletion L) (q'.adicCompletion L') x)), by
          rw [IntermediateField.mem_fixingSubgroup_iff]
          intro y hy
          obtain ⟨z, rfl⟩ := hy
          exact σ.commutes z⟩
        left_inv := fun g => Subtype.ext (AlgEquiv.ext (fun x => rfl))
        right_inv := fun σ => AlgEquiv.ext (fun x => rfl)
        map_mul' := fun a b => AlgEquiv.ext (fun x => rfl) }
    have eN_apply_coe : ∀ g : N, ⇑(eN g) = ⇑(N.subtype g) := fun g => rfl
    -- (0) `Nat.card N = e0`
    have hNcard_eq : Nat.card N = e0 := by
      rw [Nat.card_congr eN.toEquiv, IsGalois.card_aut_eq_finrank]
      exact hfinEM
    -- (2) the `Oˣ`-representation and the inclusion `Oˣ ↪ Mˣ`
    let Y : Rep ℤ N := Rep.res eN.toMonoidHom
      (Rep.of (geIntegersUnitsRep (K := L') (L := L'') q' q'' hq''lies))
    let iLin : Y.V →ₗ[ℤ] (Rep.res (MonoidHom.id N) (Rep.res N.subtype A)).V :=
      (Units.map (algebraMap (q''.adicCompletionIntegers L'')
        (q''.adicCompletion L'')).toMonoidHom).toAdditive.toIntLinearMap
    have i_equiv : ∀ g : N, iLin ∘ₗ Y.ρ g
        = (Rep.res (MonoidHom.id N) (Rep.res N.subtype A)).ρ g ∘ₗ iLin := by
      intro g
      apply LinearMap.ext
      intro u
      apply Additive.toMul.injective
      apply Units.ext
      have hL : ((Additive.toMul (iLin (Y.ρ g u)) : (q''.adicCompletion L'')ˣ) :
            q''.adicCompletion L'')
          = (eN g) ((Additive.toMul u : (q''.adicCompletionIntegers L'')ˣ) :
              q''.adicCompletion L'') :=
        geIntegersUnitsRep_apply_coe (K := L') (L := L'') q' q'' hq''lies (eN g)
          (Additive.toMul u)
      have hR : ((Additive.toMul ((Rep.res (MonoidHom.id N) (Rep.res N.subtype A)).ρ g
            (iLin u)) : (q''.adicCompletion L'')ˣ) : q''.adicCompletion L'')
          = (N.subtype g) ((Additive.toMul u : (q''.adicCompletionIntegers L'')ˣ) :
              q''.adicCompletion L'') := by
        simp only [Rep.ofMulDistribMulAction_ρ_apply_apply, toMul_ofMul, Units.coe_smul,
          Units.coe_map]
        rfl
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      calc ((Additive.toMul (iLin (Y.ρ g u)) : (q''.adicCompletion L'')ˣ) :
              q''.adicCompletion L'')
          = (eN g) ((Additive.toMul u : (q''.adicCompletionIntegers L'')ˣ) :
              q''.adicCompletion L'') := hL
        _ = (N.subtype g) ((Additive.toMul u : (q''.adicCompletionIntegers L'')ˣ) :
              q''.adicCompletion L'') := by rw [eN_apply_coe]
        _ = ((Additive.toMul ((Rep.res (MonoidHom.id N) (Rep.res N.subtype A)).ρ g
              (iLin u)) : (q''.adicCompletion L'')ˣ) : q''.adicCompletion L'') := hR.symm
    let i : Y ⟶ Rep.res (MonoidHom.id N) (Rep.res N.subtype A) :=
      Rep.ofHom ⟨iLin, i_equiv⟩
    have hizer : i ≫ ord₂ = 0 := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro u
      show valLin (iLin u) = 0
      show Multiplicative.toAdd (unitsValLog (q''.adicCompletion L'')
        (Additive.toMul (iLin u))) = 0
      have hval : Valued.v (R := q''.adicCompletion L'') (Γ₀ := WithZero (Multiplicative ℤ))
          ((Additive.toMul (iLin u) : (q''.adicCompletion L'')ˣ) : q''.adicCompletion L'') = 1 := by
        rw [show ((Additive.toMul (iLin u) : (q''.adicCompletion L'')ˣ) :
            q''.adicCompletion L'') = ((Additive.toMul u : (q''.adicCompletionIntegers L'')ˣ) :
              q''.adicCompletion L'') from rfl]
        exact (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
          (v := q'') (a := ((Additive.toMul u : (q''.adicCompletionIntegers L'')ˣ) :
            q''.adicCompletionIntegers L''))).mp (Additive.toMul u).isUnit
      rw [(unitsValLog_eq_one_iff (Additive.toMul (iLin u))).mpr hval]
      rfl
    -- (3) `H²(N, Oˣ) = 0`
    have hYsub : Subsingleton (groupCohomology Y 2) :=
      (NatCardP9.subsingleton_groupCohomology_res_mulEquiv eN
        (Rep.of (geIntegersUnitsRep (K := L') (L := L'') q' q'' hq''lies)) 2).mpr
        (geSubsingleton_groupCohomology_two_integersUnits
          (K := L') (L := L'') q' q'' hq''lies he'')
    haveI hYzero : CategoryTheory.Limits.IsZero (groupCohomology Y 2) :=
      (Commons.RepresentationTheory.GroupCohomology.isZero_iff_subsingleton_moduleCat _).mpr hYsub
    -- (4) `Mono (map (id N) ord₂ 2)`
    haveI : Fintype (q''.adicCompletion L'' ≃ₐ[q.adicCompletion L] q''.adicCompletion L'') :=
      AlgEquiv.fintype (q.adicCompletion L) (q''.adicCompletion L'')
    haveI : Fintype N := Fintype.ofFinite _
    have hinj : Function.Injective (⇑(algebraMap (q''.adicCompletionIntegers L'')
        (q''.adicCompletion L'')) : (q''.adicCompletionIntegers L'') → q''.adicCompletion L'') :=
      fun p q h => Subtype.ext h
    have hmono : Mono (groupCohomology.map (MonoidHom.id N) ord₂ 2) := by
      have hS : (⟨i, ord₂, hizer⟩ : ShortComplex (Rep ℤ N)).ShortExact := by
        refine Commons.RepresentationTheory.GroupCohomology.shortExact_of_mono_epi_elementwise
          _ ?_ ?_ ?_
        · rw [Rep.mono_iff_injective]
          intro a b hab
          have hnorm : ∀ u : Additive (q''.adicCompletionIntegers L'')ˣ,
              Additive.toMul (i.hom u) = Units.map (algebraMap (q''.adicCompletionIntegers L'')
                (q''.adicCompletion L'')).toMonoidHom (Additive.toMul u) := fun u => rfl
          have hab' : Additive.toMul (i.hom a) = Additive.toMul (i.hom b) :=
            congrArg Additive.toMul hab
          rw [hnorm a, hnorm b] at hab'
          exact Additive.toMul.injective (Units.map_injective hinj hab')
        · exact (Rep.epi_iff_surjective ord₂).mpr hord₂surj
        · intro x hx
          have hx1 : unitsValLog (q''.adicCompletion L'') (Additive.toMul x) = 1 := by
            have hx' : Multiplicative.toAdd (unitsValLog (q''.adicCompletion L'')
                (Additive.toMul x)) = 0 := hx
            refine Multiplicative.toAdd.injective ?_
            rw [hx']
            rfl
          have hv : Valued.v (R := q''.adicCompletion L'') (Γ₀ := WithZero (Multiplicative ℤ))
              ((Additive.toMul x : (q''.adicCompletion L'')ˣ) : q''.adicCompletion L'') = 1 :=
            (unitsValLog_eq_one_iff _).mp hx1
          have humem : ((Additive.toMul x : (q''.adicCompletion L'')ˣ) :
              q''.adicCompletion L'') ∈ q''.adicCompletionIntegers L'' := by
            rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
            exact le_of_eq hv
          have hunit : IsUnit (⟨((Additive.toMul x : (q''.adicCompletion L'')ˣ) :
              q''.adicCompletion L''), humem⟩ : q''.adicCompletionIntegers L'') := by
            rw [IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
            exact hv
          let w : (q''.adicCompletionIntegers L'')ˣ := hunit.unit
          have hwcoe : (algebraMap (q''.adicCompletionIntegers L'') (q''.adicCompletion L''))
              (w : q''.adicCompletionIntegers L'')
              = ((Additive.toMul x : (q''.adicCompletion L'')ˣ) : q''.adicCompletion L'') := by
            have h1 : (w : q''.adicCompletionIntegers L'')
                = ⟨((Additive.toMul x : (q''.adicCompletion L'')ˣ) : q''.adicCompletion L''),
                    humem⟩ := IsUnit.unit_spec hunit
            rw [h1]
            rfl
          refine ⟨Additive.ofMul w, ?_⟩
          apply Additive.ofMul.injective
          apply Units.ext
          show ((Units.map (algebraMap (q''.adicCompletionIntegers L'')
              (q''.adicCompletion L'')).toMonoidHom w : (q''.adicCompletion L'')ˣ) :
                q''.adicCompletion L'')
            = ((Additive.toMul x : (q''.adicCompletion L'')ˣ) : q''.adicCompletion L'')
          rw [Units.coe_map]
          exact hwcoe
      have hex : ((⟨i, ord₂, hizer⟩ : ShortComplex (Rep ℤ N)).map
          (groupCohomology.functor ℤ N 2)).Exact :=
        groupCohomology.mapShortComplex₂_exact hS 2
      have hmg : Mono (((⟨i, ord₂, hizer⟩ : ShortComplex (Rep ℤ N)).map
          (groupCohomology.functor ℤ N 2)).g) := hex.mono_g (hYzero.eq_zero_of_src _)
      have hg : ((⟨i, ord₂, hizer⟩ : ShortComplex (Rep ℤ N)).map
          (groupCohomology.functor ℤ N 2)).g = groupCohomology.map (MonoidHom.id N) ord₂ 2 := by
        show (groupCohomology.functor ℤ N 2).map ord₂
          = groupCohomology.map (MonoidHom.id N) ord₂ 2
        rw [groupCohomology.functor_map]
      rwa [hg] at hmg
    -- (5) `ord₁` and `hι`
    have hdiv : ∀ x : ↥(Representation.invariants (A.ρ.comp Δ.subtype)),
        ∃ k : ℤ, (e0 : ℤ) * k = valLin (ι.hom x) := by
      intro x
      obtain ⟨y, hy⟩ := (NatCardP9.mem_invariants_iff_repr Δ x.1).mp
        (fun h => (Representation.mem_invariants
          ((Rep.ofAlgebraAutOnUnits (q.adicCompletion L) (q''.adicCompletion L'')).ρ.comp
            Δ.subtype) x.1).mp x.2 h)
      let yval : q''.adicCompletion L'' :=
        (((y : (↥(IntermediateField.fixedField Δ))ˣ) : ↥(IntermediateField.fixedField Δ)) :
          q''.adicCompletion L'')
      have hyval_ne : yval ≠ 0 := fun h => Units.ne_zero y (Subtype.ext h)
      have hyval_mem : ((yval : q''.adicCompletion L'')) ∈ ψ.fieldRange := by
        rw [show yval = ((y : (↥(IntermediateField.fixedField Δ))ˣ) :
            ↥(IntermediateField.fixedField Δ)) from rfl]
        rw [← hΔfix]
        exact ((y : (↥(IntermediateField.fixedField Δ))ˣ) :
          ↥(IntermediateField.fixedField Δ)).2
      let yψ : (↥ψ.fieldRange)ˣ :=
        Units.mk0 ⟨yval, hyval_mem⟩ (fun h => hyval_ne (Subtype.ext_iff.mp h))
      let yK : (q₁.adicCompletion L₁)ˣ :=
        Units.mapEquiv (AlgHom.equivFieldRange ψ).symm.toMulEquiv yψ
      refine ⟨Multiplicative.toAdd (unitsValLog (q₁.adicCompletion L₁) yK), ?_⟩
      have hιx : ι.hom x = x.1 := by
        have h1 : (ι.hom).toLinearMap
            = (Submodule.subtype (Representation.invariants (A.ρ.comp Δ.subtype))) := by
          rw [show ι = Rep.resMap N.subtype φq from rfl, Rep.resMap_hom_toLinearMap]
          change (Rep.Hom.hom φq).toLinearMap
            = (Submodule.subtype (Representation.invariants (A.ρ.comp Δ.subtype)))
          rw [Rep.hom_ofHom]
        exact congr_fun (congrArg DFunLike.coe h1) x
      have htoMul : Additive.toMul (ι.hom x)
          = Units.map (algebraMap ↥(IntermediateField.fixedField Δ)
              (q''.adicCompletion L'')).toMonoidHom y := by
        rw [hιx, hy]
        rfl
      have hbase : (algebraMap (q₁.adicCompletion L₁) (q''.adicCompletion L''))
            (yK : q₁.adicCompletion L₁)
          = ((y : ↥(IntermediateField.fixedField Δ)) : q''.adicCompletion L'') := by
        rw [RingHom.algebraMap_toAlgebra]
        change ψ (yK : q₁.adicCompletion L₁) = yval
        rw [show (yK : q₁.adicCompletion L₁)
            = (AlgHom.equivFieldRange ψ).symm (yψ : (↥ψ.fieldRange)ˣ) from
          Units.coe_mapEquiv (AlgHom.equivFieldRange ψ).symm.toMulEquiv yψ]
        rw [← AlgHom.equivFieldRange_apply_coe ψ
            ((AlgHom.equivFieldRange ψ).symm (yψ : (↥ψ.fieldRange)ˣ)),
          AlgEquiv.apply_symm_apply]
        rfl
      have hyK : Units.map (algebraMap (q₁.adicCompletion L₁)
            (q''.adicCompletion L'')).toMonoidHom yK
          = Units.map (algebraMap ↥(IntermediateField.fixedField Δ)
              (q''.adicCompletion L'')).toMonoidHom y := by
        apply Units.ext
        exact hbase
      have key1 : Multiplicative.toAdd ((unitsValLog (q₁.adicCompletion L₁) yK) ^ e0)
          = (e0 : ℤ) * Multiplicative.toAdd (unitsValLog (q₁.adicCompletion L₁) yK) := by
        rw [toAdd_pow]
        simp [nsmul_eq_mul]
      have key2 : Multiplicative.toAdd (unitsValLog (q''.adicCompletion L'')
            (Units.map (algebraMap (q₁.adicCompletion L₁)
              (q''.adicCompletion L'')).toMonoidHom yK))
          = Multiplicative.toAdd ((unitsValLog (q₁.adicCompletion L₁) yK) ^ e0) := by
        rw [unitsValLog_algebraMap (K := L₁) (L := L'') q₁ q'' hq₁lies'' yK, herq''q₁]
      have key3 : Multiplicative.toAdd (unitsValLog (q''.adicCompletion L'')
            (Units.map (algebraMap ↥(IntermediateField.fixedField Δ)
              (q''.adicCompletion L'')).toMonoidHom y))
          = Multiplicative.toAdd (unitsValLog (q''.adicCompletion L'')
            (Units.map (algebraMap (q₁.adicCompletion L₁)
              (q''.adicCompletion L'')).toMonoidHom yK)) := by
        rw [hyK]
      have key4 : Multiplicative.toAdd (unitsValLog (q''.adicCompletion L'')
            (Additive.toMul (ι.hom x)))
          = Multiplicative.toAdd (unitsValLog (q''.adicCompletion L'')
            (Units.map (algebraMap ↥(IntermediateField.fixedField Δ)
              (q''.adicCompletion L'')).toMonoidHom y)) := by
        exact congrArg (fun z => Multiplicative.toAdd (unitsValLog (q''.adicCompletion L'') z))
          htoMul
      exact key1.symm.trans (key2.symm.trans (key3.symm.trans key4.symm))
    let ord₁Lin : ↥(Representation.invariants (A.ρ.comp Δ.subtype)) →ₗ[ℤ] ℤ :=
      { toFun := fun x => valLin (ι.hom x) / (e0 : ℤ)
        map_add' := fun x y => by
          obtain ⟨kx, hx⟩ := hdiv x
          obtain ⟨ky, hy⟩ := hdiv y
          obtain ⟨kxy, hxy⟩ := hdiv (x + y)
          rw [show valLin (ι.hom x) / (e0 : ℤ) = kx by
                rw [← hx, show (e0 : ℤ) * kx = kx * (e0 : ℤ) by ring, Int.mul_ediv_cancel kx hE0ne],
            show valLin (ι.hom y) / (e0 : ℤ) = ky by
                rw [← hy, show (e0 : ℤ) * ky = ky * (e0 : ℤ) by ring, Int.mul_ediv_cancel ky hE0ne],
            show valLin (ι.hom (x + y)) / (e0 : ℤ) = kxy by
                rw [← hxy, show (e0 : ℤ) * kxy = kxy * (e0 : ℤ) by ring,
                  Int.mul_ediv_cancel kxy hE0ne]]
          have hk : kxy = kx + ky := by
            refine mul_left_cancel₀ hE0ne ?_
            calc (e0 : ℤ) * kxy = valLin (ι.hom (x + y)) := hxy
              _ = valLin (ι.hom x) + valLin (ι.hom y) :=
                (congrArg valLin (map_add ι.hom x y)).trans (map_add valLin _ _)
              _ = (e0 : ℤ) * kx + (e0 : ℤ) * ky := by rw [← hx, ← hy]
              _ = (e0 : ℤ) * (kx + ky) := by ring
          rw [hk]
        map_smul' := fun k x => by
          obtain ⟨kx, hx⟩ := hdiv x
          obtain ⟨kkx, hkx⟩ := hdiv (k • x)
          rw [show valLin (ι.hom x) / (e0 : ℤ) = kx by
                rw [← hx, show (e0 : ℤ) * kx = kx * (e0 : ℤ) by ring, Int.mul_ediv_cancel kx hE0ne],
            show valLin (ι.hom (k • x)) / (e0 : ℤ) = kkx by
                rw [← hkx, show (e0 : ℤ) * kkx = kkx * (e0 : ℤ) by ring,
                  Int.mul_ediv_cancel kkx hE0ne]]
          have hk : kkx = k * kx := by
            refine mul_left_cancel₀ hE0ne ?_
            have hsm : valLin (ι.hom (k • x)) = k * valLin (ι.hom x) := by
              rw [← smul_eq_mul]
              exact (congrArg valLin (map_smul ι.hom k x)).trans (map_smul valLin k (ι.hom x))
            rw [hkx, hsm, ← hx]
            ring
          rw [hk]
          rfl }
    let ord₁ : Rep.res ((QuotientGroup.mk' Δ).comp N.subtype) (A.quotientToInvariants Δ)
        ⟶ Rep.trivial ℤ N ℤ :=
      Rep.ofHom ⟨ord₁Lin, fun g => by
        apply LinearMap.ext
        intro x
        show valLin (ι.hom ((Rep.res ((QuotientGroup.mk' Δ).comp N.subtype)
            (A.quotientToInvariants Δ)).ρ g x)) / (e0 : ℤ) = valLin (ι.hom x) / (e0 : ℤ)
        congr 1
        rw [Rep.hom_comm_apply ι g x]
        show valLin (A.ρ (N.subtype g) (ι.hom x)) = valLin (ι.hom x)
        exact hvalLin_nat g (ι.hom x)⟩
    have hι : ι ≫ ord₂ = e0 • ord₁ := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      show valLin (ι.hom x) = (e0 : ℤ) * (valLin (ι.hom x) / (e0 : ℤ))
      obtain ⟨k, hk⟩ := hdiv x
      have h2 : (e0 : ℤ) * (valLin (ι.hom x) / (e0 : ℤ)) = (e0 : ℤ) * k := by
        rw [show valLin (ι.hom x) / (e0 : ℤ) = k by
          rw [← hk, show (e0 : ℤ) * k = k * (e0 : ℤ) by ring, Int.mul_ediv_cancel k hE0ne]]
      rw [h2, ← hk]
    exact Commons.RepresentationTheory.GroupCohomology.res_comp_inf_eq_zero_of_ord
      Δ N A ord₁ ord₂ ι hmono e0 hι (by rw [hNcard_eq]) hfac

  -- ============ the cardinality chase ============
  have hNcard : Nat.card (groupCohomology (A.quotientToInvariants N) 2) =
      Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits (q.adicCompletion L) (q'.adicCompletion L')) 2) := by
    rw [NatCardP9.natCard_groupCohomology_two_quotientToInvariants_units N]
    rw [hNfix]
    exact (natCard_groupCohomology_two_units_topAlgEquiv
      (AlgEquiv.ofInjective φ hφinj)).symm
  haveI hfinNE : Finite (groupCohomology
      (Rep.ofAlgebraAutOnUnits (q.adicCompletion L) (q'.adicCompletion L')) 2) :=
    finite_groupCohomology_two_units_adicCompletion_of_isGalois q q' hq
  haveI hfinN : Finite (groupCohomology (A.quotientToInvariants N) 2) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hNcard]
    rw [Nat.card_ne_zero]
    exact ⟨⟨0⟩, inferInstance⟩
  haveI : Fintype N := Fintype.ofFinite _
  have hle : Nat.card (groupCohomology (A.quotientToInvariants Δ) 2) ≤
      Nat.card (groupCohomology (A.quotientToInvariants N) 2) :=
    Commons.RepresentationTheory.GroupCohomology.natCard_quotientToInvariants_le_of_twist
      Δ N A h1subN h1subΔ hcrux
  rw [hfin, ← hNcard]
  exact hΔcard.symm.trans_le hle


end Commons.NumberTheory.NumberField.Completion
