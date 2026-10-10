import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring
import Submission.Work.SSGRoute.InertiaDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Closedness of `I_A ⊓ Gal(Ω/K)`

Let `k` be a number field, `Ω` an algebraic closure of `k` and `A` a place of `Ω`.
The decomposition group `D_A` of `A` is closed in the Krull topology on `G_k = Ω ≃ₐ[k] Ω`
(`Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring`), and the inertia subgroup `I_A`
is closed as well: given `σ ∉ I_A`, either `σ ∉ D_A`, or some `x ∈ A` witnesses
`¬ (A.valuation (σ x - x) < 1)`, in which case the open coset `σ · Gal(Ω/k⟮x⟯)` is contained in the
complement of `I_A`.

Combined with `IntermediateField.fixingSubgroup_isClosed` for the fixing subgroup of the finite
extension `K/k`, this gives that `I_A ⊓ Gal(Ω/K)` is an intersection of two closed subgroups, hence
closed.
-/

open scoped Pointwise Topology
open Filter

namespace Work.SSGRoute

variable (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω]

/-- **A place of an algebraic closure has closed decomposition group.**  Specialisation of
`Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring` to `Ω/k` with `Ω` an algebraic
closure of the number field `k` (so that `Ω/k` is Galois). -/
theorem isClosed_decomp_algClosure [NumberField k] [IsAlgClosure k Ω]
    (A : ValuationSubring Ω) :
    IsClosed (SSGRoute.decomp k A : Set (Ω ≃ₐ[k] Ω)) := by
  haveI : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  exact Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring (K := k) (K' := Ω) A

/-- **The inertia subgroup of a place of an algebraic closure is closed in the Krull topology.**

Given `σ ∉ I_A`, either `σ ∉ D_A` — and `D_A` is closed — or there is `x ∈ A` with
`¬ (A.valuation (σ x - x) < 1)`, in which case the open coset `σ · Gal(Ω/k⟮x⟯)` is contained in the
complement of `I_A`.  Hence the complement of `I_A` is open. -/
theorem isClosed_inertiaSub_algClosure [NumberField k] [IsAlgClosure k Ω]
    (A : ValuationSubring Ω) :
    IsClosed (inertiaSub k Ω A : Set (Ω ≃ₐ[k] Ω)) := by
  haveI : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro σ hσ
  by_cases hσd : σ ∈ SSGRoute.decomp k A
  · -- some `x ∈ A` witnesses that `σ` is not inertial
    have hbad : ∃ x : Ω, x ∈ A ∧ ¬ A.valuation (σ x - x) < 1 := by
      by_contra hc
      push_neg at hc
      exact hσ ⟨hσd, fun y hy => hc y hy⟩
    obtain ⟨x, hxA, hvx⟩ := hbad
    -- the open neighbourhood `σ · Gal(Ω/k⟮x⟯)` of `σ` lies in the complement
    let E : IntermediateField k Ω := IntermediateField.adjoin k ({x} : Set Ω)
    haveI hfd : FiniteDimensional k E :=
      IntermediateField.adjoin.finiteDimensional (IsGalois.integral k x)
    have hopenE : IsOpen ((E.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) :=
      IntermediateField.fixingSubgroup_isOpen E
    have hnbhd : {τ : Ω ≃ₐ[k] Ω | σ⁻¹ * τ ∈ E.fixingSubgroup} ∈ 𝓝 σ := by
      refine (hopenE.preimage (continuous_const.mul continuous_id)).mem_nhds ?_
      simp only [Pi.mul_apply, id_eq, Set.mem_preimage]
      rw [inv_mul_cancel]
      exact E.fixingSubgroup.one_mem
    refine Filter.mem_of_superset hnbhd ?_
    intro τ hτ hτI
    apply hvx
    have hmem : (σ⁻¹ * τ) ∈ E.fixingSubgroup := hτ
    have hfix : (σ⁻¹ * τ) x = x := by
      rw [IntermediateField.mem_fixingSubgroup_iff] at hmem
      exact hmem x (IntermediateField.subset_adjoin k ({x} : Set Ω) (Set.mem_singleton x))
    have hτx : τ x = σ x := by
      have h2 : σ⁻¹ (τ x) = x := hfix
      have h3 : σ (σ⁻¹ (τ x)) = σ x := congrArg σ h2
      simpa [AlgEquiv.apply_symm_apply] using h3
    have hval := hτI.2 x hxA
    rwa [hτx] at hval
  · -- `σ ∉ D_A` and `D_A` is closed
    have hcomp : IsOpen (SSGRoute.decomp k A : Set (Ω ≃ₐ[k] Ω))ᶜ :=
      (isClosed_decomp_algClosure k Ω A).isOpen_compl
    refine Filter.mem_of_superset (hcomp.mem_nhds (by simpa using hσd)) ?_
    intro τ hτ hτI
    exact hτ hτI.1

/-- **The inertia subgroup intersected with the fixing subgroup of a finite Galois extension is
closed.**  It is the intersection of the two closed subgroups `I_A` and `Gal(Ω/K)`
(`isClosed_inertiaSub_algClosure` and `IntermediateField.fixingSubgroup_isClosed`). -/
theorem isClosed_inertiaSub_kernel (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (A : ValuationSubring Ω) :
    IsClosed ((inertiaSub k Ω A ⊓ K.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) :
      Set (Ω ≃ₐ[k] Ω)) := by
  have hI : IsClosed (inertiaSub k Ω A : Set (Ω ≃ₐ[k] Ω)) :=
    isClosed_inertiaSub_algClosure k Ω A
  have hK : IsClosed (K.fixingSubgroup : Set (Ω ≃ₐ[k] Ω)) :=
    IntermediateField.fixingSubgroup_isClosed K
  simpa only [Subgroup.coe_inf] using hI.inter hK

end Work.SSGRoute
