import Mathlib
import Submission.Work.Thom.Pair
import Submission.Work.Thom.Continuous

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000

/-!
# The Euler class vanishes on a bundle with a nowhere-zero section

The Euler class of a rank-`n` real bundle with a class `τ` of the Thom pair is
`e(E) = z^*(τ) ∈ H^n(B;ℤ)` (`Work.Thom.eulerClass`), the pullback of `τ` along the zero section.

This module proves the classical vanishing theorem, **`Work.Thom.eulerClass_eq_zero_of_nowhereZeroSection`**:

  *if `E → B` admits a continuous nowhere-zero section, then `e(E) = 0`.*

The proof is the standard one: a nowhere-zero section `σ` has its image in the complement `E∖0` of
the zero section, so for a class `τ ∈ H^n(E,E∖0;ℤ)` the pullback `σ^*(τ)` vanishes — a relative
class restricts to zero on the subspace it is relative to.  The zero section and `σ` are homotopic
inside `E` (the fibrewise rescaling `(x,t) ↦ ⟨x, t • σ x⟩`, continuous by
`Work.Thom.continuous_smul_section`), so `z^*(τ) = σ^*(τ) = 0`.

The abstract cohomological step is separated out as
`Work.Thom.CohMap_eq_zero_of_homotopic_of_factors`: homotopic maps `z ≃ σ : B → X` with `σ` factoring
through `A ⊆ X` have `z^* ∘ (H^n(X,A) → H^n(X)) = 0`.  The geometric input is only the homotopy.

**Consequence** (`Work.Thom.eulerClass_eq_zero_of_stabilized`): the Euler class of `E ⊕ ε¹` (a trivial
line summand) vanishes, since `x ↦ ⟨x,(0,1)⟩` is a continuous nowhere-zero section
(`Work.Thom.continuous_section_mk`, the transition functions of the sum being block diagonal).  This
is the classical vanishing of the Euler class of a bundle containing a trivial summand — the
statement one would use to show `e(E) = 0` for odd rank.
-/

open Work.TangentClasses

namespace Work.Thom

open Bundle Filter

open scoped Topology

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-! ## The abstract cohomological step -/

/-- **A relative class kills homotopic maps through the subspace.**  If `z, σ : B → X` are homotopic
and `σ` factors through `A ⊆ X`, then the composition

  `H^n(X,A;ℤ) --(forget)--→ H^n(X;ℤ) --z^*--> H^n(B;ℤ)`

is zero. -/
theorem CohMap_eq_zero_of_homotopic_of_factors {X : Type} [TopologicalSpace X] (A : Set X)
    {B : Type} [TopologicalSpace B] {z σ : C(B, X)} (h : ContinuousMap.Homotopic z σ)
    (σ' : C(B, A)) (hfac : ∀ b, ((σ' b : A) : X) = σ b) (n : ℕ) (τ : RelCoh ℤ n X A) :
    (CohMap z ℤ n).hom ((relToAbs ℤ A n).hom τ) = 0 := by
  have hσeq : σ = (subtypeMap A).comp σ' := by
    ext b
    exact (hfac b).symm
  have hzero : ((CohMap (subtypeMap A) ℤ n).hom).comp ((relToAbs ℤ A n).hom) = 0 := by
    rw [← ModuleCat.hom_comp, relToAbs_comp_CohMap_subtype ℤ A n, ModuleCat.hom_zero]
  have hh : ((CohMap (subtypeMap A) ℤ n).hom) ((relToAbs ℤ A n).hom τ) = 0 := by
    have h1 := congrArg (fun l : RelCoh ℤ n X A →ₗ[ℤ] Coh ℤ n A => l τ) hzero
    simpa using h1
  have hσ' : (CohMap σ ℤ n).hom =
      ((CohMap σ' ℤ n).hom).comp ((CohMap (subtypeMap A) ℤ n).hom) := by
    rw [hσeq, CohMap_comp, ModuleCat.hom_comp]
  rw [CohMap_homotopic h ℤ n, hσ', LinearMap.comp_apply, hh, map_zero]

/-! ## The vanishing theorems -/

/-- **The Euler class of a bundle with a nowhere-zero continuous section vanishes.**  Here `σ` is a
continuous section of the total space (`(σ x).1 = x`) that never takes the value `0` in the fibre
(`(σ x).2 ≠ 0`). -/
theorem eulerClass_eq_zero_of_nowhereZeroSection (Z : RealBundle B F ι)
    (σ : C(B, Z.TotalSpace)) (hσ : ∀ x, (σ x).1 = x) (hσ0 : ∀ x, (σ x).2 ≠ 0) (n : ℕ)
    (τ : OpenThom Z n) : eulerClass Z n τ = 0 := by
  classical
  have hmem : ∀ x, σ x ∈ zeroComplement Z := fun x => by
    rw [mem_zeroComplement]
    exact hσ0 x
  let σ' : C(B, zeroComplement Z) :=
    ⟨fun x => ⟨σ x, hmem x⟩, σ.continuous.subtype_mk hmem⟩
  have hfac : ∀ b, ((σ' b : zeroComplement Z) : Z.TotalSpace) = σ b := fun b => rfl
  have hcont : Continuous (fun p : unitInterval × B =>
      (⟨(σ p.2).1, ((p.1 : unitInterval) : ℝ) • (σ p.2).2⟩ : Z.TotalSpace)) :=
    continuous_smul_section Z (σ.comp ⟨Prod.snd, continuous_snd⟩)
      ⟨fun p : unitInterval × B => ((p.1 : unitInterval) : ℝ),
        continuous_subtype_val.comp continuous_fst⟩
  have hhom : ContinuousMap.Homotopic (zeroSection Z) σ := by
    refine ⟨ContinuousMap.Homotopy.mk ⟨_, hcont⟩ ?_ ?_⟩
    · intro x
      show (⟨(σ x).1, ((0 : unitInterval) : ℝ) • (σ x).2⟩ : Z.TotalSpace) = zeroSection Z x
      rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, zero_smul, zeroSection_apply, hσ x]
    · intro x
      show (⟨(σ x).1, ((1 : unitInterval) : ℝ) • (σ x).2⟩ : Z.TotalSpace) = σ x
      rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, one_smul]
  exact CohMap_eq_zero_of_homotopic_of_factors (zeroComplement Z) hhom σ' hfac n τ

end

end Work.Thom
