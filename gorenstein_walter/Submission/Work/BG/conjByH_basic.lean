import Mathlib
import Submission.Work.BG.Defs
import Submission.Work.BG.Lambda
import Submission.Work.BG.H0Conj
import Submission.Work.BG.CharBridge

/-!
# BG: the `s`-action on `CF(H₀)` — basic properties

This file proves the three structural interface statements of
`Submission/Work/BG/H0Conj.lean`:

* `ConjByHTransportProp` — agreement of `Work.BG.conjByH` with the Feit–Thompson
  library action `ClassFunction.conjBy` on `CF(H₀.subgroupOf H)`;
* `ConjByHMulProp` — `(ν^{s₁})^{s₂} = ν^{s₁ s₂}` in the library's order;
* `InduceConjByHProp` — `(ν^s)^G = ν^G`, i.e. induction to `G` does not see `s`.

The mathematical content is elementary: `s ∈ H` normalises `H₀` (because `H₀ ⊴ H`),
so `ν ↦ ν^s` is the transport of `ν` along the conjugation automorphism of `H₀`,
which leaves both the induced class function unaltered.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

variable {G : Type} [Group G] [Finite G]

/-! ### Conjugation by `s ∈ H` preserves `H₀` -/

/-- `s h s⁻¹ ∈ H₀` for `h ∈ H₀`, `s ∈ H`. -/
theorem H0_conj_mem (P : Hyp12 G) {h : G} (hh : h ∈ P.H0) (s : ↥P.H) :
    (s : G) * h * (s : G)⁻¹ ∈ P.H0 :=
  P.H0_normal.conj_mem (⟨h, P.H0_le_H hh⟩ : ↥P.H) hh s

/-- `s⁻¹ h s ∈ H₀` for `h ∈ H₀`, `s ∈ H`. -/
theorem H0_conj_mem' (P : Hyp12 G) {h : G} (hh : h ∈ P.H0) (s : ↥P.H) :
    (s : G)⁻¹ * h * (s : G) ∈ P.H0 :=
  P.H0_normal.conj_mem' (⟨h, P.H0_le_H hh⟩ : ↥P.H) hh s

/-- `s ∈ H` normalises `H₀`: `s⁻¹ y s ∈ H₀ ↔ y ∈ H₀`. -/
theorem mem_H0_conj_inv_iff (P : Hyp12 G) (s : ↥P.H) (y : G) :
    (s : G)⁻¹ * y * (s : G) ∈ P.H0 ↔ y ∈ P.H0 := by
  constructor
  · intro h
    have h' := H0_conj_mem P h s
    have heq : (s : G) * ((s : G)⁻¹ * y * (s : G)) * (s : G)⁻¹ = y := by group
    rwa [heq] at h'
  · intro h
    exact H0_conj_mem' P h s

/-- `s ∈ H` normalises `H₀`: `s y s⁻¹ ∈ H₀ ↔ y ∈ H₀`. -/
theorem mem_H0_conj_iff (P : Hyp12 G) (s : ↥P.H) (y : G) :
    (s : G) * y * (s : G)⁻¹ ∈ P.H0 ↔ y ∈ P.H0 := by
  constructor
  · intro h
    have h' := H0_conj_mem' P h s
    have heq : (s : G)⁻¹ * ((s : G) * y * (s : G)⁻¹) * (s : G) = y := by group
    rwa [heq] at h'
  · intro h
    exact H0_conj_mem P h s

/-! ### The conjugation automorphism is multiplicative -/

/-- `conjMulEquiv` is a left action: `conj_{s₁ s₂} = conj_{s₁} ∘ conj_{s₂}`. -/
theorem conjMulEquiv_mul (P : Hyp12 G) (s₁ s₂ : ↥P.H) (h : ↥P.H0) :
    conjMulEquiv P (s₁ * s₂) h = conjMulEquiv P s₁ (conjMulEquiv P s₂ h) := by
  apply Subtype.ext
  rw [conjMulEquiv_apply, conjMulEquiv_apply, conjMulEquiv_apply]
  simp only [Subgroup.coe_mul]
  group

/-! ### The three interface statements -/

/-- `ConjByHTransportProp`: `conjByH` agrees with the library action `conjBy` on
`CF(H₀.subgroupOf H)` along `H0inEquiv`. -/
theorem conjByH_transport (P : Hyp12 G) (s : ↥P.H) (ν : ClassFunction ↥P.H0 ℂ) :
    ClassFunction.compHom (H0inEquiv P).toMonoidHom (conjByH P s ν) =
      ClassFunction.conjBy (G := ↥P.H) (H := H0in P) s
        (ClassFunction.compHom (H0inEquiv P).toMonoidHom ν) := by
  ext x
  rw [ClassFunction.compHom_apply, conjByH_apply, ClassFunction.conjBy_apply,
    ClassFunction.compHom_apply]
  congr 1

/-- `ConjByHMulProp`: `(ν^{s₁})^{s₂} = ν^{s₁ s₂}`, in the library's order. -/
theorem conjByH_mul (P : Hyp12 G) (s₁ s₂ : ↥P.H) (ν : ClassFunction ↥P.H0 ℂ) :
    conjByH P (s₁ * s₂) ν = conjByH P s₂ (conjByH P s₁ ν) := by
  ext h
  rw [conjByH_apply, conjByH_apply, conjByH_apply, conjMulEquiv_mul]

/-- The summand identity behind `InduceConjByHProp`: the `x`-summand for `ν` matches the
`x * s`-summand for `ν^s`. -/
theorem induceTerm_conjByH (P : Hyp12 G) (s : ↥P.H) (ν : ClassFunction ↥P.H0 ℂ) (x g : G) :
    ClassFunction.induceTerm P.H0 (conjByH P s ν) (x * (s : G)) g =
      ClassFunction.induceTerm P.H0 ν x g := by
  classical
  have hcond : (x * (s : G))⁻¹ * g * (x * (s : G)) ∈ P.H0 ↔ x⁻¹ * g * x ∈ P.H0 := by
    have heq : (x * (s : G))⁻¹ * g * (x * (s : G)) =
        (s : G)⁻¹ * (x⁻¹ * g * x) * (s : G) := by
      group
    rw [heq]
    exact mem_H0_conj_inv_iff P s (x⁻¹ * g * x)
  by_cases hx : x⁻¹ * g * x ∈ P.H0
  · have hxs : (x * (s : G))⁻¹ * g * (x * (s : G)) ∈ P.H0 := hcond.mpr hx
    rw [ClassFunction.induceTerm_of_mem _ hxs, ClassFunction.induceTerm_of_mem _ hx,
      conjByH_apply]
    have hkey : (conjMulEquiv P s
        ⟨(x * (s : G))⁻¹ * g * (x * (s : G)), hxs⟩ : ↥P.H0) = ⟨x⁻¹ * g * x, hx⟩ := by
      apply Subtype.ext
      rw [conjMulEquiv_apply]
      group
    rw [hkey]
  · have hxs : (x * (s : G))⁻¹ * g * (x * (s : G)) ∉ P.H0 := fun h => hx (hcond.mp h)
    rw [ClassFunction.induceTerm_of_not_mem _ hxs, ClassFunction.induceTerm_of_not_mem _ hx]

/-- `InduceConjByHProp`: induction to `G` does not see `s`, `(ν^s)^G = ν^G`. -/
theorem induce_conjByH (P : Hyp12 G) [Fintype G] (s : ↥P.H)
    [Invertible (Nat.card P.H0 : ℂ)] (ν : ClassFunction ↥P.H0 ℂ) :
    ClassFunction.induce P.H0 (conjByH P s ν) = ClassFunction.induce P.H0 ν := by
  ext g
  have hsum : (∑ x : G, ClassFunction.induceTerm P.H0 ν x g) =
      ∑ x : G, ClassFunction.induceTerm P.H0 (conjByH P s ν) x g :=
    Fintype.sum_equiv (Equiv.mulRight (s : G)) _ _
      (fun x => (induceTerm_conjByH P s ν x g).symm)
  rw [ClassFunction.induce_apply, ClassFunction.induce_apply, hsum]

theorem conjByH_basic {G : Type} [Group G] [Finite G] [Fintype G] :
    Work.BG.ConjByHTransportProp (G := G) ∧ Work.BG.ConjByHMulProp (G := G) ∧
      Work.BG.InduceConjByHProp (G := G) := by
  refine ⟨?_, ?_, ?_⟩
  · intro P s ν
    exact conjByH_transport P s ν
  · intro P s₁ s₂ ν
    exact conjByH_mul P s₁ s₂ ν
  · intro P s _ ν
    exact induce_conjByH P s ν

end Work.BG
