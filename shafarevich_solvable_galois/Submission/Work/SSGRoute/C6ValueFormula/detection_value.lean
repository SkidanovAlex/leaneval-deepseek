import Mathlib
import Submission.Work.SSGRoute.Sha2Lib.coind_cocycle_value
import Submission.Work.SSGRoute.C6ValueFormula.coset_sum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node `C6`, item (3): the value of a coinduced cocycle's detection sum, term by term

This file continues `Submission.Work.SSGRoute.C6ValueFormula.coset_sum` (the coset-sum
decomposition of a `Γ`-equivariant functional on the coinduced module) and links it to the Shapiro
value rule `Work.SSGRoute.Sha2Lib.coind_cocycle_value`.

`coind_cocycle_value` computes the value of a `1`-cocycle `h` of the coinduced module at a
conjugate of the argument: if `φ d = x⁻¹ * γ * x` then

    (h γ).1 x⁻¹ = (h (φ d)).1 1 + (h x).1 x⁻¹ - A.ρ d ((h x).1 x⁻¹) .

Composing with the coset sum `ν f = Σ_x ν (δ_{1, f x})`, the individual term of the detection sum is

    `ν (δ_{1, (h γ).1 x}) = ν (δ_{1, (h (φ d)).1 1}) + ν (δ_{1, defect})`      (`h φ d = x γ x⁻¹`)

which is the form in which the Grünwald prescription is applied to the detector: the first term is
the value of the Shapiro partner `y` of `h` at the conjugate `x γ x⁻¹` of the place's decomposition
element, and the second is the `A = res_{D_w}M`-dependent defect (it vanishes when `A` carries the
trivial action, recovering formula (7.1) of
`E7cC/NOTE_C6_session17_level_via_weakApproximation.md` §7 verbatim).
-/

namespace Work.SSGRoute.C6ValueFormula

open CategoryTheory

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {k : Type} [CommRing k] {D Γ : Type} [Group D] [Group Γ]
variable (φ : D →* Γ) (A : Rep.{0} k D)
variable [Fintype Γ] [DecidableEq Γ]
variable (hker : KerActsTrivially φ A)

/-- The Dirac at a coset is additive in its value. -/
lemma dirac_add (x : Γ) (a b : A.V) :
    dirac φ A hker x (a + b) = dirac φ A hker x a + dirac φ A hker x b := by
  ext γ
  rw [Submodule.coe_add, Pi.add_apply]
  by_cases hγ : ∃ d : D, φ d * x = γ
  · rw [dirac_apply_eq φ A hker x (a + b) hγ.choose_spec,
      dirac_apply_eq φ A hker x a hγ.choose_spec,
      dirac_apply_eq φ A hker x b hγ.choose_spec, map_add]
  · rw [dirac_apply_of_not φ A hker x (a + b) hγ,
      dirac_apply_of_not φ A hker x a hγ, dirac_apply_of_not φ A hker x b hγ, add_zero]

/-- **The term rewrite.**  For a `1`-cocycle `h` of the coinduced module and elements `γ x` with
`φ d = x * γ * x⁻¹`, the `x`-term of the detection sum splits into the value of the Shapiro partner
`(h (φ d)).1 1` and the defect term. -/
theorem dirac_cocycle_term {W : Type} [AddCommGroup W] [Module k W]
    (ν : Rep.coind φ A ⟶ Rep.trivial k Γ W)
    (h : Γ → (Rep.coind φ A).V)
    (hc : h ∈ (groupCohomology.cocycles₁ (Rep.coind φ A) :
      Set (Γ → (Rep.coind φ A).V)))
    (γ x : Γ) (d : D) (hδ : φ d = x * γ * x⁻¹) :
    ν (dirac φ A hker 1 ((h γ).1 x))
      = ν (dirac φ A hker 1 ((h (φ d)).1 1))
        + ν (dirac φ A hker 1 ((h x⁻¹).1 x - A.ρ d ((h x⁻¹).1 x))) := by
  have hval := Work.SSGRoute.Sha2Lib.coind_cocycle_value φ A h hc γ x⁻¹ d
    (by rw [inv_inv]; exact hδ)
  rw [inv_inv] at hval
  rw [hval]
  rw [show (h (φ d)).1 1 + (h x⁻¹).1 x - A.ρ d ((h x⁻¹).1 x)
      = (h (φ d)).1 1 + ((h x⁻¹).1 x - A.ρ d ((h x⁻¹).1 x)) from by abel]
  rw [dirac_add, map_add]

/-- **Item (3) of the C6 route: the detection value of a coinduced cocycle as a coset sum.**  For a
`1`-cocycle `h` of the coinduced module `Rep.coind φ A`, a `Γ`-equivariant functional `ν` with
trivial coefficients, an element `γ : Γ` and functions `rep` (a coset section) and `δx` with
`φ (δx x) = x * γ * x⁻¹`, the detection value is the coset sum

    ν (h γ) = Σ_x [ ν (δ_{1, (h (φ (δx x))).1 1}) + ν (δ_{1, defect_x}) ] ,

where `(h (φ (δx x))).1 1` is the value of the *Shapiro partner* of `h` at the conjugate
`x * γ * x⁻¹`, and `defect_x = (h x⁻¹).1 x - A.ρ (δx x) ((h x⁻¹).1 x)` is the `A`-dependent defect.
This is formula (7.1) of `E7cC/NOTE_C6_session17_level_via_weakApproximation.md` §7, together with
the defect sum of §15. -/
theorem coind_cocycle_detectionValue {W : Type} [AddCommGroup W] [Module k W]
    (ν : Rep.coind φ A ⟶ Rep.trivial k Γ W)
    (h : Γ → (Rep.coind φ A).V)
    (hc : h ∈ (groupCohomology.cocycles₁ (Rep.coind φ A) :
      Set (Γ → (Rep.coind φ A).V)))
    (γ : Γ) (rep : Γ → Γ) (hrep : ∀ γ : Γ, γ * (rep γ)⁻¹ ∈ φ.range)
    (hidem : ∀ γ : Γ, rep (rep γ) = rep γ)
    (heq : ∀ γ γ' : Γ, γ * γ'⁻¹ ∈ φ.range → rep γ = rep γ')
    (δx : Γ → D) (hδ : ∀ x : Γ, φ (δx x) = x * γ * x⁻¹) :
    ν (h γ) = ∑ x ∈ Finset.image rep Finset.univ,
      (ν (dirac φ A hker 1 ((h (φ (δx x))).1 1))
        + ν (dirac φ A hker 1 ((h x⁻¹).1 x - A.ρ (δx x) ((h x⁻¹).1 x)))) := by
  rw [coind_functional_eq_cosetSum φ A hker ν rep hrep hidem heq (h γ)]
  exact Finset.sum_congr rfl fun x _ => dirac_cocycle_term φ A hker ν h hc γ x (δx x) (hδ x)
/-- The Dirac at a coset vanishes at the value `0`. -/
@[simp] lemma dirac_zero (x : Γ) :
    dirac φ A hker x (0 : A.V) = 0 := by
  ext γ
  rw [Submodule.coe_zero, Pi.zero_apply]
  by_cases hγ : ∃ d : D, φ d * x = γ
  · rw [dirac_apply_eq φ A hker x (0 : A.V) hγ.choose_spec, map_zero]
  · rw [dirac_apply_of_not φ A hker x (0 : A.V) hγ]

/-- **Formula (7.1) of the C6 route: the detection value of a coinduced cocycle at the conjugates.**
For a coefficient module `A` with the *trivial* action the defect terms of
`coind_cocycle_detectionValue` vanish identically, and the detection value is plainly the coset sum
of the values of the Shapiro partner `y δ := (h (φ δ)).1 1` of `h` at the conjugates
`x * γ * x⁻¹` of `γ`:

    ν (h γ) = Σ_x ν (δ_{1, y (x * γ * x⁻¹)}) .

This is the identity that the Grünwald prescription is applied to: the values `y (x γ x⁻¹)` are the
local data of a global class over the fixed field `K^{D_w}`. -/
theorem coind_cocycle_detectionValue_trivial [A.IsTrivial] {W : Type} [AddCommGroup W]
    [Module k W]
    (ν : Rep.coind φ A ⟶ Rep.trivial k Γ W)
    (h : Γ → (Rep.coind φ A).V)
    (hc : h ∈ (groupCohomology.cocycles₁ (Rep.coind φ A) :
      Set (Γ → (Rep.coind φ A).V)))
    (γ : Γ) (rep : Γ → Γ) (hrep : ∀ γ : Γ, γ * (rep γ)⁻¹ ∈ φ.range)
    (hidem : ∀ γ : Γ, rep (rep γ) = rep γ)
    (heq : ∀ γ γ' : Γ, γ * γ'⁻¹ ∈ φ.range → rep γ = rep γ')
    (δx : Γ → D) (hδ : ∀ x : Γ, φ (δx x) = x * γ * x⁻¹) :
    ν (h γ) = ∑ x ∈ Finset.image rep Finset.univ,
      ν (dirac φ A hker 1 ((h (φ (δx x))).1 1)) := by
  rw [coind_cocycle_detectionValue φ A hker ν h hc γ rep hrep hidem heq δx hδ]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hdef : (h x⁻¹).1 x - A.ρ (δx x) ((h x⁻¹).1 x) = 0 := by
    rw [Representation.isTrivial_def A.ρ (δx x), LinearMap.id_apply, sub_self]
  rw [hdef, dirac_zero, map_zero, add_zero]
end Work.SSGRoute.C6ValueFormula
