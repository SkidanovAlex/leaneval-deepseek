import Mathlib
import Submission.Work.SSGRoute.Sha2Lib.coind_cocycle_value
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node `C6`, item (3): the coset-sum decomposition of the coinduced module

`E7cC/NOTE_C6_session17_level_via_weakApproximation.md` §3 lists, as the still-unformalised part of
*item (3)* of the unramified detector's route, "the identification of the level pairing value with
the coset sum `Σ_x μ_x (h(σ)(x))`".  This file supplies the group-theoretic half of that
identification, in the coinduced model in which the Shapiro value rule
(`Work.SSGRoute.Sha2Lib.coind_cocycle_value`) lives.

For a group homomorphism `φ : D →* Γ` and a `D`-module `A`, the coinduced module `Rep.coind φ A` is
the submodule of the functions `Γ → A` satisfying `f (φ d * γ) = A.ρ d (f γ)`; for finite index it
is the `Γ`-module `Ind_D^Γ A`, so this is the coefficient module in which the Shapiro class of the
detector is written.

The results:

* `KerActsTrivially φ A` — the assumption (automatic in the application, where `φ` is the inclusion
  of a subgroup) that `ker φ` acts trivially on `A`; it is what makes a "Dirac at a coset" well
  defined.
* `dirac φ A hker x a` — the coinduced element supported on the left coset `φ(D) * x` with value `a`
  at `x`, together with `dirac_apply_eq` (its value at any prescribed witness of the coset),
  `dirac_apply_of_not` (it vanishes off the coset) and `dirac_eq_smul` (`δ_{x,a} = x⁻¹ · δ_{1,a}`).
* `coind_eq_sum_dirac` — **every element of the coinduced module is the sum of the Diracs over a coset
  section**.
* `coind_functional_eq_cosetSum` — **consequently a `Γ`-equivariant functional with trivial
  coefficients, evaluated at `f`, is the coset sum of its values on the Diracs**,

      ν f = Σ_{x ∈ reps} ν (δ_{1, f x}) .

This is the step that turns `μ (h d)` into a sum of *values of the Shapiro cocycle `h` at the
conjugate coordinates*; with `Sha2Lib.coind_cocycle_value` (respectively its trivial-coefficient
form `E7cC.coind_cocycle_value_trivial`, and the defect form `E7cC.coind_cocycle_value_defect`) each
term is then `y (x⁻¹ d x)` plus the defect — the formula (7.1) of the note.
-/

namespace Work.SSGRoute.C6ValueFormula

open CategoryTheory

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

section Dirac

variable {k : Type} [CommRing k] {D Γ : Type} [Group D] [Group Γ]
variable (φ : D →* Γ) (A : Rep.{0} k D)

/-- The assumption that the kernel of `φ` acts trivially on `A`: it is what makes the "Dirac at a
coset" well defined (two witnesses of the same coset differ by an element of `ker φ`).  In the
application `φ` is the inclusion of the subgroup `D̃ ≤ Γ`, so this holds trivially. -/
def KerActsTrivially : Prop := ∀ d : D, φ d = 1 → ∀ a : A.V, A.ρ d a = a

/-- The raw function underlying the Dirac at the coset of `x` with value `a`. -/
private noncomputable def diracFun (x : Γ) (a : A.V) : Γ → A.V :=
  fun γ => if h : ∃ d : D, φ d * x = γ then A.ρ h.choose a else 0

/-- Two witnesses of membership in the same coset differ by an element of `ker φ`, and `ker φ` acts
trivially on `A` by `hker`. -/
private lemma diracFun_witness_apply (hker : KerActsTrivially φ A) (x : Γ) (a : A.V)
    (d₁ d₂ : D) {γ : Γ} (h₁ : φ d₁ * x = γ) (h₂ : φ d₂ * x = γ) :
    A.ρ d₂ a = A.ρ d₁ a := by
  have hφ : φ d₂ = φ d₁ := mul_right_cancel (h₂.trans h₁.symm)
  have hk : φ (d₂ * d₁⁻¹) = 1 := by rw [map_mul, map_inv, hφ, mul_inv_cancel]
  have h2 : d₂ = (d₂ * d₁⁻¹) * d₁ := by group
  rw [h2, map_mul]
  exact hker (d₂ * d₁⁻¹) hk (A.ρ d₁ a)

/-- **The Dirac element of the coinduced module at the coset of `x` with value `a`.**  It is the
coinduced function supported on the left coset `φ(D) * x`, taking the value `a` at `x` (and
`A.ρ d a` at `φ d * x`). -/
noncomputable def dirac (hker : KerActsTrivially φ A) (x : Γ) (a : A.V) : A.ρ.coindV φ :=
  ⟨diracFun φ A x a, by
    intro d γ
    by_cases hγ : ∃ e : D, φ e * x = γ
    · have hwit : φ (d * hγ.choose) * x = φ d * γ := by
        rw [map_mul, mul_assoc, hγ.choose_spec]
      have hγ' : ∃ e : D, φ e * x = φ d * γ := ⟨d * hγ.choose, hwit⟩
      have hkey : A.ρ hγ'.choose a = A.ρ (d * hγ.choose) a :=
        (diracFun_witness_apply φ A hker x a hγ'.choose (d * hγ.choose)
          hγ'.choose_spec hwit).symm
      rw [diracFun, dif_pos hγ', diracFun, dif_pos hγ, hkey, map_mul]
      rfl
    · have hγ' : ¬ ∃ e : D, φ e * x = φ d * γ := by
        rintro ⟨e, he⟩
        have h1 : x = φ (e⁻¹ * d) * γ := by
          calc x = (φ e)⁻¹ * (φ e * x) := by group
            _ = (φ e)⁻¹ * (φ d * γ) := by rw [he]
            _ = φ (e⁻¹ * d) * γ := by rw [map_mul, map_inv]; group
        refine hγ ⟨(e⁻¹ * d)⁻¹, ?_⟩
        rw [h1, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
      rw [diracFun, dif_neg hγ', diracFun, dif_neg hγ, map_zero]⟩

/-- The Dirac at `x` takes the value `a` at `x`. -/
lemma diracFun_self (hker : KerActsTrivially φ A) (x : Γ) (a : A.V) :
    diracFun φ A x a x = a := by
  have h : ∃ d : D, φ d * x = x := ⟨1, by simp⟩
  have hval : diracFun φ A x a x = A.ρ h.choose a := by
    simp only [diracFun, dif_pos h]
  rw [hval]
  have hφ1 : φ h.choose = 1 := mul_right_cancel (by rw [h.choose_spec, one_mul])
  exact hker h.choose hφ1 a

@[simp] lemma dirac_apply_self (hker : KerActsTrivially φ A) (x : Γ) (a : A.V) :
    (dirac φ A hker x a).1 x = a := diracFun_self φ A hker x a

end Dirac

section Sum

variable {k : Type} [CommRing k] {D Γ : Type} [Group D] [Group Γ]
variable (φ : D →* Γ) (A : Rep.{0} k D)
variable [Fintype Γ] [DecidableEq Γ]
variable (hker : KerActsTrivially φ A)

/-- The Dirac vanishes away from its coset. -/
lemma dirac_apply_of_not (x : Γ) (a : A.V) {γ : Γ}
    (h : ¬ ∃ d : D, φ d * x = γ) : (dirac φ A hker x a).1 γ = 0 := by
  change diracFun φ A x a γ = 0
  rw [diracFun, dif_neg h]

/-- The Dirac takes the value prescribed by any *given* witness of its coset. -/
lemma dirac_apply_eq (x : Γ) (a : A.V) {γ : Γ} {d : D} (hd : φ d * x = γ) :
    (dirac φ A hker x a).1 γ = A.ρ d a := by
  change diracFun φ A x a γ = A.ρ d a
  let h : ∃ e : D, φ e * x = γ := ⟨d, hd⟩
  rw [diracFun, dif_pos h]
  exact diracFun_witness_apply φ A hker x a d h.choose hd h.choose_spec

/-- **The Diracs are translates of the Dirac at the identity**: `δ_{x,a} = x⁻¹ · δ_{1,a}` for the
action of `Γ` on the coinduced module (`(g · f) γ = f (γ * g)`). -/
lemma dirac_eq_smul (x : Γ) (a : A.V) :
    dirac φ A hker x a = (Rep.coind φ A).ρ x⁻¹ (dirac φ A hker 1 a) := by
  ext γ
  change diracFun φ A x a γ = (dirac φ A hker 1 a).1 (γ * x⁻¹)
  by_cases hγ : ∃ d : D, φ d * x = γ
  · have hwit : φ hγ.choose * 1 = γ * x⁻¹ := by
      rw [mul_one, eq_mul_inv_iff_mul_eq]
      exact hγ.choose_spec
    rw [diracFun, dif_pos hγ, dirac_apply_eq φ A hker 1 a hwit]
  · have hγ' : ¬ ∃ d : D, φ d * 1 = γ * x⁻¹ := by
      rintro ⟨d, hd⟩
      refine hγ ⟨d, ?_⟩
      rw [mul_one, eq_mul_inv_iff_mul_eq] at hd
      exact hd
    rw [diracFun, dif_neg hγ, dirac_apply_of_not φ A hker 1 a hγ']

/-- **Every element of the coinduced module is the sum of the Diracs over a coset section.**  The
section `rep` picks one element out of each left coset of `φ(D)`; the hypotheses say that it is
constant on cosets (`hrep`, `heq`) and idempotent (`hidem`). -/
lemma coind_eq_sum_dirac (rep : Γ → Γ) (hrep : ∀ γ : Γ, γ * (rep γ)⁻¹ ∈ φ.range)
    (hidem : ∀ γ : Γ, rep (rep γ) = rep γ)
    (heq : ∀ γ γ' : Γ, γ * γ'⁻¹ ∈ φ.range → rep γ = rep γ')
    (f : A.ρ.coindV φ) :
    f = ∑ x ∈ Finset.image rep Finset.univ, dirac φ A hker x (f.1 x) := by
  refine Subtype.ext (funext fun γ => ?_)
  rw [Submodule.coe_sum]
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single (rep γ)]
  · -- the surviving term is `f γ`, by the coinduced relation
    obtain ⟨d, hd⟩ := hrep γ
    have hd' : φ d * rep γ = γ := by rw [hd]; group
    rw [dirac_apply_eq φ A hker (rep γ) (f.1 (rep γ)) hd']
    have h1 : f.1 (φ d * rep γ) = A.ρ d (f.1 (rep γ)) :=
      (Representation.mem_coindV _ _ _).1 f.2 d (rep γ)
    rw [hd'] at h1
    exact h1
  · -- all other terms vanish: their cosets are different
    intro x hx hxne
    obtain ⟨γ₀, -, rfl⟩ := Finset.mem_image.mp hx
    refine dirac_apply_of_not φ A hker _ _ (fun hcon => hxne ?_)
    obtain ⟨d, hd⟩ := hcon
    have h1 : γ * (rep γ₀)⁻¹ ∈ φ.range := ⟨d, by rw [← hd]; group⟩
    have h2 : rep γ = rep (rep γ₀) := heq γ (rep γ₀) h1
    rw [hidem γ₀] at h2
    exact h2.symm
  · intro hmem
    exact absurd (Finset.mem_image_of_mem rep (Finset.mem_univ γ)) hmem

/-- **The coset-sum formula for a functional on the coinduced module.**  A `Γ`-equivariant
functional with *trivial* coefficients is the sum, over a set of coset representatives, of its
values at the Diracs — the "coset sum" `Σ_x μ_x (h(σ)(x))` of the detection formula (formula (7.1)
of `E7cC/NOTE_C6_session17_level_via_weakApproximation.md` §7). -/
theorem coind_functional_eq_cosetSum {W : Type} [AddCommGroup W] [Module k W]
    (ν : Rep.coind φ A ⟶ Rep.trivial k Γ W)
    (rep : Γ → Γ) (hrep : ∀ γ : Γ, γ * (rep γ)⁻¹ ∈ φ.range)
    (hidem : ∀ γ : Γ, rep (rep γ) = rep γ)
    (heq : ∀ γ γ' : Γ, γ * γ'⁻¹ ∈ φ.range → rep γ = rep γ')
    (f : A.ρ.coindV φ) :
    ν f = ∑ x ∈ Finset.image rep Finset.univ, ν (dirac φ A hker 1 (f.1 x)) := by
  conv_lhs => rw [coind_eq_sum_dirac φ A hker rep hrep hidem heq f]
  rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [dirac_eq_smul φ A hker x (f.1 x)]
  show ν.hom ((Rep.coind φ A).ρ x⁻¹ (dirac φ A hker 1 (f.1 x)))
    = ν.hom (dirac φ A hker 1 (f.1 x))
  rw [Rep.hom_comm_apply]
  rfl

end Sum

end Work.SSGRoute.C6ValueFormula
