import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ZDataMup.swCoreDefs
import Submission.Work.SSGRoute.ZSplit.FrobeniusValue
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# NodeS37: the combinatorial skeleton of the `p = 2` §4 recursion

This module contains, with no arithmetic, the objects which the assembly of
`Work.SSGRoute.ZDataTwo.mu2ThreeHalves` (see `NOTE_node_s37_p2_assembly_plan.md`) needs:

* `Gam K := {σ : K ≃ₐ[k] K // σ ≠ 1}` — the index set `G(K|k) ∖ {1}` of the paper's `Ψ`-vector
  (note that `Gam K` is *not* a subgroup: it omits `1`; inverses are taken with `ginv`);
* `IsInv` — the involutions (the paper's `G₁`);
* `theta` — a *choice* of one element from each pair `{τ, τ⁻¹}` of non-involutions, with the two
  properties that formalise the paper's `G₂`/`G₃` bookkeeping:
  `theta τ = τ ∨ theta τ = ginv τ`, and `theta (ginv τ) = theta τ`.  The latter makes the plan's
  "symmetry `v(σ) = v(σ⁻¹)`" **definitional**: the `Ψ`-entry of `τ` is defined as the value of the
  stage class at the sibling indexed by `theta τ`, so `Ψ(τ) = Ψ(τ⁻¹)` holds by construction, and the
  rule's two middle branches (`theta τ = τ` and `theta τ = ginv τ`) are the paper's `G₂`/`G₃`.
-/

namespace Work.SSGRoute.NodeS37

open _root_.SSGRoute

set_option linter.unusedSectionVars false

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-- **The index set `G(K|k) ∖ {1}`** of the paper's `Ψ`-vector. -/
abbrev Gam (K : IntermediateField k Ω) := {σ : K ≃ₐ[k] K // σ ≠ 1}

variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]

/-- **Inversion on `Gam K`**: `Gam K` omits `1`, so it is not a subgroup; this is the inverse. -/
def ginv (τ : Gam K) : Gam K :=
  ⟨τ.1⁻¹, fun h => τ.2 (by simpa using congrArg Inv.inv h)⟩

@[simp] theorem ginv_val (τ : Gam K) : (ginv τ).1 = τ.1⁻¹ := rfl

@[simp] theorem ginv_ginv (τ : Gam K) : ginv (ginv τ) = τ := Subtype.ext (inv_inv τ.1)


/-- **The involutions of `G(K|k) ∖ {1}`** (the paper's `G₁`). -/
def IsInv (τ : Gam K) : Prop := τ.1 ^ 2 = 1

theorem isInv_ginv {τ : Gam K} (h : IsInv τ) : IsInv (ginv τ) := by
  show (τ.1⁻¹) ^ 2 = 1
  rw [inv_pow, h, inv_one]

theorem ginv_eq_self_of_isInv {τ : Gam K} (h : IsInv τ) : ginv τ = τ := by
  refine Subtype.ext ?_
  show τ.1⁻¹ = τ.1
  exact inv_eq_of_mul_eq_one_left h

theorem not_isInv_ginv {τ : Gam K} (h : ¬ IsInv τ) : ¬ IsInv (ginv τ) := by
  intro hi
  exact h (by
    have h2 : (τ.1⁻¹) ^ 2 = 1 := hi
    rw [inv_pow, inv_eq_one] at h2
    exact h2)

/-- The relation on the non-involutions whose classes are the pairs `{τ, τ⁻¹}`. -/
def nonInvRel (τ υ : {σ : Gam K // ¬ IsInv σ}) : Prop :=
  τ.1.1 = υ.1.1 ∨ τ.1.1 = (υ.1.1)⁻¹

theorem nonInvRel_refl (τ : {σ : Gam K // ¬ IsInv σ}) : nonInvRel τ τ := Or.inl rfl

theorem nonInvRel_symm {τ υ : {σ : Gam K // ¬ IsInv σ}} (h : nonInvRel τ υ) :
    nonInvRel υ τ := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rw [h, inv_inv])

theorem nonInvRel_trans {τ υ ω : {σ : Gam K // ¬ IsInv σ}} (h₁ : nonInvRel τ υ)
    (h₂ : nonInvRel υ ω) : nonInvRel τ ω := by
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact Or.inl (h₁.trans h₂)
  · exact Or.inr (by rw [h₁, h₂])
  · exact Or.inr (by rw [h₁, h₂])
  · exact Or.inl (by rw [h₁, h₂, inv_inv])

/-- **The `Setoid` whose classes are the pairs `{τ, τ⁻¹}`.** -/
def nonInvSetoid (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] :
    Setoid {σ : Gam K // ¬ IsInv σ} where
  r := nonInvRel
  iseqv := ⟨fun x => nonInvRel_refl x, fun {_ _} h => nonInvRel_symm h,
    fun {_ _ _} h₁ h₂ => nonInvRel_trans h₁ h₂⟩

noncomputable section Theta

open Classical

/-- **A choice of one element from each pair `{τ, τ⁻¹}`**, with `τ` itself for involutions: the
paper's splitting `G(K|k) ∖ {1} = G₁ ∔ G₂ ∔ G₃`, in the form in which the assembly uses it. -/
def theta (τ : Gam K) : Gam K :=
  if h : IsInv τ then τ
  else (Quotient.out (Quotient.mk'' (s₁ := nonInvSetoid K) (⟨τ, h⟩ : {σ : Gam K // ¬ IsInv σ}))).1

theorem theta_of_inv {τ : Gam K} (h : IsInv τ) : theta τ = τ := by
  rw [theta, dif_pos h]

theorem theta_of_not_inv {τ : Gam K} (h : ¬ IsInv τ) :
    theta τ =
      (Quotient.out (Quotient.mk'' (s₁ := nonInvSetoid K)
        (⟨τ, h⟩ : {σ : Gam K // ¬ IsInv σ}))).1 := by
  rw [theta, dif_neg h]

theorem theta_not_isInv {τ : Gam K} (h : ¬ IsInv τ) : ¬ IsInv (theta τ) := by
  rw [theta_of_not_inv h, IsInv]
  rcases (Quotient.mk_out' (s₁ := nonInvSetoid K) (⟨τ, h⟩ : {σ : Gam K // ¬ IsInv σ}))
    with hr | hr
  · rw [hr]; exact h
  · rw [hr]; exact not_isInv_ginv h

/-- **The first property of `theta`**: it selects `τ` or `τ⁻¹`. -/
theorem theta_eq_self_or_ginv (τ : Gam K) : theta τ = τ ∨ theta τ = ginv τ := by
  by_cases h : IsInv τ
  · exact Or.inl (theta_of_inv h)
  · rw [theta_of_not_inv h]
    rcases (Quotient.mk_out' (s₁ := nonInvSetoid K) (⟨τ, h⟩ : {σ : Gam K // ¬ IsInv σ}))
      with hr | hr
    · exact Or.inl (Subtype.ext hr)
    · exact Or.inr (Subtype.ext hr)

/-- **The second property of `theta`**: it is constant on the pairs `{τ, τ⁻¹}`. -/
theorem theta_ginv (τ : Gam K) : theta (ginv τ) = theta τ := by
  by_cases h : IsInv τ
  · rw [theta_of_inv (isInv_ginv h), theta_of_inv h]
    exact ginv_eq_self_of_isInv h
  · rw [theta_of_not_inv (not_isInv_ginv h), theta_of_not_inv h]
    have hrel : nonInvRel (⟨ginv τ, not_isInv_ginv h⟩ : {σ : Gam K // ¬ IsInv σ})
        (⟨τ, h⟩ : {σ : Gam K // ¬ IsInv σ}) :=
      Or.inr rfl
    exact congrArg (fun q : Quotient (nonInvSetoid K) => (Quotient.out q).1)
      (Quotient.sound (s := nonInvSetoid K) hrel)

end Theta

noncomputable section Rule

open Classical

/-! ## The prescription rule (Schmidt--Wingberg condition (4)) -/

/-- **The witness predicate of the rule (4).**  At the stage `m` producing the `m`-th class, the
block `(l, τ)` of the `l`-th escape prime is prescribed by the "witness" branch of the paper's
condition (4) iff some *later but already constructed* class `z_t` (`l < t < m`) has the same
`Ψ`-vector as `z_l`. -/
def Witness (val : ℕ → Gam K → ZMod 2) (l m : ℕ) : Prop :=
  ∃ t : ℕ, l < t ∧ t < m ∧ ∀ τ : Gam K, val t τ = val l τ

/-- **The prescribed total datum of the stage-`m` class at the block `(l, τ)`** — i.e. at the sibling
of the `l`-th escape prime indexed by `theta τ` — as a function of the `Ψ`-vectors `val`.  This is
the paper's condition (4) together with condition (3) (`0` at the involutions):

* `τ` an involution (`G₁`): `0`;
* `theta τ = τ` (the paper's `G₂`): `val l τ` if there is a witness, `0` otherwise;
* `theta τ = ginv τ` (the paper's `G₃`): `0` if there is a witness, `val l τ` otherwise.

Here `val l τ` is the value of the `l`-th stage class at the sibling indexed by `theta τ`, so that
`val l τ = val l (ginv τ)` holds by construction (`theta_ginv`). -/
noncomputable def prVal (val : ℕ → Gam K → ZMod 2) (m l : ℕ) (τ : Gam K) : ZMod 2 :=
  if IsInv τ then 0
  else if theta τ = τ then (if Witness val l m then val l τ else 0)
  else (if Witness val l m then 0 else val l τ)

theorem prVal_of_inv {val : ℕ → Gam K → ZMod 2} {m l : ℕ} {τ : Gam K} (h : IsInv τ) :
    prVal val m l τ = 0 := by
  rw [prVal, if_pos h]

theorem prVal_of_self {val : ℕ → Gam K → ZMod 2} {m l : ℕ} {τ : Gam K} (hi : ¬ IsInv τ)
    (h : theta τ = τ) :
    prVal val m l τ = if Witness val l m then val l τ else 0 := by
  rw [prVal, if_neg hi, if_pos h]

theorem prVal_of_ginv {val : ℕ → Gam K → ZMod 2} {m l : ℕ} {τ : Gam K} (hi : ¬ IsInv τ)
    (h : theta τ = ginv τ) :
    prVal val m l τ = if Witness val l m then 0 else val l τ := by
  rw [prVal, if_neg hi, if_neg (fun hself => by
    have h1 : τ.1 = τ.1⁻¹ := congrArg Subtype.val (hself.symm.trans h)
    have h2 : τ.1 ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [h1]
      exact mul_inv_cancel τ.1
    exact hi h2)]

end Rule

end Work.SSGRoute.NodeS37
