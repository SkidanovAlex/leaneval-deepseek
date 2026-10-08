import Mathlib
import Submission.Work.Tame.Defs
import Submission.Work.Tame.Tau
import Submission.Work.Tame.card_mul_set_mul_card_inf

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Tame.indFun_Lgrp_apply_of_mem_Lhat`

The value of an induced function `Ind_{𝔏}^{X} α` at an element `A` of the tamely imbedded set
`L̂` (Feit–Thompson, p. 805): for `α ∈ 𝓒₀(L̂)` (a class function of `𝔏 = N(L̂)` vanishing outside
`L̂` and at `1`) and `A ∈ L̂`,

`Ind_{𝔏}^{X} α (A) = |C_X(A)| · |C_X(A) ∩ 𝔏|⁻¹ · α(A)`.

The proof is the standard double count.  Induction is the average over `x ∈ X` of the values
`α(x A x⁻¹)` (zero when `x A x⁻¹ ∉ 𝔏`).  Definition 9.1(i) says that the conjugates of `A` which
lie in `L̂` are exactly its `𝔏`-conjugates, so on the set `T` of conjugators of `A` back into `L̂`
the summand is constantly `α(A)`.  Moreover `T = 𝔏 · C_X(A)` and the multiplication map
`𝔏 × C_X(A) → T` has all fibres of cardinality `|𝔏 ∩ C_X(A)|`, so `|T| · |𝔏 ∩ C_X(A)| = |𝔏|·|C_X(A)|`.
Dividing by `|𝔏|` gives the claim.
-/

open scoped Pointwise

namespace Work.Tame

variable {X : Type*} [Group X]

/-- The set of conjugators of `A ∈ L̂` back into `L̂` is `𝔏 · C_X(A)`: this is the elementwise
form of Definition 9.1(i) (`conj`) together with `L̂ ⊆ 𝔏 = N(L̂)` (`sub_norm`). -/
theorem Tset_eq_Lgrp_setMul_centralizer {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    (h : IsTamelyImbedded Lhat n Hs) {A : X} (hA : A ∈ Lhat) :
    {x : X | x * A * x⁻¹ ∈ Lhat} =
      (Lgrp Lhat : Set X) * (Subgroup.centralizer ({A} : Set X) : Set X) := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_mul]
  constructor
  · intro hx
    obtain ⟨l, hl, hlA⟩ := h.conj hA hx (isConj_iff.mpr ⟨x, rfl⟩)
    refine ⟨l, hl, l⁻¹ * x, Subgroup.mem_centralizer_singleton_iff.mpr ?_, by group⟩
    have hconj : (l⁻¹ * x) * A * (l⁻¹ * x)⁻¹ = A := by
      calc (l⁻¹ * x) * A * (l⁻¹ * x)⁻¹ = l⁻¹ * (x * A * x⁻¹) * l := by group
        _ = l⁻¹ * (l * A * l⁻¹) * l := by rw [hlA]
        _ = A := by group
    have := congrArg (fun z => z * (l⁻¹ * x)) hconj
    simpa [mul_assoc] using this
  · rintro ⟨l, hl, c, hc, rfl⟩
    have hcA : c * A * c⁻¹ = A := by
      have hc' : c * A = A * c := Subgroup.mem_centralizer_singleton_iff.mp hc
      rw [hc']; group
    have hlA : l * A * l⁻¹ ∈ Lhat := ((mem_Lgrp.mp hl) A).mp hA
    have hpx : (l * c) * A * (l * c)⁻¹ = l * A * l⁻¹ := by
      calc (l * c) * A * (l * c)⁻¹ = l * (c * A * c⁻¹) * l⁻¹ := by group
        _ = l * A * l⁻¹ := by rw [hcA]
    rw [hpx]; exact hlA

variable [Fintype X]

theorem indFun_Lgrp_apply_of_mem_Lhat {X : Type*} [Group X] [Fintype X] {Lhat : Set X} {n : ℕ}
    {Hs : Fin n → Subgroup X} (h : IsTamelyImbedded Lhat n Hs)
    {α : ↥(Lgrp Lhat) → ℂ} (hα : α ∈ C0 Lhat)
    {A : X} (hA : A ∈ Lhat) (hA1 : A ≠ 1) :
    Induction.indFun (Lgrp Lhat) α A =
      ((Nat.card ↥(Subgroup.centralizer ({A} : Set X)) : ℂ) *
        ((Nat.card ↥(Subgroup.centralizer ({A} : Set X) ⊓ Lgrp Lhat) : ℂ))⁻¹) *
        α ⟨A, h.sub_norm hA⟩ := by
  classical
  have hAH : A ∈ Lgrp Lhat := h.sub_norm hA
  have hclass : CharCore.IsClassFun α := (mem_C0.mp hα).1
  have hvan : ∀ l : ↥(Lgrp Lhat), (l : X) ∉ Lhat → α l = 0 := (mem_C0.mp hα).2.1
  -- (1) each summand of the induction sum is `α A` exactly on the set of conjugators.
  have hsummand : ∀ x : X,
      (if hx : x * A * x⁻¹ ∈ Lgrp Lhat then α ⟨x * A * x⁻¹, hx⟩ else 0)
        = if x * A * x⁻¹ ∈ Lhat then α ⟨A, hAH⟩ else 0 := by
    intro x
    by_cases hxH : x * A * x⁻¹ ∈ Lgrp Lhat
    · by_cases hxL : x * A * x⁻¹ ∈ Lhat
      · rw [dif_pos hxH, if_pos hxL]
        obtain ⟨l, hl, hlA⟩ := h.conj hA hxL (isConj_iff.mpr ⟨x, rfl⟩)
        have h1 : (⟨x * A * x⁻¹, hxH⟩ : ↥(Lgrp Lhat)) =
            ⟨l, hl⟩ * ⟨A, hAH⟩ * ⟨l, hl⟩⁻¹ := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          rw [hlA]
        rw [h1]
        exact hclass ⟨A, hAH⟩ ⟨l, hl⟩
      · rw [dif_pos hxH, if_neg hxL]
        exact hvan ⟨x * A * x⁻¹, hxH⟩ hxL
    · by_cases hxL : x * A * x⁻¹ ∈ Lhat
      · exact absurd (h.sub_norm hxL) hxH
      · rw [dif_neg hxH, if_neg hxL]
  -- (2) the induction sum is `|T| · α A`.
  have hfilt : (Finset.univ.filter (fun x : X => x * A * x⁻¹ ∈ Lhat)).card =
      Nat.card ↥({x : X | x * A * x⁻¹ ∈ Lhat} : Set X) := by
    rw [Nat.card_eq_fintype_card, ← Set.toFinset_card, Set.toFinset_ofPred]
  have hsum : (∑ x : X,
        (if hx : x * A * x⁻¹ ∈ Lgrp Lhat then α ⟨x * A * x⁻¹, hx⟩ else 0))
      = (Nat.card ↥({x : X | x * A * x⁻¹ ∈ Lhat} : Set X) : ℂ) * α ⟨A, hAH⟩ := by
    rw [Finset.sum_congr rfl (fun x _ => hsummand x)]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hfilt]
  -- (3) the cardinality of `T` via the multiplication map `𝔏 × C_X(A) → T`.
  have hTcard : Nat.card ↥({x : X | x * A * x⁻¹ ∈ Lhat} : Set X) *
      Nat.card ↥(Subgroup.centralizer ({A} : Set X) ⊓ Lgrp Lhat) =
      Nat.card ↥(Subgroup.centralizer ({A} : Set X)) * Nat.card ↥(Lgrp Lhat) := by
    have h1 := card_mul_set_mul_card_inf (Lgrp Lhat) (Subgroup.centralizer ({A} : Set X))
    rw [inf_comm] at h1
    rw [← Tset_eq_Lgrp_setMul_centralizer h hA] at h1
    rw [h1, Nat.mul_comm]
  -- (4) arithmetic in `ℂ`.
  have hHne : (Nat.card ↥(Lgrp Lhat) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.card_ne_zero.mpr ⟨⟨1, (Lgrp Lhat).one_mem⟩, inferInstance⟩
  have hDne : (Nat.card ↥(Subgroup.centralizer ({A} : Set X) ⊓ Lgrp Lhat) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.card_ne_zero.mpr
      ⟨⟨1, (Subgroup.centralizer ({A} : Set X) ⊓ Lgrp Lhat).one_mem⟩, inferInstance⟩
  have hcast : (Nat.card ↥({x : X | x * A * x⁻¹ ∈ Lhat} : Set X) : ℂ) *
      (Nat.card ↥(Subgroup.centralizer ({A} : Set X) ⊓ Lgrp Lhat) : ℂ) =
      (Nat.card ↥(Subgroup.centralizer ({A} : Set X)) : ℂ) *
        (Nat.card ↥(Lgrp Lhat) : ℂ) := by
    rw [← Nat.cast_mul, hTcard, Nat.cast_mul]
  have hTval : (Nat.card ↥({x : X | x * A * x⁻¹ ∈ Lhat} : Set X) : ℂ) =
      (Nat.card ↥(Subgroup.centralizer ({A} : Set X)) : ℂ) *
        (Nat.card ↥(Lgrp Lhat) : ℂ) *
        ((Nat.card ↥(Subgroup.centralizer ({A} : Set X) ⊓ Lgrp Lhat) : ℂ))⁻¹ := by
    have := congrArg (fun z : ℂ => z *
      ((Nat.card ↥(Subgroup.centralizer ({A} : Set X) ⊓ Lgrp Lhat) : ℂ))⁻¹) hcast
    rwa [mul_assoc, mul_inv_cancel₀ hDne, mul_one] at this
  rw [Induction.indFun_apply_def, hsum, hTval]
  field_simp

end Work.Tame
