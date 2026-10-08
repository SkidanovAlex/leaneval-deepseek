import Mathlib
import Submission.Work.Induction.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Induction from a normal subgroup of index `2`

Let `K` be a normal subgroup of index `2` of a finite group `L` and `φ` a class function on
`K` which is invariant under conjugation by all of `L`.  Then

* `Ind_K^L φ (y) = 2 φ(y)` for `y ∈ K`, and
* `Ind_K^L φ (y) = 0` for `y ∉ K`.

Indeed in the trace formula every summand is `φ (x * y * x⁻¹)`, and for `x ∈ L` the element
`x * y * x⁻¹` is a conjugate of `y` in `K`; for `x ∈ K` this uses that `φ` is a class function
on `K`, for `x ∉ K` the invariance hypothesis.  (For `y ∉ K` no summand can occur at all,
since `x * y * x⁻¹ ∈ K` would force `y = x⁻¹ * (x * y * x⁻¹) * x ∈ K`.)

This is the computation behind `ζ = 1̃_{C*} - λ̃` in Glauberman (1974), step (2): the quotient
`C*/(T · H*)` has order `2`, and `λ` is invariant under `N* ⊇ C*`.
-/

set_option autoImplicit false

open Classical

namespace Work.BrauerSuzuki.Q8

theorem indFun_eq_of_index_two {L : Type*} [Group L] [Fintype L] {K : Subgroup L}
    (hK : K.Normal) (hidx : K.index = 2) {φ : K → ℂ} (hφ : Work.CharCore.IsClassFun φ)
    (hinv : ∀ (l : L) (k : K), φ ⟨l * (k : L) * l⁻¹, hK.conj_mem (k : L) k.2 l⟩ = φ k)
    {y : L} (hy : y ∈ K) :
    Work.Induction.indFun K φ y = 2 * φ ⟨y, hy⟩ := by
  rw [Work.Induction.indFun_apply_def]
  have hstep : ∀ x : L,
      (if hx : x * y * x⁻¹ ∈ K then φ ⟨x * y * x⁻¹, hx⟩ else 0) = φ ⟨y, hy⟩ := by
    intro x
    rw [dite_eq_left (hK.conj_mem y hy x)]
    exact hinv x ⟨y, hy⟩
  rw [Finset.sum_congr rfl (fun x _ => hstep x)]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : Fintype.card L = 2 * Nat.card ↥K := by
    have h1 := Subgroup.card_mul_index K
    rw [hidx] at h1
    have h2 : Nat.card L = Nat.card ↥K * 2 := h1.symm
    rw [Nat.card_eq_fintype_card (α := L)] at h2
    rw [h2, mul_comm]
  haveI : Nonempty ↥K := ⟨⟨1, K.one_mem⟩⟩
  have hne : (Nat.card ↥K : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := ↥K)).ne'
  rw [hcard]
  push_cast
  field_simp

theorem indFun_eq_zero_of_index_two {L : Type*} [Group L] [Fintype L] {K : Subgroup L}
    (hK : K.Normal) {φ : K → ℂ} {y : L} (hy : y ∉ K) :
    Work.Induction.indFun K φ y = 0 := by
  rw [Work.Induction.indFun_apply_def]
  have hstep : ∀ x : L,
      (if hx : x * y * x⁻¹ ∈ K then φ ⟨x * y * x⁻¹, hx⟩ else 0) = 0 := by
    intro x
    rw [dite_eq_right]
    intro hcon
    have h1 : x⁻¹ * (x * y * x⁻¹) * x ∈ K := hK.conj_mem' (x * y * x⁻¹) hcon x
    rw [show x⁻¹ * (x * y * x⁻¹) * x = y from by group] at h1
    exact hy h1
  rw [Finset.sum_congr rfl (fun x _ => hstep x), Finset.sum_const, smul_zero, mul_zero]

end Work.BrauerSuzuki.Q8
