import Mathlib
import Submission.Work.ZassenhausSuzuki.SzAuto.Vtriv
import Submission.Work.ZassenhausSuzuki.SzAuto.Vtriv_fixes_center

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Vtriv θ` has power-of-two order

`K = GF(2ⁿ)`, `θ : K ≃+* K` a field automorphism with `θ ≠ 1` and `Odd (orderOf θ)`, and
`A := A(K,θ) = SzA K θ`.  `Vtriv θ ≤ Aut(A)` is the *kernel of the action of `Aut(A)` on
`A/Z(A)`*: the subgroup of automorphisms `φ` with `φ x * x⁻¹` central for every `x`.

The statement proved here is that `Vtriv θ` has order a power of `2`.

## The mathematics

By `SzAuto.Vtriv_fixes_center` (proved in `SzAuto/Vtriv_fixes_center.lean`), every `φ ∈ Vtriv θ`
fixes the centre `Z(A) = {(0,b)}` pointwise, i.e. the map `Q_φ b := (φ ⟨0,b⟩).b + b` is
identically zero.  Combining this with the coordinate formula
`φ x = ⟨x.a, x.b + W_φ x⟩` and the additivity `W_φ (x*y) = W_φ x + W_φ y`
(`SzAuto.VtrivW_mul`), where `W_φ ⟨u,v⟩ = P_φ u + Q_φ v`, gives

  `φ ⟨a,b⟩ = ⟨a, b + P_φ a⟩`,   `P_φ a := W_φ ⟨a,0⟩`   for all `a, b`.

Since `K` has characteristic two, `φ² ⟨a,b⟩ = ⟨a, b + P_φ a + P_φ a⟩ = ⟨a,b⟩`: *every element of
`Vtriv θ` is an involution*, i.e. `Vtriv θ` has exponent dividing `2`.  Hence `Vtriv θ` is a
`2`-group, and a finite `2`-group has order `2^m` (`IsPGroup.iff_card`).

Note that the oddness of `orderOf θ` enters exactly through `VtrivQ_eq_zero` inside
`Vtriv_fixes_center`; the rest of the argument is uniform in `n` (including `n = 0`).
-/

noncomputable section

namespace Work.ZassenhausSuzuki.SzAuto

open SzA

variable {n : ℕ}

/-- For `φ ∈ Vtriv θ` (with `θ ≠ 1` of odd order) the automorphism `φ` acts on `A(K,θ)` by
`φ ⟨a,b⟩ = ⟨a, b + P_φ a⟩`; the second coordinate is twisted only by the additive correction
`VtrivP θ φ` along the first coordinate. -/
theorem VtrivPow_apply_eq (θ : GaloisField 2 n ≃+* GaloisField 2 n) (hθ : θ ≠ 1)
    (hodd : Odd (orderOf θ)) {φ : MulAut (SzA (GaloisField 2 n) θ)} (hφ : φ ∈ Vtriv θ)
    (x : SzA (GaloisField 2 n) θ) :
    φ x = ⟨x.a, x.b + VtrivP θ φ x.a⟩ := by
  have hW : VtrivW θ φ x = VtrivP θ φ x.a := by
    conv_lhs => rw [show x = ⟨x.a, x.b⟩ from rfl]
    rw [VtrivW_mk θ hθ hφ, VtrivQ_eq_zero θ hθ hodd hφ, add_zero]
  rw [Vtriv_coord θ hθ hφ x, hW]

/-- **Every element of `Vtriv θ` is an involution** (`K` has characteristic two). -/
theorem VtrivPow_sq_eq_one (θ : GaloisField 2 n ≃+* GaloisField 2 n) (hθ : θ ≠ 1)
    (hodd : Odd (orderOf θ)) {φ : MulAut (SzA (GaloisField 2 n) θ)} (hφ : φ ∈ Vtriv θ) :
    φ * φ = 1 := by
  refine MulEquiv.ext (fun x => ?_)
  rw [MulAut.mul_apply, VtrivPow_apply_eq θ hθ hodd hφ x,
    VtrivPow_apply_eq θ hθ hodd hφ ⟨x.a, x.b + VtrivP θ φ x.a⟩]
  apply SzA.ext <;> simp [add_assoc, CharTwo.add_self_eq_zero]

/-- `Vtriv θ` has exponent dividing `2`, i.e. it is a `2`-group. -/
theorem VtrivPow_isPGroup (θ : GaloisField 2 n ≃+* GaloisField 2 n) (hθ : θ ≠ 1)
    (hodd : Odd (orderOf θ)) : IsPGroup 2 ↥(Vtriv θ) := by
  intro ψ
  refine ⟨1, ?_⟩
  rw [pow_one]
  exact Subtype.ext (VtrivPow_sq_eq_one θ hθ hodd ψ.2)

theorem Vtriv_card_pow_two_v2 {n : ℕ} (θ : GaloisField 2 n ≃+* GaloisField 2 n) (hθ : θ ≠ 1)
    (hodd : Odd (orderOf θ)) :
    ∃ m, Nat.card ↥(Work.ZassenhausSuzuki.Vtriv θ) = 2 ^ m :=
  IsPGroup.iff_card.mp (VtrivPow_isPGroup θ hθ hodd)

end Work.ZassenhausSuzuki.SzAuto

end
