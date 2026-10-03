import Mathlib
import Submission.Work.FIArea6.ClassDetectDefs
import Submission.Work.FIArea7.GaussUnitClass
import Submission.Work.FIArea6Hecke.area5_6_of_S16Core

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea6

open Finset
open scoped BigOperators

noncomputable section

/-- **Orthogonality of additive characters of a finite abelian group.**  Summing the values
`ψ a ψ̄ b` over all complex-valued additive characters of `A` gives `|A|` when `a = b` and `0`
otherwise.  (For `A = Additive G8` this is the §16 class detection: the pairing of the characters
with the class of `z` and `z₀` modulo eight.) -/
theorem sum_addChar_mul_star {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    (a b : A) :
    (∑ ψ : AddChar A ℂ, ψ a * star (ψ b)) =
      (Fintype.card A : ℂ) * (if a = b then 1 else 0) := by
  have h : ∀ ψ : AddChar A ℂ, ψ a * star (ψ b) = ψ (a - b) := by
    intro ψ
    rw [AddChar.map_sub_eq_div, Complex.star_def,
      ← Complex.inv_eq_conj (AddChar.norm_apply ψ b), div_eq_mul_inv]
  rw [Finset.sum_congr rfl (fun ψ _ => h ψ), AddChar.sum_apply_eq_ite]
  by_cases hab : a = b
  · rw [if_pos (sub_eq_zero.mpr hab), if_pos hab, mul_one]
  · rw [if_neg (fun hc => hab (sub_eq_zero.mp hc)), if_neg hab, mul_zero]

/-- **Evaluation of the modulus-eight character attached to an additive character of `G8`.**  On
the units modulo eight, `char8Of ψ` is `ψ` read on the class of `z` in
`G8 = (ℤ[i]/8)^*`: the duality `chiEquivAddChar` sends `chi` to `p ↦ chi (lift p)`, and `chi` is
periodic modulo eight, so `chi z = chi (lift (class of z))`. -/
theorem char8Of_apply_unit (ψ : AddChar (Additive G8) ℂ) (z : GaussianInt)
    (h : Nat.Coprime (Work.FIPlan.gnorm z) 8) :
    char8Of ψ z = ψ (Additive.ofMul (Work.FIArea7.gaussUnitOf 8 z h)) := by
  have hd : 0 < (2 : ℕ) := by norm_num
  haveI : NeZero (4 * 2) := ⟨by norm_num⟩
  have hχext : Work.FIArea7.IsCharExt 2
      ((Work.FIArea7.chiEquivAddChar 2 hd).symm ψ).1 :=
    ((Work.FIArea7.chiEquivAddChar 2 hd).symm ψ).2
  have hχeq : Work.FIArea7.chiToAddChar 2 hd
      ((Work.FIArea7.chiEquivAddChar 2 hd).symm ψ).1
      ((Work.FIArea7.chiEquivAddChar 2 hd).symm ψ).2.1 = ψ :=
    Equiv.apply_symm_apply (Work.FIArea7.chiEquivAddChar 2 hd) ψ
  calc char8Of ψ z
      = ((Work.FIArea7.chiEquivAddChar 2 hd).symm ψ).1 z := rfl
    _ = ((Work.FIArea7.chiEquivAddChar 2 hd).symm ψ).1
          ⟨(((z.re : ZMod (4 * 2)).val : ℤ)), (((z.im : ZMod (4 * 2)).val : ℤ))⟩ :=
        Work.FIArea7.IsCharExt.eq_lift 2 hχext z
    _ = Work.FIArea7.chiToAddChar 2 hd
          ((Work.FIArea7.chiEquivAddChar 2 hd).symm ψ).1
          ((Work.FIArea7.chiEquivAddChar 2 hd).symm ψ).2.1
          (Additive.ofMul (Work.FIArea7.gaussUnitOf 8 z h)) := rfl
    _ = ψ (Additive.ofMul (Work.FIArea7.gaussUnitOf 8 z h)) := by rw [hχeq]

/-- `IsUnitMod4d 2` is coprimality of the norm with `8` (the modulus `4·2`). -/
theorem coprime_of_isUnitMod4d_two {z : GaussianInt}
    (hz : Work.FIArea5.S16Hecke.IsUnitMod4d 2 z) : Nat.Coprime (Work.FIPlan.gnorm z) 8 := by
  haveI : NeZero (4 * 2) := ⟨by norm_num⟩
  exact (Work.FIArea6Hecke.GaussUnit.isUnitMod4d_iff_coprime (d := 2) z).mp hz

theorem classDetect8Gauss {z z0 : GaussianInt} [Decidable (Work.FITop4.SameClass8 z z0)]
    (hz : Work.FIArea5.S16Hecke.IsUnitMod4d 2 z)
    (hz0 : Work.FIArea5.S16Hecke.IsUnitMod4d 2 z0) :
    (∑ ψ : AddChar (Additive Work.FIArea6.G8) ℂ, Work.FIArea6.char8Of ψ z * star (Work.FIArea6.char8Of ψ z0))
      = (Fintype.card Work.FIArea6.G8 : ℂ) * (if Work.FITop4.SameClass8 z z0 then 1 else 0) := by
  have hcz : Nat.Coprime (Work.FIPlan.gnorm z) 8 := coprime_of_isUnitMod4d_two hz
  have hcz0 : Nat.Coprime (Work.FIPlan.gnorm z0) 8 := coprime_of_isUnitMod4d_two hz0
  have hiff : (Additive.ofMul (Work.FIArea7.gaussUnitOf 8 z hcz)
      = Additive.ofMul (Work.FIArea7.gaussUnitOf 8 z0 hcz0)) ↔
      Work.FITop4.SameClass8 z z0 := by
    rw [Additive.ofMul.injective.eq_iff, Work.FIArea7.gaussUnitOf_eq_iff]
    rfl
  have hcard : Fintype.card (Additive Work.FIArea6.G8) = Fintype.card Work.FIArea6.G8 :=
    Fintype.card_congr Additive.ofMul
  rw [Finset.sum_congr rfl (fun ψ _ => by
    rw [char8Of_apply_unit ψ z hcz, char8Of_apply_unit ψ z0 hcz0])]
  rw [sum_addChar_mul_star, hcard]
  by_cases h : Work.FITop4.SameClass8 z z0
  · rw [if_pos h, if_pos (hiff.mpr h)]
  · rw [if_neg h, if_neg (fun hc => h (hiff.mp hc))]

end

end Work.FIArea6
