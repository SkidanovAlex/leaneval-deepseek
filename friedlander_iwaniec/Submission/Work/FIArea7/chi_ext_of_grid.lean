import Mathlib
import Submission.Work.FITop3.Defs3
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea7.GaussUnits
import Submission.Work.FIArea7.card_charMod4d_eq_card_units

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea7

/-- A character of modulus `4d` extended by zero (an `IsCharExt`) is periodic in the strong sense
that its value at `z` only depends on the residue class of `z` mod `4d`: it equals its value at
the canonical representative `(re z mod 4d) + (im z mod 4d) i`. -/
lemma IsCharExt.eq_lift (d : ℕ) [NeZero (4 * d)] {chi : GaussianInt → ℂ}
    (h : IsCharExt d chi) (z : GaussianInt) :
    chi z = chi (⟨(((z.re : ZMod (4 * d)).val : ℤ)),
      (((z.im : ZMod (4 * d)).val : ℤ))⟩ : GaussianInt) := by
  refine h.congr ?_ ?_
  · show (z.re : ZMod (4 * d)) = ((((z.re : ZMod (4 * d)).val : ℤ)) : ZMod (4 * d))
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  · show (z.im : ZMod (4 * d)) = ((((z.im : ZMod (4 * d)).val : ℤ)) : ZMod (4 * d))
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]

/-- **Characters of modulus `4d`, extended by zero, are determined by the unit grid.**
Two `IsCharMod4d`-characters of `ℤ[i]` vanishing off the units mod `4d` which agree on the
canonical lifts of the unit grid `{p : (ZMod 4d)² // IsUnit (gaussNorm p)}` are equal. -/
theorem chi_ext_of_grid (d : ℕ) (hd : 0 < d) (chi psi : GaussianInt → ℂ)
    (hchi : Work.FITop3.IsCharMod4d d chi ∧
      (∀ z : GaussianInt, ¬ Nat.Coprime (Work.FIPlan.gnorm z) (4 * d) → chi z = 0))
    (hpsi : Work.FITop3.IsCharMod4d d psi ∧
      (∀ z : GaussianInt, ¬ Nat.Coprime (Work.FIPlan.gnorm z) (4 * d) → psi z = 0))
    (hgrid : ∀ p : {p : ZMod (4 * d) × ZMod (4 * d) // IsUnit (Work.FIArea7.gaussNorm p)},
      chi ⟨((p.1.1.val : ℤ)), ((p.1.2.val : ℤ))⟩
        = psi ⟨((p.1.1.val : ℤ)), ((p.1.2.val : ℤ))⟩) :
    chi = psi := by
  have hN : NeZero (4 * d) := ⟨by omega⟩
  have hχ : Work.FIArea7.IsCharExt d chi := hchi
  have hψ : Work.FIArea7.IsCharExt d psi := hpsi
  funext z
  by_cases h : Nat.Coprime (Work.FIPlan.gnorm z) (4 * d)
  · have hu : IsUnit (gaussNorm (((z.re : ZMod (4 * d)), (z.im : ZMod (4 * d))) :
        ZMod (4 * d) × ZMod (4 * d))) := by
      show IsUnit ((z.re : ZMod (4 * d)) ^ 2 + (z.im : ZMod (4 * d)) ^ 2)
      rw [← Work.FIArea7.gnorm_cast (4 * d) z]
      exact (ZMod.isUnit_iff_coprime (Work.FIPlan.gnorm z) (4 * d)).mpr h
    have hgp := hgrid ⟨((z.re : ZMod (4 * d)), (z.im : ZMod (4 * d))), hu⟩
    rw [hχ.eq_lift d z, hψ.eq_lift d z]
    exact hgp
  · rw [hχ.eq_zero_of_not_coprime z h, hψ.eq_zero_of_not_coprime z h]

end Work.FIArea7
