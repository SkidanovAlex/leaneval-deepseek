/-
# `chiToAddChar`: the canonical forward map of the identification (§27ter, piece 1)

The identification of the dual: a character `chi` of the corrected `chi`-set (i.e. `IsCharMod4d d chi`
together with the §24-corrected conjunct "vanish off the non-units", `IsCharExt`) is sent to the
additive character of the Gaussian unit group `G = {p : (ZMod 4d)² // IsUnit (gaussNorm p)}` by
*evaluating `chi` at the Gaussian integer spelled by the coordinates of `p`*:

  `chiToAddChar d hd chi h := fun p => chi ⟨p.1.1.val, p.1.2.val⟩`.

This clause is canonical — no `Classical.choice` is needed in this direction (`chi` is determined by
its values on the representatives).  The two proof obligations are discharged by the landed pieces:

* `map_zero_eq_one'` — `chi ⟨1,0⟩ = chi 1 = 1` (`IsCharMod4d`'s first conjunct);
* `map_add_eq_mul'` — the representative of the product `p * q` in `G` is `gaussMul` of the representatives,
  and its `ZMod.val` is congruent mod `4d` to the Gaussian product of `liftToInt p` and `liftToInt q`
  **coordinatewise** (`gaussCoord_val_gaussMul`, L716); congruences mod a rational integer are
  congruences in `ℤ[i]`, so `chi`'s periodicity clause moves the value to the Gaussian product, and
  its multiplicativity clause splits it.
-/
import Mathlib
import Submission.Work.FIArea7.GaussUnits
import Submission.Work.FIArea7.gaussCoord_val_gaussMul
import Submission.Work.FIArea7.gaussMul_rep_dvd
import Submission.Work.FIArea7.one_rep_dvd
import Submission.Work.FITop3.Defs3
import Submission.Work.FIPlan.Interface

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.FIArea7

noncomputable section

/-- **The canonical forward map of the identification.**  `chi ↦ (p ↦ chi ⟨p.1.1.val, p.1.2.val⟩)`. -/
def chiToAddChar (d : ℕ) (hd : 0 < d) (chi : GaussianInt → ℂ)
    (h : Work.FITop3.IsCharMod4d d chi) :
    AddChar (Additive {p : ZMod (4 * d) × ZMod (4 * d) // IsUnit (gaussNorm p)}) ℂ where
  toFun p := chi ⟨(((Additive.toMul p).1.1).val : ℤ), (((Additive.toMul p).1.2).val : ℤ)⟩
  map_zero_eq_one' := by
    haveI : NeZero (4 * d) := ⟨by omega⟩
    have h1c : ((((1 : ZMod (4 * d)).val : ℤ)) : ZMod (4 * d)) = 1 := by
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    have h0c : ((((0 : ZMod (4 * d)).val : ℤ)) : ZMod (4 * d)) = 0 := by
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    have hz1 : (((((1 : ZMod (4 * d)).val : ℤ) - 1 : ℤ)) : ZMod (4 * d)) = 0 := by
      rw [Int.cast_sub, Int.cast_one, h1c, sub_self]
    have hz0 : (((((0 : ZMod (4 * d)).val : ℤ) - 0 : ℤ)) : ZMod (4 * d)) = 0 := by
      rw [Int.cast_sub, Int.cast_zero, h0c, sub_self]
    have hdvd : (((4 * d : ℕ) : ℤ) : GaussianInt) ∣
        ((⟨(((1 : ZMod (4 * d)).val : ℤ)), (((0 : ZMod (4 * d)).val : ℤ))⟩ : GaussianInt)
          - (1 : GaussianInt)) := one_rep_dvd (4 * d) (by omega)
    show chi (⟨(((1 : ZMod (4 * d)).val : ℤ)), (((0 : ZMod (4 * d)).val : ℤ))⟩ : GaussianInt) = 1
    rw [h.2.2.2.1 _ _ hdvd, h.1]
  map_add_eq_mul' p q := by
    haveI : NeZero (4 * d) := ⟨by omega⟩
    set u : GaussianInt :=
      ⟨(((Additive.toMul p).1.1).val : ℤ), (((Additive.toMul p).1.2).val : ℤ)⟩ with hu
    set v : GaussianInt :=
      ⟨(((Additive.toMul q).1.1).val : ℤ), (((Additive.toMul q).1.2).val : ℤ)⟩ with hv
    have hmod := gaussCoord_val_gaussMul (4 * d) (by omega) (Additive.toMul p).1 (Additive.toMul q).1
    have hdvd : (((4 * d : ℕ) : ℤ) : GaussianInt)
        ∣ (⟨((gaussMul (Additive.toMul p).1 (Additive.toMul q).1).1.val : ℤ),
            ((gaussMul (Additive.toMul p).1 (Additive.toMul q).1).2.val : ℤ)⟩ - u * v) :=
      gaussMul_rep_dvd (4 * d) (by omega) (Additive.toMul p).1 (Additive.toMul q).1
    calc chi ⟨((gaussMul (Additive.toMul p).1 (Additive.toMul q).1).1.val : ℤ),
            ((gaussMul (Additive.toMul p).1 (Additive.toMul q).1).2.val : ℤ)⟩
        = chi (u * v) := h.2.2.2.1 _ _ hdvd
      _ = chi u * chi v := h.2.1 u v

end

end Work.FIArea7
