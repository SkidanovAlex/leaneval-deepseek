/-
# `chiEquivAddChar`: the identification as an object (§29)

The dual of the Gaussian unit group `G = {p : (ZMod 4d)² // IsUnit (gaussNorm p)}` is the corrected
set of `chi`'s:

  `chiEquivAddChar d hd : {chi // IsCharMod4d d chi ∧ chi vanishes off the non-units} ≃ AddChar (Additive G) ℂ`.

(The predicate on the left is `IsCharMod4d d chi ∧ IsCharExt d chi`, with `IsCharExt` written out;
the two presentations are definitionally equal but Lean's anonymous-constructor elaboration does not
see through the `def`, so we use the unfolded one here.)

* forward: `chiToAddChar d hd chi h` (canonical, §29);
* injective: `chi_ext_of_grid` (L718) — agreement on the grid forces equality;
* surjective: `addChar_extends_charMod4d` (L712) — every `χ` is realised by the witness `chiOf (4*d) χ`,
  whose grid-agreement conjunct *is* the equality after `ext`.
-/
import Mathlib
import Submission.Work.FIArea7.ChiToAddChar
import Submission.Work.FIArea7.card_charMod4d_eq_card_units
import Submission.Work.FIArea7.chi_ext_of_grid
import Submission.Work.FIArea7.addChar_extends_charMod4d

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.FIArea7

noncomputable section

/-- **The identification, as an object**: the corrected `chi`-set is the dual of the Gaussian unit
group. -/
def chiEquivAddChar (d : ℕ) (hd : 0 < d) :
    {chi : GaussianInt → ℂ // Work.FITop3.IsCharMod4d d chi ∧
        (∀ z : GaussianInt, ¬ Nat.Coprime (Work.FIPlan.gnorm z) (4 * d) → chi z = 0)} ≃
      AddChar (Additive {p : ZMod (4 * d) × ZMod (4 * d) // IsUnit (gaussNorm p)}) ℂ :=
  Equiv.ofBijective (fun chi => chiToAddChar d hd chi.1 chi.2.1) ⟨fun chi psi h => by
    refine Subtype.ext (chi_ext_of_grid d hd chi.1 psi.1 chi.2 psi.2 ?_)
    intro p
    exact DFunLike.congr_fun h p, fun χ => by
    obtain ⟨chi, hchi, hagree⟩ := addChar_extends_charMod4d d hd χ
    exact ⟨⟨chi, hchi⟩, by
      ext p
      exact (hagree (Additive.toMul p)).symm⟩⟩

end

end Work.FIArea7
