import Mathlib
import Submission.Work.EKLContract.Defs

/-!
# The orbit map of `SL₃(ℝ)` on `X₃ = SL₃(ℝ)/SL₃(ℤ)` is open

`X₃ = G/Γ` carries the quotient topology and the (transitive) left action of `G`.  For every
`x : X₃` the partial orbit map `g ↦ g • x : G → X₃` is open: writing `x = mkX h` for a
representative `h : G`, the map factors as

  `g ↦ g • mkX h = mkX (g * h) = (mkX) ∘ (· * h)`,

the composition of the quotient map `mkX : G → G/Γ` — open because `G/Γ` is a quotient of the
topological group `G` — with right translation by `h`, which is a homeomorphism of `G`.
-/

open Work.EKLContract

namespace Work.EKLComp

lemma isOpenMap_smul (x : Work.EKLContract.X3) : IsOpenMap (fun g : Work.EKLContract.SL3 => g • x) := by
  induction x using Quotient.inductionOn with
  | h h =>
    have hfun : (fun g : Work.EKLContract.SL3 => g • QuotientGroup.mk h) =
        (Work.EKLContract.mkX ∘ fun g : Work.EKLContract.SL3 => g * h) := by
      funext g; rfl
    rw [hfun]
    exact QuotientGroup.isOpenMap_coe.comp (isOpenMap_mul_right h)

end Work.EKLComp
