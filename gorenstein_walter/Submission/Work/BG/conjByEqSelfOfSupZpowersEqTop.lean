import Mathlib
import Submission.Work.BG.CharBridge

namespace Work.BG

open OddOrder.RepresentationTheory in
theorem conjByEqSelfOfSupZpowersEqTop {X : Type} [Group X] (U : Subgroup X) [U.Normal] (c : X)
    (hsup : U ⊔ Subgroup.zpowers c = ⊤) (a : ClassFunction ↥U ℂ)
    (hc : ClassFunction.conjBy (G := X) (H := U) c a = a) :
    ∀ g : X, ClassFunction.conjBy (G := X) (H := U) g a = a := by
  -- The inertia group `I_X(a)` of `a` in `X` contains `U` (conjugation by an element
  -- of `U` acts trivially on class functions of `U`) and contains `c` by hypothesis,
  -- hence contains `U ⊔ zpowers c = ⊤`: every element of `X` fixes `a`.
  have hU : U ≤ a.inertia := fun u hu => ClassFunction.conjBy_eq_self_of_mem (H := U) hu a
  have hc' : c ∈ a.inertia := hc
  have htop : a.inertia = ⊤ :=
    top_le_iff.mp (hsup ▸ sup_le hU (Subgroup.zpowers_le.mpr hc'))
  intro g
  have : g ∈ a.inertia := by rw [htop]; exact Subgroup.mem_top g
  exact this

end Work.BG
