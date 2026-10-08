import Mathlib
import Submission.Work.Frobenius.Main
import Submission.Work.Frobenius.Nilpotent.isNilpotent_of_forall_hasNormalPComplement

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A8b: nilpotency of the Frobenius kernel

Thompson's theorem that the kernel of a Frobenius group is nilpotent is proved by showing that,
for every prime `p` dividing the order of the kernel `K`, the group `K` has a normal
`p`-complement (Thompson's normal `p`-complement criterion, area A9, applied to the fixed-point-
free action of the complement on the Sylow subgroups of `K`).

This module records the reduction: a finite group with a normal `p`-complement for every prime
`p` dividing its order is nilpotent
(`Work.Frobenius.Nilpotent.isNilpotent_of_forall_hasNormalPComplement`), and hence the Frobenius
kernel is nilpotent **assuming** the normal `p`-complement input.  Discharging that input is
exactly A9's Thompson normal `p`-complement theorem; once
`Work.NPC.thompson_npc` is available, instantiating `h` below with it completes A8b.
-/

@[expose] public section

noncomputable section

open Classical

namespace Work.Frobenius

variable {G : Type*} [Group G] [Finite G]

/-- **A8b, reduced form.**  A subgroup `K` whose carrier is the Frobenius kernel is nilpotent as
soon as it has a normal `p`-complement for every prime `p` dividing its order.  (The hypotheses
`hH`, `hK` record that `K` really is the Frobenius kernel of the complement `H`; the nilpotency
argument itself only uses the normal `p`-complements.) -/
theorem isNilpotent_kernel_of_forall_hasNormalPComplement {K H : Subgroup G}
    (hH : IsFrobeniusComplement H) (hK : (K : Set G) = frobeniusKernel H)
    (h : ∀ p : ℕ, p.Prime → p ∣ Nat.card K → Work.NPC.HasNormalPComplement p K) :
    Group.IsNilpotent K := by
  have hKne : K ≠ ⊥ := kernel_ne_bot hH hK
  exact Nilpotent.isNilpotent_of_forall_hasNormalPComplement (G := K) fun p hp hdvd =>
    h p hp (by simpa using hdvd)

end Work.Frobenius
