import Mathlib
import Submission.Work.ZJB2.Defs

namespace Work.ZJB2

open Subgroup

variable {G : Type*} [Group G]

/-! ## The centre of a nontrivial finite `p`-group is nontrivial

`Z(S) = C_G(S) ∩ S` (definition `Work.ZJB.ZS`) is the centre of the group `↥S`, viewed as a
subgroup of the ambient group `G`.  For a nontrivial finite `p`-group `↥S` that centre is
nontrivial (`IsPGroup.center_nontrivial`), which is exactly the statement `Z(S) ≠ ⊥`.

This file is self-contained on purpose: the same argument also exists as
`Work.CORE2A.centralizer_inf_ne_bot_of_isPGroup`, but that module imports
`Submission.Work.CORE2A.Defs`, which clashes with `Submission.Work.GLUE.Defs` (imported by
`Submission.Work.ZJB2.Defs`) over the constant `Work.GW2.BenderSetup.ctorIdx`, so the two
cannot be imported together. -/

/-- `C_G(S) ∩ S ≠ ⊥` for a nontrivial finite `p`-subgroup `S`. -/
theorem centralizer_inf_ne_bot_of_isPGroup {p : ℕ} [Fact p.Prime] {S : Subgroup G}
    [Finite G] (hS : IsPGroup p S) (hne : S ≠ ⊥) :
    Subgroup.centralizer (S : Set G) ⊓ S ≠ ⊥ := by
  intro hbot
  haveI hntS : Nontrivial ↥S := (Subgroup.nontrivial_iff_ne_bot S).mpr hne
  haveI hfinS : Finite ↥S := Finite.of_injective (Subtype.val : ↥S → G) Subtype.val_injective
  haveI hntZ : Nontrivial ↥(Subgroup.center ↥S) := IsPGroup.center_nontrivial hS
  obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center ↥S)
  have hcomm : ∀ g : ↥S, g * (z : ↥S) = (z : ↥S) * g := Subgroup.mem_center_iff.mp z.2
  have hzcent : ((z : ↥S) : G) ∈ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := congrArg (fun w : ↥S => (w : G)) (hcomm ⟨y, hy⟩)
    simpa using h
  have hzS : ((z : ↥S) : G) ∈ S := (z : ↥S).2
  have hmem : ((z : ↥S) : G) ∈ Subgroup.centralizer (S : Set G) ⊓ S := ⟨hzcent, hzS⟩
  rw [hbot] at hmem
  have hone : ((z : ↥S) : G) = 1 := Subgroup.mem_bot.mp hmem
  exact hz1 (Subtype.ext (Subtype.ext (by simpa using hone)))

/-- `Z(S) = C_G(S) ∩ S` is nontrivial for a nontrivial finite `p`-subgroup `S ≤ G`. -/
theorem zsNeBotOfIsPGroup {p : ℕ} [Fact p.Prime] (G : Type) [Group G] [Finite G]
    (S : Subgroup G) (hS : IsPGroup p S) (hne : S ≠ ⊥) : Work.ZJB.ZS S ≠ ⊥ := by
  show Subgroup.centralizer (S : Set G) ⊓ S ≠ ⊥
  exact centralizer_inf_ne_bot_of_isPGroup hS hne

end Work.ZJB2
