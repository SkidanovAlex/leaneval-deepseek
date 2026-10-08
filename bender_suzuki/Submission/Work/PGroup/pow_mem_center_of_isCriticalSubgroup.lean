import Mathlib
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.pow_mem_frattiniIn

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `p`-th powers of a critical subgroup are central

Let `C` be a critical subgroup of a finite `p`-group `P` (FT Lemma 8.2).  One of the defining
properties of a critical subgroup is that it is *Frattini-in-center*, `Φ(C) ≤ Z(C)`.  For a finite
`p`-group every `p`-th power lies in the Frattini subgroup (`Work.PGroup.pow_mem_frattiniIn`),
so every `x ∈ C` satisfies `x ^ p ∈ Φ(C) ≤ Z(C)`.

This is the fact that makes `C` of nilpotency class at most two with `C / Z(C)` elementary abelian.
-/

namespace Work.PGroup

theorem pow_mem_center_of_isCriticalSubgroup {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    (P C : Subgroup G) [Finite P] (hP : IsPGroup p P) (hC : Work.PGroup.IsCriticalSubgroup p P C)
    {x : G} (hx : x ∈ C) : x ^ p ∈ Work.PGroup.centerIn C := by
  -- `C ≤ P` is finite and a `p`-group; `x ^ p` lies in `Φ(C)`, and `Φ(C) ≤ Z(C)` by hypothesis.
  have hfin : Finite ↥C :=
    Finite.of_injective (Subgroup.inclusion hC.le_self) (Subgroup.inclusion_injective _)
  have hCP : IsPGroup p C := hP.to_le hC.le_self
  exact hC.frattini_le_center (@pow_mem_frattiniIn G _ p hp C hfin hCP x hx)

end Work.PGroup
