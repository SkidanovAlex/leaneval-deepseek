import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Quaternion

/-- A product of cyclic groups indexed by a subsingleton type is cyclic:
an empty product is the trivial group, and a nonempty product over a subsingleton
index is isomorphic to its single factor `Multiplicative (ZMod (n i))`, which is
cyclic because `ZMod (n i)` is additively cyclic. -/
theorem isCyclic_pi_of_subsingleton {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ι → ℕ)
    (h : Subsingleton ι) : IsCyclic ((i : ι) → Multiplicative (ZMod (n i))) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- Empty index: the product is the trivial group, hence cyclic.
    exact isCyclic_of_subsingleton
  · -- Nonempty index: identify the product with its single factor via `MulEquiv.piUnique`.
    have huniq : Unique ι := uniqueOfSubsingleton hι.some
    exact (MulEquiv.piUnique (fun i => Multiplicative (ZMod (n i)))).isCyclic.mpr inferInstance

end Work.BrauerSuzuki.Quaternion
