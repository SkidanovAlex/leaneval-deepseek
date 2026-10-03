import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! The counting function `N(a,b,q)` of *FI* §9: the number of pairs `(γ₁,γ₂)` modulo `q`
with `a γ₁² ≡ b γ₂² (mod q)`. -/

namespace Work.FIArea2

/-- `N(a,b,q)`: the number of pairs `(γ₁,γ₂)` modulo `q` with `aγ₁² ≡ bγ₂² (mod q)`. -/
def Ncount (q : ℕ) [NeZero q] (a b : ℕ) : ℕ :=
  ((Finset.univ : Finset (ZMod q × ZMod q)).filter
    (fun p => (a : ZMod q) * p.1 ^ 2 = (b : ZMod q) * p.2 ^ 2)).card

end Work.FIArea2
