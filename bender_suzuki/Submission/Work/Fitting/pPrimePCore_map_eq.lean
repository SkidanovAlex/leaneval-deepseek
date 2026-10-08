import Mathlib
import Submission.Work.Fitting.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Fitting.pPrimePCore_map_eq`

By definition `O_{p',p}(G) = O_p(G/O_{p'}(G))` pulled back along the quotient map
`π : G → G/O_{p'}(G)`.  Since `π` is surjective, pushing any subgroup of
`G/O_{p'}(G)` forward along `π` recovers it: `π(π⁻¹(X)) = X`
(`Subgroup.map_comap_eq_self`).  Applying this to `X = O_p(G/O_{p'}(G))` gives
`O_{p',p}(G)·π = O_p(G/O_{p'}(G))`, which is the statement below.
-/

noncomputable section

open Classical

namespace Work.Fitting

theorem pPrimePCore_map_eq (p : ℕ) (G : Type*) [Group G] [Finite G] :
    (Work.Fitting.pPrimePCore p G).map (QuotientGroup.mk' (Work.Fitting.pPrimeCore p G)) =
      Work.Fitting.pCore p (G ⧸ Work.Fitting.pPrimeCore p G) := by
  rw [Work.Fitting.pPrimePCore,
    Subgroup.map_comap_eq_self (by
      rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
      exact le_top)]
  rfl

end Work.Fitting
