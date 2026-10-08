import Mathlib
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.piCore_isPiNat

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `O_p(G) ≤ O_{p',p}(G)`

The `p`-core `O_p(G)` is contained in `O_{p',p}(G)`, the preimage in `G` of
`O_p(G/O_{p'}(G))`.

Indeed the image of the normal `p`-subgroup `O_p(G)` in `G/O_{p'}(G)` is a normal
subgroup whose order divides `|O_p(G)|`, hence is a `p`-group, and therefore lies in
`O_p(G/O_{p'}(G))` by maximality of the latter.
-/

noncomputable section

open Classical

namespace Work.Fitting

theorem pCore_le_pPrimePCore (p : ℕ) (G : Type*) [Group G] [Finite G] :
    Work.Fitting.pCore p G ≤ Work.Fitting.pPrimePCore p G := by
  rw [pPrimePCore, ← Subgroup.map_le_iff_le_comap]
  refine le_piCore ?_ ?_
  · exact (inferInstance : (pCore p G).Normal).map _
      (QuotientGroup.mk'_surjective (pPrimeCore p G))
  · exact isPiNat_of_dvd (Subgroup.card_map_dvd (H := pCore p G)
      (QuotientGroup.mk' (pPrimeCore p G))) (piCore_isPiNat G (fun q => q = p))

end Work.Fitting
