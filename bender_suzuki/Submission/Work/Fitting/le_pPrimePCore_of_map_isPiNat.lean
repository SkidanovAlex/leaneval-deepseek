import Mathlib
import Submission.Work.Fitting.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `N ≤ O_{p',p}(G)` when `N/O_{p'}(G)` is a `p`-group

Let `N ⊴ G` with `O_{p'}(G) ≤ N`.  The image `N̄ = N·O_{p'}(G)/O_{p'}(G) = N/O_{p'}(G)` of `N`
in `G/O_{p'}(G)` is a **normal** subgroup of `G/O_{p'}(G)` (image of a normal subgroup under a
surjection), and by hypothesis its order is a power of `p`.  Hence `N̄ ≤ O_p(G/O_{p'}(G))` by
maximality of the `p`-core, i.e. `N ≤ π⁻¹(O_p(G/O_{p'}(G))) = O_{p',p}(G)`.

Note the hypothesis `O_{p'}(G) ≤ N` is not needed for this argument: `Subgroup.map_le_iff_le_comap`
is unconditional, so `N ≤ π⁻¹(N̄) ≤ π⁻¹(O_p(G/O_{p'}(G)))` holds for every normal `N` whose image
in `G/O_{p'}(G)` is a `p`-group.
-/

noncomputable section

open Classical

namespace Work.Fitting

theorem le_pPrimePCore_of_map_isPiNat (p : ℕ) (G : Type*) [Group G] [Finite G]
    {N : Subgroup G} (hN : N.Normal) (h : Work.Fitting.pPrimeCore p G ≤ N)
    (hpi : Work.Fitting.IsPiNat (fun q => q = p)
      (Nat.card ↥(N.map (QuotientGroup.mk' (Work.Fitting.pPrimeCore p G))))) :
    N ≤ Work.Fitting.pPrimePCore p G := by
  have _ := h
  -- `O_{p',p}(G) = π⁻¹(O_p(G/O_{p'}(G)))`, so it suffices to push `N` forward along `π`.
  rw [pPrimePCore, ← Subgroup.map_le_iff_le_comap]
  -- the image of `N` is a normal `p`-subgroup of the quotient, hence inside the `p`-core.
  exact le_piCore
    (Subgroup.Normal.map hN (QuotientGroup.mk' (pPrimeCore p G))
      (QuotientGroup.mk'_surjective (pPrimeCore p G)))
    hpi

end Work.Fitting
