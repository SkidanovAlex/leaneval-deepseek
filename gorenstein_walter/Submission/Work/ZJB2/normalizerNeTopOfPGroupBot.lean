import Mathlib
import Submission.Work.GLUE.PcoreApi

namespace Work.ZJB2

theorem normalizerNeTopOfPGroupBot (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G]
    (hcore : Work.GW2.pCore p G = ⊥) (H : Subgroup G) (hH : H ≠ ⊥) (hp : IsPGroup p H) :
    Subgroup.normalizer (H : Set G) ≠ ⊤ := by
  intro htop
  -- `N_G(H) = G` means `H` is normal in `G`; being a nontrivial normal `p`-subgroup it must
  -- lie in the (largest normal `p`-subgroup) `O_p(G) = pCore p G`, which is assumed trivial.
  have hHnorm : H.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  have hle : H ≤ Work.GW2.pCore p G := Work.GW2.le_pCore_of_normal_isPGroup hp
  rw [hcore] at hle
  exact hH (le_bot_iff.mp hle)

end Work.ZJB2
