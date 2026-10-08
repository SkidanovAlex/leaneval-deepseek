import Mathlib
import Submission.Work.BSW.Basic
import Submission.Work.BSW.Api.card_sup_zpowers

namespace Work.BSW.Api

/-- In the `|K| = 2` case, `C_G(t) = ⟨t⟩ ⊔ ⟨s⟩` is a Klein four-group.

Indeed `C_G(t) = K ⊔ ⟨s⟩` (`Work.BSW.centralizer_t_eq`), `|K ⊔ ⟨s⟩| = 2|K|`
(`Work.BSW.Api.card_sup_zpowers`, which uses `K ⊓ ⟨s⟩ = ⊥`), and `|K| = 2`. -/
theorem card_centralizer_of_card_K_two {G : Type} [Group G] [Finite G] {t s : G}
    {K : Subgroup G} (h : Work.GW2.BSWHyps2 G t s K) (hk : Nat.card ↥K = 2) :
    Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = 4 := by
  rw [Work.BSW.centralizer_t_eq h, card_sup_zpowers h, hk]

end Work.BSW.Api
