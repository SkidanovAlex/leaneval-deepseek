import Mathlib
import Submission.Work.BSW.Basic

namespace Work.BSW.Api

open Subgroup

/-- The number of involutions of `G` is `|G : C_G(t)| = |G : H|`, via the bijection
`g C_G(t) ↦ t^g` (condition (iv): all involutions are conjugate to `t`). -/
theorem ncard_involutions_eq_index {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) :
    {x : G | orderOf x = 2}.ncard = (Subgroup.centralizer ({t} : Set G)).index := by
  -- Orbit–stabilizer: the index of `C_G(t)` is the number of conjugates of `t`.
  rw [Subgroup.index_centralizer_eq_ncard]
  congr 1
  -- Condition (iv) says precisely that the conjugates of `t` are the involutions: every
  -- involution is conjugate to `t`, and conversely the conjugates of `t` have order `2`.
  ext x
  constructor
  · intro hx
    exact (Work.BSW.involutions_conj h x hx).symm
  · intro hx
    change orderOf x = 2
    change IsConj t x at hx
    rw [isConj_iff] at hx
    obtain ⟨c, hc⟩ := hx
    rw [← hc, ← MulAut.conj_apply c t, MulEquiv.orderOf_eq (MulAut.conj c) t,
      Work.BSW.orderOf_t h]

end Work.BSW.Api
