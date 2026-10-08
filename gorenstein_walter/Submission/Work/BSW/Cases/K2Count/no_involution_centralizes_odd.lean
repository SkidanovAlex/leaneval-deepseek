import Mathlib
import Submission.Work.BSW.Concl
import Submission.Work.BSW.Cases.sylow_two_structure

/-!
# `|C_G(u)| = 4` for involutions: no involution centralizes an element of odd order

Hypotheses `Work.GW2.BSWHyps2 G t s K` with `|K| = 2` force every involution `u` to have
`|C_G(u)| = 4` (`Work.BSW.Cases.sylow_two_structure`).  Consequently an involution can never
commute with a nonidentity element of odd order: that element would lie in `C_G(u)`, so its order
would divide `4`, and being odd it would be `1`.

This is the `★` of Bender's `|K| = 2` counting argument (Bender 1974, §1, p. 230): it is what makes
`C_G(T)` odd for every subgroup `T` of odd order, and what makes the involution of `N_G(T)` act
fixed-point-freely on `C_G(T)`.
-/

namespace Work.BSW.Cases.K2Count

open Subgroup Work.GW2

/-- **No involution commutes with a nonidentity element of odd order.**

In the `|K| = 2` case every involution `u` has `|C_G(u)| = 4`
(`Work.BSW.Cases.sylow_two_structure`).  If `x ≠ 1` had odd order and `u x = x u`, then `x` would
lie in `C_G(u)`, so `orderOf x ∣ 4`; being odd, `orderOf x = 1`, i.e. `x = 1`. -/
theorem no_involution_centralizes_odd {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : BSWHyps2 G t s K) (hk : Nat.card ↥K = 2) :
    ∀ x : G, x ≠ 1 → Odd (orderOf x) → ∀ u : G, orderOf u = 2 → ¬ (u * x = x * u) := by
  intro x hx1 hxodd u hu hcomm
  obtain ⟨-, hcen, -, -⟩ := Work.BSW.Cases.sylow_two_structure t s K h hk
  have hxmem : x ∈ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm.symm
  have hdvd : orderOf x ∣ Nat.card ↥(Subgroup.centralizer ({u} : Set G)) := by
    have hle : Subgroup.zpowers x ≤ Subgroup.centralizer ({u} : Set G) :=
      Subgroup.zpowers_le.mpr hxmem
    have h' := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers] at h'
  rw [hcen u hu] at hdvd
  have hpos : 0 < orderOf x := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
  have hle : orderOf x ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases hx : orderOf x
  · exact hx1 (orderOf_eq_one_iff.mp hx)
  · rcases hxodd with ⟨m, hm⟩; omega
  · exact absurd hdvd (by norm_num)
  · rcases hxodd with ⟨m, hm⟩; omega

end Work.BSW.Cases.K2Count
