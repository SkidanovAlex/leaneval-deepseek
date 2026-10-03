import Mathlib
import Submission.Work.ORP311.P311Defs

namespace Work.ORP311

/-- The map `j ↦ t^j` is injective on any integer interval, since `t` has infinite
order modulo `N` (in particular `t` has infinite order: `t^k = 1` implies `k = 0`). -/
theorem injOn_zpow_Icc {G : Type*} [Group G] {N : Subgroup G} {t : G}
    (h : Work.ORP311.P311.TwistData N t) (m : ℕ) :
    Set.InjOn (fun j : ℤ => t ^ j) ↑(Finset.Icc (-(m : ℤ)) m) := by
  intro a _ b _ hab
  change t ^ a = t ^ b at hab
  have h1 : t ^ (a - b) = 1 := by rw [zpow_sub, hab, mul_inv_cancel]
  have h2 : a - b = 0 := h.inf (a - b) (by rw [h1]; exact N.one_mem)
  omega

theorem card_sWin {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {N : Subgroup G} {t : G} (h : Work.ORP311.P311.TwistData N t) (m : ℕ) : (Work.ORP311.P311.sWin t m).card = 2 * m + 1 := by
  classical
  rw [Work.ORP311.P311.sWin, Finset.card_image_of_injOn (injOn_zpow_Icc h m), Int.card_Icc]
  have : (m + 1 - -(m : ℤ)) = ((2 * m + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [this, Int.toNat_natCast]

end Work.ORP311
