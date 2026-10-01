/-
# ZeroFreeTables — t23RowA

The six rows of `rowA` of Tables 2 and 3, certified with the constant `CertSlack`
(see `Submission/Work/ZeroFreeTables/t23ExpBounds.lean` for the recipe and the numerical data).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.t23ExpBounds

open scoped BigOperators
noncomputable section

namespace Work.ZeroFreeTables

theorem t23RowA : ∀ p : ℝ × ℝ × ℝ, p ∈ rowA →
    (1 / 15) * (hb72G (p.2.2 / p.1) - hb72G ((p.2.2 - p.2.1) / p.1))
      < 8 / 9 - CertSlack * (16 * p.1 / 15) := by
  intro p hp
  simp only [rowA, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h | h | h | h
  · rw [h]
    rw [show (3.244:ℝ) / (2.3:ℝ) = ((811:ℝ)/575) by norm_num,
        show ((3.244:ℝ) - (0.2:ℝ)) / (2.3:ℝ) = ((761:ℝ)/575) by norm_num]
    rw [hb72G_closed (by norm_num : ((811:ℝ)/575) ≠ 0),
        hb72G_closed (by norm_num : ((761:ℝ)/575) ≠ 0)]
    rw [show 2 * ((811:ℝ)/575) = ((1622:ℝ)/575) by norm_num,
        show 2 * ((761:ℝ)/575) = ((1522:ℝ)/575) by norm_num]
    obtain ⟨-, h1hi⟩ := exp_bounds_quart (x := ((1622:ℝ)/575)) (lo := (16.79144:ℝ)) (hi := (16.79145:ℝ))
            (by norm_num) (by norm_num)
            (by norm_num [expErr, Finset.sum_range_succ])
            (by norm_num [expErr, Finset.sum_range_succ])
    obtain ⟨h2lo, -⟩ := exp_bounds_quart (x := ((1522:ℝ)/575)) (lo := (14.11102:ℝ)) (hi := (14.11103:ℝ))
            (by norm_num) (by norm_num)
            (by norm_num [expErr, Finset.sum_range_succ])
            (by norm_num [expErr, Finset.sum_range_succ])
    norm_num [CertSlack]
    linarith [h1hi, h2lo]
  · rw [h]
    rw [show (3.273:ℝ) / (2.3:ℝ) = ((3273:ℝ)/2300) by norm_num,
        show ((3.273:ℝ) - (0.198:ℝ)) / (2.3:ℝ) = ((123:ℝ)/92) by norm_num]
    rw [hb72G_closed (by norm_num : ((3273:ℝ)/2300) ≠ 0),
        hb72G_closed (by norm_num : ((123:ℝ)/92) ≠ 0)]
    rw [show 2 * ((3273:ℝ)/2300) = ((3273:ℝ)/1150) by norm_num,
        show 2 * ((123:ℝ)/92) = ((123:ℝ)/46) by norm_num]
    obtain ⟨-, h1hi⟩ := exp_bounds_quart (x := ((3273:ℝ)/1150)) (lo := (17.22026:ℝ)) (hi := (17.22027:ℝ))
            (by norm_num) (by norm_num)
            (by norm_num [expErr, Finset.sum_range_succ])
            (by norm_num [expErr, Finset.sum_range_succ])
    obtain ⟨h2lo, -⟩ := exp_bounds_quart (x := ((123:ℝ)/46)) (lo := (14.49658:ℝ)) (hi := (14.49659:ℝ))
            (by norm_num) (by norm_num)
            (by norm_num [expErr, Finset.sum_range_succ])
            (by norm_num [expErr, Finset.sum_range_succ])
    norm_num [CertSlack]
    linarith [h1hi, h2lo]
  · rw [h]
    rw [show (3.305:ℝ) / (2.3:ℝ) = ((661:ℝ)/460) by norm_num,
        show ((3.305:ℝ) - (0.195:ℝ)) / (2.3:ℝ) = ((311:ℝ)/230) by norm_num]
    rw [hb72G_closed (by norm_num : ((661:ℝ)/460) ≠ 0),
        hb72G_closed (by norm_num : ((311:ℝ)/230) ≠ 0)]
    rw [show 2 * ((661:ℝ)/460) = ((661:ℝ)/230) by norm_num,
        show 2 * ((311:ℝ)/230) = ((311:ℝ)/115) by norm_num]
    obtain ⟨-, h1hi⟩ := exp_bounds_quart (x := ((661:ℝ)/230)) (lo := (17.70616:ℝ)) (hi := (17.70617:ℝ))
            (by norm_num) (by norm_num)
            (by norm_num [expErr, Finset.sum_range_succ])
            (by norm_num [expErr, Finset.sum_range_succ])
    obtain ⟨h2lo, -⟩ := exp_bounds_quart (x := ((311:ℝ)/115)) (lo := (14.94456:ℝ)) (hi := (14.94457:ℝ))
            (by norm_num) (by norm_num)
            (by norm_num [expErr, Finset.sum_range_succ])
            (by norm_num [expErr, Finset.sum_range_succ])
    norm_num [CertSlack]
    linarith [h1hi, h2lo]
  · rw [h]
    rw [show (3.341:ℝ) / (2.3:ℝ) = ((3341:ℝ)/2300) by norm_num,
        show ((3.341:ℝ) - (0.192:ℝ)) / (2.3:ℝ) = ((3149:ℝ)/2300) by norm_num]
    rw [hb72G_closed (by norm_num : ((3341:ℝ)/2300) ≠ 0),
        hb72G_closed (by norm_num : ((3149:ℝ)/2300) ≠ 0)]
    rw [show 2 * ((3341:ℝ)/2300) = ((3341:ℝ)/1150) by norm_num,
        show 2 * ((3149:ℝ)/2300) = ((3149:ℝ)/1150) by norm_num]
    obtain ⟨-, h1hi⟩ := exp_bounds_quart (x := ((3341:ℝ)/1150)) (lo := (18.26921:ℝ)) (hi := (18.26922:ℝ))
            (by norm_num) (by norm_num)
            (by norm_num [expErr, Finset.sum_range_succ])
            (by norm_num [expErr, Finset.sum_range_succ])
    obtain ⟨h2lo, -⟩ := exp_bounds_quart (x := ((3149:ℝ)/1150)) (lo := (15.46007:ℝ)) (hi := (15.46008:ℝ))
            (by norm_num) (by norm_num)
            (by norm_num [expErr, Finset.sum_range_succ])
            (by norm_num [expErr, Finset.sum_range_succ])
    norm_num [CertSlack]
    linarith [h1hi, h2lo]
  · rw [h]
    rw [show (3.382:ℝ) / (2.3:ℝ) = ((1691:ℝ)/1150) by norm_num,
        show ((3.382:ℝ) - (0.188:ℝ)) / (2.3:ℝ) = ((1597:ℝ)/1150) by norm_num]
    rw [hb72G_closed (by norm_num : ((1691:ℝ)/1150) ≠ 0),
        hb72G_closed (by norm_num : ((1597:ℝ)/1150) ≠ 0)]
    rw [show 2 * ((1691:ℝ)/1150) = ((1691:ℝ)/575) by norm_num,
        show 2 * ((1597:ℝ)/1150) = ((1597:ℝ)/575) by norm_num]
    obtain ⟨-, h1hi⟩ := exp_bounds_quart (x := ((1691:ℝ)/575)) (lo := (18.93230:ℝ)) (hi := (18.93231:ℝ))
            (by norm_num) (by norm_num)
            (by norm_num [expErr, Finset.sum_range_succ])
            (by norm_num [expErr, Finset.sum_range_succ])
    obtain ⟨h2lo, -⟩ := exp_bounds_quart (x := ((1597:ℝ)/575)) (lo := (16.07702:ℝ)) (hi := (16.07703:ℝ))
            (by norm_num) (by norm_num)
            (by norm_num [expErr, Finset.sum_range_succ])
            (by norm_num [expErr, Finset.sum_range_succ])
    norm_num [CertSlack]
    linarith [h1hi, h2lo]
  · rw [h]
    rw [show (3.428:ℝ) / (2.3:ℝ) = ((857:ℝ)/575) by norm_num,
        show ((3.428:ℝ) - (0.184:ℝ)) / (2.3:ℝ) = ((811:ℝ)/575) by norm_num]
    rw [hb72G_closed (by norm_num : ((857:ℝ)/575) ≠ 0),
        hb72G_closed (by norm_num : ((811:ℝ)/575) ≠ 0)]
    rw [show 2 * ((857:ℝ)/575) = ((1714:ℝ)/575) by norm_num,
        show 2 * ((811:ℝ)/575) = ((1622:ℝ)/575) by norm_num]
    obtain ⟨-, h1hi⟩ := exp_bounds_quart (x := ((1714:ℝ)/575)) (lo := (19.70494:ℝ)) (hi := (19.70495:ℝ))
            (by norm_num) (by norm_num)
            (by norm_num [expErr, Finset.sum_range_succ])
            (by norm_num [expErr, Finset.sum_range_succ])
    obtain ⟨h2lo, -⟩ := exp_bounds_quart (x := ((1622:ℝ)/575)) (lo := (16.79144:ℝ)) (hi := (16.79145:ℝ))
            (by norm_num) (by norm_num)
            (by norm_num [expErr, Finset.sum_range_succ])
            (by norm_num [expErr, Finset.sum_range_succ])
    norm_num [CertSlack]
    linarith [h1hi, h2lo]

end Work.ZeroFreeTables
