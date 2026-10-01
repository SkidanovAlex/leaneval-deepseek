/-
# ZeroFreeTables — t23RowBC

The twelve rows `rowB ++ rowC` of Tables 2 and 3, certified with the constant `CertSlack`
(see `Submission/Work/ZeroFreeTables/t23ExpBounds.lean` for the recipe and the numerical data):

`(1/15)·(G (v/λ) − G ((v−b)/λ)) < 8/9 − CertSlack·(16λ/15)`.

Since `G x = (120 e^{2x}(x−1)² + P(x))/x⁶` with `P(x) = −32x⁵ + 80x³ + 120x² − 120`, and the
coefficient `120(x−1)²/x⁶` of `e^{2x}` is positive on the row data (`x > 1`), an upper bound
`hi1 ≥ e^{2v/λ}` and a lower bound `lo2 ≤ e^{2(v−b)/λ}` reduce each row to rational arithmetic.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.t23Defs
import Submission.Work.ZeroFreeTables.t23Gclosed
import Submission.Work.ZeroFreeTables.t23ExpBounds

open scoped BigOperators
noncomputable section

namespace Work.ZeroFreeTables

theorem t23RowBC : ∀ p : ℝ × ℝ × ℝ, p ∈ Work.ZeroFreeTables.rowB ++ Work.ZeroFreeTables.rowC →
    (1 / 15) * (Work.ZeroFreeTables.hb72G (p.2.2 / p.1) - Work.ZeroFreeTables.hb72G ((p.2.2 - p.2.1) / p.1))
      < 8 / 9 - Work.ZeroFreeTables.CertSlack * (16 * p.1 / 15) := by
  intro p hp
  rw [List.mem_append] at hp
  rcases hp with hp | hp
  · simp only [rowB, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with h | h | h | h | h | h
    · -- rowB 1 : (2.35, 0.18, 3.481)
      rw [h]
      rw [show (3.481:ℝ) / (2.35:ℝ) = ((3481:ℝ)/2350) by norm_num,
          show ((3.481:ℝ) - (0.18:ℝ)) / (2.35:ℝ) = ((3301:ℝ)/2350) by norm_num]
      rw [hb72G_closed (by norm_num : ((3481:ℝ)/2350) ≠ 0),
          hb72G_closed (by norm_num : ((3301:ℝ)/2350) ≠ 0)]
      rw [show 2 * ((3481:ℝ)/2350) = ((3481:ℝ)/1175) by norm_num,
          show 2 * ((3301:ℝ)/2350) = ((3301:ℝ)/1175) by norm_num]
      obtain ⟨-, h1hi⟩ := exp_bounds_quart (x := ((3481:ℝ)/1175)) (lo := (19.34730:ℝ)) (hi := (19.34731:ℝ))
              (by norm_num) (by norm_num)
              (by norm_num [expErr, Finset.sum_range_succ])
              (by norm_num [expErr, Finset.sum_range_succ])
      obtain ⟨h2lo, -⟩ := exp_bounds_quart (x := ((3301:ℝ)/1175)) (lo := (16.59931:ℝ)) (hi := (16.59932:ℝ))
              (by norm_num) (by norm_num)
              (by norm_num [expErr, Finset.sum_range_succ])
              (by norm_num [expErr, Finset.sum_range_succ])
      norm_num [CertSlack]
      linarith [h1hi, h2lo]
    · -- rowB 2 : (2.35, 0.175, 3.542)
      rw [h]
      rw [show (3.542:ℝ) / (2.35:ℝ) = ((1771:ℝ)/1175) by norm_num,
          show ((3.542:ℝ) - (0.175:ℝ)) / (2.35:ℝ) = ((3367:ℝ)/2350) by norm_num]
      rw [hb72G_closed (by norm_num : ((1771:ℝ)/1175) ≠ 0),
          hb72G_closed (by norm_num : ((3367:ℝ)/2350) ≠ 0)]
      rw [show 2 * ((1771:ℝ)/1175) = ((3542:ℝ)/1175) by norm_num,
          show 2 * ((3367:ℝ)/2350) = ((3367:ℝ)/1175) by norm_num]
      obtain ⟨-, h1hi⟩ := exp_bounds_quart (x := ((3542:ℝ)/1175)) (lo := (20.37824:ℝ)) (hi := (20.37825:ℝ))
              (by norm_num) (by norm_num)
              (by norm_num [expErr, Finset.sum_range_succ])
              (by norm_num [expErr, Finset.sum_range_succ])
      obtain ⟨h2lo, -⟩ := exp_bounds_quart (x := ((3367:ℝ)/1175)) (lo := (17.55839:ℝ)) (hi := (17.55840:ℝ))
              (by norm_num) (by norm_num)
              (by norm_num [expErr, Finset.sum_range_succ])
              (by norm_num [expErr, Finset.sum_range_succ])
      norm_num [CertSlack]
      linarith [h1hi, h2lo]
    · -- rowB 3 : (2.35, 0.17, 3.611)
      rw [h]
      rw [show (3.611:ℝ) / (2.35:ℝ) = ((3611:ℝ)/2350) by norm_num,
          show ((3.611:ℝ) - (0.17:ℝ)) / (2.35:ℝ) = ((3441:ℝ)/2350) by norm_num]
      rw [hb72G_closed (by norm_num : ((3611:ℝ)/2350) ≠ 0),
          hb72G_closed (by norm_num : ((3441:ℝ)/2350) ≠ 0)]
      rw [show 2 * ((3611:ℝ)/2350) = ((3611:ℝ)/1175) by norm_num,
          show 2 * ((3441:ℝ)/2350) = ((3441:ℝ)/1175) by norm_num]
      obtain ⟨-, h1hi⟩ := exp_bounds_quart (x := ((3611:ℝ)/1175)) (lo := (21.61076:ℝ)) (hi := (21.61077:ℝ))
              (by norm_num) (by norm_num)
              (by norm_num [expErr, Finset.sum_range_succ])
              (by norm_num [expErr, Finset.sum_range_succ])
      obtain ⟨h2lo, -⟩ := exp_bounds_quart (x := ((3441:ℝ)/1175)) (lo := (18.69975:ℝ)) (hi := (18.69976:ℝ))
              (by norm_num) (by norm_num)
              (by norm_num [expErr, Finset.sum_range_succ])
              (by norm_num [expErr, Finset.sum_range_succ])
      norm_num [CertSlack]
      linarith [h1hi, h2lo]
    · -- rowB 4 : (2.35, 0.164, 3.69)
      rw [h]
      rw [show (3.69:ℝ) / (2.35:ℝ) = ((369:ℝ)/235) by norm_num,
          show ((3.69:ℝ) - (0.164:ℝ)) / (2.35:ℝ) = ((3526:ℝ)/2350) by norm_num]
      rw [hb72G_closed (by norm_num : ((369:ℝ)/235) ≠ 0),
          hb72G_closed (by norm_num : ((3526:ℝ)/2350) ≠ 0)]
      rw [show 2 * ((369:ℝ)/235) = ((738:ℝ)/235) by norm_num,
          show 2 * ((3526:ℝ)/2350) = ((3526:ℝ)/1175) by norm_num]
      obtain ⟨-, h1hi⟩ := exp_bounds_quart (x := ((738:ℝ)/235)) (lo := (23.11370:ℝ)) (hi := (23.11371:ℝ))
              (by norm_num) (by norm_num)
              (by norm_num [expErr, Finset.sum_range_succ])
              (by norm_num [expErr, Finset.sum_range_succ])
      obtain ⟨h2lo, -⟩ := exp_bounds_quart (x := ((3526:ℝ)/1175)) (lo := (20.10263:ℝ)) (hi := (20.10264:ℝ))
              (by norm_num) (by norm_num)
              (by norm_num [expErr, Finset.sum_range_succ])
              (by norm_num [expErr, Finset.sum_range_succ])
      norm_num [CertSlack]
      linarith [h1hi, h2lo]
    · -- rowB 5 : (2.35, 0.158, 3.78)
      rw [h]
      rw [show (3.78:ℝ) / (2.35:ℝ) = ((378:ℝ)/235) by norm_num,
          show ((3.78:ℝ) - (0.158:ℝ)) / (2.35:ℝ) = ((3622:ℝ)/2350) by norm_num]
      rw [hb72G_closed (by norm_num : ((378:ℝ)/235) ≠ 0),
          hb72G_closed (by norm_num : ((3622:ℝ)/2350) ≠ 0)]
      rw [show 2 * ((378:ℝ)/235) = ((756:ℝ)/235) by norm_num,
          show 2 * ((3622:ℝ)/2350) = ((3622:ℝ)/1175) by norm_num]
      obtain ⟨-, h1hi⟩ := exp_bounds_quart (x := ((756:ℝ)/235)) (lo := (24.95367:ℝ)) (hi := (24.95368:ℝ))
              (by norm_num) (by norm_num)
              (by norm_num [expErr, Finset.sum_range_succ])
              (by norm_num [expErr, Finset.sum_range_succ])
      obtain ⟨h2lo, -⟩ := exp_bounds_quart (x := ((3622:ℝ)/1175)) (lo := (21.81402:ℝ)) (hi := (21.81403:ℝ))
              (by norm_num) (by norm_num)
              (by norm_num [expErr, Finset.sum_range_succ])
              (by norm_num [expErr, Finset.sum_range_succ])
      norm_num [CertSlack]
      linarith [h1hi, h2lo]
    · -- rowB 6 : (2.4, 0.151, 3.883)
      rw [h]
      rw [show (3.883:ℝ) / (2.4:ℝ) = ((3883:ℝ)/2400) by norm_num,
          show ((3.883:ℝ) - (0.151:ℝ)) / (2.4:ℝ) = ((311:ℝ)/200) by norm_num]
      rw [hb72G_closed (by norm_num : ((3883:ℝ)/2400) ≠ 0),
          hb72G_closed (by norm_num : ((311:ℝ)/200) ≠ 0)]
      rw [show 2 * ((3883:ℝ)/2400) = ((3883:ℝ)/1200) by norm_num,
          show 2 * ((311:ℝ)/200) = ((311:ℝ)/100) by norm_num]
      obtain ⟨-, h1hi⟩ := exp_bounds_quart (x := ((3883:ℝ)/1200)) (lo := (25.42755:ℝ)) (hi := (25.42756:ℝ))
              (by norm_num) (by norm_num)
              (by norm_num [expErr, Finset.sum_range_succ])
              (by norm_num [expErr, Finset.sum_range_succ])
      obtain ⟨h2lo, -⟩ := exp_bounds_quart (x := ((311:ℝ)/100)) (lo := (22.42104:ℝ)) (hi := (22.42105:ℝ))
              (by norm_num) (by norm_num)
              (by norm_num [expErr, Finset.sum_range_succ])
              (by norm_num [expErr, Finset.sum_range_succ])
      norm_num [CertSlack]
      linarith [h1hi, h2lo]
  · simp only [rowC, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with h | h | h | h | h | h
    · -- rowC 1 : (2.4, 0.144, 4.001)
      rw [h]
      rw [show (4.001:ℝ) / (2.4:ℝ) = ((4001:ℝ)/2400) by norm_num,
          show ((4.001:ℝ) - (0.144:ℝ)) / (2.4:ℝ) = ((3857:ℝ)/2400) by norm_num]
      rw [hb72G_closed (by norm_num : ((4001:ℝ)/2400) ≠ 0),
          hb72G_closed (by norm_num : ((3857:ℝ)/2400) ≠ 0)]
      rw [show 2 * ((4001:ℝ)/2400) = ((4001:ℝ)/1200) by norm_num,
          show 2 * ((3857:ℝ)/2400) = ((3857:ℝ)/1200) by norm_num]
      obtain ⟨-, h1hi⟩ := exp_bounds_quart (x := ((4001:ℝ)/1200)) (lo := (28.05499:ℝ)) (hi := (28.055:ℝ))
              (by norm_num) (by norm_num)
              (by norm_num [expErr, Finset.sum_range_succ])
              (by norm_num [expErr, Finset.sum_range_succ])
      obtain ⟨h2lo, -⟩ := exp_bounds_quart (x := ((3857:ℝ)/1200)) (lo := (24.88254:ℝ)) (hi := (24.88255:ℝ))
              (by norm_num) (by norm_num)
              (by norm_num [expErr, Finset.sum_range_succ])
              (by norm_num [expErr, Finset.sum_range_succ])
      norm_num [CertSlack]
      linarith [h1hi, h2lo]
    · -- rowC 2 : (2.4, 0.135, 4.136)
      rw [h]
      rw [show (4.136:ℝ) / (2.4:ℝ) = ((517:ℝ)/300) by norm_num,
          show ((4.136:ℝ) - (0.135:ℝ)) / (2.4:ℝ) = ((4001:ℝ)/2400) by norm_num]
      rw [hb72G_closed (by norm_num : ((517:ℝ)/300) ≠ 0),
          hb72G_closed (by norm_num : ((4001:ℝ)/2400) ≠ 0)]
      rw [show 2 * ((517:ℝ)/300) = ((517:ℝ)/150) by norm_num,
          show 2 * ((4001:ℝ)/2400) = ((4001:ℝ)/1200) by norm_num]
      obtain ⟨-, h1hi⟩ := exp_bounds_quart (x := ((517:ℝ)/150)) (lo := (31.39556:ℝ)) (hi := (31.39557:ℝ))
              (by norm_num) (by norm_num)
              (by norm_num [expErr, Finset.sum_range_succ])
              (by norm_num [expErr, Finset.sum_range_succ])
      obtain ⟨h2lo, -⟩ := exp_bounds_quart (x := ((4001:ℝ)/1200)) (lo := (28.05499:ℝ)) (hi := (28.055:ℝ))
              (by norm_num) (by norm_num)
              (by norm_num [expErr, Finset.sum_range_succ])
              (by norm_num [expErr, Finset.sum_range_succ])
      norm_num [CertSlack]
      linarith [h1hi, h2lo]
    · -- rowC 3 : (2.4, 0.126, 4.291)
      rw [h]
      rw [show (4.291:ℝ) / (2.4:ℝ) = ((4291:ℝ)/2400) by norm_num,
          show ((4.291:ℝ) - (0.126:ℝ)) / (2.4:ℝ) = ((833:ℝ)/480) by norm_num]
      rw [hb72G_closed (by norm_num : ((4291:ℝ)/2400) ≠ 0),
          hb72G_closed (by norm_num : ((833:ℝ)/480) ≠ 0)]
      rw [show 2 * ((4291:ℝ)/2400) = ((4291:ℝ)/1200) by norm_num,
          show 2 * ((833:ℝ)/480) = ((833:ℝ)/240) by norm_num]
      obtain ⟨-, h1hi⟩ := exp_bounds_quart (x := ((4291:ℝ)/1200)) (lo := (35.72437:ℝ)) (hi := (35.72438:ℝ))
              (by norm_num) (by norm_num)
              (by norm_num [expErr, Finset.sum_range_succ])
              (by norm_num [expErr, Finset.sum_range_succ])
      obtain ⟨h2lo, -⟩ := exp_bounds_quart (x := ((833:ℝ)/240)) (lo := (32.16353:ℝ)) (hi := (32.16354:ℝ))
              (by norm_num) (by norm_num)
              (by norm_num [expErr, Finset.sum_range_succ])
              (by norm_num [expErr, Finset.sum_range_succ])
      norm_num [CertSlack]
      linarith [h1hi, h2lo]
    · -- rowC 4 : (2.45, 0.117, 4.469)
      rw [h]
      rw [show (4.469:ℝ) / (2.45:ℝ) = ((4469:ℝ)/2450) by norm_num,
          show ((4.469:ℝ) - (0.117:ℝ)) / (2.45:ℝ) = ((4352:ℝ)/2450) by norm_num]
      rw [hb72G_closed (by norm_num : ((4469:ℝ)/2450) ≠ 0),
          hb72G_closed (by norm_num : ((4352:ℝ)/2450) ≠ 0)]
      rw [show 2 * ((4469:ℝ)/2450) = ((4469:ℝ)/1225) by norm_num,
          show 2 * ((4352:ℝ)/2450) = ((4352:ℝ)/1225) by norm_num]
      obtain ⟨-, h1hi⟩ := exp_bounds_quart (x := ((4469:ℝ)/1225)) (lo := (38.40406:ℝ)) (hi := (38.40407:ℝ))
              (by norm_num) (by norm_num)
              (by norm_num [expErr, Finset.sum_range_succ])
              (by norm_num [expErr, Finset.sum_range_succ])
      obtain ⟨h2lo, -⟩ := exp_bounds_quart (x := ((4352:ℝ)/1225)) (lo := (34.9058:ℝ)) (hi := (34.90581:ℝ))
              (by norm_num) (by norm_num)
              (by norm_num [expErr, Finset.sum_range_succ])
              (by norm_num [expErr, Finset.sum_range_succ])
      norm_num [CertSlack]
      linarith [h1hi, h2lo]
    · -- rowC 5 : (2.45, 0.107, 4.674)
      rw [h]
      rw [show (4.674:ℝ) / (2.45:ℝ) = ((2337:ℝ)/1225) by norm_num,
          show ((4.674:ℝ) - (0.107:ℝ)) / (2.45:ℝ) = ((4567:ℝ)/2450) by norm_num]
      rw [hb72G_closed (by norm_num : ((2337:ℝ)/1225) ≠ 0),
          hb72G_closed (by norm_num : ((4567:ℝ)/2450) ≠ 0)]
      rw [show 2 * ((2337:ℝ)/1225) = ((4674:ℝ)/1225) by norm_num,
          show 2 * ((4567:ℝ)/2450) = ((4567:ℝ)/1225) by norm_num]
      obtain ⟨-, h1hi⟩ := exp_bounds_quart (x := ((4674:ℝ)/1225)) (lo := (45.39991:ℝ)) (hi := (45.39992:ℝ))
              (by norm_num) (by norm_num)
              (by norm_num [expErr, Finset.sum_range_succ])
              (by norm_num [expErr, Finset.sum_range_succ])
      obtain ⟨h2lo, -⟩ := exp_bounds_quart (x := ((4567:ℝ)/1225)) (lo := (41.60262:ℝ)) (hi := (41.60263:ℝ))
              (by norm_num) (by norm_num)
              (by norm_num [expErr, Finset.sum_range_succ])
              (by norm_num [expErr, Finset.sum_range_succ])
      norm_num [CertSlack]
      linarith [h1hi, h2lo]
    · -- rowC 6 : (2.5, 0.097, 4.909)
      rw [h]
      rw [show (4.909:ℝ) / (2.5:ℝ) = ((4909:ℝ)/2500) by norm_num,
          show ((4.909:ℝ) - (0.097:ℝ)) / (2.5:ℝ) = ((1203:ℝ)/625) by norm_num]
      rw [hb72G_closed (by norm_num : ((4909:ℝ)/2500) ≠ 0),
          hb72G_closed (by norm_num : ((1203:ℝ)/625) ≠ 0)]
      rw [show 2 * ((4909:ℝ)/2500) = ((4909:ℝ)/1250) by norm_num,
          show 2 * ((1203:ℝ)/625) = ((2406:ℝ)/625) by norm_num]
      obtain ⟨-, h1hi⟩ := exp_bounds_quart (x := ((4909:ℝ)/1250)) (lo := (50.76463:ℝ)) (hi := (50.76464:ℝ))
              (by norm_num) (by norm_num)
              (by norm_num [expErr, Finset.sum_range_succ])
              (by norm_num [expErr, Finset.sum_range_succ])
      obtain ⟨h2lo, -⟩ := exp_bounds_quart (x := ((2406:ℝ)/625)) (lo := (46.97426:ℝ)) (hi := (46.97427:ℝ))
              (by norm_num) (by norm_num)
              (by norm_num [expErr, Finset.sum_range_succ])
              (by norm_num [expErr, Finset.sum_range_succ])
      norm_num [CertSlack]
      linarith [h1hi, h2lo]

end Work.ZeroFreeTables
