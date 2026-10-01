/-
# ZeroFreeTables — t23RowF

The sixteen **gap-filling rows** of `rowF` of Tables 2 and 3, certified with the constant
`CertSlack` (see `Submission/Work/ZeroFreeTables/t23ExpBounds.lean` for the recipe and the
numerical data, and `Submission/Work/ZeroFreeTables/t23Gclosed.lean` for the closed form of `G`).

For every row `(λ, b, v)` of `rowF` we must show

`(1/15)·(G (v/λ) − G ((v−b)/λ)) < 8/9 − CertSlack·(16λ/15)`,

where `G x = ∫₀² g(u) e^{xu} du`.  By `hb72G_closed`,

`G x = (120 e^{2x}(x−1)² − 32x⁵ + 80x³ + 120x² − 120)/x⁶  (x ≠ 0)`,

and on every row `x > 1`, so the coefficient `120(x−1)²/x⁶` of `e^{2x}` is positive.  Hence an
**upper** bound `hi1` for `e^{2v/λ}` and a **lower** bound `lo2` for `e^{2(v−b)/λ}` reduce the
certificate to rational arithmetic (`exp_bounds_quart`, two-sided Taylor bounds for `exp` on
`[0,4]`).  Rows 13–16 have `2v/λ > 4`: there `exp_bounds_quart` is applied to `2v/λ − 4` and the
bridge `exp_le_of_quart_sub` / `le_exp_of_quart_sub` (with `e⁴ ≤ 54.5981501`, `54.5981500 ≤ e⁴`)
converts the bound into one on `e^{2v/λ}`.

The bounds are `5`-decimal roundings of the exact quart bounds: for rows 1–12,
`hi1 = ⌈(S(2v/λ)+err)⁴⌉₅` and `lo2 = ⌊(S(2(v−b)/λ)−err)⁴⌋₅`; for rows 13–16,
`hi1 = ⌈54.5981501·hi1'⌉₅` and `lo2 = ⌊54.5981500·lo2'⌋₅` where `hi1'`/`lo2'` are the
corresponding quart bounds at `2v/λ − 4`.  Every row was checked by exact rational arithmetic;
the margin at the end is at least `7·10⁻³`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.t23Defs
import Submission.Work.ZeroFreeTables.t23Gclosed
import Submission.Work.ZeroFreeTables.t23ExpBounds

open scoped BigOperators
noncomputable section

namespace Work.ZeroFreeTables

theorem t23RowF : ∀ p : ℝ × ℝ × ℝ, p ∈ Work.ZeroFreeTables.rowF →
    (1 / 15) * (Work.ZeroFreeTables.hb72G (p.2.2 / p.1) - Work.ZeroFreeTables.hb72G ((p.2.2 - p.2.1) / p.1))
      < 8 / 9 - Work.ZeroFreeTables.CertSlack * (16 * p.1 / 15) := by
  intro p hp
  simp only [rowF, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rw [h]
    rw [show (1673:ℝ)/500 / ((23:ℝ)/10) = ((1673:ℝ)/1150) by norm_num,
        show ((1673:ℝ)/500 - ((588:ℝ)/3125)) / ((23:ℝ)/10) = ((39473:ℝ)/28750) by norm_num]
    rw [hb72G_closed (by norm_num : (((1673:ℝ)/1150)) ≠ 0),
        hb72G_closed (by norm_num : (((39473:ℝ)/28750)) ≠ 0)]
    rw [show 2 * ((1673:ℝ)/1150) = ((1673:ℝ)/575) by norm_num,
        show 2 * ((39473:ℝ)/28750) = ((39473:ℝ)/14375) by norm_num]
    obtain ⟨-, h1hi⟩ := exp_bounds_quart (x := ((1673:ℝ)/575)) (lo := (1834881/100000:ℝ)) (hi := (917441/50000:ℝ))
        (by norm_num) (by norm_num)
        (by norm_num [expErr, Finset.sum_range_succ])
        (by norm_num [expErr, Finset.sum_range_succ])
    obtain ⟨h2lo, -⟩ := exp_bounds_quart (x := ((39473:ℝ)/14375)) (lo := (1557937/100000:ℝ)) (hi := (778969/50000:ℝ))
        (by norm_num) (by norm_num)
        (by norm_num [expErr, Finset.sum_range_succ])
        (by norm_num [expErr, Finset.sum_range_succ])
    norm_num [CertSlack]
    linarith [h1hi, h2lo]
  · rw [h]
    rw [show (3389:ℝ)/1000 / ((23:ℝ)/10) = ((3389:ℝ)/2300) by norm_num,
        show ((3389:ℝ)/1000 - ((9217:ℝ)/50000)) / ((23:ℝ)/10) = ((160233:ℝ)/115000) by norm_num]
    rw [hb72G_closed (by norm_num : (((3389:ℝ)/2300)) ≠ 0),
        hb72G_closed (by norm_num : (((160233:ℝ)/115000)) ≠ 0)]
    rw [show 2 * ((3389:ℝ)/2300) = ((3389:ℝ)/1150) by norm_num,
        show 2 * ((160233:ℝ)/115000) = ((160233:ℝ)/57500) by norm_num]
    obtain ⟨-, h1hi⟩ := exp_bounds_quart (x := ((3389:ℝ)/1150)) (lo := (1904789/100000:ℝ)) (hi := (190479/10000:ℝ))
        (by norm_num) (by norm_num)
        (by norm_num [expErr, Finset.sum_range_succ])
        (by norm_num [expErr, Finset.sum_range_succ])
    obtain ⟨h2lo, -⟩ := exp_bounds_quart (x := ((160233:ℝ)/57500)) (lo := (811337/50000:ℝ)) (hi := (64907/4000:ℝ))
        (by norm_num) (by norm_num)
        (by norm_num [expErr, Finset.sum_range_succ])
        (by norm_num [expErr, Finset.sum_range_succ])
    norm_num [CertSlack]
    linarith [h1hi, h2lo]
  · rw [h]
    rw [show (3433:ℝ)/1000 / ((47:ℝ)/20) = ((3433:ℝ)/2350) by norm_num,
        show ((3433:ℝ)/1000 - ((3603:ℝ)/20000)) / ((47:ℝ)/20) = ((65057:ℝ)/47000) by norm_num]
    rw [hb72G_closed (by norm_num : (((3433:ℝ)/2350)) ≠ 0),
        hb72G_closed (by norm_num : (((65057:ℝ)/47000)) ≠ 0)]
    rw [show 2 * ((3433:ℝ)/2350) = ((3433:ℝ)/1175) by norm_num,
        show 2 * ((65057:ℝ)/47000) = ((65057:ℝ)/23500) by norm_num]
    obtain ⟨-, h1hi⟩ := exp_bounds_quart (x := ((3433:ℝ)/1175)) (lo := (1857287/100000:ℝ)) (hi := (232161/12500:ℝ))
        (by norm_num) (by norm_num)
        (by norm_num [expErr, Finset.sum_range_succ])
        (by norm_num [expErr, Finset.sum_range_succ])
    obtain ⟨h2lo, -⟩ := exp_bounds_quart (x := ((65057:ℝ)/23500)) (lo := (398321/25000:ℝ)) (hi := (318657/20000:ℝ))
        (by norm_num) (by norm_num)
        (by norm_num [expErr, Finset.sum_range_succ])
        (by norm_num [expErr, Finset.sum_range_succ])
    norm_num [CertSlack]
    linarith [h1hi, h2lo]
  · rw [h]
    rw [show (3489:ℝ)/1000 / ((47:ℝ)/20) = ((3489:ℝ)/2350) by norm_num,
        show ((3489:ℝ)/1000 - ((2193:ℝ)/12500)) / ((47:ℝ)/20) = ((82839:ℝ)/58750) by norm_num]
    rw [hb72G_closed (by norm_num : (((3489:ℝ)/2350)) ≠ 0),
        hb72G_closed (by norm_num : (((82839:ℝ)/58750)) ≠ 0)]
    rw [show 2 * ((3489:ℝ)/2350) = ((3489:ℝ)/1175) by norm_num,
        show 2 * ((82839:ℝ)/58750) = ((82839:ℝ)/29375) by norm_num]
    obtain ⟨-, h1hi⟩ := exp_bounds_quart (x := ((3489:ℝ)/1175)) (lo := (486987/25000:ℝ)) (hi := (1947949/100000:ℝ))
        (by norm_num) (by norm_num)
        (by norm_num [expErr, Finset.sum_range_succ])
        (by norm_num [expErr, Finset.sum_range_succ])
    obtain ⟨h2lo, -⟩ := exp_bounds_quart (x := ((82839:ℝ)/29375)) (lo := (167777/10000:ℝ)) (hi := (1677771/100000:ℝ))
        (by norm_num) (by norm_num)
        (by norm_num [expErr, Finset.sum_range_succ])
        (by norm_num [expErr, Finset.sum_range_succ])
    norm_num [CertSlack]
    linarith [h1hi, h2lo]
  · rw [h]
    rw [show (3547:ℝ)/1000 / ((47:ℝ)/20) = ((3547:ℝ)/2350) by norm_num,
        show ((3547:ℝ)/1000 - ((17017:ℝ)/100000)) / ((47:ℝ)/20) = ((337683:ℝ)/235000) by norm_num]
    rw [hb72G_closed (by norm_num : (((3547:ℝ)/2350)) ≠ 0),
        hb72G_closed (by norm_num : (((337683:ℝ)/235000)) ≠ 0)]
    rw [show 2 * ((3547:ℝ)/2350) = ((3547:ℝ)/1175) by norm_num,
        show 2 * ((337683:ℝ)/235000) = ((337683:ℝ)/117500) by norm_num]
    obtain ⟨-, h1hi⟩ := exp_bounds_quart (x := ((3547:ℝ)/1175)) (lo := (1023257/50000:ℝ)) (hi := (409303/20000:ℝ))
        (by norm_num) (by norm_num)
        (by norm_num [expErr, Finset.sum_range_succ])
        (by norm_num [expErr, Finset.sum_range_succ])
    obtain ⟨h2lo, -⟩ := exp_bounds_quart (x := ((337683:ℝ)/117500)) (lo := (1770589/100000:ℝ)) (hi := (177059/10000:ℝ))
        (by norm_num) (by norm_num)
        (by norm_num [expErr, Finset.sum_range_succ])
        (by norm_num [expErr, Finset.sum_range_succ])
    norm_num [CertSlack]
    linarith [h1hi, h2lo]
  · rw [h]
    rw [show (3619:ℝ)/1000 / ((47:ℝ)/20) = ((77:ℝ)/50) by norm_num,
        show ((3619:ℝ)/1000 - ((411:ℝ)/2500)) / ((47:ℝ)/20) = ((17273:ℝ)/11750) by norm_num]
    rw [hb72G_closed (by norm_num : (((77:ℝ)/50)) ≠ 0),
        hb72G_closed (by norm_num : (((17273:ℝ)/11750)) ≠ 0)]
    rw [show 2 * ((77:ℝ)/50) = ((77:ℝ)/25) by norm_num,
        show 2 * ((17273:ℝ)/11750) = ((17273:ℝ)/5875) by norm_num]
    obtain ⟨-, h1hi⟩ := exp_bounds_quart (x := ((77:ℝ)/25)) (lo := (13599/625:ℝ)) (hi := (2175841/100000:ℝ))
        (by norm_num) (by norm_num)
        (by norm_num [expErr, Finset.sum_range_succ])
        (by norm_num [expErr, Finset.sum_range_succ])
    obtain ⟨h2lo, -⟩ := exp_bounds_quart (x := ((17273:ℝ)/5875)) (lo := (378349/20000:ℝ)) (hi := (945873/50000:ℝ))
        (by norm_num) (by norm_num)
        (by norm_num [expErr, Finset.sum_range_succ])
        (by norm_num [expErr, Finset.sum_range_succ])
    norm_num [CertSlack]
    linarith [h1hi, h2lo]
  · rw [h]
    rw [show (1847:ℝ)/500 / ((47:ℝ)/20) = ((1847:ℝ)/1175) by norm_num,
        show ((1847:ℝ)/500 - ((15803:ℝ)/100000)) / ((47:ℝ)/20) = ((353597:ℝ)/235000) by norm_num]
    rw [hb72G_closed (by norm_num : (((1847:ℝ)/1175)) ≠ 0),
        hb72G_closed (by norm_num : (((353597:ℝ)/235000)) ≠ 0)]
    rw [show 2 * ((1847:ℝ)/1175) = ((3694:ℝ)/1175) by norm_num,
        show 2 * ((353597:ℝ)/235000) = ((353597:ℝ)/117500) by norm_num]
    obtain ⟨-, h1hi⟩ := exp_bounds_quart (x := ((3694:ℝ)/1175)) (lo := (2319251/100000:ℝ)) (hi := (579813/25000:ℝ))
        (by norm_num) (by norm_num)
        (by norm_num [expErr, Finset.sum_range_succ])
        (by norm_num [expErr, Finset.sum_range_succ])
    obtain ⟨h2lo, -⟩ := exp_bounds_quart (x := ((353597:ℝ)/117500)) (lo := (2027393/100000:ℝ)) (hi := (1013697/50000:ℝ))
        (by norm_num) (by norm_num)
        (by norm_num [expErr, Finset.sum_range_succ])
        (by norm_num [expErr, Finset.sum_range_succ])
    norm_num [CertSlack]
    linarith [h1hi, h2lo]
  · rw [h]
    rw [show (473:ℝ)/125 / ((12:ℝ)/5) = ((473:ℝ)/300) by norm_num,
        show ((473:ℝ)/125 - ((3777:ℝ)/25000)) / ((12:ℝ)/5) = ((90823:ℝ)/60000) by norm_num]
    rw [hb72G_closed (by norm_num : (((473:ℝ)/300)) ≠ 0),
        hb72G_closed (by norm_num : (((90823:ℝ)/60000)) ≠ 0)]
    rw [show 2 * ((473:ℝ)/300) = ((473:ℝ)/150) by norm_num,
        show 2 * ((90823:ℝ)/60000) = ((90823:ℝ)/30000) by norm_num]
    obtain ⟨-, h1hi⟩ := exp_bounds_quart (x := ((473:ℝ)/150)) (lo := (1170699/50000:ℝ)) (hi := (2341399/100000:ℝ))
        (by norm_num) (by norm_num)
        (by norm_num [expErr, Finset.sum_range_succ])
        (by norm_num [expErr, Finset.sum_range_succ])
    obtain ⟨h2lo, -⟩ := exp_bounds_quart (x := ((90823:ℝ)/30000)) (lo := (2064417/100000:ℝ)) (hi := (1032209/50000:ℝ))
        (by norm_num) (by norm_num)
        (by norm_num [expErr, Finset.sum_range_succ])
        (by norm_num [expErr, Finset.sum_range_succ])
    norm_num [CertSlack]
    linarith [h1hi, h2lo]
  · rw [h]
    rw [show (501:ℝ)/125 / ((12:ℝ)/5) = ((167:ℝ)/100) by norm_num,
        show ((501:ℝ)/125 - ((13527:ℝ)/100000)) / ((12:ℝ)/5) = ((129091:ℝ)/80000) by norm_num]
    rw [hb72G_closed (by norm_num : (((167:ℝ)/100)) ≠ 0),
        hb72G_closed (by norm_num : (((129091:ℝ)/80000)) ≠ 0)]
    rw [show 2 * ((167:ℝ)/100) = ((167:ℝ)/50) by norm_num,
        show 2 * ((129091:ℝ)/80000) = ((129091:ℝ)/40000) by norm_num]
    obtain ⟨-, h1hi⟩ := exp_bounds_quart (x := ((167:ℝ)/50)) (lo := (352739/12500:ℝ)) (hi := (2821913/100000:ℝ))
        (by norm_num) (by norm_num)
        (by norm_num [expErr, Finset.sum_range_succ])
        (by norm_num [expErr, Finset.sum_range_succ])
    obtain ⟨h2lo, -⟩ := exp_bounds_quart (x := ((129091:ℝ)/40000)) (lo := (1260543/50000:ℝ)) (hi := (2521087/100000:ℝ))
        (by norm_num) (by norm_num)
        (by norm_num [expErr, Finset.sum_range_succ])
        (by norm_num [expErr, Finset.sum_range_succ])
    norm_num [CertSlack]
    linarith [h1hi, h2lo]
  · rw [h]
    rw [show (2073:ℝ)/500 / ((12:ℝ)/5) = ((691:ℝ)/400) by norm_num,
        show ((2073:ℝ)/500 - ((3161:ℝ)/25000)) / ((12:ℝ)/5) = ((100489:ℝ)/60000) by norm_num]
    rw [hb72G_closed (by norm_num : (((691:ℝ)/400)) ≠ 0),
        hb72G_closed (by norm_num : (((100489:ℝ)/60000)) ≠ 0)]
    rw [show 2 * ((691:ℝ)/400) = ((691:ℝ)/200) by norm_num,
        show 2 * ((100489:ℝ)/60000) = ((100489:ℝ)/30000) by norm_num]
    obtain ⟨-, h1hi⟩ := exp_bounds_quart (x := ((691:ℝ)/200)) (lo := (791457/25000:ℝ)) (hi := (3165829/100000:ℝ))
        (by norm_num) (by norm_num)
        (by norm_num [expErr, Finset.sum_range_succ])
        (by norm_num [expErr, Finset.sum_range_succ])
    obtain ⟨h2lo, -⟩ := exp_bounds_quart (x := ((100489:ℝ)/30000)) (lo := (712307/25000:ℝ)) (hi := (2849229/100000:ℝ))
        (by norm_num) (by norm_num)
        (by norm_num [expErr, Finset.sum_range_succ])
        (by norm_num [expErr, Finset.sum_range_succ])
    norm_num [CertSlack]
    linarith [h1hi, h2lo]
  · rw [h]
    rw [show (859:ℝ)/200 / ((49:ℝ)/20) = ((859:ℝ)/490) by norm_num,
        show ((859:ℝ)/200 - ((11701:ℝ)/100000)) / ((49:ℝ)/20) = ((417799:ℝ)/245000) by norm_num]
    rw [hb72G_closed (by norm_num : (((859:ℝ)/490)) ≠ 0),
        hb72G_closed (by norm_num : (((417799:ℝ)/245000)) ≠ 0)]
    rw [show 2 * ((859:ℝ)/490) = ((859:ℝ)/245) by norm_num,
        show 2 * ((417799:ℝ)/245000) = ((417799:ℝ)/122500) by norm_num]
    obtain ⟨-, h1hi⟩ := exp_bounds_quart (x := ((859:ℝ)/245)) (lo := (1665941/50000:ℝ)) (hi := (3331883/100000:ℝ))
        (by norm_num) (by norm_num)
        (by norm_num [expErr, Finset.sum_range_succ])
        (by norm_num [expErr, Finset.sum_range_succ])
    obtain ⟨h2lo, -⟩ := exp_bounds_quart (x := ((417799:ℝ)/122500)) (lo := (3028353/100000:ℝ)) (hi := (1514177/50000:ℝ))
        (by norm_num) (by norm_num)
        (by norm_num [expErr, Finset.sum_range_succ])
        (by norm_num [expErr, Finset.sum_range_succ])
    norm_num [CertSlack]
    linarith [h1hi, h2lo]
  · rw [h]
    rw [show (4473:ℝ)/1000 / ((49:ℝ)/20) = ((639:ℝ)/350) by norm_num,
        show ((4473:ℝ)/1000 - ((2141:ℝ)/20000)) / ((49:ℝ)/20) = ((87319:ℝ)/49000) by norm_num]
    rw [hb72G_closed (by norm_num : (((639:ℝ)/350)) ≠ 0),
        hb72G_closed (by norm_num : (((87319:ℝ)/49000)) ≠ 0)]
    rw [show 2 * ((639:ℝ)/350) = ((639:ℝ)/175) by norm_num,
        show 2 * ((87319:ℝ)/49000) = ((87319:ℝ)/24500) by norm_num]
    obtain ⟨-, h1hi⟩ := exp_bounds_quart (x := ((639:ℝ)/175)) (lo := (1926483/50000:ℝ)) (hi := (3852967/100000:ℝ))
        (by norm_num) (by norm_num)
        (by norm_num [expErr, Finset.sum_range_succ])
        (by norm_num [expErr, Finset.sum_range_succ])
    obtain ⟨h2lo, -⟩ := exp_bounds_quart (x := ((87319:ℝ)/24500)) (lo := (3530557/100000:ℝ)) (hi := (1765279/50000:ℝ))
        (by norm_num) (by norm_num)
        (by norm_num [expErr, Finset.sum_range_succ])
        (by norm_num [expErr, Finset.sum_range_succ])
    norm_num [CertSlack]
    linarith [h1hi, h2lo]
  · rw [h]
    rw [show (648:ℝ)/125 / ((51:ℝ)/20) = ((864:ℝ)/425) by norm_num,
        show ((648:ℝ)/125 - ((7503:ℝ)/100000)) / ((51:ℝ)/20) = ((170299:ℝ)/85000) by norm_num]
    rw [hb72G_closed (by norm_num : (((864:ℝ)/425)) ≠ 0),
        hb72G_closed (by norm_num : (((170299:ℝ)/85000)) ≠ 0)]
    rw [show 2 * ((864:ℝ)/425) = ((1728:ℝ)/425) by norm_num,
        show 2 * ((170299:ℝ)/85000) = ((170299:ℝ)/42500) by norm_num]
    obtain ⟨-, h1quart⟩ := exp_bounds_quart (x := (((1728:ℝ)/425) - 4)) (lo := (10681/10000:ℝ)) (hi := (106811/100000:ℝ))
        (by norm_num) (by norm_num)
        (by norm_num [expErr, Finset.sum_range_succ])
        (by norm_num [expErr, Finset.sum_range_succ])
    have h1hi : Real.exp ((1728:ℝ)/425) ≤ (1457921/25000:ℝ) := exp_le_of_quart_sub h1quart (by norm_num)
    obtain ⟨h2quart, -⟩ := exp_bounds_quart (x := (((170299:ℝ)/42500) - 4)) (lo := (50353/50000:ℝ)) (hi := (100707/100000:ℝ))
        (by norm_num) (by norm_num)
        (by norm_num [expErr, Finset.sum_range_succ])
        (by norm_num [expErr, Finset.sum_range_succ])
    have h2lo : (5498361/100000:ℝ) ≤ Real.exp ((170299:ℝ)/42500) := le_exp_of_quart_sub h2quart (by norm_num) (by norm_num)
    norm_num [CertSlack]
    linarith [h1hi, h2lo]
  · rw [h]
    rw [show (5501:ℝ)/1000 / ((51:ℝ)/20) = ((5501:ℝ)/2550) by norm_num,
        show ((5501:ℝ)/1000 - ((3211:ℝ)/50000)) / ((51:ℝ)/20) = ((90613:ℝ)/42500) by norm_num]
    rw [hb72G_closed (by norm_num : (((5501:ℝ)/2550)) ≠ 0),
        hb72G_closed (by norm_num : (((90613:ℝ)/42500)) ≠ 0)]
    rw [show 2 * ((5501:ℝ)/2550) = ((5501:ℝ)/1275) by norm_num,
        show 2 * ((90613:ℝ)/42500) = ((90613:ℝ)/21250) by norm_num]
    obtain ⟨-, h1quart⟩ := exp_bounds_quart (x := (((5501:ℝ)/1275) - 4)) (lo := (68479/50000:ℝ)) (hi := (136959/100000:ℝ))
        (by norm_num) (by norm_num)
        (by norm_num [expErr, Finset.sum_range_succ])
        (by norm_num [expErr, Finset.sum_range_succ])
    have h1hi : Real.exp ((5501:ℝ)/1275) ≤ (7477709/100000:ℝ) := exp_le_of_quart_sub h1quart (by norm_num)
    obtain ⟨h2quart, -⟩ := exp_bounds_quart (x := (((90613:ℝ)/21250) - 4)) (lo := (130231/100000:ℝ)) (hi := (16279/12500:ℝ))
        (by norm_num) (by norm_num)
        (by norm_num [expErr, Finset.sum_range_succ])
        (by norm_num [expErr, Finset.sum_range_succ])
    have h2lo : (7110371/100000:ℝ) ≤ Real.exp ((90613:ℝ)/21250) := le_exp_of_quart_sub h2quart (by norm_num) (by norm_num)
    norm_num [CertSlack]
    linarith [h1hi, h2lo]
  · rw [h]
    rw [show (7303:ℝ)/1000 / ((27:ℝ)/10) = ((7303:ℝ)/2700) by norm_num,
        show ((7303:ℝ)/1000 - ((2649:ℝ)/100000)) / ((27:ℝ)/10) = ((727651:ℝ)/270000) by norm_num]
    rw [hb72G_closed (by norm_num : (((7303:ℝ)/2700)) ≠ 0),
        hb72G_closed (by norm_num : (((727651:ℝ)/270000)) ≠ 0)]
    rw [show 2 * ((7303:ℝ)/2700) = ((7303:ℝ)/1350) by norm_num,
        show 2 * ((727651:ℝ)/270000) = ((727651:ℝ)/135000) by norm_num]
    obtain ⟨-, h1quart⟩ := exp_bounds_quart (x := (((7303:ℝ)/1350) - 4)) (lo := (409443/100000:ℝ)) (hi := (102361/25000:ℝ))
        (by norm_num) (by norm_num)
        (by norm_num [expErr, Finset.sum_range_succ])
        (by norm_num [expErr, Finset.sum_range_succ])
    have h1hi : Real.exp ((7303:ℝ)/1350) ≤ (4470977/20000:ℝ) := exp_le_of_quart_sub h1quart (by norm_num)
    obtain ⟨h2quart, -⟩ := exp_bounds_quart (x := (((727651:ℝ)/135000) - 4)) (lo := (401487/100000:ℝ)) (hi := (25093/6250:ℝ))
        (by norm_num) (by norm_num)
        (by norm_num [expErr, Finset.sum_range_succ])
        (by norm_num [expErr, Finset.sum_range_succ])
    have h2lo : (21920447/100000:ℝ) ≤ Real.exp ((727651:ℝ)/135000) := le_exp_of_quart_sub h2quart (by norm_num) (by norm_num)
    norm_num [CertSlack]
    linarith [h1hi, h2lo]
  · rw [h]
    rw [show (2047:ℝ)/200 / ((14:ℝ)/5) = ((2047:ℝ)/560) by norm_num,
        show ((2047:ℝ)/200 - ((313:ℝ)/50000)) / ((14:ℝ)/5) = ((511437:ℝ)/140000) by norm_num]
    rw [hb72G_closed (by norm_num : (((2047:ℝ)/560)) ≠ 0),
        hb72G_closed (by norm_num : (((511437:ℝ)/140000)) ≠ 0)]
    rw [show 2 * ((2047:ℝ)/560) = ((2047:ℝ)/280) by norm_num,
        show 2 * ((511437:ℝ)/140000) = ((511437:ℝ)/70000) by norm_num]
    obtain ⟨-, h1quart⟩ := exp_bounds_quart (x := (((2047:ℝ)/280) - 4)) (lo := (2740469/100000:ℝ)) (hi := (274047/10000:ℝ))
        (by norm_num) (by norm_num)
        (by norm_num [expErr, Finset.sum_range_succ])
        (by norm_num [expErr, Finset.sum_range_succ])
    have h1hi : Real.exp ((2047:ℝ)/280) ≤ (149624593/100000:ℝ) := exp_le_of_quart_sub h1quart (by norm_num)
    obtain ⟨h2quart, -⟩ := exp_bounds_quart (x := (((511437:ℝ)/70000) - 4)) (lo := (1364121/50000:ℝ)) (hi := (2728243/100000:ℝ))
        (by norm_num) (by norm_num)
        (by norm_num [expErr, Finset.sum_range_succ])
        (by norm_num [expErr, Finset.sum_range_succ])
    have h2lo : (29791393/20000:ℝ) ≤ Real.exp ((511437:ℝ)/70000) := le_exp_of_quart_sub h2quart (by norm_num) (by norm_num)
    norm_num [CertSlack]
    linarith [h1hi, h2lo]

end Work.ZeroFreeTables
