import Mathlib
import Submission.Work.FIPiChain.HasB
import Submission.Work.FIChain.Defs
import Submission.Work.FIChain.window_marginsC
import Submission.Work.FITop.BformAtilEqXsum
import Submission.Work.FITop.AtilTauPowFourLe
import Submission.Work.FITop.Defs
import Submission.ASP.S7c
import Submission.ASP.S8b
import Submission.ASP.S20
import Submission.ASP.S21
import Submission.ASP.S22
import Submission.ASP.S23
import Submission.ASP.S24
import Submission.ASP.S25
import Submission.Work.FITop.SingleDvdTauSqLe
import Submission.Work.FITop.WindowRangeMarginsChain
import Submission.Work.FITop.BprimeWindowDelta1
import Submission.Work.FITop.RangeCheckChain
import Submission.ASP.S30
import Submission.Work.FITop.WolkeSquarefreeTau
import Submission.Work.FITop.AdTauAggregate
import Submission.Work.FITop.SumIteDivDvd
import Submission.Work.FIChain.scale_factsC
import Submission.Work.FIChain.rhoWindowC_param
import Submission.Work.FITop.RhoWindowCProp41
import Submission.Work.FIChain.chainRangeFactsC
import Submission.Work.FIChain.zc_sharp_bounds

open Work.FIChain

namespace Work.FIPiChain

variable [HasBc]

/-! A **wider range fact** for the pinned scale `HasBc.val = 2^31 + 2`:
`Δ · ⌊e·Yc⌋² ≤ Dc`, where `Δ = Deltac x = ⌈x^{1/100}⌉` and `Dc x = ⌊x^{11/16}⌋`.

`Work.FIChain.chainRangeFactsC` gives the chain's own range facts, in particular
`Δ·⌊e·Yc⌋·⌊Yc⌋ ≤ Dc`.  The `§4–§7` bound for the `T₂`-sum (`Submission.ASP.Tsum2`) is needed at
`z`-positions up to `e·zc x HasBc.val`, i.e. the modulus range is `Δ·M·P` with `M ≤ ⌊e·Yc⌋` and
`P ≤ ⌊e·Yc⌋`, one extra factor `e` beyond the chain's own bound.  Since
`⌊e·Yc x HasBc.val⌋ ≤ 2e·x^{5/16}` and `Deltac x ≤ 2x^{1/100}`, the product is at most
`8e²·x^{1/100+5/8} = 8e²·x^{127/200}`, which is below `x^{11/16}/2` as soon as
`x^{11/16-127/200} = x^{21/400} ≥ 16e²`; the route of `chainRangeFactsC` (which uses
`FI_ev_rpow_ge_nat (21/400)`, `FI_ev_Dcut_lower`, `FI_ev_Delta1_le_two_Lam1` and the `Yc` sandwich
of `window_marginsC`) replays verbatim with these looser constants. -/

open Filter

noncomputable section

/-- **The arithmetic core.**  With `Δ ≤ 2·x^{1/100}`, `n ≤ e·Y`, `Y ≤ 3·x^{5/16}` and
`x^{21/400} ≥ 324` one gets `Δ·n² ≤ x^{11/16}/2`.

Indeed `n² ≤ 9e²·x^{5/8}`, hence `Δ·n² ≤ 18e²·x^{127/200}`; and
`x^{11/16}/2 = (x^{21/400}/2)·x^{127/200} ≥ 162·x^{127/200}`, while `18e² < 162` because
`e < 3`.  The constants are deliberately loose (`3` in place of `2` for the `Yc`-sandwich,
`324` in place of `16e²` in the `x`-power) so that the estimate is insensitive to the `+1`
in `⌊Yc x B⌋₊ ≤ Yc x B < ⌊Yc x B⌋₊ + 1`. -/
private lemma rpow_wide_arith (x : ℕ) (Δ : ℕ) (n Y : ℝ) (hx1 : 1 < (x : ℝ))
    (hΔ : (Δ : ℝ) ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 100))
    (hn0 : 0 ≤ n) (hn : n ≤ Real.exp 1 * Y) (hY : Y ≤ 3 * (x : ℝ) ^ ((5 : ℝ) / 16))
    (hE : 324 ≤ (x : ℝ) ^ ((21 : ℝ) / 400)) :
    (Δ : ℝ) * n * n ≤ (x : ℝ) ^ ((11 : ℝ) / 16) / 2 := by
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := by linarith
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  set S : ℝ := (x : ℝ) ^ ((5 : ℝ) / 16) with hSdef
  have hS0 : 0 ≤ S := by rw [hSdef]; exact Real.rpow_nonneg hx0 _
  -- `n ≤ 3e·S`
  have hn3 : n ≤ 3 * Real.exp 1 * S := by
    have h1 : Real.exp 1 * Y ≤ Real.exp 1 * (3 * S) :=
      mul_le_mul_of_nonneg_left hY (Real.exp_pos 1).le
    linarith
  have h3S0 : 0 ≤ 3 * Real.exp 1 * S := by positivity
  -- `n² ≤ 9e²·x^{5/8}`
  have hn2 : n * n ≤ 9 * (Real.exp 1) ^ 2 * (x : ℝ) ^ ((5 : ℝ) / 8) := by
    have hsq : n * n ≤ (3 * Real.exp 1 * S) * (3 * Real.exp 1 * S) :=
      mul_le_mul hn3 hn3 hn0 h3S0
    have hSS : S * S = (x : ℝ) ^ ((5 : ℝ) / 8) := by
      rw [hSdef, ← Real.rpow_add hxpos, show (5 : ℝ) / 16 + 5 / 16 = 5 / 8 by norm_num]
    calc n * n ≤ (3 * Real.exp 1 * S) * (3 * Real.exp 1 * S) := hsq
      _ = 9 * (Real.exp 1) ^ 2 * (S * S) := by ring
      _ = 9 * (Real.exp 1) ^ 2 * (x : ℝ) ^ ((5 : ℝ) / 8) := by rw [hSS]
  -- `Δ·n² ≤ 18e²·x^{127/200}`
  have hmain : (Δ : ℝ) * n * n ≤ 18 * (Real.exp 1) ^ 2 * (x : ℝ) ^ ((127 : ℝ) / 200) := by
    have h1 : (Δ : ℝ) * n * n ≤ (Δ : ℝ) * (9 * (Real.exp 1) ^ 2 * (x : ℝ) ^ ((5 : ℝ) / 8)) := by
      calc (Δ : ℝ) * n * n = (Δ : ℝ) * (n * n) := by ring
        _ ≤ (Δ : ℝ) * (9 * (Real.exp 1) ^ 2 * (x : ℝ) ^ ((5 : ℝ) / 8)) :=
            mul_le_mul_of_nonneg_left hn2 (Nat.cast_nonneg Δ)
    have h2 : (Δ : ℝ) * (9 * (Real.exp 1) ^ 2 * (x : ℝ) ^ ((5 : ℝ) / 8))
        ≤ (2 * (x : ℝ) ^ ((1 : ℝ) / 100))
          * (9 * (Real.exp 1) ^ 2 * (x : ℝ) ^ ((5 : ℝ) / 8)) :=
      mul_le_mul_of_nonneg_right hΔ (by positivity)
    have h3 : (2 * (x : ℝ) ^ ((1 : ℝ) / 100))
          * (9 * (Real.exp 1) ^ 2 * (x : ℝ) ^ ((5 : ℝ) / 8))
        = 18 * (Real.exp 1) ^ 2 * (x : ℝ) ^ ((127 : ℝ) / 200) := by
      have h4 : (2 * (x : ℝ) ^ ((1 : ℝ) / 100))
            * (9 * (Real.exp 1) ^ 2 * (x : ℝ) ^ ((5 : ℝ) / 8))
          = 18 * (Real.exp 1) ^ 2
            * ((x : ℝ) ^ ((1 : ℝ) / 100) * (x : ℝ) ^ ((5 : ℝ) / 8)) := by ring
      rw [h4, ← Real.rpow_add hxpos, show (1 : ℝ) / 100 + 5 / 8 = 127 / 200 by norm_num]
    linarith [h1, h2, h3]
  -- `18e² < 162`
  have hexp : 18 * (Real.exp 1) ^ 2 < 162 := by
    have h : (Real.exp 1) ^ 2 < 9 := by
      have h9 : (Real.exp 1) ^ 2 = Real.exp 1 * Real.exp 1 := by ring
      rw [h9]
      nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
    linarith
  -- `x^{11/16}/2 ≥ 162·x^{127/200}`
  have hsplit : (x : ℝ) ^ ((11 : ℝ) / 16)
      = (x : ℝ) ^ ((21 : ℝ) / 400) * (x : ℝ) ^ ((127 : ℝ) / 200) := by
    rw [← Real.rpow_add hxpos, show (21 : ℝ) / 400 + 127 / 200 = 11 / 16 by norm_num]
  have hX0 : 0 ≤ (x : ℝ) ^ ((127 : ℝ) / 200) := Real.rpow_nonneg hx0 _
  have hchain : 18 * (Real.exp 1) ^ 2 * (x : ℝ) ^ ((127 : ℝ) / 200)
      ≤ 162 * (x : ℝ) ^ ((127 : ℝ) / 200) :=
    mul_le_mul_of_nonneg_right (le_of_lt hexp) hX0
  rw [hsplit]
  have h162 : (162 : ℝ) ≤ (x : ℝ) ^ ((21 : ℝ) / 400) / 2 := by linarith
  have hfin : 162 * (x : ℝ) ^ ((127 : ℝ) / 200)
      ≤ ((x : ℝ) ^ ((21 : ℝ) / 400) * (x : ℝ) ^ ((127 : ℝ) / 200)) / 2 := by
    calc 162 * (x : ℝ) ^ ((127 : ℝ) / 200)
        ≤ ((x : ℝ) ^ ((21 : ℝ) / 400) / 2) * (x : ℝ) ^ ((127 : ℝ) / 200) :=
          mul_le_mul_of_nonneg_right h162 hX0
      _ = ((x : ℝ) ^ ((21 : ℝ) / 400) * (x : ℝ) ^ ((127 : ℝ) / 200)) / 2 := by ring
  linarith [hmain, hchain, hfin]

theorem chainRangeWideBstar :
    ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      Work.FIChain.Deltac x * ⌊Real.exp 1 * Work.FIChain.Yc x HasBc.val⌋₊
        * ⌊Real.exp 1 * Work.FIChain.Yc x HasBc.val⌋₊ ≤ Work.FIChain.Dc x := by
  have hBstar : (0 : ℝ) < HasBc.val := by have := HasBc.ge_two; linarith
  have hzcv : ∀ᶠ x : ℕ in Filter.atTop,
      (⌊Work.FIChain.Yc x HasBc.val⌋₊ : ℝ)
        ≤ 2 * (x : ℝ) ^ ((5 : ℝ) / 16) := by
    filter_upwards [Work.FIChain.zc_sharp_bounds HasBc.val hBstar] with x hx
    simpa only [Work.FIChain.zc, Work.FIChain.Zc] using hx.2
  have hmain : ∀ᶠ x : ℕ in Filter.atTop,
      (Work.FIChain.Deltac x : ℝ) * (⌊Real.exp 1 * Work.FIChain.Yc x HasBc.val⌋₊ : ℝ)
          * (⌊Real.exp 1 * Work.FIChain.Yc x HasBc.val⌋₊ : ℝ)
        ≤ (Work.FIChain.Dc x : ℝ) := by
    filter_upwards [hzcv, Work.FITop.FI_ev_Delta1_le_two_Lam1,
      Work.FITop.FI_ev_Dcut_lower,
      Work.FITop.FI_ev_rpow_ge_nat ((21 : ℝ) / 400) (by norm_num) (324 : ℝ),
      eventually_ge_atTop 2] with x hzc hD2 hDcut hE hx2
    have hx1 : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 1 < x)
    have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
    have hLpos : 0 < Real.log (x : ℝ) := Real.log_pos hx1
    have hYpos : 0 < Work.FIChain.Yc x HasBc.val := by
      rw [Work.FIChain.Yc]
      refine div_pos (Real.sqrt_pos.mpr hxpos) (mul_pos ?_ ?_)
      · rw [Work.FIChain.sc]; positivity
      · exact Real.rpow_pos_of_pos hLpos _
    have hnle : (⌊Real.exp 1 * Work.FIChain.Yc x HasBc.val⌋₊ : ℝ)
        ≤ Real.exp 1 * Work.FIChain.Yc x HasBc.val :=
      Nat.floor_le (le_of_lt (mul_pos (Real.exp_pos 1) hYpos))
    have hDlat : (Work.FIChain.Deltac x : ℝ) ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 100) := by
      simpa only [Work.FIChain.Deltac, Work.FITop.Lam1] using hD2
    have hDcut' : (x : ℝ) ^ ((11 : ℝ) / 16) / 2 ≤ (Work.FIChain.Dc x : ℝ) := hDcut
    -- the `Yc` sandwich `Yc < ⌊Yc⌋ + 1 ≤ 2x^{5/16} + 1 ≤ 3x^{5/16}`
    have hx516 : (1 : ℝ) ≤ (x : ℝ) ^ ((5 : ℝ) / 16) := Real.one_le_rpow hx1.le (by norm_num)
    have hYup : Work.FIChain.Yc x HasBc.val ≤ 3 * (x : ℝ) ^ ((5 : ℝ) / 16) := by
      have hlt := Nat.lt_floor_add_one (Work.FIChain.Yc x HasBc.val)
      linarith
    have harith := rpow_wide_arith x (Work.FIChain.Deltac x)
      (↑⌊Real.exp 1 * Work.FIChain.Yc x HasBc.val⌋₊) (Work.FIChain.Yc x HasBc.val)
      hx1 hDlat (Nat.cast_nonneg _) hnle hYup hE
    linarith [harith, hDcut']
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 hmain
  refine ⟨x₀, fun x hx => ?_⟩
  have h := hx₀ x hx
  have hgoal : ((Work.FIChain.Deltac x * ⌊Real.exp 1 * Work.FIChain.Yc x HasBc.val⌋₊
      * ⌊Real.exp 1 * Work.FIChain.Yc x HasBc.val⌋₊ : ℕ) : ℝ)
      ≤ (Work.FIChain.Dc x : ℝ) := by
    push_cast
    exact h
  exact_mod_cast hgoal

end

end Work.FIPiChain
