import Mathlib
import Submission.Work.CNum.SerDnDefs
import Submission.Work.CNum.SerStepScale
import Submission.Work.CNum.SerStepSize
import Submission.Work.CNum.SerStepArith

namespace Work.CNum

open Work.ANum

/-!
# `Work.CNum.SerDnInvStep` — one step of the `SDInv` invariant

This file proves `SerDnInvStep`: the state invariant `Work.CNum.SDInv x y e σ k s` of the `serDn`
recursion (the lower bound for `log ‖h w‖`) is preserved by one application of
`Work.CNum.sdNext x y σ`.

The invariant has seven components.  Writing `c = spt x y` for the centre, `R = srad x y e` for
the disc radius and `σ` for the running geometric bound, one step replaces the state
`(px, py, pe, sg)` by

  `(⌊(px·x - py·y)/SC⌋, ⌊(px·y + py·x)/SC⌋, ⌈σ·pe/SC⌉ + 2, ⌈sg·σ/SC⌉)`.

* components `0 ≤ pe` and `m2r pe ≤ 1/100` are preserved by the purely arithmetic lemma
  `SerDnPeStep` (the `79/100` bound on `m2r σ` is what makes the product fit);
* `R^(k+1) ≤ m2r sg' ≤ 2` is the existing lemma `SerStepScale`;
* the approximation error `‖c^(k+2) - spt px' py'‖ ≤ m2r pe'` is `SerDnStepErr`
  (propagation of the old error through `c` plus the rounding error `sdRound`);
* the size bounds `|SC + px'|, |py'| ≤ 2^34` are `SerDnSizeStep`.
-/

/-! ## Auxiliary arithmetic -/

/-- Floor division at scale `SC` differs from the true quotient by at most `1 + 1/SC`:
`|⌊a/s⌋| ≤ |a|/s + 1`.  This is the floor analogue of `ceil_div_abs_le`. -/
lemma floorDiv_abs_le (a s : ℤ) (hs : 0 < s) :
    |((Int.ediv a s : ℤ) : ℝ)| ≤ |(a:ℝ)| / (s:ℝ) + 1 := by
  have h := ceil_div_abs_le (-a) s hs
  simpa using h

/-- **The `pe`-step.**  If the accumulated error mantissa `pe` is `≥ 0` and at most `1/100`, and
`m2r σ ≤ 79/100`, then the new mantissa `mulU σ pe + 2 = ⌈σ·pe/SC⌉ + 2` is again nonnegative and
at most `1/100` (the `+2` is the safety margin for one multiplication by `c`, and the shrinking
factor `79/100` leaves room for it). -/
lemma SerDnPeStep {σ pe : ℤ} (hpe : 0 ≤ pe) (hpe1 : m2r pe ≤ 1 / 100)
    (hσ0 : 0 ≤ σ) (hσ1 : m2r σ ≤ 79 / 100) :
    0 ≤ mulU σ pe + 2 ∧ m2r (mulU σ pe + 2) ≤ 1 / 100 := by
  have hSCn : (0:ℝ) < (SC:ℝ) := SC_posR
  have hmul0 : 0 ≤ mulU σ pe := by
    rw [← m2r_nonneg_iff]
    exact le_trans (mul_nonneg (m2r_nonneg_NrmSpec hσ0) (m2r_nonneg_NrmSpec hpe)) (le_mulU σ pe)
  constructor
  · omega
  · have hcast : (mulU σ pe : ℝ) * (SC:ℝ) ≤ (σ:ℝ)*(pe:ℝ) + ((SC:ℝ) - 1) := by
      have h := mulU_mul_SC_le σ pe
      have h2 : ((mulU σ pe * SC : ℤ) : ℝ) ≤ ((σ * pe + (SC - 1) : ℤ) : ℝ) := by
        exact_mod_cast h
      push_cast at h2
      linarith
    have hσm : (σ:ℝ)*100 ≤ 79*(SC:ℝ) := by
      have h := hσ1
      rw [m2r] at h
      have h2 := (div_le_iff₀ hSCn).mp h
      linarith
    have hpm : (pe:ℝ)*100 ≤ (SC:ℝ) := by
      have h := hpe1
      rw [m2r] at h
      have h2 := (div_le_iff₀ hSCn).mp h
      linarith
    have hσ0R : (0:ℝ) ≤ (σ:ℝ) := by exact_mod_cast hσ0
    have hpeR : (0:ℝ) ≤ (pe:ℝ) := by exact_mod_cast hpe
    have hSCbig : (30000 : ℝ) ≤ 21 * (SC:ℝ) := by norm_num [SC]
    have key : ((mulU σ pe : ℝ) + 2) * 100 ≤ (SC:ℝ) := by
      nlinarith [hcast, hσm, hpm, hσ0R, hpeR, hSCbig, hSCn]
    rw [m2r]
    push_cast
    rw [div_le_iff₀ hSCn]
    linarith [key, hSCn]

/-- **The error step.**  If `(px, py)` approximates `c^(k+1)` up to `m2r pe` (with `pe ≥ 0`) and
`R = srad x y e ≤ m2r σ`, then the floor-rounded product `(sdx, sdy)` approximates `c^(k+2)` up to
`m2r (mulU σ pe + 2)`.  Propagating the old error through `c` costs `m2r σ · m2r pe`, the rounding
costs `m2r 2 = 2/SC` (`sdRound`), and `m2r σ · m2r pe ≤ m2r (mulU σ pe)` (`le_mulU`). -/
lemma SerDnStepErr {x y e σ : ℤ} {k : ℕ} {px py pe : ℤ} (he : 0 ≤ e)
    (hRσ : srad x y e ≤ m2r σ) (hpe : 0 ≤ pe)
    (hp5 : ‖spt x y ^ (k + 1) - spt px py‖ ≤ m2r pe) :
    ‖spt x y ^ (k + 1 + 1) - spt (sdx x y px py) (sdy x y px py)‖ ≤ m2r (mulU σ pe + 2) := by
  have hpe0 : (0:ℝ) ≤ m2r pe := m2r_nonneg_NrmSpec hpe
  have hc : ‖spt x y‖ ≤ m2r σ := by
    have h1 : ‖spt x y‖ ≤ srad x y e := by
      have h2 : srad x y e = ‖spt x y‖ + m2r e := rfl
      rw [h2]; linarith [m2r_nonneg_NrmSpec he]
    linarith
  have hpow : ‖spt x y ^ (k + 1 + 1) - spt x y * spt px py‖ ≤ m2r σ * m2r pe := by
    have h2 : spt x y ^ (k + 1 + 1) - spt x y * spt px py
        = (spt x y ^ (k + 1) - spt px py) * spt x y := by
      rw [pow_succ]
      ring
    rw [h2, norm_mul]
    calc ‖spt x y ^ (k + 1) - spt px py‖ * ‖spt x y‖ ≤ m2r pe * m2r σ :=
          mul_le_mul hp5 hc (norm_nonneg _) hpe0
      _ = m2r σ * m2r pe := by ring
  have hmul : ‖spt x y * spt px py - spt (sdx x y px py) (sdy x y px py)‖ ≤ m2r 2 := by
    have h := sdRound x y px py
    rwa [mul_comm (spt px py) (spt x y)] at h
  have hmain : ‖spt x y ^ (k + 1 + 1) - spt (sdx x y px py) (sdy x y px py)‖
      ≤ m2r σ * m2r pe + m2r 2 := by
    have h3 : spt x y ^ (k + 1 + 1) - spt (sdx x y px py) (sdy x y px py)
        = (spt x y ^ (k + 1 + 1) - spt x y * spt px py)
          + (spt x y * spt px py - spt (sdx x y px py) (sdy x y px py)) := by ring
    rw [h3]
    exact le_trans (norm_add_le _ _) (add_le_add hpow hmul)
  refine le_trans hmain ?_
  rw [m2r_add]
  linarith [le_mulU σ pe]

/-- **The size step.**  The floor-rounded mantissas produced by one step of `sdNext` still fit in
`2^34`: `‖spt x y‖ ≤ R < 1` forces `|x|, |y| ≤ SC`, while `‖spt px py‖ ≤ 1 + m2r pe ≤ 4` gives
`|px|, |py| ≤ 4·SC`; hence `|px·x - py·y|, |px·y + py·x| ≤ 8·SC²` and the floor quotients are
bounded by `8·SC + 1`, so `|SC + px'| ≤ 9·SC + 1 < 2^34`. -/
theorem SerDnSizeStep {x y e σ : ℤ} {k : ℕ} {px py pe : ℤ} (he : 0 ≤ e)
    (hσlt : m2r σ < 1) (hRσ : srad x y e ≤ m2r σ) (hpe3 : m2r pe ≤ 3)
    (hp5 : ‖spt x y ^ (k + 1) - spt px py‖ ≤ m2r pe) :
    Int.natAbs (SC + sdx x y px py) ≤ 2 ^ 34 ∧ Int.natAbs (sdy x y px py) ≤ 2 ^ 34 := by
  have hSCposR : (0 : ℝ) < (SC : ℝ) := SC_posR
  have hSCposZ : (0 : ℤ) < SC := SC_pos
  have hme : (0 : ℝ) ≤ m2r e := by
    show (0 : ℝ) ≤ (e : ℝ) / (SC : ℝ)
    exact div_nonneg (by exact_mod_cast he) hSCposR.le
  have hc_le : ‖spt x y‖ ≤ m2r σ := by
    have h1 : ‖spt x y‖ ≤ srad x y e := by
      show ‖spt x y‖ ≤ ‖spt x y‖ + m2r e
      linarith
    linarith
  have hc1 : ‖spt x y‖ ≤ 1 := le_of_lt (lt_of_le_of_lt hc_le hσlt)
  have hpow : ‖spt x y ^ (k + 1)‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg (spt x y)) hc1
  have hp4 : ‖spt px py‖ ≤ 4 := by
    have h1 : ‖spt px py‖ ≤ ‖spt px py - spt x y ^ (k + 1)‖ + ‖spt x y ^ (k + 1)‖ := by
      have := norm_add_le (spt px py - spt x y ^ (k + 1)) (spt x y ^ (k + 1))
      rwa [sub_add_cancel] at this
    have h2 : ‖spt px py - spt x y ^ (k + 1)‖ = ‖spt x y ^ (k + 1) - spt px py‖ :=
      norm_sub_rev (spt px py) (spt x y ^ (k + 1))
    rw [h2] at h1
    linarith
  have hpx : |(px : ℝ)| ≤ 4 * (SC : ℝ) := by
    have h := abs_re_le_SC_mul_norm_spt px py
    nlinarith [norm_nonneg (spt px py)]
  have hpy : |(py : ℝ)| ≤ 4 * (SC : ℝ) := by
    have h := abs_im_le_SC_mul_norm_spt px py
    nlinarith [norm_nonneg (spt px py)]
  have hx : |(x : ℝ)| ≤ (SC : ℝ) := by
    have h := abs_re_le_SC_mul_norm_spt x y
    nlinarith [norm_nonneg (spt x y)]
  have hy : |(y : ℝ)| ≤ (SC : ℝ) := by
    have h := abs_im_le_SC_mul_norm_spt x y
    nlinarith [norm_nonneg (spt x y)]
  have hmul : ∀ a b : ℤ, |(a : ℝ)| ≤ 4 * (SC : ℝ) → |(b : ℝ)| ≤ (SC : ℝ) →
      |(a : ℝ) * (b : ℝ)| ≤ 4 * (SC : ℝ) * (SC : ℝ) := by
    intro a b ha hb
    rw [abs_mul]
    nlinarith [abs_nonneg (a : ℝ), abs_nonneg (b : ℝ), hSCposR]
  have hA : |(((px * x - py * y : ℤ)) : ℝ)| ≤ 8 * (SC : ℝ) * (SC : ℝ) := by
    have hcast : ((px * x - py * y : ℤ) : ℝ) = (px : ℝ) * (x : ℝ) - (py : ℝ) * (y : ℝ) := by
      push_cast; ring
    rw [hcast]
    have h1 := hmul px x hpx hx
    have h2 := hmul py y hpy hy
    have h3 : |(px : ℝ) * (x : ℝ) - (py : ℝ) * (y : ℝ)| ≤
        |(px : ℝ) * (x : ℝ)| + |(py : ℝ) * (y : ℝ)| := by
      have h := abs_add_le ((px : ℝ) * (x : ℝ)) (-((py : ℝ) * (y : ℝ)))
      rw [abs_neg] at h
      exact h
    linarith
  have hB : |(((px * y + py * x : ℤ)) : ℝ)| ≤ 8 * (SC : ℝ) * (SC : ℝ) := by
    have hcast : ((px * y + py * x : ℤ) : ℝ) = (px : ℝ) * (y : ℝ) + (py : ℝ) * (x : ℝ) := by
      push_cast; ring
    rw [hcast]
    have h1 := hmul px y hpx hy
    have h2 := hmul py x hpy hx
    have h3 := abs_add_le ((px : ℝ) * (y : ℝ)) ((py : ℝ) * (x : ℝ))
    linarith
  have key : ∀ a : ℤ, |(a : ℝ)| ≤ 8 * (SC : ℝ) * (SC : ℝ) →
      |(((Int.ediv a SC : ℤ)) : ℝ)| ≤ 8 * (SC : ℝ) + 1 := by
    intro a ha
    have h := floorDiv_abs_le a SC hSCposZ
    have hdiv : |(a : ℝ)| / (SC : ℝ) ≤ 8 * (SC : ℝ) := by
      rw [div_le_iff₀ hSCposR]; linarith
    linarith
  have h34 : (9 * (SC : ℝ) + 1) ≤ ((2 ^ 34 : ℕ) : ℝ) := by norm_num [SC]
  have h8 : (8 * (SC : ℝ) + 1) ≤ ((2 ^ 34 : ℕ) : ℝ) := by linarith [h34]
  constructor
  · have hsdx : |((sdx x y px py : ℤ) : ℝ)| ≤ 8 * (SC : ℝ) + 1 := by
      show |(((Int.ediv (px * x - py * y) SC : ℤ)) : ℝ)| ≤ _
      exact key (px * x - py * y) hA
    have h1 : |(((SC + sdx x y px py : ℤ)) : ℝ)| ≤ 9 * (SC : ℝ) + 1 := by
      rw [show ((SC + sdx x y px py : ℤ) : ℝ) = (SC : ℝ) + ((sdx x y px py : ℤ) : ℝ) by
        push_cast; ring]
      have h2 := abs_add_le (SC : ℝ) ((sdx x y px py : ℤ) : ℝ)
      rw [abs_of_pos hSCposR] at h2
      linarith
    exact natAbs_le_of_abs_le_real (le_trans h1 h34)
  · have hsdy : |((sdy x y px py : ℤ) : ℝ)| ≤ 8 * (SC : ℝ) + 1 := by
      show |(((Int.ediv (px * y + py * x) SC : ℤ)) : ℝ)| ≤ _
      exact key (px * y + py * x) hB
    exact natAbs_le_of_abs_le_real (le_trans hsdy h8)

/-! ## The step theorem -/

theorem SerDnInvStep {x y e σ : ℤ} {k : ℕ} {s : Work.CNum.SD} (he : 0 ≤ e) (hσ1 : Work.ANum.m2r σ ≤ 79 / 100) (hRσ : Work.CNum.srad x y e ≤ Work.ANum.m2r σ) (h : Work.CNum.SDInv x y e σ k s) : Work.CNum.SDInv x y e σ (k + 1) (Work.CNum.sdNext x y σ s) := by
  have hσ0r : 0 ≤ m2r σ := le_trans (srad_nonneg he) hRσ
  have hσ0 : 0 ≤ σ := (m2r_nonneg_iff σ).mp hσ0r
  have hσlt : m2r σ < 1 := lt_of_le_of_lt hσ1 (by norm_num)
  obtain ⟨hpe, hpe1, hk, hsg2, hp5, _hx34, _hy34⟩ := h
  obtain ⟨h1, h2⟩ := SerDnPeStep hpe hpe1 hσ0 hσ1
  obtain ⟨h3, h4⟩ := SerStepScale he hσlt hRσ hk hsg2
  have h5 := SerDnStepErr he hRσ hpe hp5
  obtain ⟨h6, h7⟩ := SerDnSizeStep he hσlt hRσ (le_trans hpe1 (by norm_num)) hp5
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

end Work.CNum
