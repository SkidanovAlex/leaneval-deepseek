import Mathlib
import Submission.Work.KMTPlan.A6.MdlDefs

namespace Work.KMTPlan.A6

/-! ## A threshold where the doubly exponential scale count beats the polynomial RHS

The statement `thresholdScaleCountGt` is the elementary (but not entirely trivial) fact that for
all sufficiently large `L` the integer `n = scaleCount 1 ρ L = ⌊2^{2ρL}⌋` is so large that
`d · 2^n` dominates `(3d+3) + dL + Cs·2^{ρL}`.

The argument is:

* `⌊2^{2ρL}⌋ ≥ 2^{2ρL} / 2` (floor lower bound), so `2^n ≥ 2^{2^{2ρL}/2}`;
* writing `t = 2^{ρL}`, the latter exponent is `t²/2 = 2^{2ρL}/2`;
* for `t ≥ max (6L, 12 Cs, 18d+24)` one has `(3d+3) + dL + Cs·t < 2^{t²/2}`;
* `t = 2^{ρL}` satisfies these three bounds for `L` large, because `2^{s} ≥ 1 + s/2` and
  `2^s ≥ (s/4)²` for `s ≥ 0`. -/

/-- **Elementary exponential lower bound.** `1 + s/2 ≤ 2^s` for `s ≥ 0`
(since `2^s = exp (s log 2)` and `log 2 > 1/2`).  Proven here to keep this module self-contained. -/
lemma twoRpow_oneAddHalf (s : ℝ) (hs : 0 ≤ s) : 1 + s / 2 ≤ (2 : ℝ) ^ s := by
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h1 : 1 + s * Real.log 2 ≤ (2 : ℝ) ^ s := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm (Real.log 2) s]
    have := Real.add_one_le_exp (s * Real.log 2)
    linarith
  have h2 : 1 + s / 2 ≤ 1 + s * Real.log 2 := by
    have := mul_le_mul_of_nonneg_left hlog hs
    linarith
  linarith

/-- **Quadratic lower bound for `2^s`.** `s^2/16 ≤ 2^s` for `s ≥ 0`
(from `2^{s/2} ≥ 1 + s/4 ≥ s/4` and `(2^{s/2})^2 = 2^s`). -/
lemma twoRpow_ge_sq_div (s : ℝ) (hs : 0 ≤ s) : s * s / 16 ≤ (2 : ℝ) ^ s := by
  have hs2 : (0 : ℝ) ≤ s / 2 := by linarith
  have h1 : 1 + (s / 2) / 2 ≤ (2 : ℝ) ^ (s / 2) := twoRpow_oneAddHalf (s / 2) hs2
  have h4 : s / 4 ≤ (2 : ℝ) ^ (s / 2) := by linarith
  have hs4 : (0 : ℝ) ≤ s / 4 := by linarith
  have hsq : (s / 4) * (s / 4) ≤ (2 : ℝ) ^ (s / 2) * (2 : ℝ) ^ (s / 2) :=
    mul_self_le_mul_self hs4 h4
  have hadd : (2 : ℝ) ^ (s / 2) * (2 : ℝ) ^ (s / 2) = (2 : ℝ) ^ s := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  linarith [hsq, hadd]

/-- **The arithmetic core of the threshold.**  If `t ≥ 6L`, `t ≥ 12 Cs` and `t ≥ 18d+24` then
`(3d+3) + dL + Cs·t < 2^{t²/2}`.  The three hypotheses give `d ≤ t/18`, `L ≤ t/6`, `Cs ≤ t/12`,
hence `(3d+3) + dL + Cs·t ≤ 19 t²/108 < t⁴/64 ≤ 2^{t²/2}`. -/
lemma thresholdArith_aux (d : ℕ) (Cs : ℝ) (L : ℕ) (t : ℝ)
    (h6 : 6 * (L : ℝ) ≤ t) (hCs : 12 * Cs ≤ t) (hd : (18 : ℝ) * d + 24 ≤ t) :
    3 * (d : ℝ) + 3 + (d : ℝ) * (L : ℝ) + Cs * t < (2 : ℝ) ^ (t * t / 2) := by
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have ht24 : (24 : ℝ) ≤ t := by linarith
  have ht0 : (0 : ℝ) < t := by linarith
  -- the three individual bounds
  have hb1 : (d : ℝ) * (L : ℝ) ≤ t * t / 108 := by
    have h1 : (d : ℝ) ≤ t / 18 := by linarith
    have h2 : (L : ℝ) ≤ t / 6 := by linarith
    calc (d : ℝ) * (L : ℝ) ≤ (t / 18) * (t / 6) :=
          mul_le_mul h1 h2 hL0 (by linarith)
      _ = t * t / 108 := by ring
  have hb2 : Cs * t ≤ t * t / 12 := by
    have h1 : Cs ≤ t / 12 := by linarith
    calc Cs * t ≤ (t / 12) * t := mul_le_mul_of_nonneg_right h1 (le_of_lt ht0)
      _ = t * t / 12 := by ring
  have hb3 : 3 * (d : ℝ) + 3 ≤ t * t / 12 := by
    have h1 : (d : ℝ) ≤ t / 18 := by linarith
    have h2 : t / 6 + 3 ≤ t * t / 12 := by nlinarith
    linarith
  have hA : 3 * (d : ℝ) + 3 + (d : ℝ) * (L : ℝ) + Cs * t ≤ 19 * (t * t) / 108 := by
    linarith [hb1, hb2, hb3]
  -- the two analytic inputs
  have hB : 19 * (t * t) / 108 < (t * t / 2) * (t * t / 2) / 16 := by nlinarith
  have hC : (t * t / 2) * (t * t / 2) / 16 ≤ (2 : ℝ) ^ (t * t / 2) :=
    twoRpow_ge_sq_div (t * t / 2) (by positivity)
  linarith [hA, hB, hC]

/-- **The scale count is at least half of `2^{2ρL}`, exponentially.**  Since
`scaleCount 1 ρ L = ⌊2^{2ρL}⌋ ≥ 2^{2ρL}/2`, monotonicity of `2^·` gives
`2^{2^{2ρL}/2} ≤ 2^{scaleCount 1 ρ L}`. -/
lemma twoRpowScaleCountGe_aux (ρ : ℝ) (hρ : 0 < ρ) (L : ℕ) :
    (2 : ℝ) ^ ((2 : ℝ) ^ (2 * ρ * (L : ℝ)) / 2) ≤
      (2 : ℝ) ^ (Work.Analysis.EndVar.scaleCount 1 ρ L) := by
  have hu : Work.Analysis.EndVar.scaleCount 1 ρ L
      = ⌊(2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋₊ := by
    simp only [Work.Analysis.EndVar.scaleCount, Int.floor_toNat, Nat.cast_one, one_mul]
  set x : ℝ := (2 : ℝ) ^ (2 * ρ * (L : ℝ)) with hx
  have hx1 : (1 : ℝ) ≤ x := Real.one_le_rpow (by norm_num) (by positivity)
  have hfloor : x / 2 ≤ (Work.Analysis.EndVar.scaleCount 1 ρ L : ℝ) := by
    rw [hu]
    rcases le_total x 2 with h2 | h2
    · have h3 : x / 2 ≤ 1 := by linarith
      have h4 : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
        have : (1 : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx1)
        exact_mod_cast this
      linarith
    · have h3 : x - 1 ≤ (⌊x⌋₊ : ℝ) := by
        have := Nat.lt_floor_add_one x
        linarith
      linarith
  have hmono := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hfloor
  rwa [Real.rpow_natCast] at hmono

/-- **The threshold.**  For `ρ > 0`, `d ≥ 2` and `Cs > 0` there is `Lmax` such that for all
`L ≥ Lmax` the scale count `scaleCount 1 ρ L = ⌊2^{2ρL}⌋` satisfies
`d · 2^{scaleCount 1 ρ L} > (3d+3) + dL + Cs·2^{ρL}`. -/
theorem thresholdScaleCountGt (ρ : ℝ) (hρ : 0 < ρ) (d : ℕ) (hd : 2 ≤ d) (Cs : ℝ) (hCs : 0 < Cs) :
    ∃ Lmax : ℕ, ∀ L : ℕ, Lmax ≤ L →
      (d : ℝ) * (2 : ℝ) ^ (Work.Analysis.EndVar.scaleCount 1 ρ L) > (3 * d + 3 : ℝ) + d * L + Cs * (2 : ℝ) ^ (ρ * L) := by
  set K : ℝ := max (96 / ρ ^ 2) (max ((24 * Cs - 2) / ρ) ((36 * (d : ℝ) + 46) / ρ)) with hK
  refine ⟨Nat.ceil K, ?_⟩
  intro L hL
  have hLK : K ≤ (L : ℝ) := le_trans (Nat.le_ceil K) (by exact_mod_cast hL)
  have hL96 : 96 / ρ ^ 2 ≤ (L : ℝ) := le_trans (le_max_left _ _) hLK
  have hL24 : (24 * Cs - 2) / ρ ≤ (L : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLK
  have hL36 : (36 * (d : ℝ) + 46) / ρ ≤ (L : ℝ) :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hLK
  have hLpos : (0 : ℝ) < (L : ℝ) := lt_of_lt_of_le (by positivity) hL96
  set t : ℝ := (2 : ℝ) ^ (ρ * (L : ℝ)) with ht
  -- `t ≥ 6L`
  have hsq : (ρ * (L : ℝ)) * (ρ * (L : ℝ)) / 16 ≤ t := by
    rw [ht]
    exact twoRpow_ge_sq_div _ (by positivity)
  have h96 : (96 : ℝ) ≤ ρ ^ 2 * (L : ℝ) := by
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < ρ ^ 2)).mp hL96
    linarith
  have ht6 : 6 * (L : ℝ) ≤ t := by nlinarith [hsq, h96, hLpos]
  -- `t ≥ 1 + ρL/2`, hence `t ≥ 12 Cs` and `t ≥ 18d + 24`
  have htlin : 1 + ρ * (L : ℝ) / 2 ≤ t := by
    rw [ht]
    exact twoRpow_oneAddHalf _ (by positivity)
  have h24' : 24 * Cs - 2 ≤ ρ * (L : ℝ) := by
    have := (div_le_iff₀ hρ).mp hL24
    linarith
  have htCs : 12 * Cs ≤ t := by linarith
  have h36' : 36 * (d : ℝ) + 46 ≤ ρ * (L : ℝ) := by
    have := (div_le_iff₀ hρ).mp hL36
    linarith
  have htd : (18 : ℝ) * d + 24 ≤ t := by linarith
  have harith := thresholdArith_aux d Cs L t ht6 htCs htd
  -- transfer the scale-count bound
  have ht2 : t * t = (2 : ℝ) ^ (2 * ρ * (L : ℝ)) := by
    rw [ht, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hpow : (2 : ℝ) ^ (t * t / 2) ≤ (2 : ℝ) ^ (Work.Analysis.EndVar.scaleCount 1 ρ L) := by
    rw [ht2]
    exact twoRpowScaleCountGe_aux ρ hρ L
  have hone : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
  have hdle : (2 : ℝ) ^ (Work.Analysis.EndVar.scaleCount 1 ρ L) ≤
      (d : ℝ) * (2 : ℝ) ^ (Work.Analysis.EndVar.scaleCount 1 ρ L) :=
    le_mul_of_one_le_left (by positivity) hone
  linarith [harith, hpow, hdle]

end Work.KMTPlan.A6
