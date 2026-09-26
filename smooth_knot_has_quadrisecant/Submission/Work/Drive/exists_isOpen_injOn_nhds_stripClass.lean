import Mathlib
import Submission.Work.Drive.strip_cover_defs

/-!
# Local injectivity of the strip covering map `stripClass`

(Submission/Work/Drive/exists_isOpen_injOn_nhds_stripClass.lean)

**What this module does.**  The strip `StripPeriod = {q : ℝ × ℝ | 0 < q.2 ∧ q.2 < period}`
is the universal cover of Kuperberg's band of secants `OpenMobius`, via the covering map
`stripClass p = {K x, K (x + y)}` (`stripSecantClass`).  Its deck transformation is the
half-twist

`stripFlip (x, y) = (x + y, period - y)` with `stripFlip ∘ stripFlip = (x, y) ↦ (x + period, y)`

(these two strip points describe the *same* unordered pair `{x, x + y}` of parameters,
which is why `stripClass` identifies them).  Accordingly `stripClass p = stripClass q` iff
`q` lies in the deck orbit of `p`, i.e. iff `q = stripFlipᵏ p` for some `k : ℤ`; in
coordinates this is the dichotomy proved here as `stripClass_eq_imp`:

* `q.1.1 = p.1.1 + k * period ∧ q.1.2 = p.1.2`, or
* `q.1.1 = p.1.1 + p.1.2 + k * period ∧ q.1.2 = period - p.1.2`.

The deck orbit of any point is a *discrete* subset of the strip (its `x`-coordinates run
to `±∞`), so the covering map is locally injective.  This is the main theorem

`exists_isOpen_injOn_nhds_stripClass : ∃ B, IsOpen B ∧ z ∈ B ∧ Set.InjOn stripClass B`,

with the explicit neighbourhood `B = {q | |q.1.1 - z.1.1| < ε ∧ |q.1.2 - z.1.2| < ε}`,
`ε = min z.1.2 (period - z.1.2) / 4`:  the bound `2 * ε < min z.1.2 (period - z.1.2)` makes
the second branch of the dichotomy impossible inside the box (a `stripFlip`-image has
parameter length `period - y ≈ period`, hence is far away), while the first branch forces
`k = 0` (a nonzero multiple of the period is longer than the box).

This is the local-injectivity half of "`stripClass` is the covering map of the strip onto
the band", needed by the strip-crosscut reduction of brick (d).
-/

noncomputable section

open LeanEval.KnotTheory.Quadrisecant

namespace Work.Drive

/-! ## 1. Classes in `AddCircle period` and integer multiples of the period -/

/-- **An integer multiple of the period is `0` in `AddCircle period` (VERIFIED).** -/
lemma coe_int_mul_period (n : ℤ) : (((n : ℝ) * period : ℝ) : AddCircle period) = 0 := by
  have h : (n : ℝ) * period = n • period := by simp [zsmul_eq_mul]
  rw [h, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero]

/-- **Two reals have the same class in `AddCircle period` iff they differ by an integer
multiple of the period (VERIFIED).** -/
lemma coe_eq_coe_iff_exists_int (x y : ℝ) :
    ((x : ℝ) : AddCircle period) = ((y : ℝ) : AddCircle period) ↔
      ∃ n : ℤ, x = y + n * period := by
  constructor
  · intro h
    have h0 : ((x - y : ℝ) : AddCircle period) = 0 := by
      rw [AddCircle.coe_sub, h, sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff period).mp h0
    refine ⟨n, ?_⟩
    have hn' : (n : ℝ) * period = x - y := by
      rw [← hn]; simp [zsmul_eq_mul]
    linarith
  · rintro ⟨n, rfl⟩
    rw [AddCircle.coe_add, coe_int_mul_period n, add_zero]

/-- **Only the `0`-th multiple of the period fits in `(-period, period)` (VERIFIED).** -/
lemma int_eq_zero_of_sub_eq_mul_period {y y' : ℝ} (hy0 : 0 < y) (hy1 : y < period)
    (hy0' : 0 < y') (hy1' : y' < period) {n : ℤ} (h : y - y' = (n : ℝ) * period) :
    n = 0 := by
  have hleaf : |n| < 1 := by
    have h1 : |y - y'| < period := by
      rw [abs_sub_lt_iff]; exact ⟨by linarith, by linarith⟩
    have h2 : |(n : ℝ)| * period = |y - y'| := by
      rw [h, abs_mul, abs_of_pos period_pos]
    have h3 : |(n : ℝ)| < 1 := by nlinarith [period_pos, h1, h2]
    have h4 : ((|n| : ℤ) : ℝ) < 1 := by rw [Int.cast_abs]; exact h3
    exact_mod_cast h4
  exact Int.abs_lt_one_iff.mp hleaf

/-- **Only the `1`-st multiple of the period fits in `(0, 2 * period)` (VERIFIED).** -/
lemma int_eq_one_of_add_eq_mul_period {y y' : ℝ} (hy0 : 0 < y) (hy1 : y < period)
    (hy0' : 0 < y') (hy1' : y' < period) {n : ℤ} (h : y + y' = (n : ℝ) * period) :
    n = 1 := by
  have hp0 : (0 : ℝ) < (n : ℝ) * period := by rw [← h]; linarith
  have hp1 : (n : ℝ) * period < 2 * period := by rw [← h]; linarith
  have h0 : (0 : ℝ) < (n : ℝ) := by nlinarith [period_pos, hp0]
  have h1 : (n : ℝ) < 2 := by nlinarith [period_pos, hp1]
  have hz : (0 : ℤ) < n := by exact_mod_cast h0
  have ho : n < 2 := by exact_mod_cast h1
  omega

/-! ## 2. The fibres of the strip covering map -/

/-- **Dichotomy for the fibre of the strip covering map (VERIFIED).**  If two strip
points carry the same secant class, then either their parameter lengths agree and their
starting parameters differ by an integer multiple of the period (the translation part of
the deck group), or one is obtained from the other by the deck generator
`stripFlip (x, y) = (x + y, period - y)`, up to the same translation. -/
lemma stripClass_eq_imp (p q : StripPeriod) (h : stripClass p = stripClass q) :
    (∃ k : ℤ, q.1.1 = p.1.1 + k * period ∧ q.1.2 = p.1.2) ∨
    (∃ k : ℤ, q.1.1 = p.1.1 + p.1.2 + k * period ∧ q.1.2 = period - p.1.2) := by
  have hc : mobiusCover (stripPair p.1 p.2.1 p.2.2) = mobiusCover (stripPair q.1 q.2.1 q.2.2) := h
  have hu : unordOfOrdered (stripPair p.1 p.2.1 p.2.2)
      = unordOfOrdered (stripPair q.1 q.2.1 q.2.2) := congrArg Subtype.val hc
  rcases (unordOfOrdered_eq_iff _ _).mp hu with heq | hsw
  · -- the two ordered pairs agree: same secant, same starting parameter
    have h1 : ((p.1.1 : ℝ) : AddCircle period) = ((q.1.1 : ℝ) : AddCircle period) := by
      have := congrArg Prod.fst (congrArg Subtype.val heq)
      simpa [stripPair] using this
    have h2 : (((p.1.1 + p.1.2 : ℝ)) : AddCircle period)
        = (((q.1.1 + q.1.2 : ℝ)) : AddCircle period) := by
      have := congrArg Prod.snd (congrArg Subtype.val heq)
      simpa [stripPair] using this
    obtain ⟨n₁, hn₁⟩ := (coe_eq_coe_iff_exists_int p.1.1 q.1.1).mp h1
    obtain ⟨n₂, hn₂⟩ := (coe_eq_coe_iff_exists_int (p.1.1 + p.1.2) (q.1.1 + q.1.2)).mp h2
    have hy : p.1.2 - q.1.2 = ((n₂ - n₁ : ℤ) : ℝ) * period := by push_cast; linarith
    have hk : n₂ - n₁ = 0 :=
      int_eq_zero_of_sub_eq_mul_period p.2.1 p.2.2 q.2.1 q.2.2 hy
    left
    exact ⟨-n₁, by push_cast; linarith,
      by have : p.1.2 - q.1.2 = 0 := by rw [hy, hk]; simp
         linarith⟩
  · -- the two ordered pairs are swapped: the secant runs from `p.1 + p.2` back to `p.1`
    have h1 : (((p.1.1 + p.1.2 : ℝ)) : AddCircle period) = ((q.1.1 : ℝ) : AddCircle period) := by
      have := congrArg Prod.fst (congrArg Subtype.val hsw)
      simpa [stripPair, swapOrdered] using this
    have h2 : ((p.1.1 : ℝ) : AddCircle period)
        = (((q.1.1 + q.1.2 : ℝ)) : AddCircle period) := by
      have := congrArg Prod.snd (congrArg Subtype.val hsw)
      simpa [stripPair, swapOrdered] using this
    obtain ⟨m, hm⟩ := (coe_eq_coe_iff_exists_int (p.1.1 + p.1.2) q.1.1).mp h1
    obtain ⟨n, hn⟩ := (coe_eq_coe_iff_exists_int p.1.1 (q.1.1 + q.1.2)).mp h2
    right
    refine ⟨-m, by push_cast; linarith, ?_⟩
    have hy : q.1.2 + p.1.2 = ((m - n : ℤ) : ℝ) * period := by push_cast; linarith
    have hmn : m - n = 1 :=
      int_eq_one_of_add_eq_mul_period q.2.1 q.2.2 p.2.1 p.2.2 hy
    have hy' : q.1.2 + p.1.2 = period := by rw [hy, hmn]; simp
    linarith

/-! ## 3. Elementary bounds separating a point from its deck orbit -/

/-- **A nonnegative integer multiple of the period keeps `y ∈ (0, period)` away from
`0` (VERIFIED).** -/
lemma self_le_abs_int_mul_period_add (k : ℤ) (hk : 0 ≤ k) {y : ℝ} (hy : 0 < y) :
    y ≤ |(k : ℝ) * period + y| := by
  have hkR : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkp : 0 ≤ (k : ℝ) * period := mul_nonneg hkR (le_of_lt period_pos)
  have hnn : 0 ≤ (k : ℝ) * period + y := by linarith
  rw [abs_of_nonneg hnn]; linarith

/-- **An integer multiple `≤ -1` of the period keeps `y ∈ (0, period)` away from `0` by
at least `period - y` (VERIFIED).** -/
lemma period_sub_le_abs_int_mul_period_add {k : ℤ} (hk : k ≤ -1) {y : ℝ}
    (hy0 : 0 < y) (hy1 : y < period) : period - y ≤ |(k : ℝ) * period + y| := by
  have hkR : (k : ℝ) ≤ -1 := by exact_mod_cast hk
  have hneg : (k : ℝ) * period + y < 0 := by nlinarith [period_pos]
  rw [abs_of_neg hneg]
  nlinarith [period_pos, hkR]

/-- **The only integer multiple of the period of absolute value `< period` is `0`
(VERIFIED).** -/
lemma abs_int_mul_period_lt_iff {k : ℤ} : |(k : ℝ) * period| < period ↔ k = 0 := by
  rw [abs_mul, abs_of_pos period_pos]
  constructor
  · intro h
    have h1 : |(k : ℝ)| < 1 := by nlinarith [period_pos, h]
    have h2 : ((|k| : ℤ) : ℝ) < 1 := by rw [Int.cast_abs]; exact h1
    have h3 : (|k| : ℤ) < 1 := by exact_mod_cast h2
    exact Int.abs_lt_one_iff.mp h3
  · rintro rfl
    simpa using period_pos

/-- **Two points within `ε` of a common point differ by less than `2ε` (VERIFIED).** -/
lemma abs_sub_lt_two_mul_of_lt {a b c ε : ℝ} (ha : |a - c| < ε) (hb : |b - c| < ε) :
    |a - b| < 2 * ε := by
  calc |a - b| = |(a - c) + (c - b)| := by ring_nf
    _ ≤ |a - c| + |c - b| := abs_add_le _ _
    _ = |a - c| + |b - c| := by rw [abs_sub_comm c b]
    _ < ε + ε := add_lt_add ha hb
    _ = 2 * ε := by ring

/-! ## 4. The main theorem: `stripClass` is injective near `z` -/

/-- **`stripClass` is injective on an open neighbourhood of every point of the strip
(VERIFIED).**  An explicit neighbourhood is the box `{|x - x₀| < ε, |y - y₀| < ε}` with
`ε = min y₀ (period - y₀) / 4`: for two points of the box, the half-twist branch of
`stripClass_eq_imp` is impossible for `y`- and `x`-reasons, and the translation branch
forces the multiple of the period to vanish. -/
theorem exists_isOpen_injOn_nhds_stripClass (z : Work.Drive.StripPeriod) :
    ∃ B : Set Work.Drive.StripPeriod, IsOpen B ∧ z ∈ B ∧ Set.InjOn Work.Drive.stripClass B := by
  set m : ℝ := min z.1.2 (period - z.1.2) with hm
  have hm_pos : 0 < m := lt_min z.2.1 (by linarith [z.2.2])
  have hm_le_left : m ≤ z.1.2 := min_le_left _ _
  have hm_le_right : m ≤ period - z.1.2 := min_le_right _ _
  set ε : ℝ := m / 4 with hε
  have hε_pos : 0 < ε := by rw [hε]; linarith
  have h2ε_lt_period : 2 * ε < period := by
    rw [hε]; nlinarith [period_pos, hm_le_left, hm_le_right]
  refine ⟨{q : StripPeriod | |q.1.1 - z.1.1| < ε ∧ |q.1.2 - z.1.2| < ε}, ?_, ?_, ?_⟩
  · -- openness: the box is the preimage of an open box under a continuous map
    have hcont : Continuous fun q : StripPeriod => (|q.1.1 - z.1.1|, |q.1.2 - z.1.2|) := by
      fun_prop
    have hset : {q : StripPeriod | |q.1.1 - z.1.1| < ε ∧ |q.1.2 - z.1.2| < ε}
        = (fun q : StripPeriod => (|q.1.1 - z.1.1|, |q.1.2 - z.1.2|)) ⁻¹'
            {w : ℝ × ℝ | w.1 < ε ∧ w.2 < ε} := rfl
    rw [hset]
    exact ((isOpen_lt continuous_fst continuous_const).inter
      (isOpen_lt continuous_snd continuous_const)).preimage hcont
  · -- the centre belongs to the box
    exact ⟨by simp [hε_pos], by simp [hε_pos]⟩
  · -- injectivity: rule out the two branches of `stripClass_eq_imp`
    intro p hp q hq hpq
    have hp_lo : -ε < p.1.2 - z.1.2 := (abs_lt.mp hp.2).1
    have hp_hi : p.1.2 - z.1.2 < ε := (abs_lt.mp hp.2).2
    have hp2_gt : 2 * ε < p.1.2 := by nlinarith [hm_pos, hm_le_left, hp_lo, hε]
    have hp2_lt : 2 * ε < period - p.1.2 := by nlinarith [hm_pos, hm_le_right, hp_hi, hε]
    rcases stripClass_eq_imp p q hpq with ⟨k, hk1, hk2⟩ | ⟨k, hk1, hk2⟩
    · -- same parameter length: the multiple of the period must be `0`
      have hk0 : k = 0 := by
        refine abs_int_mul_period_lt_iff.mp ?_
        have h1 : (k : ℝ) * period = q.1.1 - p.1.1 := by linarith
        rw [h1]
        exact lt_trans (abs_sub_lt_two_mul_of_lt (a := q.1.1) (b := p.1.1) (c := z.1.1)
          (ε := ε) hq.1 hp.1) h2ε_lt_period
      apply Subtype.ext
      refine Prod.ext ?_ ?_
      · rw [hk1]; simp [hk0]
      · exact hk2.symm
    · -- the half-twist branch: excluded by the starting parameters
      exfalso
      have hx : |(k : ℝ) * period + p.1.2| < 2 * ε := by
        have h1 : (k : ℝ) * period + p.1.2 = q.1.1 - p.1.1 := by linarith
        rw [h1]
        exact abs_sub_lt_two_mul_of_lt (a := q.1.1) (b := p.1.1) (c := z.1.1) (ε := ε) hq.1 hp.1
      by_cases hk : (0 : ℤ) ≤ k
      · have h := self_le_abs_int_mul_period_add k hk p.2.1
        linarith
      · have hk' : k ≤ -1 := by omega
        have h := period_sub_le_abs_int_mul_period_add hk' p.2.1 p.2.2
        linarith

end Work.Drive
