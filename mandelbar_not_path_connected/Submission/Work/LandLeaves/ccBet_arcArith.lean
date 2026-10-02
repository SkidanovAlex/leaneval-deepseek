/-
Copyright: subproject `Submission/Work/LandLeaves/` of `mandelbar_not_path_connected`.

# `Int.fract` arithmetic for the hard case of `ccBet_angDouble`

This module contains the arithmetic reduction of the hard case of cyclic-order preservation of
the `2k`-fold angle map `σ θ = Int.fract (4^k θ)` of the tricorn at a repelling periodic point:
for a `ccBet`-triple the three arcs of the *image* triple sum to an integer, and
`ccBet (σa) (σb) (σx)` holds exactly when that sum is `2` (rather than `1`).

It is kept in its own module so that the files that consume it do not have to import the
top-level lemma `Work.LandLeaves.ccBet_angDouble_hardCase` itself.
-/
import Mathlib
import Submission.Work.LandLeaves.Defs
import Submission.Work.LandLeaves.TypeGeometry
import Submission.Work.LandLeaves.eq_mod_one_of_rayAccum_of_angDouble_eq

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.LandLeaves

open LeanEval.ComplexAnalysis (Tantibar)

/-!
## The arithmetic of the hard case of `ccBet_angDouble`

Throughout, `M = 4^k` (`k > 0`), `σ = (angDouble)^[2k] = Int.fract (M ·)`, and

`p = fract (b - a)`, `q = fract (x - b)`, `r = fract (a - x)`, `u = fract (M p)`,
`v = fract (M q)`, `w = fract (M r)`.

For a triple with `ccBet a b x` the three arcs satisfy `p + q + r = 2`, hence
`u + v + w = 2M - (⌊Mp⌋ + ⌊Mq⌋ + ⌊Mr⌋)`, an integer in `[0,3)`.  The image triple satisfies
`ccBet (σa) (σb) (σx)` exactly when `u + v + w = 2`, i.e. exactly when the sum of the floors is
`2M - 2` rather than `2M - 1`.  This reduces the hard case to the geometric statement that the
image triple is not "cyclically consecutive".
-/

/-! ## Elementary `Int.fract` arithmetic -/

/-- `fract` of a difference of fractional parts is the `fract` of the difference. -/
theorem fract_sub_fract (u v : ℝ) : Int.fract (Int.fract u - Int.fract v) = Int.fract (u - v) := by
  rw [Int.fract_eq_fract]
  refine ⟨⌊v⌋ - ⌊u⌋, ?_⟩
  have h1 : u - Int.fract u = (⌊u⌋ : ℝ) := Int.self_sub_fract _
  have h2 : v - Int.fract v = (⌊v⌋ : ℝ) := Int.self_sub_fract _
  push_cast
  linarith

/-- `fract (M * fract t) = fract (M * t)` for the integer `M = 4^k`. -/
theorem fract_mul_four (k : ℕ) (t : ℝ) :
    Int.fract ((4 : ℝ) ^ k * Int.fract t) = Int.fract ((4 : ℝ) ^ k * t) := by
  rw [Int.fract_eq_fract]
  refine ⟨-((4 : ℤ) ^ k * ⌊t⌋), ?_⟩
  have h1 : t - Int.fract t = (⌊t⌋ : ℝ) := Int.self_sub_fract _
  push_cast
  linear_combination (-(4 : ℝ) ^ k) * h1

/-- `fract (A + B) = fract (fract A + fract B)`. -/
theorem fract_add_fracts (A B : ℝ) :
    Int.fract (A + B) = Int.fract (Int.fract A + Int.fract B) := by
  rw [Int.fract_eq_fract]
  refine ⟨⌊A⌋ + ⌊B⌋, ?_⟩
  have h1 : A - Int.fract A = (⌊A⌋ : ℝ) := Int.self_sub_fract _
  have h2 : B - Int.fract B = (⌊B⌋ : ℝ) := Int.self_sub_fract _
  push_cast
  linarith

/-- **The three arcs of a `ccBet`-triple add up to `2`**, in the form
`fract (x - a) = fract (b - a) + fract (x - b) - 1`. -/
theorem fract_arc_eq (a b x : ℝ) (h : ccBet a b x) :
    Int.fract (x - a) = Int.fract (b - a) + Int.fract (x - b) - 1 := by
  have hlow : 0 ≤ Int.fract (x - a) - Int.fract (b - a) + 1 := by
    linarith [Int.fract_nonneg (x - a), Int.fract_lt_one (b - a)]
  have hupp : Int.fract (x - a) - Int.fract (b - a) + 1 < 1 := by linarith [h.2]
  have hsplit : x - b = (x - a) - (b - a) := by ring
  have hstep : Int.fract (x - b)
      = Int.fract (Int.fract (x - a) - Int.fract (b - a)) := by
    rw [hsplit, Int.fract_eq_fract]
    refine ⟨⌊x - a⌋ - ⌊b - a⌋, ?_⟩
    have h1 : x - a - Int.fract (x - a) = (⌊x - a⌋ : ℝ) := Int.self_sub_fract _
    have h2 : b - a - Int.fract (b - a) = (⌊b - a⌋ : ℝ) := Int.self_sub_fract _
    push_cast
    linarith
  have hkey : Int.fract (Int.fract (x - a) - Int.fract (b - a))
      = Int.fract (x - a) - Int.fract (b - a) + 1 := by
    conv_lhs =>
      rw [show Int.fract (x - a) - Int.fract (b - a)
          = (Int.fract (x - a) - Int.fract (b - a) + 1) + ((-1 : ℤ) : ℝ) by push_cast; ring]
      rw [Int.fract_add_intCast]
    exact Int.fract_eq_self.mpr ⟨hlow, hupp⟩
  rw [hstep, hkey]
  ring

/-- The complementary arc: `fract (a - x) = 1 - fract (x - a)` for a nondegenerate angle. -/
theorem fract_compl_arc (a x : ℝ) (h : Int.fract (x - a) ≠ 0) :
    Int.fract (a - x) = 1 - Int.fract (x - a) := by
  have hpos : 0 < Int.fract (x - a) := lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm h)
  have hlt : Int.fract (x - a) < 1 := Int.fract_lt_one _
  have hsplit : a - x = (1 - Int.fract (x - a)) + ((-⌊x - a⌋ - 1 : ℤ) : ℝ) := by
    have h1 : x - a - Int.fract (x - a) = (⌊x - a⌋ : ℝ) := Int.self_sub_fract _
    push_cast
    linarith
  rw [hsplit, Int.fract_add_intCast]
  exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩

/-- **The arcs of the image triple.** -/
theorem image_arcs {k : ℕ} (hk : 0 < k) {a b x : ℝ} (hab : ccBet a b x) :
    Int.fract (((Work.Landing.angDouble)^[2 * k] x) - ((Work.Landing.angDouble)^[2 * k] a))
        = Int.fract (Int.fract ((4 : ℝ) ^ k * Int.fract (b - a))
            + Int.fract ((4 : ℝ) ^ k * Int.fract (x - b))) ∧
      Int.fract (((Work.Landing.angDouble)^[2 * k] b) - ((Work.Landing.angDouble)^[2 * k] a))
        = Int.fract ((4 : ℝ) ^ k * Int.fract (b - a)) := by
  have hsp : Int.fract (x - a) = Int.fract (b - a) + Int.fract (x - b) - 1 :=
    fract_arc_eq a b x hab
  constructor
  · rw [angDouble_iterate_two_mul hk x, angDouble_iterate_two_mul hk a, fract_sub_fract]
    rw [show (4 : ℝ) ^ k * x - (4 : ℝ) ^ k * a = (4 : ℝ) ^ k * (x - a) by ring]
    rw [← fract_mul_four k (x - a), hsp]
    rw [show (4 : ℝ) ^ k
          * (Int.fract (b - a) + Int.fract (x - b) - 1)
        = ((4 : ℝ) ^ k * Int.fract (b - a) + (4 : ℝ) ^ k * Int.fract (x - b))
          + ((-(4 : ℤ) ^ k : ℤ) : ℝ) by push_cast; ring]
    rw [Int.fract_add_intCast, fract_add_fracts]
  · rw [angDouble_iterate_two_mul hk b, angDouble_iterate_two_mul hk a, fract_sub_fract]
    rw [show (4 : ℝ) ^ k * b - (4 : ℝ) ^ k * a = (4 : ℝ) ^ k * (b - a) by ring]
    rw [← fract_mul_four k (b - a)]

/-- **The sum of the image arcs is an integer.** -/
theorem arc_sum_int {k : ℕ} (hk : 0 < k) {a b x : ℝ} (hab : ccBet a b x) :
    ∃ m : ℤ,
      Int.fract ((4 : ℝ) ^ k * Int.fract (b - a))
        + Int.fract ((4 : ℝ) ^ k * Int.fract (x - b))
        + Int.fract ((4 : ℝ) ^ k * Int.fract (a - x)) = m := by
  set p := Int.fract (b - a) with hp
  set q := Int.fract (x - b) with hq
  set r := Int.fract (a - x) with hr
  set s := Int.fract (x - a) with hs
  have hs0 : 0 < s := hab.1
  have hspq : s = p + q - 1 := by
    have h := fract_arc_eq a b x hab
    rw [← hs, ← hp, ← hq] at h
    linarith
  have hr1 : r = 1 - s := by
    have h := fract_compl_arc a x (by rw [← hs]; exact ne_of_gt hs0)
    rw [← hr, ← hs] at h
    linarith
  have hsum : p + q + r = 2 := by linarith
  have hkey : (4 : ℝ) ^ k * p + (4 : ℝ) ^ k * q + (4 : ℝ) ^ k * r = 2 * (4 : ℝ) ^ k := by
    have := congrArg (fun t : ℝ => (4 : ℝ) ^ k * t) hsum
    push_cast at this ⊢
    linarith
  refine ⟨2 * (4 : ℤ) ^ k - (⌊(4 : ℝ) ^ k * p⌋ + ⌊(4 : ℝ) ^ k * q⌋ + ⌊(4 : ℝ) ^ k * r⌋), ?_⟩
  have e1 : Int.fract ((4 : ℝ) ^ k * p) = (4 : ℝ) ^ k * p - (⌊(4 : ℝ) ^ k * p⌋ : ℝ) := by
    have h := Int.self_sub_fract ((4 : ℝ) ^ k * p); linarith
  have e2 : Int.fract ((4 : ℝ) ^ k * q) = (4 : ℝ) ^ k * q - (⌊(4 : ℝ) ^ k * q⌋ : ℝ) := by
    have h := Int.self_sub_fract ((4 : ℝ) ^ k * q); linarith
  have e3 : Int.fract ((4 : ℝ) ^ k * r) = (4 : ℝ) ^ k * r - (⌊(4 : ℝ) ^ k * r⌋ : ℝ) := by
    have h := Int.self_sub_fract ((4 : ℝ) ^ k * r); linarith
  rw [e1, e2, e3]
  push_cast
  linarith [hkey]

/-- **The sum of the image arcs lies in `[0,3)`.** -/
theorem arc_sum_bounds {k : ℕ} {a b x : ℝ} :
    0 ≤ Int.fract ((4 : ℝ) ^ k * Int.fract (b - a))
        + Int.fract ((4 : ℝ) ^ k * Int.fract (x - b))
        + Int.fract ((4 : ℝ) ^ k * Int.fract (a - x)) ∧
      Int.fract ((4 : ℝ) ^ k * Int.fract (b - a))
        + Int.fract ((4 : ℝ) ^ k * Int.fract (x - b))
        + Int.fract ((4 : ℝ) ^ k * Int.fract (a - x)) < 3 := by
  have h1 := Int.fract_nonneg ((4 : ℝ) ^ k * Int.fract (b - a))
  have h2 := Int.fract_nonneg ((4 : ℝ) ^ k * Int.fract (x - b))
  have h3 := Int.fract_nonneg ((4 : ℝ) ^ k * Int.fract (a - x))
  have h4 := Int.fract_lt_one ((4 : ℝ) ^ k * Int.fract (b - a))
  have h5 := Int.fract_lt_one ((4 : ℝ) ^ k * Int.fract (x - b))
  have h6 := Int.fract_lt_one ((4 : ℝ) ^ k * Int.fract (a - x))
  constructor <;> linarith

/-- **The main arithmetic reduction.** -/
theorem ccBet_angDouble_iff_arcSum {k : ℕ} (hk : 0 < k) {a b x : ℝ} (hab : ccBet a b x)
    (hu : Int.fract ((4 : ℝ) ^ k * Int.fract (b - a)) ≠ 0)
    (hv : Int.fract ((4 : ℝ) ^ k * Int.fract (x - b)) ≠ 0)
    (hw : Int.fract ((4 : ℝ) ^ k * Int.fract (a - x)) ≠ 0) :
    ccBet ((Work.Landing.angDouble)^[2 * k] a) ((Work.Landing.angDouble)^[2 * k] b)
        ((Work.Landing.angDouble)^[2 * k] x)
      ↔ Int.fract ((4 : ℝ) ^ k * Int.fract (b - a))
          + Int.fract ((4 : ℝ) ^ k * Int.fract (x - b))
          + Int.fract ((4 : ℝ) ^ k * Int.fract (a - x)) = 2 := by
  obtain ⟨h₁, h₂⟩ := image_arcs hk hab
  set u := Int.fract ((4 : ℝ) ^ k * Int.fract (b - a)) with hu'
  set v := Int.fract ((4 : ℝ) ^ k * Int.fract (x - b)) with hv'
  set w := Int.fract ((4 : ℝ) ^ k * Int.fract (a - x)) with hw'
  obtain ⟨m, hm⟩ := arc_sum_int hk hab
  obtain ⟨hb0, hb3⟩ := arc_sum_bounds (k := k) (a := a) (b := b) (x := x)
  have hu0 : 0 < u := by
    rw [hu']; exact lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hu)
  have hv0 : 0 < v := by
    rw [hv']; exact lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hv)
  have hw0 : 0 < w := by
    rw [hw']; exact lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hw)
  have hu1 : u < 1 := by rw [hu']; exact Int.fract_lt_one _
  have hv1 : v < 1 := by rw [hv']; exact Int.fract_lt_one _
  have hw1 : w < 1 := by rw [hw']; exact Int.fract_lt_one _
  have hTpos : 0 < u + v + w := by linarith
  have hm' : u + v + w = (m : ℝ) := by rw [hm]  -- hmm
  have hT : u + v + w = 1 ∨ u + v + w = 2 := by
    have hmm : u + v + w = (m : ℝ) := hm
    have hmm_pos : 0 < m := by
      have : (0 : ℝ) < (m : ℝ) := by rw [← hmm]; exact hTpos
      exact_mod_cast this
    have hmm_lt3 : m < 3 := by
      have : (m : ℝ) < 3 := by rw [← hmm]; exact hb3
      exact_mod_cast this
    have hm12 : m = 1 ∨ m = 2 := by omega
    rcases hm12 with h | h <;> [left; right] <;> rw [hmm, h] <;> norm_num
  rw [ccBet, h₁, h₂]
  rcases hT with hT | hT
  · have huv1 : u + v < 1 := by linarith
    have hh : Int.fract (u + v) = u + v := by
      rw [Int.fract_eq_self]
      exact ⟨by linarith, huv1⟩
    refine iff_of_false ?_ ?_
    · intro hcon
      rw [hh] at hcon
      linarith [hcon.2, hv0]
    · rw [hT]; norm_num
  · have huv1 : 1 < u + v := by linarith
    have huv2 : u + v < 2 := by linarith
    have hfr : Int.fract (u + v) = u + v - 1 := by
      have h1 : (0 : ℝ) ≤ u + v - 1 := by linarith
      have h2 : u + v - 1 < 1 := by linarith
      conv_lhs =>
        rw [show u + v = (u + v - 1) + ((1 : ℤ) : ℝ) by push_cast; ring]
        rw [Int.fract_add_intCast]
      exact Int.fract_eq_self.mpr ⟨h1, h2⟩
    refine iff_of_true ?_ hT
    constructor
    · rw [hfr]; linarith
    · rw [hfr]; linarith

/-! ## Nondegeneracy of the image arcs -/

/-- **Nondegeneracy.**  If two distinct angles (mod `1`) land at the repelling periodic point
`y`, then their images under the `2k`-fold angle map are again distinct: `fract` of the arc is
carried to `fract` of the arc, and the angle map is injective on the type of `y`. -/
theorem arc_ne_zero_of_rayAccum {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hrep : Work.Landing.IsRepelling c k y)
    {a b : ℝ} (ha : Work.Landing.rayAccum c φ a = {y}) (hb : Work.Landing.rayAccum c φ b = {y})
    (hab : Int.fract (b - a) ≠ 0) :
    Int.fract ((4 : ℝ) ^ k * Int.fract (b - a)) ≠ 0 := by
  intro h0
  obtain ⟨m, hm⟩ := Int.fract_eq_zero_iff.mp h0
  have hkey : ∃ m' : ℤ, (4 : ℝ) ^ k * b = (4 : ℝ) ^ k * a + m' := by
    have hb' : b - a = Int.fract (b - a) + (⌊b - a⌋ : ℝ) := by
      have := Int.self_sub_fract (b - a); linarith
    have h1 : (4 : ℝ) ^ k * b = (4 : ℝ) ^ k * a + (4 : ℝ) ^ k * (b - a) := by ring
    have h2 : (4 : ℝ) ^ k * (b - a)
        = (4 : ℝ) ^ k * Int.fract (b - a) + (4 : ℝ) ^ k * (⌊b - a⌋ : ℝ) := by
      linear_combination (4 : ℝ) ^ k * hb'
    have h3 : (4 : ℝ) ^ k * Int.fract (b - a) = (m : ℝ) := by linarith [hm]
    refine ⟨m + ((4 : ℤ) ^ k) * ⌊b - a⌋, ?_⟩
    push_cast
    linarith [h1, h2, h3]
  obtain ⟨mm, hmm⟩ := eq_mod_one_of_rayAccum_of_angDouble_eq hφ hrep hb ha hkey
  have hmm' : b - a = (mm : ℝ) := by linarith
  exact hab (by rw [hmm', Int.fract_intCast])

/-- **The sum of the image arcs is `1` or `2`.** -/
theorem arc_sum_eq_one_or_two {k : ℕ} (hk : 0 < k) {a b x : ℝ} (hab : ccBet a b x)
    (hu : Int.fract ((4 : ℝ) ^ k * Int.fract (b - a)) ≠ 0)
    (hv : Int.fract ((4 : ℝ) ^ k * Int.fract (x - b)) ≠ 0)
    (hw : Int.fract ((4 : ℝ) ^ k * Int.fract (a - x)) ≠ 0) :
    Int.fract ((4 : ℝ) ^ k * Int.fract (b - a))
        + Int.fract ((4 : ℝ) ^ k * Int.fract (x - b))
        + Int.fract ((4 : ℝ) ^ k * Int.fract (a - x)) = 1 ∨
      Int.fract ((4 : ℝ) ^ k * Int.fract (b - a))
        + Int.fract ((4 : ℝ) ^ k * Int.fract (x - b))
        + Int.fract ((4 : ℝ) ^ k * Int.fract (a - x)) = 2 := by
  obtain ⟨m, hm⟩ := arc_sum_int hk hab
  obtain ⟨hb0, hb3⟩ := arc_sum_bounds (k := k) (a := a) (b := b) (x := x)
  have hu0 : 0 < Int.fract ((4 : ℝ) ^ k * Int.fract (b - a)) :=
    lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hu)
  have hv0 : 0 < Int.fract ((4 : ℝ) ^ k * Int.fract (x - b)) :=
    lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hv)
  have hw0 : 0 < Int.fract ((4 : ℝ) ^ k * Int.fract (a - x)) :=
    lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hw)
  have hm0 : 0 < m := by
    have : (0 : ℝ) < (m : ℝ) := by rw [← hm]; linarith
    exact_mod_cast this
  have hm3 : m < 3 := by
    have : (m : ℝ) < 3 := by rw [← hm]; exact hb3
    exact_mod_cast this
  have : m = 1 ∨ m = 2 := by omega
  rcases this with h | h <;> [left; right] <;> rw [hm, h] <;> norm_num

/-- **The hard case reduced to a count of the image arcs.**  If the three angles `a, b, x` land
at the repelling periodic point `y`, satisfy `ccBet a b x` and the sum of the three image arcs is
not `1` (i.e. the image triple is not cyclically consecutive), then the `2k`-fold angle map
preserves the cyclic order. -/
theorem ccBet_angDouble_of_arcSum_ne_one {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hrep : Work.Landing.IsRepelling c k y)
    {a b x : ℝ} (ha : Work.Landing.rayAccum c φ a = {y})
    (hb : Work.Landing.rayAccum c φ b = {y}) (hx : Work.Landing.rayAccum c φ x = {y})
    (hab : ccBet a b x)
    (hne : Int.fract ((4 : ℝ) ^ k * Int.fract (b - a))
        + Int.fract ((4 : ℝ) ^ k * Int.fract (x - b))
        + Int.fract ((4 : ℝ) ^ k * Int.fract (a - x)) ≠ 1) :
    ccBet ((Work.Landing.angDouble)^[2 * k] a) ((Work.Landing.angDouble)^[2 * k] b)
      ((Work.Landing.angDouble)^[2 * k] x) := by
  have hk : 0 < k := hrep.1.1
  have hp : 0 < Int.fract (b - a) := lt_trans hab.1 hab.2
  have hxq : 0 < Int.fract (x - b) := by
    have h := fract_arc_eq a b x hab
    have := Int.fract_lt_one (b - a)
    linarith [h, hab.1]
  have hr : 0 < Int.fract (a - x) := by
    rw [fract_compl_arc a x (ne_of_gt hab.1)]
    linarith [hab.1, hab.2, Int.fract_lt_one (b - a)]
  have hu := arc_ne_zero_of_rayAccum hφ hrep ha hb (ne_of_gt hp)
  have hv := arc_ne_zero_of_rayAccum hφ hrep hb hx (ne_of_gt hxq)
  have hw := arc_ne_zero_of_rayAccum hφ hrep hx ha (ne_of_gt hr)
  have htwo : Int.fract ((4 : ℝ) ^ k * Int.fract (b - a))
        + Int.fract ((4 : ℝ) ^ k * Int.fract (x - b))
        + Int.fract ((4 : ℝ) ^ k * Int.fract (a - x)) = 2 := by
    rcases arc_sum_eq_one_or_two hk hab hu hv hw with h | h
    · exact absurd h hne
    · exact h
  exact (ccBet_angDouble_iff_arcSum hk hab hu hv hw).mpr htwo

end Work.LandLeaves
