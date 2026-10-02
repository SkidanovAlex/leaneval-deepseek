import Mathlib
import Submission.Work.LandLeaves.TypeGeometry
import Submission.Work.LandLeaves.eq_mod_one_of_rayAccum_of_angDouble_eq

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

/-! ## Auxiliary fract arithmetic for the short-arc case of cyclic-order preservation

`Int.fract` is the fractional part `x - ⌊x⌋` on `ℝ`.  The two lemmas below are the bookkeeping
needed to push the `2k`-fold angle map `angDouble^[2k] θ = fract (4^k θ)` through the cyclic
betweenness relation `ccBet`. -/

/-- The fractional part of a difference of fractional parts is the fractional part of the
difference; equivalently `fract` is insensitive to removing integer parts of the arguments. -/
private lemma fract_fract_sub_fract (u v : ℝ) :
    Int.fract (Int.fract u - Int.fract v) = Int.fract (u - v) := by
  rw [Int.fract_eq_fract]
  refine ⟨⌊v⌋ - ⌊u⌋, ?_⟩
  have h1 : u - Int.fract u = (⌊u⌋ : ℝ) := Int.self_sub_fract u
  have h2 : v - Int.fract v = (⌊v⌋ : ℝ) := Int.self_sub_fract v
  push_cast
  linarith

/-- Multiplication by the integer `4^k` commutes with `Int.fract`: only the fractional part of
the multiplier matters. -/
private lemma fract_mul_fract_four (k : ℕ) (u : ℝ) :
    Int.fract ((4 : ℝ) ^ k * u) = Int.fract ((4 : ℝ) ^ k * Int.fract u) := by
  rw [Int.fract_eq_fract]
  refine ⟨(4 : ℤ) ^ k * ⌊u⌋, ?_⟩
  have h1 : u - Int.fract u = (⌊u⌋ : ℝ) := Int.self_sub_fract u
  push_cast
  linear_combination (4 : ℝ) ^ k * h1

/-- **Short-arc case of cyclic-order preservation.**  If `a, b, x` are angles whose rays all
accumulate at the repelling periodic point `y` and `x` lies strictly counterclockwise between `a`
and `b` along the short arc (`4^k * fract (b - a) ≤ 1`), then after the `2k`-fold angle map the
same is true of the images.

The bound `4^k * fract (b - a) ≤ 1` is exactly the hypothesis that the arc from `a` to `b` does
not wrap: the only delicate point is the limiting case `4^k * fract (b - a) = 1`, which the
geometry excludes — the angles of the type of a repelling periodic point are determined modulo
`1` by `θ ↦ 4^k θ` (`eq_mod_one_of_rayAccum_of_angDouble_eq`), so `4^k (b - a) ∈ ℤ` would force
`b - a ∈ ℤ` and hence `fract (b - a) = 0`, contradicting `0 < fract (x - a) < fract (b - a)`. -/
theorem ccBet_angDouble_of_typeSet_short {c : ℂ} {φ : ℂ → ℂ} (hφ : Work.ParamRays.IsDynBottcher c φ)
    {k : ℕ} {y : ℂ} (hrep : Work.Landing.IsRepelling c k y) {a b x : ℝ}
    (ha : a ∈ Work.LandLeaves.typeSet c φ y) (hb : b ∈ Work.LandLeaves.typeSet c φ y)
    (hx : x ∈ Work.LandLeaves.typeSet c φ y)
    (hab : (4 : ℝ) ^ k * Int.fract (b - a) ≤ 1) (h : Work.LandLeaves.ccBet a b x) :
    Work.LandLeaves.ccBet ((Work.Landing.angDouble)^[2 * k] a) ((Work.Landing.angDouble)^[2 * k] b)
      ((Work.Landing.angDouble)^[2 * k] x) := by
  have hk : 0 < k := hrep.1.1
  have hp : 0 < Int.fract (x - a) := h.1
  have hpq : Int.fract (x - a) < Int.fract (b - a) := h.2
  have hqpos : 0 < Int.fract (b - a) := lt_trans hp hpq
  have hdpos : (0 : ℝ) < (4 : ℝ) ^ k := by positivity
  -- The limiting case `4^k * fract (b - a) = 1` is excluded by the injectivity of the angle map
  -- on the type of `y`.
  have hqne : (4 : ℝ) ^ k * Int.fract (b - a) ≠ 1 := by
    intro heq
    have hkey : ∃ m : ℤ, (4 : ℝ) ^ k * b = (4 : ℝ) ^ k * a + (m : ℝ) := by
      refine ⟨1 + (4 : ℤ) ^ k * ⌊b - a⌋, ?_⟩
      have hb_a : b - a = Int.fract (b - a) + (⌊b - a⌋ : ℝ) := by
        have hh := Int.self_sub_fract (b - a); linarith
      calc (4 : ℝ) ^ k * b
          = (4 : ℝ) ^ k * a + (4 : ℝ) ^ k * (b - a) := by ring
        _ = (4 : ℝ) ^ k * a + (4 : ℝ) ^ k * (Int.fract (b - a) + (⌊b - a⌋ : ℝ)) :=
            congrArg (fun t => (4 : ℝ) ^ k * a + t) (congrArg (fun t => (4 : ℝ) ^ k * t) hb_a)
        _ = (4 : ℝ) ^ k * a + (1 + (4 : ℝ) ^ k * (⌊b - a⌋ : ℝ)) := by rw [mul_add, heq]
        _ = (4 : ℝ) ^ k * a + ((1 + (4 : ℤ) ^ k * ⌊b - a⌋ : ℤ) : ℝ) := by push_cast; ring
    obtain ⟨mm, hmm⟩ :=
      eq_mod_one_of_rayAccum_of_angDouble_eq hφ hrep hb ha hkey
    have hf : Int.fract (b - a) = 0 := by
      have h1 : b - a = ((mm : ℤ) : ℝ) := by linarith
      rw [h1, Int.fract_intCast]
    linarith [hqpos]
  have hq_lt : (4 : ℝ) ^ k * Int.fract (b - a) < 1 := lt_of_le_of_ne hab hqne
  have hp_lt : (4 : ℝ) ^ k * Int.fract (x - a) < 1 := by
    have := mul_lt_mul_of_pos_left hpq hdpos
    linarith
  rw [angDouble_iterate_two_mul hk a, angDouble_iterate_two_mul hk b,
      angDouble_iterate_two_mul hk x]
  unfold Work.LandLeaves.ccBet
  rw [fract_fract_sub_fract (4 ^ k * x) (4 ^ k * a),
      fract_fract_sub_fract (4 ^ k * b) (4 ^ k * a)]
  rw [show (4 : ℝ) ^ k * x - (4 : ℝ) ^ k * a = (4 : ℝ) ^ k * (x - a) by ring,
      show (4 : ℝ) ^ k * b - (4 : ℝ) ^ k * a = (4 : ℝ) ^ k * (b - a) by ring]
  rw [fract_mul_fract_four k (x - a), fract_mul_fract_four k (b - a)]
  have e1 : Int.fract ((4 : ℝ) ^ k * Int.fract (x - a)) = (4 : ℝ) ^ k * Int.fract (x - a) := by
    rw [Int.fract_eq_self]; exact ⟨le_of_lt (mul_pos hdpos hp), hp_lt⟩
  have e2 : Int.fract ((4 : ℝ) ^ k * Int.fract (b - a)) = (4 : ℝ) ^ k * Int.fract (b - a) := by
    rw [Int.fract_eq_self]; exact ⟨le_of_lt (mul_pos hdpos hqpos), hq_lt⟩
  rw [e1, e2]
  exact ⟨mul_pos hdpos hp, mul_lt_mul_of_pos_left hpq hdpos⟩

end Work.LandLeaves
