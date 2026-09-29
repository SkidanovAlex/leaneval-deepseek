import Mathlib
import Submission.Work.Fx.piDefs

/-!
# `Work.Fx.piFloor`

`uval p` is the final integer approximation of `2^p * π` produced by the π word:
`Nval p = Dval p * 2^(2p+1) + 2^(qq p - 1)` and `uval p = Nval p / 2^(qq p)` (floor division).

The real content of the π construction is the input hypothesis, which says that
`x := Dval p * 2^(2p+1) / 2^(qq p)` is within `1/2` of `2^p * π`.  Since
`uval p = ⌊x + 1/2⌋` the extraction step can only lose another `1/2`, so the final
answer is within `1`.  This file isolates exactly that rounding argument: it is pure
floor arithmetic plus the (definitional) identity relating `uval` to `x`.
-/

namespace Work.Fx

/-- For any integers `N` and positive `D`, the flooring division `N.fdiv D` is the floor of the
real quotient: `N.fdiv D ≤ N / D < N.fdiv D + 1`. -/
lemma fdiv_floor_bounds {N D : ℤ} (hD : 0 < D) :
    ((N.fdiv D : ℤ) : ℝ) ≤ (N : ℝ) / D ∧ (N : ℝ) / D < ((N.fdiv D : ℤ) : ℝ) + 1 := by
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hdec : N.fdiv D * D + N.fmod D = N := Int.fdiv_mul_add_fmod N D
  have hrnn : 0 ≤ N.fmod D := Int.fmod_nonneg_of_pos N hD
  have hrlt : N.fmod D < D := Int.fmod_lt_of_pos N hD
  have hcast : ((N.fdiv D : ℤ) : ℝ) * (D : ℝ) + ((N.fmod D : ℤ) : ℝ) = (N : ℝ) := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) hdec
    push_cast at h
    linarith
  have hrltR : ((N.fmod D : ℤ) : ℝ) < (D : ℝ) := by exact_mod_cast hrlt
  have hrnnR : (0 : ℝ) ≤ ((N.fmod D : ℤ) : ℝ) := by exact_mod_cast hrnn
  constructor
  · rw [le_div_iff₀ hDR]; linarith
  · rw [div_lt_iff₀ hDR]; linarith

/-- Rounding to the nearest integer: if `x` is within `1/2` of `y` and the integer `N.fdiv D`
is the floor of `x + 1/2`, then `N.fdiv D` is within `1` of `y`. -/
lemma fdiv_round {N D : ℤ} (hD : 0 < D) {x y : ℝ}
    (hz : (N : ℝ) / (D : ℝ) = x + 1 / 2) (hxy : |x - y| ≤ 1 / 2) :
    |((N.fdiv D : ℤ) : ℝ) - y| ≤ 1 := by
  obtain ⟨h1, h2⟩ := fdiv_floor_bounds (N := N) hD
  have hxn : |((N.fdiv D : ℤ) : ℝ) - x| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  calc |((N.fdiv D : ℤ) : ℝ) - y|
      = |(((N.fdiv D : ℤ) : ℝ) - x) + (x - y)| := by ring_nf
    _ ≤ |((N.fdiv D : ℤ) : ℝ) - x| + |x - y| := abs_add_le _ _
    _ ≤ 1 / 2 + 1 / 2 := add_le_add hxn hxy
    _ = 1 := by norm_num

theorem piFloor (p : ℕ) (hp : 1 ≤ p)
    (hD : |(Work.Fx.Dval p : ℝ) * (2 : ℝ) ^ (2 * p + 1) / (2 : ℝ) ^ Work.Fx.qq p
            - (2 : ℝ) ^ p * Real.pi| ≤ 1 / 2) :
    |(Work.Fx.uval p : ℝ) - (2 : ℝ) ^ p * Real.pi| ≤ 1 := by
  have hDpos : (0 : ℤ) < (2 : ℤ) ^ (qq p) := by positivity
  have h1p : 1 ≤ qq p := by simp only [qq]; omega
  refine fdiv_round (N := Nval p) (D := (2 : ℤ) ^ (qq p)) hDpos ?_ hD
  -- `uval p = ⌊Nval p / 2^(qq p)⌋` and `Nval p / 2^(qq p) = x + 1/2`, because `qq p ≥ 1`.
  have hNval_cast : ((Nval p : ℤ) : ℝ)
      = (Dval p : ℝ) * (2 : ℝ) ^ (2 * p + 1) + (2 : ℝ) ^ (qq p - 1) := by
    simp only [Nval]; push_cast; ring
  have hpow_cast : (((2 : ℤ) ^ (qq p) : ℤ) : ℝ) = (2 : ℝ) ^ (qq p) := by push_cast; ring
  have hhalf : (2 : ℝ) ^ (qq p - 1) / (2 : ℝ) ^ (qq p) = 1 / 2 := by
    have h : (2 : ℝ) ^ (qq p) = (2 : ℝ) ^ (qq p - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel h1p]
    rw [h]; field_simp
  rw [hNval_cast, hpow_cast, add_div, hhalf]

end Work.Fx
