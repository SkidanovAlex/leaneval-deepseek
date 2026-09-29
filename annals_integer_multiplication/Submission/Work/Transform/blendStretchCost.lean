import Mathlib
import Submission.Work.Kernel.Raw

namespace Work.Transform

/-- Size bound for a nonneg integer value: `isz z = z.natAbs.size + 2 ≤ |z| + 2`. -/
theorem blendStretch_isz_natCast_le (P : ℕ) : HvdH.isz (P : ℤ) ≤ P + 2 := by
  simp only [HvdH.isz, Int.natAbs_natCast]
  exact Nat.add_le_add_right (Nat.size_le.mpr Nat.lt_two_pow_self) 2

/-- The key arithmetic fact behind the blend-stretch cost bound: the linear-in-`p`
prefactor `2p+9` with a full `P+2` slack fits into `12` copies of the quadratic
prefactor `(p+1)^2`. -/
theorem blendStretch_arith (p P : ℕ) :
    (P + 1) * (2 * p + 9) + (P + 2) + 1 ≤ 12 * ((P + 1) * (p + 1) ^ 2 + 1) := by
  nlinarith [sq_nonneg (p : ℤ)]

/-- Cost term with a `t` factor and an internal coefficient: replacing the cheap
linear prefactor by `12` times the quadratic one and `t` by `t+1` only makes the
term larger. -/
theorem blendStretch_mul_le_scale (a b K t : ℕ) (h : a ≤ 12 * b) :
    t * (K * a) ≤ 12 * K * ((t + 1) * b) := by
  calc t * (K * a) ≤ (t + 1) * (K * (12 * b)) :=
        Nat.mul_le_mul (Nat.le_succ t) (Nat.mul_le_mul_left K h)
    _ = 12 * K * ((t + 1) * b) := by ring

/-- Cost term of the form `K * ((t+1) * a)` with an outer coefficient: again
replacing the linear prefactor by `12` times the quadratic one enlarges it. -/
theorem blendStretch_mul_le_scale' (a b K t : ℕ) (h : a ≤ 12 * b) :
    K * ((t + 1) * a) ≤ 12 * K * ((t + 1) * b) := by
  calc K * ((t + 1) * a) = K * (t + 1) * a := by ring
    _ ≤ K * (t + 1) * (12 * b) := Nat.mul_le_mul_left (K * (t + 1)) h
    _ = 12 * K * ((t + 1) * b) := by ring

/-- Final absorption step: the accumulated `12 * C * X + Km` is dominated by
`(12 * C + 1) * (X + 1)` as soon as `Km ≤ C`. -/
theorem blendStretch_final_arith (C X Km : ℕ) (h : Km ≤ C) :
    12 * C * X + Km ≤ (12 * C + 1) * (X + 1) := by
  nlinarith

theorem blendStretchCost (Ke Km Kf p P t : ℕ) :
    t * (Ke * ((P + 1) * (2 * p + 9) + HvdH.isz (P : ℤ) + 1) + Km * ((P + 1) * (2 * p + 9) + 1))
      + Km + Kf * ((t + 1) * ((P + 1) * (2 * p + 9) + 1))
    ≤ (12 * (Ke + Km + Kf) + 1) * ((t + 1) * ((P + 1) * (p + 1) ^ 2 + 1) + 1) := by
  have hisz := blendStretch_isz_natCast_le P
  have harith := blendStretch_arith p P
  -- The cheap internal prefactor, with `isz` slack, is at most `12 * B`.
  have hA : (P + 1) * (2 * p + 9) + HvdH.isz (P : ℤ) + 1 ≤ 12 * ((P + 1) * (p + 1) ^ 2 + 1) :=
    le_trans (Nat.add_le_add_right (Nat.add_le_add_left hisz ((P + 1) * (2 * p + 9))) 1) harith
  -- ... and so is the version without the `isz` term.
  have hA0 : (P + 1) * (2 * p + 9) + 1 ≤ 12 * ((P + 1) * (p + 1) ^ 2 + 1) :=
    le_trans (Nat.add_le_add_right (Nat.le_add_right ((P + 1) * (2 * p + 9)) (P + 2)) 1) harith
  have hmain : t * (Ke * ((P + 1) * (2 * p + 9) + HvdH.isz (P : ℤ) + 1)
        + Km * ((P + 1) * (2 * p + 9) + 1))
      ≤ (12 * Ke * ((t + 1) * ((P + 1) * (p + 1) ^ 2 + 1))
        + 12 * Km * ((t + 1) * ((P + 1) * (p + 1) ^ 2 + 1))) := by
    rw [Nat.mul_add]
    exact add_le_add (blendStretch_mul_le_scale _ _ Ke t hA)
      (blendStretch_mul_le_scale _ _ Km t hA0)
  calc
    t * (Ke * ((P + 1) * (2 * p + 9) + HvdH.isz (P : ℤ) + 1) + Km * ((P + 1) * (2 * p + 9) + 1))
        + Km + Kf * ((t + 1) * ((P + 1) * (2 * p + 9) + 1))
      ≤ (12 * Ke * ((t + 1) * ((P + 1) * (p + 1) ^ 2 + 1))
        + 12 * Km * ((t + 1) * ((P + 1) * (p + 1) ^ 2 + 1))) + Km
        + 12 * Kf * ((t + 1) * ((P + 1) * (p + 1) ^ 2 + 1)) :=
        add_le_add (add_le_add hmain le_rfl) (blendStretch_mul_le_scale' _ _ Kf t hA0)
    _ = 12 * (Ke + Km + Kf) * ((t + 1) * ((P + 1) * (p + 1) ^ 2 + 1)) + Km := by ring
    _ ≤ (12 * (Ke + Km + Kf) + 1) * ((t + 1) * ((P + 1) * (p + 1) ^ 2 + 1) + 1) :=
        blendStretch_final_arith _ _ _ (by omega)

end Work.Transform
