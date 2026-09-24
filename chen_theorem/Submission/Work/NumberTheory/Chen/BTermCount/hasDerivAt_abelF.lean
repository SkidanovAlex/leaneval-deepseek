import Mathlib

namespace Work.NumberTheory.Chen.BTermCount

/-- Derivative of `t ↦ X / (q log(X/(q t)))`, the Abel weight of the inner prime sum; its derivative is `X / (q t log(X/(q t))²) ≥ 0`, so the weight is non-decreasing (the hypothesis `1 < X/(q s)` keeps the log positive and non-zero). -/
theorem hasDerivAt_abelF {X q s : ℝ} (hq : 0 < q) (hs : 0 < s) (h : 1 < X / (q * s)) :
    HasDerivAt (fun t : ℝ => X / (q * Real.log (X / (q * t))))
      (X / (q * s * (Real.log (X / (q * s))) ^ 2)) s := by
  have hqs : 0 < q * s := mul_pos hq hs
  have hX : 0 < X := by
    have : (1 : ℝ) * (q * s) < X := (lt_div_iff₀ hqs).mp h
    linarith
  have hpos : 0 < X / (q * s) := div_pos hX hqs
  have hL : 0 < Real.log (X / (q * s)) := Real.log_pos h
  -- derivative of `t ↦ q * t` at `s` is `q`
  have h1 : HasDerivAt (fun t : ℝ => q * t) q s := by
    simpa using (hasDerivAt_id s).const_mul q
  -- derivative of `t ↦ X / (q * t)` at `s`
  have hu : HasDerivAt (fun t : ℝ => X / (q * t))
      ((0 * (q * s) - X * q) / (q * s) ^ 2) s :=
    (hasDerivAt_const s X).div h1 (by positivity)
  -- compose with `Real.log`
  have hlog : HasDerivAt (fun t : ℝ => Real.log (X / (q * t)))
      (((0 * (q * s) - X * q) / (q * s) ^ 2) / (X / (q * s))) s :=
    hu.log (ne_of_gt hpos)
  -- multiply by the constant `q`
  have hden : HasDerivAt (fun t : ℝ => q * Real.log (X / (q * t)))
      (q * (((0 * (q * s) - X * q) / (q * s) ^ 2) / (X / (q * s)))) s :=
    hlog.const_mul q
  have hden_ne : q * Real.log (X / (q * s)) ≠ 0 :=
    mul_ne_zero hq.ne' (ne_of_gt hL)
  have hfin := (hasDerivAt_const s X).div hden hden_ne
  -- the resulting derivative expression equals the target value
  have hderiv_eq :
      (0 * (q * Real.log (X / (q * s))) -
          X * (q * ((0 * (q * s) - X * q) / (q * s) ^ 2 / (X / (q * s))))) /
        (q * Real.log (X / (q * s))) ^ 2
        = X / (q * s * (Real.log (X / (q * s))) ^ 2) := by
    field_simp
    ring
  rw [hderiv_eq] at hfin
  exact hfin

end Work.NumberTheory.Chen.BTermCount
