import Mathlib

/-!
# ZeroFreeTables/Table4/eulerDerivs

The two `z`-derivatives of the logarithmic Euler factor `log p / (p^z - 1)` and the
`HasDerivAt` statements computing them.  Shared by `primeTermDerivNormLe`,
`primeTermDeriv2NormLe` (the pointwise bounds of HB Table 4) and by
`eulerFactorBound` (which carries its own `private` copies of the same objects).
-/

namespace Work.ZeroFreeTables.Table4

open scoped Topology

/-- `‖p^z‖ = p^{Re z}` for a positive natural number `p`. -/
lemma cpow_norm_eq' (p : ℕ) (hp : 0 < p) (z : ℂ) :
    ‖(p : ℂ) ^ z‖ = (p : ℝ) ^ z.re := by
  have h := Complex.norm_cpow_eq_rpow_re_of_pos (show (0 : ℝ) < (p : ℝ) by exact_mod_cast hp) z
  simpa using h

/-- The first `z`-derivative of the Euler factor `log p / (p^z - 1)`:
`-(log p)^2 p^z / (p^z - 1)^2` (denominator written multiplicatively). -/
noncomputable def eulerD1' (p : ℕ) (z : ℂ) : ℂ :=
  -((Real.log (p : ℝ) : ℂ) ^ 2 * (p : ℂ) ^ z / (((p : ℂ) ^ z - 1) * ((p : ℂ) ^ z - 1)))

/-- The second `z`-derivative of the Euler factor `log p / (p^z - 1)`:
`(log p)^3 p^z (p^z + 1) / (p^z - 1)^3` (denominator written multiplicatively). -/
noncomputable def eulerD2' (p : ℕ) (z : ℂ) : ℂ :=
  (Real.log (p : ℝ) : ℂ) ^ 3 * (p : ℂ) ^ z * ((p : ℂ) ^ z + 1)
    / (((p : ℂ) ^ z - 1) * ((p : ℂ) ^ z - 1) * ((p : ℂ) ^ z - 1))

/-- The derivative of `w ↦ log p / (p^w - 1)` at a point where the denominator is non-zero. -/
lemma term_hasDerivAt' (p : ℕ) (hp : p.Prime) (z : ℂ)
    (hne : (p : ℂ) ^ z - 1 ≠ 0) :
    HasDerivAt (fun w : ℂ => (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ w - 1)) (eulerD1' p z) z := by
  have hpc : (p : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_ne_zero]
    exact_mod_cast hp.pos.ne'
  have hlog : Complex.log (p : ℂ) = (Real.log (p : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast p]
    exact (Complex.ofReal_log (x := (p : ℝ)) (by positivity)).symm
  have hA : HasDerivAt (fun w : ℂ => (p : ℂ) ^ w) ((p : ℂ) ^ z * (Real.log (p : ℝ) : ℂ)) z := by
    have h : HasDerivAt (fun w : ℂ => (p : ℂ) ^ w) ((p : ℂ) ^ z * Complex.log (p : ℂ) * 1) z :=
      (hasDerivAt_id z).const_cpow (Or.inl hpc)
    rwa [hlog, mul_one] at h
  have hden : HasDerivAt (fun w : ℂ => (p : ℂ) ^ w - 1)
      ((p : ℂ) ^ z * (Real.log (p : ℝ) : ℂ)) z := hA.sub_const 1
  have h := (hasDerivAt_const z ((Real.log (p : ℝ) : ℂ))).div hden hne
  have hd : deriv (fun w : ℂ => (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ w - 1)) z = eulerD1' p z := by
    rw [show (fun w : ℂ => (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ w - 1))
        = ((fun _ : ℂ => (Real.log (p : ℝ) : ℂ)) / (fun w : ℂ => (p : ℂ) ^ w - 1)) from rfl]
    rw [h.deriv]
    simp only [eulerD1']
    have h2 : ((p : ℂ) ^ z - 1) * ((p : ℂ) ^ z - 1) ≠ 0 := mul_ne_zero hne hne
    have h3 : ((p : ℂ) ^ z - 1) ^ 2 ≠ 0 := pow_ne_zero 2 hne
    field_simp
    ring
  rw [← hd]
  exact h.differentiableAt.hasDerivAt

/-- The derivative of `eulerD1 p` at a point where the denominator is non-zero. -/
lemma derivTerm_hasDerivAt' (p : ℕ) (hp : p.Prime) (z : ℂ)
    (hne : (p : ℂ) ^ z - 1 ≠ 0) :
    HasDerivAt (eulerD1' p) (eulerD2' p z) z := by
  have hpc : (p : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_ne_zero]
    exact_mod_cast hp.pos.ne'
  have hlog : Complex.log (p : ℂ) = (Real.log (p : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast p]
    exact (Complex.ofReal_log (x := (p : ℝ)) (by positivity)).symm
  have hA : HasDerivAt (fun w : ℂ => (p : ℂ) ^ w) ((p : ℂ) ^ z * (Real.log (p : ℝ) : ℂ)) z := by
    have h : HasDerivAt (fun w : ℂ => (p : ℂ) ^ w) ((p : ℂ) ^ z * Complex.log (p : ℂ) * 1) z :=
      (hasDerivAt_id z).const_cpow (Or.inl hpc)
    rwa [hlog, mul_one] at h
  have hnum : HasDerivAt (fun w : ℂ => (Real.log (p : ℝ) : ℂ) ^ 2 * (p : ℂ) ^ w)
      ((Real.log (p : ℝ) : ℂ) ^ 2 * ((p : ℂ) ^ z * (Real.log (p : ℝ) : ℂ))) z :=
    hA.const_mul _
  have hg : HasDerivAt (fun w : ℂ => (p : ℂ) ^ w - 1)
      ((p : ℂ) ^ z * (Real.log (p : ℝ) : ℂ)) z := hA.sub_const 1
  have hden : HasDerivAt (fun w : ℂ => ((p : ℂ) ^ w - 1) * ((p : ℂ) ^ w - 1))
      (((p : ℂ) ^ z * (Real.log (p : ℝ) : ℂ)) * ((p : ℂ) ^ z - 1)
        + ((p : ℂ) ^ z - 1) * ((p : ℂ) ^ z * (Real.log (p : ℝ) : ℂ))) z :=
    hg.mul hg
  have hne2 : ((p : ℂ) ^ z - 1) * ((p : ℂ) ^ z - 1) ≠ 0 := mul_ne_zero hne hne
  have hdiv := hnum.div hden hne2
  have h := hdiv.neg
  have hd : deriv (eulerD1' p) z = eulerD2' p z := by
    rw [show eulerD1' p
        = -(((fun w : ℂ => (Real.log (p : ℝ) : ℂ) ^ 2 * (p : ℂ) ^ w)
            / (fun w : ℂ => ((p : ℂ) ^ w - 1) * ((p : ℂ) ^ w - 1)))) from rfl]
    rw [h.deriv]
    simp only [eulerD2']
    have h3 : ((p : ℂ) ^ z - 1) * ((p : ℂ) ^ z - 1) * ((p : ℂ) ^ z - 1) ≠ 0 :=
      mul_ne_zero hne2 hne
    have h4 : (((p : ℂ) ^ z - 1) * ((p : ℂ) ^ z - 1)) ^ 2 ≠ 0 := pow_ne_zero 2 hne2
    field_simp
    ring
  rw [← hd]
  exact h.differentiableAt.hasDerivAt

/-- The half-plane `{w | 1/2 ≤ Re w}` is a neighbourhood of every `z` with `Re z ≥ 1`. -/
lemma eventually_half_le_re' (z : ℂ) (hz : 1 ≤ z.re) :
    ∀ᶠ w : ℂ in 𝓝 z, (1 / 2 : ℝ) ≤ w.re := by
  have hball : ∀ᶠ w : ℂ in 𝓝 z, dist w z < (1 / 2 : ℝ) := by
    filter_upwards [Metric.ball_mem_nhds z (show (0 : ℝ) < 1 / 2 by norm_num)] with w hw
    rwa [Metric.mem_ball] at hw
  filter_upwards [hball] with w hw
  have h1 : |w.re - z.re| ≤ ‖w - z‖ := by
    have h := Complex.abs_re_le_norm (w - z)
    simpa using h
  rw [dist_eq_norm] at hw
  have h2 : -((1 / 2 : ℝ)) < w.re - z.re := (abs_lt.mp (lt_of_le_of_lt h1 hw)).1
  linarith

/-- For a prime `p` and `Re w ≥ 1/2` the denominator `p^w - 1` is non-zero. -/
lemma cpow_sub_one_ne_zero_of_half' (p : ℕ) (hp : p.Prime) (w : ℂ)
    (hw : (1 / 2 : ℝ) ≤ w.re) : (p : ℂ) ^ w - 1 ≠ 0 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hnorm : ‖(p : ℂ) ^ w‖ = (p : ℝ) ^ w.re := cpow_norm_eq' p hp.pos w
  have hone : (1 : ℝ) < (p : ℝ) ^ w.re := by
    have hpos : (0 : ℝ) < w.re := by linarith
    have h := (Real.rpow_lt_rpow_left_iff hp1).mpr hpos
    rwa [Real.rpow_zero] at h
  intro h
  have h1 : ‖(p : ℂ) ^ w‖ = 1 := by rw [sub_eq_zero.mp h]; simp
  rw [hnorm] at h1
  linarith

end Work.ZeroFreeTables.Table4
