import Mathlib
import Submission.Work.Implosion.Basic
import Submission.Work.Implosion.Ecalle

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion.Ecalle

/-- As `t → +∞`, the Écalle point map `ζ(t·b) = a·(e^{2abt}+1)/(e^{2abt}−1)` tends to
the fixed point `−a`, provided the multiplier `e^{2abt}` decays: `Re(2ab) < 0`.

Indeed `s(t) = e^{2abt} → 0` because `‖s(t)‖ = e^{Re(2ab)·t}` and `Re(2ab) < 0`, and
`a·(s+1)/(s−1) → a·(0+1)/(0−1) = −a` since `s ↦ a·(s+1)/(s−1)` is continuous at `0`
(where its denominator equals `−1 ≠ 0`). -/
theorem ecallePt_tendsto_fixed (a : ℂ) (ha : a ≠ 0) (b : ℂ) (hb : (2 * a * b).re < 0) :
    Filter.Tendsto (fun t : ℝ => ecalPt a ((t : ℂ) * b)) Filter.atTop (nhds (-a)) := by
  -- `Re(2ab)·t → atBot`, hence `e^{Re(2ab)·t} → 0`.
  have hlin : Filter.Tendsto (fun t : ℝ => (2 * a * b).re * t) Filter.atTop Filter.atBot :=
    (Filter.tendsto_const_mul_atBot_of_neg hb).2 Filter.tendsto_id
  have hexpreal : Filter.Tendsto (fun t : ℝ => Real.exp ((2 * a * b).re * t))
      Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp hlin
  -- Transfer to the complex exponential via the norm.
  have hexp : Filter.Tendsto (fun t : ℝ => Complex.exp ((2 * a * b) * (t : ℂ)))
      Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hnorm : (fun t : ℝ => ‖Complex.exp ((2 * a * b) * (t : ℂ))‖)
        = fun t : ℝ => Real.exp ((2 * a * b).re * t) := by
      funext t
      rw [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      ring_nf
    rw [hnorm]
    exact hexpreal
  -- The Möbius-type expression is continuous at `s = 0`, with value `a·(0+1)/(0-1)`.
  have hnum : Filter.Tendsto
      (fun t : ℝ => a * (Complex.exp ((2 * a * b) * (t : ℂ)) + 1))
      Filter.atTop (nhds (a * (0 + 1))) :=
    (hexp.add tendsto_const_nhds).const_mul a
  have hden : Filter.Tendsto (fun t : ℝ => Complex.exp ((2 * a * b) * (t : ℂ)) - 1)
      Filter.atTop (nhds (0 - 1)) :=
    hexp.sub tendsto_const_nhds
  have hdiv : Filter.Tendsto
      (fun t : ℝ => a * (Complex.exp ((2 * a * b) * (t : ℂ)) + 1)
        / (Complex.exp ((2 * a * b) * (t : ℂ)) - 1))
      Filter.atTop (nhds (a * (0 + 1) / (0 - 1))) :=
    hnum.div hden (by norm_num)
  -- Identify the Écalle point map with the expression above.
  have hfun : (fun t : ℝ => ecalPt a ((t : ℂ) * b))
      = fun t : ℝ => a * (Complex.exp ((2 * a * b) * (t : ℂ)) + 1)
        / (Complex.exp ((2 * a * b) * (t : ℂ)) - 1) := by
    funext t
    simp only [ecalPt, ecalE]
    rw [show 2 * a * ((t : ℂ) * b) = 2 * a * b * (t : ℂ) by ring]
  rw [hfun]
  convert hdiv using 1
  ring_nf

end Work.Implosion.Ecalle
