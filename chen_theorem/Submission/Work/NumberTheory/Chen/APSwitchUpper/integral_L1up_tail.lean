import Mathlib

/-!
# `integral_L1up_tail` — the tail integral of the switched upper bound

We evaluate the elementary integral

  `∫ u in 2..4, ((2/5) * ((4-u)/(u+2))^5 / (1 - ((4-u)/(u+2))^2)) / u`.

On the interval `[2,4]` the substitution `t = (4-u)/(u+2)` maps `[2,4]` onto `[0,1/2]`, so the
integrand is a rational function of `u`; explicitly, using
`1 - ((4-u)/(u+2))^2 = 12 (u-1)/(u+2)^2`, it equals

  `-1/30 - (64/15)/u + (3/10)/(u-1) + (24/5)/(u+2) + (216/5)/(u+2)^3`.

An antiderivative is

  `F u = -(u/30) - (64/15) log u + (3/10) log (u-1) + (24/5) log (u+2) - (108/5)/(u+2)^2`,

and the fundamental theorem of calculus gives the value
`F 4 - F 2 = 41/60 + (51/10) log 3 - (136/15) log 2`.
-/

namespace Work.NumberTheory.Chen.APSwitchUpper

open MeasureTheory Filter
open scoped Topology

noncomputable section

/-- The integrand of `integral_L1up_tail`. -/
private def L1upInt (u : ℝ) : ℝ :=
  ((2 / 5 : ℝ) * ((4 - u) / (u + 2)) ^ 5 / (1 - ((4 - u) / (u + 2)) ^ 2)) / u

/-- The integrand, rewritten as the rational function it agrees with on `[2,4]`. -/
private def L1upRat (u : ℝ) : ℝ :=
  -1 / 30 + (-(64 / 15)) / u + (3 / 10) / (u - 1) + (24 / 5) / (u + 2)
    + (216 / 5) / (u + 2) ^ 3

/-- An antiderivative of `L1upRat`. -/
private def L1upPrim (u : ℝ) : ℝ :=
  -(u / 30) + (-(64 / 15)) * Real.log u + (3 / 10) * Real.log (u - 1)
    + (24 / 5) * Real.log (u + 2) + (-(108 / 5)) / (u + 2) ^ 2

/-- The integrand equals the rational function `L1upRat` away from its poles. -/
private lemma L1upInt_eq_rat {u : ℝ} (hu0 : u ≠ 0) (hu1 : u - 1 ≠ 0) (hu2 : u + 2 ≠ 0) :
    L1upInt u = L1upRat u := by
  have hden : 1 - ((4 - u) / (u + 2)) ^ 2 = 12 * (u - 1) / (u + 2) ^ 2 := by
    field_simp
    ring
  unfold L1upInt L1upRat
  rw [hden]
  field_simp
  ring

/-- `L1upPrim` is a primitive of `L1upRat`. -/
private lemma hasDerivAt_prim {u : ℝ} (hu0 : u ≠ 0) (hu1 : u - 1 ≠ 0) (hu2 : u + 2 ≠ 0) :
    HasDerivAt L1upPrim (L1upRat u) u := by
  have h2 : (u + 2) ^ 2 ≠ 0 := by positivity
  have t1 : HasDerivAt (fun x : ℝ => -(x / 30)) (-(1 / 30)) u :=
    ((hasDerivAt_id u).div_const 30).neg
  have t2 : HasDerivAt (fun x : ℝ => (-(64 / 15)) * Real.log x) ((-(64 / 15)) * u⁻¹) u :=
    (Real.hasDerivAt_log hu0).const_mul (-(64 / 15))
  have t3 : HasDerivAt (fun x : ℝ => (3 / 10) * Real.log (x - 1)) ((3 / 10) * (1 / (u - 1))) u :=
    (((hasDerivAt_id u).sub_const 1).log hu1).const_mul (3 / 10)
  have t4 : HasDerivAt (fun x : ℝ => (24 / 5) * Real.log (x + 2)) ((24 / 5) * (1 / (u + 2))) u :=
    (((hasDerivAt_id u).add_const 2).log hu2).const_mul (24 / 5)
  have t5 : HasDerivAt (fun x : ℝ => (-(108 / 5)) / (x + 2) ^ 2)
      ((0 * (u + 2) ^ 2 - (-(108 / 5)) * (2 * (u + 2) ^ (2 - 1) * 1)) / ((u + 2) ^ 2) ^ 2) u :=
    (hasDerivAt_const u (-(108 / 5))).div (((hasDerivAt_id u).add_const 2).pow 2) h2
  have hsum := ((((t1.add t2).add t3).add t4).add t5)
  have hGF : L1upPrim =ᶠ[𝓝 u]
      ((((fun x : ℝ => -(x / 30)) + fun x : ℝ => (-(64 / 15)) * Real.log x)
          + fun x : ℝ => (3 / 10) * Real.log (x - 1))
        + fun x : ℝ => (24 / 5) * Real.log (x + 2)) + fun x : ℝ => (-(108 / 5)) / (x + 2) ^ 2 :=
    Filter.Eventually.of_forall (fun x => by simp only [L1upPrim, Pi.add_apply])
  have hd : HasDerivAt L1upPrim (-(1 / 30) + -(64 / 15) * u⁻¹ + 3 / 10 * (1 / (u - 1))
      + 24 / 5 * (1 / (u + 2))
      + (0 * (u + 2) ^ 2 - -(108 / 5) * (2 * (u + 2) ^ (2 - 1) * 1)) / ((u + 2) ^ 2) ^ 2) u :=
    hsum.congr_of_eventuallyEq hGF
  have hval : (-(1 / 30) + -(64 / 15) * u⁻¹ + 3 / 10 * (1 / (u - 1)) + 24 / 5 * (1 / (u + 2))
      + (0 * (u + 2) ^ 2 - -(108 / 5) * (2 * (u + 2) ^ (2 - 1) * 1)) / ((u + 2) ^ 2) ^ 2) =
      L1upRat u := by
    simp only [L1upRat, Nat.reduceSub, pow_one, mul_one, zero_mul]
    field_simp
    ring
  rw [hval] at hd
  exact hd

/-- `L1upRat` is continuous on `[2,4]`. -/
private lemma continuousOn_rat : ContinuousOn L1upRat (Set.Icc (2 : ℝ) 4) := by
  have hA : ContinuousOn (fun _ : ℝ => (-1 / 30 : ℝ)) (Set.Icc (2 : ℝ) 4) := continuousOn_const
  have hB : ContinuousOn (fun x : ℝ => (-(64 / 15)) / x) (Set.Icc (2 : ℝ) 4) :=
    ContinuousOn.div continuousOn_const continuousOn_id
      (fun x hx => by intro h; rw [h] at hx; norm_num at hx)
  have hC : ContinuousOn (fun x : ℝ => (3 / 10) / (x - 1)) (Set.Icc (2 : ℝ) 4) :=
    ContinuousOn.div continuousOn_const (continuousOn_id.sub continuousOn_const)
      (fun x hx => by intro h; simp only [sub_eq_zero] at h; linarith [hx.1])
  have hD : ContinuousOn (fun x : ℝ => (24 / 5) / (x + 2)) (Set.Icc (2 : ℝ) 4) :=
    ContinuousOn.div continuousOn_const (continuousOn_id.add continuousOn_const)
      (fun x hx => by intro h; linarith [hx.1])
  have hE : ContinuousOn (fun x : ℝ => (216 / 5) / (x + 2) ^ 3) (Set.Icc (2 : ℝ) 4) :=
    ContinuousOn.div continuousOn_const ((continuousOn_id.add continuousOn_const).pow 3)
      (fun x hx => by apply pow_ne_zero; linarith [hx.1])
  have hsum : ContinuousOn ((fun _ : ℝ => (-1 / 30 : ℝ)) + (fun x : ℝ => (-(64 / 15)) / x)
      + (fun x : ℝ => (3 / 10) / (x - 1)) + (fun x : ℝ => (24 / 5) / (x + 2))
      + (fun x : ℝ => (216 / 5) / (x + 2) ^ 3)) (Set.Icc (2 : ℝ) 4) :=
    (((hA.add hB).add hC).add hD).add hE
  refine hsum.congr ?_
  intro x _
  simp only [L1upRat, Pi.add_apply]

theorem integral_L1up_tail :
    ∫ u in (2 : ℝ)..4,
        ((2 / 5 : ℝ) * ((4 - u) / (u + 2)) ^ 5 / (1 - ((4 - u) / (u + 2)) ^ 2)) / u
      = 41 / 60 + (51 / 10 : ℝ) * Real.log 3 - (136 / 15 : ℝ) * Real.log 2 := by
  have hle : (2 : ℝ) ≤ 4 := by norm_num
  have hderiv : ∀ x ∈ Set.uIcc (2 : ℝ) 4, HasDerivAt L1upPrim (L1upInt x) x := by
    intro x hx
    rw [Set.uIcc_of_le hle] at hx
    have h0 : x ≠ 0 := by intro h; rw [h] at hx; norm_num at hx
    have h1 : x - 1 ≠ 0 := by intro h; linarith [hx.1, sub_eq_zero.mp h]
    have h2 : x + 2 ≠ 0 := by intro h; linarith [hx.1, h]
    rw [L1upInt_eq_rat h0 h1 h2]
    exact hasDerivAt_prim h0 h1 h2
  have hint : IntervalIntegrable L1upInt volume (2 : ℝ) 4 := by
    have hcc : ContinuousOn L1upRat (Set.uIcc (2 : ℝ) 4) := by
      rw [Set.uIcc_of_le hle]; exact continuousOn_rat
    have hc : IntervalIntegrable L1upRat volume (2 : ℝ) 4 := hcc.intervalIntegrable
    refine IntervalIntegrable.congr (g := L1upInt) ?_ hc
    intro x hx
    rw [Set.uIoc_of_le hle] at hx
    have h0 : x ≠ 0 := by intro h; rw [h] at hx; norm_num at hx
    have h1 : x - 1 ≠ 0 := by intro h; linarith [hx.1, sub_eq_zero.mp h]
    have h2 : x + 2 ≠ 0 := by intro h; linarith [hx.1, h]
    exact (L1upInt_eq_rat h0 h1 h2).symm
  have hFTC : (∫ u in (2 : ℝ)..4, L1upInt u) = L1upPrim 4 - L1upPrim 2 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have h6 : Real.log (6 : ℝ) = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  change (∫ u in (2 : ℝ)..4, L1upInt u)
      = 41 / 60 + (51 / 10 : ℝ) * Real.log 3 - (136 / 15 : ℝ) * Real.log 2
  rw [hFTC]
  simp only [L1upPrim]
  norm_num
  rw [h4, h6]
  ring

end

end Work.NumberTheory.Chen.APSwitchUpper
