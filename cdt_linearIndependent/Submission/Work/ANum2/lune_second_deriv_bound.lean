import Mathlib
import Submission.CDTPlan.Interfaces
import Submission.Work.APsi.defs
import Submission.Work.APsi.lune_branch
import Submission.Work.APsi.lune_facts

/-!
# The second-derivative bound for the lune stage of the Theorem-A contour

The lune map of Calegari--Dimitrov--Tang (arXiv:2408.15403, eq. `(firstgobble)`) is

`lune c z = (z·B − B + √(R z))/(2C)`,  `B = 1 + c²`, `C = c² − 1`,

`R z = luneR c z = B²(1+z)² − 16c²z`  (`lune_eq` in `Submission.Work.APsi.defs`); the radicand
avoids the branch cut on the unit disc (`Work.APsi.luneR_slitPlane_of_lt`).  Writing
`R' = luneRd c z = 2B²(1+z) − 16c²`, `R'' = 2B²` one has

`lune'' = (2RR'' − R'²)/(8(c²−1)R^{3/2})`   (`lune_deriv2_aux`),

and the modulus bound

`‖lune''(z)‖ ≤ (1/(4(c²−1)))·(‖R‖^{−3/2}‖R'‖²/2 + ‖R‖^{−1/2}·R'')`   (`norm_lune_deriv2_le`).

For a disc `‖z − z₀‖ ≤ ρ` the quadratic `R` satisfies the exact Taylor identity
`R z = R z₀ + R'(z₀)(z−z₀) + B²(z−z₀)²` (`luneR_taylor`), which bounds
`R'` on the disc by `Rp = ‖R'(z₀)‖ + ρR''` and `‖R z‖` between `Rc − ρRp` and `Rc + ρRp` with
`Rc = ‖R z₀‖`; substituting gives the target `lune_second_deriv_bound`
(real-valued form; the mantissa version `luneM2_sound` follows by rounding).

All results are stated for an arbitrary `c > 1` and specialised at `c = 36/5`.  No
Every step is proved in this file from the workspace library, and the only axioms used
are `propext`, `Classical.choice` and `Quot.sound`.
-/

namespace Work.ANum2

open Submission.CDTPlan Complex Work.APsi Filter
open scoped Topology

/-- The derivative polynomial `R'` of the lune radicand `luneR c`. -/
noncomputable def luneRd (c : ℝ) (z : ℂ) : ℂ :=
  2 * (1 + (c : ℂ) ^ 2) ^ 2 * (1 + z) - 16 * (c : ℂ) ^ 2

theorem hasDerivAt_luneR (c : ℝ) (z : ℂ) :
    HasDerivAt (luneR c) (luneRd c z) z := by
  have h1 : HasDerivAt (fun w : ℂ => (1 : ℂ) + w) 1 z := (hasDerivAt_id z).const_add 1
  have h2 : HasDerivAt (fun w : ℂ => (1 + w) ^ 2) (2 * (1 + z)) z := by
    have h := h1.pow 2
    have h2' : (fun w : ℂ => (1 + w) ^ 2) = (fun w : ℂ => 1 + w) ^ 2 := by
      ext w; simp
    rw [h2']
    refine h.congr_deriv ?_
    norm_num
  have h3 : HasDerivAt (fun w : ℂ => (1 + (c : ℂ) ^ 2) ^ 2 * (1 + w) ^ 2)
      ((1 + (c : ℂ) ^ 2) ^ 2 * (2 * (1 + z))) z := h2.const_mul _
  have h4 : HasDerivAt (fun w : ℂ => 16 * (c : ℂ) ^ 2 * w) (16 * (c : ℂ) ^ 2) z := by
    simpa using (hasDerivAt_id z).const_mul (16 * (c : ℂ) ^ 2)
  have h5 : HasDerivAt (fun w : ℂ => (1 + (c : ℂ) ^ 2) ^ 2 * (1 + w) ^ 2 - 16 * (c : ℂ) ^ 2 * w)
      ((1 + (c : ℂ) ^ 2) ^ 2 * (2 * (1 + z)) - 16 * (c : ℂ) ^ 2) z := h3.sub h4
  have hfun : luneR c = fun w : ℂ =>
      (1 + (c : ℂ) ^ 2) ^ 2 * (1 + w) ^ 2 - 16 * (c : ℂ) ^ 2 * w := rfl
  rw [hfun]
  refine h5.congr_deriv ?_
  simp only [luneRd]
  ring

theorem deriv_luneR (c : ℝ) (z : ℂ) : deriv (luneR c) z = luneRd c z :=
  (hasDerivAt_luneR c z).deriv

theorem hasDerivAt_luneRd (c : ℝ) (z : ℂ) :
    HasDerivAt (luneRd c) (2 * (1 + (c : ℂ) ^ 2) ^ 2) z := by
  have h2 : HasDerivAt (fun w : ℂ => 2 * (1 + (c : ℂ) ^ 2) ^ 2 * (1 + w))
      (2 * (1 + (c : ℂ) ^ 2) ^ 2) z :=
    (((hasDerivAt_id z).const_add 1).const_mul _).congr_deriv (by ring)
  exact (h2.sub_const (16 * (c : ℂ) ^ 2)).congr_deriv (by simp only [luneRd])

theorem deriv_deriv_luneR (c : ℝ) (z : ℂ) :
    deriv (deriv (luneR c)) z = 2 * (1 + (c : ℂ) ^ 2) ^ 2 := by
  have heq : deriv (luneR c) = luneRd c := funext fun w => deriv_luneR c w
  rw [heq]
  exact (hasDerivAt_luneRd c z).deriv

/-- The radicand of the lune map lies in the slit plane on the open unit disc. -/
theorem luneR_mem_slitPlane {c : ℝ} (hc : 1 < c) {z : ℂ} (hz : ‖z‖ < 1) :
    luneR c z ∈ slitPlane := luneR_slitPlane_of_lt hc hz

/-- Exact second-order Taylor identity for the quadratic radicand. -/
theorem luneR_taylor (c : ℝ) (z z0 : ℂ) :
    luneR c z = luneR c z0 + luneRd c z0 * (z - z0)
      + (1 + (c : ℂ) ^ 2) ^ 2 * (z - z0) ^ 2 := by
  simp only [luneR, luneRd]
  ring

/-- Norm of a nonnegative real, as a complex number. -/
theorem norm_ofReal_of_nonneg {r : ℝ} (hr : 0 ≤ r) : ‖(r : ℂ)‖ = r := by
  have h := RCLike.norm_ofReal (K := ℂ) r
  rw [abs_of_nonneg hr] at h
  exact h

/-- Norms of the real constants of the lune map. -/
theorem norm_one_add_sq (c : ℝ) : ‖1 + (c : ℂ) ^ 2‖ = 1 + c ^ 2 := by
  rw [show (1 + (c : ℂ) ^ 2) = (((1 + c ^ 2 : ℝ)) : ℂ) by push_cast; ring]
  exact norm_ofReal_of_nonneg (by positivity)

theorem norm_luneC (c : ℝ) : ‖luneC c‖ = |c ^ 2 - 1| := by
  rw [show luneC c = (((c ^ 2 - 1 : ℝ)) : ℂ) by simp [luneC, luneCr]]
  exact RCLike.norm_ofReal (K := ℂ) _

/-- The explicit first derivative of `lune c` on the open unit disc. -/
theorem deriv_lune_eq (c : ℝ) (hc : 1 < c) (z : ℂ) (hz : ‖z‖ < 1) :
    deriv (lune c) z =
      (luneB c + (1 / 2 : ℂ) * (luneR c z) ^ (-(1 / 2) : ℂ) * luneRd c z)
        / (2 * luneC c) := by
  have hmem : luneR c z ∈ slitPlane := luneR_mem_slitPlane hc hz
  have hR : HasDerivAt (luneR c) (luneRd c z) z := hasDerivAt_luneR c z
  have hu : HasDerivAt (fun w : ℂ => (luneR c w) ^ (1 / 2 : ℂ))
      ((1 / 2 : ℂ) * (luneR c z) ^ ((1 / 2 : ℂ) - 1) * luneRd c z) z :=
    hR.cpow_const (c := (1 / 2 : ℂ)) hmem
  have hu' : HasDerivAt (fun w : ℂ => (luneR c w) ^ (1 / 2 : ℂ))
      ((1 / 2 : ℂ) * (luneR c z) ^ (-(1 / 2) : ℂ) * luneRd c z) z :=
    hu.congr_deriv (by rw [show ((1 / 2 : ℂ) - 1) = -(1 / 2) by norm_num])
  have hid : HasDerivAt (fun w : ℂ => w * luneB c - luneB c) (luneB c) z := by
    have h := ((hasDerivAt_id z).mul_const (luneB c)).sub_const (luneB c)
    refine h.congr_deriv ?_
    simp
  have hnum : HasDerivAt (fun w : ℂ => w * luneB c - luneB c + (luneR c w) ^ (1 / 2 : ℂ))
      (luneB c + (1 / 2 : ℂ) * (luneR c z) ^ (-(1 / 2) : ℂ) * luneRd c z) z :=
    hid.add hu'
  have hF : HasDerivAt (fun w : ℂ => (w * luneB c - luneB c + (luneR c w) ^ (1 / 2 : ℂ))
      / (2 * luneC c))
      ((luneB c + (1 / 2 : ℂ) * (luneR c z) ^ (-(1 / 2) : ℂ) * luneRd c z) / (2 * luneC c)) z :=
    hnum.div_const _
  have hfun : lune c = fun w : ℂ => (w * luneB c - luneB c + (luneR c w) ^ (1 / 2 : ℂ))
      / (2 * luneC c) := funext fun w => lune_eq c w
  rw [hfun, hF.deriv]

/-- The explicit second derivative of `lune c` on the open unit disc. -/
theorem lune_deriv2_aux (c : ℝ) (hc : 1 < c) (z : ℂ) (hz : ‖z‖ < 1) :
    deriv (deriv (lune c)) z =
      ((1 / 2 : ℂ) * ((-(1 / 2 : ℂ)) * (luneR c z) ^ (-(3 / 2) : ℂ) * (luneRd c z) ^ 2
        + (luneR c z) ^ (-(1 / 2) : ℂ) * (2 * (1 + (c : ℂ) ^ 2) ^ 2)))
      / (2 * luneC c) := by
  have hmem : luneR c z ∈ slitPlane := luneR_mem_slitPlane hc hz
  have hball : ∀ᶠ w in 𝓝 z, ‖w‖ < 1 := by
    have h : {w : ℂ | ‖w‖ < 1} ∈ 𝓝 z :=
      (isOpen_lt continuous_norm continuous_const).mem_nhds hz
    exact h
  have h1 : HasDerivAt (fun w : ℂ => (luneR c w) ^ (-(1 / 2) : ℂ))
      ((-(1 / 2 : ℂ)) * (luneR c z) ^ ((-(1 / 2 : ℂ)) - 1) * luneRd c z) z :=
    (hasDerivAt_luneR c z).cpow_const (c := (-(1 / 2) : ℂ)) hmem
  have h1' : HasDerivAt (fun w : ℂ => (luneR c w) ^ (-(1 / 2) : ℂ))
      ((-(1 / 2 : ℂ)) * (luneR c z) ^ (-(3 / 2) : ℂ) * luneRd c z) z :=
    h1.congr_deriv (by rw [show ((-(1 / 2 : ℂ)) - 1) = (-(3 / 2) : ℂ) by norm_num])
  have h2 : HasDerivAt (fun w : ℂ => luneRd c w) (2 * (1 + (c : ℂ) ^ 2) ^ 2) z :=
    hasDerivAt_luneRd c z
  have hX : HasDerivAt (fun w : ℂ => (1 / 2 : ℂ) * (luneR c w) ^ (-(1 / 2) : ℂ) * luneRd c w)
      ((1 / 2 : ℂ) * ((-(1 / 2 : ℂ)) * (luneR c z) ^ (-(3 / 2) : ℂ) * luneRd c z)
        * luneRd c z
        + (1 / 2 : ℂ) * (luneR c z) ^ (-(1 / 2) : ℂ) * (2 * (1 + (c : ℂ) ^ 2) ^ 2)) z :=
    (h1'.const_mul (1 / 2 : ℂ)).mul h2
  have hGeq : deriv (lune c) =ᶠ[𝓝 z] (fun w : ℂ =>
      luneB c / (2 * luneC c)
        + ((1 / 2 : ℂ) * (luneR c w) ^ (-(1 / 2) : ℂ) * luneRd c w) / (2 * luneC c)) :=
    hball.mono fun w hw => by rw [deriv_lune_eq c hc w hw, add_div]
  calc deriv (deriv (lune c)) z
      = deriv (fun w : ℂ => luneB c / (2 * luneC c)
          + ((1 / 2 : ℂ) * (luneR c w) ^ (-(1 / 2) : ℂ) * luneRd c w) / (2 * luneC c)) z :=
        Filter.EventuallyEq.deriv_eq hGeq
    _ = deriv (fun w : ℂ =>
          ((1 / 2 : ℂ) * (luneR c w) ^ (-(1 / 2) : ℂ) * luneRd c w) / (2 * luneC c)) z :=
        deriv_const_add (luneB c / (2 * luneC c))
    _ = deriv (fun w : ℂ => (1 / 2 : ℂ) * (luneR c w) ^ (-(1 / 2) : ℂ) * luneRd c w) z
          / (2 * luneC c) := deriv_div_const (2 * luneC c)
    _ = ((1 / 2 : ℂ) * ((-(1 / 2 : ℂ)) * (luneR c z) ^ (-(3 / 2) : ℂ) * luneRd c z)
          * luneRd c z
          + (1 / 2 : ℂ) * (luneR c z) ^ (-(1 / 2) : ℂ) * (2 * (1 + (c : ℂ) ^ 2) ^ 2))
          / (2 * luneC c) := by rw [hX.deriv]
    _ = ((1 / 2 : ℂ) * ((-(1 / 2 : ℂ)) * (luneR c z) ^ (-(3 / 2) : ℂ) * (luneRd c z) ^ 2
          + (luneR c z) ^ (-(1 / 2) : ℂ) * (2 * (1 + (c : ℂ) ^ 2) ^ 2)))
          / (2 * luneC c) := by ring

/-- Norm estimate for the second derivative of the lune map, in terms of the modulus of the
radicand and its first derivative at the point. -/
theorem norm_lune_deriv2_le (c : ℝ) (hc : 1 < c) (z : ℂ) (hz : ‖z‖ < 1) :
    ‖deriv (deriv (lune c)) z‖ ≤
      (1 / (4 * (c ^ 2 - 1))) * ((1 / 2) * ‖luneR c z‖ ^ (-(3 / 2) : ℝ) * ‖luneRd c z‖ ^ 2
        + ‖luneR c z‖ ^ (-(1 / 2) : ℝ) * (2 * (1 + c ^ 2) ^ 2)) := by
  have hc1 : (0 : ℝ) < c ^ 2 - 1 := by nlinarith
  have hCnorm : ‖(2 : ℂ) * luneC c‖ = 2 * (c ^ 2 - 1) := by
    rw [norm_mul, norm_luneC]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2, abs_of_pos hc1]
  have hnorm3 : ‖(luneR c z) ^ (-(3 / 2) : ℂ)‖ = ‖luneR c z‖ ^ (-(3 / 2) : ℝ) := by
    rw [show (-(3 / 2) : ℂ) = ((-(3 / 2) : ℝ) : ℂ) by norm_num, Complex.norm_cpow_real]
  have hnorm1 : ‖(luneR c z) ^ (-(1 / 2) : ℂ)‖ = ‖luneR c z‖ ^ (-(1 / 2) : ℝ) := by
    rw [show (-(1 / 2) : ℂ) = ((-(1 / 2) : ℝ) : ℂ) by norm_num, Complex.norm_cpow_real]
  have hB2norm : ‖(2 : ℂ) * (1 + (c : ℂ) ^ 2) ^ 2‖ = 2 * (1 + c ^ 2) ^ 2 := by
    rw [norm_mul, norm_pow, norm_one_add_sq]
    norm_num
  have hhalf : ‖(-(1 / 2) : ℂ)‖ = 1 / 2 := by norm_num
  rw [lune_deriv2_aux c hc z hz]
  have hinner : ‖(-(1 / 2 : ℂ)) * (luneR c z) ^ (-(3 / 2) : ℂ) * (luneRd c z) ^ 2
        + (luneR c z) ^ (-(1 / 2) : ℂ) * (2 * (1 + (c : ℂ) ^ 2) ^ 2)‖
      ≤ (1 / 2) * ‖luneR c z‖ ^ (-(3 / 2) : ℝ) * ‖luneRd c z‖ ^ 2
        + ‖luneR c z‖ ^ (-(1 / 2) : ℝ) * (2 * (1 + c ^ 2) ^ 2) := by
    have h2 : ‖(luneRd c z) ^ 2‖ = ‖luneRd c z‖ ^ 2 := norm_pow _ 2
    calc ‖(-(1 / 2 : ℂ)) * (luneR c z) ^ (-(3 / 2) : ℂ) * (luneRd c z) ^ 2
          + (luneR c z) ^ (-(1 / 2) : ℂ) * (2 * (1 + (c : ℂ) ^ 2) ^ 2)‖
        ≤ ‖(-(1 / 2 : ℂ)) * (luneR c z) ^ (-(3 / 2) : ℂ) * (luneRd c z) ^ 2‖
          + ‖(luneR c z) ^ (-(1 / 2) : ℂ) * (2 * (1 + (c : ℂ) ^ 2) ^ 2)‖ := norm_add_le _ _
      _ = (1 / 2) * ‖luneR c z‖ ^ (-(3 / 2) : ℝ) * ‖luneRd c z‖ ^ 2
          + ‖luneR c z‖ ^ (-(1 / 2) : ℝ) * (2 * (1 + c ^ 2) ^ 2) := by
            rw [norm_mul, norm_mul, norm_mul, hhalf, hnorm3, h2, hnorm1, hB2norm]
  calc ‖((1 / 2 : ℂ) * ((-(1 / 2 : ℂ)) * (luneR c z) ^ (-(3 / 2) : ℂ) * (luneRd c z) ^ 2
        + (luneR c z) ^ (-(1 / 2) : ℂ) * (2 * (1 + (c : ℂ) ^ 2) ^ 2))) / (2 * luneC c)‖
      = ‖(1 / 2 : ℂ) * ((-(1 / 2 : ℂ)) * (luneR c z) ^ (-(3 / 2) : ℂ) * (luneRd c z) ^ 2
        + (luneR c z) ^ (-(1 / 2) : ℂ) * (2 * (1 + (c : ℂ) ^ 2) ^ 2))‖ / ‖2 * luneC c‖ :=
        norm_div _ _
    _ = (1 / 2) * ‖(-(1 / 2 : ℂ)) * (luneR c z) ^ (-(3 / 2) : ℂ) * (luneRd c z) ^ 2
        + (luneR c z) ^ (-(1 / 2) : ℂ) * (2 * (1 + (c : ℂ) ^ 2) ^ 2)‖ / (2 * (c ^ 2 - 1)) := by
        rw [norm_mul, hCnorm]
        norm_num
    _ ≤ (1 / 2) * ((1 / 2) * ‖luneR c z‖ ^ (-(3 / 2) : ℝ) * ‖luneRd c z‖ ^ 2
        + ‖luneR c z‖ ^ (-(1 / 2) : ℝ) * (2 * (1 + c ^ 2) ^ 2)) / (2 * (c ^ 2 - 1)) := by
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hinner (by norm_num)) (by positivity)
    _ = (1 / (4 * (c ^ 2 - 1))) * ((1 / 2) * ‖luneR c z‖ ^ (-(3 / 2) : ℝ) * ‖luneRd c z‖ ^ 2
        + ‖luneR c z‖ ^ (-(1 / 2) : ℝ) * (2 * (1 + c ^ 2) ^ 2)) := by
        field_simp
        ring

/-- Elementary real-arithmetic estimate: `a^{-3/2}(A/2 + aB) ≤ t^{-3/2}(A/2 + rhi·B)` for
`0 < t ≤ a ≤ rhi`, `A, B ≥ 0`, written with a common denominator `t·√t`. -/
theorem rpow_neg_bound {a t A B rhi T : ℝ} (ha : 0 < a) (ht : 0 < t) (hta : t ≤ a)
    (hrhi : a ≤ rhi) (hA : 0 ≤ A) (hB : 0 ≤ B) (hT : 0 < T) :
    (1 / (4 * T)) * ((1 / 2) * a ^ (-(3 / 2) : ℝ) * A + a ^ (-(1 / 2) : ℝ) * B)
      ≤ (2 * rhi * B + A) / (8 * T * t * Real.sqrt t) := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have h1 : a ^ (-(3 / 2) : ℝ) = 1 / (a * Real.sqrt a) := by
    rw [Real.rpow_neg ha.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add ha,
      Real.rpow_one, Real.sqrt_eq_rpow]
    ring
  have h2 : a ^ (-(1 / 2) : ℝ) = 1 / Real.sqrt a := by
    rw [Real.rpow_neg ha.le, Real.sqrt_eq_rpow, inv_eq_one_div]
  have hts : t * Real.sqrt t ≤ a * Real.sqrt a := by
    have ht' : Real.sqrt t ≤ Real.sqrt a := Real.sqrt_le_sqrt hta
    nlinarith [Real.sqrt_nonneg t, Real.sqrt_nonneg a]
  have htsr : t * Real.sqrt t ≤ rhi * Real.sqrt a := by
    have h1' : a * Real.sqrt a ≤ rhi * Real.sqrt a :=
      mul_le_mul_of_nonneg_right hrhi (Real.sqrt_nonneg a)
    linarith
  have e1 : t * Real.sqrt t * A / (a * Real.sqrt a) ≤ A := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hts, hA]
  have e2 : 2 * (t * Real.sqrt t) * B / Real.sqrt a ≤ 2 * rhi * B := by
    rw [div_le_iff₀ hsa]
    nlinarith [htsr, hB]
  have hmain : 2 * (t * Real.sqrt t) * (A / (2 * (a * Real.sqrt a)) + B / Real.sqrt a)
      ≤ A + 2 * rhi * B := by
    have hsplit : 2 * (t * Real.sqrt t) * (A / (2 * (a * Real.sqrt a)) + B / Real.sqrt a)
        = t * Real.sqrt t * A / (a * Real.sqrt a)
          + 2 * (t * Real.sqrt t) * B / Real.sqrt a := by
      field_simp
    rw [hsplit]
    linarith
  rw [h1, h2]
  calc (1 / (4 * T)) * ((1 / 2) * (1 / (a * Real.sqrt a)) * A + 1 / Real.sqrt a * B)
      = 2 * (t * Real.sqrt t) * (A / (2 * (a * Real.sqrt a)) + B / Real.sqrt a)
          / (8 * T * (t * Real.sqrt t)) := by
        field_simp
        ring
    _ ≤ (A + 2 * rhi * B) / (8 * T * (t * Real.sqrt t)) :=
        div_le_div_of_nonneg_right hmain (by positivity)
    _ = (2 * rhi * B + A) / (8 * T * t * Real.sqrt t) := by
        rw [show (8 : ℝ) * T * (t * Real.sqrt t) = 8 * T * t * Real.sqrt t by ring]
        ring


/-- **Second-derivative bound for the lune map** (`c > 1`, general parameter): on the disc
`‖z - z0‖ ≤ ρ`, with `R = luneR c`, `R' = luneRd c`, `R'' = 2(1+c²)²`, lower bound `t` for
`‖R‖` and upper bounds `rhi` for `‖R‖`, `Rp` for `‖R'‖`,
`‖lune''(z)‖ ≤ (2·rhi·R'' + Rp²)/(8(c²-1)·t·√t)`. -/
theorem lune_second_deriv_bound_gen (c : ℝ) (hc : 1 < c) (z z0 : ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hz : ‖z - z0‖ ≤ ρ) (hdisc : ‖z0‖ + ρ < 1)
    (hRlo : ρ * (‖luneRd c z0‖ + ρ * (2 * (1 + c ^ 2) ^ 2)) < ‖luneR c z0‖) :
    ‖deriv (deriv (lune c)) z‖ ≤
      (2 * (‖luneR c z0‖ + ρ * (‖luneRd c z0‖ + ρ * (2 * (1 + c ^ 2) ^ 2)))
          * (2 * (1 + c ^ 2) ^ 2)
        + (‖luneRd c z0‖ + ρ * (2 * (1 + c ^ 2) ^ 2)) ^ 2)
      / (8 * (c ^ 2 - 1)
          * (‖luneR c z0‖ - ρ * (‖luneRd c z0‖ + ρ * (2 * (1 + c ^ 2) ^ 2)))
          * Real.sqrt (‖luneR c z0‖ - ρ * (‖luneRd c z0‖ + ρ * (2 * (1 + c ^ 2) ^ 2)))) := by
  have hT : 0 < c ^ 2 - 1 := by nlinarith
  have hzlt : ‖z‖ < 1 := by
    have h1 : ‖z‖ ≤ ‖z - z0‖ + ‖z0‖ := by
      calc ‖z‖ = ‖(z - z0) + z0‖ := by ring_nf
        _ ≤ ‖z - z0‖ + ‖z0‖ := norm_add_le _ _
    linarith
  have ha : 0 < ‖luneR c z‖ := by
    rw [norm_pos_iff]
    exact slitPlane_ne_zero (luneR_mem_slitPlane hc hzlt)
  have hX : (0 : ℝ) ≤ (1 + c ^ 2) ^ 2 := by positivity
  have hB2n : ‖(1 + (c : ℂ) ^ 2) ^ 2‖ = (1 + c ^ 2) ^ 2 := by rw [norm_pow, norm_one_add_sq]
  have hB2n2 : ‖(2 : ℂ) * (1 + (c : ℂ) ^ 2) ^ 2‖ = 2 * (1 + c ^ 2) ^ 2 := by
    rw [norm_mul, hB2n]; norm_num
  have hRsub : luneR c z - luneR c z0
      = luneRd c z0 * (z - z0) + (1 + (c : ℂ) ^ 2) ^ 2 * (z - z0) ^ 2 := by
    rw [luneR_taylor c z z0]; ring
  have hRdiff : ‖luneR c z - luneR c z0‖ ≤ ρ * ‖luneRd c z0‖ + ρ ^ 2 * (1 + c ^ 2) ^ 2 := by
    have h2n : ‖z - z0‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
    calc ‖luneR c z - luneR c z0‖
        = ‖luneRd c z0 * (z - z0) + (1 + (c : ℂ) ^ 2) ^ 2 * (z - z0) ^ 2‖ := by rw [hRsub]
      _ ≤ ‖luneRd c z0 * (z - z0)‖ + ‖(1 + (c : ℂ) ^ 2) ^ 2 * (z - z0) ^ 2‖ := norm_add_le _ _
      _ = ‖luneRd c z0‖ * ‖z - z0‖ + (1 + c ^ 2) ^ 2 * ‖z - z0‖ ^ 2 := by
          rw [norm_mul, norm_mul, hB2n, norm_pow]
      _ ≤ ‖luneRd c z0‖ * ρ + (1 + c ^ 2) ^ 2 * ρ ^ 2 :=
          add_le_add (mul_le_mul_of_nonneg_left hz (norm_nonneg _))
            (mul_le_mul_of_nonneg_left h2n hX)
      _ = ρ * ‖luneRd c z0‖ + ρ ^ 2 * (1 + c ^ 2) ^ 2 := by ring
  have hrdiff2 : ρ ^ 2 * (1 + c ^ 2) ^ 2 ≤ ρ * (ρ * (2 * (1 + c ^ 2) ^ 2)) := by
    nlinarith [sq_nonneg ρ, hX]
  have hhi : ‖luneR c z‖ ≤ ‖luneR c z0‖ + ρ * (‖luneRd c z0‖ + ρ * (2 * (1 + c ^ 2) ^ 2)) := by
    have h1 : ‖luneR c z‖ ≤ ‖luneR c z0‖ + ‖luneR c z - luneR c z0‖ := by
      calc ‖luneR c z‖ = ‖luneR c z0 + (luneR c z - luneR c z0)‖ := by ring_nf
        _ ≤ ‖luneR c z0‖ + ‖luneR c z - luneR c z0‖ := norm_add_le _ _
    linarith
  have hlo : ‖luneR c z0‖ - ρ * (‖luneRd c z0‖ + ρ * (2 * (1 + c ^ 2) ^ 2)) ≤ ‖luneR c z‖ := by
    have h1 : ‖luneR c z0‖ ≤ ‖luneR c z‖ + ‖luneR c z - luneR c z0‖ := by
      calc ‖luneR c z0‖ = ‖luneR c z + (luneR c z0 - luneR c z)‖ := by ring_nf
        _ ≤ ‖luneR c z‖ + ‖luneR c z0 - luneR c z‖ := norm_add_le _ _
        _ = ‖luneR c z‖ + ‖luneR c z - luneR c z0‖ := by rw [norm_sub_rev]
    linarith
  have hlopos : 0 < ‖luneR c z0‖ - ρ * (‖luneRd c z0‖ + ρ * (2 * (1 + c ^ 2) ^ 2)) := by
    linarith [hRlo]
  have hPd : luneRd c z - luneRd c z0 = 2 * (1 + (c : ℂ) ^ 2) ^ 2 * (z - z0) := by
    simp only [luneRd]; ring
  have hP : ‖luneRd c z‖ ≤ ‖luneRd c z0‖ + ρ * (2 * (1 + c ^ 2) ^ 2) := by
    have h1 : ‖luneRd c z‖ ≤ ‖luneRd c z0‖ + ‖luneRd c z - luneRd c z0‖ := by
      calc ‖luneRd c z‖ = ‖luneRd c z0 + (luneRd c z - luneRd c z0)‖ := by ring_nf
        _ ≤ ‖luneRd c z0‖ + ‖luneRd c z - luneRd c z0‖ := norm_add_le _ _
    have h2 : ‖luneRd c z - luneRd c z0‖ ≤ ρ * (2 * (1 + c ^ 2) ^ 2) := by
      have hpos : (0 : ℝ) ≤ 2 * (1 + c ^ 2) ^ 2 := by positivity
      rw [hPd, norm_mul, hB2n2]
      calc 2 * (1 + c ^ 2) ^ 2 * ‖z - z0‖ = ‖z - z0‖ * (2 * (1 + c ^ 2) ^ 2) := by ring
        _ ≤ ρ * (2 * (1 + c ^ 2) ^ 2) := mul_le_mul_of_nonneg_right hz hpos
    linarith
  have hstep := norm_lune_deriv2_le c hc z hzlt
  have hfin := rpow_neg_bound ha hlopos hlo hhi (sq_nonneg ‖luneRd c z‖)
    (le_of_lt (by positivity : (0 : ℝ) < 2 * (1 + c ^ 2) ^ 2)) hT
  refine hstep.trans (hfin.trans ?_)
  have hPsq : ‖luneRd c z‖ ^ 2 ≤ (‖luneRd c z0‖ + ρ * (2 * (1 + c ^ 2) ^ 2)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hP 2
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)


theorem lune_second_deriv_bound (z z0 : ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ) (hz : ‖z - z0‖ ≤ ρ)
    (hdisc : ‖z0‖ + ρ < 1)
    (hRlo : ρ * (‖2 * (1 + (36 / 5 : ℂ) ^ 2) ^ 2 * (1 + z0) - 16 * (36 / 5 : ℂ) ^ 2‖ +
        ρ * (2 * (1 + (36 / 5 : ℝ) ^ 2) ^ 2)) <
      ‖(1 + (36 / 5 : ℂ) ^ 2) ^ 2 * (1 + z0) ^ 2 - 16 * (36 / 5 : ℂ) ^ 2 * z0‖) :
    let Rpp : ℝ := 2 * (1 + (36 / 5 : ℝ) ^ 2) ^ 2
    let Rp : ℝ := ‖2 * (1 + (36 / 5 : ℂ) ^ 2) ^ 2 * (1 + z0) - 16 * (36 / 5 : ℂ) ^ 2‖ + ρ * Rpp
    let Rc : ℝ := ‖(1 + (36 / 5 : ℂ) ^ 2) ^ 2 * (1 + z0) ^ 2 - 16 * (36 / 5 : ℂ) ^ 2 * z0‖
    ‖deriv (deriv (lune (36 / 5))) z‖ ≤
      (2 * (Rc + ρ * Rp) * Rpp + Rp ^ 2) /
        (8 * ((36 / 5 : ℝ) ^ 2 - 1) * (Rc - ρ * Rp) * Real.sqrt (Rc - ρ * Rp)) := by
  have hc : (1 : ℝ) < 36 / 5 := by norm_num
  have hcast : (((36 : ℝ) / 5 : ℝ) : ℂ) = ((36 : ℂ) / 5) := by norm_num
  have hRlo' : ρ * (‖luneRd (36 / 5) z0‖ + ρ * (2 * (1 + (36 / 5 : ℝ) ^ 2) ^ 2))
      < ‖luneR (36 / 5) z0‖ := by
    simpa only [luneRd, luneR, hcast] using hRlo
  have h := lune_second_deriv_bound_gen (36 / 5) hc z z0 ρ hρ hz hdisc hRlo'
  simpa only [luneR, luneRd, hcast] using h

end Work.ANum2


