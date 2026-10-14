import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Order.Interval.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SBpsiP.SelfUprime
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25.phiB_barrier =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `phiB_barrier`

The explicit FIX-SB5 barrier `phiB` of `SB25.Defs` satisfies the five conjuncts of
`PhiBBarrier`: it is `C²` on `(0,π/2)`, it is nonnegative there, it blows up at both ends
(`θ → 0⁺` and `θ → (π/2)⁻`), and `𝓐 phiB = -15/4` on `(0,π/2)`, where
`𝓐 f = -f'' - (4 cot 2θ - tan θ) f'`.

The only non-trivial part is the ODE identity.  Writing `s = sin θ`, `c = cos θ`,
`pnum θ = 1 - 5 s³ + 3 s⁵`, `qden θ = 4 s² c³`, a direct differentiation gives
`deriv phiB = -(pnum θ)/qden θ`.  With `gg θ = 4 cos 2θ / sin 2θ - tan θ` one then has
`deriv qden = gg · qden`, so the quotient rule gives
`-deriv (deriv phiB) - gg · deriv phiB = (deriv pnum)/qden`, and finally
`deriv pnum = -(15/4) · qden` (the single place where `sin²θ + cos²θ = 1` enters), so the
expression collapses to `-15/4`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB25

set_option autoImplicit false

/-! ## §1 The algebraic vocabulary of the ODE -/

/-- `1 - 5 sin³θ + 3 sin⁵θ`. -/
def pnum (θ : ℝ) : ℝ := 1 - 5 * Real.sin θ ^ 3 + 3 * Real.sin θ ^ 5

/-- `4 sin²θ cos³θ`.  (Using `cos²θ = 1 - sin²θ` this is `4 sin²θ (1 - sin²θ) cos θ`.) -/
def qden (θ : ℝ) : ℝ := 4 * Real.sin θ ^ 2 * Real.cos θ ^ 3

/-- `-(1 - 5 sin³θ + 3 sin⁵θ)`; it satisfies `deriv phiB = numB/qden`. -/
def numB (θ : ℝ) : ℝ := -(1 - 5 * Real.sin θ ^ 3 + 3 * Real.sin θ ^ 5)

/-- `4 cos 2θ / sin 2θ - tan θ`; the coefficient of `f'` in `𝓐`. -/
def gg (θ : ℝ) : ℝ := 4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ

/-! ## §2 The derivative of `phiB` -/

/-- `deriv pnum θ = -(15/4) · qden θ` (uses `cos²θ = 1 - sin²θ`). -/
lemma hasDerivAt_pnum (θ : ℝ) : HasDerivAt pnum (-(15:ℝ)/4 * qden θ) θ := by
  have h := ((hasDerivAt_const θ (1:ℝ)).sub (((Real.hasDerivAt_sin θ).pow 3).const_mul 5)).add
    (((Real.hasDerivAt_sin θ).pow 5).const_mul 3)
  have hf : pnum = ((fun x : ℝ => 1) - fun y => 5 * (Real.sin ^ 3) y)
      + fun y => 3 * (Real.sin ^ 5) y := by
    funext t; unfold pnum
    simp only [Pi.sub_apply, Pi.add_apply, Pi.pow_apply]
  have hval : (0 - 5 * (↑(3:ℕ) * Real.sin θ ^ (3 - 1) * Real.cos θ)
      + 3 * (↑(5:ℕ) * Real.sin θ ^ (5 - 1) * Real.cos θ)) = -(15:ℝ)/4 * qden θ := by
    unfold qden
    linear_combination (15 * Real.sin θ ^ 2 * Real.cos θ) * Real.sin_sq_add_cos_sq θ
  rw [← hf, hval] at h
  exact h

/-- The raw derivative of `qden`. -/
lemma hasDerivAt_qden (θ : ℝ) :
    HasDerivAt qden (8 * Real.sin θ * Real.cos θ ^ 4 - 12 * Real.sin θ ^ 3 * Real.cos θ ^ 2) θ := by
  have h := (((Real.hasDerivAt_sin θ).pow 2).mul ((Real.hasDerivAt_cos θ).pow 3)).const_mul 4
  convert h using 1
  · funext t; unfold qden; simp only [Pi.pow_apply, Pi.mul_apply]; ring
  · simp only [Pi.pow_apply]; ring

/-- `deriv qden θ = gg θ · qden θ` on the open quadrant. -/
lemma gg_mul_qden {θ : ℝ} (hθ : θ ∈ Ioo 0 (π/2)) :
    gg θ * qden θ
      = 8 * Real.sin θ * Real.cos θ ^ 4 - 12 * Real.sin θ ^ 3 * Real.cos θ ^ 2 := by
  have hs : Real.sin θ ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos]))
  have hc : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  unfold gg qden
  rw [Real.cos_two_mul, Real.sin_two_mul, Real.tan_eq_sin_div_cos]
  field_simp
  linear_combination 16 * Real.sin_sq_add_cos_sq θ

/-- The purely algebraic identity behind `deriv phiB`: the sum of the derivatives of the five
summands of `phiB` equals `-(pnum θ)/qden θ`. -/
lemma phiB_deriv_val {θ : ℝ} (hθ : θ ∈ Ioo 0 (π/2)) :
    ((0 * (4 * Real.sin θ) - 1 * (4 * Real.cos θ)) / (4 * Real.sin θ) ^ 2 +
              (0 * (16 * (1 - Real.sin θ)) - 1 * (16 * -Real.cos θ))
                / (16 * (1 - Real.sin θ)) ^ 2 +
            (0 * (16 * (1 + Real.sin θ)) - 3 * (16 * Real.cos θ))
              / (16 * (1 + Real.sin θ)) ^ 2 -
          3 / 16 * (-Real.cos θ / (1 - Real.sin θ)) -
        9 / 16 * (Real.cos θ / (1 + Real.sin θ)) +
      0) = -(pnum θ) / qden θ := by
  have hsp : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hcpos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hlt1 : Real.sin θ < 1 := by nlinarith [Real.sin_sq_add_cos_sq θ]
  have h1m : 1 - Real.sin θ ≠ 0 := by linarith
  have h1p : 1 + Real.sin θ ≠ 0 := by linarith
  unfold pnum qden
  field_simp
  linear_combination (16 * (-(Real.cos θ) ^ 2 + Real.sin θ ^ 2 - 1)
    * (3 * Real.sin θ ^ 5 - 5 * Real.sin θ ^ 3 + 1)) * Real.sin_sq_add_cos_sq θ

/-- `deriv phiB θ = -(pnum θ)/qden θ` on `(0,π/2)`. -/
lemma hasDerivAt_phiB {θ : ℝ} (hθ : θ ∈ Ioo 0 (π/2)) :
    HasDerivAt phiB (-(pnum θ) / qden θ) θ := by
  have hsp : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hcpos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hlt1 : Real.sin θ < 1 := by nlinarith [Real.sin_sq_add_cos_sq θ]
  have h1m : 1 - Real.sin θ ≠ 0 := by linarith
  have h1p : 1 + Real.sin θ ≠ 0 := by linarith
  have hd1fn : HasDerivAt (fun t : ℝ => 4 * Real.sin t) (4 * Real.cos θ) θ :=
    (Real.hasDerivAt_sin θ).const_mul 4
  have h1 : HasDerivAt (fun t : ℝ => 1 / (4 * Real.sin t))
      ((0 * (4 * Real.sin θ) - 1 * (4 * Real.cos θ)) / (4 * Real.sin θ) ^ 2) θ :=
    (hasDerivAt_const θ (1:ℝ)).div hd1fn (by positivity)
  have hd2fn : HasDerivAt (fun t : ℝ => 16 * (1 - Real.sin t)) (16 * (-Real.cos θ)) θ :=
    ((Real.hasDerivAt_sin θ).const_sub 1).const_mul 16
  have h2 : HasDerivAt (fun t : ℝ => 1 / (16 * (1 - Real.sin t)))
      ((0 * (16 * (1 - Real.sin θ)) - 1 * (16 * (-Real.cos θ)))
        / (16 * (1 - Real.sin θ)) ^ 2) θ :=
    (hasDerivAt_const θ (1:ℝ)).div hd2fn (by positivity)
  have hd3fn : HasDerivAt (fun t : ℝ => 16 * (1 + Real.sin t)) (16 * Real.cos θ) θ :=
    ((Real.hasDerivAt_sin θ).const_add 1).const_mul 16
  have h3 : HasDerivAt (fun t : ℝ => 3 / (16 * (1 + Real.sin t)))
      ((0 * (16 * (1 + Real.sin θ)) - 3 * (16 * Real.cos θ))
        / (16 * (1 + Real.sin θ)) ^ 2) θ :=
    (hasDerivAt_const θ (3:ℝ)).div hd3fn (by positivity)
  have hlog1 : HasDerivAt (fun t : ℝ => Real.log (1 - Real.sin t))
      ((-Real.cos θ) / (1 - Real.sin θ)) θ :=
    ((Real.hasDerivAt_sin θ).const_sub 1).log h1m
  have h4 : HasDerivAt (fun t : ℝ => 3/16 * Real.log (1 - Real.sin t))
      ((3/16) * ((-Real.cos θ) / (1 - Real.sin θ))) θ := hlog1.const_mul (3/16)
  have hlog2 : HasDerivAt (fun t : ℝ => Real.log (1 + Real.sin t))
      ((Real.cos θ) / (1 + Real.sin θ)) θ :=
    ((Real.hasDerivAt_sin θ).const_add 1).log h1p
  have h5 : HasDerivAt (fun t : ℝ => 9/16 * Real.log (1 + Real.sin t))
      ((9/16) * ((Real.cos θ) / (1 + Real.sin θ))) θ := hlog2.const_mul (9/16)
  have hsum := ((((h1.add h2).add h3).sub h4).sub h5).add (hasDerivAt_const θ (1:ℝ))
  rw [show phiB = (fun t : ℝ => 1 / (4 * Real.sin t) + 1 / (16 * (1 - Real.sin t))
      + 3 / (16 * (1 + Real.sin t)) - 3/16 * Real.log (1 - Real.sin t)
      - 9/16 * Real.log (1 + Real.sin t) + 1) from rfl]
  convert hsum using 1
  exact (phiB_deriv_val hθ).symm

/-! ## §3 Positivity, smoothness and the endpoint blow-up -/

/-- On `(0,π/2)`, `sin θ < 1`. -/
lemma sin_lt_one_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Ioo 0 (π/2)) : Real.sin θ < 1 := by
  have hc : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- The two lower bounds for the "remainder" of `phiB` used in the endpoint analysis. -/
lemma phiB_rest_bounds {θ : ℝ} (hθ : θ ∈ Ioo 0 (π/2)) :
    ((0:ℝ) ≤ (16*(1 - Real.sin θ))⁻¹ + 3/(16*(1 + Real.sin θ))
        - 3/16*Real.log (1 - Real.sin θ) - 9/16*Real.log (1 + Real.sin θ) + 1) ∧
    ((0:ℝ) ≤ (4*Real.sin θ)⁻¹ + 3/(16*(1 + Real.sin θ))
        - 3/16*Real.log (1 - Real.sin θ) - 9/16*Real.log (1 + Real.sin θ) + 1) := by
  have hsp : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hlt1 : Real.sin θ < 1 := sin_lt_one_of_mem_Ioo hθ
  have hlog1 : Real.log (1 - Real.sin θ) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have hlog2 : Real.log (1 + Real.sin θ) ≤ Real.log 2 :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog2' : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
  have h1m : (0:ℝ) < 1 - Real.sin θ := by linarith
  have h1p : (0:ℝ) < 1 + Real.sin θ := by linarith
  have hA : (0:ℝ) ≤ (16*(1 - Real.sin θ))⁻¹ := by positivity
  have hA' : (0:ℝ) ≤ (4 * Real.sin θ)⁻¹ := by positivity
  have hB : (0:ℝ) ≤ 3/(16*(1 + Real.sin θ)) := by positivity
  have hC : (0:ℝ) ≤ -(3/16 * Real.log (1 - Real.sin θ)) := by nlinarith [hlog1]
  have hD : -(9/16 * Real.log 2) ≤ -(9/16 * Real.log (1 + Real.sin θ)) := by nlinarith [hlog2]
  have hE : (0:ℝ) ≤ -(9/16 * Real.log 2) + 1 := by nlinarith [hlog2']
  constructor <;> linarith

/-- `phiB θ ≥ (4 sin θ)⁻¹` on `(0,π/2)`. -/
lemma phiB_ge_sin_inv {θ : ℝ} (hθ : θ ∈ Ioo 0 (π/2)) :
    (4 * Real.sin θ)⁻¹ ≤ phiB θ := by
  have he : phiB θ =
      1/(4*Real.sin θ) + 1/(16*(1 - Real.sin θ)) + 3/(16*(1 + Real.sin θ))
        - 3/16*Real.log (1 - Real.sin θ) - 9/16*Real.log (1 + Real.sin θ) + 1 := rfl
  rw [he]
  simp only [one_div]
  linarith [(phiB_rest_bounds hθ).1]

/-- `phiB θ ≥ (16 (1 - sin θ))⁻¹` on `(0,π/2)`. -/
lemma phiB_ge_one_sub {θ : ℝ} (hθ : θ ∈ Ioo 0 (π/2)) :
    (16 * (1 - Real.sin θ))⁻¹ ≤ phiB θ := by
  have he : phiB θ =
      1/(4*Real.sin θ) + 1/(16*(1 - Real.sin θ)) + 3/(16*(1 + Real.sin θ))
        - 3/16*Real.log (1 - Real.sin θ) - 9/16*Real.log (1 + Real.sin θ) + 1 := rfl
  rw [he]
  simp only [one_div]
  linarith [(phiB_rest_bounds hθ).2]

/-- `phiB` is nonnegative on `(0,π/2)`. -/
lemma phiB_nonneg_aux {θ : ℝ} (hθ : θ ∈ Ioo 0 (π/2)) : 0 ≤ phiB θ := by
  have hsp : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  exact le_trans (by positivity) (phiB_ge_sin_inv hθ)

/-- `phiB` is `C²` on `(0,π/2)`. -/
lemma phiB_contDiffOn_aux : ContDiffOn ℝ 2 phiB (Ioo 0 (π/2)) := by
  have hspos : ∀ x ∈ Ioo (0:ℝ) (π/2), 0 < Real.sin x :=
    fun x hx => Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2, Real.pi_pos])
  have hlt1 : ∀ x ∈ Ioo (0:ℝ) (π/2), Real.sin x < 1 := fun x hx => sin_lt_one_of_mem_Ioo hx
  have hsne : ∀ x ∈ Ioo (0:ℝ) (π/2), Real.sin x ≠ 0 := fun x hx => ne_of_gt (hspos x hx)
  have hmne : ∀ x ∈ Ioo (0:ℝ) (π/2), 1 - Real.sin x ≠ 0 :=
    fun x hx => by have := hlt1 x hx; linarith
  have hpne : ∀ x ∈ Ioo (0:ℝ) (π/2), 1 + Real.sin x ≠ 0 :=
    fun x hx => by have := hspos x hx; linarith
  have hsin : ContDiffOn ℝ 2 Real.sin (Ioo 0 (π/2)) := Real.contDiff_sin.contDiffOn
  have h1 : ContDiffOn ℝ 2 (fun x : ℝ => 1/(4*Real.sin x)) (Ioo 0 (π/2)) :=
    (contDiffOn_const (c := (1:ℝ))).div ((contDiffOn_const (c := (4:ℝ))).mul hsin)
      (fun x hx => by have h := hsne x hx; positivity)
  have h2 : ContDiffOn ℝ 2 (fun x : ℝ => 1/(16*(1 - Real.sin x))) (Ioo 0 (π/2)) :=
    (contDiffOn_const (c := (1:ℝ))).div
      ((contDiffOn_const (c := (16:ℝ))).mul
        ((contDiffOn_const (c := (1:ℝ))).sub hsin))
      (fun x hx => by have h := hmne x hx; positivity)
  have h3 : ContDiffOn ℝ 2 (fun x : ℝ => 3/(16*(1 + Real.sin x))) (Ioo 0 (π/2)) :=
    (contDiffOn_const (c := (3:ℝ))).div
      ((contDiffOn_const (c := (16:ℝ))).mul
        ((contDiffOn_const (c := (1:ℝ))).add hsin))
      (fun x hx => by have h := hpne x hx; positivity)
  have h4 : ContDiffOn ℝ 2 (fun x : ℝ => 3/16 * Real.log (1 - Real.sin x)) (Ioo 0 (π/2)) :=
    (contDiffOn_const (c := (3/16:ℝ))).mul
      (((contDiffOn_const (c := (1:ℝ))).sub hsin).log hmne)
  have h5 : ContDiffOn ℝ 2 (fun x : ℝ => 9/16 * Real.log (1 + Real.sin x)) (Ioo 0 (π/2)) :=
    (contDiffOn_const (c := (9/16:ℝ))).mul
      (((contDiffOn_const (c := (1:ℝ))).add hsin).log hpne)
  have htot := ((((h1.add h2).add h3).sub h4).sub h5).add (contDiffOn_const (c := (1:ℝ)))
  refine htot.congr ?_
  intro x hx
  rw [show phiB x = 1/(4*Real.sin x) + 1/(16*(1 - Real.sin x)) + 3/(16*(1 + Real.sin x))
      - 3/16*Real.log (1 - Real.sin x) - 9/16*Real.log (1 + Real.sin x) + 1 from rfl]

/-! ## §4 The two endpoint limits -/

/-- `phiB θ → +∞` as `θ → 0⁺`. -/
lemma phiB_tendsto_zero_aux :
    Filter.Tendsto phiB (nhdsWithin (0:ℝ) (Ioi 0)) Filter.atTop := by
  have hbase : Filter.Tendsto (fun θ : ℝ => (4*θ)⁻¹)
      (nhdsWithin (0:ℝ) (Ioi 0)) Filter.atTop := by
    have h2 : Filter.Tendsto (fun x : ℝ => (1/4:ℝ) * x⁻¹)
        (nhdsWithin (0:ℝ) (Ioi 0)) Filter.atTop :=
      tendsto_inv_nhdsGT_zero.const_mul_atTop (by norm_num)
    convert h2 using 1
    ext θ; rw [mul_inv_rev, one_div]; ring
  rw [Filter.tendsto_atTop] at hbase ⊢
  intro b
  filter_upwards [hbase b, Ioo_mem_nhdsGT (show (0:ℝ) < π/2 by linarith [Real.pi_pos])]
    with θ hb hθ
  have h1 : (4*θ)⁻¹ ≤ (4*Real.sin θ)⁻¹ := by
    refine (inv_le_inv₀ (show (0:ℝ) < 4*θ by linarith [hθ.1])
      (show (0:ℝ) < 4*Real.sin θ by
        have h := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
        positivity)).mpr ?_
    have hs := Real.sin_lt hθ.1
    linarith
  exact le_trans (le_trans hb h1) (phiB_ge_sin_inv hθ)

/-- `phiB θ → +∞` as `θ → (π/2)⁻`. -/
lemma phiB_tendsto_pi_div_two_aux :
    Filter.Tendsto phiB (nhdsWithin (π/2) (Iio (π/2))) Filter.atTop := by
  have hgt : Filter.Tendsto (fun θ : ℝ => 1 - Real.sin θ)
      (nhdsWithin (π/2) (Iio (π/2))) (nhdsWithin (0:ℝ) (Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hcont : Continuous fun θ : ℝ => 1 - Real.sin θ :=
        continuous_const.sub Real.continuous_sin
      have h := hcont.continuousAt.tendsto (x := π/2)
      rw [Real.sin_pi_div_two] at h
      simpa using h.mono_left nhdsWithin_le_nhds
    · apply Filter.mem_of_superset (Ioo_mem_nhdsLT (show (0:ℝ) < π/2 by linarith [Real.pi_pos]))
      intro x hx
      exact sub_pos.mpr (sin_lt_one_of_mem_Ioo hx)
  have hbase : Filter.Tendsto (fun θ : ℝ => (16*(1 - Real.sin θ))⁻¹)
      (nhdsWithin (π/2) (Iio (π/2))) Filter.atTop := by
    have hinv : Filter.Tendsto (fun θ : ℝ => (1 - Real.sin θ)⁻¹)
        (nhdsWithin (π/2) (Iio (π/2))) Filter.atTop :=
      (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).comp hgt
    have h2 : Filter.Tendsto (fun θ : ℝ => (1/16:ℝ) * (1 - Real.sin θ)⁻¹)
        (nhdsWithin (π/2) (Iio (π/2))) Filter.atTop :=
      hinv.const_mul_atTop (by norm_num)
    convert h2 using 1
    ext θ; rw [mul_inv_rev, one_div]; ring
  rw [Filter.tendsto_atTop] at hbase ⊢
  intro b
  filter_upwards [hbase b, Ioo_mem_nhdsLT (show (0:ℝ) < π/2 by linarith [Real.pi_pos])]
    with θ hb hθ
  exact le_trans hb (phiB_ge_one_sub hθ)

/-! ## §5 The ODE identity `𝓐 phiB = -15/4` -/

/-- `𝓐 phiB = -15/4` on `(0,π/2)`, where `𝓐 f = -f'' - (4 cot 2θ - tan θ) f'`. -/
lemma phiB_ode (θ : ℝ) (hθ : θ ∈ Ioo 0 (π/2)) :
    -deriv (deriv phiB) θ - (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ)
      * deriv phiB θ = -(15 / 4) := by
  have hs : Real.sin θ ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos]))
  have hc : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hq : qden θ ≠ 0 := by unfold qden; positivity
  have hnumB : HasDerivAt numB ((15:ℝ)/4 * qden θ) θ := by
    have h := (hasDerivAt_pnum θ).neg
    have hf : numB = fun t : ℝ => -pnum t := rfl
    rw [hf]
    convert h using 1
    ring
  have hqden : HasDerivAt qden (gg θ * qden θ) θ := by
    rw [gg_mul_qden hθ]
    exact hasDerivAt_qden θ
  have hquot : HasDerivAt (fun t => numB t / qden t)
      ((((15:ℝ)/4 * qden θ) * qden θ - numB θ * (gg θ * qden θ)) / (qden θ)^2) θ :=
    hnumB.div hqden hq
  have hpoint : ∀ t ∈ Ioo 0 (π/2), deriv phiB t = numB t / qden t := by
    intro t ht
    have hh := (hasDerivAt_phiB ht).deriv
    rw [hh]; unfold numB pnum; ring
  have hcongr : (fun t : ℝ => numB t / qden t) =ᶠ[𝓝 θ] deriv phiB :=
    Filter.eventually_of_mem (IsOpen.mem_nhds isOpen_Ioo hθ)
      (fun t ht => (hpoint t ht).symm)
  have hdd : deriv (deriv phiB) θ
      = ((((15:ℝ)/4 * qden θ) * qden θ - numB θ * (gg θ * qden θ)) / (qden θ)^2) :=
    (hquot.congr_of_eventuallyEq hcongr.symm).deriv
  rw [hdd, hpoint θ hθ]
  unfold gg
  field_simp
  ring

/-! ## §6 The barrier -/

theorem phiB_barrier : Work.FTS_StreamBdry.SB25.PhiBBarrier :=
  ⟨phiB_contDiffOn_aux, fun θ hθ => phiB_nonneg_aux (θ := θ) hθ,
    phiB_tendsto_zero_aux, phiB_tendsto_pi_div_two_aux, fun θ hθ => phiB_ode θ hθ⟩

end Work.FTS_StreamBdry.SB25
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB5Aux.unif_decay_ratio_proved =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB5Aux.unif_decay_ratio_proved` — leaf E5 (`UnifDecayRatio`)

Pointwise decay in `z` together with *uniform* `∂_θ`- and `∂_θ²`-bounds `K` and vanishing at
the two ends `θ = 0`, `θ = π/2` imply *uniform* decay relative to `s2 θ = sin 2θ`:

`∀ ε > 0, ∃ R, ∀ z ≥ R, ∀ θ ∈ (0,π/2), |P z θ| ≤ ε · sin 2θ`.

## Proof scheme

Fix `ε > 0` and `δ > 0` small (`δ := min (π/8) (ε / (K+1))`), and put `th := 2εδ/π`.

* On the *middle* interval `[δ, π/2 - δ]` the pointwise convergence in `z` upgrades to uniform
  convergence (`SB25Aux.eventually_uniform_abs_le`, using only the `θ`-Lipschitz bound `K`);
  there `sin 2θ ≥ sin 2δ`, so the uniform bound `|P z θ| ≤ ε·sin 2δ` suffices.
* On `[0, δ]` (resp. `[π/2 - δ, π/2]`) the two-sided chord bound
  `SB25Aux.abs_le_chord_left` (resp. its mirror `chord_right`, proved here by reflecting the
  interval) applied with the *reference value* at `δ` (resp. at `π/2 - δ`) gives
  `|P z θ| ≤ (θ/δ)|P z δ| + (K/2)θ(δ-θ)`, and `|P z δ| ≤ th` for `z` large; the result is
  `|P z θ| ≤ θ·(2ε/π + Kδ/2) ≤ θ·(4ε/π) ≤ ε sin 2θ` since `sin 2θ ≥ (4/π)θ` on `[0,π/8]`.

The right-endpoint mirror `chord_right` is proved in this file by applying
`abs_le_chord_left` to the reflected function `θ ↦ F (b - θ)`.  This file deliberately does
**not** import `SB25Aux.abs_le_chord_right`: that module is derived from the still-open
`SB25Aux.chord_bound` and would therefore taint this theorem with `sorryAx`.  The whole proof
below rests only on the `sorry`-free modules `SB25Aux.abs_le_chord_left` and
`SB25Aux.eventually_uniform_abs_le`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB5Aux

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK gaugeMode psiP psiHatP SB5Barrier oddPerS)
open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## §1 The one-dimensional ingredients -/

/-- `∂_θ` of a fixed `z`-slice is the slice of `pth`. -/
private lemma pth_eq_deriv (P : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Spaces.pth P z = deriv (fun θ' => P z θ') := by
  funext θ
  simp only [Work.Spaces.pth]

/-- `∂_θ²` of a fixed `z`-slice is the slice of `pthIter 2`. -/
private lemma pthIter_two_eq (P : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Spaces.pthIter 2 P z = deriv (deriv (fun θ' => P z θ')) := by
  funext θ
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]

/-- Jordan's inequality in the form `(4/π) x ≤ sin 2x` for `x ∈ (0, π/8]`. -/
private lemma sin_two_ge_of_le_pi_div_eight {x : ℝ} (hx : 0 < x) (hx' : x ≤ π / 8) :
    (4 / π) * x ≤ Real.sin (2 * x) := by
  have h := Real.mul_le_sin (x := 2 * x) (by linarith) (by linarith [Real.pi_pos])
  calc (4 / π) * x = (2 / π) * (2 * x) := by ring
    _ ≤ Real.sin (2 * x) := h

/-- **Chord bound at the right endpoint.**  A `C²` function on `(a,b)` with `|F'| ≤ K`,
`|F''| ≤ K`, whose one-sided limit at `b` is `0` and which is continuous at `a` (with value
`F a`), satisfies

`|F θ| ≤ ((b - θ)/(b - a)) |F a| + (K/2) (θ - a) (b - θ)`.

This is the mirror image of `SB25Aux.abs_le_chord_left`, obtained by applying the latter to the
reflected function `x ↦ F (b - x)` on `(0, b - a)`.  Kept public so that other leaves of the
SB2/SB5 plan can reuse it instead of the copy in `SB25Aux.abs_le_chord_right`, which in this
workspace still depends on the open `SB25Aux.chord_bound`.
-/

theorem chord_right {F : ℝ → ℝ} {K a b : ℝ} (hab : a < b)
    (hlim : Filter.Tendsto F (nhdsWithin b (Set.Iio b)) (nhds 0))
    (hcont : Filter.Tendsto F (nhdsWithin a (Set.Ioi a)) (nhds (F a)))
    (hd1 : ∀ θ ∈ Set.Ioo a b, DifferentiableAt ℝ F θ)
    (hd2 : ∀ θ ∈ Set.Ioo a b, DifferentiableAt ℝ (deriv F) θ)
    (hb1 : ∀ θ ∈ Set.Ioo a b, |deriv F θ| ≤ K)
    (hb2 : ∀ θ ∈ Set.Ioo a b, |deriv (deriv F) θ| ≤ K) :
    ∀ θ ∈ Set.Ioo a b, |F θ| ≤ ((b - θ) / (b - a)) * |F a| + (K / 2) * (θ - a) * (b - θ) := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hmem : ∀ x ∈ Set.Ioo (0:ℝ) (b - a), b - x ∈ Set.Ioo a b :=
    fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hC : Continuous (fun x : ℝ => b - x) := continuous_const.sub continuous_id
  -- the reflected variable maps `0⁺` to `b⁻`
  have hsub_lim : Filter.Tendsto (fun x : ℝ => b - x) (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin b (Set.Iio b)) := by
    have hmap : Set.MapsTo (fun x : ℝ => b - x) (Set.Ioi (0:ℝ)) (Set.Iio b) := fun x hx => by
      have hx' : (0:ℝ) < x := hx
      show b - x < b
      linarith
    have ht := (hC.continuousAt (x := (0:ℝ))).continuousWithinAt
      (s := Set.Ioi (0:ℝ)) |>.tendsto_nhdsWithin hmap
    simpa only [sub_zero] using ht
  have hGlim : Filter.Tendsto (fun x : ℝ => F (b - x)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa only [Function.comp_def] using hlim.comp hsub_lim
  -- and `(b-a)⁻` to `a⁺`
  have hsub_lim2 : Filter.Tendsto (fun x : ℝ => b - x) (nhdsWithin (b - a) (Set.Iio (b - a)))
      (nhdsWithin a (Set.Ioi a)) := by
    have hmap : Set.MapsTo (fun x : ℝ => b - x) (Set.Iio (b - a)) (Set.Ioi a) := fun x hx => by
      have hx' : x < b - a := hx
      show a < b - x
      linarith
    have ht := (hC.continuousAt (x := b - a)).continuousWithinAt
      (s := Set.Iio (b - a)) |>.tendsto_nhdsWithin hmap
    simpa only [sub_sub_cancel] using ht
  have hGcont : Filter.Tendsto (fun x : ℝ => F (b - x)) (nhdsWithin (b - a) (Set.Iio (b - a)))
      (nhds (F a)) := by
    simpa only [Function.comp_def, sub_sub_cancel] using hcont.comp hsub_lim2
  have hGcont' : Filter.Tendsto (fun x : ℝ => F (b - x)) (nhdsWithin (b - a) (Set.Iio (b - a)))
      (nhds (F (b - (b - a)))) := by
    simpa only [sub_sub_cancel] using hGcont
  have hGd1 : ∀ x ∈ Set.Ioo (0:ℝ) (b - a), DifferentiableAt ℝ (fun y : ℝ => F (b - y)) x := by
    intro x hx
    exact (hd1 (b - x) (hmem x hx)).comp x
      ((differentiableAt_const (c := b)).sub differentiableAt_id)
  have hGderiv : ∀ x ∈ Set.Ioo (0:ℝ) (b - a),
      deriv (fun y : ℝ => F (b - y)) x = -deriv F (b - x) := by
    intro x hx
    have h1 : HasDerivAt (fun y : ℝ => b - y) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub b
    have h2 := (hd1 (b - x) (hmem x hx)).hasDerivAt.comp x h1
    have hd := h2.deriv
    simp only [Function.comp_def] at hd
    rw [hd]; ring
  have hGderiv_ev : ∀ x ∈ Set.Ioo (0:ℝ) (b - a),
      (deriv (fun y : ℝ => F (b - y))) =ᶠ[nhds x] (fun y => -deriv F (b - y)) := by
    intro x hx
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact hGderiv y hy
  have hGd2 : ∀ x ∈ Set.Ioo (0:ℝ) (b - a),
      DifferentiableAt ℝ (deriv (fun y : ℝ => F (b - y))) x := by
    intro x hx
    exact (Filter.EventuallyEq.differentiableAt_iff (hGderiv_ev x hx)).mpr
      (((hd2 (b - x) (hmem x hx)).comp x
        ((differentiableAt_const (c := b)).sub differentiableAt_id)).neg)
  have hneg : ∀ x ∈ Set.Ioo (0:ℝ) (b - a),
      HasDerivAt (fun y : ℝ => -deriv F (b - y)) (-(deriv (deriv F) (b - x) * -1)) x := by
    intro x hx
    have h1 : HasDerivAt (fun y : ℝ => b - y) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub b
    have h2 : HasDerivAt (deriv F ∘ fun y : ℝ => b - y) (deriv (deriv F) (b - x) * -1) x :=
      (hd2 (b - x) (hmem x hx)).hasDerivAt.comp x h1
    exact h2.neg
  have hGderiv2 : ∀ x ∈ Set.Ioo (0:ℝ) (b - a),
      deriv (deriv (fun y : ℝ => F (b - y))) x = deriv (deriv F) (b - x) := by
    intro x hx
    rw [Filter.EventuallyEq.deriv_eq (hGderiv_ev x hx)]
    have hd := (hneg x hx).deriv
    rw [hd]; ring
  have hGb1 : ∀ x ∈ Set.Ioo (0:ℝ) (b - a), |deriv (fun y : ℝ => F (b - y)) x| ≤ K := by
    intro x hx
    rw [hGderiv x hx, abs_neg]
    exact hb1 (b - x) (hmem x hx)
  have hGb2 : ∀ x ∈ Set.Ioo (0:ℝ) (b - a),
      |deriv (deriv (fun y : ℝ => F (b - y))) x| ≤ K := by
    intro x hx
    rw [hGderiv2 x hx]
    exact hb2 (b - x) (hmem x hx)
  intro θ hθ
  have hkey := Work.FTS_StreamBdry.SB25Aux.abs_le_chord_left
    (F := fun y : ℝ => F (b - y)) (K := K) (a := 0) (b := b - a) hba
    hGlim hGcont' hGd1 hGd2 hGb1 hGb2 (b - θ) ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  simp only [sub_sub_cancel, sub_zero] at hkey
  calc |F θ| ≤ ((b - θ) / (b - a)) * |F a| + K / 2 * (b - θ) * (b - a - (b - θ)) := hkey
    _ = ((b - θ) / (b - a)) * |F a| + K / 2 * (θ - a) * (b - θ) := by ring

/-! ## §2 The leaf -/

/-- **`UnifDecayRatio`** (leaf E5 of the SB5 plan): pointwise decay in `z`, a uniform
`∂_θ`-bound `K`, a uniform `∂_θ²`-bound `K` and vanishing at the two ends `θ = 0`, `θ = π/2`
give uniform decay relative to `s2 θ = sin 2θ`. -/
theorem unif_decay_ratio_proved (P : ℝ → ℝ → ℝ) (K : ℝ) :
    Work.FTS_StreamBdry.SB25.UnifDecayRatio P K := by
  intro hdiff hb1 hb2 hlim hdecay
  have hQd1 : ((1 : ℝ), (π / 4 : ℝ)) ∈ Work.Construction.Qd := by
    rw [Work.FTS_StreamBdry.mem_Qd]
    exact ⟨by norm_num, by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hK : 0 ≤ K := le_trans (abs_nonneg (Work.Spaces.pth P 1 (π / 4))) (hb1 1 (π / 4) hQd1)
  intro ε hε
  set δ : ℝ := min (π / 8) (ε / (K + 1)) with hδdef
  have hK1 : (0 : ℝ) < K + 1 := by linarith
  have hδpos : 0 < δ := lt_min (by linarith [Real.pi_pos]) (by positivity)
  have hδle_eps : δ ≤ ε / (K + 1) := min_le_right _ _
  have hδle8 : δ ≤ π / 8 := min_le_left _ _
  have hδlt : δ < π / 2 := by linarith [Real.pi_pos]
  have hKδ : K * δ ≤ 4 * ε / π := by
    have h1 : K * δ ≤ ε := by
      calc K * δ ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left hδle_eps hK
        _ = K * ε / (K + 1) := by rw [mul_div_assoc]
        _ ≤ ε := by rw [div_le_iff₀ hK1]; nlinarith [hK, hε.le]
    have h2 : ε ≤ 4 * ε / π := by
      rw [le_div_iff₀ Real.pi_pos]
      nlinarith [Real.pi_lt_four, hε.le]
    linarith
  set th : ℝ := 2 * ε * δ / π with hthdef
  have hthpos : 0 < th := by rw [hthdef]; positivity
  have hthδ : th / δ = 2 * ε / π := by
    rw [hthdef]
    field_simp
  have hA : th / δ + K * δ / 2 ≤ 4 * ε / π := by
    have h2 : K * δ / 2 ≤ 2 * ε / π := by
      have h3 := div_le_div_of_nonneg_right hKδ (by norm_num : (0 : ℝ) ≤ 2)
      have h4 : (4 : ℝ) * ε / π / 2 = 2 * ε / π := by ring
      rwa [h4] at h3
    rw [hthδ]
    calc 2 * ε / π + K * δ / 2 = K * δ / 2 + 2 * ε / π := by ring
      _ ≤ 2 * ε / π + 2 * ε / π := add_le_add_left h2 _
      _ = 4 * ε / π := by ring
  -- eventual smallness at the two reference points
  have hsmallδ : ∀ᶠ z in atTop, |P z δ| ≤ th := by
    filter_upwards [(Metric.tendsto_nhds.1 (hdecay δ ⟨hδpos, hδlt⟩)) th hthpos] with z hz
    rw [Real.dist_eq, sub_zero] at hz
    exact le_of_lt hz
  have hsmallr : ∀ᶠ z in atTop, |P z (π / 2 - δ)| ≤ th := by
    filter_upwards
      [(Metric.tendsto_nhds.1 (hdecay (π / 2 - δ) ⟨by linarith, by linarith⟩)) th hthpos]
      with z hz
    rw [Real.dist_eq, sub_zero] at hz
    exact le_of_lt hz
  have hεs : 0 < ε * Real.sin (2 * δ) :=
    mul_pos hε (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
  have hmiddle : ∀ᶠ z in atTop, ∀ θ ∈ Icc δ (π / 2 - δ), |P z θ| ≤ ε * Real.sin (2 * δ) := by
    have hG : ∀ᶠ z in atTop, ∀ θ ∈ Icc δ (π / 2 - δ),
        |P (max z 1) θ| ≤ ε * Real.sin (2 * δ) := by
      refine Work.FTS_StreamBdry.SB25Aux.eventually_uniform_abs_le (F := fun z θ => P (max z 1) θ)
        (K := K) (a := δ) (b := π / 2 - δ) (ε := ε * Real.sin (2 * δ)) (by linarith) hK ?_ ?_ hεs
      · intro z θ hθ θ' hθ'
        have hxQd : ∀ x ∈ Icc δ (π / 2 - δ), (max z 1, x) ∈ Work.Construction.Qd := by
          intro x hx
          rw [Work.FTS_StreamBdry.mem_Qd]
          exact ⟨lt_of_lt_of_le one_pos (le_max_right _ _), by linarith [hδpos, hx.1],
            by linarith [hδpos, hx.2]⟩
        have hFdiff : ∀ x ∈ Icc δ (π / 2 - δ),
            DifferentiableAt ℝ (fun θ' => P (max z 1) θ') x :=
          fun x hx => (hdiff _ x (hxQd x hx)).1
        have hFbnd : ∀ x ∈ Icc δ (π / 2 - δ), ‖deriv (fun θ' => P (max z 1) θ') x‖ ≤ K := by
          intro x hx
          have h := hb1 _ x (hxQd x hx)
          rw [pth_eq_deriv] at h
          rwa [Real.norm_eq_abs]
        have hL := (convex_Icc δ (π / 2 - δ)).norm_image_sub_le_of_norm_deriv_le hFdiff hFbnd hθ' hθ
        rwa [Real.norm_eq_abs, Real.norm_eq_abs] at hL
      · intro θ hθ
        refine (hdecay θ ⟨by linarith [hδpos, hθ.1], by linarith [hδpos, hθ.2]⟩).congr' ?_
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
        simp only [max_eq_left hz]
    filter_upwards [hG, eventually_ge_atTop (1 : ℝ)] with z hz hz1
    simp only [max_eq_left hz1] at hz
    exact hz
  have hall : ∀ᶠ z in atTop, |P z δ| ≤ th ∧ |P z (π / 2 - δ)| ≤ th ∧
      (∀ θ ∈ Icc δ (π / 2 - δ), |P z θ| ≤ ε * Real.sin (2 * δ)) := by
    filter_upwards [hsmallδ, hsmallr, hmiddle] with z h1 h2 h3
    exact ⟨h1, h2, h3⟩
  rw [Filter.eventually_atTop] at hall
  obtain ⟨R, hR⟩ := hall
  refine ⟨max R 1, ?_⟩
  intro z θ hz hθ
  have hzR : R ≤ z := le_trans (le_max_left _ _) hz
  have hzpos : 0 < z := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hz)
  obtain ⟨hrefδ, hrefr, hmid⟩ := hR z hzR
  have hzQd : ∀ x ∈ Ioo (0 : ℝ) (π / 2), (z, x) ∈ Work.Construction.Qd := by
    intro x hx
    rw [Work.FTS_StreamBdry.mem_Qd]
    exact ⟨hzpos, hx.1, hx.2⟩
  rcases lt_or_ge θ δ with hlt | hge
  · -- near θ = 0
    have hFlim : Tendsto (fun θ' => P z θ') (nhdsWithin 0 (Ioi 0)) (nhds 0) := (hlim z hzpos).1
    have hFcont : Tendsto (fun θ' => P z θ') (nhdsWithin δ (Iio δ)) (nhds (P z δ)) :=
      ((hdiff z δ (hzQd δ ⟨hδpos, hδlt⟩)).1.continuousAt).tendsto.mono_left inf_le_left
    have hmain := Work.FTS_StreamBdry.SB25Aux.abs_le_chord_left (F := fun θ' => P z θ') (K := K)
      (a := 0) (b := δ) hδpos hFlim hFcont
      (fun x hx => (hdiff z x (hzQd x ⟨hx.1, lt_trans hx.2 hδlt⟩)).1)
      (fun x hx => by
        have h := (hdiff z x (hzQd x ⟨hx.1, lt_trans hx.2 hδlt⟩)).2
        rwa [pth_eq_deriv] at h)
      (fun x hx => by
        have h := hb1 z x (hzQd x ⟨hx.1, lt_trans hx.2 hδlt⟩)
        rwa [pth_eq_deriv] at h)
      (fun x hx => by
        have h := hb2 z x (hzQd x ⟨hx.1, lt_trans hx.2 hδlt⟩)
        rwa [pthIter_two_eq] at h)
      θ ⟨hθ.1, hlt⟩
    have hsin := sin_two_ge_of_le_pi_div_eight (x := θ) (by linarith [hθ.1]) (by linarith)
    calc |P z θ| ≤ (θ / δ) * |P z δ| + K / 2 * θ * (δ - θ) := by simpa using hmain
      _ ≤ (θ / δ) * th + K / 2 * θ * δ := by
          have h1 : (θ / δ) * |P z δ| ≤ (θ / δ) * th :=
            mul_le_mul_of_nonneg_left hrefδ (le_of_lt (div_pos hθ.1 hδpos))
          have h2 : K / 2 * θ * (δ - θ) ≤ K / 2 * θ * δ := by
            have hXY : δ - θ ≤ δ := by linarith [hθ.1]
            have hX : 0 ≤ K / 2 * θ := mul_nonneg (by linarith) (le_of_lt hθ.1)
            exact mul_le_mul_of_nonneg_left hXY hX
          linarith
      _ = θ * (th / δ + K * δ / 2) := by ring_nf
      _ ≤ θ * (4 * ε / π) := mul_le_mul_of_nonneg_left hA (by linarith [hθ.1])
      _ = ε * ((4 / π) * θ) := by ring
      _ ≤ ε * Real.sin (2 * θ) := mul_le_mul_of_nonneg_left hsin hε.le
      _ = ε * Work.Construction.s2 θ := by rw [Work.Construction.s2_eq]
  · rcases le_or_gt θ (π / 2 - δ) with hmidθ | hgt
    · -- middle region
      have hθmem : θ ∈ Icc δ (π / 2 - δ) := ⟨hge, hmidθ⟩
      have hsinmono : Real.sin (2 * δ) ≤ Real.sin (2 * θ) := by
        rcases le_or_gt θ (π / 4) with h4 | h4
        · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
            (by linarith) (by linarith)
        · rw [← Real.sin_pi_sub (2 * θ)]
          exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
            (by linarith) (by linarith)
      calc |P z θ| ≤ ε * Real.sin (2 * δ) := hmid θ hθmem
        _ ≤ ε * Real.sin (2 * θ) := mul_le_mul_of_nonneg_left hsinmono hε.le
        _ = ε * Work.Construction.s2 θ := by rw [Work.Construction.s2_eq]
    · -- near θ = π/2
      have hFlim : Tendsto (fun θ' => P z θ') (nhdsWithin (π / 2) (Iio (π / 2))) (nhds 0) :=
        (hlim z hzpos).2
      have hFcont : Tendsto (fun θ' => P z θ') (nhdsWithin (π / 2 - δ) (Ioi (π / 2 - δ)))
          (nhds (P z (π / 2 - δ))) :=
        ((hdiff z (π / 2 - δ) (hzQd _ ⟨by linarith, by linarith⟩)).1.continuousAt).tendsto.mono_left
          inf_le_left
      have hmain := chord_right (F := fun θ' => P z θ') (K := K)
        (a := π / 2 - δ) (b := π / 2) (by linarith) hFlim hFcont
        (fun x hx => (hdiff z x (hzQd x ⟨by linarith [hx.1], by linarith [hx.2]⟩)).1)
        (fun x hx => by
          have h := (hdiff z x (hzQd x ⟨by linarith [hx.1], by linarith [hx.2]⟩)).2
          rwa [pth_eq_deriv] at h)
        (fun x hx => by
          have h := hb1 z x (hzQd x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
          rwa [pth_eq_deriv] at h)
        (fun x hx => by
          have h := hb2 z x (hzQd x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
          rwa [pthIter_two_eq] at h)
        θ ⟨hgt, hθ.2⟩
      have hmain' : |P z θ| ≤ ((π / 2 - θ) / δ) * |P z (π / 2 - δ)|
          + K / 2 * (θ - (π / 2 - δ)) * (π / 2 - θ) := by
        have h := hmain
        rw [show (π / 2 : ℝ) - (π / 2 - δ) = δ by ring] at h
        exact h
      have hsin := sin_two_ge_of_le_pi_div_eight (x := π / 2 - θ)
        (by linarith [hθ.2]) (by linarith [hδle8, hgt])
      have hsin2 : Real.sin (2 * θ) = Real.sin (2 * (π / 2 - θ)) := by
        rw [show 2 * θ = π - 2 * (π / 2 - θ) by ring, Real.sin_pi_sub]
      calc |P z θ| ≤ ((π / 2 - θ) / δ) * |P z (π / 2 - δ)|
            + K / 2 * (θ - (π / 2 - δ)) * (π / 2 - θ) := hmain'
        _ ≤ ((π / 2 - θ) / δ) * th + K / 2 * δ * (π / 2 - θ) := by
            have h1 : ((π / 2 - θ) / δ) * |P z (π / 2 - δ)| ≤ ((π / 2 - θ) / δ) * th :=
              mul_le_mul_of_nonneg_left hrefr (div_nonneg (by linarith [hθ.2]) (le_of_lt hδpos))
            have hXY : θ - (π / 2 - δ) ≤ δ := by linarith [hθ.2]
            have hX : 0 ≤ K / 2 * (π / 2 - θ) := mul_nonneg (by linarith) (by linarith [hθ.2])
            have h2 : K / 2 * (θ - (π / 2 - δ)) * (π / 2 - θ) ≤ K / 2 * δ * (π / 2 - θ) := by
              calc K / 2 * (θ - (π / 2 - δ)) * (π / 2 - θ)
                  = K / 2 * (π / 2 - θ) * (θ - (π / 2 - δ)) := by ring
                _ ≤ K / 2 * (π / 2 - θ) * δ := mul_le_mul_of_nonneg_left hXY hX
                _ = K / 2 * δ * (π / 2 - θ) := by ring
            linarith
        _ = (π / 2 - θ) * (th / δ + K * δ / 2) := by ring_nf
        _ ≤ (π / 2 - θ) * (4 * ε / π) := mul_le_mul_of_nonneg_left hA (by linarith [hθ.2])
        _ = ε * ((4 / π) * (π / 2 - θ)) := by ring
        _ ≤ ε * Real.sin (2 * θ) := by
            rw [hsin2]
            exact mul_le_mul_of_nonneg_left hsin hε.le
        _ = ε * Work.Construction.s2 θ := by rw [Work.Construction.s2_eq]

end Work.FTS_StreamBdry.SB5Aux
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SBpsiP.DzJ_crux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SBpsiP.DzJ_crux` — differentiating the scaled parameter integral

The level-0 representation of the stream function is
`psiP αG Ψ = -(s2 θ/αG)·J c (U'(Ψ))` with `c = 3/αG - 1` and the *scaled parameter integral*

  `J c h z θ = ∫₀¹ v^c · h (z v) θ dv`.

This file proves that `D_z = z ∂_z` may be moved inside that integral:

  `D_z (J c h) z θ = J c (D_z h) z θ`   on the open quadrant `Qd = (0,∞) × (0,π/2)`,

together with the differentiability of the `z`-slice of `J c h`, which is what makes the
identity iterable.  The proof is the standard differentiation under the interval integral
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`, with the domination
`|v^c·(v·∂_z h(zv,θ))| = v^c·|D_z h (zv,θ)|/z ≤ (2M/z)·v^c`, integrable on `(0,1)`
because `-1 < c`.  The point of using the *interval* version is that its measurability
hypotheses are stated for `volume.restrict (uIoc 0 1) = volume.restrict (Ioc 0 1)`, on
which — unlike on `Icc 0 1` — every integrand is continuous, so no measurability
bookkeeping at `v = 0` is needed.

Everything is stated with hypotheses on the whole open quadrant, as they arise from
`SlotBd` for `h = D_z^j (U'(Ψ))`, `j ≤ 2`.
-/

noncomputable section
open scoped Real Topology Interval
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SBpsiP

open Work.FTS.StreamBdryIface (Uprime SlotBd)

set_option autoImplicit false

/-- The open quadrant is open. -/
theorem isOpen_Qd' : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo

/-- **Differentiation of the scaled parameter integral.**  Under the slot-type hypotheses
(continuity of `h` and `D_z h` on `Qd`, differentiability of the `z`-slices, and the uniform
bounds `|h| ≤ M`, `|D_z h| ≤ M`), the parametric integral `J c h` is differentiable in `z` and
`D_z (J c h) = J c (D_z h)`. -/
theorem J_Dz_eq {c M : ℝ} (hc : -1 < c) {h : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (Function.uncurry h) Work.Construction.Qd)
    (hcontD : ContinuousOn (Function.uncurry (Work.Spaces.Dz h)) Work.Construction.Qd)
    (hslice : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (fun z' => h z' θ) z)
    (hbdd : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → |h z θ| ≤ M)
    (hbnd : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → |Work.Spaces.Dz h z θ| ≤ M) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (fun x => Work.FTS_StreamBdry.SB3.J c h x θ) z ∧
      Work.Spaces.Dz (Work.FTS_StreamBdry.SB3.J c h) z θ
        = Work.FTS_StreamBdry.SB3.J c (Work.Spaces.Dz h) z θ := by
  intro z θ hmem
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS_StreamBdry.mem_Qd.mp hmem
  have hθ : θ ∈ Ioo (0 : ℝ) (π / 2) := ⟨hθ0, hθ1⟩
  -- `M ≥ 0`
  have hM : 0 ≤ M := by
    have h1 : ((1 : ℝ), π / 4) ∈ Work.Construction.Qd :=
      Work.FTS_StreamBdry.mem_Qd.mpr
        ⟨by norm_num, by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    exact le_trans (abs_nonneg _) (hbdd _ _ h1)
  -- `pz h` is continuous on the open quadrant
  have hpzcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz h p.1 p.2)
      Work.Construction.Qd := by
    have hdiv : ContinuousOn
        (fun p : ℝ × ℝ => Function.uncurry (Work.Spaces.Dz h) p / p.1)
        Work.Construction.Qd :=
      hcontD.div continuousOn_fst (fun p hp => ne_of_gt (Work.FTS_StreamBdry.Qd_pos hp))
    refine hdiv.congr (fun p hp => ?_)
    show Work.Spaces.pz h p.1 p.2 = Work.Spaces.Dz h p.1 p.2 / p.1
    rw [Work.Spaces.Dz,
      mul_div_cancel_left₀ _ (ne_of_gt (Work.FTS_StreamBdry.Qd_pos hp))]
  -- continuity of the two integrands on `(0,1]`
  have hcontF : ∀ x : ℝ, 0 < x →
      ContinuousOn (fun v : ℝ => v ^ c * h (x * v) θ) (Set.Ioc (0 : ℝ) 1) := by
    intro x hx
    have h1 : ContinuousOn (fun v : ℝ => v ^ c) (Set.Ioc (0 : ℝ) 1) :=
      continuousOn_id.rpow_const (fun v hv => Or.inl (ne_of_gt hv.1))
    have h2 : ContinuousOn (fun v : ℝ => h (x * v) θ) (Set.Ioc (0 : ℝ) 1) := by
      have hlin : ContinuousOn (fun v : ℝ => (x * v, θ)) (Set.Ioc (0 : ℝ) 1) :=
        ((continuous_const.mul continuous_id).prodMk continuous_const).continuousOn
      have hcomp := hcont.comp hlin (fun v hv => ⟨mul_pos hx hv.1, hθ0, hθ1⟩)
      simpa [Function.comp_def, Function.uncurry] using hcomp
    convert h1.mul h2 using 1
  have hcontF' : ∀ x : ℝ, 0 < x → ContinuousOn
      (fun v : ℝ => v ^ c * (v * Work.Spaces.pz h (x * v) θ)) (Set.Ioc (0 : ℝ) 1) := by
    intro x hx
    have h1 : ContinuousOn (fun v : ℝ => v ^ c) (Set.Ioc (0 : ℝ) 1) :=
      continuousOn_id.rpow_const (fun v hv => Or.inl (ne_of_gt hv.1))
    have h2 : ContinuousOn (fun v : ℝ => v) (Set.Ioc (0 : ℝ) 1) := continuousOn_id
    have h3 : ContinuousOn (fun v : ℝ => Work.Spaces.pz h (x * v) θ) (Set.Ioc (0 : ℝ) 1) := by
      have hlin : ContinuousOn (fun v : ℝ => (x * v, θ)) (Set.Ioc (0 : ℝ) 1) :=
        ((continuous_const.mul continuous_id).prodMk continuous_const).continuousOn
      have hcomp := hpzcont.comp hlin (fun v hv => ⟨mul_pos hx hv.1, hθ0, hθ1⟩)
      simpa [Function.comp_def, Function.uncurry] using hcomp
    convert h1.mul (h2.mul h3) using 1
  -- the neighbourhood of `z` on which everything is differentiable; on it `x > z/2`
  have hs : Set.Ioo (z / 2) (z + 1) ∈ 𝓝 z :=
    isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  -- measurability of `F x` and of `F' z`
  have hF_meas : ∀ᶠ x in 𝓝 z, AEStronglyMeasurable
      (fun v : ℝ => v ^ c * h (x * v) θ) (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    filter_upwards [hs] with x hx
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (hcontF x (by linarith [hx.1, hz])).aestronglyMeasurable measurableSet_Ioc
  have hF'_meas : AEStronglyMeasurable
      (fun v : ℝ => v ^ c * (v * Work.Spaces.pz h (z * v) θ))
      (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (hcontF' z hz).aestronglyMeasurable measurableSet_Ioc
  -- integrability of `F z`
  have hF_int : IntervalIntegrable (fun v : ℝ => v ^ c * h (z * v) θ) volume 0 1 := by
    have hle : ∀ᵐ u ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
        ‖u ^ c * h (z * u) θ‖ ≤ M * u ^ c := by
      rw [ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall (fun u hu => ?_)
      have hu' : (z * u, θ) ∈ Work.Construction.Qd := ⟨mul_pos hz hu.1, hθ0, hθ1⟩
      have hbu : |h (z * u) θ| ≤ M := hbdd _ _ hu'
      have hx : (0 : ℝ) ≤ u ^ c := Real.rpow_nonneg hu.1.le c
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hx]
      calc u ^ c * |h (z * u) θ| ≤ u ^ c * M := mul_le_mul_of_nonneg_left hbu hx
        _ = M * u ^ c := by ring
    have hmeas : AEStronglyMeasurable (fun u : ℝ => u ^ c * h (z * u) θ)
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      (hcontF z hz).aestronglyMeasurable measurableSet_Ioc
    have hg : IntegrableOn (fun u : ℝ => M * u ^ c) (Set.Ioc (0 : ℝ) 1) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
        ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) hc).const_mul M)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
      (hg.mono' hmeas hle)
  -- integrability of the dominating function
  have hbnd_int : IntervalIntegrable (fun v : ℝ => (2 * M / z) * v ^ c) volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) hc).const_mul (2 * M / z)
  -- the domination of `F'`
  have h_bound : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) 1 → ∀ x ∈ Set.Ioo (z / 2) (z + 1),
      ‖t ^ c * (t * Work.Spaces.pz h (x * t) θ)‖ ≤ (2 * M / z) * t ^ c := by
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    intro x hx
    have ht0 : 0 < t := ht.1
    have hxpos : 0 < x := by linarith [hx.1, hz]
    have hxtpos : 0 < x * t := mul_pos hxpos ht0
    have hxne : x ≠ 0 := ne_of_gt hxpos
    have hb := hbnd (x * t) θ
      (show (x * t, θ) ∈ Work.Construction.Qd from ⟨hxtpos, hθ0, hθ1⟩)
    have htcpow : (0 : ℝ) ≤ t ^ c := Real.rpow_nonneg (le_of_lt ht0) c
    have hnorm : |t ^ c * (t * Work.Spaces.pz h (x * t) θ)|
        = t ^ c * (t * |Work.Spaces.pz h (x * t) θ|) := by
      rw [abs_mul, abs_of_nonneg htcpow, abs_mul, abs_of_pos ht0]
    have hD : t * |Work.Spaces.pz h (x * t) θ| = |Work.Spaces.Dz h (x * t) θ| / x := by
      rw [Work.Spaces.Dz, abs_mul, abs_of_pos hxtpos]
      field_simp
    have h2 : |Work.Spaces.Dz h (x * t) θ| / x ≤ 2 * M / z := by
      have h3 : |Work.Spaces.Dz h (x * t) θ| / x ≤ M / x := by
        gcongr
      have h4 : M / x ≤ 2 * M / z := by
        have h5 : M / x ≤ M / (z / 2) :=
          div_le_div_of_nonneg_left hM (by linarith [hz]) (by linarith [hx.1])
        have h6 : M / (z / 2) = 2 * M / z := by
          rw [div_eq_mul_inv, inv_div, div_eq_mul_inv]
          ring
        linarith [h5, h6]
      linarith
    rw [Real.norm_eq_abs, hnorm, hD]
    calc t ^ c * (|Work.Spaces.Dz h (x * t) θ| / x) ≤ t ^ c * (2 * M / z) :=
          mul_le_mul_of_nonneg_left h2 htcpow
      _ = 2 * M / z * t ^ c := by ring
  -- the differentiability of `F · t`
  have h_diff : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) 1 → ∀ x ∈ Set.Ioo (z / 2) (z + 1),
      HasDerivAt (fun x' : ℝ => t ^ c * h (x' * t) θ)
        (t ^ c * (t * Work.Spaces.pz h (x * t) θ)) x := by
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    intro x hx
    have ht0 : 0 < t := ht.1
    have hxpos : 0 < x := by linarith [hx.1, hz]
    have hxmem : (x * t, θ) ∈ Work.Construction.Qd :=
      ⟨mul_pos hxpos ht0, hθ0, hθ1⟩
    have h1 : HasDerivAt (fun y : ℝ => h y θ) (Work.Spaces.pz h (x * t) θ) (x * t) :=
      (hslice (x * t) θ hxmem).hasDerivAt
    have h2 : HasDerivAt (fun x' : ℝ => x' * t) t x := by
      simpa using (hasDerivAt_id x).mul_const t
    have h3 : HasDerivAt (fun x' : ℝ => h (x' * t) θ)
        (Work.Spaces.pz h (x * t) θ * t) x := by
      simpa [Function.comp_def] using h1.comp x h2
    have h4 : HasDerivAt (fun x' : ℝ => h (x' * t) θ) (t * Work.Spaces.pz h (x * t) θ) x :=
      h3.congr_deriv (by ring)
    exact h4.const_mul (t ^ c)
  obtain ⟨-, hderiv⟩ := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := 1)
    (bound := fun v : ℝ => (2 * M / z) * v ^ c)
    (F := fun x v => v ^ c * h (x * v) θ)
    (F' := fun x v => v ^ c * (v * Work.Spaces.pz h (x * v) θ))
    (x₀ := z) (s := Set.Ioo (z / 2) (z + 1)) hs hF_meas hF_int hF'_meas h_bound hbnd_int h_diff
  refine ⟨?_, ?_⟩
  · simpa only [Work.FTS_StreamBdry.SB3.J_apply] using hderiv.differentiableAt
  · have hpzJ : Work.Spaces.pz (Work.FTS_StreamBdry.SB3.J c h) z θ
        = ∫ v in (0 : ℝ)..1, v ^ c * (v * Work.Spaces.pz h (z * v) θ) := by
      simpa only [Work.FTS_StreamBdry.SB3.J_apply, Work.Spaces.pz] using hderiv.deriv
    rw [Work.Spaces.Dz, hpzJ]
    have hpoint : ∀ v : ℝ, z * (v ^ c * (v * Work.Spaces.pz h (z * v) θ))
        = v ^ c * (Work.Spaces.Dz h (z * v) θ) := by
      intro v
      rw [Work.Spaces.Dz]
      ring
    calc z * ∫ v in (0 : ℝ)..1, v ^ c * (v * Work.Spaces.pz h (z * v) θ)
        = ∫ v in (0 : ℝ)..1, z * (v ^ c * (v * Work.Spaces.pz h (z * v) θ)) :=
          (intervalIntegral.integral_const_mul _ _).symm
      _ = ∫ v in (0 : ℝ)..1, v ^ c * (Work.Spaces.Dz h (z * v) θ) := by
          refine intervalIntegral.integral_congr (fun v _ => ?_)
          exact hpoint v
      _ = Work.FTS_StreamBdry.SB3.J c (Work.Spaces.Dz h) z θ := rfl

end Work.FTS_StreamBdry.SBpsiP
end
end
