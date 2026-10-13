import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs

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
