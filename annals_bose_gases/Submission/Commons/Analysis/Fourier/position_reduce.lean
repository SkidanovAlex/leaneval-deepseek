import Mathlib.Analysis.Fourier.Notation
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Submission.Commons.Analysis.Fourier.heat_triple_integrable
import Submission.Commons.Analysis.Fourier.newton_double_integrable
import Submission.Commons.Analysis.Fourier.real_re_basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

namespace Commons.Analysis.Fourier

open Real Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace SchwartzMap FourierTransform
open Complex hiding exp

abbrev V := EuclideanSpace ℝ (Fin 3)

lemma finrank_V : Module.finrank ℝ V = 3 := by simp [V]

/-- The heat kernel `H_s(z) = s^{-3/2} exp(-π‖z‖²/s)`. -/
def heatK (s : ℝ) (z : V) : ℝ := s ^ (-(3 / 2 : ℝ)) * Real.exp (-(Real.pi * ‖z‖ ^ 2) / s)

lemma heatK_nonneg {s : ℝ} (hs : 0 ≤ s) (z : V) : 0 ≤ heatK s z := by
  dsimp [heatK]
  exact mul_nonneg (Real.rpow_nonneg hs _) (Real.exp_pos _).le

lemma heatK_le_rpow {s : ℝ} (hs : 0 ≤ s) (z : V) :
    heatK s z ≤ s ^ (-(3 / 2 : ℝ)) := by
  dsimp [heatK]
  exact mul_le_of_le_one_right (Real.rpow_nonneg hs _) (by
    have hpi2 : 0 ≤ Real.pi * ‖z‖ ^ 2 := by positivity
    have harg : -(Real.pi * ‖z‖ ^ 2) / s ≤ 0 := by
      rw [neg_div, neg_nonpos]
      exact div_nonneg hpi2 hs
    simpa using (Real.exp_le_exp.mpr harg : Real.exp (-(Real.pi * ‖z‖ ^ 2) / s) ≤ Real.exp 0))

lemma heatK_continuous {s : ℝ} (hs : 0 < s) : Continuous fun z : V => heatK s z := by
  dsimp [heatK]
  have hnum : Continuous (fun z : V => -(Real.pi * ‖z‖ ^ 2)) :=
    continuous_neg.comp (continuous_const.mul (continuous_norm.pow 2))
  have hdiv : Continuous (fun z : V => -(Real.pi * ‖z‖ ^ 2) / s) := hnum.div continuous_const (fun _ => ne_of_gt hs)
  exact continuous_const.mul (Real.continuous_exp.comp hdiv)

lemma heatK_measurable {s : ℝ} (hs : 0 < s) : Measurable fun z : V => heatK s z :=
  (heatK_continuous hs).measurable

/-! ## The 1-dimensional `s`-integral (heat kernel = Newtonian kernel) -/

/-- For `r > 0`, `∫_{s > 0} s^{-3/2} exp(-π r² / s) ds = r⁻¹`. -/
lemma heat_integral_Ioi {r : ℝ} (hr : 0 < r) :
    (∫ s : ℝ in Ioi (0 : ℝ), s ^ (-(3 / 2 : ℝ)) * Real.exp (-(Real.pi * r ^ 2) / s)) = r⁻¹ := by
  let c : ℝ := Real.pi * r ^ 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hpoint (x : ℝ) (hx : 0 < x) :
      (|(-2 : ℝ)| * x ^ ((-2 : ℝ) - 1)) *
          ((x ^ (-2 : ℝ)) ^ (-(3 / 2 : ℝ)) * Real.exp (-(c / x ^ (-2 : ℝ)))) =
        2 * Real.exp (-(c * x ^ 2)) := by
    have hpow : (x ^ (-2 : ℝ)) ^ (-(3 / 2 : ℝ)) = x ^ (3 : ℝ) := by
      rw [← Real.rpow_mul hx.le]; norm_num
    have hinv : (x ^ (-2 : ℝ))⁻¹ = x ^ (2 : ℝ) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_mul hx.le]
      norm_num
    have hexp : -(c / x ^ (-2 : ℝ)) = -(c * x ^ 2) := by
      simp [div_eq_mul_inv, hinv]
    rw [hpow, hexp]
    have hx3 : x ^ ((-2 : ℝ) - 1) * x ^ (3 : ℝ) = 1 := by
      rw [← Real.rpow_add hx]
      norm_num
    calc
      (|(-2 : ℝ)| * x ^ ((-2 : ℝ) - 1)) * (x ^ (3 : ℝ) * Real.exp (-(c * x ^ 2)))
          = (|(-2 : ℝ)| * (x ^ ((-2 : ℝ) - 1) * x ^ (3 : ℝ))) * Real.exp (-(c * x ^ 2)) := by ring
      _ = 2 * Real.exp (-(c * x ^ 2)) := by rw [hx3]; norm_num
  calc
    (∫ s : ℝ in Ioi (0 : ℝ), s ^ (-(3 / 2 : ℝ)) * Real.exp (-(Real.pi * r ^ 2) / s))
        = ∫ s : ℝ in Ioi (0 : ℝ), s ^ (-(3 / 2 : ℝ)) * Real.exp (-(c / s)) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x hx
          dsimp [c]
          congr 2
          ring
    _ = ∫ x : ℝ in Ioi (0 : ℝ), 2 * Real.exp (-(c * x ^ 2)) := by
          rw [← integral_comp_rpow_Ioi (E := ℝ)
            (g := fun s : ℝ => s ^ (-(3 / 2 : ℝ)) * Real.exp (-(c / s))) (p := (-2 : ℝ)) (by norm_num)]
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x hx
          simpa [mul_comm, mul_left_comm, mul_assoc] using hpoint x hx
    _ = √(Real.pi / c) := by
          rw [integral_const_mul]
          have hg : (∫ a : ℝ in Ioi (0 : ℝ), Real.exp (-(c * a ^ 2))) = √(Real.pi / c) / 2 := by
            simpa [mul_neg, neg_mul] using integral_gaussian_Ioi c
          rw [hg]
          field_simp [show (2 : ℝ) ≠ 0 by norm_num]
    _ = r⁻¹ := by
          have hfrac : Real.pi / c = (r ^ 2)⁻¹ := by
            dsimp [c]
            field_simp [Real.pi_ne_zero]
          have hsq : (r ^ 2)⁻¹ = (r⁻¹) ^ 2 := by
            rw [← inv_pow]
          rw [hfrac, hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg (inv_nonneg.mpr hr.le)]

/-- Heat kernel integrates to `‖z‖⁻¹` for `z ≠ 0`. -/
lemma heatK_Ioi {z : V} (hz : z ≠ 0) :
    (∫ s : ℝ in Ioi (0 : ℝ), heatK s z) = ‖z‖⁻¹ := by
  simpa [heatK] using heat_integral_Ioi (r := ‖z‖) (norm_pos_iff.mpr hz)

/-- The heat-kernel is integrable in `s` over `(0, ∞)` when `z ≠ 0`. -/
lemma heatK_integrable_Ioi {z : V} (hz : z ≠ 0) :
    Integrable (fun s : ℝ => heatK s z) (volume.restrict (Ioi (0 : ℝ))) := by
  have hne : (∫ s : ℝ in Ioi (0 : ℝ), heatK s z) ≠ 0 := by
    rw [heatK_Ioi hz]
    exact inv_ne_zero (norm_ne_zero_iff.mpr hz)
  exact by_contra (fun hn : ¬ Integrable (fun s : ℝ => heatK s z) (volume.restrict (Ioi (0 : ℝ))) =>
    hne (MeasureTheory.integral_undef hn))

/-- Pointwise (off-diagonal) identity: for `z ≠ 0`,
`∫_{s>0} c·(d·H_s(z)) ds = c·(d·‖z‖⁻¹)`. -/
lemma heatK_Ioi_mul {z : V} (hz : z ≠ 0) (c d : ℝ) :
    (∫ s : ℝ in Ioi (0 : ℝ), c * (d * heatK s z)) = c * (d * ‖z‖⁻¹) := by
  have hi : Integrable (fun s : ℝ => d * heatK s z) (volume.restrict (Ioi (0 : ℝ))) :=
    (heatK_integrable_Ioi hz).const_mul d
  calc
    (∫ s : ℝ in Ioi (0 : ℝ), c * (d * heatK s z))
        = c * (∫ s : ℝ in Ioi (0 : ℝ), d * heatK s z) := by rw [integral_const_mul]
    _ = c * (d * (∫ s : ℝ in Ioi (0 : ℝ), heatK s z)) := by rw [integral_const_mul]
    _ = c * (d * ‖z‖⁻¹) := by rw [heatK_Ioi hz]

/-- The diagonal of `V × V` is null for the product of two copies of `volume`. -/
lemma diag_null : (volume.prod volume) {p : V × V | p.1 = p.2} = 0 := by
  have hmeas : MeasurableSet {p : V × V | p.1 = p.2} := by
    have hc : Measurable (fun p : V × V => p.1 - p.2) :=
      (Continuous.sub continuous_fst continuous_snd).measurable
    have hset : {p : V × V | p.1 = p.2} =
        (fun p : V × V => p.1 - p.2) ⁻¹' ({0} : Set V) := by
      ext p
      simp [sub_eq_zero]
    rw [hset]
    exact MeasurableSet.preimage (isClosed_singleton.measurableSet : MeasurableSet ({0} : Set V)) hc
  rw [Measure.prod_apply hmeas]
  have hsec : (fun x : V => volume ((Prod.mk x) ⁻¹' {p : V × V | p.1 = p.2})) = fun _ : V => (0 : ENNReal) := by
    funext x
    have hset : (Prod.mk x) ⁻¹' {p : V × V | p.1 = p.2} = ({x} : Set V) := by
      ext y
      simp [eq_comm]
    rw [hset, measure_singleton]
  rw [hsec]
  simp


/-! ## Pair integrands on `V × V` and the per-`s` Fubini -/

/-- The position-side pair integrand at parameter `s`:
`F_s(x, y) = u x * (u y * H_s(x - y))`. -/
def heatPair (u : V → ℝ) (s : ℝ) (p : V × V) : ℝ := u p.1 * (u p.2 * heatK s (p.1 - p.2))

lemma heatPair_measurable {u : V → ℝ} (hu : Measurable u) {s : ℝ} (hs : 0 < s) :
    Measurable (fun p : V × V => heatPair u s p) := by
  unfold heatPair
  have hm1 : Measurable (fun p : V × V => u p.1) := hu.comp measurable_fst
  have hm2 : Measurable (fun p : V × V => u p.2) := hu.comp measurable_snd
  have hmsub : Measurable (fun p : V × V => p.1 - p.2) := measurable_fst.sub measurable_snd
  have hmk : Measurable (fun p : V × V => heatK s (p.1 - p.2)) := (heatK_measurable hs).comp hmsub
  exact hm1.mul (hm2.mul hmk)

lemma abs_integrable {u : V → ℝ} (hu : MeasureTheory.Integrable u) :
    MeasureTheory.Integrable (fun x : V => |u x|) := by
  simpa using hu.norm

lemma heatPair_integrable {u : V → ℝ} (hmu : Measurable u) (hui : MeasureTheory.Integrable u)
    {s : ℝ} (hs : 0 < s) :
    MeasureTheory.Integrable (fun p : V × V => heatPair u s p) := by
  have huu : MeasureTheory.Integrable (fun p : V × V => |u p.1| * |u p.2|) :=
    Integrable.mul_prod (abs_integrable hui) (abs_integrable hui)
  refine Integrable.mono' (hg := huu.const_mul (s ^ (-(3 / 2 : ℝ))))
    (hf := (heatPair_measurable hmu hs).aestronglyMeasurable) ?_
  filter_upwards with p
  unfold heatPair
  have hk0 : 0 ≤ heatK s (p.1 - p.2) := heatK_nonneg (le_of_lt hs) _
  calc
    |u p.1 * (u p.2 * heatK s (p.1 - p.2))|
        = |u p.1| * |u p.2 * heatK s (p.1 - p.2)| := by rw [abs_mul]
    _ = |u p.1| * (|u p.2| * heatK s (p.1 - p.2)) := by rw [abs_mul, abs_of_nonneg hk0]
    _ ≤ |u p.1| * (|u p.2| * s ^ (-(3 / 2 : ℝ))) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (heatK_le_rpow (le_of_lt hs) _) (abs_nonneg _)) (abs_nonneg _)
    _ = s ^ (-(3 / 2 : ℝ)) * (|u p.1| * |u p.2|) := by ring

/-- Pointwise (off the diagonal) identity: the `s`-integral of the pair integrand equals the
Newton kernel. -/
lemma heatPair_Ioi {u : V → ℝ} (p : V × V) (hp : p.1 ≠ p.2) :
    (∫ s : ℝ in Ioi (0 : ℝ), heatPair u s p) = u p.1 * (u p.2 * ‖p.1 - p.2‖⁻¹) := by
  unfold heatPair
  have hz : p.1 - p.2 ≠ 0 := sub_ne_zero.mpr hp
  exact heatK_Ioi_mul hz (u p.1) (u p.2)

/-- A.e. identity: for almost every `p`, the `s`-integral of the pair integrand equals the
Newton kernel `u(p.1)·u(p.2)·‖p.1−p.2‖⁻¹`. -/
lemma heatPair_Ioi_ae {u : V → ℝ} :
    (fun p : V × V => ∫ s : ℝ in Ioi (0 : ℝ), heatPair u s p)
      =ᵐ[volume.prod volume] (fun p : V × V => u p.1 * (u p.2 * ‖p.1 - p.2‖⁻¹)) := by
  have hae : ∀ᵐ p : V × V ∂((volume : Measure V).prod (volume : Measure V)), p.1 ≠ p.2 := by
    exact MeasureTheory.ae_iff.mpr (by simpa using diag_null)
  filter_upwards [hae] with p hp
  exact heatPair_Ioi (u := u) p hp

lemma per_s_eq {u : V → ℝ} (hmu : Measurable u) (hui : MeasureTheory.Integrable u)
    {s : ℝ} (hs : 0 < s) :
    (∫ x : V, u x * (∫ y : V, u y * heatK s (x - y)))
      = ∫ p : V × V, heatPair u s p := by
  have hint : MeasureTheory.Integrable (fun p : V × V => heatPair u s p) :=
    heatPair_integrable hmu hui hs
  calc
    (∫ x : V, u x * (∫ y : V, u y * heatK s (x - y)))
        = ∫ x : V, ∫ y : V, heatPair u s (x, y) := by
          apply integral_congr_ae
          filter_upwards with x
          simp only [heatPair]
          rw [← integral_const_mul]
    _ = ∫ p : V × V, heatPair u s p := by
          exact (integral_prod (fun p : V × V => heatPair u s p) hint).symm

theorem position_reduce_real (u : V → ℝ) (hmu : Measurable u)
    (hu_bdd : ∃ C : ℝ, ∀ x : V, |u x| ≤ C) (hui : MeasureTheory.Integrable u) :
    (∫ x : V, ∫ y : V, u x * u y * (4 * Real.pi * ‖x - y‖)⁻¹)
      = (1 / (4 * Real.pi)) *
          (∫ s : ℝ in Ioi (0 : ℝ), ∫ x : V, u x *
            (∫ y : V, u y * heatK s (x - y))) := by
  let μ2 : Measure (V × V) := (volume : Measure V).prod (volume : Measure V)
  let μs : Measure ℝ := (volume : Measure ℝ).restrict (Ioi (0 : ℝ))
  let cf : ℝ := (4 * Real.pi)⁻¹
  have hfactor : (1 / (4 * Real.pi)) = cf := by dsimp [cf]; rw [one_div]
  have hK : MeasureTheory.Integrable (fun p : V × V => u p.1 * u p.2 * ‖p.1 - p.2‖⁻¹) μ2 := by
    dsimp [μ2]
    exact newton_double_integrable u hmu hu_bdd hui
  have hJ : MeasureTheory.Integrable (fun p : V × V => u p.1 * u p.2 * (4 * Real.pi * ‖p.1 - p.2‖)⁻¹) μ2 := by
    have hpt : (fun p : V × V => u p.1 * u p.2 * (4 * Real.pi * ‖p.1 - p.2‖)⁻¹)
        = fun p : V × V => cf * (u p.1 * u p.2 * ‖p.1 - p.2‖⁻¹) := by
      funext p
      dsimp [cf]
      rw [mul_inv]
      ring
    rw [hpt]
    exact hK.const_mul cf
  have hTpair : MeasureTheory.Integrable (fun z : (V × V) × ℝ => heatPair u z.2 z.1) (μ2.prod μs) := by
    have hT := heat_triple_integrable u hmu hu_bdd hui
    have hpt : (fun z : (V × V) × ℝ => u z.1.1 * (u z.1.2 *
          (z.2 ^ (-(3 / 2 : ℝ)) * Real.exp (-(Real.pi * ‖z.1.1 - z.1.2‖ ^ 2) / z.2))))
        = fun z : (V × V) × ℝ => heatPair u z.2 z.1 := by
      funext z
      rfl
    rw [hpt] at hT
    exact hT
  have hper (s : ℝ) (hs : 0 < s) :
      (∫ x : V, u x * (∫ y : V, u y * heatK s (x - y))) = ∫ p : V × V, heatPair u s p :=
    per_s_eq hmu hui hs
  have hae_id :
      (fun p : V × V => ∫ s : ℝ, heatPair u s p ∂μs) =ᵐ[μ2]
        fun p : V × V => u p.1 * (u p.2 * ‖p.1 - p.2‖⁻¹) := by
    dsimp [μs]
    exact heatPair_Ioi_ae
  have hae_id2 :
      (fun p : V × V => ∫ s : ℝ, heatPair u s p ∂μs) =ᵐ[μ2]
        fun p : V × V => u p.1 * u p.2 * ‖p.1 - p.2‖⁻¹ := by
    filter_upwards [hae_id] with p hp
    convert hp using 1 <;> ring
  have hpid : (∫ p : V × V, u p.1 * u p.2 * ‖p.1 - p.2‖⁻¹ ∂μ2)
      = ∫ p : V × V, (∫ s : ℝ, heatPair u s p ∂μs) ∂μ2 := by
    exact (integral_congr_ae hae_id2).symm
  have hprod : (∫ z : (V × V) × ℝ, heatPair u z.2 z.1 ∂(μ2.prod μs))
      = ∫ p : V × V, (∫ s : ℝ, heatPair u s p ∂μs) ∂μ2 := by
    exact integral_prod (fun z : (V × V) × ℝ => heatPair u z.2 z.1) hTpair
  have hsym : (∫ z : (V × V) × ℝ, heatPair u z.2 z.1 ∂(μ2.prod μs))
      = ∫ s : ℝ, (∫ p : V × V, heatPair u s p ∂μ2) ∂μs := by
    exact integral_prod_symm (fun z : (V × V) × ℝ => heatPair u z.2 z.1) hTpair
  have hsg : (∫ s : ℝ, (∫ p : V × V, heatPair u s p ∂μ2) ∂μs)
      = ∫ s : ℝ, (∫ x : V, u x * (∫ y : V, u y * heatK s (x - y))) ∂μs := by
    apply integral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact (hper s hs).symm
  have hL : (∫ x : V, ∫ y : V, u x * u y * (4 * Real.pi * ‖x - y‖)⁻¹)
      = ∫ p : V × V, u p.1 * u p.2 * (4 * Real.pi * ‖p.1 - p.2‖)⁻¹ := by
    exact (integral_prod (fun p : V × V => u p.1 * u p.2 * (4 * Real.pi * ‖p.1 - p.2‖)⁻¹) hJ).symm
  have hJc : (∫ p : V × V, u p.1 * u p.2 * (4 * Real.pi * ‖p.1 - p.2‖)⁻¹ ∂μ2)
      = cf * (∫ p : V × V, u p.1 * u p.2 * ‖p.1 - p.2‖⁻¹ ∂μ2) := by
    have hpt : (fun p : V × V => u p.1 * u p.2 * (4 * Real.pi * ‖p.1 - p.2‖)⁻¹)
        = fun p : V × V => cf * (u p.1 * u p.2 * ‖p.1 - p.2‖⁻¹) := by
      funext p
      dsimp [cf]
      rw [mul_inv]
      ring
    rw [hpt]
    rw [integral_const_mul]
  calc
    (∫ x : V, ∫ y : V, u x * u y * (4 * Real.pi * ‖x - y‖)⁻¹)
        = ∫ p : V × V, u p.1 * u p.2 * (4 * Real.pi * ‖p.1 - p.2‖)⁻¹ := hL
    _ = cf * (∫ p : V × V, u p.1 * u p.2 * ‖p.1 - p.2‖⁻¹ ∂μ2) := hJc
    _ = cf * (∫ p : V × V, (∫ s : ℝ, heatPair u s p ∂μs) ∂μ2) := by rw [hpid]
    _ = cf * (∫ z : (V × V) × ℝ, heatPair u z.2 z.1 ∂(μ2.prod μs)) := by rw [hprod]
    _ = cf * (∫ s : ℝ, (∫ p : V × V, heatPair u s p ∂μ2) ∂μs) := by rw [hsym]
    _ = cf * (∫ s : ℝ, (∫ x : V, u x * (∫ y : V, u y * heatK s (x - y))) ∂μs) := by rw [hsg]
    _ = (1 / (4 * Real.pi)) *
          (∫ s : ℝ, (∫ x : V, u x * (∫ y : V, u y * heatK s (x - y))) ∂μs) := by rw [hfactor]


/-- On the position side, use the heat-kernel representation
`1/‖x−y‖ = ∫₀^∞ s^{−3/2} exp(−π‖x−y‖²/s) ds`:

`∫∫ f(x)f(y)/(4π‖x−y‖) =
 (1/4π)·∫_{s>0} ∫_x f(x)·(∫_y f(y)·s^{−3/2} exp(−π‖x−y‖²/s))`. -/
theorem position_reduce (f : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ)
    (hreal : ∀ x : EuclideanSpace ℝ (Fin 3), (f x).im = 0) :
    (∫ x : EuclideanSpace ℝ (Fin 3),
      ∫ y : EuclideanSpace ℝ (Fin 3),
        ((f x).re * (f y).re) * (4 * Real.pi * ‖x - y‖)⁻¹)
      = (1 / (4 * Real.pi)) *
          (∫ s : ℝ in Ioi (0 : ℝ),
            ∫ x : EuclideanSpace ℝ (Fin 3),
              (f x).re * (∫ y : EuclideanSpace ℝ (Fin 3), (f y).re *
                (s ^ (-(3 / 2 : ℝ)) * Real.exp (-(Real.pi * ‖x - y‖ ^ 2) / s)))) := by
  let u : V → ℝ := fun x => (f x).re
  have hu := real_re_basic f
  have h := position_reduce_real u hu.1 hu.2.1 hu.2.2
  change
    (∫ x : V, ∫ y : V, u x * u y * (4 * Real.pi * ‖x - y‖)⁻¹)
      = (1 / (4 * Real.pi)) *
          (∫ s : ℝ in Ioi (0 : ℝ), ∫ x : V, u x *
            (∫ y : V, u y * heatK s (x - y)))
  exact h

end Commons.Analysis.Fourier
