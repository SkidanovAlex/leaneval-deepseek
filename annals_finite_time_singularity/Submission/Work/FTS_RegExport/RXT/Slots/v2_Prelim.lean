/-
Copyright: work module for the Elgindi finite-time singularity project.

# `v2_Prelim` — shared vocabulary for the slot `v2_L12DzIterTendsto`

This module collects the pieces that the proof of

  `Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto`

and its delegated sub-lemmas share:

* `JetBnd C0 f` — the pointwise bound hypothesis of the slot,
  `|D_z^b D_θ^a f(z,θ)| ≤ C0 · z^{3/2}/(1+z)²` for `a + b ≤ 2` on the open quadrant;
* `hasDerivAt_integral_Itheta_Q0` — differentiation under the angular integral
  `x ↦ ∫_θ g x θ dθ` for a parametric integrand that is only continuous on the *open*
  quadrant `(0,∞) × (0,π/2)` (the analogue of
  `Work.Coercivity.hasDerivAt_integral_Itheta_of_hasDerivAt` that applies here, where the
  datum is only assumed smooth on the open quadrant);
* the elementary consequences of `JetBnd` used everywhere downstream: the bound on the
  `θ`-slice, on `∂_z` of the `D_z`-iterates, the integrability of the angular density
  `L₁₂dens`, and the real-variable bound `√x/(1+x)² ≤ a^{-3/2} + 1` for `x ≥ a > 0`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.Elliptic.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Slots

set_option autoImplicit false

/-! ## The pointwise bound hypothesis -/

/-- The pointwise bound of the slot `v2_L12DzIterTendsto`: on the open quadrant the mixed
derivatives of `f` of total order `≤ 2` are bounded by `C0 · z^{3/2}/(1+z)²`. -/
def JetBnd (C0 : ℝ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ (b a : ℕ), a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
    |Work.Spaces.mixed b a f z θ| ≤ C0 * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)

theorem JetBnd.apply {C0 : ℝ} {f : ℝ → ℝ → ℝ} (hb : JetBnd C0 f) {b a : ℕ} (h : a + b ≤ 2)
    {z θ : ℝ} (hz : 0 < z) (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    |Work.Spaces.mixed b a f z θ| ≤ C0 * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) :=
  hb b a h z θ hz h0 h1

/-- The `a = 0` case: a bound on `f` itself. -/
theorem JetBnd.self_le {C0 : ℝ} {f : ℝ → ℝ → ℝ} (hb : JetBnd C0 f) {z θ : ℝ}
    (hz : 0 < z) (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    |f z θ| ≤ C0 * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) :=
  hb 0 0 (by norm_num) z θ hz h0 h1

/-- The order-one case: a bound on `D_z f = z ∂_z f`. -/
theorem JetBnd.DzIter_le {C0 : ℝ} {f : ℝ → ℝ → ℝ} (hb : JetBnd C0 f) {z θ : ℝ}
    (hz : 0 < z) (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    |Work.Spaces.DzIter 1 f z θ| ≤ C0 * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) :=
  hb 1 0 (by norm_num) z θ hz h0 h1

/-! ## Elementary facts about the angular interval -/

/-- `λ(Iθ) = π/2`. -/
theorem real_univ_restrict_Iθ :
    (volume.restrict Work.Spaces.Iθ).real Set.univ = Real.pi / 2 := by
  rw [MeasureTheory.measureReal_def, MeasureTheory.Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Work.Spaces.Iθ, Real.volume_Icc]
  rw [ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
  ring

/-- `volume` restricted to `Iθ` is a finite measure. -/
theorem isFiniteMeasure_restrict_Iθ : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) := by
  rw [isFiniteMeasure_restrict, Work.Spaces.Iθ]
  exact isCompact_Icc.measure_ne_top

/-- `volume` restricted to `Iθ` and to the open interval `(0,π/2)` agree. -/
theorem restrict_Iθ_eq_restrict_Ioo :
    volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  rw [Work.Spaces.Iθ]
  exact MeasureTheory.Measure.restrict_congr_set
    (Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2)).symm

/-- The angular slice of a function continuous on the open quadrant is a.e. strongly
measurable on `Iθ`. -/
theorem aesm_slice_Q0 {g : ℝ → ℝ → ℝ} (hg : ContinuousOn (Function.uncurry g) Work.FTS.EllipticEst.Q0) {x : ℝ}
    (hx : 0 < x) :
    AEStronglyMeasurable (fun θ => g x θ) (volume.restrict Work.Spaces.Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry g) hg hx

/-! ## Differentiation under the angular integral, for open-quadrant data -/

/-- **Differentiation under the angular integral** for a parametric integrand which is only
continuous on the *open* quadrant.  If `V` is a neighbourhood of `x₀` consisting of positive
reals, `g` and its candidate derivative `g'` are continuous on `(0,∞) × (0,π/2)`, `θ ↦ g x₀ θ`
is integrable on `Iθ`, `g'` is uniformly bounded on `V × Iθ`, and for every interior angle
`x ↦ g x θ` has derivative `g' x θ`, then

  `∂_x (∫_θ g x θ) = ∫_θ g' x₀ θ`   at `x = x₀`. -/
theorem hasDerivAt_integral_Itheta_Q0 {g g' : ℝ → ℝ → ℝ} {V : Set ℝ} (hV : IsOpen V)
    {x₀ B : ℝ} (hx₀ : x₀ ∈ V) (hVpos : ∀ x ∈ V, 0 < x)
    (hg : ContinuousOn (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    (hg' : ContinuousOn (Function.uncurry g') Work.FTS.EllipticEst.Q0)
    (hgint : Integrable (fun θ => g x₀ θ) (volume.restrict Work.Spaces.Iθ))
    (hbound : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), ∀ x ∈ V, ‖g' x θ‖ ≤ B)
    (hdiff : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ x ∈ V, HasDerivAt (fun y => g y θ) (g' x θ) x) :
    HasDerivAt (fun x => ∫ θ in Work.Spaces.Iθ, g x θ) (∫ θ in Work.Spaces.Iθ, g' x₀ θ) x₀ := by
  have haesm : ∀ (h : ℝ → ℝ → ℝ), ContinuousOn (Function.uncurry h) Work.FTS.EllipticEst.Q0 →
      ∀ x ∈ V, AEStronglyMeasurable (fun θ => h x θ) (volume.restrict Work.Spaces.Iθ) :=
    fun h hh x hx => aesm_slice_Q0 hh (hVpos x hx)
  have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), ∀ x ∈ V,
      HasDerivAt (fun y => g y θ) (g' x θ) x := by
    rw [restrict_Iθ_eq_restrict_Ioo]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
      (fun θ hθ => hdiff θ hθ)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict Work.Spaces.Iθ) (𝕜 := ℝ)
    (F := fun x θ => g x θ) (F' := fun x θ => g' x θ) (bound := fun _ => B)
    (x₀ := x₀) (s := V) (hV.mem_nhds hx₀)
    (by filter_upwards [hV.mem_nhds hx₀] with x hx; exact haesm g hg x hx)
    hgint
    (haesm g' hg' x₀ hx₀)
    hbound
    (integrable_const B)
    hae
  exact key.2

/-! ## Real-variable bounds -/

/-- `√x/(1+x)² ≤ a^{-3/2} + 1` for `x ≥ a > 0`. -/
theorem rpow_half_div_sq_le {a x : ℝ} (ha : 0 < a) (hx : a ≤ x) :
    x ^ ((1 : ℝ) / 2) / (1 + x) ^ 2 ≤ a ^ (-(3 : ℝ) / 2) + 1 := by
  have hx0 : 0 < x := lt_of_lt_of_le ha hx
  rcases le_or_gt 1 x with h1 | h1
  · have hstep : x ^ ((1 : ℝ) / 2) / (1 + x) ^ 2 ≤ x ^ (-(3 : ℝ) / 2) := by
      rw [div_le_iff₀ (by positivity)]
      have hxx : x ^ (-(3 : ℝ) / 2) * x ^ (2 : ℕ) = x ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_natCast x 2, ← Real.rpow_add hx0]
        norm_num
      calc x ^ ((1 : ℝ) / 2) = x ^ (-(3 : ℝ) / 2) * x ^ (2 : ℕ) := hxx.symm
        _ ≤ x ^ (-(3 : ℝ) / 2) * (1 + x) ^ 2 := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hx0.le _)
            nlinarith
    have hmono : x ^ (-(3 : ℝ) / 2) ≤ a ^ (-(3 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_nonpos ha hx (by norm_num)
    linarith
  · have hstep : x ^ ((1 : ℝ) / 2) / (1 + x) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      have hxa : x ^ ((1 : ℝ) / 2) ≤ 1 := Real.rpow_le_one hx0.le (le_of_lt h1) (by norm_num)
      nlinarith [hxa, sq_nonneg (1 + x), hx0]
    have hpos : 0 ≤ a ^ (-(3 : ℝ) / 2) := Real.rpow_nonneg ha.le _
    linarith

/-- `x^{3/2} = x · x^{1/2}` for `x > 0`. -/
theorem rpow_three_halves {x : ℝ} (hx : 0 < x) :
    x ^ ((3 : ℝ) / 2) = x * x ^ ((1 : ℝ) / 2) := by
  rw [show ((3 : ℝ) / 2) = (1 : ℝ) / 2 + 1 by norm_num, Real.rpow_add hx, Real.rpow_one]
  ring

/-- `|K(θ)| ≤ 3` for every `θ`. -/
theorem abs_Ktheta_le (θ : ℝ) : |Work.Elliptic.Ktheta θ| ≤ 3 := by
  have hfun : Work.Elliptic.Ktheta θ = 3 * (Real.sin θ * Real.cos θ ^ 2) := by
    rw [Work.Elliptic.Ktheta]; ring
  rw [hfun, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
  have h1 : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
  have h2 : |Real.cos θ ^ 2| ≤ 1 := by
    rw [abs_sq]; nlinarith [sq_nonneg (Real.sin θ), Real.sin_sq_add_cos_sq θ]
  calc 3 * |Real.sin θ * Real.cos θ ^ 2| = 3 * (|Real.sin θ| * |Real.cos θ ^ 2|) := by
        rw [abs_mul]
    _ ≤ 3 * (1 * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (abs_nonneg _) (by norm_num))
          (by norm_num)
    _ = 3 := by norm_num

/-! ## Consequences of `JetBnd` -/

/-- The bound on `∂_z` of the `D_z`-iterates, `k ≤ 1`. -/
theorem JetBnd.pz_DzIter_le {C0 : ℝ} {f : ℝ → ℝ → ℝ} (hb : JetBnd C0 f)
    {k : ℕ} (hk : k ≤ 1) {x θ : ℝ} (hx : 0 < x) (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    |Work.Spaces.pz (Work.Spaces.DzIter k f) x θ|
      ≤ C0 * (x ^ ((1 : ℝ) / 2) / (1 + x) ^ 2) := by
  have hkey : Work.Spaces.pz (Work.Spaces.DzIter k f) x θ
      = Work.Spaces.DzIter (k + 1) f x θ / x := by
    show Work.Spaces.pz (Work.Spaces.DzIter k f) x θ
      = x * Work.Spaces.pz (Work.Spaces.DzIter k f) x θ / x
    rw [mul_div_cancel_left₀ _ (ne_of_gt hx)]
  rw [hkey, abs_div, abs_of_pos hx]
  have hbd := hb (k + 1) 0 (by omega) x θ hx h0 h1
  rw [rpow_three_halves hx] at hbd
  refine le_trans (div_le_div_of_nonneg_right hbd hx.le) ?_
  rw [show C0 * (x * x ^ ((1 : ℝ) / 2) / (1 + x) ^ 2) / x
      = C0 * (x ^ ((1 : ℝ) / 2) / (1 + x) ^ 2) from by
    field_simp]

/-- The angular density of `JetBnd`-data is bounded by `6 C0 s^{-3/2}`. -/
theorem JetBnd.dens_bound {C0 : ℝ} {f : ℝ → ℝ → ℝ} (hC0 : 0 ≤ C0) (hb : JetBnd C0 f)
    {s : ℝ} (hs : 0 < s) :
    ‖Work.Elliptic.L12dens f s‖ ≤ 6 * C0 * s ^ (-(3 : ℝ) / 2) := by
  have hbd : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ‖Work.Elliptic.Ktheta θ * f s θ / s‖
        ≤ 3 * C0 * (s ^ ((3 : ℝ) / 2) / (1 + s) ^ 2) / s := by
    rw [restrict_Iθ_eq_restrict_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hs, abs_mul, div_le_div_iff_of_pos_right hs]
    calc |Work.Elliptic.Ktheta θ| * |f s θ|
        ≤ 3 * (C0 * (s ^ ((3 : ℝ) / 2) / (1 + s) ^ 2)) :=
          mul_le_mul (abs_Ktheta_le θ) (hb.self_le hs hθ.1 hθ.2) (abs_nonneg _) (by norm_num)
      _ = 3 * C0 * (s ^ ((3 : ℝ) / 2) / (1 + s) ^ 2) := by ring
  have hstep := MeasureTheory.norm_integral_le_of_norm_le_const
    (μ := volume.restrict Work.Spaces.Iθ) hbd
  rw [real_univ_restrict_Iθ] at hstep
  have hkey : Work.Elliptic.L12dens f s
      = ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * f s θ / s := rfl
  rw [hkey]
  refine le_trans hstep ?_
  have hMle : 3 * C0 * (s ^ ((3 : ℝ) / 2) / (1 + s) ^ 2) / s ≤ 3 * C0 * s ^ (-(3 : ℝ) / 2) := by
    have h1 : s ^ ((3 : ℝ) / 2) / s = s ^ ((1 : ℝ) / 2) := by
      rw [rpow_three_halves hs, mul_div_cancel_left₀ _ (ne_of_gt hs)]
    rw [show 3 * C0 * (s ^ ((3 : ℝ) / 2) / (1 + s) ^ 2) / s
        = 3 * C0 * (s ^ ((3 : ℝ) / 2) / s / (1 + s) ^ 2) from by ring, h1]
    have h2 : s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2 ≤ s ^ (-(3 : ℝ) / 2) := by
      rw [div_le_iff₀ (by positivity)]
      have h3 : s ^ (-(3 : ℝ) / 2) * s ^ (2 : ℕ) = s ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_natCast s 2, ← Real.rpow_add hs]; norm_num
      calc s ^ ((1 : ℝ) / 2) = s ^ (-(3 : ℝ) / 2) * s ^ (2 : ℕ) := h3.symm
        _ ≤ s ^ (-(3 : ℝ) / 2) * (1 + s) ^ 2 := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hs.le _)
            nlinarith
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  refine le_trans (mul_le_mul_of_nonneg_right hMle (by positivity)) ?_
  have hpi : Real.pi / 2 ≤ 2 := by linarith [Real.pi_lt_four]
  have hspos : 0 ≤ 3 * C0 * s ^ (-(3 : ℝ) / 2) := by positivity
  nlinarith [mul_nonneg hC0 hspos]

/-- `L₁₂dens` of `JetBnd`-data is integrable on `(a,∞)`, `a > 0`, as soon as it is continuous
there. -/
theorem JetBnd.dens_integrable {C0 : ℝ} {f : ℝ → ℝ → ℝ} (hC0 : 0 ≤ C0) (hb : JetBnd C0 f)
    (hcont : ContinuousOn (fun s => Work.Elliptic.L12dens f s) (Set.Ioi 0)) {a : ℝ}
    (ha : 0 < a) :
    IntegrableOn (fun s => Work.Elliptic.L12dens f s) (Set.Ioi a) := by
  have hmaj : IntegrableOn (fun s : ℝ => 6 * C0 * s ^ (-(3 : ℝ) / 2)) (Set.Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3 : ℝ) / 2) < -1) ha).const_mul _
  refine Integrable.mono' hmaj ((hcont.mono (Set.Ioi_subset_Ioi ha.le)).aestronglyMeasurable
    measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact hb.dens_bound hC0 (lt_of_lt_of_le ha (le_of_lt hs))

end Work.FTS_RegExport.RXT.Slots
