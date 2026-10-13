/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/HkSqAux/Chain.lean`

The endpoint estimate of **E1**: assembling the pointwise slot sum
(`HkIntegrand_Jeps_le_integral`), the shift step (`integral_shift_le`) and the two measurability
input `aemeasurable_shift_pair` into

  `HkSq α k (J_ε f) ≤ e^{Cε} · HkSq α k f`.

The route is the `lintegral`/Tonelli one: the pointwise bound converts the iterated integral of
`HkIntegrand α k (J_ε f)` into an iterated integral of the shifted `HkIntegrand α k f` against the
probability density `Jker ρ ε`; Tonelli's theorem exchanges the `p`-integration with the
`(z,θ)`-integration; and for each `p` the shift step `integral_shift_le` bounds the result by
`e^{δ(|p₁|+|p₂|)}·HkSq α k f`.  Since the kernel is supported in `|p| ≤ ε`, the total gain is
`e^{(2c+2δ)ε}`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongEps.HkSqAux.Defs
import Submission.Work.FTS.StrongEps.HkSqAux.LogCoord
import Submission.Work.FTS.StrongEps.HkSqAux.HkIntegrand_Jeps_le_integral
import Submission.Work.FTS.StrongEps.HkSqAux.integral_shift_le
import Submission.Work.FTS.StrongEps.HkSqAux.aemeasurable_shift_pair
import Submission.Work.FTS.StrongEps.HkSqAux.aemeasurable_shift_slice
import Submission.Work.FTS.StrongEps.HkSqAux.continuousOn_HkIntegrand_Quad

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.HkSqAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- On the boundary of the closed quadrant (`z = 0`, `θ = 0` or `θ = π/2`) the `H^k`-integrand
vanishes: the radial weight `w` or the angular weight `sin(2θ)^{-η/2}` is `0` there. -/
theorem HkIntegrand_boundary_zero {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {k : ℕ} {f : ℝ → ℝ → ℝ}
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ)
    (hq : ¬(0 < z ∧ θ ∈ Set.Ioo 0 (π / 2))) :
    Work.Spaces.HkIntegrand α k f z θ = 0 := by
  rw [Work.Spaces.Iz] at hz
  rw [Work.Spaces.Iθ] at hθ
  have hη : (Work.Spaces.eta / 2 : ℝ) ≠ 0 := by
    rw [Work.Spaces.eta]; norm_num
  have hγ : (-(Work.Spaces.gam α / 2) : ℝ) ≠ 0 := by
    rw [Work.Spaces.gam]
    intro h
    have h1 : 1 + α / 10 = 0 := by linarith
    linarith [hα.1]
  rcases not_and_or.mp hq with hz0 | hθbad
  · have hz' : z = 0 := le_antisymm (not_lt.mp hz0) hz
    subst hz'
    simp only [Work.Spaces.HkIntegrand, Work.Spaces.w, Work.Spaces.Wt]
    simp
  · have hθbad' : θ ≤ 0 ∨ π / 2 ≤ θ := by
      rcases not_and_or.mp hθbad with h | h
      · exact Or.inl (not_lt.mp h)
      · exact Or.inr (not_lt.mp h)
    have hsin : Real.sin (2 * θ) = 0 := by
      rcases hθbad' with h | h
      · have h' : θ = 0 := le_antisymm h hθ.1
        subst h'
        simp
      · have h' : θ = π / 2 := le_antisymm hθ.2 h
        subst h'
        rw [show 2 * (π / 2) = π by ring, Real.sin_pi]
    simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.wTheta, hsin,
      Real.zero_rpow hη, Real.zero_rpow hγ]
    simp

theorem Jker_support_abs {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {p : ℝ × ℝ} (hp : Jker ρ ε p ≠ 0) : |p.1| + |p.2| ≤ 2 * ε := by
  have h := Jker_ne_zero_support hρ hε hp
  have h1 : p.1 ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg p.2]
  have h2 : p.2 ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg p.1]
  have ha : |p.1| ≤ ε := by
    rw [sq_le_sq] at h1
    rwa [abs_of_nonneg hε.le] at h1
  have hb : |p.2| ≤ ε := by
    rw [sq_le_sq] at h2
    rwa [abs_of_nonneg hε.le] at h2
  linarith

/-- **The pointwise bound in `ℝ≥0∞`**: at every point of the closed quadrant, the `H^k`-integrand
of `J_ε f` is dominated by `e^{2cε}` times the `p`-integral of the shifted `H^k`-integrand of `f`
against the kernel density. -/
theorem ofReal_GJ_le (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) {c : ℝ}
    (hWη : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p : ℝ × ℝ,
      Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        ≤ Real.exp (c * (|p.1| + |p.2|))
          * (Work.Spaces.w (zShift z p.1)
              / (Real.sin (2 * thShift θ p.2)) ^ (Work.Spaces.eta / 2)))
    (hWγ : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p : ℝ × ℝ,
      Work.Spaces.Wt α z θ ≤ Real.exp (c * (|p.1| + |p.2|))
        * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2))
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) (k : ℕ) :
    ENNReal.ofReal (Work.Spaces.HkIntegrand α k (Jeps ρ ε f) z θ)
      ≤ ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
            * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z p.1) (thShift θ p.2)) := by
  by_cases hq : 0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)
  · obtain ⟨hzpos, hθIoo⟩ := hq
    have hpt := HkIntegrand_Jeps_le_integral (f := f) ρ hρ hε hα hf (c := c) hzpos hθIoo k
      (hWη z θ hzpos hθIoo) (hWγ z θ hzpos hθIoo)
    have hcont : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k f q.1 q.2) Quad :=
      continuousOn_HkIntegrand_Quad α k hf
    have hexp : Continuous fun p : ℝ × ℝ => Real.exp (2 * c * (|p.1| + |p.2|)) := by
      refine Real.continuous_exp.comp (Continuous.mul continuous_const ?_)
      refine Continuous.add ?_ ?_
      · exact continuous_abs.comp continuous_fst
      · exact continuous_abs.comp continuous_snd
    have hint : Integrable (fun p : ℝ × ℝ => Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
        * Work.Spaces.HkIntegrand α k f (zShift z p.1) (thShift θ p.2)) := by
      simpa only [mul_assoc] using integrable_Jker_mul ρ hρ hε
        (A := fun p : ℝ × ℝ => Real.exp (2 * c * (|p.1| + |p.2|))
          * Work.Spaces.HkIntegrand α k f (zShift z p.1) (thShift θ p.2))
        (hexp.continuousOn.mul (continuousOn_shift_ball hzpos hθIoo
          (A := fun z' θ' => Work.Spaces.HkIntegrand α k f z' θ')
          (hcont.mono (Kz_prod_Kth_subset_Quad hzpos hε hθIoo))))
    have hnonneg : ∀ p : ℝ × ℝ, 0 ≤ Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
        * Work.Spaces.HkIntegrand α k f (zShift z p.1) (thShift θ p.2) := fun p =>
      mul_nonneg (mul_nonneg (Jker_nonneg ρ hρ ε p) (Real.exp_pos _).le)
        (Work.Spaces.HkIntegrand_nonneg α k f _ _)
    calc ENNReal.ofReal (Work.Spaces.HkIntegrand α k (Jeps ρ ε f) z θ)
        ≤ ENNReal.ofReal (∫ p : ℝ × ℝ, Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
            * Work.Spaces.HkIntegrand α k f (zShift z p.1) (thShift θ p.2)) :=
          ENNReal.ofReal_le_ofReal hpt
      _ = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
              * Work.Spaces.HkIntegrand α k f (zShift z p.1) (thShift θ p.2)) :=
          MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hnonneg)
      _ = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
              * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
              * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z p.1)
                  (thShift θ p.2)) := by
          refine lintegral_congr fun p => ?_
          rw [ENNReal.ofReal_mul (mul_nonneg (Jker_nonneg ρ hρ ε p) (Real.exp_pos _).le),
            ENNReal.ofReal_mul (Jker_nonneg ρ hρ ε p)]
  · rw [HkIntegrand_boundary_zero hα hz hθ hq, ENNReal.ofReal_zero]
    exact zero_le

theorem ofReal_exp_mul (a b : ℝ) :
    ENNReal.ofReal (Real.exp a) * ENNReal.ofReal (Real.exp b)
      = ENNReal.ofReal (Real.exp (a + b)) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos a).le, ← Real.exp_add]

/-- **Tonelli's theorem for the shifted slots**: exchanging the `(z,θ)`-integration with the
`p`-integration in the pointwise bound of `ofReal_GJ_le`. -/
theorem fubini_shift {ρ : ℝ × ℝ → ℝ} (hρc : Continuous ρ) {ε c : ℝ} {α : ℝ} {k : ℕ}
    {f : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k f q.1 q.2) Quad) :
    (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ,
        ENNReal.ofReal (Jker ρ ε p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z p.1) (thShift θ p.2)))
      = ∫⁻ p : ℝ × ℝ, (ENNReal.ofReal (Jker ρ ε p)
            * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|))))
          * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z p.1) (thShift θ p.2))) := by
  have hpair : AEMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      ENNReal.ofReal (Jker ρ ε q.2) * ENNReal.ofReal (Real.exp (2 * c * (|q.2.1| + |q.2.2|)))
        * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift q.1.1 q.2.1)
            (thShift q.1.2 q.2.2)))
      (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume) := by
    have h0 := aemeasurable_shift_pair (G := fun z θ => Work.Spaces.HkIntegrand α k f z θ)
      hcont ρ hρc ε
    have hm : Measurable fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
        ENNReal.ofReal (Real.exp (2 * c * (|q.2.1| + |q.2.2|))) := by
      refine ENNReal.measurable_ofReal.comp ?_
      refine Real.continuous_exp.measurable.comp ?_
      have h1 : Measurable fun q : (ℝ × ℝ) × (ℝ × ℝ) => |q.2.1| :=
        continuous_abs.measurable.comp measurable_snd.fst
      have h2 : Measurable fun q : (ℝ × ℝ) × (ℝ × ℝ) => |q.2.2| :=
        continuous_abs.measurable.comp measurable_snd.snd
      exact (h1.add h2).const_mul (2 * c)
    refine (h0.mul hm.aemeasurable).congr (Eventually.of_forall fun q => ?_)
    simp only [Pi.mul_apply]
    ring
  -- the iterated `(z,θ)`-integral as an integral over the product space
  have hL : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ,
        ENNReal.ofReal (Jker ρ ε p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z p.1) (thShift θ p.2)))
      = ∫⁻ q : ℝ × ℝ, ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
          * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift q.1 p.1) (thShift q.2 p.2))
        ∂MeasureTheory.volume
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [show ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))
        = (MeasureTheory.volume.prod MeasureTheory.volume).restrict
            (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) from Measure.prod_restrict (μ := MeasureTheory.volume) (ν := MeasureTheory.volume) _ _]
    exact (MeasureTheory.setLIntegral_prod (fun q : ℝ × ℝ => ∫⁻ p : ℝ × ℝ,
      ENNReal.ofReal (Jker ρ ε p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
        * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift q.1 p.1) (thShift q.2 p.2)))
      (s := Work.Spaces.Iz) (t := Work.Spaces.Iθ) (by
        rw [← Measure.prod_restrict (μ := MeasureTheory.volume) (ν := MeasureTheory.volume)]
        exact hpair.lintegral_prod_right')).symm
  rw [hL]
  -- Tonelli
  rw [MeasureTheory.lintegral_lintegral_swap
    (μ := (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) (ν := MeasureTheory.volume) hpair]
  -- back to the iterated form, for each `p`
  refine lintegral_congr fun p => ?_
  have hXne : (ENNReal.ofReal (Jker ρ ε p)
      * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  rw [MeasureTheory.lintegral_const_mul' _ _ hXne]
  have hAB : (∫⁻ q : ℝ × ℝ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
        (zShift q.1 p.1) (thShift q.2 p.2))
      ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z p.1) (thShift θ p.2)) := by
    rw [show ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))
        = (MeasureTheory.volume.prod MeasureTheory.volume).restrict
            (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) from Measure.prod_restrict (μ := MeasureTheory.volume) (ν := MeasureTheory.volume) _ _]
    exact MeasureTheory.setLIntegral_prod (fun q : ℝ × ℝ => ENNReal.ofReal
      (Work.Spaces.HkIntegrand α k f (zShift q.1 p.1) (thShift q.2 p.2)))
      (s := Work.Spaces.Iz) (t := Work.Spaces.Iθ) (by
        rw [← Measure.prod_restrict (μ := MeasureTheory.volume) (ν := MeasureTheory.volume)]
        exact aemeasurable_shift_slice hcont p)
  rw [hAB]

theorem Jker_exp_integral_le {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ) {ε c δ : ℝ} (hε : 0 < ε)
    (hc0 : 0 ≤ c) (hδ0 : 0 ≤ δ) :
    (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
        * ENNReal.ofReal (Real.exp ((2 * c + δ) * (|p.1| + |p.2|))))
      ≤ ENNReal.ofReal (Real.exp ((4 * c + 2 * δ) * ε)) := by
  have hexp : Continuous fun p : ℝ × ℝ => Real.exp ((2 * c + δ) * (|p.1| + |p.2|)) := by
    refine Real.continuous_exp.comp (Continuous.mul continuous_const ?_)
    refine Continuous.add ?_ ?_
    · exact continuous_abs.comp continuous_fst
    · exact continuous_abs.comp continuous_snd
  have hint : Integrable (fun p : ℝ × ℝ => Jker ρ ε p
      * Real.exp ((2 * c + δ) * (|p.1| + |p.2|))) :=
    integrable_Jker_mul ρ hρ hε (A := fun p : ℝ × ℝ =>
      Real.exp ((2 * c + δ) * (|p.1| + |p.2|))) hexp.continuousOn
  have hint2 : Integrable (fun p : ℝ × ℝ => Real.exp ((4 * c + 2 * δ) * ε) * Jker ρ ε p) := by
    simpa only [mul_comm] using integrable_Jker_mul ρ hρ hε
      (A := fun _ : ℝ × ℝ => Real.exp ((4 * c + 2 * δ) * ε)) continuousOn_const
  have hpoint : ∀ p : ℝ × ℝ, Jker ρ ε p * Real.exp ((2 * c + δ) * (|p.1| + |p.2|))
      ≤ Real.exp ((4 * c + 2 * δ) * ε) * Jker ρ ε p := by
    intro p
    by_cases hp : Jker ρ ε p = 0
    · rw [hp, zero_mul, mul_zero]
    · have hb := Jker_support_abs hρ hε hp
      calc Jker ρ ε p * Real.exp ((2 * c + δ) * (|p.1| + |p.2|))
          ≤ Jker ρ ε p * Real.exp ((2 * c + δ) * (2 * ε)) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Jker_nonneg ρ hρ ε p)
            exact mul_le_mul_of_nonneg_left hb (by linarith)
        _ = Real.exp ((4 * c + 2 * δ) * ε) * Jker ρ ε p := by
            rw [show Jker ρ ε p * Real.exp ((2 * c + δ) * (2 * ε))
                = Real.exp ((2 * c + δ) * (2 * ε)) * Jker ρ ε p from by rw [mul_comm]]
            congr 1
            ring
  rw [show (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
        * ENNReal.ofReal (Real.exp ((2 * c + δ) * (|p.1| + |p.2|))))
      = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p
          * Real.exp ((2 * c + δ) * (|p.1| + |p.2|))) from by
    refine lintegral_congr fun p => ?_
    rw [ENNReal.ofReal_mul (Jker_nonneg ρ hρ ε p)]]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun p => mul_nonneg (Jker_nonneg ρ hρ ε p) (Real.exp_pos _).le)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (∫ p : ℝ × ℝ, Jker ρ ε p * Real.exp ((2 * c + δ) * (|p.1| + |p.2|)))
      ≤ ∫ p : ℝ × ℝ, Real.exp ((4 * c + 2 * δ) * ε) * Jker ρ ε p :=
        integral_mono hint hint2 hpoint
    _ = Real.exp ((4 * c + 2 * δ) * ε) * ∫ p : ℝ × ℝ, Jker ρ ε p := by
        rw [MeasureTheory.integral_const_mul]
    _ = Real.exp ((4 * c + 2 * δ) * ε) := by
        rw [Jker_integral_eq_one ρ hρ hε, mul_one]

/-- **The weighted `H^k`-bound for `J_ε`** in `ℝ≥0∞`: assembling the pointwise slot sum, Tonelli
and the shift step. -/
theorem ofReal_HkSq_Jeps_le (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) {α : ℝ} (hα : α ∈ Set.Ioc 0 1)
    {k : ℕ} {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad)
    (hF : Work.Spaces.HkMem α k f) (hFJ : Work.Spaces.HkMem α k (Jeps ρ ε f))
    {c δ : ℝ} (hc0 : 0 ≤ c) (hδ0 : 0 ≤ δ)
    (hWη : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p : ℝ × ℝ,
      Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        ≤ Real.exp (c * (|p.1| + |p.2|))
          * (Work.Spaces.w (zShift z p.1)
              / (Real.sin (2 * thShift θ p.2)) ^ (Work.Spaces.eta / 2)))
    (hWγ : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p : ℝ × ℝ,
      Work.Spaces.Wt α z θ ≤ Real.exp (c * (|p.1| + |p.2|))
        * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2))
    (hJac : ∀ s ζ p₁ p₂ : ℝ, logJac s ζ
      ≤ Real.exp (δ * (|p₁| + |p₂|)) * logJac (s - p₁) (ζ - p₂)) :
    ENNReal.ofReal (Work.Spaces.HkSq α k (Jeps ρ ε f))
      ≤ ENNReal.ofReal (Real.exp ((4 * c + 2 * δ) * ε))
          * ENNReal.ofReal (Work.Spaces.HkSq α k f) := by
  have hcont : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k f q.1 q.2) Quad :=
    continuousOn_HkIntegrand_Quad α k hf
  set C : ENNReal := ENNReal.ofReal (Work.Spaces.HkSq α k f) with hC
  set E1 : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
    with hE1
  set E2 : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
    with hE2
  set E3 : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal (Real.exp ((2 * c + δ) * (|p.1| + |p.2|)))
    with hE3
  set K : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal (Jker ρ ε p) with hK
  set Φ : ℝ → ℝ → ENNReal := fun z θ =>
    ENNReal.ofReal (Work.Spaces.HkIntegrand α k (Jeps ρ ε f) z θ) with hΦ
  set Ψ : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal
    (Real.exp (δ * (|p.1| + |p.2|))) * C with hΨ
  have h1 : ENNReal.ofReal (Work.Spaces.HkSq α k (Jeps ρ ε f))
      = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, Φ z θ := by
    rw [hΦ]
    rw [Work.Spaces.HkSq]
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hFJ.2 (Eventually.of_forall fun z =>
      integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k (Jeps ρ ε f) z θ)]
    exact MeasureTheory.setLIntegral_congr_fun measurableSet_Ici (fun z hz =>
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hFJ.1 z hz)
        (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k (Jeps ρ ε f) z θ))
  have h2 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, Φ z θ)
      ≤ (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ, K p * E1 p
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z p.1)
              (thShift θ p.2))) := by
    refine MeasureTheory.setLIntegral_mono' measurableSet_Ici fun z hz =>
      MeasureTheory.setLIntegral_mono' measurableSet_Icc fun θ hθ => ?_
    rw [hΦ, hK, hE1]
    exact ofReal_GJ_le ρ hρ hε hα hf hWη hWγ hz hθ k
  have h3 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ, K p * E1 p
        * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z p.1) (thShift θ p.2)))
      = (∫⁻ p : ℝ × ℝ, (K p * E1 p)
          * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z p.1)
                (thShift θ p.2)))) := by
    rw [hK, hE1]
    exact fubini_shift hρ.cont hcont
  have h4 : (∫⁻ p : ℝ × ℝ, (K p * E1 p)
          * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z p.1)
                (thShift θ p.2))))
      ≤ (∫⁻ p : ℝ × ℝ, (K p * E1 p)
          * (E2 p * C)) := by
    refine lintegral_mono fun p => mul_le_mul_right ?_ _
    rw [hE2, hC]
    exact integral_shift_le hJac hF hcont p
  have h5 : (∫⁻ p : ℝ × ℝ, (K p * E1 p) * (E2 p * C))
      = C * (∫⁻ p : ℝ × ℝ, K p * E3 p) := by
    have hAB : ∀ p : ℝ × ℝ, E1 p * E2 p = E3 p := by
      intro p
      rw [hE1, hE2, hE3, ofReal_exp_mul]
      congr 2
      ring
    have hstep1 : (∫⁻ p : ℝ × ℝ, (K p * E1 p) * (E2 p * C))
        = ∫⁻ p : ℝ × ℝ, (K p * (E1 p * E2 p)) * C :=
      lintegral_congr fun p => by ring
    have hstep2 : (∫⁻ p : ℝ × ℝ, (K p * (E1 p * E2 p)) * C)
        = (∫⁻ p : ℝ × ℝ, K p * (E1 p * E2 p)) * C :=
      MeasureTheory.lintegral_mul_const' C _ ENNReal.ofReal_ne_top
    have hstep3 : (∫⁻ p : ℝ × ℝ, K p * (E1 p * E2 p)) = ∫⁻ p : ℝ × ℝ, K p * E3 p :=
      lintegral_congr fun p => by rw [hAB p]
    rw [hstep1, hstep2, hstep3, mul_comm]
  have h6 : (∫⁻ p : ℝ × ℝ, K p * E3 p) ≤ ENNReal.ofReal (Real.exp ((4 * c + 2 * δ) * ε)) := by
    rw [hK, hE3]
    exact Jker_exp_integral_le hρ hε hc0 hδ0
  calc ENNReal.ofReal (Work.Spaces.HkSq α k (Jeps ρ ε f))
      = (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, Φ z θ) := h1
    _ ≤ (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ, K p * E1 p
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z p.1)
              (thShift θ p.2))) := h2
    _ = (∫⁻ p : ℝ × ℝ, (K p * E1 p)
          * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z p.1)
                (thShift θ p.2)))) := h3
    _ ≤ (∫⁻ p : ℝ × ℝ, (K p * E1 p) * (E2 p * C)) := h4
    _ = C * (∫⁻ p : ℝ × ℝ, K p * E3 p) := h5
    _ ≤ C * ENNReal.ofReal (Real.exp ((4 * c + 2 * δ) * ε)) :=
        mul_le_mul_right h6 C
    _ = ENNReal.ofReal (Real.exp ((4 * c + 2 * δ) * ε))
          * ENNReal.ofReal (Work.Spaces.HkSq α k f) := by rw [hC, mul_comm]

end Work.FTS.StrongEps.HkSqAux
