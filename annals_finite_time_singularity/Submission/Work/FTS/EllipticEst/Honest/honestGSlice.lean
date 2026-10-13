/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `∂_zΨ`-slice of an honest datum is square integrable against the angular weight

For honest data `Hon α F Ψ` (Elgindi, Annals **194** (2021), the level-`0` elliptic estimate)
and every `z > 0`, the angular slice

  `θ ↦ (∂_zΨ(z,θ))² · σ θ`,   `σ θ = sin(2θ)^{-η}`,   `η = 99/100`,

is integrable on `Iθ = [0,π/2]`.

## Route

The honest class controls, at the slice `z`, the quantities `F`, `∂_θθΨ` and `z²∂_zzΨ`
(`Hon.memF`, `Hon.memB`, `Hon.memA`), but nothing directly about `∂_zΨ`.  The two inputs are

* *(boundedness of the slices of `Ψ`)* `memB` gives `(∂_θθΨ(z,·))²σ ∈ L¹`, hence (because
  `σ ≥ 1` on `(0,π/2)`) `∂_θθΨ(z,·) ∈ L¹`, and two integrations by the fundamental theorem of
  calculus (`Work.FTS.EllipticEst.SgamBound.*`) bound `Ψ(z,·)` on the open interval;

* *(the box bound)* the second-order Taylor formula along the `z`-variable,
  `∂_zΨ(z,θ) = Ψ(z+1,θ) - Ψ(z,θ) - ∫_s (z+1-s)∂_zzΨ(s,θ)`,
  together with the Cauchy–Schwarz (Jensen) bound `(∫_s |∂_zzΨ(s,θ)|)² ≤ ∫_s (∂_zzΨ(s,θ))²` over
  the unit interval; the right-hand side is `σ`-square integrable in `θ` by Tonelli, because
  `Hon.memA` supplies both the slicewise `σ`-square integrability of `∂_zzΨ` and the
  `s`-integrability of its `θ`-integral.

Since `σ ≥ 0` on `Iθ`, the level term `(Ψ(z+1,θ) - Ψ(z,θ))²σ` is dominated by a constant times
`σ ∈ L¹`, and the two pieces are assembled with `(a+b)² ≤ 2a² + 2b²`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.Honest.HonEnergyAux
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.aesm_uncurry_restrict_open
import Submission.Work.FTS.EllipticEst.SgamBound.abs_deriv_sub_le_integral_abs_D2
import Submission.Work.FTS.EllipticEst.SgamBound.abs_sub_le_mul_abs_sub_of_deriv_bound
import Submission.Work.FTS.EllipticEst.SgamBound.integrableOn_abs_of_sq_mul_sEta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Elementary facts about the weight `σ` -/

/-- The two names of the angular weight agree. -/
theorem sig_eq_sEta : Work.FTS.EllipticEst.AngSecond.sig = Work.FTS.EllipticEst.sEta := rfl

/-- `sin(2θ) > 0` on the open interval. -/
theorem sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `σ` is continuous on the open quadrant. -/
theorem continuousOn_sig_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2)
      Work.FTS.EllipticEst.Q0 := by
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, h0, h1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact sin_two_pos_of_mem_Ioo ⟨h0, h1⟩
  have hbase : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  exact hbase.rpow_const (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))

/-- `σ` is continuous on the open angular interval.

**Renamed from `continuousOn_sig_Ioo` (2026-10-04, branch-merge repair).**  `Honest/sliceBarSq2.lean`
declares a *different* lemma under that exact name, so any module whose import cone contained both
files was unimportable (`environment already contains 'Work.FTS.EllipticEst.Honest.continuousOn_sig_Ioo'`),
which split the elliptic library into two branches that several assemblies need together.  This
copy is used only by `aesm_sig_Iθ` below, and nothing outside this file refers to it; the external
references to the name (`ThetaU/Pieces/AeBarHkMem.lean`) resolve to `sliceBarSq2`'s version. -/
theorem continuousOn_sig_Ioo_open :
    ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.sEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hcont : Continuous fun θ : ℝ => ((1 : ℝ), θ) := by fun_prop
  have hmap : Set.MapsTo (fun θ : ℝ => ((1 : ℝ), θ)) (Set.Ioo 0 (Real.pi / 2))
      Work.FTS.EllipticEst.Q0 := fun θ hθ => ⟨by norm_num, hθ.1, hθ.2⟩
  have h := continuousOn_sig_Q0.comp hcont.continuousOn hmap
  simpa [Function.comp_def] using h

/-- `σ` is a.e. strongly measurable on `Iθ`. -/
theorem aesm_sig_Iθ :
    MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => Work.FTS.EllipticEst.sEta θ)
      (volume.restrict Work.Spaces.Iθ) := by
  rw [restrict_Iθ_eq_Ioo]
  exact continuousOn_sig_Ioo_open.aestronglyMeasurable measurableSet_Ioo

/-- The honest hypothesis gives smoothness of `Ψ` on the open quadrant. -/
theorem hon_smoothOpen {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) :
    Work.FTS.EllipticEst.SmoothOpen Ψ :=
  Work.FTS.EllipticEst.smoothOpen_of_forall h.sm

/-! ## The angular slices of `Ψ` are bounded -/

/-- **Boundedness of the slices of `Ψ`.**  `memB` gives `(∂_θθΨ(z,·))²σ ∈ L¹(Iθ)`; because
`σ ≥ 1` on `(0,π/2)` this makes `∂_θθΨ(z,·)` integrable, and two integrations along `θ` bound
the slice. -/
theorem hon_psi_slice_bdd {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z : ℝ} (hz : 0 < z) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |Ψ z θ| ≤ M := by
  have hsm : ∀ n : ℕ, ContDiffOn ℝ n (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) := by
    intro n
    have hf : ContDiff ℝ n (fun θ : ℝ => (z, θ)) := by fun_prop
    have hcomp := ContDiffOn.comp (f := fun θ : ℝ => (z, θ)) (g := Function.uncurry Ψ)
      (h.sm n) hf.contDiffOn (fun θ hθ => ⟨hz, hθ⟩)
    simpa [Function.comp_def, Function.uncurry] using hcomp
  have hint : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := hon_memB_sigma h hz
  have hint' : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.TT.D2 (fun s => Ψ z s) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    refine MeasureTheory.IntegrableOn.congr_fun hint (fun θ _ => ?_) measurableSet_Icc
    rfl
  have hcont2 : ContinuousOn (fun θ => Work.FTS.EllipticEst.TT.D2 (fun s => Ψ z s) θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    have h1 : ContDiffOn ℝ 1 (deriv (fun s => Ψ z s)) (Set.Ioo 0 (Real.pi / 2)) :=
      (hsm 2).deriv_of_isOpen isOpen_Ioo (by norm_num)
    have h2 : ContDiffOn ℝ 0 (deriv (deriv (fun s => Ψ z s))) (Set.Ioo 0 (Real.pi / 2)) :=
      h1.deriv_of_isOpen isOpen_Ioo (by norm_num)
    have h3 : Work.FTS.EllipticEst.TT.D2 (fun s => Ψ z s)
        = deriv (deriv (fun s => Ψ z s)) := rfl
    rw [h3]
    exact h2.continuousOn
  have hD2abs : MeasureTheory.IntegrableOn
      (fun θ => |Work.FTS.EllipticEst.TT.D2 (fun s => Ψ z s) θ|) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.SgamBound.integrableOn_abs_of_sq_mul_sEta hcont2 hint'
  have hπ4 : Real.pi / 4 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hbound1 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv (fun s => Ψ z s) θ - deriv (fun s => Ψ z s) (Real.pi / 4)|
        ≤ ∫ x in Work.Spaces.Iθ, |Work.FTS.EllipticEst.TT.D2 (fun s => Ψ z s) x| :=
    fun θ hθ =>
      Work.FTS.EllipticEst.SgamBound.abs_deriv_sub_le_integral_abs_D2 hsm hD2abs hθ hπ4
  set E : ℝ := ∫ x in Work.Spaces.Iθ, |Work.FTS.EllipticEst.TT.D2 (fun s => Ψ z s) x| with hE
  have hE0 : 0 ≤ E := by
    rw [hE]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun x _ => abs_nonneg _)
  set K : ℝ := |deriv (fun s => Ψ z s) (Real.pi / 4)| + E with hK
  have hK0 : 0 ≤ K := by rw [hK]; exact add_nonneg (abs_nonneg _) hE0
  have hKbd : ∀ ξ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun s => Ψ z s) ξ| ≤ K := by
    intro ξ hξ
    have h1 := hbound1 ξ hξ
    have h2 : |deriv (fun s => Ψ z s) ξ|
        ≤ |deriv (fun s => Ψ z s) ξ - deriv (fun s => Ψ z s) (Real.pi / 4)|
          + |deriv (fun s => Ψ z s) (Real.pi / 4)| := by
      have := abs_add_le (deriv (fun s => Ψ z s) ξ - deriv (fun s => Ψ z s) (Real.pi / 4))
        (deriv (fun s => Ψ z s) (Real.pi / 4))
      simpa using this
    rw [hK, hE]
    linarith
  set M : ℝ := |Ψ z (Real.pi / 4)| + K * (Real.pi / 2) with hM
  have hM0 : 0 ≤ M := by
    rw [hM]; exact add_nonneg (abs_nonneg _) (mul_nonneg hK0 (by positivity))
  refine ⟨M, hM0, fun θ hθ => ?_⟩
  have h2 := Work.FTS.EllipticEst.SgamBound.abs_sub_le_mul_abs_sub_of_deriv_bound
    hsm hθ hπ4 hKbd
  have h3 : |θ - Real.pi / 4| ≤ Real.pi / 2 := by
    rw [abs_le]
    exact ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  have h4 : K * |θ - Real.pi / 4| ≤ K * (Real.pi / 2) :=
    mul_le_mul_of_nonneg_left h3 hK0
  calc |Ψ z θ| = |(Ψ z θ - Ψ z (Real.pi / 4)) + Ψ z (Real.pi / 4)| := by
        rw [sub_add_cancel]
    _ ≤ |Ψ z θ - Ψ z (Real.pi / 4)| + |Ψ z (Real.pi / 4)| := abs_add_le _ _
    _ ≤ K * (Real.pi / 2) + |Ψ z (Real.pi / 4)| := by linarith
    _ = M := by rw [hM]; ring

/-! ## The one-dimensional Cauchy–Schwarz (Jensen) bound for interval integrals -/

/-- For a function continuous on `[a,a+1]`, the square of the integral is at most the integral of
the square: Jensen's inequality for the convex function `x ↦ x²` with respect to the probability
measure `vol.restrict (a,a+1]`. -/
theorem sq_integral_le_of_continuousOn {a : ℝ} {u : ℝ → ℝ}
    (hu : ContinuousOn u (Set.Icc a (a + 1))) :
    (∫ x in a..(a + 1), u x) ^ 2 ≤ ∫ x in a..(a + 1), (u x) ^ 2 := by
  haveI : MeasureTheory.IsProbabilityMeasure (volume.restrict (Set.Ioc a (a + 1))) := by
    refine ⟨?_⟩
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc]
    norm_num
  have huI : MeasureTheory.Integrable u (volume.restrict (Set.Ioc a (a + 1))) :=
    (hu.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hu2I : MeasureTheory.Integrable (fun x => (u x) ^ 2) (volume.restrict (Set.Ioc a (a + 1))) :=
    ((hu.pow 2).integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hj := ConvexOn.map_integral_le (μ := volume.restrict (Set.Ioc a (a + 1))) (s := Set.univ)
    (f := u) (g := fun x : ℝ => x ^ 2)
    (Even.convexOn_pow (𝕜 := ℝ) even_two) (continuousOn_id.pow 2) isClosed_univ
    (Filter.Eventually.of_forall (fun x => Set.mem_univ _)) huI hu2I
  rw [intervalIntegral.integral_of_le (le_add_of_nonneg_right (by norm_num : (0:ℝ) ≤ 1)),
    intervalIntegral.integral_of_le (le_add_of_nonneg_right (by norm_num : (0:ℝ) ≤ 1))]
  exact hj

/-! ## The box bound -/

/-- **`(∫_s |∂_zzΨ(s,θ)|)² · σ θ` is integrable in `θ`.**  The pointwise Cauchy–Schwarz bound over
the unit interval `[z,z+1]` reduces this to the `θ`-integrability of the box integral of
`(∂_zzΨ)²σ`, which is Tonelli applied to the honesty `Hon.memA` of `z²∂_zzΨ`. -/
theorem hon_box_abs_sq {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (∫ s in z..(z + 1), |Work.Spaces.pzIter 2 Ψ s θ|) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ := by
  simp only [sig_eq_sEta]
  have hS := hon_smoothOpen h
  have hzle : z ≤ z + 1 := by linarith
  -- ### the pointwise identity relating the `ℋ`-integrand of `z²∂_zzΨ` to the box integrand
  have hk_w : ∀ s : ℝ, 0 < s → ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 (fun s θ => s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ) s θ
        = (1 + s) ^ 4
          * ((Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    intro s hs θ hθ
    rw [HkIntegrand_zero_eq' hθ]
    have hws : (Work.Spaces.w s) ^ 2 = (1 + s) ^ 4 / s ^ 4 := by
      rw [Work.Spaces.w]
      field_simp
    rw [hws]
    field_simp
  -- ### continuity of the box integrand on the open quadrant and its measurability
  have hKcont : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pzIter 2 Ψ p.1 p.2) ^ 2
        * Work.FTS.EllipticEst.sEta p.2) Work.FTS.EllipticEst.Q0 :=
    ((hS.pzIter 2).continuousOn.pow 2).mul continuousOn_sig_Q0
  have hK_aesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.pzIter 2 Ψ p.1 p.2) ^ 2
        * Work.FTS.EllipticEst.sEta p.2)
      ((volume.restrict (Set.Ioc z (z + 1))).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.FTS.EllipticEst.aesm_uncurry_restrict_open _
      (by simpa [Work.FTS.EllipticEst.Q0] using hKcont) (le_of_lt hz)
  -- ### the `θ`-marginal of the box integrand is integrable in `s` (from `memA`)
  have hA2sub : MeasureTheory.IntegrableOn (fun s => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 (fun s θ => s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ) s θ)
      (Set.Ioc z (z + 1)) :=
    h.memA.2.mono_set (fun s hs => by
      rw [Work.Spaces.Iz]; exact le_of_lt (lt_trans hz hs.1))
  have hKmarg : MeasureTheory.IntegrableOn (fun s => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (Set.Ioc z (z + 1)) := by
    have hdom : MeasureTheory.IntegrableOn (fun s => ((1 + z) ^ 4)⁻¹
        * |∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (fun s θ => s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ) s θ|)
        (Set.Ioc z (z + 1)) :=
      (hA2sub.abs).const_mul _
    have haesm : MeasureTheory.AEStronglyMeasurable (fun s => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        (volume.restrict (Set.Ioc z (z + 1))) := hK_aesm.integral_prod_right'
    refine MeasureTheory.Integrable.mono' hdom haesm ?_
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with s hs
    have hs0 : 0 < s := lt_trans hz hs.1
    have hid : (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 (fun s θ => s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ) s θ)
        = (1 + s) ^ 4 * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => hk_w s hs0 θ hθ)
    have h1 : (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        = (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (fun s θ => s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ) s θ)
          / (1 + s) ^ 4 := by
      rw [hid]
      field_simp
    have hX : 0 ≤ |∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (fun s θ => s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ) s θ| :=
      abs_nonneg _
    have hzs : z < s := hs.1
    have hinv : ((1 + s) ^ 4)⁻¹ ≤ ((1 + z) ^ 4)⁻¹ :=
      (inv_le_inv₀ (by positivity : (0 : ℝ) < (1 + s) ^ 4)
        (by positivity : (0 : ℝ) < (1 + z) ^ 4)).mpr
        (pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 + z)
          (by linarith : 1 + z ≤ 1 + s) 4)
    rw [Real.norm_eq_abs, h1, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < (1 + s) ^ 4)]
    calc |∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (fun s θ => s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ) s θ|
          / (1 + s) ^ 4
        = |∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (fun s θ => s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ) s θ|
          * ((1 + s) ^ 4)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ |∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (fun s θ => s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ) s θ|
          * ((1 + z) ^ 4)⁻¹ := mul_le_mul_of_nonneg_left hinv hX
      _ = ((1 + z) ^ 4)⁻¹ * |∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (fun s θ => s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ) s θ| :=
          by ring
  -- ### Tonelli: the product integrand is integrable, hence so is the `s`-marginal in `θ`
  have hprod : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.Spaces.pzIter 2 Ψ p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2)
      ((volume.restrict (Set.Ioc z (z + 1))).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [MeasureTheory.integrable_prod_iff hK_aesm]
    constructor
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      filter_upwards with s hs
      exact hon_memA_sigma h (lt_trans hz hs.1)
    · refine hKmarg.congr (Filter.Eventually.of_forall (fun s => ?_))
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
      have h0 : 0 ≤ (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
        mul_nonneg (sq_nonneg _) (sEta_nonneg hθ)
      rw [Real.norm_eq_abs]
      change (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        = |(Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ|
      exact (abs_of_nonneg h0).symm
  have hth : MeasureTheory.Integrable (fun θ => ∫ s,
      ‖(Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ‖
        ∂(volume.restrict (Set.Ioc z (z + 1)))) (volume.restrict Work.Spaces.Iθ) :=
    hprod.integral_norm_prod_right
  -- ### the dominating function in `θ`
  have hdomθ : MeasureTheory.IntegrableOn (fun θ => ∫ s in z..(z + 1),
      (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
    refine hth.congr ?_
    rw [restrict_Iθ_eq_Ioo]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    rw [intervalIntegral.integral_of_le hzle]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun s _ => ?_)
    have h0 : 0 ≤ (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
      mul_nonneg (sq_nonneg _) (sEta_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
    rw [Real.norm_eq_abs]
    exact abs_of_nonneg h0
  -- ### measurability of the target
  have haesmθ : MeasureTheory.AEStronglyMeasurable (fun θ =>
      (∫ s in z..(z + 1), |Work.Spaces.pzIter 2 Ψ s θ|) ^ 2
        * Work.FTS.EllipticEst.sEta θ) (volume.restrict Work.Spaces.Iθ) := by
    have h1 : MeasureTheory.AEStronglyMeasurable (fun θ =>
        ∫ s in z..(z + 1), |Work.Spaces.pzIter 2 Ψ s θ|)
        (volume.restrict Work.Spaces.Iθ) := by
      have habs : ContinuousOn (fun p : ℝ × ℝ => |Work.Spaces.pzIter 2 Ψ p.1 p.2|)
          Work.FTS.EllipticEst.Q0 := (hS.pzIter 2).continuousOn.abs
      have h2 : MeasureTheory.AEStronglyMeasurable
          (fun p : ℝ × ℝ => |Work.Spaces.pzIter 2 Ψ p.2 p.1|)
          ((volume.restrict Work.Spaces.Iθ).prod (volume.restrict (Set.Ioc z (z + 1)))) := by
        refine (Work.FTS.EllipticEst.aesm_uncurry_restrict_open
          (fun p : ℝ × ℝ => |Work.Spaces.pzIter 2 Ψ p.1 p.2|) ?_ (le_of_lt hz)).prod_swap
        simpa [Work.FTS.EllipticEst.Q0] using habs
      have h3 := h2.integral_prod_right'
      simpa [intervalIntegral.integral_of_le hzle] using h3
    exact (h1.pow 2).mul aesm_sig_Iθ
  -- ### the pointwise Cauchy–Schwarz bound and the conclusion
  refine MeasureTheory.Integrable.mono' hdomθ haesmθ ?_
  rw [restrict_Iθ_eq_Ioo]
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
  have hcont2 : ContinuousOn (fun s => |Work.Spaces.pzIter 2 Ψ s θ|) (Set.Icc z (z + 1)) := by
    refine ((hS.pzIter 2).curry_z hθ).continuousOn.abs.mono ?_
    intro s hs
    exact lt_of_lt_of_le hz hs.1
  have hcs := sq_integral_le_of_continuousOn hcont2
  have hsq : (∫ s in z..(z + 1), |Work.Spaces.pzIter 2 Ψ s θ|) ^ 2
      ≤ ∫ s in z..(z + 1), (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 := by
    refine le_trans hcs (le_of_eq ?_)
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    rw [sq_abs]
  have hsig0 : 0 ≤ Work.FTS.EllipticEst.sEta θ := sEta_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  calc ‖(∫ s in z..(z + 1), |Work.Spaces.pzIter 2 Ψ s θ|) ^ 2
        * Work.FTS.EllipticEst.sEta θ‖
      = (∫ s in z..(z + 1), |Work.Spaces.pzIter 2 Ψ s θ|) ^ 2
        * Work.FTS.EllipticEst.sEta θ :=
        Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hsig0)
    _ ≤ (∫ s in z..(z + 1), (Work.Spaces.pzIter 2 Ψ s θ) ^ 2)
        * Work.FTS.EllipticEst.sEta θ :=
        mul_le_mul_of_nonneg_right hsq hsig0
    _ = ∫ s in z..(z + 1),
          (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
        rw [intervalIntegral.integral_mul_const]

/-! ## The second-order Taylor formula along `z` -/

/-- **The `z`-Taylor formula for `∂_zΨ`** (an integration by parts along the unit interval):
`∂_zΨ(z,θ) = Ψ(z+1,θ) - Ψ(z,θ) - ∫_s (z+1-s)∂_zzΨ(s,θ)`. -/
theorem hon_pz_taylor {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.pz Ψ z θ = (Ψ (z + 1) θ - Ψ z θ)
      - ∫ s in z..(z + 1), (z + 1 - s) * Work.Spaces.pzIter 2 Ψ s θ := by
  have hS := hon_smoothOpen h
  have hzle : z ≤ z + 1 := by linarith
  have hmem : ∀ s ∈ Set.uIcc z (z + 1), 0 < s := by
    intro s hs
    rw [Set.uIcc_of_le hzle] at hs
    exact lt_of_lt_of_le hz hs.1
  have hderiv_u : ∀ s ∈ Set.uIcc z (z + 1),
      HasDerivAt (fun t => Work.Spaces.pz Ψ t θ) (Work.Spaces.pzIter 2 Ψ s θ) s :=
    fun s hs => hS.hasDerivAt_slice_pzIter 1 hθ (hmem s hs)
  have hderiv_v : ∀ s ∈ Set.uIcc z (z + 1),
      HasDerivAt (fun t : ℝ => (z + 1) - t) (-1) s :=
    fun s _ => (hasDerivAt_id s).const_sub (z + 1)
  have hcont_u : ContinuousOn (fun s => Work.Spaces.pz Ψ s θ) (Set.uIcc z (z + 1)) :=
    (hS.pz.curry_z hθ).continuousOn.mono (fun s hs => hmem s hs)
  have hcont_u2 : ContinuousOn (fun s => Work.Spaces.pzIter 2 Ψ s θ) (Set.uIcc z (z + 1)) :=
    ((hS.pzIter 2).curry_z hθ).continuousOn.mono (fun s hs => hmem s hs)
  have hcont_v : ContinuousOn (fun s : ℝ => (z + 1) - s) (Set.uIcc z (z + 1)) :=
    (continuous_const.sub continuous_id).continuousOn
  have hint_u : IntervalIntegrable (fun s => Work.Spaces.pz Ψ s θ) volume z (z + 1) :=
    hcont_u.intervalIntegrable
  have hint_u2 : IntervalIntegrable (fun s => Work.Spaces.pzIter 2 Ψ s θ) volume z (z + 1) :=
    hcont_u2.intervalIntegrable
  have hint_v' : IntervalIntegrable (fun _ : ℝ => (-1 : ℝ)) volume z (z + 1) :=
    continuous_const.continuousOn.intervalIntegrable
  -- the fundamental theorem for `Ψ`
  have hFTC : (∫ s in z..(z + 1), Work.Spaces.pz Ψ s θ) = Ψ (z + 1) θ - Ψ z θ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs => hS.hasDerivAt_slice hθ (hmem s hs)) hint_u
  -- the integration by parts
  have hibp := intervalIntegral.integral_deriv_mul_eq_sub (u := fun s => Work.Spaces.pz Ψ s θ)
    (v := fun s : ℝ => (z + 1) - s) (u' := fun s => Work.Spaces.pzIter 2 Ψ s θ)
    (v' := fun _ => (-1 : ℝ)) hderiv_u hderiv_v hint_u2 hint_v'
  have hsplit : (∫ s in z..(z + 1),
        (Work.Spaces.pzIter 2 Ψ s θ * ((z + 1) - s) + Work.Spaces.pz Ψ s θ * (-1)))
      = (∫ s in z..(z + 1), Work.Spaces.pzIter 2 Ψ s θ * ((z + 1) - s))
        + (∫ s in z..(z + 1), Work.Spaces.pz Ψ s θ * (-1)) :=
    intervalIntegral.integral_add (hint_u2.mul_continuousOn hcont_v)
      (hint_u.mul_continuousOn continuous_const.continuousOn)
  have hneg : (∫ s in z..(z + 1), Work.Spaces.pz Ψ s θ * (-1))
      = -(∫ s in z..(z + 1), Work.Spaces.pz Ψ s θ) := by
    rw [intervalIntegral.integral_mul_const]
    ring
  rw [hsplit, hneg, hFTC] at hibp
  have hcomm : (∫ s in z..(z + 1), (z + 1 - s) * Work.Spaces.pzIter 2 Ψ s θ)
      = ∫ s in z..(z + 1), Work.Spaces.pzIter 2 Ψ s θ * ((z + 1) - s) := by
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    ring
  rw [hcomm]
  linarith [hibp]

/-! ## The main statement -/

theorem honestGSlice (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.Honest.Hon α F Ψ) :
    ∀ z, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pz Ψ z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
      Work.Spaces.Iθ := by
  intro z hz
  simp only [sig_eq_sEta]
  have hS := hon_smoothOpen h
  have hz1 : 0 < z + 1 := by linarith
  -- ### the level term is integrable
  obtain ⟨M1, hM1, hb1⟩ := hon_psi_slice_bdd h hz
  obtain ⟨M2, hM2, hb2⟩ := hon_psi_slice_bdd h hz1
  have hlevel : MeasureTheory.IntegrableOn
      (fun θ => (Ψ (z + 1) θ - Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
    have hsig_int : MeasureTheory.IntegrableOn
        (fun θ => Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := sEta_integrableOn
    have haesm : MeasureTheory.AEStronglyMeasurable
        (fun θ => (Ψ (z + 1) θ - Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        (volume.restrict Work.Spaces.Iθ) :=
      (((hS.aesm_slice_pzIter 0 hz1).sub (hS.aesm_slice_pzIter 0 hz)).pow 2).mul aesm_sig_Iθ
    refine MeasureTheory.Integrable.mono' (hsig_int.const_mul ((M1 + M2) ^ 2)) haesm ?_
    rw [restrict_Iθ_eq_Ioo]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have h1 : |Ψ (z + 1) θ - Ψ z θ| ≤ M1 + M2 := by
      have h2 := abs_sub_le (Ψ (z + 1) θ) (0 : ℝ) (Ψ z θ)
      have h3 : |Ψ (z + 1) θ| ≤ M2 := hb2 θ hθ
      have h4 : |Ψ z θ| ≤ M1 := hb1 θ hθ
      simp only [sub_zero, zero_sub, abs_neg] at h2
      linarith
    have hsig0 : 0 ≤ Work.FTS.EllipticEst.sEta θ :=
      sEta_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have h1' : (Ψ (z + 1) θ - Ψ z θ) ^ 2 ≤ (M1 + M2) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hsig0)]
    exact mul_le_mul_of_nonneg_right h1' hsig0
  -- ### the box term is integrable
  have hbox := hon_box_abs_sq h hz
  -- ### the pointwise domination on the open interval
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.Spaces.pz Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        ≤ 2 * ((Ψ (z + 1) θ - Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + 2 * ((∫ s in z..(z + 1), |Work.Spaces.pzIter 2 Ψ s θ|) ^ 2
              * Work.FTS.EllipticEst.sEta θ) := by
    intro θ hθ
    have hid := hon_pz_taylor h hz hθ
    have hzle : z ≤ z + 1 := by linarith
    have hcontF2 : ContinuousOn (fun s => Work.Spaces.pzIter 2 Ψ s θ) (Set.Icc z (z + 1)) :=
      ((hS.pzIter 2).curry_z hθ).continuousOn.mono
        (fun s hs => lt_of_lt_of_le hz hs.1)
    have hcontγ : ContinuousOn (fun s : ℝ => (z + 1 - s) * Work.Spaces.pzIter 2 Ψ s θ)
        (Set.Icc z (z + 1)) :=
      (continuous_const.sub continuous_id).continuousOn.mul hcontF2
    have hintF2 : IntervalIntegrable (fun s => Work.Spaces.pzIter 2 Ψ s θ) volume z (z + 1) := by
      have hc : ContinuousOn (fun s => Work.Spaces.pzIter 2 Ψ s θ) (Set.uIcc z (z + 1)) := by
        rw [Set.uIcc_of_le hzle]; exact hcontF2
      exact hc.intervalIntegrable
    have hintγ : IntervalIntegrable (fun s : ℝ => (z + 1 - s) * Work.Spaces.pzIter 2 Ψ s θ)
        volume z (z + 1) := by
      have hc : ContinuousOn (fun s : ℝ => (z + 1 - s) * Work.Spaces.pzIter 2 Ψ s θ)
          (Set.uIcc z (z + 1)) := by
        rw [Set.uIcc_of_le hzle]; exact hcontγ
      exact hc.intervalIntegrable
    have hbnd : |∫ s in z..(z + 1), (z + 1 - s) * Work.Spaces.pzIter 2 Ψ s θ|
        ≤ ∫ s in z..(z + 1), |Work.Spaces.pzIter 2 Ψ s θ| := by
      refine le_trans (intervalIntegral.abs_integral_le_integral_abs hzle) ?_
      refine intervalIntegral.integral_mono_on hzle hintγ.abs hintF2.abs (fun s hs => ?_)
      rw [abs_mul, abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ z + 1 - s)]
      exact mul_le_of_le_one_left (abs_nonneg _) (by linarith [hs.1])
    have h1 : |Work.Spaces.pz Ψ z θ| ≤ |Ψ (z + 1) θ - Ψ z θ|
        + ∫ s in z..(z + 1), |Work.Spaces.pzIter 2 Ψ s θ| := by
      have h2 : |Work.Spaces.pz Ψ z θ|
          ≤ |Ψ (z + 1) θ - Ψ z θ|
            + |∫ s in z..(z + 1), (z + 1 - s) * Work.Spaces.pzIter 2 Ψ s θ| := by
        rw [hid, sub_eq_add_neg]
        refine le_trans (abs_add_le _ _) ?_
        rw [abs_neg]
      linarith
    have hsig0 : 0 ≤ Work.FTS.EllipticEst.sEta θ :=
      sEta_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have h2 : (Work.Spaces.pz Ψ z θ) ^ 2
        ≤ 2 * (Ψ (z + 1) θ - Ψ z θ) ^ 2
          + 2 * (∫ s in z..(z + 1), |Work.Spaces.pzIter 2 Ψ s θ|) ^ 2 := by
      have h3 : |Work.Spaces.pz Ψ z θ| ^ 2
          ≤ (|Ψ (z + 1) θ - Ψ z θ|
            + (∫ s in z..(z + 1), |Work.Spaces.pzIter 2 Ψ s θ|)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
      have h4 : (|Ψ (z + 1) θ - Ψ z θ|
            + (∫ s in z..(z + 1), |Work.Spaces.pzIter 2 Ψ s θ|)) ^ 2
          ≤ 2 * |Ψ (z + 1) θ - Ψ z θ| ^ 2
            + 2 * (∫ s in z..(z + 1), |Work.Spaces.pzIter 2 Ψ s θ|) ^ 2 := by
        nlinarith [sq_nonneg (|Ψ (z + 1) θ - Ψ z θ|
          - (∫ s in z..(z + 1), |Work.Spaces.pzIter 2 Ψ s θ|))]
      calc (Work.Spaces.pz Ψ z θ) ^ 2 = |Work.Spaces.pz Ψ z θ| ^ 2 := by rw [sq_abs]
        _ ≤ _ := h3
        _ ≤ 2 * |Ψ (z + 1) θ - Ψ z θ| ^ 2
            + 2 * (∫ s in z..(z + 1), |Work.Spaces.pzIter 2 Ψ s θ|) ^ 2 := h4
        _ = 2 * (Ψ (z + 1) θ - Ψ z θ) ^ 2
            + 2 * (∫ s in z..(z + 1), |Work.Spaces.pzIter 2 Ψ s θ|) ^ 2 := by
            rw [sq_abs]
    calc (Work.Spaces.pz Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        ≤ (2 * (Ψ (z + 1) θ - Ψ z θ) ^ 2
            + 2 * (∫ s in z..(z + 1), |Work.Spaces.pzIter 2 Ψ s θ|) ^ 2)
          * Work.FTS.EllipticEst.sEta θ :=
          mul_le_mul_of_nonneg_right h2 hsig0
      _ = 2 * ((Ψ (z + 1) θ - Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + 2 * ((∫ s in z..(z + 1), |Work.Spaces.pzIter 2 Ψ s θ|) ^ 2
              * Work.FTS.EllipticEst.sEta θ) := by ring
  -- ### assembly
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ => (Work.Spaces.pz Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (volume.restrict Work.Spaces.Iθ) :=
    ((hS.aesm_slice_pzIter 1 hz).pow 2).mul aesm_sig_Iθ
  refine MeasureTheory.Integrable.mono'
    ((hlevel.const_mul 2).add (hbox.const_mul 2)) haesm ?_
  rw [restrict_Iθ_eq_Ioo]
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
  have hsig0 : 0 ≤ Work.FTS.EllipticEst.sEta θ :=
    sEta_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hpt' := hpt θ hθ
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hsig0)]
  exact hpt'

end Work.FTS.EllipticEst.Honest
