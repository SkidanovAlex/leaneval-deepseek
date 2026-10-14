import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.interpol_trunc_defs
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS_EllLimOK.EGap.integrableOn_PhiD
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.Cutoff
import Submission.Work.Stability.DynGEquation
-- ===== merged: Submission.Work.FTS.EllipticEst.AeColl.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeColl/Defs` — the vocabulary of the cut-off chain for `AeColl.i1PaperWeakMixed`

The route (see `NOTES_i1PaperWeakMixed_ROUTE.md`) uses the two proved 2-D cut-off identities
`I1Wk.truncZIbp2` (radial) and `I1Wk.truncThetaIbpSep` (angular), whose combination gives, for the
radial cut-off `χ_n = Work.FTS.EllipticEst.cut n` and the angular bump `ψ_δ`,

`κ·P ≤ D + Tr − 2η·A + (1/2)|W|`,

with `P, D, Tr, A` as below and `W = ∫∫ χ_n w² σ ψ_δ'' U²` controlled by the collar `Col` through
the Hardy-type rate of the slices of `U = z∂_zu` (`AeColl.sliceWBound`,
`AeColl.aeGradTraceRateUnw`).

These definitions live in their own module so that the two limit lemmas
(`AeColl.pairChain`, `AeColl.limitBound`) and the final assembly in `AeColl.i1PaperWeakMixed`
can all import them without a cycle.
-/

namespace Work.FTS.EllipticEst.AeColl

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

/-- The angular weight `σ θ = sin(2θ)^{-η}`. -/
def sigθ (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- The squared radial weight `w z²`. -/
def wt (z : ℝ) : ℝ := (Work.Spaces.w z) ^ 2

/-- `U = z ∂_z u`. -/
def Uz (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z * Work.Spaces.pz u z θ

/-- `V = z ∂_z ∂_θ u`. -/
def Vz (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z * Work.Spaces.pz (Work.Spaces.pth u) z θ

/-- `A = z² ∂_z² u`. -/
def Az (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ

/-- `cw z = 2(z-1)/(1+z) = (w²z²)'/(z·w²)`. -/
def cwf (z : ℝ) : ℝ := 2 * (z - 1) / (1 + z)

/-- The angular bump `ψ_δ` of the cut-off chain (equal to `1` on `[δ/2, π/2−δ/2]`). -/
def psiD (δ θ : ℝ) : ℝ :=
  Real.smoothTransition ((θ - δ / 4) / (δ / 4))
    * Real.smoothTransition (((Real.pi / 2 - δ / 4) - θ) / (δ / 4))

/-- The `(χ_n, ψ_δ)`-truncated angular energy of the mixed slot `V`. -/
def Ptr (u : ℝ → ℝ → ℝ) (n : ℕ) (δ : ℝ) : ℝ :=
  ∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut n z * wt z
    * ∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ * psiD δ θ * (Vz u z θ) ^ 2

/-- The `(χ_n, ψ_δ)`-truncated angular energy of `U`. -/
def Atr (u : ℝ → ℝ → ℝ) (n : ℕ) (δ : ℝ) : ℝ :=
  ∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut n z * wt z
    * ∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ * psiD δ θ * (Uz u z θ) ^ 2

/-- The `(χ_n, ψ_δ)`-truncated pairing of `A = z²∂_z²u` with `B = ∂_θ²u`. -/
def Dtr (u : ℝ → ℝ → ℝ) (n : ℕ) (δ : ℝ) : ℝ :=
  ∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.cut n z * wt z
    * sigθ θ * psiD δ θ * (Az u z θ) * (Work.Spaces.pthIter 2 u z θ)

/-- The `(χ_n, ψ_δ)`-truncated angular transfer term. -/
def Trtr (u : ℝ → ℝ → ℝ) (n : ℕ) (δ : ℝ) : ℝ :=
  ∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2),
    (deriv (fun z' => Work.FTS.EllipticEst.cut n z' * wt z' * z' ^ 2) z / z)
      * sigθ θ * psiD δ θ * (Uz u z θ) * (Work.Spaces.pthIter 2 u z θ)

/-- The angular collar energy of `V`, cut off radially by `χ_n`. -/
def Col (u : ℝ → ℝ → ℝ) (n : ℕ) (δ : ℝ) : ℝ :=
  (∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut n z * wt z
      * (∫ θ in Set.Ioo 0 δ, sigθ θ * (Vz u z θ) ^ 2))
    + ∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut n z * wt z
      * (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2), sigθ θ * (Vz u z θ) ^ 2)

/-- The radial-cutoff truncated mixed energy (the `δ ↓ 0` limit of `Ptr`). -/
def Pcut (u : ℝ → ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut n z * wt z
    * ∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ * (Vz u z θ) ^ 2

/-- The radial-cutoff truncated energy of `U` (the `δ ↓ 0` limit of `Atr`). -/
def Acut (u : ℝ → ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut n z * wt z
    * ∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ * (Uz u z θ) ^ 2

/-- The radial-cutoff truncated `⟨A,B⟩` (the `δ ↓ 0` limit of `Dtr`). -/
def Dcut (u : ℝ → ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.cut n z * wt z
    * sigθ θ * (Az u z θ) * (Work.Spaces.pthIter 2 u z θ)

/-- The radial-cutoff truncated transfer term (the `δ ↓ 0` limit of `Trtr`). -/
def Trcut (u : ℝ → ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2),
    (deriv (fun z' => Work.FTS.EllipticEst.cut n z' * wt z' * z' ^ 2) z / z)
      * sigθ θ * (Uz u z θ) * (Work.Spaces.pthIter 2 u z θ)

/-- The full (untruncated) weighted angular energy of the mixed slot `V`. -/
def Vfull (u : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Set.Ioi 0, wt z
    * ∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ * (Vz u z θ) ^ 2


end

end Work.FTS.EllipticEst.AeColl
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngSecond.I1_defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Topology Real ContDiff

namespace Work.FTS.EllipticEst.AngSecond

/-! ## Integrability on the half-line of a compactly supported function -/

/-- A function continuous on `[a,b]` (`0 < a ≤ b`) and vanishing outside `[a,b]` is integrable
on `(0,∞)`; its support is the compact subset `[a,b] ⊆ (0,∞)`. -/
private theorem integrableOn_Ioi_of_Icc_support {f : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hcont : ContinuousOn f (Set.Icc a b))
    (hzero : ∀ z, z ∉ Set.Icc a b → f z = 0) :
    MeasureTheory.IntegrableOn f (Set.Ioi 0) := by
  have hInd : MeasureTheory.Integrable ((Set.Icc a b).indicator f) volume :=
    (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
      (hcont.integrableOn_compact isCompact_Icc)
  have hfun : f = (Set.Icc a b).indicator f := by
    funext z
    by_cases hz : z ∈ Set.Icc a b
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, hzero z hz]
  rw [hfun]
  refine ⟨hInd.aestronglyMeasurable.mono_measure Measure.restrict_le_self, ?_⟩
  calc ∫⁻ z, ‖(Set.Icc a b).indicator f z‖₊ ∂(volume.restrict (Set.Ioi 0))
      ≤ ∫⁻ z, ‖(Set.Icc a b).indicator f z‖₊ ∂(volume : MeasureTheory.Measure ℝ) :=
        lintegral_mono' Measure.restrict_le_self le_rfl
    _ < ⊤ := hInd.hasFiniteIntegral

/-! ## The vocabulary of the `I₁` computation -/

/-- `G(Ψ) = z · ∂_zΨ`: the first-order radial term. -/
noncomputable def G (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z * Work.Spaces.pz Ψ z θ

/-- `Φ(Ψ) = ∂_θθΨ`: the angular term paired with `I₁`. -/
noncomputable def Phi (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 Ψ

/-- `H(Ψ) = z · ∂_z(∂_θθΨ) = ∂_θθ(z ∂_zΨ)`: the angular derivative of `G`, which the angular
integration by parts turns into `(∂_θ G)²`. -/
noncomputable def H (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ

/-- `cw z = 2(z-1)/(1+z) = 2 - 4/(1+z)`: the weight of the drift term produced by the radial
integration by parts (`z (w²)'/w² = -4/(1+z)`). -/
noncomputable def cw (z : ℝ) : ℝ := 2 * (z - 1) / (1 + z)

/-! ## Part 0: the derivative of the weight `w²` -/

theorem hasDerivAt_w2 {z : ℝ} (hz : 0 < z) :
    HasDerivAt w2 (2 * Work.Spaces.w z * Work.FTS.EllipticEst.zDw z) z := by
  have h := (Work.FTS.EllipticEst.hasDerivAt_w hz).pow 2
  have h2 : (2 : ℝ) * Work.Spaces.w z ^ (2 - 1) * Work.FTS.EllipticEst.zDw z
      = 2 * Work.Spaces.w z * Work.FTS.EllipticEst.zDw z := by norm_num
  exact h.congr_deriv h2

theorem deriv_w2_eq {z : ℝ} (hz : 0 < z) :
    deriv w2 z = 2 * Work.Spaces.w z * Work.FTS.EllipticEst.zDw z :=
  (hasDerivAt_w2 hz).deriv

theorem z_mul_deriv_w2 {z : ℝ} (hz : 0 < z) :
    z * deriv w2 z = -4 * w2 z / (1 + z) := by
  rw [deriv_w2_eq hz]
  have hz0 : z ≠ 0 := ne_of_gt hz
  have h1 : (1 : ℝ) + z ≠ 0 := by linarith
  simp only [Work.FTS.EllipticEst.zDw, w2, Work.Spaces.w]
  field_simp
  ring

theorem deriv_w2_eq' {z : ℝ} (hz : 0 < z) :
    deriv w2 z = -4 * w2 z / ((1 + z) * z) := by
  have hw := z_mul_deriv_w2 hz
  have hz0 : z ≠ 0 := ne_of_gt hz
  have h1 : (1 : ℝ) + z ≠ 0 := by linarith
  field_simp at hw ⊢
  linarith [hw]

/-! ## Part 1: the pointwise expansion of the `z`-derivative of `z² φ χ w²` -/



/-! ## Part 2: the per-`θ` integration by parts -/

/-- The explicit `z`-derivative of `z' ↦ z'² ∂_θθΨ(z',θ) · χ(z') · w²(z')` (raw form). -/
noncomputable def Dv (n : ℕ) (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  2 * z * Work.Spaces.pthIter 2 Ψ z θ * cut n z * w2 z
    + z ^ 2 * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ * cut n z * w2 z
    + z ^ 2 * Work.Spaces.pthIter 2 Ψ z θ * deriv (cut n) z * w2 z
    + z ^ 2 * Work.Spaces.pthIter 2 Ψ z θ * cut n z * deriv w2 z


/-- `z * (cut n)' z = 0` far away from the transition regions. -/
theorem deriv_cut_eq_zero_of_lt (n : ℕ) {z : ℝ} (hz : z < 1 / (n + 1 : ℝ)) :
    deriv (cut n) z = 0 := by
  have hEq : (fun y : ℝ => cut n y) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Iio.mem_nhds hz] with y hy
    exact Work.FTS.EllipticEst.cut_apply_zero_of_le n hy.le
  have := hEq.deriv_eq
  simpa using this

theorem deriv_cut_eq_zero_of_gt (n : ℕ) {z : ℝ} (hz : 3 * (n + 1 : ℝ) < z) :
    deriv (cut n) z = 0 := by
  have hEq : (fun y : ℝ => cut n y) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
    exact Work.FTS.EllipticEst.cut_apply_zero_of_ge n hy.le
  have := hEq.deriv_eq
  simpa using this

theorem Dv_eq_zero_of_notMem (n : ℕ) (Ψ : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hz : z ∉ Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ))) : Dv n Ψ z θ = 0 := by
  have hn : (0 : ℝ) < (n + 1 : ℝ) := by positivity
  have hhalf : 1 / (2 * (n + 1 : ℝ)) ≤ 1 / (n + 1 : ℝ) :=
    one_div_le_one_div_of_le hn (by linarith)
  simp only [Set.mem_Icc, not_and_or, not_le] at hz
  rcases hz with hzlt | hzgt
  · have h1 : z ≤ 1 / (n + 1 : ℝ) := by linarith
    have hzlt' : z < 1 / (n + 1 : ℝ) := by linarith
    have hχ : cut n z = 0 := Work.FTS.EllipticEst.cut_apply_zero_of_le n h1
    have hχ' : deriv (cut n) z = 0 := deriv_cut_eq_zero_of_lt n hzlt'
    simp [Dv, hχ, hχ']
  · have h1 : 3 * (n + 1 : ℝ) ≤ z := by linarith
    have hχ : cut n z = 0 := Work.FTS.EllipticEst.cut_apply_zero_of_ge n h1
    have hχ' : deriv (cut n) z = 0 := deriv_cut_eq_zero_of_gt n (by linarith)
    simp [Dv, hχ, hχ']

section Continuity


theorem continuous_deriv_cut (n : ℕ) : Continuous (deriv (Work.FTS.EllipticEst.cut n)) := by
  have hcut : ContDiff ℝ ∞ (Work.FTS.EllipticEst.cut n) := Work.FTS.EllipticEst.cut_contDiff n
  exact ((contDiff_infty_iff_deriv.mp hcut).2).continuous

end Continuity

section Helpers

theorem continuousOn_w' {a b : ℝ} (ha : 0 < a) :
    ContinuousOn Work.Spaces.w (Set.Icc a b) := by
  unfold Work.Spaces.w
  have hnum : ContinuousOn (fun z : ℝ => (1 + z) ^ 2) (Set.Icc a b) :=
    ((continuous_const.add continuous_id).pow 2).continuousOn
  have hden : ContinuousOn (fun z : ℝ => z ^ 2) (Set.Icc a b) :=
    (continuous_id.pow 2).continuousOn
  exact hnum.div hden (fun z hz => by
    have hz0 : (0 : ℝ) < z := lt_of_lt_of_le ha hz.1
    exact pow_ne_zero 2 (ne_of_gt hz0))


theorem continuousOn_w2' {a b : ℝ} (ha : 0 < a) : ContinuousOn w2 (Set.Icc a b) := by
  unfold w2
  exact (continuousOn_w' (a := a) (b := b) ha).pow 2

theorem continuousOn_deriv_w2' {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun z => deriv w2 z) (Set.Icc a b) := by
  have h4 : ContinuousOn (fun _ : ℝ => (-4 : ℝ)) (Set.Icc a b) := continuousOn_const
  have hden : ContinuousOn (fun z : ℝ => (1 + z) * z) (Set.Icc a b) :=
    (((continuous_const.add continuous_id).mul continuous_id)).continuousOn
  have h : ContinuousOn (fun z : ℝ => -4 * w2 z / ((1 + z) * z)) (Set.Icc a b) :=
    h4.mul (continuousOn_w2' (a := a) (b := b) ha) |>.div hden (fun z hz => by
      have hz0 : (0 : ℝ) < z := lt_of_lt_of_le ha hz.1
      have h1 : (1 : ℝ) + z ≠ 0 := by linarith
      exact mul_ne_zero h1 (ne_of_gt hz0))
  have heq : Set.EqOn (fun z => deriv w2 z) (fun z : ℝ => -4 * w2 z / ((1 + z) * z))
      (Set.Icc a b) := fun z hz => deriv_w2_eq' (lt_of_lt_of_le ha hz.1)
  exact (continuousOn_congr heq).mpr h




end Helpers

section IBP



end IBP

section Fubini

/-- The pointwise form of the RHS integrand of the cut-off identity. -/
noncomputable def nice (n : ℕ) (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  cut n z * w2 z
      * (2 * G Ψ z θ * Phi Ψ z θ + G Ψ z θ * H Ψ z θ - 4 * G Ψ z θ * Phi Ψ z θ / (1 + z))
    + w2 z * (G Ψ z θ * Phi Ψ z θ) * (z * deriv (cut n) z)


end Fubini

section Joint




end Joint



section SmoothNbhdAux

/-- The first coordinate is smooth on a neighbourhood of the closed quadrant. -/
theorem smoothNbhd_fst : Work.Spaces.SmoothNbhd (fun z _ : ℝ => z) :=
  contDiff_fst.contDiffOn

/-- `SmoothNbhd` is closed under pointwise products. -/
theorem smoothNbhd_mul {f g : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f)
    (hg : Work.Spaces.SmoothNbhd g) :
    Work.Spaces.SmoothNbhd (fun z θ => f z θ * g z θ) := by
  have hfun : Function.uncurry (fun z θ => f z θ * g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p * Function.uncurry g p := rfl
  show ContDiffOn ℝ ⊤ (Function.uncurry (fun z θ => f z θ * g z θ)) Work.Spaces.nbhU
  rw [hfun]
  exact hf.mul hg






end SmoothNbhdAux

end Work.FTS.EllipticEst.AngSecond
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngSecond.cut_deriv_uniform =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngSecond

open scoped Topology
open Filter Set

/-!
## Auxiliary facts about `Real.smoothTransition` and its derivative

`ψ = Real.smoothTransition` is `C^∞`, vanishes on `(-∞,0]` and equals `1` on `[1,∞)`.  Hence
`deriv ψ` vanishes off `[0,1]`, so for every `c : ℝ` the function `x ↦ (x + c) · ψ'(x)` is
continuous with support in `[0,1]`, i.e. bounded on `ℝ`.
-/

private theorem deriv_smoothTransition_eq_zero_of_lt_zero {x : ℝ} (hx : x < 0) :
    deriv Real.smoothTransition x = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
    exact Real.smoothTransition.zero_of_nonpos hy.le
  rw [h.deriv_eq, deriv_const]

private theorem deriv_smoothTransition_eq_zero_of_one_lt {x : ℝ} (hx : 1 < x) :
    deriv Real.smoothTransition x = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact Real.smoothTransition.one_of_one_le hy.le
  rw [h.deriv_eq, deriv_const]

private theorem continuous_deriv_smoothTransition : Continuous (deriv Real.smoothTransition) :=
  (Real.smoothTransition.contDiff (n := 2)).continuous_deriv (by norm_num)

private theorem abs_smoothTransition_le_one (x : ℝ) : |Real.smoothTransition x| ≤ 1 := by
  rw [abs_of_nonneg (Real.smoothTransition.nonneg x)]
  exact Real.smoothTransition.le_one x

private theorem abs_one_sub_smoothTransition_le_one (x : ℝ) :
    |1 - Real.smoothTransition x| ≤ 1 := by
  rw [abs_of_nonneg (by linarith [Real.smoothTransition.le_one x])]
  linarith [Real.smoothTransition.nonneg x]

/-- `x ↦ (x + c) · (smoothTransition)' x` is bounded, being continuous with support in `[0,1]`. -/
private theorem exists_bound_shift_mul_deriv_smoothTransition (c : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |(x + c) * deriv Real.smoothTransition x| ≤ C := by
  have hcont : Continuous (fun x : ℝ => (x + c) * deriv Real.smoothTransition x) :=
    (continuous_id.add continuous_const).mul continuous_deriv_smoothTransition
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (0 : ℝ) 1) hcont.continuousOn
  have hC0 : 0 ≤ C := by
    have h := hC 0 (by norm_num)
    rw [Real.norm_eq_abs] at h
    exact le_trans (abs_nonneg _) h
  refine ⟨C, hC0, fun x => ?_⟩
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
  · have h := hC x hx
    rwa [Real.norm_eq_abs] at h
  · simp only [Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · rw [deriv_smoothTransition_eq_zero_of_lt_zero hx, mul_zero, abs_zero]; exact hC0
    · rw [deriv_smoothTransition_eq_zero_of_one_lt hx, mul_zero, abs_zero]; exact hC0

/-!
## The product rule for `cut n`, in rescaled form

With `t = (n+1)z - 1` and `s = z/(n+1) - 2` one has `(n+1)z = t + 1` and `z/(n+1) = s + 2`, so
`z (cut n)'(z)` rewrites as a difference of two terms of the shape `(t+1)ψ'(t)` and `(s+2)ψ'(s)`.
-/

/-- Product rule for `cut n`: `cut n z = ψ((n+1)z - 1)·(1 - ψ(z/(n+1) - 2))`, so the chain
rule and the product rule give
`(cut n)'(z) = (n+1)ψ'((n+1)z-1)·(1-ψ(z/(n+1)-2)) - ψ((n+1)z-1)·ψ'(z/(n+1)-2)/(n+1)`. -/
private theorem hasDerivAt_cut_aux (n : ℕ) (z : ℝ) :
    HasDerivAt (cut n)
      (((n + 1 : ℝ) * deriv Real.smoothTransition ((n + 1 : ℝ) * z - 1))
          * (1 - Real.smoothTransition (z / (n + 1 : ℝ) - 2))
        - Real.smoothTransition ((n + 1 : ℝ) * z - 1)
          * (deriv Real.smoothTransition (z / (n + 1 : ℝ) - 2) * (1 / (n + 1 : ℝ)))) z := by
  have hψ : ∀ u : ℝ, HasDerivAt Real.smoothTransition (deriv Real.smoothTransition u) u := fun u =>
    ((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp)).differentiableAt.hasDerivAt
  have hg1 : HasDerivAt (fun y : ℝ => (n + 1 : ℝ) * y - 1) ((n + 1 : ℝ)) z := by
    simpa using ((hasDerivAt_id z).const_mul ((n + 1 : ℝ))).sub_const 1
  have h1 : HasDerivAt (Real.smoothTransition ∘ fun y : ℝ => (n + 1 : ℝ) * y - 1)
      (deriv Real.smoothTransition ((n + 1 : ℝ) * z - 1) * (n + 1 : ℝ)) z :=
    (hψ ((n + 1 : ℝ) * z - 1)).comp z hg1
  have hg2 : HasDerivAt (fun y : ℝ => y / (n + 1 : ℝ) - 2) (1 / (n + 1 : ℝ)) z := by
    simpa using ((hasDerivAt_id z).div_const ((n + 1 : ℝ))).sub_const 2
  have h2 : HasDerivAt (fun y : ℝ => 1 - Real.smoothTransition (y / (n + 1 : ℝ) - 2))
      (-(deriv Real.smoothTransition (z / (n + 1 : ℝ) - 2) * (1 / (n + 1 : ℝ)))) z := by
    have h := (hasDerivAt_const (x := z) (c := (1 : ℝ))).sub
      ((hψ (z / (n + 1 : ℝ) - 2)).comp z hg2)
    convert h using 1
    · ext y; simp [Pi.sub_apply, Function.comp_apply]
    · ring
  have hfun : cut n = (Real.smoothTransition ∘ fun y : ℝ => (n + 1 : ℝ) * y - 1)
      * (fun y : ℝ => 1 - Real.smoothTransition (y / (n + 1 : ℝ) - 2)) := by
    funext y
    simp [cut, Function.comp_apply, Pi.mul_apply]
  rw [hfun]
  convert h1.mul h2 using 1
  simp only [Function.comp_apply]
  ring

private theorem deriv_cut_mul_self (n : ℕ) (z : ℝ) :
    z * deriv (cut n) z
      = ((((n + 1 : ℝ) * z - 1) + 1)
            * deriv Real.smoothTransition ((n + 1 : ℝ) * z - 1))
          * (1 - Real.smoothTransition (z / (n + 1 : ℝ) - 2))
        - Real.smoothTransition ((n + 1 : ℝ) * z - 1)
          * (((z / (n + 1 : ℝ) - 2) + 2)
              * deriv Real.smoothTransition (z / (n + 1 : ℝ) - 2)) := by
  rw [(hasDerivAt_cut_aux n z).deriv]
  ring

/-- The uniform bound: `|z · (cut n)'(z)| ≤ C₁ + C₂` where `C₁, C₂` bound `(t+1)ψ'(t)` resp.
`(t+2)ψ'(t)`. -/
private theorem abs_z_mul_deriv_cut_le (n : ℕ) (z : ℝ) {C1 C2 : ℝ} (hC1 : 0 ≤ C1)
    (h1 : ∀ x : ℝ, |(x + 1) * deriv Real.smoothTransition x| ≤ C1)
    (hC2 : 0 ≤ C2) (h2 : ∀ x : ℝ, |(x + 2) * deriv Real.smoothTransition x| ≤ C2) :
    |z * deriv (cut n) z| ≤ C1 + C2 := by
  rw [deriv_cut_mul_self]
  have hA : |((((n + 1 : ℝ) * z - 1) + 1)
        * deriv Real.smoothTransition ((n + 1 : ℝ) * z - 1))
      * (1 - Real.smoothTransition (z / (n + 1 : ℝ) - 2))| ≤ C1 := by
    have h1' : |(((n + 1 : ℝ) * z - 1) + 1)
        * deriv Real.smoothTransition ((n + 1 : ℝ) * z - 1)| ≤ C1 := h1 _
    have h2' : |1 - Real.smoothTransition (z / (n + 1 : ℝ) - 2)| ≤ 1 :=
      abs_one_sub_smoothTransition_le_one _
    calc |((((n + 1 : ℝ) * z - 1) + 1)
          * deriv Real.smoothTransition ((n + 1 : ℝ) * z - 1))
        * (1 - Real.smoothTransition (z / (n + 1 : ℝ) - 2))|
        = |(((n + 1 : ℝ) * z - 1) + 1)
            * deriv Real.smoothTransition ((n + 1 : ℝ) * z - 1)|
          * |1 - Real.smoothTransition (z / (n + 1 : ℝ) - 2)| := abs_mul _ _
      _ ≤ C1 * 1 := mul_le_mul h1' h2' (abs_nonneg _) hC1
      _ = C1 := mul_one C1
  have hB : |Real.smoothTransition ((n + 1 : ℝ) * z - 1)
      * (((z / (n + 1 : ℝ) - 2) + 2)
          * deriv Real.smoothTransition (z / (n + 1 : ℝ) - 2))| ≤ C2 := by
    have h1' : |Real.smoothTransition ((n + 1 : ℝ) * z - 1)| ≤ 1 :=
      abs_smoothTransition_le_one _
    have h2' : |(((z / (n + 1 : ℝ) - 2) + 2)
        * deriv Real.smoothTransition (z / (n + 1 : ℝ) - 2))| ≤ C2 := h2 _
    calc |Real.smoothTransition ((n + 1 : ℝ) * z - 1)
          * (((z / (n + 1 : ℝ) - 2) + 2)
              * deriv Real.smoothTransition (z / (n + 1 : ℝ) - 2))|
        = |Real.smoothTransition ((n + 1 : ℝ) * z - 1)|
          * |(((z / (n + 1 : ℝ) - 2) + 2)
              * deriv Real.smoothTransition (z / (n + 1 : ℝ) - 2))| := abs_mul _ _
      _ ≤ 1 * C2 := mul_le_mul h1' h2' (abs_nonneg _) zero_le_one
      _ = C2 := one_mul C2
  calc |((((n + 1 : ℝ) * z - 1) + 1)
          * deriv Real.smoothTransition ((n + 1 : ℝ) * z - 1))
        * (1 - Real.smoothTransition (z / (n + 1 : ℝ) - 2))
      - Real.smoothTransition ((n + 1 : ℝ) * z - 1)
        * (((z / (n + 1 : ℝ) - 2) + 2)
            * deriv Real.smoothTransition (z / (n + 1 : ℝ) - 2))|
      ≤ |((((n + 1 : ℝ) * z - 1) + 1)
            * deriv Real.smoothTransition ((n + 1 : ℝ) * z - 1))
          * (1 - Real.smoothTransition (z / (n + 1 : ℝ) - 2))|
        + |Real.smoothTransition ((n + 1 : ℝ) * z - 1)
          * (((z / (n + 1 : ℝ) - 2) + 2)
              * deriv Real.smoothTransition (z / (n + 1 : ℝ) - 2))| := by
        simpa using abs_sub_le
          (((((n + 1 : ℝ) * z - 1) + 1)
              * deriv Real.smoothTransition ((n + 1 : ℝ) * z - 1))
            * (1 - Real.smoothTransition (z / (n + 1 : ℝ) - 2)))
          (0 : ℝ)
          (Real.smoothTransition ((n + 1 : ℝ) * z - 1)
            * (((z / (n + 1 : ℝ) - 2) + 2)
                * deriv Real.smoothTransition (z / (n + 1 : ℝ) - 2)))
    _ ≤ C1 + C2 := add_le_add hA hB

/-!
## Eventual constancy of `cut n` near a fixed non-zero point
-/

private theorem eventually_two_div_add_one_lt {z : ℝ} (hz : 0 < z) :
    ∀ᶠ n : ℕ in atTop, 2 / ((n : ℝ) + 1) < z := by
  have h : Tendsto (fun n : ℕ => (2 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 : ℝ)
    simpa only [mul_zero, mul_one_div] using ht
  exact (tendsto_order.1 h).2 z hz

private theorem eventually_le_two_mul_add_one (z : ℝ) :
    ∀ᶠ n : ℕ in atTop, z ≤ 2 * ((n : ℝ) + 1) := by
  have hbase : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).atTop_add
      tendsto_const_nhds
  exact (tendsto_atTop.1 (hbase.const_mul_atTop (by norm_num))) z

private theorem cut_eventuallyEq_one_of_pos {z : ℝ} (hz : 0 < z) :
    ∀ᶠ n : ℕ in atTop, cut n =ᶠ[𝓝 z] (fun _ => (1 : ℝ)) := by
  filter_upwards [eventually_two_div_add_one_lt hz,
    eventually_le_two_mul_add_one (z + 1)] with n hn1 hn2
  have hlt1 : 2 / ((n : ℝ) + 1) < z := hn1
  have hlt2 : z < 2 * ((n : ℝ) + 1) := by linarith
  have hε : 0 < min (z - 2 / ((n : ℝ) + 1)) (2 * ((n : ℝ) + 1) - z) / 2 := by
    have hmin : 0 < min (z - 2 / ((n : ℝ) + 1)) (2 * ((n : ℝ) + 1) - z) :=
      lt_min (by linarith) (by linarith)
    linarith
  filter_upwards [Metric.ball_mem_nhds z hε] with y hy
  rw [Metric.mem_ball, Real.dist_eq] at hy
  refine cut_eq_one_of_mem n ?_ ?_
  · have hm : min (z - 2 / ((n : ℝ) + 1)) (2 * ((n : ℝ) + 1) - z)
        ≤ z - 2 / ((n : ℝ) + 1) := min_le_left _ _
    have h1 : z - y ≤ |y - z| := by rw [abs_sub_comm]; exact le_abs_self _
    linarith
  · have hm : min (z - 2 / ((n : ℝ) + 1)) (2 * ((n : ℝ) + 1) - z)
        ≤ 2 * ((n : ℝ) + 1) - z := min_le_right _ _
    have h1 : y - z ≤ |y - z| := le_abs_self _
    linarith

private theorem cut_eventuallyEq_zero_of_neg {z : ℝ} (hz : z < 0) :
    ∀ᶠ n : ℕ in atTop, cut n =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
  filter_upwards with n
  have hε : 0 < -(z / 2) := by linarith
  filter_upwards [Metric.ball_mem_nhds z hε] with y hy
  rw [Metric.mem_ball, Real.dist_eq] at hy
  have h1 : y - z ≤ |y - z| := le_abs_self _
  have hy0 : y < 0 := by linarith
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  exact cut_apply_zero_of_le n (by linarith)

/-- For every fixed `z ≠ 0` the derivatives `(cut n)'(z)` vanish for all large `n`. -/
private theorem deriv_cut_eventually_eq_zero {z : ℝ} (hz : z ≠ 0) :
    ∀ᶠ n : ℕ in atTop, deriv (cut n) z = 0 := by
  rcases lt_or_gt_of_ne hz with h | h
  · filter_upwards [cut_eventuallyEq_zero_of_neg h] with n hn
    rw [hn.deriv_eq, deriv_const]
  · filter_upwards [cut_eventuallyEq_one_of_pos h] with n hn
    rw [hn.deriv_eq, deriv_const]

/-!
## The lemma
-/

/-- **Uniform bounds and limits for the radial cut-offs `cut n` of the truncation argument**
(`cut n z = smoothTransition ((n+1)z - 1) (1 - smoothTransition (z/(n+1) - 2))`, equal to `1`
on `[2/(n+1), 2(n+1)]` and vanishing outside `(1/(n+1), 3(n+1))`; all in
`Submission.Work.FTS.EllipticEst.interpol_trunc_defs`).

There is `K > 0` with, for every `n` and every `z`, `|z · deriv (cut n) z| ≤ K`; moreover for
every fixed `z` with `0 < z` the cut-offs converge to `1` and the scaled derivatives to `0`:
`cut n z → 1` and `z · deriv (cut n) z → 0` as `n → ∞`.

Route: the product rule on the two `smoothTransition` factors gives
`z (cut n)'(z) = [(n+1)z·ψ'((n+1)z-1)]·(1-ψ(s)) - ψ(t)·[z ψ'(s)/(n+1)]` with
`t = (n+1)z - 1`, `s = z/(n+1) - 2`; since `(n+1)z = t+1` and `z/(n+1) = s+2`, the
constant `K := sup |(t+1)ψ'(t)| + sup |(t+2)ψ'(t)|` works (`deriv ψ` is continuous with
compact support).  For fixed `z > 0` and large `n` one has `cut n ≡ 1` on a neighbourhood
of `z` (`cut_eq_one_of_mem`), hence `deriv (cut n) z = 0`. -/
theorem cut_deriv_uniform : ∃ K : ℝ, 0 < K ∧
    (∀ n : ℕ, ∀ z : ℝ, |z * deriv (Work.FTS.EllipticEst.cut n) z| ≤ K)
    ∧ (∀ z : ℝ, 0 < z → Filter.Tendsto (fun n : ℕ => Work.FTS.EllipticEst.cut n z) Filter.atTop (nhds 1))
    ∧ (∀ z : ℝ, Filter.Tendsto (fun n : ℕ => z * deriv (Work.FTS.EllipticEst.cut n) z) Filter.atTop (nhds 0)) := by
  obtain ⟨C1, hC1, h1⟩ := exists_bound_shift_mul_deriv_smoothTransition 1
  obtain ⟨C2, hC2, h2⟩ := exists_bound_shift_mul_deriv_smoothTransition 2
  refine ⟨max 1 (C1 + C2), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_, ?_, ?_⟩
  · intro n z
    exact le_trans (abs_z_mul_deriv_cut_le n z hC1 h1 hC2 h2) (le_max_right _ _)
  · intro z hz
    refine (tendsto_const_nhds (x := (1 : ℝ))).congr' ?_
    filter_upwards [cut_eventuallyEq_one_of_pos hz] with n hn
    exact hn.eq_of_nhds.symm
  · intro z
    by_cases hz : z = 0
    · subst hz
      simpa using (tendsto_const_nhds (x := (0 : ℝ)))
    · refine (tendsto_const_nhds (x := (0 : ℝ))).congr' ?_
      filter_upwards [deriv_cut_eventually_eq_zero hz] with n hn
      simp [hn]

end Work.FTS.EllipticEst.AngSecond
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngularW.cutZ2Deriv2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngularW

open scoped Real Topology
open Filter Set

noncomputable section

/-!
## The second derivative of the radial cut-off `cut n`, uniformly bounded after `z ^ 2`

`Work.FTS.EllipticEst.cut n z = ψ ((n+1) z - 1) (1 - ψ (z/(n+1) - 2))` with
`ψ = Real.smoothTransition`, the smooth step which is `0` off `(0,1)` (as are all its
derivatives).  Writing, for `w > 0`,

`cutG w z = ψ (w z - 1) (1 - ψ (z/w - 2))`

(so that `cut n = cutG ((n : ℝ) + 1)`), differentiating `cutG w` by the chain and product
rules gives

`z ^ 2 (cutG w)''(z) = ((w z) ^ 2 ψ''(w z - 1)) (1 - ψ (z/w - 2))
    - 2 ((w z) ψ'(w z - 1)) ((z/w) ψ'(z/w - 2)) - ψ (w z - 1) ((z/w) ^ 2 ψ''(z/w - 2))`

(using `z ^ 2 = (w z) (z/w)` in the middle term).  Each of the three terms is bounded
uniformly in `w > 0` and `z`: the rescaled quantities `(x + 1) ^ k ψ^{(k)}(x)` and
`(x + 2) ^ k ψ^{(k)}(x)`, `k ≤ 2`, are continuous and vanish off `[0,1]`, hence bounded,
while `|ψ| ≤ 1` and `|1 - ψ| ≤ 1`.  This gives `cutZ2Deriv2`.
-/

/-! ### Rescaled derivatives of `Real.smoothTransition` -/

private theorem deriv_sT_eq_zero_of_lt {x : ℝ} (hx : x < 0) :
    deriv Real.smoothTransition x = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
    exact Real.smoothTransition.zero_of_nonpos hy.le
  rw [h.deriv_eq, deriv_const]

private theorem deriv_sT_eq_zero_of_gt {x : ℝ} (hx : 1 < x) :
    deriv Real.smoothTransition x = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact Real.smoothTransition.one_of_one_le hy.le
  rw [h.deriv_eq, deriv_const]

private theorem continuous_deriv_deriv_sT :
    Continuous (deriv (deriv Real.smoothTransition)) := by
  have h : Continuous (iteratedDeriv 2 Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 3)).continuous_iteratedDeriv 2 (by norm_num)
  simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using h

private theorem deriv_deriv_sT_eq_zero_of_lt {x : ℝ} (hx : x < 0) :
    deriv (deriv Real.smoothTransition) x = 0 := by
  have h : deriv Real.smoothTransition =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [Metric.ball_mem_nhds x (by linarith : (0 : ℝ) < -x)] with y hy
    rw [Metric.mem_ball, Real.dist_eq] at hy
    refine deriv_sT_eq_zero_of_lt ?_
    have := (abs_lt.mp hy).2
    linarith
  rw [h.deriv_eq, deriv_const]

private theorem deriv_deriv_sT_eq_zero_of_gt {x : ℝ} (hx : 1 < x) :
    deriv (deriv Real.smoothTransition) x = 0 := by
  have h : deriv Real.smoothTransition =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [Metric.ball_mem_nhds x (by linarith : (0 : ℝ) < (x - 1) / 2)] with y hy
    rw [Metric.mem_ball, Real.dist_eq] at hy
    refine deriv_sT_eq_zero_of_gt ?_
    have := (abs_lt.mp hy).1
    linarith
  rw [h.deriv_eq, deriv_const]

private theorem abs_sT_le_one (x : ℝ) : |Real.smoothTransition x| ≤ 1 := by
  rw [abs_of_nonneg (Real.smoothTransition.nonneg x)]
  exact Real.smoothTransition.le_one x

private theorem abs_one_sub_sT_le_one (x : ℝ) : |1 - Real.smoothTransition x| ≤ 1 := by
  rw [abs_of_nonneg (by linarith [Real.smoothTransition.le_one x])]
  linarith [Real.smoothTransition.nonneg x]

/-- `x ↦ (x + c) ψ'(x)` is bounded: it is continuous and vanishes off `[0,1]`. -/
private theorem exists_bound_shift_mul_deriv (c : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |(x + c) * deriv Real.smoothTransition x| ≤ C := by
  have hcont : Continuous (fun x : ℝ => (x + c) * deriv Real.smoothTransition x) :=
    (continuous_id.add continuous_const).mul
      ((Real.smoothTransition.contDiff (n := 2)).continuous_deriv (by norm_num))
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (0 : ℝ) 1) hcont.continuousOn
  have hC0 : 0 ≤ C := by
    have h := hC 0 (by norm_num)
    rw [Real.norm_eq_abs] at h
    exact le_trans (abs_nonneg _) h
  refine ⟨C, hC0, fun x => ?_⟩
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
  · have h := hC x hx
    rwa [Real.norm_eq_abs] at h
  · simp only [Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · rw [deriv_sT_eq_zero_of_lt hx, mul_zero, abs_zero]; exact hC0
    · rw [deriv_sT_eq_zero_of_gt hx, mul_zero, abs_zero]; exact hC0

/-- `x ↦ (x + c) ^ 2 ψ''(x)` is bounded: it is continuous and vanishes off `[0,1]`. -/
private theorem exists_bound_shift_sq_mul_deriv2 (c : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |(x + c)^2 * deriv (deriv Real.smoothTransition) x| ≤ C := by
  have hcont : Continuous (fun x : ℝ => (x + c)^2 * deriv (deriv Real.smoothTransition) x) :=
    ((continuous_id.add continuous_const).pow 2).mul continuous_deriv_deriv_sT
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (0 : ℝ) 1) hcont.continuousOn
  have hC0 : 0 ≤ C := by
    have h := hC 0 (by norm_num)
    rw [Real.norm_eq_abs] at h
    exact le_trans (abs_nonneg _) h
  refine ⟨C, hC0, fun x => ?_⟩
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
  · have h := hC x hx
    rwa [Real.norm_eq_abs] at h
  · simp only [Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · rw [deriv_deriv_sT_eq_zero_of_lt hx, mul_zero, abs_zero]; exact hC0
    · rw [deriv_deriv_sT_eq_zero_of_gt hx, mul_zero, abs_zero]; exact hC0

/-! ### The cut-off in rescaled form and its first two derivatives -/

/-- The cut-off in rescaled form: `cutG w z = ψ (w z - 1) (1 - ψ (z / w - 2))`. -/
private def cutG (w z : ℝ) : ℝ :=
  Real.smoothTransition (w * z - 1) * (1 - Real.smoothTransition (z / w - 2))

/-- The first derivative of `cutG w`, as given by the chain and product rules. -/
private def dcutG (w y : ℝ) : ℝ :=
  (w * deriv Real.smoothTransition (w * y - 1)) * (1 - Real.smoothTransition (y / w - 2))
    + Real.smoothTransition (w * y - 1)
      * (-(deriv Real.smoothTransition (y / w - 2) * (1 / w)))

/-- The second derivative of `cutG w` obtained from the product and chain rules. -/
private def rawDD (w y : ℝ) : ℝ :=
  (w * (w * deriv (deriv Real.smoothTransition) (w * y - 1)))
      * (1 - Real.smoothTransition (y / w - 2))
    + (w * deriv Real.smoothTransition (w * y - 1))
      * (-(deriv Real.smoothTransition (y / w - 2) * (1 / w)))
    - ((w * deriv Real.smoothTransition (w * y - 1))
        * (deriv Real.smoothTransition (y / w - 2) * (1 / w))
      + Real.smoothTransition (w * y - 1)
        * ((deriv (deriv Real.smoothTransition) (y / w - 2) * (1 / w)) * (1 / w)))

/-- The second derivative of `cutG w`, in simplified form. -/
private def ddcutG (w z : ℝ) : ℝ :=
  w ^ 2 * deriv (deriv Real.smoothTransition) (w * z - 1)
      * (1 - Real.smoothTransition (z / w - 2))
    - 2 * (deriv Real.smoothTransition (w * z - 1)
        * deriv Real.smoothTransition (z / w - 2))
    - Real.smoothTransition (w * z - 1)
      * (deriv (deriv Real.smoothTransition) (z / w - 2) / w ^ 2)

private theorem cut_eq_cutG (n : ℕ) :
    Work.FTS.EllipticEst.cut n = cutG ((n : ℝ) + 1) := by
  funext z
  simp only [Work.FTS.EllipticEst.cut, cutG]

/-! ### Chain rules -/

private theorem hasDerivAt_sT_comp (w y : ℝ) :
    HasDerivAt (fun y : ℝ => Real.smoothTransition (w * y - 1))
      (w * deriv Real.smoothTransition (w * y - 1)) y := by
  have h1 : HasDerivAt (fun y : ℝ => w * y - 1) w y := by
    have hR : HasDerivAt (fun y : ℝ => w * y) w y := by
      simpa using ((hasDerivAt_id' y).const_mul w)
    exact hR.sub_const 1
  have h2 : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition (w * y - 1)) (w * y - 1) :=
    (((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)).differentiableAt).hasDerivAt
  exact (h2.comp y h1).congr_deriv (mul_comm _ _)

private theorem hasDerivAt_deriv_sT_comp (w y : ℝ) :
    HasDerivAt (fun y : ℝ => deriv Real.smoothTransition (w * y - 1))
      (w * deriv (deriv Real.smoothTransition) (w * y - 1)) y := by
  have h1 : HasDerivAt (fun y : ℝ => w * y - 1) w y := by
    have hR : HasDerivAt (fun y : ℝ => w * y) w y := by
      simpa using ((hasDerivAt_id' y).const_mul w)
    exact hR.sub_const 1
  have h2 : HasDerivAt (deriv Real.smoothTransition)
      (deriv (deriv Real.smoothTransition) (w * y - 1)) (w * y - 1) :=
    ((Real.smoothTransition.contDiff (n := 2)).differentiable_deriv_two.differentiableAt).hasDerivAt
  exact (h2.comp y h1).congr_deriv (mul_comm _ _)

private theorem hasDerivAt_compl_sT (w y : ℝ) :
    HasDerivAt (fun y : ℝ => 1 - Real.smoothTransition (y / w - 2))
      (-(deriv Real.smoothTransition (y / w - 2) * (1 / w))) y := by
  have h1 : HasDerivAt (fun y : ℝ => y / w - 2) (1 / w) y := by
    have hR : HasDerivAt (fun y : ℝ => y / w) (1 / w) y := by
      simpa using (hasDerivAt_id' y).div_const w
    exact hR.sub_const 2
  have h2 : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition (y / w - 2)) (y / w - 2) :=
    (((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)).differentiableAt).hasDerivAt
  exact ((hasDerivAt_const (x := y) (c := (1 : ℝ))).sub (h2.comp y h1)).congr_deriv (zero_sub _)

private theorem hasDerivAt_deriv_sT_div (w y : ℝ) :
    HasDerivAt (fun y : ℝ => deriv Real.smoothTransition (y / w - 2))
      (deriv (deriv Real.smoothTransition) (y / w - 2) * (1 / w)) y := by
  have h1 : HasDerivAt (fun y : ℝ => y / w - 2) (1 / w) y := by
    have hR : HasDerivAt (fun y : ℝ => y / w) (1 / w) y := by
      simpa using (hasDerivAt_id' y).div_const w
    exact hR.sub_const 2
  have h2 : HasDerivAt (deriv Real.smoothTransition)
      (deriv (deriv Real.smoothTransition) (y / w - 2)) (y / w - 2) :=
    ((Real.smoothTransition.contDiff (n := 2)).differentiable_deriv_two.differentiableAt).hasDerivAt
  exact (h2.comp y h1).congr_deriv rfl

private theorem hasDerivAt_deriv_sT_div_mul (w y : ℝ) :
    HasDerivAt (fun y : ℝ => deriv Real.smoothTransition (y / w - 2) * (1 / w))
      ((deriv (deriv Real.smoothTransition) (y / w - 2) * (1 / w)) * (1 / w)) y :=
  (hasDerivAt_deriv_sT_div w y).mul_const (1 / w)

/-! ### The two derivatives of `cutG` -/

private theorem hasDerivAt_cutG (w y : ℝ) :
    HasDerivAt (cutG w) (dcutG w y) y := by
  have h := (hasDerivAt_sT_comp w y).mul (hasDerivAt_compl_sT w y)
  have hfun : cutG w = (fun y : ℝ => Real.smoothTransition (w * y - 1))
      * (fun y : ℝ => 1 - Real.smoothTransition (y / w - 2)) := by
    funext y
    simp only [cutG, Pi.mul_apply]
  rw [hfun]
  refine h.congr_deriv ?_
  simp only [dcutG]

private theorem rawDD_eq_ddcutG (w y : ℝ) (hw : w ≠ 0) : rawDD w y = ddcutG w y := by
  have key : ∀ a c d e f B : ℝ,
      (w * (w * a)) * B + (w * c) * (-(d * (1 / w)))
          - ((w * c) * (d * (1 / w)) + e * ((f * (1 / w)) * (1 / w)))
        = w ^ 2 * a * B - 2 * (c * d) - e * (f / w ^ 2) := by
    intro a c d e f B
    field_simp
    ring
  simp only [rawDD, ddcutG]
  exact key _ _ _ _ _ _

private theorem hasDerivAt_dcutG (w y : ℝ) (hw : w ≠ 0) :
    HasDerivAt (dcutG w) (ddcutG w y) y := by
  have hP : HasDerivAt
      (fun y : ℝ => (w * deriv Real.smoothTransition (w * y - 1))
        * (1 - Real.smoothTransition (y / w - 2)))
      ((w * (w * deriv (deriv Real.smoothTransition) (w * y - 1)))
          * (1 - Real.smoothTransition (y / w - 2))
        + (w * deriv Real.smoothTransition (w * y - 1))
          * (-(deriv Real.smoothTransition (y / w - 2) * (1 / w)))) y :=
    ((hasDerivAt_deriv_sT_comp w y).const_mul w).mul (hasDerivAt_compl_sT w y)
  have hQ : HasDerivAt
      (fun y : ℝ => Real.smoothTransition (w * y - 1)
        * (deriv Real.smoothTransition (y / w - 2) * (1 / w)))
      ((w * deriv Real.smoothTransition (w * y - 1))
          * (deriv Real.smoothTransition (y / w - 2) * (1 / w))
        + Real.smoothTransition (w * y - 1)
          * ((deriv (deriv Real.smoothTransition) (y / w - 2) * (1 / w)) * (1 / w))) y :=
    (hasDerivAt_sT_comp w y).mul (hasDerivAt_deriv_sT_div_mul w y)
  have h := hP.sub hQ
  have hfun : dcutG w
      = (fun y : ℝ => (w * deriv Real.smoothTransition (w * y - 1))
            * (1 - Real.smoothTransition (y / w - 2)))
        - (fun y : ℝ => Real.smoothTransition (w * y - 1)
            * (deriv Real.smoothTransition (y / w - 2) * (1 / w))) := by
    funext y
    simp only [dcutG, Pi.sub_apply]
    ring
  rw [hfun]
  refine h.congr_deriv ?_
  exact rawDD_eq_ddcutG w y hw

private theorem deriv_deriv_cutG (w z : ℝ) (hw : w ≠ 0) :
    deriv (deriv (cutG w)) z = ddcutG w z := by
  have h : deriv (cutG w) = dcutG w := funext (fun y => (hasDerivAt_cutG w y).deriv)
  rw [h]
  exact (hasDerivAt_dcutG w z hw).deriv

/-! ### The uniform bound -/

private theorem z2_algebra (w z P Q R A B S : ℝ) (hw : w ≠ 0) :
    z ^ 2 * (w ^ 2 * P * B - 2 * (Q * R) - A * (S / w ^ 2))
      = ((w * z - 1 + 1) ^ 2 * P) * B
        - 2 * ((w * z - 1 + 1) * Q) * ((z / w - 2 + 2) * R)
        - A * ((z / w - 2 + 2) ^ 2 * S) := by
  field_simp
  ring

private theorem z2_mul_ddcutG (w z : ℝ) (hw : w ≠ 0) :
    z ^ 2 * ddcutG w z
      = ((w * z - 1 + 1) ^ 2 * deriv (deriv Real.smoothTransition) (w * z - 1))
          * (1 - Real.smoothTransition (z / w - 2))
        - 2 * ((w * z - 1 + 1) * deriv Real.smoothTransition (w * z - 1))
          * ((z / w - 2 + 2) * deriv Real.smoothTransition (z / w - 2))
        - Real.smoothTransition (w * z - 1)
          * ((z / w - 2 + 2) ^ 2 * deriv (deriv Real.smoothTransition) (z / w - 2)) := by
  simp only [ddcutG]
  exact z2_algebra w z _ _ _ _ _ _ hw

private theorem abs_sub_sub_le (a b c : ℝ) : |a - b - c| ≤ |a| + |b| + |c| := by
  have h1 : |a - b - c| ≤ |a - b| + |c| := by
    simpa using abs_sub_le (a - b) 0 c
  have h2 : |a - b| ≤ |a| + |b| := by
    simpa using abs_sub_le a 0 b
  linarith

private theorem bound_ddcutG {C1 C2 CA CB : ℝ} (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (h1 : ∀ x : ℝ, |(x + 1) * deriv Real.smoothTransition x| ≤ C1)
    (h2 : ∀ x : ℝ, |(x + 2) * deriv Real.smoothTransition x| ≤ C2)
    (hA : ∀ x : ℝ, |(x + 1) ^ 2 * deriv (deriv Real.smoothTransition) x| ≤ CA)
    (hB : ∀ x : ℝ, |(x + 2) ^ 2 * deriv (deriv Real.smoothTransition) x| ≤ CB)
    (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) (w z : ℝ) (hw : w ≠ 0) :
    |z ^ 2 * ddcutG w z| ≤ CA + 2 * C1 * C2 + CB := by
  rw [z2_mul_ddcutG w z hw]
  have hX : |((w * z - 1 + 1) ^ 2 * deriv (deriv Real.smoothTransition) (w * z - 1))
      * (1 - Real.smoothTransition (z / w - 2))| ≤ CA := by
    calc |((w * z - 1 + 1) ^ 2 * deriv (deriv Real.smoothTransition) (w * z - 1))
          * (1 - Real.smoothTransition (z / w - 2))|
        = |(w * z - 1 + 1) ^ 2 * deriv (deriv Real.smoothTransition) (w * z - 1)|
          * |1 - Real.smoothTransition (z / w - 2)| := abs_mul _ _
      _ ≤ CA * 1 :=
          mul_le_mul (hA (w * z - 1)) (abs_one_sub_sT_le_one (z / w - 2)) (abs_nonneg _) hCA
      _ = CA := mul_one CA
  have hY : |2 * ((w * z - 1 + 1) * deriv Real.smoothTransition (w * z - 1))
      * ((z / w - 2 + 2) * deriv Real.smoothTransition (z / w - 2))| ≤ 2 * C1 * C2 := by
    have h1' : |(w * z - 1 + 1) * deriv Real.smoothTransition (w * z - 1)| ≤ C1 :=
      h1 (w * z - 1)
    have h2' : |(z / w - 2 + 2) * deriv Real.smoothTransition (z / w - 2)| ≤ C2 :=
      h2 (z / w - 2)
    have hstep : |2 * ((w * z - 1 + 1) * deriv Real.smoothTransition (w * z - 1))
        * ((z / w - 2 + 2) * deriv Real.smoothTransition (z / w - 2))|
        = (2 * |(w * z - 1 + 1) * deriv Real.smoothTransition (w * z - 1)|)
          * |(z / w - 2 + 2) * deriv Real.smoothTransition (z / w - 2)| := by
      rw [abs_mul]
      rw [abs_mul]
      rw [abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    rw [hstep]
    calc (2 * |(w * z - 1 + 1) * deriv Real.smoothTransition (w * z - 1)|)
          * |(z / w - 2 + 2) * deriv Real.smoothTransition (z / w - 2)|
        ≤ (2 * C1) * C2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1' (by norm_num)) h2'
            (abs_nonneg _) (by linarith)
      _ = 2 * C1 * C2 := by ring
  have hZ : |Real.smoothTransition (w * z - 1)
      * ((z / w - 2 + 2) ^ 2 * deriv (deriv Real.smoothTransition) (z / w - 2))| ≤ CB := by
    calc |Real.smoothTransition (w * z - 1)
          * ((z / w - 2 + 2) ^ 2 * deriv (deriv Real.smoothTransition) (z / w - 2))|
        = |Real.smoothTransition (w * z - 1)|
          * |(z / w - 2 + 2) ^ 2 * deriv (deriv Real.smoothTransition) (z / w - 2)| := abs_mul _ _
      _ ≤ 1 * CB :=
          mul_le_mul (abs_sT_le_one _) (hB (z / w - 2)) (abs_nonneg _) zero_le_one
      _ = CB := one_mul CB
  exact le_trans (abs_sub_sub_le _ _ _) (by linarith)

theorem cutZ2Deriv2 : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ z : ℝ,
    |z ^ 2 * deriv (deriv (Work.FTS.EllipticEst.cut n)) z| ≤ C := by
  obtain ⟨C1, hC1, h1⟩ := exists_bound_shift_mul_deriv 1
  obtain ⟨C2, hC2, h2⟩ := exists_bound_shift_mul_deriv 2
  obtain ⟨CA, hCA, hA⟩ := exists_bound_shift_sq_mul_deriv2 1
  obtain ⟨CB, hCB, hB⟩ := exists_bound_shift_sq_mul_deriv2 2
  refine ⟨max 1 (CA + 2 * C1 * C2 + CB), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro n z
  have hwn : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [cut_eq_cutG n, deriv_deriv_cutG ((n : ℝ) + 1) z hwn]
  exact le_trans (bound_ddcutG hC1 hC2 h1 h2 hA hB hCA hCB ((n : ℝ) + 1) z hwn)
    (le_max_right _ _)

end

end Work.FTS.EllipticEst.AngularW
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Final.FlatCut.cutMono =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Final.FlatCut


end Work.FTS.EllipticEst.Final.FlatCut
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Final.FlatCut.cutTendstoOne =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Final.FlatCut

open Filter



end Work.FTS.EllipticEst.Final.FlatCut
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.HR2.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest.HR2



/-! ## The family `cut n` is admissible -/

theorem cut_contDiff_two (n : ℕ) : ContDiff ℝ 2 (Work.FTS.EllipticEst.cut n) :=
  (Work.FTS.EllipticEst.cut_contDiff n).of_le (by norm_num)

theorem cut_hasCompactSupport (n : ℕ) : HasCompactSupport (Work.FTS.EllipticEst.cut n) := by
  rw [HasCompactSupport, tsupport]
  refine (isCompact_Icc (a := (1 / (n + 1 : ℝ))) (b := 3 * (n + 1 : ℝ))).of_isClosed_subset
    isClosed_closure (closure_minimal ?_ isClosed_Icc)
  intro z hz
  by_contra hcon
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hcon
  rcases hcon with hlt | hlt
  · exact hz (Work.FTS.EllipticEst.cut_apply_zero_of_le n (le_of_lt hlt))
  · exact hz (Work.FTS.EllipticEst.cut_apply_zero_of_ge n (le_of_lt hlt))


/-- The cut-off family is monotone in `n`. -/
theorem cut_mono (n : ℕ) (z : ℝ) :
    Work.FTS.EllipticEst.cut n z ≤ Work.FTS.EllipticEst.cut (n + 1) z := by
  rcases le_or_gt 0 z with hz | hz
  · have h1 : ((n : ℝ) + 1) * z - 1 ≤ ((n : ℝ) + 1 + 1) * z - 1 := by nlinarith
    have h2 : z / ((n : ℝ) + 1 + 1) - 2 ≤ z / ((n : ℝ) + 1) - 2 := by
      have h2' : (0 : ℝ) < (n : ℝ) + 1 := by linarith
      have h4 : z / ((n : ℝ) + 1 + 1) ≤ z / ((n : ℝ) + 1) :=
        div_le_div_of_nonneg_left hz h2' (by linarith)
      linarith
    have ha : Real.smoothTransition (((n : ℝ) + 1) * z - 1)
        ≤ Real.smoothTransition (((n : ℝ) + 1 + 1) * z - 1) := Real.smoothTransition.monotone h1
    have hb : (1 - Real.smoothTransition (z / ((n : ℝ) + 1) - 2)) ≤
        (1 - Real.smoothTransition (z / ((n : ℝ) + 1 + 1) - 2)) := by
      have := Real.smoothTransition.monotone h2
      linarith
    have hb0 : (0 : ℝ) ≤ 1 - Real.smoothTransition (z / ((n : ℝ) + 1) - 2) :=
      sub_nonneg.mpr (Real.smoothTransition.le_one _)
    have ha0 : (0 : ℝ) ≤ Real.smoothTransition (((n : ℝ) + 1) * z - 1) :=
      Real.smoothTransition.nonneg _
    simp only [Work.FTS.EllipticEst.cut]
    push_cast
    exact mul_le_mul ha hb hb0 (le_trans ha0 ha)
  · have h1 : ((n : ℝ) + 1) * z - 1 < 0 := by
      have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      nlinarith
    have hzero : Real.smoothTransition (((n : ℝ) + 1) * z - 1) = 0 :=
      Real.smoothTransition.zero_of_nonpos h1.le
    have hnc : Work.FTS.EllipticEst.cut n z = 0 := by
      simp only [Work.FTS.EllipticEst.cut]
      push_cast
      rw [hzero, zero_mul]
    rw [hnc]
    exact Work.FTS.EllipticEst.cut_nonneg _ _


end Work.FTS.EllipticEst.Honest.HR2
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.RadCutDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The truncated radial energy functional: interface

This module collects the vocabulary used by `Work.FTS.EllipticEst.radial_energy_of_truncated`:

* the angular `θ`-integrals `thRadSq Φ`, `thDthSq Φ`, `thDivCosSq Φ`, `thGPair G Φ` of the four
  quadratic quantities appearing in the radial energy inequality and of the source pairing;
* the truncated functionals `tS, tB, tC, tP, tL` obtained from those by integrating against the
  truncated weight `cutW R = chi (·/R) · w²` of `RadialEnergyDefs`, and the truncation error
  `tErr Φ R = ∫_{z > R} w z² · ∫_θ Φ(z,θ)²`;
* the elementary facts about `cutW` (positivity, domination by `w²`, measurability, the values on
  `[0,R]` and off `[0,2R]`, pointwise convergence to `w²`);
* the dominated-convergence tool `tendsto_integral_chi_mul`;
* the identification `w z² · ∫_θ h(z,θ)² = ∫_θ (h(z,θ) · w z)²`, which turns the `L2Mem`
  hypotheses of the caller into integrability of the untruncated integrands;
* almost-everywhere strong measurability of the `θ`-integrals above (from continuity of the
  integrand on the open quadrant).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.RadCut

/-! ## The truncated functionals -/


/-- The angular integral `z ↦ ∫_θ (∂_θΦ(z,θ))²`. -/
def thDthSq (Φ : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth Φ z θ) ^ 2



/-- The truncated radial term `α² ∫ cutW R · ∫_θ (∂_zΦ)²` of the identity (written exactly as it
occurs in `TruncIdentity`). -/
def tS (Φ : ℝ → ℝ → ℝ) (R : ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, z ^ 2 * Work.FTS.EllipticEst.cutW R z
    * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz Φ z θ) ^ 2)

/-- The truncated angular term `∫ cutW R · ∫_θ (∂_θΦ)²`. -/
def tB (Φ : ℝ → ℝ → ℝ) (R : ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.cutW R z * thDthSq Φ z





/-! ## Elementary facts about the truncated weight -/








/-! ## Dominated convergence with the rescaled cut-off -/



/-! ## From the `L2Mem` hypotheses to integrability of the untruncated integrands -/





/-! ## Almost everywhere strong measurability of the angular integrals -/








end Work.FTS.EllipticEst.RadCut
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.AgmonTT =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.EllipticEst.AgmonSlice (cutRho cutRho_nonneg cutU cutF cutHs cutH cutQs)

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## 1. Elementary inequalities -/

/-- `a² ≤ 1` for `|a| ≤ 1`. -/
private lemma sq_le_one_of_abs_le_one {a : ℝ} (h : |a| ≤ 1) : a ^ 2 ≤ 1 := by
  nlinarith only [h, abs_nonneg a, sq_abs a]

/-- `3Wp²XY ≤ (1/4)Wp²X² + 9WY²` for `W, p, X, Y ≥ 0`, `p ≤ 1`. -/
private lemma young_3W (W p X Y : ℝ) (hW : 0 ≤ W) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    3 * W * p ^ 2 * X * Y ≤ (1 / 4) * (W * p ^ 2 * X ^ 2) + 9 * (W * Y ^ 2) := by
  have h1 : 12 * p * X * Y ≤ p ^ 2 * X ^ 2 + 36 * Y ^ 2 := by
    have h := sq_nonneg (p * X - 6 * Y)
    nlinarith only [h]
  have h2 : 12 * p ^ 2 * X * Y ≤ p * (p ^ 2 * X ^ 2 + 36 * Y ^ 2) := by
    have h := mul_le_mul_of_nonneg_left h1 hp0
    nlinarith only [h]
  have hbnn : 0 ≤ p ^ 2 * X ^ 2 + 36 * Y ^ 2 := by nlinarith only [sq_nonneg X, sq_nonneg Y]
  have h1mp : 0 ≤ 1 - p := by linarith only [hp1]
  have h3 : p * (p ^ 2 * X ^ 2 + 36 * Y ^ 2) ≤ p ^ 2 * X ^ 2 + 36 * Y ^ 2 := by
    nlinarith only [hbnn, h1mp, hp0]
  have h4 : 12 * W * p ^ 2 * X * Y ≤ W * (p ^ 2 * X ^ 2 + 36 * Y ^ 2) := by
    have h := mul_le_mul_of_nonneg_left (le_trans h2 h3) hW
    nlinarith only [h]
  nlinarith only [h4]

/-- `2cWpXY ≤ (1/12)Wp²X² + 12c(c+1)WY²` for `W, p, X, Y, c ≥ 0`. -/
private lemma young_2cW (W p X Y c : ℝ) (hW : 0 ≤ W) (hc : 0 ≤ c) :
    2 * c * W * p * X * Y ≤ (1 / 12) * (W * p ^ 2 * X ^ 2)
      + 12 * c * (c + 1) * (W * Y ^ 2) := by
  have h1 : 24 * c * p * X * Y ≤ p ^ 2 * X ^ 2 + 144 * c ^ 2 * Y ^ 2 := by
    have h := sq_nonneg (p * X - 12 * c * Y)
    nlinarith only [h]
  have h1' : 24 * c * p * X * Y ≤ p ^ 2 * X ^ 2 + 144 * c * (c + 1) * Y ^ 2 := by
    nlinarith only [h1, hc, sq_nonneg Y]
  have h2 : 2 * c * p * X * Y ≤ (1 / 12) * (p ^ 2 * X ^ 2) + 12 * c * (c + 1) * Y ^ 2 := by
    nlinarith only [h1']
  have h3 : W * (2 * c * p * X * Y)
      ≤ W * ((1 / 12) * (p ^ 2 * X ^ 2) + 12 * c * (c + 1) * Y ^ 2) :=
    mul_le_mul_of_nonneg_left h2 hW
  nlinarith only [h3]

/-- `2ν·Wp²(X+Z)Y ≤ ν²Wp²X² + ν²Wp²Z² + 2WY²` for `W, p, X, Z, Y, ν ≥ 0`, `p ≤ 1`. -/
private lemma young_split_clear (W p X Z Y ν : ℝ) (hW : 0 ≤ W) (hν : 0 ≤ ν) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) :
    2 * ν * (W * p ^ 2 * (X + Z) * Y)
      ≤ ν ^ 2 * (W * p ^ 2 * X ^ 2) + ν ^ 2 * (W * p ^ 2 * Z ^ 2) + 2 * (W * Y ^ 2) := by
  have h1 : 2 * ν * X * Y ≤ ν ^ 2 * X ^ 2 + Y ^ 2 := by
    have h := sq_nonneg (ν * X - Y)
    nlinarith only [h]
  have h2 : 2 * ν * W * p * X * Y ≤ ν ^ 2 * W * p * X ^ 2 + W * p * Y ^ 2 := by
    have h := mul_le_mul_of_nonneg_left h1 (mul_nonneg hW hp0)
    nlinarith only [h]
  have h3 : 2 * ν * W * p ^ 2 * X * Y ≤ ν ^ 2 * W * p ^ 2 * X ^ 2 + W * p ^ 2 * Y ^ 2 := by
    have h := mul_le_mul_of_nonneg_left h2 hp0
    nlinarith only [h]
  have h4 : W * p ^ 2 * Y ^ 2 ≤ W * Y ^ 2 := by
    have hp2 : p ^ 2 ≤ 1 := by nlinarith only [hp0, hp1]
    have h := mul_le_mul_of_nonneg_right hp2 hW
    have h' := mul_le_mul_of_nonneg_right h (sq_nonneg Y)
    nlinarith only [h']
  have h5 : 2 * ν * W * p ^ 2 * X * Y ≤ ν ^ 2 * W * p ^ 2 * X ^ 2 + W * Y ^ 2 := by
    linarith only [h3, h4]
  have h6 : 2 * ν * Z * Y ≤ ν ^ 2 * Z ^ 2 + Y ^ 2 := by
    have h := sq_nonneg (ν * Z - Y)
    nlinarith only [h]
  have h7 : 2 * ν * W * p ^ 2 * Z * Y ≤ ν ^ 2 * W * p ^ 2 * Z ^ 2 + W * Y ^ 2 := by
    have h := mul_le_mul_of_nonneg_left h6 (mul_nonneg hW (sq_nonneg p))
    have hz : W * p ^ 2 * Y ^ 2 ≤ W * Y ^ 2 := h4
    nlinarith only [h, hz]
  have h8 : 2 * ν * (W * p ^ 2 * (X + Z) * Y)
      = 2 * ν * W * p ^ 2 * X * Y + 2 * ν * W * p ^ 2 * Z * Y := by ring
  rw [h8]
  linarith only [h5, h7]

/-- The pointwise assembly (cleared of denominators): all variables nonnegative. -/
private lemma pointwise_final {α Kc W p A Z B D : ℝ} (hα : 0 < α) (hKc : 0 ≤ Kc)
    (hW : 0 ≤ W) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hA : 0 ≤ A) (hZ : 0 ≤ Z) (hB : 0 ≤ B)
    (hD : D ≤ 3 * W * p ^ 2 * A + 2 * Kc * W * p * A + W * p ^ 2 * (A + Z)) :
    12 * (α ^ 2 * (D * B))
      ≤ 12 * ((1 / 3 + α ^ 2 / 4) * (α ^ 2 * (W * p ^ 2 * A ^ 2)))
        + 12 * (((9 + 12 * Kc * (Kc + 1)) * α ^ 2 + 2) * (W * B ^ 2))
        + 12 * ((α ^ 4 / 4) * (W * p ^ 2 * Z ^ 2)) := by
  have hν : 0 ≤ α ^ 2 / 2 := by positivity
  have h1 := young_3W W p A B hW hp0 hp1
  have h2 := young_2cW W p A B Kc hW hKc
  have h3 := young_split_clear W p A Z B (α ^ 2 / 2) hW hν hp0 hp1
  have h4 : D * B ≤ (3 * W * p ^ 2 * A + 2 * Kc * W * p * A + W * p ^ 2 * (A + Z)) * B :=
    mul_le_mul_of_nonneg_right hD hB
  have hgoal : α ^ 2 * (D * B)
      ≤ (1 / 3 + α ^ 2 / 4) * (α ^ 2 * (W * p ^ 2 * A ^ 2))
        + ((9 + 12 * Kc * (Kc + 1)) * α ^ 2 + 2) * (W * B ^ 2)
        + (α ^ 4 / 4) * (W * p ^ 2 * Z ^ 2) := by
    nlinarith only [h1, h2, h3, h4, hα, hKc, hW, hp0, hp1]
  linarith only [hgoal]

/-- The final arithmetic: from `α²X ≤ (1/3+α²/4)(α²X) + (c α² + 2)P + (α⁴/4)Q` with
`c ≤ c₀`, `0 < α ≤ 1`, `X, P, Q ≥ 0`, `c, c₀ ≥ 0` and `C₀ = 100 + 100 c₀(c₀+1)`,
conclude `α²X ≤ C₀ (P + α⁴Q)`. -/
private lemma arith_final {α X P Q c c0 C0 : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hX : 0 ≤ X) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hc : 0 ≤ c) (hc0 : 0 ≤ c0) (hcc : c ≤ c0)
    (hC1 : (12 / 5) * (c0 + 2) ≤ C0) (hC2 : (12 / 5 : ℝ) ≤ C0)
    (h1 : α ^ 2 * X ≤ (1 / 3 + α ^ 2 / 4) * (α ^ 2 * X) + (c * α ^ 2 + 2) * P
      + (α ^ 4 / 4) * Q) :
    α ^ 2 * X ≤ C0 * (P + α ^ 4 * Q) := by
  have hα2 : 0 < α ^ 2 := pow_pos hα 2
  have hα2le : α ^ 2 ≤ 1 := by nlinarith only [hα, hα1]
  have hα4 : 0 ≤ α ^ 4 := by positivity
  have h2 : (5 / 12) * (α ^ 2 * X) ≤ (c * α ^ 2 + 2) * P + (α ^ 4 / 4) * Q := by
    have hle : (5 / 12 : ℝ) * (α ^ 2 * X) ≤ (2 / 3 - α ^ 2 / 4) * (α ^ 2 * X) := by
      have h56 : (5 / 12 : ℝ) ≤ 2 / 3 - α ^ 2 / 4 := by linarith only [hα2le]
      exact mul_le_mul_of_nonneg_right h56 (by positivity)
    have h1' : (2 / 3 - α ^ 2 / 4) * (α ^ 2 * X)
        ≤ (c * α ^ 2 + 2) * P + (α ^ 4 / 4) * Q := by
      nlinarith only [h1]
    linarith only [hle, h1']
  have h3 : α ^ 2 * X ≤ (12 / 5) * ((c * α ^ 2 + 2) * P + (α ^ 4 / 4) * Q) := by
    linarith only [h2]
  have h4 : c * α ^ 2 ≤ c0 := by nlinarith only [hcc, hα2le, hc, hc0]
  have h5 : (c * α ^ 2 + 2) * P ≤ (c0 + 2) * P := by nlinarith only [h4, hP]
  have h6 : (α ^ 4 / 4) * Q ≤ α ^ 4 * Q := by nlinarith only [hQ, hα4]
  have h7 : (12 / 5) * ((c * α ^ 2 + 2) * P + (α ^ 4 / 4) * Q)
      ≤ (12 / 5) * ((c0 + 2) * P + α ^ 4 * Q) := by nlinarith only [h5, h6]
  have h8a : (12 / 5) * ((c0 + 2) * P) ≤ C0 * P := by
    have h := mul_le_mul_of_nonneg_right hC1 hP
    linarith only [h]
  have h8b : (12 / 5) * (α ^ 4 * Q) ≤ C0 * (α ^ 4 * Q) := by
    have hPQ : 0 ≤ α ^ 4 * Q := mul_nonneg hα4 hQ
    have h := mul_le_mul_of_nonneg_right hC2 hPQ
    linarith only [h]
  have h8 : (12 / 5) * ((c0 + 2) * P + α ^ 4 * Q) ≤ C0 * (P + α ^ 4 * Q) := by
    linarith only [h8a, h8b]
  linarith only [h3, h7, h8]

/-- `rDzIter 2 h z = z h'(z) + z² h''(z)` on `(0,∞)`. -/
private lemma rDzIter_two_eq {h : ℝ → ℝ} (hh : ContDiffOn ℝ 2 h (Set.Ioi 0)) {z : ℝ}
    (hz : 0 < z) : rDzIter 2 h z = z * deriv h z + z ^ 2 * deriv (deriv h) z := by
  have hd1 : ContDiffOn ℝ 1 (deriv h) (Set.Ioi 0) := hh.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hdiff : DifferentiableAt ℝ (deriv h) z :=
    (hd1.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have hprod : HasDerivAt (fun y : ℝ => y * deriv h y) (deriv h z + z * deriv (deriv h) z) z := by
    have h := (hasDerivAt_id z).mul hdiff.hasDerivAt
    refine h.congr_deriv ?_
    simp only [id_eq]
    ring
  change z * deriv (fun y : ℝ => y * deriv h y) z = _
  rw [hprod.deriv]
  ring

/-! ## 2. The cut-off family `psiFun chi k` -/

/-- The cut-offs `psiFun chi k` are nondecreasing in `k` at every `z > 0`. -/
private lemma chi_psiFun_mono {z : ℝ} (hz : 0 < z) :
    ∀ k l : ℕ, 2 ≤ k → k ≤ l →
      Work.FTS.EllipticEst.psiFun Work.Stability.chi k z
        ≤ Work.FTS.EllipticEst.psiFun Work.Stability.chi l z := by
  have hpsi : ∀ k : ℕ, 0 < Real.log (k : ℝ) →
      Work.FTS.EllipticEst.psiFun Work.Stability.chi k z
        = Work.Stability.chi (|Real.log z| / Real.log (k : ℝ)) := by
    intro k hlog
    rw [Work.FTS.EllipticEst.psiFun]
    rcases lt_or_ge (Real.log z) 0 with h | h
    · have hlogz : Real.log z = -|Real.log z| := by rw [abs_of_neg h, neg_neg]
      have h2 : Real.log z / Real.log (k : ℝ) = -(|Real.log z| / Real.log (k : ℝ)) := by
        conv_lhs => rw [hlogz, neg_div]
      rw [h2, Work.Stability.chi_neg]
    · rw [abs_of_nonneg h]
  intro k l hk hkl
  have hk1 : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 1 < k)
  have hl1 : (1 : ℝ) < (l : ℝ) := by exact_mod_cast (by omega : 1 < l)
  have hlogk : 0 < Real.log (k : ℝ) := Real.log_pos hk1
  have hlogl : 0 < Real.log (l : ℝ) := Real.log_pos hl1
  rw [hpsi k hlogk, hpsi l hlogl]
  rcases eq_or_ne z 1 with rfl | hz1
  · simp
  · have hlogz : Real.log z ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hz hz1
    have habs : 0 < |Real.log z| := abs_pos.mpr hlogz
    have hlogkl : Real.log (k : ℝ) ≤ Real.log (l : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hkl)
    refine Work.ChiExplicit.chi_antitoneOn (le_of_lt (div_pos habs hlogl))
      (le_of_lt (div_pos habs hlogk)) ?_
    exact div_le_div_of_nonneg_left habs.le hlogk hlogkl

/-- The cut-offs tend to `1` as `k → ∞` at every fixed `z > 0`. -/
private lemma chi_psiFun_tendsto_one {z : ℝ} (hz : 0 < z) :
    Filter.Tendsto (fun k : ℕ => Work.FTS.EllipticEst.psiFun Work.Stability.chi k z)
      Filter.atTop (nhds 1) := by
  have hlog : Filter.Tendsto (fun k : ℕ => Real.log z / Real.log (k : ℝ)) Filter.atTop
      (nhds 0) :=
    Filter.Tendsto.const_div_atTop
      (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))) (Real.log z)
  have h1 : Filter.Tendsto (fun k : ℕ => Work.Stability.chi (Real.log z / Real.log (k : ℝ)))
      Filter.atTop (nhds (Work.Stability.chi 0)) :=
    Work.Stability.chi_continuous.continuousAt.tendsto.comp hlog
  rw [Work.Stability.chi_zero] at h1
  simpa only [Work.FTS.EllipticEst.psiFun] using h1

/-! ## 3. The unconditional `ℝ≥0∞` Agmon inequality -/

/-- The `lintegral` of `ofReal` of a continuous nonnegative function on `(0,∞)`, in terms of the
Bochner integral (when finite). -/
private theorem ofReal_integral_eq_lintegral_Iz {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Ioi 0))
    (hnn : ∀ z, 0 ≤ g z) (hne : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (g z)) ≠ ⊤) :
    ENNReal.ofReal (∫ z in Work.Spaces.Iz, g z) = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (g z) := by
  have haesm : AEStronglyMeasurable g (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    rw [Work.Spaces.Iz, ← MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0 : ℝ))]
    exact hg.aestronglyMeasurable measurableSet_Ioi
  have hint : MeasureTheory.IntegrableOn g Work.Spaces.Iz :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable haesm
      (Filter.Eventually.of_forall hnn)).mp hne
  exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall hnn)


end Work.FTS.EllipticEst.TT
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.RopBlockDecomp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

set_option autoImplicit false

/-- **The `Rop` slot's decomposition into its three pieces.** -/
theorem Rop_block_decomp {α : ℝ} {f Φs : Fn} {E : Fn → Fn} {z θ : ℝ}
    (hz₁ : DifferentiableAt ℝ (fun z' => Work.Construction.PhiTil α f (E f) z' θ) z)
    (hz₂ : DifferentiableAt ℝ (fun z' => Φs z' θ) z)
    (hz₃ : DifferentiableAt ℝ (fun z' => Work.Construction.PhiTil α (Work.Construction.Fstar α)
      Φs z' θ) z)
    (hz₄ : DifferentiableAt ℝ (fun z' => Work.Construction.Theta α (Work.Construction.Fstar α)
      z' θ) z)
    (hθ₁ : DifferentiableAt ℝ (fun θ' => Work.Construction.PhiTil α f (E f) z θ') θ)
    (hθ₂ : DifferentiableAt ℝ (fun θ' => Φs z θ') θ)
    (hθ₃ : DifferentiableAt ℝ (fun θ' => Work.Construction.PhiTil α (Work.Construction.Fstar α)
      Φs z θ') θ)
    (hθ₄ : DifferentiableAt ℝ (fun θ' => Work.Construction.Theta α (Work.Construction.Fstar α)
      z θ') θ) :
    Work.Construction.Rop α (Work.Construction.PhiTil α f (fun z θ => Φs z θ + E f z θ)) z θ
      = Work.Construction.Rop α (Work.Construction.PhiTil α f (E f)) z θ
        + Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Rop α (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ := by
  -- the two function identities
  have hfun₁ : Work.Construction.PhiTil α f (fun z θ => Φs z θ + E f z θ)
      = fun z θ => Work.Construction.PhiTil α f (E f) z θ + Φs z θ := by
    funext z θ
    simp only [Work.Construction.PhiTil, Work.Construction.Theta]
    ring
  have hfun₂ : Φs = fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
      + Work.Construction.Theta α (Work.Construction.Fstar α) z θ := by
    funext z θ
    simp only [Work.Construction.PhiTil, Work.Construction.Theta]
    ring
  rw [hfun₁]
  have h₁ := (Work.FTS.EpsEngine.Rop_Uop_Vop_add (α := α) (z := z) (θ := θ)
    (Ψ₁ := Work.Construction.PhiTil α f (E f)) (Ψ₂ := Φs) hz₁ hz₂ hθ₁ hθ₂).1
  rw [h₁]
  have h₂ := (Work.FTS.EpsEngine.Rop_Uop_Vop_add (α := α) (z := z) (θ := θ)
    (Ψ₁ := Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)
    (Ψ₂ := Work.Construction.Theta α (Work.Construction.Fstar α)) hz₃ hz₄ hθ₃ hθ₄).1
  have hRΦ : Work.Construction.Rop α Φs z θ
      = Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Rop α (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ := by
    conv_lhs => rw [hfun₂]
    exact h₂
  rw [hRΦ]
  ring

end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.H2.SliceSmooth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2

open scoped Real Topology
open Set Filter

/-- The `z`-slices of `f` are `C^∞` on `(-1,∞)`, at every angle `θ ∈ Iθ`, including the two
boundary lines `θ = 0`, `θ = π/2`. -/
def SliceSmooth (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ θ ∈ Work.Spaces.Iθ,
    ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => f z θ) (Set.Ioi (-1))

end Work.FTS.H2
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.slots =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces

set_option autoImplicit false

/-! Independent copies (renamed with a prime) of the two lemmas of `Pieces/rowsAux.lean` that
the `N₄` row proofs use, so that they do not have to import `rowsAux` (which imports the rows). -/






end Work.FTS.Nonlinear.Pieces
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.DiaDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

noncomputable section

namespace Work.FTS.StrongEps.EpsE4Thr

/-- The measure `dz dθ` on the quadrant `Iz × Iθ`. -/
abbrev diaM : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
    (MeasureTheory.volume.restrict Work.Spaces.Iθ)

end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.OpAdd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX.ProfRHSAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## A derivative bound for sums -/


/-! ## Linearity of `ℛ, U, V` in their argument -/




end Work.FTS.StrongEps.EpsRLX.ProfRHSAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.N0_tendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

/-- **Pointwise convergence of `N₀`.**  If every slot `D_z^jD_θ^i` of order `j + i ≤ 1` of the
family `F n` converges at `(z,θ)` to the corresponding slot of `Flim`, the same holds for the
family `w n` with limit `wlim`, and additionally `L₁₂(w n)(z') → L₁₂(wlim)(z')` for every
`z' ∈ Iz` (in particular at `z` itself), then `N₀ α (F n) (w n) z θ` converges to
`N₀ α Flim wlim z θ`.

`N₀` is a fixed algebraic combination of the constant profile `F_*` and of the quantities
`L₁₂(g)(z)`, `g(z,θ)`, `D_zF(z,θ)`, `D_zg(z,θ)` and `∂_θF(z,θ)` (with `F` the first and `g` the
second argument), so the statement is a limit computation.  The only subtlety is `∂_θF`: the
hypotheses control `mixed 0 1 (F n) z θ = D_θ(F n) z θ = sin(2θ)·∂_θ(F n) z θ`, i.e. `∂_θF` only
after multiplication by `sin(2θ)`; but in `N₀` the factor `∂_θF` also carries the coefficient
`(3/(2α))·sin(2θ)·L₁₂(g)(z)`, and grouping the product as
`((3/(2α))·L₁₂(g)(z))·(sin(2θ)·∂_θF)` (a pure ring identity) makes the convergent quantity
`sin(2θ)·∂_θF` the second factor.  No hypothesis on `θ` (or on the smoothness of `Flim`, `wlim`)
is needed beyond the convergence data. -/
theorem N0_tendsto {α : ℝ} {F : ℕ → Work.FTS.Galerkin.Fn} {Flim : Work.FTS.Galerkin.Fn}
    {w : ℕ → Work.FTS.Galerkin.Fn} {wlim : Work.FTS.Galerkin.Fn} {z θ : ℝ}
    (hz : z ∈ Work.Spaces.Iz)
    (hF : ∀ j i : ℕ, j + i ≤ 1 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (F n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i Flim z θ)))
    (hw : ∀ j i : ℕ, j + i ≤ 1 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (w n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i wlim z θ)))
    (hlw : ∀ z' ∈ Work.Spaces.Iz, Filter.Tendsto (fun n : ℕ => Work.Construction.L12 (w n) z')
      Filter.atTop (nhds (Work.Construction.L12 wlim z'))) :
    Filter.Tendsto (fun n : ℕ => Work.Construction.N0 α (F n) (w n) z θ) Filter.atTop
      (nhds (Work.Construction.N0 α Flim wlim z θ)) := by
  -- The slots of order `≤ 1`.
  have hL : Filter.Tendsto (fun n : ℕ => Work.Construction.L12 (w n) z) Filter.atTop
      (nhds (Work.Construction.L12 wlim z)) := hlw z hz
  have hg : Filter.Tendsto (fun n : ℕ => w n z θ) Filter.atTop (nhds (wlim z θ)) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero] using
      hw 0 0 (by norm_num)
  have hZg : Filter.Tendsto (fun n : ℕ => Work.Spaces.Dz (w n) z θ) Filter.atTop
      (nhds (Work.Spaces.Dz wlim z θ)) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
      Work.Spaces.DthIter_zero] using hw 1 0 (by norm_num)
  have hZF : Filter.Tendsto (fun n : ℕ => Work.Spaces.Dz (F n) z θ) Filter.atTop
      (nhds (Work.Spaces.Dz Flim z θ)) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
      Work.Spaces.DthIter_zero] using hF 1 0 (by norm_num)
  -- `∂_θF` is only controlled after multiplication by `sin(2θ)`.
  have hDth : Filter.Tendsto
      (fun n : ℕ => Real.sin (2 * θ) * Work.Spaces.pth (F n) z θ) Filter.atTop
      (nhds (Real.sin (2 * θ) * Work.Spaces.pth Flim z θ)) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero, Work.Spaces.Dth] using hF 0 1 (by norm_num)
  -- The `n`-independent part (`F_*`-terms of `N₀`).
  have hA : Filter.Tendsto (fun _ : ℕ =>
        (3 / (2 * α)) * Real.sin (2 * θ) * Work.Construction.L12 (Work.Construction.Fstar α) z
            * Work.Spaces.pth (Work.Construction.Fstar α) z θ
          - (Real.cos (2 * θ) - Real.sin θ ^ 2)
            * Work.Construction.L12 (Work.Construction.Fstar α) z
            * Work.Spaces.Dz (Work.Construction.Fstar α) z θ)
      Filter.atTop (nhds _) := tendsto_const_nhds
  have hB : Filter.Tendsto (fun n : ℕ =>
        (1 / α) * Work.Construction.L12 (w n) z * (w n z θ))
      Filter.atTop (nhds ((1 / α) * Work.Construction.L12 wlim z * (wlim z θ))) :=
    (hL.const_mul (1 / α)).mul hg
  have hC : Filter.Tendsto (fun n : ℕ =>
        (3 / (2 * α)) * Work.Construction.L12 (w n) z
          * (Real.sin (2 * θ) * Work.Spaces.pth (F n) z θ))
      Filter.atTop (nhds ((3 / (2 * α)) * Work.Construction.L12 wlim z
          * (Real.sin (2 * θ) * Work.Spaces.pth Flim z θ))) :=
    (hL.const_mul (3 / (2 * α))).mul hDth
  have hD : Filter.Tendsto (fun n : ℕ =>
        (Real.cos (2 * θ) - Real.sin θ ^ 2) * Work.Construction.L12 (w n) z
          * Work.Spaces.Dz (F n) z θ)
      Filter.atTop (nhds ((Real.cos (2 * θ) - Real.sin θ ^ 2) * Work.Construction.L12 wlim z
          * Work.Spaces.Dz Flim z θ)) :=
    (tendsto_const_nhds.mul hL).mul hZF
  have hE : Filter.Tendsto (fun n : ℕ =>
        (Real.cos (2 * θ) - Real.sin θ ^ 2) * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.Dz (w n) z θ)
      Filter.atTop (nhds ((Real.cos (2 * θ) - Real.sin θ ^ 2)
          * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.Dz wlim z θ)) :=
    hZg.const_mul ((Real.cos (2 * θ) - Real.sin θ ^ 2)
      * Work.Construction.L12 (Work.Construction.Fstar α) z)
  have hmain := (((hA.add hB).add hC).sub hD).sub hE
  -- `N₀` is the same expression, only the term carrying `∂_θF` is regrouped.
  convert hmain using 1
  · funext n
    simp only [Work.Construction.N0, Work.Construction.s2, Work.Construction.c2m]
    ring
  · congr 1
    simp only [Work.Construction.N0, Work.Construction.s2, Work.Construction.c2m]
    ring

end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS.StrongEps.N_tendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `N_tendsto`: the pointwise limit of `Construction.N`, and the missing hypothesis

`Work.Construction.N α F Φ` is a *bare scalar expression* in the two profiles `F`, `Φ`: expanding
`Rop`, `Uop`, `Vop` and `PhiTil` it only depends on `F`, `Φ` through the eight scalars

`F z θ`, `∂_θF(z,θ)`, `D_zF(z,θ)`, `FK F z`, `Φ̃(z,θ)`, `∂_zΦ̃(z,θ)`, `∂_θΦ̃(z,θ)`,
with `Φ̃ = PhiTil α F Φ`.

Hence, whenever the eight corresponding sequences converge, `N α (F n) (Φ n) z θ` converges to
`N α Flim Φlim z θ` — the content of `NNF_tendsto` below, used to prove the *repaired* statement
`N_tendsto_of_pz_pth`.

**The requested statement `N_tendsto` is FALSE as written** (see the module
`Submission/Work/FTS/StrongEps/NOTES_N_tendsto_FALSE.md` for the counterexample, and
`N_tendsto_of_pz_pth` for the repair): its hypotheses control
`∂_z(F n z'↦…)` and `∂_z(L₁₂(F n))` at `z` *separately*, but `N` contains
`∂_zΦ̃(z,θ) = ∂_z(Φ - (1/(4α)) sin(2θ)·L₁₂(F))(z,θ)`, and the identity
`deriv (f - c·g) z = deriv f z - c·deriv g z` **needs** `f` and `g` to be differentiable at `z`
(`deriv_sub`).  If one of them is not (e.g. a kinked `z`-slice), the two sides genuinely differ,
and the data of the hypotheses does not force differentiability.  The two extra convergence
hypotheses `hPz`, `hPth` of `N_tendsto_of_pz_pth` (convergence of `∂_zΦ̃`, `∂_θΦ̃` themselves)
are exactly what is missing.
-/

namespace Work.FTS.StrongEps

open scoped Real
open Filter

set_option autoImplicit false

noncomputable section

/-- The scalar expression of `N α F Φ z θ`: `fz = F z θ`, `fth = ∂_θF(z,θ)`, `fzD = D_zF(z,θ)`,
`fkv = FK F z`, `pv = Φ̃(z,θ)`, `pzv = ∂_zΦ̃(z,θ)`, `pthv = ∂_θΦ̃(z,θ)` with
`Φ̃ = PhiTil α F Φ`.  It is `rfl`-equal to `N α F Φ z θ` (`N_eq_NNF`). -/
def NNF (α z θ fz fth fzD fkv pv pzv pthv : ℝ) : ℝ :=
  2 * ((2 * Real.sin θ * pv + α * Real.sin θ * z * pzv + Real.cos θ * pthv) / Real.cos θ) * fz
    - 2 * (-3 * pv - α * z * pzv) * fth
    - 2 * α * (pthv - Real.tan θ * pv) * fzD
    - (1 / 2) * Real.sin (2 * θ) * fkv * fth
    - Real.sin θ ^ 2 * fkv * fz

theorem N_eq_NNF (α : ℝ) (F Φ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Construction.N α F Φ z θ
      = NNF α z θ (F z θ) (Work.Spaces.pth F z θ) (Work.Spaces.Dz F z θ)
          (Work.Construction.FK F z)
          (Work.Construction.PhiTil α F Φ z θ)
          (Work.Spaces.pz (Work.Construction.PhiTil α F Φ) z θ)
          (Work.Spaces.pth (Work.Construction.PhiTil α F Φ) z θ) := by
  simp only [Work.Construction.N, Work.Construction.Rop, Work.Construction.Uop,
    Work.Construction.Vop, Work.Construction.s2, NNF]

/-- `NNF` is continuous in its eight scalar arguments, hence preserves limits. -/
theorem NNF_tendsto {α z θ FZ FTH FZD FKV P PZ PTH : ℝ}
    {fz fth fzD fkv pv pzv pthv : ℕ → ℝ}
    (h1 : Filter.Tendsto fz Filter.atTop (nhds FZ))
    (h2 : Filter.Tendsto fth Filter.atTop (nhds FTH))
    (h3 : Filter.Tendsto fzD Filter.atTop (nhds FZD))
    (h4 : Filter.Tendsto fkv Filter.atTop (nhds FKV))
    (h5 : Filter.Tendsto pv Filter.atTop (nhds P))
    (h6 : Filter.Tendsto pzv Filter.atTop (nhds PZ))
    (h7 : Filter.Tendsto pthv Filter.atTop (nhds PTH)) :
    Filter.Tendsto
      (fun n : ℕ => NNF α z θ (fz n) (fth n) (fzD n) (fkv n) (pv n) (pzv n) (pthv n))
      Filter.atTop (nhds (NNF α z θ FZ FTH FZD FKV P PZ PTH)) := by
  have hR : Filter.Tendsto
      (fun n : ℕ => (2 * Real.sin θ * pv n + α * Real.sin θ * z * pzv n + Real.cos θ * pthv n)
        / Real.cos θ) Filter.atTop
      (nhds ((2 * Real.sin θ * P + α * Real.sin θ * z * PZ + Real.cos θ * PTH)
        / Real.cos θ)) :=
    (((h5.const_mul (2 * Real.sin θ)).add (h6.const_mul (α * Real.sin θ * z))).add
      (h7.const_mul (Real.cos θ))).div_const (Real.cos θ)
  have hU : Filter.Tendsto (fun n : ℕ => -3 * pv n - α * z * pzv n) Filter.atTop
      (nhds (-3 * P - α * z * PZ)) :=
    (h5.const_mul (-3)).sub (h6.const_mul (α * z))
  have hV : Filter.Tendsto (fun n : ℕ => pthv n - Real.tan θ * pv n) Filter.atTop
      (nhds (PTH - Real.tan θ * P)) := h7.sub (h5.const_mul (Real.tan θ))
  have hB1 := (hR.const_mul 2).mul h1
  have hB2 := (hU.const_mul 2).mul h2
  have hB3 := (hV.const_mul (2 * α)).mul h3
  have hB4 := (h4.const_mul ((1 / 2) * Real.sin (2 * θ))).mul h2
  have hB5 := (h4.const_mul (Real.sin θ ^ 2)).mul h1
  simpa only [NNF] using (((hB1.sub hB2).sub hB3).sub hB4).sub hB5

/-- **The repaired limit lemma.**  Same hypotheses as `N_tendsto`, plus the two *missing* slot
convergences: the `z`- and `θ`-derivatives of `PhiTil α (F n) (Φ n)` at `(z,θ)` converge to those
of `PhiTil α Flim Φlim`.  (They are what the identities `deriv_sub`/`deriv_const_sub` would
provide from the other hypotheses once the relevant slices are differentiable.)  With them the
statement is a limit computation, carried out by `NNF_tendsto` via `N_eq_NNF`. -/
theorem N_tendsto_of_pz_pth {α : ℝ} {F : ℕ → Work.FTS.Galerkin.Fn} {Flim : Work.FTS.Galerkin.Fn}
    {Φ : ℕ → Work.FTS.Galerkin.Fn} {Φlim : Work.FTS.Galerkin.Fn} {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hF : ∀ j i : ℕ, j + i ≤ 1 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (F n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i Flim z θ)))
    (hΦ : ∀ j i : ℕ, j + i ≤ 1 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (Φ n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i Φlim z θ)))
    (hlF : Filter.Tendsto (fun n : ℕ => Work.Construction.L12 (F n) z) Filter.atTop
      (nhds (Work.Construction.L12 Flim z)))
    (hdF : Filter.Tendsto (fun n : ℕ => deriv (fun z' : ℝ => Work.Construction.L12 (F n) z') z)
      Filter.atTop
      (nhds (deriv (fun z' : ℝ => Work.Construction.L12 Flim z') z)))
    (hFK : Filter.Tendsto (fun n : ℕ => Work.Construction.FK (F n) z) Filter.atTop
      (nhds (Work.Construction.FK Flim z)))
    (hPz : Filter.Tendsto
      (fun n : ℕ => Work.Spaces.pz (Work.Construction.PhiTil α (F n) (Φ n)) z θ) Filter.atTop
      (nhds (Work.Spaces.pz (Work.Construction.PhiTil α Flim Φlim) z θ)))
    (hPth : Filter.Tendsto
      (fun n : ℕ => Work.Spaces.pth (Work.Construction.PhiTil α (F n) (Φ n)) z θ) Filter.atTop
      (nhds (Work.Spaces.pth (Work.Construction.PhiTil α Flim Φlim) z θ))) :
    Filter.Tendsto (fun n : ℕ => Work.Construction.N α (F n) (Φ n) z θ) Filter.atTop
      (nhds (Work.Construction.N α Flim Φlim z θ)) := by
  have hsin : Real.sin (2 * θ) ≠ 0 := by
    have h1 : 0 < 2 * θ := by linarith [hθ.1]
    have h2 : 2 * θ < Real.pi := by linarith [hθ.2]
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2)
  have hF0 : Filter.Tendsto (fun n : ℕ => F n z θ) Filter.atTop (nhds (Flim z θ)) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero]
      using hF 0 0 (by norm_num)
  have hFDz : Filter.Tendsto (fun n : ℕ => Work.Spaces.Dz (F n) z θ) Filter.atTop
      (nhds (Work.Spaces.Dz Flim z θ)) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
      Work.Spaces.DthIter_zero] using hF 1 0 (by norm_num)
  have hFth' : Filter.Tendsto (fun n : ℕ => Real.sin (2 * θ) * Work.Spaces.pth (F n) z θ)
      Filter.atTop (nhds (Real.sin (2 * θ) * Work.Spaces.pth Flim z θ)) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero, Work.Spaces.Dth] using hF 0 1 (by norm_num)
  have hFth : Filter.Tendsto (fun n : ℕ => Work.Spaces.pth (F n) z θ) Filter.atTop
      (nhds (Work.Spaces.pth Flim z θ)) := by
    have h := hFth'.const_mul (Real.sin (2 * θ))⁻¹
    simpa only [← mul_assoc, inv_mul_cancel₀ hsin, one_mul] using h
  have hΦ0 : Filter.Tendsto (fun n : ℕ => Φ n z θ) Filter.atTop (nhds (Φlim z θ)) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero]
      using hΦ 0 0 (by norm_num)
  have hPval : Filter.Tendsto (fun n : ℕ => Work.Construction.PhiTil α (F n) (Φ n) z θ)
      Filter.atTop (nhds (Work.Construction.PhiTil α Flim Φlim z θ)) := by
    have h := hΦ0.sub (hlF.const_mul ((1 / (4 * α)) * Real.sin (2 * θ)))
    simpa only [Work.Construction.PhiTil, Work.Construction.Theta, Work.Construction.s2] using h
  have key := NNF_tendsto (α := α) (z := z) (θ := θ)
    (FZ := Flim z θ) (FTH := Work.Spaces.pth Flim z θ) (FZD := Work.Spaces.Dz Flim z θ)
    (FKV := Work.Construction.FK Flim z)
    (P := Work.Construction.PhiTil α Flim Φlim z θ)
    (PZ := Work.Spaces.pz (Work.Construction.PhiTil α Flim Φlim) z θ)
    (PTH := Work.Spaces.pth (Work.Construction.PhiTil α Flim Φlim) z θ)
    hF0 hFth hFDz hFK hPval hPz hPth
  convert key using 1
  · funext n
    exact N_eq_NNF α (F n) (Φ n) z θ
  · congr 1


/-- `deriv (sin (2·)) θ = 2 cos (2θ)`. -/
theorem hasDerivAt_sin_two (θ : ℝ) :
    HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
  have h := (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)
  simpa [Function.comp_def, mul_comm] using h



end

end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.Stability.ZcutSmoothCompact =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Stability

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The neighbourhood of `SmoothNbhd` -/


/-! ## Vanishing on an open set propagates to all iterated derivatives -/



/-- If `G` vanishes on the open set `V`, then so does every `∂_z^k G`. -/
theorem pzIter_eq_zero_of_vanishOn {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hG : ∀ z θ, (z, θ) ∈ V → G z θ = 0) :
    ∀ k z θ, (z, θ) ∈ V → Work.Spaces.pzIter k G z θ = 0 := by
  intro k
  induction k with
  | zero => exact hG
  | succ k ih =>
    intro z θ hzθ
    rw [Work.Spaces.pzIter_succ]
    show deriv (fun z' => Work.Spaces.pzIter k G z' θ) z = 0
    have hmem : ∀ᶠ z' in 𝓝 z, (z', θ) ∈ V :=
      (continuous_id.prodMk continuous_const).continuousAt (hV.mem_nhds hzθ)
    have hev : (fun z' => Work.Spaces.pzIter k G z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
      filter_upwards [hmem] with z' hz'
      exact ih z' θ hz'
    rw [hev.deriv_eq, deriv_const]


/-- If `G` vanishes on the open set `V`, then so does every `D_z^j G`. -/
theorem DzIter_eq_zero_of_vanishOn {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hG : ∀ z θ, (z, θ) ∈ V → G z θ = 0) :
    ∀ k z θ, (z, θ) ∈ V → Work.Spaces.DzIter k G z θ = 0 := by
  intro k
  induction k with
  | zero => exact hG
  | succ k ih =>
    intro z θ hzθ
    rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz]
    have hp : Work.Spaces.pz (Work.Spaces.DzIter k G) z θ = 0 := by
      show deriv (fun z' => Work.Spaces.DzIter k G z' θ) z = 0
      have hmem : ∀ᶠ z' in 𝓝 z, (z', θ) ∈ V :=
        (continuous_id.prodMk continuous_const).continuousAt (hV.mem_nhds hzθ)
      have hev : (fun z' => Work.Spaces.DzIter k G z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
        filter_upwards [hmem] with z' hz'
        exact ih z' θ hz'
      rw [hev.deriv_eq, deriv_const]
    rw [hp, mul_zero]


/-! ## Vacuity of `SmoothNbhd` together with compact support

`SmoothNbhd` is analyticity on the open, preconnected, unbounded set `U`; a compactly supported
function that is analytic on `U` therefore vanishes identically on `U`. -/


/-! ## Membership of a function vanishing on the domain -/




/-! ## The class membership of the cut-off -/


end Work.Stability
end
end
