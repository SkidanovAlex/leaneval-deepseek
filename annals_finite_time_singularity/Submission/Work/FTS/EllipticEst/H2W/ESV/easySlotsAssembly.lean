import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.H2W.angularAgmon
import Submission.Work.FTS.EllipticEst.H2W.aSliceData
import Submission.Work.FTS.EllipticEst.H2W.ESV.aSliceHonest
import Submission.Work.FTS.EllipticEst.H2W.Norms
import Submission.Work.FTS.EllipticEst.H2W.level0SlicesBridge
import Submission.Work.FTS.EllipticEst.H2W.ESV.HkMem_zero_sliceData
import Submission.Work.FTS.EllipticEst.H2W.eslDth2Bound
import Submission.Work.FTS.EllipticEst.H2W.ESV.eslHkMemPthTwoZsq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# `easySlotsAssembly`: the mixed `D_θ`-slots of `z²∂_z²Ψ` from the level-`0` estimate

Given (as the hypothesis `hL0`) the level-`0` (`η`-weighted) estimate for the *`A`-datum*
`A = z²∂_z²Ψ` — bounding `α⁴|A|_{ℋ⁰} + |∂_θθA|_{ℋ⁰}` by `|D_z²F - D_zF|_{ℋ⁰}` — we deduce the
two *mixed* slots `L2Sq (D_θA · Wt)` and `L2Sq (D_θ²A · Wt)` of the same datum, at the cost of
the level-`2` norm of `F`.

The route is slicewise.  For `z ∈ Iz` write `u = A z ·`; then

* the Agmon-type angular shift `H2W.angularAgmon` gives
  `∫_θ (D_θu)² sin^{-γ} ≤ C_ag (∫_θ (u'')² sin^{-η} + ∫_θ u² sin^{-η})`;
* expanding `D_θ²u = 2 sin(2θ)cos(2θ) u' + sin²(2θ) u''` and using
  `sin^{2-γ} ≤ sin^{-η}`, `sin^{4-γ} ≤ sin^{-η}` gives
  `∫_θ (D_θ²u)² sin^{-γ} ≤ (8C₁+2)(∫_θ (u'')² sin^{-η} + ∫_θ u² sin^{-η})`,
  where `C₁` is the constant of `angularAgmon.deriv_sq_mul_sEta_le`.

Integrating in `z` against `w²` turns the two right-hand sides into
`HkSq α 0 (∂_θθA) + HkSq α 0 A`, and the left-hand sides into the two `L2Sq`-slots of the goal
via the identity `(Wt α z θ)² = w z² · sin(2θ)^{-γ}` on `Iθ`.
-/

/-! ## Slice functionals and elementary weight facts -/

/-- The `θ`-slice functional `z ↦ ∫_θ (D_θ^i A z ·)² sin(2θ)^{-γ}`, the slice of the mixed
(`i ≥ 1`) slots of the `ℋ`-norms. -/
def eslS (α : ℝ) (i : ℕ) (A : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DthIter i A z θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ

/-- The `θ`-slice functional `z ↦ ∫_θ (∂_θ^i A z ·)² sin(2θ)^{-η}`, the slice of the pure
(`i = 0`) slot of the `ℋ⁰`-norm. -/
def eslE (i : ℕ) (A : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter i A z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ

theorem esl_sGam_nonneg {α θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sGam α θ :=
  Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _

/-- On `Iθ` the square of the mixed weight is `w² · sin(2θ)^{-γ}`. -/
theorem esl_Wt_sq {α z θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.Wt α z θ) ^ 2 = (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sGam α θ := by
  have hgam1 : Work.Spaces.gam α ≠ 0 := by rw [Work.Spaces.gam]; linarith
  have hgam2 : Work.Spaces.gam α / 2 ≠ 0 := by
    rw [Work.Spaces.gam]
    intro hc
    have h1 : (0 : ℝ) < 1 := by norm_num
    have h2 : (0 : ℝ) < 2 := by norm_num
    have := div_pos h1 h2
    linarith
  have hkey : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rcases eq_or_lt_of_le (sin_two_nonneg_of_mem_Iθ hθ) with hs | hs
    · rw [← hs, Real.zero_rpow (neg_ne_zero.mpr hgam2), Real.zero_rpow (neg_ne_zero.mpr hgam1)]
      norm_num
    · rw [pow_two, ← Real.rpow_add hs,
        show -(Work.Spaces.gam α / 2) + -(Work.Spaces.gam α / 2) = -(Work.Spaces.gam α) by ring]
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, hkey, Work.FTS.EllipticEst.sGam]

/-- The iterated `D_θ` of a two-variable function at `(z,θ)` is the iterated one-dimensional
`Dth1Iter` of the `θ`-slice. -/
theorem eslDthIter_slice (i : ℕ) (G : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DthIter i G z θ = Work.Elliptic.Dth1Iter i (fun θ' => G z θ') θ := by
  induction i generalizing z θ with
  | zero => rfl
  | succ n ih =>
      simp only [Work.Spaces.DthIter_succ, Work.Elliptic.Dth1Iter_succ, Work.Spaces.Dth,
        Work.Spaces.pth, Work.Elliptic.Dth1]
      have hfun : (fun t => Work.Spaces.DthIter n G z t)
          = (fun t => Work.Elliptic.Dth1Iter n (fun s => G z s) t) := by
        funext t; exact ih z t
      rw [hfun]

/-- The `ℋ⁰`-integrand of `f` integrates in `θ` to `w² · eslE 0 f`. -/
theorem eslHkIntegrand_zero_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ)
      = (Work.Spaces.w z) ^ 2 * eslE 0 f z := by
  have hpt : ∀ θ ∈ Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ
      = (Work.Spaces.w z) ^ 2
          * ((f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    intro θ hθ
    rw [Work.FTS.EllipticEst.H2W.AeDataAofAux.HkIntegrand_zero_eq]
    change (f z θ * Work.FTS.EllipticEst.H2W.Wf z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * ((f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
    rw [mul_pow, Work.FTS.EllipticEst.H2W.Wf_sq_eq (sin_two_nonneg_of_mem_Iθ hθ),
      Work.FTS.EllipticEst.H2W.rho, Work.FTS.EllipticEst.sEta]
    ring
  have h1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ)
      = ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * ((f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
    setIntegral_congr_fun measurableSet_Icc hpt
  rw [h1, MeasureTheory.integral_const_mul]
  rfl

/-- `HkSq α 0 f` is the `z`-integral of `w² eslE 0 f`. -/
theorem eslHkSq_zero_eq (α : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 f
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * eslE 0 f z := by
  rw [Work.Spaces.HkSq]
  exact setIntegral_congr_fun measurableSet_Ici fun z _ => eslHkIntegrand_zero_eq α f z

/-- `L2Sq` of the `i`-th mixed slot of `A` against the weight `Wt` is the `z`-integral of
`w² · eslS α i A`. -/
theorem eslL2SqWt_eq (α : ℝ) (hα : 0 < α) (i : ℕ) (A : ℝ → ℝ → ℝ) :
    Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 0 i A z θ * Work.Spaces.Wt α z θ)
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * eslS α i A z := by
  rw [Work.Spaces.L2Sq]
  refine setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  rw [show (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed 0 i A z θ * Work.Spaces.Wt α z θ) ^ 2)
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
          * ((Work.Spaces.DthIter i A z θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ) from
    setIntegral_congr_fun measurableSet_Icc (fun θ hθ => by
      rw [Work.Spaces.mixed_zero_left, mul_pow, esl_Wt_sq hα hθ]
      ring)]
  rw [MeasureTheory.integral_const_mul]
  rfl

/-- The `A`-datum of the reduction: `A = z² ∂_z²Ψ`. -/
def eslA (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ

/-- Pointwise domination of the `ℋ⁰`-integrand of `g` by the `ℋ²`-integrand of `F` transfers to
the integrated inequality. -/
theorem eslHkSqZero_le_of_pointwise (α : ℝ) (C : ℝ) (hC : 0 ≤ C) {F g : ℝ → ℝ → ℝ}
    (hF : Work.Spaces.HkMem α 2 F)
    (h : ∀ z θ, Work.Spaces.HkIntegrand α 0 g z θ ≤ C * Work.Spaces.HkIntegrand α 2 F z θ) :
    Work.Spaces.HkSq α 0 g ≤ C * Work.Spaces.HkSq α 2 F := by
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_mono_of_nonneg
    (f := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
    (g := fun z => C * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 2 F z θ)
    ?_ ?_ ?_
  · exact Eventually.of_forall fun z =>
      setIntegral_nonneg measurableSet_Icc
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 0 g z θ)
  · exact hF.2.const_mul C
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    have hin : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, C * Work.Spaces.HkIntegrand α 2 F z θ :=
      MeasureTheory.integral_mono_of_nonneg
        (f := fun θ => Work.Spaces.HkIntegrand α 0 g z θ)
        (g := fun θ => C * Work.Spaces.HkIntegrand α 2 F z θ)
        (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 0 g z θ)
        ((hF.1 z hz).const_mul C) (Eventually.of_forall fun θ => h z θ)
    rwa [MeasureTheory.integral_const_mul] at hin

/-- `HkSq α 0` of the difference `D_z²F - D_zF` is bounded by `4 HkSq α 2 F`. -/
theorem eslHkSqZero_sub_le (α : ℝ) (F : ℝ → ℝ → ℝ) (hF : Work.Spaces.HkMem α 2 F) :
    Work.Spaces.HkSq α 0 (fun z θ => Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ)
      ≤ 4 * Work.Spaces.HkSq α 2 F := by
  refine eslHkSqZero_le_of_pointwise α 4 (by norm_num) hF fun z θ => ?_
  rw [Work.FTS.EllipticEst.H2W.AeDataAofAux.HkIntegrand_zero_eq]
  obtain ⟨h1, h2⟩ : (Work.Spaces.DzIter 2 F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ Work.Spaces.HkIntegrand α 2 F z θ
      ∧ (Work.Spaces.DzIter 1 F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ Work.Spaces.HkIntegrand α 2 F z θ :=
    ⟨Work.Spaces.sq_le_HkIntegrand_z α 2 F z θ 2 (by norm_num),
      Work.Spaces.sq_le_HkIntegrand_z α 2 F z θ 1 (by norm_num)⟩
  set W := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hW
  set a := Work.Spaces.DzIter 2 F z θ with ha
  set b := Work.Spaces.DzIter 1 F z θ with hb
  set Hk := Work.Spaces.HkIntegrand α 2 F z θ with hHk
  have hsq : (a - b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a + b)]
  calc ((a - b) * W) ^ 2 = ((a - b) ^ 2) * W ^ 2 := by ring
    _ ≤ (2 * a ^ 2 + 2 * b ^ 2) * W ^ 2 :=
        mul_le_mul_of_nonneg_right hsq (sq_nonneg W)
    _ = 2 * (a * W) ^ 2 + 2 * (b * W) ^ 2 := by ring
    _ ≤ 2 * Hk + 2 * Hk := by linarith
    _ = 4 * Hk := by ring

/-- Positivity of the `θ`-integrand of `eslE`. -/
theorem eslE_nonneg {i : ℕ} {A : ℝ → ℝ → ℝ} {z : ℝ} {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ (Work.Spaces.pthIter i A z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
  mul_nonneg (sq_nonneg _) (sEta_nonneg_of_mem_Iθ hθ)

/-- **The mixed `D_θ`-slots of `z²∂_z²Ψ` from the level-`0` estimate for the `A`-datum.**

The analytic inputs are the four hypotheses `hag` (the Agmon angular shift), `hu1` (the weighted
`u'`-bound of `angularAgmon.deriv_sq_mul_sEta_le`), `hdth2` (the pointwise second-order bound
`D_θ²u = 2 sin cos u' + sin² u''`) and `hMemP` (`ℋ⁰`-honesty of `∂_θθ(z²∂_z²Ψ)`).  The content
is the slicewise assembly and the two `z`-integrals. -/
theorem esl_lhs_bound
    (Cag C1 : ℝ) (hCag : 0 ≤ Cag) (hC1 : 0 ≤ C1)
    (hag : ∀ (α : ℝ) (u : ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      (∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) → u 0 = 0 → u (Real.pi / 2) = 0 →
      MeasureTheory.IntegrableOn (fun θ => (deriv (fun t => deriv u t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
      (∫ θ in Work.Spaces.Iθ, (Work.Elliptic.Dth1Iter 1 u θ) ^ 2
          * Work.FTS.EllipticEst.sGam α θ)
        ≤ Cag * ((∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ)
            + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
    (hu1 : ∀ (u : ℝ → ℝ),
      ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv (fun t => deriv u t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ C1 * ((∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
            + (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ)))
    (hdth2 : ∀ (α : ℝ) (u : ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)) →
      ∀ θ ∈ Work.Spaces.Iθ,
        (Work.Elliptic.Dth1Iter 2 u θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ
          ≤ 8 * ((deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
            + 2 * ((deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
    (hMemP : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      Work.Spaces.HkMem α 0
        (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
        Work.Spaces.L2Sq (fun z θ =>
            Work.Spaces.mixed 0 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
              * Work.Spaces.Wt α z θ)
          + Work.Spaces.L2Sq (fun z θ =>
            Work.Spaces.mixed 0 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
              * Work.Spaces.Wt α z θ)
        ≤ C * (Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
            + Work.Spaces.HkSq α 0
                (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))) := by
  refine ⟨2 * (Cag + (8 * C1 + 2)), by positivity, ?_⟩
  intro α F Ψ hα hα4 h
  have haData := aSliceData α F Ψ hα hα4 h
  have haHon := aSliceHonest α F Ψ hα hα4 h
  have hMemA : Work.Spaces.HkMem α 0 (eslA Ψ) :=
    (HkMem_zero_sliceData α F Ψ h 0 (by norm_num)).2.1
  have hMemP' : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 (eslA Ψ)) := hMemP α F Ψ h
  have hIntK : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * eslE 0 (eslA Ψ) z) Work.Spaces.Iz :=
    hMemA.2.congr_fun (fun z _ => eslHkIntegrand_zero_eq α (eslA Ψ) z) measurableSet_Ici
  have hIntJ : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2
        * eslE 0 (Work.Spaces.pthIter 2 (eslA Ψ)) z) Work.Spaces.Iz :=
    hMemP'.2.congr_fun
      (fun z _ => eslHkIntegrand_zero_eq α (Work.Spaces.pthIter 2 (eslA Ψ)) z) measurableSet_Ici
  -- ## the first mixed slot
  have hslice1 : ∀ z ∈ Work.Spaces.Iz, eslS α 1 (eslA Ψ) z
      ≤ (Cag + (8 * C1 + 2)) * (eslE 0 (eslA Ψ) z
          + eslE 0 (Work.Spaces.pthIter 2 (eslA Ψ)) z) := by
    intro z hz
    obtain ⟨hsm, h0, hpi⟩ := haData.1 z hz
    have h2 := haHon z hz
    have hb : (∫ θ in Work.Spaces.Iθ,
          (Work.Elliptic.Dth1Iter 1 (fun θ' => eslA Ψ z θ') θ) ^ 2
            * Work.FTS.EllipticEst.sGam α θ)
        ≤ Cag * ((∫ θ in Work.Spaces.Iθ,
              (deriv (fun t => deriv (fun θ' => eslA Ψ z θ') t) θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)
            + (∫ θ in Work.Spaces.Iθ, (eslA Ψ z θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)) :=
      hag α (fun θ => eslA Ψ z θ) hα hα4 hsm h0 hpi h2
    have hL : eslS α 1 (eslA Ψ) z
        = ∫ θ in Work.Spaces.Iθ,
            (Work.Elliptic.Dth1Iter 1 (fun θ' => eslA Ψ z θ') θ) ^ 2
              * Work.FTS.EllipticEst.sGam α θ := by
      rw [eslS]
      refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
      rw [eslDthIter_slice]
    have hJ : (∫ θ in Work.Spaces.Iθ,
          (deriv (fun t => deriv (fun θ' => eslA Ψ z θ') t) θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ)
        = eslE 0 (Work.Spaces.pthIter 2 (eslA Ψ)) z := by
      simp only [eslE, Work.Spaces.pthIter_zero]
      refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
      simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
    have hK : (∫ θ in Work.Spaces.Iθ, (eslA Ψ z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) = eslE 0 (eslA Ψ) z := by
      simp only [eslE, Work.Spaces.pthIter_zero]
    rw [hJ, hK] at hb
    have hnn : 0 ≤ eslE 0 (eslA Ψ) z + eslE 0 (Work.Spaces.pthIter 2 (eslA Ψ)) z :=
      add_nonneg
        (setIntegral_nonneg measurableSet_Icc (fun θ hθ => eslE_nonneg hθ))
        (setIntegral_nonneg measurableSet_Icc (fun θ hθ => eslE_nonneg hθ))
    have hswap : Cag * (eslE 0 (Work.Spaces.pthIter 2 (eslA Ψ)) z + eslE 0 (eslA Ψ) z)
        = Cag * (eslE 0 (eslA Ψ) z + eslE 0 (Work.Spaces.pthIter 2 (eslA Ψ)) z) := by ring
    calc eslS α 1 (eslA Ψ) z
        = ∫ θ in Work.Spaces.Iθ,
            (Work.Elliptic.Dth1Iter 1 (fun θ' => eslA Ψ z θ') θ) ^ 2
              * Work.FTS.EllipticEst.sGam α θ := hL
      _ ≤ Cag * (eslE 0 (Work.Spaces.pthIter 2 (eslA Ψ)) z + eslE 0 (eslA Ψ) z) := hb
      _ = Cag * (eslE 0 (eslA Ψ) z + eslE 0 (Work.Spaces.pthIter 2 (eslA Ψ)) z) := hswap
      _ ≤ (Cag + (8 * C1 + 2)) * (eslE 0 (eslA Ψ) z
            + eslE 0 (Work.Spaces.pthIter 2 (eslA Ψ)) z) :=
          mul_le_mul_of_nonneg_right (by linarith : Cag ≤ Cag + (8 * C1 + 2)) hnn
  -- ## the second mixed slot
  have hslice2 : ∀ z ∈ Work.Spaces.Iz, eslS α 2 (eslA Ψ) z
      ≤ (Cag + (8 * C1 + 2)) * (eslE 0 (eslA Ψ) z
          + eslE 0 (Work.Spaces.pthIter 2 (eslA Ψ)) z) := by
    intro z hz
    obtain ⟨hsm, h0, hpi⟩ := haData.1 z hz
    have h2 : MeasureTheory.IntegrableOn
        (fun θ => (deriv (fun t => deriv (fun θ' => eslA Ψ z θ') t) θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := haHon z hz
    have hu2 : ContDiffOn ℝ 2 (fun θ => eslA Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) := hsm 2
    have h0' : MeasureTheory.IntegrableOn
        (fun θ => (eslA Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
      u_sq_mul_sEta_integrable hu2 h2
    have h1int : MeasureTheory.IntegrableOn
        (fun θ => (deriv (fun θ' => eslA Ψ z θ') θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ :=
      (hu1 (fun θ => eslA Ψ z θ) hu2 h0' h2).1
    have h1bd : (∫ θ in Work.Spaces.Iθ,
          (deriv (fun θ' => eslA Ψ z θ') θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ C1 * ((∫ θ in Work.Spaces.Iθ, (eslA Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
            + (∫ θ in Work.Spaces.Iθ,
                (deriv (fun t => deriv (fun θ' => eslA Ψ z θ') t) θ) ^ 2
                  * Work.FTS.EllipticEst.sEta θ)) :=
      (hu1 (fun θ => eslA Ψ z θ) hu2 h0' h2).2
    have hL : eslS α 2 (eslA Ψ) z
        = ∫ θ in Work.Spaces.Iθ,
            (Work.Elliptic.Dth1Iter 2 (fun θ' => eslA Ψ z θ') θ) ^ 2
              * Work.FTS.EllipticEst.sGam α θ := by
      rw [eslS]
      refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
      rw [eslDthIter_slice]
    have hrhsInt : MeasureTheory.IntegrableOn
        (fun θ => 8 * ((deriv (fun θ' => eslA Ψ z θ') θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + 2 * ((deriv (fun t => deriv (fun θ' => eslA Ψ z θ') t) θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ)) Work.Spaces.Iθ :=
      (h1int.const_mul 8).add (h2.const_mul 2)
    have hstep : (∫ θ in Work.Spaces.Iθ,
          (Work.Elliptic.Dth1Iter 2 (fun θ' => eslA Ψ z θ') θ) ^ 2
            * Work.FTS.EllipticEst.sGam α θ)
        ≤ ∫ θ in Work.Spaces.Iθ, (8 * ((deriv (fun θ' => eslA Ψ z θ') θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ)
            + 2 * ((deriv (fun t => deriv (fun θ' => eslA Ψ z θ') t) θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ)) := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ hrhsInt ?_
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        exact mul_nonneg (sq_nonneg _) (esl_sGam_nonneg hθ)
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
        exact hdth2 α (fun θ' => eslA Ψ z θ') hα hα4 hu2 θ hθ
    have hsplit : (∫ θ in Work.Spaces.Iθ, (8 * ((deriv (fun θ' => eslA Ψ z θ') θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ)
            + 2 * ((deriv (fun t => deriv (fun θ' => eslA Ψ z θ') t) θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ)))
        = 8 * (∫ θ in Work.Spaces.Iθ, (deriv (fun θ' => eslA Ψ z θ') θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ)
          + 2 * (∫ θ in Work.Spaces.Iθ,
              (deriv (fun t => deriv (fun θ' => eslA Ψ z θ') t) θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ) := by
      rw [MeasureTheory.integral_add (h1int.const_mul 8) (h2.const_mul 2),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    have hK : (∫ θ in Work.Spaces.Iθ, (eslA Ψ z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) = eslE 0 (eslA Ψ) z := by
      simp only [eslE, Work.Spaces.pthIter_zero]
    have hJ : (∫ θ in Work.Spaces.Iθ,
          (deriv (fun t => deriv (fun θ' => eslA Ψ z θ') t) θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ)
        = eslE 0 (Work.Spaces.pthIter 2 (eslA Ψ)) z := by
      simp only [eslE, Work.Spaces.pthIter_zero]
      refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
      simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
    rw [hK, hJ] at h1bd
    rw [hJ] at hsplit
    rw [hsplit] at hstep
    have hnn : 0 ≤ eslE 0 (eslA Ψ) z + eslE 0 (Work.Spaces.pthIter 2 (eslA Ψ)) z :=
      add_nonneg
        (setIntegral_nonneg measurableSet_Icc (fun θ hθ => eslE_nonneg hθ))
        (setIntegral_nonneg measurableSet_Icc (fun θ hθ => eslE_nonneg hθ))
    have hKnn : 0 ≤ eslE 0 (eslA Ψ) z :=
      setIntegral_nonneg measurableSet_Icc (fun θ hθ => eslE_nonneg hθ)
    refine le_trans hstep ?_
    calc 8 * (∫ θ in Work.Spaces.Iθ, (deriv (fun θ' => eslA Ψ z θ') θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ)
          + 2 * eslE 0 (Work.Spaces.pthIter 2 (eslA Ψ)) z
        ≤ 8 * (C1 * (eslE 0 (eslA Ψ) z + eslE 0 (Work.Spaces.pthIter 2 (eslA Ψ)) z))
          + 2 * eslE 0 (Work.Spaces.pthIter 2 (eslA Ψ)) z := by
          have hh := mul_le_mul_of_nonneg_left h1bd (by norm_num : (0:ℝ) ≤ 8)
          linarith
      _ = (8 * C1 + 2) * (eslE 0 (eslA Ψ) z + eslE 0 (Work.Spaces.pthIter 2 (eslA Ψ)) z)
          - 2 * eslE 0 (eslA Ψ) z := by ring
      _ ≤ (8 * C1 + 2) * (eslE 0 (eslA Ψ) z
            + eslE 0 (Work.Spaces.pthIter 2 (eslA Ψ)) z) := by linarith
      _ ≤ (Cag + (8 * C1 + 2)) * (eslE 0 (eslA Ψ) z
            + eslE 0 (Work.Spaces.pthIter 2 (eslA Ψ)) z) :=
          mul_le_mul_of_nonneg_right (by linarith : 8 * C1 + 2 ≤ Cag + (8 * C1 + 2)) hnn
  -- ## the value of the majorant integral
  have hval : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * ((Cag + (8 * C1 + 2)) * (eslE 0 (eslA Ψ) z
            + eslE 0 (Work.Spaces.pthIter 2 (eslA Ψ)) z)))
      = (Cag + (8 * C1 + 2)) * (Work.Spaces.HkSq α 0 (eslA Ψ)
          + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (eslA Ψ))) := by
    have h1 : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * ((Cag + (8 * C1 + 2)) * (eslE 0 (eslA Ψ) z
              + eslE 0 (Work.Spaces.pthIter 2 (eslA Ψ)) z)))
        = (Cag + (8 * C1 + 2)) * ∫ z in Work.Spaces.Iz,
            ((Work.Spaces.w z) ^ 2 * eslE 0 (eslA Ψ) z
              + (Work.Spaces.w z) ^ 2 * eslE 0 (Work.Spaces.pthIter 2 (eslA Ψ)) z) := by
      rw [show (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * ((Cag + (8 * C1 + 2)) * (eslE 0 (eslA Ψ) z
                + eslE 0 (Work.Spaces.pthIter 2 (eslA Ψ)) z)))
          = ∫ z in Work.Spaces.Iz, (Cag + (8 * C1 + 2))
              * ((Work.Spaces.w z) ^ 2 * eslE 0 (eslA Ψ) z
                + (Work.Spaces.w z) ^ 2 * eslE 0 (Work.Spaces.pthIter 2 (eslA Ψ)) z) from
        setIntegral_congr_fun measurableSet_Ici (fun z _ => by ring)]
      rw [MeasureTheory.integral_const_mul]
    rw [h1]
    have h2 : (∫ z in Work.Spaces.Iz, ((Work.Spaces.w z) ^ 2 * eslE 0 (eslA Ψ) z
          + (Work.Spaces.w z) ^ 2 * eslE 0 (Work.Spaces.pthIter 2 (eslA Ψ)) z))
        = (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * eslE 0 (eslA Ψ) z)
          + ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
              * eslE 0 (Work.Spaces.pthIter 2 (eslA Ψ)) z :=
      MeasureTheory.integral_add hIntK hIntJ
    rw [h2, ← eslHkSq_zero_eq α (eslA Ψ),
      ← eslHkSq_zero_eq α (Work.Spaces.pthIter 2 (eslA Ψ))]
  -- ## the two slots
  have hgInt : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
      * ((Cag + (8 * C1 + 2)) * (eslE 0 (eslA Ψ) z
          + eslE 0 (Work.Spaces.pthIter 2 (eslA Ψ)) z))) Work.Spaces.Iz := by
    have hsum : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * eslE 0 (eslA Ψ) z
        + (Work.Spaces.w z) ^ 2 * eslE 0 (Work.Spaces.pthIter 2 (eslA Ψ)) z) Work.Spaces.Iz :=
      (hIntK.add hIntJ).congr (Eventually.of_forall fun z => rfl)
    have h3 : MeasureTheory.IntegrableOn (fun z => (Cag + (8 * C1 + 2))
        * ((Work.Spaces.w z) ^ 2 * eslE 0 (eslA Ψ) z
          + (Work.Spaces.w z) ^ 2 * eslE 0 (Work.Spaces.pthIter 2 (eslA Ψ)) z))
        Work.Spaces.Iz := hsum.const_mul _
    refine h3.congr_fun (fun z _ => ?_) measurableSet_Ici
    ring
  have hI1 : Work.Spaces.L2Sq (fun z θ =>
        Work.Spaces.mixed 0 1 (eslA Ψ) z θ * Work.Spaces.Wt α z θ)
      ≤ (Cag + (8 * C1 + 2)) * (Work.Spaces.HkSq α 0 (eslA Ψ)
          + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (eslA Ψ))) := by
    rw [eslL2SqWt_eq α hα 1 (eslA Ψ)]
    refine le_trans (MeasureTheory.integral_mono_of_nonneg ?_ hgInt ?_) (le_of_eq hval)
    · exact Eventually.of_forall fun z => mul_nonneg (sq_nonneg _)
        (setIntegral_nonneg measurableSet_Icc
          (fun θ hθ => mul_nonneg (sq_nonneg _) (esl_sGam_nonneg hθ)))
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      exact mul_le_mul_of_nonneg_left (hslice1 z hz) (sq_nonneg _)
  have hI2 : Work.Spaces.L2Sq (fun z θ =>
        Work.Spaces.mixed 0 2 (eslA Ψ) z θ * Work.Spaces.Wt α z θ)
      ≤ (Cag + (8 * C1 + 2)) * (Work.Spaces.HkSq α 0 (eslA Ψ)
          + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (eslA Ψ))) := by
    rw [eslL2SqWt_eq α hα 2 (eslA Ψ)]
    refine le_trans (MeasureTheory.integral_mono_of_nonneg ?_ hgInt ?_) (le_of_eq hval)
    · exact Eventually.of_forall fun z => mul_nonneg (sq_nonneg _)
        (setIntegral_nonneg measurableSet_Icc
          (fun θ hθ => mul_nonneg (sq_nonneg _) (esl_sGam_nonneg hθ)))
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      exact mul_le_mul_of_nonneg_left (hslice2 z hz) (sq_nonneg _)
  change Work.Spaces.L2Sq (fun z θ =>
        Work.Spaces.mixed 0 1 (eslA Ψ) z θ * Work.Spaces.Wt α z θ)
      + Work.Spaces.L2Sq (fun z θ =>
        Work.Spaces.mixed 0 2 (eslA Ψ) z θ * Work.Spaces.Wt α z θ)
      ≤ 2 * (Cag + (8 * C1 + 2)) * (Work.Spaces.HkSq α 0 (eslA Ψ)
          + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (eslA Ψ)))
  linarith

theorem easySlotsAssembly
    (hL0 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
        α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + Work.Spaces.HkSq α 0
              (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
        ≤ C * Work.Spaces.HkSq α 0
              (fun z θ => Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
        α ^ 4 * (Work.Spaces.L2Sq (fun z θ =>
            Work.Spaces.mixed 0 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
              * Work.Spaces.Wt α z θ)
          + Work.Spaces.L2Sq (fun z θ =>
            Work.Spaces.mixed 0 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
              * Work.Spaces.Wt α z θ))
        ≤ C * Work.Spaces.HkSq α 2 F := by
  obtain ⟨C₀, hC₀pos, hL0'⟩ := hL0
  obtain ⟨Cag, hCagpos, hag₀⟩ := Work.FTS.EllipticEst.H2W.angularAgmon
  obtain ⟨Cp, hCppos, hpiv⟩ := Work.FTS.EllipticEst.H2W.pivotBound
  have hC1nn : (0 : ℝ) ≤ 20000 * Cp + 10000 * Real.pi + 1 := by positivity
  obtain ⟨C, hCpos, hCbd⟩ := esl_lhs_bound Cag (20000 * Cp + 10000 * Real.pi + 1)
    (le_of_lt hCagpos) hC1nn hag₀
    (Work.FTS.EllipticEst.H2W.deriv_sq_mul_sEta_le Cp hCppos hpiv)
    (fun α u hα hα4 hu => Work.FTS.EllipticEst.H2W.eslDth2Bound α hα hα4 u hu)
    (fun α F Ψ hh => Work.FTS.EllipticEst.H2W.eslHkMemPthTwoZsq α hh)
  refine ⟨C * C₀ * 4, by positivity, ?_⟩
  intro α F Ψ hα hα4 h
  have h1 := hCbd α F Ψ hα hα4 h
  have h2 : α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      + Work.Spaces.HkSq α 0
          (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
      ≤ C₀ * Work.Spaces.HkSq α 0
          (fun z θ => Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ) :=
    hL0' α F Ψ hα hα4 h
  have h3 := eslHkSqZero_sub_le α F h.memF
  have hCnn : 0 ≤ C := le_of_lt hCpos
  have hC₀nn : 0 ≤ C₀ := le_of_lt hC₀pos
  have hα4le : α ^ 4 ≤ 1 := pow_le_one₀ (le_of_lt hα) (by linarith)
  have hAnnn : 0 ≤ Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    setIntegral_nonneg measurableSet_Ici fun z _ =>
      setIntegral_nonneg measurableSet_Icc fun θ _ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ
  have hWnn : 0 ≤ Work.Spaces.HkSq α 0
      (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
    setIntegral_nonneg measurableSet_Ici fun z _ =>
      setIntegral_nonneg measurableSet_Icc fun θ _ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ
  have hstep1 : α ^ 4 * (Work.Spaces.L2Sq (fun z θ =>
          Work.Spaces.mixed 0 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
            * Work.Spaces.Wt α z θ)
        + Work.Spaces.L2Sq (fun z θ =>
          Work.Spaces.mixed 0 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
            * Work.Spaces.Wt α z θ))
      ≤ α ^ 4 * (C * (Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + Work.Spaces.HkSq α 0
              (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)))) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have hstep2 : α ^ 4 * (C * (Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + Work.Spaces.HkSq α 0
              (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))))
      = C * (α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + α ^ 4 * Work.Spaces.HkSq α 0
              (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))) := by
    ring
  have hstep3 : C * (α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + α ^ 4 * Work.Spaces.HkSq α 0
              (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)))
      ≤ C * (α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + Work.Spaces.HkSq α 0
              (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))) := by
    have hWW : α ^ 4 * Work.Spaces.HkSq α 0
          (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
        ≤ Work.Spaces.HkSq α 0
            (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) := by
      nlinarith [hα4le, hWnn]
    nlinarith [hCnn, hWW]
  have hstep4 : C * (α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + Work.Spaces.HkSq α 0
              (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)))
      ≤ C * (C₀ * Work.Spaces.HkSq α 0
          (fun z θ => Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ)) :=
    mul_le_mul_of_nonneg_left h2 hCnn
  have hstep5 : C * (C₀ * Work.Spaces.HkSq α 0
          (fun z θ => Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ))
      ≤ C * (C₀ * (4 * Work.Spaces.HkSq α 2 F)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hC₀nn) hCnn
  calc α ^ 4 * (Work.Spaces.L2Sq (fun z θ =>
          Work.Spaces.mixed 0 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
            * Work.Spaces.Wt α z θ)
        + Work.Spaces.L2Sq (fun z θ =>
          Work.Spaces.mixed 0 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
            * Work.Spaces.Wt α z θ))
      ≤ α ^ 4 * (C * (Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + Work.Spaces.HkSq α 0
              (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)))) := hstep1
    _ = C * (α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + α ^ 4 * Work.Spaces.HkSq α 0
              (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))) := hstep2
    _ ≤ C * (α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + Work.Spaces.HkSq α 0
              (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))) := hstep3
    _ ≤ C * (C₀ * Work.Spaces.HkSq α 0
          (fun z θ => Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ)) := hstep4
    _ ≤ C * (C₀ * (4 * Work.Spaces.HkSq α 2 F)) := hstep5
    _ = C * C₀ * 4 * Work.Spaces.HkSq α 2 F := by ring

end

end Work.FTS.EllipticEst.H2W
