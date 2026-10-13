import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.TT.interpGammaDefs
import Submission.Work.FTS.EllipticEst.TT.interpGamma_core_compact
import Submission.Work.FTS.EllipticEst.TT.sliceIBPLight
import Submission.Work.FTS.EllipticEst.TT.radialIBPOpen
import Submission.Work.FTS.EllipticEst.TT.sliceRate_light

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

/-!
# `TT.interpGamma_core`

The interpolation core of `TT.interpGamma`: for `α ∈ (0,1/4]` and a datum `G` which is `C^∞` on
the *open* quadrant, vanishes at the two angular endpoints and has the three honest
`ℋ⁰`-slots (`D_z²G`, `∂_θ²G`, `D_zG`),

  `Xint α G ≤ C (√(DDint α G · TTint α G) + HkSq α 0 (DzIter 1 G))`

with `Xint = ∫∫(D_z∂_θG)²w²σ_a`, `DDint = ∫∫(D_z²G + bD_zG)²w²σ_a`,
`TTint = ∫∫(∂_θ²G)²w²σ_a` and `σ_a = sin(2θ)^{2-γ(α)}`, `σ_η = sin(2θ)^{-η}`.

Route and status: see `NOTES_interpGamma_core.md` in this directory.  Proved here (all
sorry-free, axioms `[propext, Classical.choice, Quot.sound]`):

* the **per-θ radial T-adjoint on `(0,∞)` with its explicit flux hypothesis**
  (`radial_ibp_Ioi`, with `LzComb`, `tFlux`, `hasDerivAt_tFlux`) — the flux hypothesis is not
  removable: the kernel direction `D_zh = c z³/(1+z)⁴` of `L_z` is admissible and makes the flux
  diverge;
* the elementary weight comparisons (`σ_η ≥ 1` a.e. and `σ_a ≤ σ_η` a.e. on `Iθ`), hence the
  domination of the `σ_a`-slot and of the unweighted slot by the corresponding `ℋ⁰`-slot
  (`integral_sigA_le_HkSq`, `integral_plain_le_HkSq`, `TTint_le_HkSq`), and `|b| ≤ 3` on `z ≥ 0`.

What remains is the jump-endpoint analysis of the flux term `Φ` of the reduction
`Xint = ⟨L_zG,∂_θ²G⟩ + Φ` recorded in the NOTES.
-/

/-! ## The radial T-adjoint on `(0,∞)`, with its explicit flux hypothesis

The T-adjoint identity

  `∫_0^∞ w² (D_zF)(D_zH) = -∫_0^∞ w² (D_z²F + b D_zF) H`

is **false without a flux condition**: the reviewer refutation of the one-function comparison
`∫w²(D_zh)² ≤ C∫w²(L_zh)²` exhibits the kernel direction `D_zh = c z³/(1+z)⁴` of `L_z`, along
which the flux `Φ(z) = w(z)² z H(z) (D_zF)(z)` *diverges* (for `L_zh = 0` one has
`Φ' = w²(D_zh)² ≥ 0`).  The statement therefore carries the flux vanishing at the two ends
explicitly, in exactly the form that the slices of the elliptic problem must supply.
-/

/-- The T-adjoint combination `D_z²F + b D_zF = z (D_zF)' + b (D_zF)` of the radial IBP. -/
def LzComb (F : ℝ → ℝ) (z : ℝ) : ℝ :=
  z * deriv (fun y : ℝ => y * deriv F y) z + bcoefR z * (z * deriv F z)

/-- The flux of the radial T-adjoint: `Φ(z) = w(z)² z H(z) (z F'(z))`. -/
def tFlux (F H : ℝ → ℝ) (z : ℝ) : ℝ := (Work.Spaces.w z) ^ 2 * z * H z * (z * deriv F z)

@[simp] theorem LzComb_apply (F : ℝ → ℝ) (z : ℝ) :
    LzComb F z = z * deriv (fun y : ℝ => y * deriv F y) z + bcoefR z * (z * deriv F z) := rfl

@[simp] theorem tFlux_apply (F H : ℝ → ℝ) (z : ℝ) :
    tFlux F H z = (Work.Spaces.w z) ^ 2 * z * H z * (z * deriv F z) := rfl

/-- **The pointwise derivative of the T-adjoint flux** on `(0,∞)`:
`Φ'(z) = w²(D_zF)(D_zH) + w²(D_z²F + b D_zF) H`. -/
theorem hasDerivAt_tFlux {F H : ℝ → ℝ} (hF : ContDiffOn ℝ 2 F (Set.Ioi (0 : ℝ)))
    (hH : ContDiffOn ℝ 1 H (Set.Ioi (0 : ℝ))) :
    ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (tFlux F H)
      ((Work.Spaces.w z) ^ 2 * (z * deriv F z) * (z * deriv H z)
        + (Work.Spaces.w z) ^ 2 * LzComb F z * H z) z := by
  intro z hz
  have hz0 : (0 : ℝ) < z := hz
  -- the three factors
  have hA : HasDerivAt (fun y : ℝ => (Work.Spaces.w y) ^ 2 * y)
      ((Work.Spaces.w z) ^ 2 * bcoefR z) z := deriv_zw_sq z hz0
  have hB : HasDerivAt H (deriv H z) z :=
    ((hH.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)).hasDerivAt
  have hC1 : ContDiffOn ℝ 1 (fun y : ℝ => y * deriv F y) (Set.Ioi (0 : ℝ)) :=
    contDiffOn_id.mul (hF.deriv_of_isOpen isOpen_Ioi (by norm_num))
  have hC : HasDerivAt (fun y : ℝ => y * deriv F y)
      (deriv (fun y : ℝ => y * deriv F y) z) z :=
    ((hC1.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)).hasDerivAt
  have hmain : HasDerivAt (tFlux F H)
      (((Work.Spaces.w z) ^ 2 * bcoefR z * H z + ((Work.Spaces.w z) ^ 2 * z) * deriv H z)
          * (z * deriv F z)
        + ((Work.Spaces.w z) ^ 2 * z * H z) * deriv (fun y : ℝ => y * deriv F y) z) z := by
    have h := (hA.mul hB).mul hC
    refine h.congr_of_eventuallyEq ?_
    filter_upwards with y
    simp only [Pi.mul_apply, tFlux_apply]
  refine hmain.congr_deriv ?_
  simp only [LzComb_apply]
  ring_nf

/-- **The radial T-adjoint on `(0,∞)`, with the explicit flux hypothesis.**  For `F` of class `C²`
and `H` of class `C¹` on `(0,∞)`, with the two sides integrable and the flux `Φ(z) = w² z H (D_zF)`
vanishing at `0⁺` (in the `ContinuousWithinAt` sense, which pins `Φ(0) = 0`) and at `+∞`:

  `∫_0^∞ w² (D_zF)(D_zH) = -∫_0^∞ w² (D_z²F + b D_zF) H`.

Without the flux hypothesis the identity fails (see the module docstring). -/
theorem radial_ibp_Ioi {F H : ℝ → ℝ} (hF : ContDiffOn ℝ 2 F (Set.Ioi (0 : ℝ)))
    (hH : ContDiffOn ℝ 1 H (Set.Ioi (0 : ℝ)))
    (hcont : ContinuousWithinAt (tFlux F H) (Set.Ici (0 : ℝ)) 0)
    (hTop : Tendsto (tFlux F H) Filter.atTop (nhds 0))
    (hL : IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (z * deriv F z) * (z * deriv H z))
      (Set.Ioi (0 : ℝ)))
    (hR : IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 * LzComb F z * H z)
      (Set.Ioi (0 : ℝ))) :
    (∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * (z * deriv F z) * (z * deriv H z))
      = - ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * LzComb F z * H z := by
  have hFTC := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto (a := (0 : ℝ)) (m := (0 : ℝ))
    (f := tFlux F H)
    (f' := fun z : ℝ => (Work.Spaces.w z) ^ 2 * (z * deriv F z) * (z * deriv H z)
      + (Work.Spaces.w z) ^ 2 * LzComb F z * H z)
    hcont (fun z hz => hasDerivAt_tFlux hF hH z hz) (hL.add hR) hTop
  have h0 : tFlux F H 0 = 0 := by simp [tFlux_apply, Work.Spaces.w]
  rw [h0, sub_zero, MeasureTheory.integral_add hL hR] at hFTC
  linarith

/-! ## Elementary angular weight comparisons -/

/-- The heavy angular weight dominates `1` on the open angular interval:
`σ_η = sin(2θ)^{-η} ≥ 1` for `0 < θ < π/2`.  (At the two endpoints Lean's `rpow` gives the
value `0`, so the comparison can only hold a.e. on the closed interval.) -/
theorem one_le_sEta_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hs0 : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem_Ioo hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hη : 0 ≤ Work.Spaces.eta := Work.Spaces.eta_pos.le
  rw [Real.rpow_neg hs0.le, ← one_div, le_div_iff₀ (Real.rpow_pos_of_pos hs0 _), one_mul]
  exact Real.rpow_le_one hs0.le hs1 hη

/-- The two endpoints of `Iθ` form a null set, so the pointwise comparison of
`one_le_sEta_of_mem_Ioo` upgrades to an a.e. comparison on `Iθ`. -/
theorem ae_one_le_sEta :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  change ∀ᵐ θ ∂(volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2))),
    1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  rw [MeasureTheory.ae_iff]
  have hsub : {θ : ℝ | ¬ (θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)
      → 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))}
      ⊆ ({0, Real.pi / 2} : Set ℝ) := by
    intro θ hθ
    simp only [Set.mem_setOf_eq, not_imp] at hθ
    obtain ⟨hIθ, hP⟩ := hθ
    obtain ⟨hlo, hhi⟩ := hIθ
    by_contra hmem
    have hne0 : θ ≠ 0 := fun h => hmem (by simp [h])
    have hnep : θ ≠ Real.pi / 2 := fun h => hmem (by simp [h])
    have h0 : 0 < θ := lt_of_le_of_ne hlo (Ne.symm hne0)
    have h1 : θ < Real.pi / 2 := lt_of_le_of_ne hhi hnep
    exact hP (one_le_sEta_of_mem_Ioo ⟨h0, h1⟩)
  have hnull : volume ({0, Real.pi / 2} : Set ℝ) = 0 := by
    rw [show ({0, Real.pi / 2} : Set ℝ) = {0} ∪ {Real.pi / 2} by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]]
    exact MeasureTheory.measure_union_null (MeasureTheory.measure_singleton 0)
      (MeasureTheory.measure_singleton (Real.pi / 2))
  exact MeasureTheory.measure_mono_null hsub hnull

/-! ## The `ℋ⁰`-slot dominates the `σ_a`-slot and the unweighted slot -/

/-- The `ℋ⁰`-slice of `f` at level `0`, rewritten as `f²w²σ_η`, is integrable on `Iθ` for every
`z ∈ Iz` as soon as `f ∈ ℋ⁰`. -/
theorem integrableOn_slice_sEta_of_HkMem {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.HkMem α 0 f) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    IntegrableOn (fun θ => (f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ := by
  refine MeasureTheory.IntegrableOn.congr_fun (hf.1 z hz) ?_ measurableSet_Icc
  intro θ hθ
  exact hkIntegrand_zero_eq' α f hθ

/-- **The `ℋ⁰`-slot of `f` dominates the `σ_a`-weighted slot of `f`** (for `α ≤ 1`, where
`σ_a ≤ σ_η` a.e. on `Iθ`):  `∫∫ f² w² σ_a ≤ HkSq α 0 f`.  This is what discharges the
finiteness of `TTint` from the `HkMem` hypotheses. -/
theorem integral_sigA_le_HkSq {α : ℝ} (hα : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.HkMem α 0 f) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sigA α θ) ≤ Work.Spaces.HkSq α 0 f := by
  rw [Work.Spaces.HkSq]
  refine MeasureTheory.integral_mono_of_nonneg ?_ hf.2 ?_
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z _
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ =>
      mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sigA_nonneg α θ hθ)
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    refine MeasureTheory.integral_mono_of_nonneg ?_ (hf.1 z hz) ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sigA_nonneg α θ hθ)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [hkIntegrand_zero_eq' α f hθ]
      exact mul_le_mul_of_nonneg_left (sigA_le_sEta hα hθ)
        (mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- **The `ℋ⁰`-slot of `f` dominates the unweighted slot of `f`**:
`∫∫ f² w² ≤ HkSq α 0 f`, because `σ_η ≥ 1` a.e. on `Iθ`. -/
theorem integral_plain_le_HkSq {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.HkMem α 0 f) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (f z θ) ^ 2 * (Work.Spaces.w z) ^ 2) ≤ Work.Spaces.HkSq α 0 f := by
  rw [Work.Spaces.HkSq]
  refine MeasureTheory.integral_mono_of_nonneg ?_ hf.2 ?_
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z _
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ _ =>
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    refine MeasureTheory.integral_mono_of_nonneg ?_ (hf.1 z hz) ?_
    · filter_upwards with θ
      exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    · filter_upwards [ae_one_le_sEta, MeasureTheory.ae_restrict_mem measurableSet_Icc] with
        θ hθ _
      rw [hkIntegrand_zero_eq' α f (by
        simp only [Work.Spaces.Iθ] at *
        exact ‹_›)]
      have hnn : (0 : ℝ) ≤ (f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 :=
        mul_nonneg (sq_nonneg _) (sq_nonneg _)
      calc (f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          = (f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * 1 := by ring
        _ ≤ (f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
            mul_le_mul_of_nonneg_left hθ hnn

/-- **`TTint` is dominated by the honest `ℋ⁰`-slot of `∂_θ²G`.** -/
theorem TTint_le_HkSq {α : ℝ} (hα : α ≤ 1) {G : ℝ → ℝ → ℝ}
    (h : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 G)) :
    TTint α G ≤ Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 G) :=
  integral_sigA_le_HkSq hα h

/-- The coefficient `b z = (z-3)/(1+z)` of `DDint` is bounded by `3` on `z ≥ 0`. -/
theorem abs_bcoef_le_three {z : ℝ} (hz : 0 ≤ z) : |bcoef z| ≤ 3 := by
  have h1 : (0 : ℝ) < 1 + z := by linarith
  rw [bcoef, abs_div, abs_of_pos h1, div_le_iff₀ h1, abs_le]
  constructor <;> linarith

theorem interpGamma_core : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (G : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.SmoothOpen G →
      (∀ z : ℝ, G z 0 = 0) → (∀ z : ℝ, G z (Real.pi / 2) = 0) →
      Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 2 G) →
      Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 G) →
      Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 1 G) →
      MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iz →
      Work.FTS.EllipticEst.TT.Xint α G
        ≤ C * (Real.sqrt (Work.FTS.EllipticEst.TT.DDint α G * Work.FTS.EllipticEst.TT.TTint α G)
            + Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 G)) := by sorry

end

end Work.FTS.EllipticEst.TT
