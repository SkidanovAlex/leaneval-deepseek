/-
Copyright: work module for the Elgindi finite-time singularity project.

# `TransportS/T2Sup/smainBound`: the `Smain` summand of the per-slot transport pairing

This module proves the estimate for the `Smain` summand of the Leibniz expansion of the
transport pairing, i.e. for the pairing

  `canonW q z θ · f z θ · D_z(mixed b a g) z θ · mixed b a g z θ`

with `a + b ≤ 4` and `q ≤ η` (when `a = 0`) resp. `q ≤ γ`.  The estimate is
`|∫_z ∫_θ ·| ≤ 2 Mf HkSq α 4 g`, together with the integrability of the radial marginal.

## Route

* `Smain f g a b z θ = f z θ · mixed (b+1) a g z θ`, so the pairing is
  `canonW q · f · D_z(mixed b a g) · mixed b a g`.
* When `a + b = 4` the `g`-slot `mixed b a g` has order `4` and its `D_z` has order `5`, so the
  pointwise (Cauchy–Schwarz) route only gives `Mf · HkSq α 5 g`; the sharp estimate is the
  radial integration by parts `Main.topSlotBound`, whose boundary terms come from
  `BdryTraces α 4 g`.
* When `a + b ≤ 3` both factors are honest `ℋ⁴`-slots, so the pointwise AM–GM
  (`canonW |X||Y| ≤ (canonW X² + canonW Y²)/2 ≤ HkIntegrand α 4 g`) gives `Mf · HkSq α 4 g`.
* The integrability of the radial marginal is proved in both cases by domination: the marginal
  is bounded by `Mf · ∫_θ (HkIntegrand α k₁ g + HkIntegrand α k₂ g)` with
  `(k₁,k₂) = (5,4)` (top slot) resp. `(4,4)` (easy case), and the `θ`-marginals of
  `HkIntegrand` are integrable by `HkMem`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.TransportS.T2Sup.FinalAux
import Submission.Work.FTS.TransportS.T2Sup.Main
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.T2Sup

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Work.FTS.TransportS.SlotT2

/-! ## Interior comparison of the canonical weights -/

/-- At interior angles the canonical weight `canonW q` is monotone in the exponent. -/
theorem canonW_le_of_le {q q' z θ : ℝ} (hqq : q ≤ q') (hθ0 : 0 < θ) (hθ2 : θ < π / 2) :
    canonW q z θ ≤ canonW q' z θ := by
  have hσ0 : 0 < Real.sin (2 * θ) := sin_two_pos_of_Ioo ⟨hθ0, hθ2⟩
  have hσ1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h := Real.rpow_le_rpow_of_exponent_ge hσ0 hσ1 (show -q' ≤ -q by linarith)
  exact mul_le_mul_of_nonneg_left h (sq_nonneg _)

/-! ## The slot dominations at an arbitrary order -/

/-- `canonW q · (D_z^j g)² ≤ HkIntegrand α k g` for any `q ≤ η` and `j ≤ k`
(interior angles). -/
theorem canonW_mul_z_le_of_le {α q : ℝ} {g : ℝ → ℝ → ℝ} (k : ℕ) (hq : q ≤ Work.Spaces.eta)
    {z θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < π / 2) {j : ℕ} (hj : j ≤ k) :
    canonW q z θ * (Work.Spaces.DzIter j g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k g z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ2⟩
  have hw : canonW q z θ ≤ (Work.FTS.H2.Whz z θ) ^ 2 := by
    rw [← canonW_eta_eq z θ hθI]
    exact canonW_le_of_le hq hθ0 hθ2
  calc canonW q z θ * (Work.Spaces.DzIter j g z θ) ^ 2
      ≤ (Work.FTS.H2.Whz z θ) ^ 2 * (Work.Spaces.DzIter j g z θ) ^ 2 :=
        mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    _ = (Work.Spaces.DzIter j g z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        rw [Work.FTS.H2.Whz]; ring
    _ ≤ Work.Spaces.HkIntegrand α k g z θ :=
        Work.Spaces.sq_le_HkIntegrand_z α k g z θ j hj

/-- `canonW q · (mixed j i g)² ≤ HkIntegrand α k g` for any `q ≤ γ`, `1 ≤ i`, `i + j ≤ k`
(interior angles). -/
theorem canonW_mul_mixed_le_of_le {α q : ℝ} {g : ℝ → ℝ → ℝ} (k : ℕ)
    (hqγ : q ≤ Work.Spaces.gam α) {z θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < π / 2)
    {j i : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ k) :
    canonW q z θ * (Work.Spaces.mixed j i g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k g z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ2⟩
  have hw : canonW q z θ ≤ (Work.Spaces.Wt α z θ) ^ 2 := by
    rw [← canonW_gam_eq α z θ hθI]
    exact canonW_le_of_le hqγ hθ0 hθ2
  calc canonW q z θ * (Work.Spaces.mixed j i g z θ) ^ 2
      ≤ (Work.Spaces.Wt α z θ) ^ 2 * (Work.Spaces.mixed j i g z θ) ^ 2 :=
        mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    _ = (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
    _ ≤ Work.Spaces.HkIntegrand α k g z θ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α k g z θ i j hi hij

/-! ## The `θ`-slice bound of the `Smain` summand -/

/-- **The angular slice bound.**  If the `canonW q`-weighted squares of the two factors are
dominated by the (`θ`-integrable) functions `HkIntegrand α k₁ g` resp. `HkIntegrand α k₂ g`,
then the absolute value of the angular integral of the `Smain` summand is at most `Mf` times
the sum of the two slot energies. -/
theorem smain_slice_abs_le {α q Mf : ℝ} (hMf : 0 ≤ Mf) {f g : ℝ → ℝ → ℝ} {a b : ℕ}
    {k₁ k₂ : ℕ} {z : ℝ}
    (hI1 : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k₁ g z θ)
      Work.Spaces.Iθ)
    (hI2 : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k₂ g z θ)
      Work.Spaces.Iθ)
    (hf : ∀ θ : ℝ, 0 < θ → θ < π / 2 → |f z θ| ≤ Mf)
    (hX : ∀ θ : ℝ, 0 < θ → θ < π / 2 →
      canonW q z θ * (Work.Spaces.mixed (b + 1) a g z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α k₁ g z θ)
    (hY : ∀ θ : ℝ, 0 < θ → θ < π / 2 →
      canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α k₂ g z θ) :
    |∫ θ in Work.Spaces.Iθ, canonW q z θ * f z θ * Work.Spaces.mixed (b + 1) a g z θ
        * Work.Spaces.mixed b a g z θ|
      ≤ Mf * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k₁ g z θ)
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k₂ g z θ)) := by
  have hpt : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖canonW q z θ * f z θ * Work.Spaces.mixed (b + 1) a g z θ
        * Work.Spaces.mixed b a g z θ‖
        ≤ Mf * (Work.Spaces.HkIntegrand α k₁ g z θ + Work.Spaces.HkIntegrand α k₂ g z θ) := by
    refine ae_of_forall_Ioo (fun θ hθ => ?_)
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hcw : 0 ≤ canonW q z θ := canonW_nonneg hθI
    have hA := hX θ hθ.1 hθ.2
    have hB := hY θ hθ.1 hθ.2
    have hamgm : |Work.Spaces.mixed (b + 1) a g z θ| * |Work.Spaces.mixed b a g z θ|
        ≤ ((Work.Spaces.mixed (b + 1) a g z θ) ^ 2
            + (Work.Spaces.mixed b a g z θ) ^ 2) / 2 := by
      have h := two_mul_le_add_sq |Work.Spaces.mixed (b + 1) a g z θ|
        |Work.Spaces.mixed b a g z θ|
      rw [sq_abs, sq_abs] at h
      linarith
    have hGY : canonW q z θ * |Work.Spaces.mixed (b + 1) a g z θ|
          * |Work.Spaces.mixed b a g z θ|
        ≤ Work.Spaces.HkIntegrand α k₁ g z θ + Work.Spaces.HkIntegrand α k₂ g z θ := by
      calc canonW q z θ * |Work.Spaces.mixed (b + 1) a g z θ|
            * |Work.Spaces.mixed b a g z θ|
          = canonW q z θ * (|Work.Spaces.mixed (b + 1) a g z θ|
              * |Work.Spaces.mixed b a g z θ|) := by ring
        _ ≤ canonW q z θ * (((Work.Spaces.mixed (b + 1) a g z θ) ^ 2
              + (Work.Spaces.mixed b a g z θ) ^ 2) / 2) :=
            mul_le_mul_of_nonneg_left hamgm hcw
        _ = (canonW q z θ * (Work.Spaces.mixed (b + 1) a g z θ) ^ 2
              + canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2) / 2 := by ring
        _ ≤ Work.Spaces.HkIntegrand α k₁ g z θ + Work.Spaces.HkIntegrand α k₂ g z θ := by
            linarith [Work.Spaces.HkIntegrand_nonneg α k₁ g z θ,
              Work.Spaces.HkIntegrand_nonneg α k₂ g z θ]
    calc ‖canonW q z θ * f z θ * Work.Spaces.mixed (b + 1) a g z θ
            * Work.Spaces.mixed b a g z θ‖
        = canonW q z θ * |f z θ| * |Work.Spaces.mixed (b + 1) a g z θ|
            * |Work.Spaces.mixed b a g z θ| := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hcw]
      _ = |f z θ| * (canonW q z θ * |Work.Spaces.mixed (b + 1) a g z θ|
            * |Work.Spaces.mixed b a g z θ|) := by ring
      _ ≤ Mf * (Work.Spaces.HkIntegrand α k₁ g z θ + Work.Spaces.HkIntegrand α k₂ g z θ) :=
          mul_le_mul (hf θ hθ.1 hθ.2) hGY
            (mul_nonneg (mul_nonneg hcw (abs_nonneg _)) (abs_nonneg _)) hMf
  have h1 : ‖∫ θ, canonW q z θ * f z θ * Work.Spaces.mixed (b + 1) a g z θ
        * Work.Spaces.mixed b a g z θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)‖
      ≤ ∫ θ, ‖canonW q z θ * f z θ * Work.Spaces.mixed (b + 1) a g z θ
        * Work.Spaces.mixed b a g z θ‖ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.norm_integral_le_integral_norm _
  have h2 : (∫ θ, ‖canonW q z θ * f z θ * Work.Spaces.mixed (b + 1) a g z θ
        * Work.Spaces.mixed b a g z θ‖ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      ≤ ∫ θ, Mf * (Work.Spaces.HkIntegrand α k₁ g z θ + Work.Spaces.HkIntegrand α k₂ g z θ)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun θ => norm_nonneg _)
      ((hI1.add hI2).const_mul Mf) hpt
  have h3 : (∫ θ, Mf * (Work.Spaces.HkIntegrand α k₁ g z θ + Work.Spaces.HkIntegrand α k₂ g z θ)
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      = Mf * ((∫ θ, Work.Spaces.HkIntegrand α k₁ g z θ
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          + (∫ θ, Work.Spaces.HkIntegrand α k₂ g z θ
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hI1 hI2]
  rw [← Real.norm_eq_abs]
  exact le_trans h1 (le_trans h2 (le_of_eq h3))

/-! ## Integrability of the radial marginal -/

/-- **The marginal of the `Smain` summand is integrable.**  The dominating function is
`Mf · (∫_θ HkIntegrand α k₁ g + ∫_θ HkIntegrand α k₂ g)`, integrable by `HkMem`. -/
theorem smain_marginal_integrable {α q Mf : ℝ} (hMf : 0 ≤ Mf) {f g : ℝ → ℝ → ℝ} {a b : ℕ}
    {k₁ k₂ : ℕ}
    (hFsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hGq : Work.FTS.LocData.SmoothQuad g)
    (hm1 : Work.Spaces.HkMem α k₁ g) (hm2 : Work.Spaces.HkMem α k₂ g)
    (hf : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |f z θ| ≤ Mf)
    (hX : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      canonW q z θ * (Work.Spaces.mixed (b + 1) a g z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α k₁ g z θ)
    (hY : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α k₂ g z θ) :
    MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * f z θ * Work.Spaces.mixed (b + 1) a g z θ
          * Work.Spaces.mixed b a g z θ) Work.Spaces.Iz := by
  have hdom : MeasureTheory.Integrable
      (fun z => Mf * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k₁ g z θ)
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k₂ g z θ)))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := (hm1.2.add hm2.2).const_mul Mf
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, canonW q z θ * f z θ
          * Work.Spaces.mixed (b + 1) a g z θ
          * Work.Spaces.mixed b a g z θ) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (Work.Spaces.aesm_of_continuousOn_Qd
        (fun p : ℝ × ℝ => canonW q p.1 p.2 * f p.1 p.2
          * Work.Spaces.mixed (b + 1) a g p.1 p.2 * Work.Spaces.mixed b a g p.1 p.2)
        ((((continuousOn_canonW q).mul hFsm.continuousOn).mul
          ((SmoothQuad.smoothOpen hGq).mixed (b + 1) a |>.continuousOn)).mul
          ((SmoothQuad.smoothOpen hGq).mixed b a |>.continuousOn)))
  refine MeasureTheory.Integrable.mono' hdom haesm ?_
  refine ae_of_forall_Ioi (fun z hz => ?_)
  have hslice := smain_slice_abs_le (α := α) (q := q) (Mf := Mf) hMf (z := z)
    (hm1.1 z (le_of_lt hz)) (hm2.1 z (le_of_lt hz))
    (fun θ hθ hθ2 => hf z θ hz hθ hθ2) (fun θ hθ hθ2 => hX z θ hz hθ hθ2)
    (fun θ hθ hθ2 => hY z θ hz hθ hθ2)
  simpa [Real.norm_eq_abs] using hslice

/-! ## The easy case `a + b ≤ 3` -/

/-- **The easy case.**  When `a + b ≤ 3` both `g`-factors are honest order-`≤ 4` slots, so the
pointwise AM–GM bound gives the sharp constant `2 Mf` at order `4`. -/
theorem smain_easy {α q Mf : ℝ} (hMf : 0 ≤ Mf) {f g : ℝ → ℝ → ℝ} {a b : ℕ}
    (hFsm : Work.FTS.EllipticEst.SmoothOpen f) (hGq : Work.FTS.LocData.SmoothQuad g)
    (hm4 : Work.Spaces.HkMem α 4 g)
    (hf : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |f z θ| ≤ Mf)
    (hX : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      canonW q z θ * (Work.Spaces.mixed (b + 1) a g z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 g z θ)
    (hY : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 g z θ) :
    MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, canonW q z θ * f z θ
        * Work.Spaces.mixed (b + 1) a g z θ * Work.Spaces.mixed b a g z θ)
        Work.Spaces.Iz ∧
      |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ * f z θ
          * Work.Spaces.mixed (b + 1) a g z θ * Work.Spaces.mixed b a g z θ|
        ≤ 2 * Mf * Work.Spaces.HkSq α 4 g := by
  refine ⟨smain_marginal_integrable (k₁ := 4) (k₂ := 4) hMf hFsm hGq hm4 hm4 hf hX hY, ?_⟩
  have h1 : |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ * f z θ
        * Work.Spaces.mixed (b + 1) a g z θ * Work.Spaces.mixed b a g z θ|
      ≤ ∫ z in Work.Spaces.Iz, Mf * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)) := by
    rw [← Real.norm_eq_abs]
    refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => norm_nonneg _)
      ((hm4.2.add hm4.2).const_mul Mf) ?_
    refine ae_of_forall_Ioi fun z hz => ?_
    have hslice := smain_slice_abs_le (α := α) (q := q) (Mf := Mf) hMf (z := z)
      (hm4.1 z (le_of_lt hz)) (hm4.1 z (le_of_lt hz))
      (fun θ hθ hθ2 => hf z θ hz hθ hθ2) (fun θ hθ hθ2 => hX z θ hz hθ hθ2)
      (fun θ hθ hθ2 => hY z θ hz hθ hθ2)
    simpa [Real.norm_eq_abs] using hslice
  refine le_trans h1 (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hm4.2 hm4.2,
    Work.Spaces.HkSq]
  ring

/-! ## The main statement -/

theorem smainBound {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {f g : ℝ → ℝ → ℝ} {a b : ℕ} {q Mf : ℝ} (hMf : 0 ≤ Mf)
    (hFsm : Work.FTS.EllipticEst.SmoothOpen f) (hGq : Work.FTS.LocData.SmoothQuad g)
    (hmg4 : Work.Spaces.HkMem α 4 g) (hmg5 : Work.Spaces.HkMem α 5 g)
    (hbdry : Work.FTS.Nonlin.BdryTraces α 4 g)
    (hab : a + b ≤ 4) (hq0 : a = 0 → q ≤ Work.Spaces.eta) (hqγ : q ≤ Work.Spaces.gam α)
    (hf : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |f z θ| ≤ Mf)
    (hDf : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |Work.Spaces.Dz f z θ| ≤ Mf) :
    MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.FTS.TransportS.SlotT2.canonW q z θ * Work.FTS.TransportS.T2Sup.Smain f g a b z θ
          * Work.Spaces.mixed b a g z θ) Work.Spaces.Iz ∧
      |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.FTS.TransportS.SlotT2.canonW q z θ * Work.FTS.TransportS.T2Sup.Smain f g a b z θ
            * Work.Spaces.mixed b a g z θ| ≤ 2 * Mf * Work.Spaces.HkSq α 4 g := by
  -- unfold `Smain` (up to the reassociation of the product)
  have hInt : (fun z => ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * Smain f g a b z θ * Work.Spaces.mixed b a g z θ)
      = fun z => ∫ θ in Work.Spaces.Iθ, canonW q z θ * f z θ
          * Work.Spaces.mixed (b + 1) a g z θ * Work.Spaces.mixed b a g z θ := by
    funext z
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    dsimp only
    rw [show Smain f g a b z θ = f z θ * Work.Spaces.mixed (b + 1) a g z θ from rfl]
    ring
  rw [hInt]
  rcases lt_or_eq_of_le hab with hlt | heq
  · -- ## Case `a + b ≤ 3`
    rcases eq_or_ne a 0 with ha0 | ha0
    · -- `a = 0`, `b ≤ 3`: two pure `D_z`-slots
      subst ha0
      have hqη : q ≤ Work.Spaces.eta := hq0 rfl
      refine smain_easy (α := α) (q := q) (Mf := Mf) hMf hFsm hGq hmg4 hf ?_ ?_
      · intro z θ hz hθ0 hθ2
        simpa only [Work.Spaces.mixed_zero_right] using
          (canonW_mul_z_le_of_le (α := α) (q := q) 4 hqη (z := z) (θ := θ) hθ0 hθ2
            (j := b + 1) (by omega))
      · intro z θ hz hθ0 hθ2
        simpa only [Work.Spaces.mixed_zero_right] using
          (canonW_mul_z_le_of_le (α := α) (q := q) 4 hqη (z := z) (θ := θ) hθ0 hθ2
            (j := b) (by omega))
    · -- `a ≥ 1`, `a + b ≤ 3`: two mixed slots
      have ha1 : 1 ≤ a := by omega
      refine smain_easy (α := α) (q := q) (Mf := Mf) hMf hFsm hGq hmg4 hf ?_ ?_
      · intro z θ hz hθ0 hθ2
        exact canonW_mul_mixed_le_of_le (α := α) 4 hqγ hθ0 hθ2 (j := b + 1) (i := a)
          ha1 (by omega)
      · intro z θ hz hθ0 hθ2
        exact canonW_mul_mixed_le_of_le (α := α) 4 hqγ hθ0 hθ2 (j := b) (i := a)
          ha1 (by omega)
  · -- ## Case `a + b = 4`: the top slot
    have hsub : 4 - a = b := by omega
    have hDzfun : Work.Spaces.Dz (Work.Spaces.mixed b a g) = Work.Spaces.mixed (b + 1) a g := by
      funext z θ
      simp only [Work.Spaces.mixed]
      rw [Work.Spaces.DzIter_succ]
    have hint : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, canonW q z θ * f z θ
        * Work.Spaces.mixed (b + 1) a g z θ * Work.Spaces.mixed b a g z θ)
        Work.Spaces.Iz := by
      rcases eq_or_ne a 0 with ha0 | ha0
      · subst ha0
        have hqη : q ≤ Work.Spaces.eta := hq0 rfl
        refine smain_marginal_integrable (k₁ := 5) (k₂ := 4) hMf hFsm hGq hmg5 hmg4 hf ?_ ?_
        · intro z θ hz hθ0 hθ2
          simpa only [Work.Spaces.mixed_zero_right] using
            (canonW_mul_z_le_of_le (α := α) (q := q) 5 hqη (z := z) (θ := θ) hθ0 hθ2
              (j := b + 1) (by omega))
        · intro z θ hz hθ0 hθ2
          simpa only [Work.Spaces.mixed_zero_right] using
            (canonW_mul_z_le_of_le (α := α) (q := q) 4 hqη (z := z) (θ := θ) hθ0 hθ2
              (j := b) (by omega))
      · have ha1 : 1 ≤ a := by omega
        refine smain_marginal_integrable (k₁ := 5) (k₂ := 4) hMf hFsm hGq hmg5 hmg4 hf ?_ ?_
        · intro z θ hz hθ0 hθ2
          exact canonW_mul_mixed_le_of_le (α := α) 5 hqγ hθ0 hθ2 (j := b + 1) (i := a)
            ha1 (by omega)
        · intro z θ hz hθ0 hθ2
          exact canonW_mul_mixed_le_of_le (α := α) 4 hqγ hθ0 hθ2 (j := b) (i := a)
            ha1 (by omega)
    refine ⟨hint, ?_⟩
    -- the radial integration by parts in the top slot
    have htr : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        Filter.Tendsto (fun z => z * (Work.Spaces.mixed (4 - a) a g z θ * Work.Spaces.w z) ^ 2)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun z => z * (Work.Spaces.mixed (4 - a) a g z θ * Work.Spaces.w z) ^ 2)
          Filter.atTop (nhds 0) := by
      intro θ hθ
      have h := (hbdry a b hab).1 θ hθ
      simpa only [hsub] using h
    have hres := topSlotBound (α := α) (Mf := Mf) a (by omega) q hMf hq0 hqγ hFsm hGq
      hmg4 hmg5 hf hDf htr
    have hgoal_eq : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ * f z θ
          * Work.Spaces.mixed (b + 1) a g z θ * Work.Spaces.mixed b a g z θ)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, canonW q z θ * f z θ
          * Work.Spaces.Dz (Work.Spaces.mixed (4 - a) a g) z θ
          * Work.Spaces.mixed (4 - a) a g z θ := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      rw [hsub, hDzfun]
    rw [hgoal_eq]
    exact hres

end Work.FTS.TransportS.T2Sup
