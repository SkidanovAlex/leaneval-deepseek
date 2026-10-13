/-
# `ModalSolR/PerModeBasic` — elementary facts for the modal weak solution

This module collects the elementary facts used by the per-mode weak identity
(`ModalSolR/PerMode.lean`) and by the final assembly (`ModalSolR/weakSolExists_slice.lean`):

* `bslOp_eq_zero_off_box`: the operator applied to a test function vanishes off any closed box
  containing the (open) support box of the test function;
* `test_vanishes_off_theta` / `test_vanishes_off_z`: the test function vanishes off the box;
* `setIntegral_Q0_eq_box`: an integral over the open quadrant equals the integral over the closed
  box when the integrand vanishes on the difference;
* `acoeff_zero_of_orth`: the `m = 0` mode coefficient vanishes under the solvability condition
  `OrthCond F`, because `eFam 0 = 3 sin θ cos θ`.

Everything here is `sorry`-free.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.H2.ModalSol.Defs
import Submission.Work.EllipticEst.ModalSolution.bslOp_ibp
import Submission.Work.EllipticEst.ModalSolution.box_of_compactSupport
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.H2.ModalSolR

/-! ## Vanishing of the operator off the closed box -/

/-- For a test function supported in the open box `Ioo a b ×ˢ Ioo c d`, the operator `bslOp α φ`
vanishes at every point outside the *closed* box: such a point has a neighbourhood on which `φ`
vanishes identically. -/
theorem bslOp_eq_zero_off_box {φ : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hbox : ∀ p : ℝ × ℝ, p ∉ Set.Ioo a b ×ˢ Set.Ioo c d → φ p.1 p.2 = 0)
    {α : ℝ} {p : ℝ × ℝ} (hp : p ∉ Set.Icc a b ×ˢ Set.Icc c d) :
    Work.Elliptic.bslOp α φ p.1 p.2 = 0 := by
  have hopen : IsOpen ({q : ℝ × ℝ | q.1 < a ∨ b < q.1 ∨ q.2 < c ∨ d < q.2}) := by
    have h1 : IsOpen {q : ℝ × ℝ | q.1 < a} := isOpen_lt continuous_fst continuous_const
    have h2 : IsOpen {q : ℝ × ℝ | b < q.1} := isOpen_lt continuous_const continuous_fst
    have h3 : IsOpen {q : ℝ × ℝ | q.2 < c} := isOpen_lt continuous_snd continuous_const
    have h4 : IsOpen {q : ℝ × ℝ | d < q.2} := isOpen_lt continuous_const continuous_snd
    have heq : {q : ℝ × ℝ | q.1 < a ∨ b < q.1 ∨ q.2 < c ∨ d < q.2}
        = ({q : ℝ × ℝ | q.1 < a} ∪ {q : ℝ × ℝ | b < q.1})
          ∪ ({q : ℝ × ℝ | q.2 < c} ∪ {q : ℝ × ℝ | d < q.2}) := by
      ext q; simp only [Set.mem_setOf_eq, Set.mem_union]; tauto
    rw [heq]
    exact (h1.union h2).union (h3.union h4)
  have hmem : p ∈ {q : ℝ × ℝ | q.1 < a ∨ b < q.1 ∨ q.2 < c ∨ d < q.2} := by
    by_contra hcon
    rw [Set.mem_setOf_eq] at hcon
    simp only [not_or] at hcon
    exact hp (Set.mem_prod.mpr ⟨⟨le_of_not_gt hcon.1, le_of_not_gt hcon.2.1⟩,
      ⟨le_of_not_gt hcon.2.2.1, le_of_not_gt hcon.2.2.2⟩⟩)
  refine Work.EllipticEst.ModalSolution.bslOp_eq_zero_of_eventually_zero α
    (Filter.mem_of_superset (hopen.mem_nhds hmem) ?_)
  intro q hq
  exact hbox q (by
    intro hqK
    obtain ⟨h1, h2⟩ := Set.mem_prod.mp hqK
    rcases hq with h | h | h | h
    · exact absurd h (not_lt.mpr h1.1.le)
    · exact absurd h (not_lt.mpr h1.2.le)
    · exact absurd h (not_lt.mpr h2.1.le)
    · exact absurd h (not_lt.mpr h2.2.le))

/-- A test function supported in `Ioo a b ×ˢ Ioo c d` vanishes at every point whose second
coordinate is outside `Ioo c d`. -/
theorem test_vanishes_off_theta {φ : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hbox : ∀ p : ℝ × ℝ, p ∉ Set.Ioo a b ×ˢ Set.Ioo c d → φ p.1 p.2 = 0)
    {z θ : ℝ} (hθ : θ ∉ Set.Ioo c d) : φ z θ = 0 :=
  hbox (z, θ) (fun h => hθ (Set.mem_prod.mp h).2)

/-- A test function supported in `Ioo a b ×ˢ Ioo c d` vanishes at every point whose first
coordinate is outside `Ioo a b`. -/
theorem test_vanishes_off_z {φ : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hbox : ∀ p : ℝ × ℝ, p ∉ Set.Ioo a b ×ˢ Set.Ioo c d → φ p.1 p.2 = 0)
    {z θ : ℝ} (hz : z ∉ Set.Ioo a b) : φ z θ = 0 :=
  hbox (z, θ) (fun h => hz (Set.mem_prod.mp h).1)

/-- An integral over the open quadrant equals the corresponding integral over a measurable subset
`K ⊆ Q0` on whose complement the integrand vanishes. -/
theorem setIntegral_Q0_eq_box {f : ℝ × ℝ → ℝ} {K : Set (ℝ × ℝ)}
    (hKmeas : MeasurableSet K) (hKsub : K ⊆ Work.FTS.EllipticEst.Q0)
    (hf : ∀ p ∈ Work.FTS.EllipticEst.Q0 \ K, f p = 0) :
    (∫ p in Work.FTS.EllipticEst.Q0, f p) = ∫ p in K, f p :=
  MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    Work.FTS.EllipticEst.isOpen_Q0.measurableSet hKsub hf

/-! ## The `m = 0` coefficient vanishes under the solvability condition -/

/-- `eFam 0 θ = 3 sin θ cos θ`. -/
theorem eFam_zero_apply (θ : ℝ) :
    Work.FTS.PhiStar.Gegenbauer.eFam 0 θ = 3 * Real.sin θ * Real.cos θ := by
  simp only [Work.FTS.PhiStar.Gegenbauer.eFam, Work.FTS.PhiStar.Gegenbauer.gC,
    Nat.reduceMul, Nat.reduceAdd]
  ring

/-- **The `m = 0` mode coefficient vanishes under `OrthCond F`.**  The zeroth eigenfunction is
`eFam 0 θ = 3 sin θ cos θ`, so the numerator `∫ F z θ · eFam 0 θ · cos θ` is `3 F_*(z) = 0`. -/
theorem cmode_zero_eq_zero {F : ℝ → ℝ → ℝ} (horth : Work.Elliptic.OrthCond F) (z : ℝ) :
    Work.FTS.PhiStar.Series.cmode 0 F z = 0 := by
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hnum : (∫ θ in (0 : ℝ)..(Real.pi / 2),
      F z θ * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ * Real.cos θ) = 0 := by
    rw [intervalIntegral.integral_of_le hle, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    have h2 : (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 2),
          F z θ * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ * Real.cos θ)
        = 3 * (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 2),
            F z θ * Work.Elliptic.sinCos2 θ) := by
      rw [← MeasureTheory.integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
      rw [eFam_zero_apply, Work.Elliptic.sinCos2]
      ring
    rw [h2]
    have h3 : (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 2),
        F z θ * Work.Elliptic.sinCos2 θ) = 0 := by
      simpa only [Work.Elliptic.Fstar, Work.Spaces.Iθ] using horth z
    rw [h3, mul_zero]
  have hden : (∫ θ in (0 : ℝ)..(Real.pi / 2),
      Work.FTS.PhiStar.Gegenbauer.eFam 0 θ ^ 2 * Real.cos θ) ≠ 0 := by
    rw [intervalIntegral.integral_of_le hle, ← MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← (show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl)]
    rw [Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts 0]
    norm_num
  rw [Work.FTS.PhiStar.Series.cmode, hnum, zero_div]

/-- **The `m = 0` radial coefficient vanishes under `OrthCond F`.** -/
theorem acoeff_zero_of_orth {F : ℝ → ℝ → ℝ} (horth : Work.Elliptic.OrthCond F) (α z : ℝ) :
    Work.FTS.PhiStar.Series.acoeff α 0 F z = 0 := by
  have hc : (fun t => Work.FTS.PhiStar.Series.cmode 0 F t) = fun _ => (0 : ℝ) :=
    funext (fun t => cmode_zero_eq_zero horth t)
  show Work.FTS.PhiStar.Radial.radGreen α 0
    (fun t => Work.FTS.PhiStar.Series.cmode 0 F t) z = 0
  rw [hc]
  simp [Work.FTS.PhiStar.Radial.radGreen]
