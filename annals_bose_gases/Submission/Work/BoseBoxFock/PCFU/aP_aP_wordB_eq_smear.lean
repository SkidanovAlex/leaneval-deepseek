import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.PCFU.aQ_aP_update_invariant
import Submission.Work.BoseBoxFock.PCFU.chan_int_y_generic
import Submission.Work.BoseBoxFock.PCFU.chiW1_smear_integrable
import Submission.Work.BoseBoxFock.PCFU.wordSplitDefs
import Submission.Work.BoseFixB3.Conv.stronglyMeasurable_lowMult
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **A uniform bound on the low-momentum multiplier, for *every* `κ`.**

`Work.BoseFixB3.HighMass.abs_lowMult_le` needs `0 < κ` (to make the symbol compactly
supported); this version drops that hypothesis.  The point is that the Bochner integral of a
non-integrable function is `0`, so the inequality `‖∫ f‖ ≤ ∫ ‖f‖` is *unconditional*: if the
`p`-integrand is not integrable then both sides are `0`, and otherwise it is the honest
estimate.  In either case the right-hand side is a real number *independent of `x`*, which is
all that is used downstream. -/
lemma lowMult_abs_le_anyK {fc : Work.BoseBoxFix.LowCut} (κ ℓ : ℝ) (Ψ : E3 → ℝ) (x : E3) :
    |Work.BoseBoxFix.lowMult fc κ ℓ Ψ x| ≤ ((2 * Real.pi) ^ 3)⁻¹ *
      ∫ p : E3, |fc.f (‖p‖ / κ)| *
        ‖Submission.BoseGases.kinFT
          (fun z : E3 => (((Submission.BoseGases.acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖ := by
  have hpt : ∀ p : E3,
      ‖Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
          Submission.BoseGases.kinFT
            (fun z : E3 => (((Submission.BoseGases.acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖
        = |fc.f (‖p‖ / κ)| *
          ‖Submission.BoseGases.kinFT
            (fun z : E3 => (((Submission.BoseGases.acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖ := by
    intro p
    rw [norm_mul, norm_mul]
    have h2 : ‖Complex.exp (Complex.I * (inner ℝ p x : ℂ))‖ = 1 := by
      rw [show Complex.I * (inner ℝ p x : ℂ) = ((inner ℝ p x : ℝ) : ℂ) * Complex.I by
        push_cast; ring, Complex.norm_exp_ofReal_mul_I]
    rw [h2, one_mul,
      show ‖((fc.f (‖p‖ / κ) : ℝ) : ℂ)‖ = |fc.f (‖p‖ / κ)| from RCLike.norm_ofReal _]
  have h1 : Work.BoseBoxFix.lowMult fc κ ℓ Ψ x
      = (((2 * Real.pi) ^ 3)⁻¹) * (∫ p : E3,
          Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
            Submission.BoseGases.kinFT
              (fun z : E3 => (((Submission.BoseGases.acube ℓ).indicator Ψ z : ℝ) : ℂ)) p).re := by
    rw [show Work.BoseBoxFix.lowMult fc κ ℓ Ψ x
        = ((((2 * Real.pi) ^ 3)⁻¹ : ℝ) * ∫ p : E3,
          Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
            Submission.BoseGases.kinFT
              (fun z : E3 => (((Submission.BoseGases.acube ℓ).indicator Ψ z : ℝ) : ℂ)) p).re
        from rfl, Complex.re_ofReal_mul]
  rw [h1, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 * Real.pi) ^ 3)⁻¹)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans (Complex.abs_re_le_norm _) ?_
  have hnorm := norm_integral_le_integral_norm (μ := (volume : Measure E3))
    (fun p : E3 => Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
      Submission.BoseGases.kinFT
        (fun z : E3 => (((Submission.BoseGases.acube ℓ).indicator Ψ z : ℝ) : ℂ)) p)
  rw [show (fun p : E3 => ‖Complex.exp (Complex.I * (inner ℝ p x : ℂ)) *
        ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
        Submission.BoseGases.kinFT
          (fun z : E3 => (((Submission.BoseGases.acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖)
      = (fun p : E3 => |fc.f (‖p‖ / κ)| *
        ‖Submission.BoseGases.kinFT
          (fun z : E3 => (((Submission.BoseGases.acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖)
      from funext hpt] at hnorm
  exact hnorm

theorem aP_aP_wordB_eq_smear {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) {fc : Work.BoseBoxFix.LowCut}
    {ℓ κ Cθ : ℝ} (hℓ : 0 < ℓ) {Θ : Submission.BoseGases.X n → ℝ}
    (hΘm : Measurable Θ) (hΘb : ∀ y, |Θ y| ≤ Cθ) (hCθ : 0 ≤ Cθ)
    (x : Submission.BoseGases.X n) :
    (ℓ ^ 6) * (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j
        (Work.BoseBoxFock.PCFU.wordB v h fc κ ℓ i j Θ)) x)
      = ∫ z : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.chiScale ℓ z
            * Work.BoseBoxFock.PCFU.smearW ℓ (Work.BoseFixR.W1fun v h ℓ) z
            * Work.BoseBoxFock.PCFU.wordF fc κ ℓ i j Θ x z := by
  classical
  -- ### The slot-`j` fibre of the state `aQ_j (aP_i Θ)`.
  set Ψ : E3 → ℝ := fun z => Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
      (Function.update x j z) with hΨdef
  -- ### The word's low-slot factor is the low-momentum multiplier of that fibre.
  have hF_unfold : ∀ u : E3, Work.BoseBoxFock.PCFU.wordF fc κ ℓ i j Θ x u
      = Work.BoseBoxFix.lowMult fc κ ℓ Ψ u := by
    intro u
    rw [hΨdef]
    simp only [Work.BoseBoxFock.PCFU.wordF, Work.BoseBoxFix.lowSlot,
      Function.update_idem, Function.update_self]
  have hΨm : Measurable Ψ := by
    rw [hΨdef]
    exact (Work.BoseBoxFock.Weak.aQ_measurable j
      (Work.BoseBoxFock.Weak.aP_measurable i hΘm)).comp (by fun_prop)
  have hFasm : AEStronglyMeasurable (fun u : E3 =>
      Work.BoseBoxFock.PCFU.wordF fc κ ℓ i j Θ x u) volume := by
    have h : AEStronglyMeasurable (fun u : E3 => Work.BoseBoxFix.lowMult fc κ ℓ Ψ u) volume :=
      Work.BoseFixB3.HighMass.aestronglyMeasurable_lowMult hΨm
    rwa [show (fun u : E3 => Work.BoseBoxFix.lowMult fc κ ℓ Ψ u)
        = (fun u : E3 => Work.BoseBoxFock.PCFU.wordF fc κ ℓ i j Θ x u)
        from funext (fun u => (hF_unfold u).symm)] at h
  -- ### A uniform (in `u`) bound on the low-slot factor, valid for every `κ`.
  have hFb : ∀ u : E3, ‖Work.BoseBoxFock.PCFU.wordF fc κ ℓ i j Θ x u‖ ≤
      ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, |fc.f (‖p‖ / κ)| *
        ‖Submission.BoseGases.kinFT
          (fun z : E3 => (((Submission.BoseGases.acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖ := by
    intro u
    rw [hF_unfold u, Real.norm_eq_abs]
    exact lowMult_abs_le_anyK κ ℓ Ψ u
  -- ### Integrability of the joint integrand.
  have hint : Integrable (fun p : E3 × E3 =>
      Submission.BoseGases.chiScale ℓ p.1 * Work.BoseFixR.W1fun v h ℓ (p.1 - p.2)
        * Submission.BoseGases.chiScale ℓ p.2
        * Work.BoseBoxFock.PCFU.wordF fc κ ℓ i j Θ x p.2)
      ((volume : Measure E3).prod volume) := by
    have h1 : Integrable (fun p : E3 × E3 => Submission.BoseGases.chiScale ℓ p.1
        * Work.BoseFixR.W1fun v h ℓ (p.1 - p.2) * Submission.BoseGases.chiScale ℓ p.2)
        ((volume : Measure E3).prod volume) := chiW1_integrable h hℓ
    have h2 : AEStronglyMeasurable (fun p : E3 × E3 =>
        Work.BoseBoxFock.PCFU.wordF fc κ ℓ i j Θ x p.2)
        ((volume : Measure E3).prod volume) := hFasm.comp_snd
    have h3 : ∀ᵐ p ∂((volume : Measure E3).prod volume),
        ‖Work.BoseBoxFock.PCFU.wordF fc κ ℓ i j Θ x p.2‖ ≤
          ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, |fc.f (‖p‖ / κ)| *
            ‖Submission.BoseGases.kinFT
              (fun z : E3 => (((Submission.BoseGases.acube ℓ).indicator Ψ z : ℝ) : ℂ)) p‖ :=
      Filter.Eventually.of_forall (fun p => hFb p.2)
    exact h1.mul_bdd h2 h3
  -- ### The pointwise identity for the integrand of the double slot-mean.
  have hpt : ∀ y u : E3, Work.BoseBoxFock.PCFU.wordB v h fc κ ℓ i j Θ
        (Function.update (Function.update x i y) j u)
      = Submission.BoseGases.chiScale ℓ y * Work.BoseFixR.W1fun v h ℓ (y - u)
        * Submission.BoseGases.chiScale ℓ u
        * Work.BoseBoxFock.PCFU.wordF fc κ ℓ i j Θ x u := by
    intro y u
    have h1 : (Function.update (Function.update x i y) j u) i = y := by
      rw [Function.update_of_ne hij, Function.update_self]
    have h2 : (Function.update (Function.update x i y) j u) j = u :=
      Function.update_self j u (Function.update x i y)
    have h3 : Work.BoseBoxFix.lowSlot fc κ ℓ j
          (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
          (Function.update (Function.update x i y) j u)
        = Work.BoseBoxFix.lowSlot fc κ ℓ j
          (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ))
          (Function.update x j u) := by
      simp only [Work.BoseBoxFix.lowSlot, Function.update_idem, Function.update_self]
      congr 1
      funext z
      rw [Function.update_comm hij]
      exact aQ_aP_update_invariant hij (Function.update x j z) y
    have h4 : Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 y u
        = Submission.BoseGases.chiScale ℓ y * Work.BoseFixR.W1fun v h ℓ (y - u)
          * Submission.BoseGases.chiScale ℓ u := by
      simp only [Submission.BoseGases.wLoc, Submission.BoseGases.chiU,
        Submission.BoseGases.chiScale, Work.BoseFixR.W1fun, sub_zero]
    simp only [Work.BoseBoxFock.PCFU.wordB]
    rw [h1, h2, h3, h4, Work.BoseBoxFock.PCFU.wordF]
    ring
  -- ### The two support facts: `χ` vanishes off the centred cube.
  have hmem : ∀ z : E3, Submission.BoseGases.chiScale ℓ z ≠ 0 →
      z ∈ Submission.BoseGases.acube ℓ :=
    fun z hz => Submission.BoseGases.mem_acube_of_norm_le hℓ.le
      (Submission.BoseGases.chiScale_support_le hℓ hz)
  -- ### Step 1: unfold the two slot means.
  have hcoef : ∀ X : ℝ, ℓ ^ 6 * ((1 / ℓ ^ 3) * ((1 / ℓ ^ 3) * X)) = X := by
    intro X
    have h3 : ℓ ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hℓ)
    field_simp
  have hstep : (ℓ ^ 6) * (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j
        (Work.BoseBoxFock.PCFU.wordB v h fc κ ℓ i j Θ)) x)
      = ∫ y in Submission.BoseGases.acube ℓ, ∫ u in Submission.BoseGases.acube ℓ,
          Work.BoseBoxFock.PCFU.wordB v h fc κ ℓ i j Θ
            (Function.update (Function.update x i y) j u) := by
    rw [Submission.BoseGases.aP]
    have h2f : (fun y : E3 => Submission.BoseGases.aP ℓ j
          (Work.BoseBoxFock.PCFU.wordB v h fc κ ℓ i j Θ) (Function.update x i y))
        = fun y : E3 => (1 / ℓ ^ 3) * ∫ u in Submission.BoseGases.acube ℓ,
            Work.BoseBoxFock.PCFU.wordB v h fc κ ℓ i j Θ
              (Function.update (Function.update x i y) j u) := by
      funext y
      rw [Submission.BoseGases.aP]
    rw [h2f, MeasureTheory.integral_const_mul]
    exact hcoef _
  -- ### Step 2: the left-hand side is the full double integral.
  have hL : (ℓ ^ 6) * (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j
        (Work.BoseBoxFock.PCFU.wordB v h fc κ ℓ i j Θ)) x)
      = ∫ y : E3, ∫ u : E3, Submission.BoseGases.chiScale ℓ y
          * Work.BoseFixR.W1fun v h ℓ (y - u)
          * Submission.BoseGases.chiScale ℓ u
          * Work.BoseBoxFock.PCFU.wordF fc κ ℓ i j Θ x u := by
    refine hstep.trans ?_
    have hinner : ∀ y : E3, (∫ u in Submission.BoseGases.acube ℓ,
          Work.BoseBoxFock.PCFU.wordB v h fc κ ℓ i j Θ
            (Function.update (Function.update x i y) j u))
        = ∫ u : E3, Submission.BoseGases.chiScale ℓ y * Work.BoseFixR.W1fun v h ℓ (y - u)
          * Submission.BoseGases.chiScale ℓ u
          * Work.BoseBoxFock.PCFU.wordF fc κ ℓ i j Θ x u := by
      intro y
      have hcongr : (∫ u in Submission.BoseGases.acube ℓ,
            Work.BoseBoxFock.PCFU.wordB v h fc κ ℓ i j Θ
              (Function.update (Function.update x i y) j u))
          = ∫ u in Submission.BoseGases.acube ℓ,
              (Submission.BoseGases.chiScale ℓ y * Work.BoseFixR.W1fun v h ℓ (y - u)
                * Submission.BoseGases.chiScale ℓ u
                * Work.BoseBoxFock.PCFU.wordF fc κ ℓ i j Θ x u) :=
        integral_congr_ae (Filter.Eventually.of_forall (fun u => hpt y u))
      rw [hcongr, MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
      intro u hu
      have hχu : Submission.BoseGases.chiScale ℓ u = 0 := by
        by_contra hne
        exact hu (hmem u hne)
      simp [hχu]
    have houter : (∫ y in Submission.BoseGases.acube ℓ, ∫ u : E3,
          Submission.BoseGases.chiScale ℓ y * Work.BoseFixR.W1fun v h ℓ (y - u)
          * Submission.BoseGases.chiScale ℓ u
          * Work.BoseBoxFock.PCFU.wordF fc κ ℓ i j Θ x u)
        = ∫ y : E3, ∫ u : E3, Submission.BoseGases.chiScale ℓ y
          * Work.BoseFixR.W1fun v h ℓ (y - u)
          * Submission.BoseGases.chiScale ℓ u
          * Work.BoseBoxFock.PCFU.wordF fc κ ℓ i j Θ x u := by
      refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => ?_)
      have hχy : Submission.BoseGases.chiScale ℓ y = 0 := by
        by_contra hne
        exact hy (hmem y hne)
      have hrw : (fun u : E3 => Submission.BoseGases.chiScale ℓ y
            * Work.BoseFixR.W1fun v h ℓ (y - u) * Submission.BoseGases.chiScale ℓ u
            * Work.BoseBoxFock.PCFU.wordF fc κ ℓ i j Θ x u)
          = fun u : E3 => Submission.BoseGases.chiScale ℓ y
            * (Work.BoseFixR.W1fun v h ℓ (y - u) * Submission.BoseGases.chiScale ℓ u
              * Work.BoseBoxFock.PCFU.wordF fc κ ℓ i j Θ x u) := by
        funext u; ring
      rw [hrw, MeasureTheory.integral_const_mul, hχy, zero_mul]
    calc (∫ y in Submission.BoseGases.acube ℓ, ∫ u in Submission.BoseGases.acube ℓ,
            Work.BoseBoxFock.PCFU.wordB v h fc κ ℓ i j Θ
              (Function.update (Function.update x i y) j u))
        = ∫ y in Submission.BoseGases.acube ℓ, ∫ u : E3,
            Submission.BoseGases.chiScale ℓ y * Work.BoseFixR.W1fun v h ℓ (y - u)
            * Submission.BoseGases.chiScale ℓ u
            * Work.BoseBoxFock.PCFU.wordF fc κ ℓ i j Θ x u :=
          integral_congr_ae (Filter.Eventually.of_forall (fun y => hinner y))
      _ = _ := houter
  -- ### Step 3: the right-hand side is the same full double integral.
  have hR : (∫ z : E3, Submission.BoseGases.chiScale ℓ z
        * Work.BoseBoxFock.PCFU.smearW ℓ (Work.BoseFixR.W1fun v h ℓ) z
        * Work.BoseBoxFock.PCFU.wordF fc κ ℓ i j Θ x z)
      = ∫ z : E3, ∫ y : E3, Submission.BoseGases.chiScale ℓ y
          * Work.BoseFixR.W1fun v h ℓ (y - z)
          * Submission.BoseGases.chiScale ℓ z
          * Work.BoseBoxFock.PCFU.wordF fc κ ℓ i j Θ x z := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    simp only [Work.BoseBoxFock.PCFU.smearW]
    have hre : Submission.BoseGases.chiScale ℓ z
          * (∫ y : E3, Submission.BoseGases.chiScale ℓ y * Work.BoseFixR.W1fun v h ℓ (y - z))
          * Work.BoseBoxFock.PCFU.wordF fc κ ℓ i j Θ x z
        = Submission.BoseGases.chiScale ℓ z
          * ((∫ y : E3, Submission.BoseGases.chiScale ℓ y * Work.BoseFixR.W1fun v h ℓ (y - z))
            * Work.BoseBoxFock.PCFU.wordF fc κ ℓ i j Θ x z) := by ring
    rw [hre, ← MeasureTheory.integral_mul_const, ← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    ring
  rw [hL, hR]
  exact MeasureTheory.integral_integral_swap
    (μ := (volume : Measure E3)) (ν := (volume : Measure E3))
    (f := fun a b : E3 => Submission.BoseGases.chiScale ℓ a * Work.BoseFixR.W1fun v h ℓ (a - b)
      * Submission.BoseGases.chiScale ℓ b
      * Work.BoseBoxFock.PCFU.wordF fc κ ℓ i j Θ x b) hint

end Work.BoseBoxFock.PCFU
