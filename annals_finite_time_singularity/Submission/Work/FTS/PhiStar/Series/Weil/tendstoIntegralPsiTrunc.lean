/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Weil/tendstoIntegralPsiTrunc` — the left-hand side limit of the truncated weak identity

For a test function `φ` of class `C^∞` with compact support in the open quadrant
`Q0 = (0,∞) × (0,π/2)` and a source whose truncated mode series
`psiTrunc α (RemSource α ψ) N` is uniformly bounded on every box of the quadrant and converges
uniformly there to the mode series `R α ψ`, the integrals

  `∫_{Q0} psiTrunc α (RemSource α ψ) N · (bslOp α φ) · z^((5-α)/α) cos θ`

converge to `∫_{Q0} R α ψ · (bslOp α φ) · z^((5-α)/α) cos θ`.

**Proof.**  `φ` is supported in a compact box `K = [a,b] × [c,d] ⊆ Q0` with `d < π/2`
(`box_of_compactSupport`), and `bslOp α φ` vanishes off the *closed* box `K`
(`bslOp_eq_zero_off_box`), so both integrals may be restricted to `K` (`setIntegral_Q0_eq_box`).
On `K` the hypothesis `hbox` gives a uniform bound `B` on all partial sums and, for every
`ε > 0`, an index from which on all partial sums are within `ε` of the limit.  The partial sums
are a.e. strongly measurable on `K`: each radial coefficient is

  `acoeff α m (RemSource α ψ) = (α² · bmode m ψ) · radGreen α m (𝒜φ)`   (`acoeff_RemSource`),

hence, by `aesm_radGreen_phiA` (the measurability of the modal Green function of a *measurable*
source), a finite sum of products of a measurable function of `z` with a continuous function of
`θ`.  The limit `R α ψ` is therefore a.e. strongly measurable as well
(`aestronglyMeasurable_of_tendsto_ae`) and bounded on `K` by `B + 1`.  Both integrands are then
dominated by a multiple of `‖bslOp α φ · z^((5-α)/α) cos θ‖`, which is integrable on the compact
box `K`, and the ε-argument concludes.

The file also contains the measurability facts used above: `measurable_phiA`, the measurability
of parameter-dependent interval/tail integrals of a measurable function
(`aesm_intervalIntegral_mul_rpow`, `aesm_IoiIntegral_mul_rpow`) and their consequence
`aesm_radGreen`.

Note on the statement: the box hypothesis uses `d < π / 2`, where `π` is `Real.pi` (the file
opens the `Real` notation scope, as the rest of the project does; the angular end of the boxes
of the open quadrant is `Real.pi / 2`).

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.PhiStar.Series.Weil.Defs
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.EllipticEst.ModalSolution.box_of_compactSupport
import Submission.Work.FTS.H2.ModalSolR.PerModeBasic
import Submission.Work.FTS.H2.ModalSolR.PerMode
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.ClassC.psiTrunc_uncurry_smooth
import Submission.Work.FTS.PhiStar.Radial.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series.Weil

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Measurability of `𝒜φ = phiA α` -/

/-- `𝒜φ = phiA α = αz²φ'' + (5+α)zφ'` is measurable: it is a combination of `deriv` and
`iteratedDeriv 2`, and `deriv` is universally measurable (`measurable_deriv`). -/
theorem measurable_phiA (α : ℝ) : Measurable (Work.FTS.VocabO.phiA α) := by
  have h2 : Measurable (iteratedDeriv 2 Work.FTS.VocabO.phiR) := by
    have h : iteratedDeriv 2 Work.FTS.VocabO.phiR = deriv (deriv Work.FTS.VocabO.phiR) := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    rw [h]
    exact measurable_deriv _
  have h1 : Measurable (deriv Work.FTS.VocabO.phiR) := measurable_deriv _
  have hA : Measurable (fun z : ℝ => α * z ^ 2) :=
    measurable_const.mul (measurable_id.pow_const 2)
  have hB : Measurable (fun z : ℝ => (5 + α) * z) := measurable_const.mul measurable_id
  change Measurable (fun z : ℝ => α * z ^ 2 * iteratedDeriv 2 Work.FTS.VocabO.phiR z
    + (5 + α) * z * deriv Work.FTS.VocabO.phiR z)
  exact (hA.mul h2).add (hB.mul h1)

/-! ## Measurability of parameter-dependent integrals -/

/-- The joint integrand of the interval integral `z ↦ ∫_0^z F` on a *variable* interval:
`(z,t) ↦ 1_{(0,z]}(t)·F t·t^s`. -/
def jointIoc (F : ℝ → ℝ) (s : ℝ) : ℝ × ℝ → ℝ :=
  fun p => if p.2 ∈ Set.Ioc (0 : ℝ) p.1 then F p.2 * p.2 ^ s else 0

/-- The joint integrand of the tail integral `z ↦ ∫_{Ioi z} F`:
`(z,t) ↦ 1_{(z,∞)}(t)·F t·t^s`. -/
def jointIoi (F : ℝ → ℝ) (s : ℝ) : ℝ × ℝ → ℝ :=
  fun p => if p.2 ∈ Set.Ioi p.1 then F p.2 * p.2 ^ s else 0

theorem jointIoc_measurable {F : ℝ → ℝ} (hF : Measurable F) (s : ℝ) :
    Measurable (jointIoc F s) := by
  change Measurable (fun p : ℝ × ℝ =>
    if p.2 ∈ Set.Ioc (0 : ℝ) p.1 then F p.2 * p.2 ^ s else 0)
  refine Measurable.ite ?_ ((hF.comp measurable_snd).mul (measurable_snd.pow_const s))
    measurable_const
  exact (measurableSet_lt (measurable_const : Measurable fun _ : ℝ × ℝ => (0 : ℝ))
      measurable_snd).inter (measurableSet_le measurable_snd measurable_fst)

theorem jointIoi_measurable {F : ℝ → ℝ} (hF : Measurable F) (s : ℝ) :
    Measurable (jointIoi F s) := by
  change Measurable (fun p : ℝ × ℝ =>
    if p.2 ∈ Set.Ioi p.1 then F p.2 * p.2 ^ s else 0)
  refine Measurable.ite ?_ ((hF.comp measurable_snd).mul (measurable_snd.pow_const s))
    measurable_const
  exact measurableSet_lt measurable_fst measurable_snd

/-- **The primitive of a measurable function is a.e. strongly measurable.**  For `z > 0`,
`z ↦ ∫_0^z F(t)t^s dt` is the partial integral of the jointly measurable function
`jointIoc F s`, whence the a.e. strong measurability by
`AEStronglyMeasurable.integral_prod_right'`. -/
theorem aesm_intervalIntegral_mul_rpow (F : ℝ → ℝ) (hF : Measurable F) (s : ℝ) :
    AEStronglyMeasurable (fun z : ℝ => ∫ t in (0 : ℝ)..z, F t * t ^ s)
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) := by
  have h1 : AEStronglyMeasurable (fun z : ℝ => ∫ t, jointIoc F s (z, t) ∂(volume : Measure ℝ))
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) :=
    (jointIoc_measurable hF s).aestronglyMeasurable
      (μ := ((volume : Measure ℝ).restrict (Set.Ioi 0)).prod (volume : Measure ℝ))
      |>.integral_prod_right'
  refine h1.congr ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
  rw [intervalIntegral.integral_of_le hz.le,
    ← MeasureTheory.integral_indicator measurableSet_Ioc]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => by
    by_cases h : t ∈ Set.Ioc (0 : ℝ) z <;> simp [h, jointIoc, Set.indicator_apply])

/-- **The tail integral of a measurable function is a.e. strongly measurable.** -/
theorem aesm_IoiIntegral_mul_rpow (F : ℝ → ℝ) (hF : Measurable F) (s : ℝ) :
    AEStronglyMeasurable (fun z : ℝ => ∫ t in Set.Ioi z, F t * t ^ s)
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) := by
  have h1 : AEStronglyMeasurable (fun z : ℝ => ∫ t, jointIoi F s (z, t) ∂(volume : Measure ℝ))
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) :=
    (jointIoi_measurable hF s).aestronglyMeasurable
      (μ := ((volume : Measure ℝ).restrict (Set.Ioi 0)).prod (volume : Measure ℝ))
      |>.integral_prod_right'
  refine h1.congr ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z _hz
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => by
    by_cases h : t ∈ Set.Ioi z <;> simp [h, jointIoi, Set.indicator_apply])

/-- **The modal radial Green function of a measurable source is a.e. strongly measurable.**
`radGreen α m c` is a sum of the two parameter-dependent integrals above, multiplied by the
measurable powers `z^{-(2m+5)/α}` and `z^{2m/α}`. -/
theorem aesm_radGreen (α : ℝ) (m : ℕ) {c : ℝ → ℝ} (hc : Measurable c) :
    AEStronglyMeasurable (fun z : ℝ => Work.FTS.PhiStar.Radial.radGreen α m c z)
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) := by
  have h1 : AEStronglyMeasurable
      (fun z : ℝ => ∫ t in (0 : ℝ)..z, c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) :=
    aesm_intervalIntegral_mul_rpow c hc ((2 * (m : ℝ) + 5) / α - 1)
  have h2 : AEStronglyMeasurable
      (fun z : ℝ => ∫ t in Set.Ioi z, c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) :=
    aesm_IoiIntegral_mul_rpow c hc (-(2 * (m : ℝ) / α) - 1)
  have hz1 : AEStronglyMeasurable (fun z : ℝ => z ^ (-(2 * (m : ℝ) + 5) / α))
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) := by
    have hcont : ContinuousOn (fun z : ℝ => z ^ (-(2 * (m : ℝ) + 5) / α)) (Set.Ioi 0) :=
      continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht))
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have hz2 : AEStronglyMeasurable (fun z : ℝ => z ^ (2 * (m : ℝ) / α))
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) := by
    have hcont : ContinuousOn (fun z : ℝ => z ^ (2 * (m : ℝ) / α)) (Set.Ioi 0) :=
      continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht))
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have hmain : AEStronglyMeasurable (fun z : ℝ => 1 / (α * (4 * (m : ℝ) + 5)) *
      (z ^ (-(2 * (m : ℝ) + 5) / α)
          * (∫ t in (0 : ℝ)..z, c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
        + z ^ (2 * (m : ℝ) / α)
          * (∫ t in Set.Ioi z, c t * t ^ (-(2 * (m : ℝ) / α) - 1))))
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) :=
    ((hz1.mul h1).add (hz2.mul h2)).const_mul _
  exact hmain.congr (Filter.Eventually.of_forall fun z => rfl)

/-- The modal radial Green function for the specific source `𝒜φ` of the `Φ_*` construction. -/
theorem aesm_radGreen_phiA (α : ℝ) (m : ℕ) :
    AEStronglyMeasurable
      (fun z : ℝ => Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z)
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) :=
  aesm_radGreen α m (measurable_phiA α)

/-! ## The limit theorem -/

theorem tendstoIntegralPsiTrunc {α : ℝ} {ψ : ℝ → ℝ}
    (hbox : ∀ (a b c d : ℝ), 0 < a → a ≤ b → 0 < c → c ≤ d → d < π / 2 →
      (∃ B : ℝ, ∀ (N : ℕ) (p : ℝ × ℝ), p ∈ Work.FTS.PhiStar.Series.Weil.box a b c d →
        |Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N p.1 p.2| ≤ B) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ p : ℝ × ℝ,
        p ∈ Work.FTS.PhiStar.Series.Weil.box a b c d →
        |Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) n p.1 p.2
          - Work.FTS.PhiStar.Series.Weil.R α ψ p.1 p.2| ≤ ε))
    {φ : ℝ → ℝ → ℝ} (hφ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ))
    (hφc : HasCompactSupport (Function.uncurry φ))
    (hφs : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0) :
    Filter.Tendsto (fun N : ℕ => ∫ p in Work.FTS.EllipticEst.Q0,
        Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N p.1 p.2
          * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      Filter.atTop
      (nhds (∫ p in Work.FTS.EllipticEst.Q0,
        Work.FTS.PhiStar.Series.Weil.R α ψ p.1 p.2
          * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2))) := by
  classical
  -- ## Step 1: the compact box containing the support of the test function
  obtain ⟨a, b, c, d, ha, hab, hc, hcd, hd, hboxopen⟩ :=
    Work.EllipticEst.ModalSolution.box_of_compactSupport hφc hφs
  obtain ⟨hbdd, hconv⟩ := hbox a b c d ha hab.le hc hcd.le hd
  obtain ⟨B, hB⟩ := hbdd
  let K : Set (ℝ × ℝ) := Work.FTS.PhiStar.Series.Weil.box a b c d
  have hKdef : K = Set.Icc a b ×ˢ Set.Icc c d := rfl
  have hKmeas : MeasurableSet K := by
    rw [hKdef]
    exact measurableSet_Icc.prod measurableSet_Icc
  have hKcomp : IsCompact K := by
    rw [hKdef]
    exact isCompact_Icc.prod isCompact_Icc
  have hKsub : K ⊆ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.PhiStar.Series.Weil.box_subset_Q0 ha hab.le hc hcd.le hd
  have hφ0 : ∀ p : ℝ × ℝ, p ∉ K → φ p.1 p.2 = 0 := by
    intro p hp
    refine hboxopen p (fun hmem => hp ?_)
    exact ⟨⟨hmem.1.1.le, hmem.1.2.le⟩, ⟨hmem.2.1.le, hmem.2.2.le⟩⟩
  have hbsl0 : ∀ p : ℝ × ℝ, p ∉ K → Work.Elliptic.bslOp α φ p.1 p.2 = 0 := by
    intro p hp
    refine Work.FTS.H2.ModalSolR.bslOp_eq_zero_off_box hboxopen ?_
    simpa only [hKdef] using hp
  -- ## Step 2: the weight against which we integrate
  set g : ℝ × ℝ → ℝ :=
    fun p => Work.Elliptic.bslOp α φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2) with hg
  have hφsm : Work.FTS.EllipticEst.SmoothOpen φ :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall φ).mpr (fun n => (hφ n).contDiffOn)
  have hgc : ContinuousOn g K := by
    rw [hg, hKdef]
    refine ContinuousOn.mul
      ((Work.FTS.H2.ModalSolR.continuousOn_bslOp hφsm).mono hKsub) ?_
    exact (continuousOn_fst.rpow_const (fun p hp => Or.inl (ne_of_gt (hKsub hp).1))).mul
      ((Real.continuous_cos.comp continuous_snd).continuousOn)
  have hgint : Integrable (fun p : ℝ × ℝ => ‖g p‖)
      ((volume : Measure (ℝ × ℝ)).restrict K) :=
    hgc.norm.integrableOn_compact hKcomp
  -- ## Step 3: measurability of the partial sums and of the limit
  have hQ0prod : (volume : Measure (ℝ × ℝ)).restrict Work.FTS.EllipticEst.Q0
      = ((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
        ((volume : Measure ℝ).restrict (Set.Ioo 0 (π / 2))) := by
    rw [Work.FTS.EllipticEst.Q0, MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    exact (MeasureTheory.Measure.prod_restrict (Set.Ioi 0) (Set.Ioo 0 (π / 2))).symm
  have haesm_psiTrunc (N : ℕ) : AEStronglyMeasurable
      (fun p : ℝ × ℝ =>
        Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N p.1 p.2)
      ((volume : Measure (ℝ × ℝ)).restrict Work.FTS.EllipticEst.Q0) := by
    have hterm : ∀ m ∈ Finset.range (N + 1), AEStronglyMeasurable
        (fun p : ℝ × ℝ => (α ^ 2 * Work.FTS.PhiStar.Series.bmode m ψ)
          * Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) p.1
          * Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
        ((volume : Measure (ℝ × ℝ)).restrict Work.FTS.EllipticEst.Q0) := by
      intro m _
      have h1 : AEStronglyMeasurable
          (fun p : ℝ × ℝ =>
            Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) p.1)
          ((volume : Measure (ℝ × ℝ)).restrict Work.FTS.EllipticEst.Q0) := by
        rw [hQ0prod]
        exact (aesm_radGreen_phiA α m).comp_quasiMeasurePreserving
          MeasureTheory.Measure.quasiMeasurePreserving_fst
      have h2 : AEStronglyMeasurable
          (fun p : ℝ × ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m p.2)
          ((volume : Measure (ℝ × ℝ)).restrict Work.FTS.EllipticEst.Q0) :=
        (((Work.FTS.ClassC.contDiff_eFam_nat m 1).continuous.measurable).comp
          measurable_snd).aestronglyMeasurable
      exact (h1.const_mul _).mul h2
    have hsum := Finset.aestronglyMeasurable_sum (Finset.range (N + 1)) hterm
    refine hsum.congr ?_
    filter_upwards with p
    simp only [Finset.sum_apply, Work.FTS.PhiStar.Series.psiTrunc]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Work.FTS.PhiStar.Series.acoeff_RemSource]
  have hpsiK (N : ℕ) : AEStronglyMeasurable
      (fun p : ℝ × ℝ =>
        Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N p.1 p.2)
      ((volume : Measure (ℝ × ℝ)).restrict K) :=
    (haesm_psiTrunc N).mono_set hKsub
  have haesm_R : AEStronglyMeasurable (fun p : ℝ × ℝ => R α ψ p.1 p.2)
      ((volume : Measure (ℝ × ℝ)).restrict K) := by
    refine aestronglyMeasurable_of_tendsto_ae atTop (fun N => hpsiK N) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hKmeas] with p hp
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := hconv (ε / 2) (by linarith)
    exact ⟨N, fun n hn => by
      rw [Real.dist_eq]
      linarith [hN n hn p hp]⟩
  -- ## Step 4: integrability of the two integrands on the box
  obtain ⟨N₁, hN₁⟩ := hconv 1 one_pos
  have hRb : ∀ p : ℝ × ℝ, p ∈ K → |R α ψ p.1 p.2| ≤ B + 1 := by
    intro p hp
    have h1 : |Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N₁ p.1 p.2
        - R α ψ p.1 p.2| ≤ 1 := hN₁ N₁ le_rfl p hp
    have h2 : |Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N₁ p.1 p.2|
        ≤ B := hB N₁ p hp
    calc |R α ψ p.1 p.2|
        = |R α ψ p.1 p.2
            - Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N₁ p.1 p.2
            + Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N₁ p.1 p.2| :=
          by ring_nf
      _ ≤ |R α ψ p.1 p.2
            - Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N₁ p.1 p.2|
          + |Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N₁ p.1 p.2| :=
          abs_add_le _ _
      _ ≤ 1 + B := by
          rw [abs_sub_comm]
          exact add_le_add h1 h2
      _ = B + 1 := by ring
  have hAint (N : ℕ) : Integrable
      (fun p : ℝ × ℝ =>
        Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N p.1 p.2 * g p)
      ((volume : Measure (ℝ × ℝ)).restrict K) := by
    refine Integrable.mono' (hgint.const_mul B)
      ((hpsiK N).mul (hgc.aestronglyMeasurable hKmeas)) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hKmeas] with p hp
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hB N p hp) (abs_nonneg _)
  have hBint : Integrable (fun p : ℝ × ℝ => R α ψ p.1 p.2 * g p)
      ((volume : Measure (ℝ × ℝ)).restrict K) := by
    refine Integrable.mono' (hgint.const_mul (B + 1))
      (haesm_R.mul (hgc.aestronglyMeasurable hKmeas)) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hKmeas] with p hp
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hRb p hp) (abs_nonneg _)
  -- ## Step 5: the ε-argument on the box
  have hmain : Filter.Tendsto (fun N : ℕ => ∫ p in K,
        Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N p.1 p.2 * g p)
      Filter.atTop (nhds (∫ p in K, R α ψ p.1 p.2 * g p)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hDnn : 0 ≤ ∫ p in K, ‖g p‖ :=
      integral_nonneg fun p => norm_nonneg _
    have hden : (0 : ℝ) < (∫ p in K, ‖g p‖) + 1 := by linarith
    have hpos : 0 < ε / 2 / ((∫ p in K, ‖g p‖) + 1) :=
      div_pos (by linarith) hden
    obtain ⟨N, hN⟩ := hconv (ε / 2 / ((∫ p in K, ‖g p‖) + 1)) hpos
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq, ← Real.norm_eq_abs, ← MeasureTheory.integral_sub (hAint n) hBint]
    calc ‖∫ p in K, (Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ)
            n p.1 p.2 * g p - R α ψ p.1 p.2 * g p)‖
        ≤ ∫ p in K, ‖Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ)
            n p.1 p.2 * g p - R α ψ p.1 p.2 * g p‖ :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ p in K, ε / 2 / ((∫ p in K, ‖g p‖) + 1) * ‖g p‖ := by
          refine MeasureTheory.integral_mono_ae ((hAint n).sub hBint).norm
            (hgint.const_mul _) ?_
          filter_upwards [MeasureTheory.ae_restrict_mem hKmeas] with p hp
          have hsub : Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ)
                n p.1 p.2 * g p - R α ψ p.1 p.2 * g p
              = (Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ)
                n p.1 p.2 - R α ψ p.1 p.2) * g p := by ring
          rw [hsub, norm_mul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (hN n hn p hp) (abs_nonneg _)
      _ = ε / 2 / ((∫ p in K, ‖g p‖) + 1) * (∫ p in K, ‖g p‖) := by
          rw [MeasureTheory.integral_const_mul]
      _ ≤ ε / 2 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hden]
          nlinarith [hDnn]
      _ < ε := by linarith
  -- ## Step 6: transfer the statement back to the quadrant
  have hvanA : ∀ N : ℕ, (∫ p in Work.FTS.EllipticEst.Q0,
        Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N p.1 p.2
          * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      = ∫ p in K,
        Work.FTS.PhiStar.Series.psiTrunc α (Work.FTS.PhiStar.RemSource α ψ) N p.1 p.2 * g p := by
    intro N
    rw [Work.FTS.H2.ModalSolR.setIntegral_Q0_eq_box hKmeas hKsub (fun p hp => by
      rw [hbsl0 p hp.2]
      ring)]
    refine MeasureTheory.setIntegral_congr_fun hKmeas (fun p _ => ?_)
    simp only [hg]
    ring
  have hvanB : (∫ p in Work.FTS.EllipticEst.Q0,
        Work.FTS.PhiStar.Series.Weil.R α ψ p.1 p.2
          * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      = ∫ p in K, R α ψ p.1 p.2 * g p := by
    rw [Work.FTS.H2.ModalSolR.setIntegral_Q0_eq_box hKmeas hKsub (fun p hp => by
      rw [hbsl0 p hp.2]
      ring)]
    refine MeasureTheory.setIntegral_congr_fun hKmeas (fun p _ => ?_)
    simp only [hg]
    ring
  rw [funext hvanA, hvanB]
  exact hmain

end Work.FTS.PhiStar.Series.Weil
