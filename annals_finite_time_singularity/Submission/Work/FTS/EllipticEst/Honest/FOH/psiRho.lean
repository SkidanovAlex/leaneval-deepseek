import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.Honest.HonSliceFinite
import Submission.Work.FTS.EllipticEst.Honest.HonSliceAeYc
import Submission.Work.FTS.EllipticEst.Honest.Gap9Open
import Submission.Work.FTS.EllipticEst.Honest.SigmaPoincare
import Submission.Work.FTS.EllipticEst.Honest.HR2.Prep
import Submission.Work.FTS.EllipticEst.Honest.HR2.HkMemU
import Submission.Work.FTS.EllipticEst.Honest.HR2.HonToAe
import Submission.Work.FTS.EllipticEst.Honest.hksq_eq_w2_sliceIntegral
import Submission.Work.FTS.EllipticEst.Honest.honSliceIntFacts
import Submission.Work.FTS.EllipticEst.Honest.honLintegralSliceBridge
import Submission.Work.FTS.EllipticEst.Honest.FOH.bridge
import Submission.Work.FTS.EllipticEst.Honest.Step1G.EnergyG

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest.FOH

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

open MeasureTheory Set Filter
open scoped ENNReal Topology

variable {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}

/-! ## The three `∫⁻`-functionals of the unweighted (in `θ`) first-order estimate -/

/-- The unweighted-in-`θ` mass functional `∫⁻_z w² ∫⁻_θ Ψ²`. -/
noncomputable def Mu (Ψ : ℝ → ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
    (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Ψ z θ) ^ 2))

/-- The unweighted-in-`θ` angular-gradient functional `∫⁻_z w² ∫⁻_θ (∂_θΨ)²`. -/
noncomputable def Gu (Ψ : ℝ → ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
    (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth Ψ z θ) ^ 2))

/-- The `σ`-weighted mass functional `∫⁻_z w² ∫⁻_θ Ψ² σ`. -/
noncomputable def Ys (Ψ : ℝ → ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
    (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
      ((Ψ z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ))

/-- The `θ`-slice of an honest datum is `C²` on the open interval. -/
theorem slice_contDiffOn (h : Hon α F Ψ) {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ 2 (fun θ : ℝ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have h1 : ContDiffOn ℝ 2 (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    h.sm 2
  have h2 : ContDiffOn ℝ 2 (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
  have h3 := h1.comp h2 (fun θ hθ => Set.mem_prod.mpr ⟨hz, hθ⟩)
  exact h3

/-- The `z`-variable is positive almost everywhere for `volume.restrict Iz`. -/
theorem ae_pos_Iz : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
  rw [HR2.restrict_Iz_eq_restrict_Ioi]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioi

/-! ## The unweighted constrained gap, integrated against `w²` -/

/-- **The constrained slice gap `9∫u² ≤ ∫(u')²` (`Gap9Open`), integrated against `w²`.** -/
theorem gapMu (h : Hon α F Ψ) : (9 : ℝ≥0∞) * Mu Ψ ≤ Gu Ψ := by
  have hae := HonSliceAeYc α F Ψ h
  have hkeyIoi : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      9 * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Ψ z θ) ^ 2))
        ≤ (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth Ψ z θ) ^ 2)) := by
    filter_upwards [hae, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz hzpos
    simp only [Work.Spaces.pth]
    obtain ⟨hl0, hlπ, hint⟩ := hz
    have hcd : ContDiffOn ℝ 2 (fun θ : ℝ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
      slice_contDiffOn h hzpos
    have hcont : ContinuousOn (fun θ : ℝ => Ψ z θ) (Set.Icc 0 (Real.pi / 2)) :=
      HR2.continuousOn_Icc_of_limits (by positivity) hcd (h.d0 z) (h.dπ z) hl0 hlπ
    have hLI : MeasureTheory.IntegrableOn
        (fun θ : ℝ => ((fun θ : ℝ => Ψ z θ) θ) ^ 2) Work.Spaces.Iθ :=
      (hcont.pow 2).integrableOn_compact isCompact_Icc
    have horth : (∫ θ in Work.Spaces.Iθ,
        (fun θ : ℝ => Ψ z θ) θ * Work.Elliptic.sinCos2 θ) = 0 := by
      simpa only [Work.Elliptic.Fstar] using h.orthΨ z
    have hgap := Gap9Open (fun θ : ℝ => Ψ z θ) hcd hcont (h.d0 z) (h.dπ z) hint horth
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hLI
        (Eventually.of_forall fun θ => sq_nonneg _),
      ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
        (Eventually.of_forall fun θ => sq_nonneg _)]
    rw [show (9 : ℝ≥0∞) = ENNReal.ofReal (9 : ℝ) from by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 9)]
    exact ENNReal.ofReal_le_ofReal (by simpa only [Work.Spaces.pth] using hgap)
  have hkey : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      9 * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Ψ z θ) ^ 2))
        ≤ (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth Ψ z θ) ^ 2)) := by
    rw [HR2.restrict_Iz_eq_restrict_Ioi]
    exact hkeyIoi
  calc (9 : ℝ≥0∞) * Mu Ψ
      = ∫⁻ z in Work.Spaces.Iz, 9 * (ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
          (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Ψ z θ) ^ 2))) := by
        rw [Mu]
        exact (MeasureTheory.lintegral_const_mul' 9 _ (by norm_num)).symm
    _ = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
          (9 * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Ψ z θ) ^ 2))) := by
        refine MeasureTheory.lintegral_congr fun z => by ring
    _ ≤ ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
          (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth Ψ z θ) ^ 2)) := by
        refine MeasureTheory.lintegral_mono_ae ?_
        filter_upwards [hkey] with z hz
        exact mul_le_mul' le_rfl hz
    _ = Gu Ψ := rfl

/-! ## The `σ`-weighted mass is controlled by the unweighted angular gradient -/

/-- **The `σ`-weighted `θ`-Poincaré inequality, integrated against `w²`**: from the *slicewise*
`σ`-Poincaré inequality (as supplied by `SigmaPoincare`) one gets `Ys Ψ ≤ ofReal Cσ · Gu Ψ`. -/
theorem Ys_le_Gu_of {Cσ : ℝ}
    (hsl : ∀ f : ℝ → ℝ, ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn (fun θ => f θ * (Real.sin θ * Real.cos θ ^ 2)) Work.Spaces.Iθ →
      (∫ θ in Work.Spaces.Iθ, f θ * Real.sin θ * Real.cos θ ^ 2) = 0 →
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
          ((f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
        ≤ ENNReal.ofReal Cσ *
          (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((deriv f θ) ^ 2)))
    (h : Hon α F Ψ) : Ys Ψ ≤ ENNReal.ofReal Cσ * Gu Ψ := by
  have hae := HonSliceAeYc α F Ψ h
  have hkeyIoi : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
        ((Ψ z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ))
        ≤ ENNReal.ofReal Cσ *
          (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((Work.Spaces.pth Ψ z θ) ^ 2)) := by
    filter_upwards [hae, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz hzpos
    obtain ⟨hl0, hlπ, _⟩ := hz
    have hcd2 : ContDiffOn ℝ 2 (fun θ : ℝ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
      slice_contDiffOn h hzpos
    have hcd1 : ContDiffOn ℝ 1 (fun θ : ℝ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
      hcd2.of_le (by norm_num)
    have hcont : ContinuousOn (fun θ : ℝ => Ψ z θ) (Set.Icc 0 (Real.pi / 2)) :=
      HR2.continuousOn_Icc_of_limits (by positivity) hcd2 (h.d0 z) (h.dπ z) hl0 hlπ
    have hint2 : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (fun θ : ℝ => Ψ z θ) θ * (Real.sin θ * Real.cos θ ^ 2))
        Work.Spaces.Iθ := by
      have hc : ContinuousOn
          (fun θ : ℝ => (fun θ : ℝ => Ψ z θ) θ * (Real.sin θ * Real.cos θ ^ 2))
          Work.Spaces.Iθ := hcont.mul (by fun_prop)
      exact hc.integrableOn_compact isCompact_Icc
    have horth : (∫ θ in Work.Spaces.Iθ,
        (fun θ : ℝ => Ψ z θ) θ * (Real.sin θ * Real.cos θ ^ 2)) = 0 := by
      simpa only [Work.Elliptic.Fstar, Work.Elliptic.sinCos2] using h.orthΨ z
    have horth' : (∫ θ in Work.Spaces.Iθ,
        (fun θ : ℝ => Ψ z θ) θ * Real.sin θ * Real.cos θ ^ 2) = 0 := by
      simpa only [mul_assoc] using horth
    have hres := hsl (fun θ : ℝ => Ψ z θ) hcd1 hint2 horth'
    simpa only [Work.Spaces.pth, Work.FTS.EllipticEst.sEta,
      Work.FTS.EllipticEst.AngSecond.sig] using hres
  have hkey : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
        ((Ψ z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ))
        ≤ ENNReal.ofReal Cσ *
          (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((Work.Spaces.pth Ψ z θ) ^ 2)) := by
    rw [HR2.restrict_Iz_eq_restrict_Ioi]
    exact hkeyIoi
  calc Ys Ψ
      = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
          (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
            ((Ψ z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)) := rfl
    _ ≤ ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
          (ENNReal.ofReal Cσ * (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((Work.Spaces.pth Ψ z θ) ^ 2))) := by
        refine MeasureTheory.lintegral_mono_ae ?_
        filter_upwards [hkey] with z hz
        exact mul_le_mul' le_rfl hz
    _ = ENNReal.ofReal Cσ * ∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
          (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth Ψ z θ) ^ 2)) := by
        rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal Cσ) _
          ENNReal.ofReal_ne_top]
        refine MeasureTheory.lintegral_congr fun z => by ring
    _ = ENNReal.ofReal Cσ * Gu Ψ := rfl

/-! ## The unweighted angular gradient is bounded by `HkSq α 0 F` -/

/-- The coefficient `K(α) = 13/2 + 3α² + (3/2)α(5+α)` of the radial weight transfer. -/
noncomputable def Kcoef (α : ℝ) : ℝ := 13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α))

theorem Kcoef_le (hα : 0 < α) (hα4 : α ≤ 1 / 4) : Kcoef α ≤ 26 / 3 := by
  rw [Kcoef]
  nlinarith [hα, hα4, sq_nonneg α]

theorem Kcoef_nonneg (hα : 0 < α) : (0 : ℝ) ≤ Kcoef α := by
  rw [Kcoef]; nlinarith [hα, sq_nonneg α]

/-- **The honesty of `Ψ` and the finiteness of the unweighted mass.** -/
theorem hkMem_of_hon (h : Hon α F Ψ) : Work.Spaces.HkMem α 0 Ψ :=
  Work.FTS.EllipticEst.H2W.Ae.hr2_hkMem_u α Ψ F (HR2.hon_to_ae h)

theorem Ys_eq (h : Hon α F Ψ) :
    Ys Ψ = ENNReal.ofReal (Work.Spaces.HkSq α 0 Ψ) := by
  rw [Ys]
  exact lintegral_sig_eq_ofReal_HkSq (hkMem_of_hon h)

theorem Mu_le (h : Hon α F Ψ) : Mu Ψ ≤ Ys Ψ := by
  refine MeasureTheory.lintegral_mono_ae ?_
  refine Eventually.of_forall fun z => mul_le_mul' le_rfl ?_
  refine MeasureTheory.lintegral_mono_ae ?_
  filter_upwards [ae_mem_Ioo_Iθ'] with θ hθ
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : 1 ≤ Work.FTS.EllipticEst.sEta θ := one_le_sEta_Ioo hθ
  have h2 : (0 : ℝ) ≤ (Ψ z θ) ^ 2 := sq_nonneg _
  calc (Ψ z θ) ^ 2 = 1 * (Ψ z θ) ^ 2 := (one_mul _).symm
    _ ≤ Work.FTS.EllipticEst.sEta θ * (Ψ z θ) ^ 2 :=
        mul_le_mul_of_nonneg_right h1 h2
    _ = (Ψ z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ := mul_comm _ _

/-- **The unweighted angular gradient is bounded by `HkSq α 0 F`.**  The explicit energy
inequality `Step1G.EnergyG` plus the constrained gap `9∫Ψ² ≤ ∫(∂_θΨ)²` (the constant
`26/3 < 9` leaves the room `1/27`). -/
theorem Gu_le (h : Hon α F Ψ) :
    Gu Ψ ≤ ENNReal.ofReal (234 * Work.Spaces.HkSq α 0 F) := by
  have hmem : Work.Spaces.HkMem α 0 Ψ := hkMem_of_hon h
  have hYseq := Ys_eq h
  have hMu := Mu_le h
  have h0le : (0 : ℝ) ≤ Work.Spaces.HkSq α 0 F := HkSq_zero_nonneg α F
  -- the source mass `Mu` is finite
  have hMutop : Mu Ψ ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ hMu
    rw [hYseq]
    exact ENNReal.ofReal_ne_top
  -- the energy inequality, with the LHS's extra `α²`-term dropped
  have hen := Step1G.EnergyG α F Ψ h
  have hGu_le : Gu Ψ ≤ ENNReal.ofReal (Kcoef α) *
      (Mu Ψ + ENNReal.ofReal (Work.Spaces.HkSq α 0 F)) := by
    have h1 : Gu Ψ ≤ ENNReal.ofReal (Kcoef α) * Mu Ψ
        + ENNReal.ofReal (1 / 2) * ENNReal.ofReal (Work.Spaces.HkSq α 0 F) := by
      have h0 : Gu Ψ ≤ (ENNReal.ofReal (α ^ 2) *
            (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) *
              (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
                ((z * Work.Spaces.pz Ψ z θ) ^ 2)))) + Gu Ψ :=
        le_add_of_nonneg_left bot_le
      refine le_trans h0 ?_
      rw [Kcoef]
      exact hen
    have h12 : ENNReal.ofReal (1 / 2 : ℝ) ≤ ENNReal.ofReal (Kcoef α) :=
      ENNReal.ofReal_le_ofReal (by rw [Kcoef]; nlinarith [h.hα, sq_nonneg α])
    have hb : ENNReal.ofReal (1 / 2) * ENNReal.ofReal (Work.Spaces.HkSq α 0 F)
        ≤ ENNReal.ofReal (Kcoef α) * ENNReal.ofReal (Work.Spaces.HkSq α 0 F) :=
      mul_le_mul' h12 le_rfl
    have hgoal : ENNReal.ofReal (Kcoef α) * Mu Ψ
          + ENNReal.ofReal (1 / 2) * ENNReal.ofReal (Work.Spaces.HkSq α 0 F)
        ≤ ENNReal.ofReal (Kcoef α) *
          (Mu Ψ + ENNReal.ofReal (Work.Spaces.HkSq α 0 F)) := by
      rw [mul_add]
      exact add_le_add le_rfl hb
    exact le_trans h1 hgoal
  have hGutop : Gu Ψ ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ hGu_le
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.mpr ⟨hMutop, ENNReal.ofReal_ne_top⟩)
  -- the gap gives `Mu ≤ (9)⁻¹ Gu`
  have hgap := gapMu h
  have hMu_le : Mu Ψ ≤ (9 : ℝ≥0∞)⁻¹ * Gu Ψ := by
    have h9 : (9 : ℝ≥0∞) * Mu Ψ ≤ Gu Ψ := hgap
    calc Mu Ψ = 1 * Mu Ψ := (one_mul _).symm
      _ = ((9 : ℝ≥0∞)⁻¹ * 9) * Mu Ψ := by
          rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
      _ = (9 : ℝ≥0∞)⁻¹ * (9 * Mu Ψ) := by rw [mul_assoc]
      _ ≤ (9 : ℝ≥0∞)⁻¹ * Gu Ψ := mul_le_mul_of_nonneg_left h9 bot_le
  -- the coefficient `c = K/9 < 1`
  set c : ℝ≥0∞ := ENNReal.ofReal (Kcoef α / 9) with hc
  have hc1 : c < 1 := by
    rw [hc, ← ENNReal.ofReal_one]
    rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)]
    have hK := Kcoef_le h.hα h.hα4
    linarith
  have hKnn : (0 : ℝ) ≤ Kcoef α := by
    rw [Kcoef]; nlinarith [h.hα, sq_nonneg α]
  -- the additive constant
  have hstep : Gu Ψ ≤ c * Gu Ψ +
      ENNReal.ofReal (Kcoef α * Work.Spaces.HkSq α 0 F) := by
    have h1 : ENNReal.ofReal (Kcoef α) *
        (Mu Ψ + ENNReal.ofReal (Work.Spaces.HkSq α 0 F))
        ≤ ENNReal.ofReal (Kcoef α) *
          ((9 : ℝ≥0∞)⁻¹ * Gu Ψ + ENNReal.ofReal (Work.Spaces.HkSq α 0 F)) :=
      mul_le_mul' le_rfl (add_le_add hMu_le le_rfl)
    refine le_trans hGu_le (le_trans h1 ?_)
    have h9 : (9 : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((9 : ℝ)⁻¹) := by
      rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 9)]
      norm_num
    have hc9 : ENNReal.ofReal (Kcoef α) * ENNReal.ofReal ((9 : ℝ)⁻¹) = c := by
      rw [hc]
      exact (ENNReal.ofReal_mul hKnn).symm
    rw [mul_add, ← mul_assoc, h9, hc9, ← ENNReal.ofReal_mul hKnn]
  -- solve for `Gu`
  have hcGutop : c * Gu Ψ ≠ ⊤ :=
    ENNReal.mul_ne_top (ne_top_of_lt (lt_of_lt_of_le hc1 le_top)) hGutop
  have h1 : Gu Ψ * (1 - c) ≤ ENNReal.ofReal (Kcoef α * Work.Spaces.HkSq α 0 F) := by
    have hEeq : Gu Ψ = Gu Ψ * (1 - c) + c * Gu Ψ := by
      rw [mul_comm c (Gu Ψ), ← mul_add, tsub_add_cancel_of_le (le_of_lt hc1), mul_one]
    have h5 : Gu Ψ * (1 - c) + c * Gu Ψ ≤
        ENNReal.ofReal (Kcoef α * Work.Spaces.HkSq α 0 F) + c * Gu Ψ := by
      calc Gu Ψ * (1 - c) + c * Gu Ψ = Gu Ψ := hEeq.symm
        _ ≤ c * Gu Ψ + ENNReal.ofReal (Kcoef α * Work.Spaces.HkSq α 0 F) := hstep
        _ = ENNReal.ofReal (Kcoef α * Work.Spaces.HkSq α 0 F) + c * Gu Ψ := by rw [add_comm]
    exact (ENNReal.add_le_add_iff_right hcGutop).mp h5
  have h27 : (27 : ℝ≥0∞)⁻¹ ≤ 1 - c := by
    rw [hc]
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
    rw [show ENNReal.ofReal 1 - ENNReal.ofReal (Kcoef α / 9)
        = ENNReal.ofReal (1 - Kcoef α / 9) from
      (ENNReal.ofReal_sub (p := 1) (q := Kcoef α / 9)
        (hq := div_nonneg (Kcoef_nonneg h.hα) (by norm_num))).symm]
    rw [show ((27 : ℝ≥0∞))⁻¹ = ENNReal.ofReal ((27 : ℝ)⁻¹) from by
      rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 27)]
      norm_num]
    refine ENNReal.ofReal_le_ofReal ?_
    have hK := Kcoef_le h.hα h.hα4
    linarith
  have hEmul : Gu Ψ ≤ ENNReal.ofReal (Kcoef α * Work.Spaces.HkSq α 0 F) * 27 := by
    have h2 : Gu Ψ * (27 : ℝ≥0∞)⁻¹ ≤
        ENNReal.ofReal (Kcoef α * Work.Spaces.HkSq α 0 F) :=
      le_trans (mul_le_mul_of_nonneg_left h27 bot_le) h1
    calc Gu Ψ = Gu Ψ * (27 : ℝ≥0∞)⁻¹ * 27 := by
          rw [mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
      _ ≤ ENNReal.ofReal (Kcoef α * Work.Spaces.HkSq α 0 F) * 27 :=
          mul_le_mul_of_nonneg_right h2 bot_le
  refine le_trans hEmul ?_
  rw [show (27 : ℝ≥0∞) = ENNReal.ofReal (27 : ℝ) from by norm_num]
  rw [← ENNReal.ofReal_mul
    (mul_nonneg (Kcoef_nonneg h.hα) h0le)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hK := Kcoef_le h.hα h.hα4
  nlinarith [h0le, hK]

/-! ## The `ρ`-norm of `Ψ` -/

/-- **The `ρ`-norm of the solution is bounded by the `ρ`-norm of the source**
(the `Ψ`-half of Step 1 of `prop:H2` in the honest class). -/
theorem psiRhoBound :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), Hon α F Ψ →
      Work.Spaces.HkMem α 0 Ψ ∧ Work.Spaces.HkSq α 0 Ψ ≤ C * Work.Spaces.HkSq α 0 F := by
  obtain ⟨Cσ, hCσpos, hCσ⟩ := SigmaPoincare
  refine ⟨Cσ * 234 + 1, by positivity, ?_⟩
  intro α F Ψ h
  have hmem : Work.Spaces.HkMem α 0 Ψ := hkMem_of_hon h
  have hYs : Ys Ψ ≤ ENNReal.ofReal Cσ * Gu Ψ := Ys_le_Gu_of hCσ h
  have hGu : Gu Ψ ≤ ENNReal.ofReal (234 * Work.Spaces.HkSq α 0 F) := Gu_le h
  have hfin : Ys Ψ ≤ ENNReal.ofReal (Cσ * (234 * Work.Spaces.HkSq α 0 F)) := by
    calc Ys Ψ ≤ ENNReal.ofReal Cσ * Gu Ψ := hYs
      _ ≤ ENNReal.ofReal Cσ * ENNReal.ofReal (234 * Work.Spaces.HkSq α 0 F) :=
          mul_le_mul' le_rfl hGu
      _ = ENNReal.ofReal (Cσ * (234 * Work.Spaces.HkSq α 0 F)) := by
          rw [ENNReal.ofReal_mul hCσpos.le]
  refine ⟨hmem, ?_⟩
  have h2 : Work.Spaces.HkSq α 0 Ψ ≤ Cσ * (234 * Work.Spaces.HkSq α 0 F) := by
    have h3 : ENNReal.ofReal (Work.Spaces.HkSq α 0 Ψ)
        ≤ ENNReal.ofReal (Cσ * (234 * Work.Spaces.HkSq α 0 F)) := by
      rw [← Ys_eq h]
      exact hfin
    rw [ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg hCσpos.le (mul_nonneg (by norm_num) (HkSq_zero_nonneg α F)))] at h3
    exact h3
  calc Work.Spaces.HkSq α 0 Ψ ≤ Cσ * (234 * Work.Spaces.HkSq α 0 F) := h2
    _ = (Cσ * 234) * Work.Spaces.HkSq α 0 F := by ring
    _ ≤ (Cσ * 234 + 1) * Work.Spaces.HkSq α 0 F :=
        mul_le_mul_of_nonneg_right (by linarith) (HkSq_zero_nonneg α F)

end Work.FTS.EllipticEst.Honest.FOH
