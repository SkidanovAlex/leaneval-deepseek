import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.Asm
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.fluxSix_noDecay =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `fluxSix` without the decay hypothesis

`Work.FTS.StrongPersist.N6Trans.SixAux.fluxSix` proves the level-six top-slot radial
integration by parts

  `|∫_z∫_θ canonW q z θ · h z θ · D_z(D_z^bD_θ^a g) z θ · D_z^bD_θ^a g z θ| ≤ C M HkSq α 6 g`

for `a + b ≤ 6`, `HkMem α 6 g`, `HkMem α 7 g`, and *additionally* `DecayAll 6 g`.  That last
hypothesis is only used to make the a.e. boundary trace `z·(D_z^bD_θ^a g · w)²` vanish at
`+∞`.  It is in fact unnecessary: `SixAux.trace_slot_ae6` derives the vanishing of that trace
at *both* ends of `(0,∞)` from the `ℋ⁶ ∩ ℋ⁷` integrability alone (the one-dimensional
`H¹`-lemma `N6Trans.Hon.trace_of_weights` applied to the two weighted slots
`w²(D_z^bD_θ^ag)² ≤ HkIntegrand α 6 g` and `w²(D_z^{b+1}D_θ^ag)² ≤ HkIntegrand α 7 g`).

Consequently the *same* proof goes through verbatim with `DecayAll 6 g` dropped; this file
carries that proof (it is a copy of the body of `fluxSix`, with `hdec` removed from the
`intro` -- it was unused there anyway).  The constant `C = 2` still suffices.
-/

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Gen

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.StrongPersist.N6Trans.SixAux

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section
theorem fluxSix_noDecay : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (h g : ℝ → ℝ → ℝ) (a b : ℕ) (q M : ℝ),
    0 < α → α ≤ 1 → 0 ≤ q → q ≤ Work.Spaces.gam α → (a = 0 → q ≤ Work.Spaces.eta) →
    a + b ≤ 6 →
    Work.FTS.EllipticEst.SmoothOpen h → Work.FTS.EllipticEst.SmoothOpen g →
    Work.Spaces.HkMem α 6 g → Work.Spaces.HkMem α 7 g →
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |h z θ| ≤ M) →
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |Work.Spaces.Dz h z θ| ≤ M) →
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.FTS.TransportS.SlotT2.canonW q z θ * h z θ
          * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ|
      ≤ C * M * Work.Spaces.HkSq α 6 g := by
  refine ⟨2, by norm_num, ?_⟩
  intro α h g a b q M hα hα1 hq0 hqγ hqη hab hsh hsg hm6 hm7 hb hDb
  have hMnn : 0 ≤ M := by
    have h1 := hb 1 (Real.pi / 4) (by norm_num) (by positivity) (by linarith [Real.pi_pos])
    exact le_trans (abs_nonneg _) h1
  -- the a.e. angular data
  have hslice6 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn (fun z => Work.Spaces.HkIntegrand α 6 g z θ) Work.Spaces.Iz :=
    Work.FTS.TransportS.ae_integrableOn_slice
      (Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen hsg hm6).1
  have hslice7 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn (fun z => Work.Spaces.HkIntegrand α 7 g z θ) Work.Spaces.Iz :=
    Work.FTS.TransportS.ae_integrableOn_slice
      (Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen hsg hm7).1
  have htrace := trace_slot_ae6 α g a b hα hsg hm6 hm7 hab
  -- the pointwise slot dominations
  have hdom6 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 g z θ := by
    intro z θ _ hθ hθ2
    rcases Nat.eq_zero_or_pos a with ha | ha
    · rw [ha, Work.Spaces.mixed_zero_right]
      exact Work.FTS.TransportS.T2Sup.canonW_mul_z_le_of_le 6 (hqη ha) hθ hθ2 (by omega)
    · exact Work.FTS.TransportS.T2Sup.canonW_mul_mixed_le_of_le 6 hqγ hθ hθ2 ha (by omega)
  have hdom7 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed (b + 1) a g z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 7 g z θ := by
    intro z θ _ hθ hθ2
    rcases Nat.eq_zero_or_pos a with ha | ha
    · rw [ha, Work.Spaces.mixed_zero_right]
      exact Work.FTS.TransportS.T2Sup.canonW_mul_z_le_of_le 7 (hqη ha) hθ hθ2 (by omega)
    · exact Work.FTS.TransportS.T2Sup.canonW_mul_mixed_le_of_le 7 hqγ hθ hθ2 ha (by omega)
  -- the integrand, as a function on the product
  let F : ℝ × ℝ → ℝ := fun p => Work.FTS.TransportS.SlotT2.canonW q p.1 p.2 * h p.1 p.2
      * Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2 * Work.Spaces.mixed b a g p.1 p.2
  let Q : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)
  show |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, F (z, θ)|
      ≤ 2 * M * Work.Spaces.HkSq α 6 g
  have hcontF : ContinuousOn F Q := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.TransportS.SlotT2.canonW q p.1 p.2) Q :=
      Work.FTS.TransportS.SlotT2.continuousOn_canonW q
    have h2 : ContinuousOn (fun p : ℝ × ℝ => h p.1 p.2) Q := hsh.continuousOn
    have h3 : ContinuousOn
        (fun p : ℝ × ℝ => Work.Spaces.Dz (Work.Spaces.mixed b a g) p.1 p.2) Q :=
      (hsg.mixed (b + 1) a).continuousOn
    have h4 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed b a g p.1 p.2) Q :=
      (hsg.mixed b a).continuousOn
    exact (((h1.mul h2).mul h3).mul h4).congr (fun p _ => rfl)
  have haesmF : MeasureTheory.AEStronglyMeasurable F
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd F hcontF
  have haesmFabs : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => |F p|)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    haesmF.norm.congr (Filter.Eventually.of_forall fun p => Real.norm_eq_abs (F p))
  have hcontFabs : ContinuousOn (fun p : ℝ × ℝ => |F p|) Q :=
    continuous_abs.comp_continuousOn hcontF
  -- the pointwise bound on the integrand
  have hFpt : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |F (z, θ)| ≤ (M / 2) * (Work.Spaces.HkIntegrand α 6 g z θ
        + Work.Spaces.HkIntegrand α 7 g z θ) := by
    intro z θ hz hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hρ : 0 ≤ Work.FTS.TransportS.SlotT2.canonW q z θ :=
      Work.FTS.TransportS.SlotT2.canonW_nonneg hθI
    rcases eq_or_lt_of_le hz with hz0 | hz0
    · subst hz0
      have hzero : F ((0 : ℝ), θ) = 0 := by
        show Work.FTS.TransportS.SlotT2.canonW q (0 : ℝ) θ * h (0 : ℝ) θ
          * Work.Spaces.Dz (Work.Spaces.mixed b a g) (0 : ℝ) θ
          * Work.Spaces.mixed b a g (0 : ℝ) θ = 0
        rw [Work.FTS.TransportS.SlotT2.canonW_zero_z]
        ring
      rw [hzero, abs_zero]
      exact mul_nonneg (div_nonneg hMnn (by norm_num))
        (add_nonneg (Work.Spaces.HkIntegrand_nonneg α 6 g 0 θ)
          (Work.Spaces.HkIntegrand_nonneg α 7 g 0 θ))
    · have h6 := hdom6 z θ hz0 hθ.1 hθ.2
      have h7 := hdom7 z θ hz0 hθ.1 hθ.2
      have hsplit : F (z, θ) = h z θ * (Work.FTS.TransportS.SlotT2.canonW q z θ
          * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ) := by
        show Work.FTS.TransportS.SlotT2.canonW q z θ * h z θ
            * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ
          = h z θ * (Work.FTS.TransportS.SlotT2.canonW q z θ
            * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ * Work.Spaces.mixed b a g z θ)
        ring
      rw [hsplit]
      have hstep := abs_mul_canonW_mul_le (q := q) (M := M)
        (X := Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ)
        (Y := Work.Spaces.mixed b a g z θ) (hh := h z θ) hρ hMnn (hb z θ hz0 hθ.1 hθ.2)
      refine hstep.trans ?_
      have hdz : Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ
          = Work.Spaces.mixed (b + 1) a g z θ := rfl
      rw [hdz]
      refine mul_le_mul_of_nonneg_left ?_ (by linarith : (0 : ℝ) ≤ M / 2)
      linarith [h6, h7]
  -- the slice integrability of `|F|` for a.e. radius
  have hnz : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), (0 : ℝ) < z := by
    rw [Work.FTS.TransportS.T3BadAux.restrict_Iz_eq_Ioi]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioi
  have hsliceabs : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => |F (z, θ)|)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [hnz] with z hz
    have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
    refine MeasureTheory.Integrable.mono'
      (((hm6.1 z hzI).add (hm7.1 z hzI)).const_mul (M / 2))
      (Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => |F p|) hcontFabs hz) ?_
    refine (Work.FTS.TransportS.ae_mem_Ioo_Iθ).mono (fun θ hθ => ?_)
    rw [Real.norm_eq_abs, abs_abs]
    exact hFpt z θ hzI hθ
  -- the radial marginal
  have houtabs : MeasureTheory.Integrable
      (fun z => ∫ θ, |F (z, θ)| ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine MeasureTheory.Integrable.mono'
      (((hm6.2).add (hm7.2)).const_mul (M / 2)) ?_ ?_
    · exact MeasureTheory.AEStronglyMeasurable.integral_prod_right' haesmFabs
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      have hzI : z ∈ Work.Spaces.Iz := hz
      have hmaj : MeasureTheory.Integrable
          (fun θ => (M / 2) * (Work.Spaces.HkIntegrand α 6 g z θ
            + Work.Spaces.HkIntegrand α 7 g z θ))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        ((hm6.1 z hzI).add (hm7.1 z hzI)).const_mul (M / 2)
      have h1 : (∫ θ, |F (z, θ)| ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          ≤ ∫ θ, (M / 2) * (Work.Spaces.HkIntegrand α 6 g z θ
              + Work.Spaces.HkIntegrand α 7 g z θ)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun θ => abs_nonneg _) hmaj
          ((Work.FTS.TransportS.ae_mem_Ioo_Iθ).mono fun θ hθ => hFpt z θ hzI hθ)
      have h2 : (∫ θ, (M / 2) * (Work.Spaces.HkIntegrand α 6 g z θ
              + Work.Spaces.HkIntegrand α 7 g z θ)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          = (M / 2) * ((∫ θ, Work.Spaces.HkIntegrand α 6 g z θ
                ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
              + ∫ θ, Work.Spaces.HkIntegrand α 7 g z θ
                ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
        rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_add (hm6.1 z hzI) (hm7.1 z hzI)]
      calc ‖∫ θ, |F (z, θ)| ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)‖
          = ∫ θ, |F (z, θ)| ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
            rw [Real.norm_eq_abs,
              abs_of_nonneg (MeasureTheory.integral_nonneg fun θ => abs_nonneg _)]
        _ ≤ ∫ θ, (M / 2) * (Work.Spaces.HkIntegrand α 6 g z θ
              + Work.Spaces.HkIntegrand α 7 g z θ)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) := h1
        _ = (M / 2) * ((∫ θ, Work.Spaces.HkIntegrand α 6 g z θ
                ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
              + ∫ θ, Work.Spaces.HkIntegrand α 7 g z θ
                ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) := h2
  have hFabsint : MeasureTheory.Integrable (fun p : ℝ × ℝ => |F p|)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (Work.Spaces.integrable_prod_of_iterated
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (G := fun z θ => |F (z, θ)|) (fun z θ => abs_nonneg _) haesmFabs hsliceabs houtabs).1
  have hFint : MeasureTheory.Integrable F
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    MeasureTheory.Integrable.mono' hFabsint haesmF
      (Filter.Eventually.of_forall fun p => le_of_eq (Real.norm_eq_abs (F p)))
  -- the a.e. radial slice bound
  have hE := slotEnergy6 α q g a b hq0 hqγ hqη hab hsg hm6
  have hmono : (fun θ => |∫ z, F (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)|)
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => 2 * M * (∫ z, Work.FTS.TransportS.SlotT2.canonW q z θ
        * (Work.Spaces.mixed b a g z θ) ^ 2
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))) := by
    filter_upwards [hslice6, hslice7, htrace, Work.FTS.TransportS.ae_mem_Ioo_Iθ]
      with θ hI6 hI7 htr hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hsin : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hsnn : 0 ≤ (Real.sin (2 * θ)) ^ (-q) := Real.rpow_nonneg hsin.le _
    have hI6' : MeasureTheory.IntegrableOn
        (fun z => Work.Spaces.HkIntegrand α 6 g z θ) (Set.Ioi 0) :=
      (Work.FTS.TransportS.T3BadAux.integrableOn_Ioi_iff_Iz).mpr hI6
    have hI7' : MeasureTheory.IntegrableOn
        (fun z => Work.Spaces.HkIntegrand α 7 g z θ) (Set.Ioi 0) :=
      (Work.FTS.TransportS.T3BadAux.integrableOn_Ioi_iff_Iz).mpr hI7
    -- the two weighted slot slices
    have hYten : MeasureTheory.IntegrableOn (fun z => Work.FTS.TransportS.SlotT2.canonW q z θ
        * (Work.Spaces.mixed b a g z θ) ^ 2) (Set.Ioi 0) := by
      refine MeasureTheory.Integrable.mono' hI6' ?_ ?_
      · exact ((continuousOn_canonW_z q θ).mul
          (((hsg.mixed b a).curry_z hθ).continuousOn.pow 2)).aestronglyMeasurable measurableSet_Ioi
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
        rw [Real.norm_of_nonneg
          (mul_nonneg (Work.FTS.TransportS.SlotT2.canonW_nonneg hθI) (sq_nonneg _))]
        exact hdom6 z θ hz hθ.1 hθ.2
    have hDten : MeasureTheory.IntegrableOn (fun z => Work.FTS.TransportS.SlotT2.canonW q z θ
        * (Work.Spaces.mixed (b + 1) a g z θ) ^ 2) (Set.Ioi 0) := by
      refine MeasureTheory.Integrable.mono' hI7' ?_ ?_
      · exact ((continuousOn_canonW_z q θ).mul
          (((hsg.mixed (b + 1) a).curry_z hθ).continuousOn.pow 2)).aestronglyMeasurable
          measurableSet_Ioi
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
        rw [Real.norm_of_nonneg
          (mul_nonneg (Work.FTS.TransportS.SlotT2.canonW_nonneg hθI) (sq_nonneg _))]
        exact hdom7 z θ hz hθ.1 hθ.2
    -- the integrand of the radial integration by parts
    have hFsliceTen : MeasureTheory.IntegrableOn
        (fun z => Work.FTS.TransportS.SlotT2.canonW q z θ * h z θ
          * (z * deriv (fun z' => Work.Spaces.mixed b a g z' θ) z)
          * Work.Spaces.mixed b a g z θ) (Set.Ioi 0) := by
      refine MeasureTheory.Integrable.mono' ((hDten.add hYten).const_mul (M / 2)) ?_ ?_
      · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
        have h1 := continuousOn_canonW_z q θ
        have h2 : ContinuousOn (fun z : ℝ => h z θ) (Set.Ioi 0) := (hsh.curry_z hθ).continuousOn
        have h3 : ContinuousOn (fun z : ℝ => Work.Spaces.pz (Work.Spaces.mixed b a g) z θ)
            (Set.Ioi 0) := ((hsg.mixed b a).pz.curry_z hθ).continuousOn
        have h4 : ContinuousOn (fun z : ℝ => Work.Spaces.mixed b a g z θ) (Set.Ioi 0) :=
          (hsg.mixed b a).curry_z hθ |>.continuousOn
        exact (((h1.mul h2).mul (continuous_id.continuousOn.mul h3)).mul h4).congr
          (fun z _ => rfl)
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
        rw [Real.norm_eq_abs]
        have hρ : 0 ≤ Work.FTS.TransportS.SlotT2.canonW q z θ :=
          Work.FTS.TransportS.SlotT2.canonW_nonneg hθI
        rw [show Work.FTS.TransportS.SlotT2.canonW q z θ * h z θ
              * (z * deriv (fun z' => Work.Spaces.mixed b a g z' θ) z)
              * Work.Spaces.mixed b a g z θ
            = h z θ * (Work.FTS.TransportS.SlotT2.canonW q z θ
              * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ
              * Work.Spaces.mixed b a g z θ) from by
            simp only [Work.Spaces.Dz, Work.Spaces.pz]; ring]
        exact abs_mul_canonW_mul_le (q := q) (M := M)
          (X := Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ)
          (Y := Work.Spaces.mixed b a g z θ) (hh := h z θ) hρ hMnn (hb z θ hz hθ.1 hθ.2)
    -- the two boundary limits
    have hkey : ∀ z : ℝ, 0 < z →
        (z * Work.FTS.TransportS.SlotT2.canonW q z θ * h z θ
            * (Work.Spaces.mixed b a g z θ) ^ 2)
          = ((Real.sin (2 * θ)) ^ (-q) * h z θ)
            * (z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2) := by
      intro z _
      rw [Work.FTS.TransportS.SlotT2.canonW]
      ring
    have hlim0 : Filter.Tendsto
        (fun z => z * Work.FTS.TransportS.SlotT2.canonW q z θ * h z θ
          * (Work.Spaces.mixed b a g z θ) ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have hcore : Filter.Tendsto
          (fun z : ℝ => z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := htr.1
      have hbound : ∀ᶠ z in (nhdsWithin (0 : ℝ) (Set.Ioi 0)),
          ‖z * Work.FTS.TransportS.SlotT2.canonW q z θ * h z θ
            * (Work.Spaces.mixed b a g z θ) ^ 2‖
          ≤ ((Real.sin (2 * θ)) ^ (-q) * M)
            * |z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2| := by
        filter_upwards [self_mem_nhdsWithin] with z hz
        rw [Real.norm_eq_abs, hkey z hz, abs_mul]
        refine mul_le_mul ?_ le_rfl (abs_nonneg _) (mul_nonneg hsnn hMnn)
        rw [abs_mul, abs_of_nonneg hsnn]
        exact mul_le_mul_of_nonneg_left (hb z θ hz hθ.1 hθ.2) hsnn
      have htend : Filter.Tendsto
          (fun z : ℝ => ((Real.sin (2 * θ)) ^ (-q) * M)
            * |z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2|)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
        have h2 : Filter.Tendsto
            (fun z : ℝ => |z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2|)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
          simpa only [Real.norm_eq_abs] using tendsto_zero_iff_norm_tendsto_zero.mp hcore
        simpa using h2.const_mul ((Real.sin (2 * θ)) ^ (-q) * M)
      exact squeeze_zero_norm' hbound htend
    have hlimT : Filter.Tendsto
        (fun z => z * Work.FTS.TransportS.SlotT2.canonW q z θ * h z θ
          * (Work.Spaces.mixed b a g z θ) ^ 2)
        Filter.atTop (nhds 0) := by
      have hcore : Filter.Tendsto
          (fun z : ℝ => z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2)
          Filter.atTop (nhds 0) := htr.2
      have hbound : ∀ᶠ z in Filter.atTop,
          ‖z * Work.FTS.TransportS.SlotT2.canonW q z θ * h z θ
            * (Work.Spaces.mixed b a g z θ) ^ 2‖
          ≤ ((Real.sin (2 * θ)) ^ (-q) * M)
            * |z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2| := by
        filter_upwards [Filter.Ioi_mem_atTop (0 : ℝ)] with z hz
        rw [Real.norm_eq_abs, hkey z hz, abs_mul]
        refine mul_le_mul ?_ le_rfl (abs_nonneg _) (mul_nonneg hsnn hMnn)
        rw [abs_mul, abs_of_nonneg hsnn]
        exact mul_le_mul_of_nonneg_left (hb z θ hz hθ.1 hθ.2) hsnn
      have htend : Filter.Tendsto
          (fun z : ℝ => ((Real.sin (2 * θ)) ^ (-q) * M)
            * |z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2|)
          Filter.atTop (nhds 0) := by
        have h2 : Filter.Tendsto
            (fun z : ℝ => |z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2|)
            Filter.atTop (nhds 0) := by
          simpa only [Real.norm_eq_abs] using tendsto_zero_iff_norm_tendsto_zero.mp hcore
        simpa using h2.const_mul ((Real.sin (2 * θ)) ^ (-q) * M)
      exact squeeze_zero_norm' hbound htend
    rw [Work.FTS.TransportS.T3BadAux.restrict_Iz_eq_Ioi]
    exact sliceIbpCanonW (q := q) (M := M) (h := fun z => h z θ)
      (Y := fun z => Work.Spaces.mixed b a g z θ) (θ := θ) hMnn hθ
      (fun z hz => hsh.hasDerivAt_slice hθ hz)
      (fun z hz => (hsg.mixed b a).hasDerivAt_slice hθ hz)
      (fun z hz => hb z θ hz hθ.1 hθ.2)
      (fun z hz => hDb z θ hz hθ.1 hθ.2)
      hYten hFsliceTen hlim0 hlimT
  -- the assembly
  have hFmargint : MeasureTheory.Integrable
      (fun θ => |∫ z, F (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)|)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hFint.integral_prod_right.abs
  have hGmargint : MeasureTheory.Integrable
      (fun θ => 2 * M * (∫ z, Work.FTS.TransportS.SlotT2.canonW q z θ
        * (Work.Spaces.mixed b a g z θ) ^ 2
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hE.2.1.const_mul (2 * M)
  have hFubini : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, F (z, θ))
      = ∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz, F (z, θ) := by
    have h1 := MeasureTheory.integral_integral
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun z θ => F (z, θ)) hFint
    have h2 := MeasureTheory.integral_integral_swap
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun z θ => F (z, θ)) hFint
    exact h2
  calc |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, F (z, θ)|
      = |∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz, F (z, θ)| := by rw [hFubini]
    _ ≤ ∫ θ in Work.Spaces.Iθ, |∫ z in Work.Spaces.Iz, F (z, θ)| :=
        MeasureTheory.abs_integral_le_integral_abs
          (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
          (f := fun θ => ∫ z in Work.Spaces.Iz, F (z, θ))
    _ ≤ ∫ θ in Work.Spaces.Iθ, 2 * M * (∫ z in Work.Spaces.Iz,
          Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2) :=
        MeasureTheory.integral_mono_ae hFmargint hGmargint hmono
    _ = 2 * M * (∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz,
          Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2) :=
        MeasureTheory.integral_const_mul _ _
    _ ≤ 2 * M * Work.Spaces.HkSq α 6 g :=
        mul_le_mul_of_nonneg_left hE.2.2 (by linarith)

end

end Work.FTS.StrongPersist.H6Pair6Aux.T6Gen
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.fluxFamSix =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.SixRoute

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open Work.Spaces

/-! ## Two elementary `|·|`-manipulations

These are the bookkeeping steps of the pointwise Cauchy–Schwarz (AM–GM) bound
`|ρ f X Y| ≤ |f| · (canonW q |X| |Y|) ≤ (M/2)(canonW q X² + canonW q Y²)`, where `ρ ≤ canonW q`
is the leaf weight domination and `|f| ≤ M`.  They are stated separately so that the
reassociation of the products never has to be guessed by `ring`. -/




end

end Work.FTS.StrongPersist.N6Trans.SixRoute
end
