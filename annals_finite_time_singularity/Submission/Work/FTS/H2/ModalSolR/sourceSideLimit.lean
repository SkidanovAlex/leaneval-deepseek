/-
# `ModalSolR/sourceSideLimit` — the source-side limit of the modal expansion

Target: `Work.FTS.H2.ModalSolR.sourceSideLimit`.

For a source `F` which is `C^∞` on the open quadrant `Q0 = (0,∞) × (0,π/2)` with `F ^ 2`
integrable there, and a test function `φ` of class `C^∞` compactly supported in `Q0`, the
partial sums of the angular modal expansion of `F` converge against `φ` with the self-adjoint
weight `z ^ ((5-α)/α) cos θ`:

`∫_{Q0} (Σ_{m ≤ N} cmode m F z · eFam m θ) φ z θ (z ^ ((5-α)/α) cos θ)
   → ∫_{Q0} F z θ φ z θ (z ^ ((5-α)/α) cos θ)`.

Route (all ingredients are `sorry`-free):

* `φ` is supported in a compact box `K = [a,b] × [c,d] ⊂ Q0`, so both integrals may be
  restricted to `K` (`setIntegral_eq_of_subset_of_forall_sdiff_eq_zero`);
* writing `R_N = Σ_{m ≤ N} cmode m F · eFam m − F` for the residual of the truncation, the
  difference of the two integrals is `∫_K R_N Φ` with `Φ = φ · (z^((5-α)/α) cos θ)`;
* Cauchy–Schwarz on `K` bounds it by
  `sqrt(∫_K R_N² cos θ) · sqrt(∫_K Φ² / cos θ)`, and the second factor is a constant;
* `∫_K R_N² cos θ ≤ ∫_{z>0} rN N z` where `rN N z = ∫_θ F z θ² cos θ − Σ_{m≤N} cmode m F z² D_m`
  is the (algebraic) residual energy: the `z`-Fubini identity on the box, the truncated
  Pythagoras identity `eFam_pythagoras_alt` for a.e. `z` and the monotonicity of the integral
  against a subset;
* `∫_{z>0} rN N z → 0` by dominated convergence, the domination being
  `rN N z ≤ ∫_θ F z θ² cos θ` (Bessel's inequality, `cmode_bessel`) whose integral is finite by
  the `L²` hypothesis (`Fubini`).

The auxiliary lemmas proved in this file (`sigma_integrable`, `ae_slice_facts`) are the
measurability/integrability facts about the angular slice energy; the four lemmas used from
`SourceSide/` provide the box integrability, the Cauchy–Schwarz inequality on a set of `ℝ × ℝ`,
the joint a.e. strong measurability of the residual and the dominated-convergence limit.
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.EllipticEst.ModalSolution.eFam_expansion_L2
import Submission.Work.EllipticEst.ModalSolution.cmode_bessel
import Submission.Work.EllipticEst.ModalSolution.box_of_compactSupport
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.EllipticEst.ModalSolution.cmode_memLp
import Submission.Work.EllipticEst.ModalSolution.eFam_parseval
import Submission.Work.EllipticEst.ModalSolution.eFam_pythagoras_alt
import Submission.Work.FTS.EllipticEst.LevelOneAsm.ParsevalZIntAux
import Submission.Work.FTS.H2.ModalSol.Auxiliary.integrableOn_mul_of_sq_integrable
import Submission.Work.FTS.H2.ModalSolR.SourcePrep
import Submission.Work.FTS.H2.ModalSolR.SourceSide.integrableOn_sq_mul_continuousOn
import Submission.Work.FTS.H2.ModalSolR.SourceSide.sq_integral_mul_le_of_integrable_sq
import Submission.Work.FTS.H2.ModalSolR.SourceSide.joint_aesm_partialSum_residual
import Submission.Work.FTS.H2.ModalSolR.SourceSide.residualEnergyTendstoZero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.H2.ModalSolR

/-! ## The source-side limit -/

theorem sourceSideLimit {α : ℝ} {F φ : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hφ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ))
    (hφc : HasCompactSupport (Function.uncurry φ))
    (hφs : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    Filter.Tendsto (fun N : ℕ => ∫ p in Work.FTS.EllipticEst.Q0,
        (∑ m ∈ Finset.range (N + 1), Work.FTS.PhiStar.Series.cmode m F p.1
          * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) * φ p.1 p.2
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      Filter.atTop
      (nhds (∫ p in Work.FTS.EllipticEst.Q0,
        F p.1 p.2 * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2))) := by
  classical
  obtain ⟨a, b, c, d, ha, hab, hc, hcd, hd, hbox⟩ :=
    Work.EllipticEst.ModalSolution.box_of_compactSupport hφc hφs
  let K : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc c d
  have hab' : a ≤ b := le_of_lt hab
  have hcd' : c ≤ d := le_of_lt hcd
  have hKcomp : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKmeas : MeasurableSet K := hKcomp.isClosed.measurableSet
  have haK : K ⊆ Work.FTS.EllipticEst.Q0 := fun p hp =>
    Work.FTS.EllipticEst.mem_Q0.mpr
      ⟨lt_of_lt_of_le ha hp.1.1, lt_of_lt_of_le hc hp.2.1, lt_of_le_of_lt hp.2.2 hd⟩
  have hphi0 : ∀ p : ℝ × ℝ, p ∉ K → φ p.1 p.2 = 0 := fun p hp =>
    hbox p (fun hmem => hp ⟨⟨hmem.1.1.le, hmem.1.2.le⟩, ⟨hmem.2.1.le, hmem.2.2.le⟩⟩)
  have hvan : ∀ (h : ℝ × ℝ → ℝ), (∀ p ∈ Work.FTS.EllipticEst.Q0 \ K, h p = 0) →
      (∫ p in Work.FTS.EllipticEst.Q0, h p) = ∫ p in K, h p := fun h hh =>
    MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      Work.FTS.EllipticEst.isOpen_Q0.measurableSet haK hh
  let Φ : ℝ × ℝ → ℝ := fun p => φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2)
  let SN : ℕ → ℝ × ℝ → ℝ := fun N p => ∑ m ∈ Finset.range (N + 1),
      Work.FTS.PhiStar.Series.cmode m F p.1 * Work.FTS.PhiStar.Gegenbauer.eFam m p.2
  let RZ : ℕ → ℝ × ℝ → ℝ := fun N p => SN N p - F p.1 p.2
  let rN : ℕ → ℝ → ℝ := fun N z => (∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ)
      - ∑ m ∈ Finset.range (N + 1), (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
  have hΦcont : ContinuousOn Φ K := by
    dsimp only [Φ]
    refine ContinuousOn.mul ?_ (ContinuousOn.mul ?_ ?_)
    · exact (hφ 0).continuous.continuousOn
    · exact continuousOn_fst.rpow_const (fun p hp => Or.inl (ne_of_gt (lt_of_lt_of_le ha hp.1.1)))
    · exact (Real.continuous_cos.comp continuous_snd).continuousOn
  have hFcontK : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2 * Real.cos p.2) K :=
    ((hsm.continuousOn.mono haK).pow 2).mul
      (Real.continuous_cos.comp continuous_snd).continuousOn
  have hF2K : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2 * Real.cos p.2) K :=
    hFcontK.integrableOn_compact hKcomp
  have hΦ2K : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => Φ p ^ 2) K :=
    (hΦcont.pow 2).integrableOn_compact hKcomp
  have hRZaesm : ∀ N : ℕ, MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => RZ N p)
      ((MeasureTheory.volume : Measure (ℝ × ℝ)).restrict K) := fun N =>
    (SourceSide.joint_aesm_partialSum_residual hsm N).mono_set
      (show K ⊆ Set.Ioi 0 ×ˢ Set.Icc 0 (π / 2) from
        fun p hp => ⟨lt_of_lt_of_le ha hp.1.1, ⟨le_trans hc.le hp.2.1, le_trans hp.2.2 hd.le⟩⟩)
  have hFaesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => F p.1 p.2)
      ((MeasureTheory.volume : Measure (ℝ × ℝ)).restrict K) :=
    (hsm.continuousOn.mono haK).aestronglyMeasurable hKmeas
  have hSNaesm : ∀ N : ℕ, MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => SN N p)
      ((MeasureTheory.volume : Measure (ℝ × ℝ)).restrict K) := fun N =>
    ((hRZaesm N).add hFaesm).congr
      (Eventually.of_forall (fun p => by
        simp only [Pi.add_apply]
        dsimp only [RZ, SN]
        ring))
  have hSN2K : ∀ N : ℕ, MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => SN N p ^ 2 * Real.cos p.2) K := by
    intro N
    have hterm_int : ∀ m ∈ Finset.range (N + 1),
        MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.FTS.PhiStar.Series.cmode m F p.1) ^ 2
          * (Work.FTS.PhiStar.Gegenbauer.eFam m p.2 ^ 2 * Real.cos p.2)) K := fun m _ =>
      SourceSide.integrableOn_sq_mul_continuousOn
        (Work.EllipticEst.ModalSolution.cmode_memLp hsm hL2 m) ha hab' hc hcd'
        (((Work.EllipticEst.ModalSolution.continuous_eFam m).comp_continuousOn
            continuous_snd.continuousOn).pow 2 |>.mul
          (Real.continuous_cos.comp continuous_snd).continuousOn)
    have hdom : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => ((Finset.range (N + 1)).card : ℝ) *
        ∑ m ∈ Finset.range (N + 1), (Work.FTS.PhiStar.Series.cmode m F p.1) ^ 2
          * (Work.FTS.PhiStar.Gegenbauer.eFam m p.2 ^ 2 * Real.cos p.2)) K :=
      (integrable_finsetSum (Finset.range (N + 1)) (fun m hm => hterm_int m hm)).const_mul _
    refine MeasureTheory.Integrable.mono' hdom (((hSNaesm N).pow 2).mul
      (Real.continuous_cos.comp continuous_snd).aestronglyMeasurable) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (s := K) hKmeas] with p hp
    have hcos : 0 ≤ Real.cos p.2 := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hp.2.1, hc, Real.pi_pos], by linarith [hp.2.2, hd, Real.pi_pos]⟩
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hcos)]
    calc SN N p ^ 2 * Real.cos p.2
        = (∑ m ∈ Finset.range (N + 1), Work.FTS.PhiStar.Series.cmode m F p.1
            * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) ^ 2 * Real.cos p.2 := rfl
      _ ≤ ((Finset.range (N + 1)).card : ℝ) * (∑ m ∈ Finset.range (N + 1),
            (Work.FTS.PhiStar.Series.cmode m F p.1
              * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) ^ 2) * Real.cos p.2 :=
          mul_le_mul_of_nonneg_right sq_sum_le_card_mul_sum_sq hcos
      _ = ((Finset.range (N + 1)).card : ℝ) * ∑ m ∈ Finset.range (N + 1),
            (Work.FTS.PhiStar.Series.cmode m F p.1) ^ 2
              * (Work.FTS.PhiStar.Gegenbauer.eFam m p.2 ^ 2 * Real.cos p.2) := by
          rw [mul_assoc, Finset.sum_mul]
          congr 1
          exact Finset.sum_congr rfl (fun m _ => by ring)
  have hRQK : ∀ N : ℕ, MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => RZ N p ^ 2 * Real.cos p.2) K := by
    intro N
    refine MeasureTheory.Integrable.mono' (((hSN2K N).const_mul 2).add (hF2K.const_mul 2)) ?_ ?_
    · exact ((hRZaesm N).pow 2).mul (Real.continuous_cos.comp continuous_snd).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem (s := K) hKmeas] with p hp
      have hcos : 0 ≤ Real.cos p.2 := Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [hp.2.1, hc, Real.pi_pos], by linarith [hp.2.2, hd, Real.pi_pos]⟩
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hcos)]
      simp only [Pi.add_apply]
      dsimp only [RZ]
      nlinarith [mul_nonneg (sq_nonneg (SN N p + F p.1 p.2)) hcos]
  have hRZ2sq : ∀ N : ℕ, MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => RZ N p ^ 2) K := by
    intro N
    have hcdpos : 0 < Real.cos d := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hc, Real.pi_pos], by linarith [hd, Real.pi_pos]⟩
    refine MeasureTheory.Integrable.mono' ((hRQK N).const_mul (1 / Real.cos d)) ?_ ?_
    · exact (hRZaesm N).pow 2
    · filter_upwards [MeasureTheory.ae_restrict_mem (s := K) hKmeas] with p hp
      have hcosle : Real.cos d ≤ Real.cos p.2 := Real.cos_le_cos_of_nonneg_of_le_pi
        (by linarith [hp.2.1, hc, Real.pi_pos]) (by linarith [hd, Real.pi_pos]) hp.2.2
      rw [Real.norm_of_nonneg (sq_nonneg _), one_div, inv_mul_eq_div, le_div_iff₀ hcdpos]
      exact mul_le_mul_of_nonneg_left hcosle (sq_nonneg _)
  have hRZ2_le : ∀ N : ℕ, (∫ p in K, RZ N p ^ 2) ≤
      (1 / Real.cos d) * (∫ p in K, RZ N p ^ 2 * Real.cos p.2) := by
    intro N
    have hcdpos : 0 < Real.cos d := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hc, Real.pi_pos], by linarith [hd, Real.pi_pos]⟩
    have hptw : ∀ p ∈ K, RZ N p ^ 2 ≤ (1 / Real.cos d) * (RZ N p ^ 2 * Real.cos p.2) := by
      intro p hp
      have hcosle : Real.cos d ≤ Real.cos p.2 := Real.cos_le_cos_of_nonneg_of_le_pi
        (by linarith [hp.2.1, hc, Real.pi_pos]) (by linarith [hd, Real.pi_pos]) hp.2.2
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hcdpos]
      exact mul_le_mul_of_nonneg_left hcosle (sq_nonneg _)
    have h1 := MeasureTheory.setIntegral_mono_on (hRZ2sq N) ((hRQK N).const_mul (1 / Real.cos d))
      hKmeas hptw
    rwa [MeasureTheory.integral_const_mul] at h1
  -- the a.e. bound on the algebraic residual energy
  have hrN_bnd : ∀ N : ℕ, ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      0 ≤ rN N z ∧ rN N z ≤ ∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ := by
    intro N
    filter_upwards [ae_slice_facts hsm hL2] with z hz
    obtain ⟨hzm, hzi⟩ := hz
    have hcosnn : 0 ≤ᵐ[(MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iθ]
        (fun θ => F z θ ^ 2 * Real.cos θ) := by
      filter_upwards [MeasureTheory.ae_restrict_mem (s := Work.Spaces.Iθ) measurableSet_Icc]
        with θ hθ
      exact mul_nonneg (sq_nonneg _)
        (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩)
    have hof := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hzi hcosnn
    have hb := Work.EllipticEst.ModalSolution.cmode_bessel F z N
    have hb' : ENNReal.ofReal (∑ m ∈ Finset.range (N + 1),
        (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ))
        ≤ ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ) := by
      rw [hof]
      refine le_of_eq_of_le ?_ hb
      congr 1
      refine Finset.sum_congr rfl (fun m _ => ?_)
      ring
    have hle : (∑ m ∈ Finset.range (N + 1), (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ))
        ≤ ∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ :=
      (ENNReal.ofReal_le_ofReal_iff (MeasureTheory.integral_nonneg_of_ae hcosnn)).mp hb'
    have hsumnn : 0 ≤ ∑ m ∈ Finset.range (N + 1), (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ) :=
      Finset.sum_nonneg (fun m _ => mul_nonneg (sq_nonneg _)
        (le_of_lt (Work.EllipticEst.ModalSolution.eNorm_pos m)))
    dsimp only [rN]
    exact ⟨sub_nonneg.mpr hle, by linarith⟩
  have hrN_aesm : ∀ N : ℕ, MeasureTheory.AEStronglyMeasurable (fun z => rN N z)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    intro N
    have hsum : MeasureTheory.AEStronglyMeasurable (fun z => ∑ m ∈ Finset.range (N + 1),
        (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ))
        (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
      (integrable_finsetSum (Finset.range (N + 1)) (fun m _ =>
        (Work.EllipticEst.ModalSolution.cmode_memLp hsm hL2 m).const_mul
          (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
        |>.congr (Eventually.of_forall (fun z => by ring)))).aestronglyMeasurable
    exact ((sigma_integrable hsm hL2).aestronglyMeasurable.sub hsum).congr
      (Eventually.of_forall (fun z => rfl))
  have hrN_int : ∀ N : ℕ, MeasureTheory.IntegrableOn (fun z => rN N z) (Set.Ioi 0) := by
    intro N
    refine MeasureTheory.Integrable.mono' (sigma_integrable hsm hL2) (hrN_aesm N) ?_
    filter_upwards [hrN_bnd N] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg hz.1]
    exact hz.2
  -- the box integral as an iterated integral
  have hFub : ∀ N : ℕ, (∫ p in K, RZ N p ^ 2 * Real.cos p.2)
      = ∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, RZ N (z, θ) ^ 2 * Real.cos θ := by
    intro N
    rw [MeasureTheory.Measure.volume_eq_prod]
    exact MeasureTheory.setIntegral_prod (fun p : ℝ × ℝ => RZ N p ^ 2 * Real.cos p.2) (hRQK N)
  -- the residual energy on the box is dominated by the integrated residual energy
  have hstep : ∀ N : ℕ,
      (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, RZ N (z, θ) ^ 2 * Real.cos θ)
        ≤ ∫ z in Set.Ioi 0, rN N z := by
    intro N
    have hinner : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Icc a b)),
        (∫ θ in Set.Icc c d, RZ N (z, θ) ^ 2 * Real.cos θ) ≤ rN N z := by
      have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun x hx => lt_of_lt_of_le ha hx.1
      have h1 : ∀ᵐ z ∂((MeasureTheory.volume.restrict (Set.Ioi 0)).restrict (Set.Icc a b)),
          (∫ θ in Set.Icc c d, RZ N (z, θ) ^ 2 * Real.cos θ) ≤ rN N z := by
        filter_upwards [MeasureTheory.ae_restrict_of_ae (ae_slice_facts hsm hL2)] with z hz
        obtain ⟨hzm, hzi⟩ := hz
        have hcontS : Continuous (fun θ : ℝ => SN N (z, θ)) := by
          dsimp only [SN]
          exact continuous_finsetSum _ (fun m _ => continuous_const.mul
            (Work.EllipticEst.ModalSolution.continuous_eFam m))
        have hS2int : MeasureTheory.IntegrableOn
            (fun θ : ℝ => SN N (z, θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ :=
          ((hcontS.pow 2).mul Real.continuous_cos).continuousOn.integrableOn_compact
            (by simpa only [Work.Spaces.Iθ] using isCompact_Icc)
        have hRZint : MeasureTheory.IntegrableOn
            (fun θ : ℝ => RZ N (z, θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ := by
          refine MeasureTheory.Integrable.mono' ((hS2int.const_mul 2).add (hzi.const_mul 2)) ?_ ?_
          · exact (((hcontS.aestronglyMeasurable.sub hzm).pow 2).mul
              Real.continuous_cos.aestronglyMeasurable)
          · filter_upwards [MeasureTheory.ae_restrict_mem (s := Work.Spaces.Iθ) measurableSet_Icc]
              with θ hθ
            have hcosθ : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc
              ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
            rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hcosθ)]
            simp only [Pi.add_apply]
            dsimp only [RZ]
            nlinarith [mul_nonneg (sq_nonneg (SN N (z, θ) + F z θ)) hcosθ]
        have hEq : (∫ θ in Work.Spaces.Iθ, RZ N (z, θ) ^ 2 * Real.cos θ) = rN N z := by
          have hpyth := Work.EllipticEst.ModalSolution.eFam_pythagoras_alt F z N hzm hzi
          rw [show rN N z = (∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ)
              - ∑ m ∈ Finset.range (N + 1), (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
                  * (∫ θ in Work.Spaces.Iθ,
                      Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ) from rfl,
            ← hpyth]
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
          dsimp only [RZ, SN]
          ring
        refine le_trans ?_ (le_of_eq hEq)
        refine MeasureTheory.setIntegral_mono_set hRZint ?_ ?_
        · filter_upwards [MeasureTheory.ae_restrict_mem (s := Work.Spaces.Iθ) measurableSet_Icc]
            with θ hθ
          exact mul_nonneg (sq_nonneg _) (Real.cos_nonneg_of_mem_Icc
            ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩)
        · exact Eventually.of_forall (fun x hx => ⟨le_trans hc.le hx.1, le_trans hx.2 hd.le⟩)
      rwa [Measure.restrict_restrict_of_subset hsub] at h1
    have hfi : MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Set.Icc c d, RZ N (z, θ) ^ 2 * Real.cos θ) (Set.Icc a b) := by
      have h2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => RZ N p ^ 2 * Real.cos p.2)
          ((MeasureTheory.volume.restrict (Set.Icc a b)).prod
            (MeasureTheory.volume.restrict (Set.Icc c d))) := by
        rw [MeasureTheory.Measure.prod_restrict]
        exact hRQK N
      exact h2.integral_prod_left
    have hgi : MeasureTheory.IntegrableOn (fun z => rN N z) (Set.Icc a b) :=
      (hrN_int N).mono_set (fun x hx => lt_of_lt_of_le ha hx.1)
    calc (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, RZ N (z, θ) ^ 2 * Real.cos θ)
        ≤ ∫ z in Set.Icc a b, rN N z :=
          MeasureTheory.setIntegral_mono_ae_restrict hfi hgi hinner
      _ ≤ ∫ z in Set.Ioi 0, rN N z :=
          MeasureTheory.setIntegral_mono_set (hrN_int N)
            ((hrN_bnd N).mono (fun z hz => hz.1))
            (Eventually.of_forall (fun x hx => lt_of_lt_of_le ha hx.1))
  have hres_lim : Filter.Tendsto (fun N : ℕ => ∫ p in K, RZ N p ^ 2 * Real.cos p.2)
      Filter.atTop (nhds 0) := by
    have hDCT : Filter.Tendsto (fun N : ℕ => ∫ z in Set.Ioi 0, rN N z) Filter.atTop (nhds 0) :=
      SourceSide.residualEnergyTendstoZero hsm hL2
    refine squeeze_zero' (Eventually.of_forall (fun N => ?_))
      (Eventually.of_forall (fun N => ?_)) hDCT
    · rw [hFub N]
      exact MeasureTheory.integral_nonneg_of_ae (Eventually.of_forall (fun z =>
        MeasureTheory.integral_nonneg_of_ae (by
          filter_upwards [MeasureTheory.ae_restrict_mem (s := Set.Icc c d) measurableSet_Icc]
            with θ hθ
          exact mul_nonneg (sq_nonneg _) (Real.cos_nonneg_of_mem_Icc
            ⟨by linarith [hθ.1, hc, Real.pi_pos], by linarith [hθ.2, hd, Real.pi_pos]⟩))))
    · rw [hFub N]
      exact hstep N
  -- integrability of the residual against the test function
  have hRZΦK : ∀ N : ℕ, MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => RZ N p * Φ p) K := by
    intro N
    refine MeasureTheory.Integrable.mono' (((hRZ2sq N).add (hΦ2K)).div_const 2) ?_ ?_
    · exact (hRZaesm N).mul (hΦcont.aestronglyMeasurable hKmeas)
    · filter_upwards with p
      simp only [Pi.add_apply]
      rw [Real.norm_eq_abs, abs_mul]
      nlinarith [sq_nonneg (|RZ N p| - |Φ p|), sq_abs (RZ N p), sq_abs (Φ p)]
  have hFΦK : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 * Φ p) K :=
    ((hsm.continuousOn.mono haK).mul hΦcont).integrableOn_compact hKcomp
  have hSNΦK : ∀ N : ℕ, MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => SN N p * Φ p) K := by
    intro N
    refine ((hRZΦK N).add hFΦK).congr_fun ?_ hKmeas
    intro p hp
    simp only [Pi.add_apply]
    dsimp only [RZ, SN]
    ring
  -- Cauchy–Schwarz on the box
  have hcs : ∀ N : ℕ, (∫ p in K, RZ N p * Φ p) ^ 2
      ≤ (∫ p in K, RZ N p ^ 2) * (∫ p in K, Φ p ^ 2) := fun N =>
    SourceSide.sq_integral_mul_le_of_integrable_sq (s := K)
      (u := fun p => RZ N p) (v := fun p => Φ p) (hRZ2sq N) (hΦ2K)
      (hRZaesm N) (hΦcont.aestronglyMeasurable hKmeas)
  have hbound : ∀ N : ℕ, ‖∫ p in K, RZ N p * Φ p‖ ≤
      Real.sqrt ((1 / Real.cos d) * (∫ p in K, RZ N p ^ 2 * Real.cos p.2))
        * Real.sqrt (∫ p in K, Φ p ^ 2) := by
    intro N
    have hcdpos : 0 < Real.cos d := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hc, Real.pi_pos], by linarith [hd, Real.pi_pos]⟩
    have hB : 0 ≤ ∫ p in K, Φ p ^ 2 :=
      MeasureTheory.integral_nonneg_of_ae (by
        filter_upwards [MeasureTheory.ae_restrict_mem (s := K) hKmeas] with p hp
        exact sq_nonneg _)
    have hX : 0 ≤ (1 / Real.cos d) * (∫ p in K, RZ N p ^ 2 * Real.cos p.2) :=
      mul_nonneg (le_of_lt (div_pos one_pos hcdpos))
        (MeasureTheory.integral_nonneg_of_ae (by
          filter_upwards [MeasureTheory.ae_restrict_mem (s := K) hKmeas] with p hp
          exact mul_nonneg (sq_nonneg _) (Real.cos_nonneg_of_mem_Icc
            ⟨by linarith [hp.2.1, hc, Real.pi_pos], by linarith [hp.2.2, hd, Real.pi_pos]⟩)))
    have h1 : (∫ p in K, RZ N p * Φ p) ^ 2
        ≤ ((1 / Real.cos d) * (∫ p in K, RZ N p ^ 2 * Real.cos p.2)) * (∫ p in K, Φ p ^ 2) :=
      le_trans (hcs N) (mul_le_mul_of_nonneg_right (hRZ2_le N) hB)
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact le_trans (Real.sqrt_le_sqrt h1) (le_of_eq (Real.sqrt_mul hX _))
  have hlimZero : Filter.Tendsto (fun N : ℕ => ∫ p in K, RZ N p * Φ p) Filter.atTop
      (nhds 0) := by
    have hnorm : Filter.Tendsto (fun N : ℕ => ‖∫ p in K, RZ N p * Φ p‖) Filter.atTop
        (nhds 0) := by
      refine squeeze_zero' (Eventually.of_forall (fun N => norm_nonneg _))
        (Eventually.of_forall (fun N => hbound N)) ?_
      have hA0 : Filter.Tendsto
          (fun N : ℕ => (1 / Real.cos d) * (∫ p in K, RZ N p ^ 2 * Real.cos p.2))
          Filter.atTop (nhds 0) := by
        simpa only [mul_zero] using hres_lim.const_mul (1 / Real.cos d)
      have hs : Filter.Tendsto (fun N : ℕ =>
          Real.sqrt ((1 / Real.cos d) * (∫ p in K, RZ N p ^ 2 * Real.cos p.2)))
          Filter.atTop (nhds 0) := by
        have hcont := Real.continuous_sqrt.tendsto 0
        simpa only [Function.comp_def, Real.sqrt_zero] using hcont.comp hA0
      have hprod : Filter.Tendsto (fun N : ℕ =>
          Real.sqrt ((1 / Real.cos d) * (∫ p in K, RZ N p ^ 2 * Real.cos p.2))
            * Real.sqrt (∫ p in K, Φ p ^ 2)) Filter.atTop
          (nhds (0 * Real.sqrt (∫ p in K, Φ p ^ 2))) :=
        hs.mul_const (Real.sqrt (∫ p in K, Φ p ^ 2))
      rwa [zero_mul] at hprod
    exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa using hnorm)
  have hdiff : ∀ N : ℕ, (∫ p in K, SN N p * Φ p) - (∫ p in K, F p.1 p.2 * Φ p)
      = ∫ p in K, RZ N p * Φ p := by
    intro N
    rw [← MeasureTheory.integral_sub (hSNΦK N) hFΦK]
    congr 1
    funext p
    dsimp only [RZ]
    ring
  have hlimSN : Filter.Tendsto (fun N : ℕ => ∫ p in K, SN N p * Φ p) Filter.atTop
      (nhds (∫ p in K, F p.1 p.2 * Φ p)) := by
    have hkey : (fun N : ℕ => ∫ p in K, SN N p * Φ p)
        = fun N => (∫ p in K, RZ N p * Φ p) + (∫ p in K, F p.1 p.2 * Φ p) := by
      funext N
      have h := hdiff N
      linarith
    rw [hkey]
    simpa using hlimZero.add (tendsto_const_nhds (x := ∫ p in K, F p.1 p.2 * Φ p))
  -- transfer the limit back to the quadrant
  have hvanN : ∀ N : ℕ, (∫ p in Work.FTS.EllipticEst.Q0,
        (∑ m ∈ Finset.range (N + 1), Work.FTS.PhiStar.Series.cmode m F p.1
          * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) * φ p.1 p.2
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) = ∫ p in K, SN N p * Φ p := by
    intro N
    rw [hvan (fun p => (∑ m ∈ Finset.range (N + 1), Work.FTS.PhiStar.Series.cmode m F p.1
          * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) * φ p.1 p.2
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
        (fun p hp => by rw [hphi0 p hp.2]; ring)]
    refine MeasureTheory.setIntegral_congr_fun hKmeas (fun p _ => ?_)
    dsimp only [SN, Φ]
    ring
  have hvanF : (∫ p in Work.FTS.EllipticEst.Q0,
        F p.1 p.2 * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      = ∫ p in K, F p.1 p.2 * Φ p := by
    rw [hvan (fun p => F p.1 p.2 * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
        (fun p hp => by rw [hphi0 p hp.2]; ring)]
    refine MeasureTheory.setIntegral_congr_fun hKmeas (fun p _ => ?_)
    dsimp only [Φ]
    ring
  rw [funext hvanN, hvanF]
  exact hlimSN

end Work.FTS.H2.ModalSolR
