import Mathlib
import Submission.Work.NN.Core.czbL2Cut
import Submission.Work.NN.Core.czB_L2_aux
import Submission.Work.NN.Core.integral_normSq_dCoord_eq_dbarCoord
import Submission.Work.CR.Flat.Cauchy.bmPotential_iteratedFDeriv
import Submission.Work.NN.Core.energy_eq_of_approx
import Submission.Work.NN.Core.tendsto_ofReal_integral_cutRe_sq_mul
import Submission.Work.NN.Core.tendsto_integral_cutC_sq_mul

set_option maxHeartbeats 1600000

namespace Work.NN.Core

open Work.CR.Flat.Cauchy

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

/-- `‖x + y‖² = ‖x‖² + ‖y‖² + 2 Re(x · conj y)` for complex `x, y`. -/
private lemma complex_norm_add_sq (x y : ℂ) :
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 + 2 * (x * star y).re := by
  rw [Complex.sq_norm, Complex.normSq_add, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  simp only [Complex.star_def]

/-- Elementary AM-GM: `2xy ≤ εx² + y²/ε`. -/
private lemma two_mul_le_eps (x y ε : ℝ) (hε : 0 < ε) :
    2 * x * y ≤ ε * x ^ 2 + y ^ 2 / ε := by
  have h : (0 : ℝ) ≤ (ε * x - y) ^ 2 := sq_nonneg _
  have h2 : 2 * x * y * ε ≤ ε ^ 2 * x ^ 2 + y ^ 2 := by nlinarith [h]
  rw [show ε * x ^ 2 + y ^ 2 / ε = (ε ^ 2 * x ^ 2 + y ^ 2) / ε by field_simp]
  rw [le_div_iff₀ hε]
  linarith [h2]

/-- `Re(x · conj y) = Re(conj y · x)`-flavoured rearrangement for the cross term. -/
private lemma re_mul_star_comm (A B u : ℂ) :
    (B * u * star A).re = (A * star (u * B)).re := by
  simp only [Complex.star_def]
  rw [← Complex.conj_re (B * u * (starRingEnd ℂ) A)]
  congr 1
  simp only [map_mul, Complex.conj_conj]
  ring

/-- The cross term of the localised energy, with the real cut-off factored out. -/
private lemma re_cross_cut (A B u : ℂ) (cre : ℝ) :
    (B * u * star (((cre : ℝ) : ℂ) * A)).re = cre * (A * star (u * B)).re := by
  have h1 : star (((cre : ℝ) : ℂ) * A) = ((cre : ℝ) : ℂ) * star A := by
    rw [star_mul, show star ((cre : ℝ) : ℂ) = ((cre : ℝ) : ℂ) from by simp, mul_comm]
  rw [h1]
  have h2 : (B * u * (((cre : ℝ) : ℂ) * star A)).re = cre * (B * u * star A).re := by
    rw [show B * u * (((cre : ℝ) : ℂ) * star A) = ((cre : ℝ) : ℂ) * (B * u * star A) from
      by ring]
    simp [Complex.mul_re]
  rw [h2, re_mul_star_comm A B u]

/-- **The `∂`- and `∂̄`-energies of the Bochner–Martinelli potential agree.**  For data `h` of
class `C²` with compact support, `Σ_k ∫⁻ ‖∂_k (bmPotential h)‖² = Σ_k ∫⁻ ‖∂̄_k (bmPotential h)‖²`
(as lower integrals, so the statement is meaningful even when one side is infinite). -/
theorem czbL2_energy_eq_dbar {n : ℕ} (hn : 0 < n) {h : Fin n → (Fin n → ℂ) → ℂ}
    (hh : ∀ j, ContDiff ℝ 2 (h j)) (hcs : ∀ j, HasCompactSupport (h j)) :
    (∑ k : Fin n, ∫⁻ z : Fin n → ℂ, ENNReal.ofReal
        ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2)
      = ∑ k : Fin n, ∫⁻ z : Fin n → ℂ, ENNReal.ofReal
        ‖Work.CR.Flat.dbarCoord k (bmPotential h) z‖ ^ 2 := by
  classical
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- ## Step 1: the potential is `C¹`
  have hu : ContDiff ℝ 1 (bmPotential h) :=
    bmPotential_contDiff_of_hasCompactSupport hn (fun j => (hh j).of_le (by norm_num)) hcs
  -- ## Step 2: a common radius off which the data vanish
  choose Rj hRj using fun j => exists_radius_sup (hcs j)
  set R0 : ℝ := (∑ j : Fin n, Rj j) + 1 with hR0def
  have hR0pos : 0 < R0 := by
    have : 0 < ∑ j : Fin n, Rj j :=
      Finset.sum_pos (fun j _ => (hRj j).1) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    rw [hR0def]; linarith
  have hsupp : ∀ j x, R0 ≤ ‖x‖ → h j x = 0 := by
    intro j x hx
    refine (hRj j).2 x (le_trans ?_ hx)
    have hle : Rj j ≤ ∑ i : Fin n, Rj i :=
      Finset.single_le_sum (fun i _ => le_of_lt (hRj i).1) (Finset.mem_univ j)
    rw [hR0def]; linarith
  -- ## Step 3: decay of the potential
  obtain ⟨Cdec, hCdec0, hdec⟩ :=
    norm_bmPot_le_of_large hn hR0pos (fun j => (hh j).continuous) hcs hsupp
  have hdec' : ∀ z : Fin n → ℂ, 2 * R0 ≤ ‖z‖ →
      ‖bmPotential h z‖ ≤ Cdec * ‖z‖ ^ (1 - 2 * (n : ℝ)) := by
    intro z hz
    rw [bmPotential_eq_bmPot]
    exact hdec z hz
  -- ## the energy densities
  have hFcont : Continuous (fun z : Fin n → ℂ => ∑ k, ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2) :=
    continuous_finsetSum Finset.univ
      (fun k _ => ((continuous_dCoord_of_contDiff hu k).norm).pow 2)
  have hGcont : Continuous (fun z : Fin n → ℂ => ∑ k, ‖Work.CR.Flat.dbarCoord k (bmPotential h) z‖ ^ 2) :=
    continuous_finsetSum Finset.univ
      (fun k _ => ((continuous_dbarCoord_of_contDiff hu k).norm).pow 2)
  have hF0 : ∀ z, 0 ≤ ∑ k : Fin n, ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2 :=
    fun z => Finset.sum_nonneg (fun k _ => pow_nonneg (norm_nonneg _) 2)
  have hG0 : ∀ z, 0 ≤ ∑ k : Fin n, ‖Work.CR.Flat.dbarCoord k (bmPotential h) z‖ ^ 2 :=
    fun z => Finset.sum_nonneg (fun k _ => pow_nonneg (norm_nonneg _) 2)
  -- ## vanishing off the support of the cut-off
  have hzero : ∀ (R : ℝ) (z : Fin n → ℂ), z ∉ tsupport (cutC (n := n) R) →
      cutRe (n := n) R z = 0 ∧ (∀ j : Fin n, Work.CR.Flat.dCoord j (cutC (n := n) R) z = 0)
        ∧ (∀ j : Fin n, Work.CR.Flat.dbarCoord j (cutC (n := n) R) z = 0) := by
    intro R z hz
    have hev : cutC (n := n) R =ᶠ[nhds z] 0 := eventuallyEq_zero_of_notMem_tsupport hz
    have hz0 : cutC (n := n) R z = 0 := hev.eq_of_nhds
    have hfd : fderiv ℝ (cutC (n := n) R) z = 0 := by rw [hev.fderiv_eq]; simp
    have hcre : cutRe (n := n) R z = 0 := by
      have h := hz0; rw [cutC] at h; exact Complex.ofReal_eq_zero.mp h
    refine ⟨hcre, ?_, ?_⟩
    · intro j; simp [Work.CR.Flat.dCoord, hfd]
    · intro j; simp [Work.CR.Flat.dbarCoord, hfd]
  -- ## the pointwise expansion of the localised energy (∂)
  have hpt_d : ∀ (R : ℝ) (z : Fin n → ℂ),
      (∑ j, ‖Work.CR.Flat.dCoord j (cutC (n := n) R * bmPotential h) z‖ ^ 2)
        = (cutRe (n := n) R z) ^ 2 * (∑ k, ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2)
          + (∑ j, 2 * cutRe (n := n) R z
              * (Work.CR.Flat.dCoord j (bmPotential h) z
                  * star (bmPotential h z * Work.CR.Flat.dCoord j (cutC (n := n) R) z)).re)
          + ‖bmPotential h z‖ ^ 2 * (∑ j, ‖Work.CR.Flat.dCoord j (cutC (n := n) R) z‖ ^ 2) := by
    intro R z
    have hchid : DifferentiableAt ℝ (cutC (n := n) R) z :=
      ((contDiff_cutC R).differentiable (by norm_num)).differentiableAt
    have hud : DifferentiableAt ℝ (bmPotential h) z :=
      (hu.differentiable (by norm_num)).differentiableAt
    have hterm : ∀ j : Fin n,
        ‖Work.CR.Flat.dCoord j (cutC (n := n) R * bmPotential h) z‖ ^ 2
          = (cutRe (n := n) R z) ^ 2 * ‖Work.CR.Flat.dCoord j (bmPotential h) z‖ ^ 2
            + 2 * cutRe (n := n) R z
              * (Work.CR.Flat.dCoord j (bmPotential h) z
                  * star (bmPotential h z * Work.CR.Flat.dCoord j (cutC (n := n) R) z)).re
            + ‖bmPotential h z‖ ^ 2 * ‖Work.CR.Flat.dCoord j (cutC (n := n) R) z‖ ^ 2 := by
      intro j
      change ‖Work.CR.Flat.dCoord j (fun w => cutC (n := n) R w * bmPotential h w) z‖ ^ 2 = _
      rw [Work.CR.Flat.Cauchy.bmCz.dCoord_mul j (cutC (n := n) R) (bmPotential h) z hchid hud]
      rw [complex_norm_add_sq, norm_mul, norm_mul, mul_pow, mul_pow]
      rw [show ‖cutC (n := n) R z‖ = cutRe (n := n) R z from by
        rw [cutC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cutRe_nonneg R z)]]
      rw [show cutC (n := n) R z = ((cutRe (n := n) R z : ℝ) : ℂ) from rfl]
      have hcross := re_cross_cut (Work.CR.Flat.dCoord j (bmPotential h) z)
        (Work.CR.Flat.dCoord j (cutC (n := n) R) z) (bmPotential h z) (cutRe (n := n) R z)
      rw [hcross]
      ring
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [Finset.mul_sum]
  -- ## the pointwise expansion of the localised energy (∂̄)
  have hpt_dbar : ∀ (R : ℝ) (z : Fin n → ℂ),
      (∑ j, ‖Work.CR.Flat.dbarCoord j (cutC (n := n) R * bmPotential h) z‖ ^ 2)
        = (cutRe (n := n) R z) ^ 2 * (∑ k, ‖Work.CR.Flat.dbarCoord k (bmPotential h) z‖ ^ 2)
          + (∑ j, 2 * cutRe (n := n) R z
              * (Work.CR.Flat.dbarCoord j (bmPotential h) z
                  * star (bmPotential h z * Work.CR.Flat.dbarCoord j (cutC (n := n) R) z)).re)
          + ‖bmPotential h z‖ ^ 2 * (∑ j, ‖Work.CR.Flat.dbarCoord j (cutC (n := n) R) z‖ ^ 2) := by
    intro R z
    have hchid : DifferentiableAt ℝ (cutC (n := n) R) z :=
      ((contDiff_cutC R).differentiable (by norm_num)).differentiableAt
    have hud : DifferentiableAt ℝ (bmPotential h) z :=
      (hu.differentiable (by norm_num)).differentiableAt
    have hterm : ∀ j : Fin n,
        ‖Work.CR.Flat.dbarCoord j (cutC (n := n) R * bmPotential h) z‖ ^ 2
          = (cutRe (n := n) R z) ^ 2 * ‖Work.CR.Flat.dbarCoord j (bmPotential h) z‖ ^ 2
            + 2 * cutRe (n := n) R z
              * (Work.CR.Flat.dbarCoord j (bmPotential h) z
                  * star (bmPotential h z * Work.CR.Flat.dbarCoord j (cutC (n := n) R) z)).re
            + ‖bmPotential h z‖ ^ 2 * ‖Work.CR.Flat.dbarCoord j (cutC (n := n) R) z‖ ^ 2 := by
      intro j
      change ‖Work.CR.Flat.dbarCoord j (fun w => cutC (n := n) R w * bmPotential h w) z‖ ^ 2 = _
      rw [Work.CR.Flat.Polydisc.dbarCoord_mul j (cutC (n := n) R) (bmPotential h) z hchid hud]
      rw [complex_norm_add_sq, norm_mul, norm_mul, mul_pow, mul_pow]
      rw [show ‖cutC (n := n) R z‖ = cutRe (n := n) R z from by
        rw [cutC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cutRe_nonneg R z)]]
      rw [show cutC (n := n) R z = ((cutRe (n := n) R z : ℝ) : ℂ) from rfl]
      have hcross := re_cross_cut (Work.CR.Flat.dbarCoord j (bmPotential h) z)
        (Work.CR.Flat.dbarCoord j (cutC (n := n) R) z) (bmPotential h z) (cutRe (n := n) R z)
      rw [hcross]
      ring
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [Finset.mul_sum]

  -- ## integrability of the three pieces of the expansion
  -- ## integrability of the pieces of the expansion
  have integrable_of_supp : ∀ (R : ℝ), 0 < R → ∀ (f : (Fin n → ℂ) → ℝ), Continuous f →
      (∀ z, z ∉ tsupport (cutC (n := n) R) → f z = 0) → Integrable f := by
    intro R hR f hf hsupp
    exact hf.integrable_of_hasCompactSupport
      (HasCompactSupport.of_forall_notMem_tsupport (hasCompactSupport_cutC hR) hsupp)
  have hIntF : ∀ R : ℝ, 0 < R → Integrable (fun z => (cutRe (n := n) R z) ^ 2
      * (∑ k, ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2)) := fun R hR =>
    integrable_of_supp R hR _
      ((contDiff_cutRe R).continuous.pow 2 |>.mul hFcont) (fun z hz => by
        show (cutRe (n := n) R z) ^ 2 * (∑ k, ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2) = 0
        rw [(hzero R z hz).1]; ring)
  have hIntG : ∀ R : ℝ, 0 < R → Integrable (fun z => (cutRe (n := n) R z) ^ 2
      * (∑ k, ‖Work.CR.Flat.dbarCoord k (bmPotential h) z‖ ^ 2)) := fun R hR =>
    integrable_of_supp R hR _
      ((contDiff_cutRe R).continuous.pow 2 |>.mul hGcont) (fun z hz => by
        show (cutRe (n := n) R z) ^ 2 * (∑ k, ‖Work.CR.Flat.dbarCoord k (bmPotential h) z‖ ^ 2) = 0
        rw [(hzero R z hz).1]; ring)
  have hIntPd : ∀ R : ℝ, 0 < R → Integrable (fun z => ∑ j, 2 * cutRe (n := n) R z
      * (Work.CR.Flat.dCoord j (bmPotential h) z
          * star (bmPotential h z * Work.CR.Flat.dCoord j (cutC (n := n) R) z)).re) := fun R hR =>
    integrable_of_supp R hR _ (continuous_finsetSum _ fun j _ =>
        (continuous_const.mul (contDiff_cutRe R).continuous).mul
          (Complex.continuous_re.comp ((continuous_dCoord_of_contDiff hu j).mul
            ((hu.continuous.mul (continuous_dCoord_of_contDiff (contDiff_cutC R) j)).star))))
      (fun z hz => by
        show (∑ j, 2 * cutRe (n := n) R z * (Work.CR.Flat.dCoord j (bmPotential h) z
          * star (bmPotential h z * Work.CR.Flat.dCoord j (cutC (n := n) R) z)).re) = 0
        rw [Finset.sum_eq_zero (fun j _ => by rw [(hzero R z hz).2.1 j]; simp)])
  have hIntPb : ∀ R : ℝ, 0 < R → Integrable (fun z => ∑ j, 2 * cutRe (n := n) R z
      * (Work.CR.Flat.dbarCoord j (bmPotential h) z
          * star (bmPotential h z * Work.CR.Flat.dbarCoord j (cutC (n := n) R) z)).re) := fun R hR =>
    integrable_of_supp R hR _ (continuous_finsetSum _ fun j _ =>
        (continuous_const.mul (contDiff_cutRe R).continuous).mul
          (Complex.continuous_re.comp ((continuous_dbarCoord_of_contDiff hu j).mul
            ((hu.continuous.mul (continuous_dbarCoord_of_contDiff (contDiff_cutC R) j)).star))))
      (fun z hz => by
        show (∑ j, 2 * cutRe (n := n) R z * (Work.CR.Flat.dbarCoord j (bmPotential h) z
          * star (bmPotential h z * Work.CR.Flat.dbarCoord j (cutC (n := n) R) z)).re) = 0
        rw [Finset.sum_eq_zero (fun j _ => by rw [(hzero R z hz).2.2 j]; simp)])
  have hIntQd : ∀ R : ℝ, 0 < R → Integrable (fun z => ‖bmPotential h z‖ ^ 2
      * (∑ j, ‖Work.CR.Flat.dCoord j (cutC (n := n) R) z‖ ^ 2)) := fun R hR =>
    integrable_of_supp R hR _
      (hu.continuous.norm.pow 2 |>.mul (continuous_finsetSum _ fun j _ =>
        (continuous_dCoord_of_contDiff (contDiff_cutC R) j).norm.pow 2)) (fun z hz => by
        show ‖bmPotential h z‖ ^ 2 * (∑ j, ‖Work.CR.Flat.dCoord j (cutC (n := n) R) z‖ ^ 2) = 0
        rw [Finset.sum_eq_zero (fun j _ => by rw [(hzero R z hz).2.1 j]; simp), mul_zero])
  have hIntQb : ∀ R : ℝ, 0 < R → Integrable (fun z => ‖bmPotential h z‖ ^ 2
      * (∑ j, ‖Work.CR.Flat.dbarCoord j (cutC (n := n) R) z‖ ^ 2)) := fun R hR =>
    integrable_of_supp R hR _
      (hu.continuous.norm.pow 2 |>.mul (continuous_finsetSum _ fun j _ =>
        (continuous_dbarCoord_of_contDiff (contDiff_cutC R) j).norm.pow 2)) (fun z hz => by
        show ‖bmPotential h z‖ ^ 2 * (∑ j, ‖Work.CR.Flat.dbarCoord j (cutC (n := n) R) z‖ ^ 2) = 0
        rw [Finset.sum_eq_zero (fun j _ => by rw [(hzero R z hz).2.2 j]; simp), mul_zero])
  -- ## the integral expansion (∂)
  have expand_d : ∀ R : ℝ, 0 < R →
      (∫ z, ∑ j, ‖Work.CR.Flat.dCoord j (cutC (n := n) R * bmPotential h) z‖ ^ 2)
        = (∫ z, (cutRe (n := n) R z) ^ 2 * (∑ k, ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2))
          + (∫ z, ∑ j, 2 * cutRe (n := n) R z
              * (Work.CR.Flat.dCoord j (bmPotential h) z
                  * star (bmPotential h z * Work.CR.Flat.dCoord j (cutC (n := n) R) z)).re)
          + (∫ z, ‖bmPotential h z‖ ^ 2
              * (∑ j, ‖Work.CR.Flat.dCoord j (cutC (n := n) R) z‖ ^ 2)) := by
    intro R hR
    have h1 := hIntF R hR
    have h2 := hIntPd R hR
    have h3 := hIntQd R hR
    have hAB : Integrable (fun z => (cutRe (n := n) R z) ^ 2
        * (∑ k, ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2)
        + (∑ j, 2 * cutRe (n := n) R z * (Work.CR.Flat.dCoord j (bmPotential h) z
            * star (bmPotential h z * Work.CR.Flat.dCoord j (cutC (n := n) R) z)).re)) := h1.add h2
    rw [integral_congr_ae (Eventually.of_forall (hpt_d R))]
    have s1 : (∫ z, (cutRe (n := n) R z) ^ 2
          * (∑ k, ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2)
          + (∑ j, 2 * cutRe (n := n) R z * (Work.CR.Flat.dCoord j (bmPotential h) z
              * star (bmPotential h z * Work.CR.Flat.dCoord j (cutC (n := n) R) z)).re)
          + ‖bmPotential h z‖ ^ 2 * (∑ j, ‖Work.CR.Flat.dCoord j (cutC (n := n) R) z‖ ^ 2))
        = (∫ z, (cutRe (n := n) R z) ^ 2
              * (∑ k, ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2)
            + (∑ j, 2 * cutRe (n := n) R z * (Work.CR.Flat.dCoord j (bmPotential h) z
                * star (bmPotential h z * Work.CR.Flat.dCoord j (cutC (n := n) R) z)).re))
          + (∫ z, ‖bmPotential h z‖ ^ 2
              * (∑ j, ‖Work.CR.Flat.dCoord j (cutC (n := n) R) z‖ ^ 2)) :=
      integral_add hAB h3
    have s2 : (∫ z, (cutRe (n := n) R z) ^ 2
            * (∑ k, ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2)
          + (∑ j, 2 * cutRe (n := n) R z * (Work.CR.Flat.dCoord j (bmPotential h) z
              * star (bmPotential h z * Work.CR.Flat.dCoord j (cutC (n := n) R) z)).re))
        = (∫ z, (cutRe (n := n) R z) ^ 2
              * (∑ k, ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2))
          + (∫ z, ∑ j, 2 * cutRe (n := n) R z * (Work.CR.Flat.dCoord j (bmPotential h) z
              * star (bmPotential h z * Work.CR.Flat.dCoord j (cutC (n := n) R) z)).re) :=
      integral_add h1 h2
    rw [s1, s2]
  -- ## the integral expansion (∂̄)
  have expand_dbar : ∀ R : ℝ, 0 < R →
      (∫ z, ∑ j, ‖Work.CR.Flat.dbarCoord j (cutC (n := n) R * bmPotential h) z‖ ^ 2)
        = (∫ z, (cutRe (n := n) R z) ^ 2 * (∑ k, ‖Work.CR.Flat.dbarCoord k (bmPotential h) z‖ ^ 2))
          + (∫ z, ∑ j, 2 * cutRe (n := n) R z
              * (Work.CR.Flat.dbarCoord j (bmPotential h) z
                  * star (bmPotential h z * Work.CR.Flat.dbarCoord j (cutC (n := n) R) z)).re)
          + (∫ z, ‖bmPotential h z‖ ^ 2
              * (∑ j, ‖Work.CR.Flat.dbarCoord j (cutC (n := n) R) z‖ ^ 2)) := by
    intro R hR
    have h1 := hIntG R hR
    have h2 := hIntPb R hR
    have h3 := hIntQb R hR
    have hAB : Integrable (fun z => (cutRe (n := n) R z) ^ 2
        * (∑ k, ‖Work.CR.Flat.dbarCoord k (bmPotential h) z‖ ^ 2)
        + (∑ j, 2 * cutRe (n := n) R z * (Work.CR.Flat.dbarCoord j (bmPotential h) z
            * star (bmPotential h z * Work.CR.Flat.dbarCoord j (cutC (n := n) R) z)).re)) := h1.add h2
    rw [integral_congr_ae (Eventually.of_forall (hpt_dbar R))]
    have s1 : (∫ z, (cutRe (n := n) R z) ^ 2
          * (∑ k, ‖Work.CR.Flat.dbarCoord k (bmPotential h) z‖ ^ 2)
          + (∑ j, 2 * cutRe (n := n) R z * (Work.CR.Flat.dbarCoord j (bmPotential h) z
              * star (bmPotential h z * Work.CR.Flat.dbarCoord j (cutC (n := n) R) z)).re)
          + ‖bmPotential h z‖ ^ 2 * (∑ j, ‖Work.CR.Flat.dbarCoord j (cutC (n := n) R) z‖ ^ 2))
        = (∫ z, (cutRe (n := n) R z) ^ 2
              * (∑ k, ‖Work.CR.Flat.dbarCoord k (bmPotential h) z‖ ^ 2)
            + (∑ j, 2 * cutRe (n := n) R z * (Work.CR.Flat.dbarCoord j (bmPotential h) z
                * star (bmPotential h z * Work.CR.Flat.dbarCoord j (cutC (n := n) R) z)).re))
          + (∫ z, ‖bmPotential h z‖ ^ 2
              * (∑ j, ‖Work.CR.Flat.dbarCoord j (cutC (n := n) R) z‖ ^ 2)) :=
      integral_add hAB h3
    have s2 : (∫ z, (cutRe (n := n) R z) ^ 2
            * (∑ k, ‖Work.CR.Flat.dbarCoord k (bmPotential h) z‖ ^ 2)
          + (∑ j, 2 * cutRe (n := n) R z * (Work.CR.Flat.dbarCoord j (bmPotential h) z
              * star (bmPotential h z * Work.CR.Flat.dbarCoord j (cutC (n := n) R) z)).re))
        = (∫ z, (cutRe (n := n) R z) ^ 2
              * (∑ k, ‖Work.CR.Flat.dbarCoord k (bmPotential h) z‖ ^ 2))
          + (∫ z, ∑ j, 2 * cutRe (n := n) R z * (Work.CR.Flat.dbarCoord j (bmPotential h) z
              * star (bmPotential h z * Work.CR.Flat.dbarCoord j (cutC (n := n) R) z)).re) :=
      integral_add h1 h2
    rw [s1, s2]

  -- ## the cross-term bound (∂)
  have hp_d : ∀ (R ε : ℝ), 0 < R → 0 < ε →
      |∫ z, ∑ j, 2 * cutRe (n := n) R z
          * (Work.CR.Flat.dCoord j (bmPotential h) z
              * star (bmPotential h z * Work.CR.Flat.dCoord j (cutC (n := n) R) z)).re|
        ≤ ε * (∫ z, (cutRe (n := n) R z) ^ 2
              * (∑ k, ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2))
          + (∫ z, ‖bmPotential h z‖ ^ 2
              * (∑ j, ‖Work.CR.Flat.dCoord j (cutC (n := n) R) z‖ ^ 2)) / ε := by
    intro R ε hR hε
    have hint_chi := hIntF R hR
    have hint_q := hIntQd R hR
    have hpt : ∀ z : Fin n → ℂ,
        |∑ j, 2 * cutRe (n := n) R z
            * (Work.CR.Flat.dCoord j (bmPotential h) z
                * star (bmPotential h z * Work.CR.Flat.dCoord j (cutC (n := n) R) z)).re|
          ≤ ε * ((cutRe (n := n) R z) ^ 2
              * (∑ j, ‖Work.CR.Flat.dCoord j (bmPotential h) z‖ ^ 2))
            + (1 / ε) * (‖bmPotential h z‖ ^ 2
              * (∑ j, ‖Work.CR.Flat.dCoord j (cutC (n := n) R) z‖ ^ 2)) := by
      intro z
      have hstep : ∀ j : Fin n,
          |2 * cutRe (n := n) R z
              * (Work.CR.Flat.dCoord j (bmPotential h) z
                  * star (bmPotential h z * Work.CR.Flat.dCoord j (cutC (n := n) R) z)).re|
            ≤ ε * ((cutRe (n := n) R z) ^ 2 * ‖Work.CR.Flat.dCoord j (bmPotential h) z‖ ^ 2)
              + (1 / ε) * (‖bmPotential h z‖ ^ 2 * ‖Work.CR.Flat.dCoord j (cutC (n := n) R) z‖ ^ 2) := by
        intro j
        calc |2 * cutRe (n := n) R z
              * (Work.CR.Flat.dCoord j (bmPotential h) z
                  * star (bmPotential h z * Work.CR.Flat.dCoord j (cutC (n := n) R) z)).re|
            = 2 * cutRe (n := n) R z
                * |(Work.CR.Flat.dCoord j (bmPotential h) z
                    * star (bmPotential h z * Work.CR.Flat.dCoord j (cutC (n := n) R) z)).re| := by
              rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
                abs_of_nonneg (cutRe_nonneg R z)]
          _ ≤ 2 * cutRe (n := n) R z
                * ‖Work.CR.Flat.dCoord j (bmPotential h) z
                    * star (bmPotential h z * Work.CR.Flat.dCoord j (cutC (n := n) R) z)‖ := by
              exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _)
                (mul_nonneg (by norm_num) (cutRe_nonneg R z))
          _ = 2 * (cutRe (n := n) R z * ‖Work.CR.Flat.dCoord j (bmPotential h) z‖)
                * (‖bmPotential h z‖ * ‖Work.CR.Flat.dCoord j (cutC (n := n) R) z‖) := by
              simp only [norm_mul, norm_star]; ring
          _ ≤ ε * (cutRe (n := n) R z * ‖Work.CR.Flat.dCoord j (bmPotential h) z‖) ^ 2
                + (‖bmPotential h z‖ * ‖Work.CR.Flat.dCoord j (cutC (n := n) R) z‖) ^ 2 / ε :=
              two_mul_le_eps _ _ ε hε
          _ = ε * ((cutRe (n := n) R z) ^ 2 * ‖Work.CR.Flat.dCoord j (bmPotential h) z‖ ^ 2)
                + (1 / ε) * (‖bmPotential h z‖ ^ 2
                    * ‖Work.CR.Flat.dCoord j (cutC (n := n) R) z‖ ^ 2) := by
              rw [div_eq_mul_inv]; ring
      calc |∑ j, 2 * cutRe (n := n) R z
            * (Work.CR.Flat.dCoord j (bmPotential h) z
                * star (bmPotential h z * Work.CR.Flat.dCoord j (cutC (n := n) R) z)).re|
          ≤ ∑ j, |2 * cutRe (n := n) R z
              * (Work.CR.Flat.dCoord j (bmPotential h) z
                  * star (bmPotential h z * Work.CR.Flat.dCoord j (cutC (n := n) R) z)).re| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, (ε * ((cutRe (n := n) R z) ^ 2 * ‖Work.CR.Flat.dCoord j (bmPotential h) z‖ ^ 2)
              + (1 / ε) * (‖bmPotential h z‖ ^ 2
                  * ‖Work.CR.Flat.dCoord j (cutC (n := n) R) z‖ ^ 2)) :=
            Finset.sum_le_sum fun j _ => hstep j
        _ = ε * ((cutRe (n := n) R z) ^ 2
              * (∑ j, ‖Work.CR.Flat.dCoord j (bmPotential h) z‖ ^ 2))
            + (1 / ε) * (‖bmPotential h z‖ ^ 2
              * (∑ j, ‖Work.CR.Flat.dCoord j (cutC (n := n) R) z‖ ^ 2)) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
              ← Finset.mul_sum, ← Finset.mul_sum]
    have hg : Integrable (fun z => ε * ((cutRe (n := n) R z) ^ 2
          * (∑ k, ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2))
        + (1 / ε) * (‖bmPotential h z‖ ^ 2
          * (∑ j, ‖Work.CR.Flat.dCoord j (cutC (n := n) R) z‖ ^ 2))) :=
      (hint_chi.const_mul ε).add (hint_q.const_mul (1 / ε))
    calc |∫ z, ∑ j, 2 * cutRe (n := n) R z
          * (Work.CR.Flat.dCoord j (bmPotential h) z
              * star (bmPotential h z * Work.CR.Flat.dCoord j (cutC (n := n) R) z)).re|
        = ‖∫ z, ∑ j, 2 * cutRe (n := n) R z
            * (Work.CR.Flat.dCoord j (bmPotential h) z
                * star (bmPotential h z * Work.CR.Flat.dCoord j (cutC (n := n) R) z)).re‖ := by
          rw [Real.norm_eq_abs]
      _ ≤ ∫ z, ‖∑ j, 2 * cutRe (n := n) R z
            * (Work.CR.Flat.dCoord j (bmPotential h) z
                * star (bmPotential h z * Work.CR.Flat.dCoord j (cutC (n := n) R) z)).re‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ z, (ε * ((cutRe (n := n) R z) ^ 2
            * (∑ j, ‖Work.CR.Flat.dCoord j (bmPotential h) z‖ ^ 2))
          + (1 / ε) * (‖bmPotential h z‖ ^ 2
            * (∑ j, ‖Work.CR.Flat.dCoord j (cutC (n := n) R) z‖ ^ 2))) :=
          integral_mono_ae (hIntPd R hR).abs hg
            (Eventually.of_forall fun z => by
              show ‖∑ j, 2 * cutRe (n := n) R z
                  * (Work.CR.Flat.dCoord j (bmPotential h) z
                      * star (bmPotential h z * Work.CR.Flat.dCoord j (cutC (n := n) R) z)).re‖ ≤ _
              rw [Real.norm_eq_abs]; exact hpt z)
      _ = ε * (∫ z, (cutRe (n := n) R z) ^ 2
            * (∑ k, ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2))
          + (∫ z, ‖bmPotential h z‖ ^ 2
            * (∑ j, ‖Work.CR.Flat.dCoord j (cutC (n := n) R) z‖ ^ 2)) / ε := by
          rw [integral_add (hint_chi.const_mul ε) (hint_q.const_mul (1 / ε)),
            integral_const_mul, integral_const_mul]
          ring


  -- ## the cross-term bound (∂̄)
  have hp_dbar : ∀ (R ε : ℝ), 0 < R → 0 < ε →
      |∫ z, ∑ j, 2 * cutRe (n := n) R z
          * (Work.CR.Flat.dbarCoord j (bmPotential h) z
              * star (bmPotential h z * Work.CR.Flat.dbarCoord j (cutC (n := n) R) z)).re|
        ≤ ε * (∫ z, (cutRe (n := n) R z) ^ 2
              * (∑ k, ‖Work.CR.Flat.dbarCoord k (bmPotential h) z‖ ^ 2))
          + (∫ z, ‖bmPotential h z‖ ^ 2
              * (∑ j, ‖Work.CR.Flat.dbarCoord j (cutC (n := n) R) z‖ ^ 2)) / ε := by
    intro R ε hR hε
    have hint_chi := hIntG R hR
    have hint_q := hIntQb R hR
    have hpt : ∀ z : Fin n → ℂ,
        |∑ j, 2 * cutRe (n := n) R z
            * (Work.CR.Flat.dbarCoord j (bmPotential h) z
                * star (bmPotential h z * Work.CR.Flat.dbarCoord j (cutC (n := n) R) z)).re|
          ≤ ε * ((cutRe (n := n) R z) ^ 2
              * (∑ j, ‖Work.CR.Flat.dbarCoord j (bmPotential h) z‖ ^ 2))
            + (1 / ε) * (‖bmPotential h z‖ ^ 2
              * (∑ j, ‖Work.CR.Flat.dbarCoord j (cutC (n := n) R) z‖ ^ 2)) := by
      intro z
      have hstep : ∀ j : Fin n,
          |2 * cutRe (n := n) R z
              * (Work.CR.Flat.dbarCoord j (bmPotential h) z
                  * star (bmPotential h z * Work.CR.Flat.dbarCoord j (cutC (n := n) R) z)).re|
            ≤ ε * ((cutRe (n := n) R z) ^ 2 * ‖Work.CR.Flat.dbarCoord j (bmPotential h) z‖ ^ 2)
              + (1 / ε) * (‖bmPotential h z‖ ^ 2 * ‖Work.CR.Flat.dbarCoord j (cutC (n := n) R) z‖ ^ 2) := by
        intro j
        calc |2 * cutRe (n := n) R z
              * (Work.CR.Flat.dbarCoord j (bmPotential h) z
                  * star (bmPotential h z * Work.CR.Flat.dbarCoord j (cutC (n := n) R) z)).re|
            = 2 * cutRe (n := n) R z
                * |(Work.CR.Flat.dbarCoord j (bmPotential h) z
                    * star (bmPotential h z * Work.CR.Flat.dbarCoord j (cutC (n := n) R) z)).re| := by
              rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
                abs_of_nonneg (cutRe_nonneg R z)]
          _ ≤ 2 * cutRe (n := n) R z
                * ‖Work.CR.Flat.dbarCoord j (bmPotential h) z
                    * star (bmPotential h z * Work.CR.Flat.dbarCoord j (cutC (n := n) R) z)‖ := by
              exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _)
                (mul_nonneg (by norm_num) (cutRe_nonneg R z))
          _ = 2 * (cutRe (n := n) R z * ‖Work.CR.Flat.dbarCoord j (bmPotential h) z‖)
                * (‖bmPotential h z‖ * ‖Work.CR.Flat.dbarCoord j (cutC (n := n) R) z‖) := by
              simp only [norm_mul, norm_star]; ring
          _ ≤ ε * (cutRe (n := n) R z * ‖Work.CR.Flat.dbarCoord j (bmPotential h) z‖) ^ 2
                + (‖bmPotential h z‖ * ‖Work.CR.Flat.dbarCoord j (cutC (n := n) R) z‖) ^ 2 / ε :=
              two_mul_le_eps _ _ ε hε
          _ = ε * ((cutRe (n := n) R z) ^ 2 * ‖Work.CR.Flat.dbarCoord j (bmPotential h) z‖ ^ 2)
                + (1 / ε) * (‖bmPotential h z‖ ^ 2
                    * ‖Work.CR.Flat.dbarCoord j (cutC (n := n) R) z‖ ^ 2) := by
              rw [div_eq_mul_inv]; ring
      calc |∑ j, 2 * cutRe (n := n) R z
            * (Work.CR.Flat.dbarCoord j (bmPotential h) z
                * star (bmPotential h z * Work.CR.Flat.dbarCoord j (cutC (n := n) R) z)).re|
          ≤ ∑ j, |2 * cutRe (n := n) R z
              * (Work.CR.Flat.dbarCoord j (bmPotential h) z
                  * star (bmPotential h z * Work.CR.Flat.dbarCoord j (cutC (n := n) R) z)).re| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, (ε * ((cutRe (n := n) R z) ^ 2 * ‖Work.CR.Flat.dbarCoord j (bmPotential h) z‖ ^ 2)
              + (1 / ε) * (‖bmPotential h z‖ ^ 2
                  * ‖Work.CR.Flat.dbarCoord j (cutC (n := n) R) z‖ ^ 2)) :=
            Finset.sum_le_sum fun j _ => hstep j
        _ = ε * ((cutRe (n := n) R z) ^ 2
              * (∑ j, ‖Work.CR.Flat.dbarCoord j (bmPotential h) z‖ ^ 2))
            + (1 / ε) * (‖bmPotential h z‖ ^ 2
              * (∑ j, ‖Work.CR.Flat.dbarCoord j (cutC (n := n) R) z‖ ^ 2)) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
              ← Finset.mul_sum, ← Finset.mul_sum]
    have hg : Integrable (fun z => ε * ((cutRe (n := n) R z) ^ 2
          * (∑ k, ‖Work.CR.Flat.dbarCoord k (bmPotential h) z‖ ^ 2))
        + (1 / ε) * (‖bmPotential h z‖ ^ 2
          * (∑ j, ‖Work.CR.Flat.dbarCoord j (cutC (n := n) R) z‖ ^ 2))) :=
      (hint_chi.const_mul ε).add (hint_q.const_mul (1 / ε))
    calc |∫ z, ∑ j, 2 * cutRe (n := n) R z
          * (Work.CR.Flat.dbarCoord j (bmPotential h) z
              * star (bmPotential h z * Work.CR.Flat.dbarCoord j (cutC (n := n) R) z)).re|
        = ‖∫ z, ∑ j, 2 * cutRe (n := n) R z
            * (Work.CR.Flat.dbarCoord j (bmPotential h) z
                * star (bmPotential h z * Work.CR.Flat.dbarCoord j (cutC (n := n) R) z)).re‖ := by
          rw [Real.norm_eq_abs]
      _ ≤ ∫ z, ‖∑ j, 2 * cutRe (n := n) R z
            * (Work.CR.Flat.dbarCoord j (bmPotential h) z
                * star (bmPotential h z * Work.CR.Flat.dbarCoord j (cutC (n := n) R) z)).re‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ z, (ε * ((cutRe (n := n) R z) ^ 2
            * (∑ j, ‖Work.CR.Flat.dbarCoord j (bmPotential h) z‖ ^ 2))
          + (1 / ε) * (‖bmPotential h z‖ ^ 2
            * (∑ j, ‖Work.CR.Flat.dbarCoord j (cutC (n := n) R) z‖ ^ 2))) :=
          integral_mono_ae (hIntPb R hR).abs hg
            (Eventually.of_forall fun z => by
              show ‖∑ j, 2 * cutRe (n := n) R z
                  * (Work.CR.Flat.dbarCoord j (bmPotential h) z
                      * star (bmPotential h z * Work.CR.Flat.dbarCoord j (cutC (n := n) R) z)).re‖ ≤ _
              rw [Real.norm_eq_abs]; exact hpt z)
      _ = ε * (∫ z, (cutRe (n := n) R z) ^ 2
            * (∑ k, ‖Work.CR.Flat.dbarCoord k (bmPotential h) z‖ ^ 2))
          + (∫ z, ‖bmPotential h z‖ ^ 2
            * (∑ j, ‖Work.CR.Flat.dbarCoord j (cutC (n := n) R) z‖ ^ 2)) / ε := by
          rw [integral_add (hint_chi.const_mul ε) (hint_q.const_mul (1 / ε)),
            integral_const_mul, integral_const_mul]
          ring
  -- ## the isometry applied to the localised data
  have hiso : ∀ N : ℕ,
      (∫ z, ∑ j, ‖Work.CR.Flat.dCoord j (cutC (n := n) (N + 1) * bmPotential h) z‖ ^ 2)
        = (∫ z, ∑ j, ‖Work.CR.Flat.dbarCoord j (cutC (n := n) (N + 1) * bmPotential h) z‖ ^ 2) := by
    intro N
    exact integral_normSq_dCoord_eq_dbarCoord ((contDiff_cutC ((N : ℝ) + 1)).mul hu)
      ((hasCompactSupport_cutC (by positivity : (0 : ℝ) < (N : ℝ) + 1)).mul_right)
  -- ## the abstract limit lemma
  have key := energy_eq_of_approx
      (A := ∫⁻ z : Fin n → ℂ, ENNReal.ofReal (∑ k, ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2))
      (B := ∫⁻ z : Fin n → ℂ, ENNReal.ofReal (∑ k, ‖Work.CR.Flat.dbarCoord k (bmPotential h) z‖ ^ 2))
      (a := fun N => ∫ z, (cutRe (n := n) (N + 1) z) ^ 2
          * (∑ k, ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2))
      (b := fun N => ∫ z, (cutRe (n := n) (N + 1) z) ^ 2
          * (∑ k, ‖Work.CR.Flat.dbarCoord k (bmPotential h) z‖ ^ 2))
      (x := fun N => ∫ z, ∑ j, 2 * cutRe (n := n) (N + 1) z
          * (Work.CR.Flat.dCoord j (bmPotential h) z
              * star (bmPotential h z * Work.CR.Flat.dCoord j (cutC (n := n) (N + 1)) z)).re)
      (w := fun N => ∫ z, ∑ j, 2 * cutRe (n := n) (N + 1) z
          * (Work.CR.Flat.dbarCoord j (bmPotential h) z
              * star (bmPotential h z * Work.CR.Flat.dbarCoord j (cutC (n := n) (N + 1)) z)).re)
      (y := fun N => ∫ z, ‖bmPotential h z‖ ^ 2
          * (∑ j, ‖Work.CR.Flat.dCoord j (cutC (n := n) (N + 1)) z‖ ^ 2))
      (z := fun N => ∫ z, ‖bmPotential h z‖ ^ 2
          * (∑ j, ‖Work.CR.Flat.dbarCoord j (cutC (n := n) (N + 1)) z‖ ^ 2))
      (fun N => integral_nonneg fun z => mul_nonneg (sq_nonneg _) (hF0 z))
      (fun N => integral_nonneg fun z => mul_nonneg (sq_nonneg _) (hG0 z))
      (fun N => integral_nonneg fun z => mul_nonneg (sq_nonneg _)
        (Finset.sum_nonneg fun j _ => pow_nonneg (norm_nonneg _) 2))
      (fun N => integral_nonneg fun z => mul_nonneg (sq_nonneg _)
        (Finset.sum_nonneg fun j _ => pow_nonneg (norm_nonneg _) 2))
      (tendsto_ofReal_integral_cutRe_sq_mul hFcont hF0)
      (tendsto_ofReal_integral_cutRe_sq_mul hGcont hG0)
      (tendsto_integral_cutC_sq_mul (by linarith : (0:ℝ) < 2 * R0) hCdec0 hu.continuous hdec').1
      (tendsto_integral_cutC_sq_mul (by linarith : (0:ℝ) < 2 * R0) hCdec0 hu.continuous hdec').2
      (fun N => (expand_d ((N : ℝ) + 1) (by positivity)).symm.trans
        ((hiso N).trans (expand_dbar ((N : ℝ) + 1) (by positivity))))
      (fun N ε hε0 hε1 => hp_d ((N : ℝ) + 1) ε (by positivity) hε0)
      (fun N ε hε0 hε1 => hp_dbar ((N : ℝ) + 1) ε (by positivity) hε0)
  -- ## identify the lower integrals with the sums
  have hconv_d : (∑ k : Fin n, ∫⁻ z : Fin n → ℂ, ENNReal.ofReal
        ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2)
      = ∫⁻ z : Fin n → ℂ, ENNReal.ofReal
        (∑ k : Fin n, ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2) := by
    have h0 : ∀ (k : Fin n) (z : Fin n → ℂ),
        ENNReal.ofReal ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2
          = ENNReal.ofReal (‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2) := by
      intro k z; rw [ENNReal.ofReal_pow (norm_nonneg _)]
    simp only [h0]
    refine (lintegral_finsetSum Finset.univ
      (f := fun k z => ENNReal.ofReal (‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2))
      (fun k _ => ENNReal.measurable_ofReal.comp
        (((continuous_dCoord_of_contDiff hu k).norm.pow 2).measurable))).symm.trans ?_
    refine lintegral_congr fun z => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => pow_nonneg (norm_nonneg _) 2)]
  have hconv_b : (∑ k : Fin n, ∫⁻ z : Fin n → ℂ, ENNReal.ofReal
        ‖Work.CR.Flat.dbarCoord k (bmPotential h) z‖ ^ 2)
      = ∫⁻ z : Fin n → ℂ, ENNReal.ofReal
        (∑ k : Fin n, ‖Work.CR.Flat.dbarCoord k (bmPotential h) z‖ ^ 2) := by
    have h0 : ∀ (k : Fin n) (z : Fin n → ℂ),
        ENNReal.ofReal ‖Work.CR.Flat.dbarCoord k (bmPotential h) z‖ ^ 2
          = ENNReal.ofReal (‖Work.CR.Flat.dbarCoord k (bmPotential h) z‖ ^ 2) := by
      intro k z; rw [ENNReal.ofReal_pow (norm_nonneg _)]
    simp only [h0]
    refine (lintegral_finsetSum Finset.univ
      (f := fun k z => ENNReal.ofReal (‖Work.CR.Flat.dbarCoord k (bmPotential h) z‖ ^ 2))
      (fun k _ => ENNReal.measurable_ofReal.comp
        (((continuous_dbarCoord_of_contDiff hu k).norm.pow 2).measurable))).symm.trans ?_
    refine lintegral_congr fun z => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => pow_nonneg (norm_nonneg _) 2)]
  rw [hconv_d, hconv_b]
  exact key


end Work.NN.Core
