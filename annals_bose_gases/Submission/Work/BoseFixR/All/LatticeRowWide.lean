import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseBoxFock.AllDefs
import Submission.Work.BoseFixR.GramMassWide
import Submission.Work.BoseFixR.IntegrableChatW1sq
import Submission.Work.BoseFixR.LatticeW1sqFreeEnergyHint
import Submission.Work.BoseFixR.LatticeW1sqPairing
import Submission.Work.BoseFixR.LatticeW1sqParsevalRe
import Submission.Work.BoseFixR.LocaliseGradWideFixed
import Submission.Work.BoseFixR.W1omegaMassLe
import Submission.Work.BoseFixR.kmomLabNormGe
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.All

open MeasureTheory Metric
open _root_.BoseGases Work.UBB
open Work.BoseBox Work.BoseBoxFix Work.BoseBoxFock Work.BoseB7
open scoped Real Topology BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The lattice cosine sum is the real part of the lattice exponential sum -/

lemma phi_eq_re {N : ℕ} {ℓ : ℝ} (S : Finset (Lab N)) (c : Lab N → ℝ) :
    (fun x : E3 => ∑ k ∈ S, c k * Real.cos (inner ℝ (kmomLab ℓ N k) x))
      = fun x => (∑ k ∈ S,
          ((c k : ℂ) * Complex.exp
            (Complex.I * (inner ℝ (kmomLab ℓ N k) x : ℂ)))).re := by
  funext x
  rw [← Complex.reCLM_apply, map_sum Complex.reCLM]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, mul_comm Complex.I, Complex.exp_ofReal_mul_I_re]

/-! ## 2. The abstract comparison -/

theorem latticeRowCore {W : E3 → ℝ} {R ℓ : ℝ}
    (hR : 0 < R) (hℓ : 0 < ℓ)
    (hW : MeasureTheory.Integrable W)
    (hWnn : 0 ≤ᵐ[(MeasureTheory.volume : MeasureTheory.Measure E3)] W)
    (hWe : ∀ x, W (-x) = W x)
    (hsupp : tsupport W ⊆ Metric.ball (0 : E3) R)
    (hRℓ : R ≤ ℓ)
    (hint : MeasureTheory.Integrable (fun q : E3 => (chat W q) ^ 2 / (2 * ‖q‖ ^ 2)))
    (N : ℕ) :
    (∑ k ∈ (Finset.univ : Finset (Lab N)).erase 0,
        (chat W (kmomLab ℓ N k)) ^ 2 / ‖kmomLab ℓ N k‖ ^ 2)
      ≤ 4608 * ℓ ^ 3 * (((2 * Real.pi) ^ 3)⁻¹
          * ∫ q : E3, (chat W q) ^ 2 / ‖q‖ ^ 2) := by
  classical
  set T : ℝ := ∑ k ∈ (Finset.univ : Finset (Lab N)).erase 0,
    (chat W (kmomLab ℓ N k)) ^ 2 / ‖kmomLab ℓ N k‖ ^ 2 with hT
  set c : Lab N → ℝ := fun k => chat W (kmomLab ℓ N k) / ‖kmomLab ℓ N k‖ ^ 2 with hc
  set Φ : E3 → ℝ := fun x => ∑ k ∈ (Finset.univ : Finset (Lab N)).erase 0,
    c k * Real.cos (inner ℝ (kmomLab ℓ N k) x) with hΦ
  set E : ℝ := ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : E3, (chat W q) ^ 2 / ‖q‖ ^ 2 with hE
  -- (0) the momenta of the sum are non-zero
  have hKpos : ∀ k ∈ (Finset.univ : Finset (Lab N)).erase 0, 0 < ‖kmomLab ℓ N k‖ ^ 2 := by
    intro k hk
    have hk0 : k ≠ 0 := (Finset.mem_erase.mp hk).1
    have h1 : (0 : ℝ) < 2 * Real.pi / ℓ := by positivity
    have h2 : 0 < ‖kmomLab ℓ N k‖ := lt_of_lt_of_le h1 (kmomLabNormGe hℓ N k hk0)
    positivity
  have hTnn : 0 ≤ T := by
    rw [hT]
    exact Finset.sum_nonneg fun k _ => div_nonneg (sq_nonneg _) (by positivity)
  have hEnn : 0 ≤ E := by
    rw [hE]
    exact mul_nonneg (by positivity) (integral_nonneg fun q => by positivity)
  -- (1) the pairing `∫ W Φ = T`
  have hA : ∫ x, W x * Φ x = T := by
    rw [hΦ, hT, LatticeW1sqPairing (W := W) hW hWe hℓ N c]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hc]
    have h0 := hKpos k hk
    have h0' : ‖kmomLab ℓ N k‖ ^ 2 ≠ 0 := ne_of_gt h0
    field_simp
  -- (2) the gradient bound `∫_{box} ‖∇Φ‖² ≤ ℓ³ T`
  have hgrad : ∫ x in boxL ℓ, ‖gradient Φ x‖ ^ 2 ≤ ℓ ^ 3 * T := by
    have hcomp : (fun y : E3 => (∑ k ∈ (Finset.univ : Finset (Lab N)).erase 0,
          ((c k : ℂ) * Complex.exp
            (Complex.I * (inner ℝ (kmomLab ℓ N k) y : ℂ)))).re) = Φ := by
      rw [hΦ]
      exact (phi_eq_re (Finset.univ.erase (0 : Lab N)) c).symm
    have hp := LatticeW1sqParsevalRe (ℓ := ℓ) hℓ N (fun k => (c k : ℂ))
    rw [hcomp] at hp
    have hRHS : (∑ k ∈ (Finset.univ : Finset (Lab N)).erase 0,
        ‖kmomLab ℓ N k‖ ^ 2 * ‖((c k : ℝ) : ℂ)‖ ^ 2) = T := by
      rw [hT]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [hc, ← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
      have h0 := hKpos k hk
      field_simp
    rw [hRHS] at hp
    exact hp
  -- (3) the mass bound `∫_{box} Φ² ≤ ℓ³ (ℓ/2π)² T`
  have hmass : ∫ x in boxL ℓ, (Φ x) ^ 2 ≤ ℓ ^ 3 * ((ℓ / (2 * Real.pi)) ^ 2 * T) := by
    have hcomp : (fun x : E3 =>
          ((∑ k ∈ (Finset.univ : Finset (Lab N)).erase 0,
            ((c k : ℝ) : ℂ) • labChar ℓ N k x).re) ^ 2) = fun x => (Φ x) ^ 2 := by
      funext x
      rw [hΦ]
      congr 1
      rw [show (∑ k ∈ (Finset.univ : Finset (Lab N)).erase 0,
            ((c k : ℝ) : ℂ) • labChar ℓ N k x)
          = ∑ k ∈ (Finset.univ : Finset (Lab N)).erase 0,
              ((c k : ℝ) : ℂ) * Complex.exp
                (Complex.I * (inner ℝ (kmomLab ℓ N k) x : ℂ)) by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [smul_eq_mul, labChar_apply]]
      exact (congrFun (phi_eq_re (Finset.univ.erase (0 : Lab N)) c) x).symm
    have hp := GramMassWide (ℓ := ℓ) hℓ (S := (Finset.univ : Finset (Lab N)).erase 0)
      (z := fun k => ((c k : ℝ) : ℂ))
    rw [hcomp] at hp
    have hsum : (∑ k ∈ (Finset.univ : Finset (Lab N)).erase 0,
        ‖((c k : ℝ) : ℂ)‖ ^ 2) ≤ (ℓ / (2 * Real.pi)) ^ 2 * T := by
      rw [hT, Finset.mul_sum]
      refine Finset.sum_le_sum fun k hk => ?_
      have hk0 : k ≠ 0 := (Finset.mem_erase.mp hk).1
      have hb := kmomLabNormGe hℓ N k hk0
      have hK := hKpos k hk
      have h1 : (1 : ℝ) ≤ (ℓ / (2 * Real.pi)) ^ 2 * ‖kmomLab ℓ N k‖ ^ 2 := by
        have hmul : (1 : ℝ) ≤ (ℓ / (2 * Real.pi)) * ‖kmomLab ℓ N k‖ := by
          have h2 := mul_le_mul_of_nonneg_left hb (by positivity : (0:ℝ) ≤ ℓ / (2 * Real.pi))
          have h3 : ℓ / (2 * Real.pi) * (2 * Real.pi / ℓ) = 1 := by field_simp
          linarith [h2, h3]
        have h4 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hmul 2
        rw [mul_pow] at h4
        simpa using h4
      have hle : (1 : ℝ) / ‖kmomLab ℓ N k‖ ^ 2 ≤ (ℓ / (2 * Real.pi)) ^ 2 := by
        rw [div_le_iff₀ hK]
        linarith [h1]
      rw [hc, ← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
      have hnn : 0 ≤ (chat W (kmomLab ℓ N k)) ^ 2 / ‖kmomLab ℓ N k‖ ^ 2 := by positivity
      calc (chat W (kmomLab ℓ N k) / ‖kmomLab ℓ N k‖ ^ 2)
              * (chat W (kmomLab ℓ N k) / ‖kmomLab ℓ N k‖ ^ 2)
          = ((chat W (kmomLab ℓ N k)) ^ 2 / ‖kmomLab ℓ N k‖ ^ 2)
              * (1 / ‖kmomLab ℓ N k‖ ^ 2) := by
            field_simp
        _ ≤ ((chat W (kmomLab ℓ N k)) ^ 2 / ‖kmomLab ℓ N k‖ ^ 2)
              * (ℓ / (2 * Real.pi)) ^ 2 := mul_le_mul_of_nonneg_left hle hnn
        _ = (ℓ / (2 * Real.pi)) ^ 2
              * ((chat W (kmomLab ℓ N k)) ^ 2 / ‖kmomLab ℓ N k‖ ^ 2) := by ring
    calc ∫ x in boxL ℓ, (Φ x) ^ 2
        ≤ ℓ ^ 3 * (∑ k ∈ (Finset.univ : Finset (Lab N)).erase 0, ‖((c k : ℝ) : ℂ)‖ ^ 2) := hp
      _ ≤ ℓ ^ 3 * ((ℓ / (2 * Real.pi)) ^ 2 * T) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
  -- (4) the localisation
  obtain ⟨η, hη1, hη01, hηC2, hηcs, hηloc⟩ := LocaliseGradWideFixed (ℓ := ℓ) (R := R) hℓ hR.le hRℓ
  have hΦper : ∀ (n : Fin 3 → ℤ) (x : E3), Φ (x + lat ℓ n) = Φ x := by
    intro n x
    rw [hΦ]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    rw [inner_add_right, Work.BoseFixR.inner_kmomLab_lat (ne_of_gt hℓ) N k n]
    rw [show inner ℝ (kmomLab ℓ N k) x
          + 2 * Real.pi * ((∑ i, labVec N k i * n i : ℤ) : ℝ)
        = inner ℝ (kmomLab ℓ N k) x
          + ((∑ i, labVec N k i * n i : ℤ) : ℝ) * (2 * Real.pi) by ring]
    exact Real.cos_add_int_mul_two_pi _ _
  have hΦC2 : ContDiff ℝ 2 Φ := by
    rw [hΦ]
    refine ContDiff.sum fun k _ => ?_
    exact ContDiff.mul contDiff_const (Real.contDiff_cos.comp
      (innerSL ℝ (kmomLab ℓ N k)).contDiff)
  set E1 : ℝ := ∫ x, ‖gradient (fun y => η y * Φ y) x‖ ^ 2 with hE1
  have hE1bound : E1 ≤ 4608 * (ℓ ^ 3 * T) := by
    have hloc := hηloc Φ hΦper hΦC2
    rw [hE1]
    have hB : (ℓ ^ 2)⁻¹ * (∫ x in boxL ℓ, (Φ x) ^ 2)
        ≤ (ℓ ^ 2)⁻¹ * (ℓ ^ 3 * ((ℓ / (2 * Real.pi)) ^ 2 * T)) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    have hB2 : (ℓ ^ 2)⁻¹ * (ℓ ^ 3 * ((ℓ / (2 * Real.pi)) ^ 2 * T)) = ℓ ^ 3 * T / (4 * Real.pi ^ 2) := by
      field_simp
      ring
    rw [hB2] at hB
    have hsum2 : (∫ x in boxL ℓ, ‖gradient Φ x‖ ^ 2) + (ℓ ^ 2)⁻¹ * (∫ x in boxL ℓ, (Φ x) ^ 2)
        ≤ ℓ ^ 3 * T + ℓ ^ 3 * T / (4 * Real.pi ^ 2) := add_le_add hgrad hB
    have hfac : (4000 : ℝ) * (ℓ ^ 3 * T + ℓ ^ 3 * T / (4 * Real.pi ^ 2)) ≤ 4608 * (ℓ ^ 3 * T) := by
      have h3 : (0:ℝ) ≤ ℓ ^ 3 * T := by positivity
      have h2 : (1:ℝ) / (4 * Real.pi ^ 2) ≤ 152 / 1000 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [Real.pi_gt_three, Real.pi_pos]
      have h1 : ℓ ^ 3 * T / (4 * Real.pi ^ 2) = (ℓ ^ 3 * T) * (1 / (4 * Real.pi ^ 2)) := by ring
      calc (4000 : ℝ) * (ℓ ^ 3 * T + ℓ ^ 3 * T / (4 * Real.pi ^ 2))
          = 4000 * (ℓ ^ 3 * T) + 4000 * ((ℓ ^ 3 * T) * (1 / (4 * Real.pi ^ 2))) := by
            rw [h1]; ring
        _ ≤ 4000 * (ℓ ^ 3 * T) + 4000 * ((ℓ ^ 3 * T) * (152 / 1000)) :=
            add_le_add le_rfl
              (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 h3) (by norm_num))
        _ ≤ 4608 * (ℓ ^ 3 * T) := by nlinarith [h3]
    linarith [hloc, hsum2, hfac]
  have hE1nn : 0 ≤ E1 := by
    rw [hE1]
    exact integral_nonneg fun x => sq_nonneg _
  -- (5) the free-energy inequality
  have hfree : ∀ t : ℝ, 2 * t * T - t ^ 2 * E1 ≤ E := by
    intro t
    have hψ1 : ContDiff ℝ 1 (fun y : E3 => t * (η y * Φ y)) := by
      have h2 : ContDiff ℝ 2 (fun y : E3 => t * (η y * Φ y)) :=
        contDiff_const.mul (hηC2.mul hΦC2)
      exact h2.of_le (by norm_num)
    have hψcs : HasCompactSupport (fun y : E3 => t * (η y * Φ y)) := by
      have h1 : HasCompactSupport (fun y : E3 => (η y * Φ y) * t) :=
        (hηcs.mul_right (f' := Φ)).mul_right (f' := fun _ : E3 => t)
      simpa [mul_comm] using h1
    have hfe := LatticeW1sqFreeEnergyHint hW hWnn hWe hint hψ1 hψcs
    have hηW : ∀ x : E3, W x * (η x * Φ x) = W x * Φ x := by
      intro x
      by_cases hx : W x = 0
      · rw [hx, zero_mul, zero_mul]
      · have hxmem : x ∈ tsupport W := subset_tsupport W (Function.mem_support.mpr hx)
        have hxR : ‖x‖ < R := by
          have hb := hsupp hxmem
          simpa [Metric.mem_ball, dist_eq_norm] using hb
        rw [hη1 x (le_of_lt hxR)]
        ring
    have h1 : ∫ x, W x * (t * (η x * Φ x)) = t * T := by
      calc ∫ x, W x * (t * (η x * Φ x))
          = t * ∫ x, W x * (η x * Φ x) := by
            rw [← integral_const_mul]
            exact integral_congr_ae (ae_of_all _ fun x => by ring)
        _ = t * ∫ x, W x * Φ x := by rw [integral_congr_ae (ae_of_all _ hηW)]
        _ = t * T := by rw [hA]
    have h2 : ∫ x, ‖gradient (fun y : E3 => t * (η y * Φ y)) x‖ ^ 2 = t ^ 2 * E1 := by
      have hdiff : Differentiable ℝ (fun y : E3 => η y * Φ y) :=
        (hηC2.mul hΦC2).differentiable (by norm_num)
      have hpt : ∀ x : E3, ‖gradient (fun y : E3 => t * (η y * Φ y)) x‖ ^ 2
          = t ^ 2 * ‖gradient (fun y : E3 => η y * Φ y) x‖ ^ 2 := by
        intro x
        have hgradt : gradient (fun y : E3 => t * (η y * Φ y)) x
            = t • gradient (fun y : E3 => η y * Φ y) x := by
          simp only [gradient]
          rw [fderiv_const_mul (hdiff x) t, map_smul]
        rw [hgradt, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul, ← hE1]
    rw [h1, h2] at hfe
    rw [hE]
    linarith [hfe]
  -- (6) `T² ≤ E E₁`
  have hT2 : T ^ 2 ≤ E * E1 := by
    by_cases hT0 : T = 0
    · rw [hT0]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact mul_nonneg hEnn hE1nn
    · rcases eq_or_lt_of_le hE1nn with hE1z | hE1p
      · exfalso
        have hkey : ∀ s : ℝ, 2 * s * T ≤ E := by
          intro s
          have hs := hfree s
          rw [← hE1z] at hs
          simpa using hs
        have h2 : 2 * ((E + 1) / (2 * T)) * T = E + 1 := by
          field_simp
        have h3 := hkey ((E + 1) / (2 * T))
        linarith [h2, h3]
      · have hs := hfree (T / E1)
        have h2 : 2 * (T / E1) * T - (T / E1) ^ 2 * E1 = T ^ 2 / E1 := by
          field_simp
          ring
        have h3 : T ^ 2 / E1 ≤ E := by rw [← h2]; exact hs
        rw [div_le_iff₀ hE1p] at h3
        exact h3
  -- (7) conclude
  have hfin : T ≤ 4608 * ℓ ^ 3 * E := by
    have hstep : T ^ 2 ≤ (4608 * ℓ ^ 3 * E) * T := by
      calc T ^ 2 ≤ E * E1 := hT2
        _ ≤ E * (4608 * (ℓ ^ 3 * T)) := mul_le_mul_of_nonneg_left hE1bound hEnn
        _ = (4608 * ℓ ^ 3 * E) * T := by ring
    by_cases hTle : T ≤ 0
    · have hz : T = 0 := le_antisymm hTle hTnn
      rw [hz]
      exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hℓ.le 3)) hEnn
    · have hpos : 0 < T := not_le.mp hTle
      have hle : T * T ≤ (4608 * ℓ ^ 3 * E) * T := by simpa [pow_two] using hstep
      exact le_of_mul_le_mul_right hle hpos
  exact hfin

/-! ## 3. The honest family -/

lemma ellH_eq_ell {v : E3 → ℝ} {μ : ℝ} (hℓ : 0 < ell v μ) : ellH v μ = ell v μ := by
  show (if 0 < sideAt μ (a v) then sideAt μ (a v) else 1) = sideAt μ (a v)
  rw [if_pos (show 0 < sideAt μ (a v) from hℓ)]

lemma honestF_kmom {v : E3 → ℝ} (h : ScatSol v) (fc fu : LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) :
    (HonestBoxFam v h fc fu HM μ).F.kmom = kmomLab (ellH v μ) (HM μ).N := rfl

lemma honestPHset_subset {v : E3 → ℝ} (h : ScatSol v) (fc fu : LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) :
    (HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E
      ⊆ (Finset.univ : Finset (Lab (HM μ).N)).erase 0 := by
  intro k hk
  rw [FockData.PHset, Finset.mem_filter] at hk
  exact hk.1

lemma honestE_W1 {v : E3 → ℝ} (h : ScatSol v) (fc fu : LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) {μ : ℝ} (hℓ : 0 < ell v μ) (k : Lab (HM μ).N) :
    (HonestBoxFam v h fc fu HM μ).E.W1 k
      = uvCut fu (uvRad (ell v μ) (HM μ).N) (kmomLab (ell v μ) (HM μ).N k)
        * chat (W1fun v h (ell v μ)) (kmomLab (ell v μ) (HM μ).N k) := by
  have hkm : (HonestBoxFam v h fc fu HM μ).F.kmom = kmomLab (ellH v μ) (HM μ).N := rfl
  have hE : (HonestBoxFam v h fc fu HM μ).E.W1 k
      = uvCut fu (uvRad (sideAt μ (a v)) (HM μ).N)
          ((HonestBoxFam v h fc fu HM μ).F.kmom k)
        * chat (W1fun v h (sideAt μ (a v))) ((HonestBoxFam v h fc fu HM μ).F.kmom k) := rfl
  rw [hE, hkm, ellH_eq_ell (v := v) hℓ]
  rfl

/-- **The wide ℓ²-row of `Ŵ₁` at the honest family.** -/
theorem FarRowW1sqWide {v : E3 → ℝ} (h : ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < a v) (fc fu : LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ)
    {ε₀ μ : ℝ} (hε₀ : ε₀ ≤ 10 ^ (-(4000 : ℤ)))
    (hAdm : Work.BoseBoxFix.Adm v ε₀ μ)
    (hview : (HonestBoxFam v h fc fu HM μ).viewFSAll v h μ)
    (hRℓ : R ≤ ell v μ * Submission.BoseGases.chiR0) :
    ∑ k ∈ (HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E,
        (HonestBoxFam v h fc fu HM μ).E.W1 k ^ 2
          / ‖(HonestBoxFam v h fc fu HM μ).F.kmom k‖ ^ 2
      ≤ 10 ^ 6 * a v * (ell v μ) ^ 3 := by
  classical
  have hℓ : 0 < ell v μ :=
    pos_of_mul_pos_left (lt_of_lt_of_le hR hRℓ) (le_of_lt Submission.BoseGases.chiR0_pos)
  have hRle : R ≤ ell v μ := by
    have h1 : R ≤ ell v μ * Submission.BoseGases.chiR0 := hRℓ
    have h2 : Submission.BoseGases.chiR0 ≤ 1 := Work.BoseFixR.Rb5Lin.chiR0_le_one
    calc R ≤ ell v μ * Submission.BoseGases.chiR0 := h1
      _ ≤ ell v μ * 1 := mul_le_mul_of_nonneg_left h2 hℓ.le
      _ = ell v μ := by ring
  have hWi : MeasureTheory.Integrable (W1fun v h (ell v μ)) := by
    rw [W1fun_eq_wScaled]
    exact Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ hRℓ
  have hWnn : 0 ≤ᵐ[(MeasureTheory.volume : MeasureTheory.Measure E3)] W1fun v h (ell v μ) := by
    rw [W1fun_eq_wScaled]
    exact Submission.BoseGases.wScaled_g0_nonneg_ae (v := v) (R := R) (ℓ := ell v μ)
      hR hv hvrad hv_supp h
  have hrow := latticeRowCore (W := W1fun v h (ell v μ)) (R := R) (ℓ := ell v μ)
    hR hℓ hWi hWnn (isEven_W1fun h hvrad (ell v μ))
    (tsupport_W1fun_subset h hv_supp (ell v μ)) hRle
    (IntegrableChatW1sq (v := v) h hv hvrad hR hℓ hv_supp hRℓ) (HM μ).N
  -- the mass bound for `E`
  have hEmass : ((2 * Real.pi) ^ 3)⁻¹
      * (∫ q : E3, (chat (W1fun v h (ell v μ)) q) ^ 2 / ‖q‖ ^ 2)
      ≤ 64 * Real.pi * a v := by
    have h1 := mass_le_W1omega2 (v := v) h hv hvrad hR hv_supp hRℓ hℓ hWi
    have h2 := W1omegaMassLe (v := v) h hv hvrad hR hℓ hv_supp hRℓ
    have hsplit : (∫ q : E3, (chat (W1fun v h (ell v μ)) q) ^ 2 / ‖q‖ ^ 2)
        = 2 * (∫ q : E3, (chat (W1fun v h (ell v μ)) q) ^ 2 / (2 * ‖q‖ ^ 2)) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun q => by ring)
    rw [hsplit, show ((2 * Real.pi) ^ 3)⁻¹
        * (2 * ∫ q : E3, (chat (W1fun v h (ell v μ)) q) ^ 2 / (2 * ‖q‖ ^ 2))
        = 2 * (((2 * Real.pi) ^ 3)⁻¹
            * ∫ q : E3, (chat (W1fun v h (ell v μ)) q) ^ 2 / (2 * ‖q‖ ^ 2)) by ring]
    linarith [h1, h2]
  have hT : (∑ k ∈ (Finset.univ : Finset (Lab (HM μ).N)).erase 0,
      (chat (W1fun v h (ell v μ)) (kmomLab (ell v μ) (HM μ).N k)) ^ 2
        / ‖kmomLab (ell v μ) (HM μ).N k‖ ^ 2) ≤ 10 ^ 6 * a v * (ell v μ) ^ 3 := by
    have h1 : 4608 * (ell v μ) ^ 3
        * (((2 * Real.pi) ^ 3)⁻¹
            * ∫ q : E3, (chat (W1fun v h (ell v μ)) q) ^ 2 / ‖q‖ ^ 2)
        ≤ 4608 * (ell v μ) ^ 3 * (64 * Real.pi * a v) :=
      mul_le_mul_of_nonneg_left hEmass (by positivity)
    have h2 : 4608 * (ell v μ) ^ 3 * (64 * Real.pi * a v)
        ≤ 10 ^ 6 * a v * (ell v μ) ^ 3 := by
      have ha : 0 ≤ a v := hav.le
      have hl : 0 ≤ (ell v μ) ^ 3 := pow_nonneg hℓ.le 3
      have hp : (294912 : ℝ) * Real.pi ≤ 10 ^ 6 := by
        have hπ : Real.pi ≤ 3.15 := le_of_lt Real.pi_lt_d2
        nlinarith [hπ]
      calc 4608 * (ell v μ) ^ 3 * (64 * Real.pi * a v)
          = ((294912 : ℝ) * Real.pi) * (a v * (ell v μ) ^ 3) := by ring
        _ ≤ 10 ^ 6 * (a v * (ell v μ) ^ 3) :=
            mul_le_mul_of_nonneg_right hp (mul_nonneg ha hl)
        _ = 10 ^ 6 * a v * (ell v μ) ^ 3 := by ring
    linarith [hrow, h1, h2]
  -- the `P_H` bookkeeping
  have hpt : ∀ k ∈ (HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E,
      (HonestBoxFam v h fc fu HM μ).E.W1 k ^ 2
          / ‖(HonestBoxFam v h fc fu HM μ).F.kmom k‖ ^ 2
        ≤ (chat (W1fun v h (ell v μ)) (kmomLab (ell v μ) (HM μ).N k)) ^ 2
            / ‖kmomLab (ell v μ) (HM μ).N k‖ ^ 2 := by
    intro k _
    rw [honestE_W1 h fc fu HM hℓ k, honestF_kmom h fc fu HM μ,
      ellH_eq_ell (v := v) hℓ]
    have hle1 : uvCut fu (uvRad (ell v μ) (HM μ).N) (kmomLab (ell v μ) (HM μ).N k) ≤ 1 :=
      fu.le_one _
    have hle0 : 0 ≤ uvCut fu (uvRad (ell v μ) (HM μ).N) (kmomLab (ell v μ) (HM μ).N k) :=
      fu.nonneg _
    have hsq : (uvCut fu (uvRad (ell v μ) (HM μ).N)
        (kmomLab (ell v μ) (HM μ).N k)) ^ 2 ≤ 1 := by nlinarith
    calc (uvCut fu (uvRad (ell v μ) (HM μ).N) (kmomLab (ell v μ) (HM μ).N k)
            * chat (W1fun v h (ell v μ)) (kmomLab (ell v μ) (HM μ).N k)) ^ 2
            / ‖kmomLab (ell v μ) (HM μ).N k‖ ^ 2
        = (uvCut fu (uvRad (ell v μ) (HM μ).N) (kmomLab (ell v μ) (HM μ).N k)) ^ 2
            * (chat (W1fun v h (ell v μ)) (kmomLab (ell v μ) (HM μ).N k)) ^ 2
            / ‖kmomLab (ell v μ) (HM μ).N k‖ ^ 2 := by ring
      _ ≤ 1 * (chat (W1fun v h (ell v μ)) (kmomLab (ell v μ) (HM μ).N k)) ^ 2
            / ‖kmomLab (ell v μ) (HM μ).N k‖ ^ 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hsq (sq_nonneg _))
            (sq_nonneg _)
      _ = _ := by ring
  refine le_trans (Finset.sum_le_sum hpt) ?_
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (honestPHset_subset h fc fu HM μ)
    (fun k _ _ => div_nonneg (sq_nonneg _) (sq_nonneg _))) ?_
  exact hT

end Work.BoseFixR.All
