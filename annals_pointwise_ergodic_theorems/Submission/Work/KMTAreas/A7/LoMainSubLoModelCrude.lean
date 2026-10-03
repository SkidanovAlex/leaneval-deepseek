import Mathlib
import Submission.Work.KMTAreas.A7.LoDefs
import Submission.Work.KMTAreas.A7.BilinOpLp
import Submission.Work.KMTAreas.A7.eLpNorm_lintegral_le
import Submission.Work.KMTAreas.A7rand.eLpNorm_iwConv_le_kernelMass
import Submission.Work.KMTAreas.A7.kernelMass_of_modulatedBump
import Submission.Work.KMTAreas.A7.kmtEta_deriv_bounds
import Submission.Work.KMTAreas.tsum_one_div_sq_succ_le_two
import Submission.Port.Aesm

set_option autoImplicit false

namespace Work.KMTAreas.A7

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators FourierTransform
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier Work.Analysis.EndVar Work.KMTContract
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems

noncomputable section

/-! ## §1 The level-0 arithmetic frequency set -/

lemma iwP_zero (ρ : ℝ) : iwP ρ 0 = {1} := by
  unfold iwP
  rw [if_pos (Nat.zero_le (iwC0 ρ))]
  norm_num

lemma iwArithFreqs_zero (ρ : ℝ) : iwArithFreqs ρ 0 = {0} := by
  unfold iwArithFreqs
  rw [iwP_zero]
  ext α
  simp

/-! ## §2 The kernel mass of a compressed bump profile -/

/-- The constant of the kernel-mass bound for a bump with profile mass `A₀` and second-derivative
mass `B₀`. -/
noncomputable def massC (A₀ B₀ : ℝ) : ℝ :=
  4 * (A₀ + 1) + 2 * Real.pi * Real.sqrt ((A₀ + 1) * (B₀ / (4 * Real.pi ^ 2) + 1))

lemma massC_pos {A₀ B₀ : ℝ} (hA : 0 ≤ A₀) (_hB : 0 ≤ B₀) : 0 < massC A₀ B₀ := by
  unfold massC
  have h1 : 0 < 4 * (A₀ + 1) := by linarith
  have h2 : 0 ≤ 2 * Real.pi * Real.sqrt ((A₀ + 1) * (B₀ / (4 * Real.pi ^ 2) + 1)) :=
    mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (Real.sqrt_nonneg _)
  linarith

/-- **The `ℓ¹` mass of the kernel of the level-`0` IW multiplier with compressed bump profile.**
For a profile `ψ` of compact support the convolution kernel of `Tle ρ 0 (ψ (a·) e(c·))` has `ℓ¹`
mass bounded by `massC A₀ B₀`, uniformly in `ρ`, in `a ≥ 1` and in the modulation `c`. -/
lemma kernelMass_scaled (ρ c a A₀ B₀ : ℝ) (φ : ℝ → ℂ) (hφcd : ContDiff ℝ 2 φ)
    (hφcs : HasCompactSupport φ) (ha : 1 ≤ a) (hA₀ : 0 ≤ A₀) (hB₀ : 0 ≤ B₀)
    (h1 : (∫ y : ℝ, ‖φ y‖) ≤ A₀ / a) (h2 : (∫ y : ℝ, ‖iteratedDeriv 2 φ y‖) ≤ B₀ * a) :
    Summable (fun j : ℤ => ‖iwKernel (iwSymbolSet (iwArithFreqs ρ 0)
        (periodize (fun y : ℝ => φ y * ee (c * y)))) j‖) ∧
    (∑' j : ℤ, ‖iwKernel (iwSymbolSet (iwArithFreqs ρ 0)
        (periodize (fun y : ℝ => φ y * ee (c * y)))) j‖) ≤ massC A₀ B₀ := by
  obtain ⟨hsumm, hbound⟩ := kernelMass_of_modulatedBump (iwArithFreqs ρ 0) φ c a A₀ B₀
    hφcd hφcs ha hA₀ hB₀ h1 h2
  refine ⟨hsumm, ?_⟩
  have heq : 4 * ((iwArithFreqs ρ 0).card * A₀ + 1)
      + 2 * Real.pi * Real.sqrt (((iwArithFreqs ρ 0).card * A₀ + 1)
          * ((iwArithFreqs ρ 0).card * B₀ / (4 * Real.pi ^ 2) + 1)) = massC A₀ B₀ := by
    rw [iwArithFreqs_zero, Finset.card_singleton, Nat.cast_one]
    simp [massC]
  exact hbound.trans (le_of_eq heq)

/-- Young's inequality for the level-`0` IW multiplier, from an `ℓ¹` mass bound on its kernel. -/
lemma eLpNorm_Tle_zero_of_mass (ρ : ℝ) (p : ENNReal) (hp : 1 < p) (φ : ℝ → ℂ) (C : ℝ)
    (hsumm : Summable (fun j : ℤ => ‖iwKernel (iwSymbolSet (iwArithFreqs ρ 0)
      (periodize φ)) j‖))
    (hmass : (∑' j : ℤ, ‖iwKernel (iwSymbolSet (iwArithFreqs ρ 0) (periodize φ)) j‖) ≤ C)
    (u : ℤ → ℂ) :
    eLpNorm (Tle ρ 0 φ u) p Measure.count ≤ ENNReal.ofReal C * eLpNorm u p Measure.count := by
  have hkey : Tle ρ 0 φ u = iwConv (iwArithFreqs ρ 0) (periodize φ) u := rfl
  rw [hkey]
  refine (Work.KMTAreas.A7rand.eLpNorm_iwConv_le_kernelMass (A := iwArithFreqs ρ 0)
    (Φ := periodize φ) (q := p) (le_of_lt hp) u).trans ?_
  have hof : (∑' j : ℤ, ENNReal.ofReal ‖iwKernel (iwSymbolSet (iwArithFreqs ρ 0)
        (periodize φ)) j‖)
      = ENNReal.ofReal (∑' j : ℤ, ‖iwKernel (iwSymbolSet (iwArithFreqs ρ 0)
        (periodize φ)) j‖) :=
    (ENNReal.ofReal_tsum_of_nonneg (fun j => norm_nonneg _) hsumm).symm
  rw [hof]
  exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hmass) zero_le

/-- **The `ℓᵖ` single-scale bound for a compressed bump profile.** -/
lemma eLpNorm_Tle_zero_comp (p : ENNReal) (hp : 1 < p)
    (ψ : ℝ → ℂ) (hψcd : ContDiff ℝ 2 ψ) (hψzero : ∀ y : ℝ, 1 ≤ |y| → ψ y = 0)
    (A₀ B₀ : ℝ) (hA₀ : 0 ≤ A₀) (hB₀ : 0 ≤ B₀)
    (hI : (∫ y : ℝ, ‖ψ y‖) ≤ A₀) (hI2 : (∫ y : ℝ, ‖iteratedDeriv 2 ψ y‖) ≤ B₀) :
    ∀ (ρ a c : ℝ), 1 ≤ a → ∀ (u : ℤ → ℂ),
      eLpNorm (Tle ρ 0 (fun y : ℝ => ψ (a * y) * ee (c * y)) u) p Measure.count
        ≤ ENNReal.ofReal (massC A₀ B₀) * eLpNorm u p Measure.count := by
  intro ρ a c ha u
  have hapos : 0 < a := lt_of_lt_of_le zero_lt_one ha
  set φ : ℝ → ℂ := fun y => ψ (a * y) with hφ
  have hφcd : ContDiff ℝ 2 φ := hψcd.comp (contDiff_const.mul contDiff_id)
  have hφcs : HasCompactSupport φ := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := Set.Icc (-(1 / a)) (1 / a)) isCompact_Icc ?_
    intro y hy
    have hne : φ y ≠ 0 := hy
    have hlt : ¬ (1 ≤ |a * y|) := fun hc => hne (hψzero _ hc)
    rw [not_le, abs_mul, abs_of_pos hapos] at hlt
    have hlt' : |y| < 1 / a := by
      rw [lt_div_iff₀ hapos]
      linarith [hlt]
    obtain ⟨h1, h2⟩ := abs_lt.mp hlt'
    exact Set.mem_Icc.mpr ⟨h1.le, h2.le⟩
  have hm1 : (∫ y : ℝ, ‖φ y‖) ≤ A₀ / a := by
    have heq : (∫ y : ℝ, ‖φ y‖) = a⁻¹ * (∫ y : ℝ, ‖ψ y‖) :=
      integral_norm_comp_mul_left_varphiN ψ hapos
    rw [heq, div_eq_mul_inv, mul_comm A₀ a⁻¹]
    exact mul_le_mul_of_nonneg_left hI (inv_nonneg.mpr hapos.le)
  have hm2 : (∫ y : ℝ, ‖iteratedDeriv 2 φ y‖) ≤ B₀ * a := by
    have hpt : ∀ y : ℝ, ‖iteratedDeriv 2 φ y‖ = a ^ 2 * ‖iteratedDeriv 2 ψ (a * y)‖ := by
      intro y
      rw [iteratedDeriv_two_comp_mul_left_varphiN ψ hψcd a y, norm_smul,
        Real.norm_of_nonneg (sq_nonneg a)]
    calc (∫ y : ℝ, ‖iteratedDeriv 2 φ y‖)
        = ∫ y : ℝ, a ^ 2 * ‖iteratedDeriv 2 ψ (a * y)‖ := by
          rw [show (fun y : ℝ => ‖iteratedDeriv 2 φ y‖)
            = fun y : ℝ => a ^ 2 * ‖iteratedDeriv 2 ψ (a * y)‖ from funext hpt]
      _ = a ^ 2 * (∫ y : ℝ, ‖iteratedDeriv 2 ψ (a * y)‖) :=
          integral_const_mul (a ^ 2) _
      _ = a ^ 2 * (a⁻¹ * (∫ y : ℝ, ‖iteratedDeriv 2 ψ y‖)) := by
          rw [integral_norm_comp_mul_left_varphiN (iteratedDeriv 2 ψ) hapos]
      _ ≤ a ^ 2 * (a⁻¹ * B₀) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hI2 (inv_nonneg.mpr hapos.le)) (sq_nonneg a)
      _ = B₀ * a := by
          field_simp
  obtain ⟨hsumm, hmass⟩ := kernelMass_scaled ρ c a A₀ B₀ φ hφcd hφcs ha hA₀ hB₀ hm1 hm2
  exact eLpNorm_Tle_zero_of_mass ρ p hp (fun y => φ y * ee (c * y)) (massC A₀ B₀) hsumm hmass u




/-! ## §4a The level-`0` projection `Tle ρ 0 (η_{≤k})` for `k ≤ 0` -/

lemma eLpNorm_Tle_etaCut_neg (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : ℝ) (k : ℤ), k ≤ 0 → ∀ (u : ℤ → ℂ),
      eLpNorm (Tle ρ 0 (etaCut Work.KMTContract.kmtEta k) u) p Measure.count
        ≤ ENNReal.ofReal C * eLpNorm u p Measure.count := by
  set A₀ : ℝ := ∫ y : ℝ, ‖Work.KMTContract.kmtEta y‖ with hA₀def
  set B₀ : ℝ := ∫ y : ℝ, ‖iteratedDeriv 2 Work.KMTContract.kmtEta y‖ with hB₀def
  have hA₀ : 0 ≤ A₀ := by rw [hA₀def]; exact integral_nonneg (fun y => norm_nonneg _)
  have hB₀ : 0 ≤ B₀ := by rw [hB₀def]; exact integral_nonneg (fun y => norm_nonneg _)
  refine ⟨massC A₀ B₀, massC_pos hA₀ hB₀, fun ρ k hk u => ?_⟩
  have ha1 : 1 ≤ (2 : ℝ) ^ (-k) := by
    have h0 : (0 : ℤ) ≤ -k := by omega
    calc (1 : ℝ) = (2 : ℝ) ^ (0 : ℤ) := by simp
      _ ≤ (2 : ℝ) ^ (-k) := zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) h0
  have hcomp := eLpNorm_Tle_zero_comp p hp Work.KMTContract.kmtEta (contDiff_kmtEta 2)
    (fun y hy => Work.KMTContract.kmtEta_zero hy) A₀ B₀ hA₀ hB₀ (le_of_eq hA₀def.symm)
      (le_of_eq hB₀def.symm) ρ ((2 : ℝ) ^ (-k)) 0 ha1 u
  have hfun : (fun y : ℝ => Work.KMTContract.kmtEta (((2 : ℝ) ^ (-k)) * y) * ee ((0:ℝ) * y))
      = etaCut Work.KMTContract.kmtEta k := by
    funext y
    rw [etaCut]
    have hz : ((2 : ℝ) ^ (-k)) * y = y / (2 : ℝ) ^ k := by
      rw [zpow_neg, inv_mul_eq_div]
    rw [hz]
    simp [ee]
  rw [hfun] at hcomp
  exact hcomp

/-! ## §4b The modulated bump `φ_{N,t}` -/

lemma eLpNorm_Tle_varphiNt (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : ℝ) (N k₁ : ℕ), 2 ^ k₁ ≤ N → ∀ (t : ℝ),
      t ∈ Set.Icc (1/2 : ℝ) 1 → ∀ (f : ℤ → ℂ),
      eLpNorm (Tle ρ 0 (varphiNt N k₁ t) f) p Measure.count
        ≤ ENNReal.ofReal C * eLpNorm f p Measure.count := by
  obtain ⟨C₁, hC₁, hb⟩ := Tle_varphiNt_single_scale 1 (by norm_num) 0 p hp hptop
  refine ⟨(C₁ : ℝ), by exact_mod_cast hC₁, fun ρ N k₁ hN t ht f => ?_⟩
  have hρ0 : iwArithFreqs ρ 0 = iwArithFreqs 1 0 := by rw [iwArithFreqs_zero, iwArithFreqs_zero]
  have hT : Tle ρ 0 (varphiNt N k₁ t) = Tle 1 0 (varphiNt N k₁ t) := by
    show iwConv (iwArithFreqs ρ 0) (periodize (varphiNt N k₁ t))
      = iwConv (iwArithFreqs 1 0) (periodize (varphiNt N k₁ t))
    rw [hρ0]
  rw [hT]
  exact hb N k₁ hN t ht f




/-! ## §4c The modulated bump `φ̃_{N,t}` -/

lemma eLpNorm_Tle_varphitildeNt (P : Polynomial ℤ) (d : ℕ) (p : ENNReal) (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : ℝ) (N k₂ : ℕ), 2 ^ k₂ ≤ N → ∀ (t : ℝ) (g : ℤ → ℂ),
      eLpNorm (Tle ρ 0 (varphitildeNt P d N k₂ t) g) p Measure.count
        ≤ ENNReal.ofReal C * eLpNorm g p Measure.count := by
  set A : ℝ := ∫ y : ℝ, ‖Work.KMTContract.kmtEta y‖ with hA
  set B : ℝ := ∫ y : ℝ, ‖iteratedDeriv 2 Work.KMTContract.kmtEta y‖ with hB
  have hA0 : 0 ≤ A := by rw [hA]; exact integral_nonneg (fun y => norm_nonneg _)
  have hB0 : 0 ≤ B := by rw [hB]; exact integral_nonneg (fun y => norm_nonneg _)
  set ρd : ℝ := (2 : ℝ) ^ (d : ℝ) with hρd
  have hρd1 : 1 ≤ ρd := by
    rw [hρd]; exact Real.one_le_rpow (by norm_num) (by positivity)
  have hρd0 : 0 < ρd := lt_of_lt_of_le zero_lt_one hρd1
  set A₀ : ℝ := 2 * A with hA₀def
  set B₀ : ℝ := (1 + ρd) * B with hB₀def
  have hA₀ : 0 ≤ A₀ := by rw [hA₀def]; linarith
  have hB₀ : 0 ≤ B₀ := by rw [hB₀def]; nlinarith [hρd1, hB0]
  refine ⟨massC A₀ B₀, massC_pos hA₀ hB₀, fun ρ N k₂ hNk t g => ?_⟩
  have hkL : (k₂ : ℝ) ≤ (Work.Analysis.EndVar.logN N : ℝ) := by
    have h1 : 2 ^ k₂ ≤ max N 2 := le_trans hNk (le_max_left _ _)
    have h2 : k₂ ≤ Nat.log 2 (max N 2) := Nat.le_log_of_pow_le (by norm_num) h1
    have h3 : (Nat.log 2 (max N 2) : ℝ) = (Work.Analysis.EndVar.logN N : ℝ) := by
      simp only [Work.Analysis.EndVar.logN, Int.cast_natCast]
    calc (k₂ : ℝ) ≤ (Nat.log 2 (max N 2) : ℝ) := by exact_mod_cast h2
      _ = (Work.Analysis.EndVar.logN N : ℝ) := h3
  set a₂ : ℝ := (2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k₂ : ℝ))) with ha₂
  set c₂ : ℝ := PevalR P ((N : ℝ) * t) with hc₂
  have ha₂1 : 1 ≤ a₂ := by
    rw [ha₂]
    refine Real.one_le_rpow (by norm_num) ?_
    have h : (0 : ℝ) ≤ (Work.Analysis.EndVar.logN N : ℝ) - (k₂ : ℝ) := by linarith
    positivity
  rcases eq_or_ne k₂ 0 with hk0 | hk0
  · subst hk0
    -- the bottom scale `k₂ = 0`: the profile is `η` itself
    have hval : varphitildeN d N 0 = fun ξ : ℝ => Work.KMTContract.kmtEta (a₂ * ξ) := by
      funext ξ
      simp only [varphitildeN, reduceIte, ha₂, Nat.cast_zero, sub_zero]
    have hvt : varphitildeNt P d N 0 t
        = fun y : ℝ => Work.KMTContract.kmtEta (a₂ * y) * ee (c₂ * y) := by
      funext y
      simp only [varphitildeNt, hval, hc₂]
    rw [hvt]
    exact eLpNorm_Tle_zero_comp p hp Work.KMTContract.kmtEta (contDiff_kmtEta 2)
      (fun y hy => Work.KMTContract.kmtEta_zero hy) A₀ B₀ hA₀ hB₀
      (by rw [hA₀def, hA]; linarith [hA0])
      (by rw [hB₀def, hB]; nlinarith [hρd1, hB0])
      ρ a₂ c₂ ha₂1 g
  · -- the interior scales: the profile is `η - η(ρ·)` with `ρ = 2^d`
    set ψ : ℝ → ℂ := fun y : ℝ => Work.KMTContract.kmtEta y
      - Work.KMTContract.kmtEta (ρd * y) with hψ
    have hψcd : ContDiff ℝ 2 ψ := by
      rw [hψ]
      exact (contDiff_kmtEta 2).sub ((contDiff_kmtEta 2).comp (contDiff_const.mul contDiff_id))
    have hψzero : ∀ y : ℝ, 1 ≤ |y| → ψ y = 0 := by
      intro y hy
      rw [hψ]
      simp only [Pi.sub_apply]
      have hdy : 1 ≤ |ρd * y| := by
        rw [abs_mul, abs_of_pos hρd0]
        nlinarith [hρd1, abs_nonneg y]
      rw [Work.KMTContract.kmtEta_zero hy, Work.KMTContract.kmtEta_zero hdy, sub_zero]
    have hψcs : HasCompactSupport ψ := by
      refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-1:ℝ) 1) isCompact_Icc ?_
      intro x hx
      have h : ¬ (1 ≤ |x|) := fun hc => hx (hψzero x hc)
      rw [not_le] at h
      obtain ⟨h1, h2⟩ := abs_lt.mp h
      exact Set.mem_Icc.mpr ⟨h1.le, h2.le⟩
    have hψint : Integrable ψ := hψcd.continuous.integrable_of_hasCompactSupport hψcs
    have hint1 : Integrable (fun y : ℝ => ‖Work.KMTContract.kmtEta y‖) :=
      integrable_kmtEta_varphiN.norm
    have hint2 : Integrable (fun y : ℝ => ‖Work.KMTContract.kmtEta (ρd * y)‖) :=
      integrable_kmtEta_varphiN.norm.comp_mul_left' (ne_of_gt hρd0)
    have hJval : (∫ y : ℝ, ‖Work.KMTContract.kmtEta (ρd * y)‖) = ρd⁻¹ * A := by
      rw [integral_norm_comp_mul_left_varphiN Work.KMTContract.kmtEta hρd0, hA]
    have hI : (∫ y : ℝ, ‖ψ y‖) ≤ A₀ := by
      have hpt : ∀ y : ℝ, ‖ψ y‖ ≤ ‖Work.KMTContract.kmtEta y‖
          + ‖Work.KMTContract.kmtEta (ρd * y)‖ := by
        intro y; rw [hψ]; simp only [Pi.sub_apply]; exact norm_sub_le _ _
      calc (∫ y : ℝ, ‖ψ y‖)
          ≤ ∫ y : ℝ, (‖Work.KMTContract.kmtEta y‖ + ‖Work.KMTContract.kmtEta (ρd * y)‖) :=
            integral_mono hψint.norm (hint1.add hint2) hpt
        _ = (∫ y : ℝ, ‖Work.KMTContract.kmtEta y‖)
              + (∫ y : ℝ, ‖Work.KMTContract.kmtEta (ρd * y)‖) := integral_add hint1 hint2
        _ = A + ρd⁻¹ * A := by rw [hJval, hA]
        _ ≤ A₀ := by
            rw [hA₀def]
            have h1 : ρd⁻¹ * A ≤ A := by
              rw [inv_mul_le_iff₀ hρd0]
              nlinarith [hA0]
            linarith
    have hint1d : Integrable (fun y : ℝ => ‖iteratedDeriv 2 Work.KMTContract.kmtEta y‖) :=
      integrable_iteratedDeriv_two_kmtEta_varphiN
    have hint2d : Integrable (fun y : ℝ => ‖iteratedDeriv 2 Work.KMTContract.kmtEta (ρd * y)‖) :=
      integrable_iteratedDeriv_two_kmtEta_varphiN.comp_mul_left' (ne_of_gt hρd0)
    have hI2 : (∫ y : ℝ, ‖iteratedDeriv 2 ψ y‖) ≤ B₀ := by
      have hchain : ∀ y : ℝ,
          iteratedDeriv 2 (fun z : ℝ => Work.KMTContract.kmtEta (ρd * z)) y
            = (ρd ^ 2 : ℝ) • iteratedDeriv 2 Work.KMTContract.kmtEta (ρd * y) := by
        intro y
        exact iteratedDeriv_two_comp_mul_left_varphiN Work.KMTContract.kmtEta
          (contDiff_kmtEta 2) ρd y
      have hpt : ∀ y : ℝ, ‖iteratedDeriv 2 ψ y‖ ≤ ‖iteratedDeriv 2 Work.KMTContract.kmtEta y‖
          + ρd ^ 2 * ‖iteratedDeriv 2 Work.KMTContract.kmtEta (ρd * y)‖ := by
        intro y
        have hsub : iteratedDeriv 2 ψ y
            = iteratedDeriv 2 Work.KMTContract.kmtEta y
              - iteratedDeriv 2 (fun z : ℝ => Work.KMTContract.kmtEta (ρd * z)) y := by
          rw [hψ]
          exact iteratedDeriv_sub (contDiff_kmtEta 2).contDiffAt
            (((contDiff_kmtEta 2).comp (contDiff_const.mul contDiff_id)).contDiffAt)
        rw [hsub]
        calc ‖iteratedDeriv 2 Work.KMTContract.kmtEta y
              - iteratedDeriv 2 (fun z : ℝ => Work.KMTContract.kmtEta (ρd * z)) y‖
            ≤ ‖iteratedDeriv 2 Work.KMTContract.kmtEta y‖
              + ‖iteratedDeriv 2 (fun z : ℝ => Work.KMTContract.kmtEta (ρd * z)) y‖ :=
              norm_sub_le _ _
          _ = ‖iteratedDeriv 2 Work.KMTContract.kmtEta y‖
              + ρd ^ 2 * ‖iteratedDeriv 2 Work.KMTContract.kmtEta (ρd * y)‖ := by
              rw [hchain y, norm_smul, Real.norm_of_nonneg (sq_nonneg ρd), mul_comm]
      have hψdint : Integrable (fun y : ℝ => ‖iteratedDeriv 2 ψ y‖) := by
        have hcs2 : HasCompactSupport (iteratedDeriv 2 ψ) := by
          rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
          exact hψcs.deriv.deriv
        exact ((hψcd.continuous_iteratedDeriv 2 (by norm_num)).integrable_of_hasCompactSupport
          hcs2).norm
      calc (∫ y : ℝ, ‖iteratedDeriv 2 ψ y‖)
          ≤ ∫ y : ℝ, (‖iteratedDeriv 2 Work.KMTContract.kmtEta y‖
              + ρd ^ 2 * ‖iteratedDeriv 2 Work.KMTContract.kmtEta (ρd * y)‖) :=
            integral_mono hψdint (hint1d.add (hint2d.const_mul _)) hpt
        _ = (∫ y : ℝ, ‖iteratedDeriv 2 Work.KMTContract.kmtEta y‖)
              + ρd ^ 2 * (∫ y : ℝ, ‖iteratedDeriv 2 Work.KMTContract.kmtEta (ρd * y)‖) := by
            rw [integral_add hint1d (hint2d.const_mul _), integral_const_mul]
        _ = B + ρd ^ 2 * (ρd⁻¹ * B) := by
            rw [integral_norm_comp_mul_left_varphiN (iteratedDeriv 2 Work.KMTContract.kmtEta)
              hρd0, hB]
        _ ≤ B₀ := by
            rw [hB₀def, hρd]
            have hsq : (2 : ℝ) ^ (d : ℝ) * ((2 : ℝ) ^ (d : ℝ) * ((2 : ℝ) ^ (d : ℝ))⁻¹ * B)
                = (2 : ℝ) ^ (d : ℝ) * B := by
              rw [mul_inv_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)), one_mul]
            nlinarith [hB0, Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) (d:ℝ)]
    have ha₂val : (2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k₂ : ℝ) + 1))
        = a₂ * ρd := by
      rw [ha₂, hρd]
      rw [show (d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k₂ : ℝ) + 1)
          = (d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k₂ : ℝ)) + (d : ℝ) by ring]
      rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    have hval : varphitildeN d N k₂ = fun ξ : ℝ => ψ (a₂ * ξ) := by
      funext ξ
      simp only [varphitildeN, if_neg hk0, hψ]
      rw [ha₂val, ha₂]
      ring_nf
    have hvt : varphitildeNt P d N k₂ t = fun y : ℝ => ψ (a₂ * y) * ee (c₂ * y) := by
      funext y
      simp only [varphitildeNt, hval, hc₂]
    rw [hvt]
    exact eLpNorm_Tle_zero_comp p hp ψ hψcd hψzero A₀ B₀ hA₀ hB₀ hI hI2 ρ a₂ c₂ ha₂1 g


/-! ## The vanishing of the tuples at a zero argument -/

lemma Ablock_zero_left_aux (m : ℕ) (P : Polynomial ℤ) (g : ℤ → ℂ) (x : ℤ) :
    Ablock TZ m X P 0 g x = 0 := by
  simp [Ablock]

lemma Ablock_zero_right_aux (m : ℕ) (P : Polynomial ℤ) (f : ℤ → ℂ) (x : ℤ) :
    Ablock TZ m X P f 0 x = 0 := by
  simp [Ablock]

lemma Fpiece_zero_aux (ρ : ℝ) (l₁ : ℕ) (k₁ : ℤ) (N : ℕ) :
    Fpiece (kmtPj ρ) 0 l₁ k₁ N (0 : ℤ → ℂ) = 0 := by
  simp [Fpiece, piece, piExact]

lemma Gpiece_zero_aux (ρ : ℝ) (d : ℤ) (l₂ : ℕ) (k₂ : ℤ) (N : ℕ) :
    Gpiece (kmtPj ρ) d 0 l₂ k₂ N (0 : ℤ → ℂ) = 0 := by
  simp [Gpiece, piece, piExact]

lemma varpPiece_zero_left' (ρ : ℝ) (P : Polynomial ℤ) (d : ℕ) (N : NNReal) (g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) :
    varpPiece (kmtPj ρ) P d N 0 g l₁ l₂ k₁ k₂ = 0 := by
  funext x
  unfold varpPiece
  rw [Fpiece_zero_aux ρ l₁ (k₁ : ℤ) (Nat.floor N)]
  simp only [AhalfR, Ahalf]
  rw [Ablock_zero_left_aux, mul_zero]
  rfl

lemma varpPiece_zero_right' (ρ : ℝ) (P : Polynomial ℤ) (d : ℕ) (N : NNReal) (f : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) :
    varpPiece (kmtPj ρ) P d N f 0 l₁ l₂ k₁ k₂ = 0 := by
  funext x
  unfold varpPiece
  rw [Gpiece_zero_aux ρ (d : ℤ) l₂ (k₂ : ℤ) (Nat.floor N)]
  simp only [AhalfR, Ahalf]
  rw [Ablock_zero_right_aux, mul_zero]
  rfl

lemma mainPartTuple_zero_left' (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal) (g : ℤ → ℂ)
    (k₁ k₂ n : ℕ) : mainPartTuple ρ P C₀ a 0 g 0 0 k₁ k₂ n = 0 := by
  funext x
  rw [mainPartTuple_apply]
  split_ifs with h
  · exact funext_iff.mp (varpPiece_zero_left' ρ P P.natDegree (a n) g 0 0 k₁ k₂) x
  · rfl

lemma mainPartTuple_zero_right' (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal) (f : ℤ → ℂ)
    (k₁ k₂ n : ℕ) : mainPartTuple ρ P C₀ a f 0 0 0 k₁ k₂ n = 0 := by
  funext x
  rw [mainPartTuple_apply]
  split_ifs with h
  · exact funext_iff.mp (varpPiece_zero_right' ρ P P.natDegree (a n) f 0 0 k₁ k₂) x
  · rfl

lemma loModelTuple_zero_left' (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal) (g : ℤ → ℂ)
    (k₁ k₂ n : ℕ) : loModelTuple ρ P C₀ a 0 g 0 0 k₁ k₂ n = 0 := by
  funext x
  simp [loModelTuple, Tle_zero_right]

lemma loModelTuple_zero_right' (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal) (f : ℤ → ℂ)
    (k₁ k₂ n : ℕ) : loModelTuple ρ P C₀ a f 0 0 0 k₁ k₂ n = 0 := by
  funext x
  simp [loModelTuple, Tle_zero_right]

/-- On the counting measure on `ℤ`, `eLpNorm` vanishes only for the zero function. -/
lemma eq_zero_of_eLpNorm_eq_zero_loc {p : ENNReal} (hp : p ≠ 0) {h : ℤ → ℂ}
    (hh : eLpNorm h p Measure.count = 0) : h = 0 := by
  have hmeas : AEStronglyMeasurable h (Measure.count : Measure ℤ) :=
    (measurable_of_countable h).aestronglyMeasurable
  have hae : h =ᵐ[Measure.count] 0 := (eLpNorm_eq_zero_iff hp).mp hh
  funext x
  rw [Filter.EventuallyEq] at hae
  exact (Measure.ae_count_iff.mp hae) x

/-- The exact-height projection at arithmetic height `0` is the level-`0` IW multiplier. -/
lemma piExact_zero_eq_Tle (ρ : ℝ) (m : ℤ) (u : ℤ → ℂ) :
    piExact (kmtPj ρ) 0 m u = Tle ρ 0 (etaCut kmtEta m) u := by
  rw [piExact, if_pos rfl]
  change kmtProj ρ 0 m u = Tle ρ 0 (etaCut kmtEta m) u
  rw [← Tle_etaCut]

/-! ## The theorem -/

theorem LoMainSubLoModelCrude (P : Polynomial ℤ) (p₁ p₂ : ENNReal)
    (hdeg : 2 ≤ P.natDegree) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂) (htp₂ : p₂ < ⊤)
    (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (k₁ k₂ n : ℕ) (f g : ℤ → ℂ),
      Work.KMTAreas.A7.loGuard ρ C₀ a 0 0 k₁ k₂ n →
      MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g 0 0 k₁ k₂ n x
          - Work.KMTAreas.A7.loModelTuple ρ P C₀ a f g 0 0 k₁ k₂ n x)
        (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
  obtain ⟨Cp, hCppos, hCpb⟩ := eLpNorm_Tle_etaCut_neg p₁ hp₁ htp₁
  obtain ⟨Cq, hCqpos, hCqb⟩ := eLpNorm_Tle_etaCut_neg p₂ hp₂ htp₂
  obtain ⟨Cf, hCfpos, hCfb⟩ := eLpNorm_Tle_varphiNt p₁ hp₁ htp₁
  obtain ⟨Cg, hCgpos, hCgb⟩ := eLpNorm_Tle_varphitildeNt P P.natDegree p₂ hp₂
  have hCpq : 0 < (Cp + Cp) * (Cq + Cq) := mul_pos (by linarith) (by linarith)
  have hCfg : 0 < Cf * Cg := mul_pos hCfpos hCgpos
  refine ⟨(Cp + Cp) * (Cq + Cq) + Cf * Cg + 1, by linarith, ?_⟩
  intro ρ C₀ a k₁ k₂ n f g hguard
  have hq1 : 1 ≤ (p₁⁻¹ + p₂⁻¹)⁻¹ := ENNReal.one_le_inv.mpr hsum
  have hqinv : p₁⁻¹ + p₂⁻¹ = ((p₁⁻¹ + p₂⁻¹)⁻¹)⁻¹ := (inv_inv _).symm
  have hqinv' : ((p₁⁻¹ + p₂⁻¹)⁻¹)⁻¹ = p₁⁻¹ + p₂⁻¹ := inv_inv _
  by_cases hA0 : eLpNorm f p₁ Measure.count = 0
  · -- `f = 0`
    have hf0 : f = 0 := eq_zero_of_eLpNorm_eq_zero_loc (ne_of_gt (lt_trans zero_lt_one hp₁)) hA0
    subst hf0
    have hz : (fun x : ℤ => mainPartTuple ρ P C₀ a 0 g 0 0 k₁ k₂ n x
        - loModelTuple ρ P C₀ a 0 g 0 0 k₁ k₂ n x) = 0 := by
      funext x
      rw [congr_fun (mainPartTuple_zero_left' ρ P C₀ a g k₁ k₂ n) x,
        congr_fun (loModelTuple_zero_left' ρ P C₀ a g k₁ k₂ n) x]
      simp
    rw [hz]
    simp
  by_cases hB0 : eLpNorm g p₂ Measure.count = 0
  · -- `g = 0`
    have hg0 : g = 0 := eq_zero_of_eLpNorm_eq_zero_loc (ne_of_gt (lt_trans zero_lt_one hp₂)) hB0
    subst hg0
    have hz : (fun x : ℤ => mainPartTuple ρ P C₀ a f 0 0 0 k₁ k₂ n x
        - loModelTuple ρ P C₀ a f 0 0 0 k₁ k₂ n x) = 0 := by
      funext x
      rw [congr_fun (mainPartTuple_zero_right' ρ P C₀ a f k₁ k₂ n) x,
        congr_fun (loModelTuple_zero_right' ρ P C₀ a f k₁ k₂ n) x]
      simp
    rw [hz]
    simp
  by_cases hAtop : eLpNorm f p₁ Measure.count = ⊤
  · rw [hAtop]
    have hR : ENNReal.ofReal ((Cp + Cp) * (Cq + Cq) + Cf * Cg + 1) * (⊤ : ENNReal)
        * eLpNorm g p₂ Measure.count = ⊤ := by
      rw [ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr (by linarith)), ENNReal.top_mul hB0]
    rw [hR]
    exact le_top
  by_cases hBtop : eLpNorm g p₂ Measure.count = ⊤
  · rw [hBtop]
    have hne : ENNReal.ofReal ((Cp + Cp) * (Cq + Cq) + Cf * Cg + 1)
        * eLpNorm f p₁ Measure.count ≠ 0 :=
      mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr (by linarith)) hA0
    have hR : ENNReal.ofReal ((Cp + Cp) * (Cq + Cq) + Cf * Cg + 1)
        * eLpNorm f p₁ Measure.count * (⊤ : ENNReal) = ⊤ := ENNReal.mul_top hne
    rw [hR]
    exact le_top
  -- the non-degenerate case
  have hAb : eLpNorm f p₁ Measure.count < ⊤ := lt_top_iff_ne_top.mpr hAtop
  have hBb : eLpNorm g p₂ Measure.count < ⊤ := lt_top_iff_ne_top.mpr hBtop
  obtain ⟨hIdx, hCut, hReg⟩ := hguard
  have hN2 : 2 ≤ Nat.floor (a n) := by
    have h2 : 2 ≤ splitCut ρ (max (max 0 0) (max k₁ k₂)) := by
      unfold splitCut
      have h1 : 1 ≤ 2 ^ scaleCount 1 ρ (max (max 0 0) (max k₁ k₂)) := Nat.one_le_two_pow
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 ^ scaleCount 1 ρ (max (max 0 0) (max k₁ k₂))) :=
            Nat.pow_le_pow_right (by norm_num) h1
    omega
  have hlogeq : (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat
      = Nat.log 2 (max (Nat.floor (a n)) 2) := by
    unfold Work.Analysis.EndVar.logN
    rw [Int.toNat_natCast]
  have hk1 : k₁ ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat := by
    have := hReg.1
    omega
  have hk2 : k₂ ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat := by
    have := hReg.2
    omega
  have hpow1 : 2 ^ k₁ ≤ Nat.floor (a n) := by
    rw [hlogeq] at hk1
    calc 2 ^ k₁ ≤ 2 ^ Nat.log 2 (max (Nat.floor (a n)) 2) :=
          Nat.pow_le_pow_right (by norm_num) hk1
      _ ≤ max (Nat.floor (a n)) 2 := Nat.pow_log_le_self 2 (by omega)
      _ = Nat.floor (a n) := max_eq_left (by omega)
  have hpow2 : 2 ^ k₂ ≤ Nat.floor (a n) := by
    rw [hlogeq] at hk2
    calc 2 ^ k₂ ≤ 2 ^ Nat.log 2 (max (Nat.floor (a n)) 2) :=
          Nat.pow_le_pow_right (by norm_num) hk2
      _ ≤ max (Nat.floor (a n)) 2 := Nat.pow_log_le_self 2 (by omega)
      _ = Nat.floor (a n) := max_eq_left (by omega)
  have hk1z : (k₁ : ℤ) ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)) := by
    have h : ((Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat : ℤ)
        = Work.Analysis.EndVar.logN (Nat.floor (a n)) :=
      Int.toNat_of_nonneg (Work.Analysis.EndVar.logN_nonneg _)
    omega
  have hk2z : (k₂ : ℤ) ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)) := by
    have h : ((Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat : ℤ)
        = Work.Analysis.EndVar.logN (Nat.floor (a n)) :=
      Int.toNat_of_nonneg (Work.Analysis.EndVar.logN_nonneg _)
    omega
  have hκ1 : -(Work.Analysis.EndVar.logN (Nat.floor (a n))) + (k₁ : ℤ) ≤ 0 := by omega
  have hκ1' : -(Work.Analysis.EndVar.logN (Nat.floor (a n))) + ((k₁ : ℤ) - 1) ≤ 0 := by omega
  have hκ2 : (P.natDegree : ℤ) * (-(Work.Analysis.EndVar.logN (Nat.floor (a n)))
      + (k₂ : ℤ)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (by omega)
  have hκ2' : (P.natDegree : ℤ) * (-(Work.Analysis.EndVar.logN (Nat.floor (a n)))
      + ((k₂ : ℤ) - 1)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (by omega)
  -- the bounds for the two pieces of the main part
  have hFb : eLpNorm (Fpiece (kmtPj ρ) 0 0 (k₁ : ℤ) (Nat.floor (a n)) f) p₁ Measure.count
      ≤ (ENNReal.ofReal Cp + ENNReal.ofReal Cp) * eLpNorm f p₁ Measure.count := by
    by_cases hk : (k₁ : ℤ) = 0
    · have hF : Fpiece (kmtPj ρ) 0 0 (k₁ : ℤ) (Nat.floor (a n)) f
          = Tle ρ 0 (etaCut kmtEta (-(Work.Analysis.EndVar.logN (Nat.floor (a n)))
              + (k₁ : ℤ))) f := by
        rw [Fpiece_eq]
        have hass : (-((0:ℕ) : ℤ)) = (k₁ : ℤ) := by rw [hk]; norm_num
        rw [hass, piece_self, piExact_zero_eq_Tle]
      rw [hF]
      refine (hCpb ρ _ hκ1 f).trans ?_
      refine mul_le_mul' (le_add_right le_rfl) le_rfl
    · have hF : Fpiece (kmtPj ρ) 0 0 (k₁ : ℤ) (Nat.floor (a n)) f
          = Tle ρ 0 (etaCut kmtEta (-(Work.Analysis.EndVar.logN (Nat.floor (a n)))
                + (k₁ : ℤ))) f
            - Tle ρ 0 (etaCut kmtEta (-(Work.Analysis.EndVar.logN (Nat.floor (a n)))
                + ((k₁ : ℤ) - 1))) f := by
        rw [Fpiece_eq, piece_of_ne (by
          intro h
          exact hk (by rw [h]; norm_num))]
        rw [piExact_zero_eq_Tle, piExact_zero_eq_Tle]
      rw [hF]
      refine (eLpNorm_sub_le (le_of_lt hp₁)).trans ?_
      refine (add_le_add (hCpb ρ _ hκ1 f) (hCpb ρ _ hκ1' f)).trans ?_
      rw [← add_mul]
  have hGb : eLpNorm (Gpiece (kmtPj ρ) (P.natDegree : ℤ) 0 0 (k₂ : ℤ) (Nat.floor (a n)) g)
        p₂ Measure.count
      ≤ (ENNReal.ofReal Cq + ENNReal.ofReal Cq) * eLpNorm g p₂ Measure.count := by
    by_cases hk : (k₂ : ℤ) = 0
    · have hG : Gpiece (kmtPj ρ) (P.natDegree : ℤ) 0 0 (k₂ : ℤ) (Nat.floor (a n)) g
          = Tle ρ 0 (etaCut kmtEta ((P.natDegree : ℤ)
              * (-(Work.Analysis.EndVar.logN (Nat.floor (a n))) + (k₂ : ℤ)))) g := by
        rw [Gpiece_eq]
        have hass : (-((0:ℕ) : ℤ)) = (k₂ : ℤ) := by rw [hk]; norm_num
        rw [hass, piece_self, piExact_zero_eq_Tle]
      rw [hG]
      refine (hCqb ρ _ hκ2 g).trans ?_
      refine mul_le_mul' (le_add_right le_rfl) le_rfl
    · have hG : Gpiece (kmtPj ρ) (P.natDegree : ℤ) 0 0 (k₂ : ℤ) (Nat.floor (a n)) g
          = Tle ρ 0 (etaCut kmtEta ((P.natDegree : ℤ)
                * (-(Work.Analysis.EndVar.logN (Nat.floor (a n))) + (k₂ : ℤ)))) g
            - Tle ρ 0 (etaCut kmtEta ((P.natDegree : ℤ)
                * (-(Work.Analysis.EndVar.logN (Nat.floor (a n))) + ((k₂ : ℤ) - 1)))) g := by
        rw [Gpiece_eq, piece_of_ne (by
          intro h
          exact hk (by rw [h]; norm_num))]
        rw [piExact_zero_eq_Tle, piExact_zero_eq_Tle]
      rw [hG]
      refine (eLpNorm_sub_le (le_of_lt hp₂)).trans ?_
      refine (add_le_add (hCqb ρ _ hκ2 g) (hCqb ρ _ hκ2' g)).trans ?_
      rw [← add_mul]
  have hmF : MemLp (Fpiece (kmtPj ρ) 0 0 (k₁ : ℤ) (Nat.floor (a n)) f) p₁ Measure.count :=
    (MeasureTheory.memLp_iff.mpr (lt_of_le_of_lt hFb (ENNReal.mul_lt_top
        (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩) hAb)))
  have hmG : MemLp (Gpiece (kmtPj ρ) (P.natDegree : ℤ) 0 0 (k₂ : ℤ) (Nat.floor (a n)) g)
      p₂ Measure.count :=
    (MeasureTheory.memLp_iff.mpr (lt_of_le_of_lt hGb (ENNReal.mul_lt_top
        (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩) hBb)))
  have hmain : eLpNorm (varpPiece (kmtPj ρ) P P.natDegree (a n) f g 0 0 k₁ k₂)
      (p₁⁻¹ + p₂⁻¹)⁻¹ Measure.count
      ≤ (ENNReal.ofReal (Cp + Cp) * ENNReal.ofReal (Cq + Cq))
          * (eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count) := by
    unfold varpPiece
    refine (eLpNorm_AhalfR_le TZ measurePreserving_TZ (a n) X P (q₁ := p₁) (q₂ := p₂)
      hqinv hq1 hmF hmG).trans ?_
    refine (mul_le_mul' hFb hGb).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_add hCppos.le hCppos.le, ENNReal.ofReal_add hCqpos.le hCqpos.le]
    ring
  have hmodel : eLpNorm (fun x : ℤ => ∫ t in (1/2 : ℝ)..1,
      (Tle ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f x)
        * (Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x))
      (p₁⁻¹ + p₂⁻¹)⁻¹ Measure.count
      ≤ ENNReal.ofReal (Cf * Cg)
          * (eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count) := by
    refine (eLpNorm_mono_enorm (hf := by pw_aesm)
      (f := fun x : ℤ => ∫ t in (1/2 : ℝ)..1,
        (Tle ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f x)
          * (Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x))
      (g := fun x : ℤ => ∫⁻ t in Set.Ioc ((1:ℝ)/2) 1, ‖(Tle ρ 0
          (varphiNt (Nat.floor (a n)) k₁ t) f x)
          * (Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x)‖ₑ)
      (fun x => ?_)).trans ?_
    · rw [show (∫ t in (1/2 : ℝ)..1,
          (Tle ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f x)
            * (Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x))
          = ∫ t in Set.Ioc ((1:ℝ)/2) 1,
            (Tle ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f x)
              * (Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x) from
        intervalIntegral.integral_of_le (by norm_num)]
      simpa only [enorm_eq_self] using
        (enorm_integral_le_lintegral_enorm (fun t : ℝ =>
          (Tle ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f x)
            * (Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x)))
    · refine Work.KMTAreas.A7.eLpNorm_lintegral_le _ hq1 (fun t x => ‖(Tle ρ 0
          (varphiNt (Nat.floor (a n)) k₁ t) f x)
          * (Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x)‖ₑ)
          (ENNReal.ofReal (Cf * Cg)
            * (eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count)) ?_
      intro t ht
      have ht' : t ∈ Set.Icc ((1:ℝ)/2) 1 := Set.Ioc_subset_Icc_self ht
      rw [eLpNorm_enorm (hf := by pw_aesm) (fun x : ℤ => (Tle ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f x)
            * (Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x))]
      refine (Commons.MeasureTheory.Function.eLpNorm_mul_le_eLpNorm_mul_eLpNorm_complex
        (p := (p₁⁻¹ + p₂⁻¹)⁻¹) (q := p₁) (r := p₂) hqinv'
        (measurable_of_countable _).aemeasurable
        (measurable_of_countable _).aemeasurable).trans ?_
      refine (mul_le_mul' (hCfb ρ _ k₁ hpow1 t ht' f) (hCgb ρ _ k₂ hpow2 t g)).trans ?_
      rw [ENNReal.ofReal_mul hCfpos.le]
      exact le_of_eq (by ring)
  have hdiff : (fun x : ℤ => mainPartTuple ρ P C₀ a f g 0 0 k₁ k₂ n x
      - loModelTuple ρ P C₀ a f g 0 0 k₁ k₂ n x)
      = fun x : ℤ => if loGuard ρ C₀ a 0 0 k₁ k₂ n then
          (varpPiece (kmtPj ρ) P P.natDegree (a n) f g 0 0 k₁ k₂ x
            - ∫ t in (1/2 : ℝ)..1, (Tle ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f x)
              * (Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x))
        else 0 := by
    funext x
    rw [mainPartTuple_apply]
    simp only [loModelTuple]
    by_cases h : loGuard ρ C₀ a 0 0 k₁ k₂ n <;> simp [h]
  rw [hdiff]
  have hind : eLpNorm (fun x : ℤ => if loGuard ρ C₀ a 0 0 k₁ k₂ n then
        (varpPiece (kmtPj ρ) P P.natDegree (a n) f g 0 0 k₁ k₂ x
          - ∫ t in (1/2 : ℝ)..1, (Tle ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f x)
            * (Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x))
      else 0) (p₁⁻¹ + p₂⁻¹)⁻¹ Measure.count
      ≤ eLpNorm (fun x : ℤ => (varpPiece (kmtPj ρ) P P.natDegree (a n) f g 0 0 k₁ k₂ x
          - ∫ t in (1/2 : ℝ)..1, (Tle ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f x)
            * (Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x)))
        (p₁⁻¹ + p₂⁻¹)⁻¹ Measure.count := by
    refine eLpNorm_mono_enorm (hf := by pw_aesm) (f := fun x : ℤ => if loGuard ρ C₀ a 0 0 k₁ k₂ n then
        (varpPiece (kmtPj ρ) P P.natDegree (a n) f g 0 0 k₁ k₂ x
          - ∫ t in (1/2 : ℝ)..1, (Tle ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f x)
            * (Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x))
      else 0) (g := fun x : ℤ => (varpPiece (kmtPj ρ) P P.natDegree (a n) f g 0 0 k₁ k₂ x
          - ∫ t in (1/2 : ℝ)..1, (Tle ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f x)
            * (Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x))) ?_
    intro x
    by_cases h : loGuard ρ C₀ a 0 0 k₁ k₂ n <;> simp [h]
  refine hind.trans ?_
  refine (eLpNorm_sub_le hq1).trans ?_
  refine (add_le_add hmain hmodel).trans ?_
  set X : ENNReal := eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count with hX
  have hcomb : (ENNReal.ofReal (Cp + Cp) * ENNReal.ofReal (Cq + Cq)) * X
      + ENNReal.ofReal (Cf * Cg) * X
      = ENNReal.ofReal ((Cp + Cp) * (Cq + Cq) + Cf * Cg) * X := by
    rw [← add_mul]
    congr 1
    rw [← ENNReal.ofReal_mul (by linarith : (0:ℝ) ≤ Cp + Cp),
      ← ENNReal.ofReal_add (by nlinarith [hCppos, hCqpos] : (0:ℝ) ≤ (Cp + Cp) * (Cq + Cq))
        (by nlinarith [hCfpos, hCgpos] : (0:ℝ) ≤ Cf * Cg)]
  rw [hcomb]
  have hXeq : ENNReal.ofReal ((Cp + Cp) * (Cq + Cq) + Cf * Cg + 1)
      * eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count
      = ENNReal.ofReal ((Cp + Cp) * (Cq + Cq) + Cf * Cg + 1) * X := by
    rw [hX, mul_assoc]
  rw [hXeq]
  refine mul_le_mul' ?_ le_rfl
  exact ENNReal.ofReal_le_ofReal (by linarith)


end

end Work.KMTAreas.A7
