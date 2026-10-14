import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstAux.SmoothErr
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstMain
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongPersist.Vocab
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO2
import Submission.Work.H2W.FstarDzIterFourPsiAe
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.ThetaAgmon.agmon_interval
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.ChiaBasic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWAux

set_option autoImplicit false

/-- The summable majorant of the `m`-th term of the series of `chia ψ (k+1)`: with
`λ_m ≥ 4m²` and `√(2m+1) ≥ 1` the term is bounded by `3 Cd Cg (m+1)^{-3}`. -/
private def chiaMajorant (Cd Cg : ℝ) (m : ℕ) : ℝ :=
  3 * Cd * Cg * (1 / ((m : ℝ) + 1) ^ 3)

private lemma chiaMajorant_nonneg (Cd Cg : ℝ) (hCd : 0 < Cd) (hCg : 0 < Cg) (m : ℕ) :
    0 ≤ chiaMajorant Cd Cg m := by
  rw [chiaMajorant]
  positivity

/-- `eFam m` is continuous (a polynomial in `cos θ` and `sin θ`). -/
private lemma continuous_eFam (m : ℕ) : Continuous (Work.FTS.PhiStar.Gegenbauer.eFam m) := by
  change Continuous (fun θ : ℝ =>
    Real.cos θ * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ))
  exact Real.continuous_cos.mul
    ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous.comp
      Real.continuous_sin)

private lemma continuous_sinCos2 : Continuous Work.Elliptic.sinCos2 := by
  change Continuous (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
  exact Real.continuous_sin.mul (Real.continuous_cos.pow 2)

/-- `e_m(0) = 0`: the odd-indexed Gegenbauer polynomials vanish at the origin. -/
private lemma eFam_apply_zero (m : ℕ) : Work.FTS.PhiStar.Gegenbauer.eFam m 0 = 0 := by
  simp [Work.FTS.PhiStar.Gegenbauer.eFam, Work.FTS.PhiStar.Gegenbauer.gC_odd_zero]

/-- `e_m(π/2) = 0`. -/
private lemma eFam_apply_pi_div_two (m : ℕ) :
    Work.FTS.PhiStar.Gegenbauer.eFam m (Real.pi / 2) = 0 := by
  simp [Work.FTS.PhiStar.Gegenbauer.eFam, Real.cos_pi_div_two]

/-- The `sin θ cos² θ`-moment of `e_m` vanishes for `m ≥ 1`: `λ_m e_m` has vanishing moment
(`MomentLamEFam`) and `λ_m ≠ 0` for `m ≥ 1`. -/
private lemma integral_eFam_mul_sinCos2 (m : ℕ) (hm : 1 ≤ m) :
    (∫ θ in Work.Spaces.Iθ,
      Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.Elliptic.sinCos2 θ) = 0 := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hlam : Work.FTS.PhiStar.Gegenbauer.lam m ≠ 0 := by
    rw [Work.FTS.PhiStar.Gegenbauer.lam]
    positivity
  have hpt : ∀ θ : ℝ,
      Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.Elliptic.sinCos2 θ
        = (Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹
          * ((Work.FTS.PhiStar.Gegenbauer.lam m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
              * Work.Elliptic.sinCos2 θ) := by
    intro θ
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
  have hcongr : (∫ θ in Work.Spaces.Iθ,
        Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.Elliptic.sinCos2 θ)
      = ∫ θ in Work.Spaces.Iθ, (Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹
          * ((Work.FTS.PhiStar.Gegenbauer.lam m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
              * Work.Elliptic.sinCos2 θ) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => hpt θ)
  rw [hcongr, MeasureTheory.integral_const_mul, (MomentLamEFam m).1, mul_zero]

/-- `Σ_m (m+1)^{-3}` is summable (it is `Σ_m m^{-3}`, shifted). -/
private lemma summable_rpow_neg_three :
    Summable (fun m : ℕ => ((m : ℝ) + 1) ^ (-(3 : ℝ))) := by
  have h0 : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 : ℝ))) :=
    (Real.summable_nat_rpow (p := (-(3 : ℝ)))).mpr (by norm_num)
  have h1 := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-(3 : ℝ))) 1).mpr h0
  simpa only [Nat.cast_add, Nat.cast_one] using h1

/-- `x^{-3} = 1/x³` (the exponent written as a `ℕ`-cast so that `Real.rpow_natCast` applies). -/
private lemma rpow_neg_three {x : ℝ} (hx : 0 ≤ x) : x ^ (-(3 : ℝ)) = 1 / x ^ 3 := by
  rw [show (-(3 : ℝ)) = -(((3 : ℕ)) : ℝ) by norm_num,
    Real.rpow_neg hx (((3 : ℕ)) : ℝ), Real.rpow_natCast, one_div]

/-- The majorant sequences are summable. -/
private lemma summable_chiaMajorant (Cd Cg : ℝ) : Summable (chiaMajorant Cd Cg) := by
  have h : Summable (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1) ^ 3) := by
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
      summable_rpow_neg_three
    rw [rpow_neg_three (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1)]
  change Summable (fun m : ℕ => 3 * Cd * Cg * (1 / ((m : ℝ) + 1) ^ 3))
  exact h.mul_left (3 * Cd * Cg)

/-- Arithmetic core of the term bound: with `λ ≥ 4M²` (`M = m ≥ 1`) and `√(2M+1) ≥ 1` one has
`(2M+1)/(λ²√(2M+1)) ≤ 3/(M+1)³`. -/
private lemma chia_arith_core (Cd Cg L M : ℝ) (hCd : 0 < Cd) (hCg : 0 < Cg)
    (hM : 1 ≤ M) (hL : 4 * M ^ 2 ≤ L) :
    (Cd / (L * Real.sqrt (2 * M + 1))) * L⁻¹ * (Cg * (2 * M + 1))
      ≤ 3 * Cd * Cg * (1 / (M + 1) ^ 3) := by
  have hLpos : 0 < L := by nlinarith [hL, hM, sq_nonneg M]
  have hMpos : 0 < M + 1 := by linarith
  have hNpos : 0 < 2 * M + 1 := by linarith
  have hspos : 0 < Real.sqrt (2 * M + 1) := Real.sqrt_pos.mpr hNpos
  have hs1 : 1 ≤ Real.sqrt (2 * M + 1) := Real.one_le_sqrt.mpr (by linarith)
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hsne : Real.sqrt (2 * M + 1) ≠ 0 := ne_of_gt hspos
  have hLNne : L * Real.sqrt (2 * M + 1) ≠ 0 := ne_of_gt (mul_pos hLpos hspos)
  have hL2Nne : L ^ 2 * Real.sqrt (2 * M + 1) ≠ 0 :=
    ne_of_gt (mul_pos (pow_pos hLpos 2) hspos)
  -- `16 M⁴ ≤ L²`
  have hLsq : 16 * M ^ 4 ≤ L ^ 2 := by
    have h1 : (4 * M ^ 2) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by positivity) hL 2
    have h2 : (4 * M ^ 2) ^ 2 = 16 * M ^ 4 := by ring
    rwa [h2] at h1
  -- `(2M+1)(M+1)³ ≤ 3 L²`
  have hfinal : (2 * M + 1) * (M + 1) ^ 3 ≤ 3 * L ^ 2 := by
    have h2M : M + 1 ≤ 2 * M := by linarith
    have hcube : (M + 1) ^ 3 ≤ (2 * M) ^ 3 := pow_le_pow_left₀ (by linarith) h2M 3
    have hN3 : 2 * M + 1 ≤ 3 * (M + 1) := by linarith
    calc (2 * M + 1) * (M + 1) ^ 3
        ≤ (3 * (M + 1)) * (M + 1) ^ 3 := mul_le_mul_of_nonneg_right hN3 (by positivity)
      _ = 3 * ((M + 1) ^ 3 * (M + 1)) := by ring
      _ ≤ 3 * ((2 * M) ^ 3 * (2 * M)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul hcube h2M (by linarith) (by positivity)
      _ = 48 * M ^ 4 := by ring
      _ ≤ 3 * L ^ 2 := by linarith [hLsq]
  have hkey : (2 * M + 1) / L ^ 2 ≤ 3 / (M + 1) ^ 3 := by
    rw [div_le_div_iff₀ (pow_pos hLpos 2) (pow_pos hMpos 3)]
    exact hfinal
  have heq : (Cd / (L * Real.sqrt (2 * M + 1))) * L⁻¹ * (Cg * (2 * M + 1))
      = Cd * Cg * ((2 * M + 1) / (L ^ 2 * Real.sqrt (2 * M + 1))) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    rw [show (L ^ 2 * Real.sqrt (2 * M + 1))⁻¹
        = (L * Real.sqrt (2 * M + 1))⁻¹ * L⁻¹ by
      rw [show L ^ 2 * Real.sqrt (2 * M + 1) = (L * Real.sqrt (2 * M + 1)) * L by ring,
        mul_inv]]
    ring
  have hmono : (2 * M + 1) / (L ^ 2 * Real.sqrt (2 * M + 1)) ≤ (2 * M + 1) / L ^ 2 := by
    rw [div_le_div_iff₀ (mul_pos (pow_pos hLpos 2) hspos) (pow_pos hLpos 2)]
    have hh : L ^ 2 ≤ L ^ 2 * Real.sqrt (2 * M + 1) := by
      simpa using mul_le_mul_of_nonneg_left hs1 (sq_nonneg L)
    exact mul_le_mul_of_nonneg_left hh (by linarith)
  rw [heq]
  calc Cd * Cg * ((2 * M + 1) / (L ^ 2 * Real.sqrt (2 * M + 1)))
      ≤ Cd * Cg * ((2 * M + 1) / L ^ 2) := mul_le_mul_of_nonneg_left hmono (by positivity)
    _ ≤ Cd * Cg * (3 / (M + 1) ^ 3) := mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = 3 * Cd * Cg * (1 / (M + 1) ^ 3) := by ring

/-- Termwise bound for the series of `chia ψ (k+1)`. -/
private lemma chia_term_bound (ψ : ℝ → ℝ) {Cd Cg : ℝ} (hCd : 0 < Cd) (hCg : 0 < Cg)
    (hdec : ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ Cg * (2 * (m : ℝ) + 1))
    (k : ℕ) :
    ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      ‖Work.FTS.PhiStar.Series.bmode m ψ * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ‖ ≤ chiaMajorant Cd Cg m := by
  intro m θ hθ
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have hzero : Work.FTS.PhiStar.Series.bmode 0 ψ
        * ((Work.FTS.PhiStar.Gegenbauer.lam 0)⁻¹) ^ (k + 1)
        * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ = 0 := by
      simp [Work.FTS.PhiStar.Gegenbauer.lam]
    rw [hzero, norm_zero, chiaMajorant]
    positivity
  · have hM : 1 ≤ (m : ℝ) := by exact_mod_cast hm
    have hL4 : 4 * (m : ℝ) ^ 2 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
      rw [Work.FTS.PhiStar.Gegenbauer.lam]
      nlinarith [hM]
    have hLam1 : 1 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
      have hM2 : 1 ≤ (m : ℝ) ^ 2 := by nlinarith [hM]
      nlinarith [hL4, hM2]
    have hLampos : 0 < Work.FTS.PhiStar.Gegenbauer.lam m := lt_of_lt_of_le one_pos hLam1
    have hP : |((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)|
        ≤ (Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹ := by
      rw [abs_of_nonneg (pow_nonneg (le_of_lt (inv_pos.mpr hLampos)) _), inv_pow]
      have hp : (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 1
          ≤ (Work.FTS.PhiStar.Gegenbauer.lam m) ^ (k + 1) :=
        pow_le_pow_right₀ hLam1 (by omega)
      have h' := one_div_le_one_div_of_le
        (show (0 : ℝ) < (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 1 by positivity) hp
      simpa only [one_div, pow_one] using h'
    have hb : |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) := hdec m hm
    have he : |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ Cg * (2 * (m : ℝ) + 1) := hgr m θ hθ
    have hden : 0 < Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1) :=
      mul_pos hLampos (Real.sqrt_pos.mpr (by linarith))
    have hstep : ‖Work.FTS.PhiStar.Series.bmode m ψ
          * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ‖
        ≤ (Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
            * (Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹ * (Cg * (2 * (m : ℝ) + 1)) := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul hb hP (abs_nonneg _) (le_of_lt (div_pos hCd hden))) he
        (abs_nonneg _) (le_of_lt (mul_pos (div_pos hCd hden) (inv_pos.mpr hLampos)))
    refine le_trans hstep ?_
    rw [chiaMajorant]
    exact chia_arith_core Cd Cg (Work.FTS.PhiStar.Gegenbauer.lam m) (m : ℝ) hCd hCg hM hL4

/-- `chia ψ (k+1)` agrees with its defining `eFam`-series on all of `Iθ` (on the open interval
this is `chia_eq_tsum`; at the two endpoints both sides vanish). -/
private lemma chia_eq_tsum_Iθ (ψ : ℝ → ℝ) (k : ℕ) :
    EqOn (chia ψ (k + 1)) (fun θ : ℝ => ∑' m : ℕ,
      Work.FTS.PhiStar.Series.bmode m ψ
        * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ) Work.Spaces.Iθ := by
  intro θ hθ
  rw [Work.Spaces.Iθ] at hθ
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · subst h0
    have hL : chia ψ (k + 1) 0 = 0 := by
      change Work.Construction.s2 0 * Wt ψ (k + 1) 0 = 0
      rw [Work.Construction.s2_eq]
      simp
    have hR : (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
          * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
          * Work.FTS.PhiStar.Gegenbauer.eFam m 0) = 0 := by
      rw [show (fun m : ℕ => Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
            * Work.FTS.PhiStar.Gegenbauer.eFam m 0) = (fun _ => (0 : ℝ)) by
        funext m
        simp [eFam_apply_zero m]]
      exact (hasSum_zero (α := ℝ)).tsum_eq
    show chia ψ (k + 1) 0 = (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
          * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
          * Work.FTS.PhiStar.Gegenbauer.eFam m 0)
    rw [hL, hR]
  · rcases lt_or_eq_of_le hθ.2 with h2 | h2
    · exact chia_eq_tsum ψ k ⟨h0, h2⟩
    · subst h2
      have hL : chia ψ (k + 1) (Real.pi / 2) = 0 := by
        change Work.Construction.s2 (Real.pi / 2) * Wt ψ (k + 1) (Real.pi / 2) = 0
        rw [Work.Construction.s2_eq, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi,
          zero_mul]
      have hR : (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
            * Work.FTS.PhiStar.Gegenbauer.eFam m (Real.pi / 2)) = 0 := by
        rw [show (fun m : ℕ => Work.FTS.PhiStar.Series.bmode m ψ
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
              * Work.FTS.PhiStar.Gegenbauer.eFam m (Real.pi / 2)) = (fun _ => (0 : ℝ)) by
          funext m
          simp [eFam_apply_pi_div_two m]]
        exact (hasSum_zero (α := ℝ)).tsum_eq
      show chia ψ (k + 1) (Real.pi / 2) = (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
            * Work.FTS.PhiStar.Gegenbauer.eFam m (Real.pi / 2))
      rw [hL, hR]

/-- **The basic facts about `chia ψ j` for `j = k+1 ≥ 1`.** -/
private lemma chia_basic_aux (ψ : ℝ → ℝ)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * (2 * (m : ℝ) + 1))
    (k : ℕ) :
    ContinuousOn (chia ψ (k + 1)) (Set.Ioo 0 (Real.pi / 2)) ∧
      (∃ M : ℝ, ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) → |chia ψ (k + 1) θ| ≤ M) ∧
      MeasureTheory.IntegrableOn (fun θ : ℝ =>
        chia ψ (k + 1) θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, chia ψ (k + 1) θ * Work.Elliptic.sinCos2 θ) = 0 := by
  obtain ⟨Cd, hCd, hdec⟩ := hdec
  obtain ⟨Cg, hCg, hgr⟩ := hgr
  have hsum : Summable (chiaMajorant Cd Cg) := summable_chiaMajorant Cd Cg
  have hterm : ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      ‖Work.FTS.PhiStar.Series.bmode m ψ
        * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ‖ ≤ chiaMajorant Cd Cg m :=
    fun m θ hθ => chia_term_bound ψ hCd hCg hdec hgr k m θ hθ
  -- the series converges absolutely and uniformly on `Iθ`
  have hGcont : ContinuousOn (fun θ : ℝ => ∑' m : ℕ,
      Work.FTS.PhiStar.Series.bmode m ψ
        * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ) Work.Spaces.Iθ :=
    continuousOn_tsum (fun m => ((continuous_eFam m).const_mul _).continuousOn) hsum hterm
  have hsub : Set.Ioo 0 (Real.pi / 2) ⊆ Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact Set.Ioo_subset_Icc_self
  have hEq : EqOn (chia ψ (k + 1)) (fun θ : ℝ => ∑' m : ℕ,
      Work.FTS.PhiStar.Series.bmode m ψ
        * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ) Work.Spaces.Iθ :=
    chia_eq_tsum_Iθ ψ k
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- continuity on the open interval
    exact (hGcont.mono hsub).congr (hEq.mono hsub)
  · -- boundedness on the open interval
    refine ⟨∑' m : ℕ, chiaMajorant Cd Cg m, fun θ hθ => ?_⟩
    have hθI : θ ∈ Work.Spaces.Iθ := hsub hθ
    have hEqθ : chia ψ (k + 1) θ = ∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
        * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ := hEq hθI
    rw [hEqθ]
    have hsumθ : Summable (fun m : ℕ => ‖Work.FTS.PhiStar.Series.bmode m ψ
        * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ‖) :=
      Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => hterm m θ hθI) hsum
    calc |∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        = ‖∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ‖ := by rw [Real.norm_eq_abs]
      _ ≤ ∑' m : ℕ, ‖Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ‖ := norm_tsum_le_tsum_norm hsumθ
      _ ≤ ∑' m : ℕ, chiaMajorant Cd Cg m :=
          Summable.tsum_le_tsum (fun m => hterm m θ hθI) hsumθ hsum
  · -- integrability of the integrand on `Iθ`
    have hcont_prod : ContinuousOn (fun θ : ℝ => (∑' m : ℕ,
        Work.FTS.PhiStar.Series.bmode m ψ
          * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.Elliptic.sinCos2 θ)
        Work.Spaces.Iθ :=
      hGcont.mul continuous_sinCos2.continuousOn
    have hInt : MeasureTheory.IntegrableOn (fun θ : ℝ => (∑' m : ℕ,
        Work.FTS.PhiStar.Series.bmode m ψ
          * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.Elliptic.sinCos2 θ)
        Work.Spaces.Iθ :=
      ContinuousOn.integrableOn_compact isCompact_Icc hcont_prod
    refine hInt.congr_fun (fun θ hθ => ?_) measurableSet_Icc
    simp only [hEq hθ]
  · -- the integral vanishes
    have hIntEq : (∫ θ in Work.Spaces.Iθ, chia ψ (k + 1) θ * Work.Elliptic.sinCos2 θ)
        = ∫ θ in Work.Spaces.Iθ, (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.Elliptic.sinCos2 θ :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => by simp only [hEq hθ])
    rw [hIntEq]
    -- the termwise integrals vanish
    have htermInt : ∀ m : ℕ, (∫ θ in Work.Spaces.Iθ,
        (Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.Elliptic.sinCos2 θ) = 0 := by
      intro m
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        have hzero : (fun θ : ℝ => (Work.FTS.PhiStar.Series.bmode 0 ψ
              * ((Work.FTS.PhiStar.Gegenbauer.lam 0)⁻¹) ^ (k + 1)
              * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ) * Work.Elliptic.sinCos2 θ)
            = fun _ => (0 : ℝ) := by
          funext θ
          simp [Work.FTS.PhiStar.Gegenbauer.lam]
        rw [hzero]
        simp
      · have hsplit : (∫ θ in Work.Spaces.Iθ,
            (Work.FTS.PhiStar.Series.bmode m ψ
                * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
                * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.Elliptic.sinCos2 θ)
            = (Work.FTS.PhiStar.Series.bmode m ψ
                * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1))
              * (∫ θ in Work.Spaces.Iθ,
                  Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.Elliptic.sinCos2 θ) := by
          rw [show (∫ θ in Work.Spaces.Iθ,
                (Work.FTS.PhiStar.Series.bmode m ψ
                    * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
                    * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.Elliptic.sinCos2 θ)
              = ∫ θ in Work.Spaces.Iθ, (Work.FTS.PhiStar.Series.bmode m ψ
                    * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1))
                  * (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.Elliptic.sinCos2 θ) from
            MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
          rw [MeasureTheory.integral_const_mul]
        rw [hsplit, integral_eFam_mul_sinCos2 m hm, mul_zero]
    have hFint : ∀ m : ℕ, MeasureTheory.IntegrableOn (fun θ : ℝ =>
        (Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.Elliptic.sinCos2 θ)
        Work.Spaces.Iθ := by
      intro m
      exact ContinuousOn.integrableOn_compact isCompact_Icc
        (((continuous_eFam m).const_mul _).mul continuous_sinCos2).continuousOn
    have hpart_cont : ∀ N : ℕ, Continuous (fun θ : ℝ =>
        (∑ m ∈ Finset.range N, Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.Elliptic.sinCos2 θ) :=
      fun N => (continuous_finsetSum (Finset.range N)
        (fun m _ => (continuous_eFam m).const_mul _)).mul continuous_sinCos2
    have hK : 0 ≤ ∑' m : ℕ, chiaMajorant Cd Cg m :=
      tsum_nonneg (fun m => chiaMajorant_nonneg Cd Cg hCd hCg m)
    have hmain : Tendsto (fun N : ℕ => ∫ θ, (∑ m ∈ Finset.range N,
            Work.FTS.PhiStar.Series.bmode m ψ
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.Elliptic.sinCos2 θ
          ∂(volume.restrict Work.Spaces.Iθ)) atTop
        (𝓝 (∫ θ, (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.Elliptic.sinCos2 θ
            ∂(volume.restrict Work.Spaces.Iθ))) :=
      tendsto_integral_of_dominated_convergence
        (μ := volume.restrict Work.Spaces.Iθ)
        (F := fun (N : ℕ) (θ : ℝ) => (∑ m ∈ Finset.range N,
            Work.FTS.PhiStar.Series.bmode m ψ
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.Elliptic.sinCos2 θ)
        (f := fun (θ : ℝ) => (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.Elliptic.sinCos2 θ)
        (fun θ : ℝ => (∑' m : ℕ, chiaMajorant Cd Cg m) * ‖Work.Elliptic.sinCos2 θ‖)
        (fun N => (hpart_cont N).aestronglyMeasurable)
        (ContinuousOn.integrableOn_compact (μ := volume) (K := Work.Spaces.Iθ) isCompact_Icc
          (continuous_const.mul (continuous_norm.comp continuous_sinCos2)).continuousOn)
      (fun N => (MeasureTheory.ae_restrict_mem measurableSet_Icc).mono (fun θ hθ => by
        have h1 : ‖∑ m ∈ Finset.range N, Work.FTS.PhiStar.Series.bmode m ψ
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ‖
            ≤ ∑ m ∈ Finset.range N, chiaMajorant Cd Cg m :=
          le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun m _ => hterm m θ hθ))
        have h2 : ∑ m ∈ Finset.range N, chiaMajorant Cd Cg m
            ≤ ∑' m : ℕ, chiaMajorant Cd Cg m :=
          Summable.sum_le_tsum (Finset.range N)
            (fun m _ => chiaMajorant_nonneg Cd Cg hCd hCg m) hsum
        rw [norm_mul]
        exact mul_le_mul (le_trans h1 h2) le_rfl (norm_nonneg _) hK))
      ((MeasureTheory.ae_restrict_mem measurableSet_Icc).mono (fun θ hθ => by
        have hsumθ : Summable (fun m : ℕ => Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ) :=
          Summable.of_norm_bounded hsum (fun m => hterm m θ hθ)
        have hpart := hsumθ.hasSum.tendsto_sum_nat
        exact Filter.Tendsto.mul_const (Work.Elliptic.sinCos2 θ) hpart))
    have hzeroN : ∀ N : ℕ, (∫ θ, (∑ m ∈ Finset.range N, Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.Elliptic.sinCos2 θ
          ∂(volume.restrict Work.Spaces.Iθ)) = 0 := by
      intro N
      have h1 : (∫ θ, (∑ m ∈ Finset.range N, Work.FTS.PhiStar.Series.bmode m ψ
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.Elliptic.sinCos2 θ
            ∂(volume.restrict Work.Spaces.Iθ))
          = ∫ θ, (∑ m ∈ Finset.range N, (Work.FTS.PhiStar.Series.bmode m ψ
                * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
                * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.Elliptic.sinCos2 θ)
              ∂(volume.restrict Work.Spaces.Iθ) := by
        refine integral_congr_ae ?_
        filter_upwards with θ
        rw [Finset.sum_mul]
      rw [h1, MeasureTheory.integral_finsetSum (Finset.range N) (fun m _ => hFint m),
        Finset.sum_eq_zero (fun m _ => htermInt m)]
    have hconst : (fun N : ℕ => (∫ θ, (∑ m ∈ Finset.range N, Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.Elliptic.sinCos2 θ
          ∂(volume.restrict Work.Spaces.Iθ))) = fun _ => (0 : ℝ) := by
      funext N
      exact hzeroN N
    have hlim0 : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop
        (𝓝 (∫ θ, (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.Elliptic.sinCos2 θ
            ∂(volume.restrict Work.Spaces.Iθ))) := by
      refine Filter.Tendsto.congr (fun N => ?_) hmain
      exact hzeroN N
    exact (tendsto_nhds_unique tendsto_const_nhds hlim0).symm

theorem ChiaBasic (ψ : ℝ → ℝ)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * (2 * (m : ℝ) + 1))
    (hQ : ∃ C : ℕ → ℝ, (∀ l : ℕ, 0 ≤ C l) ∧
      ∀ (m : ℕ), 1 ≤ m → ∀ (l : ℕ), l ≤ 8 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |iteratedDeriv l (Work.FTS.PhiStar.FlatWAux.Qm m) θ|
          ≤ C l * (2 * (m : ℝ) + 1) ^ (2 * l + 2)) :
    (∀ j : ℕ, 1 ≤ j → j ≤ Work.FTS.PhiStar.FlatWAux.J →
        ContinuousOn (Work.FTS.PhiStar.FlatWAux.chia ψ j) (Set.Ioo 0 (Real.pi / 2))) ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ Work.FTS.PhiStar.FlatWAux.J →
        ∃ M : ℝ, ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
          |Work.FTS.PhiStar.FlatWAux.chia ψ j θ| ≤ M) ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ Work.FTS.PhiStar.FlatWAux.J →
        MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.PhiStar.FlatWAux.chia ψ j θ
          * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ) ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ Work.FTS.PhiStar.FlatWAux.J →
        (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.FlatWAux.chia ψ j θ
          * Work.Elliptic.sinCos2 θ) = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj _
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = k + 1 := ⟨j - 1, by omega⟩
    exact (chia_basic_aux ψ hdec hgr k).1
  · intro j hj _
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = k + 1 := ⟨j - 1, by omega⟩
    exact (chia_basic_aux ψ hdec hgr k).2.1
  · intro j hj _
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = k + 1 := ⟨j - 1, by omega⟩
    exact (chia_basic_aux ψ hdec hgr k).2.2.1
  · intro j hj _
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = k + 1 := ⟨j - 1, by omega⟩
    exact (chia_basic_aux ψ hdec hgr k).2.2.2

end Work.FTS.PhiStar.FlatWAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.WtBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology BigOperators

namespace Work.FTS.PhiStar.FlatWAux


end Work.FTS.PhiStar.FlatWAux
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.EstTendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Joint a.e. strong measurability of the `ℋᵏ`-integrand -/

theorem aestronglyMeasurable_uncurry_HkIntegrand {α : ℝ} {k : ℕ} {G : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen G) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k G p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _ (hsm.continuousOn_HkIntegrand α k)

/-- The inner `θ`-integral of the `ℋᵏ`-integrand is a.e. strongly measurable in `z`. -/
theorem aemeasurable_integral_HkIntegrand {α : ℝ} {k : ℕ} {G : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen G) :
    AEMeasurable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k G z θ)
      (volume.restrict Work.Spaces.Iz) :=
  (aestronglyMeasurable_uncurry_HkIntegrand (α := α) (k := k) hsm).integral_prod_right'.aemeasurable

/-- The `Ω_n`-part of the `ℋᵏ`-integrand is jointly a.e. strongly measurable. -/
theorem aestronglyMeasurable_uncurry_omegaPart {α : ℝ} {k : ℕ} (n : ℕ) {G : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen G) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (omegaPart α k n G p.1 p.2))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  have hbase : AEStronglyMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k G p.1 p.2))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (aestronglyMeasurable_uncurry_HkIntegrand (α := α) (k := k) hsm).aemeasurable |>.aestronglyMeasurable
  have hind : AEStronglyMeasurable
      ((Omega n).indicator fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k G p.1 p.2))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    hbase.indicator (Omega_measurable n)
  refine hind.congr ?_
  filter_upwards with p
  unfold omegaPart
  by_cases h : p ∈ Omega n <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]

/-- The `z`-a.e. measurability of the `Ω_n`-integral. -/
theorem aemeasurable_lintegral_omegaPart {α : ℝ} {k : ℕ} (n : ℕ) {G : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen G) :
    AEMeasurable (fun z : ℝ => ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (omegaPart α k n G z θ)) (volume.restrict Work.Spaces.Iz) :=
  AEMeasurable.lintegral_prod_right'
    (μ := volume.restrict Work.Spaces.Iz) (ν := volume.restrict Work.Spaces.Iθ)
    (f := fun p : ℝ × ℝ => ENNReal.ofReal (omegaPart α k n G p.1 p.2))
    (aestronglyMeasurable_uncurry_omegaPart (α := α) (k := k) n hsm).aemeasurable

/-! ## The bound on the `ℋᵏ`-square of the error -/

theorem HkSq_err_le (k : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α k F)
    (htr : Work.FTS.PhiStar.ThetaTraces α k F)
    (hFs : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0)
    {Cm RPb : ℝ} (hCm : 0 ≤ Cm) (hRPb : 0 ≤ RPb)
    (hmom : ∀ n : ℕ, 2 ≤ n →
      (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal ((Work.Spaces.w z) ^ 2
          * ∑ m ∈ Finset.range (k + 1),
              (Work.Spaces.DzIter m (fun z' _ : ℝ => mu n F z') z 0) ^ 2))
        ≤ ENNReal.ofReal (Cm * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F))
    (hmem : ∀ n : ℕ, 3 ≤ n → Work.Spaces.HkMem α k (err n F))
    (hRP : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (rhoProf α k θ)) ≤ ENNReal.ofReal RPb) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 3 ≤ n →
      Work.Spaces.HkSq α k (err n F)
        ≤ C * ((∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)).toReal
            + (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F) := by
  obtain ⟨Ccrux, hCcruxpos, hcrux⟩ := theta_lintegral_le k α hα hα1
  have hCcrux : 0 ≤ Ccrux := hCcruxpos.le
  set κ : ℝ := Cm * (RPb + 1) with hκdef
  have hκ : 0 ≤ κ := by
    rw [hκdef]
    exact mul_nonneg hCm (by linarith)
  refine ⟨Ccrux * (1 + κ), by positivity, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hsmE : Work.FTS.EllipticEst.SmoothOpen (err n F) := EstAux.smoothOpen_err hsm hn1
  set E : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (err n F) z θ with hE
  set P : ℝ → ℝ≥0∞ := fun z => ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (omegaPart α k n F z θ) with hP
  set Q : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2
      * ∑ m ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter m (fun z' _ : ℝ => mu n F z') z 0) ^ 2) with hQ
  set RP : ℝ≥0∞ := ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (rhoProf α k θ) with hRPdef
  have hRPne : RP ≠ ⊤ := by
    rw [hRPdef]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hRP
  set Tn : ℝ := (∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)).toReal with hTn
  set Λn : ℝ := (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F with hΛn
  -- ## (1) the `θ`-slice identity
  have hslice : ∀ z ∈ Work.Spaces.Iz, ENNReal.ofReal (E z)
      = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k (err n F) z θ) := by
    intro z hz
    rw [hE]
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal ((hmem n hn).1 z hz)
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k (err n F) z θ)
  -- ## (2) the estimate `EstMain.theta_lintegral_le` at each `z`
  have hstep : ∀ z ∈ Work.Spaces.Iz, ENNReal.ofReal (E z)
      ≤ ENNReal.ofReal Ccrux * (P z + Q z * RP) := by
    intro z hz
    rw [hslice z hz]
    exact hcrux n F hn hsm htr z hz
  -- ## (3) integrate over `z`
  have hPmeas : AEMeasurable P (volume.restrict Work.Spaces.Iz) := by
    rw [hP]
    exact aemeasurable_lintegral_omegaPart (α := α) (k := k) n hsm
  have hAfin : (∫⁻ z in Work.Spaces.Iz, P z) < ⊤ := by
    calc (∫⁻ z in Work.Spaces.Iz, P z)
        ≤ ∫⁻ z in Work.Spaces.Iz,
            ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) := by
          refine lintegral_mono_ae (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
            (fun z hz => lintegral_ofReal_omegaPart_le hF hz))
      _ = ENNReal.ofReal (∫ z in Work.Spaces.Iz,
            ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) :=
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hF.2
            (Filter.Eventually.of_forall fun z =>
              integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k F z θ)).symm
      _ < ⊤ := ENNReal.ofReal_lt_top
  have hlin : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (E z))
      ≤ ENNReal.ofReal Ccrux
        * ((∫⁻ z in Work.Spaces.Iz, P z) + (∫⁻ z in Work.Spaces.Iz, Q z) * RP) := by
    calc (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (E z))
        ≤ ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal Ccrux * (P z + Q z * RP) :=
          lintegral_mono_ae (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hstep)
      _ = ENNReal.ofReal Ccrux
            * (∫⁻ z in Work.Spaces.Iz, (P z + Q z * RP)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal Ccrux
            * ((∫⁻ z in Work.Spaces.Iz, P z) + (∫⁻ z in Work.Spaces.Iz, Q z * RP)) := by
          rw [lintegral_add_left' hPmeas]
      _ = ENNReal.ofReal Ccrux
            * ((∫⁻ z in Work.Spaces.Iz, P z) + (∫⁻ z in Work.Spaces.Iz, Q z) * RP) := by
          rw [lintegral_mul_const' RP Q hRPne]
  -- ## (4) the two `z`-integrals
  have hPint : (∫⁻ z in Work.Spaces.Iz, P z)
      = ∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2) := by
    have hprod : (volume : Measure (ℝ × ℝ)).restrict Work.Spaces.Dom
        = (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) := by
      rw [Work.Spaces.Dom]
      exact (Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := volume)
        Work.Spaces.Iz Work.Spaces.Iθ).symm
    have h1 : (∫⁻ z in Work.Spaces.Iz, P z)
        = ∫⁻ p, ENNReal.ofReal (omegaPart α k n F p.1 p.2) ∂(volume.restrict Work.Spaces.Dom) := by
      rw [hP, hprod]
      exact (MeasureTheory.lintegral_lintegral (μ := volume.restrict Work.Spaces.Iz)
        (ν := volume.restrict Work.Spaces.Iθ)
        (f := fun z θ : ℝ => ENNReal.ofReal (omegaPart α k n F z θ))
        (aestronglyMeasurable_uncurry_omegaPart (α := α) (k := k) n hsm).aemeasurable)
    have h2 : (∫⁻ p, ENNReal.ofReal (omegaPart α k n F p.1 p.2)
          ∂(volume.restrict Work.Spaces.Dom))
        = ∫⁻ p, (Omega n).indicator
            (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)) p
          ∂(volume.restrict Work.Spaces.Dom) := by
      refine lintegral_congr fun p => ?_
      unfold omegaPart
      by_cases h : p ∈ Omega n <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
    rw [h1, h2, lintegral_indicator (Omega_measurable n)]
    congr 1
    rw [Measure.restrict_restrict (Omega_measurable n), Set.inter_comm]
  have hQint : (∫⁻ z in Work.Spaces.Iz, Q z)
      ≤ ENNReal.ofReal (Cm * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F) := by
    have hI : (volume.restrict (Set.Ioi (0 : ℝ))) = volume.restrict Work.Spaces.Iz := by
      rw [Work.Spaces.Iz]
      exact MeasureTheory.restrict_Ioi_eq_restrict_Ici
    rw [← hI, hQ]
    exact hmom n hn2
  -- ## (5) convert to real numbers
  have hHkSq : Work.Spaces.HkSq α k (err n F)
      = (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (E z)).toReal := by
    rw [hE, Work.Spaces.HkSq]
    exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun z =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k (err n F) z θ)
      (aemeasurable_integral_HkIntegrand (α := α) (k := k) hsmE).aestronglyMeasurable
  have hTn0 : 0 ≤ Tn := by rw [hTn]; exact ENNReal.toReal_nonneg
  have hΛ0 : 0 ≤ Λn := by
    rw [hΛn]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Work.Spaces.HkSq_nonneg α k F)
  rw [hHkSq, hTn, hΛn]
  have hmid1 : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (E z)).toReal
      ≤ Ccrux * ((∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)).toReal
          + (Cm * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F)
              * (RPb)) := by
    calc (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (E z)).toReal
        ≤ (ENNReal.ofReal Ccrux
            * ((∫⁻ z in Work.Spaces.Iz, P z) + (∫⁻ z in Work.Spaces.Iz, Q z) * RP)).toReal :=
          ENNReal.toReal_mono (by
            refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top
              (ne_of_lt (ENNReal.add_lt_top.mpr ⟨hAfin, ?_⟩))
            exact ENNReal.mul_lt_top (lt_of_le_of_lt hQint ENNReal.ofReal_lt_top)
              (lt_top_iff_ne_top.mpr hRPne))
            hlin
      _ = Ccrux * (((∫⁻ z in Work.Spaces.Iz, P z)
            + (∫⁻ z in Work.Spaces.Iz, Q z) * RP).toReal) := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCcrux]
      _ ≤ Ccrux * ((∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)).toReal
            + (Cm * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F)
              * (RPb)) := by
          refine mul_le_mul_of_nonneg_left ?_ hCcrux
          have hQb : (∫⁻ z in Work.Spaces.Iz, Q z).toReal
              ≤ Cm * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F := by
            refine le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top hQint) ?_
            rw [ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg hCm
              (Real.rpow_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg n)) _))
              (Work.Spaces.HkSq_nonneg α k F))]
          have hRPb' : RP.toReal ≤ RPb := by
            refine le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top hRP) ?_
            rw [ENNReal.toReal_ofReal hRPb]
          have hnn : 0 ≤ Cm * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F :=
            mul_nonneg (mul_nonneg hCm (Real.rpow_nonneg
              (div_nonneg (by norm_num) (Nat.cast_nonneg n)) _))
              (Work.Spaces.HkSq_nonneg α k F)
          calc ((∫⁻ z in Work.Spaces.Iz, P z) + (∫⁻ z in Work.Spaces.Iz, Q z) * RP).toReal
              ≤ (∫⁻ z in Work.Spaces.Iz, P z).toReal
                + ((∫⁻ z in Work.Spaces.Iz, Q z) * RP).toReal := ENNReal.toReal_add_le
            _ = (∫⁻ z in Work.Spaces.Iz, P z).toReal
                + (∫⁻ z in Work.Spaces.Iz, Q z).toReal * RP.toReal := by
                rw [ENNReal.toReal_mul]
            _ = (∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
                    ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)).toReal
                + (∫⁻ z in Work.Spaces.Iz, Q z).toReal * RP.toReal := by rw [hPint]
            _ ≤ (∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
                    ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)).toReal
                + (Cm * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F)
                  * (RPb) := by
                refine add_le_add le_rfl ?_
                calc (∫⁻ z in Work.Spaces.Iz, Q z).toReal * RP.toReal
                    ≤ (Cm * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F)
                      * RP.toReal := mul_le_mul_of_nonneg_right hQb ENNReal.toReal_nonneg
                  _ ≤ (Cm * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F)
                      * (RPb) := mul_le_mul_of_nonneg_left hRPb' hnn
  have h2 : 0 ≤ (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F :=
    mul_nonneg (Real.rpow_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg n)) _)
      (Work.Spaces.HkSq_nonneg α k F)
  have hCκ : Cm * RPb ≤ κ := by
    rw [hκdef]
    nlinarith [mul_nonneg hCm hRPb]
  have haux : Ccrux * ((∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)).toReal
        + (Cm * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F)
          * (RPb))
      ≤ Ccrux * (1 + κ) * ((∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)).toReal
        + (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F) := by
    have hTn1 : (∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)).toReal
        ≤ (1 + κ) * (∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)).toReal := by
      rw [add_mul, one_mul]
      exact le_add_of_nonneg_right (mul_nonneg hκ (ENNReal.toReal_nonneg))
    have hΛ1 : κ * ((2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F)
        ≤ (1 + κ) * ((2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F) := by
      rw [add_mul, one_mul]
      exact le_add_of_nonneg_left h2
    calc Ccrux * ((∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)).toReal
        + (Cm * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F)
          * (RPb))
        = Ccrux * ((∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)).toReal
          + (Cm * (RPb)) * ((2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)
            * Work.Spaces.HkSq α k F)) := by ring
      _ ≤ Ccrux * ((∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)).toReal
          + κ * ((2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F)) := by
          refine mul_le_mul_of_nonneg_left ?_ hCcrux
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hCκ h2)
      _ ≤ Ccrux * (1 + κ) * ((∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)).toReal
          + (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F) := by
          calc Ccrux * ((∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
                ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)).toReal
              + κ * ((2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F))
              ≤ Ccrux * ((1 + κ) * (∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
                  ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)).toReal
                + (1 + κ) * ((2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F)) :=
                mul_le_mul_of_nonneg_left (add_le_add hTn1 hΛ1) hCcrux
            _ = Ccrux * (1 + κ) * ((∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
                  ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)).toReal
                + (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F) := by ring
  exact le_trans hmid1 haux

/-! ## The convergence of the `ℋᵏ`-norm of the error -/

theorem tendsto_HkSq_err (k : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α k F)
    (htr : Work.FTS.PhiStar.ThetaTraces α k F)
    (hFs : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0)
    {Cm RPb : ℝ} (hCm : 0 ≤ Cm) (hRPb : 0 ≤ RPb)
    (hmom : ∀ n : ℕ, 2 ≤ n →
      (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal ((Work.Spaces.w z) ^ 2
          * ∑ m ∈ Finset.range (k + 1),
              (Work.Spaces.DzIter m (fun z' _ : ℝ => mu n F z') z 0) ^ 2))
        ≤ ENNReal.ofReal (Cm * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F))
    (hmem : ∀ n : ℕ, 3 ≤ n → Work.Spaces.HkMem α k (err n F))
    (hRP : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (rhoProf α k θ)) ≤ ENNReal.ofReal RPb) :
    Filter.Tendsto (fun n : ℕ => Work.Spaces.HkSq α k (err n F)) Filter.atTop (nhds 0) := by
  obtain ⟨C, hCpos, hbnd⟩ := HkSq_err_le k α hα hα1 hsm hF htr hFs hCm hRPb hmom hmem hRP
  have hTn : Filter.Tendsto (fun n : ℕ => (∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)).toReal)
      Filter.atTop (nhds 0) :=
    (ENNReal.tendsto_toReal (by simp)).comp (tendsto_lintegral_Omega hF)
  have hΛ : Filter.Tendsto (fun n : ℕ =>
      (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F)
      Filter.atTop (nhds 0) := by
    have hbase : Filter.Tendsto (fun n : ℕ => (2 : ℝ) / (n : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hcont : ContinuousAt (fun x : ℝ => x ^ (2 + Work.Spaces.eta)) 0 :=
      Real.continuousAt_rpow_const 0 _ (Or.inr (by rw [Work.Spaces.eta]; norm_num))
    have h0 : (0 : ℝ) ^ (2 + Work.Spaces.eta) = 0 :=
      Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)
    simpa [h0] using (hcont.tendsto.comp hbase).mul tendsto_const_nhds
  have hlim : Filter.Tendsto (fun n : ℕ => C * ((∫⁻ p in (Omega n ∩ Work.Spaces.Dom),
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)).toReal
      + (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) * Work.Spaces.HkSq α k F))
      Filter.atTop (nhds (C * (0 + 0))) :=
    Filter.Tendsto.const_mul C (hTn.add hΛ)
  rw [add_zero, mul_zero] at hlim
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards with n
    exact Work.Spaces.HkSq_nonneg α k (err n F)
  · filter_upwards [Filter.eventually_ge_atTop 3] with n hn
    exact hbnd n hn

end Work.FTS.PhiStar.Honesty.CptApp
end
end
