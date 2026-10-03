import Mathlib
import Submission.Work.KMTPlan.A6.LowSmallSymDefs
import Submission.Work.KMTAreas.A7.BilinOpLp
import Submission.Work.KMTAreas.A7.BilinOpKhalf
import Submission.Work.KMTAreas.A5.Basic
import Submission.Work.KMTPlan.A6.pieceL2BoundRect
import Submission.Work.KMTAreas.A7.CwTsumLe
import Submission.Work.KMTAreas.A7.ExceptionalSupport
import Submission.Work.KMTAreas.A7.eLpNorm_lintegral_le
import Submission.Work.KMTAreas.A7.kmtEta_deriv_bounds
import Submission.Work.KMTAreas.A7.Tle_varphiNt_bounded
import Submission.Work.KMTAreas.A7.Tle_varphitildeNt_bounded
import Submission.Work.KMTAreas.tsum_inv_sq_shift_le
import Submission.Work.Analysis.Hilbert.ratio_multiplier_lp
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier Work.KMTAreas.A7
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTContract

/-! ## Elementary preliminaries -/

/-- The arithmetic symbol `m_Ẑ` is an average of `q` unit complex numbers, hence has modulus
at most one. -/
theorem mZ_norm_le_one (P : Polynomial ℤ) (q : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) : ‖mZ P q α₁ α₂‖ ≤ 1 := by
  rw [mZ]
  by_cases hq : q = 0
  · subst hq; simp
  · have hqr : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
    have hsum : ‖∑ n ∈ Finset.range q,
        fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖ ≤ (q : ℝ) := by
      calc ‖∑ n ∈ Finset.range q,
            fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖
          ≤ ∑ n ∈ Finset.range q,
              ‖fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖ :=
            norm_sum_le _ _
        _ = ∑ _n ∈ Finset.range q, (1 : ℝ) := by
            refine Finset.sum_congr rfl (fun n _ => ?_)
            rw [norm_mul, fourier_apply, fourier_apply, Circle.norm_coe, Circle.norm_coe, mul_one]
        _ = (q : ℝ) := by simp
    calc ‖(q : ℂ)⁻¹ * ∑ n ∈ Finset.range q,
            fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖
        = ‖(q : ℂ)⁻¹‖ * ‖∑ n ∈ Finset.range q,
            fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖ := norm_mul _ _
      _ = (q : ℝ)⁻¹ * ‖∑ n ∈ Finset.range q,
            fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖ := by
          rw [norm_inv, Complex.norm_natCast]
      _ ≤ (q : ℝ)⁻¹ * (q : ℝ) := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hqr.le)
      _ = 1 := by field_simp

/-- The exact-height arithmetic kernel is bounded by the product of the two cardinalities. -/
theorem arithKernelEx_norm_le (ρ : ℝ) (P : Polynomial ℤ) (q : ℕ) (l₁ l₂ : ℕ)
    (j₁ j₂ : ℤ) :
    ‖arithKernelEx ρ P q l₁ l₂ j₁ j₂‖
      ≤ ((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ) := by
  rw [arithKernelEx]
  calc ‖∑ α₁ ∈ diffFreqs ρ l₁, ∑ α₂ ∈ diffFreqs ρ l₂,
        mZ P q α₁ α₂ * fourier (T := 1) (-j₁) α₁ * fourier (T := 1) (-j₂) α₂‖
      ≤ ∑ α₁ ∈ diffFreqs ρ l₁, ‖∑ α₂ ∈ diffFreqs ρ l₂,
          mZ P q α₁ α₂ * fourier (T := 1) (-j₁) α₁ * fourier (T := 1) (-j₂) α₂‖ :=
        norm_sum_le _ _
    _ ≤ ∑ α₁ ∈ diffFreqs ρ l₁, ∑ α₂ ∈ diffFreqs ρ l₂,
          ‖mZ P q α₁ α₂ * fourier (T := 1) (-j₁) α₁ * fourier (T := 1) (-j₂) α₂‖ :=
        Finset.sum_le_sum (fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ _α₁ ∈ diffFreqs ρ l₁, ∑ _α₂ ∈ diffFreqs ρ l₂, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun α₁ _ => Finset.sum_le_sum (fun α₂ _ => ?_))
        rw [norm_mul, norm_mul, fourier_apply, fourier_apply, Circle.norm_coe, Circle.norm_coe,
          mul_one, mul_one]
        exact mZ_norm_le_one P q α₁ α₂
    _ = ((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]

/-- The cardinality of the exact-height frequency set `(ℚ/ℤ)_l` is bounded by that of
`(ℚ/ℤ)_{≤B}` for `l ≤ B`. -/
theorem diffFreqs_card_le (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {l B : ℕ} (hl : l ≤ B) :
    (diffFreqs ρ l).card ≤ (iwArithFreqs ρ B).card := by
  refine Finset.card_le_card (fun α hα => ?_)
  rw [diffFreqs] at hα
  by_cases h0 : l = 0
  · rw [if_pos h0] at hα
    exact iwArithFreqs_mono hρ hρ1 (Nat.zero_le B) hα
  · rw [if_neg h0] at hα
    exact iwArithFreqs_mono hρ hρ1 hl (Finset.mem_sdiff.mp hα).1

/-- Monotonicity of the small-scale threshold `splitCut ρ L = 2^{2^{⌊2^{2ρL}⌋}}`. -/
theorem splitCut_mono_local (ρ : ℝ) (hρ : 0 ≤ ρ) : Monotone (Work.KMTAreas.A7.splitCut ρ) := by
  intro L M hLM
  rw [Work.KMTAreas.A7.splitCut, Work.KMTAreas.A7.splitCut]
  exact Nat.pow_le_pow_right (by norm_num)
    (Nat.pow_le_pow_right (by norm_num) (Work.KMTAreas.A7.ExcSupport.scaleCount_mono 1 hρ hLM))

/-- The kernel `khalf m P` of the halved average is `ℓ¹(ℤ²)` with mass at most one. -/
theorem khalf_mass_le_one (m : ℕ) (P : Polynomial ℤ) :
    Summable (fun p : ℤ × ℤ => ‖khalf m P p.1 p.2‖) ∧
      (∑' p : ℤ × ℤ, ‖khalf m P p.1 p.2‖) ≤ 1 := by
  have hsupp : ∀ p : ℤ × ℤ,
      p ∉ (Finset.Ioc ((m : ℤ) / 2) (m : ℤ)).image (fun a => (a, P.eval a)) →
      khalf m P p.1 p.2 = 0 := by
    rintro ⟨a, b⟩ hp
    rw [khalf]
    by_cases hc : (m / 2 : ℤ) < a ∧ a ≤ (m : ℤ) ∧ b = P.eval a
    · rw [if_pos hc]; exfalso; apply hp
      obtain ⟨h1, h2, h3⟩ := hc
      exact Finset.mem_image.mpr ⟨a, Finset.mem_Ioc.mpr ⟨h1, h2⟩, by rw [h3]⟩
    · rw [if_neg hc]
  refine ⟨summable_of_ne_finset_zero (fun p hp => by rw [hsupp p hp]; simp), ?_⟩
  set A : Finset ℤ := Finset.Ioc ((m:ℤ)/2) (m:ℤ) with hA
  have h1 : (∑' p : ℤ × ℤ, ‖khalf m P p.1 p.2‖)
      = ∑ a ∈ A, ‖khalf m P a (P.eval a)‖ := by
    rw [tsum_eq_sum (s := A.image (fun a => (a, P.eval a)))
      (fun p hp => by rw [hsupp p hp]; simp)]
    rw [Finset.sum_image]
    intro a _ b _ h
    exact (Prod.ext_iff.mp h).1
  rw [h1]
  have hstep : ∑ a ∈ A, ‖khalf m P a (P.eval a)‖ ≤ ∑ _a ∈ A, ((m:ℝ))⁻¹ := by
    refine Finset.sum_le_sum (fun a _ => ?_)
    rw [khalf]
    split_ifs with _hc
    · rw [norm_inv, Complex.norm_natCast]
    · simp only [norm_zero]; positivity
  refine hstep.trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [hA]
    simp
  · have hcard : (A.card : ℝ) ≤ (m:ℝ) := by
      rw [hA, Int.card_Ioc]
      have h2 : (m:ℤ) - (m:ℤ)/2 ≤ (m:ℤ) := by
        have : (0:ℤ) ≤ (m:ℤ)/2 := Int.ediv_nonneg (Int.natCast_nonneg m) (by norm_num)
        omega
      have := Int.toNat_le.mpr h2
      exact_mod_cast this
    have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
    calc (A.card : ℝ) * ((m:ℝ))⁻¹ ≤ (m:ℝ) * (m:ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right hcard (inv_nonneg.mpr hmpos.le)
      _ = 1 := by field_simp

/-- The Fourier coefficients of the rescaled cutoff `η_{≤c}`, `c ≤ 0`, have a uniformly bounded
`ℓ¹` mass. -/
theorem cw_etaCut_mass_le :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℤ, c ≤ 0 →
      Summable (fun j : ℤ => ‖cw (etaCut kmtEta c) j‖) ∧
      (∑' j : ℤ, ‖cw (etaCut kmtEta c) j‖) ≤ C := by
  obtain ⟨Ccw, _hCcwpos, hCcw⟩ := Work.KMTAreas.A7.CwTsumLe
  obtain ⟨M0, M1, M2, hM0, hM1, hM2, _hcd, hb0, hb1, hb2, hz0, hz1, hz2, _hd1, _hd2⟩ :=
    Work.KMTAreas.A7.kmtEta_deriv_bounds
  have hiter : iteratedDeriv 2 kmtEta = deriv (deriv kmtEta) := by
    rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hη0 : ∀ y : ℝ, ‖kmtEta y‖ ≤ M0 := by
    intro y
    rcases lt_or_ge (1:ℝ) |y| with h | h
    · rw [hz0 y (le_of_lt h), norm_zero]; exact hM0
    · exact hb0 y h
  have hη1 : ∀ y : ℝ, ‖deriv kmtEta y‖ ≤ M1 := by
    intro y
    rcases lt_or_ge (1:ℝ) |y| with h | h
    · rw [hz1 y (le_of_lt h), norm_zero]; exact hM1
    · exact hb1 y h
  have hη2 : ∀ y : ℝ, ‖deriv (deriv kmtEta) y‖ ≤ M2 := by
    intro y
    rw [← hiter]
    rcases lt_or_ge (1:ℝ) |y| with h | h
    · rw [hz2 y (le_of_lt h), norm_zero]; exact hM2
    · exact hb2 y h
  set C0 : ℝ := max M0 (max M1 M2) with _hC0def
  have h0C0 : M0 ≤ C0 := le_max_left _ _
  have h1C0 : M1 ≤ C0 := le_trans (le_max_left _ _) (le_max_right _ _)
  have h2C0 : M2 ≤ C0 := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨max (Ccw * C0) 0 + 1, by positivity, fun c hc => ?_⟩
  set R : ℝ := ((2:ℝ)^c)⁻¹ with hRdef
  have hRpos : 0 < R := by
    rw [hRdef]; exact inv_pos.mpr (zpow_pos (by norm_num : (0:ℝ) < 2) c)
  have hR1 : 1 ≤ R := by
    rw [hRdef, ← zpow_neg]
    exact one_le_zpow₀ (by norm_num : (1:ℝ) ≤ 2) (by omega)
  have hR0 : 0 ≤ C0 := le_trans hM0 h0C0
  have hE : ∀ θ : ℝ, etaCut kmtEta c θ = kmtEta (R * θ) := by
    intro θ
    simp only [etaCut, hRdef, div_eq_mul_inv]
    ring_nf
  have hbd : ∀ θ : ℝ, ‖etaCut kmtEta c θ‖ ≤ C0 := by
    intro θ; rw [hE θ]; exact le_trans (hη0 _) h0C0
  have hbd1 : ∀ θ : ℝ, ‖deriv (etaCut kmtEta c) θ‖ ≤ C0 * R := by
    intro θ
    have hfun : etaCut kmtEta c = fun θ : ℝ => kmtEta (R * θ) := funext hE
    rw [hfun, deriv_comp_mul_left, norm_smul, Real.norm_eq_abs, abs_of_pos hRpos]
    exact (mul_le_mul_of_nonneg_left (le_trans (hη1 _) h1C0) hRpos.le).trans (le_of_eq (by ring))
  have hbd2 : ∀ θ : ℝ, ‖deriv (deriv (etaCut kmtEta c)) θ‖ ≤ C0 * R ^ 2 := by
    intro θ
    have hfun : etaCut kmtEta c = fun θ : ℝ => kmtEta (R * θ) := funext hE
    rw [hfun]
    have h1 : deriv (fun θ : ℝ => kmtEta (R * θ)) = fun θ => R • deriv kmtEta (R * θ) := by
      funext θ; exact deriv_comp_mul_left R kmtEta θ
    rw [h1]
    rw [show (fun θ : ℝ => R • deriv kmtEta (R * θ)) = R • (fun θ => deriv kmtEta (R * θ))
      from rfl]
    rw [deriv_const_smul_field]
    rw [show deriv (fun θ : ℝ => deriv kmtEta (R * θ)) θ
        = R • deriv (deriv kmtEta) (R * θ) from deriv_comp_mul_left R (deriv kmtEta) θ]
    rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hRpos]
    have hM2 := hη2 (R * θ)
    calc R * (R * ‖deriv (deriv kmtEta) (R * θ)‖) ≤ R * (R * M2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hM2 hRpos.le) hRpos.le
      _ ≤ R * (R * C0) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2C0 hRpos.le) hRpos.le
      _ = C0 * R ^ 2 := by ring
  have hsup : ∀ θ : ℝ, 1 / R < |θ| → etaCut kmtEta c θ = 0 := by
    intro θ hθ
    rw [hE θ]
    refine hz0 _ ?_
    have hthis : 1 < R * |θ| := by
      have h2 := mul_lt_mul_of_pos_left hθ hRpos
      rwa [mul_div_cancel₀ _ (ne_of_gt hRpos)] at h2
    rw [abs_mul, abs_of_pos hRpos]
    exact le_of_lt hthis
  obtain ⟨Cd, _hCdpos, hCd⟩ := Work.KMTAreas.A7.cw_etaCut_decay c
  refine ⟨Summable.of_nonneg_of_le (fun j => norm_nonneg _)
    (fun j => (hCd j).trans (le_of_eq (by ring)))
    (Work.KMTAreas.A7.summable_one_div_sq_int.mul_left Cd), ?_⟩
  refine (hCcw (etaCut kmtEta c) C0 R hR0 hR1
    ((Work.KMTAreas.A7.contDiff_etaCut c).of_le (WithTop.coe_le_coe.mpr le_top))
    hbd hbd1 hbd2 hsup).trans ?_
  exact le_trans (le_max_left _ _) (le_add_of_nonneg_right (by norm_num))

/-! ## The `ℓ¹` mass of the kernel of the exact-height IW multipliers `Tm` -/

/-- The `S`-constant of the bump bounds for `φ_{N,k}`. -/
noncomputable def phiS (N k : ℕ) : ℝ :=
  Classical.choose (Classical.choose_spec (varphiNt_bounds N k))

theorem phiS_spec (N k : ℕ) : 0 ≤ phiS N k ∧ ∀ t ∈ Set.Icc (1/2 : ℝ) 1,
    (∀ y : ℝ, Classical.choose (varphiNt_bounds N k) ≤ |y| → varphiNt N k t y = 0) ∧
    ContDiff ℝ 2 (varphiNt N k t) ∧ HasCompactSupport (varphiNt N k t) ∧
    (∫ y, ‖varphiNt N k t y‖) ≤ phiS N k ∧
    (∫ y, ‖iteratedDeriv 2 (varphiNt N k t) y‖) ≤ phiS N k :=
  Classical.choose_spec (Classical.choose_spec (varphiNt_bounds N k))

/-- The decay constant of the Fourier transform of `φ̃_{N,k}`. -/
noncomputable def phiC (P : Polynomial ℤ) (N k : ℕ) : ℝ :=
  Classical.choose (fourierDecay_varphitildeN P.natDegree N k)

theorem phiC_spec (P : Polynomial ℤ) (N k : ℕ) : 0 < phiC P N k ∧ ∀ x : ℝ,
    ‖FourierTransform.fourier (varphitildeN P.natDegree N k) x‖
      ≤ phiC P N k / (1 + |x|)^2 :=
  Classical.choose_spec (fourierDecay_varphitildeN P.natDegree N k)

/-- The shift constant of the modulation `e(P(Nt)ξ)`. -/
noncomputable def KvF (P : Polynomial ℤ) (N : ℕ) : ℝ :=
  (2 * max 1 ((∑ i ∈ Finset.range (P.natDegree + 1), |((P.coeff i : ℤ) : ℝ)|) *
    (1 + (N:ℝ))^P.natDegree) + 1)^2

theorem KvF_nonneg (P : Polynomial ℤ) (N : ℕ) : 0 ≤ KvF P N := by
  rw [KvF]; positivity

/-- The `ℓ¹` mass of the kernel of `Tm ρ l` applied to one of the two bump families of the
small-scale model is uniformly bounded on the rectangle `l ≤ B`, `k ≤ B`, `N ≤ K`. -/
theorem tmKer_mass_bound (P : Polynomial ℤ) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B K : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      (∀ (l k N : ℕ) (t : ℝ), l ≤ B → k ≤ B → N ≤ K → t ∈ Set.Icc (1/2 : ℝ) 1 →
        Summable (fun j : ℤ => ‖tmKer ρ l (varphiNt N k t) j‖) ∧
        (∑' j : ℤ, ‖tmKer ρ l (varphiNt N k t) j‖) ≤ C) ∧
      (∀ (l k N : ℕ) (t : ℝ), l ≤ B → k ≤ B → N ≤ K → t ∈ Set.Icc (1/2 : ℝ) 1 →
        Summable (fun j : ℤ => ‖tmKer ρ l (varphitildeNt P P.natDegree N k t) j‖) ∧
        (∑' j : ℤ, ‖tmKer ρ l (varphitildeNt P P.natDegree N k t) j‖) ≤ C) := by
  classical
  have hDle : ∀ l : ℕ, l ≤ B → ((diffFreqs ρ l).card : ℝ) ≤ ((iwArithFreqs ρ B).card : ℝ) :=
    fun l hl => by exact_mod_cast diffFreqs_card_le ρ hρ hρ1 hl
  set D : ℝ := ((iwArithFreqs ρ B).card : ℝ) with hDdef
  set Rect : Finset (ℕ × ℕ) := (Finset.range (K+1)).product (Finset.range (B+1)) with hRectdef
  have hRectmem : ∀ N k, N ≤ K → k ≤ B → (N, k) ∈ Rect := by
    intro N k hN hk
    rw [hRectdef]
    exact Finset.mem_product.mpr ⟨by rw [Finset.mem_range]; omega,
      by rw [Finset.mem_range]; omega⟩
  have hRectne : Rect.Nonempty := ⟨(0,0), hRectmem 0 0 (Nat.zero_le _) (Nat.zero_le _)⟩
  set SB : ℝ := ∑' j : ℤ, ‖kmtKernWeight j‖ with hSBdef
  have hSB0 : 0 ≤ SB := tsum_nonneg (fun j => norm_nonneg _)
  set C1 : ℝ := Finset.sup' Rect hRectne
    (fun p => (4 * (D * max (phiS p.1 p.2) 0) + 1) * SB) with hC1def
  set C2 : ℝ := Finset.sup' Rect hRectne
    (fun p => (D * max (phiC P p.1 p.2) 0 * max (KvF P p.1) 0) * SB) with hC2def
  refine ⟨max (max C1 C2) 0 + 1, by positivity, ?_, ?_⟩
  · intro l k N t hl hk hN ht
    obtain ⟨_hS0, hSt⟩ := phiS_spec N k
    obtain ⟨_hv, hcdt, hcst, hint1, hint2⟩ := hSt t ht
    have hmax0 : 0 ≤ max (phiS N k) 0 := le_max_right _ _
    have hcd : ((diffFreqs ρ l).card : ℝ) ≤ D := by
      rw [hDdef]; exact hDle l hl
    have hdec : ∀ j : ℤ, ‖tmKer ρ l (varphiNt N k t) j‖
        ≤ (4 * (D * max (phiS N k) 0) + 1) * ‖kmtKernWeight j‖ := by
      intro j
      have h0 := iwKernel_decay_of_bump (diffFreqs ρ l) hcdt hcst hmax0
        (le_trans hint1 (le_max_left _ _)) (le_trans hint2 (le_max_left _ _)) j
      refine h0.trans ?_
      have hmono : 4 * (((diffFreqs ρ l).card : ℝ) * max (phiS N k) 0) + 1
          ≤ 4 * (D * max (phiS N k) 0) + 1 := by
        have := mul_le_mul_of_nonneg_right hcd hmax0
        linarith
      exact mul_le_mul_of_nonneg_right hmono (norm_nonneg _)
    refine ⟨Summable.of_nonneg_of_le (fun j => norm_nonneg _) hdec
      (summable_kmtKernWeight.mul_left _), ?_⟩
    have h1 : (∑' j : ℤ, ‖tmKer ρ l (varphiNt N k t) j‖)
        ≤ (4 * (D * max (phiS N k) 0) + 1) * SB := by
      refine (Summable.tsum_le_tsum hdec (Summable.of_nonneg_of_le (fun j => norm_nonneg _) hdec
        (summable_kmtKernWeight.mul_left _)) (summable_kmtKernWeight.mul_left _)).trans ?_
      rw [tsum_mul_left, hSBdef]
    have hle : (4 * (D * max (phiS N k) 0) + 1) * SB ≤ C1 := by
      rw [hC1def]
      exact Finset.le_sup'
        (f := fun p : ℕ × ℕ => (4 * (D * max (phiS p.1 p.2) 0) + 1) * SB)
        (hRectmem N k hN hk)
    exact h1.trans (hle.trans ((le_max_left _ _).trans ((le_max_left _ _).trans
      (le_add_of_nonneg_right (by norm_num)))))
  · intro l k N t hl hk hN ht
    obtain ⟨hCfpos, hCfdec⟩ := phiC_spec P N k
    set Mv : ℝ := max 1 ((∑ i ∈ Finset.range (P.natDegree + 1), |((P.coeff i : ℤ) : ℝ)|) *
      (1 + (N:ℝ))^P.natDegree) with hMvdef
    have hMv0 : 0 ≤ Mv := le_trans zero_le_one (le_max_left _ _)
    have ht1 : |t| ≤ 1 := by
      obtain ⟨h1, h2⟩ := ht
      rw [abs_le]; exact ⟨by linarith, h2⟩
    have hc : |PevalR P ((N:ℝ) * t)| ≤ Mv :=
      le_trans (abs_PevalR_mul_le P N ht1) (le_max_right _ _)
    have hchar : ∀ y : ℤ,
        ‖∑ α ∈ diffFreqs ρ l, fourier (T := 1) y α‖ ≤ ((diffFreqs ρ l).card : ℝ) := by
      intro y
      calc ‖∑ α ∈ diffFreqs ρ l, fourier (T := 1) y α‖
          ≤ ∑ α ∈ diffFreqs ρ l, ‖fourier (T := 1) y α‖ := norm_sum_le _ _
        _ = ∑ _α ∈ diffFreqs ρ l, (1:ℝ) := by
            refine Finset.sum_congr rfl (fun α _ => ?_)
            rw [fourier_apply]; exact Circle.norm_coe _
        _ = ((diffFreqs ρ l).card : ℝ) := by simp
    have h0 : ∀ j : ℤ, ‖tmKer ρ l (varphitildeNt P P.natDegree N k t) j‖
        ≤ (((diffFreqs ρ l).card : ℝ) * phiC P N k * KvF P N) / (1 + |(j:ℝ)|)^2 := by
      intro j
      rw [tmKer, IwKernelArithChar (diffFreqs ρ l)
          (integrable_varphitildeNt_aux P P.natDegree N k t) j,
        cw_eq_fourierTransform, fourier_varphitildeNt_eq P P.natDegree N k t (j:ℝ)]
      have h2 : ‖FourierTransform.fourier (varphitildeN P.natDegree N k)
            ((j:ℝ) - PevalR P ((N:ℝ)*t))‖ ≤ phiC P N k * KvF P N / (1 + |(j:ℝ)|)^2 := by
        refine (hCfdec _).trans ?_
        have hmaj := one_div_sq_le_of_abs_sub_le hMv0 hc j
        calc phiC P N k / (1 + |(j:ℝ) - PevalR P ((N:ℝ)*t)|)^2
            = phiC P N k * (1 / (1 + |(j:ℝ) - PevalR P ((N:ℝ)*t)|)^2) :=
              div_eq_mul_one_div _ _
          _ ≤ phiC P N k * (KvF P N / (1 + |(j:ℝ)|)^2) := by
              refine mul_le_mul_of_nonneg_left ?_ hCfpos.le
              have hmaj' := hmaj
              rw [hMvdef] at hmaj'
              exact hmaj'
          _ = phiC P N k * KvF P N / (1 + |(j:ℝ)|)^2 := (mul_div_assoc _ _ _).symm
      calc ‖(∑ α ∈ diffFreqs ρ l, fourier (T := 1) (-j) α) *
              FourierTransform.fourier (varphitildeN P.natDegree N k)
                ((j:ℝ) - PevalR P ((N:ℝ)*t))‖
          = ‖∑ α ∈ diffFreqs ρ l, fourier (T := 1) (-j) α‖ *
              ‖FourierTransform.fourier (varphitildeN P.natDegree N k)
                ((j:ℝ) - PevalR P ((N:ℝ)*t))‖ := norm_mul _ _
        _ ≤ ((diffFreqs ρ l).card : ℝ) * (phiC P N k * KvF P N / (1 + |(j:ℝ)|)^2) :=
            mul_le_mul (hchar (-j)) h2 (norm_nonneg _) (Nat.cast_nonneg _)
        _ = ((diffFreqs ρ l).card : ℝ) * phiC P N k * KvF P N / (1 + |(j:ℝ)|)^2 := by ring
    have hdec : ∀ j : ℤ, ‖tmKer ρ l (varphitildeNt P P.natDegree N k t) j‖
        ≤ (D * max (phiC P N k) 0 * max (KvF P N) 0) * ‖kmtKernWeight j‖ := by
      intro j
      refine (h0 j).trans ?_
      rw [norm_kmtKernWeight, div_eq_mul_one_div]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have hD0' : (0:ℝ) ≤ D := by rw [hDdef]; positivity
      have hcd : ((diffFreqs ρ l).card : ℝ) ≤ D := by rw [hDdef]; exact hDle l hl
      refine mul_le_mul (mul_le_mul hcd (le_max_left _ _) hCfpos.le hD0')
        (le_max_left _ _) (KvF_nonneg P N) ?_
      exact mul_nonneg hD0' (le_max_right _ _)
    refine ⟨Summable.of_nonneg_of_le (fun j => norm_nonneg _) hdec
      (summable_kmtKernWeight.mul_left _), ?_⟩
    have h1 : (∑' j : ℤ, ‖tmKer ρ l (varphitildeNt P P.natDegree N k t) j‖)
        ≤ (D * max (phiC P N k) 0 * max (KvF P N) 0) * SB := by
      refine (Summable.tsum_le_tsum hdec (Summable.of_nonneg_of_le (fun j => norm_nonneg _) hdec
        (summable_kmtKernWeight.mul_left _)) (summable_kmtKernWeight.mul_left _)).trans ?_
      rw [tsum_mul_left, hSBdef]
    have hle : (D * max (phiC P N k) 0 * max (KvF P N) 0) * SB ≤ C2 := by
      rw [hC2def]
      exact Finset.le_sup'
        (f := fun p : ℕ × ℕ => (D * max (phiC P p.1 p.2) 0 * max (KvF P p.1) 0) * SB)
        (hRectmem N k hN hk)
    exact h1.trans (hle.trans ((le_max_right _ _).trans ((le_max_left _ _).trans
      (le_add_of_nonneg_right (by norm_num)))))

/-- The final arithmetic of the constants: combining the two bounds. -/
theorem const_combine (c b : ℝ) (hc : 0 ≤ c) (hb : 0 ≤ b) (X Y : ℝ≥0∞) :
    ENNReal.ofReal (c*c) * X * Y + ENNReal.ofReal b * X * Y
      ≤ ENNReal.ofReal (max 1 (c*c + b)) * X * Y := by
  rw [← add_mul, ← add_mul, ← ENNReal.ofReal_add (by positivity) hb]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (ENNReal.ofReal_le_ofReal (le_max_right _ _)) bot_le) bot_le

/-- Frequency bound for a multiple of a bounded frequency: if `d * B₀ ≤ KB` and
`-(B₀:ℤ) ≤ X ≤ (B₀:ℤ)` then `d * X ∈ [-KB, KB]`. -/
theorem freqBound_mul (d : ℕ) {B₀ KB : ℕ} (hdKB : d * B₀ ≤ KB) {X : ℤ}
    (hX : -((B₀:ℤ)) ≤ X) (hX₂ : X ≤ (B₀:ℤ)) :
    -((KB:ℤ)) ≤ (d:ℤ) * X ∧ (d:ℤ) * X ≤ (KB:ℤ) := by
  have hd0 : (0:ℤ) ≤ (d:ℤ) := Int.natCast_nonneg _
  have h1 : (d:ℤ) * (-(B₀:ℤ)) ≤ (d:ℤ) * X := mul_le_mul_of_nonneg_left hX hd0
  have h2 : (d:ℤ) * X ≤ (d:ℤ) * (B₀:ℤ) := mul_le_mul_of_nonneg_left hX₂ hd0
  have h3 : (d:ℤ) * (B₀:ℤ) ≤ (KB:ℤ) := by exact_mod_cast hdKB
  have h4 : -((KB:ℤ)) ≤ (d:ℤ) * (-(B₀:ℤ)) := by
    rw [show (d:ℤ) * (-(B₀:ℤ)) = -((d:ℤ) * (B₀:ℤ)) by ring]
    omega
  exact ⟨le_trans h4 h1, le_trans h2 h3⟩

/-! ## The crude bound -/

theorem lowSmall_crude_bound (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (C₀ : ℕ) (B : ℕ) :
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ M : ℝ, 0 < M ∧ ∀ (Λ : NNReal) (a : ℕ → NNReal)
      (l₁ l₂ k₁ k₂ n : ℕ) (f g : ℤ → ℂ),
      1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ m, 1 ≤ a m) →
      MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
      MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
      Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ ≤ B →
      Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n →
      Work.KMTAreas.A7.mainRegime ρ k₁ k₂ (Nat.floor (a n)) →
      (max k₁ k₂ + 2 * Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) + 1
        ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat) →
      MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTPlan.A6.colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
          - Work.KMTPlan.A6.lowModel ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) 1 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal M * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  intro ρ hρ hρ1
  set Kthr : ℕ := splitCut ρ B with hKthrdef
  set LgN : ℕ := (Work.Analysis.EndVar.logN Kthr).toNat with hLgNdef
  set B₀ : ℕ := max B (LgN + (B + 2)) with hB₀def
  set KB : ℕ := (P.natDegree + 1) * (B₀ + 1) with hKBdef
  obtain ⟨Cpc, _hCpcpos, hCpc⟩ := pieceL2BoundRect ρ B₀ KB
  obtain ⟨Cw, hCwpos, hCw⟩ := cw_etaCut_mass_le
  obtain ⟨Ctm, _hCtmpos, hCtm⟩ := tmKer_mass_bound P ρ hρ hρ1 B Kthr
  set D : ℝ := ((iwArithFreqs ρ B).card : ℝ) with hDdef
  refine ⟨max 1 ((Cpc:ℝ) * (Cpc:ℝ) + (D*D*Cw*Cw)*(Ctm*Ctm)),
    lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro Λ a l₁ l₂ k₁ k₂ n f g _hΛ _ha _ha1 _hf _hg hlc hset _hreg _hthr
  have hBB₀ : B ≤ B₀ := by rw [hB₀def]; exact le_max_left _ _
  have hB₀KB : B₀ ≤ KB := by
    rw [hKBdef]
    calc B₀ = 1 * B₀ := (one_mul _).symm
      _ ≤ (P.natDegree + 1) * B₀ := Nat.mul_le_mul (Nat.le_add_left 1 P.natDegree) (le_refl B₀)
      _ ≤ (P.natDegree + 1) * (B₀ + 1) := Nat.mul_le_mul_left _ (Nat.le_succ B₀)
  have hLgB₀ : LgN ≤ B₀ := by
    rw [hB₀def]; exact le_trans (Nat.le_add_right LgN (B + 2)) (le_max_right _ _)
  have hLg1B₀ : LgN + 1 ≤ B₀ := by
    rw [hB₀def]; exact le_trans (Nat.add_le_add_left (by omega) LgN) (le_max_right _ _)
  have hdKB : P.natDegree * B₀ ≤ KB := by
    rw [hKBdef]
    exact le_trans (Nat.mul_le_mul (Nat.le_add_right P.natDegree 1) (le_refl B₀))
      (Nat.mul_le_mul_left _ (Nat.le_succ B₀))
  have hNK : Nat.floor (a n) ≤ Kthr := by
    rw [hKthrdef]
    exact le_trans hset.2 (splitCut_mono_local ρ hρ.le hlc)
  have hlog : Work.Analysis.EndVar.logN (Nat.floor (a n)) ≤ (LgN : ℤ) := by
    have h1 : Work.Analysis.EndVar.logN (Nat.floor (a n)) ≤ Work.Analysis.EndVar.logN Kthr :=
      Work.Analysis.EndVar.logN_mono hNK
    have h2 : Work.Analysis.EndVar.logN Kthr ≤ (LgN : ℤ) := by
      rw [hLgNdef]; exact Int.self_le_toNat _
    linarith
  have hlog0 : (0:ℤ) ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)) :=
    Work.Analysis.EndVar.logN_nonneg _
  have hlc₁ : l₁ ≤ B :=
    le_trans (by rw [lcL]; exact le_trans (le_max_left _ _) (le_max_left _ _)) hlc
  have hlc₂ : l₂ ≤ B :=
    le_trans (by rw [lcL]; exact le_trans (le_max_right _ _) (le_max_left _ _)) hlc
  have hlk₁ : k₁ ≤ B :=
    le_trans (by rw [lcL]; exact le_trans (le_max_left _ _) (le_max_right _ _)) hlc
  have hlk₂ : k₂ ≤ B :=
    le_trans (by rw [lcL]; exact le_trans (le_max_right _ _) (le_max_right _ _)) hlc
  have hl₁B₀ : l₁ ≤ B₀ := le_trans hlc₁ hBB₀
  have hl₂B₀ : l₂ ≤ B₀ := le_trans hlc₂ hBB₀
  -- the frequency memberships of the two pieces
  have hfrF1 : -(Work.Analysis.EndVar.logN (Nat.floor (a n))) + (k₁:ℤ)
      ∈ Finset.Icc (-(KB:ℤ)) (KB:ℤ) := by
    rw [Finset.mem_Icc]
    have h := freqBound_mul 1 (B₀ := B₀) (KB := KB) (by simpa using hB₀KB)
      (X := -(Work.Analysis.EndVar.logN (Nat.floor (a n))) + (k₁:ℤ))
      (by omega) (by omega)
    simpa using h
  have hfrF2 : -(Work.Analysis.EndVar.logN (Nat.floor (a n))) + ((k₁:ℤ) - 1)
      ∈ Finset.Icc (-(KB:ℤ)) (KB:ℤ) := by
    rw [Finset.mem_Icc]
    have h := freqBound_mul 1 (B₀ := B₀) (KB := KB) (by simpa using hB₀KB)
      (X := -(Work.Analysis.EndVar.logN (Nat.floor (a n))) + ((k₁:ℤ) - 1))
      (by omega) (by omega)
    simpa using h
  have hfrG1 : (P.natDegree : ℤ) * (-(Work.Analysis.EndVar.logN (Nat.floor (a n))) + (k₂:ℤ))
      ∈ Finset.Icc (-(KB:ℤ)) (KB:ℤ) := by
    rw [Finset.mem_Icc]
    exact freqBound_mul P.natDegree (B₀ := B₀) (KB := KB) hdKB
      (X := -(Work.Analysis.EndVar.logN (Nat.floor (a n))) + (k₂:ℤ))
      (by omega) (by omega)
  have hfrG2 : (P.natDegree : ℤ) * (-(Work.Analysis.EndVar.logN (Nat.floor (a n)))
      + ((k₂:ℤ) - 1)) ∈ Finset.Icc (-(KB:ℤ)) (KB:ℤ) := by
    rw [Finset.mem_Icc]
    exact freqBound_mul P.natDegree (B₀ := B₀) (KB := KB) hdKB
      (X := -(Work.Analysis.EndVar.logN (Nat.floor (a n))) + ((k₂:ℤ) - 1))
      (by omega) (by omega)
  -- the two pieces of the concrete column
  set U : ℤ → ℂ := Work.Analysis.EndVar.Fpiece (kmtPj ρ) 0 l₁ (k₁:ℤ) (Nat.floor (a n)) f
    with hUdef
  set V : ℤ → ℂ := Work.Analysis.EndVar.Gpiece (kmtPj ρ) (P.natDegree:ℤ) 0 l₂ (k₂:ℤ)
    (Nat.floor (a n)) g with hVdef
  have hU : eLpNorm U 2 Measure.count ≤ ENNReal.ofReal (Cpc:ℝ) * eLpNorm f 2 Measure.count := by
    rw [hUdef, Work.Analysis.EndVar.Fpiece_eq]
    have h1 := hCpc l₁ (fun s : ℤ => -(Work.Analysis.EndVar.logN (Nat.floor (a n))) + s) 0
      (k₁:ℤ) f hl₁B₀ hfrF1 hfrF2
    rwa [← ENNReal.ofReal_coe_nnreal] at h1
  have hV : eLpNorm V 2 Measure.count ≤ ENNReal.ofReal (Cpc:ℝ) * eLpNorm g 2 Measure.count := by
    rw [hVdef, Work.Analysis.EndVar.Gpiece_eq]
    have h1 := hCpc l₂ (fun s : ℤ => (P.natDegree : ℤ) *
      (-(Work.Analysis.EndVar.logN (Nat.floor (a n))) + s)) 0 (k₂:ℤ) g hl₂B₀ hfrG1 hfrG2
    rwa [← ENNReal.ofReal_coe_nnreal] at h1
  -- the concrete column is a bilinear convolution
  have hcol_pt : ∀ x : ℤ, ‖colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x‖
      ≤ ‖bilinOp (khalf (Nat.floor (a n)) P) U V x‖ := by
    intro x
    by_cases hs : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n
    · have h1 := colSmall_eq_varpCol_on ρ P C₀ a f g l₁ l₂ k₁ k₂ n x hs
      have h2 := Work.Analysis.EndVar.varpCol_eq_piece (Pj := kmtPj ρ) (P := P)
        (d := P.natDegree) (C₀ := C₀) (a := a) (f := f) (g := g) (l₁ := l₁) (l₂ := l₂)
        (k₁ := k₁) (k₂ := k₂) (n := n) (x := x)
        (Work.Analysis.EndVar.inIndexSet_iff_le.mp hs.1)
      have h3 : Work.Analysis.EndVar.varpPiece (kmtPj ρ) P P.natDegree (a n) f g l₁ l₂ k₁ k₂ x
          = bilinOp (khalf (Nat.floor (a n)) P) U V x := by
        show AhalfR TZ (a n) Polynomial.X P
          (Work.Analysis.EndVar.Fpiece (kmtPj ρ) 0 l₁ (k₁:ℤ) (Nat.floor (a n)) f)
          (Work.Analysis.EndVar.Gpiece (kmtPj ρ) (P.natDegree:ℤ) 0 l₂ (k₂:ℤ)
            (Nat.floor (a n)) g) x = bilinOp (khalf (Nat.floor (a n)) P) U V x
        exact congrFun (BilinOpKhalf (a n) P U V) x
      rw [h1, h2, h3]
    · rw [colSmall_eq_zero_of_not ρ P C₀ a f g l₁ l₂ k₁ k₂ n x hs, norm_zero]
      exact norm_nonneg _
  have hcol : eLpNorm (fun x : ℤ => colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) 1 Measure.count
      ≤ ENNReal.ofReal ((Cpc:ℝ) * (Cpc:ℝ)) * eLpNorm f 2 Measure.count
          * eLpNorm g 2 Measure.count := by
    refine (eLpNorm_mono (hf := by pw_aesm) hcol_pt).trans ?_
    refine (BilinOpLp (K := khalf (Nat.floor (a n)) P) (u := U) (v := V)
      (p := 1) (p₁ := 2) (p₂ := 2) ?_ le_rfl (khalf_mass_le_one _ P).1).trans ?_
    · rw [ENNReal.inv_two_add_inv_two, inv_one]
    · have hmass : ENNReal.ofReal (∑' q : ℤ × ℤ, ‖khalf (Nat.floor (a n)) P q.1 q.2‖) ≤ 1 := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (khalf_mass_le_one (Nat.floor (a n)) P).2
      calc ENNReal.ofReal (∑' q : ℤ × ℤ, ‖khalf (Nat.floor (a n)) P q.1 q.2‖)
            * eLpNorm U 2 Measure.count * eLpNorm V 2 Measure.count
          ≤ 1 * (ENNReal.ofReal (Cpc:ℝ) * eLpNorm f 2 Measure.count)
              * (ENNReal.ofReal (Cpc:ℝ) * eLpNorm g 2 Measure.count) :=
            mul_le_mul' (mul_le_mul' hmass hU) hV
        _ = ENNReal.ofReal ((Cpc:ℝ) * (Cpc:ℝ)) * eLpNorm f 2 Measure.count
              * eLpNorm g 2 Measure.count := by
            rw [one_mul, mul_mul_mul_comm,
              ← ENNReal.ofReal_mul (show (0:ℝ) ≤ (Cpc:ℝ) by positivity)]
            ring
  -- the model column
  set u : ℕ := uScale ρ (lcL l₁ l₂ k₁ k₂) with _hudef
  set Fl : ℝ → ℤ → ℂ := fun t x => BtwistEx ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
      (Tm ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f)
      (Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x with _hFldef
  have hlow_pt : ∀ x : ℤ, ‖lowModel ρ P C₀ a f g l₁ l₂ k₁ k₂ n x‖ₑ
      ≤ ∫⁻ t in Set.Ioc (1/2 : ℝ) 1, ‖Fl t x‖ₑ := by
    intro x
    rw [lowModel_apply]
    by_cases hs : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n
    · rw [if_pos hs]
      rw [intervalIntegral.integral_of_le (by norm_num : (1/2:ℝ) ≤ 1)]
      exact enorm_integral_le_lintegral_enorm (fun t : ℝ => Fl t x)
    · rw [if_neg hs]
      simp
  -- the two `cw` masses of the window `m_*`
  have hc0 : -(2 * (u:ℤ)) ≤ 0 := by
    have : (0:ℤ) ≤ 2 * (u:ℤ) := by positivity
    omega
  have hc1 : -((P.natDegree:ℤ) * 2 * (u:ℤ)) ≤ 0 := by
    have : (0:ℤ) ≤ (P.natDegree:ℤ) * 2 * (u:ℤ) := by positivity
    omega
  have hcw1sum : Summable (fun a' : ℤ => ‖cw (mStarF u) a'‖) := (hCw _ hc0).1
  have hcw2sum : Summable (fun b' : ℤ => ‖cw (mStargF P.natDegree u) b'‖) := (hCw _ hc1).1
  have hcw1le : (∑' a' : ℤ, ‖cw (mStarF u) a'‖) ≤ Cw := (hCw _ hc0).2
  have hcw2le : (∑' b' : ℤ, ‖cw (mStargF P.natDegree u) b'‖) ≤ Cw := (hCw _ hc1).2
  -- the mass of the kernel of the twisted bilinear multiplier
  have hD0 : (0:ℝ) ≤ D := by rw [hDdef]; exact Nat.cast_nonneg _
  have hkerbound : ∀ q : ℤ × ℤ, ‖arithKerM ρ P l₁ l₂ k₁ k₂ q.1 q.2‖
      ≤ (D * D) * (‖cw (mStarF u) q.1‖ * ‖cw (mStargF P.natDegree u) q.2‖) := by
    intro q
    have h1 : ‖arithKernelEx ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ q.1 q.2‖ ≤ D * D := by
      refine (arithKernelEx_norm_le ρ P _ l₁ l₂ q.1 q.2).trans ?_
      have hh₁ : ((diffFreqs ρ l₁).card : ℝ) ≤ D := by
        rw [hDdef]; exact_mod_cast diffFreqs_card_le ρ hρ hρ1 hlc₁
      have hh₂ : ((diffFreqs ρ l₂).card : ℝ) ≤ D := by
        rw [hDdef]; exact_mod_cast diffFreqs_card_le ρ hρ hρ1 hlc₂
      exact mul_le_mul hh₁ hh₂ (Nat.cast_nonneg _) (by rw [hDdef]; positivity)
    rw [arithKerM, norm_mul, norm_mul]
    calc ‖arithKernelEx ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ q.1 q.2‖
          * ‖cw (mStarF u) q.1‖ * ‖cw (mStargF P.natDegree u) q.2‖
        ≤ ((D * D) * ‖cw (mStarF u) q.1‖) * ‖cw (mStargF P.natDegree u) q.2‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
            (norm_nonneg _)
      _ = (D * D) * (‖cw (mStarF u) q.1‖ * ‖cw (mStargF P.natDegree u) q.2‖) := by ring
  have hprodsum : Summable (fun q : ℤ × ℤ =>
      ‖cw (mStarF u) q.1‖ * ‖cw (mStargF P.natDegree u) q.2‖) :=
    hcw1sum.mul_of_nonneg hcw2sum (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hker_sum : Summable (fun q : ℤ × ℤ => ‖arithKerM ρ P l₁ l₂ k₁ k₂ q.1 q.2‖) := by
    refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) hkerbound ?_
    exact hprodsum.mul_left _
  have hprodtsum : (∑' q : ℤ × ℤ,
        ‖cw (mStarF u) q.1‖ * ‖cw (mStargF P.natDegree u) q.2‖)
      = (∑' a' : ℤ, ‖cw (mStarF u) a'‖)
        * (∑' b' : ℤ, ‖cw (mStargF P.natDegree u) b'‖) := by
    rw [Summable.tsum_prod' hprodsum (fun a' => hcw2sum.mul_left (‖cw (mStarF u) a'‖))]
    dsimp only
    rw [tsum_congr (fun b : ℤ => hcw2sum.tsum_mul_left (‖cw (mStarF u) b‖))]
    exact hcw1sum.tsum_mul_right _
  have hker_mass : (∑' q : ℤ × ℤ, ‖arithKerM ρ P l₁ l₂ k₁ k₂ q.1 q.2‖) ≤ D*D*Cw*Cw := by
    calc (∑' q : ℤ × ℤ, ‖arithKerM ρ P l₁ l₂ k₁ k₂ q.1 q.2‖)
        ≤ ∑' q : ℤ × ℤ, (D * D)
            * (‖cw (mStarF u) q.1‖ * ‖cw (mStargF P.natDegree u) q.2‖) :=
          Summable.tsum_le_tsum hkerbound hker_sum (hprodsum.mul_left _)
      _ = (D * D) * ((∑' a' : ℤ, ‖cw (mStarF u) a'‖)
            * (∑' b' : ℤ, ‖cw (mStargF P.natDegree u) b'‖)) := by
          rw [hprodsum.tsum_mul_left (D*D), hprodtsum]
      _ ≤ (D * D) * (Cw * Cw) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul hcw1le hcw2le
            (tsum_nonneg (fun _ => norm_nonneg _)) hCwpos.le) (mul_nonneg hD0 hD0)
      _ = D*D*Cw*Cw := by ring
  have hlow : eLpNorm (fun x : ℤ => lowModel ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) 1 Measure.count
      ≤ ENNReal.ofReal ((D*D*Cw*Cw)*(Ctm*Ctm)) * eLpNorm f 2 Measure.count
          * eLpNorm g 2 Measure.count := by
    refine (eLpNorm_mono_enorm (hf := by pw_aesm) (f := fun x : ℤ => lowModel ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
      (g := fun x : ℤ => ∫⁻ t in Set.Ioc (1/2 : ℝ) 1, ‖Fl t x‖ₑ)
      (fun x => by simpa only [enorm_eq_self] using hlow_pt x)).trans ?_
    refine Work.KMTAreas.A7.eLpNorm_lintegral_le 1 le_rfl (fun t x => ‖Fl t x‖ₑ) _ ?_
    intro t ht
    have htI : t ∈ Set.Icc (1/2 : ℝ) 1 := ⟨le_of_lt ht.1, ht.2⟩
    rw [eLpNorm_enorm (hf := by pw_aesm)]
    have hFt : Fl t = bilinOp (arithKerM ρ P l₁ l₂ k₁ k₂)
        (Tm ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f)
        (Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) := by
      funext x
      exact BtwistEx_eq_bilinOp ρ P l₁ l₂ k₁ k₂
        (Tm ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f)
        (Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x
    rw [hFt]
    have hTm1 : eLpNorm (Tm ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f) 2 Measure.count
        ≤ ENNReal.ofReal Ctm * eLpNorm f 2 Measure.count := by
      obtain ⟨hsum1, hle1⟩ := hCtm.1 l₁ k₁ (Nat.floor (a n)) t hlc₁ hlk₁ hNK htI
      rw [Tm_eq_convOp]
      have hstep := Work.Analysis.Hilbert.eLpNorm_conv_count_le (p := 2) (by norm_num)
        (tmKer ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t)) f
      rw [ENNReal.ofReal_ofNat] at hstep
      refine hstep.trans ?_
      have hof : (∑' z : ℤ, ENNReal.ofReal ‖tmKer ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) z‖)
          = ENNReal.ofReal (∑' z : ℤ,
              ‖tmKer ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) z‖) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun z => norm_nonneg _) hsum1).symm
      rw [hof]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal hle1) le_rfl
    have hTm2 : eLpNorm (Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) 2
        Measure.count ≤ ENNReal.ofReal Ctm * eLpNorm g 2 Measure.count := by
      obtain ⟨hsum2, hle2⟩ := hCtm.2 l₂ k₂ (Nat.floor (a n)) t hlc₂ hlk₂ hNK htI
      rw [Tm_eq_convOp]
      have hstep := Work.Analysis.Hilbert.eLpNorm_conv_count_le (p := 2) (by norm_num)
        (tmKer ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t)) g
      rw [ENNReal.ofReal_ofNat] at hstep
      refine hstep.trans ?_
      have hof : (∑' z : ℤ, ENNReal.ofReal
            ‖tmKer ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) z‖)
          = ENNReal.ofReal (∑' z : ℤ,
              ‖tmKer ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) z‖) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun z => norm_nonneg _) hsum2).symm
      rw [hof]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal hle2) le_rfl
    refine (BilinOpLp (K := arithKerM ρ P l₁ l₂ k₁ k₂)
      (u := Tm ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f)
      (v := Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g)
      (p := 1) (p₁ := 2) (p₂ := 2) ?_ le_rfl hker_sum).trans ?_
    · rw [ENNReal.inv_two_add_inv_two, inv_one]
    · calc ENNReal.ofReal (∑' q : ℤ × ℤ, ‖arithKerM ρ P l₁ l₂ k₁ k₂ q.1 q.2‖)
            * eLpNorm (Tm ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f) 2 Measure.count
            * eLpNorm (Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) 2
                Measure.count
          ≤ ENNReal.ofReal (D*D*Cw*Cw)
              * (ENNReal.ofReal Ctm * eLpNorm f 2 Measure.count)
              * (ENNReal.ofReal Ctm * eLpNorm g 2 Measure.count) :=
            mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal hker_mass) hTm1) hTm2
        _ = ENNReal.ofReal (D*D*Cw*Cw) * (ENNReal.ofReal Ctm * ENNReal.ofReal Ctm)
              * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by ring
        _ = ENNReal.ofReal ((D*D*Cw*Cw)*(Ctm*Ctm)) * eLpNorm f 2 Measure.count
              * eLpNorm g 2 Measure.count := by
            rw [← ENNReal.ofReal_mul (show (0:ℝ) ≤ Ctm by positivity),
              ← ENNReal.ofReal_mul (show (0:ℝ) ≤ D*D*Cw*Cw by positivity)]
  -- assembling the two halves
  have hsub : eLpNorm (fun x : ℤ => colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
        - lowModel ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) 1 Measure.count
      ≤ ENNReal.ofReal ((Cpc:ℝ) * (Cpc:ℝ)) * eLpNorm f 2 Measure.count
          * eLpNorm g 2 Measure.count
        + ENNReal.ofReal ((D*D*Cw*Cw)*(Ctm*Ctm)) * eLpNorm f 2 Measure.count
          * eLpNorm g 2 Measure.count :=
    (eLpNorm_sub_le (by norm_num)).trans
      (add_le_add hcol hlow)
  exact hsub.trans (const_combine (Cpc:ℝ) ((D*D*Cw*Cw)*(Ctm*Ctm)) (by positivity)
    (by positivity) _ _)

end

end Work.KMTPlan.A6
