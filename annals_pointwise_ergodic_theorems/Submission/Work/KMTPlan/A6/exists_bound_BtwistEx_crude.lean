import Mathlib
import Submission.Work.KMTPlan.A6.LowSmallDefs
import Submission.Work.KMTAreas.A7.BilinOpLp
import Submission.Work.KMTAreas.A7.CwTsumLe
import Submission.Work.KMTAreas.A7.kmtEta_deriv_bounds
import Submission.Work.KMTAreas.A7.Tle_varphitildeNt_bounded

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# The crude `l¹ → l² × l²` bound for the twisted bilinear multiplier `BtwistEx`

`Work.KMTPlan.A6.BtwistEx ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u) h k` is the bilinear
convolution of `h` and `k` with the kernel

  `K_u(j₁,j₂) = arithKernelEx ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ j₁ j₂ · cw (mStarF u) j₁
                   · cw (mStargF P.natDegree u) j₂`.

The arithmetic factor is a *finite* double sum of terms of modulus at most one, so
`‖arithKernelEx …‖ ≤ |(ℚ/ℤ)_{l₁}| · |(ℚ/ℤ)_{l₂}|` uniformly in every variable; the two remaining
factors are the Fourier coefficients of the §6 windows `m_* = η_{≤-2u}` and
`m̃_* = η_{≤-2du}`, whose `ℓ¹`-masses are bounded by an **absolute constant, uniformly in `u`**
(the crude multiplier estimate `Work.KMTAreas.A7.CwTsumLe`, applied to a bump of inverse width
`R = 2^{2u} ≥ 1`; the dilation of `η` contributes exactly the factors `R`, `R²` that the three
hypotheses of `CwTsumLe` ask for).

The kernel is therefore an `ℓ¹(ℤ²)` kernel whose mass is bounded uniformly in `u`, and Young's
inequality for the bilinear convolution (`Work.KMTAreas.A7.BilinOpLp` at `(p,p₁,p₂) = (1,2,2)`)
gives the bound `‖BtwistEx … h k‖_{ℓ¹} ≤ C ‖h‖_{ℓ²} ‖k‖_{ℓ²}` with `C` independent of `u`.

This is the *crude* (no gain) counterpart of the small-scale estimate `ssuBtwistEx`, and is the
statement requested as `Work.KMTPlan.A6.exists_bound_BtwistEx_crude`.
-/

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.KMTAreas.A7

/-! ## The chain rule for right dilations -/

private lemma absc_deriv_comp_mul_left (f : ℝ → ℂ) (c : ℝ) :
    deriv (fun y : ℝ => f (c * y)) = fun y => (c : ℂ) * deriv f (c * y) := by
  funext y
  rw [deriv_comp_mul_left, Complex.real_smul]

private lemma absc_deriv_deriv_comp_mul_left (f : ℝ → ℂ) (c x : ℝ) :
    deriv (deriv (fun y : ℝ => f (c * y))) x
      = (c : ℂ) * ((c : ℂ) * deriv (deriv f) (c * x)) := by
  rw [absc_deriv_comp_mul_left f c, deriv_const_mul_field, deriv_comp_mul_left,
    Complex.real_smul]

private lemma absc_iteratedDeriv_two_eq_deriv (f : ℝ → ℂ) :
    iteratedDeriv 2 f = deriv (deriv f) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]

/-! ## A uniform `ℓ¹` bound for the Fourier coefficients of `η_{≤c}`, `c ≤ 0` -/

/-- **The `ℓ¹` mass of the Fourier coefficients of the rescaled cutoff `η_{≤c}` is bounded
uniformly in `c ≤ 0`.**  Writing `R = 2^{-c} ≥ 1` one has `η_{≤c}(θ) = η(Rθ)`, so the sup-norm
and the first two derivatives of `η_{≤c}` are bounded by `C₀`, `C₀·R`, `C₀·R²` with a single
amplitude `C₀ = max M₀ (max M₁ M₂)` independent of `c`; `Work.KMTAreas.A7.CwTsumLe` converts
these three bounds (and the support hypothesis `η_{≤c} = 0` for `|θ| > 1/R`) into
`∑_j ‖cw (η_{≤c}) j‖ ≤ C·C₀` with `C` absolute. -/
private theorem absc_cw_etaCut_tsum_le_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℤ, c ≤ 0 →
      ∑' j : ℤ, ‖cw (etaCut Work.KMTContract.kmtEta c) j‖ ≤ C := by
  obtain ⟨Ccw, hCcwpos, hCcw⟩ := CwTsumLe
  obtain ⟨M0, M1, M2, hM0, hM1, hM2, hcd, hb0, hb1, hb2, hz0, hz1, hz2, _, _⟩ :=
    Work.KMTAreas.A7.kmtEta_deriv_bounds
  have hη0 : ∀ y : ℝ, ‖Work.KMTContract.kmtEta y‖ ≤ M0 := by
    intro y
    rcases lt_or_ge (1 : ℝ) |y| with h | h
    · rw [hz0 y (le_of_lt h), norm_zero]; exact hM0
    · exact hb0 y h
  have hη1 : ∀ y : ℝ, ‖deriv Work.KMTContract.kmtEta y‖ ≤ M1 := by
    intro y
    rcases lt_or_ge (1 : ℝ) |y| with h | h
    · rw [hz1 y (le_of_lt h), norm_zero]; exact hM1
    · exact hb1 y h
  have hη2 : ∀ y : ℝ, ‖deriv (deriv Work.KMTContract.kmtEta) y‖ ≤ M2 := by
    intro y
    rw [← absc_iteratedDeriv_two_eq_deriv]
    rcases lt_or_ge (1 : ℝ) |y| with h | h
    · rw [hz2 y (le_of_lt h), norm_zero]; exact hM2
    · exact hb2 y h
  set C0 : ℝ := max M0 (max M1 M2) with hC0def
  have h0C0 : M0 ≤ C0 := le_max_left _ _
  have h1C0 : M1 ≤ C0 := le_trans (le_max_left _ _) (le_max_right _ _)
  have h2C0 : M2 ≤ C0 := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨max (Ccw * C0) 0 + 1, by positivity, fun c hc => ?_⟩
  set R : ℝ := ((2 : ℝ) ^ c)⁻¹ with hRdef
  have hRpos : 0 < R := by
    rw [hRdef]; exact inv_pos.mpr (zpow_pos (by norm_num : (0 : ℝ) < 2) c)
  have hR1 : 1 ≤ R := by
    rw [hRdef, ← zpow_neg]
    exact one_le_zpow₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hR0 : 0 ≤ C0 := le_trans hM0 h0C0
  have hRnn : 0 ≤ R := hRpos.le
  have hRC : ‖((R : ℝ) : ℂ)‖ = R := by
    rw [Complex.norm_real, Real.norm_of_nonneg hRnn]
  have hE : ∀ θ : ℝ, etaCut Work.KMTContract.kmtEta c θ = Work.KMTContract.kmtEta (R * θ) := by
    intro θ
    simp only [etaCut, hRdef, div_eq_mul_inv]
    ring_nf
  have hbd : ∀ θ : ℝ, ‖etaCut Work.KMTContract.kmtEta c θ‖ ≤ C0 := by
    intro θ; rw [hE θ]; exact le_trans (hη0 _) h0C0
  have hbd1 : ∀ θ : ℝ, ‖deriv (etaCut Work.KMTContract.kmtEta c) θ‖ ≤ C0 * R := by
    intro θ
    have hfun : etaCut Work.KMTContract.kmtEta c
        = fun θ : ℝ => Work.KMTContract.kmtEta (R * θ) := funext hE
    rw [hfun, absc_deriv_comp_mul_left, norm_mul, hRC]
    calc R * ‖deriv Work.KMTContract.kmtEta (R * θ)‖ ≤ R * M1 :=
          mul_le_mul_of_nonneg_left (hη1 (R * θ)) hRnn
      _ ≤ C0 * R := by
          rw [mul_comm C0 R]; exact mul_le_mul_of_nonneg_left h1C0 hRnn
  have hbd2 : ∀ θ : ℝ, ‖deriv (deriv (etaCut Work.KMTContract.kmtEta c)) θ‖ ≤ C0 * R ^ 2 := by
    intro θ
    have hfun : etaCut Work.KMTContract.kmtEta c
        = fun θ : ℝ => Work.KMTContract.kmtEta (R * θ) := funext hE
    rw [hfun, absc_deriv_deriv_comp_mul_left Work.KMTContract.kmtEta R θ, norm_mul, norm_mul,
      hRC]
    calc R * (R * ‖deriv (deriv Work.KMTContract.kmtEta) (R * θ)‖) ≤ R * (R * M2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hη2 (R * θ)) hRnn) hRnn
      _ ≤ C0 * R ^ 2 := by nlinarith [h2C0, hRnn, sq_nonneg R]
  have hsup : ∀ θ : ℝ, 1 / R < |θ| → etaCut Work.KMTContract.kmtEta c θ = 0 := by
    intro θ hθ
    rw [hE θ]
    refine hz0 _ ?_
    have hthis : 1 < R * |θ| := by
      have h2 := mul_lt_mul_of_pos_left hθ hRpos
      rwa [mul_div_cancel₀ _ (ne_of_gt hRpos)] at h2
    rw [abs_mul, abs_of_pos hRpos]
    exact le_of_lt hthis
  have hcdE : ContDiff ℝ 2 (etaCut Work.KMTContract.kmtEta c) := by
    have hfun : etaCut Work.KMTContract.kmtEta c
        = fun θ : ℝ => Work.KMTContract.kmtEta (R * θ) := funext hE
    rw [hfun]
    exact hcd.comp (contDiff_const.mul contDiff_id)
  refine (hCcw (etaCut Work.KMTContract.kmtEta c) C0 R hR0 hR1 hcdE hbd hbd1 hbd2 hsup).trans ?_
  exact le_trans (le_max_left _ _) (le_add_of_nonneg_right (by norm_num))

/-! ## Summability of the coefficient kernels of the two windows -/

/-- The coefficients of the tensor factor `m_* = η_{≤-2u}` are `ℓ¹`. -/
private lemma absc_summable_cw_mStarF (u : ℕ) :
    Summable fun j : ℤ => ‖cw (mStarF u) j‖ := by
  obtain ⟨C, _hCpos, hdec⟩ := cw_etaCut_decay (-(2 * (u : ℤ)))
  have hmaj : Summable (fun j : ℤ => C / (1 + |(j : ℝ)|) ^ 2) := by
    have h := summable_one_div_sq_int.mul_left C
    have heq : (fun j : ℤ => C / (1 + |(j : ℝ)|) ^ 2)
        = fun j : ℤ => C * (1 / (1 + |(j : ℝ)|) ^ 2) := by
      funext j; rw [div_eq_mul_inv, one_div]
    rw [heq]; exact h
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) hmaj
  simpa only [mStarF] using hdec j

/-- The coefficients of the tensor factor `η_{≤-2du}` are `ℓ¹`. -/
private lemma absc_summable_cw_mStargF (P : Polynomial ℤ) (u : ℕ) :
    Summable fun j : ℤ => ‖cw (mStargF P.natDegree u) j‖ := by
  obtain ⟨C, _hCpos, hdec⟩ := cw_etaCut_decay (-((P.natDegree : ℤ) * 2 * (u : ℤ)))
  have hmaj : Summable (fun j : ℤ => C / (1 + |(j : ℝ)|) ^ 2) := by
    have h := summable_one_div_sq_int.mul_left C
    have heq : (fun j : ℤ => C / (1 + |(j : ℝ)|) ^ 2)
        = fun j : ℤ => C * (1 / (1 + |(j : ℝ)|) ^ 2) := by
      funext j; rw [div_eq_mul_inv, one_div]
    rw [heq]; exact h
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) hmaj
  simpa only [mStargF] using hdec j

/-! ## The arithmetic kernel is bounded by the product of the two cardinalities -/

/-- The characters of the circle have modulus one. -/
private lemma absc_norm_fourier_circle_one (n : ℤ) (α : Work.Analysis.IonescuWainger.Circle) :
    ‖fourier (T := 1) n α‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe _

/-- The arithmetic symbol `m_Ẑ` is the average over `ℤ/qℤ` of a product of two characters, hence
has modulus at most one. -/
private lemma absc_norm_mZ_le_one (P : Polynomial ℤ) (q : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) :
    ‖mZ P q α₁ α₂‖ ≤ 1 := by
  rw [mZ]
  by_cases hq : q = 0
  · subst hq; simp
  · have hqr : (0 : ℝ) < q := by
      have h1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq
      exact_mod_cast h1
    have hsum : ‖∑ n ∈ Finset.range q,
        fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖ ≤ (q : ℝ) := by
      calc ‖∑ n ∈ Finset.range q, fourier (T := 1) (n : ℤ) α₁
              * fourier (T := 1) (P.eval (n : ℤ)) α₂‖
          ≤ ∑ n ∈ Finset.range q, ‖fourier (T := 1) (n : ℤ) α₁
              * fourier (T := 1) (P.eval (n : ℤ)) α₂‖ := norm_sum_le _ _
        _ = ∑ _n ∈ Finset.range q, (1 : ℝ) := by
            refine Finset.sum_congr rfl (fun n _ => ?_)
            rw [norm_mul, absc_norm_fourier_circle_one, absc_norm_fourier_circle_one, mul_one]
        _ = (q : ℝ) := by simp
    have hqnorm : ‖(q : ℂ)⁻¹‖ = (q : ℝ)⁻¹ := by rw [norm_inv, Complex.norm_natCast]
    calc ‖(q : ℂ)⁻¹ * ∑ n ∈ Finset.range q, fourier (T := 1) (n : ℤ) α₁
            * fourier (T := 1) (P.eval (n : ℤ)) α₂‖
        = ‖(q : ℂ)⁻¹‖ * ‖∑ n ∈ Finset.range q, fourier (T := 1) (n : ℤ) α₁
            * fourier (T := 1) (P.eval (n : ℤ)) α₂‖ := norm_mul _ _
      _ ≤ (q : ℝ)⁻¹ * (q : ℝ) := by
          rw [hqnorm]
          exact mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hqr.le)
      _ = 1 := by field_simp

/-- **The arithmetic kernel `arithKernelEx` is bounded by the product of the cardinalities** of
the two exact-height frequency sets `(ℚ/ℤ)_{l₁}`, `(ℚ/ℤ)_{l₂}`: it is a double sum of
`|(ℚ/ℤ)_{l₁}|·|(ℚ/ℤ)_{l₂}|` terms `m_Ẑ(α₁,α₂) e(-j₁α₁) e(-j₂α₂)`, with `|m_Ẑ| ≤ 1` and
unit-modulus characters. -/
private lemma absc_arithKernelEx_norm_le (ρ : ℝ) (P : Polynomial ℤ) (q : ℕ) (l₁ l₂ : ℕ)
    (j₁ j₂ : ℤ) :
    ‖arithKernelEx ρ P q l₁ l₂ j₁ j₂‖
      ≤ ((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ) := by
  rw [arithKernelEx]
  calc ‖∑ α₁ ∈ diffFreqs ρ l₁, ∑ α₂ ∈ diffFreqs ρ l₂,
          mZ P q α₁ α₂ * fourier (T := 1) (-j₁) α₁
            * fourier (T := 1) (-j₂) α₂‖
      ≤ ∑ α₁ ∈ diffFreqs ρ l₁,
          ‖∑ α₂ ∈ diffFreqs ρ l₂,
            mZ P q α₁ α₂ * fourier (T := 1) (-j₁) α₁
              * fourier (T := 1) (-j₂) α₂‖ := norm_sum_le _ _
    _ ≤ ∑ α₁ ∈ diffFreqs ρ l₁,
          ∑ α₂ ∈ diffFreqs ρ l₂,
            ‖mZ P q α₁ α₂ * fourier (T := 1) (-j₁) α₁
              * fourier (T := 1) (-j₂) α₂‖ :=
        Finset.sum_le_sum (fun a _ => norm_sum_le _ _)
    _ ≤ ∑ _α₁ ∈ diffFreqs ρ l₁,
          ∑ _α₂ ∈ diffFreqs ρ l₂, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => ?_))
        have h1 : ‖fourier (T := 1) (-j₁) a‖ = 1 := absc_norm_fourier_circle_one _ _
        have h2 : ‖fourier (T := 1) (-j₂) b‖ = 1 := absc_norm_fourier_circle_one _ _
        rw [norm_mul, norm_mul, h1, h2]
        linarith [norm_nonneg (mZ P q a b), absc_norm_mZ_le_one P q a b]
    _ = ((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]

/-! ## The kernel of `BtwistEx` -/

/-- The kernel of `BtwistEx` as a function of the two summation variables. -/
private noncomputable def abscBtwK (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ u : ℕ) :
    ℤ → ℤ → ℂ :=
  fun j₁ j₂ =>
    arithKernelEx ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ j₁ j₂
      * cw (mStarF u) j₁ * cw (mStargF P.natDegree u) j₂

/-- `BtwistEx` is the bilinear convolution operator with kernel `abscBtwK` (definitional). -/
private lemma absc_BtwistEx_eq_bilinOp (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ u : ℕ)
    (h k : ℤ → ℂ) :
    BtwistEx ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u) h k
      = bilinOp (abscBtwK ρ P l₁ l₂ u) h k := rfl

/-! ## The crude bound -/

theorem exists_bound_BtwistEx_crude (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℕ) (h k : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ =>
          Work.KMTPlan.A6.BtwistEx ρ P l₁ l₂ (Work.KMTAreas.A7.mStarF u)
            (Work.KMTAreas.A7.mStargF P.natDegree u) h k x)
        1 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm h 2 MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm k 2 MeasureTheory.Measure.count := by
  obtain ⟨Cw, hCwpos, hCwm⟩ := absc_cw_etaCut_tsum_le_uniform
  set A : ℝ := ((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ) with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  refine ⟨A * (Cw * Cw), mul_nonneg hA0 (mul_nonneg hCwpos.le hCwpos.le), fun u h k => ?_⟩
  have hf : Summable fun j : ℤ => ‖cw (mStarF u) j‖ := absc_summable_cw_mStarF u
  have hg : Summable fun j : ℤ => ‖cw (mStargF P.natDegree u) j‖ :=
    absc_summable_cw_mStargF P u
  have hfsum : (∑' j : ℤ, ‖cw (mStarF u) j‖) ≤ Cw := by
    have hc : -(2 * (u : ℤ)) ≤ 0 :=
      neg_nonpos.mpr (mul_nonneg (by norm_num) (Int.natCast_nonneg _))
    simpa only [mStarF] using hCwm (-(2 * (u : ℤ))) hc
  have hgsum : (∑' j : ℤ, ‖cw (mStargF P.natDegree u) j‖) ≤ Cw := by
    have hc : -((P.natDegree : ℤ) * 2 * (u : ℤ)) ≤ 0 :=
      neg_nonpos.mpr (mul_nonneg (mul_nonneg (Int.natCast_nonneg _) (by norm_num))
        (Int.natCast_nonneg _))
    simpa only [mStargF] using hCwm (-((P.natDegree : ℤ) * 2 * (u : ℤ))) hc
  have hpt : ∀ j₁ j₂ : ℤ, ‖abscBtwK ρ P l₁ l₂ u j₁ j₂‖
      ≤ A * (‖cw (mStarF u) j₁‖ * ‖cw (mStargF P.natDegree u) j₂‖) := by
    intro j₁ j₂
    simp only [abscBtwK]
    rw [norm_mul, norm_mul]
    have h1 : ‖arithKernelEx ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ j₁ j₂‖ ≤ A := by
      rw [hA]
      exact absc_arithKernelEx_norm_le ρ P _ l₁ l₂ j₁ j₂
    calc ‖arithKernelEx ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ j₁ j₂‖
            * ‖cw (mStarF u) j₁‖ * ‖cw (mStargF P.natDegree u) j₂‖
        = ‖arithKernelEx ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ j₁ j₂‖
            * (‖cw (mStarF u) j₁‖ * ‖cw (mStargF P.natDegree u) j₂‖) := by ring
      _ ≤ A * (‖cw (mStarF u) j₁‖ * ‖cw (mStargF P.natDegree u) j₂‖) :=
          mul_le_mul h1 le_rfl (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hA0
  have hprod : Summable fun q : ℤ × ℤ =>
      ‖cw (mStarF u) q.1‖ * ‖cw (mStargF P.natDegree u) q.2‖ :=
    hf.mul_of_nonneg hg (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hmaj : Summable fun q : ℤ × ℤ =>
      A * (‖cw (mStarF u) q.1‖ * ‖cw (mStargF P.natDegree u) q.2‖) :=
    hprod.mul_left A
  have hKsumm : Summable fun q : ℤ × ℤ => ‖abscBtwK ρ P l₁ l₂ u q.1 q.2‖ :=
    Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => hpt q.1 q.2) hmaj
  have hmass : ∑' q : ℤ × ℤ, ‖abscBtwK ρ P l₁ l₂ u q.1 q.2‖ ≤ A * (Cw * Cw) := by
    calc ∑' q : ℤ × ℤ, ‖abscBtwK ρ P l₁ l₂ u q.1 q.2‖
        ≤ ∑' q : ℤ × ℤ,
            A * (‖cw (mStarF u) q.1‖ * ‖cw (mStargF P.natDegree u) q.2‖) :=
          Summable.tsum_le_tsum (fun q => hpt q.1 q.2) hKsumm hmaj
      _ = A * ((∑' j : ℤ, ‖cw (mStarF u) j‖)
            * (∑' j : ℤ, ‖cw (mStargF P.natDegree u) j‖)) := by
          rw [hprod.tsum_mul_left A, hf.tsum_mul_tsum hg hprod]
      _ ≤ A * (Cw * Cw) := by
          refine mul_le_mul_of_nonneg_left ?_ hA0
          exact mul_le_mul hfsum hgsum (tsum_nonneg (fun j => norm_nonneg _)) hCwpos.le
  rw [absc_BtwistEx_eq_bilinOp ρ P l₁ l₂ u h k]
  refine (Work.KMTAreas.A7.BilinOpLp (K := abscBtwK ρ P l₁ l₂ u) (u := h) (v := k)
    (p := 1) (p₁ := 2) (p₂ := 2) ?_ le_rfl hKsumm).trans ?_
  · rw [ENNReal.inv_two_add_inv_two, inv_one]
  · exact mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal hmass) le_rfl) le_rfl

end

end Work.KMTPlan.A6
