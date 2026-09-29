import Mathlib
import Submission.CDTPlan.Interfaces
import Submission.CDT.Discrepancy
import Submission.Work.Holonomy3.defs
import Submission.Work.Holonomy3.comp_defs
import Submission.Work.Holonomy3.min_coeff
import Submission.Work.Holonomy3.assembly_defs
import Submission.Work.Holonomy3.fstats
import Submission.Work.Holonomy3.siegel
import Submission.Work.Holonomy3.seeding_defs
import Submission.Work.Holonomy3.blockIdx_spec
import Submission.Work.Holonomy3.card_blockIdx_close
import Submission.Work.Holonomy3.exists_monotone_perm
import Submission.Work.Holonomy3.exists_lexmin_minimal
import Submission.Work.Holonomy3.coeff_cleared_eq
import Submission.Work.Holonomy3.cleared_taylor
import Submission.Work.Holonomy3.assembly_lemmas
import Submission.Work.Holonomy3.clearedFun_pointwise_bound
import Submission.Work.Holonomy3.integral_sup_bound
import Submission.Work.Holonomy3.mv_lex_defs
import Submission.Work.Holonomy3.mv_lexmin_coeff_le_integral
import Submission.Work.Holonomy3.mv_lexmin_coeff_le_integral_smoothed
import Submission.Work.Holonomy3.mv_lex_measurable_norm_G
import Submission.Work.Holonomy3.integrable_sup_circleLog
import Submission.Work.Holonomy3.exists_sieve_params
import Submission.Work.Holonomy3.log_den_coeff_le
import Submission.Work.Holonomy3.abel_sum_bound
import Submission.Work.Holonomy3.scaled_setup
import Submission.Work.Holonomy3.exists_scaled_family
import Submission.Work.Holonomy3.pullback_coeff_growth
import Submission.Work.Holonomy3.exists_sup_bound_circle
import Submission.Work.Holonomy3.exists_circleLog_bound
import Submission.Work.Holonomy3.coeff_rename_auxSeries
import Submission.Work.Holonomy3.final_sift
import Submission.Work.Holonomy3.radius_reduction
import Submission.Work.Holonomy3.sieve_err_compare
import Submission.Work.ZeroEst2.zero_estimate_all

/-!
# The assembly of the fine holonomy bound (`l ≤ 2`)

This module contains the proof of `Work.Holonomy3.holonomy_bound_l2` (the paper's Theorem
`main:elementary form` in the holonomic case) for the *scaled* maps `z ↦ φ k (ρ z)`, `0 < ρ < 1`
(`main_bound_scaled`), together with its elementary supporting lemmas.  The passage `ρ → 1` is
`Work.Holonomy3.radius_reduction`.

The design follows `Submission/Work/Holonomy3/NOTES_DESIGN.md`; the one deviation from the earlier
notes is that the pointwise bound on the cleared composite is *not* used in the `max (·) 0` form
(that variant is false, see `Submission/Work/Holonomy3/integral_max_sup_bound_false.lean`): instead
the smoothed Jensen bound `mv_lexmin_coeff_le_integral_smoothed` and the smoothed comparison lemma
`integral_log_add_le_of_pointwise` below replace it, with a `+ log 2` which is absorbed by the
`o(α)` constants.
-/

namespace Work.Holonomy3

open Submission.CDTPlan MeasureTheory Filter Topology
open scoped BigOperators

noncomputable section

/-! ## Elementary supporting lemmas -/

/-- The norms of a rational with respect to the real and the complex absolute values agree. -/
theorem norm_ratCast_complex (q : ℚ) : ‖((q : ℚ) : ℂ)‖ = ‖((q : ℚ) : ℝ)‖ := by
  rw [← RCLike.ofReal_ratCast (K := ℂ) q, RCLike.norm_ofReal, Real.norm_eq_abs]

/-- The derivative at `0` of the scaled map `z ↦ φ (ρ z)`. -/
theorem deriv_comp_mul (φ : ℂ → ℂ) (hφ : DifferentiableAt ℂ φ 0) (ρ : ℝ) :
    deriv (fun z : ℂ => φ ((ρ : ℂ) * z)) 0 = (ρ : ℂ) * deriv φ 0 := by
  have hg : DifferentiableAt ℂ (fun z : ℂ => ((ρ : ℂ)) * z) 0 := by fun_prop
  have h := deriv_comp (x := (0 : ℂ)) (h := fun z : ℂ => (ρ : ℂ) * z) (h₂ := φ)
    (by simpa using hφ) hg
  rw [show (fun z : ℂ => φ ((ρ : ℂ) * z)) = φ ∘ (fun z : ℂ => (ρ : ℂ) * z) from rfl, h]
  have hd : deriv (fun z : ℂ => (ρ : ℂ) * z) 0 = (ρ : ℂ) := deriv_const_mul_id (ρ : ℂ)
  rw [mul_zero, hd, mul_comm]

/-- **The smoothed comparison lemma.**  If `F` is integrable, `‖G‖` is measurable and bounded by
`B`, and `log ‖G x‖ ≤ F x` whenever `G x ≠ 0`, while `log δ ≤ F x` for all `x`, then

  `∫ log (‖G x‖ + δ) ≤ ∫ F + log 2`.

The `+ log 2` is the price of smoothing: `log (a + δ) ≤ log 2 + max (log a) (log δ)`. -/
theorem integral_log_add_le_of_pointwise {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {Gfun : X → ℂ} {F : X → ℝ}
    (hF : Integrable F μ) (hmeas : Measurable (fun x => ‖Gfun x‖)) {B δ : ℝ}
    (hB : ∀ x, ‖Gfun x‖ ≤ B) (hδ0 : 0 < δ)
    (hδF : ∀ᵐ x ∂μ, Real.log δ ≤ F x)
    (hpt : ∀ᵐ x ∂μ, Gfun x ≠ 0 → Real.log ‖Gfun x‖ ≤ F x) :
    ∫ x, Real.log (‖Gfun x‖ + δ) ∂μ ≤ ∫ x, F x ∂μ + Real.log 2 := by
  have h2 : ∀ᵐ x ∂μ, Real.log (‖Gfun x‖ + δ) ≤ F x + Real.log 2 := by
    filter_upwards [hδF, hpt] with x hδF hpt
    rcases eq_or_ne (Gfun x) 0 with h0 | h0
    · rw [h0, norm_zero, zero_add]
      have h2' : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      linarith [hδF]
    · have hgn : 0 < ‖Gfun x‖ := norm_pos_iff.mpr h0
      by_cases h1 : δ ≤ ‖Gfun x‖
      · calc Real.log (‖Gfun x‖ + δ) ≤ Real.log (2 * ‖Gfun x‖) :=
            Real.log_le_log (by linarith) (by linarith)
          _ = Real.log 2 + Real.log ‖Gfun x‖ := Real.log_mul (by norm_num) (ne_of_gt hgn)
          _ ≤ Real.log 2 + F x := by linarith [hpt h0]
          _ = F x + Real.log 2 := by ring
      · calc Real.log (‖Gfun x‖ + δ) ≤ Real.log (2 * δ) :=
            Real.log_le_log (by linarith) (by linarith)
          _ = Real.log 2 + Real.log δ := Real.log_mul (by norm_num) (ne_of_gt hδ0)
          _ ≤ Real.log 2 + F x := by linarith [hδF]
          _ = F x + Real.log 2 := by ring
  have hint1 : Integrable (fun x => Real.log (‖Gfun x‖ + δ)) μ := by
    refine Integrable.of_bound ?_ (max |Real.log δ| |Real.log (B + δ)|)
      (Filter.Eventually.of_forall (fun x => ?_))
    · exact (Real.measurable_log.comp (hmeas.add_const δ)).aestronglyMeasurable
    · have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB x)
      have hδB : 0 < ‖Gfun x‖ + δ := by positivity
      have hle : ‖Gfun x‖ + δ ≤ B + δ := by linarith [hB x]
      have hlo : Real.log δ ≤ Real.log (‖Gfun x‖ + δ) :=
        Real.log_le_log hδ0 (by linarith [norm_nonneg (Gfun x)])
      have hhi : Real.log (‖Gfun x‖ + δ) ≤ Real.log (B + δ) :=
        Real.log_le_log hδB hle
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · have h3 : -|Real.log δ| ≤ Real.log δ := neg_abs_le _
        have h4 : |Real.log δ| ≤ max |Real.log δ| |Real.log (B + δ)| := le_max_left _ _
        linarith
      · have h3 : Real.log (B + δ) ≤ |Real.log (B + δ)| := le_abs_self _
        have h4 : |Real.log (B + δ)| ≤ max |Real.log δ| |Real.log (B + δ)| := le_max_right _ _
        linarith
  have hint2 : Integrable (fun x => F x + Real.log 2) μ :=
    hF.add (integrable_const (Real.log 2))
  calc ∫ x, Real.log (‖Gfun x‖ + δ) ∂μ ≤ ∫ x, (F x + Real.log 2) ∂μ :=
        integral_mono_ae hint1 hint2 h2
    _ = ∫ x, F x ∂μ + Real.log 2 := by
        rw [integral_add hF (integrable_const _), integral_const, probReal_univ, one_smul]

/-- **`-log (den β) ≤ log |β|` for a nonzero rational `β`.**  Equivalently `den β · |β| ≥ 1`,
since `β = num/den` with `num ≠ 0`. -/
theorem neg_log_den_le_log (β : ℚ) (hβ : β ≠ 0) :
    -Real.log ((β.den : ℕ) : ℝ) ≤ Real.log ‖((β : ℚ) : ℂ)‖ := by
  have hnum : β.num ≠ 0 := by
    intro h
    exact hβ (by rw [← Rat.num_div_den β, h]; simp)
  have hnumR : (0 : ℝ) < |((β.num : ℤ) : ℝ)| := by
    rw [abs_pos]
    intro h
    exact hnum (by exact_mod_cast h)
  have hden : (0 : ℝ) < ((β.den : ℕ) : ℝ) := by exact_mod_cast β.den_pos
  have h1 : ‖((β : ℚ) : ℂ)‖ = |((β.num : ℤ) : ℝ)| / ((β.den : ℕ) : ℝ) := by
    rw [norm_ratCast_complex, Real.norm_eq_abs]
    have h2 : ((β : ℚ) : ℝ) = ((β.num : ℤ) : ℝ) / ((β.den : ℕ) : ℝ) := by
      conv_lhs => rw [← Rat.num_div_den β]
      push_cast
      ring
    rw [h2, abs_div, abs_of_pos hden]
  have hpos : (0 : ℝ) < ‖((β : ℚ) : ℂ)‖ := by
    rw [norm_pos_iff]; exact_mod_cast hβ
  have hAbsNum : (1 : ℝ) ≤ |((β.num : ℤ) : ℝ)| := by
    have h : (1 : ℤ) ≤ |β.num| := Int.one_le_abs hnum
    exact_mod_cast h
  have hge1 : 1 ≤ ((β.den : ℕ) : ℝ) * ‖((β : ℚ) : ℂ)‖ := by
    rw [h1, mul_div_cancel₀ _ (ne_of_gt hden)]
    exact hAbsNum
  have hlog : 0 ≤ Real.log (((β.den : ℕ) : ℝ) * ‖((β : ℚ) : ℂ)‖) :=
    Real.log_nonneg hge1
  rw [Real.log_mul (ne_of_gt hden) (ne_of_gt hpos)] at hlog
  set A : ℝ := Real.log ((β.den : ℕ) : ℝ) with hA
  set Bq : ℝ := Real.log ‖((β : ℚ) : ℂ)‖ with hBq
  rw [hA, hBq] at hlog
  rw [hA, hBq]
  linarith

/-- **The elementary rearrangement `(m/A)·(Y + A·η) = (2/B)·Y + m·η`** for `A = m·B/2`: this is
what turns the `final_sift` conclusion (with `A = m·ds·Dint/2`) into the form that is compared
with the numeric sift `Work.Holonomy3.sieveErr` in `Work.Holonomy3.sieve_err_compare`. -/
theorem mul_div_eta_identity {m A B η Y : ℝ} (hm : m ≠ 0) (hB : B ≠ 0) (hA : A = m * B / 2) :
    (m / A) * (Y + A * η) = (2 / B) * Y + m * η := by
  subst hA
  have hA0 : m * B / 2 ≠ 0 := div_ne_zero (mul_ne_zero hm hB) (by norm_num)
  have h2B : (2 : ℝ) / B = m / (m * B / 2) := by
    rw [div_eq_div_iff hB hA0]
    ring
  rw [h2B, mul_add, ← mul_assoc, div_mul_cancel₀ _ hA0]

end

end Work.Holonomy3

namespace Work.Holonomy3

open Submission.CDTPlan MeasureTheory Filter Topology
open scoped BigOperators

noncomputable section

set_option maxHeartbeats 8000000

/-- **Property `(⋆)` of Lemma `Siegel`**, in the form used by the assembly: from the multivariable
Shidlovsky lemma, every nonzero minimal-degree monomial of the auxiliary series has *strictly*
smaller exponents than the box size `(m + δ) D` and box discrepancy `< ε` in that box.  The
hypothesis on the template is `degreeOf j ≤ D` (the weak form produced by `siegel`), and the
Shidlovsky lemma is applied with `D + 1`; the arithmetic hypothesis is `m + C < δ D`. -/
theorem min_monomial_lowdisc_strict {m : ℕ} {f : Fin m → PowerSeries ℚ} (C : ℕ)
    (hC : ∀ (d D : ℕ) (Q : (Fin d → Fin m) → MvPolynomial (Fin d) ℚ),
      (∀ i j, (Q i).degreeOf j < D) →
      ∀ n : Fin d →₀ ℕ, MvPowerSeries.coeff n (auxSeries f Q) ≠ 0 →
      (∀ n' : Fin d →₀ ℕ, n'.degree < n.degree →
        MvPowerSeries.coeff n' (auxSeries f Q) = 0) →
      ∀ j, n j ≤ m * D + C) :
    ∀ (d D : ℕ) (Q : (Fin d → Fin m) → MvPolynomial (Fin d) ℚ),
      (∀ i j, (Q i).degreeOf j ≤ D) → ∀ δ ε : ℝ, 0 < δ → (m : ℝ) + (C : ℝ) < δ * D →
      (∀ n : Fin d →₀ ℕ, (∀ j, (n j : ℝ) ≤ (m + δ) * D) →
        ε ≤ Submission.CDT.Discrepancy.disc (fun j => (n j : ℝ) / ((m + δ) * D)) →
        MvPowerSeries.coeff n (auxSeries f Q) = 0) →
      ∀ n : Fin d →₀ ℕ, MvPowerSeries.coeff n (auxSeries f Q) ≠ 0 →
      (∀ n' : Fin d →₀ ℕ, n'.degree < n.degree →
        MvPowerSeries.coeff n' (auxSeries f Q) = 0) →
      (∀ j, (n j : ℝ) < (m + δ) * D) ∧
        Submission.CDT.Discrepancy.disc (fun j => (n j : ℝ) / ((m + δ) * D)) < ε := by
  intro d D Q hQD δ ε hδ hbox hvan n hn hmin
  have hdeg : ∀ i j, (Q i).degreeOf j < D + 1 :=
    fun i j => lt_of_le_of_lt (hQD i j) (Nat.lt_succ_self D)
  have hCsh : ∀ j, n j ≤ m * (D + 1) + C := hC d (D + 1) Q hdeg n hn hmin
  have hbound : ∀ j, (n j : ℝ) ≤ (m : ℝ) * ((D : ℝ) + 1) + (C : ℝ) := fun j => by
    have h := hCsh j
    push_cast
    exact_mod_cast h
  have hfar : (m : ℝ) * ((D : ℝ) + 1) + (C : ℝ) < (m + δ) * D := by
    have h2 : (m : ℝ) + (C : ℝ) < δ * (D : ℝ) := hbox
    have e1 : (m : ℝ) * ((D : ℝ) + 1) + (C : ℝ)
        = (m : ℝ) * (D : ℝ) + ((m : ℝ) + (C : ℝ)) := by ring
    have e2 : (m + δ) * (D : ℝ) = (m : ℝ) * (D : ℝ) + δ * (D : ℝ) := by ring
    rw [e1, e2]; linarith
  have hlt : ∀ j, (n j : ℝ) < (m + δ) * D := fun j => lt_of_le_of_lt (hbound j) hfar
  refine ⟨hlt, ?_⟩
  by_contra hnot
  exact hn (hvan n (fun j => le_of_lt (hlt j)) (not_lt.mp hnot))

/-- **The box principle of `Work.Holonomy3.siegel`, with the constants extracted as functions of the
sieve parameter `ε`.** -/
theorem siegel_functions {m r : ℕ} (hm : 0 < m) (b : Fin m → Fin r → ℕ) (e : Fin m → ℕ)
    (f : Fin m → PowerSeries ℚ) (hden : ∀ i, HasDenomType (e i) (b i) (f i))
    (hpi : PolyIndependent f) (hdc : DClosed f) (A : ℝ) (hA : 1 ≤ A)
    (hgr : ∀ i n, ‖((PowerSeries.coeff n (f i) : ℚ) : ℝ)‖ ≤ A ^ n) :
    ∃ (δf : ℝ → ℝ) (d₀f : ℝ → ℕ) (D₀f : ℝ → ℕ → ℕ),
      (∀ ε, 0 < ε → ε < 1 → 0 < δf ε ∧ δf ε < ε) ∧
      (∀ ε (hε0 : 0 < ε) (hε1 : ε < 1) (d : ℕ), d₀f ε ≤ d → m ∣ d →
        ∀ D : ℕ, D₀f ε d ≤ D →
          ∃ Q : (Fin d → Fin m) → MvPolynomial (Fin d) ℚ,
            AuxTemplate D ε (Real.exp (ε * d * D)) Q ∧ auxSeries f Q ≠ 0 ∧
            (∀ n : Fin d →₀ ℕ, (∀ j, (n j : ℝ) ≤ (m - δf ε) * D) →
              MvPowerSeries.coeff n (auxSeries f Q) = 0) ∧
            (∀ n : Fin d →₀ ℕ, (∀ j, (n j : ℝ) ≤ (m + δf ε) * D) →
              ε ≤ Submission.CDT.Discrepancy.disc (fun j => (n j : ℝ) / ((m + δf ε) * D)) →
              MvPowerSeries.coeff n (auxSeries f Q) = 0)) := by
  classical
  have hsieg : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧ ∃ d₀ : ℕ,
      ∀ d : ℕ, d₀ ≤ d → m ∣ d → ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
        ∃ Q : (Fin d → Fin m) → MvPolynomial (Fin d) ℚ,
          AuxTemplate D ε (Real.exp (ε * d * D)) Q ∧ auxSeries f Q ≠ 0 ∧
          (∀ n : Fin d →₀ ℕ, (∀ j, (n j : ℝ) ≤ (m - δ) * D) →
            MvPowerSeries.coeff n (auxSeries f Q) = 0) ∧
          (∀ n : Fin d →₀ ℕ, (∀ j, (n j : ℝ) ≤ (m + δ) * D) →
            ε ≤ Submission.CDT.Discrepancy.disc (fun j => (n j : ℝ) / ((m + δ) * D)) →
            MvPowerSeries.coeff n (auxSeries f Q) = 0) :=
    fun ε hε0 hε1 => siegel hm b e f hden hpi hdc A hA hgr ε hε0 hε1
  let δf : ℝ → ℝ := fun ε => if h : 0 < ε ∧ ε < 1 then (hsieg ε h.1 h.2).choose else 0
  have hδf : ∀ ε, 0 < ε → ε < 1 → 0 < δf ε ∧ δf ε < ε := by
    intro ε hε0 hε1
    have h := (hsieg ε hε0 hε1).choose_spec
    have h2 : δf ε = (hsieg ε hε0 hε1).choose := by
      simp only [δf, dif_pos (⟨hε0, hε1⟩ : 0 < ε ∧ ε < 1)]
    rw [h2]
    exact ⟨h.1, h.2.1⟩
  let d₀f : ℝ → ℕ := fun ε =>
    if h : 0 < ε ∧ ε < 1 then ((hsieg ε h.1 h.2).choose_spec.2.2).choose else 0
  have hd₀f : ∀ ε (hε0 : 0 < ε) (hε1 : ε < 1) (d : ℕ), d₀f ε ≤ d → m ∣ d →
      ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
        ∃ Q : (Fin d → Fin m) → MvPolynomial (Fin d) ℚ,
          AuxTemplate D ε (Real.exp (ε * d * D)) Q ∧ auxSeries f Q ≠ 0 ∧
          (∀ n : Fin d →₀ ℕ, (∀ j, (n j : ℝ) ≤ (m - δf ε) * D) →
            MvPowerSeries.coeff n (auxSeries f Q) = 0) ∧
          (∀ n : Fin d →₀ ℕ, (∀ j, (n j : ℝ) ≤ (m + δf ε) * D) →
            ε ≤ Submission.CDT.Discrepancy.disc (fun j => (n j : ℝ) / ((m + δf ε) * D)) →
            MvPowerSeries.coeff n (auxSeries f Q) = 0) := by
    intro ε hε0 hε1 d hd hmd
    have h2 : d₀f ε = ((hsieg ε hε0 hε1).choose_spec.2.2).choose := by
      simp only [d₀f, dif_pos (⟨hε0, hε1⟩ : 0 < ε ∧ ε < 1)]
    rw [h2] at hd
    have hδeq : (hsieg ε hε0 hε1).choose = δf ε := by
      simp only [δf, dif_pos (⟨hε0, hε1⟩ : 0 < ε ∧ ε < 1)]
    have h := ((hsieg ε hε0 hε1).choose_spec.2.2).choose_spec d hd hmd
    rw [hδeq] at h
    exact h
  let D₀f : ℝ → ℕ → ℕ := fun ε d =>
    if h : (0 < ε ∧ ε < 1 ∧ d₀f ε ≤ d ∧ m ∣ d) then
      (hd₀f ε h.1 h.2.1 d h.2.2.1 h.2.2.2).choose else 0
  refine ⟨δf, d₀f, D₀f, hδf, ?_⟩
  intro ε hε0 hε1 d hd hmd D hD
  have h2 : D₀f ε d = (hd₀f ε hε0 hε1 d hd hmd).choose := by
    simp only [D₀f, dif_pos (⟨hε0, hε1, hd, hmd⟩ : 0 < ε ∧ ε < 1 ∧ d₀f ε ≤ d ∧ m ∣ d)]
  rw [h2] at hD
  exact (hd₀f ε hε0 hε1 d hd hmd).choose_spec D hD

/-- **The main bound for the scaled maps** `z ↦ φ k (ρ z)`, `0 < ρ < 1`, under the extra
hypothesis that the scaled maps are zero-free on the unit circle (which is what makes `circleLog`
of the scaled maps bounded and continuous).  This is the paper's Theorem `main:elementary form`
before the passage `ρ → 1` (`Work.Holonomy3.radius_reduction`). -/
theorem main_bound_scaled (hZ : ZeroEstimateAll) {m r l : ℕ} {b : Fin m → Fin r → ℕ}
    {e : Fin m → ℕ} {f : Fin m → PowerSeries ℚ} {φ : Fin (l + 1) → ℂ → ℂ}
    {γ : Fin (l + 2) → ℝ} {ξ : ℝ}
    (hm : 0 < m) (hl : l ≤ 2) (hb : ColumnShape b) (hden : ∀ i, HasDenomType (e i) (b i) (f i))
    (hpi : PolyIndependent f) (hdc : DClosed f)
    (hadm : ∀ k, AdmissibleMap (φ k)) (hpm : ∀ i k, PullbackMero (f i) (φ k))
    (hderiv : ∀ k, 0 < ‖deriv (φ k) 0‖) (hmono : StrictMono (fun k => ‖deriv (φ k) 0‖))
    (hγ0 : γ 0 = 0) (hγlast : γ (Fin.last (l + 1)) = m) (hγmono : StrictMono γ)
    (hξ0 : 0 ≤ ξ) (hξm : ξ ≤ m)
    (hτ : tauFlat b + tauSharpAt e ξ < Real.log ‖deriv (φ (Fin.last l)) 0‖)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hzf : ∀ k z, ‖z‖ = 1 → φ k (ρ * z) ≠ 0) :
    (m : ℝ) * (Real.log ‖deriv (fun z : ℂ => φ (Fin.last l) (ρ * z)) 0‖
        - (tauFlat b + tauSharpAt e ξ))
      ≤ rearrInt (fun k => (γ k.succ - γ k.castSucc) / m) (fun k z => φ k (ρ * z)) +
        (1 / (m : ℝ)) * ∑ k : Fin l, (γ k.succ.castSucc) ^ 2 *
          Real.log (‖deriv (φ k.succ) 0‖ / ‖deriv (φ k.castSucc) 0‖) := by
  classical
  refine le_of_forall_pos_le_add (fun η₁ hη₁ => ?_)
  -- ═══════════ 1. normalisation of the family
  have hper : ∀ i : Fin m, ∃ C A : ℝ, 0 < C ∧ 1 ≤ A ∧
      ∀ n : ℕ, ‖((PowerSeries.coeff n (f i) : ℚ) : ℂ)‖ ≤ C * A ^ n :=
    fun i => pullback_coeff_growth (hpm i 0) (hderiv 0)
  choose Cc Ac hCc hAc hgr using hper
  set i0 : Fin m := ⟨0, hm⟩ with hi0def
  set C0 : ℝ := (∑ i : Fin m, Cc i) + 1 with hC0def
  set A0 : ℝ := (∑ i : Fin m, Ac i) + 1 with hA0def
  have hC0le : ∀ i, Cc i ≤ C0 := fun i => by
    have h := Finset.single_le_sum (f := Cc) (fun j _ => (hCc j).le) (Finset.mem_univ i)
    rw [hC0def]; linarith
  have hA0le : ∀ i, Ac i ≤ A0 := fun i => by
    have h := Finset.single_le_sum (f := Ac) (fun j _ => le_trans zero_le_one (hAc j))
      (Finset.mem_univ i)
    rw [hA0def]; linarith
  have hC0pos : 0 < C0 := lt_of_lt_of_le (hCc i0) (hC0le i0)
  have hA01 : 1 ≤ A0 := le_trans (hAc i0) (hA0le i0)
  have hgrR : ∀ i n, ‖((PowerSeries.coeff n (f i) : ℚ) : ℝ)‖ ≤ C0 * A0 ^ n := by
    intro i n
    rw [← norm_ratCast_complex (PowerSeries.coeff n (f i))]
    exact le_trans (hgr i n)
      (mul_le_mul (hC0le i) (pow_le_pow_left₀ (le_trans zero_le_one (hAc i)) (hA0le i) n)
        (pow_nonneg (le_trans zero_le_one (hAc i)) n) hC0pos.le)
  obtain ⟨q, hqpos, hden', hpi', hdc', hpm', hgr'⟩ :=
    exists_scaled_family b e f φ hden hpi hdc hpm A0 C0 hA01 hC0pos hgrR
  set f' : Fin m → PowerSeries ℚ := fun i => (q : ℚ)⁻¹ • f i with hf'def
  have hden'' : ∀ i, HasDenomType (e i) (b i) (f' i) := hden'
  have hpi'' : PolyIndependent f' := hpi'
  have hdc'' : DClosed f' := hdc'
  have hpm'' : ∀ i k, PullbackMero (f' i) (φ k) := hpm'
  -- ═══════════ 2. the scaled maps and their Taylor series
  obtain ⟨ψ, Φ, N, P, hψeq, hψa, hψ0, hψderiv, hΦprop, hPull⟩ :=
    scaled_setup (r' := r) f' φ hadm hpm'' hρ0
  have hΦ0 : ∀ k, PowerSeries.coeff 0 (Φ k) = 0 := fun k => (hΦprop k).1
  have hΦ1 : ∀ k, PowerSeries.coeff 1 (Φ k) = deriv (ψ k) 0 := fun k => (hΦprop k).2.1
  have hΦsum : ∀ k z, ‖z‖ < 1 / ρ →
      HasSum (fun p : ℕ => PowerSeries.coeff p (Φ k) * z ^ p) (ψ k z) :=
    fun k => (hΦprop k).2.2
  -- ═══════════ 3. the constants
  have hρdiv1 : 1 < 1 / ρ := by rw [lt_div_iff₀ hρ0]; linarith
  set ρ' : ℝ := (1 + 1 / ρ) / 2 with hρ'def
  have hρ'1 : 1 < ρ' := by rw [hρ'def]; linarith
  have hρ'lt : ρ' < 1 / ρ := by rw [hρ'def]; linarith
  set L : Fin (l + 1) → ℝ := fun k => Real.log ‖deriv (ψ k) 0‖ with hLdef
  set B : ℝ := ∑ k : Fin (l + 1), |L k| with hBdef
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun k _ => abs_nonneg _)
  have hLB : ∀ k, |L k| ≤ B := fun k =>
    Finset.single_le_sum (fun j _ => abs_nonneg (L j)) (Finset.mem_univ k)
  have hψkeq : ∀ k, ψ k = fun z : ℂ => φ k ((ρ : ℂ) * z) := fun k => by rw [hψeq]
  have hnormρ : ‖(ρ : ℂ)‖ = ρ := (RCLike.norm_ofReal (K := ℂ) ρ).trans (abs_of_pos hρ0)
  have hψadm : ∀ k, AdmissibleMap (ψ k) := by
    intro k
    have hk := hadm k
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hψkeq k]
      have hmaps : Set.MapsTo (fun z : ℂ => (ρ : ℂ) * z) (Metric.closedBall 0 1)
          (Metric.closedBall 0 1) := by
        intro z hz
        simp only [Metric.mem_closedBall, dist_zero_right] at hz ⊢
        rw [norm_mul, hnormρ]
        nlinarith [norm_nonneg z]
      exact hk.1.comp (continuous_const.mul continuous_id).continuousOn hmaps
    · rw [hψkeq k]
      have hmaps : Set.MapsTo (fun z : ℂ => (ρ : ℂ) * z) (Metric.ball 0 1) (Metric.ball 0 1) := by
        intro z hz
        simp only [Metric.mem_ball, dist_zero_right] at hz ⊢
        rw [norm_mul, hnormρ]
        nlinarith [norm_nonneg z]
      rw [show (fun z : ℂ => φ k ((ρ : ℂ) * z)) = φ k ∘ (fun z : ℂ => (ρ : ℂ) * z) from rfl]
      exact hk.2.1.comp (by fun_prop) hmaps
    · rw [hψkeq k]
      simp only [mul_zero]
      exact hk.2.2.1
    · intro z hz
      rw [hψkeq k]
      exact hzf k z hz
  obtain ⟨G0, hG00, hcont, hg⟩ := exists_circleLog_bound ψ hψadm
  obtain ⟨M, hM1, hMbound⟩ := exists_sup_bound_circle ψ N P (1 / ρ) hρdiv1 hψa
    (fun i k => (hPull i k).2.1)
  set U0 : ℝ := ∑ i : Fin m, ∑ p : Fin (l + 1), |Real.log ‖(P i p).eval 0‖| with hU0def
  have hU00 : 0 ≤ U0 :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun p _ => abs_nonneg _))
  have hM'1 : 1 ≤ max 1 M := le_max_left _ _
  -- ═══════════ 4. the sieve
  obtain ⟨Csh, hCsh⟩ := hZ m f' hpi'' hdc''
  obtain ⟨δf, d₀f, D₀f, hδf, hD₀f⟩ :=
    siegel_functions hm b e f' hden'' hpi'' hdc'' A0 hA01 hgr'
  set η : ℝ := η₁ / (16 * (m : ℝ)) with hηdef
  have hη0 : 0 < η := by rw [hηdef]; positivity
  obtain ⟨ε₁, hε₁0, hε₁1, d₁, hd₁⟩ := log_den_coeff_le hm b hb e f' hden'' ξ hξ0 hξm η hη0
  -- the `log_den_coeff_le` threshold in the sieve variable, as a function of `d`
  let Dld : ℕ → ℕ := fun dd => if h : (d₁ ≤ dd ∧ m ∣ dd) then Classical.choose (hd₁ dd h.1 h.2) else 0
  have hDld : ∀ dd, d₁ ≤ dd → m ∣ dd → ∀ D : ℕ, Dld dd ≤ D →
      ∀ ee : ℝ, 0 < ee → ee < ε₁ → ∀ nn : Fin dd → ℕ, Monotone nn →
      (∀ j : Fin dd, (nn j : ℝ) ≤ (m : ℝ) * D * ((j : ℝ) / dd) + 3 * m * ee * D) →
      ∀ QQ : (Fin dd → Fin m) → MvPolynomial (Fin dd) ℚ, (∀ i, QQ i ≠ 0 → Balanced i) →
      (∀ i j, (QQ i).degreeOf j < D) → (∀ i k, ∃ a : ℤ, (QQ i).coeff k = a) →
      ∀ nn' : Fin dd →₀ ℕ, (∀ j, nn' j = nn j) →
        MvPowerSeries.coeff nn' (auxSeries f' QQ) ≠ 0 →
      Real.log ((Rat.den (MvPowerSeries.coeff nn' (auxSeries f' QQ)) : ℕ) : ℝ)
        ≤ ((m : ℝ) * dd * D / 2) * (tauFlat b + tauSharpAt e ξ + η) := by
    intro dd hdd hmd D hDle ee he0 he1 nn hn hbound QQ hQbal hQdeg hQint nn' hnn' hcoeff
    have h2 : Dld dd = Classical.choose (hd₁ dd hdd hmd) := by
      simp only [Dld, dif_pos (⟨hdd, hmd⟩ : d₁ ≤ dd ∧ m ∣ dd)]
    rw [h2] at hDle
    exact Classical.choose_spec (hd₁ dd hdd hmd) D hDle ee he0 he1 nn hn hbound QQ hQbal
      hQdeg hQint nn' hnn' hcoeff
  let d₀c : ℝ → ℕ := fun ee => max (d₀f ee) d₁
  let D₀c : ℝ → ℕ → ℕ := fun ee dd => max (D₀f ee dd) (Dld dd)
  obtain ⟨ε, ds, Ds, hε0, hε1, hεε₁, hds0, hmdvd, hdsd₀c, hDs0, hDsD₀c, hδDs, hErrs⟩ :=
    exists_sieve_params (l := l) hm hG00 hB0 (le_refl 0) hU00 hM'1 hη₁ hε₁0
      (fun ee he0 he1 => (hδf ee he0 he1).1) (fun ee he0 he1 => (hδf ee he0 he1).2)
      (d₀ := d₀c) (D₀ := D₀c)
  have hdsd₁ : d₁ ≤ ds := le_trans (le_max_right _ _) hdsd₀c
  have hdsd₂ : d₀f ε ≤ ds := le_trans (le_max_left _ _) hdsd₀c
  have hDsDld : Dld ds ≤ Ds := le_trans (le_max_right _ _) hDsD₀c
  have hDsD₀ : D₀f ε ds ≤ Ds := le_trans (le_max_left _ _) hDsD₀c
  set Dint : ℕ := Ds + 1 with hDintdef
  have hDint0 : 0 < Dint := Nat.succ_pos _
  obtain ⟨Q, hQaux, hQne, hQbox, hQbad⟩ := hD₀f ε hε0 hε1 ds hdsd₂ hmdvd Ds hDsD₀
  -- ═══════════ 5. the extracted monomial, its sorting, the seeding
  have hQne₀ : ∃ nn : Fin ds →₀ ℕ, MvPowerSeries.coeff nn (auxSeries f' Q) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hQne (funext fun nn => h nn)
  obtain ⟨n, hnβ, hnmin, hnlex⟩ := exists_lexmin_minimal
    (fun nn : Fin ds →₀ ℕ => ((MvPowerSeries.coeff nn (auxSeries f' Q) : ℚ) : ℂ))
    (by obtain ⟨nn, hn⟩ := hQne₀; exact ⟨nn, by exact_mod_cast hn⟩)
  have hnβ' : MvPowerSeries.coeff n (auxSeries f' Q) ≠ 0 := fun h => hnβ (by rw [h]; simp)
  have hnmin' : ∀ nn : Fin ds →₀ ℕ, nn.degree < n.degree →
      MvPowerSeries.coeff nn (auxSeries f' Q) = 0 := fun nn hnn => by
    have h := hnmin nn hnn
    exact_mod_cast h
  have hQdeg : ∀ i j, (Q i).degreeOf j ≤ Ds := by
    intro i j
    rw [MvPolynomial.degreeOf_le_iff]
    intro m hm
    exact (hQaux.2.1 i m hm).1 j
  have hCshbox : (m : ℝ) + (Csh : ℝ) < δf ε * Ds := by
    have h1 : (m : ℝ) + (Csh : ℝ) + 1 ≤ δf ε * Ds := hδDs
    linarith
  obtain ⟨hstar_lt, hstar_disc⟩ :=
    min_monomial_lowdisc_strict (m := m) (f := f') Csh hCsh ds Ds Q hQdeg (δf ε) ε
      (hδf ε hε0 hε1).1 hCshbox hQbad n hnβ' hnmin'
  obtain ⟨π, hπmono⟩ := exists_monotone_perm (fun j : Fin ds => n j)
  have hπmono' : Monotone (fun i : Fin ds => n (π i)) := hπmono
  set κ : Fin ds → Fin (l + 1) := fun s => blockIdx m γ (π.symm s) with hκdef
  set nT : Fin ds →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun j => n (π j)) with hnTdef
  have hnTapply : ∀ j, nT j = n (π j) := fun j =>
    congrFun (Finsupp.coe_equivFunOnFinite_symm (fun j => n (π j))) j
  set QT : (Fin ds → Fin m) → MvPolynomial (Fin ds) ℚ :=
    fun i => MvPolynomial.rename π.symm (Q (i ∘ π.symm)) with hQTdef
  have hcκ : ∀ p : Fin (l + 1),
      |((Finset.univ.filter (fun a : Fin ds => κ a = p)).card : ℝ) / ds
        - (γ p.succ - γ p.castSucc) / m| ≤ 2 / ds := by
    intro p
    have h1 := card_blockIdx_close m hm hds0 γ hγ0 hγlast hγmono p
    have hcard : (Finset.univ.filter (fun a : Fin ds => κ a = p)).card
        = (Finset.univ.filter (fun j : Fin ds => blockIdx m γ j = p)).card := by
      have hset : (Finset.univ.filter (fun a : Fin ds => κ a = p))
          = (Finset.univ.filter (fun j : Fin ds => blockIdx m γ j = p)).map
              ⟨π, π.injective⟩ := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
          Function.Embedding.coeFn_mk]
        constructor
        · intro ha
          exact ⟨π.symm a, by simpa [hκdef] using ha, by simp⟩
        · rintro ⟨j, hj, hja⟩
          rw [← hja]
          simpa [hκdef] using hj
      rw [hset, Finset.card_map]
    rw [hcard]; exact h1
  -- ═══════════ 6. the numerical parameters
  set A : ℝ := (m : ℝ) * ds * Dint / 2 with hAdef
  set rearr : ℝ := rearrInt (fun k => (γ k.succ - γ k.castSucc) / m) ψ with hrearrdef
  set Ssum : ℝ := ∑ k : Fin l, (γ k.succ.castSucc) ^ 2 * (L k.succ - L k.castSucc) with hSsumdef
  set β : ℚ := (auxSeries f' Q).coeff n with hβdef
  have hβne : β ≠ 0 := hnβ'
  have hδleε : δf ε ≤ ε := le_of_lt (hδf ε hε0 hε1).2
  have hDs1 : 1 ≤ Ds := by
    by_contra hcon
    have h0 : Ds = 0 := by omega
    have h2 : 0 < δf ε := (hδf ε hε0 hε1).1
    have hδ0 := hδDs
    rw [h0] at hδ0
    simp only [Nat.cast_zero, mul_zero] at hδ0
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hc0 : (0 : ℝ) ≤ (Csh : ℝ) := Nat.cast_nonneg Csh
    linarith
  have hDintR : (Dint : ℝ) = (Ds : ℝ) + 1 := by rw [hDintdef]; push_cast; ring
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hδmε : δf ε ≤ (m : ℝ) * ε :=
    le_trans hδleε (le_mul_of_one_le_left hε0.le (by exact_mod_cast hm))
  have hDsR : (0 : ℝ) ≤ (Ds : ℝ) := Nat.cast_nonneg Ds
  have hε1' : ε ≤ 1 := le_of_lt hε1
  have hj0 : ∀ j : Fin ds, (0 : ℝ) ≤ (j : ℝ) / ds :=
    fun j => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hj1 : ∀ j : Fin ds, (j : ℝ) / ds ≤ 1 := fun j => by
    rw [div_le_one (by exact_mod_cast hds0)]
    exact_mod_cast le_of_lt j.2
  have hposD : ∀ c : ℝ, 0 < c → (0 : ℝ) < (m + c) * Ds := by
    intro c hc
    have h2 : (0 : ℝ) < (m : ℝ) + c := by linarith
    positivity
  -- ✦ (B4) the Abel summation
  have hsorted : ∀ j : Fin ds,
      |(n (π j) : ℝ) / ((m + δf ε) * Ds) - (j : ℝ) / ds| ≤ ε := by
    intro j
    have hpos := hposD (δf ε) (hδf ε hε0 hε1).1
    have ht : ∀ j : Fin ds, (n (π j) : ℝ) / ((m + δf ε) * Ds) ∈ Set.Ico 0 1 := by
      intro j
      refine ⟨div_nonneg (Nat.cast_nonneg _) hpos.le, ?_⟩
      rw [div_lt_one hpos]
      exact hstar_lt (π j)
    have hmono : Monotone (fun j : Fin ds => (n (π j) : ℝ) / ((m + δf ε) * Ds)) := by
      intro a b hab
      refine div_le_div_of_nonneg_right ?_ hpos.le
      exact_mod_cast hπmono' hab
    have hdisc : Submission.CDT.Discrepancy.disc
        (fun j : Fin ds => (n (π j) : ℝ) / ((m + δf ε) * Ds)) ≤ ε := by
      rw [disc_comp_perm (fun j : Fin ds => (n j : ℝ) / ((m + δf ε) * Ds)) π]
      exact le_of_lt hstar_disc
    obtain ⟨h1, h2⟩ := sorted_bounds _ ht hmono hε0.le hdisc j
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hnum_hi : ∀ j : Fin ds,
      (n (π j) : ℝ) ≤ (m + δf ε) * Ds * ((j : ℝ) / ds) + (m + δf ε) * Ds * ε := by
    intro j
    have hpos := hposD (δf ε) (hδf ε hε0 hε1).1
    obtain ⟨-, h2⟩ := abs_le.mp (hsorted j)
    have hB := (div_le_iff₀ hpos).mp (by linarith :
      (n (π j) : ℝ) / ((m + δf ε) * Ds) ≤ (j : ℝ) / ds + ε)
    rw [add_mul] at hB
    linarith [hB]
  have hnum_lo : ∀ j : Fin ds,
      (m + δf ε) * Ds * ((j : ℝ) / ds - ε) ≤ (n (π j) : ℝ) := by
    intro j
    have hpos := hposD (δf ε) (hδf ε hε0 hε1).1
    obtain ⟨h1, -⟩ := abs_le.mp (hsorted j)
    have hA := (le_div_iff₀ hpos).mp (by linarith :
      (j : ℝ) / ds - ε ≤ (n (π j) : ℝ) / ((m + δf ε) * Ds))
    rw [sub_mul] at hA
    linarith [hA]
  have hbox : ∀ j : Fin ds, (nT j : ℝ) ≤ (m : ℝ) * Dint * ((j : ℝ) / ds) + 3 * m * ε * Dint := by
    intro j
    have h1 := hnum_hi j
    rw [hnTapply j, hDintR]
    nlinarith [h1, hδmε, hj0 j, hj1 j, hDsR, hε0.le, hε1', hmR]
  have habel_hyp : ∀ j : Fin ds,
      |(nT j : ℝ) - (m : ℝ) * Dint * ((j : ℝ) / ds)| ≤ (m : ℝ) * Dint * (3 * ε + 1 / Dint) := by
    intro j
    have h1 := hnum_hi j
    have h1' := hnum_lo j
    have hexp : (m : ℝ) * ((Ds : ℝ) + 1) * (3 * ε + 1 / ((Ds : ℝ) + 1))
        = 3 * (m : ℝ) * ε * ((Ds : ℝ) + 1) + (m : ℝ) := by
      field_simp
    rw [hnTapply j, hDintR, hexp]
    rw [abs_le]
    constructor <;> nlinarith [h1, h1', hδmε, hj0 j, hj1 j, hDsR, hε0.le, hε1', hmR]
  have hbound4 : A * (L (Fin.last l) - (1 / (m : ℝ) ^ 2) * Ssum)
      - ((m : ℝ) * ds * Dint) * B * (3 * ε + 1 / Dint + 16 * ((l : ℝ) + 1) / ds)
      ≤ ∑ s : Fin ds, (n s : ℝ) * L (κ s) := by
    have hab := abel_sum_bound (l := l) m Dint hm hds0 γ hγ0 hγlast hγmono L B hB0 hLB
      (fun j : Fin ds => nT j) (3 * ε + 1 / Dint) (by positivity) habel_hyp
    have hsum : ∑ j : Fin ds, (nT j : ℝ) * L (blockIdx m γ j) = ∑ s : Fin ds, (n s : ℝ) * L (κ s) := by
      rw [sum_comp_blockIdx m γ L (fun s => n s) π]
      exact Finset.sum_congr rfl (fun j _ => by rw [hnTapply j])
    have hab0 := hab
    rw [hsum] at hab0
    have hab' : ((m : ℝ) * ds * Dint / 2) * (L (Fin.last l) - (1 / (m : ℝ) ^ 2) * Ssum)
        ≤ ∑ s : Fin ds, (n s : ℝ) * L (κ s)
          + ((m : ℝ) * ds * Dint) * B * (3 * ε + 1 / Dint + 16 * ((l : ℝ) + 1) / ds) := by
      rw [hSsumdef]
      exact hab0
    rw [hAdef]
    linarith [hab']
  -- ✦ (B3) the denominator arithmetic
  have hQTdeg : ∀ i j, (QT i).degreeOf j < Dint := by
    intro i j
    have h1 := MvPolynomial.degreeOf_rename_of_injective (p := Q (i ∘ π.symm)) π.symm.injective (π j)
    have h2 : π.symm (π j) = j := by simp
    rw [h2] at h1
    have h3 : QT i = MvPolynomial.rename π.symm (Q (i ∘ π.symm)) := rfl
    rw [h3, h1]
    exact lt_of_le_of_lt (hQdeg (i ∘ π.symm) (π j)) (Nat.lt_succ_self Ds)
  have hQTbal : ∀ i, QT i ≠ 0 → Balanced i := by
    intro i hi
    have h1 : Q (i ∘ π.symm) ≠ 0 := by
      intro h
      exact hi (by rw [hQTdef]; simp [h])
    have h2 := hQaux.1 (i ∘ π.symm) h1
    intro s
    have h3 : (Finset.univ.filter (fun j : Fin ds => (i ∘ π.symm) j = s)).card = ds / m := h2 s
    have himg : (Finset.univ.filter (fun j : Fin ds => i (π.symm j) = s))
        = (Finset.univ.filter (fun j : Fin ds => i j = s)).map ⟨π, π.injective⟩ := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Function.Embedding.coeFn_mk]
      constructor
      · intro ha; exact ⟨π.symm a, by simpa using ha, by simp⟩
      · rintro ⟨j, hj, hja⟩
        rw [← hja]; simpa using hj
    have h4 : (Finset.univ.filter (fun j : Fin ds => (i ∘ π.symm) j = s)).card
        = (Finset.univ.filter (fun j : Fin ds => i j = s)).card := by
      have h5 : (Finset.univ.filter (fun j : Fin ds => (i ∘ π.symm) j = s))
          = (Finset.univ.filter (fun j : Fin ds => i (π.symm j) = s)) := rfl
      rw [h5, himg, Finset.card_map]
    rw [← h4]; exact h3
  have hQTint : ∀ i k, ∃ a : ℤ, (QT i).coeff k = a := by
    intro i k
    have hmap : Finsupp.mapDomain π.symm
        (Finsupp.equivFunOnFinite.symm (fun y => k (π.symm y))) = k := by
      ext x
      have h3 := Finsupp.mapDomain_apply_of_injective (f := π.symm) π.symm.injective
        (Finsupp.equivFunOnFinite.symm (fun y => k (π.symm y))) (π x)
      simp only [Equiv.symm_apply_apply] at h3
      rw [h3]
      simp
    have h1 : (QT i).coeff k
        = (Q (i ∘ π.symm)).coeff (Finsupp.equivFunOnFinite.symm (fun y => k (π.symm y))) := by
      rw [hQTdef]
      have h2 := MvPolynomial.coeff_rename_mapDomain π.symm π.symm.injective
        (Q (i ∘ π.symm)) (Finsupp.equivFunOnFinite.symm (fun y => k (π.symm y)))
      rw [hmap] at h2
      exact h2
    rw [h1]
    exact hQaux.2.2.1 (i ∘ π.symm) _
  have hnTmono : Monotone (fun j : Fin ds => nT j) := by
    intro a b hab
    show nT a ≤ nT b
    rw [hnTapply a, hnTapply b]
    exact hπmono' hab
  have hcoeffT : MvPowerSeries.coeff nT (auxSeries f' QT) ≠ 0 := by
    rw [coeff_rename_auxSeries f' Q π n]
    exact_mod_cast hnβ'
  have hden := hDld ds hdsd₁ hmdvd Dint
    (le_trans hDsDld (Nat.le_succ Ds)) ε hε0 hεε₁ (fun j : Fin ds => nT j) hnTmono
    hbox QT hQTbal hQTdeg hQTint nT (fun j => rfl) hcoeffT
  have hbound3 : -(A * (tauFlat b + tauSharpAt e ξ + η))
      ≤ Real.log ‖((β : ℚ) : ℂ)‖ := by
    have hrat : ((m : ℝ) * ds * Dint / 2) * (tauFlat b + tauSharpAt e ξ + η)
        = A * (tauFlat b + tauSharpAt e ξ + η) := by rw [hAdef]
    have hden' : Real.log ((Rat.den β : ℕ) : ℝ)
        ≤ A * (tauFlat b + tauSharpAt e ξ + η) := by
      rw [hrat] at hden
      rw [coeff_rename_auxSeries f' Q π n, ← hβdef] at hden
      exact hden
    have h2 : -Real.log ((Rat.den β : ℕ) : ℝ) ≤ Real.log ‖((β : ℚ) : ℂ)‖ := by
      have h := neg_log_den_le_log (MvPowerSeries.coeff nT (auxSeries f' QT)) hcoeffT
      rw [coeff_rename_auxSeries f' Q π n, ← hβdef] at h
      exact h
    linarith
  -- ✦ (B1) + (B2): the cleared composite, the Jensen bound and the integral bound
  set Ψ : Fin ds → ℂ → ℂ := fun s => ψ (κ s) with hΨdef
  set Ns : Fin m → Fin ds → ℂ → ℂ := fun i s => N i (κ s) with hNsdef
  set Ps : Fin m → Fin ds → Polynomial ℂ := fun i s => P i (κ s) with hPsdef
  set Φs : Fin ds → PowerSeries ℂ := fun s => Φ (κ s) with hΦsdef
  set Qc : (Fin ds → Fin m) → MvPolynomial (Fin ds) ℂ :=
    fun i => MvPolynomial.map (algebraMap ℚ ℂ) (Q i) with hQcdef
  set Gm : (Fin ds → ℂ) → ℂ := clearedFun Qc Ψ Ns Ps with hGmdef
  set g : MvPowerSeries (Fin ds) ℂ := uPoly Ps *
    diagComp Φs (auxSeriesC (fun i => PowerSeries.map (algebraMap ℚ ℂ) (f' i)) Qc) with hgdef
  have hΦ1ne : ∀ s : Fin ds, PowerSeries.coeff 1 (Φs s) ≠ 0 := by
    intro s
    rw [hΦsdef]
    rw [hΦ1 (κ s), hψderiv (κ s)]
    exact mul_ne_zero (by exact_mod_cast hρ0.ne')
      (norm_ne_zero_iff.mp (ne_of_gt (hderiv (κ s))))
  have hTaylor := cleared_taylor f' Q Ψ Φs (1 / ρ) hρdiv1
    (fun s => hψa (κ s)) (fun s => hψ0 (κ s)) (fun s z hz => hΦsum (κ s) z hz)
    Ns Ps (fun i s => hPull i (κ s))
  have hGHas : ∀ z : Fin ds → ℂ, (∀ j, ‖z j‖ ≤ ρ') →
      HasSum (fun mm : Fin ds →₀ ℕ => MvPowerSeries.coeff mm g * ∏ j, z j ^ (mm j)) (Gm z) := by
    intro z hz
    have h := hTaylor z (fun s => lt_of_le_of_lt (hz s) hρ'lt)
    simpa [hgdef, hGmdef, hQcdef] using h
  have hminC : ∀ nn : Fin ds →₀ ℕ, nn.degree < n.degree →
      MvPowerSeries.coeff nn (auxSeriesC (fun i => PowerSeries.map (algebraMap ℚ ℂ) (f' i))
        Qc) = 0 := by
    intro nn hnn
    have h := hnmin' nn hnn
    rw [hQcdef]
    rw [auxSeriesC_map, MvPowerSeries.coeff_map, h]
    simp
  have hminG : ∀ mm : Fin ds →₀ ℕ, mm.degree < n.degree → MvPowerSeries.coeff mm g = 0 := by
    intro mm hm
    rw [hgdef,
      coeff_mul_eq_of_min (uPoly Ps) _ (fun m' hm' => diagComp_vanishes_below Φs _ n hminC m'
        (lt_trans hm' hm)) rfl,
      diagComp_vanishes_below Φs _ n hminC mm hm, mul_zero]
  have hlexC : ∀ mm : Fin ds →₀ ℕ, mm.degree = n.degree →
      MvPowerSeries.coeff mm (auxSeriesC (fun i => PowerSeries.map (algebraMap ℚ ℂ) (f' i)) Qc) ≠ 0 →
      mm = n ∨ ∃ j : Fin ds, (∀ i : Fin ds, i < j → mm i = n i) ∧ n j < mm j := by
    intro mm hd hm
    rw [hQcdef] at hm
    rw [auxSeriesC_map, MvPowerSeries.coeff_map] at hm
    exact hnlex mm hd (fun h => hm (by rw [← h]; simp))
  have hlexG : ∀ mm : Fin ds →₀ ℕ, mm.degree = n.degree → MvPowerSeries.coeff mm g ≠ 0 →
      mm = n ∨ ∃ j : Fin ds, (∀ i : Fin ds, i < j → mm i = n i) ∧ n j < mm j := by
    intro mm hd hm
    rw [hgdef, coeff_mul_eq_of_min (uPoly Ps) _ (fun m' hm' => diagComp_vanishes_below Φs _ n
      hminC m' (lt_of_lt_of_eq hm' hd)) rfl] at hm
    have hm' : MvPowerSeries.coeff mm (diagComp Φs (auxSeriesC
        (fun i => PowerSeries.map (algebraMap ℚ ℂ) (f' i)) Qc)) ≠ 0 := by
      intro hc
      exact hm (by rw [hc, mul_zero])
    exact lexmin_transfer Φs _ n (fun s => hΦ0 (κ s)) hminC hlexC (fun s => hΦ1ne s) mm hd hm'
  have hcleared_ne : MvPowerSeries.coeff n g ≠ 0 := by
    rw [hgdef]
    exact coeff_cleared_ne_zero f' Q Φs Ps n (fun s => hΦ0 (κ s)) hnβ'
      (fun i s => (hPull i (κ s)).1) (fun s => hΦ1ne s) hminC
  -- the constants of the pointwise bound
  set Cpt : ℝ := ε * ds * Ds + ds * Real.log Dint + ds * Real.log (m : ℝ)
    + ds * Real.log (max 1 M) with hCptdef
  set δJ : ℝ := Real.exp (Cpt - ds * Ds * G0 - 1) with hδJdef
  have hδJ0 : 0 < δJ := Real.exp_pos _
  -- the smoothed Jensen bound
  have hJensen := mv_lexmin_coeff_le_integral_smoothed g Gm ρ' hρ'1 hGHas n hcleared_ne hminG
    hlexG δJ hδJ0
  -- the value of the coefficient
  have hΦ0s : ∀ s : Fin ds, PowerSeries.coeff 0 (Φs s) = 0 := fun s => by
    rw [hΦsdef]; exact hΦ0 (κ s)
  have hcoeffid := coeff_cleared_eq f' Q Φs Ps n hΦ0s hminC
  have hcoeffid' : MvPowerSeries.coeff n g
      = (∏ s : Fin ds, ∏ i : Fin m, (Ps i s).eval 0) * (((auxSeries f' Q).coeff n : ℚ) : ℂ)
        * ∏ s : Fin ds, (PowerSeries.coeff 1 (Φs s)) ^ (n s) := by
    rw [hgdef]
    exact hcoeffid
  set lnu0 : ℝ := Real.log ‖∏ s : Fin ds, ∏ i : Fin m, (Ps i s).eval 0‖ with hlnu0def
  set Tsum : ℝ := ∑ s : Fin ds, (n s : ℝ) * L (κ s) with hTsumdef
  have hLval : ∀ k : Fin (l + 1), L k = Real.log ‖deriv (ψ k) 0‖ := fun k => rfl
  have hbound1 : lnu0 + Real.log ‖((β : ℚ) : ℂ)‖ + Tsum ≤
      ∫ t : Fin ds → ℝ, Real.log (‖Gm (tor t)‖ + δJ) ∂(torMeasure ds) := by
    have hprod1 : (∏ s : Fin ds, ∏ i : Fin m, (Ps i s).eval 0) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun s _ => Finset.prod_ne_zero_iff.mpr
        (fun i _ => (hPull i (κ s)).1))
    have hprod2 : (((auxSeries f' Q).coeff n : ℚ) : ℂ) ≠ 0 := by
      rw [← hβdef]; exact_mod_cast hβne
    have hprod3 : (∏ s : Fin ds, (PowerSeries.coeff 1 (Φs s)) ^ (n s)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun s _ => pow_ne_zero _ (hΦ1ne s))
    have hnorm : ‖MvPowerSeries.coeff n g‖
        = ‖∏ s : Fin ds, ∏ i : Fin m, (Ps i s).eval 0‖
          * ‖((β : ℚ) : ℂ)‖
          * ∏ s : Fin ds, ‖PowerSeries.coeff 1 (Φs s)‖ ^ (n s) := by
      rw [hcoeffid', hβdef]
      simp only [norm_mul, norm_prod, norm_pow]
    have hprod1n : ‖∏ s : Fin ds, ∏ i : Fin m, (Ps i s).eval 0‖ ≠ 0 :=
      norm_ne_zero_iff.mpr hprod1
    have hprod2n : ‖((β : ℚ) : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr hprod2
    have hprod3n : (∏ s : Fin ds, ‖PowerSeries.coeff 1 (Φs s)‖ ^ (n s)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun s _ =>
        pow_ne_zero _ (norm_ne_zero_iff.mpr (hΦ1ne s)))
    have hlog : Real.log ‖MvPowerSeries.coeff n g‖
        = lnu0 + Real.log ‖((β : ℚ) : ℂ)‖
          + ∑ s : Fin ds, (n s : ℝ) * L (κ s) := by
      rw [hnorm, hlnu0def, Real.log_mul (mul_ne_zero hprod1n hprod2n) hprod3n,
        Real.log_mul hprod1n hprod2n, Real.log_prod]
      · congr 1
        refine Finset.sum_congr rfl (fun s _ => ?_)
        rw [Real.log_pow, hΦsdef, hΦ1 (κ s), hLval (κ s)]
      · intro s _
        exact pow_ne_zero _ (norm_ne_zero_iff.mpr (hΦ1ne s))
    rw [← hlog]
    exact hJensen
  -- the pointwise bound and the integral bound
  set K : Finset (Fin ds →₀ ℕ) := Finset.univ.biUnion (fun i => (Q i).support) with hKdef
  have hQcsupp : ∀ i, (Qc i).support = (Q i).support := by
    intro i
    rw [hQcdef]
    exact MvPolynomial.support_map_of_injective (Q i) (algebraMap ℚ ℂ).injective
  have hKsup : ∀ i, (Q i).support ⊆ K := fun i k hk =>
    Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hk⟩
  have hKsupc : ∀ i, (Qc i).support ⊆ K := fun i k hk =>
    hKsup i (by rw [← hQcsupp i]; exact hk)
  have hsumzero : ∀ QQ : (Fin ds → Fin m) → MvPolynomial (Fin ds) ℚ,
      (∀ i, QQ i = 0) → auxSeries f' QQ = 0 := by
    intro QQ hQ
    rw [auxSeries]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    have h2 : ((QQ i : MvPolynomial (Fin ds) ℚ) : MvPowerSeries (Fin ds) ℚ) = 0 := by
      rw [hQ i]
      ext n
      simp
    rw [h2, zero_mul]
  have hKne : K.Nonempty := by
    by_contra hempty
    have hzero : ∀ i : Fin ds → Fin m, Q i = 0 := by
      intro i
      by_contra hi
      have hne : ∃ k, (Q i).coeff k ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hi (MvPolynomial.ext (Q i) 0 (fun k => by
          rw [MvPolynomial.coeff_zero]
          exact hcon k))
      obtain ⟨k, hk⟩ := hne
      exact hempty ⟨k, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
        MvPolynomial.mem_support_iff.mpr hk⟩⟩
    exact hQne (hsumzero Q hzero)
  have hKdegN : ∀ k ∈ K, ∀ j : Fin ds, k j ≤ Ds := by
    intro k hk j
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hk
    exact (hQaux.2.1 i k hi).1 j
  have hKdeg : ∀ k ∈ K, ∀ j : Fin ds, (k j : ℝ) ≤ Ds := fun k hk j =>
    Nat.cast_le.mpr (hKdegN k hk j)
  have hKdisc : ∀ k ∈ K, Submission.CDT.Discrepancy.disc (fun j : Fin ds => (k j : ℝ) / Ds) < ε := by
    intro k hk
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hk
    exact (hQaux.2.1 i k hi).2
  have hQc_coeff : ∀ i : Fin ds → Fin m, ∀ k, (Qc i).coeff k
      = ((((Q i).coeff k : ℚ)) : ℂ) := by
    intro i k
    rw [hQcdef, MvPolynomial.coeff_map]
    rfl
  have hNrc : ∀ i, (((Qc i).support.card : ℝ)) ≤ (Dint : ℝ) ^ ds := by
    intro i
    have h1 : (Qc i).support.card = (Q i).support.card := by rw [hQcsupp i]
    rw [h1]
    have h2 : ((Q i).support.image
          (fun k : Fin ds →₀ ℕ => (Finsupp.equivFunOnFinite k : Fin ds → ℕ)))
        ⊆ Fintype.piFinset (fun _ : Fin ds => Finset.range (Ds + 1)) := by
      intro f hf
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hf
      rw [Fintype.mem_piFinset]
      intro j
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le ((hQaux.2.1 i k hk).1 j)
    have h3 : ((Q i).support.image
          (fun k : Fin ds →₀ ℕ => (Finsupp.equivFunOnFinite k : Fin ds → ℕ))).card
        ≤ (Fintype.piFinset (fun _ : Fin ds => Finset.range (Ds + 1))).card :=
      Finset.card_le_card h2
    rw [Finset.card_image_of_injective (Q i).support Finsupp.equivFunOnFinite.injective] at h3
    have h4 : (Fintype.piFinset (fun _ : Fin ds => Finset.range (Ds + 1))).card
        = (Ds + 1) ^ ds := by
      rw [Fintype.card_piFinset]
      simp [Finset.card_range]
    rw [h4] at h3
    have h5 : (Ds + 1) ^ ds = Dint ^ ds := by rw [hDintdef]
    rw [h5] at h3
    exact_mod_cast h3
  have hQc_coeffb : ∀ i k, k ∈ (Qc i).support → ‖(Qc i).coeff k‖
      ≤ Real.exp (ε * ds * Ds) := by
    intro i k hk
    rw [hQc_coeff i k, norm_ratCast_complex]
    exact hQaux.2.2.2 i k
  have hU : ∀ i s z, ‖z‖ = 1 →
      ‖Ns i s z * ∏ i' ∈ Finset.univ.erase i, (Ps i' s).eval z‖ ≤ max 1 M := by
    intro i s z hz
    exact le_trans (hMbound i (κ s) z hz) (le_max_right _ _)
  have hpt : ∀ t : Fin ds → ℝ, Gm (tor t) ≠ 0 →
      Real.log ‖Gm (tor t)‖ ≤ Cpt + K.sup' hKne
        (fun k : Fin ds →₀ ℕ => ∑ s : Fin ds, (k s : ℝ) * circleLog (Ψ s) (t s)) := by
    intro t ht
    have hz : ∀ s, ‖tor t s‖ = 1 := fun s => norm_tor t s
    have h := clearedFun_pointwise_bound Qc Ψ Ns Ps (Real.exp (ε * ds * Ds)) (max 1 M)
      ((Dint : ℝ) ^ ds) (Real.one_le_exp (by positivity)) (le_max_left _ _)
      (one_le_pow₀ (by exact_mod_cast hDint0)) (by exact_mod_cast hm)
      hNrc hQc_coeffb K hKne hKsupc hU (tor t) hz (by rw [← hGmdef]; exact ht)
    have hlogE : Real.log (Real.exp (ε * ds * Ds)) = ε * ds * Ds := Real.log_exp _
    have hlogN : Real.log ((Dint : ℝ) ^ ds) = ds * Real.log Dint := by
      rw [Real.log_pow]
    have hsup : ∀ s : Fin ds, Real.log ‖Ψ s (tor t s)‖ = circleLog (Ψ s) (t s) := fun s => rfl
    rw [hGmdef, hCptdef]
    rw [hlogE, hlogN] at h
    simpa [hsup] using h
  have hint : Integrable (fun t : Fin ds → ℝ => K.sup' hKne
      (fun k : Fin ds →₀ ℕ => ∑ s : Fin ds, (k s : ℝ) * circleLog (Ψ s) (t s)))
      (torMeasure ds) :=
    integrable_sup_circleLog K hKne ψ κ (Ds : ℝ) G0 hcont hg hKdeg (Nat.cast_nonneg _) hG00
  have hFint : Integrable (fun t : Fin ds → ℝ => Cpt + K.sup' hKne
      (fun k : Fin ds →₀ ℕ => ∑ s : Fin ds, (k s : ℝ) * circleLog (Ψ s) (t s)))
      (torMeasure ds) := (integrable_const Cpt).add hint
  obtain ⟨hbnd_meas, hbnd_B⟩ := mv_lex_measurable_norm_G g Gm hρ'1 hGHas
  have hδJF : ∀ᵐ t ∂(torMeasure ds), Real.log δJ ≤ Cpt + K.sup' hKne
      (fun k : Fin ds →₀ ℕ => ∑ s : Fin ds, (k s : ℝ) * circleLog (Ψ s) (t s)) := by
    have hae : ∀ᵐ t ∂(torMeasure ds), ∀ s : Fin ds, t s ∈ Set.Icc (0:ℝ) 1 :=
      MeasureTheory.ae_all_iff.2 (fun s => ae_eval_mem_Icc s)
    filter_upwards [hae] with t ht
    obtain ⟨k0, hk0⟩ := hKne
    have hlow : -(ds : ℝ) * Ds * G0 ≤ ∑ s : Fin ds, (k0 s : ℝ) * circleLog (Ψ s) (t s) := by
      have h1 : ∀ s : Fin ds, -(G0) ≤ circleLog (Ψ s) (t s) := by
        intro s
        have h2 := hg (κ s) (t s) (ht s)
        have h3 : circleLog (ψ (κ s)) (t s) = circleLog (Ψ s) (t s) := by rw [hΨdef]
        linarith [abs_le.mp h2]
      calc -(ds : ℝ) * Ds * G0 = ∑ _s : Fin ds, -(Ds * G0) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
        _ ≤ ∑ s : Fin ds, (k0 s : ℝ) * circleLog (Ψ s) (t s) := by
            refine Finset.sum_le_sum (fun s _ => ?_)
            have h4 : (k0 s : ℝ) ≤ Ds := hKdeg k0 hk0 s
            have h5 : (k0 s : ℝ) * (-(G0)) ≤ (k0 s : ℝ) * circleLog (Ψ s) (t s) :=
              mul_le_mul_of_nonneg_left (h1 s) (Nat.cast_nonneg _)
            have h6 : (k0 s : ℝ) * G0 ≤ (Ds : ℝ) * G0 := mul_le_mul_of_nonneg_right h4 hG00
            nlinarith [h5, h6]
    rw [hδJdef, Real.log_exp]
    have hlow' : -(ds : ℝ) * Ds * G0 - 1 ≤
        ∑ s : Fin ds, (k0 s : ℝ) * circleLog (Ψ s) (t s) := by linarith [hlow]
    have hmid : Real.log δJ ≤ Cpt + ∑ s : Fin ds, (k0 s : ℝ) * circleLog (Ψ s) (t s) := by
      rw [hδJdef, Real.log_exp]
      linarith [hlow']
    have hsupp := Finset.le_sup' (f := fun k : Fin ds →₀ ℕ =>
      ∑ s : Fin ds, (k s : ℝ) * circleLog (Ψ s) (t s)) hk0
    linarith [hmid, hsupp]
  have hcmp := integral_log_add_le_of_pointwise hFint hbnd_meas hbnd_B hδJ0 hδJF
    (Filter.Eventually.of_forall hpt)
  have hKdisc' : ∀ k ∈ K, Submission.CDT.Discrepancy.disc
      (fun j : Fin ds => (k j : ℝ) / ((Ds : ℝ) + 1)) ≤ ε + 2 / ((Ds : ℝ) + 1) := by
    intro k hk
    have h1 := hKdisc k hk
    have h2 : Submission.CDT.Discrepancy.disc (fun j : Fin ds => (k j : ℝ) / ((Ds : ℝ) + 1))
        ≤ Submission.CDT.Discrepancy.disc (fun j : Fin ds => (k j : ℝ) / (Ds : ℝ))
          + 2 * (1 / ((Ds : ℝ) + 1)) := by
      refine disc_le_disc_add (fun j : Fin ds => (k j : ℝ) / (Ds : ℝ))
        (fun j : Fin ds => (k j : ℝ) / ((Ds : ℝ) + 1)) ?_ ?_ (by positivity) ?_
      · intro j
        exact ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
          by rw [div_le_one (by positivity)]; exact_mod_cast hKdeg k hk j⟩
      · intro j
        exact ⟨div_nonneg (Nat.cast_nonneg _) (by positivity),
          by rw [div_le_one (by positivity)]; linarith [hKdeg k hk j]⟩
      · intro j
        have hk0 : (0:ℝ) ≤ (k j : ℝ) := Nat.cast_nonneg _
        have h5 : (k j : ℝ) ≤ Ds := hKdeg k hk j
        have hD0 : (0:ℝ) < (Ds:ℝ) := by positivity
        have hD1 : (0:ℝ) < (Ds:ℝ) + 1 := by positivity
        rw [abs_sub_comm, abs_of_nonneg (by
          rw [sub_nonneg]
          exact div_le_div_of_nonneg_left hk0 hD0 (by linarith))]
        rw [div_sub_div _ _ (ne_of_gt hD0) (ne_of_gt hD1)]
        rw [div_le_iff₀ (by positivity : (0:ℝ) < (Ds : ℝ) * ((Ds : ℝ) + 1))]
        have h6 : (1 / ((Ds : ℝ) + 1)) * ((Ds : ℝ) * ((Ds : ℝ) + 1)) = (Ds : ℝ) := by
          field_simp
        rw [h6]
        nlinarith [h5, hk0, hD0]
    have h1' := le_of_lt h1
    have h7 : (2:ℝ) * (1 / ((Ds : ℝ) + 1)) = 2 / ((Ds : ℝ) + 1) := by ring
    rw [h7] at h2
    linarith [h2, h1']
  have hint_sup := integral_sup_bound (l := l) hds0 K hKne (Ds + 1) hDint0
    (fun k hk j => Nat.lt_succ_of_le (hKdegN k hk j))
    (ε + 2 / ((Ds : ℝ) + 1)) (by positivity) (by simpa using hKdisc') ψ κ
    (fun k => (γ k.succ - γ k.castSucc) / m) hcκ hG00 hcont hg
  have hbound2 : (∫ t : Fin ds → ℝ, Real.log (‖Gm (tor t)‖ + δJ) ∂(torMeasure ds))
      ≤ A * (1 / (m : ℝ)) * rearr
        + (Cpt + Real.log 2
          + ((Dint : ℝ) / (2 * ds)) * (8 * ((l : ℝ) + 1) ^ 2 * ((ds : ℝ) + 1) + ds) * G0
          + (Dint : ℝ) * (ε + 2 / Dint + 1 / ds) * ds * G0) := by
    have h1 : (∫ t : Fin ds → ℝ, Real.log (‖Gm (tor t)‖ + δJ) ∂(torMeasure ds)) ≤
        (∫ t : Fin ds → ℝ, (Cpt + K.sup' hKne (fun k : Fin ds →₀ ℕ =>
          ∑ s : Fin ds, (k s : ℝ) * circleLog (Ψ s) (t s))) ∂(torMeasure ds))
          + Real.log 2 := hcmp
    have h2 : (∫ t : Fin ds → ℝ, (Cpt + K.sup' hKne (fun k : Fin ds →₀ ℕ =>
          ∑ s : Fin ds, (k s : ℝ) * circleLog (Ψ s) (t s))) ∂(torMeasure ds))
        = Cpt + ∫ t : Fin ds → ℝ, K.sup' hKne (fun k : Fin ds →₀ ℕ =>
          ∑ s : Fin ds, (k s : ℝ) * circleLog (Ψ s) (t s)) ∂(torMeasure ds) := by
      rw [integral_add (integrable_const Cpt) hint, integral_const, probReal_univ, one_smul]
    have h3 : (∫ t : Fin ds → ℝ, K.sup' hKne (fun k : Fin ds →₀ ℕ =>
          ∑ s : Fin ds, (k s : ℝ) * circleLog (Ψ s) (t s)) ∂(torMeasure ds))
        ≤ (((Ds : ℝ) + 1) / (2 * ds)) * ((ds : ℝ) ^ 2 * rearr
            + (8 * ((l : ℝ) + 1) ^ 2 * ((ds : ℝ) + 1) + ds) * G0)
          + ((Ds : ℝ) + 1) * (ε + 2 / ((Ds : ℝ) + 1) + 1 / ds) * ds * G0 := by
      have h := hint_sup
      push_cast at h
      rw [hrearrdef]
      exact h
    rw [hrearrdef] at h3
    have key : A * (1 / (m : ℝ)) * rearr + (Cpt + Real.log 2
          + ((Dint : ℝ) / (2 * ds)) * (8 * ((l : ℝ) + 1) ^ 2 * ((ds : ℝ) + 1) + ds) * G0
          + (Dint : ℝ) * (ε + 2 / Dint + 1 / ds) * ds * G0)
        = ((Ds : ℝ) + 1) / (2 * ds) * ((ds : ℝ) ^ 2
              * rearrInt (fun k => (γ k.succ - γ k.castSucc) / m) ψ
            + (8 * ((l : ℝ) + 1) ^ 2 * ((ds : ℝ) + 1) + ds) * G0)
          + ((Ds : ℝ) + 1) * (ε + 2 / ((Ds : ℝ) + 1) + 1 / ds) * ds * G0
          + (Cpt + Real.log 2) := by
      have hdsne : ((ds : ℕ) : ℝ) ≠ 0 := by positivity
      have hmne : ((m : ℕ) : ℝ) ≠ 0 := by positivity
      rw [hAdef, hDintdef]
      field_simp
      push_cast
      ring
    rw [key]
    linarith [h1, h2, h3]
  -- ═══════════ 8. the final assembly
  -- TODO (see `NOTES_DESIGN.md`, "SESSION 4 STATUS"): combine `hbound1`–`hbound4` with
  -- `final_sift`, then bound the resulting error by `η₁` using `hErrs` (`sieveErr ≤ η₁`) and the
  -- term-by-term comparison `(2/(ds*Dint))*(errC+errE+|lnu0|) ≤` the sieveErr expression with `Ds`,
  -- plus `|lnu0| ≤ ds*U0`; finally rewrite `L (Fin.last l)` and the `Ssum` sum into the
  -- statement's `deriv (fun z => φ k (ρ*z))` / `log(‖deriv (φ k.succ) 0‖/‖deriv (φ k.castSucc) 0‖)`.
  set errC : ℝ := Cpt + Real.log 2
    + ((Dint : ℝ) / (2 * ds)) * (8 * ((l : ℝ) + 1) ^ 2 * ((ds : ℝ) + 1) + ds) * G0
    + (Dint : ℝ) * (ε + 2 / Dint + 1 / ds) * ds * G0 with herrCdef
  set errE : ℝ := ((m : ℝ) * ds * Dint) * B * (3 * ε + 1 / Dint + 16 * ((l : ℝ) + 1) / ds)
    with herrEdef
  have lnu0b : |lnu0| ≤ (ds : ℝ) * U0 := by
    have hprod : ∀ s : Fin ds, ∏ i : Fin m, (Ps i s).eval 0 ≠ 0 := fun s =>
      Finset.prod_ne_zero_iff.mpr (fun i _ => (hPull i (κ s)).1)
    have hlog : lnu0 = ∑ s : Fin ds, ∑ i : Fin m, Real.log ‖(Ps i s).eval 0‖ := by
      rw [hlnu0def, norm_prod, Real.log_prod]
      · refine Finset.sum_congr rfl (fun s _ => ?_)
        rw [norm_prod, Real.log_prod]
        intro i _
        exact norm_ne_zero_iff.mpr ((hPull i (κ s)).1)
      · intro s _
        exact norm_ne_zero_iff.mpr (hprod s)
    calc |lnu0| = |∑ s : Fin ds, ∑ i : Fin m, Real.log ‖(Ps i s).eval 0‖| := by rw [hlog]
      _ ≤ ∑ s : Fin ds, |∑ i : Fin m, Real.log ‖(Ps i s).eval 0‖| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s : Fin ds, ∑ i : Fin m, |Real.log ‖(Ps i s).eval 0‖| :=
          Finset.sum_le_sum (fun s _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _s : Fin ds, U0 := by
          refine Finset.sum_le_sum (fun s _ => ?_)
          rw [hU0def]
          refine Finset.sum_le_sum (fun i _ => ?_)
          exact Finset.single_le_sum (f := fun p : Fin (l + 1) => |Real.log ‖(P i p).eval 0‖|)
            (fun p _ => abs_nonneg _) (Finset.mem_univ (κ s))
      _ = (ds : ℝ) * U0 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hS1 := final_sift (l := l) hm hds0 hDint0 γ L rearr
    (∫ t : Fin ds → ℝ, Real.log (‖Gm (tor t)‖ + δJ) ∂(torMeasure ds)) Tsum lnu0
    (Real.log ‖((β : ℚ) : ℂ)‖) (tauFlat b + tauSharpAt e ξ) η errC errE |lnu0|
    (by simpa [hlnu0def] using hbound1)
    (by rw [hAdef] at hbound2; rw [herrCdef]; exact hbound2)
    (by rw [hAdef] at hbound3; exact hbound3)
    (by rw [hAdef] at hbound4; rw [herrEdef]; exact hbound4)
    (neg_le_abs lnu0) hη0.le
  have herr : ((m : ℝ) / ((m : ℝ) * ds * Dint / 2)) *
      (errC + errE + |lnu0| + ((m : ℝ) * ds * Dint / 2) * η) ≤ η₁ := by
    rw [mul_div_eta_identity (A := (m : ℝ) * ds * Dint / 2) (B := (ds : ℝ) * Dint)
      (Y := errC + errE + |lnu0|) (ne_of_gt hmR) (by positivity) (by ring)]
    rw [hηdef, hDintR]
    have herrC' : errC = ε * ds * Ds + ds * Real.log ((Ds : ℝ) + 1) + ds * Real.log (m : ℝ)
        + ds * Real.log (max 1 M) + Real.log 2
        + (((Ds : ℝ) + 1) / (2 * ds)) * (8 * ((l : ℝ) + 1) ^ 2 * ((ds : ℝ) + 1) + ds) * G0
        + ((Ds : ℝ) + 1) * (ε + 2 / ((Ds : ℝ) + 1) + 1 / ds) * ds * G0 := by
      rw [herrCdef, hCptdef, hDintR]
    have herrE' : errE = (m : ℝ) * ds * ((Ds : ℝ) + 1) * B
        * (3 * ε + 1 / ((Ds : ℝ) + 1) + 16 * ((l : ℝ) + 1) / ds) := by
      rw [herrEdef, hDintR]
    exact sieve_err_compare hm hds0 hDs1 hε0.le hG00 hB0 hU00 hM'1 lnu0b herrC' herrE' hErrs
  have hfin1 : (m : ℝ) * (L (Fin.last l) - (tauFlat b + tauSharpAt e ξ)) ≤
      rearr + (1 / (m : ℝ)) * Ssum + η₁ := by linarith [hS1, herr]
  have hLlast : L (Fin.last l) = Real.log ‖deriv (fun z : ℂ => φ (Fin.last l) (ρ * z)) 0‖ := by
    simp only [hLdef, hψeq]
  have hrearr' : rearr = rearrInt (fun k => (γ k.succ - γ k.castSucc) / m)
      (fun k z => φ k (ρ * z)) := by
    simp only [hrearrdef, hψeq]
  have hsumeq : (1 / (m : ℝ)) * Ssum = (1 / (m : ℝ)) * ∑ k : Fin l,
      (γ k.succ.castSucc) ^ 2 * Real.log (‖deriv (φ k.succ) 0‖ / ‖deriv (φ k.castSucc) 0‖) := by
    rw [hSsumdef]
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have h1 : L k.succ = Real.log ρ + Real.log ‖deriv (φ k.succ) 0‖ := by
      simp only [hLdef, hψderiv k.succ, norm_mul, hnormρ]
      rw [Real.log_mul (ne_of_gt hρ0) (ne_of_gt (hderiv k.succ))]
    have h2 : L k.castSucc = Real.log ρ + Real.log ‖deriv (φ k.castSucc) 0‖ := by
      simp only [hLdef, hψderiv k.castSucc, norm_mul, hnormρ]
      rw [Real.log_mul (ne_of_gt hρ0) (ne_of_gt (hderiv k.castSucc))]
    have h3 : (Real.log ρ + Real.log ‖deriv (φ k.succ) 0‖)
        - (Real.log ρ + Real.log ‖deriv (φ k.castSucc) 0‖)
        = Real.log (‖deriv (φ k.succ) 0‖ / ‖deriv (φ k.castSucc) 0‖) := by
      rw [Real.log_div (ne_of_gt (hderiv k.succ)) (ne_of_gt (hderiv k.castSucc))]
      ring
    rw [h1, h2, h3]
  rw [hLlast, hrearr', hsumeq] at hfin1
  exact hfin1


end

end Work.Holonomy3
