import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_lvl_err_aux
import Submission.Work.BourgainPlan.Maximal.mst_freeze_defs
import Submission.Work.BourgainPlan.Maximal.mstFreeze_coeff_identity
import Submission.Work.BourgainPlan.Maximal.mstFreeze_xi_bounds
import Submission.Work.BourgainPlan.Maximal.mstHat_sampling_bound

namespace Work.BourgainPlan.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle

/-- Continuity of the bump transform `mstHat Ξ` in the frequency, for continuous `Ξ`. -/
theorem mstHat_continuous_of_continuous {Ξ : ℝ → ℂ} (hΞ : Continuous Ξ) :
    Continuous (fun τ : ℝ => mstHat Ξ τ) := by
  have h_eq : (fun τ : ℝ => mstHat Ξ τ)
      = fun τ : ℝ => ∫ u in (-(1 / 2) : ℝ)..(1 / 2), Ξ u *
          Complex.exp ((((-(2 * Real.pi * τ * u)) : ℝ) : ℂ) * Complex.I) := by
    funext τ
    rw [mstHat_apply]
  rw [h_eq]
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  have h1 : Continuous (fun p : ℝ × ℝ => Ξ p.2) := hΞ.comp continuous_snd
  have h2 : Continuous (fun p : ℝ × ℝ => ((-(2 * Real.pi * p.1 * p.2)) : ℝ)) := by fun_prop
  have h3 : Continuous (fun p : ℝ × ℝ =>
      ((((-(2 * Real.pi * p.1 * p.2)) : ℝ) : ℂ) * Complex.I)) :=
    (Complex.continuous_ofReal.comp h2).mul continuous_const
  exact h1.mul (Complex.continuous_exp.comp h3)

theorem mstFreeze_arc_coeff_bound (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hc : 0 < P.leadingCoeff)
    (l : ℕ) (hl : 1 ≤ l) {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) (M : ℝ) (hM : 0 < M) (hηc : ContDiff ℝ 2 η)
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M) (hη0 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (hder1 : ∀ x : ℝ, |x| * ‖deriv η x‖ ≤ M)
    (hder2 : ∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 η x‖ ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ∀ k : ℕ,
      ∀ β ∈ Work.BourgainPlan.Maximal.mstU l (s + 1),
      Summable (fun m : ℤ => ‖Work.BourgainPlan.Maximal.arcCoeff P l P.natDegree χ η
          (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊) s k β m‖) ∧
      (∑' m : ℤ, ‖Work.BourgainPlan.Maximal.arcCoeff P l P.natDegree χ η
          (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊) s k β m‖)
        ≤ C * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2)) := by
  classical
  obtain ⟨C₂, hC₂pos, s₂, hsz⟩ :=
    mstFreeze_xi_bounds P hd hc l hl hχ0 hχ1 η M hM hηc hηbd hη0 hder1 hder2
  obtain ⟨Clat, hClatpos, hClat⟩ := lattice_shift_inv_sq_bound
  refine ⟨4 * Clat * C₂, by positivity, s₂, ?_⟩
  intro s hs k β hβ
  have hχd : χ + 1 ≤ (P.natDegree : ℝ) := by
    have h2 : (2 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
    linarith
  set c : ℝ := mstScale P.natDegree χ s with hcdef
  set e : ℝ := Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2)) with he
  set Ξ : ℝ → ℂ :=
    mstFreezeXi P ⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊ β (mstScale P.natDegree χ s) η
    with hΞ
  have hcpos : 0 < c := by rw [hcdef]; exact mstScale_pos P.natDegree χ s
  have hc1 : 1 ≤ c := by rw [hcdef]; exact one_le_mstScale hχd s
  have hepos : 0 < e := by rw [he]; exact Real.exp_pos _
  have hboundΞ : ∀ t : ℝ, ‖mstHat Ξ t‖ ≤ C₂ * e := by
    intro t
    rw [hΞ, he]
    exact (hsz s hs β hβ).1 t
  have hdecayΞ : ∀ t : ℝ, t ≠ 0 → ‖mstHat Ξ t‖ ≤ (C₂ * e) / t ^ 2 := by
    intro t ht
    rw [hΞ, he]
    exact (hsz s hs β hβ).2 t ht
  have hsam : ∀ σ₀ : ℝ, Summable (fun m : ℤ => c⁻¹ * ‖mstHat Ξ ((m + σ₀) / c)‖) ∧
      (∑' m : ℤ, c⁻¹ * ‖mstHat Ξ ((m + σ₀) / c)‖)
        ≤ 2 * Clat * (C₂ * e + C₂ * e) :=
    fun σ₀ => mstHat_sampling_le hClat (by positivity) (by positivity) hboundΞ hdecayΞ c σ₀ hc1
  -- continuity of the frozen symbol
  have hΞcont : Continuous Ξ := by
    rw [hΞ]
    exact Continuous.mul
      ((continuous_mstTht_self P ⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊ β (iwRep β)).comp
        (continuous_id.div_const (mstScale P.natDegree χ s))) hηc.continuous
  -- the coefficient identity, with the `star (fourier m β)` factor bounded by one
  have hcoeff : ∀ m : ℤ, ‖arcCoeff P l P.natDegree χ η
        ⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊ s k β m‖
      ≤ ∫ σ in (0 : ℝ)..1,
          c⁻¹ * ‖mstHat Ξ (((m : ℝ) + (toRealPoly P).eval ((2 ^ k : ℝ) * σ)) / c)‖ := by
    intro m
    rw [show arcCoeff P l P.natDegree χ η ⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊ s k β m
          = fourierCoeff (mstFreezeFn P ⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊ P.natDegree
              χ η s k β) m from rfl,
      mstFreezeFn_fourierCoeff P ⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊ P.natDegree χ η
        hηc hη0 s k (hcdef ▸ hc1) β m]
    rw [← hΞ, ← hcdef]
    set I : ℂ := ∫ σ in (0 : ℝ)..1,
      mstHat Ξ (((m : ℝ) + (toRealPoly P).eval ((2 ^ k : ℝ) * σ)) / c) with hI
    have hphase : ‖(fourier (-m)) (((iwRep β : ℝ)) : Circ)‖ = 1 := by
      rw [fourier_apply, Circle.norm_coe]
    have hcinv : ‖(((c : ℝ) : ℂ))⁻¹‖ = c⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos]
    have hInorm : ‖I‖ ≤ ∫ σ in (0 : ℝ)..1,
        ‖mstHat Ξ (((m : ℝ) + (toRealPoly P).eval ((2 ^ k : ℝ) * σ)) / c)‖ := by
      rw [hI]
      exact intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    have hstep : ‖(fourier (-m)) (((iwRep β : ℝ)) : Circ) * ((((c : ℝ) : ℂ))⁻¹ * I)‖
        ≤ c⁻¹ * ‖I‖ := by
      rw [norm_mul, norm_mul, hphase, hcinv, one_mul]
    calc ‖(fourier (-m)) (((iwRep β : ℝ)) : Circ) * ((((c : ℝ) : ℂ))⁻¹ * I)‖
        ≤ c⁻¹ * ‖I‖ := hstep
      _ ≤ c⁻¹ * ∫ σ in (0 : ℝ)..1,
            ‖mstHat Ξ (((m : ℝ) + (toRealPoly P).eval ((2 ^ k : ℝ) * σ)) / c)‖ :=
          mul_le_mul_of_nonneg_left hInorm (by positivity)
      _ = ∫ σ in (0 : ℝ)..1,
            c⁻¹ * ‖mstHat Ξ (((m : ℝ) + (toRealPoly P).eval ((2 ^ k : ℝ) * σ)) / c)‖ := by
          rw [intervalIntegral.integral_const_mul]
  -- continuity of the sigma-integrands
  have hgc : ∀ m : ℤ, Continuous (fun σ : ℝ =>
      c⁻¹ * ‖mstHat Ξ (((m : ℝ) + (toRealPoly P).eval ((2 ^ k : ℝ) * σ)) / c)‖) := by
    intro m
    have hmh : Continuous (fun τ : ℝ => mstHat Ξ τ) := mstHat_continuous_of_continuous hΞcont
    refine Continuous.mul continuous_const ((hmh.comp ?_).norm)
    exact (continuous_const.add (((Polynomial.continuous (toRealPoly P)).comp
      (continuous_const.mul continuous_id)))).div_const c
  -- the finite partial sums are uniformly bounded
  have hfin : ∀ F : Finset ℤ, ∑ m ∈ F, ‖arcCoeff P l P.natDegree χ η
        ⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊ s k β m‖
      ≤ 2 * Clat * (C₂ * e + C₂ * e) := by
    intro F
    calc ∑ m ∈ F, ‖arcCoeff P l P.natDegree χ η
            ⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊ s k β m‖
        ≤ ∑ m ∈ F, ∫ σ in (0 : ℝ)..1,
            c⁻¹ * ‖mstHat Ξ (((m : ℝ) + (toRealPoly P).eval ((2 ^ k : ℝ) * σ)) / c)‖ :=
          Finset.sum_le_sum (fun m _ => hcoeff m)
      _ = ∫ σ in (0 : ℝ)..1, ∑ m ∈ F,
            c⁻¹ * ‖mstHat Ξ (((m : ℝ) + (toRealPoly P).eval ((2 ^ k : ℝ) * σ)) / c)‖ :=
          (intervalIntegral.integral_finsetSum (fun m _ => (hgc m).intervalIntegrable 0 1)).symm
      _ ≤ ∫ σ in (0 : ℝ)..1, 2 * Clat * (C₂ * e + C₂ * e) := by
          refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ ?_
          · exact (continuous_finsetSum F (fun m _ => hgc m)).intervalIntegrable 0 1
          · exact continuous_const.intervalIntegrable 0 1
          · intro σ _
            exact le_trans
              (Summable.sum_le_tsum F (fun m _ => by positivity)
                (hsam ((toRealPoly P).eval ((2 ^ k : ℝ) * σ))).1)
              (hsam ((toRealPoly P).eval ((2 ^ k : ℝ) * σ))).2
      _ = 2 * Clat * (C₂ * e + C₂ * e) := by
          rw [intervalIntegral.integral_const]; norm_num
  refine ⟨summable_of_sum_le (fun m => norm_nonneg _) hfin, ?_⟩
  refine (Real.tsum_le_of_sum_le (fun m => norm_nonneg _) hfin).trans ?_
  rw [show 2 * Clat * (C₂ * e + C₂ * e)
      = (4 * Clat * C₂) * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2)) from by rw [he]; ring]

end

end Work.BourgainPlan.Maximal
