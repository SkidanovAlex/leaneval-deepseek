import Mathlib
import Submission.Work.GM.Affine.WinMass_basic
import Submission.Work.GM.Affine.region_II_defs
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.winmass_halfmass_core
import Submission.Work.GM.Affine.winmass_window_halfmass
import Submission.Work.GM.Affine.halfmass_le_profile_sq
import Submission.Work.GM.Affine.Bsum_periodization
import Submission.Work.GM.Affine.Hfun_sq_integral_le
import Submission.Work.GM.Affine.f_sq_le_const_sq_smallT
import Submission.Work.GM.Affine.periodization_le_window_sum

/-!
# `WinMass` dominates the `L²`-mass of the profile (`GM §9`)

For `f ≥ 0` continuous with `SuppHyp C₀ f`, `M₂ > 0`, `M₃ ≥ 1` there is an absolute constant
`c > 0` with

  `c * ∫ u, (Hprof f M₂ u) ^ 2 ≤ WinMass f M₂ M₃`.

Route.  `WinMass` is the `M₃`-multiple of the sum, over `ℓ ∈ ℤ`, of the `L²`-mass of
`Bsum f M₂ = Fhat (Hprof f M₂)` over the windows `Iwin M₃ ℓ = [ℓ - 2/M₃, ℓ + 2/M₃]`
(`WinMass_eq_window_sum`).  Dropping the part of each window that lies to the right of `ℓ`
gives the `ℓ`-sum of the half-window masses `∫_0^T ‖Bsum f M₂ (ℓ+u)‖²`, which Tonelli turns
into `∫_0^T Σ'_ℓ ‖Bsum f M₂ (ℓ+u)‖² du` (`periodization_le_window_sum`).  That half-window
mass is `≥ θ T ∫ (Hprof f M₂)²` by `winmass_halfmass_core`, and with
`T = min (2/M₃) (1/2)` the factor `M₃ θ T` is bounded below by `θ/2` since `M₃ ≥ 1`.
-/

namespace Work.GM.Affine

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

noncomputable section

/-- `WinMass` is the `M₃`-multiple of the `ℓ`-sum of the window masses of `‖Bsum f M₂‖²`. -/
lemma WinMass_eq_window_sum (f : ℝ → ℝ) {M₂ M₃ : ℝ} (hM₃ : 0 < M₃) :
    WinMass f M₂ M₃ = M₃ * ∑' ℓ : ℤ, ∫ x in Iwin M₃ ℓ, ‖Bsum f M₂ x‖ ^ 2 := by
  have hc : (0 : ℝ) < 1 / M₃ := by positivity
  have hterm : ∀ ℓ : ℤ, (∫ τ in Set.Icc (-2 : ℝ) 2, ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2)
      = M₃ * ∫ x in Iwin M₃ ℓ, ‖Bsum f M₂ x‖ ^ 2 := by
    intro ℓ
    have h := window_mul_Icc (fun x : ℝ => ‖Bsum f M₂ x‖ ^ 2) (c := 1 / M₃) (d := (ℓ : ℝ)) hc
    have hL : (∫ τ in Set.Icc (-2 : ℝ) 2, ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2)
        = ∫ τ in Set.Icc (-2 : ℝ) 2, ‖Bsum f M₂ ((ℓ : ℝ) + (1 / M₃) * τ)‖ ^ 2 := by
      refine setIntegral_congr_fun measurableSet_Icc (fun τ _ => ?_)
      show ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 = ‖Bsum f M₂ ((ℓ : ℝ) + (1 / M₃) * τ)‖ ^ 2
      rw [Hfun_eq_Bsum,
        show (ℓ : ℝ) + τ / M₃ = (ℓ : ℝ) + (1 / M₃) * τ from by ring]
    have hR : (∫ x in Set.Icc ((ℓ : ℝ) - 2 * (1 / M₃)) ((ℓ : ℝ) + 2 * (1 / M₃)),
          ‖Bsum f M₂ x‖ ^ 2)
        = ∫ x in Iwin M₃ ℓ, ‖Bsum f M₂ x‖ ^ 2 := by
      have hset : (2 : ℝ) * (1 / M₃) = 2 / M₃ := by ring_nf
      show (∫ x in Set.Icc ((ℓ : ℝ) - 2 * (1 / M₃)) ((ℓ : ℝ) + 2 * (1 / M₃)),
          ‖Bsum f M₂ x‖ ^ 2)
        = ∫ x in Set.Icc ((ℓ : ℝ) - 2 / M₃) ((ℓ : ℝ) + 2 / M₃), ‖Bsum f M₂ x‖ ^ 2
      rw [hset]
    rw [hR] at h
    rw [hL]
    calc (∫ τ in Set.Icc (-2 : ℝ) 2, ‖Bsum f M₂ ((ℓ : ℝ) + (1 / M₃) * τ)‖ ^ 2)
        = M₃ * ((1 / M₃) * ∫ τ in Set.Icc (-2 : ℝ) 2,
            ‖Bsum f M₂ ((ℓ : ℝ) + (1 / M₃) * τ)‖ ^ 2) := by
          rw [one_div, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hM₃), one_mul]
      _ = M₃ * ∫ x in Iwin M₃ ℓ, ‖Bsum f M₂ x‖ ^ 2 := by rw [h]
  rw [WinMass, tsum_congr hterm, tsum_mul_left]

theorem WinMass_ge_hprof {C₀ K : ℝ} (hC₀ : 1 ≤ C₀) (hK : 0 < K) :
    ∃ c : ℝ, 0 < c ∧ ∀ M₂ M₃ : ℝ, 0 < M₂ → 1 ≤ M₃ →
      ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
      c * ∫ u, (Hprof f M₂ u) ^ 2 ≤ WinMass f M₂ M₃ := by
  obtain ⟨θ, hθpos, hcore⟩ := winmass_halfmass_core
  refine ⟨θ / 2, by linarith, ?_⟩
  intro M₂ M₃ hM₂ hM₃ f hf hfnn hsup
  have hM₃pos : (0 : ℝ) < M₃ := lt_of_lt_of_le zero_lt_one hM₃
  have hC₀pos : (0 : ℝ) < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have hfcs : HasCompactSupport f := by
    refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (1 / C₀) C₀)
      isCompact_Icc ?_
    intro u hu
    rw [Function.mem_support] at hu
    exact hsup u hu
  have hHcont : Continuous (Hprof f M₂) := Hprof_continuous hf M₂
  have hHnn : ∀ u : ℝ, 0 ≤ Hprof f M₂ u := fun u => Finset.sum_nonneg (fun m _ => hfnn _)
  have hHcs : HasCompactSupport (Hprof f M₂) := Hprof_hasCompactSupport hsup hC₀ hM₂.le
  have hBs : ∀ x : ℝ, Bsum f M₂ x = Fhat (Hprof f M₂) x :=
    fun x => Bsum_eq_Fhat_Hprof hf hsup hC₀ hM₂ x
  have hBc : Continuous (fun x : ℝ => Bsum f M₂ x) := by
    unfold Bsum
    refine continuous_finsetSum _ (fun m₂ _ => ?_)
    exact continuous_const.mul
      ((continuous_Fhat_aux hf hfcs).comp (continuous_const.mul continuous_id))
  have hgcont : Continuous (fun x : ℝ => ‖Bsum f M₂ x‖ ^ 2) := (hBc.norm).pow 2
  have hgnn : ∀ x : ℝ, 0 ≤ ‖Bsum f M₂ x‖ ^ 2 := fun x => sq_nonneg _
  have hgint : Integrable (fun x : ℝ => ‖Bsum f M₂ x‖ ^ 2) := by
    have hcontC : Continuous (fun u : ℝ => ((Hprof f M₂ u : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp hHcont
    have hcsC : HasCompactSupport (fun u : ℝ => ((Hprof f M₂ u : ℝ) : ℂ)) :=
      hHcs.comp_left (g := fun z : ℝ => (z : ℂ)) (by simp)
    have h := integrable_fourier_sq_of_continuous_hasCompactSupport hcontC hcsC
    refine h.congr (Filter.Eventually.of_forall (fun x => ?_))
    show ‖FourierTransform.fourier (fun u : ℝ => ((Hprof f M₂ u : ℝ) : ℂ)) x‖ ^ 2
      = ‖Bsum f M₂ x‖ ^ 2
    rw [show FourierTransform.fourier (fun u : ℝ => ((Hprof f M₂ u : ℝ) : ℂ))
        = fun x => Fhat (Hprof f M₂) x from rfl, hBs x]
  set T : ℝ := min (2 / M₃) (1 / 2) with hTdef
  have hTpos : 0 < T := by rw [hTdef]; exact lt_min (by positivity) (by norm_num)
  have hThalf : T ≤ 1 / 2 := by rw [hTdef]; exact min_le_right _ _
  have hTa : T ≤ 2 / M₃ := by rw [hTdef]; exact min_le_left _ _
  -- covering / periodisation
  have hkey := periodization_le_window_sum (a := 2 / M₃) (T := T)
    (by positivity) hTpos hThalf hTa hgcont hgnn hgint
  have hkey' : (∫ u in (0 : ℝ)..T, ∑' ℓ : ℤ, ‖Bsum f M₂ ((ℓ : ℝ) + u)‖ ^ 2)
      ≤ ∑' ℓ : ℤ, ∫ x in Iwin M₃ ℓ, ‖Bsum f M₂ x‖ ^ 2 := hkey
  -- the half-window mass of the profile
  have hcore' : θ * T * (∫ u, (Hprof f M₂ u) ^ 2)
      ≤ ∫ u in (0 : ℝ)..T, ∑' ℓ : ℤ, ‖Fhat (Hprof f M₂) ((ℓ : ℝ) + u)‖ ^ 2 :=
    hcore hHcont hHnn hHcs hTpos hThalf
  have hconv : (∫ u in (0 : ℝ)..T, ∑' ℓ : ℤ, ‖Fhat (Hprof f M₂) ((ℓ : ℝ) + u)‖ ^ 2)
      = ∫ u in (0 : ℝ)..T, ∑' ℓ : ℤ, ‖Bsum f M₂ ((ℓ : ℝ) + u)‖ ^ 2 := by
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    exact tsum_congr (fun ℓ => by rw [hBs])
  have hchain : θ * T * (∫ u, (Hprof f M₂ u) ^ 2)
      ≤ ∑' ℓ : ℤ, ∫ x in Iwin M₃ ℓ, ‖Bsum f M₂ x‖ ^ 2 :=
    le_trans hcore' (le_trans (le_of_eq hconv) hkey')
  have hWM : WinMass f M₂ M₃
      = M₃ * ∑' ℓ : ℤ, ∫ x in Iwin M₃ ℓ, ‖Bsum f M₂ x‖ ^ 2 :=
    WinMass_eq_window_sum f hM₃pos
  have hX : (0 : ℝ) ≤ ∫ u, (Hprof f M₂ u) ^ 2 := integral_nonneg (fun u => sq_nonneg _)
  have hMT : (1 : ℝ) / 2 ≤ M₃ * T := by
    by_cases hcase : 2 / M₃ ≤ 1 / 2
    · have h2 : M₃ * (2 / M₃) = 2 := by
        rw [mul_comm]; exact div_mul_cancel₀ 2 (ne_of_gt hM₃pos)
      rw [hTdef, min_eq_left hcase, h2]
      norm_num
    · rw [hTdef, min_eq_right (le_of_lt (not_le.mp hcase))]
      nlinarith [hM₃]
  have hstep : (θ / 2) * (∫ u, (Hprof f M₂ u) ^ 2)
      ≤ M₃ * (θ * T * (∫ u, (Hprof f M₂ u) ^ 2)) := by
    have h1 : (1 / 2 : ℝ) * (∫ u, (Hprof f M₂ u) ^ 2)
        ≤ (M₃ * T) * (∫ u, (Hprof f M₂ u) ^ 2) :=
      mul_le_mul_of_nonneg_right hMT hX
    calc (θ / 2) * (∫ u, (Hprof f M₂ u) ^ 2)
        = θ * ((1 / 2) * (∫ u, (Hprof f M₂ u) ^ 2)) := by ring
      _ ≤ θ * ((M₃ * T) * (∫ u, (Hprof f M₂ u) ^ 2)) := mul_le_mul_of_nonneg_left h1 hθpos.le
      _ = M₃ * (θ * T * (∫ u, (Hprof f M₂ u) ^ 2)) := by ring
  have hfinal : M₃ * (θ * T * (∫ u, (Hprof f M₂ u) ^ 2)) ≤ WinMass f M₂ M₃ := by
    rw [hWM]
    exact mul_le_mul_of_nonneg_left hchain hM₃pos.le
  exact le_trans hstep hfinal

end

end Work.GM.Affine
