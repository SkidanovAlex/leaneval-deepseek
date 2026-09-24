import Mathlib
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.assembly_aux
import Submission.Work.GM.Affine.plancherel_continuous
import Submission.Work.GM.Affine.low_freq_ge_local_mass
import Submission.Work.GM.Affine.local_mass_comparison

/-!
# GM §9: the high-frequency tail of `Fhat f` is dominated by the low-frequency mass

The main result of this file is `Work.GM.Affine.high_tail_le_low_sq`: for `f ≥ 0` continuous,
supported in `[1/C₀, C₀]`, satisfying the `Λ`-form Fourier decay hypothesis of GM §9 together
with the compatibility `Λ ≤ 16 c 2 1 T³ ∫f`, and for every `δ > 0`,

  `∫_{ξ > T/2} ‖Fhat f ξ‖² ≤ C (δ) T^(2δ) ∫_{|ξ| ≤ T/2} ‖Fhat f ξ‖²`.

The proof decomposes into a purely local/mass statement and an elementary positive-kernel
lower bound for the low-frequency integral:

* `Work.GM.Affine.local_mass_comparison` (the analytic crux, the "sharpness cap"): under the
  same hypotheses, `∫ u, f u ^ 2 ≤ C T^(2δ) T ∫ u, f u * (∫ v in [u-1/T, u+1/T], f v)`.
  Equivalently: `f` has no features narrower than `T^(-1-2δ)`.
* `Work.GM.Affine.low_freq_ge_local_mass` (elementary, via the Fejér-type positive kernel
  `A * sinc²(π A ·)`, `A = T/2`, whose Fourier transform is the triangle `(1 - |ξ|/A)_+`):
  `(1/5) T ∫ u, f u * (∫ v in [u-1/T, u+1/T], f v) ≤ ∫_{|ξ| ≤ T/2} ‖Fhat f ξ‖²`.

Combining the two with Plancherel and the conjugate symmetry `Fhat f (-ξ) = conj (Fhat f ξ)`
(so that `∫_ℝ ‖Fhat f‖² = low + 2 * high`) gives the result.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-! ### Conjugate symmetry of `Fhat` for a real-valued function -/

lemma htlls_fourier_conj_neg (g : ℝ → ℂ) (ξ : ℝ) :
    FourierTransform.fourier (fun u => (starRingEnd ℂ) (g u)) ξ
      = (starRingEnd ℂ) (FourierTransform.fourier g (-ξ)) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  rw [← integral_conj]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with v
  rw [smul_eq_mul, smul_eq_mul, map_mul, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring_nf

lemma htlls_Fhat_neg_eq_conj (f : ℝ → ℝ) (ξ : ℝ) :
    Fhat f (-ξ) = (starRingEnd ℂ) (Fhat f ξ) := by
  have h := htlls_fourier_conj_neg (fun u : ℝ => ((f u : ℝ) : ℂ)) ξ
  have hfun : (fun u : ℝ => (starRingEnd ℂ) (((f u : ℝ) : ℂ)))
      = fun u : ℝ => ((f u : ℝ) : ℂ) := by
    funext u; exact Complex.conj_ofReal _
  rw [hfun] at h
  unfold Fhat
  rw [h, Complex.conj_conj]

lemma htlls_sq_norm_Fhat_neg (f : ℝ → ℝ) (ξ : ℝ) :
    ‖Fhat f (-ξ)‖ ^ 2 = ‖Fhat f ξ‖ ^ 2 := by
  rw [htlls_Fhat_neg_eq_conj]; simp

/-! ### Splitting an integral into middle range and two tails -/

lemma htlls_integral_eq_Ioc_add_tails {g : ℝ → ℝ} (hInt : Integrable g) {a : ℝ} (ha : 0 ≤ a) :
    ∫ ξ, g ξ = (∫ ξ in Set.Ioc (-a) a, g ξ)
      + ((∫ ξ in Set.Iic (-a), g ξ) + (∫ ξ in Set.Ioi a, g ξ)) := by
  have hA : MeasurableSet (Set.Ioc (-a) a) := measurableSet_Ioc
  have hdisj : Disjoint (Set.Iic (-a)) (Set.Ioi a) := by
    rw [Set.disjoint_left]
    intro x hx hy
    simp only [Set.mem_Iic] at hx
    simp only [Set.mem_Ioi] at hy
    linarith
  have h2 : (∫ ξ in (Set.Ioc (-a) a)ᶜ, g ξ)
      = (∫ ξ in Set.Iic (-a), g ξ) + (∫ ξ in Set.Ioi a, g ξ) := by
    rw [Set.compl_Ioc,
      MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hInt.integrableOn hInt.integrableOn]
  rw [← h2]
  exact (MeasureTheory.integral_add_compl (s := Set.Ioc (-a) a) measurableSet_Ioc hInt).symm

lemma htlls_setIntegral_Iic_neg_eq_Ioi {g : ℝ → ℝ} (h : ∀ x, g (-x) = g x) (a : ℝ) :
    (∫ ξ in Set.Iic (-a), g ξ) = ∫ ξ in Set.Ioi a, g ξ := by
  have h1 : (∫ x in Set.Ioi a, g (-x)) = ∫ x in Set.Iic (-a), g x := integral_comp_neg_Ioi a g
  rw [show (fun x => g (-x)) = g from funext h] at h1
  exact h1.symm

/-! ### The main estimate -/

theorem high_tail_le_low_sq {C₀ T₀ : ℝ} (hC₀ : 1 ≤ C₀) (hT₀ : 1 ≤ T₀)
    (c : ℕ → ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        ∀ Λ : ℝ, 0 < Λ →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
        ∫ ξ in Set.Ioi (T / 2), ‖Fhat f ξ‖ ^ 2
          ≤ C * T ^ (2 * δ) * ∫ ξ in Set.Ioc (-(T / 2)) (T / 2), ‖Fhat f ξ‖ ^ 2 := by
  obtain ⟨C₂, hC₂pos, hL2'⟩ := local_mass_comparison hC₀ hT₀ c δ hδ
  refine ⟨5 * C₂ + 1, by linarith, ?_⟩
  intro T hT f hf hfnn hsupp Λ hΛpos hdec hcompat
  have hT1 : (1 : ℝ) ≤ T := le_trans hT₀ hT
  have hcs : HasCompactSupport f := hasCompactSupport_of_suppHyp hC₀ hsupp
  -- Plancherel
  have hplan : (∫ u, (f u) ^ 2) = ∫ ξ, ‖Fhat f ξ‖ ^ 2 := by
    have h := plancherel_continuous (fun u : ℝ => ((f u : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp hf) (hcs.comp_left (g := Complex.ofReal) (by simp))
    have hL : (∫ x, ‖(fun u : ℝ => ((f u : ℝ) : ℂ)) x‖ ^ 2) = ∫ u, (f u) ^ 2 := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with u
      simp
    rw [hL] at h
    have hR : (∫ ξ, ‖FourierTransform.fourier (fun u : ℝ => ((f u : ℝ) : ℂ)) ξ‖ ^ 2)
        = ∫ ξ, ‖Fhat f ξ‖ ^ 2 := rfl
    rw [hR] at h
    exact h
  by_cases hzero : (∫ u, (f u) ^ 2) = 0
  · -- trivial case: `f = 0` a.e., hence `Fhat f = 0`
    have hcs2 : HasCompactSupport (fun u : ℝ => f u ^ 2) :=
      hcs.comp_left (g := fun x : ℝ => x ^ 2) (by simp)
    have hint2 : Integrable (fun u : ℝ => (f u) ^ 2) :=
      (hf.pow 2).integrable_of_hasCompactSupport hcs2
    have hae2 : (fun u : ℝ => (f u) ^ 2) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun u => sq_nonneg _) hint2).mp hzero
    have hfae : f =ᵐ[volume] 0 := by
      filter_upwards [hae2] with u hu
      simpa [pow_eq_zero_iff] using hu
    have hF0 : ∀ ξ, Fhat f ξ = 0 := by
      intro ξ
      have h1 : (fun u : ℝ => Real.fourierChar (-inner ℝ u ξ) • (f u : ℂ)) =ᵐ[volume] (0 : ℝ → ℂ) := by
        filter_upwards [hfae] with u hu
        rw [hu]; simp
      rw [Fhat, Real.fourier_eq]
      rw [MeasureTheory.integral_congr_ae h1]
      simp
    simp only [hF0, norm_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0)]
    simp
  · have hIntg : Integrable (fun ξ => ‖Fhat f ξ‖ ^ 2) := by
      by_contra hcon
      have hz : (∫ ξ, ‖Fhat f ξ‖ ^ 2) = 0 := integral_undef hcon
      rw [hz] at hplan
      exact hzero hplan
    have hsplit := htlls_integral_eq_Ioc_add_tails hIntg (by linarith : (0:ℝ) ≤ T / 2)
    have hsymm : (∫ ξ in Set.Iic (-(T / 2)), ‖Fhat f ξ‖ ^ 2)
        = ∫ ξ in Set.Ioi (T / 2), ‖Fhat f ξ‖ ^ 2 :=
      htlls_setIntegral_Iic_neg_eq_Ioi (fun x => htlls_sq_norm_Fhat_neg f x) (T / 2)
    have hkey : (∫ ξ, ‖Fhat f ξ‖ ^ 2)
        = (∫ ξ in Set.Ioc (-(T / 2)) (T / 2), ‖Fhat f ξ‖ ^ 2)
          + 2 * (∫ ξ in Set.Ioi (T / 2), ‖Fhat f ξ‖ ^ 2) := by
      rw [hsplit, hsymm]; ring
    -- the two mass/`low` inequalities
    have hb1 := low_freq_ge_local_mass hC₀ hT₀ T hT f hf hfnn hsupp
    have hb2 := hL2' T hT f hf hfnn hsupp Λ hΛpos hdec hcompat
    set low : ℝ := ∫ ξ in Set.Ioc (-(T / 2)) (T / 2), ‖Fhat f ξ‖ ^ 2 with hlowdef
    set high : ℝ := ∫ ξ in Set.Ioi (T / 2), ‖Fhat f ξ‖ ^ 2 with hhighdef
    set Q : ℝ := ∫ u, (f u) * (∫ v in Set.Icc (u - 1 / T) (u + 1 / T), f v) with hQdef
    have hQnn : 0 ≤ Q := by
      rw [hQdef]
      apply integral_nonneg
      intro u
      have h1 : 0 ≤ f u := hfnn u
      have h2 : 0 ≤ ∫ v in Set.Icc (u - 1 / T) (u + 1 / T), f v := integral_nonneg hfnn
      exact mul_nonneg h1 h2
    have hlownn : 0 ≤ low := by
      rw [hlowdef]; exact integral_nonneg (fun x => sq_nonneg _)
    have hb1' : T * Q ≤ 5 * low := by
      have := hb1
      rw [hQdef, hlowdef] at this
      linarith
    have hmain : (∫ u, (f u) ^ 2) ≤ 5 * C₂ * T ^ (2 * δ) * low := by
      have h1 : (∫ u, (f u) ^ 2) ≤ C₂ * T ^ (2 * δ) * (T * Q) := by
        have := hb2
        rw [hQdef] at this
        calc (∫ u, (f u) ^ 2) ≤ C₂ * T ^ (2 * δ) * T * Q := this
          _ = C₂ * T ^ (2 * δ) * (T * Q) := by ring
      have h2 : C₂ * T ^ (2 * δ) * (T * Q) ≤ C₂ * T ^ (2 * δ) * (5 * low) :=
        mul_le_mul_of_nonneg_left hb1' (by positivity)
      have h3 : C₂ * T ^ (2 * δ) * (5 * low) = 5 * C₂ * T ^ (2 * δ) * low := by ring
      linarith [h1, h2, h3.le, h3.ge]
    have hkey' : (∫ u, (f u) ^ 2) = low + 2 * high := by
      rw [hplan, hkey, hlowdef, hhighdef]
    have h2high : 2 * high ≤ 5 * C₂ * T ^ (2 * δ) * low := by
      have hpos : 0 ≤ T ^ (2 * δ) := (Real.rpow_pos_of_pos (by linarith : (0:ℝ) < T) _).le
      linarith [hkey', hmain]
    have hTpos : (0:ℝ) < T := by linarith
    have hTp : 0 < T ^ (2 * δ) := Real.rpow_pos_of_pos hTpos _
    have hX : (0:ℝ) ≤ T ^ (2 * δ) * low := mul_nonneg hTp.le hlownn
    have hab : 5 * C₂ / 2 ≤ 5 * C₂ + 1 := by linarith
    have hfinal : high ≤ (5 * C₂ + 1) * T ^ (2 * δ) * low := by
      calc high ≤ (5 * C₂ / 2) * T ^ (2 * δ) * low := by linarith [h2high]
        _ = (5 * C₂ / 2) * (T ^ (2 * δ) * low) := by ring
        _ ≤ (5 * C₂ + 1) * (T ^ (2 * δ) * low) := mul_le_mul_of_nonneg_right hab hX
        _ = (5 * C₂ + 1) * T ^ (2 * δ) * low := by ring
    rw [hlowdef, hhighdef] at hfinal
    exact hfinal

end

end Work.GM.Affine
