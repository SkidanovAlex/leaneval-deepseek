/-
# Assembly of the square-function bound for the lacunary deviation family

This module reduces the target `Work.KMTAreas.A7.lacDilDevSqSum` to the three analytic inputs
about the linearized deviation kernel `lacDevLin` (its symbol bound `lacDevSymBound`, its `ℓ²`
bound `lacDevL2` and its discrete Hörmander condition `lacDevHormander`), together with the
corpus's Khintchine linearisation `sqSum_lintegral_le_uniformSigns_noLin` and the discrete
Calderón–Zygmund `ℓᵖ` bounds `discrete_convolution_lp_bounded(_large)`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LacDevBasics
import Submission.Work.KMTAreas.A7.sqSum_lintegral_le_uniformSigns_noLin
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

/-! ## Elementary reindexing -/

/-- Reindexing a convolution: `∑_j k j · f (x - j) = ∑_y k (x - y) · f y`. -/
lemma tsum_kernel_conv_reindex (k f : ℤ → ℂ) (x : ℤ) :
    (∑' j : ℤ, k j * f (x - j)) = ∑' y : ℤ, k (x - y) * f y := by
  have hs : ∀ i : ℤ, x - (x - i) = i := fun i => by ring
  have h := Equiv.tsum_eq
    (⟨fun y => x - y, fun y => x - y, fun y => by ring, fun y => by ring⟩ : ℤ ≃ ℤ)
    (fun i : ℤ => k i * f (x - i))
  have h2 : (∑' i : ℤ, k (x - i) * f i) = ∑' i : ℤ, k i * f (x - i) := by
    rw [← h]
    refine tsum_congr fun i => ?_
    show k (x - i) * f i = k (x - i) * f (x - (x - i))
    rw [hs i]
  exact h2.symm

/-! ## Two bridges between `eLpNorm` and `lintegral` -/

/-- An `eLpNorm` bound in `ℓᵖ(ℤ)` gives the corresponding `lintegral` bound (raise to the `p`-th
power). -/
lemma lintegral_rpow_le_of_eLpNorm_le {p : ℝ} (hp : 0 < p) (F f : ℤ → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (h : eLpNorm F (ENNReal.ofReal p) Measure.count
        ≤ ENNReal.ofReal M * eLpNorm f (ENNReal.ofReal p) Measure.count) :
    ∫⁻ x : ℤ, ‖F x‖ₑ ^ p ∂Measure.count
      ≤ ENNReal.ofReal (M ^ p) * ∫⁻ x : ℤ, ‖f x‖ₑ ^ p ∂Measure.count := by
  have hGL : (eLpNorm F (ENNReal.ofReal p) Measure.count) ^ p
      = ∫⁻ x : ℤ, ‖F x‖ₑ ^ p ∂Measure.count := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm)
      (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le,
      one_div]
    exact ENNReal.rpow_inv_rpow hp.ne' _
  have hfL : (eLpNorm f (ENNReal.ofReal p) Measure.count) ^ p
      = ∫⁻ x : ℤ, ‖f x‖ₑ ^ p ∂Measure.count := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm)
      (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le,
      one_div]
    exact ENNReal.rpow_inv_rpow hp.ne' _
  calc ∫⁻ x : ℤ, ‖F x‖ₑ ^ p ∂Measure.count
      = (eLpNorm F (ENNReal.ofReal p) Measure.count) ^ p := hGL.symm
    _ ≤ (ENNReal.ofReal M * eLpNorm f (ENNReal.ofReal p) Measure.count) ^ p :=
        ENNReal.rpow_le_rpow h hp.le
    _ = (ENNReal.ofReal M) ^ p * (eLpNorm f (ENNReal.ofReal p) Measure.count) ^ p :=
        ENNReal.mul_rpow_of_nonneg _ _ hp.le
    _ = ENNReal.ofReal (M ^ p) * ∫⁻ x : ℤ, ‖f x‖ₑ ^ p ∂Measure.count := by
        rw [hfL, ← ENNReal.ofReal_rpow_of_nonneg hM hp.le]

/-- If the `ℓᵖ`-`lintegral` of `f` is finite, then the real `p`-series of `f` is summable. -/
lemma summable_norm_rpow_of_lintegral_ne_top {p : ℝ} (hp : 0 < p) {f : ℤ → ℂ}
    (h : (∫⁻ x : ℤ, ‖f x‖ₑ ^ p ∂Measure.count) ≠ ⊤) :
    Summable (fun x : ℤ => ‖f x‖ ^ p) := by
  set g : ℤ → ℝ≥0 := fun x => (‖f x‖ ^ p).toNNReal with hg
  have hcoe : ∀ x : ℤ, ((g x : ℝ≥0) : ℝ≥0∞) = ‖f x‖ₑ ^ p := by
    intro x
    rw [hg]
    simp only
    rw [show ‖f x‖ₑ = ENNReal.ofReal ‖f x‖ from by simp [enorm],
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (f x)) hp.le,
      ENNReal.ofReal_eq_coe_nnreal (Real.rpow_nonneg (norm_nonneg (f x)) p)]
    congr 1
    exact Real.toNNReal_of_nonneg (Real.rpow_nonneg (norm_nonneg (f x)) p)
  have h' : (∑' x : ℤ, ((g x : ℝ≥0) : ℝ≥0∞)) ≠ ⊤ := by
    rw [tsum_congr hcoe]
    rw [MeasureTheory.lintegral_count] at h
    exact h
  have hsum2 : Summable (fun x : ℤ => ((g x : ℝ≥0) : ℝ)) :=
    (ENNReal.tsum_coe_ne_top_iff_summable_coe (f := g)).mp h'
  refine Summable.of_nonneg_of_le (f := fun x : ℤ => ((g x : ℝ≥0) : ℝ))
    (g := fun x : ℤ => ‖f x‖ ^ p)
    (fun x => Real.rpow_nonneg (norm_nonneg (f x)) p) (fun x => ?_) hsum2
  refine le_of_eq ?_
  rw [hg]
  simp only
  exact (Real.coe_toNNReal (‖f x‖ ^ p) (Real.rpow_nonneg (norm_nonneg (f x)) p)).symm

/-- A `p`-summable function is bounded. -/
lemma norm_le_of_summable_norm_rpow {p : ℝ} (hp : 0 < p) {f : ℤ → ℂ}
    (hf : Summable (fun x : ℤ => ‖f x‖ ^ p)) : ∃ N : ℝ, ∀ x : ℤ, ‖f x‖ ≤ N := by
  refine ⟨(∑' x : ℤ, ‖f x‖ ^ p) ^ (1 / p) + 1, fun x => ?_⟩
  have h1 : ‖f x‖ ^ p ≤ ∑' y : ℤ, ‖f y‖ ^ p := by
    have h2 : ENNReal.ofReal (‖f x‖ ^ p) ≤ ∑' y : ℤ, ENNReal.ofReal (‖f y‖ ^ p) :=
      ENNReal.le_tsum (f := fun y : ℤ => ENNReal.ofReal (‖f y‖ ^ p)) x
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun y => by positivity) hf] at h2
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h2
  have h3 : ‖f x‖ = (‖f x‖ ^ p) ^ (1 / p) := by
    rw [← Real.rpow_mul (norm_nonneg _), mul_one_div, div_self hp.ne', Real.rpow_one]
  rw [h3]
  calc (‖f x‖ ^ p) ^ (1 / p) ≤ (∑' y : ℤ, ‖f y‖ ^ p) ^ (1 / p) :=
        Real.rpow_le_rpow (by positivity) h1 (by positivity)
    _ ≤ (∑' y : ℤ, ‖f y‖ ^ p) ^ (1 / p) + 1 := by linarith

/-! ## The assembly -/

/-- **The square-function bound for the lacunary deviation family, from its three analytic
inputs.** -/
theorem lacDilDevSqSum_of_inputs (p : ℝ) (hp : 1 < p) (K : SchwartzMap ℝ ℂ)
    (Csym : ℝ) (hCsympos : 0 < Csym)
    (hsym : ∀ (σ : ℕ → ℕ), (∀ n, 1 ≤ σ n) → (∀ n, 2 * σ n ≤ σ (n + 1)) →
      ∀ (U : Finset ℕ) (ω : ℕ → Bool) (θ : ℝ),
        ‖∑' j : ℤ, lacDevLin K σ U ω j * Work.KMTAreas.ADev.chr j θ‖ ≤ Csym)
    (hL2 : ∃ A : ℝ, 0 < A ∧ ∀ (σ : ℕ → ℕ), (∀ n, 1 ≤ σ n) → (∀ n, 2 * σ n ≤ σ (n + 1)) →
      ∀ (U : Finset ℕ) (ω : ℕ → Bool) (g : ℤ → ℂ), Summable g →
        eLpNorm (fun x : ℤ => ∑' y : ℤ, lacDevLin K σ U ω (x - y) * g y) 2 Measure.count
          ≤ ENNReal.ofReal A * eLpNorm g 2 Measure.count)
    (hHorm : ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℕ → ℕ), (∀ n, 1 ≤ σ n) → (∀ n, 2 * σ n ≤ σ (n + 1)) →
      ∀ (U : Finset ℕ) (ω : ℕ → Bool) (y : ℤ), y ≠ 0 →
        ∫⁻ x in {x : ℤ | 2 * y.natAbs ≤ x.natAbs},
            ‖lacDevLin K σ U ω (x - y) - lacDevLin K σ U ω x‖ₑ ∂Measure.count
          ≤ ENNReal.ofReal C) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℕ → ℕ) (hσ1 : ∀ n, 1 ≤ σ n)
      (hσ2 : ∀ n, 2 * σ n ≤ σ (n + 1)) (f : ℤ → ℂ),
      eLpNorm (fun x : ℤ => (∑' n : ℕ, ‖devOp K σ n f x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
          (ENNReal.ofReal p) Measure.count
        ≤ ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) Measure.count := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  obtain ⟨A2, hA2pos, hA2⟩ := hL2
  obtain ⟨Ak, hAkpos, hAk⟩ := hHorm
  obtain ⟨Bk, hBkpos, hBk⟩ := lacDevLin_norm_le K
  -- ## Step 1: the linearized `ℓᵖ` bound, from the discrete Calderón–Zygmund theorem
  have hlin : ∃ M : ℝ, 0 < M ∧ ∀ (σ : ℕ → ℕ) (hσ1 : ∀ n, 1 ≤ σ n)
      (hσ2 : ∀ n, 2 * σ n ≤ σ (n + 1)) (U : Finset ℕ) (ω : ℕ → Bool) (g : ℤ → ℂ),
      Summable (fun n : ℤ => ‖g n‖ ^ p) →
      eLpNorm (fun x : ℤ => ∑' y : ℤ, lacDevLin K σ U ω (x - y) * g y)
          (ENNReal.ofReal p) Measure.count
        ≤ ENNReal.ofReal M * eLpNorm g (ENNReal.ofReal p) Measure.count := by
    rcases lt_trichotomy p 2 with h2 | h2 | h2
    · obtain ⟨C1, hC1pos, hCZ⟩ :=
        Commons.Analysis.DiscreteCZ.discrete_convolution_lp_bounded (H := ℂ) hp h2
      refine ⟨C1 * (24 * A2 ^ 2 + 4 * Ak + 100) ^ (2 / p - 1) * A2 ^ (2 - 2 / p),
        by positivity, ?_⟩
      intro σ hσ1 hσ2 U ω g hg
      have h1 := hCZ (lacDevLin K σ U ω) A2 Ak Bk hA2pos hAkpos.le
        (fun z => hBk σ hσ1 hσ2 U ω z)
        (fun y hy => hAk σ hσ1 hσ2 U ω y hy)
        (fun f hf => by
          rw [show (fun x : ℤ => ∑' y : ℤ, lacDevLin K σ U ω (x - y) • f y)
              = (fun x : ℤ => ∑' y : ℤ, lacDevLin K σ U ω (x - y) * f y) from
                funext fun x => tsum_congr fun y => by rw [smul_eq_mul]]
          exact hA2 σ hσ1 hσ2 U ω f hf)
        g hg
      rw [show (fun x : ℤ => ∑' y : ℤ, lacDevLin K σ U ω (x - y) • g y)
          = (fun x : ℤ => ∑' y : ℤ, lacDevLin K σ U ω (x - y) * g y) from
            funext fun x => tsum_congr fun y => by rw [smul_eq_mul]] at h1
      exact h1
    · subst h2
      refine ⟨A2, hA2pos, ?_⟩
      intro σ hσ1 hσ2 U ω g hg
      have hg' : Summable (fun n : ℤ => ‖g n‖ ^ (2 : ℝ)) := hg
      refine Commons.Analysis.DiscreteCZ.lp_bound_of_finsupp (H := ℂ)
        (K := lacDevLin K σ U ω) (p := 2) (c := A2) (by norm_num) hA2pos.le ?_ g hg'
      intro f hf
      obtain ⟨t, ht⟩ := hf
      have hfs : Summable f := summable_of_ne_finset_zero (s := t) fun x hx => ht x hx
      have h1 := hA2 σ hσ1 hσ2 U ω f hfs
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) from by norm_num] at h1
      exact h1
    · obtain ⟨C1, hC1pos, hCZ⟩ :=
        Commons.Analysis.DiscreteCZ.discrete_convolution_lp_bounded_large (H := ℂ) h2
      refine ⟨C1 * (24 * A2 ^ 2 + 4 * Ak + 100) ^ (2 / (p / (p - 1)) - 1)
        * A2 ^ (2 - 2 / (p / (p - 1))), by positivity, ?_⟩
      intro σ hσ1 hσ2 U ω g hg
      have h1 := hCZ (lacDevLin K σ U ω) A2 Ak Bk hA2pos hAkpos.le
        (fun z => hBk σ hσ1 hσ2 U ω z)
        (fun y hy => hAk σ hσ1 hσ2 U ω y hy)
        (fun f hf => by
          rw [show (fun x : ℤ => ∑' y : ℤ, lacDevLin K σ U ω (x - y) • f y)
              = (fun x : ℤ => ∑' y : ℤ, lacDevLin K σ U ω (x - y) * f y) from
                funext fun x => tsum_congr fun y => by rw [smul_eq_mul]]
          exact hA2 σ hσ1 hσ2 U ω f hf)
        g hg
      rw [show (fun x : ℤ => ∑' y : ℤ, lacDevLin K σ U ω (x - y) • g y)
          = (fun x : ℤ => ∑' y : ℤ, lacDevLin K σ U ω (x - y) * g y) from
            funext fun x => tsum_congr fun y => by rw [smul_eq_mul]] at h1
      exact h1
  obtain ⟨M, hMpos, hlin'⟩ := hlin
  -- ## Step 2: the linearized bound for the deviation operators themselves
  have hdev : ∀ (σ : ℕ → ℕ) (hσ1 : ∀ n, 1 ≤ σ n) (hσ2 : ∀ n, 2 * σ n ≤ σ (n + 1))
      (U : Finset ℕ) (ω : ℕ → Bool) (f : ℤ → ℂ),
      ∫⁻ x : ℤ, ‖∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * devOp K σ n f x‖ₑ ^ p
          ∂Measure.count
        ≤ ENNReal.ofReal (M ^ p) * ∫⁻ x : ℤ, ‖f x‖ₑ ^ p ∂Measure.count := by
    intro σ hσ1 hσ2 U ω f
    by_cases hQ : (∫⁻ x : ℤ, ‖f x‖ₑ ^ p ∂Measure.count) = ⊤
    · have hMp : (0 : ℝ) < M ^ p := Real.rpow_pos_of_pos hMpos p
      rw [hQ, ENNReal.mul_top (by
        rw [ne_eq, ENNReal.ofReal_eq_zero]; exact not_le.mpr hMp)]
      exact le_top
    · have hsumm : Summable (fun x : ℤ => ‖f x‖ ^ p) :=
        summable_norm_rpow_of_lintegral_ne_top hp0 hQ
      obtain ⟨N, hN⟩ := norm_le_of_summable_norm_rpow hp0 hsumm
      have hid : ∀ x : ℤ, ‖∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * devOp K σ n f x‖ₑ
          = ‖∑' y : ℤ, lacDevLin K σ U ω (x - y) * f y‖ₑ := by
        intro x
        rw [show (∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * devOp K σ n f x)
            = ∑ n ∈ U, Work.KMTAreas.ADev.bSign ω n * devOp K σ n f x from
              Finset.sum_congr rfl fun n _ => by rw [Work.KMTAreas.ADev.bSign]]
        rw [lacDevLin_conv K σ hσ1 U ω f ⟨N, hN⟩ x, tsum_kernel_conv_reindex]
      have hconv := hlin' σ hσ1 hσ2 U ω f hsumm
      have hmain := lintegral_rpow_le_of_eLpNorm_le hp0
        (fun x : ℤ => ∑' y : ℤ, lacDevLin K σ U ω (x - y) * f y) f (le_of_lt hMpos) hconv
      rw [show (fun x : ℤ => ‖∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * devOp K σ n f x‖ₑ ^ p)
          = fun x : ℤ => ‖∑' y : ℤ, lacDevLin K σ U ω (x - y) * f y‖ₑ ^ p from
            funext fun x => by rw [hid x]]
      exact hmain
  -- ## Step 3: Khintchine linearisation
  obtain ⟨Kc, hKcpos, hKhint⟩ := sqSum_lintegral_le_uniformSigns_noLin p hp
  refine ⟨(Kc * M ^ p) ^ (1 / p), Real.rpow_pos_of_pos (by positivity) _, ?_⟩
  intro σ hσ1 hσ2 f
  have hK := hKhint (fun n f => devOp K σ n f)
    (fun n f => (measurable_of_countable _).aemeasurable) M (le_of_lt hMpos)
    (fun U ω f => hdev σ hσ1 hσ2 U ω f) f
  -- ## Step 4: pass back to `eLpNorm`
  have hFL : eLpNorm (fun x : ℤ => (∑' n : ℕ, ‖devOp K σ n f x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
        (ENNReal.ofReal p) Measure.count
      = (∫⁻ x : ℤ, (∑' n : ℕ, ‖devOp K σ n f x‖ₑ ^ (2 : ℝ)) ^ (p / 2) ∂Measure.count)
          ^ (1 / p) := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm)
      (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp0.le]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [enorm_eq_self, ← ENNReal.rpow_mul]
    congr 1
    ring
  have hfL : eLpNorm f (ENNReal.ofReal p) Measure.count
      = (∫⁻ x : ℤ, ‖f x‖ₑ ^ p ∂Measure.count) ^ (1 / p) := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm)
      (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp0.le]
  have hC1 : ENNReal.ofReal ((Kc * M ^ p) ^ (1 / p))
      = (ENNReal.ofReal (Kc * M ^ p)) ^ (1 / p) :=
    (ENNReal.ofReal_rpow_of_nonneg (show (0 : ℝ) ≤ Kc * M ^ p from by positivity)
      (show (0 : ℝ) ≤ 1 / p from by positivity)).symm
  have hC2 : (ENNReal.ofReal (Kc * M ^ p)) ^ (1 / p)
        * (∫⁻ x : ℤ, ‖f x‖ₑ ^ p ∂Measure.count) ^ (1 / p)
      = (ENNReal.ofReal (Kc * M ^ p) * ∫⁻ x : ℤ, ‖f x‖ₑ ^ p ∂Measure.count) ^ (1 / p) :=
    (ENNReal.mul_rpow_of_nonneg _ _ (show (0 : ℝ) ≤ 1 / p from by positivity)).symm
  rw [hFL, hfL, hC1, hC2]
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  exact hK

end

end Work.KMTAreas.A7
