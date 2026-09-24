import Mathlib
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.region_II_defs
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.smoothed_properties
import Submission.Work.GM.Affine.plancherel_continuous
import Submission.Work.GM.Affine.integrable_Fhat_sq
import Submission.Work.GM.Affine.smoothed_local
import Submission.Work.GM.Affine.card_int_in_interval_le

/-!
# Basic reductions for `Work.GM.Affine.WinMass_core`

GM §9 region II: with `B(u) = Bsum f M₂ u = Σ_{m₂ ∈ R2 M₂} m₂ Fhat f (m₂ u)` and
`H(u) = Hprof f M₂ u = Σ_{m₂ ∈ R2 M₂} f (u/m₂)`,

* `B = Fhat H` (`Bsum_eq_Fhat_Hprof`), hence by Plancherel
  `∫ ‖B‖² = ∫ H²` (`integral_normSq_Bsum_eq_integral_Hprof_sq`);
* `Hfun f M₂ M₃ ℓ τ = B ((ℓ:ℝ) + τ/M₃)`, so `WinMass` is the `M₃`-multiple of the sum of the
  local `L²`-masses of `B` over the windows of radius `2/M₃` around the integers.

These are the input-side reductions for the target `Work.GM.Affine.WinMass_core`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- The `m₂`-profile `H(u) = Σ_{m₂ ∈ R2 M₂} f (u/m₂)`; its Fourier transform is `Bsum f M₂`. -/
def Hprof (f : ℝ → ℝ) (M₂ : ℝ) (u : ℝ) : ℝ := ∑ m₂ ∈ R2 M₂, f (u / (m₂ : ℝ))

lemma R2_pos' {M₂ : ℝ} {m₂ : ℤ} (hm : m₂ ∈ R2 M₂) : (0:ℝ) < (m₂:ℝ) := by
  have h1 : (1:ℤ) ≤ m₂ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
  exact_mod_cast (by omega : (0:ℤ) < m₂)

lemma R2_le' {M₂ : ℝ} {m₂ : ℤ} (hm : m₂ ∈ R2 M₂) : (m₂:ℝ) ≤ 2 * M₂ := by
  have h1 : m₂ ≤ ⌊2 * M₂⌋ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).2
  have h2 : ((⌊2 * M₂⌋ : ℤ) : ℝ) ≤ 2 * M₂ := Int.floor_le _
  have h3 : (m₂:ℝ) ≤ ((⌊2 * M₂⌋ : ℤ) : ℝ) := by exact_mod_cast h1
  linarith

/-- Change of variables `u ↦ u/c` for `c > 0`. -/
lemma integral_comp_div (F : ℝ → ℂ) {c : ℝ} (hc : 0 < c) :
    (∫ u : ℝ, F (u / c)) = c * ∫ v : ℝ, F v := by
  have h1 : (∫ u : ℝ, F (u / c)) = ∫ u : ℝ, F (c⁻¹ * u) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    show F (u / c) = F (c⁻¹ * u)
    rw [show u / c = c⁻¹ * u from by rw [div_eq_mul_inv, mul_comm]]
  rw [h1, MeasureTheory.Measure.integral_comp_mul_left]
  rw [show |(c⁻¹)⁻¹| = c from by rw [inv_inv, abs_of_pos hc]]
  rw [Complex.real_smul]

lemma Hprof_continuous {f : ℝ → ℝ} (hf : Continuous f) (M₂ : ℝ) :
    Continuous (Hprof f M₂) := by
  unfold Hprof
  refine continuous_finsetSum _ (fun m₂ _ => ?_)
  exact hf.comp (continuous_id.div_const _)

lemma Hprof_hasCompactSupport {C₀ : ℝ} {f : ℝ → ℝ} (hsup : SuppHyp C₀ f) (hC₀ : 1 ≤ C₀)
    {M₂ : ℝ} (hM₂ : 0 ≤ M₂) : HasCompactSupport (Hprof f M₂) := by
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  refine HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (-(2 * C₀ * M₂)) (2 * C₀ * M₂)) isCompact_Icc ?_
  intro u hu
  rw [Function.mem_support, Hprof] at hu
  rw [Set.mem_Icc]
  by_contra hcon
  refine hu (Finset.sum_eq_zero (fun m₂ hm₂ => ?_))
  by_contra hne
  have hm₂pos : (0:ℝ) < (m₂:ℝ) := R2_pos' hm₂
  have hm₂le : (m₂:ℝ) ≤ 2 * M₂ := R2_le' hm₂
  have humem : u / (m₂:ℝ) ∈ Set.Icc (1/C₀) C₀ := hsup _ hne
  rw [Set.mem_Icc] at humem
  have hdiv : u = (u/(m₂:ℝ)) * (m₂:ℝ) := (div_mul_cancel₀ u (ne_of_gt hm₂pos)).symm
  have hu1 : 0 < u := by
    have h : (1/C₀) * (m₂:ℝ) ≤ u := by rw [hdiv]; exact mul_le_mul_of_nonneg_right humem.1 hm₂pos.le
    have h2 : 0 < (1/C₀) * (m₂:ℝ) := mul_pos (one_div_pos.mpr hC₀pos) hm₂pos
    linarith
  have hu2 : u ≤ 2 * C₀ * M₂ := by
    have h : u ≤ C₀ * (m₂:ℝ) := by rw [hdiv]; exact mul_le_mul_of_nonneg_right humem.2 hm₂pos.le
    nlinarith [h, hm₂le, hC₀pos.le]
  exact hcon ⟨by linarith, hu2⟩

lemma Fhat_eq_integral' (f : ℝ → ℝ) (ξ : ℝ) :
    Fhat f ξ = ∫ u : ℝ, (f u : ℂ) * efun (-(u * ξ)) := by
  rw [Fhat, Real.fourier_real_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
  have hchar : (Real.fourierChar (-(v * ξ)) : ℂ) = efun (-(v * ξ)) := by
    rw [efun, Real.fourierChar_apply]
    congr 1
    push_cast
    ring
  simp only [Circle.smul_def, smul_eq_mul]
  rw [hchar, mul_comm]

lemma contDiff_efun : Continuous efun := by unfold efun; fun_prop

/-- `Bsum f M₂` is the Fourier transform of `Hprof f M₂`. -/
lemma Bsum_eq_Fhat_Hprof {C₀ : ℝ} {f : ℝ → ℝ} (hf : Continuous f) (hsup : SuppHyp C₀ f)
    (hC₀ : 1 ≤ C₀) {M₂ : ℝ} (hM₂ : 0 < M₂) (x : ℝ) :
    Bsum f M₂ x = Fhat (Hprof f M₂) x := by
  have hL : Bsum f M₂ x
      = ∑ m₂ ∈ R2 M₂, ((m₂:ℝ):ℂ) * ∫ v : ℝ, (f v : ℂ) * efun (-(v * ((m₂:ℝ) * x))) := by
    rw [Bsum]
    exact Finset.sum_congr rfl (fun m₂ _ => by rw [Fhat_eq_integral'])
  have hR : Fhat (Hprof f M₂) x
      = ∫ u : ℝ, ((∑ m₂ ∈ R2 M₂, f (u / (m₂:ℝ)) : ℝ) : ℂ) * efun (-(u * x)) := by
    rw [Fhat_eq_integral']; rfl
  rw [hL, hR]
  have hsub : ∀ m₂ ∈ R2 M₂, (∫ u : ℝ, (f (u / (m₂:ℝ)) : ℂ) * efun (-(u * x)))
      = (m₂:ℝ) * ∫ v : ℝ, (f v : ℂ) * efun (-(v * ((m₂:ℝ) * x))) := by
    intro m₂ hm₂
    have hm₂pos : (0:ℝ) < (m₂:ℝ) := R2_pos' hm₂
    have hpt : (fun u : ℝ => (f (u / (m₂:ℝ)) : ℂ) * efun (-(u * x)))
        = fun u : ℝ => ((fun v : ℝ => (f v : ℂ) * efun (-(v * ((m₂:ℝ) * x)))) (u / (m₂:ℝ))) := by
      funext u
      simp only
      have e2 : -((u / (m₂:ℝ)) * ((m₂:ℝ) * x)) = -(u * x) := by field_simp; try ring
      rw [e2]
    rw [hpt]
    rw [integral_comp_div (c := (m₂:ℝ))
      (F := fun v : ℝ => (f v : ℂ) * efun (-(v * ((m₂:ℝ) * x)))) hm₂pos]
  have hfun : (fun u : ℝ => ((∑ m₂ ∈ R2 M₂, f (u / (m₂:ℝ)) : ℝ) : ℂ) * efun (-(u * x)))
      = fun u : ℝ => ∑ m₂ ∈ R2 M₂, ((f (u / (m₂:ℝ)) : ℝ) : ℂ) * efun (-(u * x)) := by
    funext u
    rw [show ((∑ m₂ ∈ R2 M₂, f (u / (m₂:ℝ)) : ℝ) : ℂ)
        = ∑ m₂ ∈ R2 M₂, ((f (u / (m₂:ℝ)) : ℝ) : ℂ) from by push_cast; rfl]
    rw [Finset.sum_mul]
  rw [hfun]
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl (fun m₂ hm₂ => ?_)
    exact (hsub m₂ hm₂).symm
  · intro m₂ hm₂
    have hm₂pos : (0:ℝ) < (m₂:ℝ) := R2_pos' hm₂
    have hsupp : ∀ u : ℝ, (f (u / (m₂:ℝ)) : ℂ) ≠ 0 → u ∈ Set.Icc (m₂/C₀) (m₂*C₀) := by
      intro u hu
      have hne : f (u / (m₂:ℝ)) ≠ 0 := by simpa using hu
      have hmem : u / (m₂:ℝ) ∈ Set.Icc (1/C₀) C₀ := hsup _ hne
      rw [Set.mem_Icc] at hmem ⊢
      have hdiv : u = (u/(m₂:ℝ)) * (m₂:ℝ) := (div_mul_cancel₀ u (ne_of_gt hm₂pos)).symm
      constructor
      · have h : (1/C₀) * (m₂:ℝ) ≤ u := by
          rw [hdiv]; exact mul_le_mul_of_nonneg_right hmem.1 hm₂pos.le
        have h2 : (m₂:ℝ)/C₀ = (1/C₀)*(m₂:ℝ) := by ring
        linarith [h]
      · have h : u ≤ C₀ * (m₂:ℝ) := by
          rw [hdiv]; exact mul_le_mul_of_nonneg_right hmem.2 hm₂pos.le
        nlinarith [h]
    have hcs₂ : HasCompactSupport (fun u : ℝ => (f (u / (m₂:ℝ)) : ℂ)) :=
      HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (m₂/C₀) (m₂*C₀)) isCompact_Icc
        (fun u hu => by rw [Function.mem_support] at hu; exact hsupp u hu)
    have hcont : Continuous (fun u : ℝ => (f (u / (m₂:ℝ)) : ℂ)) :=
      Complex.continuous_ofReal.comp (hf.comp (continuous_id.div_const _))
    exact (hcont.mul (contDiff_efun.comp (by fun_prop : Continuous fun u : ℝ => -(u * x)))).integrable_of_hasCompactSupport
      (hcs₂.mul_right (f' := fun u : ℝ => efun (-(u * x))))

lemma norm_ofReal_sq (r : ℝ) : ‖((r : ℝ) : ℂ)‖ ^ 2 = r ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_ofReal]; ring

/-- Plancherel: the `L²`-mass of `Bsum` is that of `Hprof`. -/
lemma integral_normSq_Bsum_eq_integral_Hprof_sq {C₀ : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    (hsup : SuppHyp C₀ f) (hC₀ : 1 ≤ C₀) {M₂ : ℝ} (hM₂ : 0 < M₂) :
    ∫ x, ‖Bsum f M₂ x‖ ^ 2 = ∫ u, (Hprof f M₂ u) ^ 2 := by
  have hHcont : Continuous (Hprof f M₂) := Hprof_continuous hf M₂
  have hHcs : HasCompactSupport (Hprof f M₂) := Hprof_hasCompactSupport hsup hC₀ hM₂.le
  have hcontC : Continuous (fun u : ℝ => ((Hprof f M₂ u : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hHcont
  have hcsC : HasCompactSupport (fun u : ℝ => ((Hprof f M₂ u : ℝ) : ℂ)) :=
    hHcs.comp_left (g := fun z : ℝ => (z : ℂ)) (by simp)
  have hplan := plancherel_continuous (fun u : ℝ => ((Hprof f M₂ u : ℝ) : ℂ)) hcontC hcsC
  have h1 : (∫ x, ‖Bsum f M₂ x‖ ^ 2) = ∫ x, ‖Fhat (Hprof f M₂) x‖ ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall (fun x => by
      show ‖Bsum f M₂ x‖ ^ 2 = ‖Fhat (Hprof f M₂) x‖ ^ 2
      rw [Bsum_eq_Fhat_Hprof hf hsup hC₀ hM₂ x]))
  have h2 : (∫ x, ‖Fhat (Hprof f M₂) x‖ ^ 2)
      = ∫ x, ‖FourierTransform.fourier (fun u : ℝ => ((Hprof f M₂ u : ℝ) : ℂ)) x‖ ^ 2 := rfl
  rw [h1, h2, ← hplan]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun x => norm_ofReal_sq _))

/-! ## Counting `ℓ`'s in the windows `Iwin M₃ ℓ = Icc (ℓ - 2/M₃) (ℓ + 2/M₃)` -/

/-- The window `[ℓ - 2/M₃, ℓ + 2/M₃]`. -/
def Iwin (M₃ : ℝ) (ℓ : ℤ) : Set ℝ := Set.Icc ((ℓ:ℝ) - 2/M₃) ((ℓ:ℝ) + 2/M₃)

lemma Iwin_measurable (M₃ : ℝ) (ℓ : ℤ) : MeasurableSet (Iwin M₃ ℓ) := measurableSet_Icc

lemma mem_Iwin {M₃ : ℝ} {ℓ : ℤ} {x : ℝ} :
    x ∈ Iwin M₃ ℓ ↔ |x - (ℓ:ℝ)| ≤ 2/M₃ := by
  rw [Iwin, Set.mem_Icc, abs_le]
  constructor <;> intro h
  · exact ⟨by linarith [h.1], by linarith [h.2]⟩
  · exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- Each real `x` lies in at most `1 + 4/M₃` of the windows `Iwin M₃ ℓ`. -/
lemma tsum_indicator_Iwin_le {M₃ : ℝ} (hM₃ : 0 < M₃) (x : ℝ) :
    (∑' ℓ : ℤ, (Iwin M₃ ℓ).indicator (fun _ => (1:ℝ)) x) ≤ 1 + 4/M₃ := by
  set Q : Finset ℤ := Finset.Icc ⌈x - 2/M₃⌉ ⌊x + 2/M₃⌋ with hQdef
  have hsupp : ∀ ℓ : ℤ, ℓ ∉ Q → (Iwin M₃ ℓ).indicator (fun _ => (1:ℝ)) x = 0 := by
    intro ℓ hℓ
    rw [Set.indicator_of_notMem]
    intro hx
    rw [mem_Iwin] at hx
    rw [hQdef, Finset.mem_Icc, not_and_or] at hℓ
    rcases hℓ with h | h
    · have h1 : (ℓ:ℝ) < x - 2 / M₃ := by
        have := Int.lt_ceil.mp (not_le.mp h)
        exact_mod_cast this
      linarith [abs_le.mp hx]
    · have h1 : (ℓ:ℝ) > x + 2 / M₃ := by
        have h2 : (⌊x + 2/M₃⌋ : ℤ) < ℓ := not_le.mp h
        have h3 : (x + 2/M₃ : ℝ) < ((⌊x + 2/M₃⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
        have h4 : ((⌊x + 2/M₃⌋ : ℤ) : ℝ) + 1 ≤ (ℓ:ℝ) := by
          exact_mod_cast (by omega : ⌊x + 2/M₃⌋ + 1 ≤ ℓ)
        linarith
      linarith [abs_le.mp hx]
  rw [tsum_eq_sum hsupp]
  have hpoint : ∀ ℓ ∈ Q, (Iwin M₃ ℓ).indicator (fun _ => (1:ℝ)) x ≤ (1:ℝ) := by
    intro ℓ hℓ
    by_cases hx : x ∈ Iwin M₃ ℓ
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]; norm_num
  have hsum : (∑ ℓ ∈ Q, (Iwin M₃ ℓ).indicator (fun _ => (1:ℝ)) x) ≤ (Q.card : ℝ) := by
    calc (∑ ℓ ∈ Q, (Iwin M₃ ℓ).indicator (fun _ => (1:ℝ)) x) ≤ ∑ ℓ ∈ Q, (1:ℝ) :=
          Finset.sum_le_sum hpoint
      _ = (Q.card : ℝ) := by simp
  have hcard : (Q.card : ℝ) ≤ 2 * (2/M₃) + 1 := by
    refine card_int_in_interval_le (r := 2/M₃) (ξ := x) (by positivity) Q ?_
    intro n hn
    rw [hQdef, Finset.mem_Icc] at hn
    rw [abs_le]
    constructor
    · have h1 : (x - 2/M₃ : ℝ) ≤ (⌈x - 2/M₃⌉ : ℝ) := Int.le_ceil _
      have h2 : (⌈x - 2/M₃⌉ : ℝ) ≤ (n:ℝ) := by exact_mod_cast hn.1
      linarith
    · have h1 : ((⌊x + 2/M₃⌋ : ℤ) : ℝ) ≤ x + 2/M₃ := Int.floor_le _
      have h2 : (n:ℝ) ≤ ((⌊x + 2/M₃⌋ : ℤ) : ℝ) := by exact_mod_cast hn.2
      linarith
  have hcard' : (Q.card : ℝ) ≤ 4/M₃ + 1 := by
    rw [show 2 * (2/M₃) + 1 = 4/M₃ + 1 from by ring] at hcard
    exact hcard
  linarith [hsum, hcard']

/-- Finset form of the window counting: even over an arbitrary finite set `s ⊆ ℤ`, each `x` lies in
at most `1 + 4/M₃` of the windows `Iwin M₃ ℓ`, `ℓ ∈ s`. -/
lemma finset_sum_indicator_Iwin_le {M₃ : ℝ} (hM₃ : 0 < M₃) (x : ℝ) (s : Finset ℤ) :
    (∑ ℓ ∈ s, (Iwin M₃ ℓ).indicator (fun _ => (1:ℝ)) x) ≤ 1 + 4/M₃ := by
  classical
  set Q : Finset ℤ := s.filter (fun ℓ => x ∈ Iwin M₃ ℓ) with hQdef
  have h1 : (∑ ℓ ∈ s, (Iwin M₃ ℓ).indicator (fun _ => (1:ℝ)) x) = (Q.card : ℝ) := by
    rw [show (∑ ℓ ∈ s, (Iwin M₃ ℓ).indicator (fun _ => (1:ℝ)) x)
        = ∑ ℓ ∈ s, (if x ∈ Iwin M₃ ℓ then (1:ℝ) else 0) from by
      refine Finset.sum_congr rfl (fun ℓ _ => ?_)
      rw [Set.indicator_apply]]
    rw [Finset.sum_boole, hQdef]
  rw [h1]
  have hcard := card_int_in_interval_le (r := 2/M₃) (ξ := x) (by positivity) Q ?_
  · have : (Q.card : ℝ) ≤ 2 * (2/M₃) + 1 := hcard
    rw [show 2 * (2/M₃) + 1 = 4/M₃ + 1 from by ring] at this
    linarith
  · intro n hn
    rw [hQdef, Finset.mem_filter] at hn
    have h := mem_Iwin.mp hn.2
    rwa [abs_sub_comm] at h

end

end Work.GM.Affine
