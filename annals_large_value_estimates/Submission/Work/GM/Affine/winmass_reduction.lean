import Mathlib
import Submission.Work.GM.Affine.far_mass_eq
import Submission.Work.GM.Affine.win_mass_eq
import Submission.Work.GM.Affine.Bsum_periodization
import Submission.Work.GM.Affine.WinMass_basic
import Submission.Work.GM.Affine.pair_swap
import Submission.Work.GM.Affine.intervalIntegrable_parametric
import Submission.Work.GM.Affine.farTauWin_aux

namespace Work.GM.Affine

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

noncomputable section

/-! ## The objects of the assembly -/

/-- The integers on which `Hprof f M₂ (u + ·)` can be nonzero for `u ∈ [0,1]`, given
`SuppHyp C₀ f`: exactly `0 ≤ ℓ ≤ ⌊2 C₀ M₂⌋`. -/
def wmIdx (C₀ M₂ : ℝ) : Finset ℤ := Finset.Icc 0 ⌊2 * C₀ * M₂⌋

/-- The trigonometric polynomial `Σ_{ℓ ∈ s} Hprof f M₂ (u + ℓ) e(ℓ t)` of the assembly. -/
def wmTrig (f : ℝ → ℝ) (M₂ : ℝ) (s : Finset ℤ) (u t : ℝ) : ℂ :=
  ∑ ℓ ∈ s, ((Hprof f M₂ (u + (ℓ : ℝ)) : ℝ) : ℂ) *
    Complex.exp (2 * ↑Real.pi * Complex.I * ((ℓ : ℂ) * (t : ℂ)))

/-- Its modulus squared, the `u`-slice integrand of the assembly. -/
def wmPhi (f : ℝ → ℝ) (M₂ : ℝ) (s : Finset ℤ) (u t : ℝ) : ℝ := ‖wmTrig f M₂ s u t‖ ^ 2

/-- `wmTrig` with the (implicitly finite) sum over all of `ℤ`; this is the object of
`Bsum_periodization`. -/
def wmTrigTsum (f : ℝ → ℝ) (M₂ : ℝ) (u t : ℝ) : ℂ :=
  ∑' ℓ : ℤ, ((Hprof f M₂ (u + (ℓ : ℝ)) : ℝ) : ℂ) *
    Complex.exp (2 * ↑Real.pi * Complex.I * ((ℓ : ℂ) * (t : ℂ)))

/-- The full `ℤ`-sum version of `wmPhi`. -/
def wmPsi (f : ℝ → ℝ) (M₂ : ℝ) (u t : ℝ) : ℝ := ‖wmTrigTsum f M₂ u t‖ ^ 2

/-- The weight `‖ψ̂₁(K M₃ t)‖²`. -/
def wmW (K M₃ : ℝ) (t : ℝ) : ℝ := ‖psi1hat K (M₃ * t)‖ ^ 2

/-- `Σ'_ℓ ‖Bsum f M₂ (ℓ + t)‖²`, the common integrand of `FarMass` and `WinMass`. -/
def wmMass (f : ℝ → ℝ) (M₂ t : ℝ) : ℝ := ∑' ℓ : ℤ, ‖Bsum f M₂ ((ℓ : ℝ) + t)‖ ^ 2

/-- The far set `|t| > 2/M₃`. -/
def wmFar (M₃ : ℝ) : Set ℝ := Set.Ioi (2 / M₃) ∪ Set.Iio (-(2 / M₃))

/-- The window `|t| ≤ 2/M₃`. -/
def wmWin (M₃ : ℝ) : Set ℝ := Set.Icc (-(2 / M₃)) (2 / M₃)

/-! ## The support of `Hprof f M₂` -/

/-- `Hprof f M₂` vanishes for `x ≤ 0` and for `x > 2 C₀ M₂` when `SuppHyp C₀ f`. -/
lemma Hprof_eq_zero_of_notMem {C₀ M₂ : ℝ} (hC₀ : 1 ≤ C₀) (hM₂ : 0 < M₂) {f : ℝ → ℝ}
    (hsup : SuppHyp C₀ f) {x : ℝ} (hx : x ≤ 0 ∨ 2 * C₀ * M₂ < x) : Hprof f M₂ x = 0 := by
  rw [Hprof]
  refine Finset.sum_eq_zero fun m₂ hm₂ => ?_
  by_contra hne
  have hm₂pos : (0 : ℝ) < (m₂ : ℝ) := R2_pos' hm₂
  have hm₂le : (m₂ : ℝ) ≤ 2 * M₂ := R2_le' hm₂
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have hmem := hsup _ hne
  rw [Set.mem_Icc] at hmem
  rcases hx with hx | hx
  · have hxpos : 0 < x := by
      have h1 : 0 < x / (m₂ : ℝ) := lt_of_lt_of_le (one_div_pos.mpr hC₀pos) hmem.1
      calc (0 : ℝ) < (x / (m₂ : ℝ)) * (m₂ : ℝ) := mul_pos h1 hm₂pos
        _ = x := div_mul_cancel₀ x hm₂pos.ne'
    linarith
  · have h2 : x ≤ C₀ * (m₂ : ℝ) := by
      have h3 := mul_le_mul_of_nonneg_right hmem.2 hm₂pos.le
      rwa [div_mul_cancel₀ x hm₂pos.ne'] at h3
    nlinarith [h2, hm₂le, hC₀pos.le]

/-- The support bound in the form used below: `u + ℓ ∉ (0, 2 C₀ M₂]` forces `ℓ ∉ wmIdx C₀ M₂`
for `u ∈ [0,1]`. -/
lemma wmIdx_mem_of_Hprof_ne {C₀ M₂ : ℝ} (hC₀ : 1 ≤ C₀) (hM₂ : 0 < M₂) {f : ℝ → ℝ}
    (hsup : SuppHyp C₀ f) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) {ℓ : ℤ}
    (hne : Hprof f M₂ (u + (ℓ : ℝ)) ≠ 0) : ℓ ∈ wmIdx C₀ M₂ := by
  have hz := Hprof_eq_zero_of_notMem (f := f) hC₀ hM₂ hsup (x := u + (ℓ : ℝ))
  have h1 : ¬ (u + (ℓ : ℝ) ≤ 0) := fun h => hne (hz (Or.inl h))
  have h2 : ¬ (2 * C₀ * M₂ < u + (ℓ : ℝ)) := fun h => hne (hz (Or.inr h))
  push_neg at h1 h2
  rw [wmIdx, Finset.mem_Icc]
  constructor
  · by_contra h
    push_neg at h
    have h3 : (ℓ : ℝ) ≤ -1 := by exact_mod_cast (by omega : ℓ ≤ -1)
    have h4 : u + (ℓ : ℝ) ≤ 0 := by linarith [hu.2]
    linarith
  · have h3 : (ℓ : ℝ) ≤ 2 * C₀ * M₂ := by linarith [hu.1, h2]
    exact_mod_cast (Int.le_floor.mpr h3)

/-- The `ℤ`-sum defining `wmTrigTsum` is the finite sum defining `wmTrig` over `wmIdx C₀ M₂`,
for `u ∈ [0,1]`. -/
lemma wmTrigTsum_eq {C₀ M₂ : ℝ} (hC₀ : 1 ≤ C₀) (hM₂ : 0 < M₂) {f : ℝ → ℝ}
    (hsup : SuppHyp C₀ f) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) :
    wmTrigTsum f M₂ u t = wmTrig f M₂ (wmIdx C₀ M₂) u t := by
  rw [wmTrigTsum, wmTrig]
  refine tsum_eq_sum (s := wmIdx C₀ M₂) fun ℓ hℓ => ?_
  have hz : Hprof f M₂ (u + (ℓ : ℝ)) = 0 := by
    by_contra hne
    exact hℓ (wmIdx_mem_of_Hprof_ne hC₀ hM₂ hsup hu hne)
  simp [hz]

/-- `Hprof f M₂` is nonnegative when `f` is. -/
lemma Hprof_nonneg {f : ℝ → ℝ} (hfnn : ∀ u, 0 ≤ f u) (M₂ x : ℝ) : 0 ≤ Hprof f M₂ x := by
  rw [Hprof]
  exact Finset.sum_nonneg fun m₂ _ => hfnn _

/-! ## Continuity and bounds -/

lemma continuous_wmTrig (f : ℝ → ℝ) (M₂ : ℝ) (s : Finset ℤ) (hf : Continuous f) :
    Continuous (fun p : ℝ × ℝ => wmTrig f M₂ s p.1 p.2) := by
  unfold wmTrig
  refine continuous_finsetSum _ (fun ℓ _ => ?_)
  have h1 : Continuous (fun p : ℝ × ℝ => ((Hprof f M₂ (p.1 + (ℓ : ℝ)) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((Hprof_continuous hf M₂).comp (continuous_fst.add continuous_const))
  have h2 : Continuous (fun p : ℝ × ℝ =>
      Complex.exp (2 * ↑Real.pi * Complex.I * ((ℓ : ℂ) * (p.2 : ℂ)))) := by
    fun_prop
  exact h1.mul h2

lemma continuous_wmPhi (f : ℝ → ℝ) (M₂ : ℝ) (s : Finset ℤ) (hf : Continuous f) :
    Continuous (fun p : ℝ × ℝ => wmPhi f M₂ s p.1 p.2) := by
  unfold wmPhi
  exact (continuous_wmTrig f M₂ s hf).norm.pow 2

lemma continuous_wmW (K M₃ : ℝ) : Continuous (wmW K M₃) := by
  unfold wmW
  exact (((psi1hat_continuous K).comp (continuous_const.mul continuous_id)).norm).pow 2

/-- A uniform bound for `wmPhi f M₂ s` on `[0,1] × ℝ`. -/
lemma exists_bound_wmPhi {C₀ M₂ : ℝ} (hC₀ : 1 ≤ C₀) (hM₂ : 0 < M₂) {f : ℝ → ℝ}
    (hf : Continuous f) (hsup : SuppHyp C₀ f) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ t, ‖wmPhi f M₂ (wmIdx C₀ M₂) u t‖ ≤ D := by
  classical
  obtain ⟨Cb, hCb⟩ : ∃ Cb : ℝ, ∀ x ∈ Set.Icc (0 : ℝ) (2 * C₀ * M₂),
      ‖((Hprof f M₂ x : ℝ) : ℂ)‖ ≤ Cb :=
    isCompact_Icc.exists_bound_of_continuousOn
      (Complex.continuous_ofReal.comp (Hprof_continuous hf M₂)).continuousOn
  set B : ℝ := max Cb 0 with hBdef
  have hBnn : 0 ≤ B := le_max_right _ _
  have hB : ∀ x : ℝ, ‖((Hprof f M₂ x : ℝ) : ℂ)‖ ≤ B := by
    intro x
    by_cases hx : x ≤ 0 ∨ 2 * C₀ * M₂ < x
    · rw [Hprof_eq_zero_of_notMem hC₀ hM₂ hsup hx]
      simp only [Complex.ofReal_zero, norm_zero]
      exact hBnn
    · push_neg at hx
      exact le_trans (hCb x ⟨hx.1.le, hx.2⟩) (le_max_left _ _)
  refine ⟨((wmIdx C₀ M₂).card * B) ^ 2, by positivity, fun u hu t => ?_⟩
  have hterm : ∀ ℓ ∈ wmIdx C₀ M₂,
      ‖((Hprof f M₂ (u + (ℓ : ℝ)) : ℝ) : ℂ)
        * Complex.exp (2 * ↑Real.pi * Complex.I * ((ℓ : ℂ) * (t : ℂ)))‖ ≤ B := by
    intro ℓ _
    have hexp : Complex.exp (2 * ↑Real.pi * Complex.I * ((ℓ : ℂ) * (t : ℂ)))
        = efun ((ℓ : ℝ) * t) := by
      rw [efun]
      push_cast
      ring_nf
    rw [norm_mul, hexp, norm_efun, mul_one]
    exact hB _
  have htrig : ‖wmTrig f M₂ (wmIdx C₀ M₂) u t‖ ≤ ((wmIdx C₀ M₂).card : ℝ) * B := by
    rw [wmTrig]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ ℓ ∈ wmIdx C₀ M₂, ‖((Hprof f M₂ (u + (ℓ : ℝ)) : ℝ) : ℂ)
            * Complex.exp (2 * ↑Real.pi * Complex.I * ((ℓ : ℂ) * (t : ℂ)))‖
        ≤ ∑ _ℓ ∈ wmIdx C₀ M₂, B := Finset.sum_le_sum hterm
      _ = ((wmIdx C₀ M₂).card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [wmPhi]
  have h1 : ‖(‖wmTrig f M₂ (wmIdx C₀ M₂) u t‖ : ℝ) ^ 2‖
      = ‖wmTrig f M₂ (wmIdx C₀ M₂) u t‖ ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [h1]
  exact sq_le_sq' (by linarith [norm_nonneg (wmTrig f M₂ (wmIdx C₀ M₂) u t)]) htrig

lemma integrable_wmW {K M₃ : ℝ} (hM₃ : 0 < M₃) : Integrable (wmW K M₃) :=
  (psi1hat_sq_integrable K).comp_mul_left' hM₃.ne'

lemma wmFar_measurable (M₃ : ℝ) : MeasurableSet (wmFar M₃) :=
  measurableSet_Ioi.union measurableSet_Iio

lemma wmWin_measurable (M₃ : ℝ) : MeasurableSet (wmWin M₃) := measurableSet_Icc

lemma one_integrableOn_wmWin (M₃ : ℝ) :
    IntegrableOn (fun _ : ℝ => (1 : ℝ)) (wmWin M₃) volume := by
  refine IntegrableOn.of_bound ?_ aestronglyMeasurable_const 1
    (Filter.Eventually.of_forall (fun x => le_of_eq (norm_one))) 
  rw [wmWin]
  exact isCompact_Icc.measure_lt_top

/-- Splitting the integral over the far set into the two half-lines. -/
lemma setIntegral_wmFar_eq {K M₃ D : ℝ} (hM₃ : 0 < M₃) {f : ℝ → ℝ} {M₂ : ℝ} {s : Finset ℤ}
    (hf : Continuous f) (hbdd : ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ t, ‖wmPhi f M₂ s u t‖ ≤ D)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    ∫ t in wmFar M₃, wmPhi f M₂ s u t * wmW K M₃ t
      = (∫ t in Set.Ioi (2 / M₃), wmPhi f M₂ s u t * wmW K M₃ t)
        + (∫ t in Set.Iio (-(2 / M₃)), wmPhi f M₂ s u t * wmW K M₃ t) := by
  have hpt : ∀ t : ℝ, ‖wmPhi f M₂ s u t * wmW K M₃ t‖ ≤ D * ‖wmW K M₃ t‖ := by
    intro t
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbdd u hu t) (norm_nonneg _)
  have hcont_t : Continuous (fun t : ℝ => wmPhi f M₂ s u t * wmW K M₃ t) :=
    ((continuous_wmPhi f M₂ s hf).comp (continuous_const.prodMk continuous_id)).mul
      (continuous_wmW K M₃)
  have hint : ∀ T : Set ℝ, IntegrableOn (fun t : ℝ => wmPhi f M₂ s u t * wmW K M₃ t) T volume := by
    intro T
    refine Integrable.mono' (((integrable_wmW (K := K) hM₃).norm.const_mul D).integrableOn)
      hcont_t.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall hpt
  have hdisj : Disjoint (Set.Ioi (2 / M₃)) (Set.Iio (-(2 / M₃))) := by
    rw [Set.disjoint_left]
    intro x h1 h2
    rw [Set.mem_Ioi] at h1
    rw [Set.mem_Iio] at h2
    have : (0 : ℝ) < 2 / M₃ := by positivity
    linarith
  rw [wmFar]
  exact setIntegral_union hdisj measurableSet_Iio (hint _) (hint _)

/-! ## The assembly -/

/-- Assembly: the target inequality `FarMass ≤ C · WinMass` follows from the per-sequence crux
`far_sampling_crux`, using the two mass identities (`far_mass_eq`, `win_mass_eq`) and the
periodisation identity `Bsum_periodization`. -/
theorem winmass_reduction {C₀ K C : ℝ} (hC₀ : 1 ≤ C₀) (hK : 0 < K) (hC : 0 < C)
    (hcrux : ∀ M₃ : ℝ, 1 ≤ M₃ → ∀ (s : Finset ℤ) (H : ℤ → ℝ), (∀ ℓ, 0 ≤ H ℓ) →
      ((∫ t in Set.Ioi (2 / M₃),
          ‖∑ ℓ ∈ s, (H ℓ : ℂ) * Complex.exp (2 * ↑Real.pi * Complex.I * ((ℓ : ℂ) * (t : ℂ)))‖ ^ 2
            * ‖psi1hat K (M₃ * t)‖ ^ 2)
        + (∫ t in Set.Iio (-(2 / M₃)),
          ‖∑ ℓ ∈ s, (H ℓ : ℂ) * Complex.exp (2 * ↑Real.pi * Complex.I * ((ℓ : ℂ) * (t : ℂ)))‖ ^ 2
            * ‖psi1hat K (M₃ * t)‖ ^ 2))
      ≤ C * ∫ t in Set.Icc (-(2 / M₃)) (2 / M₃),
          ‖∑ ℓ ∈ s, (H ℓ : ℂ) * Complex.exp (2 * ↑Real.pi * Complex.I * ((ℓ : ℂ) * (t : ℂ)))‖ ^ 2) :
    ∀ M₂ M₃ : ℝ, 0 < M₂ → 1 ≤ M₃ → ∀ f : ℝ → ℝ, Continuous f →
      (∀ u, 0 ≤ f u) → SuppHyp C₀ f → FarMass K f M₂ M₃ ≤ C * WinMass f M₂ M₃ := by
  intro M₂ M₃ hM₂ hM₃ f hf hfnn hsup
  have hM₃pos : 0 < M₃ := lt_of_lt_of_le zero_lt_one hM₃
  obtain ⟨D, hDnn, hDbdd⟩ := exists_bound_wmPhi (M₂ := M₂) hC₀ hM₂ hf hsup
  set s : Finset ℤ := wmIdx C₀ M₂ with hs
  -- continuity of the integrand of the crux
  have hcont : Continuous (fun p : ℝ × ℝ => wmPhi f M₂ s p.1 p.2 * wmW K M₃ p.2) :=
    (continuous_wmPhi f M₂ s hf).mul ((continuous_wmW K M₃).comp continuous_snd)
  have hDbdd' : ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ t, ‖wmPhi f M₂ s u t‖ ≤ D := by
    intro u hu t
    rw [hs]
    exact hDbdd u hu t
  -- `Bsum_periodization` at every `t`
  have hG : ∀ t : ℝ, wmMass f M₂ t = ∫ u in (0 : ℝ)..1, wmPsi f M₂ u t := by
    intro t
    simp only [wmMass, wmPsi, wmTrigTsum]
    exact Bsum_periodization hC₀ hM₂ hf hsup t
  -- the identification `wmPsi = wmPhi` on `u ∈ [0,1]`
  have hident : ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, wmPsi f M₂ u t = wmPhi f M₂ s u t := by
    intro u hu t
    rw [wmPsi, wmPhi, hs]
    exact congrArg (fun z : ℂ => ‖z‖ ^ 2) (wmTrigTsum_eq hC₀ hM₂ hsup hu t)
  -- LHS rewrite
  have hL1 : ∫ t in wmFar M₃, wmMass f M₂ t * wmW K M₃ t
      = ∫ t in wmFar M₃, (∫ u in (0 : ℝ)..1, wmPhi f M₂ s u t) * wmW K M₃ t := by
    refine setIntegral_congr_fun (wmFar_measurable M₃) fun t _ => ?_
    rw [hG t]
    congr 1
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hu
    exact hident u hu t
  -- Fubini on the far side
  have hswapF := pair_swap (S := wmFar M₃) (wmFar_measurable M₃) (w := wmW K M₃) (D := D)
    hDnn hcont ((integrable_wmW (K := K) hM₃pos).integrableOn) hDbdd'
  have hstep1 : ∫ t in wmFar M₃, wmMass f M₂ t * wmW K M₃ t
      = ∫ u in (0 : ℝ)..1, ∫ t in wmFar M₃, wmPhi f M₂ s u t * wmW K M₃ t :=
    hL1.trans hswapF
  -- the pointwise crux
  have hpt : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      (∫ t in wmFar M₃, wmPhi f M₂ s u t * wmW K M₃ t)
        ≤ C * ∫ t in wmWin M₃, wmPhi f M₂ s u t := by
    intro u hu
    have hsplit := setIntegral_wmFar_eq (K := K) (D := D) hM₃pos hf hDbdd' hu
    rw [hsplit]
    have hcu := hcrux M₃ hM₃ s (fun ℓ : ℤ => Hprof f M₂ (u + (ℓ : ℝ)))
      (fun ℓ => Hprof_nonneg hfnn M₂ _)
    simpa only [wmPhi, wmTrig, wmW, wmWin, hs] using hcu
  -- the same with the trivial weight `1` (the window side)
  have hcont1 : Continuous (fun p : ℝ × ℝ => wmPhi f M₂ s p.1 p.2 * (1 : ℝ)) := by
    simpa using continuous_wmPhi f M₂ s hf
  -- monotonicity in `u`
  have hAint : IntervalIntegrable
      (fun u => ∫ t in wmFar M₃, wmPhi f M₂ s u t * wmW K M₃ t) volume 0 1 :=
    intervalIntegrable_parametric (wmFar_measurable M₃) hDnn hcont
      ((integrable_wmW (K := K) hM₃pos).integrableOn) hDbdd'
  have hBint : IntervalIntegrable
      (fun u => ∫ t in wmWin M₃, wmPhi f M₂ s u t) volume 0 1 := by
    have h1 : IntervalIntegrable
        (fun u => ∫ t in wmWin M₃, wmPhi f M₂ s u t * (1 : ℝ)) volume 0 1 :=
      intervalIntegrable_parametric (wmWin_measurable M₃) hDnn hcont1
        (one_integrableOn_wmWin M₃) hDbdd'
    simpa using h1
  have hCint : IntervalIntegrable
      (fun u => C * ∫ t in wmWin M₃, wmPhi f M₂ s u t) volume 0 1 :=
    hBint.const_mul C
  have hmono : (∫ u in (0 : ℝ)..1, ∫ t in wmFar M₃, wmPhi f M₂ s u t * wmW K M₃ t)
      ≤ ∫ u in (0 : ℝ)..1, C * ∫ t in wmWin M₃, wmPhi f M₂ s u t :=
    intervalIntegral.integral_mono_on (by norm_num) hAint hCint hpt
  have hR1 : ∫ u in (0 : ℝ)..1, C * ∫ t in wmWin M₃, wmPhi f M₂ s u t
      = C * ∫ u in (0 : ℝ)..1, ∫ t in wmWin M₃, wmPhi f M₂ s u t :=
    intervalIntegral.integral_const_mul C
      (fun u => ∫ t in wmWin M₃, wmPhi f M₂ s u t)
  have hswapW : ∫ t in wmWin M₃, (∫ u in (0 : ℝ)..1, wmPhi f M₂ s u t)
      = ∫ u in (0 : ℝ)..1, ∫ t in wmWin M₃, wmPhi f M₂ s u t := by
    simpa using pair_swap (S := wmWin M₃) (wmWin_measurable M₃) (w := fun _ : ℝ => (1:ℝ))
      (D := D) hDnn hcont1 (one_integrableOn_wmWin M₃) hDbdd'
  have hR2 : ∫ u in (0 : ℝ)..1, ∫ t in wmWin M₃, wmPhi f M₂ s u t
      = ∫ t in wmWin M₃, wmMass f M₂ t := by
    rw [← hswapW]
    refine setIntegral_congr_fun (wmWin_measurable M₃) fun t _ => ?_
    rw [hG t]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hu
    exact (hident u hu t).symm
  have hmain : ∫ t in wmFar M₃, wmMass f M₂ t * wmW K M₃ t
      ≤ C * ∫ t in wmWin M₃, wmMass f M₂ t :=
    calc ∫ t in wmFar M₃, wmMass f M₂ t * wmW K M₃ t
        = ∫ u in (0 : ℝ)..1, ∫ t in wmFar M₃, wmPhi f M₂ s u t * wmW K M₃ t := hstep1
      _ ≤ ∫ u in (0 : ℝ)..1, C * ∫ t in wmWin M₃, wmPhi f M₂ s u t := hmono
      _ = C * ∫ t in wmWin M₃, wmMass f M₂ t := by rw [hR1, hR2]
  rw [far_mass_eq hC₀ hK hM₂ hM₃pos hf hsup, win_mass_eq hC₀ hM₂ hM₃pos hf hsup]
  have hmain' : ∫ t in (Set.Ioi (2 / M₃) ∪ Set.Iio (-(2 / M₃))),
        (∑' ℓ : ℤ, ‖Bsum f M₂ ((ℓ : ℝ) + t)‖ ^ 2) * ‖psi1hat K (M₃ * t)‖ ^ 2
      ≤ C * ∫ t in Set.Icc (-(2 / M₃)) (2 / M₃),
          (∑' ℓ : ℤ, ‖Bsum f M₂ ((ℓ : ℝ) + t)‖ ^ 2) := by
    simpa only [wmFar, wmMass, wmW, wmWin] using hmain
  calc M₃ * (∫ t in (Set.Ioi (2 / M₃) ∪ Set.Iio (-(2 / M₃))),
        (∑' ℓ : ℤ, ‖Bsum f M₂ ((ℓ : ℝ) + t)‖ ^ 2) * ‖psi1hat K (M₃ * t)‖ ^ 2)
      ≤ M₃ * (C * ∫ t in Set.Icc (-(2 / M₃)) (2 / M₃),
          (∑' ℓ : ℤ, ‖Bsum f M₂ ((ℓ : ℝ) + t)‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hmain' hM₃pos.le
    _ = C * (M₃ * ∫ t in Set.Icc (-(2 / M₃)) (2 / M₃),
          (∑' ℓ : ℤ, ‖Bsum f M₂ ((ℓ : ℝ) + t)‖ ^ 2)) := by ring

end

end Work.GM.Affine
