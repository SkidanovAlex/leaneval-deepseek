import Mathlib
import Submission.Work.ZeroDensity.LogFree.poleLSDefs
import Submission.Work.ZeroDensity.LogFree.HB7MvtAny

open scoped BigOperators
open MeasureTheory intervalIntegral

namespace Work.ZeroDensity.LogFree

private lemma hb7fi_slice_cont (γ : ℝ) {t : ℝ} (ht : 0 < t) :
    Continuous (fun b : ℝ => (t : ℂ) ^ ((b : ℂ) - (γ : ℂ) * Complex.I)) := by
  have hc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  have h1 : Continuous (fun b : ℝ => ((t ^ b : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_const_rpow ht.ne')
  have h2 : Continuous
      (fun b : ℝ => ((t ^ b : ℝ) : ℂ) * (t : ℂ) ^ ((-(γ : ℂ)) * Complex.I)) :=
    h1.mul continuous_const
  refine h2.congr (fun b => ?_)
  rw [show ((t ^ b : ℝ) : ℂ) = (t : ℂ) ^ ((b : ℂ)) from Complex.ofReal_cpow ht.le b]
  rw [← Complex.cpow_add _ _ hc]
  congr 1
  ring

private lemma hb7fi_slice_integrable (a γ : ℝ) (z : ℂ) {A t : ℝ} (ht : 0 < t) (hA : 0 ≤ A) :
    IntervalIntegrable
      (fun b : ℝ => (if b ≤ a then z else 0) * (t : ℂ) ^ ((b : ℂ) - (γ : ℂ) * Complex.I))
      volume 0 A := by
  have hcont : Continuous (fun b : ℝ => z * (t : ℂ) ^ ((b : ℂ) - (γ : ℂ) * Complex.I)) :=
    continuous_const.mul (hb7fi_slice_cont γ ht)
  have hG : Integrable ((Set.Ioc (0:ℝ) a).indicator
      (fun b : ℝ => z * (t : ℂ) ^ ((b : ℂ) - (γ : ℂ) * Complex.I))) volume :=
    (integrable_indicator_iff measurableSet_Ioc).2 hcont.integrableOn_Ioc
  have hInd : IntervalIntegrable ((Set.Ioc (0:ℝ) a).indicator
      (fun b : ℝ => z * (t : ℂ) ^ ((b : ℂ) - (γ : ℂ) * Complex.I))) volume 0 A :=
    ⟨hG.integrableOn, hG.integrableOn⟩
  refine hInd.congr (fun b hb => ?_)
  rw [Set.uIoc_of_le hA] at hb
  have hb0 : 0 < b := hb.1
  by_cases hba : b ≤ a
  · rw [if_pos hba, Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hb0, hba⟩)]
  · rw [if_neg hba, Set.indicator_of_notMem (fun hc => hba hc.2), zero_mul]

private lemma hb7fi_expansion_term (a γ : ℝ) (z : ℂ) {A t : ℝ}
    (ht : 0 < t) (hA : 0 ≤ A) (ha0 : 0 ≤ a) (haA : a ≤ A) :
    z * (t : ℂ) ^ ((a : ℂ) - (γ : ℂ) * Complex.I)
      = z * (t : ℂ) ^ ((-(γ : ℂ)) * Complex.I)
        + ((Real.log t : ℝ) : ℂ) * (∫ b in (0)..A,
            (if b ≤ a then z else 0) * (t : ℂ) ^ ((b : ℂ) - (γ : ℂ) * Complex.I)) := by
  have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  set c : ℂ := (t : ℂ) ^ ((-(γ : ℂ)) * Complex.I) with hc
  set Q : ℝ := ∫ b in (0)..a, t ^ b with hQ
  have hcpow : ∀ b : ℝ, (t : ℂ) ^ ((b : ℂ) - (γ : ℂ) * Complex.I) = ((t ^ b : ℝ) : ℂ) * c := by
    intro b
    have h1 : ((t ^ b : ℝ) : ℂ) = (t : ℂ) ^ ((b : ℂ)) := Complex.ofReal_cpow ht.le b
    have h2 : (b : ℂ) + ((-(γ : ℂ)) * Complex.I) = (b : ℂ) - (γ : ℂ) * Complex.I := by ring
    rw [← h2, Complex.cpow_add _ _ htne, ← h1, ← hc]
  have hFTC : ((Real.log t : ℝ) : ℂ) * (Q : ℂ) = ((t ^ a : ℝ) : ℂ) - 1 := by
    have hderiv : ∀ b ∈ Set.uIcc (0:ℝ) a, HasDerivAt (fun b : ℝ => t ^ b) (Real.log t * t ^ b) b := by
      intro b _
      simpa using (hasDerivAt_id b).const_rpow ht
    have hint : IntervalIntegrable (fun b : ℝ => Real.log t * t ^ b) volume 0 a :=
      Continuous.intervalIntegrable (continuous_const.mul (Real.continuous_const_rpow ht.ne')) 0 a
    have h := integral_eq_sub_of_hasDerivAt hderiv hint
    rw [Real.rpow_zero] at h
    rw [intervalIntegral.integral_const_mul] at h
    rw [hQ]
    have h' := congrArg (fun r : ℝ => (r : ℂ)) h
    push_cast at h'
    simpa using h'
  have htrunc : (∫ b in (0)..A,
        (if b ≤ a then z else 0) * (t : ℂ) ^ ((b : ℂ) - (γ : ℂ) * Complex.I))
      = z * (∫ b in (0)..a, (t : ℂ) ^ ((b : ℂ) - (γ : ℂ) * Complex.I)) := by
    have hae : ∀ᵐ b ∂(volume : Measure ℝ), b ∈ Set.uIoc (0:ℝ) A →
        (if b ≤ a then z else 0) * (t : ℂ) ^ ((b : ℂ) - (γ : ℂ) * Complex.I)
          = (Set.Ioc (0:ℝ) a).indicator
              (fun b : ℝ => z * (t : ℂ) ^ ((b : ℂ) - (γ : ℂ) * Complex.I)) b := by
      rw [Set.uIoc_of_le hA]
      filter_upwards with b hb
      have hb0 : 0 < b := hb.1
      by_cases hba : b ≤ a
      · rw [if_pos hba, Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hb0, hba⟩)]
      · rw [if_neg hba, Set.indicator_of_notMem (fun hc => hba hc.2), zero_mul]
    rw [intervalIntegral.integral_congr_ae hae, integral_of_le hA]
    rw [setIntegral_indicator measurableSet_Ioc]
    rw [show Set.Ioc (0:ℝ) A ∩ Set.Ioc (0:ℝ) a = Set.Ioc (0:ℝ) a from by
      ext b
      simp only [Set.mem_inter_iff, Set.mem_Ioc]
      exact ⟨fun h => h.2, fun h => ⟨⟨h.1, le_trans h.2 haA⟩, h⟩⟩]
    rw [← integral_of_le ha0, intervalIntegral.integral_const_mul]
  have hI : (∫ b in (0)..a, (t : ℂ) ^ ((b : ℂ) - (γ : ℂ) * Complex.I)) = (Q : ℂ) * c := by
    rw [intervalIntegral.integral_congr (fun b _ => hcpow b)]
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal]
  rw [htrunc, hI]
  have hTa : (t : ℂ) ^ ((a : ℂ) - (γ : ℂ) * Complex.I) = ((t ^ a : ℝ) : ℂ) * c := by
    have h1 : ((t ^ a : ℝ) : ℂ) = (t : ℂ) ^ ((a : ℂ)) := Complex.ofReal_cpow ht.le a
    have h2 : (a : ℂ) + ((-(γ : ℂ)) * Complex.I) = (a : ℂ) - (γ : ℂ) * Complex.I := by ring
    rw [← h2, Complex.cpow_add _ _ htne, ← h1, ← hc]
  rw [hTa]
  have hkey : ((Real.log t : ℝ) : ℂ) * (z * ((Q : ℂ) * c))
      = z * c * (((Real.log t : ℝ) : ℂ) * (Q : ℂ)) := by ring
  rw [hkey, hFTC]
  ring

private theorem hb7fi_expansion {ι : Type*} [Fintype ι] (a γ : ι → ℝ) (ζ : ι → ℂ) {A t : ℝ}
    (ht : 0 < t) (hA : 0 ≤ A) (ha0 : ∀ i, 0 ≤ a i) (haA : ∀ i, a i ≤ A) :
    (∑ i, ζ i * (t : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I))
      = (∑ i, ζ i * (t : ℂ) ^ ((-(γ i : ℂ)) * Complex.I))
        + ((Real.log t : ℝ) : ℂ) * (∫ b in (0)..A,
            ∑ i, (if b ≤ a i then ζ i else 0) * (t : ℂ) ^ ((b : ℂ) - (γ i : ℂ) * Complex.I)) := by
  have hterm : ∀ i, ζ i * (t : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)
      = ζ i * (t : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)
        + ((Real.log t : ℝ) : ℂ) * (∫ b in (0)..A,
            (if b ≤ a i then ζ i else 0) * (t : ℂ) ^ ((b : ℂ) - (γ i : ℂ) * Complex.I)) :=
    fun i => hb7fi_expansion_term (a i) (γ i) (ζ i) ht hA (ha0 i) (haA i)
  calc (∑ i, ζ i * (t : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I))
      = ∑ i, (ζ i * (t : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)
          + ((Real.log t : ℝ) : ℂ) * (∫ b in (0)..A,
              (if b ≤ a i then ζ i else 0) * (t : ℂ) ^ ((b : ℂ) - (γ i : ℂ) * Complex.I))) :=
        Finset.sum_congr rfl (fun i _ => hterm i)
    _ = (∑ i, ζ i * (t : ℂ) ^ ((-(γ i : ℂ)) * Complex.I))
          + ∑ i, ((Real.log t : ℝ) : ℂ) * (∫ b in (0)..A,
              (if b ≤ a i then ζ i else 0) * (t : ℂ) ^ ((b : ℂ) - (γ i : ℂ) * Complex.I)) :=
        Finset.sum_add_distrib
    _ = (∑ i, ζ i * (t : ℂ) ^ ((-(γ i : ℂ)) * Complex.I))
          + ((Real.log t : ℝ) : ℂ) * ∑ i, (∫ b in (0)..A,
              (if b ≤ a i then ζ i else 0) * (t : ℂ) ^ ((b : ℂ) - (γ i : ℂ) * Complex.I)) := by
        rw [Finset.mul_sum]
    _ = (∑ i, ζ i * (t : ℂ) ^ ((-(γ i : ℂ)) * Complex.I))
          + ((Real.log t : ℝ) : ℂ) * (∫ b in (0)..A,
              ∑ i, (if b ≤ a i then ζ i else 0) * (t : ℂ) ^ ((b : ℂ) - (γ i : ℂ) * Complex.I)) := by
        congr 1
        rw [intervalIntegral.integral_finset_sum]
        intro i _
        exact hb7fi_slice_integrable (a i) (γ i) (ζ i) ht hA

private lemma hb7fi_cont_cpow {w : ℂ} {η : ℝ} (hη : 0 ≤ η) :
    ContinuousOn (fun t : ℝ => (t : ℂ) ^ w) (Set.uIcc (Real.exp (-η)) 1) := by
  intro x hx
  rw [Set.uIcc_of_le (Real.exp_le_one_iff.mpr (by linarith only [hη]))] at hx
  exact (Complex.continuousAt_ofReal_cpow_const x w
    (Or.inr (ne_of_gt (lt_of_lt_of_le (Real.exp_pos _) hx.1)))).continuousWithinAt

private theorem hb7fi_level {C : ℝ} (hC : 0 ≤ C) (hMVT : MvtMul C)
    {ι : Type*} [Fintype ι] {δ η : ℝ} (hδ : 0 < δ) (hη : 0 ≤ η)
    (a γ : ι → ℝ) (ζ : ι → ℂ) (hsep : ∀ i j, i ≠ j → δ ≤ |γ i - γ j|) {b : ℝ} (hb : 0 ≤ b) :
    (∫ t in Real.exp (-η)..1,
        ‖∑ i, (if b ≤ a i then ζ i else 0) * (t : ℂ) ^ ((b : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / t)
      ≤ (η + C / δ) * ∑ i, ‖ζ i‖ ^ 2 := by
  have hle1 : Real.exp (-η) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hη])
  have hcont_big : ContinuousOn (fun t : ℝ =>
      ‖∑ i, (if b ≤ a i then ζ i else 0) * (t : ℂ) ^ ((b : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / t)
      (Set.uIcc (Real.exp (-η)) 1) := by
    have hsum : ContinuousOn (fun t : ℝ =>
        ∑ i, (if b ≤ a i then ζ i else 0) * (t : ℂ) ^ ((b : ℂ) - (γ i : ℂ) * Complex.I))
        (Set.uIcc (Real.exp (-η)) 1) :=
      continuousOn_finsetSum Finset.univ (fun i _ =>
        (hb7fi_cont_cpow (w := (b:ℂ) - (γ i:ℂ) * Complex.I) hη).const_mul _)
    refine ((hsum.norm.pow 2).div continuousOn_id (fun x hx => ?_)).congr (fun x _ => ?_)
    · rw [Set.uIcc_of_le hle1] at hx
      exact ne_of_gt (lt_of_lt_of_le (Real.exp_pos _) hx.1)
    · rfl
  have hcont_w : ContinuousOn (fun t : ℝ =>
      ‖∑ i, (if b ≤ a i then ζ i else 0) * (t : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)‖ ^ 2 / t)
      (Set.uIcc (Real.exp (-η)) 1) := by
    have hsum : ContinuousOn (fun t : ℝ =>
        ∑ i, (if b ≤ a i then ζ i else 0) * (t : ℂ) ^ ((-(γ i : ℂ)) * Complex.I))
        (Set.uIcc (Real.exp (-η)) 1) :=
      continuousOn_finsetSum Finset.univ (fun i _ =>
        (hb7fi_cont_cpow (w := (-(γ i:ℂ)) * Complex.I) hη).const_mul _)
    refine ((hsum.norm.pow 2).div continuousOn_id (fun x hx => ?_)).congr (fun x _ => ?_)
    · rw [Set.uIcc_of_le hle1] at hx
      exact ne_of_gt (lt_of_lt_of_le (Real.exp_pos _) hx.1)
    · rfl
  have hpoint : ∀ t ∈ Set.Icc (Real.exp (-η)) 1,
      ‖∑ i, (if b ≤ a i then ζ i else 0) * (t : ℂ) ^ ((b : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / t
        ≤ ‖∑ i, (if b ≤ a i then ζ i else 0) * (t : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)‖ ^ 2 / t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos _) ht.1
    have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
    have hsum_eq : ∑ i, (if b ≤ a i then ζ i else 0) * (t : ℂ) ^ ((b : ℂ) - (γ i : ℂ) * Complex.I)
        = ((t ^ b : ℝ) : ℂ)
          * ∑ i, (if b ≤ a i then ζ i else 0) * (t : ℂ) ^ ((-(γ i : ℂ)) * Complex.I) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hba : b ≤ a i
      · have h := Complex.cpow_add (x := (t:ℂ)) ((b:ℂ)) ((-(γ i:ℂ)) * Complex.I) htne
        rw [show (b:ℂ) + ((-(γ i:ℂ)) * Complex.I) = (b:ℂ) - (γ i:ℂ) * Complex.I from by ring] at h
        rw [h, Complex.ofReal_cpow ht0.le b]
        ring
      · simp [hba]
    have hnorm : ‖∑ i, (if b ≤ a i then ζ i else 0) * (t : ℂ) ^ ((b : ℂ) - (γ i : ℂ) * Complex.I)‖
        ≤ ‖∑ i, (if b ≤ a i then ζ i else 0) * (t : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)‖ := by
      rw [hsum_eq, norm_mul]
      have hnb : ‖((t ^ b : ℝ) : ℂ)‖ = t ^ b := by
        have h : ‖((t ^ b : ℝ) : ℂ)‖ = |(t ^ b : ℝ)| := by simp
        rw [h, abs_of_nonneg (Real.rpow_nonneg ht0.le b)]
      rw [hnb]
      calc t ^ b * ‖∑ i, (if b ≤ a i then ζ i else 0) * (t : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)‖
            ≤ 1 * ‖∑ i, (if b ≤ a i then ζ i else 0) * (t : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)‖ :=
              mul_le_mul_of_nonneg_right (Real.rpow_le_one ht0.le ht.2 hb) (norm_nonneg _)
        _ = _ := one_mul _
    have h2 : ‖∑ i, (if b ≤ a i then ζ i else 0) * (t : ℂ) ^ ((b : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2
        ≤ ‖∑ i, (if b ≤ a i then ζ i else 0) * (t : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)‖ ^ 2 := by
      nlinarith only [norm_nonneg (∑ i, (if b ≤ a i then ζ i else 0) * (t : ℂ) ^ ((b : ℂ) - (γ i : ℂ) * Complex.I)),
        norm_nonneg (∑ i, (if b ≤ a i then ζ i else 0) * (t : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)), hnorm]
    exact div_le_div_of_nonneg_right h2 ht0.le
  have hmono : (∫ t in Real.exp (-η)..1,
        ‖∑ i, (if b ≤ a i then ζ i else 0) * (t : ℂ) ^ ((b : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / t)
      ≤ ∫ t in Real.exp (-η)..1,
        ‖∑ i, (if b ≤ a i then ζ i else 0) * (t : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)‖ ^ 2 / t :=
    intervalIntegral.integral_mono_on hle1 hcont_big.intervalIntegrable hcont_w.intervalIntegrable
      (fun t ht => hpoint t ht)
  refine hmono.trans ?_
  have hmvt := HB7MvtAny hMVT δ hδ γ (fun i => (if b ≤ a i then ζ i else 0))
    (Real.exp (-η)) 1 (Real.exp_pos _) hle1 hsep
  have hlog : Real.log (1 / Real.exp (-η)) = η := by
    rw [one_div, Real.log_inv, Real.log_exp]; ring
  rw [hlog] at hmvt
  have hsum_le : (∑ i, ‖(if b ≤ a i then ζ i else 0)‖ ^ 2) ≤ ∑ i, ‖ζ i‖ ^ 2 :=
    Finset.sum_le_sum (fun i _ => by by_cases h : b ≤ a i <;> simp [h])
  refine hmvt.trans ?_
  exact mul_le_mul_of_nonneg_left hsum_le (add_nonneg hη (div_nonneg hC hδ.le))

private lemma hb7fi_integrable_const_Ioc (A c : ℝ) :
    Integrable (fun _ : ℝ => c) (volume.restrict (Set.Ioc 0 A)) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc 0 A)) := by
    rw [MeasureTheory.isFiniteMeasure_restrict, Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  exact integrable_const_iff.mpr (Or.inr inferInstance)

private lemma hb7fi_integral_const_Ioc (A c : ℝ) (hA : 0 ≤ A) :
    (∫ b in (0)..A, c) = A * c := by
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]

private lemma hb7fi_setIntegral_const_Ioc (A c : ℝ) (hA : 0 ≤ A) :
    (∫ b in Set.Ioc (0:ℝ) A, c) = A * c := by
  rw [MeasureTheory.setIntegral_const]
  have h1 : Measure.real volume (Set.Ioc (0:ℝ) A) = A := by
    show (volume (Set.Ioc (0:ℝ) A)).toReal = A
    rw [Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal hA]
  rw [h1, smul_eq_mul]

private lemma hb7fi_sq_le_sq {x y : ℝ} (hx : 0 ≤ x) (h : x ≤ y) : x ^ 2 ≤ y ^ 2 := by
  nlinarith only [hx, h]

private lemma hb7fi_intervalInt_bdd {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {a b C : ℝ}
    (hab : a ≤ b)
    (hf : AEStronglyMeasurable f (volume.restrict (Set.Ioc a b)))
    (hb : ∀ x ∈ Set.Ioc a b, ‖f x‖ ≤ C) : IntervalIntegrable f volume a b := by
  have hs : (volume : Measure ℝ) (Set.Ioc a b) < ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  refine ⟨IntegrableOn.of_bound hs hf C ?_, ?_⟩
  · rw [ae_restrict_iff' measurableSet_Ioc]; exact Filter.Eventually.of_forall hb
  · rw [Set.Ioc_eq_empty_of_le hab]; exact integrableOn_empty

private lemma hb7fi_sq_integral_le {A : ℝ} (hA : 0 ≤ A) {φ : ℝ → ℝ}
    (hφ : IntervalIntegrable φ volume 0 A)
    (hφ2 : IntervalIntegrable (fun b => φ b ^ 2) volume 0 A) :
    (∫ b in (0)..A, φ b) ^ 2 ≤ A * ∫ b in (0)..A, φ b ^ 2 := by
  rcases lt_or_eq_of_le hA with hApos | hA0
  · set P : ℝ := ∫ b in (0)..A, φ b with hP
    set Q : ℝ := ∫ b in (0)..A, φ b ^ 2 with hQ
    set c : ℝ := P / A with hc
    have hψeq : (fun b => (φ b - c) ^ 2) = fun b => φ b ^ 2 - (2*c) * φ b + c^2 := by
      funext b; ring
    have hnn : 0 ≤ ∫ b in (0)..A, (φ b - c) ^ 2 :=
      intervalIntegral.integral_nonneg hApos.le (fun b _ => sq_nonneg _)
    rw [hψeq, intervalIntegral.integral_add (hφ2.sub (hφ.const_mul _)) intervalIntegrable_const,
        intervalIntegral.integral_sub hφ2 (hφ.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hnn
    simp only [smul_eq_mul, sub_zero] at hnn
    rw [← hP, ← hQ, hc] at hnn
    have key : P ^ 2 ≤ A * Q := by
      have h1 : Q - 2 * (P / A) * P + (P / A) ^ 2 * A = Q - P^2 / A := by
        field_simp; ring
      have h2 : P ^ 2 / A ≤ Q := by linarith only [hnn, h1]
      have h3 := (div_le_iff₀ hApos).mp h2
      linarith only [h3, mul_comm Q A]
    exact key
  · rw [← hA0, intervalIntegral.integral_same, intervalIntegral.integral_same]
    simp

private lemma hb7fi_cont_cpow_exp (c : ℂ) {t : ℝ} (ht : t ≠ 0) :
    Continuous (fun b : ℝ => (t : ℂ) ^ ((b : ℂ) + c)) := by
  rw [continuous_iff_continuousAt]
  intro b
  exact (continuousAt_const_cpow (Complex.ofReal_ne_zero.mpr ht)).comp
    (by fun_prop : ContinuousAt (fun b : ℝ => (b : ℂ) + c) b)

private theorem hb7fi_swap {ι : Type*} [Fintype ι] {η A M : ℝ} (hη : 0 ≤ η) (hA : 0 ≤ A)
    (a γ : ι → ℝ) (ζ : ι → ℂ)
    (hM : ∀ b ∈ Set.Icc (0:ℝ) A,
      (∫ t in Real.exp (-η)..1,
          ‖∑ i, (if b ≤ a i then ζ i else 0) * (t : ℂ) ^ ((b : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / t) ≤ M) :
    IntervalIntegrable (fun t => (Real.log t) ^ 2 / t *
          ‖∫ b in (0)..A,
              ∑ i, (if b ≤ a i then ζ i else 0) * (t : ℂ) ^ ((b : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2)
        volume (Real.exp (-η)) 1
    ∧ (∫ t in Real.exp (-η)..1, (Real.log t) ^ 2 / t *
          ‖∫ b in (0)..A,
              ∑ i, (if b ≤ a i then ζ i else 0) * (t : ℂ) ^ ((b : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2)
        ≤ η ^ 2 * A ^ 2 * M := by
  set H : ℝ → ℝ → ℂ := fun b t => ∑ i, (if b ≤ a i then ζ i else 0) *
      (t : ℂ) ^ ((b : ℂ) - (γ i : ℂ) * Complex.I) with hH
  set F : ℝ → ℝ → ℝ := fun t b => (Real.log t) ^ 2 / t * ‖H b t‖ ^ 2 with hF
  have hM' : ∀ b ∈ Set.Icc (0:ℝ) A, (∫ t in Real.exp (-η)..1, ‖H b t‖ ^ 2 / t) ≤ M := hM
  have hle1 : Real.exp (-η) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hη])
  have hpm : MeasurableSet (Set.uIoc (Real.exp (-η)) 1 ×ˢ Set.uIoc 0 A) :=
    measurableSet_uIoc.prod measurableSet_uIoc
  have hcpow (i : ι) : ContinuousOn
      (fun p : ℝ × ℝ => (p.1 : ℂ) ^ ((p.2 : ℂ) - (γ i : ℂ) * Complex.I))
      (Set.uIoc (Real.exp (-η)) 1 ×ˢ Set.uIoc 0 A) := by
    apply ContinuousOn.cpow
    · exact (Complex.continuous_ofReal.comp continuous_fst).continuousOn
    · exact ((Complex.continuous_ofReal.comp continuous_snd).sub continuous_const).continuousOn
    · intro p hp
      rw [Set.mem_prod] at hp
      have hp1 : Real.exp (-η) < p.1 := by
        rw [Set.uIoc_of_le hle1] at hp; exact hp.1.1
      exact Complex.ofReal_mem_slitPlane.mpr (lt_trans (Real.exp_pos _) hp1)
  have hHjoint : AEStronglyMeasurable (fun p : ℝ × ℝ => H p.2 p.1)
      (volume.restrict (Set.uIoc (Real.exp (-η)) 1 ×ˢ Set.uIoc 0 A)) := by
    have heq : (fun p : ℝ × ℝ => H p.2 p.1)
        = fun p : ℝ × ℝ => ∑ i, (if p.2 ≤ a i then ζ i else 0) *
            (p.1 : ℂ) ^ ((p.2 : ℂ) - (γ i : ℂ) * Complex.I) := by
      funext p; simp only [hH]
    rw [heq]
    have hfin := Finset.aestronglyMeasurable_sum
      (μ := volume.restrict (Set.uIoc (Real.exp (-η)) 1 ×ˢ Set.uIoc 0 A)) (s := Finset.univ)
      (f := fun i (p : ℝ × ℝ) => (if p.2 ≤ a i then ζ i else 0) *
        (p.1 : ℂ) ^ ((p.2 : ℂ) - (γ i : ℂ) * Complex.I)) (fun i _ => ?_)
    · have heq2 : (∑ i, (fun p : ℝ × ℝ => (if p.2 ≤ a i then ζ i else 0) *
          (p.1 : ℂ) ^ ((p.2 : ℂ) - (γ i : ℂ) * Complex.I)))
          = fun p : ℝ × ℝ => ∑ i, (if p.2 ≤ a i then ζ i else 0) *
              (p.1 : ℂ) ^ ((p.2 : ℂ) - (γ i : ℂ) * Complex.I) := by
        funext p; rw [Finset.sum_apply]
      rwa [heq2] at hfin
    refine (Measurable.ite ?_ measurable_const measurable_const).aestronglyMeasurable.mul ?_
    · exact measurableSet_le measurable_snd measurable_const
    · exact (hcpow i).aestronglyMeasurable hpm
  have hFjoint : AEStronglyMeasurable (Function.uncurry F)
      (volume.restrict (Set.uIoc (Real.exp (-η)) 1 ×ˢ Set.uIoc 0 A)) := by
    have hfac : Measurable (fun p : ℝ × ℝ => (Real.log p.1) ^ 2 / p.1) :=
      (Measurable.pow (Real.measurable_log.comp measurable_fst)
        (measurable_const : Measurable fun _ : ℝ × ℝ => (2:ℕ))).div measurable_fst
    exact hfac.aestronglyMeasurable.mul (hHjoint.norm.pow 2)
  have hS0 : (0:ℝ) ≤ ∑ i, ‖ζ i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hHbd : ∀ p : ℝ × ℝ, 0 < p.1 → p.1 ≤ 1 → 0 ≤ p.2 → ‖H p.2 p.1‖ ≤ ∑ i, ‖ζ i‖ := by
    intro p hp1pos hp1le hp2ge
    simp only [hH]
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul]
    have h1 : ‖(p.1 : ℂ) ^ ((p.2 : ℂ) - (γ i : ℂ) * Complex.I)‖ ≤ 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hp1pos]
      have hre : ((p.2 : ℂ) - (γ i : ℂ) * Complex.I).re = p.2 := by
        simp [Complex.sub_re, Complex.mul_re]
      rw [hre]
      exact Real.rpow_le_one hp1pos.le hp1le hp2ge
    calc ‖(if p.2 ≤ a i then ζ i else 0)‖ * ‖(p.1 : ℂ) ^ ((p.2 : ℂ) - (γ i : ℂ) * Complex.I)‖
          ≤ ‖(if p.2 ≤ a i then ζ i else 0)‖ * 1 := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ ≤ ‖ζ i‖ := by by_cases h : p.2 ≤ a i <;> simp [h]
  have hΨbd : ∀ᵐ p ∂(volume.restrict (Set.uIoc (Real.exp (-η)) 1 ×ˢ Set.uIoc 0 A)),
      ‖Function.uncurry F p‖ ≤ η ^ 2 * Real.exp η * (∑ i, ‖ζ i‖) ^ 2 := by
    rw [ae_restrict_iff' hpm]
    refine Filter.Eventually.of_forall (fun p hp => ?_)
    rw [Set.mem_prod, Set.uIoc_of_le hle1, Set.uIoc_of_le hA] at hp
    have hp1pos : 0 < p.1 := lt_trans (Real.exp_pos _) hp.1.1
    have hp1le : p.1 ≤ 1 := hp.1.2
    have hp2ge : 0 ≤ p.2 := hp.2.1.le
    have hlog : (Real.log p.1) ^ 2 ≤ η ^ 2 := by
      have h1 : -η ≤ Real.log p.1 := by
        have := Real.log_le_log (Real.exp_pos (-η)) hp.1.1.le
        rwa [Real.log_exp] at this
      have h2 : Real.log p.1 ≤ 0 := Real.log_nonpos hp1pos.le hp1le
      nlinarith only [h1, h2, hη]
    have hinv : p.1⁻¹ ≤ Real.exp η := by
      rw [inv_le_comm₀ hp1pos (Real.exp_pos η), ← Real.exp_neg]
      exact hp.1.1.le
    have hq : (Real.log p.1) ^ 2 / p.1 ≤ η ^ 2 * Real.exp η := by
      rw [div_eq_mul_inv]
      exact mul_le_mul hlog hinv (by positivity) (sq_nonneg η)
    have hH2 : ‖H p.2 p.1‖ ^ 2 ≤ (∑ i, ‖ζ i‖) ^ 2 := by
      nlinarith only [hHbd p hp1pos hp1le hp2ge, norm_nonneg (H p.2 p.1), hS0, hHbd, hp1pos, hp1le, hp2ge]
    have huncur : ‖Function.uncurry F p‖
        = (Real.log p.1) ^ 2 / p.1 * ‖H p.2 p.1‖ ^ 2 := by
      have hnn : 0 ≤ Function.uncurry F p := by
        simp only [Function.uncurry, hF]; positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      simp only [Function.uncurry, hF]
    rw [huncur]
    calc (Real.log p.1) ^ 2 / p.1 * ‖H p.2 p.1‖ ^ 2
          ≤ (η ^ 2 * Real.exp η) * (∑ i, ‖ζ i‖) ^ 2 :=
            mul_le_mul hq hH2 (by positivity) (by positivity)
      _ = η ^ 2 * Real.exp η * (∑ i, ‖ζ i‖) ^ 2 := by ring
  have hvol : (volume : Measure (ℝ × ℝ))
      (Set.uIoc (Real.exp (-η)) 1 ×ˢ Set.uIoc 0 A) < ⊤ := by
    change (volume.prod volume : Measure (ℝ × ℝ))
      (Set.uIoc (Real.exp (-η)) 1 ×ˢ Set.uIoc 0 A) < ⊤
    rw [Measure.prod_prod, Set.uIoc_of_le hle1, Set.uIoc_of_le hA,
        Real.volume_Ioc, Real.volume_Ioc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hFint : IntegrableOn (Function.uncurry F)
      (Set.uIoc (Real.exp (-η)) 1 ×ˢ Set.uIoc 0 A) volume :=
    IntegrableOn.of_bound hvol hFjoint _ hΨbd
  have hFub := intervalIntegral_intervalIntegral_swap (F := F) hFint
  have hprodH : AEStronglyMeasurable (fun p : ℝ × ℝ => H p.2 p.1)
      ((volume.restrict (Set.Ioc (Real.exp (-η)) 1)).prod (volume.restrict (Set.Ioc 0 A))) := by
    rw [Set.uIoc_of_le hle1, Set.uIoc_of_le hA] at hHjoint
    change AEStronglyMeasurable (fun p : ℝ × ℝ => H p.2 p.1)
      ((volume.prod volume).restrict (Set.Ioc (Real.exp (-η)) 1 ×ˢ Set.Ioc 0 A)) at hHjoint
    rwa [← Measure.prod_restrict] at hHjoint
  have hprodF : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Set.Ioc (Real.exp (-η)) 1)).prod (volume.restrict (Set.Ioc 0 A))) := by
    rw [Set.uIoc_of_le hle1, Set.uIoc_of_le hA] at hFjoint
    change AEStronglyMeasurable (Function.uncurry F)
      ((volume.prod volume).restrict (Set.Ioc (Real.exp (-η)) 1 ×ˢ Set.Ioc 0 A)) at hFjoint
    rwa [← Measure.prod_restrict] at hFjoint
  have hHmarg : AEStronglyMeasurable (fun t : ℝ => ∫ b in (0)..A, H b t)
      (volume.restrict (Set.Ioc (Real.exp (-η)) 1)) := by
    have h := hprodH.integral_prod_right'
    rw [show (fun t : ℝ => ∫ b in (0)..A, H b t)
        = fun t : ℝ => ∫ b, H b t ∂(volume.restrict (Set.Ioc 0 A)) from
      funext fun t => intervalIntegral.integral_of_le hA]
    exact h
  have hFmarg : AEStronglyMeasurable (fun t : ℝ => ∫ b in (0)..A, F t b)
      (volume.restrict (Set.Ioc (Real.exp (-η)) 1)) := by
    have h := hprodF.integral_prod_right'
    rw [show (fun t : ℝ => ∫ b in (0)..A, F t b)
        = fun t : ℝ => ∫ b, F t b ∂(volume.restrict (Set.Ioc 0 A)) from
      funext fun t => intervalIntegral.integral_of_le hA]
    exact h
  have hlogcont : ContinuousOn (fun t : ℝ => (Real.log t) ^ 2 / t) (Set.uIcc (Real.exp (-η)) 1) := by
    have h1 : ContinuousOn (fun t : ℝ => Real.log t) (Set.uIcc (Real.exp (-η)) 1) := by
      intro x hx
      rw [Set.uIcc_of_le hle1] at hx
      exact (Real.continuousAt_log (ne_of_gt (lt_of_lt_of_le (Real.exp_pos _) hx.1))).continuousWithinAt
    refine (h1.pow 2).div continuousOn_id ?_
    intro t ht
    rw [Set.uIcc_of_le hle1] at ht
    exact ne_of_gt (lt_of_lt_of_le (Real.exp_pos _) ht.1)
  have hHcont (b : ℝ) : ContinuousOn (fun t : ℝ => H b t) (Set.uIcc (Real.exp (-η)) 1) := by
    simp only [hH]
    refine continuousOn_finsetSum Finset.univ (fun i _ => ?_)
    exact (hb7fi_cont_cpow (w := (b : ℂ) - (γ i : ℂ) * Complex.I) hη).const_mul _
  have hQcont (b : ℝ) : ContinuousOn (fun t : ℝ => ‖H b t‖ ^ 2 / t) (Set.uIcc (Real.exp (-η)) 1) :=
    ((hHcont b).norm.pow 2).div continuousOn_id (fun t ht => by
      rw [Set.uIcc_of_le hle1] at ht
      exact ne_of_gt (lt_of_lt_of_le (Real.exp_pos _) ht.1))
  have hFcont (b : ℝ) : ContinuousOn (fun t : ℝ => F t b) (Set.uIcc (Real.exp (-η)) 1) := by
    have h := hlogcont.mul ((hHcont b).norm.pow 2)
    have heq : ((fun t : ℝ => Real.log t ^ 2 / t) * (fun x : ℝ => ‖H b x‖) ^ 2)
        = (fun t : ℝ => F t b) := by
      funext t; simp only [Pi.mul_apply, Pi.pow_apply, hF]
    rwa [heq] at h
  have hHble : ∀ b : ℝ, 0 ≤ b → ∀ t : ℝ, 0 < t → t ≤ 1 → ‖H b t‖ ≤ ∑ i, ‖ζ i‖ :=
    fun b hb t ht0 ht1 => hHbd (t, b) ht0 ht1 hb
  have hCS : ∀ t ∈ Set.Icc (Real.exp (-η)) 1,
      ‖∫ b in (0)..A, H b t‖ ^ 2 ≤ A * ∫ b in (0)..A, ‖H b t‖ ^ 2 := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos _) ht.1
    have ht1 : t ≤ 1 := ht.2
    have hm : AEStronglyMeasurable (fun b : ℝ => H b t) (volume.restrict (Set.Ioc 0 A)) := by
      simp only [hH]
      have hfin := Finset.aestronglyMeasurable_sum
        (μ := volume.restrict (Set.Ioc 0 A)) (s := Finset.univ)
        (f := fun i (b : ℝ) => (if b ≤ a i then ζ i else 0) *
          (t : ℂ) ^ ((b : ℂ) - (γ i : ℂ) * Complex.I)) (fun i _ => ?_)
      · have heq2 : (∑ i, (fun b : ℝ => (if b ≤ a i then ζ i else 0) *
            (t : ℂ) ^ ((b : ℂ) - (γ i : ℂ) * Complex.I)))
            = fun b : ℝ => ∑ i, (if b ≤ a i then ζ i else 0) *
                (t : ℂ) ^ ((b : ℂ) - (γ i : ℂ) * Complex.I) := by
          funext b; rw [Finset.sum_apply]
        rwa [heq2] at hfin
      · refine (Measurable.ite ?_ measurable_const measurable_const).aestronglyMeasurable.mul ?_
        · exact measurableSet_le measurable_id measurable_const
        · exact (hb7fi_cont_cpow_exp (-((γ i : ℂ) * Complex.I)) ht0.ne').aestronglyMeasurable.restrict
    have hφ : IntervalIntegrable (fun b : ℝ => ‖H b t‖) volume 0 A :=
      hb7fi_intervalInt_bdd hA hm.norm (fun b hb => by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact hHble b hb.1.le t ht0 ht1)
    have hφ2 : IntervalIntegrable (fun b : ℝ => ‖H b t‖ ^ 2) volume 0 A :=
      hb7fi_intervalInt_bdd hA (hm.norm.pow 2) (fun b hb => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact hb7fi_sq_le_sq (norm_nonneg _) (hHble b hb.1.le t ht0 ht1))
    have hnorm := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
      (f := fun b => H b t) hA
    exact (hb7fi_sq_le_sq (norm_nonneg _) hnorm).trans (hb7fi_sq_integral_le hA hφ hφ2)
  have hΦle : ∀ t ∈ Set.Icc (Real.exp (-η)) 1,
      (Real.log t) ^ 2 / t * ‖∫ b in (0)..A, H b t‖ ^ 2 ≤ A * ∫ b in (0)..A, F t b := by
    intro t ht
    have h2 : (∫ b in (0)..A, F t b) = (Real.log t) ^ 2 / t * ∫ b in (0)..A, ‖H b t‖ ^ 2 := by
      simp only [hF]; exact intervalIntegral.integral_const_mul _ _
    rw [h2]
    have hnn : 0 ≤ (Real.log t) ^ 2 / t := by
      have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos _) ht.1
      positivity
    calc (Real.log t) ^ 2 / t * ‖∫ b in (0)..A, H b t‖ ^ 2
        ≤ (Real.log t) ^ 2 / t * (A * ∫ b in (0)..A, ‖H b t‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hCS t ht) hnn
      _ = A * ((Real.log t) ^ 2 / t * ∫ b in (0)..A, ‖H b t‖ ^ 2) := by ring
  have hlogmeas : AEStronglyMeasurable (fun t : ℝ => (Real.log t) ^ 2 / t)
      (volume.restrict (Set.Ioc (Real.exp (-η)) 1)) :=
    (Measurable.div (Measurable.pow Real.measurable_log
      (measurable_const : Measurable fun _ : ℝ => (2:ℕ))) measurable_id).aestronglyMeasurable
  have hφb : ∀ t : ℝ, 0 < t → t ≤ 1 →
      IntervalIntegrable (fun b : ℝ => ‖H b t‖) volume 0 A := by
    intro t ht0 ht1
    have hm : AEStronglyMeasurable (fun b : ℝ => H b t) (volume.restrict (Set.Ioc 0 A)) := by
      simp only [hH]
      have hfin := Finset.aestronglyMeasurable_sum
        (μ := volume.restrict (Set.Ioc 0 A)) (s := Finset.univ)
        (f := fun i (b : ℝ) => (if b ≤ a i then ζ i else 0) *
          (t : ℂ) ^ ((b : ℂ) - (γ i : ℂ) * Complex.I)) (fun i _ => ?_)
      · have heq2 : (∑ i, (fun b : ℝ => (if b ≤ a i then ζ i else 0) *
            (t : ℂ) ^ ((b : ℂ) - (γ i : ℂ) * Complex.I)))
            = fun b : ℝ => ∑ i, (if b ≤ a i then ζ i else 0) *
                (t : ℂ) ^ ((b : ℂ) - (γ i : ℂ) * Complex.I) := by
          funext b; rw [Finset.sum_apply]
        rwa [heq2] at hfin
      · refine (Measurable.ite ?_ measurable_const measurable_const).aestronglyMeasurable.mul ?_
        · exact measurableSet_le measurable_id measurable_const
        · exact (hb7fi_cont_cpow_exp (-((γ i : ℂ) * Complex.I)) ht0.ne').aestronglyMeasurable.restrict
    exact hb7fi_intervalInt_bdd hA hm.norm (fun b hb => by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact hHble b hb.1.le t ht0 ht1)
  have hΦ_int : IntervalIntegrable
      (fun t : ℝ => (Real.log t) ^ 2 / t * ‖∫ b in (0)..A, H b t‖ ^ 2)
      volume (Real.exp (-η)) 1 := by
    have hbdd : ∀ t ∈ Set.Ioc (Real.exp (-η)) 1,
        ‖(fun t : ℝ => (Real.log t) ^ 2 / t * ‖∫ b in (0)..A, H b t‖ ^ 2) t‖
          ≤ η ^ 2 * Real.exp η * (A * ∑ i, ‖ζ i‖) ^ 2 := by
      intro t ht
      have ht0 : 0 < t := lt_trans (Real.exp_pos _) ht.1
      have hnn : 0 ≤ (Real.log t) ^ 2 / t * ‖∫ b in (0)..A, H b t‖ ^ 2 := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      have ht1 : t ≤ 1 := ht.2
      have hlog : (Real.log t) ^ 2 ≤ η ^ 2 := by
        have h1 : -η ≤ Real.log t := by
          have := Real.log_le_log (Real.exp_pos (-η)) ht.1.le
          rwa [Real.log_exp] at this
        have h2 : Real.log t ≤ 0 := Real.log_nonpos ht0.le ht1
        nlinarith only [h1, h2, hη]
      have hinv : t⁻¹ ≤ Real.exp η := by
        rw [inv_le_comm₀ ht0 (Real.exp_pos η), ← Real.exp_neg]
        exact ht.1.le
      have hq : (Real.log t) ^ 2 / t ≤ η ^ 2 * Real.exp η := by
        rw [div_eq_mul_inv]
        exact mul_le_mul hlog hinv (by positivity) (sq_nonneg η)
      have hInt : ‖∫ b in (0)..A, H b t‖ ≤ A * ∑ i, ‖ζ i‖ := by
        calc ‖∫ b in (0)..A, H b t‖ ≤ ∫ b in (0)..A, ‖H b t‖ :=
              intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := fun b => H b t) hA
          _ ≤ ∫ b in (0)..A, (∑ i, ‖ζ i‖) :=
              intervalIntegral.integral_mono_on hA (hφb t ht0 ht1) intervalIntegrable_const
                (fun b hb => hHble b hb.1 t ht0 ht1)
          _ = A * ∑ i, ‖ζ i‖ := hb7fi_integral_const_Ioc A _ hA
      calc (Real.log t) ^ 2 / t * ‖∫ b in (0)..A, H b t‖ ^ 2
          ≤ (η ^ 2 * Real.exp η) * (A * ∑ i, ‖ζ i‖) ^ 2 :=
            mul_le_mul hq (hb7fi_sq_le_sq (norm_nonneg _) hInt) (by positivity) (by positivity)
        _ = η ^ 2 * Real.exp η * (A * ∑ i, ‖ζ i‖) ^ 2 := by ring
    exact hb7fi_intervalInt_bdd hle1 (hlogmeas.mul (hHmarg.norm.pow 2)) hbdd
  have hCb : ∀ t ∈ Set.Ioc (Real.exp (-η)) 1,
      (∫ b in (0)..A, F t b) ≤ A * (η ^ 2 * Real.exp η * (∑ i, ‖ζ i‖) ^ 2) := by
    intro t ht
    have ht0 : 0 < t := lt_trans (Real.exp_pos _) ht.1
    have ht1 : t ≤ 1 := ht.2
    have h1 : (∫ b in Set.Ioc (0:ℝ) A, F t b)
        ≤ ∫ b in Set.Ioc (0:ℝ) A, (η ^ 2 * Real.exp η * (∑ i, ‖ζ i‖) ^ 2) := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ (hb7fi_integrable_const_Ioc A _) ?_
      · filter_upwards with b; simp only [hF]; positivity
      · show ∀ᵐ b ∂(volume.restrict (Set.Ioc (0:ℝ) A)),
            F t b ≤ η ^ 2 * Real.exp η * (∑ i, ‖ζ i‖) ^ 2
        rw [ae_restrict_iff' measurableSet_Ioc]
        refine Filter.Eventually.of_forall (fun b hb => ?_)
        have hlog : (Real.log t) ^ 2 ≤ η ^ 2 := by
          have h1 : -η ≤ Real.log t := by
            have := Real.log_le_log (Real.exp_pos (-η)) ht.1.le
            rwa [Real.log_exp] at this
          have h2 : Real.log t ≤ 0 := Real.log_nonpos ht0.le ht1
          nlinarith only [h1, h2, hη]
        have hinv : t⁻¹ ≤ Real.exp η := by
          rw [inv_le_comm₀ ht0 (Real.exp_pos η), ← Real.exp_neg]
          exact ht.1.le
        have hq : (Real.log t) ^ 2 / t ≤ η ^ 2 * Real.exp η := by
          rw [div_eq_mul_inv]
          exact mul_le_mul hlog hinv (by positivity) (sq_nonneg η)
        have hH2 : ‖H b t‖ ^ 2 ≤ (∑ i, ‖ζ i‖) ^ 2 :=
          hb7fi_sq_le_sq (norm_nonneg _) (hHble b hb.1.le t ht0 ht1)
        simp only [hF]
        calc (Real.log t) ^ 2 / t * ‖H b t‖ ^ 2
            ≤ (η ^ 2 * Real.exp η) * (∑ i, ‖ζ i‖) ^ 2 :=
              mul_le_mul hq hH2 (by positivity) (by positivity)
          _ = η ^ 2 * Real.exp η * (∑ i, ‖ζ i‖) ^ 2 := by ring
    calc (∫ b in (0)..A, F t b) = ∫ b in Set.Ioc (0:ℝ) A, F t b :=
          intervalIntegral.integral_of_le hA
      _ ≤ ∫ b in Set.Ioc (0:ℝ) A, (η ^ 2 * Real.exp η * (∑ i, ‖ζ i‖) ^ 2) := h1
      _ = A * (η ^ 2 * Real.exp η * (∑ i, ‖ζ i‖) ^ 2) :=
          hb7fi_setIntegral_const_Ioc A _ hA
  have hg_int : IntervalIntegrable (fun t : ℝ => A * ∫ b in (0)..A, F t b)
      volume (Real.exp (-η)) 1 := by
    have hbdd : ∀ t ∈ Set.Ioc (Real.exp (-η)) 1,
        ‖(fun t : ℝ => A * ∫ b in (0)..A, F t b) t‖
          ≤ A * (A * (η ^ 2 * Real.exp η * (∑ i, ‖ζ i‖) ^ 2)) := by
      intro t ht
      have ht0 : 0 < t := lt_trans (Real.exp_pos _) ht.1
      have h1 := hCb t ht
      have h2 : (0:ℝ) ≤ ∫ b in (0)..A, F t b :=
        intervalIntegral.integral_nonneg hA (fun b hb => by
          simp only [hF]
          exact mul_nonneg (div_nonneg (sq_nonneg _) ht0.le) (sq_nonneg _))
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hA h2)]
      exact mul_le_mul_of_nonneg_left h1 hA
    exact hb7fi_intervalInt_bdd hle1 (hFmarg.const_mul A) hbdd
  have hFub_le : (∫ b in (0)..A, ∫ t in Real.exp (-η)..1, F t b) ≤ A * (η ^ 2 * M) := by
    have hinner_b : ∀ b ∈ Set.Ioc (0:ℝ) A, (∫ t in Real.exp (-η)..1, F t b) ≤ η ^ 2 * M := by
      intro b hb
      have h2 : (∫ t in Real.exp (-η)..1, F t b)
          ≤ ∫ t in Real.exp (-η)..1, η ^ 2 * (‖H b t‖ ^ 2 / t) := by
        refine intervalIntegral.integral_mono_on hle1 (hFcont b).intervalIntegrable
          ((hQcont b).const_mul (η ^ 2)).intervalIntegrable (fun t ht => ?_)
        have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos _) ht.1
        have hlog : (Real.log t) ^ 2 ≤ η ^ 2 := by
          have h1 : -η ≤ Real.log t := by
            have := Real.log_le_log (Real.exp_pos (-η)) ht.1
            rwa [Real.log_exp] at this
          have h2 : Real.log t ≤ 0 := Real.log_nonpos ht0.le ht.2
          nlinarith only [h1, h2, hη]
        have hnn : 0 ≤ ‖H b t‖ ^ 2 / t := by positivity
        simp only [hF]
        calc (Real.log t) ^ 2 / t * ‖H b t‖ ^ 2
            = (Real.log t) ^ 2 * (‖H b t‖ ^ 2 / t) := by
              rw [div_mul_eq_mul_div, mul_div_assoc]
          _ ≤ η ^ 2 * (‖H b t‖ ^ 2 / t) := mul_le_mul_of_nonneg_right hlog hnn
      rw [intervalIntegral.integral_const_mul] at h2
      exact h2.trans (mul_le_mul_of_nonneg_left (hM' b ⟨hb.1.le, hb.2⟩) (sq_nonneg η))
    have h1 : (∫ b in Set.Ioc (0:ℝ) A, ∫ t in Real.exp (-η)..1, F t b)
        ≤ ∫ b in Set.Ioc (0:ℝ) A, (η ^ 2 * M) := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ (hb7fi_integrable_const_Ioc A _) ?_
      · filter_upwards with b
        refine intervalIntegral.integral_nonneg hle1 (fun t ht => ?_)
        simp only [hF]
        exact mul_nonneg (div_nonneg (sq_nonneg _)
          (le_of_lt (lt_of_lt_of_le (Real.exp_pos _) ht.1))) (sq_nonneg _)
      · show ∀ᵐ b ∂(volume.restrict (Set.Ioc (0:ℝ) A)),
            (∫ t in Real.exp (-η)..1, F t b) ≤ η ^ 2 * M
        rw [ae_restrict_iff' measurableSet_Ioc]
        exact Filter.Eventually.of_forall (fun b hb => hinner_b b hb)
    calc (∫ b in (0)..A, ∫ t in Real.exp (-η)..1, F t b)
        = ∫ b in Set.Ioc (0:ℝ) A, ∫ t in Real.exp (-η)..1, F t b :=
          intervalIntegral.integral_of_le hA
      _ ≤ ∫ b in Set.Ioc (0:ℝ) A, (η ^ 2 * M) := h1
      _ = A * (η ^ 2 * M) := hb7fi_setIntegral_const_Ioc A _ hA
  have hΦ_le : (∫ t in Real.exp (-η)..1, (Real.log t) ^ 2 / t * ‖∫ b in (0)..A, H b t‖ ^ 2)
      ≤ A * ∫ t in Real.exp (-η)..1, ∫ b in (0)..A, F t b := by
    have h1 := intervalIntegral.integral_mono_on hle1 hΦ_int hg_int (fun t ht => hΦle t ht)
    rwa [intervalIntegral.integral_const_mul] at h1
  constructor
  · exact hΦ_int
  · calc (∫ t in Real.exp (-η)..1, (Real.log t) ^ 2 / t * ‖∫ b in (0)..A, H b t‖ ^ 2)
        ≤ A * ∫ t in Real.exp (-η)..1, ∫ b in (0)..A, F t b := hΦ_le
      _ = A * ∫ b in (0)..A, ∫ t in Real.exp (-η)..1, F t b := by rw [hFub]
      _ ≤ A * (A * (η ^ 2 * M)) := mul_le_mul_of_nonneg_left hFub_le hA
      _ = η ^ 2 * A ^ 2 * M := by ring

theorem HB7FreezeInterval {C : ℝ} (hMVT : Work.ZeroDensity.LogFree.MvtMul C)
    {ι : Type*} [Fintype ι] {δ η A : ℝ} (hδ : 0 < δ) (hη : 0 ≤ η) (hA : 0 ≤ A)
    (hηA : η * A ≤ 1)
    (a : ι → ℝ) (ha0 : ∀ i, 0 ≤ a i) (haA : ∀ i, a i ≤ A)
    (γ : ι → ℝ) (hsep : ∀ i j, i ≠ j → δ ≤ |γ i - γ j|) (ζ : ι → ℂ) :
    (∫ t in Real.exp (-η)..1,
        ‖∑ i, ζ i * (t : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / t)
      ≤ 16 * (η + C / δ) * ∑ i, ‖ζ i‖ ^ 2 := by
  have hle1 : Real.exp (-η) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hη])
  have hC : 0 ≤ C := by
    have h := hMVT 1 one_pos 1 (fun _ => (0:ℝ)) (fun _ => (1:ℂ)) 1 1 (by norm_num) le_rfl
      (by intro i j hij; exact absurd (Subsingleton.elim i j) hij)
    rw [intervalIntegral.integral_same] at h
    simp only [Fin.sum_univ_one, norm_one] at h
    have h1 : (1:ℝ)/1 = 1 := by norm_num
    rw [h1, Real.log_one, zero_add, div_one, one_pow, mul_one] at h
    exact h
  have hS : (0:ℝ) ≤ ∑ i, ‖ζ i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  set H : ℝ → ℝ → ℂ := fun b t => ∑ i, (if b ≤ a i then ζ i else 0) *
      (t : ℂ) ^ ((b : ℂ) - (γ i : ℂ) * Complex.I) with hH
  set Ff : ℝ → ℂ := fun t => ∑ i, ζ i * (t : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I) with hFf
  set Gg : ℝ → ℂ := fun t => ∑ i, ζ i * (t : ℂ) ^ ((-(γ i : ℂ)) * Complex.I) with hGg
  have hMlevel : ∀ b ∈ Set.Icc (0:ℝ) A,
      (∫ t in Real.exp (-η)..1, ‖H b t‖ ^ 2 / t) ≤ (η + C / δ) * ∑ i, ‖ζ i‖ ^ 2 := by
    intro b hb
    exact hb7fi_level hC hMVT hδ hη a γ ζ hsep hb.1
  obtain ⟨hEint, hEbound⟩ := hb7fi_swap hη hA a γ ζ hMlevel
  have hGmv : (∫ t in Real.exp (-η)..1, ‖Gg t‖ ^ 2 / t) ≤ (η + C / δ) * ∑ i, ‖ζ i‖ ^ 2 := by
    have h := HB7MvtAny hMVT δ hδ γ ζ (Real.exp (-η)) 1 (Real.exp_pos _) hle1 hsep
    have hlog : Real.log (1 / Real.exp (-η)) = η := by
      rw [one_div, Real.log_inv, Real.log_exp]; ring
    rw [hlog] at h
    simpa only [hGg] using h
  have hFcont : ContinuousOn (fun t : ℝ => Ff t) (Set.uIcc (Real.exp (-η)) 1) := by
    simp only [hFf]
    exact continuousOn_finsetSum Finset.univ (fun i _ =>
      (hb7fi_cont_cpow (w := (a i : ℂ) - (γ i : ℂ) * Complex.I) hη).const_mul _)
  have hGcont : ContinuousOn (fun t : ℝ => Gg t) (Set.uIcc (Real.exp (-η)) 1) := by
    simp only [hGg]
    exact continuousOn_finsetSum Finset.univ (fun i _ =>
      (hb7fi_cont_cpow (w := (-(γ i : ℂ)) * Complex.I) hη).const_mul _)
  have hne : ∀ t ∈ Set.uIcc (Real.exp (-η)) 1, t ≠ 0 := by
    intro t ht
    rw [Set.uIcc_of_le hle1] at ht
    exact ne_of_gt (lt_of_lt_of_le (Real.exp_pos _) ht.1)
  have hFint : IntervalIntegrable (fun t : ℝ => ‖Ff t‖ ^ 2 / t) volume (Real.exp (-η)) 1 :=
    ((hFcont.norm.pow 2).div continuousOn_id hne).intervalIntegrable
  have hGint : IntervalIntegrable (fun t : ℝ => ‖Gg t‖ ^ 2 / t) volume (Real.exp (-η)) 1 :=
    ((hGcont.norm.pow 2).div continuousOn_id hne).intervalIntegrable
  have hpt : ∀ t ∈ Set.Icc (Real.exp (-η)) 1,
      ‖Ff t‖ ^ 2 / t ≤ 2 * (‖Gg t‖ ^ 2 / t)
        + 2 * ((Real.log t) ^ 2 / t * ‖∫ b in (0)..A, H b t‖ ^ 2) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos _) ht.1
    have hexp : Ff t = Gg t + ((Real.log t : ℝ) : ℂ) * (∫ b in (0)..A, H b t) := by
      simp only [hFf, hGg, hH]
      exact hb7fi_expansion a γ ζ ht0 hA ha0 haA
    have h2 : ‖Gg t + ((Real.log t : ℝ) : ℂ) * (∫ b in (0)..A, H b t)‖ ^ 2
        ≤ 2 * ‖Gg t‖ ^ 2
          + 2 * ‖((Real.log t : ℝ) : ℂ) * (∫ b in (0)..A, H b t)‖ ^ 2 := by
      have h := norm_add_le (Gg t) (((Real.log t : ℝ) : ℂ) * (∫ b in (0)..A, H b t))
      have h1 := norm_nonneg (Gg t)
      have h3 := norm_nonneg (((Real.log t : ℝ) : ℂ) * (∫ b in (0)..A, H b t))
      have h4 := norm_nonneg (Gg t + (((Real.log t : ℝ) : ℂ) * (∫ b in (0)..A, H b t)))
      have h5 := hb7fi_sq_le_sq h4 h
      linarith only [h5, h1, h3, sq_nonneg (‖Gg t‖ - ‖(((Real.log t : ℝ) : ℂ) * (∫ b in (0)..A, H b t))‖)]
    have h3 : ‖((Real.log t : ℝ) : ℂ) * (∫ b in (0)..A, H b t)‖ ^ 2
        = (Real.log t) ^ 2 * ‖∫ b in (0)..A, H b t‖ ^ 2 := by
      rw [norm_mul, show ‖((Real.log t : ℝ) : ℂ)‖ = |Real.log t| from by simp, mul_pow, sq_abs]
    rw [h3] at h2
    rw [hexp, div_le_iff₀ ht0]
    have hc : (2 * (‖Gg t‖ ^ 2 / t) + 2 * ((Real.log t) ^ 2 / t * ‖∫ b in (0)..A, H b t‖ ^ 2)) * t
        = 2 * ‖Gg t‖ ^ 2 + 2 * ((Real.log t) ^ 2 * ‖∫ b in (0)..A, H b t‖ ^ 2) := by
      field_simp
    rw [hc]
    exact h2
  have hsum_int : IntervalIntegrable (fun t : ℝ => 2 * (‖Gg t‖ ^ 2 / t)
      + 2 * ((Real.log t) ^ 2 / t * ‖∫ b in (0)..A, H b t‖ ^ 2)) volume (Real.exp (-η)) 1 :=
    (hGint.const_mul 2).add (hEint.const_mul 2)
  have hmono := intervalIntegral.integral_mono_on hle1 hFint hsum_int (fun t ht => hpt t ht)
  have hsplit : (∫ t in Real.exp (-η)..1, (2 * (‖Gg t‖ ^ 2 / t)
        + 2 * ((Real.log t) ^ 2 / t * ‖∫ b in (0)..A, H b t‖ ^ 2)))
      = 2 * (∫ t in Real.exp (-η)..1, ‖Gg t‖ ^ 2 / t)
        + 2 * (∫ t in Real.exp (-η)..1, (Real.log t) ^ 2 / t * ‖∫ b in (0)..A, H b t‖ ^ 2) := by
    rw [intervalIntegral.integral_add (hGint.const_mul 2) (hEint.const_mul 2),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have h2G : 2 * (∫ t in Real.exp (-η)..1, ‖Gg t‖ ^ 2 / t) ≤ 2 * ((η + C / δ) * ∑ i, ‖ζ i‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hGmv (by norm_num)
  have h2E : 2 * (∫ t in Real.exp (-η)..1, (Real.log t) ^ 2 / t * ‖∫ b in (0)..A, H b t‖ ^ 2)
      ≤ 2 * (η ^ 2 * A ^ 2 * ((η + C / δ) * ∑ i, ‖ζ i‖ ^ 2)) :=
    mul_le_mul_of_nonneg_left hEbound (by norm_num)
  calc (∫ t in Real.exp (-η)..1, ‖∑ i, ζ i * (t : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / t)
      = ∫ t in Real.exp (-η)..1, ‖Ff t‖ ^ 2 / t := by simp only [hFf]
    _ ≤ ∫ t in Real.exp (-η)..1, (2 * (‖Gg t‖ ^ 2 / t)
          + 2 * ((Real.log t) ^ 2 / t * ‖∫ b in (0)..A, H b t‖ ^ 2)) := hmono
    _ = 2 * (∫ t in Real.exp (-η)..1, ‖Gg t‖ ^ 2 / t)
          + 2 * (∫ t in Real.exp (-η)..1, (Real.log t) ^ 2 / t * ‖∫ b in (0)..A, H b t‖ ^ 2) := hsplit
    _ ≤ 2 * ((η + C / δ) * ∑ i, ‖ζ i‖ ^ 2)
          + 2 * (η ^ 2 * A ^ 2 * ((η + C / δ) * ∑ i, ‖ζ i‖ ^ 2)) := add_le_add h2G h2E
    _ ≤ 16 * (η + C / δ) * ∑ i, ‖ζ i‖ ^ 2 := by
      have hp : 0 ≤ (η + C / δ) * ∑ i, ‖ζ i‖ ^ 2 :=
        mul_nonneg (add_nonneg hη (div_nonneg hC hδ.le)) hS
      have hsq : η ^ 2 * A ^ 2 ≤ 1 := by
        have h0 : 0 ≤ η * A := mul_nonneg hη hA
        have h1 : η * A * (η * A) ≤ 1 * 1 := mul_le_mul hηA hηA h0 (by norm_num)
        linarith only [h1]
      have hkey : 2 * ((η + C / δ) * ∑ i, ‖ζ i‖ ^ 2)
          + 2 * (η ^ 2 * A ^ 2 * ((η + C / δ) * ∑ i, ‖ζ i‖ ^ 2))
          ≤ 16 * ((η + C / δ) * ∑ i, ‖ζ i‖ ^ 2) := by
        have h2 : η ^ 2 * A ^ 2 * ((η + C / δ) * ∑ i, ‖ζ i‖ ^ 2)
            ≤ 1 * ((η + C / δ) * ∑ i, ‖ζ i‖ ^ 2) := mul_le_mul_of_nonneg_right hsq hp
        linarith only [hp, h2]
      calc 2 * ((η + C / δ) * ∑ i, ‖ζ i‖ ^ 2)
            + 2 * (η ^ 2 * A ^ 2 * ((η + C / δ) * ∑ i, ‖ζ i‖ ^ 2))
          ≤ 16 * ((η + C / δ) * ∑ i, ‖ζ i‖ ^ 2) := hkey
        _ = 16 * (η + C / δ) * ∑ i, ‖ζ i‖ ^ 2 := by ring

end Work.ZeroDensity.LogFree
