import Mathlib
import Submission.Commons.Analysis.Fourier.z_neighborhood_of_real_bandpass_uniform
import Submission.Commons.Analysis.Fourier.fourier_eq_zero_of_not_integrable

namespace Commons.Analysis.Fourier

open MeasureTheory Filter Finset
open scoped BigOperators ENNReal FourierTransform

set_option maxHeartbeats 8000000

/-! ## Periodisation (lifting) helpers  (copied to be self-contained) -/

/-- The representative of `t` modulo `1` in `Ico (-1/2) (1/2)`. -/
private noncomputable def resRep (t : ℝ) : ℝ := Int.fract (t + 1 / 2) - 1 / 2

private lemma resRep_mem (t : ℝ) : resRep t ∈ Set.Ico (-(1 / 2) : ℝ) (1 / 2) := by
  have h1 : 0 ≤ Int.fract (t + 1 / 2) := Int.fract_nonneg _
  have h2 : Int.fract (t + 1 / 2) < 1 := Int.fract_lt_one _
  simp only [resRep, Set.mem_Ico]
  constructor <;> linarith

private lemma resRep_int (t : ℝ) : ∃ n : ℤ, resRep t = t + n := by
  refine ⟨-(⌊t + 1 / 2⌋), ?_⟩
  have h := Int.fract_add_floor (t + 1 / 2)
  simp only [resRep]
  push_cast
  linarith [h]

/-- The lifted frequency set: representatives of `-(lam k)` modulo `1` together with their two
integer neighbours. -/
private noncomputable def liftedSet (N : ℕ) (lam : Fin N → ℝ) : Finset ℝ :=
  Finset.univ.biUnion fun k : Fin N =>
    (Finset.Icc (-1 : ℤ) 1).image fun m : ℤ => resRep (-(lam k)) - (m : ℝ)

private lemma mem_liftedSet {N : ℕ} {lam : Fin N → ℝ} {a : ℝ} :
    a ∈ liftedSet N lam ↔ ∃ k : Fin N, ∃ m : ℤ, m ∈ Finset.Icc (-1 : ℤ) 1 ∧
      resRep (-(lam k)) - (m : ℝ) = a := by
  simp only [liftedSet, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]

private lemma liftedSet_card_le (N : ℕ) (lam : Fin N → ℝ) : (liftedSet N lam).card ≤ 3 * N := by
  have h3 : (Finset.Icc (-1 : ℤ) 1).card = 3 := by decide
  calc (liftedSet N lam).card
      ≤ ∑ k ∈ Finset.univ, ((Finset.Icc (-1 : ℤ) 1).image
          (fun m : ℤ => resRep (-(lam k)) - (m : ℝ))).card := Finset.card_biUnion_le
    _ ≤ ∑ _k ∈ Finset.univ, 3 := Finset.sum_le_sum (fun k _ =>
          le_trans Finset.card_image_le (le_of_eq h3))
    _ = 3 * N := by simp [Finset.sum_const, Finset.card_univ, mul_comm]

private lemma int_mem_Icc_of_abs_le (z : ℤ) (h : |((z : ℤ) : ℝ)| ≤ 3 / 2) :
    z ∈ Finset.Icc (-1 : ℤ) 1 := by
  rw [Finset.mem_Icc]
  rw [abs_le] at h
  constructor
  · by_contra hc
    push Not at hc
    have h2 : ((z : ℤ) : ℝ) ≤ -2 := by exact_mod_cast (by omega : z ≤ (-2 : ℤ))
    linarith [h.1]
  · by_contra hc
    push Not at hc
    have h2 : (2 : ℝ) ≤ ((z : ℤ) : ℝ) := by exact_mod_cast (by omega : (2 : ℤ) ≤ z)
    linarith [h.2]

private lemma dyadic_pos (j : ℕ) : 0 < (2 : ℝ) ^ (-(j : ℝ) - 1) := Real.rpow_pos_of_pos (by norm_num) _

private lemma dyadic_le_half (j : ℕ) : (2 : ℝ) ^ (-(j : ℝ) - 1) ≤ 1 / 2 := by
  have h : (-(j : ℝ) - 1) ≤ (-1 : ℝ) := by
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  calc (2 : ℝ) ^ (-(j : ℝ) - 1) ≤ (2 : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) h
    _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num

/-- **The periodisation (lifting) lemma.** -/
private lemma periodic_set_eq {N : ℕ} (lam : Fin N → ℝ) {r : ℝ} (hrpos : 0 < r) (hr : r ≤ 1 / 2)
    {ξ : ℝ} (hξ : ξ ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2)) :
    (∃ k : Fin N, ∃ l : ℤ, |ξ + (l : ℝ) + lam k| ≤ r)
      ↔ (∃ a ∈ liftedSet N lam, |ξ - a| ≤ r) := by
  have hbound : ∀ k : Fin N, |ξ - resRep (-(lam k))| ≤ 1 := by
    intro k
    have h := resRep_mem (-(lam k))
    have h1 : -(1 / 2 : ℝ) ≤ resRep (-(lam k)) := h.1
    have h2 : resRep (-(lam k)) < 1 / 2 := h.2
    rw [abs_le]
    constructor <;> linarith [h1, h2, hξ.1, hξ.2]
  constructor
  · rintro ⟨k, l, hl⟩
    obtain ⟨n, hn⟩ := resRep_int (-(lam k))
    have hN : resRep (-(lam k)) + lam k = (n : ℝ) := by
      have h : resRep (-(lam k)) = -(lam k) + n := hn
      rw [h]; push_cast; ring
    have hz : |(((l + n : ℤ) : ℝ))| ≤ 3 / 2 := by
      have heq : ((l + n : ℤ) : ℝ) = (ξ + (l : ℝ) + lam k) - (ξ - resRep (-(lam k))) := by
        push_cast; linarith [hN]
      rw [heq]
      have habs : |(ξ + (l : ℝ) + lam k) - (ξ - resRep (-(lam k)))|
          ≤ |ξ + (l : ℝ) + lam k| + |ξ - resRep (-(lam k))| := by
        rw [sub_eq_add_neg]
        simpa [abs_sub_comm] using abs_add_le (ξ + (l : ℝ) + lam k) (-(ξ - resRep (-(lam k))))
      calc |(ξ + (l : ℝ) + lam k) - (ξ - resRep (-(lam k)))|
          ≤ |ξ + (l : ℝ) + lam k| + |ξ - resRep (-(lam k))| := habs
        _ ≤ r + 1 := by linarith [hl, hbound k]
        _ ≤ 3 / 2 := by linarith
    refine ⟨resRep (-(lam k)) - ((l + n : ℤ) : ℝ), ?_, ?_⟩
    · rw [mem_liftedSet]
      exact ⟨k, l + n, int_mem_Icc_of_abs_le _ hz, rfl⟩
    · have heq : ξ - (resRep (-(lam k)) - ((l + n : ℤ) : ℝ)) = ξ + (l : ℝ) + lam k := by
        push_cast; linarith [hN]
      rw [heq]; exact hl
  · rintro ⟨a, ha, ha'⟩
    rw [mem_liftedSet] at ha
    obtain ⟨k, m, hm, rfl⟩ := ha
    obtain ⟨n, hn⟩ := resRep_int (-(lam k))
    have hN : resRep (-(lam k)) + lam k = (n : ℝ) := by
      have h : resRep (-(lam k)) = -(lam k) + n := hn
      rw [h]; push_cast; ring
    refine ⟨k, m - n, ?_⟩
    have heq : ξ + ((m - n : ℤ) : ℝ) + lam k
        = ξ - (resRep (-(lam k)) - (m : ℝ)) := by
      push_cast; linarith [hN]
    rw [heq]; exact ha'

/-! ## The periodic frequency set on the torus -/

/-- The periodic `2^{-j-1}`-neighbourhood of `{lam k}` modulo `1`, with `- lam k` (the form in
which it appears in the discrete maximal function). -/
private def Rj (N : ℕ) (lam : Fin N → ℝ) (j : ℕ) : Set ℝ :=
  {θ : ℝ | ∃ k : Fin N, ∃ l : ℤ, |θ + (l : ℝ) - lam k| ≤ (2 : ℝ) ^ (-(j : ℝ) - 1)}

private lemma measurableSet_Rj (N : ℕ) (lam : Fin N → ℝ) (j : ℕ) : MeasurableSet (Rj N lam j) := by
  have hset : Rj N lam j = ⋃ k : Fin N, ⋃ l : ℤ,
      {θ : ℝ | |θ + (l:ℝ) - lam k| ≤ (2:ℝ)^(-(j:ℝ)-1)} := by
    ext θ; simp only [Rj, Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [hset]
  refine MeasurableSet.iUnion (fun k => MeasurableSet.iUnion (fun l => ?_))
  exact (isClosed_le (by fun_prop) continuous_const).measurableSet

private lemma intervalIntegrable_ind (N : ℕ) (lam : Fin N → ℝ) (j : ℕ) (a b : ℝ) (r : ℤ) (c : ℂ) :
    IntervalIntegrable (fun θ : ℝ => c * (Set.indicator (Rj N lam j) (fun _ => (1:ℂ)) θ
      * Complex.exp (-(2*Real.pi*Complex.I*((r:ℂ))*(θ:ℂ))))) volume a b := by
  have hmeas : AEStronglyMeasurable (fun θ : ℝ => c * (Set.indicator (Rj N lam j) (fun _ => (1:ℂ)) θ
      * Complex.exp (-(2*Real.pi*Complex.I*((r:ℂ))*(θ:ℂ))))) volume :=
    (measurable_const.mul ((measurable_const.indicator (measurableSet_Rj N lam j)).mul
      (Complex.continuous_exp.comp (by fun_prop)).measurable)).aestronglyMeasurable
  have hb : ∀ θ, ‖c * (Set.indicator (Rj N lam j) (fun _ => (1:ℂ)) θ
      * Complex.exp (-(2*Real.pi*Complex.I*((r:ℂ))*(θ:ℂ))))‖ ≤ ‖c‖ := by
    intro θ
    rw [norm_mul]
    have h1 : ‖Set.indicator (Rj N lam j) (fun _ => (1:ℂ)) θ
        * Complex.exp (-(2*Real.pi*Complex.I*((r:ℂ))*(θ:ℂ)))‖ ≤ 1 := by
      rw [norm_mul]
      have ha : ‖Set.indicator (Rj N lam j) (fun _ => (1:ℂ)) θ‖ ≤ 1 := by
        by_cases h : θ ∈ Rj N lam j
        · rw [Set.indicator_of_mem h]; simp
        · rw [Set.indicator_of_notMem h]; simp
      have hb2 : ‖Complex.exp (-(2*Real.pi*Complex.I*((r:ℂ))*(θ:ℂ)))‖ = 1 := by
        have hph : -(2*Real.pi*Complex.I*((r:ℂ))*(θ:ℂ))
            = (↑(-(2*Real.pi*((r:ℝ))*θ)) : ℂ) * Complex.I := by push_cast; ring
        rw [hph, Complex.norm_exp_ofReal_mul_I]
      rw [hb2, mul_one]; exact ha
    calc ‖c‖ * ‖Set.indicator (Rj N lam j) (fun _ => (1:ℂ)) θ
          * Complex.exp (-(2*Real.pi*Complex.I*((r:ℂ))*(θ:ℂ)))‖ ≤ ‖c‖ * 1 :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = ‖c‖ := mul_one _
  refine ⟨MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top hmeas.restrict ‖c‖ ?_,
          MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top hmeas.restrict ‖c‖ ?_⟩
  · filter_upwards with x using hb x
  · filter_upwards with x using hb x

/-- The Fourier-addition identity used to move the `n`-sum outside the integral. -/
private lemma exp_mul_exp (n m : ℤ) (θ : ℝ) :
    Complex.exp (2*Real.pi*Complex.I*(n:ℂ)*(θ:ℂ)) * Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ)))
      = Complex.exp (-(2*Real.pi*Complex.I*(((m-n:ℤ):ℂ))*(θ:ℂ))) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast; ring

/-- The target's inner integral equals the sum form used by the discrete transference lemma. -/
private lemma inner_eq (N : ℕ) (lam : Fin N → ℝ) (g : ℤ → ℂ) (s : Finset ℤ) (j : ℕ) (m : ℤ) :
    (∫ θ in (0:ℝ)..1, Set.indicator (Rj N lam j)
        (fun θ => ∑ n ∈ s, g n * Complex.exp (2*Real.pi*Complex.I*(n:ℂ)*(θ:ℂ))) θ
        * Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ))))
      = ∑ n ∈ s, g n * (∫ θ in Set.Icc (0:ℝ) 1,
          Set.indicator (Rj N lam j)
            (fun θ => Complex.exp (-(2*Real.pi*Complex.I*(((m-n:ℤ):ℂ))*(θ:ℂ)))) θ) := by
  classical
  have hpoint : ∀ θ : ℝ,
      Set.indicator (Rj N lam j)
          (fun θ => ∑ n ∈ s, g n * Complex.exp (2*Real.pi*Complex.I*(n:ℂ)*(θ:ℂ))) θ
          * Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ)))
        = ∑ n ∈ s, g n * (Set.indicator (Rj N lam j) (fun _ => (1:ℂ)) θ
            * Complex.exp (-(2*Real.pi*Complex.I*(((m-n:ℤ):ℂ))*(θ:ℂ)))) := by
    intro θ
    by_cases h : θ ∈ Rj N lam j
    · rw [Set.indicator_of_mem h]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Set.indicator_of_mem h, one_mul]
      rw [show (g n * Complex.exp (2*Real.pi*Complex.I*(n:ℂ)*(θ:ℂ)))
            * Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ)))
          = g n * (Complex.exp (2*Real.pi*Complex.I*(n:ℂ)*(θ:ℂ))
            * Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ)))) from by ring,
        exp_mul_exp]
    · rw [Set.indicator_of_notMem h]
      simp [Set.indicator_of_notMem h]
  have hstep1 : (∫ θ in (0:ℝ)..1, Set.indicator (Rj N lam j)
        (fun θ => ∑ n ∈ s, g n * Complex.exp (2*Real.pi*Complex.I*(n:ℂ)*(θ:ℂ))) θ
        * Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ))))
      = ∫ θ in (0:ℝ)..1, ∑ n ∈ s, g n * (Set.indicator (Rj N lam j) (fun _ => (1:ℂ)) θ
            * Complex.exp (-(2*Real.pi*Complex.I*(((m-n:ℤ):ℂ))*(θ:ℂ)))) := by
    apply intervalIntegral.integral_congr
    intro θ _
    exact hpoint θ
  rw [hstep1]
  have hfin : ∀ n ∈ s, IntervalIntegrable (fun θ : ℝ => g n *
      (Set.indicator (Rj N lam j) (fun _ => (1:ℂ)) θ
      * Complex.exp (-(2*Real.pi*Complex.I*(((m-n:ℤ):ℂ))*(θ:ℂ))))) volume (0:ℝ) 1 :=
    fun n _ => intervalIntegrable_ind N lam j 0 1 (m-n) (g n)
  rw [intervalIntegral.integral_finsetSum hfin]
  apply Finset.sum_congr rfl
  intro n hn
  rw [intervalIntegral.integral_const_mul]
  congr 1
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1), ← integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards with θ
  by_cases h : θ ∈ Rj N lam j
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_mul]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]


/-! ## The two real-line band-pass maximal functions (as abbreviations) -/

/-- The real-line band-pass maximal function with the periodic frequency set. -/
private noncomputable def Rform (N : ℕ) (lam : Fin N → ℝ) (h : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ x : ℝ, (⨆ j : ℕ, ‖∫ ξ in (-(1/2):ℝ)..(1/2), (𝓕 h) ξ *
        Set.indicator {ξ : ℝ | ∃ k : Fin N, ∃ l : ℤ, |ξ + (l:ℝ) + lam k| ≤ (2:ℝ)^(-(j:ℝ)-1)}
          (fun _ => (1:ℂ)) ξ *
        Complex.exp (2*Real.pi*Complex.I*(ξ:ℂ)*(x:ℂ))‖ₑ)^(2:ℝ) ∂volume

/-- The real-line band-pass maximal function with the lifted finite frequency set. -/
private noncomputable def Lform (N : ℕ) (lam : Fin N → ℝ) (h : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ x : ℝ, (⨆ j : ℕ, ‖∫ ξ in (-(1/2):ℝ)..(1/2), (𝓕 h) ξ *
        Set.indicator {ξ : ℝ | ∃ a ∈ (liftedSet N lam : Set ℝ), |ξ - a| ≤ (2:ℝ)^(-(j:ℝ)-1)}
          (fun _ => (1:ℂ)) ξ *
        Complex.exp (2*Real.pi*Complex.I*(ξ:ℂ)*(x:ℂ))‖ₑ)^(2:ℝ) ∂volume

private lemma indicator_eq_of_mem_iff {S T : Set ℝ} {ξ : ℝ} (h : ξ ∈ S ↔ ξ ∈ T) :
    Set.indicator S (fun _ => (1:ℂ)) ξ = Set.indicator T (fun _ => (1:ℂ)) ξ := by
  by_cases hS : ξ ∈ S
  · rw [Set.indicator_of_mem hS, Set.indicator_of_mem (h.mp hS)]
  · rw [Set.indicator_of_notMem hS, Set.indicator_of_notMem (fun hT => hS (h.mpr hT))]

/-- On the fundamental domain the periodic frequency set equals the neighbourhood of the lifted
finite set, so the two real-line band-pass maximal functions agree. -/
private lemma Rform_eq_Lform (N : ℕ) (lam : Fin N → ℝ) (h : ℝ → ℂ) :
    Rform N lam h = Lform N lam h := by
  unfold Rform Lform
  apply lintegral_congr; intro x
  congr 1
  apply iSup_congr; intro j
  have hInt : (∫ ξ in (-(1/2):ℝ)..(1/2), (𝓕 h) ξ *
        Set.indicator {ξ : ℝ | ∃ k : Fin N, ∃ l : ℤ, |ξ + (l:ℝ) + lam k| ≤ (2:ℝ)^(-(j:ℝ)-1)}
          (fun _ => (1:ℂ)) ξ * Complex.exp (2*Real.pi*Complex.I*(ξ:ℂ)*(x:ℂ)))
      = (∫ ξ in (-(1/2):ℝ)..(1/2), (𝓕 h) ξ *
        Set.indicator {ξ : ℝ | ∃ a ∈ (liftedSet N lam : Set ℝ), |ξ - a| ≤ (2:ℝ)^(-(j:ℝ)-1)}
          (fun _ => (1:ℂ)) ξ * Complex.exp (2*Real.pi*Complex.I*(ξ:ℂ)*(x:ℂ))) := by
    apply intervalIntegral.integral_congr
    intro ξ hξ
    rw [Set.uIcc_of_le (by norm_num : (-(1/2):ℝ) ≤ 1/2)] at hξ
    beta_reduce
    rw [indicator_eq_of_mem_iff
      (show ξ ∈ ({θ : ℝ | ∃ k : Fin N, ∃ l : ℤ, |θ + (l:ℝ) + lam k| ≤ (2:ℝ)^(-(j:ℝ)-1)} : Set ℝ)
          ↔ ξ ∈ ({θ : ℝ | ∃ a ∈ (liftedSet N lam : Set ℝ), |θ - a| ≤ (2:ℝ)^(-(j:ℝ)-1)} : Set ℝ) from
        periodic_set_eq lam (dyadic_pos j) (dyadic_le_half j) hξ)]
  rw [hInt]

/-! ## The two discrete maximal functions (as abbreviations) -/

/-- The target's discrete maximal function (with the `n`-sum inside the integral). -/
private noncomputable def Tgt (N : ℕ) (lam : Fin N → ℝ) (g : ℤ → ℂ) (s : Finset ℤ) : ℝ≥0∞ :=
  ∫⁻ m : ℤ, (⨆ j : ℕ, ‖∫ θ in (0:ℝ)..1,
        Set.indicator {θ : ℝ | ∃ k : Fin N, ∃ l : ℤ, |θ + (l:ℝ) - lam k| ≤ (2:ℝ)^(-(j:ℝ)-1)}
          (fun θ => ∑ n ∈ s, g n * Complex.exp (2*Real.pi*Complex.I*(n:ℂ)*(θ:ℂ))) θ *
        Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ)))‖ₑ)^(2:ℝ)
      ∂MeasureTheory.Measure.count

/-- The discrete maximal function in the form produced by the transference lemma (the `n`-sum
outside the integral). -/
private noncomputable def Trf (N : ℕ) (lam : Fin N → ℝ) (g : ℤ → ℂ) (s : Finset ℤ) : ℝ≥0∞ :=
  ∫⁻ m : ℤ, (⨆ j : ℕ, ‖∑ n ∈ s, g n *
          (∫ θ in Set.Icc (0:ℝ) 1,
            Set.indicator {θ : ℝ | ∃ k : Fin N, ∃ l : ℤ, |θ + (l:ℝ) - lam k| ≤ (2:ℝ)^(-(j:ℝ)-1)}
              (fun θ => Complex.exp (-(2*Real.pi*Complex.I*(((m-n:ℤ):ℂ))*(θ:ℂ)))) θ)‖ₑ)^(2:ℝ)
      ∂MeasureTheory.Measure.count

private lemma Tgt_eq_Trf (N : ℕ) (lam : Fin N → ℝ) (g : ℤ → ℂ) (s : Finset ℤ) :
    Tgt N lam g s = Trf N lam g s := by
  unfold Tgt Trf
  apply lintegral_congr; intro m
  congr 1
  apply iSup_congr; intro j
  rw [show (∫ θ in (0:ℝ)..1,
        Set.indicator {θ : ℝ | ∃ k : Fin N, ∃ l : ℤ, |θ + (l:ℝ) - lam k| ≤ (2:ℝ)^(-(j:ℝ)-1)}
          (fun θ => ∑ n ∈ s, g n * Complex.exp (2*Real.pi*Complex.I*(n:ℂ)*(θ:ℂ))) θ *
        Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ))))
      = (∑ n ∈ s, g n * (∫ θ in Set.Icc (0:ℝ) 1,
            Set.indicator {θ : ℝ | ∃ k : Fin N, ∃ l : ℤ, |θ + (l:ℝ) - lam k| ≤ (2:ℝ)^(-(j:ℝ)-1)}
              (fun θ => Complex.exp (-(2*Real.pi*Complex.I*(((m-n:ℤ):ℂ))*(θ:ℂ)))) θ)) from by
    simpa only [Rj] using inner_eq N lam g s j m]

/-! ## The main transference theorem -/

theorem periodic_neighborhood_of_real_line_bandpass
    (H : ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset ℝ) (f : ℝ → ℂ), Integrable f →
      ∫⁻ (x : ℝ), (⨆ j : ℕ, ‖∫ ξ in (-(1/2):ℝ)..(1/2),
          (𝓕 f) ξ *
          Set.indicator {ξ : ℝ | ∃ a ∈ (s : Set ℝ), |ξ - a| ≤ (2:ℝ)^(-(j:ℝ)-1)} (fun _ => (1:ℂ)) ξ *
          Complex.exp (2*Real.pi*Complex.I*(ξ:ℂ)*(x:ℂ))‖ₑ)^(2:ℝ) ∂volume
        ≤ ENNReal.ofReal ((C * Real.log ((s.card:ℝ)+2)^2)^2) * ∫⁻ x, ‖f x‖ₑ^(2:ℝ) ∂volume) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ (N : ℕ) (lam : Fin N → ℝ) (g : ℤ → ℂ) (s : Finset ℤ),
      (∀ n, n ∉ s → g n = 0) →
      ∫⁻ m : ℤ, (⨆ j : ℕ, ‖∫ θ in (0:ℝ)..1,
          Set.indicator {θ : ℝ | ∃ k : Fin N, ∃ l : ℤ, |θ + (l:ℝ) - lam k| ≤ (2:ℝ)^(-(j:ℝ)-1)}
            (fun θ => ∑ n ∈ s, g n * Complex.exp (2*Real.pi*Complex.I*(n:ℂ)*(θ:ℂ))) θ *
          Complex.exp (-(2*Real.pi*Complex.I*(m:ℂ)*(θ:ℂ)))‖ₑ)^(2:ℝ)
        ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((C' * Real.log ((N:ℝ)+2)^2)^2)
        * ∫⁻ n, ‖g n‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count := by
  obtain ⟨CH, hCHpos, hH⟩ := H
  obtain ⟨C0, hC0pos, hC0⟩ := z_neighborhood_of_real_bandpass_uniform
  refine ⟨Real.sqrt C0 * CH * 9, by positivity, ?_⟩
  intro N lam g s hs
  obtain ⟨gR, hgR_memLp, hgR_norm, hgR_bound⟩ := hC0 N lam g s hs
  -- step 2: the count integral of `‖g‖²` as a finite sum
  have hg_count : (∫⁻ n : ℤ, ‖g n‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count)
      = ∑ n ∈ s, ‖g n‖ₑ^(2:ℝ) := by
    rw [MeasureTheory.lintegral_count]
    exact tsum_eq_sum (s := s) (fun n hn => by rw [hs n hn]; simp)
  -- step 3: real-line bound with the lifted frequency set
  have hRL : Lform N lam gR
      ≤ ENNReal.ofReal ((CH * Real.log (((liftedSet N lam).card:ℝ)+2)^2)^2)
        * ∫⁻ x : ℝ, ‖gR x‖ₑ^(2:ℝ) ∂volume := by
    rcases em (Integrable gR) with hgint | hgnint
    · exact hH (liftedSet N lam) gR hgint
    · have hf0 : 𝓕 gR = 0 := fourier_eq_zero_of_not_integrable hgnint
      have hzero : Lform N lam gR = 0 := by
        unfold Lform
        simp only [hf0, Pi.zero_apply, zero_mul]
        simp
      rw [hzero]; positivity
  -- step 4: the constant comparison
  have hconst : C0 * (CH * Real.log (((liftedSet N lam).card:ℝ)+2)^2)^2
      ≤ (Real.sqrt C0 * CH * 9 * Real.log ((N:ℝ)+2)^2)^2 := by
    have hC0nn : (0:ℝ) ≤ C0 := hC0pos.le
    have hsqC : (Real.sqrt C0)^2 = C0 := Real.sq_sqrt hC0nn
    have hN2 : (2:ℝ) ≤ (N:ℝ) + 2 := by
      have : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
      linarith
    have hcard : ((liftedSet N lam).card : ℝ) + 2 ≤ 3 * ((N:ℝ) + 2) := by
      have h := liftedSet_card_le N lam
      have hcast : ((liftedSet N lam).card : ℝ) ≤ 3 * (N:ℝ) := by
        have h' : ((liftedSet N lam).card : ℝ) ≤ ((3*N : ℕ) : ℝ) := by exact_mod_cast h
        simpa using h'
      linarith
    have hlogle : Real.log (((liftedSet N lam).card:ℝ)+2) ≤ 3 * Real.log ((N:ℝ)+2) := by
      have hlogN2 : Real.log 2 ≤ Real.log ((N:ℝ)+2) := Real.log_le_log (by norm_num) hN2
      have hlog3 : Real.log 3 ≤ 2 * Real.log ((N:ℝ)+2) := by
        have h4 : Real.log ((2:ℝ)^2) = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
        calc Real.log 3 ≤ Real.log ((2:ℝ)^2) := Real.log_le_log (by norm_num) (by norm_num)
          _ = 2 * Real.log 2 := h4
          _ ≤ 2 * Real.log ((N:ℝ)+2) := by linarith
      calc Real.log (((liftedSet N lam).card:ℝ)+2) ≤ Real.log (3 * ((N:ℝ)+2)) :=
            Real.log_le_log (by positivity) hcard
        _ = Real.log 3 + Real.log ((N:ℝ)+2) := Real.log_mul (by norm_num) (by positivity)
        _ ≤ 3 * Real.log ((N:ℝ)+2) := by linarith
    have ha : (0:ℝ) ≤ Real.log (((liftedSet N lam).card:ℝ)+2) :=
      Real.log_nonneg (by
        have : (0:ℝ) ≤ ((liftedSet N lam).card : ℝ) := Nat.cast_nonneg _
        linarith)
    have h4 : Real.log (((liftedSet N lam).card:ℝ)+2)^4 ≤ 81 * Real.log ((N:ℝ)+2)^4 := by
      have h := pow_le_pow_left₀ ha hlogle 4
      have h3 : (3 * Real.log ((N:ℝ)+2))^4 = 81 * Real.log ((N:ℝ)+2)^4 := by ring
      rw [h3] at h; exact h
    have hCHnn : (0:ℝ) ≤ CH := hCHpos.le
    calc C0 * (CH * Real.log (((liftedSet N lam).card:ℝ)+2)^2)^2
        = C0 * CH^2 * Real.log (((liftedSet N lam).card:ℝ)+2)^4 := by ring
      _ ≤ C0 * CH^2 * (81 * Real.log ((N:ℝ)+2)^4) :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = (Real.sqrt C0 * CH * 9 * Real.log ((N:ℝ)+2)^2)^2 := by
            rw [mul_pow, mul_pow, mul_pow, hsqC]; ring
  -- step 5: assemble
  change Tgt N lam g s ≤ ENNReal.ofReal ((Real.sqrt C0 * CH * 9 * Real.log ((N:ℝ)+2)^2)^2)
        * ∫⁻ n : ℤ, ‖g n‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count
  calc Tgt N lam g s
      = Trf N lam g s := Tgt_eq_Trf N lam g s
    _ ≤ ENNReal.ofReal C0 * Rform N lam gR := hgR_bound
    _ = ENNReal.ofReal C0 * Lform N lam gR := by rw [Rform_eq_Lform N lam gR]
    _ ≤ ENNReal.ofReal C0 * (ENNReal.ofReal ((CH * Real.log (((liftedSet N lam).card:ℝ)+2)^2)^2)
          * ∫⁻ x : ℝ, ‖gR x‖ₑ^(2:ℝ) ∂volume) := mul_le_mul' le_rfl hRL
    _ = (ENNReal.ofReal C0 * ENNReal.ofReal ((CH * Real.log (((liftedSet N lam).card:ℝ)+2)^2)^2))
          * ∫⁻ x : ℝ, ‖gR x‖ₑ^(2:ℝ) ∂volume := by rw [mul_assoc]
    _ = ENNReal.ofReal (C0 * (CH * Real.log (((liftedSet N lam).card:ℝ)+2)^2)^2)
          * ∫⁻ x : ℝ, ‖gR x‖ₑ^(2:ℝ) ∂volume := by rw [← ENNReal.ofReal_mul hC0pos.le]
    _ ≤ ENNReal.ofReal ((Real.sqrt C0 * CH * 9 * Real.log ((N:ℝ)+2)^2)^2)
          * ∫⁻ x : ℝ, ‖gR x‖ₑ^(2:ℝ) ∂volume :=
        mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hconst) zero_le
    _ = ENNReal.ofReal ((Real.sqrt C0 * CH * 9 * Real.log ((N:ℝ)+2)^2)^2)
          * ∑ n ∈ s, ‖g n‖ₑ^(2:ℝ) := by rw [hgR_norm]
    _ = ENNReal.ofReal ((Real.sqrt C0 * CH * 9 * Real.log ((N:ℝ)+2)^2)^2)
          * ∫⁻ n : ℤ, ‖g n‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count := by rw [← hg_count]

end Commons.Analysis.Fourier
