import Mathlib
import Submission.Commons.MeasureTheory.Integral.simplex_integral_scaled

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Commons.Analysis.Integral

noncomputable section

/-- A hyperplane `∑ i, t i = a` in `Fin k → ℝ` has Lebesgue measure zero. -/
private lemma volume_sum_eq_zero {k : ℕ} (hk : 1 ≤ k) (a : ℝ) :
    (MeasureTheory.volume : MeasureTheory.Measure (Fin k → ℝ))
      {t : Fin k → ℝ | ∑ i, t i = a} = 0 := by
  let L : (Fin k → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun t => ∑ i, t i
      map_add' := by intro x y; simp [Finset.sum_add_distrib]
      map_smul' := by intro c x; simp [Finset.mul_sum] }
  let i0 : Fin k := ⟨0, by omega⟩
  let p : Fin k → ℝ := Pi.single i0 a
  let s : AffineSubspace ℝ (Fin k → ℝ) := AffineSubspace.mk' p L.ker
  have hset : (s : Set (Fin k → ℝ)) = {t | ∑ i, t i = a} := by
    ext t
    change t ∈ AffineSubspace.mk' p L.ker ↔ t ∈ {t | ∑ i, t i = a}
    rw [AffineSubspace.mem_mk', LinearMap.mem_ker]
    simp only [Set.mem_ofPred_eq]
    have hp : L p = a := by simp [L, p]
    have hvsub : (t -ᵥ p) = t - p := rfl
    rw [hvsub, map_sub, hp, sub_eq_zero]
    simp [L]
  rw [← hset]
  refine MeasureTheory.Measure.addHaar_affineSubspace (μ := MeasureTheory.volume)
    (E := Fin k → ℝ) s ?_
  intro htop
  have hmem : (p + Pi.single i0 1) ∈ s := by rw [htop]; trivial
  change (p + Pi.single i0 1) ∈ (s : Set (Fin k → ℝ)) at hmem
  rw [hset] at hmem
  simp only [Set.mem_ofPred_eq] at hmem
  have hsum : ∑ i, (p + Pi.single i0 1 : Fin k → ℝ) i = a + 1 := by
    simp [p, Finset.sum_add_distrib]
  linarith

/-- The simplex `{t | tᵢ ≥ 0, ∑ tᵢ ≤ c}` is measurable. -/
private lemma measurableSet_simplex_body (k : ℕ) (c : ℝ) :
    MeasurableSet {t : Fin k → ℝ | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ c} := by
  have h : {t : Fin k → ℝ | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ c}
      = (⋂ i, {t : Fin k → ℝ | 0 ≤ t i}) ∩ {t : Fin k → ℝ | ∑ i, t i ≤ c} := by
    ext t; simp [Set.mem_iInter]
  rw [h]
  exact (MeasurableSet.iInter fun i =>
      measurableSet_le measurable_const (measurable_pi_apply i)).inter
    (measurableSet_le (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)) measurable_const)

/-- The simplex `{t | tᵢ ≥ 0, ∑ tᵢ ≤ c}` has finite Lebesgue measure. -/
private lemma volume_simplex_body_lt_top (k : ℕ) (c : ℝ) :
    (MeasureTheory.volume : MeasureTheory.Measure (Fin k → ℝ))
      {t : Fin k → ℝ | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ c} < ∞ := by
  calc (MeasureTheory.volume : MeasureTheory.Measure (Fin k → ℝ))
        {t : Fin k → ℝ | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ c}
      ≤ (MeasureTheory.volume : MeasureTheory.Measure (Fin k → ℝ))
          (Set.pi Set.univ (fun _ : Fin k => Set.Icc (0:ℝ) c)) := by
        refine measure_mono ?_
        intro t ht
        simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
        intro i
        exact ⟨ht.1 i, le_trans (Finset.single_le_sum (fun j _ => ht.1 j)
          (Finset.mem_univ i)) ht.2⟩
    _ = ∏ _ : Fin k, (MeasureTheory.volume : MeasureTheory.Measure ℝ) (Set.Icc (0:ℝ) c) :=
        volume_pi_pi _
    _ < ∞ := ENNReal.prod_lt_top (fun i _ => by
        rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)

/-- The volume of the orthant simplex `{t | tᵢ ≥ 0, ∑ tᵢ ≤ c}` is `c^k / k!`. -/
private lemma volume_simplex_body {k : ℕ} (hk : 1 ≤ k) {c : ℝ} (hc : 0 ≤ c) :
    ((MeasureTheory.volume : MeasureTheory.Measure (Fin k → ℝ))
      {t : Fin k → ℝ | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ c}).toReal
      = c ^ k / ((k.factorial : ℕ) : ℝ) := by
  rcases eq_or_lt_of_le hc with rfl | hcpos
  · have hset : {t : Fin k → ℝ | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ (0:ℝ)}
        ⊆ {t : Fin k → ℝ | ∑ i, t i = (0:ℝ)} := by
      intro t ht
      exact le_antisymm ht.2 (Finset.sum_nonneg (fun i _ => ht.1 i))
    have hvol : (MeasureTheory.volume : MeasureTheory.Measure (Fin k → ℝ))
        {t : Fin k → ℝ | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ (0:ℝ)} = 0 :=
      measure_mono_null hset (volume_sum_eq_zero hk 0)
    rw [hvol]
    have hk0 : k ≠ 0 := by omega
    simp [zero_pow hk0]
  · set S : Set (Fin k → ℝ) := {t | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ c} with hS
    have hSmeas : MeasurableSet S := measurableSet_simplex_body k c
    have h := Commons.MeasureTheory.Integral.simplex_integral_scaled c hcpos 0
      (fun _ : Fin k => 0)
    have hL : ∫ t : Fin k → ℝ in S,
        (c - ∑ i, t i) ^ (0:ℕ) * ∏ i, (t i) ^ ((fun _ : Fin k => (0:ℕ)) i)
        = ∫ _ in S, (1:ℝ) := by
      apply setIntegral_congr_fun hSmeas
      intro t ht
      simp
    have hInt : ∫ _ in S, (1:ℝ)
        = (MeasureTheory.volume : MeasureTheory.Measure (Fin k → ℝ)).real S := by
      rw [setIntegral_const, smul_eq_mul, mul_one]
    have hcalc : ∫ t : Fin k → ℝ in S,
        (c - ∑ i, t i) ^ (0:ℕ) * ∏ i, (t i) ^ ((fun _ : Fin k => (0:ℕ)) i)
        = c ^ k / ((k.factorial : ℕ) : ℝ) := by
      rw [h]
      simp
    change (MeasureTheory.volume : MeasureTheory.Measure (Fin k → ℝ)).real S
      = c ^ k / ((k.factorial : ℕ) : ℝ)
    rw [← hInt, ← hL]
    exact hcalc

theorem volume_orthant_slab_ge_one {k : ℕ} (hk : 1 ≤ k) {a c : ℝ} (ha : 0 ≤ a)
    (hac : a ≤ c) :
    (MeasureTheory.volume {t : Fin k → ℝ |
        (∀ i : Fin k, 0 ≤ t i) ∧ a ≤ ∑ i : Fin k, t i ∧ ∑ i : Fin k, t i ≤ c}).toReal
      = (c ^ k - a ^ k) / ((k.factorial : ℕ) : ℝ) := by
  have hc : 0 ≤ c := le_trans ha hac
  set S : ℝ → Set (Fin k → ℝ) :=
    fun x => {t | (∀ i : Fin k, 0 ≤ t i) ∧ ∑ i, t i ≤ x} with hS
  set T : Set (Fin k → ℝ) :=
    {t | (∀ i : Fin k, 0 ≤ t i) ∧ a ≤ ∑ i, t i ∧ ∑ i, t i ≤ c} with hT
  set A : Set (Fin k → ℝ) := S c \ S a with hA
  set B : Set (Fin k → ℝ) := {t | ∑ i, t i = a} with hB
  have hBnull : (MeasureTheory.volume : MeasureTheory.Measure (Fin k → ℝ)) B = 0 :=
    volume_sum_eq_zero hk a
  have hTsub : T ⊆ A ∪ B := by
    intro t ht
    rcases ht with ⟨h0, h1, h2⟩
    by_cases h3 : ∑ i, t i ≤ a
    · right
      exact le_antisymm h3 h1
    · left
      refine ⟨⟨h0, h2⟩, ?_⟩
      intro htSa
      exact h3 htSa.2
  have hAsub : A ⊆ T := by
    intro t ht
    rcases ht with ⟨htS, htnot⟩
    rcases htS with ⟨h0, h2⟩
    have h1 : a ≤ ∑ i, t i := by
      by_contra hlt
      exact htnot ⟨h0, le_of_lt (lt_of_not_ge hlt)⟩
    exact ⟨h0, h1, h2⟩
  have hvolAB_le : (MeasureTheory.volume : MeasureTheory.Measure (Fin k → ℝ)) (A ∪ B)
      ≤ (MeasureTheory.volume : MeasureTheory.Measure (Fin k → ℝ)) A := by
    calc (MeasureTheory.volume : MeasureTheory.Measure (Fin k → ℝ)) (A ∪ B)
        ≤ (MeasureTheory.volume : MeasureTheory.Measure (Fin k → ℝ)) A
            + (MeasureTheory.volume : MeasureTheory.Measure (Fin k → ℝ)) B :=
              measure_union_le A B
      _ = (MeasureTheory.volume : MeasureTheory.Measure (Fin k → ℝ)) A := by
            rw [hBnull, add_zero]
  have hvolT_eq : (MeasureTheory.volume : MeasureTheory.Measure (Fin k → ℝ)) T
      = (MeasureTheory.volume : MeasureTheory.Measure (Fin k → ℝ)) A :=
    le_antisymm (le_trans (measure_mono hTsub) hvolAB_le) (measure_mono hAsub)
  have hSa_sub : S a ⊆ S c := by
    intro t ht
    exact ⟨ht.1, le_trans ht.2 hac⟩
  have hSa_meas : MeasurableSet (S a) := measurableSet_simplex_body k a
  have hSa_fin : (MeasureTheory.volume : MeasureTheory.Measure (Fin k → ℝ)) (S a) ≠ ∞ :=
    ne_of_lt (volume_simplex_body_lt_top k a)
  have hA_eq : (MeasureTheory.volume : MeasureTheory.Measure (Fin k → ℝ)) A
      = (MeasureTheory.volume : MeasureTheory.Measure (Fin k → ℝ)) (S c)
        - (MeasureTheory.volume : MeasureTheory.Measure (Fin k → ℝ)) (S a) := by
    rw [hA]
    exact measure_sdiff hSa_sub hSa_meas.nullMeasurableSet hSa_fin
  have hSc_fin : (MeasureTheory.volume : MeasureTheory.Measure (Fin k → ℝ)) (S c) ≠ ∞ :=
    ne_of_lt (volume_simplex_body_lt_top k c)
  have hSc_le : (MeasureTheory.volume : MeasureTheory.Measure (Fin k → ℝ)) (S a)
      ≤ (MeasureTheory.volume : MeasureTheory.Measure (Fin k → ℝ)) (S c) :=
    measure_mono hSa_sub
  rw [hvolT_eq, hA_eq]
  rw [ENNReal.toReal_sub_of_le hSc_le hSc_fin]
  rw [volume_simplex_body hk hc, volume_simplex_body hk ha]
  ring

end

end Commons.Analysis.Integral
