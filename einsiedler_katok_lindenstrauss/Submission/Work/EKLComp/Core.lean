import Mathlib
import Submission.Work.EKLContract.Interfaces

/-!
# C3 — Kolmogorov–Sinai entropy basics: foundation

Self-contained foundation for `P_EntropyBasics` (component C3 of the frozen EKL contract):
finite Gibbs inequality, subadditivity of `negMulLog`, basic properties of `Hfam`, the
entropy-of-a-join inequality, the partition structure of `joinSets`, Fekete/subadditivity,
and the resulting API for `hPart` and `ent`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

noncomputable section

namespace Work.EKLComp.Core

open Work.EKLContract

variable {X : Type*} [mX : MeasurableSpace X]

/-! ## 0. Toolbox -/

/-- A set has measure at most `1` in a probability space. -/
theorem prob_measure_le_one (μ : Measure X) [IsProbabilityMeasure μ] (s : Set X) : μ s ≤ 1 := by
  rw [← measure_univ (μ := μ)]
  exact measure_mono (Set.subset_univ _)

theorem prob_toReal_le_one (μ : Measure X) [IsProbabilityMeasure μ] (s : Set X) :
    (μ s).toReal ≤ 1 :=
  (ENNReal.toReal_le_toReal (measure_ne_top μ _) ENNReal.one_ne_top).mpr
    (prob_measure_le_one μ s)

theorem prob_toReal_nonneg (μ : Measure X) (s : Set X) : 0 ≤ (μ s).toReal :=
  ENNReal.toReal_nonneg

/-- A double sum over a product type as an iterated sum. -/
theorem sum_prod_univ {ι κ : Type*} [Fintype ι] [Fintype κ] {M : Type*} [AddCommMonoid M]
    (f : ι × κ → M) : ∑ q : ι × κ, f q = ∑ i, ∑ j, f (i, j) := by
  rw [← Finset.univ_product_univ, Finset.sum_product]

/-! ## 1. A finite Gibbs (log-sum) inequality -/

/-- Gibbs' inequality on a finite type: for `p q : ι → ℝ` with `p, q ≥ 0`, equal sums, and
`p i > 0 → q i > 0`, we have `∑ i, p i * log (p i / q i) ≥ 0`. -/
theorem sum_mul_log_div_nonneg {ι : Type*} [Fintype ι] (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (hsum : ∑ i, p i = ∑ i, q i)
    (hpos : ∀ i, 0 < p i → 0 < q i) :
    0 ≤ ∑ i, p i * Real.log (p i / q i) := by
  have key : ∀ i, p i - q i ≤ p i * Real.log (p i / q i) := by
    intro i
    rcases eq_or_lt_of_le (hp i) with h0 | h0
    · rw [← h0, zero_mul]
      linarith [hq i]
    · have hq0 : 0 < q i := hpos i h0
      have hlog : Real.log (p i / q i) = - Real.log (q i / p i) := by
        rw [Real.log_div (ne_of_gt h0) (ne_of_gt hq0),
            Real.log_div (ne_of_gt hq0) (ne_of_gt h0)]
        ring
      have h2 : Real.log (q i / p i) ≤ q i / p i - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hq0 h0)
      have h3 : p i * (q i / p i - 1) = q i - p i := by
        field_simp
      have h4 := mul_le_mul_of_nonneg_left h2 (le_of_lt h0)
      rw [h3] at h4
      rw [hlog]
      nlinarith [h4]
  calc (0 : ℝ) = ∑ i, (p i - q i) := by
        rw [Finset.sum_sub_distrib, hsum, sub_self]
    _ ≤ ∑ i, p i * Real.log (p i / q i) := Finset.sum_le_sum fun i _ => key i

/-! ## 2. Subadditivity of `negMulLog` on `[0,1]` -/

theorem negMulLog_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    Real.negMulLog (a + b) ≤ Real.negMulLog a + Real.negMulLog b := by
  rcases eq_or_lt_of_le (add_nonneg ha hb) with h0 | h0
  · have ha' : a = 0 := le_antisymm (by linarith) ha
    have hb' : b = 0 := le_antisymm (by linarith) hb
    rw [ha', hb']
    simp
  · have ht0 : 0 < a + b := h0
    have htne : a + b ≠ 0 := ne_of_gt ht0
    set t : ℝ := a + b with ht
    have ht0' : 0 < t := by rw [ht]; exact ht0
    set l : ℝ := a / t with hl
    have hl0 : 0 ≤ l := by rw [hl]; positivity
    have hl1 : l ≤ 1 := by
      rw [hl, div_le_one ht0']
      linarith [ht]
    have hlt : 1 - l ≤ 1 := by linarith
    have h1l : 0 ≤ 1 - l := by linarith
    have hla : a = l * t := by
      rw [hl]
      exact (div_mul_cancel₀ a htne).symm
    have hlb : b = (1 - l) * t := by
      have hbt : b = t - a := by rw [ht]; ring
      rw [hbt, hla]; ring
    rw [hla, hlb, Real.negMulLog_mul, Real.negMulLog_mul]
    have hl0' : 0 ≤ Real.negMulLog l := Real.negMulLog_nonneg hl0 hl1
    have hl1' : 0 ≤ Real.negMulLog (1 - l) := Real.negMulLog_nonneg h1l hlt
    nlinarith [mul_nonneg (le_of_lt ht0') hl0', mul_nonneg (le_of_lt ht0') hl1']

/-- Subadditivity of `negMulLog` over a finite sum. -/
theorem negMulLog_sum_le {ι : Type*} (x : ι → ℝ) :
    ∀ (s : Finset ι), (∀ i ∈ s, 0 ≤ x i) → (∑ i ∈ s, x i ≤ 1) →
      Real.negMulLog (∑ i ∈ s, x i) ≤ ∑ i ∈ s, Real.negMulLog (x i) := by
  classical
  intro s
  induction s using Finset.induction with
  | empty => intro _ _; simp
  | insert a s ha ih =>
    intro hx hs
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h1 : 0 ≤ x a := hx a (Finset.mem_insert_self a s)
    have h2 : 0 ≤ ∑ i ∈ s, x i :=
      Finset.sum_nonneg fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have h3 : x a + ∑ i ∈ s, x i ≤ 1 := by
      have := hs; rwa [Finset.sum_insert ha] at this
    have h4 : ∑ i ∈ s, x i ≤ 1 := by linarith
    have h5 := ih (fun i hi => hx i (Finset.mem_insert_of_mem hi)) h4
    have h6 := negMulLog_add_le h1 h2 h3
    linarith

/-! ## 3. Measurable partitions of a probability space -/

/-- A finite measurable partition of `X`, indexed by an arbitrary finite type. -/
def IsMPart {ι : Type*} [Fintype ι] (A : ι → Set X) : Prop :=
  (∀ i, MeasurableSet (A i)) ∧ Pairwise (fun i j => Disjoint (A i) (A j)) ∧
    (⋃ i, A i) = Set.univ

theorem IsMPart.measurable {ι : Type*} [Fintype ι] {A : ι → Set X} (h : IsMPart A) :
    ∀ i, MeasurableSet (A i) := h.1

theorem IsMPart.disjoint {ι : Type*} [Fintype ι] {A : ι → Set X} (h : IsMPart A) :
    Pairwise (fun i j => Disjoint (A i) (A j)) := h.2.1

theorem IsMPart.cover {ι : Type*} [Fintype ι] {A : ι → Set X} (h : IsMPart A) :
    (⋃ i, A i) = Set.univ := h.2.2

/-- The total mass of a finite measurable partition of a probability space is `1`. -/
theorem IsMPart.sum_measure (μ : Measure X) {ι : Type*} [Fintype ι] {A : ι → Set X}
    (h : IsMPart A) : ∑ i, μ (A i) = μ Set.univ := by
  rw [← h.cover, measure_iUnion h.disjoint h.measurable, tsum_fintype]

theorem IsMPart.sum_measure_toReal (μ : Measure X) [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] {A : ι → Set X} (h : IsMPart A) :
    ∑ i, (μ (A i)).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun i _ => measure_ne_top μ _), h.sum_measure,
    measure_univ, ENNReal.toReal_one]

/-- Slicing a measurable set by a finite partition. -/
theorem IsMPart.sum_measure_inter (μ : Measure X) {ι : Type*} [Fintype ι] {B : ι → Set X}
    (h : IsMPart B) {S : Set X} (hS : MeasurableSet S) :
    ∑ j, μ (S ∩ B j) = μ S := by
  have hset : (⋃ j : ι, (S ∩ B j)) = S := by
    rw [← Set.inter_iUnion, h.cover, Set.inter_univ]
  conv_rhs => rw [← hset]
  rw [measure_iUnion
    (fun j k hjk => (h.disjoint hjk).mono Set.inter_subset_right Set.inter_subset_right)
    (fun j => hS.inter (h.measurable j)), tsum_fintype]

/-! ## 4. Basic properties of `Hfam` -/

theorem Hfam_nonneg (μ : Measure X) [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    (P : ι → Set X) : 0 ≤ Hfam μ P := by
  refine Finset.sum_nonneg fun i _ =>
    Real.negMulLog_nonneg ENNReal.toReal_nonneg (prob_toReal_le_one μ (P i))

theorem Hfam_equiv (μ : Measure X) {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (R : κ → Set X) : Hfam μ (fun i => R (e i)) = Hfam μ R :=
  Fintype.sum_equiv e (fun i => Real.negMulLog (μ (R (e i))).toReal)
    (fun k => Real.negMulLog (μ (R k)).toReal) fun _ => rfl

theorem Hfam_congr_ae (μ : Measure X) {ι : Type*} [Fintype ι] {P Q : ι → Set X}
    (h : ∀ i, P i =ᵐ[μ] Q i) : Hfam μ P = Hfam μ Q := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [measure_congr (h i)]

/-- Shannon's bound: a partition of a probability space into `card ι` atoms has entropy at most
`log (card ι)`. -/
theorem Hfam_le_log_card (μ : Measure X) [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    {P : ι → Set X} (h : IsMPart P) : Hfam μ P ≤ Real.log (Fintype.card ι : ℝ) := by
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hc | hc
  · haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hc
    have h0 : Hfam μ P = 0 := by simp [Hfam]
    rw [h0, hc]
    simp
  · set n : ℝ := (Fintype.card ι : ℝ) with hn
    have hnpos : 0 < n := by rw [hn]; exact_mod_cast hc
    have hnne : n ≠ 0 := ne_of_gt hnpos
    have hx0 : ∀ i, 0 ≤ (μ (P i)).toReal := fun i => ENNReal.toReal_nonneg
    have hsum : ∑ i, (μ (P i)).toReal = 1 := h.sum_measure_toReal μ
    have hw : ∀ i ∈ (Finset.univ : Finset ι), (0:ℝ) ≤ 1 / n :=
      fun i _ => le_of_lt (one_div_pos.mpr hnpos)
    have hwsum : ∑ i ∈ (Finset.univ : Finset ι), (1 / n : ℝ) = 1 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hn]
      field_simp
    have hj := Real.concaveOn_negMulLog.le_map_sum (t := (Finset.univ : Finset ι))
      (w := fun _ : ι => (1 / n : ℝ)) (p := fun i => (μ (P i)).toReal) hw hwsum
      (fun i _ => Set.mem_Ici.mpr (hx0 i))
    simp only [smul_eq_mul] at hj
    have hweighted : ∑ i, (1 / n) * (μ (P i)).toReal = 1 / n := by
      rw [← Finset.mul_sum, hsum, mul_one]
    rw [hweighted] at hj
    have hj' : (1 / n) * Hfam μ P ≤ Real.negMulLog (1 / n) := by
      rw [Hfam, Finset.mul_sum]
      exact hj
    have h2 : Real.negMulLog (1 / n) = Real.log n / n := by
      simp only [Real.negMulLog_def]
      rw [Real.log_div one_ne_zero hnne, Real.log_one]
      field_simp
      ring
    rw [h2] at hj'
    have h3 : n * ((1 / n) * Hfam μ P) ≤ n * (Real.log n / n) :=
      mul_le_mul_of_nonneg_left hj' (le_of_lt hnpos)
    have h4 : n * ((1 / n) * Hfam μ P) = Hfam μ P := by field_simp
    have h5 : n * (Real.log n / n) = Real.log n := by field_simp
    rw [h4, h5] at h3
    simpa [hn] using h3

/-! ## 5. The entropy of a join -/

/-- Entropy is monotone under refinement: if every atom of `B` lies inside some atom of `A`,
then `H(A) ≤ H(B)`. -/
theorem Hfam_mono (μ : Measure X) [IsProbabilityMeasure μ] {ι κ : Type*} [Fintype ι]
    [Fintype κ] {A : ι → Set X} {B : κ → Set X} (hA : IsMPart A) (hB : IsMPart B) (f : κ → ι)
    (hsub : ∀ j, B j ⊆ A (f j)) : Hfam μ A ≤ Hfam μ B := by
  classical
  have hunion : ∀ i, (⋃ j ∈ (Finset.univ.filter fun j => f j = i), B j) = A i := by
    intro i
    refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hjS, hxj⟩ := Set.mem_iUnion.mp hj
      have hfj : f j = i := (Finset.mem_filter.mp hjS).2
      rw [← hfj]
      exact hsub j hxj
    · intro x hx
      have hx' : x ∈ ⋃ j, B j := by rw [hB.cover]; trivial
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx'
      have hfj : f j = i := by
        by_contra hne
        exact Set.disjoint_left.mp (hA.disjoint hne) (hsub j hj) hx
      exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hfj, hj⟩⟩
  have hsum_meas : ∀ i, ∑ j ∈ (Finset.univ.filter fun j => f j = i), μ (B j) = μ (A i) := by
    intro i
    rw [← hunion i,
      measure_biUnion_finset (s := Finset.univ.filter fun j => f j = i) (f := B)
        (fun j _ k _ hjk => hB.disjoint hjk) (fun j _ => hB.measurable j)]
  have hsum_real : ∀ i, ∑ j ∈ (Finset.univ.filter fun j => f j = i), (μ (B j)).toReal
      = (μ (A i)).toReal := by
    intro i
    rw [← ENNReal.toReal_sum (fun j _ => measure_ne_top μ _), hsum_meas i]
  calc Hfam μ A = ∑ i, (μ (A i)).toReal.negMulLog := rfl
    _ = ∑ i, (∑ j ∈ (Finset.univ.filter fun j => f j = i), (μ (B j)).toReal).negMulLog := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hsum_real i]
    _ ≤ ∑ i, ∑ j ∈ (Finset.univ.filter fun j => f j = i), (μ (B j)).toReal.negMulLog := by
        refine Finset.sum_le_sum fun i _ => negMulLog_sum_le (fun j => (μ (B j)).toReal) _ ?_ ?_
        · intro j _; exact ENNReal.toReal_nonneg
        · rw [hsum_real i]; exact prob_toReal_le_one μ (A i)
    _ = ∑ j, (μ (B j)).toReal.negMulLog :=
        Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset κ))
          (t := (Finset.univ : Finset ι)) (g := f)
          (fun x _ => Finset.mem_univ (f x)) (fun j => (μ (B j)).toReal.negMulLog)
    _ = Hfam μ B := rfl

/-- Entropy of a join is subadditive: `H(A ∨ B) ≤ H(A) + H(B)`. -/
theorem Hfam_inter_le (μ : Measure X) [IsProbabilityMeasure μ] {ι κ : Type*} [Fintype ι]
    [Fintype κ] {A : ι → Set X} {B : κ → Set X} (hA : IsMPart A) (hB : IsMPart B) :
    Hfam μ (fun p : ι × κ => A p.1 ∩ B p.2) ≤ Hfam μ A + Hfam μ B := by
  classical
  have hrowR : ∀ i, ∑ j, (μ (A i ∩ B j)).toReal = (μ (A i)).toReal := by
    intro i
    rw [← ENNReal.toReal_sum (fun j _ => measure_ne_top μ _),
      IsMPart.sum_measure_inter μ hB (hA.measurable i)]
  have hcolR : ∀ j, ∑ i, (μ (A i ∩ B j)).toReal = (μ (B j)).toReal := by
    intro j
    have h1 : ∑ i, μ (A i ∩ B j) = μ (B j) := by
      rw [Finset.sum_congr rfl (fun i _ => by rw [Set.inter_comm])]
      exact IsMPart.sum_measure_inter μ hA (hB.measurable j)
    rw [← ENNReal.toReal_sum (fun i _ => measure_ne_top μ _), h1]
  have hsplit : ∀ q : ι × κ, (μ (A q.1 ∩ B q.2)).toReal ≤ (μ (A q.1)).toReal := by
    intro q
    exact (ENNReal.toReal_le_toReal (measure_ne_top μ _) (measure_ne_top μ _)).mpr
      (measure_mono Set.inter_subset_left)
  have hsplit' : ∀ q : ι × κ, (μ (A q.1 ∩ B q.2)).toReal ≤ (μ (B q.2)).toReal := by
    intro q
    exact (ENNReal.toReal_le_toReal (measure_ne_top μ _) (measure_ne_top μ _)).mpr
      (measure_mono Set.inter_subset_right)
  have hsum_c : ∑ q : ι × κ, (μ (A q.1 ∩ B q.2)).toReal = 1 := by
    rw [sum_prod_univ]
    rw [Finset.sum_congr rfl (fun i _ => hrowR i), hA.sum_measure_toReal μ]
  have hsum_d : ∑ q : ι × κ, (μ (A q.1)).toReal * (μ (B q.2)).toReal = 1 := by
    rw [sum_prod_univ]
    have h2 : ∀ i : ι, ∑ j : κ, (μ (A i)).toReal * (μ (B j)).toReal = (μ (A i)).toReal := by
      intro i
      rw [← Finset.mul_sum, hB.sum_measure_toReal μ, mul_one]
    rw [Finset.sum_congr rfl (fun i _ => h2 i), hA.sum_measure_toReal μ]
  have hpos : ∀ q : ι × κ, 0 < (μ (A q.1 ∩ B q.2)).toReal →
      0 < (μ (A q.1)).toReal * (μ (B q.2)).toReal := by
    intro q hq
    have h1 : (μ (A q.1)).toReal ≠ 0 := by
      intro h0
      have := hsplit q
      rw [h0] at this
      linarith
    have h2 : (μ (B q.2)).toReal ≠ 0 := by
      intro h0
      have := hsplit' q
      rw [h0] at this
      linarith
    exact mul_pos (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm h1))
      (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm h2))
  have hD := sum_mul_log_div_nonneg (fun q : ι × κ => (μ (A q.1 ∩ B q.2)).toReal)
    (fun q : ι × κ => (μ (A q.1)).toReal * (μ (B q.2)).toReal)
    (fun q => ENNReal.toReal_nonneg)
    (fun q => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    (by rw [hsum_c, hsum_d]) hpos
  have hterm : ∀ q : ι × κ,
      Real.negMulLog ((μ (A q.1 ∩ B q.2)).toReal) =
        - ((μ (A q.1 ∩ B q.2)).toReal * Real.log ((μ (A q.1)).toReal))
        - ((μ (A q.1 ∩ B q.2)).toReal * Real.log ((μ (B q.2)).toReal))
        - ((μ (A q.1 ∩ B q.2)).toReal *
            Real.log ((μ (A q.1 ∩ B q.2)).toReal / ((μ (A q.1)).toReal * (μ (B q.2)).toReal))) := by
    intro q
    rcases eq_or_lt_of_le (ENNReal.toReal_nonneg (a := μ (A q.1 ∩ B q.2))) with h0 | h0
    · have h0' : (μ (A q.1 ∩ B q.2)).toReal = 0 := h0.symm
      rw [h0']; simp
    · have ha : 0 < (μ (A q.1)).toReal := lt_of_lt_of_le h0 (hsplit q)
      have hb : 0 < (μ (B q.2)).toReal := lt_of_lt_of_le h0 (hsplit' q)
      have hab : (μ (A q.1)).toReal * (μ (B q.2)).toReal ≠ 0 :=
        ne_of_gt (mul_pos ha hb)
      have hx : (μ (A q.1 ∩ B q.2)).toReal =
          (μ (A q.1)).toReal * (μ (B q.2)).toReal *
            ((μ (A q.1 ∩ B q.2)).toReal / ((μ (A q.1)).toReal * (μ (B q.2)).toReal)) := by
        field_simp
      have hlog : Real.log ((μ (A q.1 ∩ B q.2)).toReal) =
          Real.log ((μ (A q.1)).toReal) + Real.log ((μ (B q.2)).toReal)
            + Real.log ((μ (A q.1 ∩ B q.2)).toReal /
                ((μ (A q.1)).toReal * (μ (B q.2)).toReal)) := by
        conv_lhs => rw [hx]
        rw [Real.log_mul hab (div_ne_zero (ne_of_gt h0) hab),
          Real.log_mul (ne_of_gt ha) (ne_of_gt hb)]
      simp only [Real.negMulLog_eq_neg]
      rw [hlog]
      ring
  have hAterm : ∑ q : ι × κ, (μ (A q.1 ∩ B q.2)).toReal * Real.log ((μ (A q.1)).toReal)
      = - ∑ i, Real.negMulLog ((μ (A i)).toReal) := by
    rw [sum_prod_univ]
    have hstep : ∀ i : ι,
        (∑ j : κ, (μ (A (i,j).1 ∩ B (i,j).2)).toReal * Real.log (μ (A (i,j).1)).toReal)
        = (μ (A i)).toReal * Real.log ((μ (A i)).toReal) := by
      intro i
      have hred : (∑ j : κ, (μ (A (i,j).1 ∩ B (i,j).2)).toReal * Real.log (μ (A (i,j).1)).toReal)
          = ∑ j : κ, (μ (A i ∩ B j)).toReal * Real.log ((μ (A i)).toReal) := rfl
      rw [hred, ← Finset.sum_mul, hrowR i]
    rw [Finset.sum_congr rfl (fun i _ => hstep i)]
    simp only [Real.negMulLog_eq_neg, Finset.sum_neg_distrib, neg_neg]
  have hBterm : ∑ q : ι × κ, (μ (A q.1 ∩ B q.2)).toReal * Real.log ((μ (B q.2)).toReal)
      = - ∑ j, Real.negMulLog ((μ (B j)).toReal) := by
    rw [sum_prod_univ, Finset.sum_comm]
    have hstep : ∀ j : κ,
        (∑ i : ι, (μ (A (i,j).1 ∩ B (i,j).2)).toReal * Real.log (μ (B (i,j).2)).toReal)
        = (μ (B j)).toReal * Real.log ((μ (B j)).toReal) := by
      intro j
      have hred : (∑ i : ι, (μ (A (i,j).1 ∩ B (i,j).2)).toReal * Real.log (μ (B (i,j).2)).toReal)
          = ∑ i : ι, (μ (A i ∩ B j)).toReal * Real.log ((μ (B j)).toReal) := rfl
      rw [hred, ← Finset.sum_mul, hcolR j]
    rw [Finset.sum_congr rfl (fun j _ => hstep j)]
    simp only [Real.negMulLog_eq_neg, Finset.sum_neg_distrib, neg_neg]
  have hidentity :
      Hfam μ (fun p : ι × κ => A p.1 ∩ B p.2) =
        ∑ i, Real.negMulLog ((μ (A i)).toReal) + ∑ j, Real.negMulLog ((μ (B j)).toReal)
        - ∑ q : ι × κ, (μ (A q.1 ∩ B q.2)).toReal *
            Real.log ((μ (A q.1 ∩ B q.2)).toReal / ((μ (A q.1)).toReal * (μ (B q.2)).toReal)) := by
    simp only [Hfam]
    rw [Finset.sum_congr rfl (fun q _ => hterm q), Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_neg_distrib, hAterm, hBterm]
    ring
  rw [hidentity]
  simp only [Hfam]
  linarith [hD]

end Work.EKLComp.Core
