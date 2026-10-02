import Submission.Work.Deep.Nibble.r2_setup

set_option autoImplicit false
set_option linter.unusedVariables false
open scoped BigOperators

namespace Work.Deep.Nibble

open Work.Deep.Reed

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The expectation of an indicator is the probability of the event. -/
lemma FinProb.exp_indicator {Ω : Type*} [Fintype Ω] (μ : FinProb Ω) (P : Ω → Prop)
    [DecidablePred P] :
    μ.exp (fun ω => if P ω then (1 : ℝ) else 0) = μ.prob {ω | P ω} := by
  classical
  rw [FinProb.exp, FinProb.prob]
  exact Finset.sum_congr rfl fun ω _ => by by_cases h : P ω <;> simp [h]

/-- Probability of a disjoint finite union. -/
lemma FinProb.prob_biUnion_disjoint {Ω : Type*} [Fintype Ω] (μ : FinProb Ω) {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (A : ι → Set Ω)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (A i) (A j)) :
    μ.prob (⋃ i ∈ s, A i) = ∑ i ∈ s, μ.prob (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [FinProb.prob_empty]
  | insert a s ha ih =>
      have hdisj' : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (A i) (A j) :=
        fun i hi j hj hij => hdisj i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
      have hdisja : Disjoint (A a) (⋃ i ∈ s, A i) := by
        rw [Set.disjoint_left]
        intro x hx hxU
        simp only [Set.mem_iUnion] at hxU
        obtain ⟨i, hi, hxi⟩ := hxU
        have hne : a ≠ i := fun h => ha (h ▸ hi)
        exact (Set.disjoint_left.mp (hdisj a (Finset.mem_insert_self a s) i
          (Finset.mem_insert_of_mem hi) hne) hx) hxi
      have hunion : (⋃ i ∈ insert a s, A i) = A a ∪ (⋃ i ∈ s, A i) := by
        ext x; simp [Finset.set_biUnion_insert]
      rw [hunion, Finset.sum_insert ha]
      have h := FinProb.prob_union_add_inter μ (A a) (⋃ i ∈ s, A i)
      rw [Set.disjoint_iff_inter_eq_empty.mp hdisja, FinProb.prob_empty] at h
      rw [ih hdisj'] at h
      linarith

/-- The number of kept edges through `v` as a sum of indicators. -/
lemma kAtF_eq_sum (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (v : V) :
    kAtF 𝓖 ω v = ∑ e ∈ thruF 𝓖 v, (if ω e = true then 1 else 0) := by
  classical
  rw [kAtF, Finset.card_filter]

/-- The number of kept edges as a sum of indicators. -/
lemma keptF_card_eq_sum (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) :
    (keptF 𝓖 ω).card = ∑ e : 𝓖, (if ω e = true then 1 else 0) := by
  classical
  rw [keptF, Finset.card_filter]

/-- The number of uncovered vertices as a sum of indicators. -/
lemma uncovF_card_eq_sum (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) :
    (uncovF 𝓖 ω).card = ∑ v : V, (if ∀ e ∈ thruF 𝓖 v, ω e = false then 1 else 0) := by
  classical
  rw [uncovF, Finset.card_filter]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h : v ∉ covX 𝓖 ω
  · rw [if_pos h, if_pos ((uncovered_iff 𝓖 ω v).mp h)]
  · rw [if_neg h, if_neg (fun hc => h ((uncovered_iff 𝓖 ω v).mpr hc))]

/-- The expectation of the indicator of a coordinate being kept is `p`. -/
lemma exp_coord (𝓖 : Set (Set V)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (e : 𝓖) :
    (edgeMeasure 𝓖 p hp0 hp1).exp (fun ω => if ω e = true then (1 : ℝ) else 0) = p := by
  classical
  rw [FinProb.exp_indicator, edgeMeasure_prob_coord]

/-- The probability that a prescribed set of coordinates is kept and the rest of a finite
set of coordinates is not kept, is the product of the Bernoulli weights. -/
lemma prob_box_pattern (𝓖 : Set (Set V)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (S : Finset 𝓖) (e : 𝓖) (he : e ∈ S) :
    (edgeMeasure 𝓖 p hp0 hp1).prob
        {ω : 𝓖 → Bool | ω e = true ∧ ∀ f ∈ S.erase e, ω f = false}
      = p * (1 - p) ^ (S.card - 1) := by
  classical
  have hset : {ω : 𝓖 → Bool | ω e = true ∧ ∀ f ∈ S.erase e, ω f = false}
      = {ω : 𝓖 → Bool | ∀ f ∈ S, ω f = (decide (f = e) : Bool)} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hωe, hrest⟩ f hf
      by_cases hfe : f = e
      · simp [hfe, hωe]
      · have : ω f = false := hrest f (Finset.mem_erase.mpr ⟨hfe, hf⟩)
        simp [this, hfe]
    · intro h
      refine ⟨?_, ?_⟩
      · have := h e he
        simpa using this
      · intro f hf
        obtain ⟨hfe, hfS⟩ := Finset.mem_erase.mp hf
        have := h f hfS
        simpa [hfe] using this
  rw [hset, edgeMeasure_prob_box']
  have h1 : (if (decide (e = e) : Bool) = true then p else 1 - p) = p := by simp
  have h2 : (∏ x ∈ S.erase e, (if (decide (x = e) : Bool) = true then p else 1 - p))
      = (1 - p) ^ (S.card - 1) := by
    have hpt : ∀ x ∈ S.erase e,
        (if (decide (x = e) : Bool) = true then p else 1 - p) = (1 - p) := by
      intro x hx
      obtain ⟨hxe, -⟩ := Finset.mem_erase.mp hx
      simp [hxe]
    rw [Finset.prod_congr rfl hpt, Finset.prod_const, Finset.card_erase_of_mem he]
  rw [← Finset.insert_erase he, Finset.prod_insert (Finset.notMem_erase e S), h1, h2,
    Finset.insert_erase he]

/-- Expectation of a finite sum of real random variables. -/
lemma FinProb.exp_sum_finset {Ω : Type*} [Fintype Ω] (μ : FinProb Ω) {ι : Type*}
    (s : Finset ι) (X : ι → Ω → ℝ) :
    μ.exp (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, μ.exp (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [FinProb.exp_const]
  | insert a s ha ih =>
      have hpt : (fun ω => ∑ i ∈ insert a s, X i ω) = (fun ω => X a ω + ∑ i ∈ s, X i ω) :=
        funext fun ω => Finset.sum_insert ha
      rw [hpt, FinProb.exp_add, ih, Finset.sum_insert ha]

theorem r2_exp_basic (𝓖 : Set (Set V)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (edgeMeasure 𝓖 p hp0 hp1).exp (fun ω => ((keptF 𝓖 ω).card : ℝ)) = (Nat.card 𝓖 : ℝ) * p
  ∧ (∀ v : V, (edgeMeasure 𝓖 p hp0 hp1).prob {ω : 𝓖 → Bool | v ∉ covX 𝓖 ω}
      = (1 - p) ^ (hd 𝓖 v))
  ∧ (∀ v : V, (edgeMeasure 𝓖 p hp0 hp1).exp (fun ω => ((kAtF 𝓖 ω v : ℕ) : ℝ))
      = (hd 𝓖 v : ℝ) * p)
  ∧ (∀ v : V, (edgeMeasure 𝓖 p hp0 hp1).prob {ω : 𝓖 → Bool | kAtF 𝓖 ω v = 1}
      = (hd 𝓖 v : ℝ) * p * (1 - p) ^ (hd 𝓖 v - 1))
  ∧ ((edgeMeasure 𝓖 p hp0 hp1).exp (fun ω => ((uncovF 𝓖 ω).card : ℝ))
      = ∑ v : V, (1 - p) ^ (hd 𝓖 v)) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hpt : ∀ ω : 𝓖 → Bool, ((keptF 𝓖 ω).card : ℝ) = ∑ e : 𝓖, (if ω e = true then (1:ℝ) else 0) := by
      intro ω
      rw [keptF_card_eq_sum 𝓖 ω, Nat.cast_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      by_cases h : ω e = true <;> simp [h]
    rw [show (fun ω : 𝓖 → Bool => ((keptF 𝓖 ω).card : ℝ))
        = (fun ω => ∑ e : 𝓖, (if ω e = true then (1:ℝ) else 0)) from funext hpt]
    rw [FinProb.exp_sum]
    rw [show (∑ e : 𝓖, (edgeMeasure 𝓖 p hp0 hp1).exp (fun ω => if ω e = true then (1:ℝ) else 0))
        = ∑ _e : 𝓖, p from Finset.sum_congr rfl (fun e _ => exp_coord 𝓖 hp0 hp1 e)]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  · intro v
    have hset : {ω : 𝓖 → Bool | v ∉ covX 𝓖 ω} = {ω : 𝓖 → Bool | ∀ e ∈ thruF 𝓖 v, ω e = false} := by
      ext ω
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq, uncovered_iff]
    rw [hset, edgeMeasure_prob_unkept, hd_eq_card_thruF]
  · intro v
    have hpt : ∀ ω : 𝓖 → Bool, ((kAtF 𝓖 ω v : ℕ) : ℝ)
        = ∑ e ∈ thruF 𝓖 v, (if ω e = true then (1:ℝ) else 0) := by
      intro ω
      rw [kAtF_eq_sum 𝓖 ω v, Nat.cast_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      by_cases h : ω e = true <;> simp [h]
    rw [show (fun ω : 𝓖 → Bool => ((kAtF 𝓖 ω v : ℕ) : ℝ))
        = (fun ω => ∑ e ∈ thruF 𝓖 v, (if ω e = true then (1:ℝ) else 0)) from funext hpt]
    rw [FinProb.exp_sum_finset]
    rw [show (∑ e ∈ thruF 𝓖 v, (edgeMeasure 𝓖 p hp0 hp1).exp (fun ω => if ω e = true then (1:ℝ) else 0))
        = ∑ _e ∈ thruF 𝓖 v, p from Finset.sum_congr rfl (fun e _ => exp_coord 𝓖 hp0 hp1 e)]
    rw [Finset.sum_const, nsmul_eq_mul, hd_eq_card_thruF]
  · intro v
    have hset : {ω : 𝓖 → Bool | kAtF 𝓖 ω v = 1}
        = ⋃ e ∈ thruF 𝓖 v,
            {ω : 𝓖 → Bool | ω e = true ∧ ∀ f ∈ (thruF 𝓖 v).erase e, ω f = false} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · intro h
        obtain ⟨e, he⟩ := Finset.card_eq_one.mp h
        have hmem : e ∈ (thruF 𝓖 v).filter (fun e => ω e = true) := by
          rw [he]; exact Finset.mem_singleton_self e
        obtain ⟨heT, hωe⟩ := Finset.mem_filter.mp hmem
        refine ⟨e, heT, hωe, fun f hf => ?_⟩
        by_contra hc
        have hfmem : f ∈ (thruF 𝓖 v).filter (fun e => ω e = true) :=
          Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp hf).2, by simpa using hc⟩
        rw [he] at hfmem
        exact (Finset.mem_erase.mp hf).1 (Finset.mem_singleton.mp hfmem)
      · rintro ⟨e, heT, hωe, hrest⟩
        rw [kAtF]
        have hfil : (thruF 𝓖 v).filter (fun f => ω f = true) = {e} := by
          ext f
          rw [Finset.mem_singleton]
          constructor
          · intro hf
            obtain ⟨hfT, hωf⟩ := Finset.mem_filter.mp hf
            by_contra hfe
            have h1 : ω f = false := hrest f (Finset.mem_erase.mpr ⟨hfe, hfT⟩)
            rw [h1] at hωf
            exact Bool.noConfusion hωf
          · intro hfe
            rw [hfe]
            exact Finset.mem_filter.mpr ⟨heT, hωe⟩
        rw [hfil, Finset.card_singleton]
    have hdisj : ∀ e ∈ thruF 𝓖 v, ∀ f ∈ thruF 𝓖 v, e ≠ f →
        Disjoint {ω : 𝓖 → Bool | ω e = true ∧ ∀ g ∈ (thruF 𝓖 v).erase e, ω g = false}
          {ω : 𝓖 → Bool | ω f = true ∧ ∀ g ∈ (thruF 𝓖 v).erase f, ω g = false} := by
      intro e he f hf hef
      rw [Set.disjoint_left]
      rintro ω ⟨hωe, hrest⟩ ⟨hωf, -⟩
      have h1 : ω f = false := hrest f (Finset.mem_erase.mpr ⟨Ne.symm hef, hf⟩)
      rw [h1] at hωf
      exact Bool.noConfusion hωf
    rw [hset, FinProb.prob_biUnion_disjoint _ _ _ hdisj]
    rw [show (∑ e ∈ thruF 𝓖 v, (edgeMeasure 𝓖 p hp0 hp1).prob
            {ω : 𝓖 → Bool | ω e = true ∧ ∀ f ∈ (thruF 𝓖 v).erase e, ω f = false})
        = ∑ _e ∈ thruF 𝓖 v, p * (1 - p) ^ ((thruF 𝓖 v).card - 1) from
        Finset.sum_congr rfl (fun e he => prob_box_pattern 𝓖 hp0 hp1 (thruF 𝓖 v) e he)]
    rw [Finset.sum_const, nsmul_eq_mul, hd_eq_card_thruF]
    ring
  · have hpt : ∀ ω : 𝓖 → Bool, ((uncovF 𝓖 ω).card : ℝ)
        = ∑ v : V, (if ∀ e ∈ thruF 𝓖 v, ω e = false then (1:ℝ) else 0) := by
      intro ω
      rw [uncovF_card_eq_sum 𝓖 ω, Nat.cast_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases h : ∀ e ∈ thruF 𝓖 v, ω e = false <;> simp [h]
    rw [show (fun ω : 𝓖 → Bool => ((uncovF 𝓖 ω).card : ℝ))
        = (fun ω => ∑ v : V, (if ∀ e ∈ thruF 𝓖 v, ω e = false then (1:ℝ) else 0)) from funext hpt]
    rw [FinProb.exp_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [FinProb.exp_indicator, edgeMeasure_prob_unkept, hd_eq_card_thruF]

end Work.Deep.Nibble
