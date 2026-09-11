import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Notation
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Distributions.SetBernoulli
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ChallengeDeps
import Submission.Multi

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open Classical
open MeasureTheory ProbabilityTheory Measure
open scoped BigOperators ENNReal NNReal

namespace Submission

open _root_.SupremumOfSelectorProcesses

namespace Discret1

variable {C : Type*} [Fintype C] [DecidableEq C] [MeasurableSpace C] [MeasurableSingletonClass C]

noncomputable def countVec {N : ℕ} (X : Fin N → C) (c : C) : ℕ :=
  (Finset.univ.filter (fun i : Fin N => X i = c)).card

noncomputable def atom (μ : C → ℝ≥0) : Measure C :=
  ∑ c : C, (μ c : ℝ≥0∞) • Measure.dirac c

open scoped NNReal

/-- All tuples over `Fin N` whose count vector is exactly `m`. -/
noncomputable def Tuples (N : ℕ) (m : C → ℕ) : Finset (Fin N → C) := by
  classical
  exact (Finset.univ : Finset (Fin N → C)).filter (fun t => ∀ c : C, countVec (N := N) t c = m c)

/-- Coordinatewise saturated decrement of a count vector at one coordinate. -/
def decOne (m : C → ℕ) (c : C) : C → ℕ := fun d => m d - (if d = c then 1 else 0)

@[simp] lemma mem_Tuples {N : ℕ} {m : C → ℕ} {t : Fin N → C} :
    t ∈ Tuples N m ↔ ∀ c : C, countVec (N := N) t c = m c := by
  classical
  rw [Tuples, Finset.mem_filter]
  simp

lemma decOne_eq_of_eq_zero {m : C → ℕ} {c : C} (hmc : m c = 0) : decOne m c = m := by
  funext d
  by_cases h : d = c
  · subst d
    simp [decOne, hmc]
  · simp [decOne, h]

lemma countVec_eq_sum_indicator {N : ℕ} (X : Fin N → C) (c : C) :
    countVec X c = ∑ i : Fin N, (if X i = c then 1 else 0) := by
  classical
  unfold countVec
  rw [Finset.card_eq_sum_ones]
  rw [Finset.sum_filter]

lemma sum_countVec {N : ℕ} (t : Fin N → C) : (∑ c : C, countVec t c) = N := by
  classical
  calc
    (∑ c : C, countVec t c)
        = (∑ c : C, ((Finset.univ : Finset (Fin N)).filter (fun i => t i = c)).card) := by
            simp [countVec]
    _ = ((Finset.univ : Finset (Fin N)).filter (fun i => t i ∈ (Finset.univ : Finset C))).card := by
            rw [Finset.sum_card_fiberwise_eq_card_filter (s := (Finset.univ : Finset (Fin N))) (t := (Finset.univ : Finset C)) (g := t)]
    _ = N := by simp

lemma tuples_zero (m : C → ℕ) (hm : (∑ c : C, m c) = 0) :
    (Tuples 0 m).card = 1 := by
  classical
  have hmc : ∀ c : C, m c = 0 := by
    intro c
    exact (Finset.sum_eq_zero_iff.mp hm) c (Finset.mem_univ c)
  have hcond : ∀ t : Fin 0 → C, (∀ c : C, countVec (N := 0) t c = m c) := by
    intro t c
    rw [hmc c]
    simp [countVec]
  have hf : Tuples 0 m = Finset.univ := by
    ext t
    constructor
    · intro ht
      exact Finset.mem_univ t
    · intro ht
      exact mem_Tuples.mpr (hcond t)
  rw [hf]
  simp

lemma tuples_empty_of_sum_ne {N : ℕ} {m : C → ℕ} (h : (∑ c : C, m c) ≠ N) :
    (Tuples N m).card = 0 := by
  classical
  rw [Finset.card_eq_zero]
  rw [Finset.eq_empty_iff_forall_notMem]
  intro t ht
  have hsum : (∑ c : C, countVec (N := N) t c) = (∑ c : C, m c) := by
    exact Finset.sum_congr rfl (by intro c hc; exact ((mem_Tuples.mp ht) c))
  have h2 : (∑ c : C, countVec (N := N) t c) ≠ N := by
    rwa [hsum]
  exact h2 (sum_countVec (N := N) t)

lemma countVec_cons {N : ℕ} (c : C) (t : Fin N → C) (d : C) :
    countVec (N := N + 1) (Fin.cons c t) d = countVec t d + (if c = d then 1 else 0) := by
  classical
  unfold countVec
  rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones]
  rw [Finset.sum_filter, Finset.sum_filter]
  rw [Fin.sum_univ_succ]
  simp [Fin.cons_zero]
  rw [add_comm]

lemma cons_tail_self {N : ℕ} (x : Fin (N + 1) → C) : Fin.cons (x 0) (Fin.tail x) = x := by
  exact Fin.cons_self_tail x

lemma countVec_tail {N : ℕ} (t : Fin (N + 1) → C) (d : C) :
    countVec (N := N + 1) t d = countVec (N := N) (Fin.tail t) d + (if t 0 = d then 1 else 0) := by
  classical
  rw [← cons_tail_self (N := N) t]
  rw [countVec_cons]
  simp [Fin.cons_zero]

lemma cons_mem_tuples_succ {N : ℕ} {m : C → ℕ} (hm : (∑ c : C, m c) = N + 1)
    {c : C} {t : Fin N → C} (ht : t ∈ Tuples N (decOne m c)) :
    Fin.cons c t ∈ Tuples (N + 1) m := by
  rw [mem_Tuples]
  intro d
  rw [countVec_cons]
  have htd : countVec (N := N) t d = decOne m c d := (mem_Tuples.mp ht) d
  rw [htd]
  unfold decOne
  by_cases hdc : d = c
  · subst d
    have hmc : 1 ≤ m c := by
      by_contra h0
      have hmc0 : m c = 0 := by omega
      have hne : (∑ x : C, decOne m c x) ≠ N := by
        rw [decOne_eq_of_eq_zero hmc0]
        rw [hm]
        omega
      have hempty : (Tuples N (decOne m c)).card = 0 :=
        tuples_empty_of_sum_ne (N := N) (m := decOne m c) hne
      have hEq : Tuples N (decOne m c) = ∅ := Finset.card_eq_zero.mp hempty
      exact Finset.notMem_empty t (by simpa [hEq] using ht)
    simp
    omega
  · have hne : d ≠ c := hdc
    simp [decOne, hne, hne.symm]

lemma tail_mem_tuples {N : ℕ} {m : C → ℕ} (x : Fin (N + 1) → C)
    (hx : x ∈ Tuples (N + 1) m) :
    Fin.tail x ∈ Tuples N (decOne m (x 0)) := by
  classical
  rw [mem_Tuples]
  intro d
  have hxd : countVec (N := N + 1) x d = m d := (mem_Tuples.mp hx) d
  have hsplit := countVec_tail (N := N) x d
  rw [hxd] at hsplit
  unfold decOne
  by_cases hdx : x 0 = d
  · subst d
    simp at hsplit ⊢
    omega
  · have hif : (if x 0 = d then 1 else 0) = 0 := by simp [hdx]
    have hif2 : (if d = x 0 then 1 else 0) = 0 := by
      have hdne : d ≠ x 0 := by exact fun h => hdx h.symm
      simp [hdne]
    rw [hif2]
    rw [hif] at hsplit
    omega

/-- Decomposing tuples on `N+1` coordinates by the value of the first coordinate. -/
lemma tuples_succ_card {N : ℕ} {m : C → ℕ} (hm : (∑ c : C, m c) = N + 1) :
    (Tuples (N + 1) m).card = ∑ c : C, (Tuples N (decOne m c)).card := by
  classical
  let img : C → Finset (Fin (N + 1) → C) :=
    fun c => (Tuples N (decOne m c)).image (fun t : Fin N → C => Fin.cons c t)
  have hcover : Tuples (N + 1) m = (Finset.univ : Finset C).biUnion img := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_biUnion]
      refine ⟨x 0, Finset.mem_univ _, ?_⟩
      rw [Finset.mem_image]
      refine ⟨Fin.tail x, ?_, ?_⟩
      · exact tail_mem_tuples (N := N) (m := m) x hx
      · exact (cons_tail_self (N := N) x)
    · intro hx
      rw [Finset.mem_biUnion] at hx
      rcases hx with ⟨c, hc, hx2⟩
      rw [Finset.mem_image] at hx2
      rcases hx2 with ⟨t, ht, rfl⟩
      exact cons_mem_tuples_succ (N := N) (m := m) hm ht
  rw [hcover]
  have hdisj : ((Finset.univ : Finset C) : Set C).PairwiseDisjoint img := by
    intro c hc c' hc' hne
    change Disjoint (img c) (img c')
    rw [Finset.disjoint_left]
    intro x hx hx'
    have hx0 : x 0 = c := by
      rcases (Finset.mem_image.mp hx) with ⟨t, ht, rfl⟩
      simp [Fin.cons_zero]
    have hx0' : x 0 = c' := by
      rcases (Finset.mem_image.mp hx') with ⟨t, ht, rfl⟩
      simp [Fin.cons_zero]
    exact hne (hx0.symm.trans hx0')
  rw [Finset.card_biUnion hdisj]
  simp [img]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.card_image_of_injective
  intro t t' h
  have ht := congrArg Fin.tail h
  simpa [Fin.tail_cons] using ht

lemma sum_decOne (m : C → ℕ) (c : C) (hmc : 1 ≤ m c) :
    (∑ d : C, decOne m c d) = (∑ d : C, m d) - 1 := by
  classical
  have hsplit (f : C → ℕ) : (∑ d : C, f d) = f c + ∑ d ∈ (Finset.univ.erase c), f d := by
    rw [← Finset.add_sum_erase (s := (Finset.univ : Finset C)) f (Finset.mem_univ c)]
  calc
    (∑ d : C, decOne m c d)
        = decOne m c c + ∑ d ∈ (Finset.univ.erase c), decOne m c d := hsplit (fun d => decOne m c d)
    _ = (m c - 1) + ∑ d ∈ (Finset.univ.erase c), m d := by
          congr 1
          · simp [decOne]
          · apply Finset.sum_congr rfl
            intro d hd
            have hne : d ≠ c := (Finset.mem_erase.mp hd).1
            simp [decOne, hne]
    _ = (∑ d : C, m d) - 1 := by
          rw [hsplit (fun d => m d)]
          omega

lemma prod_fact_decOne (m : C → ℕ) (c : C) (hmc : 1 ≤ m c) :
    (∏ d : C, Nat.factorial (m d)) = (m c) * ∏ d : C, Nat.factorial (decOne m c d) := by
  classical
  have hsplit (f : C → ℕ) : (∏ d : C, f d) = f c * ∏ d ∈ (Finset.univ.erase c), f d := by
    rw [← Finset.mul_prod_erase (s := (Finset.univ : Finset C)) f (Finset.mem_univ c)]
  calc
    (∏ d : C, Nat.factorial (m d))
        = Nat.factorial (m c) * ∏ d ∈ (Finset.univ.erase c), Nat.factorial (m d) := hsplit (fun d => Nat.factorial (m d))
    _ = Nat.factorial (m c) * ∏ d ∈ (Finset.univ.erase c), Nat.factorial (decOne m c d) := by
          congr 1
          apply Finset.prod_congr rfl
          intro d hd
          have hne : d ≠ c := (Finset.mem_erase.mp hd).1
          simp [decOne, hne]
    _ = (m c * Nat.factorial (m c - 1)) * ∏ d ∈ (Finset.univ.erase c), Nat.factorial (decOne m c d) := by
          congr 1
          have hfact : Nat.factorial (m c) = m c * Nat.factorial (m c - 1) := by
            have hn : (m c - 1) + 1 = m c := Nat.succ_pred_eq_of_pos hmc
            calc
              Nat.factorial (m c) = Nat.factorial ((m c - 1) + 1) := by rw [hn]
              _ = ((m c - 1) + 1) * Nat.factorial (m c - 1) := Nat.factorial_succ (m c - 1)
              _ = m c * Nat.factorial (m c - 1) := by rw [hn]
          rw [hfact]
    _ = (m c) * (Nat.factorial (m c - 1) * ∏ d ∈ (Finset.univ.erase c), Nat.factorial (decOne m c d)) := by ac_rfl
    _ = (m c) * ∏ d : C, Nat.factorial (decOne m c d) := by
          congr 1
          rw [hsplit (fun d => Nat.factorial (decOne m c d))]
          simp [decOne]

/-- Number of tuples over `Fin N` with count vector `m` equals the multinomial coefficient. -/
lemma tuples_card_mul_factorial (N : ℕ) (m : C → ℕ) (hm : (∑ c : C, m c) = N) :
    (Tuples N m).card * (∏ c : C, Nat.factorial (m c)) = Nat.factorial N := by
  classical
  induction N generalizing m with
  | zero =>
      rw [tuples_zero m hm]
      have hmc : ∀ c : C, m c = 0 := by
        intro c
        exact (Finset.sum_eq_zero_iff.mp hm) c (Finset.mem_univ c)
      simp [hmc]
  | succ N ih =>
      calc
        (Tuples (N + 1) m).card * (∏ c : C, Nat.factorial (m c))
            = (∑ c : C, (Tuples N (decOne m c)).card) * (∏ c : C, Nat.factorial (m c)) := by
                rw [tuples_succ_card hm]
        _ = ∑ c : C, ((Tuples N (decOne m c)).card * (∏ d : C, Nat.factorial (m d))) := by
                rw [Finset.sum_mul]
        _ = ∑ c : C, ((m c) * Nat.factorial N) := by
                apply Finset.sum_congr rfl
                intro c hc
                by_cases hmc0 : m c = 0
                · have hterm0 : (Tuples N (decOne m c)).card * (∏ d : C, Nat.factorial (m d)) = 0 := by
                    rw [decOne_eq_of_eq_zero hmc0]
                    have hne : (∑ x : C, m x) ≠ N := by omega
                    rw [tuples_empty_of_sum_ne (m := m) hne]
                    simp
                  rw [hterm0, hmc0]
                  simp
                · have hmc : 1 ≤ m c := by omega
                  have hdecsum : (∑ d : C, decOne m c d) = N := by
                    have hd := sum_decOne m c hmc
                    rw [hd, hm]
                    omega
                  have hIH := ih (decOne m c) hdecsum
                  have hsplit := prod_fact_decOne (m := m) (c := c) hmc
                  calc
                    (Tuples N (decOne m c)).card * (∏ d : C, Nat.factorial (m d))
                        = (Tuples N (decOne m c)).card * ((m c) * ∏ d : C, Nat.factorial (decOne m c d)) := by rw [hsplit]
                    _ = (m c) * ((Tuples N (decOne m c)).card * ∏ d : C, Nat.factorial (decOne m c d)) := by ac_rfl
                    _ = (m c) * Nat.factorial N := by rw [hIH]
        _ = (∑ c : C, m c) * Nat.factorial N := by
                rw [← Finset.sum_mul]
        _ = (N + 1) * Nat.factorial N := by rw [hm]
        _ = Nat.factorial (N + 1) := by rw [Nat.factorial_succ]

/-- Grouping the coordinate product by the values of the coordinates. -/
lemma prod_coord {N : ℕ} (t : Fin N → C) {M : Type*} [CommMonoid M] (a : C → M) :
    (∏ i : Fin N, a (t i)) = ∏ c : C, a c ^ countVec t c := by
  classical
  calc
    (∏ i : Fin N, a (t i))
        = ∏ c : C, (∏ i ∈ (Finset.univ : Finset (Fin N)) with t i = c, a c) := by
            rw [Finset.prod_fiberwise' (s := (Finset.univ : Finset (Fin N))) (g := t) (f := a)]
    _ = ∏ c : C, a c ^ countVec t c := by
            apply Finset.prod_congr rfl
            intro c hc
            rw [Finset.prod_const]
            rfl

/-- Probability of exact joint coincidence via independence. -/
lemma prob_iInter_event {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {N : ℕ}
    (X : Fin N → Ω → C) (hX : iIndepFun X P) (t : Fin N → C) :
    P (⋂ i : Fin N, {ω | X i ω = t i}) = ∏ i : Fin N, P {ω | X i ω = t i} := by
  classical
  refine iIndepFun.meas_iInter (s := fun i : Fin N => {ω | X i ω = t i}) hX ?_
  intro i
  rw [MeasurableSpace.measurableSet_comap]
  refine ⟨{t i}, measurableSet_singleton (t i), ?_⟩
  ext ω
  simp

/-- Multinomial decomposition: the probability of a count vector equals
`#tuples × ∏_c (μ c)^(m c)`. -/
lemma prob_S_eq_card_mul_prod {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {N : ℕ} (X : Fin N → Ω → C) (μ : C → ℝ≥0) (m : C → ℕ)
    (hX : iIndepFun X P) (hmeas : ∀ i : Fin N, Measurable (X i))
    (hlaw : ∀ i : Fin N, ∀ c : C, P {ω | X i ω = c} = (μ c : ℝ≥0∞)) :
    P {ω | ∀ c : C, countVec (fun i : Fin N => X i ω) c = m c}
      = ((Tuples N m).card : ℝ≥0∞) * ∏ c : C, (μ c : ℝ≥0∞) ^ m c := by
  classical
  let A : (Fin N → C) → Set Ω := fun t => ⋂ i : Fin N, {ω | X i ω = t i}
  have hS_eq : {ω | ∀ c : C, countVec (fun i : Fin N => X i ω) c = m c}
      = ⋃ t ∈ (Tuples N m : Finset (Fin N → C)), A t := by
    ext ω
    constructor
    · intro hω
      rw [show (ω ∈ (⋃ b ∈ (Tuples N m : Finset (Fin N → C)), A b))
          ↔ ∃ b, b ∈ (Tuples N m : Finset (Fin N → C)) ∧ ω ∈ A b by simp]
      refine ⟨fun i => X i ω, mem_Tuples.mpr hω, ?_⟩
      simpa [A]
    · intro hω
      rw [show (ω ∈ (⋃ b ∈ (Tuples N m : Finset (Fin N → C)), A b))
          ↔ ∃ b, b ∈ (Tuples N m : Finset (Fin N → C)) ∧ ω ∈ A b by simp] at hω
      rcases hω with ⟨t, ht, htω⟩
      have hx : ∀ i : Fin N, X i ω = t i := by simpa [A] using htω
      intro c
      have htcv : countVec t c = m c := (mem_Tuples.mp ht) c
      have heqfun : (fun i : Fin N => X i ω) = t := funext hx
      rw [heqfun, htcv]
  have hdisj : ((Tuples N m : Finset (Fin N → C)) : Set (Fin N → C)).PairwiseDisjoint A := by
    intro t ht t' ht' hne
    change Disjoint (A t) (A t')
    rw [Set.disjoint_left]
    intro ω hω hω'
    apply hne
    funext i
    have h1 : ∀ j : Fin N, X j ω = t j := by simpa [A] using hω
    have h2 : ∀ j : Fin N, X j ω = t' j := by simpa [A] using hω'
    exact (h1 i).symm.trans (h2 i)
  have hmeasA : ∀ t ∈ (Tuples N m : Finset (Fin N → C)), MeasurableSet (A t) := by
    intro t ht
    dsimp [A]
    exact MeasurableSet.iInter (fun i : Fin N => by
      have heq : {ω | X i ω = t i} = X i ⁻¹' ({t i} : Set C) := by
        ext ω
        simp
      rw [heq]
      exact MeasurableSet.preimage (measurableSet_singleton (t i)) (hmeas i))
  have hPAt : ∀ t : Fin N → C, P (A t) = ∏ i : Fin N, ((μ (t i) : ℝ≥0) : ℝ≥0∞) := by
    intro t
    calc
      P (A t) = P (⋂ i : Fin N, {ω | X i ω = t i}) := rfl
      _ = ∏ i : Fin N, P {ω | X i ω = t i} := prob_iInter_event P X hX t
      _ = ∏ i : Fin N, ((μ (t i) : ℝ≥0) : ℝ≥0∞) := by
            apply Finset.prod_congr rfl
            intro i hi
            exact hlaw i (t i)
  have hPAt' : ∀ t : Fin N → C, t ∈ Tuples N m →
      P (A t) = ∏ c : C, (μ c : ℝ≥0∞) ^ m c := by
    intro t ht
    calc
      P (A t) = ∏ i : Fin N, ((μ (t i) : ℝ≥0) : ℝ≥0∞) := hPAt t
      _ = ∏ c : C, (μ c : ℝ≥0∞) ^ countVec t c := by
            rw [prod_coord t (fun c : C => (μ c : ℝ≥0∞))]
      _ = ∏ c : C, (μ c : ℝ≥0∞) ^ m c := by
            apply Finset.prod_congr rfl
            intro c hc
            rw [(mem_Tuples.mp ht) c]
  calc
    P {ω | ∀ c : C, countVec (fun i : Fin N => X i ω) c = m c}
        = ∑ t ∈ (Tuples N m : Finset (Fin N → C)), P (A t) := by
            rw [hS_eq]
            exact measure_biUnion_finset (s := (Tuples N m : Finset (Fin N → C))) (f := A) hdisj hmeasA
    _ = ∑ t ∈ (Tuples N m : Finset (Fin N → C)), (∏ c : C, (μ c : ℝ≥0∞) ^ m c) := by
            apply Finset.sum_congr rfl
            intro t ht
            exact hPAt' t ht
    _ = ((Tuples N m).card : ℝ≥0∞) * (∏ c : C, (μ c : ℝ≥0∞) ^ m c) := by
            rw [Finset.sum_const]
            simp [nsmul_eq_mul]

/-- ENNReal assembly: from the (cast) counting identity to the multinomial formula. -/
lemma ennreal_count_mul {N : ℕ} (m : C → ℕ) (k : ℕ) (μ : C → ℝ≥0)
    (hcount : (k : ℝ≥0∞) * (∏ c : C, (Nat.factorial (m c) : ℝ≥0∞)) = (Nat.factorial N : ℝ≥0∞)) :
    (Nat.factorial N : ℝ≥0∞) * ∏ c : C, ((μ c : ℝ≥0∞) ^ m c * (Nat.factorial (m c) : ℝ≥0∞)⁻¹)
      = (k : ℝ≥0∞) * ∏ c : C, (μ c : ℝ≥0∞) ^ m c := by
  classical
  calc
    (Nat.factorial N : ℝ≥0∞) * ∏ c : C, ((μ c : ℝ≥0∞) ^ m c * (Nat.factorial (m c) : ℝ≥0∞)⁻¹)
        = (k * ∏ c : C, (Nat.factorial (m c) : ℝ≥0∞)) * ∏ c : C, ((μ c : ℝ≥0∞) ^ m c * (Nat.factorial (m c) : ℝ≥0∞)⁻¹) := by
            rw [← hcount]
    _ = k * ((∏ c : C, (Nat.factorial (m c) : ℝ≥0∞)) * ∏ c : C, ((μ c : ℝ≥0∞) ^ m c * (Nat.factorial (m c) : ℝ≥0∞)⁻¹)) := by
            rw [mul_assoc]
    _ = k * (∏ c : C, ((Nat.factorial (m c) : ℝ≥0∞) * ((μ c : ℝ≥0∞) ^ m c * (Nat.factorial (m c) : ℝ≥0∞)⁻¹))) := by
            rw [← Finset.prod_mul_distrib]
    _ = k * (∏ c : C, (((Nat.factorial (m c) : ℝ≥0∞) * (Nat.factorial (m c) : ℝ≥0∞)⁻¹) * (μ c : ℝ≥0∞) ^ m c)) := by
            congr 1
            apply Finset.prod_congr rfl
            intro c hc
            ac_rfl
    _ = k * (∏ c : C, (μ c : ℝ≥0∞) ^ m c) := by
            congr 1
            apply Finset.prod_congr rfl
            intro c hc
            rw [ENNReal.mul_inv_cancel (by exact_mod_cast (Nat.factorial_ne_zero (m c)))
              (ENNReal.natCast_ne_top (Nat.factorial (m c)))]
            simp

open scoped NNReal

theorem prob_countVec {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {N : ℕ} (X : Fin N → Ω → C) (μ : C → ℝ≥0) (m : C → ℕ)
    (hX : iIndepFun X P) (hmeas : ∀ i : Fin N, Measurable (X i))
    (hlaw : ∀ i : Fin N, ∀ c : C, P {ω | X i ω = c} = (μ c : ℝ≥0∞))
    (hm : (∑ c : C, m c) = N) :
    P {ω | ∀ c : C, countVec (fun i : Fin N => X i ω) c = m c}
      = ((Nat.factorial N : ℝ≥0∞) * ∏ c : C, (μ c : ℝ≥0∞) ^ m c * (Nat.factorial (m c) : ℝ≥0∞)⁻¹) := by
  classical
  have hPS : P {ω | ∀ c : C, countVec (fun i : Fin N => X i ω) c = m c}
      = ((Tuples N m).card : ℝ≥0∞) * ∏ c : C, (μ c : ℝ≥0∞) ^ m c := by
    exact prob_S_eq_card_mul_prod (Ω := Ω) P X μ m hX hmeas hlaw
  have hcountN : (Tuples N m).card * (∏ c : C, Nat.factorial (m c)) = Nat.factorial N :=
    tuples_card_mul_factorial N m hm
  have hcast : ((Tuples N m).card : ℝ≥0∞) * (∏ c : C, (Nat.factorial (m c) : ℝ≥0∞)) =
      (Nat.factorial N : ℝ≥0∞) := by
    exact_mod_cast hcountN
  rw [hPS]
  exact (ennreal_count_mul (m := m) (k := (Tuples N m).card) (μ := μ) hcast).symm

end Discret1
end Submission
