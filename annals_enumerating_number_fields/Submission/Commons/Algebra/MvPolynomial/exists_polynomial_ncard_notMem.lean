import Mathlib.Data.Finsupp.PWO
import Submission.Commons.Order.WellQuasiOrder.exists_finset_subset_forall_le
import Submission.Commons.Combinatorics.Finset.sum_powerset_indicator
import Submission.Commons.Combinatorics.MvPolynomial.exists_polynomial_ncard_degree

noncomputable section

open Finset

namespace Commons.Algebra.MvPolynomial

/-- The upper set `{c | s ≤ c}` intersected with the degree-`t` layer is in bijection (by
translation by `s`) with the degree-`(t - s.degree)` layer. -/
private theorem ncard_degree_upper {n : ℕ} (s : Fin n →₀ ℕ) {t : ℕ} (h : s.degree ≤ t) :
    Set.ncard {c : Fin n →₀ ℕ | c.degree = t ∧ s ≤ c} =
      Set.ncard {e : Fin n →₀ ℕ | e.degree = t - s.degree} := by
  refine Set.ncard_congr' ?_
  refine
    { toFun := fun c => ⟨c.1 - s, ?_⟩
      invFun := fun e => ⟨s + e.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · obtain ⟨hct, hsc⟩ := c.2
    have h1 : c.1 = s + (c.1 - s) := (add_tsub_cancel_of_le hsc).symm
    have h3 : c.1.degree = s.degree + (c.1 - s).degree := by
      calc c.1.degree = (s + (c.1 - s)).degree := congrArg Finsupp.degree h1
        _ = s.degree + (c.1 - s).degree := map_add Finsupp.degree s (c.1 - s)
    show (c.1 - s).degree = t - s.degree
    omega
  · have het : e.1.degree = t - s.degree := e.2
    refine ⟨?_, ?_⟩
    · have hh : (s + e.1).degree = s.degree + e.1.degree := map_add Finsupp.degree s e.1
      rw [hh, het]
      exact Nat.add_sub_of_le h
    · exact le_self_add
  · intro c
    exact Subtype.ext (add_tsub_cancel_of_le c.2.2)
  · intro e
    exact Subtype.ext (add_tsub_cancel_left s e.1)

theorem exists_polynomial_ncard_notMem (n : ℕ) :
    ∀ S : Set (Fin n →₀ ℕ), ∃ p : Polynomial ℚ, ∃ N : ℕ, ∀ t : ℕ, N ≤ t →
      (Set.ncard {c : Fin n →₀ ℕ | c.degree = t ∧ ∀ s ∈ S, ¬ (s ≤ c)} : ℚ) = p.eval (t : ℚ) := by
  intro S
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- n = 0
    refine ⟨0, 1, fun t ht => ?_⟩
    have hempty : {c : Fin 0 →₀ ℕ | c.degree = t ∧ ∀ s ∈ S, ¬ (s ≤ c)} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro c hc
      rw [Set.mem_ofPred_eq] at hc
      have h0 : c.degree = 0 := by
        rw [Finsupp.degree_eq_sum]
        simp
      omega
    rw [hempty]
    simp
  · -- n ≥ 1
    obtain ⟨A, hAsub, hAcov⟩ := Commons.Order.WellQuasiOrder.exists_finset_subset_forall_le S
    obtain ⟨Q, hQ⟩ := Commons.Combinatorics.MvPolynomial.exists_polynomial_ncard_degree hn
    set p : Polynomial ℚ := ∑ T ∈ A.powerset, Polynomial.C ((-1 : ℚ) ^ T.card) *
        (Q.comp (Polynomial.X - Polynomial.C (((T.sup id).degree : ℕ) : ℚ))) with hp_def
    refine ⟨p, (A.sup id).degree, fun t ht => ?_⟩
    -- evaluation of `p`
    have hp : p.eval (t : ℚ) = ∑ T ∈ A.powerset,
        (-1 : ℚ) ^ T.card * Q.eval (((t - (T.sup id).degree : ℕ) : ℚ)) := by
      rw [hp_def, Polynomial.eval_finsetSum]
      apply Finset.sum_congr rfl
      intro T hT
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
        Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      have hTA : T ⊆ A := Finset.mem_powerset.mp hT
      have hdTle : (T.sup id).degree ≤ t :=
        le_trans (Finsupp.degree_mono (Finset.sup_mono hTA)) ht
      rw [← Nat.cast_sub hdTle]
    -- the finite set `U` of degree-`t` vectors
    set U : Finset (Fin n →₀ ℕ) := (Finsupp.finite_of_degree_eq (σ := Fin n) t).toFinset with hUdef
    have hU : (U : Set (Fin n →₀ ℕ)) = {c | c.degree = t} := by
      rw [hUdef]; exact Set.Finite.coe_toFinset _
    have hP : ∀ c : Fin n →₀ ℕ, (c ∈ U ↔ c.degree = t) := by
      intro c
      rw [← Finset.mem_coe, hU]
      exact Iff.rfl
    have hset : {c : Fin n →₀ ℕ | c.degree = t ∧ ∀ s ∈ S, ¬ (s ≤ c)}
        = {c : Fin n →₀ ℕ | c.degree = t ∧ ∀ a ∈ A, ¬ (a ≤ c)} := by
      ext c; simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun a ha => h2 a (hAsub a ha)⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun s hs hle => by
          obtain ⟨a, ha, hle'⟩ := hAcov s hs
          exact h2 a ha (le_trans hle' hle)⟩
    have hcard : (Set.ncard {c : Fin n →₀ ℕ | c.degree = t ∧ ∀ s ∈ S, ¬ (s ≤ c)} : ℚ)
        = ∑ c ∈ U, (if ∀ a ∈ A, ¬ (a ≤ c) then (1 : ℚ) else 0) := by
      rw [hset]
      have hfin : (U.filter (fun c : Fin n →₀ ℕ => ∀ a ∈ A, ¬ (a ≤ c)) : Set (Fin n →₀ ℕ))
          = {c : Fin n →₀ ℕ | c.degree = t ∧ ∀ a ∈ A, ¬ (a ≤ c)} := by
        ext c
        simp only [Finset.mem_coe, Finset.mem_filter, Set.mem_ofPred_eq, hP c]
      rw [← hfin, Set.ncard_coe_finset, Finset.card_filter]
      push_cast
      rfl
    have hsum1 : ∑ c ∈ U, (if ∀ a ∈ A, ¬ (a ≤ c) then (1 : ℚ) else 0)
        = ∑ T ∈ A.powerset, (-1 : ℚ) ^ T.card *
            (∑ c ∈ U, (if ∀ a ∈ T, a ≤ c then (1 : ℚ) else 0)) := by
      calc ∑ c ∈ U, (if ∀ a ∈ A, ¬ (a ≤ c) then (1 : ℚ) else 0)
          = ∑ c ∈ U, ∑ T ∈ A.powerset, (-1 : ℚ) ^ T.card *
              (if ∀ a ∈ T, a ≤ c then (1 : ℚ) else 0) := by
            apply Finset.sum_congr rfl
            intro c _
            rw [← Commons.Combinatorics.Finset.sum_powerset_indicator A (fun a => a ≤ c)]
        _ = ∑ T ∈ A.powerset, ∑ c ∈ U, (-1 : ℚ) ^ T.card *
              (if ∀ a ∈ T, a ≤ c then (1 : ℚ) else 0) := Finset.sum_comm
        _ = ∑ T ∈ A.powerset, (-1 : ℚ) ^ T.card *
              (∑ c ∈ U, (if ∀ a ∈ T, a ≤ c then (1 : ℚ) else 0)) := by
            apply Finset.sum_congr rfl
            intro T _
            rw [Finset.mul_sum]
    have hsum2 : ∀ T ∈ A.powerset, (∑ c ∈ U, (if ∀ a ∈ T, a ≤ c then (1 : ℚ) else 0))
        = Q.eval (((t - (T.sup id).degree : ℕ) : ℚ)) := by
      intro T hT
      have hTA : T ⊆ A := Finset.mem_powerset.mp hT
      have hdTle : (T.sup id).degree ≤ t :=
        le_trans (Finsupp.degree_mono (Finset.sup_mono hTA)) ht
      have h1 : (∑ c ∈ U, (if ∀ a ∈ T, a ≤ c then (1 : ℚ) else 0))
          = ((U.filter (fun c : Fin n →₀ ℕ => ∀ a ∈ T, a ≤ c)).card : ℚ) := by
        rw [Finset.card_filter]
        push_cast
        rfl
      have hseteq : (U.filter (fun c : Fin n →₀ ℕ => ∀ a ∈ T, a ≤ c) : Set (Fin n →₀ ℕ))
          = {c : Fin n →₀ ℕ | c.degree = t ∧ ∀ a ∈ T, a ≤ c} := by
        ext c
        simp only [Finset.mem_coe, Finset.mem_filter, Set.mem_ofPred_eq, hP c]
      have h2 : ((U.filter (fun c : Fin n →₀ ℕ => ∀ a ∈ T, a ≤ c)).card : ℚ)
          = (Set.ncard {c : Fin n →₀ ℕ | c.degree = t ∧ ∀ a ∈ T, a ≤ c} : ℚ) := by
        rw [← hseteq, Set.ncard_coe_finset]
      have h3 : {c : Fin n →₀ ℕ | c.degree = t ∧ ∀ a ∈ T, a ≤ c}
          = {c : Fin n →₀ ℕ | c.degree = t ∧ (T.sup id) ≤ c} := by
        ext c; simp only [Set.mem_ofPred_eq]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, Finset.sup_le h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, fun a ha => le_trans (Finset.le_sup (f := id) ha) h2⟩
      rw [h1, h2, h3]
      rw [show Set.ncard {c : Fin n →₀ ℕ | c.degree = t ∧ (T.sup id) ≤ c}
            = Set.ncard {e : Fin n →₀ ℕ | e.degree = t - (T.sup id).degree} from
          ncard_degree_upper (T.sup id) hdTle]
      exact hQ (t - (T.sup id).degree)
    have hL : (Set.ncard {c : Fin n →₀ ℕ | c.degree = t ∧ ∀ s ∈ S, ¬ (s ≤ c)} : ℚ)
        = ∑ T ∈ A.powerset, (-1 : ℚ) ^ T.card * Q.eval (((t - (T.sup id).degree : ℕ) : ℚ)) := by
      rw [hcard, hsum1]
      apply Finset.sum_congr rfl
      intro T hT
      rw [hsum2 T hT]
    rw [hL, ← hp]

end Commons.Algebra.MvPolynomial