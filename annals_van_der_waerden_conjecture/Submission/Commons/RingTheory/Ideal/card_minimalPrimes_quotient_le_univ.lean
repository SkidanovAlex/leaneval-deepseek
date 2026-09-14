import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Data.Finsupp.PWO
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Star
import Mathlib.Data.Sym.NatCard
import Mathlib.GroupTheory.CosetCover
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option warn.classDefReducibility false

-- ==== from Submission.Commons.Order.WellQuasiOrder.exists_finset_subset_forall_le ====
section

namespace Commons.Order.WellQuasiOrder

open Set

/-- In a well-quasi-ordered preorder, every subset `S` admits a finite subset `A ⊆ S`
whose down-closure contains `S`: every `s ∈ S` is above some `a ∈ A`. -/
private theorem exists_finset_subset_forall_le {α : Type*} [Preorder α] [WellQuasiOrderedLE α]
    (S : Set α) : ∃ A : Finset α, (∀ a ∈ A, a ∈ S) ∧ ∀ s ∈ S, ∃ a ∈ A, a ≤ s := by
  classical
  have : WellQuasiOrderedLE (Antisymmetrization α (· ≤ ·)) :=
    Monotone.wellQuasiOrderedLE_of_wellQuasiOrderedLE_of_surjective
      (f := toAntisymmetrization (α := α) (· ≤ ·)) (toAntisymmetrization_mono (α := α))
      (fun b => ⟨ofAntisymmetrization (α := α) (· ≤ ·) b,
        toAntisymmetrization_ofAntisymmetrization (α := α) (r := (· ≤ ·)) b⟩)
  let T : Set (Antisymmetrization α (· ≤ ·)) := toAntisymmetrization (α := α) (· ≤ ·) '' S
  have hT : T.IsPWO := isPWO_of_wellQuasiOrderedLE T
  let M : Set (Antisymmetrization α (· ≤ ·)) := {m | Minimal (· ∈ T) m}
  have hanti : IsAntichain (· ≤ ·) M := by
    intro m hm m' hm' hne hle
    exact hne (le_antisymm hle (hm'.2 hm.1 hle))
  have hfin : M.Finite := hanti.finite_of_wellQuasiOrdered wellQuasiOrdered_le
  have hrep : ∀ m, m ∈ M →
      ∃ a ∈ S, toAntisymmetrization (α := α) (· ≤ ·) a = m := fun m hm => hm.1
  let A : Finset α := hfin.toFinset.attach.image
    (fun m => Classical.choose (hrep m.1 (hfin.mem_toFinset.mp m.2)))
  refine ⟨A, ?_, ?_⟩
  · intro a ha
    obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp ha
    exact (Classical.choose_spec (hrep m.1 (hfin.mem_toFinset.mp m.2))).1
  · intro s hs
    obtain ⟨m, hle, hm⟩ := hT.exists_le_minimal
      (show toAntisymmetrization (α := α) (· ≤ ·) s ∈ T from Set.mem_image_of_mem _ hs)
    have hmM : m ∈ M := hm
    refine ⟨Classical.choose (hrep m hmM), ?_, ?_⟩
    · refine Finset.mem_image.mpr ⟨⟨m, hfin.mem_toFinset.mpr hmM⟩, Finset.mem_attach _ _, ?_⟩
      rfl
    · have hqa : toAntisymmetrization (α := α) (· ≤ ·)
          (Classical.choose (hrep m hmM)) = m := (Classical.choose_spec (hrep m hmM)).2
      have h1 : toAntisymmetrization (α := α) (· ≤ ·) (Classical.choose (hrep m hmM)) ≤
          toAntisymmetrization (α := α) (· ≤ ·) s := by rw [hqa]; exact hle
      exact toAntisymmetrization_le_toAntisymmetrization_iff.mp h1

end Commons.Order.WellQuasiOrder
end


-- ==== from Submission.Commons.Combinatorics.Finset.sum_powerset_indicator ====
section

namespace Commons.Combinatorics.Finset

/-- Rational version of `Finset.sum_powerset_neg_one_pow_card`: the alternating sum of
`(-1) ^ card` over the powerset of a finset equals `1` for the empty finset and `0` otherwise. -/
private theorem sum_powerset_neg_one_pow_card_rat {α : Type*} [DecidableEq α] (x : Finset α) :
    (∑ m ∈ x.powerset, (-1 : ℚ) ^ m.card) = if x = ∅ then 1 else 0 := by
  have h := Finset.sum_powerset_neg_one_pow_card (x := x)
  have hcast : ((∑ m ∈ x.powerset, (-1 : ℤ) ^ m.card : ℤ) : ℚ)
      = ∑ m ∈ x.powerset, (-1 : ℚ) ^ m.card := by
    push_cast
    rfl
  rw [← hcast, h]
  split_ifs <;> norm_num

private theorem sum_powerset_indicator {ι : Type*} [DecidableEq ι] (s : Finset ι) (p : ι → Prop) [DecidablePred p] :
    ∑ T ∈ s.powerset, (-1 : ℚ) ^ T.card * (if ∀ i ∈ T, p i then (1 : ℚ) else 0) =
      (if ∀ i ∈ s, ¬ p i then (1 : ℚ) else 0) := by
  classical
  set A := s.filter p with hA
  have hAsub : A ⊆ s := by
    rw [hA]
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hpow : A.powerset = s.powerset.filter (· ⊆ A) := by
    ext T
    simp only [Finset.mem_powerset, Finset.mem_filter]
    exact ⟨fun h => ⟨h.trans hAsub, h⟩, fun h => h.2⟩
  have hsum :
      (∑ T ∈ s.powerset, (-1 : ℚ) ^ T.card * (if ∀ i ∈ T, p i then (1 : ℚ) else 0))
        = ∑ T ∈ A.powerset, (-1 : ℚ) ^ T.card := by
    rw [hpow, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro T hT
    have hiff : (∀ i ∈ T, p i) ↔ T ⊆ A := by
      constructor
      · intro hp i hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mp hT hi, hp i hi⟩
      · intro hTA i hi
        exact (Finset.mem_filter.mp (hTA hi)).2
    by_cases hTA : T ⊆ A
    · rw [if_pos (hiff.mpr hTA), if_pos hTA, mul_one]
    · rw [if_neg (fun h => hTA (hiff.mp h)), if_neg hTA, mul_zero]
  rw [hsum, sum_powerset_neg_one_pow_card_rat A]
  have hAempty : (∀ i ∈ s, ¬ p i) ↔ A = ∅ := by
    rw [hA]
    exact Finset.filter_eq_empty_iff.symm
  by_cases h : A = ∅
  · rw [if_pos h, if_pos (hAempty.mpr h)]
  · rw [if_neg h, if_neg (fun hh => h (hAempty.mp hh))]

end Commons.Combinatorics.Finset
end


-- ==== from Submission.Commons.Algebra.MvPowerSeries.card_finsupp_degree_eq ====
section

/-!
# The number of monomials of a given total degree

The monomials of total degree `m` in `n = Fintype.card σ` variables correspond to the
multisets of size `m` drawn from `σ` (a monomial `∏ xᵢ ^ dᵢ` is determined by the multiset
in which `xᵢ` occurs `dᵢ` times).  This file makes that bijection explicit, giving the
stars-and-bars count `(n + m - 1).choose m`.
-/

namespace Commons.Algebra.MvPowerSeries

/-- A finitely supported function `d : σ →₀ ℕ` has finsupp-sum with `id` equal to its
`Finsupp.degree` (both are the sum of the values over the support). -/
private lemma finsupp_sum_id_eq_degree {σ : Type*} (d : σ →₀ ℕ) : d.sum (fun _ ↦ id) = d.degree := rfl

/-- The number of monomials of total degree exactly `m` in `Fintype.card σ` variables is
`(Fintype.card σ + m - 1).choose m`. -/
private theorem card_finsupp_degree_eq (σ : Type*) [Fintype σ] [DecidableEq σ] (m : ℕ) :
    Nat.card {d : σ →₀ ℕ // d.degree = m} = (Fintype.card σ + m - 1).choose m := by
  -- `Sym σ m` is the type of multisets of size `m` over `σ`; `Sym.equivNatSum` identifies
  -- it with finitely supported maps `σ →₀ ℕ` of total mass `m`, and for `ℕ`-valued maps
  -- the total mass is the degree.
  have hdeg : ∀ d : σ →₀ ℕ, d.sum (fun _ ↦ id) = d.degree := fun d => rfl
  rw [← Nat.card_eq_fintype_card, ← Sym.natCard_sym_eq_choose σ m]
  refine Nat.card_congr (Equiv.symm ?_)
  exact (Sym.equivNatSum σ m).trans
    (Equiv.subtypeEquivRight (fun d => by rw [hdeg d]))

end Commons.Algebra.MvPowerSeries
end


-- ==== from Submission.Commons.Combinatorics.MvPolynomial.exists_polynomial_ncard_degree ====
section

namespace Commons.Combinatorics.MvPolynomial

private theorem exists_polynomial_ncard_degree {n : ℕ} (hn : 1 ≤ n) :
    ∃ Q : Polynomial ℚ, ∀ m : ℕ, (Set.ncard {c : Fin n →₀ ℕ | c.degree = m} : ℚ) = Q.eval (m : ℚ) := by
  refine ⟨Polynomial.C (((n - 1).factorial : ℚ))⁻¹ *
    (ascPochhammer ℚ (n - 1)).comp (Polynomial.X + 1), ?_⟩
  intro m
  have hcount : Set.ncard {c : Fin n →₀ ℕ | c.degree = m} = (n + m - 1).choose m := by
    rw [← Nat.card_coe_set_eq]
    change Nat.card {c : Fin n →₀ ℕ // c.degree = m} = (n + m - 1).choose m
    rw [Commons.Algebra.MvPowerSeries.card_finsupp_degree_eq (Fin n) m, Fintype.card_fin]
  rw [hcount, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp]
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  have heval : (ascPochhammer ℚ (n - 1)).eval ((m : ℚ) + 1) =
      (((m + n - 1).descFactorial (n - 1) : ℕ) : ℚ) := by
    rw [show (m : ℚ) + 1 = ((m + 1 : ℕ) : ℚ) by push_cast; ring]
    rw [ascPochhammer_nat_eq_natCast_ascFactorial]
    rw [← Nat.add_descFactorial_eq_ascFactorial' (m + 1) (n - 1)]
    rw [show (m + 1) + (n - 1) - 1 = m + n - 1 by omega]
  rw [heval]
  have hchoose : (((m + n - 1).descFactorial (n - 1) : ℕ) : ℚ) =
      ((n - 1).factorial : ℚ) * ((m + n - 1).choose (n - 1) : ℚ) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  rw [hchoose]
  have hsym : (m + n - 1).choose (n - 1) = (n + m - 1).choose m := by
    rw [Nat.add_comm n m]
    exact Nat.choose_symm_of_eq_add (by omega)
  rw [hsym]
  have hne : ((n - 1).factorial : ℚ) ≠ 0 := by positivity
  rw [inv_mul_cancel_left₀ hne]

end Commons.Combinatorics.MvPolynomial
end


-- ==== from Submission.Commons.Algebra.MvPolynomial.exists_polynomial_ncard_notMem ====
section

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

private theorem exists_polynomial_ncard_notMem (n : ℕ) :
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
end
end


-- ==== from Submission.Commons.RingTheory.Ideal.Hilbert.exists_hilbertPoly_homogeneous_quotient ====
section

open MvPolynomial
open scoped MonomialOrder

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option linter.style.longLine false

namespace Commons.RingTheory.Ideal.Hilbert

variable {k : Type*} [Field k] {n : ℕ}

/-- The set of "standard monomials" of degree `t` for `I`: monomials of total degree `t` that
are not divisible by the leading monomial (w.r.t. `degLex`) of any nonzero element of `I`. -/
private def stdSet (I : Ideal (MvPolynomial (Fin n) k)) (t : ℕ) : Set (Fin n →₀ ℕ) :=
  {c | c.degree = t ∧ ∀ b ∈ I, b ≠ 0 → ¬ (MonomialOrder.degLex.degree b ≤ c)}

/-- **Macaulay's theorem.** The dimension of the degree-`t` piece of `R ⧸ I` equals the number of
standard monomials of degree `t`. -/
private theorem finrank_homogeneous_quotient_eq_ncard_standard
    (I : Ideal (MvPolynomial (Fin n) k))
    (hI : ∀ x ∈ I, ∀ j, MvPolynomial.homogeneousComponent j x ∈ I) (t : ℕ) :
    Module.finrank k (Submodule.map (I.mkQ.restrictScalars k)
        (MvPolynomial.homogeneousSubmodule (Fin n) k t))
      = Set.ncard {c : Fin n →₀ ℕ | c.degree = t ∧ ∀ b ∈ I, b ≠ 0 →
          ¬ (MonomialOrder.degLex.degree b ≤ c)} := by
  classical
  rw [← stdSet]
  set Std : Set (Fin n →₀ ℕ) := stdSet I t with hStd
  have hStdfin : Set.Finite Std :=
    (Finsupp.finite_of_degree_eq (σ := Fin n) t).subset (fun c hc => hc.1)
  haveI : Fintype Std := hStdfin.fintype
  let q : MvPolynomial (Fin n) k →ₗ[k] MvPolynomial (Fin n) k ⧸ I := I.mkQ.restrictScalars k
  have hq : ∀ x, q x = I.mkQ x := fun x => rfl
  set W : Submodule k (MvPolynomial (Fin n) k) :=
    Submodule.span k (Set.range (fun c : Std => MvPolynomial.monomial c.1 (1 : k))) with hW
  -- linear independence of the images of the standard monomials in the quotient
  have hlin : LinearIndependent k
      (fun c : Std => q (MvPolynomial.monomial c.1 (1 : k))) := by
    rw [Fintype.linearIndependent_iff]
    intro g hsum
    set v : MvPolynomial (Fin n) k := ∑ c : Std, g c • MvPolynomial.monomial c.1 (1 : k) with hv
    have hmem : v ∈ I := by
      have h : q v = 0 := by rw [hv]; rw [map_sum]; simpa using hsum
      rw [hq, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
      exact h
    by_contra hg
    obtain ⟨c₀, hc₀⟩ := not_forall.mp hg
    have hcoeff : MvPolynomial.coeff c₀.1 v = g c₀ := by
      rw [hv, MvPolynomial.coeff_sum]
      simp only [MvPolynomial.coeff_smul, smul_eq_mul, MvPolynomial.coeff_monomial]
      rw [Finset.sum_eq_single c₀]
      · simp
      · intro c _ hc
        rw [if_neg (fun h => hc (Subtype.ext h)), mul_zero]
      · intro h; exact absurd (Finset.mem_univ c₀) h
    have hvne : v ≠ 0 := by
      intro h0
      rw [h0, MvPolynomial.coeff_zero] at hcoeff
      exact hc₀ hcoeff.symm
    have hsupport : ∀ d ∈ v.support, ∃ c : Std, c.1 = d := by
      intro d hd
      rw [MvPolynomial.mem_support_iff] at hd
      by_contra hcon
      rw [not_exists] at hcon
      apply hd
      rw [hv, MvPolynomial.coeff_sum]
      apply Finset.sum_eq_zero
      intro c _
      rw [MvPolynomial.coeff_smul, smul_eq_mul]
      rw [show MvPolynomial.coeff d (MvPolynomial.monomial c.1 (1 : k)) = 0 from ?_, mul_zero]
      rw [MvPolynomial.coeff_monomial, if_neg]
      intro h; exact hcon c h
    obtain ⟨c₁, hc₁⟩ : ∃ c : Std, c.1 = MonomialOrder.degLex.degree v := by
      refine hsupport _ ?_
      rw [MonomialOrder.degree_mem_support_iff]; exact hvne
    exact c₁.2.2 v hmem hvne (by rw [hc₁])
  have hmapW : Submodule.map q W =
      Submodule.span k (Set.range (fun c : Std => q (MvPolynomial.monomial c.1 (1 : k)))) := by
    rw [hW, Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩; exact ⟨c, rfl⟩
    · rintro ⟨c, rfl⟩; exact ⟨_, ⟨c, rfl⟩, rfl⟩
  have hfrW : Module.finrank k ↥(Submodule.map q W) = Std.ncard := by
    rw [hmapW, finrank_span_eq_card hlin]
    rw [Set.ncard_eq_toFinset_card Std hStdfin, hStdfin.card_toFinset]
  -- `W` consists of homogeneous polynomials of degree `t`
  have hWle : W ≤ MvPolynomial.homogeneousSubmodule (Fin n) k t := by
    rw [hW]
    refine Submodule.span_le.mpr ?_
    rintro x ⟨c, rfl⟩
    exact MvPolynomial.mem_homogeneousSubmodule t _ |>.mpr
      (MvPolynomial.isHomogeneous_monomial (1 : k) c.2.1)
  have hle : Submodule.map q (MvPolynomial.homogeneousSubmodule (Fin n) k t) ≤
      Submodule.map q W := by
    rintro y ⟨f, hf, rfl⟩
    have hB : ∀ b ∈ ({b : MvPolynomial (Fin n) k | b ∈ I ∧ b ≠ 0} : Set _),
        IsUnit (MonomialOrder.degLex.leadingCoeff b) := fun b hb =>
      isUnit_iff_ne_zero.mpr (MonomialOrder.leadingCoeff_ne_zero_iff.mpr hb.2)
    obtain ⟨g, r, hgr, hdeg, hstd⟩ := MonomialOrder.div_set (m := MonomialOrder.degLex)
      (R := k) (B := {b : MvPolynomial (Fin n) k | b ∈ I ∧ b ≠ 0}) hB f
    refine Submodule.mem_map.mpr ⟨MvPolynomial.homogeneousComponent t r, ?_, ?_⟩
    · rw [hW]
      rw [MvPolynomial.homogeneousComponent_apply]
      refine Submodule.sum_mem _ (fun d hd => ?_)
      rw [Finset.mem_filter] at hd
      obtain ⟨hdmem, hddeg⟩ := hd
      rw [show MvPolynomial.monomial d (MvPolynomial.coeff d r) =
        (MvPolynomial.coeff d r) • MvPolynomial.monomial d (1 : k) from by
          rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨d, hddeg, ?_⟩, rfl⟩)
      intro b hb hbne
      exact hstd d hdmem b ⟨hb, hbne⟩
    · rw [hq, hq, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      have hfr : f - r ∈ I := by
        rw [hgr, add_sub_cancel_right, Finsupp.linearCombination_apply]
        exact I.sum_mem (fun b _ => I.smul_mem (g b) b.2.1)
      have h2 : MvPolynomial.homogeneousComponent t (f - r) ∈ I := hI _ hfr t
      rw [map_sub, MvPolynomial.homogeneousComponent_eq_self
        (MvPolynomial.mem_homogeneousSubmodule t f |>.mp hf)] at h2
      simpa using I.neg_mem h2
  have hEq : Submodule.map q W = Submodule.map q (MvPolynomial.homogeneousSubmodule (Fin n) k t) :=
    le_antisymm (Submodule.map_mono hWle) hle
  rw [← hEq]
  exact hfrW

/-- The Hilbert function of the quotient of a polynomial ring by a homogeneous ideal is
eventually given by a polynomial with rational coefficients. -/
private theorem exists_hilbertPoly_homogeneous_quotient {k : Type*} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (hI : ∀ x ∈ I, ∀ j, MvPolynomial.homogeneousComponent j x ∈ I) :
    ∃ p : Polynomial ℚ, ∃ N : ℕ, ∀ t : ℕ, N ≤ t →
      (Module.finrank k (Submodule.map (I.mkQ.restrictScalars k)
        (MvPolynomial.homogeneousSubmodule (Fin n) k t)) : ℚ) = p.eval (t : ℚ) := by
  obtain ⟨p, N, hp⟩ := Commons.Algebra.MvPolynomial.exists_polynomial_ncard_notMem n
    {b : Fin n →₀ ℕ | ∃ x ∈ I, x ≠ 0 ∧ MonomialOrder.degLex.degree x = b}
  refine ⟨p, N, fun t ht => ?_⟩
  have hset : {c : Fin n →₀ ℕ | c.degree = t ∧ ∀ b ∈ I, b ≠ 0 →
        ¬ (MonomialOrder.degLex.degree b ≤ c)}
      = {c : Fin n →₀ ℕ | c.degree = t ∧
          ∀ s ∈ ({b : Fin n →₀ ℕ | ∃ x ∈ I, x ≠ 0 ∧ MonomialOrder.degLex.degree x = b} : Set _),
            ¬ (s ≤ c)} := by
    ext c
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun s hs => by
        obtain ⟨x, hx, hxne, rfl⟩ := hs
        exact h2 x hx hxne⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun b hb hbne => h2 (MonomialOrder.degLex.degree b) ⟨b, hb, hbne, rfl⟩⟩
  rw [finrank_homogeneous_quotient_eq_ncard_standard I hI t, hset]
  exact hp t ht

end Commons.RingTheory.Ideal.Hilbert
end


-- ==== from Submission.Commons.Algebra.MvPolynomial.homogeneousComponent_mul_of_isHomogeneous_right ====
section

namespace Commons.Algebra.MvPolynomial

-- The graded-algebra structure on `MvPolynomial` induced by the total degree.  Mathlib
-- deliberately does not register it globally (one may want another grading), so we bring it
-- into scope locally for the proof below.
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Multiplying a polynomial `u` on the right by a homogeneous polynomial `g` of degree `a`
shifts the homogeneous decomposition by `a`: the `(j + a)`-th homogeneous component of `u * g`
is the `j`-th homogeneous component of `u` multiplied by `g`.

This is the `MvPolynomial` analogue of the graded-ring fact
`DirectSum.coe_decompose_mul_add_of_right_mem`. -/
private theorem homogeneousComponent_mul_of_isHomogeneous_right {σ K : Type*} [CommSemiring K]
    {g : MvPolynomial σ K} {a : ℕ} (hg : g.IsHomogeneous a) (u : MvPolynomial σ K) (j : ℕ) :
    MvPolynomial.homogeneousComponent (j + a) (u * g) = MvPolynomial.homogeneousComponent j u * g := by
  classical
  -- `homogeneousComponent` is the graded projection attached to the total-degree grading.
  have hbridge : ∀ (x : MvPolynomial σ K) (i : ℕ),
      ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ K) x) i : MvPolynomial σ K) =
        MvPolynomial.homogeneousComponent i x := by
    intro x i
    rw [← MvPolynomial.decomposition.decompose'_apply]
    rfl
  have hgmem : g ∈ MvPolynomial.homogeneousSubmodule σ K a := hg
  have key : ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ K) (u * g)) (j + a) :
      MvPolynomial σ K) = (DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ K) u j :
        MvPolynomial σ K) * g :=
    DirectSum.coe_decompose_mul_add_of_right_mem (MvPolynomial.homogeneousSubmodule σ K)
      (i := j) (j := a) hgmem
  rw [hbridge, hbridge] at key
  exact key

end Commons.Algebra.MvPolynomial
end


-- ==== from Submission.Commons.RingTheory.Ideal.Hilbert.hilbertFun_bezout ====
section

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Commons.RingTheory.Ideal.Hilbert

open MvPolynomial

/-- Bezout relation for Hilbert functions: for a homogeneous ideal `I` and a homogeneous
nonzerodivisor `g` of degree `e` modulo `I`, the Hilbert function of `R ⧸ I` is the sum of
the Hilbert functions of `R ⧸ (I + (g))` and of `R ⧸ I` shifted by `e`. -/
private theorem hilbertFun_bezout {k : Type*} [Field k] {m : ℕ}
    (I : Ideal (MvPolynomial (Fin m) k))
    (hI : ∀ x ∈ I, ∀ j, MvPolynomial.homogeneousComponent j x ∈ I)
    {g : MvPolynomial (Fin m) k} {e : ℕ} (hg : g.IsHomogeneous e) (hg0 : g ≠ 0)
    (hreg : IsSMulRegular (MvPolynomial (Fin m) k ⧸ I) g) (j : ℕ) (hj : e ≤ j) :
    Module.finrank k (Submodule.map ((I ⊔ Ideal.span {g}).mkQ.restrictScalars k)
        (MvPolynomial.homogeneousSubmodule (Fin m) k j))
      + Module.finrank k (Submodule.map (I.mkQ.restrictScalars k)
        (MvPolynomial.homogeneousSubmodule (Fin m) k (j - e)))
      = Module.finrank k (Submodule.map (I.mkQ.restrictScalars k)
        (MvPolynomial.homogeneousSubmodule (Fin m) k j)) := by
  classical
  let J : Ideal (MvPolynomial (Fin m) k) := I ⊔ Ideal.span {g}
  let qI : MvPolynomial (Fin m) k →ₗ[k] (MvPolynomial (Fin m) k ⧸ I) := (I.mkQ).restrictScalars k
  let qJ : MvPolynomial (Fin m) k →ₗ[k] (MvPolynomial (Fin m) k ⧸ J) := (J.mkQ).restrictScalars k
  let Vj : Submodule k (MvPolynomial (Fin m) k) := MvPolynomial.homogeneousSubmodule (Fin m) k j
  let Vje : Submodule k (MvPolynomial (Fin m) k) := MvPolynomial.homogeneousSubmodule (Fin m) k (j - e)
  let A : Submodule k (MvPolynomial (Fin m) k ⧸ I) := Submodule.map qI Vje
  let B : Submodule k (MvPolynomial (Fin m) k ⧸ I) := Submodule.map qI Vj
  let C : Submodule k (MvPolynomial (Fin m) k ⧸ J) := Submodule.map qJ Vj
  change Module.finrank k C + Module.finrank k A = Module.finrank k B
  haveI : Module.Finite k A :=
    Module.Finite.of_fg (Submodule.FG.map qI (MvPolynomial.homogeneousSubmodule_fg (Fin m) k (j - e)))
  haveI : Module.Finite k B :=
    Module.Finite.of_fg (Submodule.FG.map qI (MvPolynomial.homogeneousSubmodule_fg (Fin m) k j))
  -- multiplication by g on the quotient R ⧸ I
  let bar_m : (MvPolynomial (Fin m) k ⧸ I) →ₗ[k] (MvPolynomial (Fin m) k ⧸ I) :=
    (g • (LinearMap.id : (MvPolynomial (Fin m) k ⧸ I) →ₗ[MvPolynomial (Fin m) k]
      (MvPolynomial (Fin m) k ⧸ I))).restrictScalars k
  have bar_m_apply : ∀ z, bar_m z = g • z := by
    intro z
    simp only [bar_m, LinearMap.restrictScalars_apply, LinearMap.smul_apply, LinearMap.id_apply]
  have qI_apply : ∀ x, qI x = Ideal.Quotient.mk I x := fun x => rfl
  have qJ_apply : ∀ x, qJ x = Ideal.Quotient.mk J x := fun x => rfl
  have qI_smul : ∀ (a r : MvPolynomial (Fin m) k), qI (a * r) = a • qI r := by
    intro a r
    show Submodule.mkQ I (a * r) = a • Submodule.mkQ I r
    rw [← smul_eq_mul]
    exact map_smul (Submodule.mkQ I) a r
  have bar_m_qI : ∀ r, bar_m (qI r) = qI (g * r) := by
    intro r
    rw [bar_m_apply, qI_smul]
  have hbar_inj : Function.Injective bar_m := by
    intro x y hxy
    rw [bar_m_apply x, bar_m_apply y] at hxy
    exact hreg hxy
  -- multiplication by g maps A into B
  have hAB : ∀ x ∈ A, bar_m x ∈ B := by
    intro x hx
    rw [Submodule.mem_map] at hx ⊢
    obtain ⟨r, hr, rfl⟩ := hx
    refine ⟨g * r, ?_, (bar_m_qI r).symm⟩
    have hr' : r.IsHomogeneous (j - e) := by
      simpa only [Vje, MvPolynomial.mem_homogeneousSubmodule] using hr
    have hgr : (g * r).IsHomogeneous (e + (j - e)) := hg.mul hr'
    rw [show e + (j - e) = j from by omega] at hgr
    simpa only [Vj, MvPolynomial.mem_homogeneousSubmodule] using hgr
  -- the quotient map π : R ⧸ I → R ⧸ J
  have hIJ : I ≤ J := le_sup_left
  let π : (MvPolynomial (Fin m) k ⧸ I) →ₗ[k] (MvPolynomial (Fin m) k ⧸ J) :=
    (Ideal.Quotient.factorₐ k hIJ).toLinearMap
  have hpi_apply : ∀ x, π (qI x) = qJ x := by
    intro x
    change (Ideal.Quotient.factorₐ k hIJ) (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J x
    rw [Ideal.Quotient.factorₐ_apply, Ideal.Quotient.factor_mk]
  have hBC : ∀ x ∈ B, π x ∈ C := by
    intro x hx
    rw [Submodule.mem_map] at hx ⊢
    obtain ⟨r, hr, rfl⟩ := hx
    exact ⟨r, hr, (hpi_apply r).symm⟩
  have hbar_ker : ∀ x ∈ A, π (bar_m x) = 0 := by
    intro x hx
    rw [Submodule.mem_map] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    rw [bar_m_qI, hpi_apply, qJ_apply]
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_right (Ideal.mul_mem_right r (Ideal.span {g}) (Ideal.mem_span_singleton_self g))
  -- inclusion of the kernel of π into B inside the image of multiplication by g
  have hker_le : π.ker ⊓ B ≤ Submodule.map bar_m A := by
    intro y hy
    rw [Submodule.mem_inf] at hy
    obtain ⟨hyker, hyB⟩ := hy
    rw [LinearMap.mem_ker] at hyker
    rw [Submodule.mem_map] at hyB
    obtain ⟨r, hrVj, hr_eq⟩ := hyB
    have hqJ : qJ r = 0 := by
      rw [← hpi_apply r, hr_eq]; exact hyker
    have hqJmk : Ideal.Quotient.mk J r = 0 := by rw [← qJ_apply r]; exact hqJ
    have hrJ : r ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hqJmk
    rw [Submodule.mem_sup] at hrJ
    obtain ⟨i, hiI, s, hs, his⟩ := hrJ
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hs
    have hrc : r = i + g * c := by rw [← his, hc]
    have hrVj' : r ∈ MvPolynomial.homogeneousSubmodule (Fin m) k j := by
      simpa only [Vj] using hrVj
    have hr_hom : MvPolynomial.homogeneousComponent j r = r := by
      have h := MvPolynomial.homogeneousComponent_of_mem (m := j) hrVj'
      simpa using h
    have hgc : MvPolynomial.homogeneousComponent j (g * c)
        = g * MvPolynomial.homogeneousComponent (j - e) c := by
      have hje : (j - e) + e = j := by omega
      calc MvPolynomial.homogeneousComponent j (g * c)
          = MvPolynomial.homogeneousComponent ((j - e) + e) (c * g) := by
            rw [mul_comm g c, hje]
        _ = MvPolynomial.homogeneousComponent (j - e) c * g :=
            Commons.Algebra.MvPolynomial.homogeneousComponent_mul_of_isHomogeneous_right hg c (j - e)
        _ = g * MvPolynomial.homogeneousComponent (j - e) c := mul_comm _ _
    have hr_eq2 : r = MvPolynomial.homogeneousComponent j i
        + g * MvPolynomial.homogeneousComponent (j - e) c := by
      have hcomp := congrArg (MvPolynomial.homogeneousComponent j) hrc
      rw [map_add, hgc, hr_hom] at hcomp
      exact hcomp
    have hc'_mem : MvPolynomial.homogeneousComponent (j - e) c ∈ Vje := by
      simp only [Vje, MvPolynomial.mem_homogeneousSubmodule]
      exact MvPolynomial.homogeneousComponent_isHomogeneous (j - e) c
    have hi_mem : MvPolynomial.homogeneousComponent j i ∈ I := hI i hiI j
    have h0 : qI (MvPolynomial.homogeneousComponent j i) = 0 := by
      rw [qI_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact hi_mem
    rw [Submodule.mem_map]
    refine ⟨qI (MvPolynomial.homogeneousComponent (j - e) c), ?_, ?_⟩
    · rw [Submodule.mem_map]
      exact ⟨_, hc'_mem, rfl⟩
    · rw [bar_m_qI, ← hr_eq, hr_eq2, map_add, h0, zero_add]
  -- the two linear maps
  let f : A →ₗ[k] B := LinearMap.restrict bar_m hAB
  have hf_ker : f.ker = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    apply Subtype.ext
    have hxval : bar_m (x : MvPolynomial (Fin m) k ⧸ I) = 0 := by
      have h : ((f x : ↥B) : MvPolynomial (Fin m) k ⧸ I) = 0 := by rw [hx]; simp
      exact h
    have : (x : MvPolynomial (Fin m) k ⧸ I) = 0 :=
      hbar_inj (by rw [hxval, bar_m_apply]; simp)
    exact this
  have hfinA : Module.finrank k A = Module.finrank k f.range := by
    have h := LinearMap.finrank_range_add_finrank_ker f
    rw [hf_ker] at h
    simp only [finrank_bot, add_zero] at h
    exact h.symm
  let hh : B →ₗ[k] C := LinearMap.restrict π hBC
  have hh_range : hh.range = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro y
    rw [LinearMap.mem_range]
    have hy : (y : MvPolynomial (Fin m) k ⧸ J) ∈ Submodule.map qJ Vj := y.property
    rw [Submodule.mem_map] at hy
    obtain ⟨r, hrVj, hr_eq⟩ := hy
    refine ⟨⟨qI r, ?_⟩, ?_⟩
    · rw [Submodule.mem_map]
      exact ⟨r, hrVj, rfl⟩
    · apply Subtype.ext
      show π (qI r) = (y : MvPolynomial (Fin m) k ⧸ J)
      rw [hpi_apply r]; exact hr_eq
  have hh_ker : hh.ker = f.range := by
    apply le_antisymm
    · intro y hy
      rw [LinearMap.mem_ker] at hy
      have hyval : π (y : MvPolynomial (Fin m) k ⧸ I) = 0 := by
        have h : ((hh y : ↥C) : MvPolynomial (Fin m) k ⧸ J) = 0 := by rw [hy]; simp
        exact h
      have hyker : (y : MvPolynomial (Fin m) k ⧸ I) ∈ π.ker :=
        LinearMap.mem_ker.mpr hyval
      have hyinf : (y : MvPolynomial (Fin m) k ⧸ I) ∈ π.ker ⊓ B :=
        Submodule.mem_inf.mpr ⟨hyker, y.property⟩
      have hmem := hker_le hyinf
      rw [Submodule.mem_map] at hmem
      obtain ⟨x, hxA, hx_eq⟩ := hmem
      rw [LinearMap.mem_range]
      refine ⟨⟨x, hxA⟩, ?_⟩
      apply Subtype.ext
      exact hx_eq
    · intro y hy
      rw [LinearMap.mem_range] at hy
      obtain ⟨x, hx⟩ := hy
      rw [LinearMap.mem_ker]
      rw [← hx]
      apply Subtype.ext
      show π (bar_m (x : MvPolynomial (Fin m) k ⧸ I)) = 0
      exact hbar_ker x.val x.property
  have hkey := LinearMap.finrank_range_add_finrank_ker hh
  rw [hh_range, finrank_top, hh_ker] at hkey
  rw [← hfinA] at hkey
  exact hkey

end Commons.RingTheory.Ideal.Hilbert
end


-- ==== from Submission.Commons.Algebra.Polynomial.coeff_comp_X_sub_C ====
section

namespace Commons.Algebra.Polynomial

/-- The `n`-th coefficient of `(X - c)^n` is `1`. -/
private theorem coeff_X_sub_C_pow_self {R : Type*} [CommRing R] (c : R) (n : ℕ) :
    ((Polynomial.X - Polynomial.C c) ^ n).coeff n = 1 := by
  nontriviality R
  have hmonic : (Polynomial.X - Polynomial.C c).Monic := Polynomial.monic_X_sub_C c
  have hnd : ((Polynomial.X - Polynomial.C c) ^ n).natDegree = n := by
    rw [hmonic.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  have := (hmonic.pow n).coeff_natDegree
  rwa [hnd] at this

/-- The `n`-th coefficient of `(X - c)^e` vanishes when `e < n`. -/
private theorem coeff_X_sub_C_pow_eq_zero {R : Type*} [CommRing R] (c : R) {e n : ℕ} (h : e < n) :
    ((Polynomial.X - Polynomial.C c) ^ e).coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  calc ((Polynomial.X - Polynomial.C c) ^ e).natDegree
      ≤ e * (Polynomial.X - Polynomial.C c).natDegree := Polynomial.natDegree_pow_le
    _ ≤ e * 1 := Nat.mul_le_mul_left e (Polynomial.natDegree_X_sub_C_le c)
    _ = e := mul_one e
    _ < n := h

/-- Translating the variable does not change the coefficient of degree `n` when `n` is at least the
degree of the polynomial: `(f (X - c)).coeff n = f.coeff n` for `n ≥ f.natDegree`. -/
private theorem coeff_comp_X_sub_C {R : Type*} [CommRing R] (f : Polynomial R) (c : R) {n : ℕ}
    (hn : f.natDegree ≤ n) : (f.comp (Polynomial.X - Polynomial.C c)).coeff n = f.coeff n := by
  rw [Polynomial.comp_eq_sum_left, Polynomial.coeff_sum, Polynomial.sum_def]
  simp only [Polynomial.coeff_C_mul]
  rw [Finset.sum_eq_single n]
  · rw [coeff_X_sub_C_pow_self, mul_one]
  · intro e he hne
    rw [coeff_X_sub_C_pow_eq_zero c
      (lt_of_le_of_ne ((Polynomial.le_natDegree_of_mem_supp e he).trans hn) hne), mul_zero]
  · intro hnmem
    rw [Polynomial.mem_support_iff] at hnmem
    rw [not_not.mp hnmem, zero_mul]

end Commons.Algebra.Polynomial
end


-- ==== from Submission.Commons.Algebra.Polynomial.coeff_nonneg_of_eventually_eval_nonneg ====
section

namespace Commons.Algebra.Polynomial

/-- A rational polynomial of degree at most `d` which takes nonnegative values at all sufficiently
large natural numbers has nonnegative coefficient of degree `d`. -/
private theorem coeff_nonneg_of_eventually_eval_nonneg {f : Polynomial ℚ} {d : ℕ}
    (hd : f.natDegree ≤ d) (hf : ∃ N, ∀ n : ℕ, N ≤ n → 0 ≤ f.eval (n : ℚ)) :
    0 ≤ f.coeff d := by
  by_contra hcon
  have hcon : f.coeff d < 0 := lt_of_not_ge hcon
  obtain ⟨N, hN⟩ := hf
  have hc : f.coeff d ≠ 0 := ne_of_lt hcon
  have hnd : f.natDegree = d := by
    rcases lt_or_ge f.natDegree d with h | h
    · exact absurd (Polynomial.coeff_eq_zero_of_natDegree_lt h) hc
    · exact le_antisymm hd h
  have hfne : f ≠ 0 := by
    intro h
    exact hc (by simp [h])
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0
    have hC : f = Polynomial.C (f.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hnd
    have := hN N le_rfl
    rw [hC, Polynomial.eval_C] at this
    linarith
  · have hdeg : 0 < f.degree := by
      rw [Polynomial.degree_eq_natDegree hfne, hnd]
      exact WithBot.coe_pos.mpr hdpos
    have hlc : f.leadingCoeff ≤ 0 := by
      rw [← Polynomial.coeff_natDegree, hnd]
      exact le_of_lt hcon
    have hlim := Polynomial.tendsto_atBot_of_leadingCoeff_nonpos f hdeg hlc
    have hev : ∀ᶠ x : ℚ in Filter.atTop, f.eval x < 0 := by
      have h1 : ∀ᶠ x : ℚ in Filter.atTop, f.eval x ≤ (-1 : ℚ) :=
        (Filter.tendsto_atBot.mp hlim) (-1)
      filter_upwards [h1] with x hx
      linarith
    obtain ⟨q, hq⟩ := Filter.eventually_atTop.mp hev
    obtain ⟨k, hk⟩ := exists_nat_ge q
    have hmax : q ≤ ((max k N : ℕ) : ℚ) := by
      have : (k : ℚ) ≤ ((max k N : ℕ) : ℚ) := by exact_mod_cast Nat.le_max_left k N
      linarith
    have hneg := hq ((max k N : ℕ) : ℚ) hmax
    have hpos := hN (max k N) (Nat.le_max_right k N)
    linarith

end Commons.Algebra.Polynomial
end


-- ==== from Submission.Commons.RingTheory.Ideal.Hilbert.sum_coeff_le_coeff_hilbertPoly ====
section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open MvPolynomial

namespace Commons.RingTheory.Ideal.Hilbert

noncomputable section

/-! ## General linear-algebra helper lemmas -/

section General

variable {k M N : Type*} [Field k] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-- Rank-nullity in the form used below. -/
private lemma finrank_map_add_finrank_inf_ker (f : M →ₗ[k] N) (V : Submodule k M) [Module.Finite k ↥V] :
    Module.finrank k ↥(Submodule.map f V) + Module.finrank k ↥(V ⊓ f.ker)
      = Module.finrank k ↥V := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict V)
  rw [LinearMap.range_domRestrict] at h
  have hker : Module.finrank k ↥((f.domRestrict V).ker)
      = Module.finrank k ↥(V ⊓ f.ker) := by
    rw [LinearMap.ker_domRestrict]
    rw [← Submodule.finrank_map_subtype_eq V (Submodule.comap V.subtype f.ker),
      Submodule.map_comap_subtype]
  rwa [hker] at h

end General

section Algebra

variable {k R : Type*} [Field k] [CommRing R] [Algebra k R]

/-- The Hilbert-function value at a graded piece `V` of the quotient by an ideal `I`: the dimension
of the image of `V` in `R ⧸ I`. -/
private def hilbertFun (I : Ideal R) (V : Submodule k R) : ℕ :=
  Module.finrank k ↥(Submodule.map (I.mkQ.restrictScalars k) V)

/-- The Hilbert-function value is the dimension of `V` minus the dimension of `V ⊓ I`. -/
private lemma hilbertFun_eq_sub (I : Ideal R) (V : Submodule k R) [Module.Finite k ↥V] :
    hilbertFun I V = Module.finrank k ↥V - Module.finrank k ↥(V ⊓ I.restrictScalars k) := by
  have h := finrank_map_add_finrank_inf_ker (I.mkQ.restrictScalars k) V
  rw [show (I.mkQ.restrictScalars k).ker = I.restrictScalars k from ?_] at h
  · exact Nat.eq_sub_of_add_eq h
  · rw [LinearMap.ker_restrictScalars, Submodule.ker_mkQ]

/-- The Hilbert function is antitone in the ideal. -/
private lemma hilbertFun_anti {I J : Ideal R} (hIJ : I ≤ J) (V : Submodule k R) [Module.Finite k ↥V] :
    hilbertFun J V ≤ hilbertFun I V := by
  rw [hilbertFun_eq_sub J V, hilbertFun_eq_sub I V]
  refine Nat.sub_le_sub_left ?_ _
  exact Submodule.finrank_mono (inf_le_inf_left V (Submodule.restrictScalars_mono k hIJ))

end Algebra

section Homogeneous

open MvPolynomial

variable {k : Type*} [Field k] {m : ℕ}

/-- The minimal primes of an ideal are pairwise incomparable. -/
private lemma not_le_of_mem_minimalPrimes {K : Ideal (MvPolynomial (Fin m) k)}
    {p q : ↥(K.minimalPrimes)} (h : p ≠ q) : ¬ (p.1 ≤ q.1) := by
  intro hle
  exact h (Subtype.ext (le_antisymm hle (q.2.2 p.2.1 hle)))

/-- A homogeneous ideal which is not contained in another ideal contains a homogeneous element
which is not in the second ideal. -/
private lemma exists_isHomogeneous_mem_notMem {K J : Ideal (MvPolynomial (Fin m) k)}
    (hK : ∀ x ∈ K, ∀ j, MvPolynomial.homogeneousComponent j x ∈ K) (h : ¬ K ≤ J) :
    ∃ (u : MvPolynomial (Fin m) k) (e : ℕ), u.IsHomogeneous e ∧ u ∈ K ∧ u ∉ J := by
  obtain ⟨x, hxK, hxJ⟩ := Set.not_subset.mp h
  by_contra hcon
  push Not at hcon
  refine hxJ ?_
  rw [← MvPolynomial.sum_homogeneousComponent x]
  exact Ideal.sum_mem J fun j _ =>
    hcon (MvPolynomial.homogeneousComponent j x) j
      (MvPolynomial.homogeneousComponent_isHomogeneous j x) (hK x hxK j)

/-- For a homogeneous minimal prime `q` of a homogeneous ideal, there is a homogeneous element
which lies in every other minimal prime but not in `q`. -/
private lemma exists_isHomogeneous_mem_forall_mem_notMem {K : Ideal (MvPolynomial (Fin m) k)}
    (hq : ∀ q ∈ K.minimalPrimes, ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q)
    [Fintype ↥(K.minimalPrimes)] (q : ↥(K.minimalPrimes)) :
    ∃ (u : MvPolynomial (Fin m) k) (e : ℕ), u.IsHomogeneous e ∧
      (∀ q' : ↥(K.minimalPrimes), q' ≠ q → u ∈ (q'.1 : Ideal _)) ∧ u ∉ (q.1 : Ideal _) := by
  classical
  haveI : (q.1 : Ideal (MvPolynomial (Fin m) k)).IsPrime := q.2.1.1
  have hnotle : ¬ (⨅ (q' : {q' : ↥(K.minimalPrimes) // q' ≠ q}),
        (q'.1.1 : Ideal (MvPolynomial (Fin m) k))) ≤ (q.1 : Ideal _) := by
    intro hle
    have hx : ∀ (q' : ↥(K.minimalPrimes)) (h : q' ≠ q),
        ∃ x : MvPolynomial (Fin m) k, x ∈ (q'.1 : Ideal _) ∧ x ∉ (q.1 : Ideal _) := by
      intro q' h
      obtain ⟨x, hx1, hx2⟩ := Set.not_subset.mp (not_le_of_mem_minimalPrimes (p := q') (q := q) h)
      exact ⟨x, hx1, hx2⟩
    let x : (i : {q' : ↥(K.minimalPrimes) // q' ≠ q}) → MvPolynomial (Fin m) k :=
      fun i => Classical.choose (hx i.1 i.2)
    have hxmem : ∀ i, x i ∈ (i.1.1 : Ideal _) := fun i => (Classical.choose_spec (hx i.1 i.2)).1
    have hxnot : ∀ i, x i ∉ (q.1 : Ideal _) := fun i => (Classical.choose_spec (hx i.1 i.2)).2
    have hmem : (∏ i, x i) ∈ (q.1 : Ideal _) := by
      refine hle (Ideal.mem_iInf.mpr (fun i => ?_))
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem x (Finset.mem_univ i)
      rw [hc]
      exact Ideal.mul_mem_right c (i.1.1) (hxmem i)
    have hnotmem : (∏ i, x i) ∉ (q.1 : Ideal _) := by
      rw [Ideal.IsPrime.prod_mem_iff]
      rintro ⟨i, -, hi⟩
      exact hxnot i hi
    exact hnotmem hmem
  obtain ⟨u, hu, huq⟩ : ∃ u, u ∈ (⨅ (q' : {q' : ↥(K.minimalPrimes) // q' ≠ q}),
      (q'.1.1 : Ideal (MvPolynomial (Fin m) k))) ∧ u ∉ (q.1 : Ideal _) := by
    by_contra h
    push Not at h
    exact hnotle fun x hx => h x hx
  have hex : ∃ j, MvPolynomial.homogeneousComponent j u ∉ (q.1 : Ideal _) := by
    by_contra h
    push Not at h
    refine huq ?_
    rw [← MvPolynomial.sum_homogeneousComponent u]
    exact Ideal.sum_mem _ fun j _ => h j
  obtain ⟨j, hj⟩ := hex
  refine ⟨MvPolynomial.homogeneousComponent j u, j,
    MvPolynomial.homogeneousComponent_isHomogeneous j u, ?_, hj⟩
  intro q' hq'
  exact hq q'.1 q'.2 u (Ideal.mem_iInf.mp hu ⟨q', hq'⟩) j

/-- **Key inequality.** If `D q` is the degree of a homogeneous element `u q` which lies in every
minimal prime of `K` except `q` (where it does not lie), then the sum of the Hilbert functions of the
minimal primes, shifted by `D q`, is bounded by the Hilbert function of the radical `⋂ q`. -/
private lemma sum_hilbertFun_le_hilbertFun_sInf {K : Ideal (MvPolynomial (Fin m) k)}
    [Fintype ↥(K.minimalPrimes)] (D : ↥(K.minimalPrimes) → ℕ)
    (hu : ∀ q : ↥(K.minimalPrimes), ∃ u : MvPolynomial (Fin m) k, u.IsHomogeneous (D q) ∧
      (∀ q' : ↥(K.minimalPrimes), q' ≠ q → u ∈ (q'.1 : Ideal _)) ∧ u ∉ (q.1 : Ideal _))
    {t : ℕ} (hDt : ∀ q, D q ≤ t) :
    (∑ q : ↥(K.minimalPrimes),
        hilbertFun (q.1 : Ideal _) (MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q)))
      ≤ hilbertFun (sInf K.minimalPrimes) (MvPolynomial.homogeneousSubmodule (Fin m) k t) := by
  classical
  choose u hu using hu
  set A : Ideal (MvPolynomial (Fin m) k) := sInf K.minimalPrimes with hA
  haveI hfin : ∀ s, Module.Finite k ↥(MvPolynomial.homogeneousSubmodule (Fin m) k s) := fun s =>
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin m) k s)
  -- the image of a degree `t - D q` piece under multiplication by `u q` lands in degree `t`
  have hmem_cod : ∀ (q : ↥(K.minimalPrimes))
      (x : ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q))),
      A.mkQ (u q * (x : MvPolynomial (Fin m) k)) ∈
        Submodule.map (A.mkQ.restrictScalars k) (MvPolynomial.homogeneousSubmodule (Fin m) k t) := by
    intro q x
    refine Submodule.mem_map.mpr ⟨u q * (x : MvPolynomial (Fin m) k), ?_, rfl⟩
    have h3 : (u q * (x : MvPolynomial (Fin m) k)).IsHomogeneous (D q + (t - D q)) :=
      ((hu q).1).mul x.2
    rwa [Nat.add_sub_cancel' (hDt q)] at h3
  -- the component maps
  let comp : (q : ↥(K.minimalPrimes)) →
      ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q)) →ₗ[k]
        (MvPolynomial (Fin m) k ⧸ A) :=
    fun q => (A.mkQ.restrictScalars k).comp
      (((LinearMap.mulLeft (MvPolynomial (Fin m) k) (u q)).restrictScalars k).comp
        (Submodule.subtype (MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q))))
  have comp_apply : ∀ (q : ↥(K.minimalPrimes))
      (x : ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q))),
      comp q x = A.mkQ (u q * (x : MvPolynomial (Fin m) k)) := by
    intro q x
    rfl
  let Ψ : ((q : ↥(K.minimalPrimes)) →
        ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q))) →ₗ[k] (MvPolynomial (Fin m) k ⧸ A) :=
    ∑ q : ↥(K.minimalPrimes), (comp q).comp (LinearMap.proj q)
  have Ψ_apply : ∀ w : ((q : ↥(K.minimalPrimes)) →
        ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q))),
      Ψ w = ∑ q, A.mkQ (u q * (w q : MvPolynomial (Fin m) k)) := by
    intro w
    rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl (fun q _ => comp_apply q (w q))
  -- the range is contained in the degree `t` piece of `R ⧸ A`
  have hrange_le : Ψ.range ≤ Submodule.map (A.mkQ.restrictScalars k)
      (MvPolynomial.homogeneousSubmodule (Fin m) k t) := by
    rintro y ⟨w, rfl⟩
    rw [Ψ_apply w]
    exact Submodule.sum_mem _ (fun q _ => hmem_cod q (w q))
  -- the kernel is contained in the tuples with components in the corresponding minimal prime
  have hker_mem : ∀ (w : ((q : ↥(K.minimalPrimes)) →
        ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q)))), Ψ w = 0 →
      ∀ q₀ : ↥(K.minimalPrimes), ((w q₀ : ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q₀))) :
        MvPolynomial (Fin m) k) ∈ (q₀.1 : Ideal _) := by
    intro w hw q₀
    haveI : (q₀.1 : Ideal (MvPolynomial (Fin m) k)).IsPrime := q₀.2.1.1
    have hsum0 : (∑ q, A.mkQ (u q * (w q : MvPolynomial (Fin m) k))) = 0 := by
      rw [← Ψ_apply w, hw]
    have hsum : (∑ q, u q * (w q : MvPolynomial (Fin m) k)) ∈ A := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      rw [map_sum]
      exact hsum0
    have hmemA : (∑ q, u q * (w q : MvPolynomial (Fin m) k)) ∈ (q₀.1 : Ideal _) :=
      (sInf_le q₀.2 : A ≤ (q₀.1 : Ideal _)) hsum
    have hsplit : u q₀ * (w q₀ : MvPolynomial (Fin m) k)
        = (∑ q, u q * (w q : MvPolynomial (Fin m) k))
          - ∑ q ∈ Finset.univ.erase q₀, u q * (w q : MvPolynomial (Fin m) k) := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ q₀)]
      abel
    have hmem2 : (∑ q ∈ Finset.univ.erase q₀, u q * (w q : MvPolynomial (Fin m) k))
        ∈ (q₀.1 : Ideal _) := by
      refine Ideal.sum_mem _ fun q hq => ?_
      have hne : q ≠ q₀ := (Finset.mem_erase.mp hq).1
      have hmem : u q ∈ (q₀.1 : Ideal _) := (hu q).2.1 q₀ (Ne.symm hne)
      exact Ideal.mul_mem_right (w q : MvPolynomial (Fin m) k) (q₀.1) hmem
    have hprod : u q₀ * (w q₀ : MvPolynomial (Fin m) k) ∈ (q₀.1 : Ideal _) := by
      rw [hsplit]
      exact Ideal.sub_mem _ hmemA hmem2
    rcases Ideal.IsPrime.mem_or_mem q₀.2.1.1 hprod with h | h
    · exact absurd h (hu q₀).2.2
    · exact h
  -- the "kernel side": the inclusion of the tuples lying in the corresponding minimal prime
  let inc : ((q : ↥(K.minimalPrimes)) → ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q)
        ⊓ (q.1).restrictScalars k)) →ₗ[k]
      ((q : ↥(K.minimalPrimes)) → ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q))) :=
    LinearMap.pi (fun q => (Submodule.inclusion (inf_le_left)).comp (LinearMap.proj q))
  have hinc_inj : Function.Injective inc := by
    intro x y hxy
    funext q
    have h := congrFun (congrArg (fun (z : ((q : ↥(K.minimalPrimes)) →
        ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q)))) => fun q => (z q : MvPolynomial (Fin m) k)) hxy) q
    exact Subtype.ext h
  have hker_le : Ψ.ker ≤ inc.range := by
    intro w hw
    rw [LinearMap.mem_ker] at hw
    refine ⟨fun q => ⟨w q, (w q).2, hker_mem w hw q⟩, ?_⟩
    funext q
    rfl
  have hker_finrank : Module.finrank k ↥(Ψ.ker)
      ≤ ∑ q : ↥(K.minimalPrimes), Module.finrank k
          ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q) ⊓ (q.1).restrictScalars k) := by
    have hfin_inc : Module.finrank k ↥(inc.range)
        = Module.finrank k (((q : ↥(K.minimalPrimes)) →
            ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q) ⊓ (q.1).restrictScalars k))) := by
      have h := LinearMap.finrank_range_add_finrank_ker inc
      rw [show inc.ker = ⊥ from ?_] at h
      · simp only [finrank_bot, add_zero] at h; exact h
      · rw [Submodule.eq_bot_iff]
        intro x hx
        exact hinc_inj (by rw [map_zero, hx])
    calc Module.finrank k ↥(Ψ.ker) ≤ Module.finrank k ↥(inc.range) :=
          Submodule.finrank_mono hker_le
      _ = Module.finrank k (((q : ↥(K.minimalPrimes)) →
            ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q) ⊓ (q.1).restrictScalars k))) :=
          hfin_inc
      _ = ∑ q : ↥(K.minimalPrimes), Module.finrank k
            ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q) ⊓ (q.1).restrictScalars k) :=
          Module.finrank_pi_fintype k
  have hrange_finrank : Module.finrank k ↥(Ψ.range)
      ≤ Module.finrank k ↥(MvPolynomial.homogeneousSubmodule (Fin m) k t)
        - Module.finrank k ↥(MvPolynomial.homogeneousSubmodule (Fin m) k t ⊓ A.restrictScalars k) := by
    calc Module.finrank k ↥(Ψ.range)
        ≤ Module.finrank k ↥(Submodule.map (A.mkQ.restrictScalars k)
            (MvPolynomial.homogeneousSubmodule (Fin m) k t)) :=
          Submodule.finrank_mono hrange_le
      _ = Module.finrank k ↥(MvPolynomial.homogeneousSubmodule (Fin m) k t)
            - Module.finrank k ↥(MvPolynomial.homogeneousSubmodule (Fin m) k t ⊓ A.restrictScalars k) :=
          hilbertFun_eq_sub A (MvPolynomial.homogeneousSubmodule (Fin m) k t)
  have hrank := LinearMap.finrank_range_add_finrank_ker Ψ
  have hDom : Module.finrank k (((q : ↥(K.minimalPrimes)) →
      ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q))))
      = ∑ q : ↥(K.minimalPrimes), Module.finrank k
          ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q)) :=
    Module.finrank_pi_fintype k
  have key : (∑ q : ↥(K.minimalPrimes), Module.finrank k
        ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q)))
      ≤ (∑ q : ↥(K.minimalPrimes), Module.finrank k
          ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q) ⊓ (q.1).restrictScalars k))
        + (Module.finrank k ↥(MvPolynomial.homogeneousSubmodule (Fin m) k t)
            - Module.finrank k ↥(MvPolynomial.homogeneousSubmodule (Fin m) k t ⊓ A.restrictScalars k)) := by
    calc (∑ q : ↥(K.minimalPrimes), Module.finrank k
            ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q)))
        = Module.finrank k (((q : ↥(K.minimalPrimes)) →
            ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q)))) := hDom.symm
      _ = Module.finrank k ↥(Ψ.ker) + Module.finrank k ↥(Ψ.range) := by
            rw [add_comm]; exact hrank.symm
      _ ≤ _ := add_le_add hker_finrank hrange_finrank
  rw [Finset.sum_congr rfl (fun q _ => hilbertFun_eq_sub (q.1 : Ideal _) _),
    hilbertFun_eq_sub A (MvPolynomial.homogeneousSubmodule (Fin m) k t)]
  rw [Finset.sum_tsub_distrib Finset.univ (fun q _ => Submodule.finrank_mono inf_le_left)]
  exact Nat.sub_le_iff_le_add.mpr (by rw [add_comm]; exact key)

end Homogeneous

end


/-- For a homogeneous ideal `K` all of whose minimal primes have the same dimension, the sum over
the minimal primes of the degree-coefficient of the Hilbert polynomial of the quotient by that prime
is at most the corresponding degree-coefficient of the Hilbert polynomial of `S ⧸ K`.
Here the "Hilbert polynomials" are provided by the hypotheses that the Hilbert functions are
eventually given by the polynomials `P` and `Pq`. -/
private theorem sum_coeff_le_coeff_hilbertPoly {k : Type*} [Field k] {m : ℕ}
    (K : Ideal (MvPolynomial (Fin m) k))
    (hK : ∀ x ∈ K, ∀ j, MvPolynomial.homogeneousComponent j x ∈ K)
    (hq : ∀ q ∈ K.minimalPrimes, ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q)
    (P : Polynomial ℚ)
    (hP : ∃ N, ∀ t ≥ N, (Module.finrank k (Submodule.map (K.mkQ.restrictScalars k)
        (MvPolynomial.homogeneousSubmodule (Fin m) k t)) : ℚ) = P.eval (t : ℚ))
    (Pq : ↥(K.minimalPrimes) → Polynomial ℚ)
    (hPq : ∀ q, ∃ N, ∀ t ≥ N, (Module.finrank k (Submodule.map ((q.1).mkQ.restrictScalars k)
        (MvPolynomial.homogeneousSubmodule (Fin m) k t)) : ℚ) = (Pq q).eval (t : ℚ))
    (δ : ℕ) (hδ : ∀ q, (Pq q).natDegree = δ) (hPδ : P.natDegree ≤ δ)
    [Fintype ↥(K.minimalPrimes)] :
    (∑ q : ↥(K.minimalPrimes), (Pq q).coeff δ) ≤ P.coeff δ := by
  classical
  haveI hfin : ∀ s, Module.Finite k ↥(MvPolynomial.homogeneousSubmodule (Fin m) k s) := fun s =>
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin m) k s)
  -- for every minimal prime `q`, a homogeneous element lying in all the *other* minimal primes
  choose u e hue using fun q : ↥(K.minimalPrimes) =>
    exists_isHomogeneous_mem_forall_mem_notMem hq q
  -- the resulting inequality between Hilbert functions
  have hkey : ∀ t : ℕ, (∀ q : ↥(K.minimalPrimes), e q ≤ t) →
      (∑ q : ↥(K.minimalPrimes),
          Module.finrank k (Submodule.map ((q.1).mkQ.restrictScalars k)
            (MvPolynomial.homogeneousSubmodule (Fin m) k (t - e q))))
        ≤ Module.finrank k (Submodule.map (K.mkQ.restrictScalars k)
            (MvPolynomial.homogeneousSubmodule (Fin m) k t)) := by
    intro t ht
    refine le_trans (sum_hilbertFun_le_hilbertFun_sInf e (fun q => ⟨u q, hue q⟩) ht) ?_
    exact hilbertFun_anti (le_sInf (fun q hq => hq.le)) _
  obtain ⟨N, hN⟩ := hP
  choose Nq hNq using hPq
  -- the inequality of Hilbert functions, evaluated at large `t`
  have hineq : ∃ T : ℕ, ∀ t ≥ T,
      (∑ q : ↥(K.minimalPrimes), (Pq q).eval ((t - e q : ℕ) : ℚ)) ≤ P.eval (t : ℚ) := by
    refine ⟨max N (Finset.univ.sup (fun q : ↥(K.minimalPrimes) => Nq q + e q)), fun t ht => ?_⟩
    have htN : N ≤ t := le_trans (le_max_left _ _) ht
    have hbound : ∀ q : ↥(K.minimalPrimes),
        Nq q + e q ≤ Finset.univ.sup (fun q : ↥(K.minimalPrimes) => Nq q + e q) :=
      fun q => Finset.le_sup (f := fun q : ↥(K.minimalPrimes) => Nq q + e q) (Finset.mem_univ q)
    have hsupT : Finset.univ.sup (fun q : ↥(K.minimalPrimes) => Nq q + e q) ≤ t :=
      le_trans (le_max_right _ _) ht
    have he_le : ∀ q : ↥(K.minimalPrimes), Nq q ≤ t - e q := fun q => by
      have := hbound q; have := hsupT; omega
    have he_t : ∀ q : ↥(K.minimalPrimes), e q ≤ t := fun q => by
      have := hbound q; have := hsupT; omega
    have hsum_eq : (∑ q : ↥(K.minimalPrimes), (Pq q).eval ((t - e q : ℕ) : ℚ))
        = ((∑ q : ↥(K.minimalPrimes), Module.finrank k (Submodule.map ((q.1).mkQ.restrictScalars k)
            (MvPolynomial.homogeneousSubmodule (Fin m) k (t - e q))) : ℕ) : ℚ) := by
      rw [Nat.cast_sum]
      exact Finset.sum_congr rfl (fun q _ => (hNq q (t - e q) (he_le q)).symm)
    rw [hsum_eq]
    have h1 : ((∑ q : ↥(K.minimalPrimes), Module.finrank k (Submodule.map ((q.1).mkQ.restrictScalars k)
          (MvPolynomial.homogeneousSubmodule (Fin m) k (t - e q))) : ℕ) : ℚ)
        ≤ ((Module.finrank k (Submodule.map (K.mkQ.restrictScalars k)
          (MvPolynomial.homogeneousSubmodule (Fin m) k t)) : ℕ) : ℚ) := by
      exact_mod_cast hkey t he_t
    rwa [hN t htN] at h1
  obtain ⟨T, hT⟩ := hineq
  -- the polynomial whose values are the above sums
  set S : Polynomial ℚ := ∑ q : ↥(K.minimalPrimes),
    (Pq q).comp (Polynomial.X - Polynomial.C ((e q : ℕ) : ℚ)) with hS
  have hS_eval : ∀ n : ℕ, (∀ q : ↥(K.minimalPrimes), e q ≤ n) → S.eval (n : ℚ)
      = ∑ q : ↥(K.minimalPrimes), (Pq q).eval ((n - e q : ℕ) : ℚ) := by
    intro n hn
    rw [hS, Polynomial.eval_finsetSum]
    exact Finset.sum_congr rfl (fun q _ => by
      rw [Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
        Nat.cast_sub (hn q)])
  have hpoly : ∃ N' : ℕ, ∀ n : ℕ, N' ≤ n → 0 ≤ (P - S).eval (n : ℚ) := by
    refine ⟨max T (Finset.univ.sup e), fun n hn => ?_⟩
    have hnT : T ≤ n := le_trans (le_max_left _ _) hn
    have hne : ∀ q : ↥(K.minimalPrimes), e q ≤ n := fun q =>
      le_trans (Finset.le_sup (f := e) (Finset.mem_univ q)) (le_trans (le_max_right _ _) hn)
    rw [Polynomial.eval_sub, hS_eval n hne]
    exact sub_nonneg.mpr (hT n hnT)
  have hdeg : (P - S).natDegree ≤ δ := by
    refine le_trans (Polynomial.natDegree_sub_le P S) (max_le hPδ ?_)
    rw [hS]
    refine le_trans (Polynomial.natDegree_sum_le Finset.univ _) ?_
    refine Finset.sup_le (fun q _ => ?_)
    refine le_trans Polynomial.natDegree_comp_le ?_
    rw [Polynomial.natDegree_X_sub_C, mul_one]
    exact le_of_eq (hδ q)
  have hcoeff : 0 ≤ (P - S).coeff δ :=
    Commons.Algebra.Polynomial.coeff_nonneg_of_eventually_eval_nonneg hdeg hpoly
  have hScoeff : S.coeff δ = ∑ q : ↥(K.minimalPrimes), (Pq q).coeff δ := by
    rw [hS, Polynomial.finsetSum_coeff]
    exact Finset.sum_congr rfl (fun q _ =>
      Commons.Algebra.Polynomial.coeff_comp_X_sub_C (Pq q) (((e q : ℕ) : ℚ)) (le_of_eq (hδ q)))
  rw [Polynomial.coeff_sub, hScoeff, sub_nonneg] at hcoeff
  exact hcoeff

end Commons.RingTheory.Ideal.Hilbert
end


-- ==== from Submission.Commons.RingTheory.Ideal.Hilbert.localBoundPoly ====
section

namespace Commons.RingTheory.Ideal.Hilbert

/-- The `(n-1)`-st coefficient of `(X - C c)^n` is `-n*c`. -/
private theorem coeff_X_sub_C_pow_pred {R : Type*} [CommRing R] (c : R) :
    ∀ {n : ℕ}, 1 ≤ n → ((Polynomial.X - Polynomial.C c) ^ n).coeff (n - 1) = -((n : R) * c) := by
  intro n
  induction n with
  | zero => intro hn; omega
  | succ n ih =>
    intro hn
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      simp
    · have hkey := Polynomial.coeff_mul_X_sub_C
        (p := (Polynomial.X - Polynomial.C c) ^ n) (r := c) (a := n - 1)
      rw [show n - 1 + 1 = n from by omega] at hkey
      rw [show ((Polynomial.X - Polynomial.C c) ^ (n + 1))
            = (Polynomial.X - Polynomial.C c) ^ n * (Polynomial.X - Polynomial.C c)
          from pow_succ _ _]
      rw [show n + 1 - 1 = n from by omega, hkey, ih hnpos,
        Commons.Algebra.Polynomial.coeff_X_sub_C_pow_self c n]
      push_cast
      ring

/-- The `(n-1)`-st coefficient of `f.comp (X - C c)` when `f.natDegree = n ≥ 1`. -/
private theorem coeff_comp_X_sub_C_pred {R : Type*} [CommRing R] (f : Polynomial R) (c : R) {n : ℕ}
    (hn : f.natDegree = n) (hn1 : 1 ≤ n) :
    (f.comp (Polynomial.X - Polynomial.C c)).coeff (n - 1)
      = f.coeff (n - 1) - (n : R) * c * f.leadingCoeff := by
  have hle : f.eraseLead.natDegree ≤ n - 1 := by
    rcases eq_or_ne f.nextCoeff 0 with h0 | h0
    · have hh := Polynomial.natDegree_eraseLead_le_of_nextCoeff_eq_zero h0
      rw [hn] at hh; omega
    · have hh := Polynomial.natDegree_eraseLead h0
      rw [hn] at hh; omega
  have hcomp := Commons.Algebra.Polynomial.coeff_comp_X_sub_C (n := n - 1) f.eraseLead c hle
  have hdecomp : f = f.eraseLead + Polynomial.C f.leadingCoeff * Polynomial.X ^ n := by
    have h := Polynomial.eraseLead_add_C_mul_X_pow f
    rw [hn] at h
    exact h.symm
  conv_lhs => rw [hdecomp, Polynomial.add_comp, Polynomial.C_mul_comp, Polynomial.X_pow_comp]
  rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, hcomp,
    Polynomial.eraseLead_coeff_of_ne (n - 1) (by omega), coeff_X_sub_C_pow_pred c hn1]
  ring

private theorem localBoundPoly {k : Type*} [Field k] {m : ℕ}
    (K : Ideal (MvPolynomial (Fin m) k))
    (hK : ∀ x ∈ K, ∀ j, MvPolynomial.homogeneousComponent j x ∈ K)
    (hq : ∀ q ∈ K.minimalPrimes, ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q)
    (P : Polynomial ℚ)
    (hP : ∃ N, ∀ t ≥ N, (Module.finrank k (Submodule.map (K.mkQ.restrictScalars k)
        (MvPolynomial.homogeneousSubmodule (Fin m) k t)) : ℚ) = P.eval (t : ℚ))
    (Pq : ↥(K.minimalPrimes) → Polynomial ℚ)
    (hPq : ∀ q, ∃ N, ∀ t ≥ N, (Module.finrank k (Submodule.map ((q.1).mkQ.restrictScalars k)
        (MvPolynomial.homogeneousSubmodule (Fin m) k t)) : ℚ) = (Pq q).eval (t : ℚ))
    (Pp : Polynomial ℚ) (Np e : ℕ) (hNp : 1 ≤ Np) (he : 0 < e)
    (hPdeg : P.natDegree = Np - 1) (hPpdeg : Pp.natDegree = Np)
    (hbez : P = Pp - Pp.comp (Polynomial.X - Polynomial.C (e : ℚ)))
    (hdeg : ∀ q, (Pq q).natDegree = Np - 1)
    [Fintype ↥(K.minimalPrimes)] :
    (∑ q : ↥(K.minimalPrimes), (Pq q).leadingCoeff * ((Pq q).natDegree).factorial) ≤
      ((e.max 1 : ℕ) : ℚ) * Pp.leadingCoeff * Np.factorial := by
  -- the sum of the degree-`(Np-1)` coefficients of the `Pq`'s is bounded by that of `P`
  have hsum := sum_coeff_le_coeff_hilbertPoly K hK hq P hP Pq hPq (Np - 1) hdeg (le_of_eq hPdeg)
  have hcoeff_lc : ∀ q : ↥(K.minimalPrimes), (Pq q).coeff (Np - 1) = (Pq q).leadingCoeff :=
    fun q => by rw [← Polynomial.coeff_natDegree, hdeg q]
  have hP_lc : P.coeff (Np - 1) = P.leadingCoeff := by
    rw [← Polynomial.coeff_natDegree, hPdeg]
  have hsum_lc : (∑ q : ↥(K.minimalPrimes), (Pq q).leadingCoeff) ≤ P.leadingCoeff := by
    rw [Finset.sum_congr rfl (fun q _ => (hcoeff_lc q).symm), hP_lc.symm]
    exact hsum
  -- the leading coefficient of `P` in terms of that of `Pp`
  have hbez_lc : P.leadingCoeff = (e : ℚ) * (Np : ℚ) * Pp.leadingCoeff := by
    have hcomp := coeff_comp_X_sub_C_pred Pp (e : ℚ) hPpdeg hNp
    rw [← Polynomial.coeff_natDegree, hPdeg, hbez, Polynomial.coeff_sub, hcomp]
    ring
  have hLHS : (∑ q : ↥(K.minimalPrimes), (Pq q).leadingCoeff * ((Pq q).natDegree).factorial)
      = (∑ q : ↥(K.minimalPrimes), (Pq q).leadingCoeff) * ((Np - 1).factorial : ℚ) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun q _ => by rw [hdeg q])
  rw [hLHS]
  refine le_trans (mul_le_mul_of_nonneg_right hsum_lc (by positivity)) ?_
  rw [hbez_lc]
  have hemax : e.max 1 = e := Nat.max_eq_left (by omega)
  have hfac : Np.factorial = Np * (Np - 1).factorial := by
    conv_lhs => rw [← Nat.sub_add_cancel hNp]
    rw [Nat.factorial_succ, Nat.sub_add_cancel hNp]
  rw [hemax, hfac, Nat.cast_mul]
  exact le_of_eq (by ring)

end Commons.RingTheory.Ideal.Hilbert

end


-- ==== from Submission.Commons.Algebra.MvPolynomial.idealOfVars_isMaximal ====
section

namespace Commons.Algebra.MvPolynomial

/-- The ideal of variables of `MvPolynomial (Fin m) k` is the kernel of the constant coefficient
map. -/
private lemma idealOfVars_eq_ker_constantCoeff {k : Type*} [Field k] {m : ℕ} :
    MvPolynomial.idealOfVars (Fin m) k = RingHom.ker MvPolynomial.constantCoeff := by
  ext x
  rw [MvPolynomial.idealOfVars, RingHom.mem_ker, MvPolynomial.constantCoeff_eq,
    show Set.range (MvPolynomial.X : Fin m → MvPolynomial (Fin m) k)
      = MvPolynomial.X '' (Set.univ : Set (Fin m)) from by ext; simp,
    MvPolynomial.mem_ideal_span_X_image]
  constructor
  · intro h
    by_contra hc
    obtain ⟨i, -, hi⟩ := h 0 (MvPolynomial.mem_support_iff.mpr hc)
    exact hi (by simp)
  · intro h m' hm'
    have hm0 : m' ≠ 0 := by
      intro h0
      exact (MvPolynomial.mem_support_iff.mp hm') (by rw [h0]; exact h)
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hm0
    exact ⟨i, Set.mem_univ i, hi⟩

private theorem idealOfVars_isMaximal {k : Type*} [Field k] {m : ℕ} :
    (MvPolynomial.idealOfVars (Fin m) k).IsMaximal := by
  rw [idealOfVars_eq_ker_constantCoeff]
  exact RingHom.ker_isMaximal_of_surjective MvPolynomial.constantCoeff
    (fun x => ⟨MvPolynomial.C x, by simp⟩)

end Commons.Algebra.MvPolynomial
end


-- ==== from Submission.Commons.RingTheory.KrullDimension.ringKrullDim_eq_of_isIntegral ====
section

namespace Commons.RingTheory.KrullDimension

open Ideal

/-- An injective integral extension of commutative rings preserves Krull dimension. -/
private theorem ringKrullDim_eq_of_isIntegral {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] (h : Function.Injective (algebraMap A B)) :
    ringKrullDim B = ringKrullDim A := by
  -- The contraction of primes is strictly monotone, giving `dim B ≤ dim A`.
  have hstrict : StrictMono (PrimeSpectrum.comap (algebraMap A B)) := by
    intro p q hpq
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal] at hpq ⊢
    rw [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal]
    exact Ideal.IsIntegral.comap_lt_comap hpq
  have hBA : ringKrullDim B ≤ ringKrullDim A :=
    Order.krullDim_le_of_strictMono _ hstrict
  -- Going-up lifts every chain of primes of `A` to one in `B`, giving `dim A ≤ dim B`.
  have hker : Ideal.comap (algebraMap A B) (⊥ : Ideal B) = ⊥ := by
    rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp h]
  have hAB : ringKrullDim A ≤ ringKrullDim B := by
    unfold ringKrullDim Order.krullDim
    apply iSup_le
    intro p
    have hmem : Ideal.comap (algebraMap A B) (⊥ : Ideal B) ≤ (RelSeries.head p).asIdeal := by
      rw [hker]; exact bot_le
    obtain ⟨Q, -, hQprime, hQcomap⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral (R := A) (S := B)
        (RelSeries.head p).asIdeal ⊥ hmem
    obtain ⟨L, hLlen, -, -⟩ :=
      @Ideal.exists_ltSeries_of_hasGoingUp A B _ _ _ _ p Q hQprime
        (Ideal.LiesOver.mk hQcomap.symm)
    rw [← hLlen]
    exact le_iSup (fun q : LTSeries (PrimeSpectrum B) => (q.length : WithBot ℕ∞)) L
  exact le_antisymm hBA hAB

end Commons.RingTheory.KrullDimension
end


-- ==== from Submission.Commons.RingTheory.Trdeg.trdeg_fractionRing_mvPolynomial ====
section

/-!
# Transcendence degree of the fraction field of a multivariate polynomial ring

For a field `K` and a natural number `s`, the field of fractions of the polynomial ring
`K[X₁, …, X_s]` has transcendence degree exactly `s` over `K`.  The variables already
form a transcendence basis of the polynomial ring, whose transcendence degree over `K`
is `s`, and passing to the fraction field adds only algebraic elements, so it does not
change the transcendence degree.
-/

namespace Commons.RingTheory.Trdeg

open Cardinal

/-- The transcendence degree over `K` of the fraction field of `MvPolynomial (Fin s) K` is `s`. -/
private theorem trdeg_fractionRing_mvPolynomial (K : Type*) [Field K] (s : ℕ) :
    Algebra.trdeg K (FractionRing (MvPolynomial (Fin s) K)) = (s : Cardinal) := by
  -- The fraction field of `K[X₁, …, X_s]` is a localization of it, hence algebraic over it.
  have hzero : Algebra.trdeg (MvPolynomial (Fin s) K)
      (FractionRing (MvPolynomial (Fin s) K)) = 0 :=
    @trdeg_eq_zero _ _ _ _ _
      (IsLocalization.isAlgebraic (FractionRing (MvPolynomial (Fin s) K))
        (nonZeroDivisors (MvPolynomial (Fin s) K)))
  -- Transcendence degree is additive in towers.
  have hadd := trdeg_add_eq K (MvPolynomial (Fin s) K)
    (A := FractionRing (MvPolynomial (Fin s) K))
  rw [hzero, add_zero] at hadd
  -- Reduce to the transcendence degree of the polynomial ring, which is `s`.
  rw [← hadd, MvPolynomial.trdeg_of_isDomain, Cardinal.lift_mk_fin]

end Commons.RingTheory.Trdeg
end


-- ==== from Submission.Commons.RingTheory.KrullDimension.ringKrullDim_quotient_add_height_eq ====
section

open Polynomial
universe u
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
namespace Commons.RingTheory.KrullDimension

-- (from the earlier scratch file, correctly proved)
private theorem exists_ringKrullDim_eq_and_trdeg_eq (K : Type u) [Field K] (A : Type u) [CommRing A]
    [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] :
    ∃ s : ℕ, Algebra.trdeg K A = (s : Cardinal) ∧ ringKrullDim A = (s : WithBot ℕ∞) := by
  obtain ⟨s, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg K A
  letI : Algebra (MvPolynomial (Fin s) K) A := g.toRingHom.toAlgebra
  haveI : IsScalarTower K (MvPolynomial (Fin s) K) A :=
    IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  haveI : Module.Finite (MvPolynomial (Fin s) K) A := hfin
  haveI : FaithfulSMul (MvPolynomial (Fin s) K) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K) A := Algebra.IsIntegral.of_finite _ _
  refine ⟨s, ?_, ?_⟩
  · have h1 : Algebra.trdeg (MvPolynomial (Fin s) K) A = 0 :=
      trdeg_eq_zero_iff.mpr Algebra.IsIntegral.isAlgebraic
    have h2 := trdeg_add_eq K (MvPolynomial (Fin s) K) (A := A)
    rw [h1, add_zero] at h2
    rw [← h2, MvPolynomial.trdeg_of_isDomain, Cardinal.lift_mk_fin]
  · have hdim : ringKrullDim A = ringKrullDim (MvPolynomial (Fin s) K) :=
      ringKrullDim_eq_of_isIntegral hg
    rw [hdim, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      zero_add, Nat.card_eq_fintype_card, Fintype.card_fin]

section
attribute [local instance] Polynomial.algebra

private theorem height_eq_one_of_isPrime_ne_bot_of_comap_C_eq_bot {B : Type*} [CommRing B] [IsDomain B]
    (Q : Ideal B[X]) [Q.IsPrime] (hQ : Q.comap (Polynomial.C : B →+* B[X]) = ⊥) (hne : Q ≠ ⊥) :
    Q.height = 1 := by
  set M : Submonoid B[X] := (nonZeroDivisors B).map (Polynomial.C : B →+* B[X]) with hM
  haveI : IsLocalization M (FractionRing B)[X] :=
    Polynomial.isLocalization (nonZeroDivisors B) (FractionRing B)
  have hdisj : Disjoint (M : Set B[X]) (Q : Set B[X]) := by
    rw [Set.disjoint_left]
    intro x hxM hxQ
    obtain ⟨b, hb, rfl⟩ := hxM
    have hb1 : b ∈ Q.comap (Polynomial.C : B →+* B[X]) := by
      rw [Ideal.mem_comap]; exact hxQ
    rw [hQ] at hb1
    simp only [Ideal.mem_bot] at hb1
    exact one_ne_zero ((mem_nonZeroDivisors_iff.mp hb).1 1 (by rw [hb1, zero_mul]))
  rw [← IsLocalization.height_map_of_disjoint M Q (S := (FractionRing B)[X]) hdisj]
  haveI hQ' : (Q.map (algebraMap B[X] (FractionRing B)[X])).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M (FractionRing B)[X] Q inferInstance hdisj
  have hne' : Q.map (algebraMap B[X] (FractionRing B)[X]) ≠ ⊥ := by
    have hinj : Function.Injective (algebraMap B[X] (FractionRing B)[X]) := by
      rw [show (algebraMap B[X] (FractionRing B)[X]) =
        Polynomial.mapRingHom (algebraMap B (FractionRing B)) from rfl]
      exact Polynomial.map_injective _ (IsLocalization.injective (FractionRing B) le_rfl)
    intro h
    exact hne ((Ideal.map_eq_bot_iff_of_injective (I := Q) hinj).mp h)
  haveI : (Q.map (algebraMap B[X] (FractionRing B)[X])).IsMaximal := hQ'.isMaximal hne'
  exact IsPrincipalIdealRing.height_eq_one_of_isMaximal _
    (Polynomial.not_isField (FractionRing B))

private theorem ringKrullDim_quotient_polynomial_eq_of_comap_C_eq_bot {K : Type u} [Field K] {B : Type u}
    [CommRing B] [IsDomain B] [Algebra K B] [Algebra.FiniteType K B]
    (Q : Ideal B[X]) [Q.IsPrime] (hQ : Q.comap (Polynomial.C : B →+* B[X]) = ⊥) (hne : Q ≠ ⊥) :
    ringKrullDim (B[X] ⧸ Q) = ringKrullDim B := by
  set x : B[X] ⧸ Q := Ideal.Quotient.mk Q Polynomial.X with hx_def
  have haeval : Polynomial.aeval x = Ideal.Quotient.mkₐ B Q := by
    apply Polynomial.algHom_ext
    rw [Polynomial.aeval_X, Ideal.Quotient.mkₐ_eq_mk]
  have hx : IsAlgebraic B x := by
    rw [isAlgebraic_iff_not_injective]
    intro hinj
    obtain ⟨f, hfQ, hfne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    refine hfne ?_
    have h0 : Polynomial.aeval x f = 0 := by
      rw [haeval, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hfQ]
    exact hinj (by rw [h0, map_zero])
  have hTop : Algebra.adjoin B {x} = ⊤ := by
    have h1 : (Algebra.adjoin B {(Polynomial.X : B[X])}).map (Ideal.Quotient.mkₐ B Q)
        = Algebra.adjoin B {x} := AlgHom.map_adjoin_singleton _ _
    rw [← h1, Polynomial.adjoin_X (R := B), Algebra.map_top]
    exact (AlgHom.range_eq_top _).mpr (Ideal.Quotient.mkₐ_surjective B Q)
  have halg : Algebra.IsAlgebraic B (B[X] ⧸ Q) := by
    rw [Algebra.isAlgebraic_def]
    intro y
    have hle : Algebra.adjoin B {x} ≤ Subalgebra.algebraicClosure B (B[X] ⧸ Q) := by
      rw [Algebra.adjoin_le_iff]
      rintro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact (Subalgebra.mem_algebraicClosure B (B[X] ⧸ Q)).mpr hx
    exact (Subalgebra.mem_algebraicClosure B (B[X] ⧸ Q)).mp
      (hle (by rw [hTop]; trivial))
  obtain ⟨s, hs, hdim⟩ := exists_ringKrullDim_eq_and_trdeg_eq K (B[X] ⧸ Q)
  obtain ⟨t, ht, hdimt⟩ := exists_ringKrullDim_eq_and_trdeg_eq K B
  have hst : s = t := by
    have htr : Algebra.trdeg K (B[X] ⧸ Q) = Algebra.trdeg K B := by
      have hinj : Function.Injective (algebraMap B (B[X] ⧸ Q)) := by
        intro a b hab
        have hQa : Polynomial.C (a - b) ∈ Q := by
          refine Ideal.Quotient.eq_zero_iff_mem.mp ?_
          change (algebraMap B (B[X] ⧸ Q)) (a - b) = 0
          rw [map_sub, hab, sub_self]
        have hmem : a - b ∈ Q.comap (Polynomial.C : B →+* B[X]) := by
          rw [Ideal.mem_comap]; exact hQa
        rw [hQ] at hmem
        exact sub_eq_zero.mp hmem
      haveI : FaithfulSMul B (B[X] ⧸ Q) :=
        ⟨fun {m₁ m₂} h => hinj (by simpa [Algebra.algebraMap_eq_smul_one] using h 1)⟩
      have h0 : Algebra.trdeg B (B[X] ⧸ Q) = 0 := trdeg_eq_zero_iff.mpr halg
      have h2 := trdeg_add_eq K B (A := B[X] ⧸ Q)
      rw [h0, add_zero] at h2
      exact h2.symm
    rw [hs, ht] at htr
    exact Nat.cast_injective htr
  rw [hdim, hdimt, hst]


/-- The one-step dimension/height formula: for a prime `P` of `A[X]` over a finitely generated
domain `A` over a field, `ht(P) + dim(A[X]/P) = ht(P ∩ A) + dim(A/(P ∩ A)) + 1`. -/
private theorem height_add_ringKrullDim_quotient_polynomial {K : Type u} [Field K] {A : Type u}
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A]
    (P : Ideal (Polynomial A)) [P.IsPrime] :
    P.height + ringKrullDim (Polynomial A ⧸ P) =
      (P.comap (Polynomial.C : A →+* Polynomial A)).height +
        ringKrullDim (A ⧸ P.comap (Polynomial.C : A →+* Polynomial A)) + 1 := by
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  set q : Ideal A := P.comap (Polynomial.C : A →+* Polynomial A) with hqdef
  haveI hqprime : q.IsPrime := hqdef ▸ Ideal.IsPrime.comap (Polynomial.C : A →+* Polynomial A)
  set I : Ideal (Polynomial A) := q.map (Polynomial.C : A →+* Polynomial A) with hIdef
  have hle : I ≤ P := by rw [hIdef, Ideal.map_le_iff_le_comap, hqdef]
  have hIker : RingHom.ker (Polynomial.mapRingHom (Ideal.Quotient.mk q)) = I := by
    rw [Polynomial.ker_mapRingHom, Ideal.mk_ker]
  set e : Polynomial (A ⧸ q) ≃+* (Polynomial A ⧸ I) :=
    Ideal.polynomialQuotientEquivQuotientPolynomial q with hedef
  set Pb : Ideal (Polynomial A ⧸ I) := P.map (Ideal.Quotient.mk I) with hPbdef
  haveI hPbprime : Pb.IsPrime := hPbdef ▸ Ideal.isPrime_map_quotientMk_of_isPrime hle
  set g : Polynomial (A ⧸ q) →+* (Polynomial A ⧸ P) :=
    (DoubleQuot.quotQuotEquivQuotOfLE hle).toRingHom.comp
      ((Ideal.Quotient.mk Pb).comp (e : Polynomial (A ⧸ q) →+* (Polynomial A ⧸ I))) with hgdef
  set Q : Ideal (Polynomial (A ⧸ q)) := RingHom.ker g with hQdef
  haveI hQprime : Q.IsPrime := hQdef ▸ RingHom.ker_isPrime g
  have hgsurj : Function.Surjective g := by
    rw [hgdef]
    exact (DoubleQuot.quotQuotEquivQuotOfLE hle).surjective.comp
      ((Ideal.Quotient.mk_surjective).comp e.surjective)
  have hker : Q = Pb.comap (e : Polynomial (A ⧸ q) →+* (Polynomial A ⧸ I)) := by
    have h1 : g = ((DoubleQuot.quotQuotEquivQuotOfLE hle).toRingHom.comp
        (Ideal.Quotient.mk Pb)).comp (e : Polynomial (A ⧸ q) →+* (Polynomial A ⧸ I)) := by
      rw [hgdef, RingHom.comp_assoc]
    rw [hQdef, h1, ← RingHom.comap_ker]
    congr 1
    rw [← RingHom.comap_ker,
      show (DoubleQuot.quotQuotEquivQuotOfLE hle).toRingHom =
        ((DoubleQuot.quotQuotEquivQuotOfLE hle : _ ≃+* _) : _ →+* _) from rfl,
      RingHom.ker_coe_equiv, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  have hQheight : Q.height = Pb.height := by
    rw [hker]; exact RingEquiv.height_comap e Pb
  haveI hliesover : P.LiesOver q := Ideal.LiesOver.mk (by rw [hqdef, Ideal.under_def, Polynomial.algebraMap_eq])
  have hPheight : P.height = q.height + Pb.height := by
    have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (R := A) (S := Polynomial A) q P
    simpa [hPbdef, hIdef] using h
  have hdim : ringKrullDim (Polynomial (A ⧸ q) ⧸ Q) = ringKrullDim (Polynomial A ⧸ P) := by
    rw [hQdef]
    exact ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hgsurj)
  have hQcomap : Q.comap (Polynomial.C : (A ⧸ q) →+* Polynomial (A ⧸ q)) = ⊥ := by
    rw [eq_bot_iff]
    intro d hd
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective d
    rw [Ideal.mem_comap, hQdef, RingHom.mem_ker] at hd
    have hgval : g (Polynomial.C (Ideal.Quotient.mk q a)) =
        Ideal.Quotient.mk P (Polynomial.C a) := by
      rw [hgdef, RingHom.comp_apply, RingHom.comp_apply]
      have h1 : (↑e : Polynomial (A ⧸ q) →+* Polynomial A ⧸ I) (Polynomial.C (Ideal.Quotient.mk q a)) =
          Ideal.Quotient.mk I (Polynomial.C a) := by
        rw [show Polynomial.C (Ideal.Quotient.mk q a) =
          (Polynomial.C a).map (Ideal.Quotient.mk q) from by simp]
        exact Ideal.polynomialQuotientEquivQuotientPolynomial_map_mk q (Polynomial.C a)
      rw [h1]
      exact DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk (Polynomial.C a) hle
    rw [hgval, Ideal.Quotient.eq_zero_iff_mem] at hd
    rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem, hqdef, Ideal.mem_comap]
    exact hd
  by_cases hQbot : Q = ⊥
  · have hPb0 : Pb.height = 0 := by rw [← hQheight, hQbot, Ideal.height_bot]
    rw [hPheight, hPb0, ← hdim, hQbot,
      RingEquiv.ringKrullDim (RingEquiv.quotientBot (Polynomial (A ⧸ q))),
      Polynomial.ringKrullDim_of_isNoetherianRing]
    simp only [WithBot.coe_add, add_zero, zero_add]
    abel
  · have hQheight1 : Q.height = 1 :=
      height_eq_one_of_isPrime_ne_bot_of_comap_C_eq_bot Q hQcomap hQbot
    have hdimQ : ringKrullDim (Polynomial (A ⧸ q) ⧸ Q) = ringKrullDim (A ⧸ q) :=
      ringKrullDim_quotient_polynomial_eq_of_comap_C_eq_bot (K := K) (B := A ⧸ q) Q hQcomap hQbot
    have hPb1 : Pb.height = 1 := by rw [← hQheight, hQheight1]
    rw [hPheight, hPb1, ← hdim, hdimQ]
    simp only [WithBot.coe_add, WithBot.coe_one]
    abel
/-- For the polynomial ring `K[X_1,…,X_n]` over a field `K` and a prime ideal `P`, the dimension of
the quotient plus the height of `P` equals `n` (catenarity + equidimensionality of affine space). -/
private theorem ringKrullDim_quotient_add_height_eq {K : Type*} [Field K] (n : ℕ)
    (P : Ideal (MvPolynomial (Fin n) K)) [P.IsPrime] :
    ringKrullDim (MvPolynomial (Fin n) K ⧸ P) + P.height = (n : WithBot ℕ∞) := by
  induction n with
  | zero =>
    have hdim : ringKrullDim (MvPolynomial (Fin 0) K) = 0 := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
        Nat.card_eq_fintype_card, Fintype.card_fin]
      norm_num
    have h1 : P.height = 0 := by
      have h := P.height_le_ringKrullDim_of_isPrime
      rw [hdim] at h
      exact le_antisymm (WithBot.coe_le_coe.mp h) bot_le
    have h2 : ringKrullDim (MvPolynomial (Fin 0) K ⧸ P) = 0 := by
      refine le_antisymm ?_ (ringKrullDim_nonneg_of_nontrivial)
      calc ringKrullDim (MvPolynomial (Fin 0) K ⧸ P) ≤ ringKrullDim (MvPolynomial (Fin 0) K) :=
            ringKrullDim_quotient_le P
        _ = 0 := hdim
    rw [h2, h1]
    norm_num
  | succ n ih =>
    set e : MvPolynomial (Fin (n + 1)) K ≃ₐ[K] Polynomial (MvPolynomial (Fin n) K) :=
      MvPolynomial.finSuccEquiv K n with hedef
    set P' : Ideal (Polynomial (MvPolynomial (Fin n) K)) :=
      P.map (e : MvPolynomial (Fin (n + 1)) K →+* Polynomial (MvPolynomial (Fin n) K)) with hP'def
    set q : Ideal (MvPolynomial (Fin n) K) :=
      P'.comap (Polynomial.C : MvPolynomial (Fin n) K →+* Polynomial (MvPolynomial (Fin n) K))
      with hqdef
    haveI hP'prime : P'.IsPrime := by
      rw [hP'def]
      exact Ideal.map_isPrime_of_equiv
        (e : MvPolynomial (Fin (n + 1)) K ≃ₐ[K] Polynomial (MvPolynomial (Fin n) K))
    have hheight : P.height = P'.height := by
      rw [hP'def]
      exact (RingEquiv.height_map
        (e : MvPolynomial (Fin (n + 1)) K ≃+* Polynomial (MvPolynomial (Fin n) K)) P).symm
    have hdim : ringKrullDim (Polynomial (MvPolynomial (Fin n) K) ⧸ P') =
        ringKrullDim (MvPolynomial (Fin (n + 1)) K ⧸ P) := by
      rw [hP'def]
      exact (ringKrullDim_eq_of_ringEquiv
        (Ideal.quotientEquiv P (P.map (e : MvPolynomial (Fin (n + 1)) K →+*
          Polynomial (MvPolynomial (Fin n) K))) e.toRingEquiv rfl)).symm
    have hH := height_add_ringKrullDim_quotient_polynomial (K := K)
      (A := MvPolynomial (Fin n) K) P'
    have hIH := ih q
    rw [← hdim, hheight, add_comm, hH,
      add_comm (↑q.height) (ringKrullDim (MvPolynomial (Fin n) K ⧸ q)), hIH]
    simp only [WithBot.coe_add, Nat.cast_add, Nat.cast_one]

end

end Commons.RingTheory.KrullDimension
end


-- ==== from Submission.Commons.RingTheory.KrullDimension.quotient_add_one_of_mem_minimalPrimes_sup_span ====
section

/-!
# Dimension drop for minimal primes over `p + (f)`

Let `k` be a field, `A = k[X₁, …, Xₘ]` and let `p ⊆ A` be a prime ideal, `f ∉ p` with
`p + (f) ≠ ⊤`. If `q` is a minimal prime of `p + (f)`, then

`dim A ⧸ q + 1 = dim A ⧸ p`.

This is the "one step" of catenarity/equidimensionality for affine domains: in the domain
`R = A ⧸ p`, the ideal `q ⧸ p` is a minimal prime over the principal ideal generated by the
nonzero element `f mod p`, so it has height one, and quotienting by a prime of height one drops
the Krull dimension by exactly one.

The two ingredients are

* `ringKrullDim_quotient_add_height_eq_of_fg_domain`, the catenarity formula
  `dim R ⧸ Q + ht Q = dim R` for a finitely generated domain `R` over a field, and
* Krull's principal ideal theorem, giving `ht Q = 1` for a minimal prime `Q` over a nonzero
  principal ideal.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Commons.RingTheory.KrullDimension

/-- **Catenarity of affine domains.** Let `R` be a finitely generated domain over a field `K` and
let `Q ⊆ R` be a prime ideal. Then `dim R ⧸ Q + ht Q = dim R`.

The proof uses Noether normalization `φ : K[X₁,…,X_s] → R` (injective, module finite) with
`s = dim R`. If `𝔭` is the contraction of `Q` to `B = K[X₁,…,X_s]`, then

* `dim R = s = dim B` and `dim R ⧸ Q = dim B ⧸ 𝔭` (integral extensions preserve the dimension),
* `dim B ⧸ 𝔭 + ht 𝔭 = s` (catenarity of the polynomial ring),
* `ht 𝔭 = ht Q`: the inequality `ht 𝔭 ≤ ht Q` is going down for the integral extension (the base
  `B` is a polynomial ring, hence integrally closed), while `ht Q ≤ ht 𝔭` holds because
  contracting a strictly increasing chain of primes of `R` to `B` keeps it strictly increasing.
-/
private theorem ringKrullDim_quotient_add_height_eq_of_fg_domain {K R : Type*} [Field K]
    [CommRing R] [IsDomain R] [Algebra K R] [Algebra.FiniteType K R] (Q : Ideal R) [Q.IsPrime] :
    ringKrullDim (R ⧸ Q) + Q.height = ringKrullDim R := by
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing K R
  -- Noether normalization of `R` over `K`.
  obtain ⟨s, φ, hφinj, hφfin⟩ := exists_finite_inj_algHom_of_fg K R
  let B := MvPolynomial (Fin s) K
  letI : Algebra B R := φ.toRingHom.toAlgebra
  have hmap : algebraMap B R = φ.toRingHom := rfl
  haveI : IsScalarTower K B R := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  haveI : Module.Finite B R := hφfin
  haveI : Algebra.IsIntegral B R := Algebra.IsIntegral.of_finite B R
  haveI : FaithfulSMul B R :=
    (faithfulSMul_iff_algebraMap_injective B R).mpr (by rw [hmap]; exact hφinj)
  have hdimR : ringKrullDim R = (s : WithBot ℕ∞) := by
    rw [ringKrullDim_eq_of_isIntegral (A := B) (B := R) (by rw [hmap]; exact hφinj),
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  -- The contraction `𝔭 = B ∩ Q` of `Q`.
  set 𝔭 : Ideal B := Q.under B with h𝔭def
  haveI h𝔭prime : 𝔭.IsPrime := by rw [h𝔭def, Ideal.under_def]; exact Ideal.IsPrime.comap _
  haveI hlies : Q.LiesOver 𝔭 := Ideal.over_under Q
  haveI : Algebra.HasGoingDown B R := inferInstance
  -- `ht 𝔭 ≤ ht Q` by going down (the base is a polynomial ring, hence integrally closed).
  have h𝔭Q : 𝔭.height ≤ Q.height :=
    calc 𝔭.height
        ≤ 𝔭.height + (Q.map (Ideal.Quotient.mk (Ideal.map (algebraMap B R) 𝔭))).height :=
          le_add_right le_rfl
      _ = Q.height := (Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown 𝔭 Q).symm
  -- `ht Q ≤ ht 𝔭`: contracting a chain of primes of `R` to `B` keeps it strict.
  have hQ𝔭 : Q.height ≤ 𝔭.height := by
    have hstrict : StrictMono (PrimeSpectrum.comap (algebraMap B R)) := fun x y hxy => by
      rw [← PrimeSpectrum.asIdeal_lt_asIdeal] at hxy ⊢
      exact Ideal.IsIntegral.comap_lt_comap hxy
    obtain ⟨l, hlast, hlen⟩ := Ideal.exists_ltSeries_length_eq_height Q
    let l' : LTSeries (PrimeSpectrum B) := l.map (PrimeSpectrum.comap (algebraMap B R)) hstrict
    have hlen' : l'.length = l.length := LTSeries.map_length l _ _
    have hlast' : l'.last = (⟨𝔭, h𝔭prime⟩ : PrimeSpectrum B) := by
      rw [LTSeries.last_map, hlast]
      refine PrimeSpectrum.ext ?_
      show Ideal.comap (algebraMap B R) Q = 𝔭
      rw [h𝔭def, Ideal.under_def]
    have h1 : ((l'.length : ℕ) : ℕ∞) ≤ 𝔭.height := by
      have := Order.length_le_height (p := l')
        (x := (⟨𝔭, h𝔭prime⟩ : PrimeSpectrum B)) (le_of_eq hlast')
      rwa [← PrimeSpectrum.height_eq_orderHeight (⟨𝔭, h𝔭prime⟩ : PrimeSpectrum B)] at this
    rw [← hlen]
    calc (l.length : ℕ∞) = ((l'.length : ℕ) : ℕ) := by rw [hlen']
      _ ≤ 𝔭.height := h1
  -- Catenarity of the polynomial ring: `dim B ⧸ 𝔭 + ht 𝔭 = dim B`.
  have hcat : ringKrullDim (B ⧸ 𝔭) + 𝔭.height = (s : WithBot ℕ∞) :=
    ringKrullDim_quotient_add_height_eq s 𝔭
  -- Integral extensions preserve the dimension, so `dim R ⧸ Q = dim B ⧸ 𝔭`.
  have hquot : ringKrullDim (R ⧸ Q) = ringKrullDim (B ⧸ 𝔭) :=
    ringKrullDim_eq_of_isIntegral (A := B ⧸ 𝔭) (B := R ⧸ Q)
      (Ideal.algebraMap_quotient_injective (A := R) (I := Q))
  rw [hdimR, hquot]
  refine le_antisymm ?_ ?_
  · calc ringKrullDim (B ⧸ 𝔭) + Q.height
        ≤ ringKrullDim (B ⧸ 𝔭) + 𝔭.height :=
          add_le_add (le_refl _) (WithBot.coe_le_coe.mpr hQ𝔭)
      _ = (s : WithBot ℕ∞) := hcat
  · calc (s : WithBot ℕ∞) = ringKrullDim (B ⧸ 𝔭) + 𝔭.height := hcat.symm
      _ ≤ ringKrullDim (B ⧸ 𝔭) + Q.height :=
          add_le_add (le_refl _) (WithBot.coe_le_coe.mpr h𝔭Q)

/-- Let `R` be a finitely generated domain over a field `K`. If `Q` is a prime ideal of `R`
minimal over the principal ideal generated by a nonzero element, then `dim R ⧸ Q + 1 = dim R`:
`Q` has height one, so quotienting by it drops the dimension by exactly one. -/
private theorem ringKrullDim_quotient_add_one_of_mem_minimalPrimes_span {K R : Type*} [Field K]
    [CommRing R] [IsDomain R] [Algebra K R] [Algebra.FiniteType K R] {g : R} (hg : g ≠ 0)
    (Q : Ideal R) (hQ : Q ∈ (Ideal.span {g}).minimalPrimes) :
    ringKrullDim (R ⧸ Q) + 1 = ringKrullDim R := by
  haveI hQprime : Q.IsPrime := hQ.1.1
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing K R
  -- `Q` is nonzero, since `0 ≠ g ∈ Q`.
  have hne : Q ≠ ⊥ := by
    intro h
    have : g ∈ (⊥ : Ideal R) := h ▸ hQ.1.2 (Ideal.subset_span (Set.mem_singleton g))
    exact hg (by simpa using this)
  -- Krull's principal ideal theorem, plus `Q ≠ 0`, gives `ht Q = 1`.
  have hht : Q.height = 1 := by
    refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
      (Ideal.span {g}) Q hQ) ?_
    have hlt : (⊥ : Ideal R) < Q := lt_of_le_of_ne bot_le (Ne.symm hne)
    have := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    rwa [Ideal.height_bot, zero_add] at this
  have := ringKrullDim_quotient_add_height_eq_of_fg_domain (K := K) Q
  rwa [hht, WithBot.coe_one] at this

/-- If `k` is a field, `p` is a prime ideal of `k[X₁, …, Xₘ]` closed under taking homogeneous
components, `f ∉ p` and `p + (f) ≠ ⊤`, then for every minimal prime `q` of `p + (f)` the quotient
by `q` has Krull dimension exactly one less than the quotient by `p`:
`ringKrullDim (A ⧸ q) + 1 = ringKrullDim (A ⧸ p)`. -/
private theorem quotient_add_one_of_mem_minimalPrimes_sup_span {k : Type*} [Field k] {m : ℕ}
    (p : Ideal (MvPolynomial (Fin m) k)) [p.IsPrime]
    (hp : ∀ x ∈ p, ∀ j, MvPolynomial.homogeneousComponent j x ∈ p)
    {f : MvPolynomial (Fin m) k} (hf : f ∉ p)
    (q : Ideal (MvPolynomial (Fin m) k)) [q.IsPrime]
    (hq : q ∈ (p ⊔ Ideal.span {f}).minimalPrimes) (hne : p ⊔ Ideal.span {f} ≠ ⊤) :
    ringKrullDim (MvPolynomial (Fin m) k ⧸ q) + 1 = ringKrullDim (MvPolynomial (Fin m) k ⧸ p) := by
  have hpq : p ≤ q := le_trans le_sup_left hq.1.2
  have hg : Ideal.Quotient.mk p f ≠ 0 := fun h0 => hf (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  -- The image of `p + (f)` in `A ⧸ p` is the principal ideal generated by the image of `f`.
  have hspan : (p ⊔ Ideal.span {f}).map (Ideal.Quotient.mk p) =
      Ideal.span {Ideal.Quotient.mk p f} := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, Ideal.map_quotient_self, bot_sup_eq]
  -- The image of `q` is a minimal prime over that principal ideal.
  have hmem : (q.map (Ideal.Quotient.mk p)) ∈
      (Ideal.span {Ideal.Quotient.mk p f}).minimalPrimes := by
    rw [← hspan, Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective]
    refine ⟨q, ?_, rfl⟩
    have hsup : (p ⊔ Ideal.span {f}) ⊔ RingHom.ker (Ideal.Quotient.mk p) = p ⊔ Ideal.span {f} := by
      rw [Ideal.mk_ker]
      exact sup_eq_left.mpr (le_sup_left : p ≤ p ⊔ Ideal.span {f})
    rwa [hsup]
  haveI : IsDomain (MvPolynomial (Fin m) k ⧸ p) := Ideal.Quotient.isDomain p
  haveI : Algebra.FiniteType k (MvPolynomial (Fin m) k ⧸ p) := Algebra.FiniteType.quotient k p
  have hmain := ringKrullDim_quotient_add_one_of_mem_minimalPrimes_span (K := k) hg
    (q.map (Ideal.Quotient.mk p)) hmem
  have he : ((MvPolynomial (Fin m) k ⧸ p) ⧸ (q.map (Ideal.Quotient.mk p))) ≃+*
      (MvPolynomial (Fin m) k ⧸ q) :=
    (DoubleQuot.quotQuotEquivQuotSup p q).trans (Ideal.quotEquivOfEq (sup_eq_right.mpr hpq))
  rw [ringKrullDim_eq_of_ringEquiv he] at hmain
  exact hmain

end Commons.RingTheory.KrullDimension
end


-- ==== from Submission.Commons.Algebra.MvPolynomial.finrank_homogeneousSubmodule_eq_choose ====
section

namespace Commons.Algebra.MvPolynomial

private theorem finrank_homogeneousSubmodule_eq_choose {k : Type*} [Field k] (n d : ℕ) :
    Module.finrank k (MvPolynomial.homogeneousSubmodule (Fin n) k d) = (n + d - 1).choose d := by
  classical
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  have hfin : Finite {e : Fin n →₀ ℕ | e.degree = d} :=
    (Finsupp.finite_of_degree_eq (σ := Fin n) d).to_subtype
  have hft : Fintype {e : Fin n →₀ ℕ | e.degree = d} := Fintype.ofFinite _
  rw [(AddMonoidAlgebra.supportedEquivFinsupp (R := k) (S := k)
    ({e : Fin n →₀ ℕ | e.degree = d})).finrank_eq]
  rw [Module.finrank_finsupp_self]
  rw [← Nat.card_eq_fintype_card]
  change Nat.card {e : Fin n →₀ ℕ // e.degree = d} = (n + d - 1).choose d
  rw [Commons.Algebra.MvPowerSeries.card_finsupp_degree_eq]
  simp only [Fintype.card_fin]

end Commons.Algebra.MvPolynomial
end


-- ==== from Submission.Commons.Algebra.MvPolynomial.finrank_map_bot_mkQ_homogeneousSubmodule ====
section

namespace Commons.Algebra.MvPolynomial

/-- The `t`-th graded piece of a polynomial ring in `m` variables has dimension
`(m + t - 1).choose t`, and its image under the quotient by the zero ideal (which
is an isomorphism onto the ring itself) has the same dimension. -/
private theorem finrank_map_bot_mkQ_homogeneousSubmodule {k : Type*} [Field k] {m : ℕ} (t : ℕ) :
    Module.finrank k (Submodule.map ((⊥ : Ideal (MvPolynomial (Fin m) k)).mkQ.restrictScalars k)
      (MvPolynomial.homogeneousSubmodule (Fin m) k t)) = (m + t - 1).choose t := by
  -- The quotient map by the zero ideal is a bijective `k`-linear map, hence a linear
  -- equivalence; mapping along it preserves the dimension.
  let f : MvPolynomial (Fin m) k →ₗ[k]
      MvPolynomial (Fin m) k ⧸ (⊥ : Submodule (MvPolynomial (Fin m) k) (MvPolynomial (Fin m) k)) :=
    (⊥ : Ideal (MvPolynomial (Fin m) k)).mkQ.restrictScalars k
  have hfinj : Function.Injective f := by
    intro a b hab
    have h : (Submodule.Quotient.mk a : MvPolynomial (Fin m) k ⧸
        (⊥ : Submodule (MvPolynomial (Fin m) k) (MvPolynomial (Fin m) k))) =
        Submodule.Quotient.mk b := hab
    rw [Submodule.Quotient.eq] at h
    exact sub_eq_zero.mp (by simpa using h)
  have hfsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := Submodule.mkQ_surjective
      (⊥ : Submodule (MvPolynomial (Fin m) k) (MvPolynomial (Fin m) k)) y
    exact ⟨x, hx⟩
  let e : MvPolynomial (Fin m) k ≃ₗ[k]
      MvPolynomial (Fin m) k ⧸ (⊥ : Submodule (MvPolynomial (Fin m) k) (MvPolynomial (Fin m) k)) :=
    LinearEquiv.ofBijective f ⟨hfinj, hfsurj⟩
  have he : (e : MvPolynomial (Fin m) k →ₗ[k]
      MvPolynomial (Fin m) k ⧸ (⊥ : Submodule (MvPolynomial (Fin m) k) (MvPolynomial (Fin m) k))) = f :=
    rfl
  rw [← finrank_homogeneousSubmodule_eq_choose (k := k) m t]
  rw [show ((⊥ : Ideal (MvPolynomial (Fin m) k)).mkQ.restrictScalars k) = f from rfl, ← he]
  rw [LinearEquiv.finrank_map_eq e]

end Commons.Algebra.MvPolynomial
end


-- ==== from Submission.Commons.Algebra.Polynomial.one_le_coeff_mul_factorial_of_eventually_int ====
section

namespace Commons.Algebra.Polynomial

noncomputable section

/-- The forward difference operator `P ↦ P(X+1) - P(X)`. -/
private def fdiff (P : Polynomial ℚ) : Polynomial ℚ := Polynomial.taylor 1 P - P

private lemma fdiff_eval (P : Polynomial ℚ) (x : ℚ) :
    (fdiff P).eval x = P.eval (x + 1) - P.eval x := by
  simp [fdiff, Polynomial.taylor_eval]

/-- For a polynomial of degree `≤ 1`, the value at `1` is the sum of the first two coefficients. -/
private lemma eval_one_of_natDegree_le_one {q : Polynomial ℚ} (h : q.natDegree ≤ 1) :
    q.eval 1 = q.coeff 0 + q.coeff 1 := by
  have h2 : q.natDegree < 2 := by omega
  rw [Polynomial.eval_eq_sum_range' (p := q) (n := 2) h2 (1 : ℚ)]
  simp [Finset.sum_range_succ]

/-- The coefficient of `X^(m-1)` in the Taylor shift of `Q` at `1`. -/
private lemma coeff_taylor_one_pred {Q : Polynomial ℚ} {m : ℕ} (hm : 1 ≤ m)
    (hQ : Q.natDegree ≤ m) :
    (Polynomial.taylor 1 Q).coeff (m - 1) = Q.coeff (m - 1) + (m : ℚ) * Q.coeff m := by
  rw [Polynomial.taylor_coeff]
  have hdeg : (Polynomial.hasseDeriv (m - 1) Q).natDegree ≤ 1 := by
    have h := Polynomial.natDegree_hasseDeriv_le Q (m - 1)
    omega
  rw [eval_one_of_natDegree_le_one hdeg,
    Polynomial.hasseDeriv_coeff (k := m - 1) (f := Q) (n := 0),
    Polynomial.hasseDeriv_coeff (k := m - 1) (f := Q) (n := 1)]
  have hch : (m.choose (m - 1) : ℚ) = (m : ℚ) := by
    have h := Nat.choose_symm (show m - 1 ≤ m by omega)
    rw [show m - (m - 1) = 1 by omega, Nat.choose_one_right] at h
    exact_mod_cast h.symm
  rw [show 0 + (m - 1) = m - 1 by omega, show 1 + (m - 1) = m by omega,
    Nat.choose_self, Nat.cast_one, one_mul, hch]

/-- The coefficient of `X^m` in the Taylor shift of `Q` at `1`. -/
private lemma coeff_taylor_one_self {Q : Polynomial ℚ} {m : ℕ} (hQ : Q.natDegree ≤ m) :
    (Polynomial.taylor 1 Q).coeff m = Q.coeff m := by
  rw [Polynomial.taylor_coeff]
  have hdeg : (Polynomial.hasseDeriv m Q).natDegree ≤ 0 := by
    have h := Polynomial.natDegree_hasseDeriv_le Q m
    omega
  rw [Polynomial.eq_C_of_natDegree_eq_zero (le_antisymm hdeg (Nat.zero_le _)),
    Polynomial.eval_C, Polynomial.hasseDeriv_coeff (k := m) (f := Q) (n := 0)]
  simp

/-- The forward difference of a polynomial of degree `m ≠ 0` has degree `m - 1` and leading
coefficient `m` times the original leading coefficient. -/
private lemma fdiff_natDegree_leadingCoeff {Q : Polynomial ℚ} (hm : Q.natDegree ≠ 0) :
    (fdiff Q).natDegree = Q.natDegree - 1 ∧
    (fdiff Q).leadingCoeff = (Q.natDegree : ℚ) * Q.leadingCoeff := by
  set m := Q.natDegree with hmdef
  have hm1 : 1 ≤ m := by omega
  have hcoeff : (fdiff Q).coeff (m - 1) = (m : ℚ) * Q.coeff m := by
    rw [fdiff, Polynomial.coeff_sub, coeff_taylor_one_pred hm1 (le_of_eq hmdef.symm)]
    ring
  have hcoeffm : (fdiff Q).coeff m = 0 := by
    rw [fdiff, Polynomial.coeff_sub, coeff_taylor_one_self (le_of_eq hmdef.symm)]
    ring
  have hQne : Q ≠ 0 := by
    intro h0
    exact hm (by rw [hmdef, h0, Polynomial.natDegree_zero])
  have hlc : Q.coeff m ≠ 0 := by
    rw [hmdef, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hQne
  have hne : (fdiff Q).coeff (m - 1) ≠ 0 := by
    rw [hcoeff]
    exact mul_ne_zero (by exact_mod_cast (show m ≠ 0 by omega)) hlc
  have hsub : (fdiff Q).natDegree ≤ m := by
    rw [fdiff]
    calc (Polynomial.taylor 1 Q - Q).natDegree
        ≤ max (Polynomial.taylor 1 Q).natDegree Q.natDegree := Polynomial.natDegree_sub_le _ _
      _ = max m m := by rw [Polynomial.natDegree_taylor, hmdef]
      _ = m := max_self m
  have hge : m - 1 ≤ (fdiff Q).natDegree := Polynomial.le_natDegree_of_ne_zero hne
  have hlt : (fdiff Q).natDegree < m := by
    rcases lt_or_eq_of_le hsub with h | h
    · exact h
    · exfalso
      have hfdne : fdiff Q ≠ 0 := fun h0 => hne (by rw [h0, Polynomial.coeff_zero])
      have : (fdiff Q).coeff m ≠ 0 := by
        rw [← h, Polynomial.coeff_natDegree]
        exact Polynomial.leadingCoeff_ne_zero.mpr hfdne
      exact this hcoeffm
  have hnd : (fdiff Q).natDegree = m - 1 := by omega
  refine ⟨by rw [hnd, hmdef], ?_⟩
  rw [← Polynomial.coeff_natDegree, hnd, hcoeff, hmdef, Polynomial.coeff_natDegree]

/-- The forward difference of an eventually-integer-valued rational polynomial is again
eventually integer valued. -/
private lemma fdiff_eventually_int {Q : Polynomial ℚ}
    (h : ∃ N : ℚ, ∀ t : ℚ, N ≤ t → ∃ z : ℤ, Q.eval t = z) :
    ∃ N : ℚ, ∀ t : ℚ, N ≤ t → ∃ z : ℤ, (fdiff Q).eval t = z := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun t ht => ?_⟩
  obtain ⟨z1, h1⟩ := hN (t + 1) (by linarith)
  obtain ⟨z2, h2⟩ := hN t ht
  refine ⟨z1 - z2, ?_⟩
  rw [fdiff_eval, h1, h2]
  push_cast
  ring

/-- Any iterate of the forward difference of an eventually-integer-valued rational polynomial
is again eventually integer valued. -/
private lemma fdiff_iterate_eventually_int (k : ℕ) {P : Polynomial ℚ}
    (h : ∃ N : ℚ, ∀ t : ℚ, N ≤ t → ∃ z : ℤ, P.eval t = z) :
    ∃ N : ℚ, ∀ t : ℚ, N ≤ t → ∃ z : ℤ, ((fdiff^[k]) P).eval t = z := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact fdiff_eventually_int ih

/-- Iterating the forward difference: after `k` steps the degree has dropped by `k` and the
leading coefficient has been multiplied by the descending factorial `n.descFactorial k`. -/
private lemma fdiff_iterate_natDegree_coeff (P : Polynomial ℚ) (k : ℕ) (hk : k ≤ P.natDegree) :
    ((fdiff^[k]) P).natDegree = P.natDegree - k ∧
    ((fdiff^[k]) P).coeff (P.natDegree - k) =
      ((P.natDegree.descFactorial k : ℕ) : ℚ) * P.coeff P.natDegree := by
  induction k with
  | zero => simp [Nat.descFactorial_zero]
  | succ k ih =>
    have hk' : k ≤ P.natDegree := by omega
    obtain ⟨hnd, hcoeff⟩ := ih hk'
    have hmne : ((fdiff^[k]) P).natDegree ≠ 0 := by rw [hnd]; omega
    obtain ⟨hdnd, hdlc⟩ := fdiff_natDegree_leadingCoeff (Q := (fdiff^[k]) P) hmne
    have hidx : P.natDegree - (k + 1) = P.natDegree - k - 1 := by omega
    constructor
    · rw [Function.iterate_succ_apply', hdnd, hnd]
      omega
    · have hlc2 : ((fdiff^[k]) P).leadingCoeff =
          ((P.natDegree.descFactorial k : ℕ) : ℚ) * P.coeff P.natDegree := by
        rw [← Polynomial.coeff_natDegree, hnd, hcoeff]
      rw [Function.iterate_succ_apply', hidx,
        show P.natDegree - k - 1 = (fdiff ((fdiff^[k]) P)).natDegree by rw [hdnd, hnd],
        Polynomial.coeff_natDegree, hdlc, hlc2, Nat.descFactorial_succ]
      rw [hnd]
      push_cast
      ring

private theorem one_le_coeff_mul_factorial_of_eventually_int {P : Polynomial ℚ}
    (hpos : ∃ N, ∀ t ≥ N, 0 < P.eval (t : ℚ))
    (hint : ∃ N, ∀ t ≥ N, ∃ z : ℤ, P.eval (t : ℚ) = z) :
    1 ≤ P.coeff P.natDegree * P.natDegree.factorial := by
  have hPne : P ≠ 0 := by
    intro h0
    obtain ⟨N, hN⟩ := hpos
    have := hN N le_rfl
    rw [h0, Polynomial.eval_zero] at this
    exact lt_irrefl 0 this
  obtain ⟨hnd, hcoeff⟩ := fdiff_iterate_natDegree_coeff P P.natDegree le_rfl
  have hnd0 : ((fdiff^[P.natDegree]) P).natDegree = 0 := by
    rw [hnd, Nat.sub_self]
  have hconst : ((fdiff^[P.natDegree]) P) =
      Polynomial.C ((P.natDegree.factorial : ℚ) * P.coeff P.natDegree) := by
    rw [Polynomial.eq_C_of_natDegree_eq_zero hnd0]
    congr 1
    have h := hcoeff
    rw [Nat.sub_self, Nat.descFactorial_self] at h
    exact h
  -- integrality of the top finite difference
  obtain ⟨N', hN'⟩ := fdiff_iterate_eventually_int P.natDegree hint
  obtain ⟨z, hz⟩ := hN' N' le_rfl
  rw [hconst, Polynomial.eval_C] at hz
  -- positivity of the leading coefficient
  have hnonneg : 0 ≤ P.coeff P.natDegree := by
    apply coeff_nonneg_of_eventually_eval_nonneg (f := P) (d := P.natDegree) le_rfl
    obtain ⟨N, hN⟩ := hpos
    obtain ⟨N₀, hN₀⟩ := exists_nat_ge N
    refine ⟨N₀, fun n hn => ?_⟩
    have hcast : N ≤ (n : ℚ) := le_trans hN₀ (by exact_mod_cast hn)
    exact le_of_lt (hN (n : ℚ) hcast)
  have hane : P.coeff P.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hPne
  have hapos : 0 < P.coeff P.natDegree := lt_of_le_of_ne hnonneg (Ne.symm hane)
  have hfacpos : (0 : ℚ) < (P.natDegree.factorial : ℚ) := by
    exact_mod_cast Nat.factorial_pos P.natDegree
  have hqpos : 0 < (P.natDegree.factorial : ℚ) * P.coeff P.natDegree := mul_pos hfacpos hapos
  have hzpos : 0 < z := by
    have h := hqpos
    rw [hz] at h
    exact_mod_cast h
  have hgoal : (1 : ℚ) ≤ (P.natDegree.factorial : ℚ) * P.coeff P.natDegree := by
    rw [hz]
    exact_mod_cast (show (1 : ℤ) ≤ z by omega)
  simpa [mul_comm] using hgoal

end

end Commons.Algebra.Polynomial
end


-- ==== from Submission.Commons.Algebra.Polynomial.natDegree_sub_taylor_natCast ====
section

open Polynomial

namespace Commons.Algebra.Polynomial

/-- The coefficient of degree `P.natDegree - 1` of the Taylor expansion `taylor a P` of `P` at `a`.
Writing `n = P.natDegree`, only the terms of `P` of degree `n - 1` and `n` contribute, so
`(taylor a P).coeff (n - 1) = P.coeff (n - 1) + n * a * P.coeff n`.  (This is the `k = 1`
Hasse-derivative coefficient of the shift `X ↔ X + a`.) -/
private theorem coeff_taylor_natDegree_sub_one {R : Type*} [CommSemiring R] (P : R[X]) (a : R)
    (hn : 0 < P.natDegree) :
    (taylor a P).coeff (P.natDegree - 1) =
      P.coeff (P.natDegree - 1) + (P.natDegree : R) * a * P.coeff P.natDegree := by
  have h1 : (taylor a P).coeff (P.natDegree - 1) =
      (hasseDeriv (P.natDegree - 1) P).eval a := by
    rw [taylor_coeff]
  rw [h1]
  have hnd : (hasseDeriv (P.natDegree - 1) P).natDegree < 2 := by
    have := natDegree_hasseDeriv_le P (P.natDegree - 1)
    omega
  rw [eval_eq_sum_range' hnd a]
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [Finset.sum_range_zero, zero_add]
  rw [hasseDeriv_coeff, hasseDeriv_coeff]
  simp only [zero_add, pow_zero, mul_one, pow_one]
  rw [Nat.choose_self]
  have h2 : 1 + (P.natDegree - 1) = P.natDegree := by omega
  rw [h2]
  have h3 : P.natDegree.choose (P.natDegree - 1) = P.natDegree := by
    rw [Nat.choose_symm (k := 1) (by omega : 1 ≤ P.natDegree), Nat.choose_one_right]
  rw [h3]
  ring

/-- The first-order Taylor defect `P - taylor (-e) P` of a nonzero polynomial `P` over `ℚ`
and a positive natural number `e`: it has degree one less than `P`, and its leading coefficient
is `e * P.natDegree * P.coeff P.natDegree`. -/
private theorem natDegree_sub_taylor_natCast {P : Polynomial ℚ} {e : ℕ} (he : 0 < e) (hP : P ≠ 0) :
    (P - Polynomial.taylor (-(e : ℚ)) P).natDegree = P.natDegree - 1 ∧
    (P - Polynomial.taylor (-(e : ℚ)) P).coeff (P.natDegree - 1)
      = (e : ℚ) * P.natDegree * P.coeff P.natDegree := by
  by_cases hn : P.natDegree = 0
  · -- `P` is a nonzero constant, so the Taylor defect vanishes.
    have hC : P = C (P.coeff 0) := eq_C_of_natDegree_le_zero (by omega)
    rw [hC]
    simp [taylor_C]
  · have hn' : 0 < P.natDegree := by omega
    have hcoeff : (P - taylor (-(e : ℚ)) P).coeff (P.natDegree - 1)
        = (e : ℚ) * P.natDegree * P.coeff P.natDegree := by
      rw [coeff_sub, coeff_taylor_natDegree_sub_one P (-(e : ℚ)) hn']
      ring
    constructor
    · -- The defect has degree at most `n - 1` ...
      have hle : (P - taylor (-(e : ℚ)) P).natDegree ≤ P.natDegree - 1 := by
        by_cases hQ : P - taylor (-(e : ℚ)) P = 0
        · rw [hQ, natDegree_zero]; omega
        · have hdeg : (P - taylor (-(e : ℚ)) P).degree < P.degree :=
            degree_sub_lt_left (by rw [degree_taylor]) hP (by rw [leadingCoeff_taylor])
          rw [degree_eq_natDegree hP] at hdeg
          have := (natDegree_lt_iff_degree_lt hQ).mpr hdeg
          omega
      -- ... and its `(n - 1)`-st coefficient is nonzero, so the degree is exactly `n - 1`.
      have hne : (P - taylor (-(e : ℚ)) P).coeff (P.natDegree - 1) ≠ 0 := by
        rw [hcoeff]
        have he' : (e : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr he.ne'
        have hn'' : (P.natDegree : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn'.ne'
        have hc : P.coeff P.natDegree ≠ 0 := by
          rw [coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hP
        exact mul_ne_zero (mul_ne_zero he' hn'') hc
      exact natDegree_eq_of_le_of_coeff_ne_zero hle hne
    · rw [hcoeff]

end Commons.Algebra.Polynomial
end


-- ==== from Submission.Commons.RingTheory.Ideal.finite_subtype_minimalPrimes ====
section

namespace Commons.RingTheory.Ideal

private theorem finite_subtype_minimalPrimes {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R) :
    Finite {p : Ideal R // p ∈ I.minimalPrimes} :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing R I).to_subtype

end Commons.RingTheory.Ideal

end


-- ==== from Submission.Commons.RingTheory.KrullDimension.one_le_quotient_of_ne_idealOfVars ====
section

namespace Commons.RingTheory.KrullDimension

/-- Every element of a homogeneous prime ideal in a polynomial ring over a field has vanishing
constant coefficient, hence lies in the ideal of variables. -/
private lemma le_idealOfVars_of_homogeneous_prime {k : Type*} [Field k] {m : ℕ}
    (q : Ideal (MvPolynomial (Fin m) k)) [q.IsPrime]
    (hq : ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q) :
    q ≤ MvPolynomial.idealOfVars (Fin m) k := by
  intro x hx
  have hc0 : MvPolynomial.coeff 0 x = 0 := by
    have h0 : MvPolynomial.homogeneousComponent 0 x ∈ q := hq x hx 0
    rw [MvPolynomial.homogeneousComponent_zero] at h0
    by_contra hne
    have hunit : (MvPolynomial.C ((MvPolynomial.coeff 0 x)⁻¹) : MvPolynomial (Fin m) k) *
        MvPolynomial.C (MvPolynomial.coeff 0 x) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hne, map_one]
    have h1 : (1 : MvPolynomial (Fin m) k) ∈ q := by
      rw [← hunit]
      exact Ideal.mul_mem_left q _ h0
    exact Ideal.one_notMem q h1
  have hidV : MvPolynomial.idealOfVars (Fin m) k
      = Ideal.span (MvPolynomial.X '' (Set.univ : Set (Fin m))) := by
    rw [MvPolynomial.idealOfVars, Set.image_univ]
  rw [hidV, MvPolynomial.mem_ideal_span_X_image]
  intro d hd
  rw [MvPolynomial.mem_support_iff] at hd
  have hd0 : d ≠ 0 := by
    intro hdz
    exact hd (by rw [hdz]; exact hc0)
  obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    exact hd0 (Finsupp.ext h)
  exact ⟨i, Set.mem_univ i, hi⟩

private theorem one_le_quotient_of_ne_idealOfVars {k : Type*} [Field k] {m : ℕ}
    (q : Ideal (MvPolynomial (Fin m) k)) [q.IsPrime]
    (hq : ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q)
    (hqM : q ≠ MvPolynomial.idealOfVars (Fin m) k) :
    (1 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin m) k ⧸ q) := by
  have hqle := le_idealOfVars_of_homogeneous_prime q hq
  -- The ideal of variables is proper.
  have hIdV_ne_top : MvPolynomial.idealOfVars (Fin m) k ≠ ⊤ := by
    intro htop
    have hle_ker : MvPolynomial.idealOfVars (Fin m) k ≤
        RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin m) k →+* k) := by
      rw [MvPolynomial.idealOfVars, Ideal.span_le]
      rintro x ⟨i, rfl⟩
      simp
    have h1 : (1 : MvPolynomial (Fin m) k) ∈ MvPolynomial.idealOfVars (Fin m) k := by
      rw [htop]; exact Submodule.mem_top
    have hmem := hle_ker h1
    rw [RingHom.mem_ker] at hmem
    simp at hmem
  -- Build a prime ideal strictly above `q`, maximal above the ideal of variables.
  obtain ⟨M, hMmax, hIdVleM⟩ :=
    Ideal.exists_le_maximal (MvPolynomial.idealOfVars (Fin m) k) hIdV_ne_top
  have hqMle : q ≤ M := hqle.trans hIdVleM
  have hMne : M ≠ q := by
    intro heq
    have hle : MvPolynomial.idealOfVars (Fin m) k ≤ q := heq ▸ hIdVleM
    exact hqM (le_antisymm hqle hle)
  have hMprime : M.IsPrime := hMmax.isPrime
  let f : MvPolynomial (Fin m) k →+* (MvPolynomial (Fin m) k ⧸ q) := Ideal.Quotient.mk q
  have hker_le : RingHom.ker f ≤ M := by
    show RingHom.ker (Ideal.Quotient.mk q) ≤ M
    rw [Ideal.mk_ker]
    exact hqMle
  have hmap_prime : (M.map f).IsPrime :=
    Ideal.map_isPrime_of_surjective (f := f) Ideal.Quotient.mk_surjective (I := M)
      (H := hMprime) hker_le
  have hmap_ne_bot : M.map f ≠ ⊥ := fun h => by
    rw [Ideal.map_eq_bot_iff_le_ker (I := M) f] at h
    rw [Ideal.mk_ker] at h
    exact hMne (le_antisymm h hqMle)
  rw [ringKrullDim, Order.one_le_krullDim_iff]
  refine ⟨⟨⊥, inferInstance⟩, ⟨M.map f, hmap_prime⟩, ?_⟩
  rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
  exact lt_of_le_of_ne bot_le (Ne.symm hmap_ne_bot)

end Commons.RingTheory.KrullDimension
end


-- ==== from Submission.Commons.Order.WithBot_ENat_add_one_inj ====
section

namespace Commons.Order

private theorem WithBot_ENat_add_one_inj {x y : WithBot ℕ∞} (h : x + 1 = y + 1) : x = y :=
  (ENat.WithBot.add_one_cancel (a := x) (b := y)).mp h

end Commons.Order
end


-- ==== from Submission.Commons.RingTheory.Ideal.minimalPrimes_homogeneous ====
section

namespace Commons.RingTheory.Ideal

open MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- For the standard `ℕ`-grading of a multivariate polynomial ring, the decomposition map
is the homogeneous component projection. -/
private lemma decompose_eq_homogeneousComponent {k : Type*} [CommSemiring k] {m : ℕ}
    (x : MvPolynomial (Fin m) k) (j : ℕ) :
    (DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin m) k) x j :
        MvPolynomial (Fin m) k) = MvPolynomial.homogeneousComponent j x := by
  rw [← DirectSum.Decomposition.decompose'_eq]
  exact MvPolynomial.decomposition.decompose'_apply x j

private theorem minimalPrimes_homogeneous {k : Type*} [Field k] {m : ℕ}
    (J : Ideal (MvPolynomial (Fin m) k))
    (hJ : ∀ x ∈ J, ∀ j, MvPolynomial.homogeneousComponent j x ∈ J)
    {q : Ideal (MvPolynomial (Fin m) k)} (hq : q ∈ J.minimalPrimes) :
    ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q := by
  classical
  have hJhom : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin m) k) := by
    intro i x hx
    rw [decompose_eq_homogeneousComponent]
    exact hJ x hx i
  have hqprime : q.IsPrime := hq.1.1
  have hcoreprime :
      (q.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin m) k)).toIdeal.IsPrime :=
    hqprime.homogeneousCore
  have hJ_le_core :
      J ≤ (q.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin m) k)).toIdeal := by
    have hmono : J.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin m) k) ≤
        q.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin m) k) :=
      Ideal.homogeneousCore_mono _ hq.1.2
    have hto : (J.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin m) k)).toIdeal ≤
        (q.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin m) k)).toIdeal :=
      hmono
    rwa [Ideal.IsHomogeneous.toIdeal_homogeneousCore_eq_self hJhom] at hto
  have hcore_le_q :
      (q.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin m) k)).toIdeal ≤ q :=
    Ideal.toIdeal_homogeneousCore_le _ q
  have hq_le_core :
      q ≤ (q.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin m) k)).toIdeal :=
    hq.2 ⟨hcoreprime, hJ_le_core⟩ hcore_le_q
  have hqhom : q.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin m) k) :=
    (Ideal.IsHomogeneous.iff_eq _ q).mpr (le_antisymm hcore_le_q hq_le_core)
  intro x hx j
  exact (MvPolynomial.mem_iff_homogeneousComponent_mem hqhom x).mp hx j

end

end Commons.RingTheory.Ideal
end


-- ==== from Submission.Commons.RingTheory.Ideal.Hilbert.dim_quotient_sup_span_eq_dim_sub_one ====
section

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# Dimension of quotients of a polynomial ring by a hypersurface

We prove that if `A` is a finitely generated domain over a field `K` and `0 ≠ g ∈ A` is a
nonunit, then the quotient `A ⧸ (g)` has Krull dimension exactly one less than `A`:

`ringKrullDim (A ⧸ span {g}) + 1 = ringKrullDim A`.

The proof combines two ingredients:
* an upper bound: a quotient by a non-zero-divisor drops the dimension by at least one
  (`ringKrullDim_quotient_succ_le_of_nonZeroDivisor`);
* a lower bound, which uses the fact that every maximal ideal of a finitely generated domain over
  a field has height equal to the Krull dimension ("equidimensionality"), obtained from Noether
  normalization and going-down.
-/

namespace Commons.RingTheory.Ideal.Hilbert

open MvPolynomial

/-- Every maximal ideal of the polynomial ring `K[X₁, …, Xₛ]` over a field `K` has height `s`. -/
private theorem height_maximal_mvPolynomial {k : Type*} [Field k] (s : ℕ)
    (m : Ideal (MvPolynomial (Fin s) k)) [m.IsMaximal] : m.height = s := by
  induction s with
  | zero =>
    obtain ⟨e⟩ : Nonempty (MvPolynomial (Fin 0) k ≃+* k) :=
      ⟨MvPolynomial.isEmptyRingEquiv k (Fin 0)⟩
    have hmap : (Ideal.map e m).height = m.height := RingEquiv.height_map e m
    have hmax : (Ideal.map e m).IsMaximal := Ideal.map_isMaximal_of_equiv e
    have hbot : (⊥ : Ideal k).IsMaximal := (Ring.isField_iff_maximal_bot).mp (Field.toIsField k)
    have : Ideal.map e m = ⊥ := (hbot.eq_of_le hmax.ne_top bot_le).symm
    rw [this, Ideal.height_bot] at hmap
    exact hmap.symm
  | succ n ih =>
    set e := MvPolynomial.finSuccEquiv k n with he
    let P : Ideal (Polynomial (MvPolynomial (Fin n) k)) :=
      Ideal.map (e : MvPolynomial (Fin (n + 1)) k →+* _) m
    haveI : P.IsMaximal := Ideal.map_isMaximal_of_equiv e.toRingEquiv
    have h1 : P.height = m.height := RingEquiv.height_map e.toRingEquiv m
    let p : Ideal (MvPolynomial (Fin n) k) := P.under (MvPolynomial (Fin n) k)
    have hp : p = Ideal.comap Polynomial.C P := rfl
    haveI : p.IsMaximal := by rw [hp]; exact Polynomial.isMaximal_comap_C_of_isJacobsonRing P
    have h2 : P.height = p.height + 1 := Polynomial.height_eq_height_add_one p P
    have h3 : p.height = n := ih p
    rw [h3] at h2
    rw [h1] at h2
    rw [h2]
    push_cast
    ring

/-- **Equidimensionality.** Every maximal ideal of a finitely generated domain over a field has
height equal to the Krull dimension of the ring. -/
private theorem height_eq_ringKrullDim_of_isMaximal {K A : Type*} [Field K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] (M : Ideal A) [M.IsMaximal] :
    M.height = ringKrullDim A := by
  obtain ⟨s, φ, hφinj, hφfin⟩ := exists_finite_inj_algHom_of_fg K A
  let B := MvPolynomial (Fin s) K
  letI : Algebra B A := φ.toRingHom.toAlgebra
  have hmap : algebraMap B A = φ.toRingHom := rfl
  haveI : IsScalarTower K B A := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  haveI : Module.Finite B A := hφfin
  haveI : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  haveI : FaithfulSMul B A :=
    (faithfulSMul_iff_algebraMap_injective B A).mpr (by rw [hmap]; exact hφinj)
  have hdim : ringKrullDim A = (s : WithBot ℕ∞) := by
    rw [Commons.RingTheory.KrullDimension.ringKrullDim_eq_of_isIntegral
        (by rw [hmap]; exact hφinj),
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hle : M.height ≤ (s : ℕ∞) := by
    have h := Ideal.height_le_ringKrullDim_of_isPrime (R := A) (I := M)
    rw [hdim] at h
    exact WithBot.coe_le_coe.mp h
  have hm : (M.under B).height = (s : ℕ∞) := height_maximal_mvPolynomial s (M.under B)
  have hge : (s : ℕ∞) ≤ M.height := by
    obtain ⟨l, hlast, hlen⟩ := Ideal.exists_ltSeries_length_eq_height (M.under B)
    rw [hm] at hlen
    have hlen' : l.length = s := by exact_mod_cast hlen
    haveI : M.LiesOver l.last.asIdeal := by
      rw [hlast]; exact ⟨rfl⟩
    obtain ⟨L, hLlen, hLlast, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown l M
    rw [hlen'] at hLlen
    have h1 : (s : ℕ∞) ≤ Order.height (⟨M, inferInstance⟩ : PrimeSpectrum A) := by
      rw [← hLlen]
      exact Order.length_le_height (le_of_eq hLlast)
    rw [← PrimeSpectrum.height_eq_orderHeight (⟨M, inferInstance⟩ : PrimeSpectrum A)] at h1
    exact h1
  rw [hdim]
  exact le_antisymm (WithBot.coe_le_coe.mpr hle) (WithBot.coe_le_coe.mpr hge)

/-- If `A` is a finitely generated domain over a field and `0 ≠ g ∈ A` is a nonunit, then
`ringKrullDim (A ⧸ span {g}) + 1 = ringKrullDim A`. -/
private theorem ringKrullDim_quotient_span_singleton_add_one {K A : Type*} [Field K] [CommRing A]
    [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] {g : A} (hg : g ≠ 0)
    (hgu : ¬ IsUnit g) :
    ringKrullDim (A ⧸ Ideal.span {g}) + 1 = ringKrullDim A := by
  refine le_antisymm ?_ ?_
  · exact ringKrullDim_quotient_succ_le_of_nonZeroDivisor
      (by rwa [mem_nonZeroDivisors_iff_ne_zero])
  · obtain ⟨M, hMmax, hleM⟩ :=
      Ideal.exists_le_maximal (Ideal.span {g}) (Ideal.span_singleton_eq_top.not.mpr hgu)
    haveI : M.IsMaximal := hMmax
    haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
    have hht : (M.height : WithBot ℕ∞) = ringKrullDim A :=
      height_eq_ringKrullDim_of_isMaximal (K := K) M
    rw [← hht]
    exact Ideal.height_le_ringKrullDim_quotient_add_one
      (hleM (Ideal.subset_span (Set.mem_singleton g)))

/-- If `A` is a finitely generated domain over a field and `0 ≠ g ∈ A` is a nonunit, then there
is `d ≠ 0` with `dim A = d` and `dim (A ⧸ (g)) = d - 1`. -/
private theorem exists_ringKrullDim_quotient_span_singleton_add_one {K A : Type*} [Field K] [CommRing A]
    [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] {g : A} (hg : g ≠ 0)
    (hgu : ¬ IsUnit g) :
    ∃ d : ℕ, 0 < d ∧ ringKrullDim A = (d : WithBot ℕ∞) ∧
      ringKrullDim (A ⧸ Ideal.span {g}) = ((d - 1 : ℕ) : WithBot ℕ∞) := by
  obtain ⟨s, φ, hφinj, hφfin⟩ := exists_finite_inj_algHom_of_fg K A
  let B := MvPolynomial (Fin s) K
  letI : Algebra B A := φ.toRingHom.toAlgebra
  have hmap : algebraMap B A = φ.toRingHom := rfl
  haveI : IsScalarTower K B A := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  haveI : Module.Finite B A := hφfin
  haveI : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  haveI : FaithfulSMul B A :=
    (faithfulSMul_iff_algebraMap_injective B A).mpr (by rw [hmap]; exact hφinj)
  have hdim : ringKrullDim A = (s : WithBot ℕ∞) := by
    rw [Commons.RingTheory.KrullDimension.ringKrullDim_eq_of_isIntegral
        (by rw [hmap]; exact hφinj),
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hdrop : ringKrullDim (A ⧸ Ideal.span {g}) + 1 = ringKrullDim A :=
    ringKrullDim_quotient_span_singleton_add_one (K := K) hg hgu
  haveI : Nontrivial (A ⧸ Ideal.span {g}) :=
    Ideal.Quotient.nontrivial_iff.mpr (Ideal.span_singleton_eq_top.not.mpr hgu)
  have hpos : 0 < s := by
    have h1 : (1 : WithBot ℕ∞) ≤ ringKrullDim A := by
      rw [← hdrop]
      calc (1 : WithBot ℕ∞) = 0 + 1 := by simp
        _ ≤ ringKrullDim (A ⧸ Ideal.span {g}) + 1 := by
            gcongr; exact ringKrullDim_nonneg_of_nontrivial
    rw [hdim] at h1
    have h2 : (1 : ℕ∞) ≤ (s : ℕ∞) := WithBot.coe_le_coe.mp h1
    have h2' : (1 : ℕ) ≤ s := ENat.natCast_le_natCast.mp h2
    omega
  have hquot : ringKrullDim (A ⧸ Ideal.span {g}) = ((s - 1 : ℕ) : WithBot ℕ∞) := by
    have hne : ringKrullDim (A ⧸ Ideal.span {g}) ≠ ⊥ := by
      intro h0
      rw [h0, WithBot.bot_add, hdim] at hdrop
      exact WithBot.bot_ne_coe hdrop
    obtain ⟨D, hD⟩ := WithBot.ne_bot_iff_exists.mp hne
    have hD1 : D + 1 = (s : ℕ∞) := by
      have h' : ((D + 1 : ℕ∞) : WithBot ℕ∞) = ((s : ℕ∞) : WithBot ℕ∞) := by
        rw [← hD, hdim] at hdrop
        rw [WithBot.coe_add, WithBot.coe_one]
        exact hdrop
      exact WithBot.coe_inj.mp h'
    have hDtop : D ≠ ⊤ := by
      intro htop
      rw [htop, top_add] at hD1
      exact ENat.natCast_ne_top s hD1.symm
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hDtop
    have hn1 : n + 1 = s := by
      have h := hD1
      rw [← hn] at h
      have h' : ((n + 1 : ℕ) : ℕ∞) = (s : ℕ∞) := by push_cast; exact h
      exact_mod_cast h'
    have hn2 : n = s - 1 := by omega
    rw [← hD, ← hn, hn2]
    push_cast
    rfl
  exact ⟨s, hpos, hdim, hquot⟩

/-- If `p` is a homogeneous prime ideal of the polynomial ring `k[X₁,…,Xₘ]` over a field `k`,
`f ∉ p` is a nonzero polynomial with `p + (f) ≠ ⊤`, then the dimension of `R ⧸ p` is `d ≠ 0`
and the dimension of `R ⧸ (p + (f))` is `d - 1`. -/
private theorem dim_quotient_sup_span_eq_dim_sub_one {k : Type*} [Field k] {m : ℕ}
    (p : Ideal (MvPolynomial (Fin m) k)) [p.IsPrime]
    (hp : ∀ x ∈ p, ∀ j, MvPolynomial.homogeneousComponent j x ∈ p)
    {f : MvPolynomial (Fin m) k} (hf : f ∉ p) (hf0 : f ≠ 0)
    (hproper : p ⊔ Ideal.span {f} ≠ ⊤) :
    ∃ d : ℕ, ringKrullDim (MvPolynomial (Fin m) k ⧸ p) = (d : WithBot ℕ∞) ∧ d ≠ 0 ∧
      ringKrullDim (MvPolynomial (Fin m) k ⧸ (p ⊔ Ideal.span {f})) = ((d - 1 : ℕ) : WithBot ℕ∞) := by
  let A := MvPolynomial (Fin m) k ⧸ p
  let g : A := Ideal.Quotient.mk p f
  haveI : IsDomain A := Ideal.Quotient.isDomain p
  have hg : g ≠ 0 := by
    change Ideal.Quotient.mk p f ≠ 0
    exact fun h => hf (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hspan : (Ideal.span {f}).map (Ideal.Quotient.mk p) = Ideal.span {g} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hgu : ¬ IsUnit g := by
    rw [← Ideal.span_singleton_eq_top]
    intro htop
    have hdom : Subsingleton ((MvPolynomial (Fin m) k ⧸ p) ⧸
        (Ideal.span {f}).map (Ideal.Quotient.mk p)) := by
      rw [hspan, htop]
      infer_instance
    have hsub : Subsingleton ((MvPolynomial (Fin m) k) ⧸ (p ⊔ Ideal.span {f})) := by
      haveI := hdom
      refine ⟨fun x y => ?_⟩
      have hxy : (DoubleQuot.quotQuotEquivQuotSup p (Ideal.span {f})).symm x
          = (DoubleQuot.quotQuotEquivQuotSup p (Ideal.span {f})).symm y :=
        Subsingleton.elim _ _
      simpa using congrArg (DoubleQuot.quotQuotEquivQuotSup p (Ideal.span {f})) hxy
    exact hproper (Ideal.Quotient.subsingleton_iff.mp hsub)
  obtain ⟨d, hd0, hdA, hdquot⟩ :=
    exists_ringKrullDim_quotient_span_singleton_add_one (K := k) (A := A) hg hgu
  refine ⟨d, ?_, hd0.ne', ?_⟩
  · exact hdA
  · have he : (A ⧸ Ideal.span {g}) ≃+* (MvPolynomial (Fin m) k) ⧸ (p ⊔ Ideal.span {f}) :=
      (Ideal.quotEquivOfEq hspan.symm).trans
        (DoubleQuot.quotQuotEquivQuotSup p (Ideal.span {f}))
    have heq2 : ringKrullDim (MvPolynomial (Fin m) k ⧸ (p ⊔ Ideal.span {f}))
        = ringKrullDim (A ⧸ Ideal.span {g}) :=
      (ringKrullDim_eq_of_ringEquiv
        (R := A ⧸ Ideal.span {g})
        (S := MvPolynomial (Fin m) k ⧸ (p ⊔ Ideal.span {f})) he).symm
    rw [heq2, hdquot]

end Commons.RingTheory.Ideal.Hilbert
end


-- ==== from Submission.Commons.Algebra.Polynomial.natDegree_le_of_eventually_abs_eval_le ====
section

namespace Commons.Algebra.Polynomial

open Filter

private theorem natDegree_le_of_eventually_abs_eval_le {P : Polynomial ℚ} {k : ℕ} {C : ℚ} {N : ℕ}
    (h : ∀ n : ℕ, N ≤ n → |P.eval (n : ℚ)| ≤ C * (n : ℚ) ^ k) :
    P.natDegree ≤ k := by
  by_contra hcon
  have hcon : k < P.natDegree := lt_of_not_ge hcon
  have hPne : P ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hcon
    omega
  rcases le_or_gt C 0 with hC | hC
  · have hroot : ∀ n : ℕ, N ≤ n → P.eval (n : ℚ) = 0 := by
      intro n hn
      have h1 := h n hn
      have h2 : C * (n : ℚ) ^ k ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hC (by positivity)
      have h3 : |P.eval (n : ℚ)| ≤ 0 := le_trans h1 h2
      exact abs_eq_zero.mp (le_antisymm h3 (abs_nonneg _))
    refine hPne (Polynomial.eq_zero_of_infinite_isRoot P ?_)
    refine (Set.infinite_range_of_injective (f := fun n : ℕ => ((N + n : ℕ) : ℚ)) ?_).mono ?_
    · intro a b hab
      have h' : (N + a : ℕ) = N + b := Nat.cast_injective hab
      omega
    · rintro x ⟨n, rfl⟩
      simpa using hroot (N + n) (Nat.le_add_right N n)
  · set Q : Polynomial ℚ := Polynomial.X ^ k with hQdef
    have hQne : Q ≠ 0 := by
      rw [hQdef]; exact pow_ne_zero _ Polynomial.X_ne_zero
    have hdeg : Q.degree < P.degree := by
      rw [hQdef, Polynomial.degree_X_pow, Polynomial.degree_eq_natDegree hPne]
      exact WithBot.coe_lt_coe.mpr hcon
    have hev : ∀ᶠ n : ℕ in atTop, C < |P.eval (n : ℚ) / Q.eval (n : ℚ)| :=
      Filter.Eventually.natCast_atTop (R := ℚ) <|
        (Polynomial.abs_div_tendsto_atTop_atTop_of_degree_gt P Q hdeg hQne).eventually
          (eventually_gt_atTop C)
    obtain ⟨M, hM⟩ := eventually_atTop.mp hev
    set n : ℕ := max (max M N) 1 with hn
    have hnM : M ≤ n := by
      rw [hn]; exact le_trans (le_max_left M N) (le_max_left (max M N) 1)
    have hnN : N ≤ n := by
      rw [hn]; exact le_trans (le_max_right M N) (le_max_left (max M N) 1)
    have hn1 : 1 ≤ n := by
      rw [hn]; exact le_max_right (max M N) 1
    have hrw : Q.eval (n : ℚ) = (n : ℚ) ^ k := by
      rw [hQdef, Polynomial.eval_pow, Polynomial.eval_X]
    have hbound := hM n hnM
    rw [hrw] at hbound
    have hpowpos : 0 < (n : ℚ) ^ k := by
      apply pow_pos
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
    have habs : |P.eval (n : ℚ) / (n : ℚ) ^ k| = |P.eval (n : ℚ)| / (n : ℚ) ^ k := by
      rw [abs_div, abs_of_pos hpowpos]
    rw [habs] at hbound
    have hmul : C * (n : ℚ) ^ k < |P.eval (n : ℚ)| := (lt_div_iff₀ hpowpos).mp hbound
    exact absurd hmul (not_lt.mpr (h n hnN))

end Commons.Algebra.Polynomial
end


-- ==== from Submission.Commons.Algebra.Polynomial.le_natDegree_of_eventually_le_eval ====
section

namespace Commons.Algebra.Polynomial

private theorem le_natDegree_of_eventually_le_eval {P : Polynomial ℚ} {k : ℕ} {C : ℚ} {N : ℕ}
    (hC : 0 < C) (h : ∀ n : ℕ, N ≤ n → C * (n : ℚ) ^ k ≤ P.eval (n : ℚ)) :
    k ≤ P.natDegree := by
  by_contra hcon
  rw [not_le] at hcon
  have hk : 0 < k := lt_of_le_of_lt (Nat.zero_le _) hcon
  set Q : Polynomial ℚ := Polynomial.X ^ k with hQ
  have hQeval : ∀ x : ℚ, Q.eval x = x ^ k := by
    intro x; rw [hQ, Polynomial.eval_pow, Polynomial.eval_X]
  have hdeg : P.degree < Q.degree := by
    rw [hQ, Polynomial.degree_X_pow]
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree (WithBot.coe_lt_coe.mpr hcon)
  have htend : Filter.Tendsto (fun x : ℚ => P.eval x / Q.eval x) Filter.atTop (nhds 0) :=
    Polynomial.div_tendsto_atTop_zero_of_degree_lt P Q hdeg
  have hevQ : ∀ᶠ x : ℚ in Filter.atTop, P.eval x / Q.eval x < C :=
    htend.eventually (eventually_lt_nhds hC)
  have hevN : ∀ᶠ n : ℕ in Filter.atTop, P.eval (n : ℚ) / Q.eval (n : ℚ) < C :=
    Filter.Eventually.natCast_atTop hevQ
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hevN
  set n : ℕ := max M (max N 1) with hn
  have hnM : M ≤ n := le_max_left _ _
  have hnN : N ≤ n := le_trans (le_max_left N 1) (le_max_right M (max N 1))
  have hn1 : 1 ≤ n := le_trans (le_max_right N 1) (le_max_right M (max N 1))
  have hltC : P.eval (n : ℚ) / (n : ℚ) ^ k < C := by
    simpa only [hQeval] using hM n hnM
  have hpos : (0 : ℚ) < (n : ℚ) ^ k :=
    pow_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)) k
  have hle : C ≤ P.eval (n : ℚ) / (n : ℚ) ^ k := by
    rw [le_div_iff₀ hpos]
    exact h n hnN
  linarith

end Commons.Algebra.Polynomial
end


-- ==== from Submission.Commons.Algebra.Polynomial.EventuallyPoly.partialSum ====
section

namespace Commons.Algebra.Polynomial.EventuallyPoly

open Finset

noncomputable section

/-- Auxiliary polynomial whose value at `t` is `∑_{s<t} s ^ n`. -/
private def powSumPoly (n : ℕ) : _root_.Polynomial ℚ :=
  (_root_.Polynomial.bernoulli (n + 1) - _root_.Polynomial.C (_root_.bernoulli (n + 1))) *
    _root_.Polynomial.C (((n + 1 : ℕ) : ℚ)⁻¹)

private lemma powSumPoly_eval (n t : ℕ) :
    (powSumPoly n).eval (t : ℚ) = ∑ s ∈ Finset.range t, (s : ℚ) ^ n := by
  unfold powSumPoly
  rw [_root_.Polynomial.eval_mul, _root_.Polynomial.eval_sub, _root_.Polynomial.eval_C,
    _root_.Polynomial.eval_C, _root_.Polynomial.bernoulli_succ_eval]
  have hne : (((n : ℚ) + 1)) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

/-- Auxiliary polynomial whose value at `t` is `∑_{s<t} p.eval s`. -/
private def sumPoly (p : _root_.Polynomial ℚ) : _root_.Polynomial ℚ :=
  ∑ i ∈ Finset.range (p.natDegree + 1), _root_.Polynomial.C (p.coeff i) * powSumPoly i

private lemma sumPoly_eval (p : _root_.Polynomial ℚ) (t : ℕ) :
    (sumPoly p).eval (t : ℚ) = ∑ s ∈ Finset.range t, p.eval (s : ℚ) := by
  have h2 : (sumPoly p).eval (t : ℚ)
      = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * ∑ s ∈ Finset.range t, (s : ℚ) ^ i := by
    rw [sumPoly, _root_.Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro i _
    rw [_root_.Polynomial.eval_mul, _root_.Polynomial.eval_C, powSumPoly_eval]
  have h1 : (∑ s ∈ Finset.range t, p.eval (s : ℚ))
      = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * ∑ s ∈ Finset.range t, (s : ℚ) ^ i := by
    simp_rw [_root_.Polynomial.eval_eq_sum_range]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  rw [h2, ← h1]

end

private theorem partialSum {f : ℕ → ℚ}
    (hf : ∃ p : Polynomial ℚ, ∃ N : ℕ, ∀ t : ℕ, N ≤ t → f t = p.eval (t : ℚ)) :
    ∃ q : Polynomial ℚ, ∃ M : ℕ, ∀ t : ℕ, M ≤ t →
      (∑ s ∈ Finset.range t, f s) = q.eval (t : ℚ) := by
  obtain ⟨p, N, hfN⟩ := hf
  refine ⟨sumPoly p + Polynomial.C ((∑ s ∈ Finset.range N, f s) - (sumPoly p).eval (N : ℚ)),
    N, ?_⟩
  intro t ht
  rw [Polynomial.eval_add, Polynomial.eval_C]
  have hIcoF : ∑ s ∈ Finset.Ico N t, f s = ∑ s ∈ Finset.Ico N t, p.eval (s : ℚ) := by
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.mem_Ico] at hs
    exact hfN s hs.1
  have hIcoP : ∑ s ∈ Finset.Ico N t, p.eval (s : ℚ)
      = (∑ s ∈ Finset.range t, p.eval (s : ℚ))
        - (∑ s ∈ Finset.range N, p.eval (s : ℚ)) :=
    Finset.sum_Ico_eq_sub _ ht
  calc ∑ s ∈ Finset.range t, f s
      = ∑ s ∈ Finset.range N, f s + ∑ s ∈ Finset.Ico N t, f s := by
        rw [Finset.sum_range_add_sum_Ico f ht]
    _ = ∑ s ∈ Finset.range N, f s + ∑ s ∈ Finset.Ico N t, p.eval (s : ℚ) := by rw [hIcoF]
    _ = ∑ s ∈ Finset.range N, f s
          + ((∑ s ∈ Finset.range t, p.eval (s : ℚ))
              - (∑ s ∈ Finset.range N, p.eval (s : ℚ))) := by rw [hIcoP]
    _ = (sumPoly p).eval (t : ℚ)
          + ((∑ s ∈ Finset.range N, f s) - (sumPoly p).eval (N : ℚ)) := by
        rw [sumPoly_eval p t, sumPoly_eval p N]
        ring

end Commons.Algebra.Polynomial.EventuallyPoly
end


-- ==== from Submission.Commons.RingTheory.Ideal.Hilbert.homogeneous_prime_avoidance ====
section

namespace Commons.RingTheory.Ideal.Hilbert

open MvPolynomial

noncomputable section

private theorem aux {k : Type*} [Field k] {m : ℕ}
    (I : Ideal (MvPolynomial (Fin m) k))
    (hI : ∀ x ∈ I, ∀ j, MvPolynomial.homogeneousComponent j x ∈ I) :
    ∀ (n : ℕ) (q : Fin n → Ideal (MvPolynomial (Fin m) k)),
      (∀ i, (q i).IsPrime) →
      (∀ i, ∀ x ∈ q i, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q i) →
      (∀ i, ¬ I ≤ q i) →
      ∃ (e : ℕ) (f : MvPolynomial (Fin m) k), f.IsHomogeneous e ∧ f ∈ I ∧ ∀ i, f ∉ q i := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n IH =>
    rcases n with _ | _ | n
    · intro q hqprime hqhom hqI
      exact ⟨0, 0, MvPolynomial.isHomogeneous_zero (Fin m) k 0, I.zero_mem,
        fun i => absurd i.isLt (Nat.not_lt_zero i.val)⟩
    · intro q hqprime hqhom hqI
      obtain ⟨g, hgI, hgq⟩ : ∃ g ∈ I, g ∉ q 0 := by
        by_contra h
        apply hqI 0
        intro x hx
        by_contra hx'
        exact h ⟨x, hx, hx'⟩
      obtain ⟨j, hj⟩ : ∃ j, MvPolynomial.homogeneousComponent j g ∉ q 0 := by
        by_contra h
        apply hgq
        rw [← MvPolynomial.sum_homogeneousComponent g]
        apply Ideal.sum_mem
        intro j _
        by_contra h'
        exact h ⟨j, h'⟩
      refine ⟨j, MvPolynomial.homogeneousComponent j g,
        MvPolynomial.homogeneousComponent_isHomogeneous j g, hI g hgI j, fun i => ?_⟩
      rw [Fin.eq_zero i]
      exact hj
    · intro q hqprime hqhom hqI
      by_contra hcon
      have hcon' : ∀ (e : ℕ) (f : MvPolynomial (Fin m) k),
          f.IsHomogeneous e → f ∈ I → ∃ i, f ∈ q i := by
        intro e f he hfI
        by_contra h
        exact hcon ⟨e, f, he, hfI, fun i hfi => h ⟨i, hfi⟩⟩
      have hkey : ∀ i : Fin (n + 2), ∃ (e : ℕ) (x : MvPolynomial (Fin m) k),
          x.IsHomogeneous e ∧ x ∈ I ∧ ∀ j : Fin (n + 1), x ∉ q (i.succAbove j) := by
        intro i
        exact IH (n + 1) (by omega) (fun j => q (i.succAbove j))
          (fun j => hqprime _) (fun j => hqhom _) (fun j => hqI _)
      let E : Fin (n + 2) → ℕ := fun i => Classical.choose (hkey i)
      let X : Fin (n + 2) → MvPolynomial (Fin m) k :=
        fun i => Classical.choose (Classical.choose_spec (hkey i))
      have hX : ∀ i, (X i).IsHomogeneous (E i) ∧ X i ∈ I ∧
          ∀ j : Fin (n + 1), X i ∉ q (i.succAbove j) :=
        fun i => Classical.choose_spec (Classical.choose_spec (hkey i))
      have hXq : ∀ i, X i ∈ q i := by
        intro i
        obtain ⟨k, hk⟩ := hcon' (E i) (X i) (hX i).1 (hX i).2.1
        by_cases hki : k = i
        · rw [hki] at hk; exact hk
        · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hki
          rw [← hj] at hk
          exact absurd hk ((hX i).2.2 j)
      have hXne : ∀ i, X i ≠ 0 := by
        intro i h0
        have hmem : (0 : MvPolynomial (Fin m) k) ∈ q (i.succAbove 0) := (q _).zero_mem
        rw [← h0] at hmem
        exact (hX i).2.2 0 hmem
      have hEpos : ∀ i, 1 ≤ E i := by
        intro i
        rw [Nat.one_le_iff_ne_zero]
        intro hE0
        have hhom0 : (X i).IsHomogeneous 0 := hE0 ▸ (hX i).1
        have htd : (X i).totalDegree = 0 := hhom0.totalDegree (hXne i)
        have hCe : X i = MvPolynomial.C ((X i).coeff 0) :=
          MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp htd
        have hc : (X i).coeff 0 ≠ 0 := by
          intro hc
          exact hXne i (by rw [hCe, hc, map_zero])
        have hunit : IsUnit (X i) := by
          rw [hCe]
          exact IsUnit.map MvPolynomial.C (isUnit_iff_ne_zero.mpr hc)
        exact (hqprime i).ne_top (Ideal.eq_top_of_isUnit_mem (q i) (hXq i) hunit)
      let M : ℕ := ∏ j : Fin (n + 1), E ((0 : Fin (n + 2)).succAbove j)
      let B : Fin (n + 1) → ℕ := fun j =>
        E 0 * ∏ j' ∈ Finset.univ.erase j, E ((0 : Fin (n + 2)).succAbove j')
      let a : ℕ := (n + 1) * M
      let z : MvPolynomial (Fin m) k :=
        (X 0)^a + ∏ j : Fin (n + 1), (X ((0 : Fin (n + 2)).succAbove j))^(B j)
      have hM : 1 ≤ M := Finset.one_le_prod' (fun j _ => hEpos _)
      have ha : 0 < a := by
        have : a = (n + 1) * M := rfl
        rw [this]
        exact Nat.mul_pos (by omega) (by omega)
      have hBpos : ∀ j, 0 < B j := by
        intro j
        have hB : B j = E 0 * ∏ j' ∈ Finset.univ.erase j, E ((0 : Fin (n + 2)).succAbove j') := rfl
        rw [hB]
        have h1 : 1 ≤ ∏ j' ∈ Finset.univ.erase j, E ((0 : Fin (n + 2)).succAbove j') :=
          Finset.one_le_prod' (fun j' _ => hEpos _)
        have h2 : 1 ≤ E 0 * ∏ j' ∈ Finset.univ.erase j, E ((0 : Fin (n + 2)).succAbove j') :=
          Nat.mul_le_mul (hEpos (0 : Fin (n + 2))) h1
        omega
      have hzI : z ∈ I := by
        have hzdef : z = (X 0)^a + ∏ j : Fin (n + 1), (X ((0 : Fin (n + 2)).succAbove j))^(B j) := rfl
        rw [hzdef]
        exact I.add_mem (I.pow_mem_of_mem (hX 0).2.1 a ha)
          (Ideal.prod_mem I (Finset.mem_univ (0 : Fin (n + 1)))
            (I.pow_mem_of_mem (hX _).2.1 (B 0) (hBpos 0)))
      have hdeg : (∑ j ∈ Finset.univ, E ((0 : Fin (n + 2)).succAbove j) * B j) = E 0 * a := by
        have hterm : ∀ j : Fin (n + 1), E ((0 : Fin (n + 2)).succAbove j) * B j = E 0 * M := by
          intro j
          have h1 : E ((0 : Fin (n + 2)).succAbove j) *
              ∏ j' ∈ Finset.univ.erase j, E ((0 : Fin (n + 2)).succAbove j') = M :=
            Finset.mul_prod_erase Finset.univ (fun j' => E ((0 : Fin (n + 2)).succAbove j')) (Finset.mem_univ j)
          have hB : B j = E 0 * ∏ j' ∈ Finset.univ.erase j, E ((0 : Fin (n + 2)).succAbove j') := rfl
          rw [hB, ← h1]
          ring
        rw [Finset.sum_congr rfl (fun j _ => hterm j)]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        have : a = (n + 1) * M := rfl
        rw [this, smul_eq_mul]
        ring
      have hz_hom : z.IsHomogeneous (E 0 * a) := by
        have h1 : ((X 0)^a).IsHomogeneous (E 0 * a) := (hX 0).1.pow a
        have h2 : (∏ j : Fin (n + 1),
            (X ((0 : Fin (n + 2)).succAbove j))^(B j)).IsHomogeneous (E 0 * a) := by
          rw [← hdeg]
          exact IsHomogeneous.prod Finset.univ
            (fun j => (X ((0 : Fin (n + 2)).succAbove j))^(B j))
            (fun j => E ((0 : Fin (n + 2)).succAbove j) * B j)
            (fun j _ => (hX _).1.pow (B j))
        have hzdef : z = (X 0)^a + ∏ j : Fin (n + 1), (X ((0 : Fin (n + 2)).succAbove j))^(B j) := rfl
        rw [hzdef]
        exact h1.add h2
      have hzq : ∀ i, z ∉ q i := by
        intro i
        by_cases hi : i = 0
        · rw [hi]
          intro hz
          have h1 : (X 0)^a ∈ q 0 := (q 0).pow_mem_of_mem (hXq 0) a ha
          have hprod : (∏ j : Fin (n + 1), (X ((0 : Fin (n + 2)).succAbove j))^(B j)) ∈ q 0 := by
            have heq : (∏ j : Fin (n + 1), (X ((0 : Fin (n + 2)).succAbove j))^(B j)) = z - (X 0)^a := by
              have hzdef : z = (X 0)^a + ∏ j : Fin (n + 1), (X ((0 : Fin (n + 2)).succAbove j))^(B j) := rfl
              rw [hzdef]; ring
            rw [heq]
            exact (q 0).sub_mem hz h1
          rw [Ideal.IsPrime.prod_mem_iff (hp := hqprime 0)] at hprod
          obtain ⟨j, -, hjq⟩ := hprod
          have hnot : X ((0 : Fin (n + 2)).succAbove j) ∉ q 0 := by
            obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq (Fin.succAbove_ne (0 : Fin (n + 2)) j).symm
            have hh := (hX ((0 : Fin (n + 2)).succAbove j)).2.2 j'
            rw [hj'] at hh
            exact hh
          exact hnot (((hqprime 0).pow_mem_iff_mem (B j) (hBpos j)).mp hjq)
        · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hi
          intro hz
          have hx0 : X (0 : Fin (n + 2)) ∉ q i := by
            rw [← hj]
            exact (hX 0).2.2 j
          have h1 : (X 0)^a ∉ q i := fun hh => hx0 (((hqprime i).pow_mem_iff_mem a ha).mp hh)
          have hprod : (∏ j : Fin (n + 1), (X ((0 : Fin (n + 2)).succAbove j))^(B j)) ∈ q i := by
            apply Ideal.prod_mem (q i) (Finset.mem_univ j)
            rw [hj]
            exact (q i).pow_mem_of_mem (hXq i) (B j) (hBpos j)
          refine h1 ?_
          have heq : (X 0)^a = z - (∏ j : Fin (n + 1), (X ((0 : Fin (n + 2)).succAbove j))^(B j)) := by
            have hzdef : z = (X 0)^a + ∏ j : Fin (n + 1), (X ((0 : Fin (n + 2)).succAbove j))^(B j) := rfl
            rw [hzdef]; ring
          rw [heq]
          exact (q i).sub_mem hz hprod
      exact hcon ⟨E 0 * a, z, hz_hom, hzI, hzq⟩

private theorem homogeneous_prime_avoidance {k : Type*} [Field k] {m : ℕ}
    (I : Ideal (MvPolynomial (Fin m) k))
    (hI : ∀ x ∈ I, ∀ j, MvPolynomial.homogeneousComponent j x ∈ I)
    (P : Finset (Ideal (MvPolynomial (Fin m) k)))
    (hPprime : ∀ p ∈ P, p.IsPrime)
    (hPhom : ∀ p ∈ P, ∀ x ∈ p, ∀ j, MvPolynomial.homogeneousComponent j x ∈ p)
    (hIP : ∀ p ∈ P, ¬ I ≤ p) :
    ∃ (e : ℕ) (f : MvPolynomial (Fin m) k), f.IsHomogeneous e ∧ f ∈ I ∧ ∀ p ∈ P, f ∉ p := by
  classical
  obtain ⟨e, f, hh, hI', hp⟩ := aux I hI P.card
    (fun i => (P.equivFin.symm i : {x // x ∈ P}).1)
    (fun i => hPprime _ (P.equivFin.symm i).2)
    (fun i => hPhom _ (P.equivFin.symm i).2)
    (fun i => hIP _ (P.equivFin.symm i).2)
  refine ⟨e, f, hh, hI', fun p hp_mem => ?_⟩
  simpa using hp (P.equivFin ⟨p, hp_mem⟩)

end

end Commons.RingTheory.Ideal.Hilbert
end


-- ==== from Submission.Commons.Algebra.MvPolynomial.sum_finrank_homogeneous_le_finrank ====
section

namespace Commons.Algebra.MvPolynomial

set_option linter.style.haveILetI false in
/-- If `I` is a graded (homogeneous) ideal of `MvPolynomial σ K` and the quotient is finite
dimensional, then for every bound `M` the sum of the `K`-dimensions of the images in the
quotient of the homogeneous pieces of degree `< M` is bounded by the dimension of the quotient.
This is the degree-independence (graded direct sum) of `MvPolynomial σ K ⧸ I`. -/
private theorem finrank_sum_map_homogeneousSubmodule_le {σ K : Type*} [Field K] [Fintype σ]
    [DecidableEq σ] (I : Ideal (MvPolynomial σ K))
    (hI : ∀ (j : ℕ) (p : MvPolynomial σ K),
      p ∈ I → MvPolynomial.homogeneousComponent j p ∈ I)
    [Module.Finite K (MvPolynomial σ K ⧸ I)] (M : ℕ) :
    ∑ j : Fin M, Module.finrank K ↥(Submodule.map ((I.mkQ).restrictScalars K)
        (MvPolynomial.homogeneousSubmodule σ K j.val)) ≤
      Module.finrank K (MvPolynomial σ K ⧸ I) := by
  classical
  let S : ℕ → Submodule K (MvPolynomial σ K ⧸ I) := fun j =>
    Submodule.map ((I.mkQ).restrictScalars K) (MvPolynomial.homogeneousSubmodule σ K j)
  have hker : ∀ p : MvPolynomial σ K, (I.mkQ.restrictScalars K) p = 0 ↔ p ∈ I := by
    intro p
    rw [LinearMap.restrictScalars_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  let F : ((j : Fin M) → ↥(S j.val)) →ₗ[K] (MvPolynomial σ K ⧸ I) :=
    { toFun := fun x => ∑ j : Fin M, ((x j : ↥(S j.val)) : MvPolynomial σ K ⧸ I)
      map_add' := fun x y => by
        simp only [Pi.add_apply, Submodule.coe_add, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        simp only [Pi.smul_apply, Submodule.coe_smul, Finset.smul_sum, RingHom.id_apply] }
  have hF_apply : ∀ x, F x = ∑ j : Fin M, ((x j : ↥(S j.val)) : MvPolynomial σ K ⧸ I) :=
    fun x => rfl
  have hzero : ∀ z : (j : Fin M) → ↥(S j.val), F z = 0 → z = 0 := by
    intro z hz0
    choose t ht_mem ht_eq using fun j : Fin M => Submodule.mem_map.mp (z j).property
    have hqP : (I.mkQ.restrictScalars K) (∑ j : Fin M, t j) = 0 := by
      rw [map_sum]
      have hsum : (∑ j : Fin M, (I.mkQ.restrictScalars K) (t j))
          = ∑ j : Fin M, ((z j : ↥(S j.val)) : MvPolynomial σ K ⧸ I) :=
        Finset.sum_congr rfl (fun j _ => ht_eq j)
      rw [hsum, ← hF_apply z]; exact hz0
    have hP : (∑ j : Fin M, t j) ∈ I := (hker _).mp hqP
    funext i
    apply Subtype.ext
    show ((z i : ↥(S i.val)) : MvPolynomial σ K ⧸ I) = 0
    rw [← ht_eq i]
    apply (hker (t i)).mpr
    have h1 : (∑ j : Fin M, MvPolynomial.homogeneousComponent i.val (t j)) ∈ I := by
      have hh := hI i.val (∑ j : Fin M, t j) hP
      rwa [map_sum] at hh
    have heq : (∑ j : Fin M, MvPolynomial.homogeneousComponent i.val (t j))
        = ∑ j : Fin M, (if i.val = j.val then t j else 0) :=
      Finset.sum_congr rfl (fun j _ =>
        MvPolynomial.homogeneousComponent_of_mem (ht_mem j))
    have hsum2 : (∑ j : Fin M, (if i.val = j.val then t j else 0)) = t i := by
      rw [Fintype.sum_eq_single i]
      · simp
      · intro j hj
        rw [if_neg (fun h => hj (Fin.ext h).symm)]
    rw [heq, hsum2] at h1
    exact h1
  have hinj : Function.Injective F := by
    intro x y hxy
    have h0 : F (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hres := hzero (x - y) h0
    exact sub_eq_zero.mp hres
  haveI : ∀ j : Fin M, Module.Finite K ↥(S j.val) := fun j =>
    Module.Finite.of_fg (Submodule.FG.map ((I.mkQ).restrictScalars K)
      (MvPolynomial.homogeneousSubmodule_fg σ K j.val))
  have hle := LinearMap.finrank_le_finrank_of_injective (f := F) hinj
  rwa [Module.finrank_pi_fintype] at hle

private theorem sum_finrank_homogeneous_le_finrank {k : Type*} [Field k] {m : ℕ}
    (q : Ideal (MvPolynomial (Fin m) k))
    (hq : ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q)
    [Module.Finite k (MvPolynomial (Fin m) k ⧸ q)] :
    ∀ t : ℕ, (∑ u ∈ Finset.range (t + 1), Module.finrank k
      (Submodule.map (q.mkQ.restrictScalars k) (MvPolynomial.homogeneousSubmodule (Fin m) k u)))
      ≤ Module.finrank k (MvPolynomial (Fin m) k ⧸ q) := by
  intro t
  have h := finrank_sum_map_homogeneousSubmodule_le (σ := Fin m) (K := k) q
    (fun j p hp => hq p hp j) (t + 1)
  have h2 : (∑ u ∈ Finset.range (t + 1), Module.finrank k
        (Submodule.map (q.mkQ.restrictScalars k)
          (MvPolynomial.homogeneousSubmodule (Fin m) k u)))
      = ∑ j : Fin (t + 1), Module.finrank k
        (Submodule.map (q.mkQ.restrictScalars k)
          (MvPolynomial.homogeneousSubmodule (Fin m) k j.val)) :=
    (Fin.sum_univ_eq_sum_range (fun u => Module.finrank k
      (Submodule.map (q.mkQ.restrictScalars k)
        (MvPolynomial.homogeneousSubmodule (Fin m) k u))) (t + 1)).symm
  rw [h2]
  exact h

end Commons.Algebra.MvPolynomial
end


-- ==== from Submission.Commons.RingTheory.Ideal.Hilbert.hilbert_sum_upper_bound ====
section

open MvPolynomial

namespace Commons.RingTheory.Ideal.Hilbert

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## Membership in the irrelevant ideal -/

private lemma mem_idealOfVars_iff_coeff_zero_hub {σ : Type*} {K : Type*} [Field K]
    (x : MvPolynomial σ K) :
    x ∈ MvPolynomial.idealOfVars σ K ↔ MvPolynomial.coeff 0 x = 0 := by
  rw [MvPolynomial.idealOfVars,
    show Set.range (MvPolynomial.X) = MvPolynomial.X '' (Set.univ : Set σ) from by simp,
    MvPolynomial.mem_ideal_span_X_image]
  constructor
  · intro h
    by_contra hc
    have hm : (0 : σ →₀ ℕ) ∈ x.support := MvPolynomial.mem_support_iff.mpr hc
    obtain ⟨i, -, hi⟩ := h 0 hm
    exact hi (by simp)
  · intro h m hm
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact (MvPolynomial.mem_support_iff.mp hm) h
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hm0
    exact ⟨i, Set.mem_univ i, hi⟩

private lemma idealOfVars_eq_ker_constantCoeff {k : Type*} [Field k] {m : ℕ} :
    MvPolynomial.idealOfVars (Fin m) k = RingHom.ker MvPolynomial.constantCoeff := by
  ext x
  rw [RingHom.mem_ker, mem_idealOfVars_iff_coeff_zero_hub, MvPolynomial.constantCoeff_eq]

private def idealOfVars_isMaximal {k : Type*} [Field k] {m : ℕ} :
    (MvPolynomial.idealOfVars (Fin m) k).IsMaximal := by
  rw [idealOfVars_eq_ker_constantCoeff]
  exact RingHom.ker_isMaximal_of_surjective MvPolynomial.constantCoeff
    (fun x => ⟨MvPolynomial.C x, by simp⟩)
attribute [local instance] idealOfVars_isMaximal

private lemma idealOfVars_homogeneousComponent_mem {k : Type*} [Field k] {m : ℕ}
    {x : MvPolynomial (Fin m) k} (hx : x ∈ MvPolynomial.idealOfVars (Fin m) k) (j : ℕ) :
    MvPolynomial.homogeneousComponent j x ∈ MvPolynomial.idealOfVars (Fin m) k := by
  rw [mem_idealOfVars_iff_coeff_zero_hub] at hx ⊢
  rw [MvPolynomial.coeff_homogeneousComponent]
  have h0 : Finsupp.degree (0 : Fin m →₀ ℕ) = 0 := by simp
  rw [h0]
  by_cases hj : (0 : ℕ) = j
  · simp [hj, hx]
  · simp [hj]

/-! ## Minimal primes of a homogeneous ideal -/

private theorem minimalPrimes_homogeneousComponent_mem {k : Type*} [Field k] {m : ℕ}
    {q : Ideal (MvPolynomial (Fin m) k)}
    (hq : ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q)
    {p : Ideal (MvPolynomial (Fin m) k)} (hp : p ∈ q.minimalPrimes) :
    ∀ x ∈ p, ∀ j, MvPolynomial.homogeneousComponent j x ∈ p := by
  classical
  have hcore : (Ideal.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin m) k) p).toIdeal.IsPrime :=
    hp.1.1.homogeneousCore
  have hqle : q ≤ (Ideal.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin m) k) p).toIdeal := by
    intro x hx
    rw [← MvPolynomial.sum_homogeneousComponent x]
    refine Ideal.sum_mem _ fun j _ => ?_
    exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem
      ⟨j, MvPolynomial.homogeneousComponent_mem j x⟩ (hp.1.2 (hq x hx j))
  have heq : (Ideal.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin m) k) p).toIdeal = p :=
    le_antisymm (Ideal.toIdeal_homogeneousCore_le _ p)
      (hp.2 ⟨hcore, hqle⟩ (Ideal.toIdeal_homogeneousCore_le _ p))
  intro x hx j
  rw [← heq] at hx
  have h := (MvPolynomial.mem_iff_homogeneousComponent_mem
    (HomogeneousIdeal.isHomogeneous (Ideal.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin m) k) p))
    x).mp hx j
  rwa [heq] at h

private theorem minimalPrimes_le_idealOfVars_hub {k : Type*} [Field k] {m : ℕ}
    {q : Ideal (MvPolynomial (Fin m) k)}
    (hq : ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q)
    {p : Ideal (MvPolynomial (Fin m) k)} (hp : p ∈ q.minimalPrimes) :
    p ≤ MvPolynomial.idealOfVars (Fin m) k := by
  intro x hx
  rw [mem_idealOfVars_iff_coeff_zero_hub]
  have hx0 : MvPolynomial.homogeneousComponent 0 x ∈ p :=
    minimalPrimes_homogeneousComponent_mem hq hp x hx 0
  rw [MvPolynomial.homogeneousComponent_zero] at hx0
  by_contra hne
  have h1 : (1 : MvPolynomial (Fin m) k) ∈ p := by
    have hmem := p.mul_mem_left (MvPolynomial.C (MvPolynomial.coeff 0 x)⁻¹) hx0
    rwa [← MvPolynomial.C_mul, inv_mul_cancel₀ hne, MvPolynomial.C_1] at hmem
  exact hp.1.1.ne_top ((Ideal.eq_top_iff_one p).mpr h1)

/-- If a minimal prime of `q` contains the irrelevant ideal, then `ringKrullDim (S ⧸ q) ≤ 0`. -/
private theorem ringKrullDim_le_zero_of_minimalPrimes_idealOfVars_le {k : Type*} [Field k] {m : ℕ}
    {q : Ideal (MvPolynomial (Fin m) k)}
    (hq : ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q)
    {p : Ideal (MvPolynomial (Fin m) k)} (hp : p ∈ q.minimalPrimes)
    (hle : MvPolynomial.idealOfVars (Fin m) k ≤ p) :
    ringKrullDim (MvPolynomial (Fin m) k ⧸ q) ≤ ((0 : ℕ) : WithBot ℕ∞) := by
  have hp_le : p ≤ MvPolynomial.idealOfVars (Fin m) k := minimalPrimes_le_idealOfVars_hub hq hp
  have hp_eq : p = MvPolynomial.idealOfVars (Fin m) k := le_antisymm hp_le hle
  have hmax : ∀ J ∈ q.minimalPrimes, J.IsMaximal := by
    intro J hJ
    have hJle : J ≤ MvPolynomial.idealOfVars (Fin m) k := minimalPrimes_le_idealOfVars_hub hq hJ
    have hJle_p : J ≤ p := le_trans hJle (le_of_eq hp_eq.symm)
    have hp_le_J : p ≤ J := hp.2 ⟨hJ.1.1, hJ.1.2⟩ hJle_p
    rw [le_antisymm hJle_p hp_le_J, hp_eq]
    exact idealOfVars_isMaximal
  have h0 : Ring.KrullDimLE 0 (MvPolynomial (Fin m) k ⧸ q) :=
    Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr hmax
  exact Ring.krullDimLE_iff.mp h0

private theorem homogeneous_span_singleton {k : Type*} [Field k] {m : ℕ}
    {f : MvPolynomial (Fin m) k} {e : ℕ} (hf : f.IsHomogeneous e) :
    Ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin m) k) (Ideal.span {f}) :=
  Ideal.homogeneous_span (MvPolynomial.homogeneousSubmodule (Fin m) k) {f}
    (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      exact ⟨e, (MvPolynomial.mem_homogeneousSubmodule e x).mpr (hx ▸ hf)⟩)

/-! ## Dimension drop by a homogeneous element -/

private theorem ringKrullDim_quotient_sup_span_le {R : Type*} [CommRing R] (q : Ideal R) (f : R)
    (hqf : ∀ p ∈ q.minimalPrimes, f ∉ p) {n : ℕ}
    (hd : ringKrullDim (R ⧸ q) ≤ ((n + 1 : ℕ) : WithBot ℕ∞)) :
    ringKrullDim (R ⧸ (q ⊔ Ideal.span {f})) ≤ ((n : ℕ) : WithBot ℕ∞) := by
  have hdk : Order.krullDim ↥(PrimeSpectrum.zeroLocus (q : Set R)) ≤ ((n + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← ringKrullDim_quotient]; exact hd
  rw [ringKrullDim_quotient]
  have hsub : PrimeSpectrum.zeroLocus ((q ⊔ Ideal.span {f} : Ideal R) : Set R)
      ⊆ PrimeSpectrum.zeroLocus (q : Set R) :=
    PrimeSpectrum.zeroLocus_anti_mono (by intro x hx; exact le_sup_left (a := q) hx)
  rcases isEmpty_or_nonempty ↥(PrimeSpectrum.zeroLocus ((q ⊔ Ideal.span {f} : Ideal R) : Set R)) with hem | hne
  · rw [Order.krullDim_eq_bot]; exact bot_le
  · have h2 : (⨆ p : LTSeries ↥(PrimeSpectrum.zeroLocus ((q ⊔ Ideal.span {f} : Ideal R) : Set R)),
        ((p.length : ℕ) : ℕ∞)) ≤ ((n : ℕ) : ℕ∞) := by
      apply iSup_le
      intro l
      have hmono : StrictMono (fun x : ↥(PrimeSpectrum.zeroLocus ((q ⊔ Ideal.span {f} : Ideal R) : Set R)) =>
          (⟨x.1, hsub x.2⟩ : ↥(PrimeSpectrum.zeroLocus (q : Set R)))) := fun a b h => h
      let lq : LTSeries ↥(PrimeSpectrum.zeroLocus (q : Set R)) := l.map _ hmono
      have hlqlen : lq.length = l.length := rfl
      haveI : (lq.head.1.asIdeal).IsPrime := lq.head.1.isPrime
      have hqle : q ≤ lq.head.1.asIdeal :=
        (PrimeSpectrum.mem_zeroLocus _ _).mp lq.head.2
      obtain ⟨p0, hp0mem, hp0le⟩ := Ideal.exists_minimalPrimes_le (I := q) (J := lq.head.1.asIdeal) hqle
      have hfmem : f ∈ lq.head.1.asIdeal := by
        have h1 : (q ⊔ Ideal.span {f} : Ideal R) ≤ l.head.1.asIdeal :=
          (PrimeSpectrum.mem_zeroLocus _ _).mp l.head.2
        exact h1 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
      have hfnot : f ∉ p0 := hqf p0 hp0mem
      let P0 : PrimeSpectrum R := ⟨p0, hp0mem.1.1⟩
      have hP0mem : P0 ∈ PrimeSpectrum.zeroLocus (q : Set R) :=
        (PrimeSpectrum.mem_zeroLocus _ _).mpr hp0mem.1.2
      have hp0lt : (⟨P0, hP0mem⟩ : ↥(PrimeSpectrum.zeroLocus (q : Set R))) < lq.head := by
        refine lt_of_le_of_ne (show P0 ≤ lq.head.1 from hp0le) ?_
        intro hcon
        have h2 : p0 = lq.head.1.asIdeal := by
          simpa [P0] using congrArg (fun x : ↥(PrimeSpectrum.zeroLocus (q : Set R)) => x.1.asIdeal) hcon
        exact hfnot (h2.symm ▸ hfmem)
      let l' : LTSeries ↥(PrimeSpectrum.zeroLocus (q : Set R)) := lq.cons _ hp0lt
      have hlen : l'.length = l.length + 1 := by
        rw [RelSeries.cons_length, hlqlen]
      have hbound := Order.LTSeries.length_le_krullDim l'
      rw [hlen] at hbound
      have hbound' : l.length + 1 ≤ n + 1 := by
        exact_mod_cast hbound.trans hdk
      rw [ENat.natCast_le_natCast]
      omega
    rw [Order.krullDim_eq_iSup_length]
    exact WithBot.coe_le_coe.mpr h2

/-! ## The recursion inequality for Hilbert functions -/

private theorem hilbertFun_recursion {k : Type*} [Field k] {m : ℕ}
    (q : Ideal (MvPolynomial (Fin m) k))
    (hq : ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q)
    {f : MvPolynomial (Fin m) k} {e : ℕ}
    (hf : f.IsHomogeneous e) (u : ℕ) (he : e ≤ u) :
    hilbertFun q (homogeneousSubmodule (Fin m) k u)
      ≤ hilbertFun q (homogeneousSubmodule (Fin m) k (u - e))
        + hilbertFun (q ⊔ Ideal.span {f}) (homogeneousSubmodule (Fin m) k u) := by
  classical
  set q' : Ideal (MvPolynomial (Fin m) k) := q ⊔ Ideal.span {f} with hq'def
  set V : Submodule k (MvPolynomial (Fin m) k) := homogeneousSubmodule (Fin m) k u with hVdef
  set Ve : Submodule k (MvPolynomial (Fin m) k) := homogeneousSubmodule (Fin m) k (u - e) with hVedef
  set N : Submodule k (MvPolynomial (Fin m) k) := V ⊓ q.restrictScalars k with hNdef
  set M : Submodule k (MvPolynomial (Fin m) k) := V ⊓ q'.restrictScalars k with hMdef
  haveI hVfg : V.FG := by rw [hVdef]; exact homogeneousSubmodule_fg (Fin m) k u
  haveI hVfin : Module.Finite k ↥V := Module.Finite.of_fg hVfg
  haveI hVefg : Ve.FG := by rw [hVedef]; exact homogeneousSubmodule_fg (Fin m) k (u - e)
  haveI hVefin : Module.Finite k ↥Ve := Module.Finite.of_fg hVefg
  haveI hMfg : M.FG := Submodule.FG.of_le hVfg (by rw [hMdef]; exact inf_le_left)
  haveI hMfin : Module.Finite k ↥M := Module.Finite.of_fg hMfg
  haveI hNfg : N.FG := Submodule.FG.of_le hVfg (by rw [hNdef]; exact inf_le_left)
  haveI hNfin : Module.Finite k ↥N := Module.Finite.of_fg hNfg
  have hNM : N ≤ M := by
    rw [hNdef, hMdef]
    exact inf_le_inf_left V (by rw [hq'def]; exact Submodule.restrictScalars_mono k le_sup_left)
  set φ : MvPolynomial (Fin m) k →ₗ[k] (MvPolynomial (Fin m) k ⧸ q) :=
    (q.mkQ).restrictScalars k with hφdef
  set φ' : MvPolynomial (Fin m) k →ₗ[k] (MvPolynomial (Fin m) k ⧸ q') :=
    (q'.mkQ).restrictScalars k with hφ'def
  set ρ : (MvPolynomial (Fin m) k ⧸ q) →ₗ[k] (MvPolynomial (Fin m) k ⧸ q') :=
    (Ideal.Quotient.factorₐ k (le_sup_left : q ≤ q')).toLinearMap with hρdef
  have hρφ : ρ.comp φ = φ' := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, hφdef, hρdef, hφ'def]
    rw [show (Ideal.Quotient.factorₐ k (le_sup_left : q ≤ q')).toLinearMap
        ((q.mkQ).restrictScalars k x)
        = Ideal.Quotient.factor (le_sup_left : q ≤ q') (Ideal.Quotient.mk q x) from rfl,
      Ideal.Quotient.factor_mk]
    rfl
  haveI hφVfg : (Submodule.map φ V).FG := Submodule.FG.map φ hVfg
  haveI hφVfin : Module.Finite k ↥(Submodule.map φ V) := Module.Finite.of_fg hφVfg
  have step1 : Module.finrank k ↥(Submodule.map φ V)
      = Module.finrank k ↥(Submodule.map φ' V) + Module.finrank k ↥(Submodule.map φ V ⊓ ρ.ker) := by
    have h := Commons.RingTheory.Ideal.Hilbert.finrank_map_add_finrank_inf_ker (k := k) ρ
      (Submodule.map φ V)
    have hmap : Submodule.map ρ (Submodule.map φ V) = Submodule.map φ' V := by
      rw [← Submodule.map_comp, hρφ]
    rw [hmap] at h
    omega
  have step2 : Submodule.map φ V ⊓ ρ.ker = Submodule.map φ M := by
    apply le_antisymm
    · intro y hy
      rw [Submodule.mem_inf] at hy
      obtain ⟨hyW, hyker⟩ := hy
      rw [Submodule.mem_map] at hyW
      obtain ⟨x, hxV, rfl⟩ := hyW
      rw [LinearMap.mem_ker] at hyker
      have hxq' : x ∈ q' := by
        have h1 : Ideal.Quotient.mk q' x = 0 := by
          have h2 : φ' x = 0 := by
            rw [show φ' x = ρ (φ x) from (congrFun (congrArg DFunLike.coe hρφ) x).symm, hyker]
          rwa [hφ'def] at h2
        exact Ideal.Quotient.eq_zero_iff_mem.mp h1
      refine Submodule.mem_map.mpr ⟨x, ?_, rfl⟩
      simp only [hMdef, Submodule.mem_inf]
      exact ⟨hxV, hxq'⟩
    · rintro y ⟨x, hxM, rfl⟩
      simp only [hMdef, Submodule.mem_inf] at hxM
      obtain ⟨hxV, hxq'⟩ := hxM
      rw [Submodule.mem_inf]
      refine ⟨Submodule.mem_map.mpr ⟨x, hxV, rfl⟩, ?_⟩
      rw [LinearMap.mem_ker]
      rw [show ρ (φ x) = φ' x from congrFun (congrArg DFunLike.coe hρφ) x]
      rw [hφ'def]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hxq'
  have hφker : φ.ker = q.restrictScalars k := by
    simp only [hφdef, LinearMap.ker_restrictScalars, Submodule.ker_mkQ]
  have step3 : Module.finrank k ↥(Submodule.map φ M) = Module.finrank k ↥M - Module.finrank k ↥N := by
    have h := Commons.RingTheory.Ideal.Hilbert.finrank_map_add_finrank_inf_ker (k := k) φ M
    have hMN : M ⊓ φ.ker = N := by
      rw [hφker]
      show (M ⊓ q.restrictScalars k) = N
      rw [hMdef, hNdef]
      ext x
      simp only [Submodule.mem_inf]
      constructor
      · rintro ⟨⟨hxV, hxq'⟩, hxq⟩
        exact ⟨hxV, hxq⟩
      · rintro ⟨hxV, hxq⟩
        exact ⟨⟨hxV, (by rw [hq'def]; exact le_sup_left (a := q) (b := Ideal.span {f}) hxq)⟩, hxq⟩
    rw [hMN] at h
    omega
  have step4 : Module.finrank k ↥M - Module.finrank k ↥N
      ≤ hilbertFun q (homogeneousSubmodule (Fin m) k (u - e)) := by
    rw [hilbertFun_eq_sub, ← hVedef]
    set ψ : Ve →ₗ[k] (MvPolynomial (Fin m) k ⧸ N) :=
      { toFun := fun x => Submodule.mkQ N (f * (x : MvPolynomial (Fin m) k))
        map_add' := by intro x y; simp only [Submodule.coe_add, mul_add, map_add]
        map_smul' := by intro c x; simp only [SetLike.val_smul, mul_smul_comm, map_smul,
          RingHom.id_apply] } with hψdef
    have hψ_apply : ∀ x : Ve, ψ x = Submodule.mkQ N (f * (x : MvPolynomial (Fin m) k)) := fun x => rfl
    have hψ_range : ψ.range = Submodule.map (Submodule.mkQ N) M := by
      apply le_antisymm
      · rintro y ⟨x, rfl⟩
        refine Submodule.mem_map.mpr ⟨f * (x : MvPolynomial (Fin m) k), ?_, rfl⟩
        simp only [hMdef, Submodule.mem_inf]
        refine ⟨?_, ?_⟩
        · rw [hVdef, mem_homogeneousSubmodule]
          have hx : (x : MvPolynomial (Fin m) k).IsHomogeneous (u - e) := x.2
          have := hf.mul hx
          rwa [Nat.add_sub_cancel' he] at this
        · rw [hq'def]
          exact Ideal.mul_mem_right _ _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
      · rintro y ⟨z, hzM, rfl⟩
        simp only [hMdef, Submodule.mem_inf] at hzM
        obtain ⟨hzV, hzq'⟩ := hzM
        change z.IsHomogeneous u at hzV
        have hzq'ideal : z ∈ q' := hzq'
        rw [hq'def] at hzq'ideal
        obtain ⟨a, haq, b, hb, hab⟩ := Submodule.mem_sup.mp hzq'ideal
        rw [Ideal.mem_span_singleton] at hb
        obtain ⟨c, rfl⟩ := hb
        rw [LinearMap.mem_range]
        refine ⟨⟨homogeneousComponent (u - e) c, ?_⟩, ?_⟩
        · rw [hVedef, mem_homogeneousSubmodule]
          exact homogeneousComponent_isHomogeneous _ _
        · rw [hψ_apply]
          have hdecomp : z = homogeneousComponent u a + f * homogeneousComponent (u - e) c := by
            have h1 : z = homogeneousComponent u (a + f * c) := by
              rw [← hab, homogeneousComponent_eq_self (show (a + f * c).IsHomogeneous u from by
                rw [hab]; exact hzV)]
            rw [h1, map_add]
            congr 1
            rw [mul_comm f c]
            have h2 := Commons.Algebra.MvPolynomial.homogeneousComponent_mul_of_isHomogeneous_right
              hf c (u - e)
            rw [show (u - e) + e = u from Nat.sub_add_cancel he] at h2
            rw [h2, mul_comm]
          have haN : homogeneousComponent u a ∈ N := by
            simp only [hNdef, Submodule.mem_inf]
            exact ⟨mem_homogeneousSubmodule _ _ |>.mpr (homogeneousComponent_isHomogeneous _ _),
              hq a haq u⟩
          rw [hdecomp, map_add, show Submodule.mkQ N (homogeneousComponent u a) = 0 from by
            rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact haN, zero_add]
    have hrn := LinearMap.finrank_range_add_finrank_ker ψ
    rw [hψ_range] at hrn
    have hmapN : Module.finrank k ↥(Submodule.map (Submodule.mkQ N) M)
        = Module.finrank k ↥M - Module.finrank k ↥N := by
      have h := Commons.RingTheory.Ideal.Hilbert.finrank_map_add_finrank_inf_ker (k := k)
        (Submodule.mkQ N) M
      rw [Submodule.ker_mkQ, inf_eq_right.mpr hNM] at h
      omega
    rw [hmapN] at hrn
    set K0 : Submodule k ↥Ve := Submodule.comap Ve.subtype (Ve ⊓ q.restrictScalars k) with hK0
    have hK0_le : K0 ≤ ψ.ker := by
      intro x hx
      rw [hK0, Submodule.mem_comap, Submodule.mem_inf] at hx
      obtain ⟨-, hxq⟩ := hx
      rw [LinearMap.mem_ker, hψ_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      simp only [hNdef, Submodule.mem_inf]
      refine ⟨?_, ?_⟩
      · rw [mem_homogeneousSubmodule]
        have hx' : (x : MvPolynomial (Fin m) k).IsHomogeneous (u - e) := x.2
        have := hf.mul hx'
        rwa [Nat.add_sub_cancel' he] at this
      · exact Ideal.mul_mem_left q f (show (x : MvPolynomial (Fin m) k) ∈ q from hxq)
    have hfin_le : Module.finrank k ↥(Ve ⊓ q.restrictScalars k) ≤ Module.finrank k ↥ψ.ker := by
      have h1 : Module.finrank k ↥(Ve ⊓ q.restrictScalars k) = Module.finrank k ↥K0 := by
        have := Submodule.finrank_map_subtype_eq Ve K0
        rw [hK0, Submodule.map_comap_subtype, inf_eq_right.mpr inf_le_left] at this
        exact this
      rw [h1]
      exact Submodule.finrank_mono hK0_le
    omega
  have hmain : Module.finrank k ↥(Submodule.map φ V)
      ≤ Module.finrank k ↥(Submodule.map φ' V)
        + hilbertFun q (homogeneousSubmodule (Fin m) k (u - e)) := by
    rw [step1, step2, step3]
    exact Nat.add_le_add_left step4 _
  calc hilbertFun q (homogeneousSubmodule (Fin m) k u)
      = Module.finrank k ↥(Submodule.map φ V) := rfl
    _ ≤ Module.finrank k ↥(Submodule.map φ' V)
        + hilbertFun q (homogeneousSubmodule (Fin m) k (u - e)) := hmain
    _ = hilbertFun (q ⊔ Ideal.span {f}) (homogeneousSubmodule (Fin m) k u)
        + hilbertFun q (homogeneousSubmodule (Fin m) k (u - e)) := rfl
    _ = hilbertFun q (homogeneousSubmodule (Fin m) k (u - e))
        + hilbertFun (q ⊔ Ideal.span {f}) (homogeneousSubmodule (Fin m) k u) := add_comm _ _

/-! ## An arithmetic lemma -/

private theorem sum_bound_of_recursion {H H' : ℕ → ℕ} {e : ℕ} (he : 1 ≤ e)
    (hrec : ∀ u, e ≤ u → H u ≤ H (u - e) + H' u) {n C' : ℕ}
    (h' : ∀ t : ℕ, ∑ u ∈ Finset.range (t + 1), H' u ≤ C' * (t + 1) ^ n) :
    ∃ C : ℕ, ∀ t : ℕ, ∑ u ∈ Finset.range (t + 1), H u ≤ C * (t + 1) ^ (n + 1) := by
  classical
  set B : ℕ := ∑ u ∈ Finset.range e, H u with hB
  have hmono : ∀ s t : ℕ, s ≤ t →
      ∑ u ∈ Finset.range (s + 1), H u ≤ ∑ u ∈ Finset.range (t + 1), H u := by
    intro s t hst
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro u hu; simp only [Finset.mem_range] at hu ⊢; omega
    · intro u _ _; exact Nat.zero_le _
  have hrec_sum : ∀ t, e ≤ t →
      (∑ u ∈ Finset.range (t + 1), H u)
        ≤ B + (∑ u ∈ Finset.range (t - e + 1), H u)
          + ∑ u ∈ Finset.range (t + 1), H' u := by
    intro t ht
    have hsplit : ∑ u ∈ Finset.range (t + 1), H u
        = B + ∑ j ∈ Finset.range (t + 1 - e), H (e + j) := by
      have h := Finset.sum_range_add (fun u => H u) e (t + 1 - e)
      rw [show e + (t + 1 - e) = t + 1 from by omega] at h
      rw [h, hB]
    have hrec2 : ∑ j ∈ Finset.range (t + 1 - e), H (e + j)
        ≤ (∑ j ∈ Finset.range (t + 1 - e), H j)
          + ∑ j ∈ Finset.range (t + 1 - e), H' (e + j) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum (fun j hj => ?_)
      have h2 := hrec (e + j) (by omega)
      rw [show e + j - e = j from by omega] at h2
      exact h2
    have hH' : ∑ j ∈ Finset.range (t + 1 - e), H' (e + j)
        ≤ ∑ u ∈ Finset.range (t + 1), H' u := by
      have hiff : ∑ j ∈ Finset.range (t + 1 - e), H' (e + j)
          = ∑ u ∈ Finset.Ico e (t + 1), H' u := by
        rw [Finset.sum_Ico_eq_sum_range]
      rw [hiff]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro u hu; simp only [Finset.mem_Ico, Finset.mem_range] at hu ⊢; omega
      · intro u _ _; exact Nat.zero_le _
    have hSeq : ∑ j ∈ Finset.range (t + 1 - e), H j = ∑ u ∈ Finset.range (t - e + 1), H u := by
      have : t + 1 - e = t - e + 1 := by omega
      rw [this]
    rw [hsplit]
    calc B + ∑ j ∈ Finset.range (t + 1 - e), H (e + j)
        ≤ B + ((∑ j ∈ Finset.range (t + 1 - e), H j)
            + ∑ j ∈ Finset.range (t + 1 - e), H' (e + j)) := add_le_add_right hrec2 B
      _ = B + ((∑ u ∈ Finset.range (t - e + 1), H u)
            + ∑ j ∈ Finset.range (t + 1 - e), H' (e + j)) := by rw [hSeq]
      _ ≤ B + ((∑ u ∈ Finset.range (t - e + 1), H u)
            + ∑ u ∈ Finset.range (t + 1), H' u) :=
          add_le_add_right (add_le_add_right hH' _) B
      _ = B + (∑ u ∈ Finset.range (t - e + 1), H u)
            + ∑ u ∈ Finset.range (t + 1), H' u := by ring
  have key : ∀ t, ∑ u ∈ Finset.range (t + 1), H u
      ≤ B * (t + 1) + C' * ∑ v ∈ Finset.range (t + 1), (v + 1) ^ n := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      rcases lt_or_ge t e with ht | ht
      · have h1 : ∑ u ∈ Finset.range (t + 1), H u ≤ B := by
          rw [hB]
          have := hmono t (e - 1) (by omega)
          simpa [Nat.sub_add_cancel he] using this
        have h2 : B ≤ B * (t + 1) := by
          calc B = B * 1 := (mul_one B).symm
            _ ≤ B * (t + 1) := Nat.mul_le_mul_left B (by omega)
        have h3 : 0 ≤ C' * ∑ v ∈ Finset.range (t + 1), (v + 1) ^ n := Nat.zero_le _
        linarith
      · have hlt : t - e < t := by omega
        have hIH := ih (t - e) hlt
        have hs : ∑ u ∈ Finset.range (t - e + 1), H u
            ≤ B * (t - e + 1) + C' * ∑ v ∈ Finset.range (t - e + 1), (v + 1) ^ n := hIH
        have hS := hrec_sum t ht
        have h'c := h' t
        have hpoly : (∑ v ∈ Finset.range (t - e + 1), (v + 1) ^ n) + (t + 1) ^ n
            ≤ ∑ v ∈ Finset.range (t + 1), (v + 1) ^ n := by
          have hdecomp := Finset.sum_range_add (fun v => (v + 1) ^ n) (t - e + 1) e
          rw [show t - e + 1 + e = t + 1 from by omega] at hdecomp
          rw [hdecomp]
          have hmem : e - 1 ∈ Finset.range e := by simp only [Finset.mem_range]; omega
          have hterm : ((t - e + 1 + (e - 1)) + 1) ^ n
              ≤ ∑ i ∈ Finset.range e, ((t - e + 1 + i) + 1) ^ n :=
            Finset.single_le_sum (f := fun i => ((t - e + 1 + i) + 1) ^ n)
              (fun i _ => Nat.zero_le _) hmem
          have heq : (t - e + 1 + (e - 1)) + 1 = t + 1 := by omega
          rw [heq] at hterm
          linarith
        have hBt : B * (t - e + 1) + B ≤ B * (t + 1) := by
          have : B * (t - e + 1) + B = B * (t - e + 2) := by ring
          rw [this]
          exact Nat.mul_le_mul_left B (by omega)
        have hC : C' * (∑ v ∈ Finset.range (t - e + 1), (v + 1) ^ n) + C' * (t + 1) ^ n
            ≤ C' * ∑ v ∈ Finset.range (t + 1), (v + 1) ^ n := by
          rw [← Nat.mul_add]
          exact Nat.mul_le_mul_left C' hpoly
        calc ∑ u ∈ Finset.range (t + 1), H u
            ≤ B + (∑ u ∈ Finset.range (t - e + 1), H u) + ∑ u ∈ Finset.range (t + 1), H' u := hS
          _ ≤ B + (B * (t - e + 1) + C' * ∑ v ∈ Finset.range (t - e + 1), (v + 1) ^ n)
                + C' * (t + 1) ^ n := by linarith
          _ = (B * (t - e + 1) + B) + (C' * (∑ v ∈ Finset.range (t - e + 1), (v + 1) ^ n)
                + C' * (t + 1) ^ n) := by ring
          _ ≤ B * (t + 1) + C' * ∑ v ∈ Finset.range (t + 1), (v + 1) ^ n := by linarith
  refine ⟨B + C', fun t => ?_⟩
  have h1 := key t
  have h2 : ∑ v ∈ Finset.range (t + 1), (v + 1) ^ n ≤ (t + 1) * (t + 1) ^ n := by
    calc ∑ v ∈ Finset.range (t + 1), (v + 1) ^ n
        ≤ ∑ v ∈ Finset.range (t + 1), (t + 1) ^ n := by
          apply Finset.sum_le_sum
          intro v hv
          simp only [Finset.mem_range] at hv
          exact Nat.pow_le_pow_left (by omega) n
      _ = (t + 1) * (t + 1) ^ n := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hBle : B * (t + 1) ≤ B * (t + 1) ^ (n + 1) := by
    apply Nat.mul_le_mul_left
    calc (t + 1) = (t + 1) ^ 1 := (pow_one _).symm
      _ ≤ (t + 1) ^ (n + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hCle : C' * ∑ v ∈ Finset.range (t + 1), (v + 1) ^ n ≤ C' * (t + 1) ^ (n + 1) := by
    rw [show (t + 1) ^ (n + 1) = (t + 1) * (t + 1) ^ n from pow_succ' _ _]
    exact Nat.mul_le_mul_left C' h2
  calc ∑ u ∈ Finset.range (t + 1), H u
      ≤ B * (t + 1) + C' * ∑ v ∈ Finset.range (t + 1), (v + 1) ^ n := h1
    _ ≤ (B + C') * (t + 1) ^ (n + 1) := by
        rw [add_mul]
        exact add_le_add hBle hCle

/-! ## The main bound -/

private theorem hilbert_sum_upper_bound {k : Type*} [Field k] {m : ℕ}
    (q : Ideal (MvPolynomial (Fin m) k))
    (hq : ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q)
    (d : ℕ) (hd : ringKrullDim (MvPolynomial (Fin m) k ⧸ q) = (d : WithBot ℕ∞)) :
    ∃ C : ℕ, ∀ t : ℕ, (∑ u ∈ Finset.range (t + 1), Module.finrank k
        (Submodule.map (q.mkQ.restrictScalars k)
          (MvPolynomial.homogeneousSubmodule (Fin m) k u))) ≤ C * (t + 1) ^ d := by
  classical
  have key : ∀ d : ℕ, ∀ (q : Ideal (MvPolynomial (Fin m) k)),
      (∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q) →
      ringKrullDim (MvPolynomial (Fin m) k ⧸ q) ≤ (d : WithBot ℕ∞) →
      ∃ C : ℕ, ∀ t : ℕ, (∑ u ∈ Finset.range (t + 1), hilbertFun q
          (MvPolynomial.homogeneousSubmodule (Fin m) k u)) ≤ C * (t + 1) ^ d := by
    intro d
    induction d with
    | zero =>
      intro q hq hle
      haveI : IsArtinianRing k := inferInstance
      haveI : Algebra.FiniteType k (MvPolynomial (Fin m) k ⧸ q) := Algebra.FiniteType.quotient k q
      haveI hfin : Module.Finite k (MvPolynomial (Fin m) k ⧸ q) := by
        rw [Module.finite_iff_krullDimLE_zero, Ring.krullDimLE_iff]
        exact hle
      refine ⟨Module.finrank k (MvPolynomial (Fin m) k ⧸ q), fun t => ?_⟩
      have h := Commons.Algebra.MvPolynomial.sum_finrank_homogeneous_le_finrank q hq t
      simpa [hilbertFun, pow_one] using h
    | succ n ih =>
      intro q hq hle
      by_cases hcase : ringKrullDim (MvPolynomial (Fin m) k ⧸ q) ≤ ((n : ℕ) : WithBot ℕ∞)
      · obtain ⟨C, hC⟩ := ih q hq hcase
        refine ⟨C, fun t => ?_⟩
        calc (∑ u ∈ Finset.range (t + 1), hilbertFun q
                (MvPolynomial.homogeneousSubmodule (Fin m) k u))
            ≤ C * (t + 1) ^ n := hC t
          _ ≤ C * (t + 1) ^ (n + 1) :=
              Nat.mul_le_mul_left C (Nat.pow_le_pow_right (by omega) (by omega))
      · have hqne : q ≠ ⊤ := by
          intro hqt
          haveI : Subsingleton (MvPolynomial (Fin m) k ⧸ q) :=
            Ideal.Quotient.subsingleton_iff.mpr hqt
          rw [ringKrullDim_eq_bot_of_subsingleton] at hcase
          exact absurd (bot_le : (⊥ : WithBot ℕ∞) ≤ ((n : ℕ) : WithBot ℕ∞)) hcase
        have hPfin : (q.minimalPrimes : Set (Ideal (MvPolynomial (Fin m) k))).Finite :=
          Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin m) k) q
        set P : Finset (Ideal (MvPolynomial (Fin m) k)) := hPfin.toFinset with hPdef
        have hPmem : ∀ p, p ∈ P ↔ p ∈ q.minimalPrimes := by
          intro p; rw [hPdef]; exact Set.Finite.mem_toFinset hPfin
        obtain ⟨e, f, hfhom, hfI, hfnot⟩ := homogeneous_prime_avoidance
          (MvPolynomial.idealOfVars (Fin m) k)
          (fun x hx j => idealOfVars_homogeneousComponent_mem hx j) P
          (fun p hp => ((hPmem p).mp hp).1.1)
          (fun p hp x hx j => minimalPrimes_homogeneousComponent_mem hq ((hPmem p).mp hp) x hx j)
          (fun p hp => by
            intro hle'
            have h0 := ringKrullDim_le_zero_of_minimalPrimes_idealOfVars_le hq ((hPmem p).mp hp) hle'
            exact hcase (le_trans h0 (show ((0:ℕ) : WithBot ℕ∞) ≤ ((n : ℕ) : WithBot ℕ∞) from by
              exact_mod_cast Nat.zero_le n)))
        have he1 : 1 ≤ e := by
          rw [Nat.one_le_iff_ne_zero]
          intro he0
          have hcoeff : f.coeff 0 = 0 := (mem_idealOfVars_iff_coeff_zero_hub f).mp hfI
          have h1 : MvPolynomial.homogeneousComponent 0 f = f :=
            MvPolynomial.homogeneousComponent_of_mem
              ((MvPolynomial.mem_homogeneousSubmodule 0 f).mpr (he0 ▸ hfhom))
          rw [MvPolynomial.homogeneousComponent_zero, hcoeff, MvPolynomial.C_0] at h1
          obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes hqne
          exact (hfnot p ((hPmem p).mpr hp)) (h1 ▸ p.zero_mem)
        have hq' : ∀ x ∈ q ⊔ Ideal.span {f}, ∀ j,
            MvPolynomial.homogeneousComponent j x ∈ q ⊔ Ideal.span {f} := by
          intro x hx j
          have hq_hom : Ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin m) k) q := by
            rw [Ideal.IsHomogeneous.iff_eq]
            refine le_antisymm (Ideal.toIdeal_homogeneousCore_le _ q) ?_
            intro y hy
            rw [← MvPolynomial.sum_homogeneousComponent y]
            refine Ideal.sum_mem _ fun j _ => ?_
            exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem
              ⟨j, MvPolynomial.homogeneousComponent_mem j y⟩ (hq y hy j)
          have hhom : Ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin m) k)
              (q ⊔ Ideal.span {f}) := hq_hom.sup (homogeneous_span_singleton hfhom)
          exact (MvPolynomial.mem_iff_homogeneousComponent_mem hhom x).mp hx j
        have hdrop : ringKrullDim (MvPolynomial (Fin m) k ⧸ (q ⊔ Ideal.span {f}))
            ≤ ((n : ℕ) : WithBot ℕ∞) := by
          exact ringKrullDim_quotient_sup_span_le q f
            (fun p hp => hfnot p ((hPmem p).mpr hp)) hle
        obtain ⟨C', hC'⟩ := ih (q ⊔ Ideal.span {f}) hq' hdrop
        have hrec : ∀ u, e ≤ u → hilbertFun q (MvPolynomial.homogeneousSubmodule (Fin m) k u)
            ≤ hilbertFun q (MvPolynomial.homogeneousSubmodule (Fin m) k (u - e))
              + hilbertFun (q ⊔ Ideal.span {f}) (MvPolynomial.homogeneousSubmodule (Fin m) k u) :=
          fun u hu => hilbertFun_recursion q hq hfhom u hu
        exact sum_bound_of_recursion he1 hrec hC'
  have := key d q hq (le_of_eq hd)
  simpa [hilbertFun] using this

end Commons.RingTheory.Ideal.Hilbert
end


-- ==== from Submission.Commons.Algebra.MvPolynomial.exists_pow_idealOfVars_le_of_homogeneousComponent_mem ====
section

/-!
# `idealOfVars ^ N ≤ I` for a graded finite-codimensional ideal

Let `R = MvPolynomial σ ℂ` with `σ` finite, and let `I ⊆ R` be an ideal that is closed under
taking homogeneous components (i.e. `I` is a *homogeneous* / graded ideal for the total-degree
grading).  If the quotient `R ⧸ I` is finite dimensional over `ℂ`, then `I` contains a power
of the irrelevant ideal `idealOfVars = ⟨X i⟩`.

The proof is the standard graded argument.  Write `A = R ⧸ I` and let
`S j = map (mkQ I) (homogeneousSubmodule σ ℂ j) ⊆ A` be the image of the degree-`j` part.
Because `I` is homogeneous, the map
`(j : Fin M) → S j → A`, `x ↦ ∑ j, x j`
is injective (degree reasons), so `∑_{j < M} finrank S j ≤ finrank A` for every `M`.  A sum of
natural numbers with all partial sums bounded by the fixed integer `finrank A` has only finitely
many nonzero terms, whence `S j = ⊥` for `j ≥ N`.  Thus every homogeneous polynomial of degree
`≥ N` lies in `I`; in particular the degree-`N` monomials do, and since these generate
`idealOfVars ^ N` we get `idealOfVars ^ N ≤ I`.
-/

namespace Commons.Algebra.MvPolynomial

open _root_.MvPolynomial

set_option linter.style.haveILetI false

/-- If all partial sums `∑_{j < M} c j` are bounded by `d`, then only finitely many `c j` are
nonzero. -/
private lemma exists_forall_eq_zero_of_sum_range_le {c : ℕ → ℕ} {d : ℕ}
    (h : ∀ M, ∑ j ∈ Finset.range M, c j ≤ d) : ∃ N, ∀ j ≥ N, c j = 0 := by
  by_contra hcon
  push_neg at hcon
  -- `hcon : ∀ N, ∃ j, N ≤ j ∧ c j ≠ 0`, so `{j | c j ≠ 0}` is infinite.
  have hinf : (Set.Infinite {j : ℕ | c j ≠ 0}) := by
    rw [Set.infinite_iff_exists_gt]
    intro N
    obtain ⟨j, hj, hjc⟩ := hcon (N + 1)
    exact ⟨j, hjc, hj⟩
  obtain ⟨t, ht_sub, ht_card⟩ := hinf.exists_subset_card_eq (d + 1)
  have ht_ne : ∀ j ∈ t, c j ≠ 0 := fun j hj => ht_sub hj
  have h1 : d + 1 ≤ ∑ j ∈ t, c j := by
    calc d + 1 = t.card := ht_card.symm
      _ = ∑ _j ∈ t, 1 := by simp
      _ ≤ ∑ j ∈ t, c j :=
          Finset.sum_le_sum (fun j hj => Nat.one_le_iff_ne_zero.mpr (ht_ne j hj))
  have h2 : ∑ j ∈ t, c j ≤ d := by
    have hsub : t ⊆ Finset.range (t.sup id + 1) := by
      intro j hj
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hj)
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_) (h _)
    intro j _ _
    exact Nat.zero_le _
  omega

/-- The images of the homogeneous pieces of `R` in `A = R ⧸ I` are linearly `ℂ`-independent in
the strong sense that the summation map out of a finite product is injective. -/
private lemma finrank_sum_map_le {σ K : Type*} [Field K] [Fintype σ] [DecidableEq σ]
    (I : Ideal (MvPolynomial σ K))
    (hI : ∀ (j : ℕ) (p : MvPolynomial σ K),
      p ∈ I → MvPolynomial.homogeneousComponent j p ∈ I)
    (hfin : Module.Finite K (MvPolynomial σ K ⧸ I)) (M : ℕ) :
    ∑ j : Fin M, Module.finrank K ↥(Submodule.map ((I.mkQ).restrictScalars K)
        (MvPolynomial.homogeneousSubmodule σ K j.val)) ≤
      Module.finrank K (MvPolynomial σ K ⧸ I) := by
  classical
  let S : ℕ → Submodule K (MvPolynomial σ K ⧸ I) := fun j =>
    Submodule.map ((I.mkQ).restrictScalars K) (MvPolynomial.homogeneousSubmodule σ K j)
  have hker : ∀ p : MvPolynomial σ K, (I.mkQ.restrictScalars K) p = 0 ↔ p ∈ I := by
    intro p
    rw [LinearMap.restrictScalars_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  let F : ((j : Fin M) → ↥(S j.val)) →ₗ[K] (MvPolynomial σ K ⧸ I) :=
    { toFun := fun x => ∑ j : Fin M, ((x j : ↥(S j.val)) : MvPolynomial σ K ⧸ I)
      map_add' := fun x y => by
        simp only [Pi.add_apply, Submodule.coe_add, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        simp only [Pi.smul_apply, Submodule.coe_smul, Finset.smul_sum, RingHom.id_apply] }
  have hF_apply : ∀ x, F x = ∑ j : Fin M, ((x j : ↥(S j.val)) : MvPolynomial σ K ⧸ I) :=
    fun x => rfl
  have hzero : ∀ z : (j : Fin M) → ↥(S j.val), F z = 0 → z = 0 := by
    intro z hz0
    choose t ht_mem ht_eq using fun j : Fin M => Submodule.mem_map.mp (z j).property
    have hqP : (I.mkQ.restrictScalars K) (∑ j : Fin M, t j) = 0 := by
      rw [map_sum]
      have hsum : (∑ j : Fin M, (I.mkQ.restrictScalars K) (t j))
          = ∑ j : Fin M, ((z j : ↥(S j.val)) : MvPolynomial σ K ⧸ I) :=
        Finset.sum_congr rfl (fun j _ => ht_eq j)
      rw [hsum, ← hF_apply z]; exact hz0
    have hP : (∑ j : Fin M, t j) ∈ I := (hker _).mp hqP
    funext i
    apply Subtype.ext
    show ((z i : ↥(S i.val)) : MvPolynomial σ K ⧸ I) = 0
    rw [← ht_eq i]
    apply (hker (t i)).mpr
    have h1 : (∑ j : Fin M, MvPolynomial.homogeneousComponent i.val (t j)) ∈ I := by
      have hh := hI i.val (∑ j : Fin M, t j) hP
      rwa [map_sum] at hh
    have heq : (∑ j : Fin M, MvPolynomial.homogeneousComponent i.val (t j))
        = ∑ j : Fin M, (if i.val = j.val then t j else 0) :=
      Finset.sum_congr rfl (fun j _ =>
        MvPolynomial.homogeneousComponent_of_mem (ht_mem j))
    have hsum2 : (∑ j : Fin M, (if i.val = j.val then t j else 0)) = t i := by
      rw [Fintype.sum_eq_single i]
      · simp
      · intro j hj
        rw [if_neg (fun h => hj (Fin.ext h).symm)]
    rw [heq, hsum2] at h1
    exact h1
  have hinj : Function.Injective F := by
    intro x y hxy
    have h0 : F (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hres := hzero (x - y) h0
    exact sub_eq_zero.mp hres
  haveI : ∀ j : Fin M, Module.Finite K ↥(S j.val) := fun j =>
    Module.Finite.of_fg (Submodule.FG.map ((I.mkQ).restrictScalars K)
      (MvPolynomial.homogeneousSubmodule_fg σ K j.val))
  have hle := LinearMap.finrank_le_finrank_of_injective (f := F) hinj
  rwa [Module.finrank_pi_fintype] at hle

private theorem exists_pow_idealOfVars_le_of_homogeneousComponent_mem {σ : Type*} [Fintype σ] [DecidableEq σ]
    (I : Ideal (MvPolynomial σ ℂ))
    (hI : ∀ (j : ℕ) (p : MvPolynomial σ ℂ), p ∈ I → MvPolynomial.homogeneousComponent j p ∈ I)
    (hfin : Module.Finite ℂ (MvPolynomial σ ℂ ⧸ I)) :
    ∃ N : ℕ, MvPolynomial.idealOfVars σ ℂ ^ N ≤ I := by
  classical
  let A := MvPolynomial σ ℂ ⧸ I
  let q : MvPolynomial σ ℂ →ₗ[ℂ] A := (I.mkQ).restrictScalars ℂ
  let S : ℕ → Submodule ℂ A := fun j => Submodule.map q (MvPolynomial.homogeneousSubmodule σ ℂ j)
  have hker : ∀ p : MvPolynomial σ ℂ, q p = 0 ↔ p ∈ I := by
    intro p
    change (I.mkQ.restrictScalars ℂ) p = 0 ↔ p ∈ I
    rw [LinearMap.restrictScalars_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  -- Partial sums of `finrank ℂ (S j)` are bounded by `finrank ℂ A`.
  have hbound : ∀ M, ∑ j ∈ Finset.range M, Module.finrank ℂ (S j) ≤ Module.finrank ℂ A := by
    intro M
    rw [← Fin.sum_univ_eq_sum_range (fun j => Module.finrank ℂ (S j)) M]
    have h := finrank_sum_map_le (K := ℂ) I hI hfin M
    simpa only [S, A, q] using h
  obtain ⟨N, hN⟩ :=
    exists_forall_eq_zero_of_sum_range_le (c := fun j => Module.finrank ℂ (S j)) hbound
  refine ⟨N, ?_⟩
  -- Every homogeneous polynomial of degree `≥ N` lies in `I`.
  have hmem : ∀ j ≥ N, ∀ p ∈ MvPolynomial.homogeneousSubmodule σ ℂ j, p ∈ I := by
    intro j hj p hp
    haveI : Module.Finite ℂ ↥(S j) :=
      Module.Finite.of_fg (Submodule.FG.map q (MvPolynomial.homogeneousSubmodule_fg σ ℂ j))
    have hbot : S j = ⊥ := (Submodule.finrank_eq_zero).mp (hN j hj)
    have hmemS : q p ∈ S j := Submodule.mem_map.mpr ⟨p, hp, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmemS
    exact (hker p).mp hmemS
  rw [MvPolynomial.pow_idealOfVars_eq_span]
  rw [Ideal.span_le]
  rintro y ⟨d, hd, rfl⟩
  exact hmem N le_rfl (MvPolynomial.monomial d 1) (by
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact MvPolynomial.isHomogeneous_monomial 1 hd)

end Commons.Algebra.MvPolynomial
end


-- ==== from Submission.Commons.Algebra.MvPolynomial.homogeneous_isHomogeneous_mem_of_finite_quotient ====
section

namespace Commons.Algebra.MvPolynomial

private theorem homogeneous_isHomogeneous_mem_of_finite_quotient {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℂ))
    (hI : ∀ (j : ℕ) (p : MvPolynomial (Fin n) ℂ), p ∈ I → MvPolynomial.homogeneousComponent j p ∈ I)
    (hfin : Module.Finite ℂ (MvPolynomial (Fin n) ℂ ⧸ I)) :
    ∃ N : ℕ, ∀ j, N ≤ j → ∀ p : MvPolynomial (Fin n) ℂ, p.IsHomogeneous j → p ∈ I := by
  obtain ⟨N, hN⟩ :=
    exists_pow_idealOfVars_le_of_homogeneousComponent_mem I hI hfin
  refine ⟨N, fun j hj p hp => ?_⟩
  apply hN
  rw [MvPolynomial.mem_pow_idealOfVars_iff']
  intro d hd
  exact hp.coeff_eq_zero (by omega)

end Commons.Algebra.MvPolynomial

end


-- ==== from Submission.Commons.Algebra.MvPolynomial.finite_adjoin_range_of_finite_quotient ====
section

namespace Commons.Algebra.MvPolynomial

-- `MvPolynomial` carries a total-degree graded-algebra structure that Mathlib deliberately
-- does not register globally; we need it to speak about homogeneous ideals.
attribute [local instance] MvPolynomial.gradedAlgebra

set_option linter.style.haveILetI false

/-- **Finiteness of the polynomial ring over the subalgebra generated by a homogeneous system
of parameters.**

Let `g₁, …, gₙ ∈ ℂ[x₁,…,xₙ]` be homogeneous of a common positive degree `e`.  If the quotient
`ℂ[x₁,…,xₙ]/(g₁,…,gₙ)` is finite dimensional over `ℂ`, then `ℂ[x₁,…,xₙ]` is a finite module
over the subalgebra `ℂ[g₁,…,gₙ]`.

The proof is the standard graded argument.  Since the (homogeneous) ideal `(g₁,…,gₙ)` contains
all homogeneous pieces above some degree `D`, every polynomial of degree `> D` lies in the
ideal; writing a homogeneous `p` of degree `j > D` as `∑ cᵢ gᵢ` and taking its degree-`j`
component reduces it to a `ℂ[g₁,…,gₙ]`-combination of polynomials of degree `j - e < j`.  So
strong induction on the degree shows that the monomials of degree `≤ D` generate
`ℂ[x₁,…,xₙ]` over `ℂ[g₁,…,gₙ]`. -/
private theorem finite_adjoin_range_of_finite_quotient {n e : ℕ} (g : Fin n → MvPolynomial (Fin n) ℂ)
    (hg : ∀ i, (g i).IsHomogeneous e) (he : 1 ≤ e)
    (hfin : Module.rank ℂ (MvPolynomial (Fin n) ℂ ⧸ Ideal.span (Set.range g)) < Cardinal.aleph0) :
    Module.Finite ↥(Algebra.adjoin ℂ (Set.range g)) (MvPolynomial (Fin n) ℂ) := by
  classical
  set A : Subalgebra ℂ (MvPolynomial (Fin n) ℂ) := Algebra.adjoin ℂ (Set.range g) with hA
  set I : Ideal (MvPolynomial (Fin n) ℂ) := Ideal.span (Set.range g) with hIdef
  -- `I` is homogeneous because it is spanned by homogeneous elements.
  have hIhom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) ℂ) := by
    rw [hIdef]
    refine Ideal.homogeneous_span (MvPolynomial.homogeneousSubmodule (Fin n) ℂ) (Set.range g) ?_
    rintro x ⟨i, rfl⟩
    exact ⟨e, hg i⟩
  have hIcomp : ∀ (j : ℕ) (p : MvPolynomial (Fin n) ℂ),
      p ∈ I → MvPolynomial.homogeneousComponent j p ∈ I :=
    fun j p hp => MvPolynomial.homogeneousComponent_mem_of_mem hIhom hp j
  -- Finiteness of the quotient.
  have hfin' : Module.rank ℂ (MvPolynomial (Fin n) ℂ ⧸ I) < Cardinal.aleph0 := by
    rw [hIdef]; exact hfin
  haveI hIfin : Module.Finite ℂ (MvPolynomial (Fin n) ℂ ⧸ I) :=
    Module.rank_lt_aleph0_iff.mp hfin'
  -- All homogeneous pieces of degree `≥ N` lie in `I`.
  obtain ⟨N, hN⟩ := homogeneous_isHomogeneous_mem_of_finite_quotient I hIcomp hIfin
  set D : ℕ := max N e with hD
  have hDgeN : N ≤ D := by rw [hD]; exact le_max_left _ _
  have hDgee : e ≤ D := by rw [hD]; exact le_max_right _ _
  -- The generating set: monomials of degree `≤ D`.
  haveI : Finite {d : Fin n →₀ ℕ // d.degree ≤ D} := Finsupp.finite_of_degree_le (σ := Fin n) D
  let T : Set (MvPolynomial (Fin n) ℂ) :=
    Set.range (fun d : {d : Fin n →₀ ℕ // d.degree ≤ D} => MvPolynomial.monomial d.1 (1 : ℂ))
  have hTfin : T.Finite := Set.finite_range _
  let M : Submodule A (MvPolynomial (Fin n) ℂ) := Submodule.span A T
  have hMfg : M.FG := Submodule.fg_span hTfin
  have hmon : ∀ (d : Fin n →₀ ℕ), d.degree ≤ D → MvPolynomial.monomial d (1 : ℂ) ∈ M := by
    intro d hd
    exact Submodule.subset_span ⟨⟨d, hd⟩, rfl⟩
  -- Strong induction on the degree: every homogeneous polynomial lies in `M`.
  have hind : ∀ j : ℕ, ∀ p : MvPolynomial (Fin n) ℂ, p.IsHomogeneous j → p ∈ M := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro p hp
      by_cases hj : j ≤ D
      · -- small degree: expand into monomials of degree `j ≤ D`
        rw [MvPolynomial.as_sum p]
        refine Submodule.sum_mem M (fun d hd => ?_)
        have hdne : MvPolynomial.coeff d p ≠ 0 := MvPolynomial.mem_support_iff.mp hd
        have hdeg : d.degree = j := by
          by_contra hne
          exact hdne (hp.coeff_eq_zero hne)
        have hlt : d.degree ≤ D := by omega
        have h1 : MvPolynomial.monomial d (1 : ℂ) ∈ M := hmon d hlt
        have hCA : (MvPolynomial.C (MvPolynomial.coeff d p) : MvPolynomial (Fin n) ℂ) ∈ A := by
          rw [← MvPolynomial.algebraMap_eq]
          exact A.algebraMap_mem _
        have hsm : (⟨MvPolynomial.C (MvPolynomial.coeff d p), hCA⟩ : A) •
            (MvPolynomial.monomial d (1 : ℂ)) ∈ M :=
          Submodule.smul_mem M _ h1
        have heq : (⟨MvPolynomial.C (MvPolynomial.coeff d p), hCA⟩ : A) •
            (MvPolynomial.monomial d (1 : ℂ)) = MvPolynomial.monomial d (MvPolynomial.coeff d p) := by
          rw [Subalgebra.smul_def, smul_eq_mul, MvPolynomial.C_mul_monomial, mul_one]
        rwa [heq] at hsm
      · -- large degree: `p ∈ I`, reduce to degree `j - e`
        push Not at hj
        have hjN : N ≤ j := le_trans hDgeN (le_of_lt hj)
        have hpe : e ≤ j := le_trans hDgee (le_of_lt hj)
        have hpI : p ∈ I := hN j hjN p hp
        have hpI' : p ∈ Ideal.span (Set.range g) := by rw [← hIdef]; exact hpI
        obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).mp hpI'
        have hqmem : ∀ i, MvPolynomial.homogeneousComponent (j - e) (c i) ∈ M := fun i =>
          ih (j - e) (by omega) (MvPolynomial.homogeneousComponent (j - e) (c i))
            (MvPolynomial.homogeneousComponent_isHomogeneous (j - e) (c i))
        have hterm : ∀ i, MvPolynomial.homogeneousComponent (j - e) (c i) * g i ∈ M := by
          intro i
          have hgi : g i ∈ A := Algebra.subset_adjoin (Set.mem_range_self i)
          have hsm : (⟨g i, hgi⟩ : A) • (MvPolynomial.homogeneousComponent (j - e) (c i)) ∈ M :=
            Submodule.smul_mem M _ (hqmem i)
          have heq : MvPolynomial.homogeneousComponent (j - e) (c i) * g i
              = (⟨g i, hgi⟩ : A) • (MvPolynomial.homogeneousComponent (j - e) (c i)) := by
            rw [Subalgebra.smul_def, smul_eq_mul, mul_comm]
          rwa [heq]
        have hp_eq : p = ∑ i, MvPolynomial.homogeneousComponent (j - e) (c i) * g i := by
          have h1 : p = MvPolynomial.homogeneousComponent j (∑ i, c i * g i) := by
            rw [hc, MvPolynomial.homogeneousComponent_eq_self hp]
          rw [h1, map_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          have key := homogeneousComponent_mul_of_isHomogeneous_right (hg i) (c i) (j - e)
          rw [Nat.sub_add_cancel hpe] at key
          exact key
        rw [hp_eq]
        exact Submodule.sum_mem M (fun i _ => hterm i)
  -- Hence `M = ⊤` and `M` is finitely generated, so `ℂ[x₁,…,xₙ]` is a finite `A`-module.
  have htop : (⊤ : Submodule A (MvPolynomial (Fin n) ℂ)) ≤ M := by
    intro p _
    rw [← MvPolynomial.sum_homogeneousComponent p]
    exact Submodule.sum_mem M (fun i _ => hind i _ (MvPolynomial.homogeneousComponent_isHomogeneous i p))
  have hMtop : M = ⊤ := eq_top_iff.mpr htop
  have hfg : (⊤ : Submodule A (MvPolynomial (Fin n) ℂ)).FG := hMtop ▸ hMfg
  exact Module.Finite.of_fg_top hfg

end Commons.Algebra.MvPolynomial

end


-- ==== from Submission.Commons.Algebra.MvPolynomial.quotient_span_range_X_castLE_algEquiv ====
section

/-!
# Quotient of a polynomial ring by a set of variables
-/

namespace Commons.Algebra.MvPolynomial

open _root_.MvPolynomial

/-- Quotienting `R[X_i : i ∈ σ]` by the ideal generated by the variables indexed by a decidable
predicate `p` yields the polynomial ring in the remaining variables. -/
private theorem quotient_span_X_image_algEquiv {R : Type*} [CommRing R] {σ : Type*}
    (p : σ → Prop) [DecidablePred p] :
    Nonempty ((MvPolynomial σ R ⧸ Ideal.span
        ((fun i : σ => (MvPolynomial.X i : MvPolynomial σ R)) '' {i : σ | p i})) ≃ₐ[R]
      MvPolynomial {i : σ // ¬ p i} R) := by
  classical
  set I : Ideal (MvPolynomial σ R) :=
    Ideal.span ((fun i : σ => (MvPolynomial.X i : MvPolynomial σ R)) '' {i : σ | p i})
  set φ : σ → MvPolynomial {i : σ // ¬ p i} R :=
    (fun i => if h : p i then 0 else MvPolynomial.X ⟨i, h⟩) with hφ
  set ψ : {i : σ // ¬ p i} → MvPolynomial σ R ⧸ I :=
    (fun j => Ideal.Quotient.mk I (MvPolynomial.X (j : σ))) with hψ
  set f : MvPolynomial σ R →ₐ[R] MvPolynomial {i : σ // ¬ p i} R := MvPolynomial.aeval φ with hf
  set g : MvPolynomial {i : σ // ¬ p i} R →ₐ[R] MvPolynomial σ R ⧸ I := MvPolynomial.aeval ψ with hg
  have hker : I ≤ RingHom.ker (f : MvPolynomial σ R →+* MvPolynomial {i : σ // ¬ p i} R) := by
    refine Ideal.span_le.mpr ?_
    rintro a ⟨i, hi, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    change f (MvPolynomial.X i) = 0
    rw [show f (MvPolynomial.X i) = φ i from MvPolynomial.aeval_X φ i]
    simp only [hφ, dif_pos (show p i from hi)]
  have hfI : ∀ a ∈ I, f a = 0 := fun a ha => RingHom.mem_ker.mp (hker ha)
  set fbar : (MvPolynomial σ R ⧸ I) →ₐ[R] MvPolynomial {i : σ // ¬ p i} R :=
    Ideal.Quotient.liftₐ I f hfI with hfbar
  have h_lift : ∀ x : MvPolynomial σ R, fbar (Ideal.Quotient.mk I x) = f x := by
    intro x
    rw [hfbar, Ideal.Quotient.liftₐ_apply]
    exact Ideal.Quotient.lift_mk I (f : MvPolynomial σ R →+* MvPolynomial {i : σ // ¬ p i} R) hfI
  have h1 : fbar.comp g = AlgHom.id R (MvPolynomial {i : σ // ¬ p i} R) := by
    apply MvPolynomial.algHom_ext
    intro j
    rw [AlgHom.comp_apply, AlgHom.id_apply]
    change fbar (g (MvPolynomial.X j)) = MvPolynomial.X j
    rw [show g (MvPolynomial.X j) = ψ j from MvPolynomial.aeval_X ψ j]
    rw [hψ, h_lift]
    rw [show f (MvPolynomial.X (j : σ)) = φ (j : σ) from MvPolynomial.aeval_X φ (j : σ)]
    simp only [hφ]
    rw [dif_neg j.prop]
  have hcomp : g.comp f = Ideal.Quotient.mkₐ R I := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    change g (f (MvPolynomial.X i)) = Ideal.Quotient.mk I (MvPolynomial.X i)
    rw [show f (MvPolynomial.X i) = φ i from MvPolynomial.aeval_X φ i]
    simp only [hφ]
    split_ifs with hi
    · rw [map_zero]
      have hmem : (MvPolynomial.X i : MvPolynomial σ R) ∈ I :=
        Ideal.subset_span (s := ((fun i : σ => (MvPolynomial.X i : MvPolynomial σ R))
          '' {i : σ | p i})) ⟨i, hi, rfl⟩
      exact (Ideal.Quotient.eq_zero_iff_mem.mpr hmem).symm
    · rw [show g (MvPolynomial.X ⟨i, hi⟩) = ψ ⟨i, hi⟩ from MvPolynomial.aeval_X ψ ⟨i, hi⟩]
  have key : ∀ x : MvPolynomial σ R, g (f x) = Ideal.Quotient.mk I x := fun x => by
    have h := DFunLike.congr_fun hcomp x
    rw [Ideal.Quotient.mkₐ_eq_mk] at h
    simpa [AlgHom.comp_apply] using h
  have h2 : g.comp fbar = AlgHom.id R (MvPolynomial σ R ⧸ I) := by
    apply AlgHom.ext
    intro q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    show g (fbar (Ideal.Quotient.mk I x)) = Ideal.Quotient.mk I x
    rw [h_lift]
    exact key x
  exact ⟨AlgEquiv.ofAlgHom fbar g h1 h2⟩

/-- The quotient of `ℂ[X_0, …, X_{n-1}]` by the ideal generated by `X_0, …, X_{k-1}` is the
polynomial ring in the remaining `n - k` variables. -/
private theorem quotient_span_range_X_castLE_algEquiv {n k : ℕ} (hk : k ≤ n) :
    Nonempty ((MvPolynomial (Fin n) ℂ ⧸ Ideal.span (Set.range (fun i : Fin k =>
        (MvPolynomial.X (Fin.castLE hk i) : MvPolynomial (Fin n) ℂ)))) ≃ₐ[ℂ]
      MvPolynomial (Fin (n - k)) ℂ) := by
  classical
  have hrange : Set.range (Fin.castLE hk) = {i : Fin n | (i : ℕ) < k} := by
    ext i
    constructor
    · rintro ⟨j, rfl⟩
      simp [Fin.val_castLE]
    · intro hi
      exact ⟨⟨(i : ℕ), hi⟩, Fin.ext (by simp)⟩
  have hset : ((fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℂ)) ''
      {i : Fin n | (i : ℕ) < k})
      = Set.range (fun i : Fin k =>
          (MvPolynomial.X (Fin.castLE hk i) : MvPolynomial (Fin n) ℂ)) := by
    rw [← hrange, ← Set.range_comp]
    rfl
  obtain ⟨e⟩ := quotient_span_X_image_algEquiv (R := ℂ) (σ := Fin n)
    (fun i : Fin n => (i : ℕ) < k)
  let e_sub : {i : Fin n // ¬ ((i : ℕ) < k)} ≃ Fin (n - k) :=
    { toFun := fun i => ⟨(i : ℕ) - k, by
        have h1 : (i : ℕ) < n := i.1.isLt
        have h2 : k ≤ (i : ℕ) := Nat.le_of_not_lt i.2
        omega⟩
      invFun := fun j => ⟨⟨k + (j : ℕ), by
          have h1 : (j : ℕ) < n - k := j.isLt
          omega⟩, by
        rw [Fin.val_mk, not_lt]
        exact Nat.le_add_right k (j : ℕ)⟩
      left_inv := by
        intro i
        apply Subtype.ext
        apply Fin.ext
        dsimp only
        have h2 : k ≤ (i : ℕ) := Nat.le_of_not_lt i.2
        omega
      right_inv := by
        intro j
        apply Fin.ext
        dsimp only
        omega }
  exact ⟨(Ideal.quotientEquivAlgOfEq ℂ (congrArg Ideal.span hset.symm)).trans
    (e.trans (MvPolynomial.renameEquiv ℂ e_sub))⟩

end Commons.Algebra.MvPolynomial
end


-- ==== from Submission.Commons.Algebra.MvPolynomial.isPrime_span_range_X_castLE ====
section

namespace Commons.Algebra.MvPolynomial

open _root_.MvPolynomial

private theorem isPrime_span_range_X_castLE {n k : ℕ} (hk : k ≤ n) :
    (Ideal.span (Set.range (fun i : Fin k =>
      (MvPolynomial.X (Fin.castLE hk i) : MvPolynomial (Fin n) ℂ)))).IsPrime := by
  classical
  set I : Ideal (MvPolynomial (Fin n) ℂ) :=
    Ideal.span (Set.range (fun i : Fin k =>
      (MvPolynomial.X (Fin.castLE hk i) : MvPolynomial (Fin n) ℂ))) with hI
  let φ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
    MvPolynomial.aeval (fun i : Fin n =>
      if (i : ℕ) < k then 0 else (MvPolynomial.X i : MvPolynomial (Fin n) ℂ))
  have hφX : ∀ i : Fin n, φ (MvPolynomial.X i)
      = if (i : ℕ) < k then 0 else (MvPolynomial.X i : MvPolynomial (Fin n) ℂ) := by
    intro i
    show MvPolynomial.aeval (fun j : Fin n =>
      if (j : ℕ) < k then 0 else (MvPolynomial.X j : MvPolynomial (Fin n) ℂ))
      (MvPolynomial.X i) = _
    rw [MvPolynomial.aeval_X]
  have hI_le : I ≤ RingHom.ker φ := by
    rw [hI, Ideal.span_le]
    rintro x ⟨i, rfl⟩
    apply RingHom.mem_ker.mpr
    change φ (MvPolynomial.X (Fin.castLE hk i)) = 0
    rw [hφX, Fin.val_castLE, if_pos i.isLt]
  have hM : ∀ p : MvPolynomial (Fin n) ℂ, p - φ p ∈ I := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      have hca : φ (MvPolynomial.C a) = MvPolynomial.C a := by
        rw [MvPolynomial.C_eq_algebraMap]
        exact AlgHom.commutes φ a
      rw [hca, sub_self]
      exact Submodule.zero_mem I
    | add p q hp hq =>
      rw [map_add]
      have hd : p + q - (φ p + φ q) = (p - φ p) + (q - φ q) := by abel
      rw [hd]
      exact I.add_mem hp hq
    | mul_X p m hp =>
      rw [map_mul, hφX]
      have hd : p * MvPolynomial.X m
          - φ p * (if (m : ℕ) < k then 0 else (MvPolynomial.X m : MvPolynomial (Fin n) ℂ))
          = (p - φ p) * MvPolynomial.X m
            + φ p * (MvPolynomial.X m -
                (if (m : ℕ) < k then 0 else (MvPolynomial.X m : MvPolynomial (Fin n) ℂ))) := by
        ring
      rw [hd]
      apply I.add_mem
      · exact I.mul_mem_right _ hp
      · apply I.mul_mem_left
        by_cases hmk : (m : ℕ) < k
        · rw [if_pos hmk, sub_zero]
          apply Ideal.subset_span
          refine ⟨⟨m, hmk⟩, ?_⟩
          change MvPolynomial.X (Fin.castLE hk ⟨m, hmk⟩) = MvPolynomial.X m
          rw [show Fin.castLE hk ⟨m, hmk⟩ = m from Fin.ext (by simp)]
        · rw [if_neg hmk, sub_self]
          exact Submodule.zero_mem I
  have hker_le : RingHom.ker φ ≤ I := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have h := hM x
    rwa [hx, sub_zero] at h
  have hIeq : I = RingHom.ker φ := le_antisymm hI_le hker_le
  rw [hIeq]
  exact RingHom.ker_isPrime φ

end Commons.Algebra.MvPolynomial
end


-- ==== from Submission.Commons.Algebra.MvPolynomial.exists_isHomogeneous_one_notMem_minimalPrimes ====
section

set_option linter.style.haveILetI false

open MvPolynomial

namespace Commons.Algebra.MvPolynomial

/-! # A homogeneous linear form avoiding all minimal primes of small height -/

/-- The `ℂ`-algebra endomorphism of `ℂ[X_1,…,X_n]` that kills the first `k` variables and
fixes the remaining ones. -/
private noncomputable def varProj (n k : ℕ) :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  MvPolynomial.aeval fun i : Fin n => if (i : ℕ) < k then 0 else MvPolynomial.X i

private lemma varProj_zero (n : ℕ) : varProj n 0 = AlgHom.id ℂ (MvPolynomial (Fin n) ℂ) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [varProj]

private lemma varProj_self (n : ℕ) :
    varProj n n = MvPolynomial.aeval (0 : Fin n → MvPolynomial (Fin n) ℂ) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [varProj]

private lemma varProj_succ_comp (n k : ℕ) :
    (varProj n (k+1)).comp (varProj n k) = varProj n (k+1) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply]
  have hXk : varProj n k (X i) = (if (i:ℕ) < k then 0 else MvPolynomial.X i) := by simp [varProj]
  have hXk1 : varProj n (k+1) (X i) = (if (i:ℕ) < k+1 then 0 else MvPolynomial.X i) := by simp [varProj]
  rw [hXk, hXk1]
  by_cases h : (i:ℕ) < k
  · rw [if_pos h, map_zero, if_pos (by omega)]
  · rw [if_neg h, hXk1]

private lemma ker_varProj_le_succ (n k : ℕ) :
    RingHom.ker (varProj n k) ≤ RingHom.ker (varProj n (k+1)) := by
  intro p hp
  simp only [RingHom.mem_ker] at hp ⊢
  rw [← varProj_succ_comp n k]
  simp only [AlgHom.comp_apply, hp, map_zero]

private lemma ker_varProj_lt_succ {n k : ℕ} (hk : k < n) :
    RingHom.ker (varProj n k) < RingHom.ker (varProj n (k+1)) := by
  refine lt_of_le_of_ne (ker_varProj_le_succ n k) (fun heq => ?_)
  have hmem : (MvPolynomial.X ⟨k, hk⟩ : MvPolynomial (Fin n) ℂ) ∈
      RingHom.ker (varProj n (k+1)) := by
    simp only [RingHom.mem_ker, varProj, MvPolynomial.aeval_X]
    simp
  have hnotmem : (MvPolynomial.X ⟨k, hk⟩ : MvPolynomial (Fin n) ℂ) ∉
      RingHom.ker (varProj n k) := by
    simp only [RingHom.mem_ker, varProj, MvPolynomial.aeval_X]
    simp
  rw [heq] at hnotmem
  exact hnotmem hmem

/-- The kernel of the augmentation `X i ↦ 0` is the ideal spanned by all variables. -/
private lemma ker_aeval_zero_eq_idealOfVars (n : ℕ) :
    RingHom.ker (MvPolynomial.aeval (0 : Fin n → MvPolynomial (Fin n) ℂ)) =
      MvPolynomial.idealOfVars (Fin n) ℂ := by
  ext p
  rw [MvPolynomial.idealOfVars, ← Set.image_univ, MvPolynomial.mem_ideal_span_X_image,
    RingHom.mem_ker]
  have hiff : (∀ m ∈ p.support, ∃ i : Fin n, m i ≠ 0) ↔ p.coeff 0 = 0 := by
    constructor
    · intro h
      by_contra hc
      have hm : (0 : Fin n →₀ ℕ) ∈ p.support := by
        rw [MvPolynomial.mem_support_iff]; exact hc
      obtain ⟨i, hi⟩ := h 0 hm
      exact hi (by simp)
    · intro h m hm
      have hm0 : m ≠ 0 := by
        intro h0
        rw [h0, MvPolynomial.mem_support_iff] at hm
        exact hm h
      by_contra hc
      push Not at hc
      exact hm0 (Finsupp.ext fun i => by simpa using hc i)
  have hU : (∀ m ∈ p.support, ∃ i ∈ Set.univ, m i ≠ 0) ↔
      ∀ m ∈ p.support, ∃ i : Fin n, m i ≠ 0 := by simp
  rw [hU, hiff]
  constructor
  · intro h
    have hc := congrArg MvPolynomial.constantCoeff h
    rw [MvPolynomial.aeval_zero] at hc
    simpa only [MvPolynomial.algebraMap_eq, MvPolynomial.constantCoeff_C, map_zero,
      MvPolynomial.constantCoeff_eq] using hc
  · intro h
    rw [MvPolynomial.aeval_zero, MvPolynomial.algebraMap_eq, MvPolynomial.C_eq_zero,
      MvPolynomial.constantCoeff_eq]
    exact h

/-- A prime ideal containing all variables has height at least the number of variables. -/
private lemma idealOfVars_le_height {n : ℕ} (p : Ideal (MvPolynomial (Fin n) ℂ)) [p.IsPrime]
    (h : MvPolynomial.idealOfVars (Fin n) ℂ ≤ p) : (n : ℕ∞) ≤ p.height := by
  have hK0 : RingHom.ker (varProj n 0) = ⊥ := by
    rw [varProj_zero]
    exact (RingHom.injective_iff_ker_eq_bot (AlgHom.id ℂ (MvPolynomial (Fin n) ℂ))).mp
      (fun a b h => h)
  have hKn : RingHom.ker (varProj n n) ≤ p := by
    rw [varProj_self, ker_aeval_zero_eq_idealOfVars]; exact h
  have key : ∀ k ≤ n, (k : ℕ∞) ≤ (RingHom.ker (varProj n k)).height := by
    intro k
    induction k with
    | zero => intro _; simp [hK0]
    | succ k ih =>
        intro hk
        have hkn : k < n := Nat.lt_of_succ_le hk
        have hstep := ker_varProj_lt_succ (n := n) hkn
        haveI : (RingHom.ker (varProj n k)).IsPrime := RingHom.ker_isPrime _
        haveI : (RingHom.ker (varProj n (k+1))).IsPrime := RingHom.ker_isPrime _
        have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hstep
        have h2 : (k : ℕ∞) + 1 ≤ (RingHom.ker (varProj n k)).height + 1 := by
          gcongr; exact ih (Nat.le_of_lt hkn)
        calc (k+1 : ℕ∞) = (k : ℕ∞) + 1 := by norm_cast
          _ ≤ (RingHom.ker (varProj n k)).height + 1 := h2
          _ ≤ (RingHom.ker (varProj n (k+1))).height := h1
  exact (key n le_rfl).trans (Ideal.height_mono hKn)

private theorem exists_isHomogeneous_one_notMem_minimalPrimes {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℂ))
    (hht : ∀ p ∈ I.minimalPrimes, p.height < (n : ℕ∞)) :
    ∃ ℓ : MvPolynomial (Fin n) ℂ, ℓ.IsHomogeneous 1 ∧ ∀ p ∈ I.minimalPrimes, ℓ ∉ p := by
  classical
  haveI hfin : Finite ↥(I.minimalPrimes) :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) ℂ) I).to_subtype
  let ψ : (Fin n → ℂ) →ₗ[ℂ] MvPolynomial (Fin n) ℂ :=
    Fintype.linearCombination ℂ (fun i : Fin n => (X i : MvPolynomial (Fin n) ℂ))
  have hψ_single : ∀ i : Fin n, ψ (Pi.single i (1 : ℂ)) = (X i : MvPolynomial (Fin n) ℂ) := by
    intro i
    rw [show ψ (Pi.single i 1) = Fintype.linearCombination ℂ _ (Pi.single i 1) from rfl,
      Fintype.linearCombination_apply]
    simp
  have hψ_hom : ∀ a, (ψ a).IsHomogeneous 1 := by
    intro a
    rw [show ψ a = Fintype.linearCombination ℂ _ a from rfl, Fintype.linearCombination_apply]
    apply MvPolynomial.IsHomogeneous.sum
    intro i _
    rw [MvPolynomial.smul_eq_C_mul]
    exact MvPolynomial.isHomogeneous_C_mul_X _ _
  set W : Ideal (MvPolynomial (Fin n) ℂ) → Submodule ℂ (Fin n → ℂ) :=
    fun p => Submodule.comap ψ (p.restrictScalars ℂ) with hWdef
  have hWmem : ∀ p a, a ∈ W p ↔ ψ a ∈ p := fun p a => Iff.rfl
  have hproper : ∀ x : ↥(I.minimalPrimes), W x.val ≠ ⊤ := by
    intro x hx
    haveI := x.property.isPrime
    have hle : MvPolynomial.idealOfVars (Fin n) ℂ ≤ x.val := by
      rw [MvPolynomial.idealOfVars, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      have hmem : ψ (Pi.single i (1 : ℂ)) ∈ x.val :=
        (hWmem x.val _).mp (by rw [hx]; exact Submodule.mem_top)
      rwa [hψ_single i] at hmem
    have h1 : (n : ℕ∞) ≤ x.val.height := idealOfVars_le_height x.val hle
    have h2 : x.val.height < (n : ℕ∞) := hht x.val x.property
    exact (not_lt.mpr h1) h2
  have hnotcover : (⋃ x : ↥(I.minimalPrimes), (W x.val : Set (Fin n → ℂ))) ≠ Set.univ := by
    intro hc
    obtain ⟨x, hx⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hc
    exact hproper x hx
  obtain ⟨a, ha⟩ := (Set.ne_univ_iff_exists_notMem _).mp hnotcover
  have ha' : ∀ x : ↥(I.minimalPrimes), a ∉ W x.val := by
    intro x hx
    exact ha (Set.mem_iUnion.mpr ⟨x, hx⟩)
  refine ⟨ψ a, hψ_hom a, fun p hp hmem => ?_⟩
  exact ha' ⟨p, hp⟩ ((hWmem p a).mpr hmem)

end Commons.Algebra.MvPolynomial
end


-- ==== from Submission.Commons.Algebra.MvPolynomial.height_idealOfVars ====
section

namespace Commons.Algebra.MvPolynomial

private theorem height_idealOfVars (n : ℕ) :
    (MvPolynomial.idealOfVars (Fin n) ℂ).height = (n : ℕ∞) := by
  haveI : (MvPolynomial.idealOfVars (Fin n) ℂ).IsPrime := by
    rw [← Commons.Algebra.MvPolynomial.ker_aeval_zero_eq_idealOfVars n]
    exact RingHom.ker_isPrime _
  refine le_antisymm ?_ ?_
  · have h := Ideal.height_le_ringKrullDim_of_isPrime
      (R := MvPolynomial (Fin n) ℂ) (I := MvPolynomial.idealOfVars (Fin n) ℂ)
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      zero_add] at h
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h
    exact WithBot.coe_le_coe.mp h
  · exact Commons.Algebra.MvPolynomial.idealOfVars_le_height _ le_rfl

end Commons.Algebra.MvPolynomial
end


-- ==== from Submission.Commons.Algebra.MvPolynomial.ringKrullDim_quotient_of_homogeneous_mprimary ====
section

set_option linter.ambiguousOpen false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Commons.Algebra.MvPolynomial

open _root_.MvPolynomial

private theorem ringKrullDim_le_of_isIntegral {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.IsIntegral R A] : ringKrullDim A ≤ ringKrullDim R :=
  Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R A))
    (fun _ _ h => Ideal.IsIntegral.comap_lt_comap h)

private theorem ringKrullDim_le_of_adjoin_range_eq_top {m : ℕ} {A : Type*} [CommRing A] [Algebra ℂ A]
    (a : Fin m → A) (h : Algebra.adjoin ℂ (Set.range a) = ⊤) : ringKrullDim A ≤ (m : ℕ) := by
  let ψ : MvPolynomial (Fin m) ℂ →ₐ[ℂ] A := MvPolynomial.aeval a
  have hsurj : Function.Surjective ψ := by
    rw [← AlgHom.range_eq_top, MvPolynomial.aeval_range a, h]
  have h1 : ringKrullDim A ≤ ringKrullDim (MvPolynomial (Fin m) ℂ) :=
    ringKrullDim_le_of_surjective ψ.toRingHom hsurj
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
    Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  exact_mod_cast h1

private theorem LTSeries_length_le_ringKrullDim_quotient {R : Type*} [CommRing R] {J : Ideal R}
    (l : LTSeries (PrimeSpectrum R)) (h : J ≤ (l 0).asIdeal) :
    (l.length : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ J) := by
  have hall : ∀ i : Fin (l.length + 1), J ≤ (l i).asIdeal := fun i =>
    le_trans h (l.monotone (Fin.zero_le i))
  let l₁ : LTSeries ↥(PrimeSpectrum.zeroLocus (J : Set R)) :=
    { length := l.length
      toFun := fun i => ⟨l i, by rw [PrimeSpectrum.mem_zeroLocus]; exact hall i⟩
      step := fun i => l.step i }
  have hlen : l₁.length = l.length := rfl
  have h1 := Order.LTSeries.length_le_krullDim l₁
  rw [hlen] at h1
  have h2 : Order.krullDim ↥(PrimeSpectrum.zeroLocus (J : Set R)) = ringKrullDim (R ⧸ J) := by
    rw [ringKrullDim, Order.krullDim_eq_of_orderIso
      (Ideal.primeSpectrumQuotientOrderIsoZeroLocus J)]
  rwa [h2] at h1

private lemma nat_sub_le_of_le_add {d : ℕ∞} {k n : ℕ} (hkn : k ≤ n)
    (h : (n : ℕ∞) ≤ d + (k : ℕ∞)) : ((n - k : ℕ) : ℕ∞) ≤ d := by
  rw [ENat.natCast_sub, tsub_le_iff_right]
  exact h

private lemma idealOfVars_ne_top (n : ℕ) :
    MvPolynomial.idealOfVars (Fin n) ℂ ≠ ⊤ := by
  intro htop
  have hle : MvPolynomial.idealOfVars (Fin n) ℂ ≤ RingHom.ker MvPolynomial.constantCoeff := by
    rw [MvPolynomial.idealOfVars, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [RingHom.mem_ker, MvPolynomial.constantCoeff_eq]
  have : (1 : MvPolynomial (Fin n) ℂ) ∈ RingHom.ker MvPolynomial.constantCoeff :=
    hle (htop ▸ Submodule.mem_top)
  simp [RingHom.mem_ker, MvPolynomial.constantCoeff_eq] at this

private theorem ringKrullDim_quotient_of_homogeneous_mprimary {n e : ℕ} (g : Fin n → MvPolynomial (Fin n) ℂ)
    (hg : ∀ i, (g i).IsHomogeneous e) (he : 1 ≤ e)
    (hfin : Module.rank ℂ (MvPolynomial (Fin n) ℂ ⧸ Ideal.span (Set.range g)) < Cardinal.aleph0)
    (k : ℕ) (hk : k ≤ n) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸
        Ideal.span (Set.range (fun j : Fin k => g (Fin.castLE hk j)))) = (n - k : ℕ) := by
  have hB := finite_adjoin_range_of_finite_quotient g hg he hfin
  let φ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ := MvPolynomial.aeval g
  have hrange : φ.range = Algebra.adjoin ℂ (Set.range g) := MvPolynomial.aeval_range g
  have hInt : Algebra.IsIntegral ↥φ.range (MvPolynomial (Fin n) ℂ) := by
    rw [hrange]; exact Algebra.IsIntegral.of_finite _ _
  have hcomp : φ.toRingHom = (algebraMap ↥φ.range (MvPolynomial (Fin n) ℂ)).comp
      (AlgHom.rangeRestrict φ).toRingHom := by
    ext x
    · rfl
    · simp [AlgHom.rangeRestrict]
  have hstrict : StrictMono (PrimeSpectrum.comap φ.toRingHom) := by
    have h1 : StrictMono (PrimeSpectrum.comap (algebraMap ↥φ.range (MvPolynomial (Fin n) ℂ))) :=
      fun P Q h => Ideal.IsIntegral.comap_lt_comap h
    have h2 : StrictMono (PrimeSpectrum.comap (AlgHom.rangeRestrict φ).toRingHom) :=
      RingHom.strictMono_comap_of_surjective (AlgHom.rangeRestrict_surjective φ)
    rw [hcomp, PrimeSpectrum.comap_comp]
    exact h2.comp h1
  have hchain : ∀ l : LTSeries (PrimeSpectrum (MvPolynomial (Fin n) ℂ)),
      Ideal.span (Set.range (fun j : Fin k => g (Fin.castLE hk j))) ≤ (l 0).asIdeal →
      l.length ≤ n - k := by
    intro l hl
    haveI : Algebra.IsIntegral ↥φ.range (MvPolynomial (Fin n) ℂ) := hInt
    let l' : LTSeries (PrimeSpectrum (MvPolynomial (Fin n) ℂ)) :=
      l.map (PrimeSpectrum.comap φ.toRingHom) hstrict
    have hlen : l'.length = l.length := LTSeries.map_length _ _ _
    have hJk : (Ideal.span (Set.range (fun i : Fin k =>
        (MvPolynomial.X (Fin.castLE hk i) : MvPolynomial (Fin n) ℂ)))) ≤ (l' 0).asIdeal := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [show (l' 0).asIdeal = Ideal.comap φ.toRingHom (l 0).asIdeal from
        PrimeSpectrum.comap_asIdeal φ.toRingHom (l 0)]
      change φ.toRingHom (MvPolynomial.X (Fin.castLE hk i)) ∈ (l 0).asIdeal
      rw [show φ.toRingHom (MvPolynomial.X (Fin.castLE hk i)) = g (Fin.castLE hk i) from
        MvPolynomial.aeval_X g _]
      exact hl (Ideal.subset_span ⟨i, rfl⟩)
    have h1 := LTSeries_length_le_ringKrullDim_quotient l' hJk
    have h2 : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸
        Ideal.span (Set.range (fun i : Fin k =>
          (MvPolynomial.X (Fin.castLE hk i) : MvPolynomial (Fin n) ℂ)))) =
        ((n - k : ℕ) : WithBot ℕ∞) := by
      obtain ⟨ee⟩ := quotient_span_range_X_castLE_algEquiv hk
      rw [ringKrullDim_eq_of_ringEquiv ee.toRingEquiv,
        MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
        Nat.card_eq_fintype_card, Fintype.card_fin]
    rw [hlen, h2] at h1
    exact_mod_cast h1
  have hIVle : Ideal.span (Set.range (fun j : Fin k => g (Fin.castLE hk j))) ≤
      MvPolynomial.idealOfVars (Fin n) ℂ := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    rw [MvPolynomial.idealOfVars,
      show Set.range (MvPolynomial.X) = MvPolynomial.X '' (Set.univ : Set (Fin n)) from by simp]
    change g (Fin.castLE hk j) ∈ Ideal.span (MvPolynomial.X '' (Set.univ : Set (Fin n)))
    rw [MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    have hmdeg : Finsupp.degree m = e := by
      by_contra hc
      exact (MvPolynomial.mem_support_iff.mp hm) ((hg (Fin.castLE hk j)).coeff_eq_zero hc)
    have hne0 : m ≠ 0 := by
      intro h0
      have h1 : Finsupp.degree m = 0 := by rw [h0, Finsupp.degree_eq_zero_iff]
      omega
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hne0
    exact ⟨i, Set.mem_univ i, hi⟩
  haveI : Nontrivial (MvPolynomial (Fin n) ℂ ⧸
      Ideal.span (Set.range (fun j : Fin k => g (Fin.castLE hk j)))) :=
    Ideal.Quotient.nontrivial_iff.mpr (fun htop =>
      idealOfVars_ne_top n (top_le_iff.mp (htop ▸ hIVle)))
  have hup : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸
      Ideal.span (Set.range (fun j : Fin k => g (Fin.castLE hk j)))) ≤ ((n - k : ℕ) : WithBot ℕ∞) := by
    rw [ringKrullDim, Order.krullDim_eq_iSup_length,
      ← WithBot.coe_natCast, WithBot.coe_le_coe, iSup_le_iff]
    intro l
    let J : Ideal (MvPolynomial (Fin n) ℂ) :=
      Ideal.span (Set.range (fun j : Fin k => g (Fin.castLE hk j)))
    let l₁ : LTSeries ↥(PrimeSpectrum.zeroLocus (J : Set (MvPolynomial (Fin n) ℂ))) :=
      l.map (Ideal.primeSpectrumQuotientOrderIsoZeroLocus J) (OrderIso.strictMono _)
    let l₂ : LTSeries (PrimeSpectrum (MvPolynomial (Fin n) ℂ)) :=
      l₁.map Subtype.val (fun _ _ h => h)
    have hlen : l₂.length = l.length := by
      calc l₂.length = l₁.length := LTSeries.map_length _ _ _
        _ = l.length := LTSeries.map_length _ _ _
    have hJ : J ≤ (l₂ 0).asIdeal := by
      simp only [l₂, l₁]
      exact (l.map (Ideal.primeSpectrumQuotientOrderIsoZeroLocus J)
        (OrderIso.strictMono _) 0).2
    have hmain := hchain l₂ (by simpa only [J] using hJ)
    rw [hlen] at hmain
    exact_mod_cast hmain
  have hlow : ((n - k : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸
      Ideal.span (Set.range (fun j : Fin k => g (Fin.castLE hk j)))) := by
    set J : Ideal (MvPolynomial (Fin n) ℂ) :=
      Ideal.span (Set.range (fun j : Fin k => g (Fin.castLE hk j))) with hJdef
    have hJle : J ≤ MvPolynomial.idealOfVars (Fin n) ℂ := by
      rw [hJdef]; exact hIVle
    haveI hIVprime : (MvPolynomial.idealOfVars (Fin n) ℂ).IsPrime := by
      rw [← Commons.Algebra.MvPolynomial.ker_aeval_zero_eq_idealOfVars n]
      exact RingHom.ker_isPrime _
    have hK := Ideal.height_le_ringKrullDim_quotient_add_encard (R := MvPolynomial (Fin n) ℂ)
      (p := MvPolynomial.idealOfVars (Fin n) ℂ)
      (s := Set.range (fun j : Fin k => g (Fin.castLE hk j)))
      (by rintro _ ⟨j, rfl⟩; exact hJle (Ideal.subset_span ⟨j, rfl⟩))
    rw [height_idealOfVars] at hK
    rw [show Ideal.span (Set.range (fun j : Fin k => g (Fin.castLE hk j))) = J from hJdef.symm] at hK
    -- arithmetic
    have hne : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≠ ⊥ := by
      intro hbot
      have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) ℂ ⧸ J)
      rw [hbot] at h0
      exact not_le_of_gt (WithBot.bot_lt_coe (0 : ℕ∞)) h0
    obtain ⟨e', he'⟩ := WithBot.ne_bot_iff_exists.mp hne
    · have hK' : (n : ℕ∞) ≤ e' +
          (Set.range (fun j : Fin k => g (Fin.castLE hk j))).encard := by
        have := hK
        rw [← he'] at this
        rw [← WithBot.coe_add, WithBot.coe_le_coe] at this
        exact this
      have henc : (Set.range (fun j : Fin k => g (Fin.castLE hk j))).encard ≤ (k : ℕ∞) := by
        have h1 : (Set.range (fun j : Fin k => g (Fin.castLE hk j))).encard
            ≤ (Set.univ : Set (Fin k)).encard := by
          rw [show Set.range (fun j : Fin k => g (Fin.castLE hk j))
              = (fun j : Fin k => g (Fin.castLE hk j)) '' Set.univ from by simp]
          exact Set.encard_image_le _ _
        rw [Set.encard_univ, ENat.card_eq_coe_natCard, Nat.card_eq_fintype_card,
          Fintype.card_fin] at h1
        exact h1
      have h2 : (n : ℕ∞) ≤ e' + (k : ℕ∞) := hK'.trans (add_le_add (le_refl e') henc)
      have h3 : ((n - k : ℕ) : ℕ∞) ≤ e' := nat_sub_le_of_le_add hk h2
      rw [← he', ← WithBot.coe_natCast, WithBot.coe_le_coe]
      exact h3

  exact le_antisymm hup hlow

end Commons.Algebra.MvPolynomial

end


-- ==== from Submission.Commons.RingTheory.Ideal.Hilbert.ringKrullDim_quotient_eq_height_idealOfVars ====
section

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

namespace Commons.RingTheory.Ideal.Hilbert

open MvPolynomial

universe u

/-! ## Auxiliary lemmas -/

/-- The irrelevant ideal is proper (it is contained in the augmentation kernel). -/
private lemma idealOfVars_ne_top {k : Type*} [Field k] {m : ℕ} :
    MvPolynomial.idealOfVars (Fin m) k ≠ ⊤ := by
  intro htop
  have hle : MvPolynomial.idealOfVars (Fin m) k ≤ RingHom.ker MvPolynomial.constantCoeff := by
    rw [MvPolynomial.idealOfVars, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [RingHom.mem_ker]
  have : (1 : MvPolynomial (Fin m) k) ∈ RingHom.ker MvPolynomial.constantCoeff :=
    hle (htop ▸ Submodule.mem_top)
  simp [RingHom.mem_ker] at this

/-- Membership in the irrelevant ideal is to have vanishing constant term. -/
private lemma mem_idealOfVars_iff_coeff_zero {σ : Type*} {K : Type*} [Field K] (x : MvPolynomial σ K) :
    x ∈ MvPolynomial.idealOfVars σ K ↔ MvPolynomial.coeff 0 x = 0 := by
  rw [MvPolynomial.idealOfVars,
    show Set.range (MvPolynomial.X) = MvPolynomial.X '' (Set.univ : Set σ) from by simp,
    MvPolynomial.mem_ideal_span_X_image]
  constructor
  · intro h
    by_contra hc
    have hm : (0 : σ →₀ ℕ) ∈ x.support := MvPolynomial.mem_support_iff.mpr hc
    obtain ⟨i, -, hi⟩ := h 0 hm
    exact hi (by simp)
  · intro h m hm
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact (MvPolynomial.mem_support_iff.mp hm) h
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hm0
    exact ⟨i, Set.mem_univ i, hi⟩

/-- A homogeneous polynomial of positive degree lies in the irrelevant ideal. -/
private lemma isHomogeneous_mem_idealOfVars {σ : Type*} {K : Type*} [Field K]
    {y : MvPolynomial σ K} {j : ℕ} (hy : y.IsHomogeneous j) (hj : 1 ≤ j) :
    y ∈ MvPolynomial.idealOfVars σ K := by
  rw [MvPolynomial.idealOfVars,
    show Set.range (MvPolynomial.X) = MvPolynomial.X '' (Set.univ : Set σ) from by simp,
    MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  have hdeg : Finsupp.degree m = j := by
    by_contra hc
    exact (MvPolynomial.mem_support_iff.mp hm) (hy.coeff_eq_zero hc)
  have hm0 : m ≠ 0 := by
    intro h0
    have h0' : Finsupp.degree m = 0 := by rw [h0, Finsupp.degree_eq_zero_iff]
    omega
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hm0
  exact ⟨i, Set.mem_univ i, hi⟩

/-- The height of the image of a prime ideal in a quotient is at most its height. -/
private theorem height_map_quotient_le {R : Type*} [CommRing R] {P Q : Ideal R} (hPQ : P ≤ Q) [Q.IsPrime] :
    (Q.map (Ideal.Quotient.mk P)).height ≤ Q.height := by
  haveI hprime : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hPQ)
  have hsm : StrictMono (PrimeSpectrum.comap (Ideal.Quotient.mk P)) :=
    RingHom.strictMono_comap_of_surjective (f := Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  have hc : (PrimeSpectrum.comap (Ideal.Quotient.mk P))
      (⟨Q.map (Ideal.Quotient.mk P), hprime⟩ : PrimeSpectrum (R ⧸ P)) =
      (⟨Q, ‹Q.IsPrime›⟩ : PrimeSpectrum R) := by
    rw [PrimeSpectrum.ext_iff]
    show Ideal.comap (Ideal.Quotient.mk P) (Ideal.map (Ideal.Quotient.mk P) Q) = Q
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hPQ
  have h := Order.height_le_height_apply_of_strictMono
    (PrimeSpectrum.comap (Ideal.Quotient.mk P)) hsm
    (⟨Q.map (Ideal.Quotient.mk P), hprime⟩ : PrimeSpectrum (R ⧸ P))
  rw [hc] at h
  calc (Q.map (Ideal.Quotient.mk P)).height
      = Order.height (⟨Q.map (Ideal.Quotient.mk P), hprime⟩ : PrimeSpectrum (R ⧸ P)) := by
        rw [← PrimeSpectrum.height_eq_orderHeight]
    _ ≤ Order.height (⟨Q, ‹Q.IsPrime›⟩ : PrimeSpectrum R) := h
    _ = Q.height := by rw [← PrimeSpectrum.height_eq_orderHeight]

/-- Every maximal ideal of a polynomial ring over a field has height the number of variables. -/
private theorem maximalIdeal_height_lower {k : Type u} [Field k] :
    ∀ (s : ℕ) (p : Ideal (MvPolynomial (Fin s) k)), p.IsMaximal → (s : ℕ∞) ≤ p.height := by
  intro s
  induction s with
  | zero => intro p hp; exact zero_le
  | succ s ih =>
    intro p hp
    let e := (MvPolynomial.finSuccEquiv k s).toRingEquiv
    let P : Ideal (Polynomial (MvPolynomial (Fin s) k)) := p.map e
    haveI hp' : p.IsMaximal := hp
    haveI hP : P.IsMaximal := Ideal.map_isMaximal_of_equiv e
    haveI hc : (Ideal.comap Polynomial.C P).IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing P
    haveI hlie : P.LiesOver (Ideal.comap Polynomial.C P) := Ideal.LiesOver.mk rfl
    have h1 : P.height = (Ideal.comap Polynomial.C P).height + 1 :=
      Polynomial.height_eq_height_add_one _ P
    have h2 : (s : ℕ∞) ≤ (Ideal.comap Polynomial.C P).height := ih _ hc
    have h3 : ((s + 1 : ℕ) : ℕ∞) ≤ P.height := by
      have h3a : ((s : ℕ∞) + 1) ≤ P.height := by
        rw [h1]; exact add_le_add h2 le_rfl
      have hs1 : ((s + 1 : ℕ) : ℕ∞) = (s : ℕ∞) + 1 := by push_cast; ring
      rwa [hs1]
    have h4 : (p.map e).height = p.height := RingEquiv.height_map e p
    rw [← h4]
    exact h3

private theorem maximalIdeal_height_eq_card {k : Type u} [Field k] {s : ℕ}
    (p : Ideal (MvPolynomial (Fin s) k)) [p.IsMaximal] : p.height = (s : ℕ∞) := by
  refine le_antisymm ?_ (maximalIdeal_height_lower s p ‹p.IsMaximal›)
  have h := Ideal.height_le_ringKrullDim_of_isPrime (I := p)
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
    Nat.card_eq_fintype_card, Fintype.card_fin] at h
  exact WithBot.coe_le_coe.mp h

/-- In a finitely generated domain over a field, every maximal ideal has height the Krull
dimension. -/
private theorem fg_domain_maximalIdeal_height_eq_ringKrullDim {k B : Type*} [Field k] [CommRing B]
    [IsDomain B] [Algebra k B] [Algebra.FiniteType k B] (n : Ideal B) [n.IsMaximal] :
    (n.height : WithBot ℕ∞) = ringKrullDim B := by
  obtain ⟨s, g, hg_inj, hg_fin⟩ := exists_finite_inj_algHom_of_fg k B
  letI : Algebra (MvPolynomial (Fin s) k) B := g.toRingHom.toAlgebra
  have hmap : algebraMap (MvPolynomial (Fin s) k) B = g.toRingHom := rfl
  haveI : Module.Finite (MvPolynomial (Fin s) k) B := hg_fin
  haveI : IsScalarTower k (MvPolynomial (Fin s) k) B :=
    IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) B := Algebra.IsIntegral.of_finite _ _
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (by rw [hmap]; exact hg_inj)
  let p' : Ideal (MvPolynomial (Fin s) k) := n.comap (algebraMap (MvPolynomial (Fin s) k) B)
  haveI hp'max : p'.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal n
  have hp'height : p'.height = (s : ℕ∞) := maximalIdeal_height_eq_card (s := s) p'
  have hdimB : ringKrullDim B = (s : WithBot ℕ∞) := by
    rw [Commons.RingTheory.KrullDimension.ringKrullDim_eq_of_isIntegral
        (by rw [hmap]; exact hg_inj),
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  refine le_antisymm (Ideal.height_le_ringKrullDim_of_isPrime (I := n)) ?_
  rw [hdimB]
  haveI : p'.FiniteHeight := ⟨Or.inr (by rw [hp'height]; exact ENat.natCast_ne_top s)⟩
  obtain ⟨l, hlast, hlen⟩ := Ideal.exists_ltSeries_length_eq_height p'
  have hls : l.length = s := by
    rw [hp'height] at hlen
    exact Nat.cast_injective hlen
  haveI : n.LiesOver (RelSeries.last l).asIdeal := by
    rw [hlast]
    exact Ideal.LiesOver.mk rfl
  obtain ⟨L, hLlen, hLlast, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown l n
  have hfin : L.length ≤ n.height := by
    calc L.length ≤ Order.height (RelSeries.last L) := Order.length_le_height_last (p := L)
      _ = Order.height (⟨n, ‹n.IsMaximal›.isPrime⟩ : PrimeSpectrum B) := by rw [hLlast]
      _ = n.height := by rw [← PrimeSpectrum.height_eq_orderHeight]
  rw [hLlen, hls] at hfin
  exact_mod_cast hfin

noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Minimal primes of a homogeneous ideal are contained in the irrelevant ideal. -/
private theorem minimalPrimes_le_idealOfVars {k : Type*} [Field k] {m : ℕ}
    (J : Ideal (MvPolynomial (Fin m) k))
    (hJ : ∀ x ∈ J, ∀ j, MvPolynomial.homogeneousComponent j x ∈ J)
    {p : Ideal (MvPolynomial (Fin m) k)} (hp : p ∈ J.minimalPrimes) :
    p ≤ MvPolynomial.idealOfVars (Fin m) k := by
  classical
  haveI hpp : p.IsPrime := hp.1.1
  have hJhom : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin m) k) := by
    rw [Ideal.IsHomogeneous.iff_eq]
    refine le_antisymm (Ideal.toIdeal_homogeneousCore_le _ J) ?_
    intro x hx
    rw [← MvPolynomial.sum_homogeneousComponent x]
    refine Ideal.sum_mem _ fun i hi => ?_
    exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem
      ⟨i, MvPolynomial.homogeneousComponent_mem i x⟩ (hJ x hx i)
  have hphom : p.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin m) k) := by
    rw [Ideal.IsHomogeneous.iff_eq]
    refine le_antisymm (Ideal.toIdeal_homogeneousCore_le _ p) ?_
    have hqprime :
        ((Ideal.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin m) k) p).toIdeal).IsPrime :=
      Ideal.IsPrime.homogeneousCore hpp
    have hJle_hc : J ≤
        (Ideal.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin m) k) p).toIdeal := by
      rw [← Ideal.IsHomogeneous.toIdeal_homogeneousCore_eq_self hJhom]
      exact (Ideal.homogeneousCore.gc (MvPolynomial.homogeneousSubmodule (Fin m) k)).monotone_l
        (Ideal.homogeneousCore_mono _ hp.1.2)
    exact hp.2 ⟨hqprime, hJle_hc⟩ (Ideal.toIdeal_homogeneousCore_le _ p)
  intro x hx
  rw [mem_idealOfVars_iff_coeff_zero]
  have hxmem : ∀ n, MvPolynomial.homogeneousComponent n x ∈ p :=
    (MvPolynomial.mem_iff_homogeneousComponent_mem (I := p) hphom x).mp hx
  have h0 : MvPolynomial.C (MvPolynomial.coeff 0 x) ∈ p := by
    rw [← MvPolynomial.homogeneousComponent_zero]
    exact hxmem 0
  by_contra hne
  have h1 : (1 : MvPolynomial (Fin m) k) ∈ p := by
    have hmem := p.mul_mem_left (MvPolynomial.C (MvPolynomial.coeff 0 x)⁻¹) h0
    rwa [← MvPolynomial.C_mul, inv_mul_cancel₀ hne, MvPolynomial.C_1] at hmem
  exact hpp.ne_top ((Ideal.eq_top_iff_one p).mpr h1)

end

private theorem ringKrullDim_quotient_eq_height_idealOfVars {k : Type*} [Field k] {m : ℕ}
    (J : Ideal (MvPolynomial (Fin m) k))
    (hJ : ∀ x ∈ J, ∀ j, MvPolynomial.homogeneousComponent j x ∈ J)
    (hJle : J ≤ MvPolynomial.idealOfVars (Fin m) k) :
    ringKrullDim (MvPolynomial (Fin m) k ⧸ J) =
      ((MvPolynomial.idealOfVars (Fin m) k).map (Ideal.Quotient.mk J)).height := by
  classical
  have hn_eq : MvPolynomial.idealOfVars (Fin m) k = RingHom.ker MvPolynomial.constantCoeff := by
    ext x
    rw [RingHom.mem_ker, mem_idealOfVars_iff_coeff_zero, MvPolynomial.constantCoeff_eq]
  have hnprime : (MvPolynomial.idealOfVars (Fin m) k).IsPrime := by
    rw [hn_eq]; exact RingHom.ker_isPrime _
  haveI hnmax : (MvPolynomial.idealOfVars (Fin m) k).IsMaximal := by
    rw [hn_eq]
    exact RingHom.ker_isMaximal_of_surjective MvPolynomial.constantCoeff
      (fun x => ⟨MvPolynomial.C x, by simp⟩)
  haveI hnAmax : ((MvPolynomial.idealOfVars (Fin m) k).map (Ideal.Quotient.mk J)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hJle)
  haveI hnAprime : ((MvPolynomial.idealOfVars (Fin m) k).map (Ideal.Quotient.mk J)).IsPrime :=
    hnAmax.isPrime
  refine le_antisymm ?_ (Ideal.height_le_ringKrullDim_of_isPrime (I := _))
  rw [ringKrullDim_le_iff_height_le]
  intro Q hQ
  rw [WithBot.coe_le_coe]
  rw [show Q.height = Order.height (⟨Q, hQ⟩ : PrimeSpectrum (MvPolynomial (Fin m) k ⧸ J)) from
      PrimeSpectrum.height_eq_orderHeight (⟨Q, hQ⟩ : PrimeSpectrum (MvPolynomial (Fin m) k ⧸ J))]
  apply Order.height_le
  intro l hl
  obtain ⟨P, hP, hPle⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal (MvPolynomial (Fin m) k ⧸ J)))
    (J := (l.toFun 0).asIdeal) bot_le
  have hPprime : P.IsPrime := hP.1.1
  haveI hPprimeI : P.IsPrime := hPprime
  have hp_mem : P.comap (Ideal.Quotient.mk J) ∈ J.minimalPrimes := by
    have h := Ideal.minimalPrimes_comap_of_surjective (f := Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective hP
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at h
    exact h
  have hP_le_nA : P ≤ (MvPolynomial.idealOfVars (Fin m) k).map (Ideal.Quotient.mk J) := by
    rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective P]
    exact Ideal.map_mono (minimalPrimes_le_idealOfVars J hJ hp_mem)
  haveI : Algebra.FiniteType k (MvPolynomial (Fin m) k ⧸ J) := Algebra.FiniteType.quotient k J
  haveI : Algebra.FiniteType k ((MvPolynomial (Fin m) k ⧸ J) ⧸ P) :=
    Algebra.FiniteType.quotient k P
  haveI : (((MvPolynomial.idealOfVars (Fin m) k).map (Ideal.Quotient.mk J)).map
      (Ideal.Quotient.mk P)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hP_le_nA)
  have hchain := Commons.Algebra.MvPolynomial.LTSeries_length_le_ringKrullDim_quotient l hPle
  have hM := fg_domain_maximalIdeal_height_eq_ringKrullDim (k := k)
    (B := (MvPolynomial (Fin m) k ⧸ J) ⧸ P)
    (n := ((MvPolynomial.idealOfVars (Fin m) k).map (Ideal.Quotient.mk J)).map (Ideal.Quotient.mk P))
  rw [← hM] at hchain
  have hchain' : l.length ≤ (((MvPolynomial.idealOfVars (Fin m) k).map
      (Ideal.Quotient.mk J)).map (Ideal.Quotient.mk P)).height := WithBot.coe_le_coe.mp hchain
  exact hchain'.trans (height_map_quotient_le hP_le_nA)

end Commons.RingTheory.Ideal.Hilbert

end


-- ==== from Submission.Commons.RingTheory.Ideal.Hilbert.hilbertFun_eq_sum_hilbertFun_sup_span_X ====
section

set_option linter.style.haveILetI false

open MvPolynomial
open Commons.RingTheory.Ideal.Hilbert

namespace Commons.RingTheory.Ideal.Hilbert

private lemma hilbertFun_homogeneousSubmodule_zero {k : Type*} [Field k] {m : ℕ}
    (I : Ideal (MvPolynomial (Fin m) k)) (hI : I ≠ ⊤) :
    hilbertFun I (MvPolynomial.homogeneousSubmodule (Fin m) k 0) = 1 := by
  classical
  haveI : Module.Finite k ↥(MvPolynomial.homogeneousSubmodule (Fin m) k 0) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin m) k 0)
  rw [hilbertFun_eq_sub]
  have hbot : MvPolynomial.homogeneousSubmodule (Fin m) k 0 ⊓ I.restrictScalars k = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [Submodule.mem_inf] at hx
    obtain ⟨hxV, hxI⟩ := hx
    rw [MvPolynomial.homogeneousSubmodule_zero] at hxV
    obtain ⟨y, hy⟩ := Submodule.mem_one.mp hxV
    by_contra hx0
    have hy0 : y ≠ 0 := fun hyy => hx0 (by rw [← hy, hyy, map_zero])
    have hsmul : y⁻¹ • x = 1 := by
      rw [← hy, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hy0, map_one]
    have h1I : (1 : MvPolynomial (Fin m) k) ∈ I := by
      rw [← hsmul]
      exact (I.restrictScalars k).smul_mem y⁻¹ hxI
    exact hI ((Ideal.eq_top_iff_one I).mpr h1I)
  rw [hbot, MvPolynomial.homogeneousSubmodule_zero, Submodule.one_eq_span,
    finrank_span_singleton (one_ne_zero)]
  simp

private lemma hilbertFun_succ {k : Type*} [Field k] {m : ℕ}
    (p : Ideal (MvPolynomial (Fin m) k)) [p.IsPrime]
    (hp : ∀ x ∈ p, ∀ j, MvPolynomial.homogeneousComponent j x ∈ p)
    {i : Fin m} (hf : MvPolynomial.X i ∉ p) (u : ℕ) :
    hilbertFun p (MvPolynomial.homogeneousSubmodule (Fin m) k (u+1))
      = hilbertFun p (MvPolynomial.homogeneousSubmodule (Fin m) k u)
        + hilbertFun (p ⊔ Ideal.span {MvPolynomial.X i})
            (MvPolynomial.homogeneousSubmodule (Fin m) k (u+1)) := by
  classical
  let R := MvPolynomial (Fin m) k
  let t : R := MvPolynomial.X i
  let J : Ideal R := p ⊔ Ideal.span {t}
  let V : ℕ → Submodule k R := fun j => MvPolynomial.homogeneousSubmodule (Fin m) k j
  let A : ℕ → Submodule k (R ⧸ p) := fun j => Submodule.map (p.mkQ.restrictScalars k) (V j)
  let C : ℕ → Submodule k (R ⧸ J) := fun j => Submodule.map (J.mkQ.restrictScalars k) (V j)
  change Module.finrank k ↥(A (u+1)) = Module.finrank k ↥(A u) + Module.finrank k ↥(C (u+1))
  let σ : R ⧸ p →ₗ[k] R ⧸ J := (Ideal.Quotient.factorₐ k (le_sup_left)).toLinearMap
  have hσ : ∀ x : R, σ ((p.mkQ.restrictScalars k) x) = (J.mkQ.restrictScalars k) x := by
    intro x
    simp only [Submodule.mkQ_apply, LinearMap.restrictScalars_apply, σ, AlgHom.toLinearMap_apply,
      Ideal.Quotient.factorₐ_apply]
    rw [Ideal.Quotient.mk_eq_mk, Ideal.Quotient.factor_mk]
    exact (Ideal.Quotient.mk_eq_mk x).symm
  have hC : ∀ j, C j = Submodule.map σ (A j) := by
    intro j
    apply le_antisymm
    · intro y hy
      rw [Submodule.mem_map] at hy ⊢
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨(p.mkQ.restrictScalars k) x, ⟨x, hx, rfl⟩, (hσ x).symm⟩
    · intro y hy
      rw [Submodule.mem_map] at hy ⊢
      obtain ⟨z, hz, rfl⟩ := hy
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hz
      exact ⟨x, hx, hσ x⟩
  let mσ : R ⧸ p →ₗ[k] R ⧸ p :=
    (LinearMap.mulLeft (R ⧸ p) (Ideal.Quotient.mk p t)).restrictScalars k
  have hmσ : ∀ x, mσ x = (Ideal.Quotient.mk p t) * x := by
    intro x
    simp [mσ, LinearMap.mulLeft_apply]
  have hmσ_π : ∀ x : R, mσ ((p.mkQ.restrictScalars k) x) = (p.mkQ.restrictScalars k) (t * x) := by
    intro x
    rw [hmσ]
    simp only [Submodule.mkQ_apply, LinearMap.restrictScalars_apply]
    rw [Ideal.Quotient.mk_eq_mk]
    exact (map_mul (Ideal.Quotient.mk p) t x).symm
  have hmem : ∀ x ∈ A u, mσ x ∈ A (u+1) := by
    intro x hx
    rw [Submodule.mem_map] at hx ⊢
    obtain ⟨v, hv, rfl⟩ := hx
    refine ⟨t * v, ?_, (hmσ_π v).symm⟩
    rw [MvPolynomial.mem_homogeneousSubmodule]
    have hv' : v.IsHomogeneous u := (MvPolynomial.mem_homogeneousSubmodule u v).mp hv
    have hmul : (MvPolynomial.X i * v).IsHomogeneous (1 + u) :=
      (MvPolynomial.isHomogeneous_X k i).mul hv'
    rw [Nat.add_comm 1 u] at hmul
    exact hmul
  let f : A u →ₗ[k] A (u+1) := LinearMap.restrict mσ hmem
  have hf_apply : ∀ y : A u, ((f y : A (u+1)) : R ⧸ p) = mσ (y : R ⧸ p) := fun y => rfl
  let g : A (u+1) →ₗ[k] R ⧸ J := σ.comp (Submodule.subtype (A (u+1)))
  have hg_apply : ∀ x : A (u+1), g x = σ (x : R ⧸ p) := fun x => rfl
  have hg_range : g.range = C (u+1) := by
    rw [hC (u+1)]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(x : R ⧸ p), x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hmσ_inj : ∀ z ∈ A u, mσ z = 0 → z = 0 := by
    intro z hz hz0
    obtain ⟨w, hw, hwz⟩ := Submodule.mem_map.mp hz
    have ht_w : t * w ∈ p := by
      have h1 : (p.mkQ.restrictScalars k) (t * w) = 0 := by
        rw [← hmσ_π w, hwz]
        exact hz0
      simp only [LinearMap.restrictScalars_apply, Submodule.mkQ_apply] at h1
      rw [Ideal.Quotient.mk_eq_mk] at h1
      exact Ideal.Quotient.eq_zero_iff_mem.mp h1
    have hw_p : w ∈ p := by
      rcases Ideal.IsPrime.mem_or_mem (show p.IsPrime from inferInstance) ht_w with h | h
      · exact absurd h hf
      · exact h
    rw [← hwz]
    simp only [LinearMap.restrictScalars_apply, Submodule.mkQ_apply]
    rw [Ideal.Quotient.mk_eq_mk]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hw_p
  have hf_inj : Function.Injective f := by
    intro y1 y2 h
    apply Subtype.ext
    have h' : mσ ((y1 : A u) : R ⧸ p) = mσ ((y2 : A u) : R ⧸ p) := by
      have := congrArg (fun z : A (u+1) => (z : R ⧸ p)) h
      rw [hf_apply, hf_apply] at this
      exact this
    have hmem1 : ((y1 : A u) : R ⧸ p) - ((y2 : A u) : R ⧸ p) ∈ A u :=
      (A u).sub_mem y1.property y2.property
    have h0 : mσ (((y1 : A u) : R ⧸ p) - ((y2 : A u) : R ⧸ p)) = 0 := by
      rw [map_sub, h', sub_self]
    have := hmσ_inj _ hmem1 h0
    exact sub_eq_zero.mp this
  have hg_ker : g.ker = f.range := by
    ext x
    constructor
    · intro hx
      rw [LinearMap.mem_ker] at hx
      have hgx : σ (x : R ⧸ p) = 0 := by
        have hh : g x = 0 := hx
        simpa [hg_apply] using hh
      obtain ⟨v, hv, hvx⟩ := Submodule.mem_map.mp x.property
      have hvJ : v ∈ J := by
        have h1 : (J.mkQ.restrictScalars k) v = 0 := by
          rw [← hσ v, hvx]
          exact hgx
        simp only [LinearMap.restrictScalars_apply, Submodule.mkQ_apply] at h1
        rw [Ideal.Quotient.mk_eq_mk] at h1
        exact Ideal.Quotient.eq_zero_iff_mem.mp h1
      rw [Submodule.mem_sup] at hvJ
      obtain ⟨a, ha, b, hb, hab⟩ := hvJ
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hb
      have hv_eq : v = a + t * c := by rw [← hab, ← hc]
      have hv_comp : MvPolynomial.homogeneousComponent (u+1) v = v := by
        have := MvPolynomial.homogeneousComponent_of_mem (m := u+1) hv
        simpa using this
      have htc : MvPolynomial.homogeneousComponent (u+1) (t * c)
          = t * MvPolynomial.homogeneousComponent u c := by
        rw [mul_comm t c, Commons.Algebra.MvPolynomial.homogeneousComponent_mul_of_isHomogeneous_right
          (MvPolynomial.isHomogeneous_X k i) c u, mul_comm]
      have hveq2 : v = MvPolynomial.homogeneousComponent (u+1) a
          + t * MvPolynomial.homogeneousComponent u c := by
        have := congrArg (MvPolynomial.homogeneousComponent (u+1)) hv_eq
        rw [map_add, htc, hv_comp] at this
        exact this
      have hcu_mem : MvPolynomial.homogeneousComponent u c ∈ V u := by
        rw [MvPolynomial.mem_homogeneousSubmodule]
        exact MvPolynomial.homogeneousComponent_isHomogeneous u c
      have hdiff : t * MvPolynomial.homogeneousComponent u c - v ∈ p := by
        have : t * MvPolynomial.homogeneousComponent u c - v
            = -(MvPolynomial.homogeneousComponent (u+1) a) := by
          rw [hveq2]; ring
        rw [this]
        exact p.neg_mem (hp a ha (u+1))
      have hEq : (p.mkQ.restrictScalars k) (t * MvPolynomial.homogeneousComponent u c)
          = (p.mkQ.restrictScalars k) v := by
        rw [← sub_eq_zero, ← map_sub]
        simp only [LinearMap.restrictScalars_apply, Submodule.mkQ_apply]
        rw [Ideal.Quotient.mk_eq_mk]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hdiff
      rw [LinearMap.mem_range]
      refine ⟨⟨(p.mkQ.restrictScalars k) (MvPolynomial.homogeneousComponent u c),
        Submodule.mem_map.mpr ⟨MvPolynomial.homogeneousComponent u c, hcu_mem, rfl⟩⟩, ?_⟩
      apply Subtype.ext
      rw [hf_apply, hmσ_π, hEq, hvx]
    · intro hx
      rw [LinearMap.mem_range] at hx
      obtain ⟨y, rfl⟩ := hx
      rw [LinearMap.mem_ker]
      obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.mp y.property
      show σ (mσ ↑y) = 0
      rw [← hwv, hmσ_π w, hσ]
      simp only [LinearMap.restrictScalars_apply, Submodule.mkQ_apply]
      rw [Ideal.Quotient.mk_eq_mk]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_sup_right (Ideal.mul_mem_right w (Ideal.span {t})
          (Ideal.mem_span_singleton_self t)))
  haveI hfinA : Module.Finite k ↥(A (u+1)) :=
    Module.Finite.of_fg (Submodule.FG.map _ (MvPolynomial.homogeneousSubmodule_fg (Fin m) k (u+1)))
  have hrank := LinearMap.finrank_range_add_finrank_ker g
  rw [hg_range, hg_ker] at hrank
  have hfr : Module.finrank k ↥(f.range) = Module.finrank k ↥(A u) :=
    LinearMap.finrank_range_of_inj hf_inj
  rw [hfr] at hrank
  omega

private theorem hilbertFun_eq_sum_hilbertFun_sup_span_X {k : Type*} [Field k] {m : ℕ}
    (p : Ideal (MvPolynomial (Fin m) k)) [p.IsPrime]
    (hp : ∀ x ∈ p, ∀ j, MvPolynomial.homogeneousComponent j x ∈ p)
    {i : Fin m} (hf : MvPolynomial.X i ∉ p)
    (hK : p ⊔ Ideal.span {MvPolynomial.X i} ≠ ⊤) (u : ℕ) :
    Commons.RingTheory.Ideal.Hilbert.hilbertFun p
        (MvPolynomial.homogeneousSubmodule (Fin m) k u)
      = ∑ j ∈ Finset.range (u + 1),
          Commons.RingTheory.Ideal.Hilbert.hilbertFun (p ⊔ Ideal.span {MvPolynomial.X i})
            (MvPolynomial.homogeneousSubmodule (Fin m) k j) := by
  induction u with
  | zero =>
      rw [Finset.sum_range_one]
      rw [hilbertFun_homogeneousSubmodule_zero p (show p ≠ ⊤ from (inferInstance : p.IsPrime).ne_top),
        hilbertFun_homogeneousSubmodule_zero (p ⊔ Ideal.span {MvPolynomial.X i}) hK]
  | succ u ih =>
      rw [Finset.sum_range_succ, ← ih]
      exact hilbertFun_succ p hp hf u

end Commons.RingTheory.Ideal.Hilbert

end


-- ==== from Submission.Commons.RingTheory.KrullDimension.exists_minimalPrime_ringKrullDim_quotient_eq ====
section

namespace Commons.RingTheory.KrullDimension

/-- For any commutative ring `A` of Krull dimension `d`, there is a minimal prime `p` of `A`
such that the quotient `A ⧸ p` again has Krull dimension `d`. -/
private theorem exists_minimalPrimes_ringKrullDim_eq {A : Type*} [CommRing A]
    {d : ℕ} (hd : ringKrullDim A = (d : WithBot ℕ∞)) :
    ∃ p ∈ minimalPrimes A, ringKrullDim (A ⧸ p) = (d : WithBot ℕ∞) := by
  -- A strict chain of `d + 1` primes of `A`.
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp (le_of_eq hd.symm)
  -- Extend the chain downwards to a minimal prime `q` below its head.
  obtain ⟨q, hqmem, hqle⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := l.head.asIdeal) bot_le
  -- Every prime of the chain lies above `q`, so the chain sits in `zeroLocus q`.
  have hmem : ∀ i, (l i) ∈ PrimeSpectrum.zeroLocus (R := A) q := by
    intro i
    rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
    exact le_trans hqle (by simpa using LTSeries.head_le l i)
  -- Push the chain into the closed set `zeroLocus q`.
  let l' : LTSeries (PrimeSpectrum.zeroLocus (R := A) q) :=
    LTSeries.mk l.length (fun i => ⟨l i, hmem i⟩) (fun i j hij => by
      rw [Subtype.mk_lt_mk]; exact l.strictMono hij)
  have hlow : (d : WithBot ℕ∞) ≤ Order.krullDim (PrimeSpectrum.zeroLocus (R := A) q) := by
    rw [← hl]
    exact Order.le_krullDim_iff.mpr ⟨l', rfl⟩
  have hqdim_le : ringKrullDim (A ⧸ q) ≤ (d : WithBot ℕ∞) := by
    rw [← hd]; exact ringKrullDim_quotient_le q
  have hqdim_ge : (d : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ q) := by
    rw [ringKrullDim_quotient q]; exact hlow
  exact ⟨q, hqmem, le_antisymm hqdim_le hqdim_ge⟩

private theorem exists_minimalPrime_ringKrullDim_quotient_eq {R : Type*} [CommRing R]
    (q : Ideal R) (d : ℕ) (hd : ringKrullDim (R ⧸ q) = (d : WithBot ℕ∞)) :
    ∃ p ∈ q.minimalPrimes, ringKrullDim (R ⧸ p) = (d : WithBot ℕ∞) := by
  obtain ⟨p', hp'mem, hp'dim⟩ :=
    exists_minimalPrimes_ringKrullDim_eq (A := R ⧸ q) hd
  refine ⟨p'.comap (Ideal.Quotient.mk q), ?_, ?_⟩
  · rw [Ideal.minimalPrimes_eq_comap]
    exact ⟨p', hp'mem, rfl⟩
  · have hqp : q ≤ p'.comap (Ideal.Quotient.mk q) := by
      intro x hx
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact p'.zero_mem
    have hmap : (p'.comap (Ideal.Quotient.mk q)).map (Ideal.Quotient.mk q) = p' :=
      Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective p'
    have he : ((R ⧸ q) ⧸ p') ≃+* (R ⧸ p'.comap (Ideal.Quotient.mk q)) :=
      (Ideal.quotEquivOfEq hmap).symm.trans (DoubleQuot.quotQuotEquivQuotOfLE hqp)
    rw [← RingEquiv.ringKrullDim he]
    exact hp'dim

end Commons.RingTheory.KrullDimension
end


-- ==== from Submission.Commons.Algebra.BigOperators.sum_Icc_pow_lower_bound ====
section

open scoped BigOperators

namespace Commons.Algebra.BigOperators

open Finset

/-- Telescoping identity over an integer interval:
`∑_{j=M}^{t} (f (j+1) - f j) = f (t+1) - f M` for `M ≤ t`. -/
private lemma sum_Icc_shift_sub {G : Type*} [AddCommGroup G] (M t : ℕ) (h : M ≤ t) (f : ℕ → G) :
    ∑ j ∈ Finset.Icc M t, (f (j + 1) - f j) = f (t + 1) - f M := by
  rw [← Finset.Ico_add_one_right_eq_Icc M t]
  rw [Finset.sum_Ico_eq_sub _ (show M ≤ t + 1 by omega)]
  rw [Finset.sum_range_sub, Finset.sum_range_sub]
  abel

/-- For `0 ≤ a`, `(a+1)^(k+1) - a^(k+1) ≤ (k+1) (a+1)^k`. -/
private lemma pow_succ_sub_pow_le (a : ℚ) (ha : 0 ≤ a) (k : ℕ) :
    (a + 1) ^ (k + 1) - a ^ (k + 1) ≤ (k + 1 : ℚ) * (a + 1) ^ k := by
  have hx : a ≤ a + 1 := by linarith
  have hpow : ∀ i, (k + 1) - 1 - i = k - i := fun i => by omega
  have hval : (a + 1) ^ (k + 1) - a ^ (k + 1)
      = ∑ i ∈ Finset.range (k + 1), (a + 1) ^ i * a ^ (k - i) := by
    have h := geom_sum₂_mul (a + 1) a (k + 1)
    rw [show (a + 1) - a = 1 by ring, mul_one] at h
    simpa [hpow] using h.symm
  rw [hval]
  calc ∑ i ∈ Finset.range (k + 1), (a + 1) ^ i * a ^ (k - i)
      ≤ ∑ _i ∈ Finset.range (k + 1), (a + 1) ^ k := by
        apply Finset.sum_le_sum
        intro i hi
        have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have h1 : a ^ (k - i) ≤ (a + 1) ^ (k - i) := pow_le_pow_left₀ ha hx (k - i)
        calc (a + 1) ^ i * a ^ (k - i)
            ≤ (a + 1) ^ i * (a + 1) ^ (k - i) :=
              mul_le_mul_of_nonneg_left h1 (pow_nonneg (by linarith) i)
          _ = (a + 1) ^ k := by rw [← pow_add, Nat.add_sub_cancel' hik]
    _ = (k + 1 : ℚ) * (a + 1) ^ k := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- The termwise lower bound used in the telescoping estimate. -/
private lemma le_pow_diff_div (a : ℚ) (ha : 0 ≤ a) (k : ℕ) :
    ((a + 1) ^ (k + 1) - a ^ (k + 1)) / (k + 1 : ℚ) ≤ (a + 1) ^ k := by
  rw [div_le_iff₀ (by positivity : (0 : ℚ) < (k + 1))]
  calc (a + 1) ^ (k + 1) - a ^ (k + 1) ≤ (k + 1 : ℚ) * (a + 1) ^ k := pow_succ_sub_pow_le a ha k
    _ = (a + 1) ^ k * (k + 1 : ℚ) := by ring

private theorem sum_Icc_pow_lower_bound (k M : ℕ) :
    ∃ c : ℚ, 0 < c ∧ ∃ N : ℕ, ∀ t : ℕ, N ≤ t →
      c * ((t : ℚ) + 1) ^ (k + 1) ≤ ∑ j ∈ Finset.Icc M t, ((j : ℚ) + 1) ^ k := by
  refine ⟨1 / (2 * (k + 1)), ?_, 2 * M + 1, ?_⟩
  · positivity
  · intro t ht
    have hMle : M ≤ t := by omega
    have hterm : ∀ j ∈ Finset.Icc M t,
        (((j : ℚ) + 1) ^ (k + 1) - (j : ℚ) ^ (k + 1)) / (k + 1 : ℚ) ≤ ((j : ℚ) + 1) ^ k :=
      fun j _ => le_pow_diff_div (j : ℚ) (Nat.cast_nonneg j) k
    have htel : ∑ j ∈ Finset.Icc M t, (((j : ℚ) + 1) ^ (k + 1) - (j : ℚ) ^ (k + 1))
        = ((t : ℚ) + 1) ^ (k + 1) - (M : ℚ) ^ (k + 1) := by
      have h := sum_Icc_shift_sub M t hMle (fun j : ℕ => (j : ℚ) ^ (k + 1))
      simpa [Nat.cast_add, Nat.cast_one] using h
    have hbound : (((t : ℚ) + 1) ^ (k + 1) - (M : ℚ) ^ (k + 1)) / (k + 1 : ℚ)
        ≤ ∑ j ∈ Finset.Icc M t, ((j : ℚ) + 1) ^ k := by
      have h := Finset.sum_le_sum hterm
      rw [← Finset.sum_div] at h
      rwa [htel] at h
    have hpow2 : 2 * (M : ℚ) ^ (k + 1) ≤ ((t : ℚ) + 1) ^ (k + 1) := by
      have ha : (2 : ℚ) * (M : ℚ) ≤ (t : ℚ) + 1 := by
        have hcast : ((2 * M + 1 : ℕ) : ℚ) ≤ (t : ℚ) := by exact_mod_cast ht
        push_cast at hcast
        linarith
      have h1 : (2 * (M : ℚ)) ^ (k + 1) ≤ ((t : ℚ) + 1) ^ (k + 1) :=
        pow_le_pow_left₀ (by positivity) ha (k + 1)
      have h2 : 2 * (M : ℚ) ^ (k + 1) ≤ (2 * (M : ℚ)) ^ (k + 1) := by
        rw [mul_pow]
        have hle : (2 : ℚ) ≤ 2 ^ (k + 1) := by
          calc (2 : ℚ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        exact mul_le_mul_of_nonneg_right hle (pow_nonneg (Nat.cast_nonneg M) (k + 1))
      linarith
    have hfinal : 1 / (2 * (k + 1)) * ((t : ℚ) + 1) ^ (k + 1)
        ≤ (((t : ℚ) + 1) ^ (k + 1) - (M : ℚ) ^ (k + 1)) / (k + 1 : ℚ) := by
      rw [le_div_iff₀ (by positivity : (0 : ℚ) < (k + 1))]
      have h1 : (1 / (2 * (k + 1)) : ℚ) * (k + 1) = 1 / 2 := by
        have hk : (k + 1 : ℚ) ≠ 0 := by positivity
        field_simp
      calc (1 / (2 * (k + 1)) : ℚ) * ((t : ℚ) + 1) ^ (k + 1) * (k + 1)
          = ((1 / (2 * (k + 1)) : ℚ) * (k + 1)) * ((t : ℚ) + 1) ^ (k + 1) := by ring
        _ = (1 / 2) * ((t : ℚ) + 1) ^ (k + 1) := by rw [h1]
        _ = ((t : ℚ) + 1) ^ (k + 1) / 2 := by ring
        _ ≤ ((t : ℚ) + 1) ^ (k + 1) - (M : ℚ) ^ (k + 1) := by linarith
    linarith [hfinal, hbound]

end Commons.Algebra.BigOperators

end


-- ==== from Submission.Commons.RingTheory.Ideal.Hilbert.hilbert_sum_lower_bound ====
section

namespace Commons.RingTheory.Ideal.Hilbert
open MvPolynomial

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

attribute [local instance] MvPolynomial.gradedAlgebra

private lemma hilbertFun_zero {k : Type*} [Field k] {m : ℕ} (q : Ideal (MvPolynomial (Fin m) k))
    (hq : q ≠ ⊤) :
    hilbertFun q (MvPolynomial.homogeneousSubmodule (Fin m) k 0) = 1 := by
  haveI hfin : Module.Finite k ↥(MvPolynomial.homogeneousSubmodule (Fin m) k 0) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin m) k 0)
  rw [hilbertFun_eq_sub]
  have hfinrank : Module.finrank k ↥(MvPolynomial.homogeneousSubmodule (Fin m) k 0) = 1 := by
    rw [Commons.Algebra.MvPolynomial.finrank_homogeneousSubmodule_eq_choose]
    simp
  have hinter : (MvPolynomial.homogeneousSubmodule (Fin m) k 0 ⊓ q.restrictScalars k) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [Submodule.mem_inf] at hx
    obtain ⟨hxV, hxq⟩ := hx
    have h1 : MvPolynomial.homogeneousComponent 0 x = x :=
      MvPolynomial.homogeneousComponent_eq_self
        ((MvPolynomial.mem_homogeneousSubmodule 0 x).mp hxV)
    have h2 : MvPolynomial.homogeneousComponent 0 x = MvPolynomial.C (MvPolynomial.coeff 0 x) :=
      MvPolynomial.homogeneousComponent_zero x
    have hxC : x = MvPolynomial.C (MvPolynomial.coeff 0 x) := h1.symm.trans h2
    have hxq' : MvPolynomial.C (MvPolynomial.coeff 0 x) ∈ q := hxC ▸ hxq
    by_contra hc
    have hc0 : MvPolynomial.coeff 0 x ≠ 0 := by
      intro h; exact hc (by rw [hxC, h, MvPolynomial.C_0])
    have h1' : (1 : MvPolynomial (Fin m) k) ∈ q := by
      have hm := q.mul_mem_left (MvPolynomial.C (MvPolynomial.coeff 0 x)⁻¹) hxq'
      rwa [← MvPolynomial.C_mul, inv_mul_cancel₀ hc0, MvPolynomial.C_1] at hm
    exact hq ((Ideal.eq_top_iff_one q).mpr h1')
  rw [hfinrank, hinter]
  simp

private theorem lower_bound_aux {k : Type*} [Field k] {m : ℕ} (d : ℕ) :
    ∀ (q : Ideal (MvPolynomial (Fin m) k))
      (hq : ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q),
      ringKrullDim (MvPolynomial (Fin m) k ⧸ q) = (d : WithBot ℕ∞) →
      ∃ c : ℚ, 0 < c ∧ ∃ N : ℕ, ∀ t : ℕ, N ≤ t →
        c * ((t : ℚ) + 1) ^ d ≤ ((∑ u ∈ Finset.range (t + 1), hilbertFun q
          (MvPolynomial.homogeneousSubmodule (Fin m) k u)) : ℚ) := by
  induction d with
  | zero =>
      intro q hq hd
      have hqne : q ≠ ⊤ := by
        intro hqt
        haveI : Subsingleton (MvPolynomial (Fin m) k ⧸ q) :=
          Ideal.Quotient.subsingleton_iff.mpr hqt
        rw [ringKrullDim_eq_bot_of_subsingleton] at hd
        exact WithBot.bot_ne_coe hd
      refine ⟨1, one_pos, 0, fun t _ => ?_⟩
      have h0 : hilbertFun q (MvPolynomial.homogeneousSubmodule (Fin m) k 0) = 1 :=
        hilbertFun_zero q hqne
      have hmem : (0 : ℕ) ∈ Finset.range (t + 1) := Finset.mem_range.mpr (Nat.succ_pos t)
      have hle : hilbertFun q (MvPolynomial.homogeneousSubmodule (Fin m) k 0)
          ≤ ∑ u ∈ Finset.range (t + 1), hilbertFun q
              (MvPolynomial.homogeneousSubmodule (Fin m) k u) :=
        Finset.single_le_sum (f := fun u => hilbertFun q
            (MvPolynomial.homogeneousSubmodule (Fin m) k u)) (fun _ _ => Nat.zero_le _) hmem
      rw [h0] at hle
      have : (1 : ℚ) ≤ ((∑ u ∈ Finset.range (t + 1), hilbertFun q
          (MvPolynomial.homogeneousSubmodule (Fin m) k u)) : ℚ) := by exact_mod_cast hle
      simpa using this
  | succ n ih =>
      intro q hq hd
      obtain ⟨p, hpmem, hpd⟩ := Commons.RingTheory.KrullDimension.exists_minimalPrime_ringKrullDim_quotient_eq q (n + 1) hd
      haveI hpIsPrime : p.IsPrime := hpmem.1.1
      have hqle : q ≤ p := hpmem.1.2
      have hphom := minimalPrimes_homogeneousComponent_mem hq hpmem
      have hple := minimalPrimes_le_idealOfVars q hq hpmem
      have hex : ∃ i : Fin m, MvPolynomial.X i ∉ p := by
        by_contra hcon
        push Not at hcon
        have hle : MvPolynomial.idealOfVars (Fin m) k ≤ p := by
          rw [MvPolynomial.idealOfVars]
          refine Ideal.span_le.mpr (fun x hx => ?_)
          rw [Set.mem_range] at hx
          obtain ⟨i, rfl⟩ := hx
          exact hcon i
        have hle0 := ringKrullDim_le_zero_of_minimalPrimes_idealOfVars_le hq hpmem hle
        rw [hd] at hle0
        have hgt : ((0 : ℕ) : WithBot ℕ∞) < ((n + 1 : ℕ) : WithBot ℕ∞) := by
          exact_mod_cast Nat.succ_pos n
        exact (not_le_of_gt hgt) hle0
      obtain ⟨i, hi⟩ := hex
      have hf0 : (MvPolynomial.X i : MvPolynomial (Fin m) k) ≠ 0 := MvPolynomial.X_ne_zero (R := k) i
      have hproper : p ⊔ Ideal.span {MvPolynomial.X i} ≠ ⊤ := by
        intro htop
        have hle : p ⊔ Ideal.span {MvPolynomial.X i} ≤ MvPolynomial.idealOfVars (Fin m) k := by
          refine sup_le hple ?_
          rw [Ideal.span_le]
          rintro x hx
          rw [Set.mem_singleton_iff] at hx
          rw [hx, MvPolynomial.idealOfVars]
          exact Ideal.subset_span ⟨i, rfl⟩
        exact idealOfVars_ne_top (top_le_iff.mp (htop ▸ hle))
      obtain ⟨d', hd'p, hd'ne, hd'K⟩ :=
        dim_quotient_sup_span_eq_dim_sub_one p hphom hi hf0 hproper
      have hd'eq : d' = n + 1 := by
        have h1 : ((d' : ℕ) : ℕ∞) = ((n + 1 : ℕ) : ℕ∞) :=
          (WithBot.coe_inj (α := ℕ∞)).mp (hd'p.symm.trans hpd)
        exact WithTop.coe_inj.mp h1
      have hphomI : Ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin m) k) p := by
        rw [Ideal.IsHomogeneous.iff_eq]
        refine le_antisymm (Ideal.toIdeal_homogeneousCore_le _ p) ?_
        intro y hy
        rw [← MvPolynomial.sum_homogeneousComponent y]
        refine Ideal.sum_mem _ fun j _ => ?_
        exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem
          ⟨j, MvPolynomial.homogeneousComponent_mem j y⟩ (hphom y hy j)
      have hKhom : ∀ x ∈ p ⊔ Ideal.span {MvPolynomial.X i}, ∀ j,
          MvPolynomial.homogeneousComponent j x ∈ p ⊔ Ideal.span {MvPolynomial.X i} := by
        have hsup : Ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin m) k)
            (p ⊔ Ideal.span {MvPolynomial.X i}) :=
          hphomI.sup (homogeneous_span_singleton (MvPolynomial.isHomogeneous_X k i))
        intro x hx j
        exact (MvPolynomial.mem_iff_homogeneousComponent_mem hsup x).mp hx j
      have hdimK : ringKrullDim (MvPolynomial (Fin m) k ⧸ (p ⊔ Ideal.span {MvPolynomial.X i}))
          = (n : WithBot ℕ∞) := by
        rw [hd'K, hd'eq]
        congr 1
      obtain ⟨c', hc'pos, N', hN'⟩ := ih _ hKhom hdimK
      obtain ⟨c'', hc''pos, N'', hN''⟩ :=
        Commons.Algebra.BigOperators.sum_Icc_pow_lower_bound n N'
      refine ⟨c' * c'', mul_pos hc'pos hc''pos, max (max N' N'') 1, fun t ht => ?_⟩
      haveI hfin : ∀ s : ℕ, Module.Finite k ↥(MvPolynomial.homogeneousSubmodule (Fin m) k s) :=
        fun s => Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin m) k s)
      have htN' : N' ≤ t := le_trans (le_trans (le_max_left N' N'') (le_max_left (max N' N'') 1)) ht
      have htN'' : N'' ≤ t := le_trans (le_trans (le_max_right N' N'') (le_max_left (max N' N'') 1)) ht
      have hbez : ∀ u, hilbertFun p (MvPolynomial.homogeneousSubmodule (Fin m) k u)
          = ∑ j ∈ Finset.range (u + 1), hilbertFun (p ⊔ Ideal.span {MvPolynomial.X i})
              (MvPolynomial.homogeneousSubmodule (Fin m) k j) :=
        fun u => hilbertFun_eq_sum_hilbertFun_sup_span_X p hphom hi hproper u
      have hs1 : ∑ u ∈ Finset.range (t + 1), hilbertFun p (MvPolynomial.homogeneousSubmodule (Fin m) k u)
          ≤ ∑ u ∈ Finset.range (t + 1), hilbertFun q (MvPolynomial.homogeneousSubmodule (Fin m) k u) :=
        Finset.sum_le_sum (fun u _ => hilbertFun_anti hqle _)
      have hsub : Finset.Icc N' t ⊆ Finset.range (t + 1) := by
        intro u hu
        rw [Finset.mem_Icc] at hu
        rw [Finset.mem_range]
        omega
      have hsq_icc : ∑ u ∈ Finset.Icc N' t, hilbertFun p (MvPolynomial.homogeneousSubmodule (Fin m) k u)
          ≤ ∑ u ∈ Finset.range (t + 1), hilbertFun p (MvPolynomial.homogeneousSubmodule (Fin m) k u) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun u _ _ => Nat.zero_le _)
      have hterm : ∀ u ∈ Finset.Icc N' t,
          c' * ((u : ℚ) + 1) ^ n ≤ (hilbertFun p (MvPolynomial.homogeneousSubmodule (Fin m) k u) : ℚ) := by
        intro u hu
        rw [Finset.mem_Icc] at hu
        have h := hN' u hu.1
        have hcast : (∑ j ∈ Finset.range (u + 1), (hilbertFun (p ⊔ Ideal.span {MvPolynomial.X i})
            (MvPolynomial.homogeneousSubmodule (Fin m) k j) : ℚ))
            = (hilbertFun p (MvPolynomial.homogeneousSubmodule (Fin m) k u) : ℚ) := by
          rw [← Nat.cast_sum, ← hbez u]
        rw [hcast] at h
        exact h
      have hL4 := hN'' t htN''
      have hmul : c' * (c'' * ((t : ℚ) + 1) ^ (n + 1))
          ≤ c' * ∑ j ∈ Finset.Icc N' t, ((j : ℚ) + 1) ^ n :=
        mul_le_mul_of_nonneg_left hL4 hc'pos.le
      have hsum1 : ∑ u ∈ Finset.Icc N' t, c' * ((u : ℚ) + 1) ^ n
          ≤ ∑ u ∈ Finset.Icc N' t, (hilbertFun p (MvPolynomial.homogeneousSubmodule (Fin m) k u) : ℚ) :=
        Finset.sum_le_sum hterm
      have hfac : ∑ u ∈ Finset.Icc N' t, c' * ((u : ℚ) + 1) ^ n
          = c' * ∑ u ∈ Finset.Icc N' t, ((u : ℚ) + 1) ^ n := by
        rw [Finset.mul_sum]
      have hcast : ∑ u ∈ Finset.Icc N' t, (hilbertFun p (MvPolynomial.homogeneousSubmodule (Fin m) k u) : ℚ)
          = ((∑ u ∈ Finset.Icc N' t, hilbertFun p (MvPolynomial.homogeneousSubmodule (Fin m) k u) : ℕ) : ℚ) := by
        rw [Nat.cast_sum]
      have hchain1 : c' * c'' * ((t : ℚ) + 1) ^ (n + 1)
          ≤ ((∑ u ∈ Finset.Icc N' t, hilbertFun p (MvPolynomial.homogeneousSubmodule (Fin m) k u) : ℕ) : ℚ) := by
        calc c' * c'' * ((t : ℚ) + 1) ^ (n + 1)
            = c' * (c'' * ((t : ℚ) + 1) ^ (n + 1)) := by ring
          _ ≤ c' * ∑ j ∈ Finset.Icc N' t, ((j : ℚ) + 1) ^ n := hmul
          _ = ∑ u ∈ Finset.Icc N' t, c' * ((u : ℚ) + 1) ^ n := hfac.symm
          _ ≤ ∑ u ∈ Finset.Icc N' t, (hilbertFun p (MvPolynomial.homogeneousSubmodule (Fin m) k u) : ℚ) := hsum1
          _ = ((∑ u ∈ Finset.Icc N' t, hilbertFun p (MvPolynomial.homogeneousSubmodule (Fin m) k u) : ℕ) : ℚ) := hcast
      have hnat : (∑ u ∈ Finset.Icc N' t, hilbertFun p (MvPolynomial.homogeneousSubmodule (Fin m) k u))
          ≤ ∑ u ∈ Finset.range (t + 1), hilbertFun q (MvPolynomial.homogeneousSubmodule (Fin m) k u) :=
        le_trans hsq_icc hs1
      have hcast2 : ((∑ u ∈ Finset.Icc N' t, hilbertFun p (MvPolynomial.homogeneousSubmodule (Fin m) k u) : ℕ) : ℚ)
          ≤ ((∑ u ∈ Finset.range (t + 1), hilbertFun q (MvPolynomial.homogeneousSubmodule (Fin m) k u)) : ℚ) := by
        exact_mod_cast hnat
      exact le_trans hchain1 hcast2

private theorem hilbert_sum_lower_bound {k : Type*} [Field k] {m : ℕ}
    (q : Ideal (MvPolynomial (Fin m) k))
    (hq : ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q)
    (d : ℕ) (hd : ringKrullDim (MvPolynomial (Fin m) k ⧸ q) = (d : WithBot ℕ∞)) :
    ∃ c : ℚ, 0 < c ∧ ∃ N : ℕ, ∀ t : ℕ, N ≤ t →
      c * ((t : ℚ) + 1) ^ d ≤ ((∑ u ∈ Finset.range (t + 1), Module.finrank k
        (Submodule.map (q.mkQ.restrictScalars k)
          (MvPolynomial.homogeneousSubmodule (Fin m) k u))) : ℚ) := by
  simpa only [hilbertFun] using lower_bound_aux d q hq hd

end Commons.RingTheory.Ideal.Hilbert

/-!
# Lower bound for the partial sums of the Hilbert function of a homogeneous quotient

For a homogeneous ideal `q` of `k[X₁,…,Xₘ]` with `ringKrullDim (R ⧸ q) = d`, the partial sums
of the Hilbert function grow at least like `C (t+1)^d`.

We prove this by induction on `d`.  A minimal prime `p` of `q` with `dim (R ⧸ p) = d` gives
the reduction to the domain (prime) case.  In the prime case, choosing `Xᵢ ∉ p` produces an
exact relation `HilbertFun p t = ∑_{j ≤ t} HilbertFun (p + (Xᵢ)) j`, so the induction applied
to `p + (Xᵢ)` (whose dimension is `d - 1`) together with the elementary lower bound
`∑_{j=M}^t (j+1)^{d-1} ≥ c (t+1)^d` gives the result.
-/

end


-- ==== from Submission.Commons.RingTheory.Ideal.Hilbert.natDegree_hilbertPoly_eq_dim_sub_one ====
section

namespace Commons.RingTheory.Ideal.Hilbert

open MvPolynomial Polynomial

variable {k : Type*} [Field k] {m : ℕ}

/-! ## The degree of the partial sums of a polynomial -/

private lemma natDegree_bernoulli_eq (n : ℕ) : (Polynomial.bernoulli n).natDegree = n := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · rw [Polynomial.bernoulli]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    simp only [Finset.mem_range] at hi
    exact (Polynomial.natDegree_monomial_le (m := n - i) _).trans (by omega)
  · rw [Polynomial.coeff_bernoulli, if_pos (Nat.le_refl _), Nat.sub_self, _root_.bernoulli_zero,
      one_mul, Nat.choose_self]
    norm_num

private lemma coeff_powSumPoly (n : ℕ) :
    (Commons.Algebra.Polynomial.EventuallyPoly.powSumPoly n).coeff (n + 1)
      = ((n + 1 : ℕ) : ℚ)⁻¹ := by
  rw [Commons.Algebra.Polynomial.EventuallyPoly.powSumPoly, Polynomial.coeff_mul_C,
    Polynomial.coeff_sub, Polynomial.coeff_C]
  have h1 : ¬ ((n + 1) = 0) := by omega
  rw [if_neg h1, sub_zero]
  rw [Polynomial.coeff_bernoulli, if_pos (Nat.le_refl _), Nat.sub_self, _root_.bernoulli_zero,
    one_mul, Nat.choose_self, Nat.cast_one]
  ring

private lemma natDegree_powSumPoly (n : ℕ) :
    (Commons.Algebra.Polynomial.EventuallyPoly.powSumPoly n).natDegree = n + 1 := by
  rw [Commons.Algebra.Polynomial.EventuallyPoly.powSumPoly]
  have hb : (Polynomial.bernoulli (n + 1)).natDegree = n + 1 := natDegree_bernoulli_eq _
  have h1 : (Polynomial.bernoulli (n + 1) - Polynomial.C (_root_.bernoulli (n + 1))).natDegree
      = n + 1 := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
    · exact hb
    · rw [Polynomial.natDegree_C, hb]; omega
  rw [Polynomial.natDegree_mul_C (inv_ne_zero (by positivity)), h1]

private lemma natDegree_sumPoly {P : Polynomial ℚ} (hP : P ≠ 0) :
    (Commons.Algebra.Polynomial.EventuallyPoly.sumPoly P).natDegree = P.natDegree + 1 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · rw [Commons.Algebra.Polynomial.EventuallyPoly.sumPoly]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    refine le_trans (Polynomial.natDegree_mul_le) ?_
    rw [Polynomial.natDegree_C, natDegree_powSumPoly]
    simp only [Finset.mem_range] at hi
    omega
  · rw [Commons.Algebra.Polynomial.EventuallyPoly.sumPoly, Polynomial.finsetSum_coeff,
      Finset.sum_eq_single P.natDegree]
    · rw [Polynomial.coeff_C_mul, coeff_powSumPoly, mul_comm]
      exact mul_ne_zero (inv_ne_zero (by positivity)) (Polynomial.leadingCoeff_ne_zero.mpr hP)
    · intro i hi hne
      have hdeg : (Commons.Algebra.Polynomial.EventuallyPoly.powSumPoly i).natDegree
          < P.natDegree + 1 := by
        rw [natDegree_powSumPoly]
        simp only [Finset.mem_range] at hi
        omega
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_eq_zero_of_natDegree_lt hdeg, mul_zero]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) h

/-- The partial sums of a nonzero polynomial of degree `k` form a polynomial of degree `k + 1`. -/
private theorem exists_partialSumPoly_natDegree {P : Polynomial ℚ} (hP : P ≠ 0) :
    ∃ Q : Polynomial ℚ, Q.natDegree = P.natDegree + 1 ∧ ∀ t : ℕ,
      (∑ u ∈ Finset.range (t + 1), P.eval (u : ℚ)) = Q.eval (t : ℚ) := by
  refine ⟨(Commons.Algebra.Polynomial.EventuallyPoly.sumPoly P).comp
    (Polynomial.X + Polynomial.C 1), ?_, ?_⟩
  · rw [Polynomial.natDegree_comp, natDegree_sumPoly hP, Polynomial.natDegree_X_add_C]
    ring
  · intro t
    rw [Polynomial.eval_comp]
    rw [show (Polynomial.eval (t:ℚ) (Polynomial.X + Polynomial.C (1:ℚ)))
        = ((t + 1 : ℕ) : ℚ) from by
      rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]; push_cast; ring]
    rw [Commons.Algebra.Polynomial.EventuallyPoly.sumPoly_eval]

/-! ## The main theorem -/

private theorem natDegree_hilbertPoly_eq_dim_sub_one {k : Type*} [Field k] {m : ℕ}
    (q : Ideal (MvPolynomial (Fin m) k)) [q.IsPrime]
    (hq : ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q)
    (P : Polynomial ℚ)
    (hP : ∃ N, ∀ t ≥ N, (Module.finrank k (Submodule.map (q.mkQ.restrictScalars k)
        (MvPolynomial.homogeneousSubmodule (Fin m) k t)) : ℚ) = P.eval (t : ℚ))
    (hP0 : P ≠ 0) :
    ∃ d : ℕ, ringKrullDim (MvPolynomial (Fin m) k ⧸ q) = (d : WithBot ℕ∞) ∧ d = P.natDegree + 1 := by
  classical
  haveI : Nontrivial (MvPolynomial (Fin m) k ⧸ q) :=
    Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsPrime.ne_top ‹q.IsPrime›)
  have hd_ne_bot : ringKrullDim (MvPolynomial (Fin m) k ⧸ q) ≠ ⊥ := by
    have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin m) k ⧸ q)
    intro h; rw [h] at h0
    exact not_le_of_gt (WithBot.bot_lt_coe (0 : ℕ∞)) h0
  have hd_ne_top : ringKrullDim (MvPolynomial (Fin m) k ⧸ q) ≠ ⊤ := by
    have hle : ringKrullDim (MvPolynomial (Fin m) k ⧸ q) ≤ ringKrullDim (MvPolynomial (Fin m) k) :=
      ringKrullDim_quotient_le q
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
      Nat.card_eq_fintype_card, Fintype.card_fin] at hle
    intro h
    rw [h] at hle
    exact (fun hh => ENat.natCast_ne_top m (WithBot.coe_injective hh)) (le_antisymm le_top hle)
  obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp hd_ne_bot
  have ha_top : a ≠ ⊤ := by intro h; exact hd_ne_top (by rw [← ha, h]; rfl)
  obtain ⟨d, hd'⟩ := ENat.ne_top_iff_exists.mp ha_top
  have hdd : ringKrullDim (MvPolynomial (Fin m) k ⧸ q) = (d : WithBot ℕ∞) := by
    rw [← ha, ← hd']; rfl
  obtain ⟨C, hC'⟩ := hilbert_sum_upper_bound q hq d hdd
  obtain ⟨Q, hQdeg, hQ⟩ := exists_partialSumPoly_natDegree hP0
  obtain ⟨N0, hN0'⟩ := hP
  -- The Hilbert function of the quotient, as a `ℚ`-valued function.
  let f : ℕ → ℚ := fun u => (Module.finrank k (Submodule.map (q.mkQ.restrictScalars k)
    (MvPolynomial.homogeneousSubmodule (Fin m) k u)) : ℚ)
  have hcastsum : ∀ t, (∑ u ∈ Finset.range (t+1), f u)
      = ((∑ u ∈ Finset.range (t+1), Module.finrank k (Submodule.map (q.mkQ.restrictScalars k)
          (MvPolynomial.homogeneousSubmodule (Fin m) k u)) : ℕ) : ℚ) := by
    intro t; simp only [f, Nat.cast_sum]
  have hfN0 : ∀ u ≥ N0, f u = P.eval (u : ℚ) := by
    intro u hu; simpa only [f] using hN0' u hu
  have hFbound : ∀ t, (∑ u ∈ Finset.range (t+1), f u) ≤ (C : ℚ) * ((t : ℚ) + 1) ^ d := by
    intro t
    rw [hcastsum t]
    have h1 : ((∑ u ∈ Finset.range (t+1), Module.finrank k (Submodule.map (q.mkQ.restrictScalars k)
        (MvPolynomial.homogeneousSubmodule (Fin m) k u)) : ℕ) : ℚ)
        ≤ ((C * (t+1)^d : ℕ) : ℚ) := by
      exact_mod_cast hC' t
    push_cast at h1
    simpa using h1
  set K : ℚ := (∑ u ∈ Finset.range N0, f u) - ∑ u ∈ Finset.range N0, P.eval (u : ℚ) with hK
  have hQF : ∀ t ≥ N0, (∑ u ∈ Finset.range (t+1), f u) = Q.eval (t : ℚ) + K := by
    intro t ht
    have htn : N0 + (t + 1 - N0) = t + 1 := by omega
    have hsplit : (∑ u ∈ Finset.range (t+1), f u)
        = (∑ u ∈ Finset.range N0, f u) + ∑ j ∈ Finset.range (t + 1 - N0), f (N0 + j) := by
      conv_lhs => rw [← htn]
      rw [Finset.sum_range_add]
    have hsubst : ∑ j ∈ Finset.range (t + 1 - N0), f (N0 + j)
        = ∑ j ∈ Finset.range (t + 1 - N0), P.eval ((N0 + j : ℕ) : ℚ) :=
      Finset.sum_congr rfl (fun j hj => by
        simp only [Finset.mem_range] at hj
        exact hfN0 (N0 + j) (by omega))
    have hPS : (∑ u ∈ Finset.range (t+1), P.eval (u : ℚ))
        = (∑ u ∈ Finset.range N0, P.eval (u : ℚ))
          + ∑ j ∈ Finset.range (t + 1 - N0), P.eval ((N0 + j : ℕ) : ℚ) := by
      conv_lhs => rw [← htn]
      rw [Finset.sum_range_add]
    have hQ' : Q.eval (t : ℚ) = (∑ u ∈ Finset.range N0, P.eval (u : ℚ))
          + ∑ j ∈ Finset.range (t + 1 - N0), P.eval ((N0 + j : ℕ) : ℚ) := by
      rw [← hQ t, hPS]
    rw [hsplit, hsubst, hQ', hK]
    ring
  -- `natDegree Q ≤ d`
  have hQle : Q.natDegree ≤ d := by
    refine Commons.Algebra.Polynomial.natDegree_le_of_eventually_abs_eval_le
      (C := (C : ℚ) * 2 ^ d + |K|) (N := max N0 1) ?_
    intro t ht
    have htN0 : N0 ≤ t := le_trans (le_max_left _ _) ht
    have ht1 : 1 ≤ t := le_trans (le_max_right _ _) ht
    have ht1' : (1 : ℚ) ≤ (t : ℚ) := by exact_mod_cast ht1
    have hQeq : Q.eval (t : ℚ) = (∑ u ∈ Finset.range (t+1), f u) - K := by
      rw [hQF t htN0]; ring
    have hnonneg : (0 : ℚ) ≤ ∑ u ∈ Finset.range (t+1), f u :=
      Finset.sum_nonneg (fun u _ => by simp only [f]; exact Nat.cast_nonneg _)
    have ht0 : (0 : ℚ) ≤ (t : ℚ) := Nat.cast_nonneg t
    have hpow : ((t : ℚ) + 1) ^ d ≤ 2 ^ d * (t : ℚ) ^ d := by
      calc ((t : ℚ) + 1) ^ d ≤ (2 * (t : ℚ)) ^ d :=
            pow_le_pow_left₀ (by linarith [ht0]) (by linarith [ht1']) d
        _ = 2 ^ d * (t : ℚ) ^ d := by rw [mul_pow]
    have hKle : |K| ≤ |K| * (t : ℚ) ^ d := by
      have h1 : (1 : ℚ) ≤ (t : ℚ) ^ d := one_le_pow₀ ht1'
      nlinarith [abs_nonneg K]
    rw [hQeq]
    calc |(∑ u ∈ Finset.range (t+1), f u) - K|
          ≤ |∑ u ∈ Finset.range (t+1), f u| + |K| := by
            simpa [sub_eq_add_neg] using abs_add_le (∑ u ∈ Finset.range (t+1), f u) (-K)
      _ = (∑ u ∈ Finset.range (t+1), f u) + |K| := by rw [abs_of_nonneg hnonneg]
      _ ≤ (C : ℚ) * 2 ^ d * (t : ℚ) ^ d + |K| * (t : ℚ) ^ d := by
            have h2 : (0 : ℚ) ≤ (C : ℚ) := Nat.cast_nonneg C
            have h3 := mul_le_mul_of_nonneg_left hpow h2
            nlinarith [hFbound t, h3, hKle]
      _ = ((C : ℚ) * 2 ^ d + |K|) * (t : ℚ) ^ d := by ring
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · rw [h0] at hQle; omega
    · exact hpos
  obtain ⟨c, hcpos, Nc, hc'⟩ := hilbert_sum_lower_bound q hq d hdd
  have hc : ∀ t ≥ Nc, c * ((t : ℚ) + 1) ^ d ≤ (∑ u ∈ Finset.range (t+1), f u) := by
    intro t ht
    rw [hcastsum t, Nat.cast_sum]
    exact hc' t ht
  -- `d ≤ natDegree Q`
  have hQge : d ≤ Q.natDegree := by
    refine Commons.Algebra.Polynomial.le_natDegree_of_eventually_le_eval
      (C := c / 2) (N := max (max Nc N0) (Nat.ceil (2 * |K| / c) + 1))
      (div_pos hcpos (by norm_num)) ?_
    intro t ht
    have htNc : Nc ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
    have htN0 : N0 ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht
    have ht1 : 1 ≤ t := by
      have h3 : Nat.ceil (2 * |K| / c) + 1 ≤ t := le_trans (le_max_right _ _) ht
      omega
    have ht1' : (1 : ℚ) ≤ (t : ℚ) := by exact_mod_cast ht1
    have htK : 2 * |K| / c ≤ (t : ℚ) := by
      have h1 : ((Nat.ceil (2 * |K| / c) : ℕ) : ℚ) ≤ (t : ℚ) := by
        have h2 : Nat.ceil (2 * |K| / c) ≤ t := by
          have h3 : Nat.ceil (2 * |K| / c) + 1 ≤ t := le_trans (le_max_right _ _) ht
          omega
        exact_mod_cast h2
      have h3 : 2 * |K| / c ≤ (Nat.ceil (2 * |K| / c) : ℚ) := Nat.le_ceil _
      linarith
    have h1 := hc t htNc
    have h2 := hQF t htN0
    rw [h2] at h1
    have h3 : c * (t : ℚ) ^ d ≤ c * ((t : ℚ) + 1) ^ d := by
      have hb : (t : ℚ) ≤ (t : ℚ) + 1 := by linarith
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Nat.cast_nonneg t) hb d) hcpos.le
    have h5 : |K| ≤ c / 2 * (t : ℚ) := by
      rw [div_le_iff₀ hcpos] at htK
      nlinarith [htK]
    have h6 : (t : ℚ) ≤ (t : ℚ) ^ d := by
      have h7 : (t : ℚ) ^ 1 ≤ (t : ℚ) ^ d := pow_le_pow_right₀ ht1' hd1
      simpa using h7
    have h7c : |K| ≤ c / 2 * (t : ℚ) ^ d := by
      have h8 : (0 : ℚ) ≤ c / 2 := le_of_lt (div_pos hcpos (by norm_num))
      have h9 : c / 2 * (t : ℚ) ≤ c / 2 * (t : ℚ) ^ d := mul_le_mul_of_nonneg_left h6 h8
      linarith [h5, h9]
    have h11 : K ≤ |K| := le_abs_self K
    nlinarith [h1, h3, h7c, h11]
  have hdeg : Q.natDegree = d := le_antisymm hQle hQge
  exact ⟨d, hdd, by omega⟩

end Commons.RingTheory.Ideal.Hilbert

end


-- ==== from Submission.Commons.RingTheory.KrullDimension.quotient_idealOfVars_eq_zero ====
section

namespace Commons.RingTheory.KrullDimension

/-- The quotient of `k[x₁,…,x_m]` by the ideal of the variables is the field `k`, so it has
Krull dimension zero. -/
private theorem quotient_idealOfVars_eq_zero {k : Type*} [Field k] {m : ℕ} :
    ringKrullDim (MvPolynomial (Fin m) k ⧸ MvPolynomial.idealOfVars (Fin m) k) = 0 := by
  have hmax : (MvPolynomial.idealOfVars (Fin m) k).IsMaximal :=
    Commons.Algebra.MvPolynomial.idealOfVars_isMaximal
  exact ringKrullDim_eq_zero_of_isField
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmax)

end Commons.RingTheory.KrullDimension
end


-- ==== from Submission.Commons.RingTheory.Ideal.card_minimalPrimes_homogeneous_le ====
section

/-!
# A Bezout bound for the number of minimal primes of a homogeneous ideal

If `F : Fin n → k[X_0,…,X_n]` is a family of homogeneous polynomials of degrees `d i`, then the
number of minimal primes of the ideal generated by them is at most `∏ i, (d i).max 1`.

The mathematical content is the classical *Bezout inequality for the number of irreducible
components*: the number of irreducible components of the intersection of `n` hypersurfaces of
degrees `d_1, …, d_n` in `P^n` is at most `d_1 ⋯ d_n`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Commons.RingTheory.Ideal

open MvPolynomial

open Classical

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The minimal primes of an ideal are in bijection with the minimal primes of the zero ideal of
the quotient. -/
private theorem natCard_minimalPrimes_quotient {R : Type*} [CommRing R] (I : Ideal R) :
    Nat.card ↥(I.minimalPrimes) = Nat.card ↥(Ideal.minimalPrimes (⊥ : Ideal (R ⧸ I))) := by
  classical
  have hbot : Ideal.comap (Ideal.Quotient.mk I) (⊥ : Ideal (R ⧸ I)) = I := by
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  have hcomap : ∀ q : ↥(Ideal.minimalPrimes (⊥ : Ideal (R ⧸ I))),
      Ideal.comap (Ideal.Quotient.mk I) (q : Ideal _) ∈ I.minimalPrimes := by
    intro q
    have h := Ideal.minimalPrimes_comap_of_surjective (f := Ideal.Quotient.mk I)
      I.mkQ_surjective (I := (⊥ : Ideal (R ⧸ I))) q.2
    rwa [hbot] at h
  have hinj : Function.Injective (fun q : ↥(Ideal.minimalPrimes (⊥ : Ideal (R ⧸ I))) =>
      (⟨Ideal.comap (Ideal.Quotient.mk I) (q : Ideal _), hcomap q⟩ : ↥(I.minimalPrimes))) := by
    intro p q hpq
    have h1 : Ideal.comap (Ideal.Quotient.mk I) (p : Ideal _) =
        Ideal.comap (Ideal.Quotient.mk I) (q : Ideal _) := congrArg Subtype.val hpq
    refine Subtype.ext (le_antisymm ?_ ?_)
    · exact (Ideal.comap_le_comap_iff_of_surjective (Ideal.Quotient.mk I) I.mkQ_surjective _ _).mp
        (le_of_eq h1)
    · exact (Ideal.comap_le_comap_iff_of_surjective (Ideal.Quotient.mk I) I.mkQ_surjective _ _).mp
        (le_of_eq h1.symm)
  have hsurj : Function.Surjective (fun q : ↥(Ideal.minimalPrimes (⊥ : Ideal (R ⧸ I))) =>
      (⟨Ideal.comap (Ideal.Quotient.mk I) (q : Ideal _), hcomap q⟩ : ↥(I.minimalPrimes))) := by
    intro p
    have hp : (p : Ideal R) ∈ Ideal.comap (Ideal.Quotient.mk I) '' Ideal.minimalPrimes
        (⊥ : Ideal (R ⧸ I)) := by
      rw [← Ideal.minimalPrimes_eq_comap]; exact p.2
    obtain ⟨q, hq, hqp⟩ := hp
    refine ⟨⟨q, hq⟩, ?_⟩
    show (⟨Ideal.comap (Ideal.Quotient.mk I) q, hcomap ⟨q, hq⟩⟩ : ↥(I.minimalPrimes)) = p
    exact Subtype.ext hqp
  exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩)).symm

variable {k : Type*} [Field k] {m : ℕ}

/-- The minimal primes of an ideal of a polynomial ring over a field form a finite type. -/
private def inst_anon_c47_1 (K : Ideal (MvPolynomial (Fin m) k)) : Fintype ↥(K.minimalPrimes) :=
  haveI : Finite ↥(K.minimalPrimes) := Commons.RingTheory.Ideal.finite_subtype_minimalPrimes K
  Fintype.ofFinite _
attribute [local instance] inst_anon_c47_1




/-! ## Homogeneity of the ideals appearing in the induction -/

/-- The `j`-th homogeneous component of an element of a sum of homogeneous ideals lies in the
sum. -/
private theorem homogeneousComponent_mem_sup {J J' : Ideal (MvPolynomial (Fin m) k)}
    (hJ : ∀ x ∈ J, ∀ j, MvPolynomial.homogeneousComponent j x ∈ J)
    (hJ' : ∀ x ∈ J', ∀ j, MvPolynomial.homogeneousComponent j x ∈ J') :
    ∀ x ∈ J ⊔ J', ∀ j, MvPolynomial.homogeneousComponent j x ∈ J ⊔ J' := by
  intro x hx j
  rw [Submodule.mem_sup] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  rw [map_add]
  exact add_mem (Ideal.mem_sup_left (hJ a ha j)) (Ideal.mem_sup_right (hJ' b hb j))

/-- The ideal generated by a single homogeneous element is homogeneous. -/
private theorem homogeneousComponent_mem_span_singleton {g : MvPolynomial (Fin m) k} {e : ℕ}
    (hg : g.IsHomogeneous e) :
    ∀ x ∈ Ideal.span {g}, ∀ j, MvPolynomial.homogeneousComponent j x ∈ Ideal.span {g} := by
  have hhom : (Ideal.span {g}).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin m) k) := by
    apply Ideal.homogeneous_span
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨e, hg⟩
  intro x hx j
  exact (MvPolynomial.mem_iff_homogeneousComponent_mem hhom x).mp hx j

/-- The irrelevant ideal is homogeneous. -/
private theorem homogeneousComponent_mem_idealOfVars :
    ∀ x ∈ MvPolynomial.idealOfVars (Fin m) k, ∀ j,
      MvPolynomial.homogeneousComponent j x ∈ MvPolynomial.idealOfVars (Fin m) k := by
  have hhom : (MvPolynomial.idealOfVars (Fin m) k).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin m) k) := by
    rw [MvPolynomial.idealOfVars]
    apply Ideal.homogeneous_span
    rintro y ⟨i, rfl⟩
    exact ⟨1, MvPolynomial.isHomogeneous_X (σ := Fin m) (R := k) i⟩
  intro x hx j
  exact (MvPolynomial.mem_iff_homogeneousComponent_mem hhom x).mp hx j

/-- The positive-degree part of the polynomial ring is contained in the ideal of the variables. -/
private theorem homogeneousSubmodule_subset_idealOfVars_of_pos (t : ℕ) (ht : 1 ≤ t) :
    (MvPolynomial.homogeneousSubmodule (Fin m) k t : Set (MvPolynomial (Fin m) k)) ⊆
      (MvPolynomial.idealOfVars (Fin m) k : Set (MvPolynomial (Fin m) k)) := by
  intro x hx
  show x ∈ MvPolynomial.idealOfVars (Fin m) k
  rw [← pow_one (MvPolynomial.idealOfVars (Fin m) k)]
  exact (MvPolynomial.mem_pow_idealOfVars_iff (σ := Fin m) (R := k) 1 x).mpr (by
    intro d hd
    have h : Finsupp.weight (fun _ : Fin m => 1) d = t := hx (Finsupp.mem_support_iff.mp hd)
    rw [← Finsupp.degree_eq_weight_one] at h
    omega)

/-! ## The Hilbert polynomial of a homogeneous quotient -/

/-- The Hilbert polynomial of the quotient by a homogeneous ideal: a polynomial in `ℚ[X]` which
agrees with the Hilbert function `t ↦ dim_k (S ⧸ J)_t` for all sufficiently large `t`. -/
private def hilbPoly (J : Ideal (MvPolynomial (Fin m) k))
    (hJ : ∀ x ∈ J, ∀ j, MvPolynomial.homogeneousComponent j x ∈ J) : Polynomial ℚ :=
  Classical.choose (Commons.RingTheory.Ideal.Hilbert.exists_hilbertPoly_homogeneous_quotient J hJ)

private theorem hilbPoly_spec (J : Ideal (MvPolynomial (Fin m) k))
    (hJ : ∀ x ∈ J, ∀ j, MvPolynomial.homogeneousComponent j x ∈ J) :
    ∃ N, ∀ t ≥ N, (Module.finrank k (Submodule.map (J.mkQ.restrictScalars k)
      (MvPolynomial.homogeneousSubmodule (Fin m) k t)) : ℚ) = (hilbPoly J hJ).eval (t : ℚ) :=
  Classical.choose_spec (Commons.RingTheory.Ideal.Hilbert.exists_hilbertPoly_homogeneous_quotient J hJ)

private theorem hilbPoly_congr {J : Ideal (MvPolynomial (Fin m) k)}
    (h1 h2 : ∀ x ∈ J, ∀ j, MvPolynomial.homogeneousComponent j x ∈ J) :
    hilbPoly J h1 = hilbPoly J h2 :=
  congrArg (fun h => Classical.choose
    (Commons.RingTheory.Ideal.Hilbert.exists_hilbertPoly_homogeneous_quotient J h))
    (Subsingleton.elim h1 h2)

/-- Two rational polynomials agreeing on all sufficiently large natural numbers are equal. -/
private theorem polynomial_eq_of_eventually_eval_eq {P Q : Polynomial ℚ}
    (h : ∃ N : ℕ, ∀ t : ℕ, N ≤ t → P.eval (t : ℚ) = Q.eval (t : ℚ)) : P = Q := by
  obtain ⟨N, hN⟩ := h
  refine Polynomial.eq_of_infinite_eval_eq P Q ?_
  refine Set.Infinite.mono ?_ (Set.Infinite.image (s := Set.Ici N) (f := fun n : ℕ => (n : ℚ))
    (Nat.cast_injective.injOn) (Set.Ici_infinite N))
  rintro x ⟨n, hn, rfl⟩
  exact hN n hn

/-- The degree of the Hilbert polynomial of the quotient by a homogeneous prime. -/
private def hilbDim (q : Ideal (MvPolynomial (Fin m) k))
    (hq : ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q) : ℕ :=
  (hilbPoly q hq).natDegree

/-- The degree of the projective variety `Proj (S ⧸ q)`: the leading coefficient of the Hilbert
polynomial of `S ⧸ q` times the factorial of the degree of that polynomial. -/
private def hilbDeg (q : Ideal (MvPolynomial (Fin m) k))
    (hq : ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q) : ℚ :=
  (hilbPoly q hq).leadingCoeff * (hilbDim q hq).factorial

private theorem hilbDeg_eq_coeff (q : Ideal (MvPolynomial (Fin m) k))
    (hq : ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q) :
    hilbDeg q hq = (hilbPoly q hq).coeff (hilbDim q hq) * (hilbDim q hq).factorial := by
  rw [hilbDeg, hilbDim, Polynomial.coeff_natDegree]

private theorem hilbDeg_nonneg (q : Ideal (MvPolynomial (Fin m) k))
    (hq : ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q) : 0 ≤ hilbDeg q hq := by
  rw [hilbDeg]
  refine mul_nonneg ?_ (by positivity)
  obtain ⟨N, hN⟩ := hilbPoly_spec q hq
  refine Commons.Algebra.Polynomial.coeff_nonneg_of_eventually_eval_nonneg (f := hilbPoly q hq)
    (d := hilbDim q hq) (le_of_eq rfl) ⟨N, fun t ht => ?_⟩
  rw [← hN t ht]
  positivity

/-- For a homogeneous prime which is not the irrelevant ideal, the Hilbert polynomial is
nonzero: the Hilbert function is eventually positive. -/
private theorem hilbPoly_ne_zero_of_ne_idealOfVars (q : Ideal (MvPolynomial (Fin m) k)) [q.IsPrime]
    (hq : ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q)
    (hqM : q ≠ MvPolynomial.idealOfVars (Fin m) k) : hilbPoly q hq ≠ 0 := by
  intro hzero
  obtain ⟨N, hN⟩ := hilbPoly_spec q hq
  obtain ⟨i, hi⟩ : ∃ i : Fin m, MvPolynomial.X i ∉ q := by
    by_contra hcon
    push Not at hcon
    refine hqM (Ideal.IsMaximal.eq_of_le Commons.Algebra.MvPolynomial.idealOfVars_isMaximal
      (Ideal.IsPrime.ne_top' (I := q)) ?_).symm
    rw [MvPolynomial.idealOfVars]
    exact Ideal.span_le.mpr (by rintro x ⟨j, rfl⟩; exact hcon j)
  set t := max N 1 with ht
  have hmem : (Submodule.mkQ q) (MvPolynomial.X i ^ t) ∈
      Submodule.map (q.mkQ.restrictScalars k) (MvPolynomial.homogeneousSubmodule (Fin m) k t) := by
    refine Submodule.mem_map.mpr ⟨MvPolynomial.X i ^ t, ?_, rfl⟩
    exact MvPolynomial.isHomogeneous_X_pow i t
  have hne : (Submodule.mkQ q) (MvPolynomial.X i ^ t) ≠ 0 := by
    intro h0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
    exact hi (Ideal.IsPrime.mem_of_pow_mem (I := q) ‹q.IsPrime› t h0)
  have hpos : (0 : ℚ) < (Module.finrank k
      ↥(Submodule.map (q.mkQ.restrictScalars k)
        (MvPolynomial.homogeneousSubmodule (Fin m) k t)) : ℚ) := by
    have hfin : Module.Finite k ↥(Submodule.map (q.mkQ.restrictScalars k)
        (MvPolynomial.homogeneousSubmodule (Fin m) k t)) :=
      Module.Finite.of_fg (Submodule.FG.map _ (MvPolynomial.homogeneousSubmodule_fg (Fin m) k t))
    have h1 : Module.finrank k ↥(Submodule.span k {(Submodule.mkQ q) (MvPolynomial.X i ^ t)}) = 1 :=
      finrank_span_singleton hne
    have h2 : Submodule.span k {(Submodule.mkQ q) (MvPolynomial.X i ^ t)} ≤
        Submodule.map (q.mkQ.restrictScalars k) (MvPolynomial.homogeneousSubmodule (Fin m) k t) := by
      rw [Submodule.span_le, Set.singleton_subset_iff]
      simpa using hmem
    have h3 : 1 ≤ Module.finrank k ↥(Submodule.map (q.mkQ.restrictScalars k)
        (MvPolynomial.homogeneousSubmodule (Fin m) k t)) := by
      rw [← h1]
      exact Submodule.finrank_mono h2
    exact_mod_cast h3
  have hzero' : (Module.finrank k (Submodule.map (q.mkQ.restrictScalars k)
      (MvPolynomial.homogeneousSubmodule (Fin m) k t)) : ℚ) = 0 := by
    have h := hN t (le_max_left _ _)
    rw [hzero, Polynomial.eval_zero] at h
    exact h
  linarith

/-! ## The base case: the polynomial ring itself -/

private theorem hilbPoly_bot_eq (hm : 0 < m) :
    hilbPoly (⊥ : Ideal (MvPolynomial (Fin m) k))
      (fun x hx j => by rw [Submodule.mem_bot] at hx; simp [hx]) =
      Polynomial.preHilbertPoly ℚ (m - 1) 0 := by
  obtain ⟨N, hN⟩ := hilbPoly_spec (⊥ : Ideal (MvPolynomial (Fin m) k))
    (fun x hx j => by rw [Submodule.mem_bot] at hx; simp [hx])
  refine polynomial_eq_of_eventually_eval_eq ⟨max N 1, fun t ht => ?_⟩
  have htN : N ≤ t := le_trans (le_max_left _ _) ht
  rw [← hN t htN, Commons.Algebra.MvPolynomial.finrank_map_bot_mkQ_homogeneousSubmodule t,
    Polynomial.preHilbertPoly_eq_choose_sub_add ℚ (m - 1) (k := 0) (n := t) (Nat.zero_le t),
    Nat.sub_zero]
  have hsym : (m + t - 1).choose t = (m + t - 1).choose (m - 1) := by
    have h2 : m + t - 1 - t = m - 1 := by omega
    have h := Nat.choose_symm (n := m + t - 1) (k := t) (show t ≤ m + t - 1 by omega)
    rw [h2] at h
    exact h.symm
  have harg : t + (m - 1) = m + t - 1 := by omega
  rw [harg, hsym]

private theorem hilbDeg_bot_eq_one (hm : 0 < m) :
    hilbDeg (⊥ : Ideal (MvPolynomial (Fin m) k))
      (fun x hx j => by rw [Submodule.mem_bot] at hx; simp [hx]) = 1 := by
  have hbot := hilbPoly_bot_eq (k := k) (m := m) hm
  rw [hilbDeg, hilbDim, hbot, Polynomial.natDegree_preHilbertPoly,
    Polynomial.leadingCoeff_preHilbertPoly]
  have hf : (((m - 1).factorial : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (m - 1)
  field_simp


/-! ## The Bezout relation for Hilbert polynomials -/

/-- The Bezout relation: for a homogeneous prime `p` and a homogeneous element `f` of degree `e`
which is not in `p`, the Hilbert polynomial of the quotient by `p + (f)` is the difference of the
Hilbert polynomial of `S ⧸ p` and its shift by `e`. -/
private theorem hilbPoly_sup_span_eq {p : Ideal (MvPolynomial (Fin m) k)} [p.IsPrime]
    (hp : ∀ x ∈ p, ∀ j, MvPolynomial.homogeneousComponent j x ∈ p)
    {f : MvPolynomial (Fin m) k} {e : ℕ} (hf : f.IsHomogeneous e) (hf0 : f ≠ 0)
    (hfp : f ∉ p) :
    hilbPoly (p ⊔ Ideal.span {f})
        (homogeneousComponent_mem_sup hp (homogeneousComponent_mem_span_singleton hf)) =
      hilbPoly p hp - Polynomial.taylor (-(e : ℚ)) (hilbPoly p hp) := by
  have hreg : IsSMulRegular (MvPolynomial (Fin m) k ⧸ p) f := by
    rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
    intro a ha
    exact (Ideal.IsPrime.mem_or_mem ‹p.IsPrime› ha).resolve_left hfp
  obtain ⟨N1, hN1⟩ := hilbPoly_spec p hp
  obtain ⟨N2, hN2⟩ := hilbPoly_spec (p ⊔ Ideal.span {f})
    (homogeneousComponent_mem_sup hp (homogeneousComponent_mem_span_singleton hf))
  refine polynomial_eq_of_eventually_eval_eq ⟨max (max N1 N2) (e + N1), fun j hj => ?_⟩
  have hj1 : N1 ≤ j := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hj
  have hj2 : N2 ≤ j := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hj
  have hj3 : e + N1 ≤ j := le_trans (le_max_right _ _) hj
  have hje : e ≤ j := by omega
  have hbez := Commons.RingTheory.Ideal.Hilbert.hilbertFun_bezout p hp hf hf0 hreg j hje
  have h1 := hN1 j hj1
  have h3 := hN1 (j - e) (by omega)
  have hbezQ : ((Module.finrank k (Submodule.map ((p ⊔ Ideal.span {f}).mkQ.restrictScalars k)
        (MvPolynomial.homogeneousSubmodule (Fin m) k j))
      + Module.finrank k (Submodule.map (p.mkQ.restrictScalars k)
        (MvPolynomial.homogeneousSubmodule (Fin m) k (j - e))) : ℕ) : ℚ)
      = (Module.finrank k (Submodule.map (p.mkQ.restrictScalars k)
        (MvPolynomial.homogeneousSubmodule (Fin m) k j)) : ℚ) := by
    exact_mod_cast hbez
  rw [Nat.cast_add, hN2 j hj2, h3, h1] at hbezQ
  rw [Polynomial.eval_sub, Polynomial.taylor_eval]
  rw [show (j : ℚ) + -(e : ℚ) = ((j - e : ℕ) : ℚ) from by rw [Nat.cast_sub hje]; ring]
  linarith

/-- The Hilbert polynomial of the quotient by `p + (f)` has degree one less than that of `S ⧸ p`. -/
private theorem hilbDim_sup_span_eq {p : Ideal (MvPolynomial (Fin m) k)} [p.IsPrime]
    (hp : ∀ x ∈ p, ∀ j, MvPolynomial.homogeneousComponent j x ∈ p)
    {f : MvPolynomial (Fin m) k} {e : ℕ} (hf : f.IsHomogeneous e) (hf0 : f ≠ 0) (he : 0 < e)
    (hfp : f ∉ p) (hP : hilbPoly p hp ≠ 0) :
    hilbDim (p ⊔ Ideal.span {f})
      (homogeneousComponent_mem_sup hp (homogeneousComponent_mem_span_singleton hf))
      = hilbDim p hp - 1 := by
  have h := hilbPoly_sup_span_eq hp hf hf0 hfp
  rw [hilbDim, h]
  exact (Commons.Algebra.Polynomial.natDegree_sub_taylor_natCast he hP).1

/-- The Hilbert polynomial of the quotient by the irrelevant ideal is zero. -/
private theorem hilbPoly_idealOfVars_eq_zero :
    hilbPoly (MvPolynomial.idealOfVars (Fin m) k) homogeneousComponent_mem_idealOfVars = 0 := by
  obtain ⟨N, hN⟩ := hilbPoly_spec (MvPolynomial.idealOfVars (Fin m) k)
    homogeneousComponent_mem_idealOfVars
  refine polynomial_eq_of_eventually_eval_eq ⟨max N 1, fun t ht => ?_⟩
  have htN : N ≤ t := le_trans (le_max_left _ _) ht
  have h0 : (Module.finrank k (Submodule.map
      ((MvPolynomial.idealOfVars (Fin m) k).mkQ.restrictScalars k)
      (MvPolynomial.homogeneousSubmodule (Fin m) k t)) : ℚ) = 0 := by
    have hbot : Submodule.map ((MvPolynomial.idealOfVars (Fin m) k).mkQ.restrictScalars k)
        (MvPolynomial.homogeneousSubmodule (Fin m) k t) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      rw [Submodule.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      change Ideal.Quotient.mk (MvPolynomial.idealOfVars (Fin m) k) y = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact homogeneousSubmodule_subset_idealOfVars_of_pos (k := k) (m := m) t
        (le_trans (le_max_right _ _) ht) hy
    rw [hbot]
    simp
  rw [← hN t htN, h0]
  simp


/-- A variable not lying in a homogeneous prime different from the irrelevant ideal. -/
private theorem exists_X_notMem_of_ne_idealOfVars (q : Ideal (MvPolynomial (Fin m) k)) [q.IsPrime]
    (hq : q ≠ MvPolynomial.idealOfVars (Fin m) k) :
    ∃ i : Fin m, MvPolynomial.X i ∉ q := by
  by_contra hcon
  push Not at hcon
  refine hq (Commons.Algebra.MvPolynomial.idealOfVars_isMaximal.eq_of_le (Ideal.IsPrime.ne_top' (I := q)) ?_).symm
  rw [MvPolynomial.idealOfVars]
  exact Ideal.span_le.mpr (by rintro x ⟨j, rfl⟩; exact hcon j)

/-- A homogeneous prime different from the irrelevant ideal has quotient of dimension at least
one, hence a nonzero Hilbert polynomial. -/
private theorem one_le_ringKrullDim_quotient_of_ne_idealOfVars' (q : Ideal (MvPolynomial (Fin m) k))
    [q.IsPrime] (hhom : ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q)
    (hq : q ≠ MvPolynomial.idealOfVars (Fin m) k) :
    (1 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin m) k ⧸ q) :=
  Commons.RingTheory.KrullDimension.one_le_quotient_of_ne_idealOfVars q hhom hq


/-! ## Equidimensionality and the local Bezout bound -/

/-- A homogeneous prime with zero-dimensional quotient has vanishing Hilbert polynomial. -/
private theorem hilbPoly_eq_zero_of_ringKrullDim_quotient_eq_zero (q : Ideal (MvPolynomial (Fin m) k))
    [q.IsPrime] (hq : ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q)
    (hz : ringKrullDim (MvPolynomial (Fin m) k ⧸ q) = 0) : hilbPoly q hq = 0 := by
  have hqM : q = MvPolynomial.idealOfVars (Fin m) k := by
    by_contra hne
    have h1 := Commons.RingTheory.KrullDimension.one_le_quotient_of_ne_idealOfVars q hq hne
    rw [hz] at h1
    exact absurd h1 (by simp)
  subst hqM
  rw [hilbPoly_congr hq (homogeneousComponent_mem_idealOfVars (k := k) (m := m)),
    hilbPoly_idealOfVars_eq_zero]

/-- Equidimensionality: every minimal prime of `p + (f)` has Hilbert polynomial of degree one
less than that of `S ⧸ p`. -/
private theorem hilbDim_minimalPrimes_sup_span_eq {p : Ideal (MvPolynomial (Fin m) k)} [p.IsPrime]
    (hp : ∀ x ∈ p, ∀ j, MvPolynomial.homogeneousComponent j x ∈ p)
    {f : MvPolynomial (Fin m) k} (hf : f.IsHomogeneous f.totalDegree) (hfp : f ∉ p)
    (hf0 : f ≠ 0) (htop : p ⊔ Ideal.span {f} ≠ ⊤) (hP : hilbPoly p hp ≠ 0) :
    ∀ q : ↥((p ⊔ Ideal.span {f}).minimalPrimes),
      hilbDim q.1 (minimalPrimes_homogeneous _
        (homogeneousComponent_mem_sup hp (homogeneousComponent_mem_span_singleton hf)) q.2)
        = hilbDim p hp - 1 := by
  intro q
  haveI : q.1.IsPrime := q.2.1.1
  have hK := homogeneousComponent_mem_sup hp (homogeneousComponent_mem_span_singleton hf)
  have hq_hom := minimalPrimes_homogeneous (p ⊔ Ideal.span {f}) hK q.2
  have heqd := Commons.RingTheory.KrullDimension.quotient_add_one_of_mem_minimalPrimes_sup_span
    p hp hfp q.1 q.2 htop
  obtain ⟨dp, hdp, hdpeq⟩ := Commons.RingTheory.Ideal.Hilbert.natDegree_hilbertPoly_eq_dim_sub_one p hp (hilbPoly p hp)
    (hilbPoly_spec p hp) hP
  -- the dimension of `S ⧸ q` equals `hilbDim p`
  have hqdim : ringKrullDim (MvPolynomial (Fin m) k ⧸ q.1) = (hilbDim p hp : WithBot ℕ∞) := by
    have h1 : ((hilbDim p hp + 1 : ℕ) : WithBot ℕ∞) = ringKrullDim (MvPolynomial (Fin m) k ⧸ p) := by
      rw [hdp]
      exact congrArg _ hdpeq.symm
    have h2 : ringKrullDim (MvPolynomial (Fin m) k ⧸ q.1) + 1
        = ((hilbDim p hp : ℕ) : WithBot ℕ∞) + 1 := by
      rw [heqd, ← h1]
      push_cast
      ring
    exact Commons.Order.WithBot_ENat_add_one_inj h2
  by_cases hp0 : hilbDim p hp = 0
  · -- then every minimal prime is the irrelevant ideal
    have hqM : q.1 = MvPolynomial.idealOfVars (Fin m) k := by
      by_contra hne
      have h1 := Commons.RingTheory.KrullDimension.one_le_quotient_of_ne_idealOfVars q.1 hq_hom hne
      rw [hqdim, hp0] at h1
      exact absurd h1 (by simp)
    have hqdim0 : ringKrullDim (MvPolynomial (Fin m) k ⧸ q.1) = 0 := by
      rw [hqdim, hp0]; rfl
    show hilbDim q.1 hq_hom = hilbDim p hp - 1
    rw [hilbDim, hilbPoly_eq_zero_of_ringKrullDim_quotient_eq_zero q.1 hq_hom hqdim0,
      Polynomial.natDegree_zero, hp0]
  · -- the general case
    have hqne : q.1 ≠ MvPolynomial.idealOfVars (Fin m) k := by
      intro hcon
      have hz : ringKrullDim (MvPolynomial (Fin m) k ⧸ q.1) = 0 := by
        rw [hcon]; exact Commons.RingTheory.KrullDimension.quotient_idealOfVars_eq_zero
      rw [hz] at hqdim
      have hz' : (hilbDim p hp : WithBot ℕ∞) = 0 := hqdim.symm
      exact hp0 (WithBot.coe_inj.mp (by simpa using hz'))
    have hqP : hilbPoly q.1 hq_hom ≠ 0 :=
      hilbPoly_ne_zero_of_ne_idealOfVars q.1 hq_hom hqne
    obtain ⟨dq, hdq, hdqe⟩ := Commons.RingTheory.Ideal.Hilbert.natDegree_hilbertPoly_eq_dim_sub_one q.1 hq_hom
      (hilbPoly q.1 hq_hom) (hilbPoly_spec q.1 hq_hom) hqP
    rw [hdq] at hqdim
    have h5 : dq = hilbDim p hp :=
      ENat.natCast_inj.mp (WithBot.coe_inj.mp hqdim)
    have h6 : (hilbPoly q.1 hq_hom).natDegree = hilbDim p hp - 1 := by omega
    simpa [hilbDim] using h6


/-- The local Bezout bound: the sum of the degrees of the minimal primes of `p + (f)` is at most
`deg f` times the degree of `S ⧸ p`. -/
private theorem sum_hilbDeg_minimalPrimes_sup_span_le {p : Ideal (MvPolynomial (Fin m) k)} [p.IsPrime]
    (hp : ∀ x ∈ p, ∀ j, MvPolynomial.homogeneousComponent j x ∈ p)
    {f : MvPolynomial (Fin m) k} (hf : f.IsHomogeneous f.totalDegree) (hfp : f ∉ p) :
    (∑ q : ↥((p ⊔ Ideal.span {f}).minimalPrimes),
      hilbDeg q.1 (minimalPrimes_homogeneous _
        (homogeneousComponent_mem_sup hp (homogeneousComponent_mem_span_singleton hf)) q.2))
      ≤ ((f.totalDegree.max 1 : ℕ) : ℚ) * hilbDeg p hp := by
  classical

  by_cases htop : p ⊔ Ideal.span {f} = ⊤
  · haveI : IsEmpty ↥((p ⊔ Ideal.span {f}).minimalPrimes) := by
      rw [htop]
      refine ⟨fun q => ?_⟩
      rw [Ideal.minimalPrimes_top] at q
      exact q.2
    rw [Finset.sum_eq_zero (fun q _ => (IsEmpty.false q).elim)]
    exact mul_nonneg (by positivity) (hilbDeg_nonneg p hp)
  · by_cases hdeg0 : f.totalDegree = 0
    · exfalso
      have hfc : f = MvPolynomial.C (MvPolynomial.coeff 0 f) := by
        have h1 := MvPolynomial.homogeneousComponent_eq_self (p := f) (n := 0)
          ((MvPolynomial.mem_homogeneousSubmodule 0 f).mpr (by simpa [hdeg0] using hf))
        rw [MvPolynomial.homogeneousComponent_zero] at h1
        exact h1.symm
      have hc0 : MvPolynomial.coeff 0 f ≠ 0 := by
        intro h
        rw [h, MvPolynomial.C_0] at hfc
        exact hfp (hfc ▸ p.zero_mem)
      refine htop ?_
      rw [hfc]
      have hunit : IsUnit (MvPolynomial.C (MvPolynomial.coeff 0 f) : MvPolynomial (Fin m) k) :=
        IsUnit.of_mul_eq_one (MvPolynomial.C (MvPolynomial.coeff 0 f)⁻¹) (by
          rw [← map_mul, mul_inv_cancel₀ hc0, map_one])
      exact Ideal.eq_top_of_isUnit_mem _
        (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) hunit
    · have hf0 : f ≠ 0 := fun h => hfp (h ▸ p.zero_mem)
      have hfpM : p ≠ MvPolynomial.idealOfVars (Fin m) k := by
        intro hcon
        rw [hcon] at hfp
        exact hfp (homogeneousSubmodule_subset_idealOfVars_of_pos (k := k) (m := m)
          f.totalDegree (by omega) ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr hf))
      obtain ⟨d, hd, hd0, hdK⟩ := Commons.RingTheory.Ideal.Hilbert.dim_quotient_sup_span_eq_dim_sub_one p hp hfp hf0 htop
      have hPp : hilbPoly p hp ≠ 0 := hilbPoly_ne_zero_of_ne_idealOfVars p hp hfpM
      obtain ⟨dp, hdp, hdpeq⟩ := Commons.RingTheory.Ideal.Hilbert.natDegree_hilbertPoly_eq_dim_sub_one p hp (hilbPoly p hp)
        (hilbPoly_spec p hp) hPp
      have hdpd : dp = d := by
        have h : ((dp : ℕ) : WithBot ℕ∞) = ((d : ℕ) : WithBot ℕ∞) := hdp.symm.trans hd
        exact_mod_cast h
      have hNp : hilbDim p hp = d - 1 := by
        have h1 : hilbDim p hp + 1 = dp := hdpeq.symm
        omega
      by_cases hd1 : d = 1
      · have hzero : ∀ q : ↥((p ⊔ Ideal.span {f}).minimalPrimes),
            hilbDeg q.1 (minimalPrimes_homogeneous _
              (homogeneousComponent_mem_sup hp (homogeneousComponent_mem_span_singleton hf)) q.2)
            = 0 := by
          intro q
          haveI : q.1.IsPrime := q.2.1.1
          have heqd := Commons.RingTheory.KrullDimension.quotient_add_one_of_mem_minimalPrimes_sup_span
            p hp hfp q.1 q.2 htop
          have hqdim0 : ringKrullDim (MvPolynomial (Fin m) k ⧸ q.1) = 0 := by
            refine Commons.Order.WithBot_ENat_add_one_inj (x := ringKrullDim
              (MvPolynomial (Fin m) k ⧸ q.1)) (y := 0) ?_
            rw [heqd, hdp, hdpd, hd1]
            rfl
          rw [hilbDeg, hilbPoly_eq_zero_of_ringKrullDim_quotient_eq_zero q.1 _ hqdim0,
            Polynomial.leadingCoeff_zero, zero_mul]
        rw [Finset.sum_eq_zero (fun q _ => hzero q)]
        exact mul_nonneg (by positivity) (hilbDeg_nonneg p hp)
      · have hd2 : 2 ≤ d := by omega
        have hNp1 : 1 ≤ hilbDim p hp := by omega
        have hEqd := hilbDim_minimalPrimes_sup_span_eq hp hf hfp hf0 htop hPp
        have hdeg : ∀ q : ↥((p ⊔ Ideal.span {f}).minimalPrimes),
            (hilbPoly q.1 (minimalPrimes_homogeneous _
              (homogeneousComponent_mem_sup hp (homogeneousComponent_mem_span_singleton hf)) q.2)).natDegree
            = hilbDim p hp - 1 := fun q => hEqd q
        have hPdeg : (hilbPoly (p ⊔ Ideal.span {f})
            (homogeneousComponent_mem_sup hp (homogeneousComponent_mem_span_singleton hf))).natDegree
            = hilbDim p hp - 1 :=
          hilbDim_sup_span_eq hp hf hf0 (by omega) hfp hPp
        have hbez := hilbPoly_sup_span_eq (p := p) hp hf hf0 hfp
        have hbez' : hilbPoly (p ⊔ Ideal.span {f})
            (homogeneousComponent_mem_sup hp (homogeneousComponent_mem_span_singleton hf))
            = hilbPoly p hp - (hilbPoly p hp).comp
              (Polynomial.X - Polynomial.C ((f.totalDegree : ℚ))) := by
          rw [hbez, Polynomial.taylor_apply, Polynomial.C_neg]
          ring
        have hkey := Commons.RingTheory.Ideal.Hilbert.localBoundPoly (K := p ⊔ Ideal.span {f})
          (homogeneousComponent_mem_sup hp (homogeneousComponent_mem_span_singleton hf))
          (fun q hq x hx j => minimalPrimes_homogeneous (p ⊔ Ideal.span {f})
            (homogeneousComponent_mem_sup hp (homogeneousComponent_mem_span_singleton hf)) hq x hx j)
          (hilbPoly (p ⊔ Ideal.span {f})
            (homogeneousComponent_mem_sup hp (homogeneousComponent_mem_span_singleton hf)))
          (hilbPoly_spec _ _)
          (fun q => hilbPoly q.1 (minimalPrimes_homogeneous _
            (homogeneousComponent_mem_sup hp (homogeneousComponent_mem_span_singleton hf)) q.2))
          (fun q => hilbPoly_spec _ _)
          (hilbPoly p hp) (hilbDim p hp) f.totalDegree hNp1 (by omega) hPdeg rfl hbez' hdeg
        calc (∑ q : ↥((p ⊔ Ideal.span {f}).minimalPrimes),
              hilbDeg q.1 (minimalPrimes_homogeneous _
                (homogeneousComponent_mem_sup hp (homogeneousComponent_mem_span_singleton hf)) q.2))
            = ∑ q : ↥((p ⊔ Ideal.span {f}).minimalPrimes),
                (hilbPoly q.1 (minimalPrimes_homogeneous _
                  (homogeneousComponent_mem_sup hp (homogeneousComponent_mem_span_singleton hf)) q.2)).leadingCoeff
                  * ((hilbPoly q.1 (minimalPrimes_homogeneous _
                    (homogeneousComponent_mem_sup hp (homogeneousComponent_mem_span_singleton hf)) q.2)).natDegree).factorial := by
              apply Finset.sum_congr rfl
              intro q _
              rw [hilbDeg, hilbDim]
            _ ≤ ((f.totalDegree.max 1 : ℕ) : ℚ) * (hilbPoly p hp).leadingCoeff
                  * (hilbDim p hp).factorial := hkey
            _ = ((f.totalDegree.max 1 : ℕ) : ℚ) * hilbDeg p hp := by
              rw [hilbDeg]; ring


/-! ## The degree of a minimal prime is at least one -/

/-- A variable which is not in a homogeneous prime gives at least one dimension in each positive
degree. -/
private theorem one_le_finrank_homogeneousSubmodule_map (q : Ideal (MvPolynomial (Fin m) k)) [q.IsPrime]
    {i : Fin m} (hi : MvPolynomial.X i ∉ q) {t : ℕ} (ht : 1 ≤ t) :
    1 ≤ Module.finrank k (Submodule.map (q.mkQ.restrictScalars k)
      (MvPolynomial.homogeneousSubmodule (Fin m) k t)) := by
  have hmem : (Submodule.mkQ q) (MvPolynomial.X i ^ t) ∈
      Submodule.map (q.mkQ.restrictScalars k) (MvPolynomial.homogeneousSubmodule (Fin m) k t) := by
    refine Submodule.mem_map.mpr ⟨MvPolynomial.X i ^ t, ?_, rfl⟩
    exact MvPolynomial.isHomogeneous_X_pow i t
  have hne : (Submodule.mkQ q) (MvPolynomial.X i ^ t) ≠ 0 := by
    intro h0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
    exact hi (Ideal.IsPrime.mem_of_pow_mem (I := q) ‹q.IsPrime› t h0)
  have hfin : Module.Finite k ↥(Submodule.map (q.mkQ.restrictScalars k)
      (MvPolynomial.homogeneousSubmodule (Fin m) k t)) :=
    Module.Finite.of_fg (Submodule.FG.map _ (MvPolynomial.homogeneousSubmodule_fg (Fin m) k t))
  have h1 : Module.finrank k ↥(Submodule.span k {(Submodule.mkQ q) (MvPolynomial.X i ^ t)}) = 1 :=
    finrank_span_singleton hne
  have h2 : Submodule.span k {(Submodule.mkQ q) (MvPolynomial.X i ^ t)} ≤
      Submodule.map (q.mkQ.restrictScalars k) (MvPolynomial.homogeneousSubmodule (Fin m) k t) := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    simpa using hmem
  rw [← h1]
  exact Submodule.finrank_mono h2

/-- For a homogeneous prime which is not the irrelevant ideal, the Hilbert function is eventually
positive. -/
private theorem hilbPoly_pos_of_ne_idealOfVars (q : Ideal (MvPolynomial (Fin m) k)) [q.IsPrime]
    (hq : ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q)
    (hqM : q ≠ MvPolynomial.idealOfVars (Fin m) k) :
    ∃ N : ℕ, ∀ t : ℕ, N ≤ t → 0 < (hilbPoly q hq).eval (t : ℚ) := by
  obtain ⟨i, hi⟩ := exists_X_notMem_of_ne_idealOfVars q hqM
  obtain ⟨N, hN⟩ := hilbPoly_spec q hq
  refine ⟨max N 1, fun t ht => ?_⟩
  rw [← hN t (le_trans (le_max_left _ _) ht)]
  have ht1 : 1 ≤ t := le_trans (le_max_right _ _) ht
  have h := one_le_finrank_homogeneousSubmodule_map q hi ht1
  have hcast : (1 : ℚ) ≤ (Module.finrank k (Submodule.map (q.mkQ.restrictScalars k)
      (MvPolynomial.homogeneousSubmodule (Fin m) k t)) : ℚ) := by exact_mod_cast h
  linarith

/-- Finite differences preserve eventual integrality on the natural numbers. -/
private lemma fdiff_eventually_int_nat {Q : Polynomial ℚ}
    (h : ∃ N : ℕ, ∀ t : ℕ, N ≤ t → ∃ z : ℤ, Q.eval (t : ℚ) = z) :
    ∃ N : ℕ, ∀ t : ℕ, N ≤ t →
      ∃ z : ℤ, (Commons.Algebra.Polynomial.fdiff Q).eval (t : ℚ) = z := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun t ht => ?_⟩
  obtain ⟨z1, h1⟩ := hN (t + 1) (by omega)
  obtain ⟨z2, h2⟩ := hN t ht
  refine ⟨z1 - z2, ?_⟩
  rw [Commons.Algebra.Polynomial.fdiff_eval,
    show ((t : ℚ) + 1) = ((t + 1 : ℕ) : ℚ) from by push_cast; ring, h1, h2]
  push_cast
  ring

/-- Every iterate of the forward difference preserves eventual integrality on the natural
numbers. -/
private lemma fdiff_iterate_eventually_int_nat (k : ℕ) {P : Polynomial ℚ}
    (h : ∃ N : ℕ, ∀ t : ℕ, N ≤ t → ∃ z : ℤ, P.eval (t : ℚ) = z) :
    ∃ N : ℕ, ∀ t : ℕ, N ≤ t →
      ∃ z : ℤ, ((Commons.Algebra.Polynomial.fdiff^[k]) P).eval (t : ℚ) = z := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact fdiff_eventually_int_nat ih

/-- If a rational polynomial is eventually positive and integer valued on the natural numbers then
its leading coefficient times `d!` is at least one. -/
private theorem one_le_coeff_mul_factorial_of_eventually_int_nat {P : Polynomial ℚ}
    (hpos : ∃ N : ℕ, ∀ t : ℕ, N ≤ t → 0 < P.eval (t : ℚ))
    (hint : ∃ N : ℕ, ∀ t : ℕ, N ≤ t → ∃ z : ℤ, P.eval (t : ℚ) = z) :
    1 ≤ P.coeff P.natDegree * P.natDegree.factorial := by
  have hPne : P ≠ 0 := by
    intro h0
    obtain ⟨N, hN⟩ := hpos
    have := hN N le_rfl
    rw [h0, Polynomial.eval_zero] at this
    exact lt_irrefl 0 this
  obtain ⟨hnd, hcoeff⟩ :=
    Commons.Algebra.Polynomial.fdiff_iterate_natDegree_coeff P P.natDegree le_rfl
  have hnd0 : ((Commons.Algebra.Polynomial.fdiff^[P.natDegree]) P).natDegree = 0 := by
    rw [hnd, Nat.sub_self]
  have hconst : ((Commons.Algebra.Polynomial.fdiff^[P.natDegree]) P) =
      Polynomial.C ((P.natDegree.factorial : ℚ) * P.coeff P.natDegree) := by
    rw [Polynomial.eq_C_of_natDegree_eq_zero hnd0]
    congr 1
    have h := hcoeff
    rw [Nat.sub_self, Nat.descFactorial_self] at h
    exact h
  obtain ⟨N', hN'⟩ := fdiff_iterate_eventually_int_nat P.natDegree hint
  obtain ⟨z, hz⟩ := hN' N' le_rfl
  rw [hconst, Polynomial.eval_C] at hz
  have hnonneg : 0 ≤ P.coeff P.natDegree := by
    apply Commons.Algebra.Polynomial.coeff_nonneg_of_eventually_eval_nonneg (f := P)
      (d := P.natDegree) le_rfl
    obtain ⟨N, hN⟩ := hpos
    exact ⟨N, fun n hn => le_of_lt (hN n hn)⟩
  have hane : P.coeff P.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hPne
  have hapos : 0 < P.coeff P.natDegree := lt_of_le_of_ne hnonneg (Ne.symm hane)
  have hfacpos : (0 : ℚ) < (P.natDegree.factorial : ℚ) := by
    exact_mod_cast Nat.factorial_pos P.natDegree
  have hqpos : 0 < (P.natDegree.factorial : ℚ) * P.coeff P.natDegree :=
    mul_pos hfacpos hapos
  have hzpos : 0 < z := by
    have h := hqpos
    rw [hz] at h
    exact_mod_cast h
  have hgoal : (1 : ℚ) ≤ (P.natDegree.factorial : ℚ) * P.coeff P.natDegree := by
    rw [hz]
    exact_mod_cast (show (1 : ℤ) ≤ z by omega)
  simpa [mul_comm] using hgoal

/-- The degree of the projective variety `Proj (S ⧸ q)` of a homogeneous prime `q` which is not
the irrelevant ideal is at least one. -/
private theorem one_le_hilbDeg (q : Ideal (MvPolynomial (Fin m) k)) [q.IsPrime]
    (hq : ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q)
    (hqM : q ≠ MvPolynomial.idealOfVars (Fin m) k) : 1 ≤ hilbDeg q hq := by
  have hint : ∃ N : ℕ, ∀ t : ℕ, N ≤ t → ∃ z : ℤ, (hilbPoly q hq).eval (t : ℚ) = z := by
    obtain ⟨N, hN⟩ := hilbPoly_spec q hq
    refine ⟨N, fun t ht => ?_⟩
    refine ⟨Module.finrank k (Submodule.map (q.mkQ.restrictScalars k)
      (MvPolynomial.homogeneousSubmodule (Fin m) k t)), ?_⟩
    rw [← hN t ht]
    push_cast
    ring
  have h := one_le_coeff_mul_factorial_of_eventually_int_nat
    (P := hilbPoly q hq) (hilbPoly_pos_of_ne_idealOfVars q hq hqM) hint
  simpa only [hilbDeg, hilbDim, Polynomial.coeff_natDegree] using h

/-- A proper homogeneous prime ideal of `k[X_0,…,X_n]` is contained in the ideal of the
variables. -/
private theorem le_idealOfVars_of_isPrime_of_homogeneous (p : Ideal (MvPolynomial (Fin m) k)) [p.IsPrime]
    (hp : ∀ x ∈ p, ∀ j, MvPolynomial.homogeneousComponent j x ∈ p) :
    p ≤ MvPolynomial.idealOfVars (Fin m) k := by
  intro x hx
  rw [MvPolynomial.idealOfVars, ← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro a ha
  by_cases ha0 : a = 0
  · exfalso
    have hcoeff : x.coeff 0 ≠ 0 := MvPolynomial.mem_support_iff.mp (ha0 ▸ ha)
    have hC : MvPolynomial.C (x.coeff 0) ∈ p := by
      have h := hp x hx 0
      rwa [MvPolynomial.homogeneousComponent_zero] at h
    exact (Ideal.IsPrime.ne_top' (I := p)) (Ideal.eq_top_of_isUnit_mem p hC
      (IsUnit.map MvPolynomial.C (isUnit_iff_ne_zero.mpr hcoeff)))
  · obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp ha0
    exact ⟨i, Set.mem_univ i, hi⟩

/-! ## A homogeneity-proof-free Hilbert polynomial -/

/-- The Hilbert polynomial of the quotient by a homogeneous ideal, as a function of the ideal
alone, so that rewriting the ideal is possible. -/
private noncomputable def idealHilbPoly (J : Ideal (MvPolynomial (Fin m) k)) : Polynomial ℚ :=
  if h : ∃ (_ : ∀ x ∈ J, ∀ j, MvPolynomial.homogeneousComponent j x ∈ J), True then
    hilbPoly J h.choose
  else 0

private theorem idealHilbPoly_eq (J : Ideal (MvPolynomial (Fin m) k))
    (hJ : ∀ x ∈ J, ∀ j, MvPolynomial.homogeneousComponent j x ∈ J) :
    idealHilbPoly J = hilbPoly J hJ := by
  rw [idealHilbPoly, dif_pos (show ∃ (_ : ∀ x ∈ J, ∀ j,
    MvPolynomial.homogeneousComponent j x ∈ J), True from ⟨hJ, trivial⟩)]

/-- The degree of the projective variety `Proj (S ⧸ J)`, for a homogeneous ideal `J`. -/
private noncomputable def idealDeg (J : Ideal (MvPolynomial (Fin m) k)) : ℚ :=
  (idealHilbPoly J).leadingCoeff * ((idealHilbPoly J).natDegree).factorial

private theorem idealDeg_eq (J : Ideal (MvPolynomial (Fin m) k))
    (hJ : ∀ x ∈ J, ∀ j, MvPolynomial.homogeneousComponent j x ∈ J) :
    idealDeg J = hilbDeg J hJ := by
  rw [idealDeg, hilbDeg, hilbDim, idealHilbPoly_eq J hJ]

private theorem idealDeg_nonneg (J : Ideal (MvPolynomial (Fin m) k)) : 0 ≤ idealDeg J := by
  by_cases h : ∃ (_ : ∀ x ∈ J, ∀ j, MvPolynomial.homogeneousComponent j x ∈ J), True
  · rw [idealDeg, idealHilbPoly, dif_pos h]
    exact hilbDeg_nonneg J h.choose
  · rw [idealDeg, idealHilbPoly, dif_neg h]
    simp

private theorem hilbDeg_congr {J : Ideal (MvPolynomial (Fin m) k)}
    (h1 h2 : ∀ x ∈ J, ∀ j, MvPolynomial.homogeneousComponent j x ∈ J) :
    hilbDeg J h1 = hilbDeg J h2 := by
  simp only [hilbDeg, hilbDim, hilbPoly_congr h1 h2]

/-! ## Covering and the local Bezout bound -/

/-- Every minimal prime of `K + (f)` is minimal over `p + (f)` for some minimal prime `p` of `K`. -/
private theorem exists_minimalPrime_le_sup_span_of_mem_minimalPrimes {K : Ideal (MvPolynomial (Fin m) k)}
    {f : MvPolynomial (Fin m) k} {q : Ideal (MvPolynomial (Fin m) k)}
    (hq : q ∈ (K ⊔ Ideal.span {f}).minimalPrimes) :
    ∃ p ∈ K.minimalPrimes, p ≤ q ∧ q ∈ (p ⊔ Ideal.span {f}).minimalPrimes := by
  haveI : q.IsPrime := hq.1.1
  obtain ⟨p, hp, hpq⟩ :=
    Ideal.exists_minimalPrimes_le (I := K) (J := q) (le_trans le_sup_left hq.1.2)
  have hfq : f ∈ q := hq.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
  refine ⟨p, hp, hpq, ⟨⟨‹q.IsPrime›, sup_le hpq ?_⟩, fun y hy hyq => ?_⟩⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff]; exact hfq
  · exact hq.2 ⟨hy.1, sup_le (le_trans hp.1.2 (le_trans le_sup_left hy.2))
      (le_trans le_sup_right hy.2)⟩ hyq

/-- The local Bezout bound, in the proof-free formulation. -/
private theorem sum_idealDeg_minimalPrimes_sup_span_le {p : Ideal (MvPolynomial (Fin m) k)} [p.IsPrime]
    (hp : ∀ x ∈ p, ∀ j, MvPolynomial.homogeneousComponent j x ∈ p)
    {f : MvPolynomial (Fin m) k} (hf : f.IsHomogeneous f.totalDegree) :
    (∑ q : ↥((p ⊔ Ideal.span {f}).minimalPrimes), idealDeg q.1)
      ≤ ((f.totalDegree.max 1 : ℕ) : ℚ) * idealDeg p := by
  classical
  by_cases hfp : f ∈ p
  · have hsup : p ⊔ Ideal.span {f} = p :=
      sup_eq_left.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfp))
    rw [hsup]
    have hmem : p ∈ p.minimalPrimes :=
      ⟨⟨‹p.IsPrime›, le_rfl⟩, fun y hy _ => hy.2⟩
    have hsum : (∑ q : ↥(p.minimalPrimes), idealDeg q.1) = idealDeg p := by
      refine Finset.sum_eq_single (⟨p, hmem⟩ : ↥(p.minimalPrimes)) ?_ ?_
      · intro b _ hb
        have hbp : b.1 = p :=
          le_antisymm (b.2.2 ⟨‹p.IsPrime›, le_rfl⟩ b.2.1.2) b.2.1.2
        exact absurd (Subtype.ext hbp) hb
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hsum]
    have h1 : (1 : ℚ) ≤ ((f.totalDegree.max 1 : ℕ) : ℚ) := by
      have : (1 : ℕ) ≤ f.totalDegree.max 1 := le_max_right _ _
      exact_mod_cast this
    nlinarith [idealDeg_nonneg p]
  · have hK := homogeneousComponent_mem_sup hp (homogeneousComponent_mem_span_singleton hf)
    have hcongr : (∑ q : ↥((p ⊔ Ideal.span {f}).minimalPrimes), idealDeg q.1)
        = ∑ q : ↥((p ⊔ Ideal.span {f}).minimalPrimes),
            hilbDeg q.1 (minimalPrimes_homogeneous _ hK q.2) :=
      Finset.sum_congr rfl fun q _ => idealDeg_eq q.1 (minimalPrimes_homogeneous _ hK q.2)
    rw [hcongr, idealDeg_eq p hp]
    exact sum_hilbDeg_minimalPrimes_sup_span_le hp hf hfp

/-! ## The induction over the generators -/

/-- The degree of the ideal generated by a homogeneous family is at most the product of the
degrees. -/
private theorem sum_idealDeg_span_range_le (hm : 0 < m) :
    ∀ (r : ℕ), r ≤ m → ∀ (G : Fin r → MvPolynomial (Fin m) k),
    (hG : ∀ i, (G i).IsHomogeneous ((G i).totalDegree)) →
    (∑ p : ↥((Ideal.span (Set.range G)).minimalPrimes), idealDeg p.1)
    ≤ ∏ i : Fin r, ((G i).totalDegree.max 1 : ℚ) := by
  intro r
  induction r with
  | zero =>
    intro hr G hG
    have hbot : Ideal.span (Set.range G) = (⊥ : Ideal (MvPolynomial (Fin m) k)) := by
      rw [Set.range_eq_empty G, Ideal.span_empty]
    rw [hbot]
    have hbotproof : ∀ x ∈ (⊥ : Ideal (MvPolynomial (Fin m) k)), ∀ j,
        MvPolynomial.homogeneousComponent j x ∈ (⊥ : Ideal (MvPolynomial (Fin m) k)) :=
      fun x hx j => by rw [Submodule.mem_bot] at hx; simp [hx]
    have hmem : (⊥ : Ideal (MvPolynomial (Fin m) k)) ∈
        (⊥ : Ideal (MvPolynomial (Fin m) k)).minimalPrimes :=
      ⟨⟨Ideal.isPrime_bot, le_rfl⟩, fun y hy _ => hy.2⟩
    have hsum : (∑ q : ↥((⊥ : Ideal (MvPolynomial (Fin m) k)).minimalPrimes), idealDeg q.1)
        = idealDeg (⊥ : Ideal (MvPolynomial (Fin m) k)) := by
      refine Finset.sum_eq_single
        (⟨⊥, hmem⟩ : ↥((⊥ : Ideal (MvPolynomial (Fin m) k)).minimalPrimes)) ?_ ?_
      · intro b _ hb
        have hbp : b.1 = ⊥ :=
          le_antisymm (b.2.2 ⟨Ideal.isPrime_bot, le_rfl⟩ b.2.1.2) b.2.1.2
        exact absurd (Subtype.ext hbp) hb
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hsum, idealDeg_eq (⊥ : Ideal (MvPolynomial (Fin m) k)) hbotproof,
      hilbDeg_congr hbotproof (fun x hx j => by rw [Submodule.mem_bot] at hx; simp [hx]),
      hilbDeg_bot_eq_one hm]
    simp
  | succ r ih =>
    intro hr G hG
    have hr' : r ≤ m := by omega
    let f : MvPolynomial (Fin m) k := G (Fin.last r)
    let G' : Fin r → MvPolynomial (Fin m) k := fun i => G i.castSucc
    have hG' : ∀ i, (G' i).IsHomogeneous ((G' i).totalDegree) := fun i => hG i.castSucc
    have hf : f.IsHomogeneous f.totalDegree := hG (Fin.last r)
    have hspan : Ideal.span (Set.range G) = Ideal.span (Set.range G') ⊔ Ideal.span {f} := by
      have hrange : Set.range G = Set.range G' ∪ {f} := by
        ext x
        constructor
        · rintro ⟨i, rfl⟩
          rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
          · exact Or.inl ⟨j, rfl⟩
          · exact Or.inr rfl
        · rintro (⟨j, rfl⟩ | rfl)
          · exact ⟨j.castSucc, rfl⟩
          · exact ⟨Fin.last r, rfl⟩
      rw [hrange, Ideal.span_union]
    rw [hspan]
    set K' : Ideal (MvPolynomial (Fin m) k) := Ideal.span (Set.range G') with hK'def
    have hK' : ∀ x ∈ K', ∀ j, MvPolynomial.homogeneousComponent j x ∈ K' := by
      have hhom : K'.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin m) k) := by
        rw [hK'def]
        apply Ideal.homogeneous_span
        rintro x ⟨i, rfl⟩
        exact ⟨(G' i).totalDegree, hG' i⟩
      intro x hx j
      exact (MvPolynomial.mem_iff_homogeneousComponent_mem hhom x).mp hx j
    have hcover :
        (∑ q : ↥((K' ⊔ Ideal.span {f}).minimalPrimes), idealDeg q.1)
        ≤ ∑ x : (Σ p : ↥(K'.minimalPrimes), ↥((p.1 ⊔ Ideal.span {f}).minimalPrimes)),
            idealDeg x.2.1 := by
      have hex : ∀ q : ↥((K' ⊔ Ideal.span {f}).minimalPrimes),
          ∃ p : ↥(K'.minimalPrimes),
            p.1 ≤ q.1 ∧ q.1 ∈ (p.1 ⊔ Ideal.span {f}).minimalPrimes := by
        intro q
        obtain ⟨p, hp, hle, hmem⟩ :=
          exists_minimalPrime_le_sup_span_of_mem_minimalPrimes (K := K') (f := f) q.2
        exact ⟨⟨p, hp⟩, hle, hmem⟩
      choose P hPle hPmem using hex
      let Φ : ↥((K' ⊔ Ideal.span {f}).minimalPrimes) →
          (Σ p : ↥(K'.minimalPrimes), ↥((p.1 ⊔ Ideal.span {f}).minimalPrimes)) :=
        fun q => ⟨P q, ⟨q.1, hPmem q⟩⟩
      have hinj : Function.Injective Φ := by
        intro a b hab
        exact Subtype.ext (congrArg (fun z => z.2.1) hab)
      have h1 : (∑ x ∈ (Finset.univ.image Φ), idealDeg x.2.1)
          = ∑ q : ↥((K' ⊔ Ideal.span {f}).minimalPrimes), idealDeg q.1 :=
        Finset.sum_image (f := fun x => idealDeg x.2.1) (s := Finset.univ) (g := Φ)
          (fun a _ b _ hab => hinj hab)
      rw [← h1]
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
      intro x _ _
      exact idealDeg_nonneg x.2.1
    calc (∑ q : ↥((K' ⊔ Ideal.span {f}).minimalPrimes), idealDeg q.1)
        ≤ ∑ x : (Σ p : ↥(K'.minimalPrimes), ↥((p.1 ⊔ Ideal.span {f}).minimalPrimes)),
            idealDeg x.2.1 := hcover
      _ = ∑ p : ↥(K'.minimalPrimes),
            ∑ q : ↥((p.1 ⊔ Ideal.span {f}).minimalPrimes), idealDeg q.1 :=
          Fintype.sum_sigma (f := fun x : (Σ p : ↥(K'.minimalPrimes),
            ↥((p.1 ⊔ Ideal.span {f}).minimalPrimes)) => idealDeg x.2.1)
      _ ≤ ∑ p : ↥(K'.minimalPrimes), ((f.totalDegree.max 1 : ℕ) : ℚ) * idealDeg p.1 := by
          refine Finset.sum_le_sum (fun p _ => ?_)
          haveI : p.1.IsPrime := p.2.1.1
          exact sum_idealDeg_minimalPrimes_sup_span_le (minimalPrimes_homogeneous K' hK' p.2) hf
      _ = ((f.totalDegree.max 1 : ℕ) : ℚ) * ∑ p : ↥(K'.minimalPrimes), idealDeg p.1 := by
          rw [Finset.mul_sum]
      _ ≤ ((f.totalDegree.max 1 : ℕ) : ℚ) * ∏ i : Fin r, ((G' i).totalDegree.max 1 : ℚ) := by
          refine mul_le_mul_of_nonneg_left (ih hr' G' hG') ?_
          positivity
      _ = ∏ i : Fin (r+1), ((G i).totalDegree.max 1 : ℚ) := by
          rw [Fin.prod_univ_castSucc]
          ring

/-- **Main result.** The number of minimal primes of the ideal generated by `n` homogeneous
polynomials of degrees `d i` in `n + 1` variables is at most `∏ i, (d i).max 1`. -/
private theorem card_minimalPrimes_homogeneous_le {k : Type*} [Field k] {n : ℕ}
    (F : Fin n → MvPolynomial (Fin (n+1)) k)
    (hF : ∀ i, (F i).IsHomogeneous ((F i).totalDegree)) :
    Nat.card {p : Ideal (MvPolynomial (Fin (n+1)) k ⧸ Ideal.span (Set.range F)) //
      p ∈ Ideal.minimalPrimes (⊥ : Ideal (MvPolynomial (Fin (n+1)) k ⧸ Ideal.span (Set.range F)))}
      ≤ ∏ i, (F i).totalDegree.max 1 := by
  rw [← natCard_minimalPrimes_quotient (Ideal.span (Set.range F))]
  set I : Ideal (MvPolynomial (Fin (n+1)) k) := Ideal.span (Set.range F) with hI
  have hIhom : ∀ x ∈ I, ∀ j, MvPolynomial.homogeneousComponent j x ∈ I := by
    have hhom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n+1)) k) := by
      rw [hI]
      apply Ideal.homogeneous_span
      rintro x ⟨i, rfl⟩
      exact ⟨(F i).totalDegree, hF i⟩
    intro x hx j
    exact (MvPolynomial.mem_iff_homogeneousComponent_mem hhom x).mp hx j
  by_cases hM : MvPolynomial.idealOfVars (Fin (n+1)) k ∈ I.minimalPrimes
  · have hsingle : I.minimalPrimes = {MvPolynomial.idealOfVars (Fin (n+1)) k} := by
      ext q
      constructor
      · intro hq
        have hqhom := minimalPrimes_homogeneous I hIhom hq
        haveI : q.IsPrime := hq.1.1
        have hqle : q ≤ MvPolynomial.idealOfVars (Fin (n+1)) k :=
          le_idealOfVars_of_isPrime_of_homogeneous q hqhom
        have hmle : MvPolynomial.idealOfVars (Fin (n+1)) k ≤ q := hM.2 hq.1 hqle
        exact Set.mem_singleton_iff.mpr (le_antisymm hqle hmle)
      · intro hq
        exact Set.mem_singleton_iff.mp hq ▸ hM
    rw [hsingle]
    have hcard : Nat.card ↥({MvPolynomial.idealOfVars (Fin (n+1)) k} :
        Set (Ideal (MvPolynomial (Fin (n+1)) k))) = 1 := by simp
    rw [hcard]
    exact Finset.one_le_prod (s := Finset.univ) fun i _ => le_max_right _ _
  · have hone : ∀ p : ↥(I.minimalPrimes), (1 : ℚ) ≤ idealDeg p.1 := by
      intro p
      haveI : p.1.IsPrime := p.2.1.1
      have hphom := minimalPrimes_homogeneous I hIhom p.2
      have hpne : p.1 ≠ MvPolynomial.idealOfVars (Fin (n+1)) k :=
        fun hcon => hM (hcon ▸ p.2)
      rw [idealDeg_eq p.1 hphom]
      exact one_le_hilbDeg p.1 hphom hpne
    have hcard : (∑ p : ↥(I.minimalPrimes), (1 : ℚ)) = (Nat.card ↥(I.minimalPrimes) : ℚ) := by
      rw [Nat.card_eq_fintype_card, Finset.sum_const, Finset.card_univ]
      simp [nsmul_eq_mul]
    have hle : (Nat.card ↥(I.minimalPrimes) : ℚ) ≤
        ∑ p : ↥(I.minimalPrimes), idealDeg p.1 := by
      have h2 := Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset ↥(I.minimalPrimes))) =>
        hone p)
      rwa [hcard] at h2
    have h3 := le_trans hle
      (sum_idealDeg_span_range_le (k := k) (m := n+1) (by omega) n (Nat.le_succ n) F hF)
    exact_mod_cast h3

end

end Commons.RingTheory.Ideal

end


-- ==== from Submission.Commons.RingTheory.Ideal.card_minimalPrimes_quotient_eq ====
section

namespace Commons.RingTheory.Ideal

private theorem card_minimalPrimes_quotient_eq {R : Type*} [CommRing R] (I : Ideal R) :
    Nat.card {q : Ideal (R ⧸ I) // q ∈ Ideal.minimalPrimes (⊥ : Ideal (R ⧸ I))}
      = Nat.card {p : Ideal R // p ∈ I.minimalPrimes} := by
  let mk := Ideal.Quotient.mk I
  have hker : RingHom.ker mk = I := Ideal.mk_ker
  have hforward : ∀ p : Ideal R, p ∈ I.minimalPrimes →
      p.map mk ∈ Ideal.minimalPrimes (⊥ : Ideal (R ⧸ I)) := by
    intro p hp
    have hpprime : p.IsPrime := hp.isPrime
    have hple : I ≤ p := hp.le
    have hpmin : ∀ y : Ideal R, y.IsPrime → I ≤ y → y ≤ p → p ≤ y :=
      fun y hy hyI hyple => hp.2 ⟨hy, hyI⟩ hyple

    show (⊥ : Ideal (R ⧸ I)).IsMinimalPrime (p.map mk)
    refine ⟨⟨Ideal.isPrime_map_quotientMk_of_isPrime hple, bot_le⟩, ?_⟩
    intro q hq hle
    have hqprime : q.IsPrime := hq.1

    have hcomapprime : (q.comap mk).IsPrime := inferInstance
    have hIle : I ≤ q.comap mk :=
      le_trans (le_of_eq hker.symm) (Ideal.ker_le_comap mk)
    have hle' : q.comap mk ≤ p := by
      rw [← Ideal.comap_map_mk hple]
      exact Ideal.comap_mono hle
    have hpge : p ≤ q.comap mk := hpmin (q.comap mk) hcomapprime hIle hle'
    have heq : q.comap mk = p := le_antisymm hle' hpge
    have heq2 : p.map mk = q := by
      rw [← heq, Ideal.map_comap_of_surjective mk Ideal.Quotient.mk_surjective]
    exact le_of_eq heq2
  have hbackward : ∀ q : Ideal (R ⧸ I), q ∈ Ideal.minimalPrimes (⊥ : Ideal (R ⧸ I)) →
      q.comap mk ∈ I.minimalPrimes := by
    intro q hq
    have hqprime : q.IsPrime := hq.isPrime
    have hqmin : ∀ y : Ideal (R ⧸ I), y.IsPrime → y ≤ q → q ≤ y :=
      fun y hy hyq => hq.2 ⟨hy, bot_le⟩ hyq

    show I.IsMinimalPrime (q.comap mk)
    refine ⟨⟨inferInstance, ?_⟩, ?_⟩
    · exact le_trans (le_of_eq hker.symm) (Ideal.ker_le_comap mk)
    · intro r hr hle
      have hrprime : r.IsPrime := hr.1
      have hrI : I ≤ r := hr.2

      have hrmap : (r.map mk).IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hrI
      have hle' : r.map mk ≤ q :=
        (Ideal.map_mono hle).trans
          (le_of_eq (Ideal.map_comap_of_surjective mk Ideal.Quotient.mk_surjective q))
      have hqle : q ≤ r.map mk := hqmin (r.map mk) hrmap hle'
      have heq : r.map mk = q := le_antisymm hle' hqle
      have heq2 : q.comap mk = r := by
        rw [← heq, Ideal.comap_map_mk hrI]
      exact le_of_eq heq2
  refine Nat.card_congr ?_
  refine
    { toFun := fun q => ⟨q.1.comap mk, hbackward q.1 q.2⟩
      invFun := fun p => ⟨p.1.map mk, hforward p.1 p.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro q
    exact Subtype.ext (Ideal.map_comap_of_surjective mk Ideal.Quotient.mk_surjective q.1)
  · intro p
    exact Subtype.ext (Ideal.comap_map_mk p.2.le)

end Commons.RingTheory.Ideal
end


-- ==== from Submission.Commons.RingTheory.Ideal.card_minimalPrimes_comap_eq ====
section

set_option linter.style.haveILetI false

namespace Commons.RingTheory.Ideal

/-- If `φ : A →+* B` is surjective and `q` is a minimal prime over `I ≤ B`, then the contraction
`q.comap φ` is a minimal prime over `I.comap φ`. -/
private theorem minimalPrimes_comap_of_surjective {A B : Type*} [CommSemiring A] [CommSemiring B]
    (φ : A →+* B) (hφ : Function.Surjective φ) {I q : Ideal B} (hq : q ∈ I.minimalPrimes) :
    Ideal.comap φ q ∈ (I.comap φ).minimalPrimes := by
  haveI : q.IsPrime := hq.isPrime
  refine ⟨⟨inferInstance, Ideal.comap_mono hq.le⟩, ?_⟩
  intro r hr hle
  haveI : r.IsPrime := hr.1
  obtain ⟨r₀, hr₀, hr₀le⟩ := Ideal.exists_minimalPrimes_le (I := I.comap φ) (J := r) hr.2
  obtain ⟨q₀, hq₀, hq₀eq⟩ := Ideal.exists_minimalPrimes_comap_eq φ r₀ hr₀
  have hle₀ : q₀ ≤ q :=
    (Ideal.comap_le_comap_iff_of_surjective φ hφ q₀ q).1 (by rw [hq₀eq]; exact hr₀le.trans hle)
  have hge : q ≤ q₀ := hq.2 ⟨hq₀.isPrime, hq₀.le⟩ hle₀
  have hEq : r₀ = Ideal.comap φ q := by rw [← hq₀eq, le_antisymm hle₀ hge]
  rw [hEq] at hr₀le
  exact hr₀le

private theorem card_minimalPrimes_comap_eq {A B : Type*} [CommSemiring A] [CommSemiring B] (φ : A →+* B)
    (hφ : Function.Surjective φ) (I : Ideal B) :
    Nat.card {p : Ideal A // p ∈ (I.comap φ).minimalPrimes} =
      Nat.card {p : Ideal B // p ∈ I.minimalPrimes} := by
  refine Nat.card_congr ?_
  let fwd : {p : Ideal A // p ∈ (I.comap φ).minimalPrimes} →
      {p : Ideal B // p ∈ I.minimalPrimes} := fun p =>
    ⟨Classical.choose (Ideal.exists_minimalPrimes_comap_eq φ p.1 p.2),
      (Classical.choose_spec (Ideal.exists_minimalPrimes_comap_eq φ p.1 p.2)).1⟩
  have hfwd : ∀ p, Ideal.comap φ (fwd p).1 = p.1 := fun p =>
    (Classical.choose_spec (Ideal.exists_minimalPrimes_comap_eq φ p.1 p.2)).2
  refine
    { toFun := fwd
      invFun := fun q => ⟨Ideal.comap φ q.1, minimalPrimes_comap_of_surjective φ hφ q.2⟩
      left_inv := fun p => Subtype.ext (hfwd p)
      right_inv := ?_ }
  intro q
  apply Subtype.ext
  apply Ideal.comap_injective_of_surjective φ hφ
  rw [hfwd ⟨Ideal.comap φ q.1, minimalPrimes_comap_of_surjective φ hφ q.2⟩]

end Commons.RingTheory.Ideal

end


-- ==== from Submission.Commons.RingTheory.Ideal.isPrime_sup_span_X_sub_one ====
section

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
open MvPolynomial

namespace Commons.RingTheory.Ideal

section HomogeneousAeval

variable {k T : Type*} [CommSemiring k] [CommSemiring T] [Algebra k T] {n : ℕ}
local notation "R" => MvPolynomial (Fin (n+1)) k

private theorem monomial_aeval
    [Algebra R T] [IsScalarTower k R T]
    (y : T) (hy : algebraMap R T (MvPolynomial.X 0) * y = 1)
    (s : Fin (n+1) →₀ ℕ) (c : k) :
    MvPolynomial.aeval (fun i : Fin (n+1) => if i = 0 then (1 : T) else algebraMap R T (MvPolynomial.X i) * y)
        (MvPolynomial.monomial s c)
      = algebraMap R T (MvPolynomial.monomial s c) * y ^ s.degree := by
  rw [MvPolynomial.aeval_monomial]
  have hg : ∀ i : Fin (n+1),
      (if i = 0 then (1 : T) else algebraMap R T (MvPolynomial.X i) * y)
        = algebraMap R T (MvPolynomial.X i) * y := by
    intro i
    by_cases hi : i = 0
    · subst hi
      simpa using hy.symm
    · simp only [if_neg hi]
  have hL : s.prod (fun i e => (if i = 0 then (1 : T) else algebraMap R T (MvPolynomial.X i) * y) ^ e)
      = s.prod (fun i e => (algebraMap R T (MvPolynomial.X i) * y) ^ e) :=
    Finsupp.prod_congr (fun i _ => by rw [hg i])
  rw [hL]
  rw [Finsupp.prod_pow]
  have hstep : (∏ i, (algebraMap R T (MvPolynomial.X i) * y) ^ (s i))
      = (∏ i, (algebraMap R T (MvPolynomial.X i)) ^ (s i)) * (∏ i, y ^ (s i)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [mul_pow]
  rw [hstep]
  rw [show (∏ i : Fin (n+1), y ^ (s i)) = y ^ (∑ i, s i) by
    rw [Finset.prod_pow_eq_pow_sum]]
  rw [Finsupp.degree_eq_sum]
  have hAmono : algebraMap R T (MvPolynomial.monomial s c)
      = (algebraMap k T) c * ∏ i, (algebraMap R T (MvPolynomial.X i)) ^ (s i) := by
    rw [MvPolynomial.monomial_eq]
    rw [show s.prod (fun i e => MvPolynomial.X i ^ e) = ∏ i, (MvPolynomial.X i) ^ (s i) by
      rw [Finsupp.prod_pow]]
    rw [map_mul, map_prod]
    congr 1
    · rw [MvPolynomial.C_eq_algebraMap]
      exact (IsScalarTower.algebraMap_apply k R T c).symm
    · apply Finset.prod_congr rfl
      intro i _
      rw [map_pow]
  rw [hAmono]
  ring

private theorem aeval_homogeneous_eq
    [Algebra R T] [IsScalarTower k R T]
    (y : T) (hy : algebraMap R T (MvPolynomial.X 0) * y = 1)
    {f : R} {d : ℕ} (hf : f.IsHomogeneous d) :
    MvPolynomial.aeval (fun i : Fin (n+1) => if i = 0 then (1 : T) else algebraMap R T (MvPolynomial.X i) * y) f
      = algebraMap R T f * y ^ d := by
  have hdeg : ∀ v ∈ f.support, v.degree = d := by
    intro v hv
    rw [Finsupp.degree_apply]
    exact (hf.degree_eq_sum_deg_support hv).symm
  conv_lhs => rw [MvPolynomial.as_sum f]
  rw [map_sum]
  rw [Finset.sum_congr rfl (fun v hv => by rw [monomial_aeval y hy v (MvPolynomial.coeff v f)])]
  rw [Finset.sum_congr rfl (fun v hv => by rw [hdeg v hv])]
  rw [← Finset.sum_mul]
  congr 1
  rw [← map_sum, ← MvPolynomial.as_sum]

private theorem aeval_eq_sum_homogeneousComponent
    [Algebra R T] [IsScalarTower k R T]
    (y : T) (hy : algebraMap R T (MvPolynomial.X 0) * y = 1)
    (f : R) :
    MvPolynomial.aeval (fun i : Fin (n+1) => if i = 0 then (1 : T) else algebraMap R T (MvPolynomial.X i) * y) f
      = ∑ d ∈ Finset.range (f.totalDegree + 1),
          algebraMap R T (MvPolynomial.homogeneousComponent d f) * y ^ d := by
  conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent f]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [aeval_homogeneous_eq y hy (MvPolynomial.homogeneousComponent_isHomogeneous d f)]

end HomogeneousAeval

section Main
variable {k : Type*} [Field k] {n : ℕ}
local notation "R" => MvPolynomial (Fin (n+1)) k

private theorem isPrime_sup_span_X_sub_one_aux
    (Q : Ideal R) [Q.IsPrime]
    (hQ : ∀ x ∈ Q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ Q)
    (hX : (MvPolynomial.X 0 : R) ∉ Q) :
    (Q ⊔ Ideal.span {(MvPolynomial.X 0 : R) - 1}).IsPrime := by
  classical
  let S := Localization.Away (MvPolynomial.X 0 : R)
  haveI hSaway : IsLocalization.Away (MvPolynomial.X 0 : R) S := inferInstance
  let y : S := IsLocalization.Away.invSelf (MvPolynomial.X 0 : R)
  have hy : algebraMap R S (MvPolynomial.X 0) * y = 1 := IsLocalization.Away.mul_invSelf _
  -- disjointness of powers of X0 from Q
  have hdisj : Disjoint (Submonoid.powers (MvPolynomial.X 0 : R) : Set R) (Q : Set R) := by
    rw [Set.disjoint_left]
    intro m hm hmQ
    obtain ⟨j, rfl⟩ := (Submonoid.mem_powers_iff m (MvPolynomial.X 0)).mp hm
    exact hX (Ideal.IsPrime.mem_of_pow_mem ‹Q.IsPrime› j hmQ)
  -- QS is prime, so S ⧸ QS is a domain
  set QS : Ideal S := Q.map (algebraMap R S) with hQSdef
  haveI hQSprime : QS.IsPrime := by
    rw [hQSdef]
    exact IsLocalization.isPrime_of_isPrime_disjoint
      (Submonoid.powers (MvPolynomial.X 0 : R)) S Q ‹Q.IsPrime› hdisj
  haveI : IsDomain (S ⧸ QS) := inferInstance
  -- the substitution map
  let ρa : R →ₐ[k] S := MvPolynomial.aeval
    (fun i : Fin (n+1) => if i = 0 then (1 : S) else algebraMap R S (MvPolynomial.X i) * y)
  let g' : R →+* (S ⧸ QS) := (Ideal.Quotient.mk QS).comp ρa.toRingHom
  -- X0 - 1 ∈ ker g'
  have hX0ker : (MvPolynomial.X 0 : R) - 1 ∈ RingHom.ker g' := by
    rw [RingHom.mem_ker]
    have h1 : ρa ((MvPolynomial.X 0 : R) - 1) = 0 := by
      rw [map_sub, map_one]
      have : ρa (MvPolynomial.X 0 : R) = 1 := by
        change MvPolynomial.aeval _ (MvPolynomial.X 0) = 1
        rw [MvPolynomial.aeval_X]
        simp
      rw [this, sub_self]
    show g' ((MvPolynomial.X 0 : R) - 1) = 0
    rw [show g' ((MvPolynomial.X 0 : R) - 1) = Ideal.Quotient.mk QS (ρa ((MvPolynomial.X 0 : R) - 1)) from rfl, h1, map_zero]
  have hspan_le : Ideal.span {(MvPolynomial.X 0 : R) - 1} ≤ RingHom.ker g' := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hX0ker
  -- Q ⊆ ker g'
  have hQ_le : Q ≤ RingHom.ker g' := by
    intro q hq
    rw [RingHom.mem_ker]
    have hmem : ρa q ∈ QS := by
      have hsum : ρa q = ∑ d ∈ Finset.range (q.totalDegree + 1),
          algebraMap R S (MvPolynomial.homogeneousComponent d q) * y ^ d :=
        aeval_eq_sum_homogeneousComponent y hy q
      rw [hsum]
      apply Ideal.sum_mem
      intro d _
      exact Ideal.mul_mem_right _ QS (Ideal.mem_map_of_mem (algebraMap R S) (hQ q hq d))
    show g' q = 0
    rw [show g' q = Ideal.Quotient.mk QS (ρa q) from rfl, Ideal.Quotient.eq_zero_iff_mem.mpr hmem]
  -- ker g' ⊆ Q ⊔ span{X0 - 1}
  have hker_le : RingHom.ker g' ≤ Q ⊔ Ideal.span {(MvPolynomial.X 0 : R) - 1} := by
    intro f hf
    rw [RingHom.mem_ker] at hf
    have hmem : ρa f ∈ QS := Ideal.Quotient.eq_zero_iff_mem.mp hf
    let N := f.totalDegree
    let F : ℕ → R := fun i => MvPolynomial.homogeneousComponent i f
    set H : R := ∑ d ∈ Finset.range (N+1),
      F d * (MvPolynomial.X 0)^(N - d) with hHdef
    have hzy : y * (algebraMap R S (MvPolynomial.X 0)) = 1 := by
      rw [mul_comm]; exact hy
    have hpowy : ∀ d ≤ N, y^d * (algebraMap R S (MvPolynomial.X 0))^N
        = (algebraMap R S (MvPolynomial.X 0))^(N-d) := by
      intro d hd
      have h1 : (algebraMap R S (MvPolynomial.X 0))^N
          = (algebraMap R S (MvPolynomial.X 0))^d * (algebraMap R S (MvPolynomial.X 0))^(N-d) := by
        rw [← pow_add, Nat.add_sub_of_le hd]
      rw [h1, ← mul_assoc, ← mul_pow, hzy, one_pow, one_mul]
    have hAH : algebraMap R S H = ρa f * (algebraMap R S (MvPolynomial.X 0))^N := by
      have hsum : ρa f = ∑ d ∈ Finset.range (N + 1),
          algebraMap R S (MvPolynomial.homogeneousComponent d f) * y ^ d :=
        aeval_eq_sum_homogeneousComponent y hy f
      rw [hsum, Finset.sum_mul, hHdef]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mem_range] at hd
      have hdN : d ≤ N := Nat.lt_succ_iff.mp hd
      have hL : algebraMap R S (MvPolynomial.homogeneousComponent d f * (MvPolynomial.X 0)^(N - d))
          = algebraMap R S (MvPolynomial.homogeneousComponent d f)
            * (algebraMap R S (MvPolynomial.X 0))^(N-d) := by
        rw [map_mul, map_pow]
      have hR : (algebraMap R S (MvPolynomial.homogeneousComponent d f) * y^d)
            * (algebraMap R S (MvPolynomial.X 0))^N
          = algebraMap R S (MvPolynomial.homogeneousComponent d f)
            * (algebraMap R S (MvPolynomial.X 0))^(N-d) := by
        rw [mul_assoc, hpowy d hdN]
      rw [hL, hR]
    have hunder : QS.under R = Q := by
      rw [hQSdef]
      exact IsLocalization.under_map_of_isPrime_disjoint
        (Submonoid.powers (MvPolynomial.X 0 : R)) S (inferInstance : Q.IsPrime) hdisj
    have hH_mem : H ∈ Q := by
      rw [← hunder, Ideal.mem_under]
      rw [hAH]
      exact Ideal.mul_mem_right _ QS hmem
    have hf_diff : f - H ∈ Ideal.span {(MvPolynomial.X 0 : R) - 1} := by
      have hsplit : f - H = ∑ d ∈ Finset.range (N+1),
          F d * (1 - (MvPolynomial.X 0)^(N-d)) := by
        have hF : f = ∑ i ∈ Finset.range (N+1), F i := by
          change f = ∑ i ∈ Finset.range (N+1), MvPolynomial.homogeneousComponent i f
          simpa using (MvPolynomial.sum_homogeneousComponent f).symm
        calc f - H
            = (∑ i ∈ Finset.range (N+1), F i) - H := by rw [hF]
          _ = (∑ i ∈ Finset.range (N+1), F i)
                - (∑ d ∈ Finset.range (N+1), F d * (MvPolynomial.X 0)^(N-d)) := by rw [hHdef]
          _ = ∑ d ∈ Finset.range (N+1), (F d - F d * (MvPolynomial.X 0)^(N-d)) := by rw [Finset.sum_sub_distrib]
          _ = ∑ d ∈ Finset.range (N+1), F d * (1 - (MvPolynomial.X 0)^(N-d)) := by
              apply Finset.sum_congr rfl
              intro d _
              ring
      rw [hsplit]
      apply Ideal.sum_mem
      intro d _
      apply Ideal.mul_mem_left
      rw [Ideal.mem_span_singleton]
      use -(∑ i ∈ Finset.range (N-d), (MvPolynomial.X 0)^i)
      rw [← geom_sum_mul_neg (MvPolynomial.X 0) (N-d)]
      ring
    have : f = H + (f - H) := by ring
    rw [this]
    refine Ideal.add_mem _ ?_ ?_
    · exact (le_sup_left : Q ≤ Q ⊔ Ideal.span {(MvPolynomial.X 0 : R) - 1}) hH_mem
    · exact (le_sup_right : Ideal.span {(MvPolynomial.X 0 : R) - 1} ≤ Q ⊔ Ideal.span {(MvPolynomial.X 0 : R) - 1}) hf_diff
  have hker : RingHom.ker g' = Q ⊔ Ideal.span {(MvPolynomial.X 0 : R) - 1} :=
    le_antisymm hker_le (sup_le hQ_le hspan_le)
  have e : R ⧸ (Q ⊔ Ideal.span {(MvPolynomial.X 0 : R) - 1}) ≃+* ↥g'.range :=
    hker ▸ RingHom.quotientKerEquivRange g'
  let ψ : R ⧸ (Q ⊔ Ideal.span {(MvPolynomial.X 0 : R) - 1}) →+* (S ⧸ QS) :=
    (Subring.subtype g'.range).comp e.toRingHom
  have hinj : Function.Injective ψ := by
    intro a b hab
    exact e.injective (Subtype.ext hab)
  haveI : IsDomain (R ⧸ (Q ⊔ Ideal.span {(MvPolynomial.X 0 : R) - 1})) :=
    Function.Injective.isDomain ψ hinj
  exact (Ideal.Quotient.isDomain_iff_prime _).mp ‹IsDomain (R ⧸ (Q ⊔ Ideal.span {(MvPolynomial.X 0 : R) - 1}))›

end Main

/-- If `Q` is a homogeneous prime ideal of `k[X₀,…,Xₙ]` with `X₀ ∉ Q`, then the ideal
`Q + (X₀ - 1)` is prime: it is the ideal of the affine chart `X₀ = 1` of the projective
variety cut out by `Q`. -/
private theorem isPrime_sup_span_X_sub_one {k : Type*} [Field k] {n : ℕ}
    (Q : Ideal (MvPolynomial (Fin (n+1)) k)) [Q.IsPrime]
    (hQ : ∀ x ∈ Q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ Q)
    (hX : (MvPolynomial.X 0 : MvPolynomial (Fin (n+1)) k) ∉ Q) :
    (Q ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (n+1)) k) - 1}).IsPrime :=
  isPrime_sup_span_X_sub_one_aux Q hQ hX

end Commons.RingTheory.Ideal
end


-- ==== from Submission.Commons.Algebra.MvPolynomial.surjective_aeval_dehom ====
section

namespace Commons.Algebra.MvPolynomial

private theorem surjective_aeval_dehom {k : Type*} [Field k] (r : ℕ) :
    Function.Surjective (MvPolynomial.aeval (fun i : Fin (r+1) => Fin.cases (1 : MvPolynomial (Fin r) k) (fun j => MvPolynomial.X j) i) :
      MvPolynomial (Fin (r+1)) k →ₐ[k] MvPolynomial (Fin r) k) := by
  intro p
  refine ⟨MvPolynomial.rename Fin.succ p, ?_⟩
  rw [MvPolynomial.aeval_rename]
  have h : (fun i : Fin (r+1) => Fin.cases (1 : MvPolynomial (Fin r) k) (fun j => MvPolynomial.X j) i) ∘ Fin.succ
        = fun j : Fin r => MvPolynomial.X j := by
    funext j
    simp [Function.comp_apply]
  rw [h]
  exact MvPolynomial.aeval_X_left_apply p

end Commons.Algebra.MvPolynomial
end


-- ==== from Submission.Commons.Algebra.MvPolynomial.ker_aeval_dehom ====
section

namespace Commons.Algebra.MvPolynomial

/-- The kernel of evaluation of a one-variable polynomial at an element `a` of a commutative
ring is the principal ideal generated by `X - C a`. -/
private theorem ker_evalRingHom_eq_span {R : Type*} [CommRing R] (a : R) :
    RingHom.ker (Polynomial.evalRingHom a) = Ideal.span {Polynomial.X - Polynomial.C a} := by
  ext q
  rw [RingHom.mem_ker, Ideal.mem_span_singleton, Polynomial.dvd_iff_isRoot]
  rfl

/-- The algebra map `k[X₀, …, X_r] → k[X₁, …, X_r]`, `X₀ ↦ 1`, `X_{j+1} ↦ X_j`, agrees with
the composition of `finSuccEquiv` and evaluation of a univariate polynomial at `1` (as ring
homomorphisms). -/
private theorem aeval_dehom_eq_evalRingHom_comp {k : Type*} [Field k] (r : ℕ) :
    (MvPolynomial.aeval (fun i : Fin (r+1) =>
      Fin.cases (1 : MvPolynomial (Fin r) k) (fun j => MvPolynomial.X j) i)).toRingHom
    = (Polynomial.evalRingHom (1 : MvPolynomial (Fin r) k)).comp
        (MvPolynomial.finSuccEquiv k r :
          MvPolynomial (Fin (r+1)) k →+* Polynomial (MvPolynomial (Fin r) k)) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply]
    rw [MvPolynomial.finSuccEquiv_eq]
    simp [MvPolynomial.eval₂Hom_C]
  · intro i
    induction i using Fin.cases with
    | zero =>
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe]
      rw [MvPolynomial.finSuccEquiv_eq]
      simp [MvPolynomial.eval₂Hom_X']
    | succ j =>
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe]
      rw [MvPolynomial.finSuccEquiv_eq]
      simp [MvPolynomial.eval₂Hom_X']

/-- Pointwise form of `aeval_dehom_eq_evalRingHom_comp`. -/
private theorem aeval_dehom_apply {k : Type*} [Field k] (r : ℕ) (p : MvPolynomial (Fin (r+1)) k) :
    MvPolynomial.aeval (fun i : Fin (r+1) =>
        Fin.cases (1 : MvPolynomial (Fin r) k) (fun j => MvPolynomial.X j) i) p
      = Polynomial.eval (1 : MvPolynomial (Fin r) k) (MvPolynomial.finSuccEquiv k r p) := by
  have h := RingHom.congr_fun (aeval_dehom_eq_evalRingHom_comp (k := k) r) p
  rw [RingHom.comp_apply] at h
  simpa [Polynomial.coe_evalRingHom] using h

private theorem ker_aeval_dehom {k : Type*} [Field k] (r : ℕ) :
    RingHom.ker (MvPolynomial.aeval (fun i : Fin (r+1) => Fin.cases (1 : MvPolynomial (Fin r) k) (fun j => MvPolynomial.X j) i) :
      MvPolynomial (Fin (r+1)) k →ₐ[k] MvPolynomial (Fin r) k).toRingHom =
        Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (r+1)) k) - 1} := by
  apply le_antisymm
  · intro p hp
    rw [RingHom.mem_ker] at hp
    rw [Ideal.mem_span_singleton]
    have hp' : Polynomial.eval (1 : MvPolynomial (Fin r) k)
        (MvPolynomial.finSuccEquiv k r p) = 0 := by
      rw [← aeval_dehom_apply (k := k) r p]
      exact hp
    have hdiv : (Polynomial.X - 1 : Polynomial (MvPolynomial (Fin r) k)) ∣
        MvPolynomial.finSuccEquiv k r p := by
      simpa using (Polynomial.dvd_iff_isRoot (p := MvPolynomial.finSuccEquiv k r p)
        (a := (1 : MvPolynomial (Fin r) k))).mpr hp'
    obtain ⟨q, hq⟩ := hdiv
    have hsymm : (MvPolynomial.finSuccEquiv k r).symm
        (Polynomial.X - 1 : Polynomial (MvPolynomial (Fin r) k)) =
          (MvPolynomial.X 0 : MvPolynomial (Fin (r+1)) k) - 1 := by
      rw [AlgEquiv.symm_apply_eq, map_sub, map_one, MvPolynomial.finSuccEquiv_X_zero]
    refine ⟨(MvPolynomial.finSuccEquiv k r).symm q, ?_⟩
    calc p = (MvPolynomial.finSuccEquiv k r).symm (MvPolynomial.finSuccEquiv k r p) :=
            (AlgEquiv.symm_apply_apply _ _).symm
      _ = (MvPolynomial.finSuccEquiv k r).symm
            ((Polynomial.X - 1 : Polynomial (MvPolynomial (Fin r) k)) * q) := by rw [hq]
      _ = (MvPolynomial.finSuccEquiv k r).symm
            (Polynomial.X - 1 : Polynomial (MvPolynomial (Fin r) k)) *
            (MvPolynomial.finSuccEquiv k r).symm q := by rw [map_mul]
      _ = ((MvPolynomial.X 0 : MvPolynomial (Fin (r+1)) k) - 1) *
            (MvPolynomial.finSuccEquiv k r).symm q := by rw [hsymm]
  · rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    simp [RingHom.mem_ker, Fin.cases_zero]

end Commons.Algebra.MvPolynomial
end


-- ==== from Submission.Commons.Algebra.MvPolynomial.exists_homogenization ====
section

namespace Commons.Algebra.MvPolynomial

open _root_.MvPolynomial

private theorem exists_homogenization {k : Type*} [Field k] {r : ℕ} (f : MvPolynomial (Fin r) k) :
    ∃ F : MvPolynomial (Fin (r+1)) k,
      (F.IsHomogeneous F.totalDegree) ∧ F.totalDegree ≤ f.totalDegree ∧
      (MvPolynomial.aeval (fun i : Fin (r+1) => Fin.cases (1 : MvPolynomial (Fin r) k) (fun j => MvPolynomial.X j) i) F = f) := by
  set ψ : Fin (r+1) → MvPolynomial (Fin r) k :=
    (fun i => Fin.cases (1 : MvPolynomial (Fin r) k) (fun j => MvPolynomial.X j) i) with hψ
  let F : MvPolynomial (Fin (r+1)) k :=
    ∑ n ∈ Finset.range (f.totalDegree + 1),
      rename (Fin.succ : Fin r → Fin (r+1)) (homogeneousComponent n f) *
        X (0 : Fin (r+1)) ^ (f.totalDegree - n)
  have hhom : F.IsHomogeneous f.totalDegree := by
    dsimp only [F]
    apply IsHomogeneous.sum
    intro n hn
    have hnle : n ≤ f.totalDegree := by
      have := Finset.mem_range.mp hn; omega
    have h1 : (rename (Fin.succ : Fin r → Fin (r+1)) (homogeneousComponent n f)).IsHomogeneous n :=
      (homogeneousComponent_isHomogeneous n f).rename_isHomogeneous
    have h2 : ((X (R := k) (0 : Fin (r+1))) ^ (f.totalDegree - n)).IsHomogeneous (f.totalDegree - n) := by
      simpa using (isHomogeneous_X (R := k) (0 : Fin (r+1))).pow (f.totalDegree - n)
    have h3 := h1.mul h2
    rwa [Nat.add_sub_cancel' hnle] at h3
  refine ⟨F, ?_, ?_, ?_⟩
  · rcases eq_or_ne F 0 with h | h
    · rw [h, MvPolynomial.totalDegree_zero]
      exact isHomogeneous_zero _ _ _
    · rw [hhom.totalDegree h]; exact hhom
  · exact hhom.totalDegree_le
  · have hcomp : ψ ∘ (Fin.succ : Fin r → Fin (r+1)) = (MvPolynomial.X : Fin r → MvPolynomial (Fin r) k) := by
      funext j
      simp only [Function.comp_apply, hψ, Fin.cases_succ]
    have h0 : ψ (0 : Fin (r+1)) = 1 := by
      simp only [hψ, Fin.cases_zero]
    have h_eval : ∀ n, aeval ψ (rename (Fin.succ : Fin r → Fin (r+1)) (homogeneousComponent n f) *
        X (0 : Fin (r+1)) ^ (f.totalDegree - n)) = homogeneousComponent n f := by
      intro n
      rw [map_mul, map_pow, aeval_rename, aeval_X, hcomp, aeval_X_left_apply, h0, one_pow, mul_one]
    dsimp only [F]
    rw [map_sum]
    have hsum : ∑ x ∈ Finset.range (f.totalDegree + 1),
        aeval ψ (rename (Fin.succ : Fin r → Fin (r+1)) (homogeneousComponent x f) *
          X (0 : Fin (r+1)) ^ (f.totalDegree - x))
        = ∑ x ∈ Finset.range (f.totalDegree + 1), homogeneousComponent x f :=
      Finset.sum_congr rfl (fun n _ => h_eval n)
    rw [hsum, sum_homogeneousComponent f]

end Commons.Algebra.MvPolynomial
end


-- ==== from Submission.Commons.Algebra.MvPolynomial.span_range_homogeneousComponent_mem ====
section

namespace Commons.Algebra.MvPolynomial

-- The total-degree grading on `MvPolynomial` (the family of submodules
-- `MvPolynomial.homogeneousSubmodule σ R`) is deliberately *not* registered as a global
-- instance by Mathlib, since one may want to use another grading.  We bring it into scope
-- locally so that the graded-ring theory applies below.
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The ideal generated by a family of homogeneous polynomials is a homogeneous ideal:
the `j`-th homogeneous component of any element of `Ideal.span (Set.range F)` again lies in
that ideal.

Since an ideal generated by homogeneous elements is automatically homogeneous (here via
`Ideal.homogeneous_span`), this is exactly the characterization
`MvPolynomial.mem_iff_homogeneousComponent_mem` of homogeneous ideals. -/
private theorem span_range_homogeneousComponent_mem {k : Type*} [Field k] {r : ℕ} (F : Fin r → MvPolynomial (Fin (r+1)) k)
    (hF : ∀ i, (F i).IsHomogeneous ((F i).totalDegree)) :
    ∀ x ∈ Ideal.span (Set.range F), ∀ j, MvPolynomial.homogeneousComponent j x ∈ Ideal.span (Set.range F) := by
  -- The generators `F i` are homogeneous, so the ideal they span is a homogeneous ideal.
  have hhom : (Ideal.span (Set.range F)).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (r+1)) k) := by
    apply Ideal.homogeneous_span
    intro x hx
    obtain ⟨i, rfl⟩ := hx
    exact ⟨(F i).totalDegree, hF i⟩
  intro x hx j
  exact (MvPolynomial.mem_iff_homogeneousComponent_mem hhom x).mp hx j

end Commons.Algebra.MvPolynomial

end


-- ==== from Submission.Commons.RingTheory.Ideal.card_minimalPrimes_quotient_le ====
section

/-!
# Bezout bound for the number of minimal primes of a complete intersection

If `f : Fin r → k[X_1,…,X_r]` is a family of polynomials, then the number of minimal primes
of `k[X_1,…,X_r]/(f_1,…,f_r)` is at most `∏ i, (deg f i).max 1`.

The proof homogenizes the `f i` to forms `F i` in `k[X_0,…,X_r]` and applies the projective
Bezout bound `card_minimalPrimes_homogeneous_le`, together with the fact that the affine chart
`X_0 = 1` does not increase the number of minimal primes.
-/

open MvPolynomial

namespace Commons.RingTheory.Ideal

section Bridge

variable {k : Type*} [Field k] {n : ℕ}

/-- The number of minimal primes over `J ⊔ span{X 0 - 1}` is at most the number of minimal
primes over the homogeneous ideal `J`.  (A self-contained version of the proof, phrased with
the component-form homogeneity hypothesis so that it can be combined with the projective
Bezout bound.) -/
private theorem card_minimalPrimes_sup_le_aux
    (J : Ideal (MvPolynomial (Fin (n+1)) k))
    (hJ : ∀ x ∈ J, ∀ j, MvPolynomial.homogeneousComponent j x ∈ J) :
    Nat.card {p : Ideal (MvPolynomial (Fin (n+1)) k) //
        p ∈ (J ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (n+1)) k) - 1}).minimalPrimes}
      ≤ Nat.card {p : Ideal (MvPolynomial (Fin (n+1)) k) // p ∈ J.minimalPrimes} := by
  classical
  haveI : Finite {p : Ideal (MvPolynomial (Fin (n+1)) k) // p ∈ J.minimalPrimes} :=
    finite_subtype_minimalPrimes J
  have exists_below : ∀ (𝔔 : Ideal (MvPolynomial (Fin (n+1)) k)),
      𝔔 ∈ (J ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (n+1)) k) - 1}).minimalPrimes →
      ∃ 𝔮 ∈ J.minimalPrimes, 𝔮 ≤ 𝔔 := by
    intro 𝔔 h𝔔
    haveI : 𝔔.IsPrime := h𝔔.isPrime
    exact Ideal.exists_minimalPrimes_le (I := J) (le_trans le_sup_left h𝔔.le)
  let g : {𝔔 : Ideal (MvPolynomial (Fin (n+1)) k) //
        𝔔 ∈ (J ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (n+1)) k) - 1}).minimalPrimes} →
      {𝔮 : Ideal (MvPolynomial (Fin (n+1)) k) // 𝔮 ∈ J.minimalPrimes} :=
    fun 𝔔 => ⟨Classical.choose (exists_below 𝔔.1 𝔔.2),
      (Classical.choose_spec (exists_below 𝔔.1 𝔔.2)).1⟩
  have hg_le : ∀ 𝔔, (g 𝔔).1 ≤ 𝔔.1 := fun 𝔔 => (Classical.choose_spec (exists_below 𝔔.1 𝔔.2)).2
  have h_eq : ∀ 𝔔, (g 𝔔).1 ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (n+1)) k) - 1}
      = 𝔔.1 := by
    intro 𝔔
    haveI : (g 𝔔).1.IsPrime := (g 𝔔).2.isPrime
    have hcomp : ∀ x ∈ (g 𝔔).1, ∀ j,
        MvPolynomial.homogeneousComponent j x ∈ (g 𝔔).1 :=
      minimalPrimes_homogeneous J hJ (g 𝔔).2
    have hXq : (MvPolynomial.X 0 : MvPolynomial (Fin (n+1)) k) ∉ (g 𝔔).1 := by
      intro h
      have h1 : (MvPolynomial.X 0 : MvPolynomial (Fin (n+1)) k) ∈ 𝔔.1 := hg_le 𝔔 h
      have h2 : (MvPolynomial.X 0 : MvPolynomial (Fin (n+1)) k) - 1 ∈ 𝔔.1 :=
        𝔔.2.le (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _)))
      have h3 : (1 : MvPolynomial (Fin (n+1)) k) ∈ 𝔔.1 := by
        have := sub_mem h1 h2
        simpa using this
      exact 𝔔.2.isPrime.ne_top ((Ideal.eq_top_iff_one 𝔔.1).mpr h3)
    have hsup_prime := isPrime_sup_span_X_sub_one (g 𝔔).1 hcomp hXq
    have hle : (g 𝔔).1 ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (n+1)) k) - 1} ≤ 𝔔.1 :=
      sup_le (hg_le 𝔔) (le_trans le_sup_right 𝔔.2.le)
    have hIle : J ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (n+1)) k) - 1} ≤
        (g 𝔔).1 ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (n+1)) k) - 1} :=
      sup_le (le_trans (g 𝔔).2.le le_sup_left) le_sup_right
    have hmin : 𝔔.1 ≤ (g 𝔔).1 ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (n+1)) k) - 1} :=
      (show Minimal (fun q => q.IsPrime ∧
          (J ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (n+1)) k) - 1}) ≤ q) 𝔔.1
        from 𝔔.2).2 ⟨hsup_prime, hIle⟩ hle
    exact le_antisymm hle hmin
  exact Nat.card_le_card_of_injective g (by
    intro 𝔔1 𝔔2 h
    apply Subtype.ext
    have hv : (g 𝔔1).1 = (g 𝔔2).1 := congrArg Subtype.val h
    rw [← h_eq 𝔔1, ← h_eq 𝔔2, hv])

/-- Setting `X 0 = 1` does not increase the number of minimal primes of the quotient by a
homogeneous ideal. -/
private theorem card_minimalPrimes_sup_span_X_sub_one_le_aux
    (J : Ideal (MvPolynomial (Fin (n+1)) k))
    (hJ : ∀ x ∈ J, ∀ j, MvPolynomial.homogeneousComponent j x ∈ J) :
    Nat.card {p : Ideal (MvPolynomial (Fin (n+1)) k ⧸ (J ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (n+1)) k) - 1})) //
        p ∈ Ideal.minimalPrimes (⊥ : Ideal (MvPolynomial (Fin (n+1)) k ⧸ (J ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (n+1)) k) - 1})))}
      ≤ Nat.card {p : Ideal (MvPolynomial (Fin (n+1)) k ⧸ J) //
          p ∈ Ideal.minimalPrimes (⊥ : Ideal (MvPolynomial (Fin (n+1)) k ⧸ J))} := by
  calc Nat.card {p : Ideal (MvPolynomial (Fin (n+1)) k ⧸ (J ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (n+1)) k) - 1})) //
          p ∈ Ideal.minimalPrimes (⊥ : Ideal (MvPolynomial (Fin (n+1)) k ⧸ (J ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (n+1)) k) - 1})))}
      = Nat.card {p : Ideal (MvPolynomial (Fin (n+1)) k) //
          p ∈ (J ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (n+1)) k) - 1}).minimalPrimes} :=
        card_minimalPrimes_quotient_eq _
    _ ≤ Nat.card {p : Ideal (MvPolynomial (Fin (n+1)) k) // p ∈ J.minimalPrimes} :=
        card_minimalPrimes_sup_le_aux J hJ
    _ = Nat.card {p : Ideal (MvPolynomial (Fin (n+1)) k ⧸ J) //
          p ∈ Ideal.minimalPrimes (⊥ : Ideal (MvPolynomial (Fin (n+1)) k ⧸ J))} :=
        (card_minimalPrimes_quotient_eq J).symm

end Bridge

private theorem card_minimalPrimes_quotient_le {k : Type*} [Field k] {r : ℕ}
    (f : Fin r → MvPolynomial (Fin r) k) :
    Nat.card {p : Ideal (MvPolynomial (Fin r) k ⧸ Ideal.span (Set.range f)) //
      p ∈ Ideal.minimalPrimes (⊥ : Ideal (MvPolynomial (Fin r) k ⧸ Ideal.span (Set.range f)))}
      ≤ ∏ i, (f i).totalDegree.max 1 := by
  classical
  let φ : MvPolynomial (Fin (r+1)) k →ₐ[k] MvPolynomial (Fin r) k :=
    MvPolynomial.aeval
      (fun i : Fin (r+1) => Fin.cases (1 : MvPolynomial (Fin r) k) (fun j => MvPolynomial.X j) i)
  have hφsurj : Function.Surjective φ := Commons.Algebra.MvPolynomial.surjective_aeval_dehom r
  have hφker : RingHom.ker φ.toRingHom =
      Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (r+1)) k) - 1} :=
    Commons.Algebra.MvPolynomial.ker_aeval_dehom r
  choose F hFhom hFdeg hFdehom using fun i =>
    Commons.Algebra.MvPolynomial.exists_homogenization (f i)
  let J : Ideal (MvPolynomial (Fin (r+1)) k) := Ideal.span (Set.range F)
  have hJhom : ∀ x ∈ J, ∀ j, MvPolynomial.homogeneousComponent j x ∈ J :=
    Commons.Algebra.MvPolynomial.span_range_homogeneousComponent_mem F hFhom
  have hmap : Ideal.map φ.toRingHom J = Ideal.span (Set.range f) := by
    rw [show J = Ideal.span (Set.range F) from rfl, Ideal.map_span]
    have himg : ⇑φ.toRingHom '' Set.range F = Set.range f := by
      rw [← Set.range_comp]
      congr 1
      funext i
      exact hFdehom i
    rw [himg]
  have hcomap : (Ideal.span (Set.range f)).comap φ.toRingHom
      = J ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (r+1)) k) - 1} := by
    apply le_antisymm
    · intro g hg
      rw [Ideal.mem_comap] at hg
      rw [← hmap] at hg
      obtain ⟨j, hj, hjeq⟩ := (Ideal.mem_map_iff_of_surjective φ.toRingHom hφsurj).mp hg
      have hkerg : g - j ∈ RingHom.ker φ.toRingHom := by
        rw [RingHom.mem_ker, map_sub, hjeq, sub_self]
      rw [hφker] at hkerg
      have : g = j + (g - j) := by ring
      rw [this]
      exact add_mem (Ideal.mem_sup_left hj) (Ideal.mem_sup_right hkerg)
    · rw [sup_le_iff]
      constructor
      · intro x hx
        rw [Ideal.mem_comap, ← hmap]
        exact Ideal.mem_map_of_mem _ hx
      · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
        have hX0 : φ.toRingHom (MvPolynomial.X 0 : MvPolynomial (Fin (r+1)) k) = 1 := by
          show φ (MvPolynomial.X 0) = 1
          simp only [φ, MvPolynomial.aeval_X, Fin.cases_zero]
        rw [map_sub, map_one, hX0, sub_self]
        exact Submodule.zero_mem _
  have hmin : Nat.card {p : Ideal (MvPolynomial (Fin r) k) //
        p ∈ (Ideal.span (Set.range f)).minimalPrimes}
      = Nat.card {p : Ideal (MvPolynomial (Fin (r+1)) k) //
        p ∈ (J ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (r+1)) k) - 1}).minimalPrimes} := by
    rw [← card_minimalPrimes_comap_eq φ.toRingHom hφsurj (Ideal.span (Set.range f)), hcomap]
  calc Nat.card {p : Ideal (MvPolynomial (Fin r) k ⧸ Ideal.span (Set.range f)) //
        p ∈ Ideal.minimalPrimes (⊥ : Ideal (MvPolynomial (Fin r) k ⧸ Ideal.span (Set.range f)))}
      = Nat.card {p : Ideal (MvPolynomial (Fin r) k) //
          p ∈ (Ideal.span (Set.range f)).minimalPrimes} :=
        card_minimalPrimes_quotient_eq _
    _ = Nat.card {p : Ideal (MvPolynomial (Fin (r+1)) k) //
          p ∈ (J ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (r+1)) k) - 1}).minimalPrimes} := hmin
    _ = Nat.card {p : Ideal (MvPolynomial (Fin (r+1)) k ⧸
            (J ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (r+1)) k) - 1})) //
          p ∈ Ideal.minimalPrimes (⊥ : Ideal (MvPolynomial (Fin (r+1)) k ⧸
            (J ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (r+1)) k) - 1})))} :=
        (card_minimalPrimes_quotient_eq _).symm
    _ ≤ Nat.card {p : Ideal (MvPolynomial (Fin (r+1)) k ⧸ J) //
          p ∈ Ideal.minimalPrimes (⊥ : Ideal (MvPolynomial (Fin (r+1)) k ⧸ J))} :=
        card_minimalPrimes_sup_span_X_sub_one_le_aux J hJhom
    _ = Nat.card {p : Ideal (MvPolynomial (Fin (r+1)) k) // p ∈ J.minimalPrimes} :=
        card_minimalPrimes_quotient_eq J
    _ ≤ ∏ i, (F i).totalDegree.max 1 := by
        rw [← card_minimalPrimes_quotient_eq J]
        exact card_minimalPrimes_homogeneous_le F hFhom
    _ ≤ ∏ i, (f i).totalDegree.max 1 := by
        apply Finset.prod_le_prod
        · intro i _
          exact Nat.zero_le _
        · intro i _
          exact max_le_max_right 1 (hFdeg i)

end Commons.RingTheory.Ideal

end

-- re-register converted instances as local instances for the rest of the file
attribute [local instance] Commons.RingTheory.Ideal.Hilbert.idealOfVars_isMaximal
attribute [local instance] Commons.RingTheory.Ideal.inst_anon_c47_1

-- ===== Target theorem =====
namespace Commons.RingTheory.Ideal

universe u

/-- Bézout bound for the number of minimal primes of a complete intersection: if
`f : Fin r → k[X_1,…,X_r]` is a family of polynomials, then the number of minimal primes
of `k[X_1,…,X_r]/(f_1,…,f_r)` is at most `∏ i, (deg f i).max 1`. -/
theorem card_minimalPrimes_quotient_le_univ {k : Type u} [Field k] {r : ℕ}
    (f : Fin r → MvPolynomial (Fin r) k) :
    Nat.card {p : Ideal (MvPolynomial (Fin r) k ⧸ Ideal.span (Set.range f)) //
      p ∈ Ideal.minimalPrimes (⊥ : Ideal (MvPolynomial (Fin r) k ⧸ Ideal.span (Set.range f)))}
      ≤ ∏ i, (f i).totalDegree.max 1 := by
  exact card_minimalPrimes_quotient_le f

end Commons.RingTheory.Ideal