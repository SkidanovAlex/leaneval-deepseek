import Mathlib
import Submission.SlabDP
import Submission.Variational
import Submission.Commons.NumberTheory.KroneckerSums.sum_fin12_ite_count_eq_sum_dedup
import Submission.Commons.NumberTheory.KroneckerSums.sum_prod_dedup_eq_sum_fin12_fin12
import Submission.Commons.NumberTheory.KroneckerSums.sum_product_cons_zero
import Submission.Commons.Data.List.dedup_count_pos_iff
import Submission.SimplexMarginal

set_option linter.unnecessarySeqFocus false

open scoped BigOperators
open Finset

/-!
# The bridge `Ssum β β' k = slabLevel k (mult β) (mult β')` — dictionary and bookkeeping

`Submission/Variational.lean` defines `Ssum α β k` by a recursion on *lists* (`eraseOne` removes one
occurrence of a present part, and the sum runs over `0 :: σ.dedup`); `Submission/SlabDP.lean`
defines the *level* operator `slabStep` on *multiplicity vectors* (the sum runs over `Fin 12`, with
a "part present" test).  This module holds the dictionary between the two presentations and the
bookkeeping lemmas the induction consumes:

* `mult σ i` — the number of occurrences of the part `2(i+1)` in the signature `σ`;
* `mult_cons` — the `count` bookkeeping for a cons;
* `indPart_mult` / `mult_sub_indPart` — removing one occurrence of the part `2(i+1)` from the
  vector corresponds to `eraseOne` on the signature (the step case of the induction).

The full bridge, and the two `Finset`-sum correspondences (`dedup`-sums of `Ssum` vs the
`"part present"` sums of `slabStep`), are recorded in the roadmap §21 as the next pieces.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- The multiplicity vector of a signature: the `i`-th entry counts the occurrences of the part
`2(i+1)` (so the signature is rebuilt from the twelve even parts `2,4,…,24`). -/
def mult (σ : List ℕ) (i : Fin 12) : ℕ := σ.count (2 * ((i : ℕ) + 1))

@[simp] lemma mult_nil (i : Fin 12) : mult [] i = 0 := rfl

/-- Bookkeeping for a cons. -/
lemma mult_cons (a : ℕ) (σ : List ℕ) (i : Fin 12) :
    mult (a :: σ) i = (if a = 2 * ((i : ℕ) + 1) then 1 + mult σ i else mult σ i) := by
  rw [mult, mult, List.count_cons]
  by_cases h : a = 2 * ((i : ℕ) + 1) <;> simp [h] <;> omega

/-- `mult` is invariant when only the odd parts (or parts outside `2,4,…,24`) are changed:
for a signature supported on the twelve even parts, `mult` determines the signature's
even-part content. -/
lemma mult_eq_zero_iff_of_even (σ : List ℕ)
    (h : ∀ a ∈ σ, ∃ i : Fin 12, a = 2 * ((i : ℕ) + 1)) :
    mult σ = 0 ↔ σ = [] := by
  constructor
  · intro h0
    by_contra hne
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil σ hne
    obtain ⟨i, hi⟩ := h a ha
    have hne0 : mult σ i ≠ 0 := by
      intro hz
      have hmem : 2 * ((i : ℕ) + 1) ∉ σ := by
        simpa [mult] using (List.count_eq_zero.mp hz)
      exact hmem (hi ▸ ha)
    rw [h0] at hne0
    exact hne0 rfl
  · rintro rfl
    funext i
    simp



/-- **The spine of the step obligation.**  Removing one occurrence of the part `2(i+1)` from a
signature subtracts exactly the unit vector `indPart i` from its multiplicity vector.  (When the
part is absent, `eraseOne` is the identity and the truncated subtraction gives `0`, so the
identity holds in all cases.) -/
lemma mult_eraseOne (β : List ℕ) (i : Fin 12) :
    mult (eraseOne β (2 * ((i : ℕ) + 1))) = mult β - indPart i := by
  induction β with
  | nil =>
      funext j
      simp [eraseOne, mult, indPart]
  | cons a t ih =>
      by_cases ha : a = 2 * ((i : ℕ) + 1)
      · subst ha
        rw [eraseOne, if_pos rfl]
        funext j
        rw [Pi.sub_apply]
        simp only [mult_cons]
        by_cases hj : j = i
        · subst hj
          rw [if_pos rfl]
          simp [indPart]
        · have hne : 2 * ((i : ℕ) + 1) ≠ 2 * ((j : ℕ) + 1) := by
            intro hc
            exact hj (Fin.ext (by omega))
          rw [if_neg hne]
          have hid : indPart i j = 0 := by simp [indPart, hj]
          rw [hid]
          simp
      · rw [eraseOne, if_neg ha]
        funext j
        have ihj := congrFun ih j
        rw [Pi.sub_apply] at ihj ⊢
        simp only [mult_cons]
        rw [ihj]
        by_cases hj : j = i
        · have hid : indPart i j = 1 := by simp [indPart, hj]
          have hb : a ≠ 2 * ((j : ℕ) + 1) := by
            intro hc
            exact ha (by rw [← hj]; exact hc)
          rw [hid, if_neg hb, if_neg hb]
        · have hid : indPart i j = 0 := by simp [indPart, hj]
          rw [hid]
          by_cases hb : a = 2 * ((j : ℕ) + 1) <;> simp [hb]


/-- **Base case of the bridge**: at level `0` the level table is the point mass at the origin and
`Ssum β β' 0` is `1` exactly when `β = β' = []`, the two conditions agreeing by
`mult_eq_zero_iff_of_even`. -/
theorem Ssum_zero_eq_slabLevel_zero (β β' : List ℕ)
    (hβ : ∀ a ∈ β, ∃ i : Fin 12, a = 2 * ((i : ℕ) + 1))
    (hβ' : ∀ a ∈ β', ∃ i : Fin 12, a = 2 * ((i : ℕ) + 1)) :
    Ssum β β' 0 = slabLevel 0 (mult β) (mult β') := by
  rw [slabLevel_zero]
  simp only [Ssum, slabBase]
  by_cases h : β = [] ∧ β' = []
  · obtain ⟨rfl, rfl⟩ := h
    have h0 : mult [] = 0 := by funext i; exact mult_nil i
    rw [h0]; rfl
  · have hne : ¬ (mult β = 0 ∧ mult β' = 0) := by
      rintro ⟨h1, h2⟩
      exact h ⟨(mult_eq_zero_iff_of_even β hβ).mp h1,
              (mult_eq_zero_iff_of_even β' hβ').mp h2⟩
    rw [if_neg h, if_neg hne]


/-- **L233 in the direction the bridge's step case consumes**: `Ssum`'s `dedup`-sum over the
present parts equals the `Fin 12`-sum with the "part present" test. -/
theorem sum_dedup_eq_sum_fin12 (β : List ℕ)
    (hβ : ∀ a ∈ β, ∃ i : Fin 12, a = 2 * ((i : ℕ) + 1))
    (G : ℕ → ℕ) (F : Fin 12 → ℕ) (hGF : ∀ i : Fin 12, G (2 * ((i : ℕ) + 1)) = F i) :
    (β.dedup.map G).sum = ∑ i : Fin 12, (if 0 < mult β i then F i else 0) :=
  (Commons.NumberTheory.KroneckerSums.sum_fin12_ite_count_eq_sum_dedup β G hβ F hGF).symm


/-- **The recursion's `k+1` step, unfolded** (the first line of the assembly recipe): the
`List.foldl` this exposes is exactly what L234 splits into its four groups. -/
theorem Ssum_succ (β β' : List ℕ) (k : ℕ) :
    Ssum β β' (k + 1)
      = ((0 :: β.dedup).product (0 :: β'.dedup)).foldl
          (fun acc pq => acc + Nat.factorial (pq.1 + pq.2)
            * Ssum (eraseOne β pq.1) (eraseOne β' pq.2) k) 0 := rfl

/-- **`slabStep` unfolded** at the level-`k` values (the matching target of the assembly): the four
terms are, in order, `f m n`, the `p`-sum, the `q`-sum and the double sum. -/
theorem slabStep_eq (f : (Fin 12 → ℕ) → (Fin 12 → ℕ) → ℕ) (m n : Fin 12 → ℕ) :
    slabStep f m n
      = f m n
        + (∑ p : Fin 12, if 0 < m p then (Nat.factorial (2 * ((p : ℕ) + 1))) * f (m - indPart p) n else 0)
        + (∑ q : Fin 12, if 0 < n q then (Nat.factorial (2 * ((q : ℕ) + 1))) * f m (n - indPart q) else 0)
        + (∑ p : Fin 12, ∑ q : Fin 12,
            if 0 < m p ∧ 0 < n q then
              (Nat.factorial (2 * ((p : ℕ) + 1) + 2 * ((q : ℕ) + 1))) * f (m - indPart p) (n - indPart q)
            else 0) := rfl


/-- **The `hGF` side condition of rewrite 3** (the `q`-side group, mirroring the `p`-side): given
the level-`k` identification for the predecessor state, the `dedup`-sum integrand of the `p`-sum
matches the `Fin 12`-indexed integrand of `slabStep`, using `mult_eraseOne` for the body. -/
theorem hGF_step (β β' : List ℕ) (k : ℕ) (i : Fin 12)
    (ih : Ssum (eraseOne β (2 * ((i : ℕ) + 1))) β' k
            = slabLevel k (mult (eraseOne β (2 * ((i : ℕ) + 1)))) (mult β')) :
    Nat.factorial (2 * ((i : ℕ) + 1)) * Ssum (eraseOne β (2 * ((i : ℕ) + 1))) β' k
      = Nat.factorial (2 * ((i : ℕ) + 1))
          * slabLevel k (mult β - indPart i) (mult β') := by
  rw [ih, mult_eraseOne]

/-- The same on the `q`-side. -/
theorem hGF_step_q (β β' : List ℕ) (k : ℕ) (i : Fin 12)
    (ih : Ssum β (eraseOne β' (2 * ((i : ℕ) + 1))) k
            = slabLevel k (mult β) (mult (eraseOne β' (2 * ((i : ℕ) + 1))))) :
    Nat.factorial (2 * ((i : ℕ) + 1)) * Ssum β (eraseOne β' (2 * ((i : ℕ) + 1))) k
      = Nat.factorial (2 * ((i : ℕ) + 1))
          * slabLevel k (mult β) (mult β' - indPart i) := by
  rw [ih, mult_eraseOne]


/-- **The `hGF` side condition of group 4** (the cross terms, both coordinates at once): the
double-`foldl` integrand over `β.dedup.product β'.dedup` matches the double sum of `slabStep`,
the body being rewritten by `mult_eraseOne` *twice* — once per coordinate. -/
theorem hGF_step_cross (β β' : List ℕ) (k : ℕ) (i j : Fin 12)
    (ih : Ssum (eraseOne β (2 * ((i : ℕ) + 1))) (eraseOne β' (2 * ((j : ℕ) + 1))) k
            = slabLevel k (mult (eraseOne β (2 * ((i : ℕ) + 1))))
                (mult (eraseOne β' (2 * ((j : ℕ) + 1))))) :
    Nat.factorial (2 * ((i : ℕ) + 1) + 2 * ((j : ℕ) + 1))
        * Ssum (eraseOne β (2 * ((i : ℕ) + 1))) (eraseOne β' (2 * ((j : ℕ) + 1))) k
      = Nat.factorial (2 * ((i : ℕ) + 1) + 2 * ((j : ℕ) + 1))
          * slabLevel k (mult β - indPart i) (mult β' - indPart j) := by
  rw [ih, mult_eraseOne, mult_eraseOne]


/-- **Group 1 of the step case.**  `eraseOne` fixes a list in which the part does not occur — in
particular, for a signature over `2,4,…,24`, removing the *absent* part `0` is the identity.  This
is what collapses the first `slabStep` group to the induction hypothesis. -/
lemma eraseOne_of_notMem (β : List ℕ) (v : ℕ) (h : v ∉ β) : eraseOne β v = β := by
  induction β with
  | nil => rfl
  | cons a t ih =>
      have ha : a ≠ v := fun hc => h (by simp [hc])
      have ht : v ∉ t := fun hc => h (by simp [hc])
      rw [eraseOne, if_neg ha, ih ht]

/-- Group 1, in the form the step case uses: for a signature over `2,4,…,24` the part `0` is
absent, so `mult` is unchanged and the group-1 summand is `1 * Ssum β β' k`. -/
lemma eraseOne_zero_of_support (β : List ℕ)
    (hβ : ∀ a ∈ β, ∃ i : Fin 12, a = 2 * ((i : ℕ) + 1)) :
    eraseOne β 0 = β :=
  eraseOne_of_notMem β 0 (fun hc => by
    obtain ⟨i, hi⟩ := hβ 0 hc
    have : 2 * ((i : ℕ) + 1) = 0 := hi.symm
    omega)


/-- **Group 2 of the four-group match (step 1 of §36), instantiated and closed.**  The `p`-sum of
`Ssum`'s step, reindexed onto `Fin 12` with the `slabStep` body: the dedup-sum of
`p! * Ssum (eraseOne β p) β' k` equals the `Fin 12`-sum of
`(2(i+1))! * slabLevel k (mult β - indPart i) (mult β')` over the present parts — the `hGF` side
condition being `hGF_step` (§32) fed by the induction hypothesis. -/
theorem group_p_sum (β β' : List ℕ) (k : ℕ)
    (hβ : ∀ a ∈ β, ∃ i : Fin 12, a = 2 * ((i : ℕ) + 1))
    (hβ' : ∀ a ∈ β', ∃ i : Fin 12, a = 2 * ((i : ℕ) + 1))
    (ih : ∀ i : Fin 12, Ssum (eraseOne β (2 * ((i : ℕ) + 1))) β' k
        = slabLevel k (mult (eraseOne β (2 * ((i : ℕ) + 1)))) (mult β')) :
    (β.dedup.map (fun p => (p + 0).factorial * Ssum (eraseOne β p) (eraseOne β' 0) k)).sum
      = ∑ i : Fin 12,
          (if 0 < mult β i then
            Nat.factorial (2 * ((i : ℕ) + 1)) * slabLevel k (mult β - indPart i) (mult β')
           else 0) := by
  rw [show (fun p => (p + 0).factorial * Ssum (eraseOne β p) (eraseOne β' 0) k)
        = (fun p => (p + 0).factorial * Ssum (eraseOne β p) β' k) from by
      funext p
      rw [eraseOne_zero_of_support β' hβ']]
  exact sum_dedup_eq_sum_fin12 β hβ
    (fun p => (p + 0).factorial * Ssum (eraseOne β p) β' k)
    (fun i => Nat.factorial (2 * ((i : ℕ) + 1)) * slabLevel k (mult β - indPart i) (mult β'))
    (fun i => hGF_step β β' k i (ih i))


/-- **Group 3 of the four-group match (the mirror of `group_p_sum`).**  The `q`-sum of `Ssum`'s
step reindexed onto `Fin 12` with the `slabStep` body; the only differences from the `p`-side are
the exchanged roles of `β, β'` and `hGF_step_q` in place of `hGF_step`. -/
theorem group_q_sum (β β' : List ℕ) (k : ℕ)
    (hβ : ∀ a ∈ β, ∃ i : Fin 12, a = 2 * ((i : ℕ) + 1))
    (hβ' : ∀ a ∈ β', ∃ i : Fin 12, a = 2 * ((i : ℕ) + 1))
    (ih : ∀ i : Fin 12, Ssum β (eraseOne β' (2 * ((i : ℕ) + 1))) k
        = slabLevel k (mult β) (mult (eraseOne β' (2 * ((i : ℕ) + 1))))) :
    (β'.dedup.map (fun q => (0 + q).factorial * Ssum (eraseOne β 0) (eraseOne β' q) k)).sum
      = ∑ i : Fin 12,
          (if 0 < mult β' i then
            Nat.factorial (2 * ((i : ℕ) + 1)) * slabLevel k (mult β) (mult β' - indPart i)
           else 0) := by
  rw [show (fun q => (0 + q).factorial * Ssum (eraseOne β 0) (eraseOne β' q) k)
        = (fun q => (0 + q).factorial * Ssum β (eraseOne β' q) k) from by
      funext q
      rw [eraseOne_zero_of_support β hβ]]
  exact sum_dedup_eq_sum_fin12 β' hβ'
    (fun q => (0 + q).factorial * Ssum β (eraseOne β' q) k)
    (fun i => Nat.factorial (0 + 2 * ((i : ℕ) + 1)) * slabLevel k (mult β) (mult β' - indPart i))
    (fun i => by simpa using hGF_step_q β β' k i (ih i))


/-- `eraseOne` preserves the support hypothesis (every element is one of `2,4,…,24`). -/
lemma eraseOne_support (β : List ℕ) (v : ℕ)
    (hβ : ∀ a ∈ β, ∃ i : Fin 12, a = 2 * ((i : ℕ) + 1)) :
    ∀ a ∈ eraseOne β v, ∃ i : Fin 12, a = 2 * ((i : ℕ) + 1) := by
  induction β with
  | nil => intro a ha; simp [eraseOne] at ha
  | cons b t ih =>
      intro a ha
      by_cases h : b = v
      · rw [eraseOne, if_pos h] at ha
        exact (fun c hc => hβ c (by simp [hc])) a ha
      · rw [eraseOne, if_neg h] at ha
        rcases List.mem_cons.mp ha with hb | ha'
        · rw [hb]; exact hβ b (by simp)
        · exact ih (fun c hc => hβ c (by simp [hc])) a ha'


/-- **Group 4 of the four-group match (the cross terms).**  The double `foldl` over
`β.dedup.product β'.dedup` reindexed onto `Fin 12 × Fin 12` with the `slabStep` cross body: the
wrapper is L235 (`sum_prod_dedup_eq_sum_fin12_fin12`) with the `hHF` side condition `hGF_step_cross`
fed by the induction hypothesis, and the two `if`-conditions reconciled by `dedup_count_pos_iff`
(L236). -/
theorem group_pq_sum (β β' : List ℕ) (k : ℕ)
    (hβ : ∀ a ∈ β, ∃ i : Fin 12, a = 2 * ((i : ℕ) + 1))
    (hβ' : ∀ a ∈ β', ∃ i : Fin 12, a = 2 * ((i : ℕ) + 1))
    (ih : ∀ i j : Fin 12,
        Ssum (eraseOne β (2 * ((i : ℕ) + 1))) (eraseOne β' (2 * ((j : ℕ) + 1))) k
          = slabLevel k (mult (eraseOne β (2 * ((i : ℕ) + 1))))
              (mult (eraseOne β' (2 * ((j : ℕ) + 1))))) :
    (β.dedup.product β'.dedup).foldl
        (fun acc pq => acc + Nat.factorial (pq.1 + pq.2)
          * Ssum (eraseOne β pq.1) (eraseOne β' pq.2) k) 0
      = ∑ i : Fin 12, ∑ j : Fin 12,
          (if 0 < mult β i ∧ 0 < mult β' j then
            Nat.factorial (2 * ((i : ℕ) + 1) + 2 * ((j : ℕ) + 1))
              * slabLevel k (mult β - indPart i) (mult β' - indPart j)
           else 0) := by
  have hmain := Commons.NumberTheory.KroneckerSums.sum_prod_dedup_eq_sum_fin12_fin12
    β.dedup β'.dedup
    (fun p hp => hβ p (List.mem_dedup.mp hp))
    (fun q hq => hβ' q (List.mem_dedup.mp hq))
    (fun p q => Nat.factorial (p + q) * Ssum (eraseOne β p) (eraseOne β' q) k)
    (fun i j => Nat.factorial (2 * ((i : ℕ) + 1) + 2 * ((j : ℕ) + 1))
      * slabLevel k (mult β - indPart i) (mult β' - indPart j))
    (fun i j => hGF_step_cross β β' k i j (ih i j))
  rw [show (β.dedup.product β'.dedup) = (β.dedup.dedup.product β'.dedup.dedup) from by
    simp only [List.dedup_idem]]
  rw [hmain]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  refine if_congr ?_ rfl rfl
  exact and_congr (Commons.Data.List.dedup_count_pos_iff β (2 * ((i : ℕ) + 1))).2
    (Commons.Data.List.dedup_count_pos_iff β' (2 * ((j : ℕ) + 1))).2

/-- **THE BRIDGE.**  The definitional recursion `Ssum` on signatures agrees with the level
operator `slabLevel` on the multiplicity vectors of `Submission/SlabDP.lean`:
`Ssum β β' k = slabLevel k (mult β) (mult β')` for signatures over the twelve even parts
`2,4,…,24`.  Proof: induction on `k`; the base case is `Ssum_zero_eq_slabLevel_zero` (§25), and
the step splits `Ssum`'s double `List.foldl` by `sum_product_cons_zero` into its four groups (the
constant `0×0` term, the `p`-sum, the `q`-sum and the cross sum), reindexes each of them onto
`Fin 12` by `group_p_sum`/`group_q_sum`/`group_pq_sum`, and matches the four terms of `slabStep`
(§29, `slabStep_eq`).

This is the identity that makes `slabLevel` a *memoizable* substitute for the exponential `Ssum`
recursion: `slabLevel k` becomes a table over the `272²` multiplicity-vector states of degree
`≤ 24`, computed by the DP `w_{k+1} = slabStep w_k`. -/
theorem Ssum_eq_slabLevel (β β' : List ℕ) (k : ℕ)
    (hβ : ∀ a ∈ β, ∃ i : Fin 12, a = 2 * ((i : ℕ) + 1))
    (hβ' : ∀ a ∈ β', ∃ i : Fin 12, a = 2 * ((i : ℕ) + 1)) :
    Ssum β β' k = slabLevel k (mult β) (mult β') := by
  induction k generalizing β β' with
  | zero => exact Ssum_zero_eq_slabLevel_zero β β' hβ hβ'
  | succ k ih =>
      have hne : ∀ p ∈ β.dedup, p ≠ 0 := by
        intro p hp hp0
        obtain ⟨i, hi⟩ := hβ p (List.mem_dedup.mp hp)
        omega
      have hne' : ∀ q ∈ β'.dedup, q ≠ 0 := by
        intro q hq hq0
        obtain ⟨j, hj⟩ := hβ' q (List.mem_dedup.mp hq)
        omega
      rw [Ssum_succ,
        Commons.NumberTheory.KroneckerSums.sum_product_cons_zero β.dedup β'.dedup hne hne'
          (fun p q => Nat.factorial (p + q) * Ssum (eraseOne β p) (eraseOne β' q) k)]
      rw [show slabLevel (k + 1) (mult β) (mult β')
            = slabStep (slabLevel k) (mult β) (mult β') from rfl]
      rw [slabStep_eq (slabLevel k) (mult β) (mult β')]
      rw [group_p_sum β β' k hβ hβ' (fun i => ih _ _ (eraseOne_support β _ hβ) hβ'),
        group_q_sum β β' k hβ hβ' (fun i => ih _ _ hβ (eraseOne_support β' _ hβ')),
        group_pq_sum β β' k hβ hβ'
          (fun i j => ih _ _ (eraseOne_support β _ hβ) (eraseOne_support β' _ hβ'))]
      have hterm : (0 + 0).factorial * Ssum (eraseOne β 0) (eraseOne β' 0) k
          = slabLevel k (mult β) (mult β') := by
        rw [eraseOne_zero_of_support β hβ, eraseOne_zero_of_support β' hβ',
          ih β β' hβ hβ']
        norm_num
      rw [hterm]

end Commons.NumberTheory.MaynardSieve
