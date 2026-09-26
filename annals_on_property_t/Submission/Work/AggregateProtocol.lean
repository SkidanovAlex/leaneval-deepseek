import Submission.Work.T3RebalanceTuple
import Submission.Work.T1Absorb
import Submission.Work.Confine

open FreeGroup
open Commons.GroupTheory.FreeGroup
set_option autoImplicit false

/-!
# The aggregate `a_m = Γ_m(w_1,…,w_n)` — first link of the reduction protocol

The classical reduction analyses, for the current basis images `w_i = α(a_i)`,
the *aggregate* expressions of the standard generators in terms of them:
`a_m = Γ_m(w_1,…,w_n)` is a product of factors whose group value is the single
generator `a_m`.  This module formalises that object at the word level and
proves the *first link* of the protocol: from the balanced state of an
interior factor of the aggregate one reads off (a) the balanced system
element `es[j]` whose word splits as `A ++ B` with `|A| = |B|`, the two
neighbours covering exactly the two halves (Nielsen 1919 p. 270: "α_p =
A_p·B_p, die Zerlegung in zwei Hälften"), and (b) the *witnesses* — the basis
images that end with `B` or begin with `B⁻¹` (respectively end with `A⁻¹` /
begin with `A`), depending on the sign with which the neighbour factor occurs
— which the rebalancing moves of `T3RebalanceTuple` consume.

Concretely:

* `aggregateWords es` — the word-level aggregate: the list of the reduced
  words of the factors `es`;
* `aggregate_reduce_letter` — if `es.prod = of m` (the factors compose to the
  standard generator `a_m`), the reduction of the flattened aggregate is the
  single-letter word `[(m,true)]`: the aggregate "consumes itself" to `a_m`;
* `aggregate_confined_factor` — by the general-`k` selection lemma
  (`Confine.confined_factor_exists`) such an aggregate has a *confined*
  factor;
* `aggregate_balanced_element` — for a confined interior factor in the
  balanced (not-strict on either junction) state, the element `es[j]` is the
  **balanced element**: `es[j].toWord = A ++ B` with `|A| = |B|`, and the two
  neighbouring words are `X ++ invRev A` and `invRev B ++ Z` (each neighbour
  covers exactly its half);
* `witness_*` — recording, for each orientation of the neighbouring factors
  (a basis image or its inverse), the `B`-ending / `B⁻¹`-beginning (and the
  mirrored `A⁻¹`-ending / `A`-beginning) structure of the corresponding basis
  image, in exactly the form `T3RebalanceTuple.norm_mul_*_le` /
  `rebalance_move_N_*` expect.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-- The **word-level aggregate**: the list of the reduced words of the
factors `es` of the expression `Γ_m(w_1,…,w_n)`.  (An `abbrev` so that the
factor-word structure is transparent to the index lemmas.) -/
abbrev aggregateWords {n : ℕ} (es : List (FreeGroup (Fin n))) :
    List (List (Fin n × Bool)) :=
  es.map FreeGroup.toWord

/-- Every factor word of an aggregate is reduced. -/
lemma aggregateWords_reduced {n : ℕ} (es : List (FreeGroup (Fin n))) :
    ∀ L ∈ aggregateWords es, FreeGroup.IsReduced L := by
  intro L hL
  rcases (List.mem_map.mp hL) with ⟨e, he, rfl⟩
  exact FreeGroup.isReduced_toWord (x := e)

/-- The factors of the aggregate and the list have the same length. -/
lemma aggregateWords_length {n : ℕ} (es : List (FreeGroup (Fin n))) :
    (aggregateWords es).length = es.length := by
  simp [aggregateWords]

/-- The reduction of the flattened aggregate equals the word of the product
of the factors. -/
lemma aggregate_flatten_reduce {n : ℕ} (es : List (FreeGroup (Fin n))) :
    FreeGroup.reduce ((aggregateWords es).flatten) = es.prod.toWord := by
  simpa [aggregateWords] using (reduce_flatten_toWord_prod es)

/-- **The aggregate reduces to `a_m`.**  If the factors of the aggregate
compose to the standard generator `a_m = of m`, then the free reduction of
the concatenation of the factor words is the single-letter word `[(m,true)]`
— the aggregate "consumes itself" down to `a_m` ("die Γ-Ausdrücke … die sich
durch Absorption ganz aufzehren"). -/
theorem aggregate_reduce_letter {n : ℕ} (es : List (FreeGroup (Fin n)))
    (m : Fin n) (hs : es.prod = FreeGroup.of m) :
    FreeGroup.reduce ((aggregateWords es).flatten) = [(m, true)] := by
  rw [aggregate_flatten_reduce]
  rw [hs]
  rw [FreeGroup.toWord_of]

/-- The reduced aggregate of a standard generator has length ≤ 1. -/
lemma aggregate_reduce_length_le_one {n : ℕ} (es : List (FreeGroup (Fin n)))
    (m : Fin n) (hs : es.prod = FreeGroup.of m) :
    (FreeGroup.reduce ((aggregateWords es).flatten)).length ≤ 1 := by
  rw [aggregate_reduce_letter es m hs]
  simp

/-- **Confined factor selection for the aggregate.**  An aggregate of `k ≥ 2`
factors composing to a standard generator has a *confined* factor: a factor
whose letters pair only with the two adjacent blocks of the aggregate
(Nielsen's aggregate lemma, general-`k` form; `Confine.confined_factor_exists`
applied to `aggregateWords es`). -/
theorem aggregate_confined_factor {n : ℕ} (es : List (FreeGroup (Fin n)))
    (m : Fin n) (hs : es.prod = FreeGroup.of m) (hk : 2 ≤ es.length) :
    ∃ j < es.length, Confined (aggregateWords es) j := by
  classical
  let Fs : List (List (Fin n × Bool)) := aggregateWords es
  have hredF : ∀ L ∈ Fs, FreeGroup.IsReduced L := by
    intro L hL
    have hL' : L ∈ aggregateWords es := by simpa [Fs] using hL
    exact aggregateWords_reduced es L hL'
  have hkF : 2 ≤ Fs.length := by
    rw [aggregateWords_length]
    exact hk
  have hsurv : (survivorPos Fs.flatten).length ≤ 1 := by
    rw [survivorPos_length]
    have hr := aggregate_reduce_letter es m hs
    rw [hr]
    simp
  rcases confined_factor_exists (α := Fin n) Fs hredF hkF hsurv with ⟨j, hjF, hc⟩
  refine ⟨j, ?_, ?_⟩
  · rw [← aggregateWords_length es]
    exact hjF
  · simpa [Fs] using hc

/-- **The balanced aggregate element.**  For a confined interior factor `j`
of the aggregate whose two junction alignments absorb at most half of its word
(the balanced state of `T3Rebalance.t3_balanced_decomposition`), the element
`es[j]` is the **balanced element**: its word splits as `A ++ B` with
`|A| = |B|`, the word of the left neighbour is `X ++ invRev A` and the word
of the right neighbour is `invRev B ++ Z` — the two neighbours cover exactly
the two halves. -/
theorem aggregate_balanced_element {n : ℕ} (es : List (FreeGroup (Fin n)))
    {j : ℕ} (hj : j < es.length) (hj0 : 0 < j) (hjk : j + 1 < es.length)
    (hm : j - 1 < es.length) (hconf : Confined (aggregateWords es) j)
    (hnotL : 2 * align ((es[j - 1]).toWord) ((es[j]).toWord) ≤ ((es[j]).toWord).length)
    (hnotR : 2 * align ((es[j]).toWord) ((es[j + 1]).toWord) ≤ ((es[j]).toWord).length) :
    ∃ (A B X Z : List (Fin n × Bool)),
      (es[j]).toWord = A ++ B ∧ A.length = B.length ∧
      (es[j - 1]).toWord = X ++ FreeGroup.invRev A ∧
      (es[j + 1]).toWord = FreeGroup.invRev B ++ Z := by
  classical
  let Fs : List (List (Fin n × Bool)) := aggregateWords es
  have hredF : ∀ L ∈ Fs, FreeGroup.IsReduced L := by
    intro L hL
    have hL' : L ∈ aggregateWords es := by simpa [Fs] using hL
    exact aggregateWords_reduced es L hL'
  have hjF : j < Fs.length := by rw [aggregateWords_length]; exact hj
  have hjkF : j + 1 < Fs.length := by rw [aggregateWords_length]; exact hjk
  have hmF : j - 1 < Fs.length := by rw [aggregateWords_length]; exact hm
  have hg_jm : Fs[j - 1] = (es[j - 1]).toWord := by
    rw [List.getElem_map]
  have hg_j : Fs[j] = (es[j]).toWord := by
    rw [List.getElem_map]
  have hg_jp : Fs[j + 1] = (es[j + 1]).toWord := by
    rw [List.getElem_map]
  have hnotLF : 2 * align (Fs[j - 1]) (Fs[j]) ≤ (Fs[j]).length := by
    rw [hg_jm, hg_j]
    exact hnotL
  have hnotRF : 2 * align (Fs[j]) (Fs[j + 1]) ≤ (Fs[j]).length := by
    rw [hg_j, hg_jp]
    exact hnotR
  rcases t3_balanced_decomposition Fs hredF (j := j) hjF hj0 hjkF hmF
    (by simpa [Fs] using hconf) hnotLF hnotRF with
    ⟨k, hk, hlen, hlenA, hlenB, htail, hhead⟩
  -- k = align (Fs[j-1]) (Fs[j]);  |Fs[j]| = 2k;  |take k| = |drop k| = k
  -- htail : (Fs[j-1]).drop (|Fs[j-1]| - k) = invRev (Fs[j].take k)
  -- hhead : (Fs[j+1]).take k = invRev (Fs[j].drop k)
  let A : List (Fin n × Bool) := Fs[j].take k
  let B : List (Fin n × Bool) := Fs[j].drop k
  have hmid : (es[j]).toWord = A ++ B := by
    calc
      (es[j]).toWord = Fs[j] := hg_j.symm
      _ = (Fs[j].take k) ++ (Fs[j].drop k) := (List.take_append_drop k (Fs[j])).symm
      _ = A ++ B := by simp [A, B]
  have hlenA' : A.length = B.length := by
    have h1 : A.length = k := by
      unfold A
      rw [List.length_take]
      rw [min_eq_left]
      omega
    have h2 : B.length = k := by
      unfold B
      rw [List.length_drop]
      rw [hlen]
      omega
    omega
  have hleft : ∃ X : List (Fin n × Bool),
      (es[j - 1]).toWord = X ++ FreeGroup.invRev A := by
    refine ⟨Fs[j - 1].take ((Fs[j - 1]).length - k), ?_⟩
    have htailA : (Fs[j - 1]).drop ((Fs[j - 1]).length - k) = FreeGroup.invRev A := by
      simpa [A] using htail
    calc
      (es[j - 1]).toWord = Fs[j - 1] := hg_jm.symm
      _ = (Fs[j - 1].take ((Fs[j - 1]).length - k))
            ++ (Fs[j - 1].drop ((Fs[j - 1]).length - k)) :=
            (List.take_append_drop ((Fs[j - 1]).length - k) (Fs[j - 1])).symm
      _ = (Fs[j - 1].take ((Fs[j - 1]).length - k)) ++ FreeGroup.invRev A := by
            rw [htailA]
  have hright : ∃ Z : List (Fin n × Bool),
      (es[j + 1]).toWord = FreeGroup.invRev B ++ Z := by
    refine ⟨Fs[j + 1].drop k, ?_⟩
    have hheadB : (Fs[j + 1]).take k = FreeGroup.invRev B := by
      simpa [B] using hhead
    calc
      (es[j + 1]).toWord = Fs[j + 1] := hg_jp.symm
      _ = (Fs[j + 1].take k) ++ (Fs[j + 1].drop k) :=
            (List.take_append_drop k (Fs[j + 1])).symm
      _ = FreeGroup.invRev B ++ (Fs[j + 1].drop k) := by
            rw [hheadB]
  rcases hleft with ⟨X, hX⟩
  rcases hright with ⟨Z, hZ⟩
  refine ⟨A, B, X, Z, hmid, hlenA', hX, hZ⟩
/-! ## Witnesses: the `B`-ending / `B⁻¹`-beginning basis images

From the balanced state (`aggregate_balanced_element`) the *right neighbour*
factor `es[j+1]` has word `invRev B ++ Z`.  If that factor is a basis image
`w_u = α(of u)`, then `w_u` itself *begins with* `B⁻¹` (the begins-with-
`B_p⁻¹` witness, consumed by `T3RebalanceTuple.rebalance_move_N_le_left`);
if it is the inverse `w_u⁻¹ = (α(of u))⁻¹`, then `w_u` *ends with* `B` (the
ends-with-`B_p` witness, consumed by `rebalance_move_N_le`).  The mirrored
witnesses from the left neighbour (word `X ++ invRev A`) are recorded
symmetrically.  Each lemma consumes the balanced-state datum `hbal` produced
by `aggregate_balanced_element` (balanced factor `j`) plus the orientation of
the neighbour factor; the three index-bound hypotheses make the factor
indexing well-formed.
-/

/-- Right-neighbour witness, `es[j+1] = +w_u`: `w_u` begins with `B⁻¹`
("mit dem Bestandteil `B_p⁻¹` anfängt"). -/
theorem witness_begin_invB {n : ℕ} (es : List (FreeGroup (Fin n)))
    {j : ℕ} (hj : j < es.length) (hmj : j - 1 < es.length) (hjp : j + 1 < es.length)
    (hbal : ∃ (A B X Z : List (Fin n × Bool)),
      (es[j]).toWord = A ++ B ∧ A.length = B.length ∧
      (es[j - 1]).toWord = X ++ FreeGroup.invRev A ∧
      (es[j + 1]).toWord = FreeGroup.invRev B ++ Z)
    (w : FreeGroup (Fin n)) (hu : es[j + 1] = w) :
    ∃ (B Y : List (Fin n × Bool)), w.toWord = FreeGroup.invRev B ++ Y := by
  rcases hbal with ⟨A, B, X, Z, hm, hAB, hl, hr⟩
  refine ⟨B, Z, ?_⟩
  rw [← hu]
  exact hr

/-- Right-neighbour witness, `es[j+1] = -w_u`: `w_u` ends with `B`
("mit dem Bestandteil `B_p` endigt"). -/
theorem witness_end_B {n : ℕ} (es : List (FreeGroup (Fin n)))
    {j : ℕ} (hj : j < es.length) (hmj : j - 1 < es.length) (hjp : j + 1 < es.length)
    (hbal : ∃ (A B X Z : List (Fin n × Bool)),
      (es[j]).toWord = A ++ B ∧ A.length = B.length ∧
      (es[j - 1]).toWord = X ++ FreeGroup.invRev A ∧
      (es[j + 1]).toWord = FreeGroup.invRev B ++ Z)
    (w : FreeGroup (Fin n)) (hu : es[j + 1] = w⁻¹) :
    ∃ (B Y : List (Fin n × Bool)), w.toWord = Y ++ B := by
  rcases hbal with ⟨A, B, X, Z, hm, hAB, hl, hr⟩
  refine ⟨B, FreeGroup.invRev Z, ?_⟩
  have hw : w = (es[j + 1])⁻¹ := by
    rw [hu]
    simp
  calc
    w.toWord = ((es[j + 1])⁻¹).toWord := by rw [hw]
    _ = FreeGroup.invRev (es[j + 1].toWord) := by rw [FreeGroup.toWord_inv]
    _ = FreeGroup.invRev (FreeGroup.invRev B ++ Z) := by rw [hr]
    _ = FreeGroup.invRev Z ++ B := by
        rw [FreeGroup.invRev_append]
        rw [FreeGroup.invRev_invRev]

/-- Left-neighbour witness, `es[j-1] = +w_v`: `w_v` ends with `A⁻¹`. -/
theorem witness_end_invA {n : ℕ} (es : List (FreeGroup (Fin n)))
    {j : ℕ} (hj : j < es.length) (hmj : j - 1 < es.length) (hjp : j + 1 < es.length)
    (hbal : ∃ (A B X Z : List (Fin n × Bool)),
      (es[j]).toWord = A ++ B ∧ A.length = B.length ∧
      (es[j - 1]).toWord = X ++ FreeGroup.invRev A ∧
      (es[j + 1]).toWord = FreeGroup.invRev B ++ Z)
    (w : FreeGroup (Fin n)) (hv : es[j - 1] = w) :
    ∃ (A Y : List (Fin n × Bool)), w.toWord = Y ++ FreeGroup.invRev A := by
  rcases hbal with ⟨A, B, X, Z, hm, hAB, hl, hr⟩
  refine ⟨A, X, ?_⟩
  rw [← hv]
  exact hl

/-- Left-neighbour witness, `es[j-1] = -w_v`: `w_v` begins with `A`. -/
theorem witness_begin_A {n : ℕ} (es : List (FreeGroup (Fin n)))
    {j : ℕ} (hj : j < es.length) (hmj : j - 1 < es.length) (hjp : j + 1 < es.length)
    (hbal : ∃ (A B X Z : List (Fin n × Bool)),
      (es[j]).toWord = A ++ B ∧ A.length = B.length ∧
      (es[j - 1]).toWord = X ++ FreeGroup.invRev A ∧
      (es[j + 1]).toWord = FreeGroup.invRev B ++ Z)
    (w : FreeGroup (Fin n)) (hv : es[j - 1] = w⁻¹) :
    ∃ (A Y : List (Fin n × Bool)), w.toWord = A ++ Y := by
  rcases hbal with ⟨A, B, X, Z, hm, hAB, hl, hr⟩
  refine ⟨A, FreeGroup.invRev X, ?_⟩
  have hw : w = (es[j - 1])⁻¹ := by
    rw [hv]
    simp
  calc
    w.toWord = ((es[j - 1])⁻¹).toWord := by rw [hw]
    _ = FreeGroup.invRev (es[j - 1].toWord) := by rw [FreeGroup.toWord_inv]
    _ = FreeGroup.invRev (X ++ FreeGroup.invRev A) := by rw [hl]
    _ = A ++ FreeGroup.invRev X := by
        rw [FreeGroup.invRev_append]
        rw [FreeGroup.invRev_invRev]

/-- Convenience: from the balanced aggregate state the two right-side
witnesses (basis image or its inverse) supply the `B`-ending /
`B⁻¹`-beginning structure of the corresponding basis image `w_u`. -/
theorem aggregate_witnesses_right {n : ℕ} (es : List (FreeGroup (Fin n)))
    {j : ℕ} (hj : j < es.length) (hmj : j - 1 < es.length) (hjp : j + 1 < es.length)
    (hbal : ∃ (A B X Z : List (Fin n × Bool)),
      (es[j]).toWord = A ++ B ∧ A.length = B.length ∧
      (es[j - 1]).toWord = X ++ FreeGroup.invRev A ∧
      (es[j + 1]).toWord = FreeGroup.invRev B ++ Z)
    (w : FreeGroup (Fin n)) (hu : es[j + 1] = w ∨ es[j + 1] = w⁻¹) :
    (∃ (B Y : List (Fin n × Bool)), w.toWord = FreeGroup.invRev B ++ Y) ∨
    (∃ (B Y : List (Fin n × Bool)), w.toWord = Y ++ B) := by
  rcases hu with hu | hu
  · left
    exact witness_begin_invB es hj hmj hjp hbal w hu
  · right
    exact witness_end_B es hj hmj hjp hbal w hu

/-! ### Assembled witnesses (balanced aggregate state → basis-image structure)

The next two theorems package the first link end-to-end: from the balanced
state of a confined interior factor `j` of the aggregate
(`aggregate_balanced_element`) and the orientation of the *right neighbour*
factor, the corresponding basis image `w_u = α(of u)` has the
`B⁻¹`-beginning / `B`-ending word structure that the rebalancing moves
`T3RebalanceTuple.rebalance_move_N_le_left` (resp. `rebalance_move_N_le`)
consume.  The `j`-index bounds make the factor indexing well-formed.
-/

/-- Balanced aggregate + right neighbour `= +α(of u)` gives the
begins-with-`B⁻¹` witness `w_u`. -/
theorem aggregate_witness_begin_invB {n : ℕ} {u : Fin n}
    (α : MulAut (FreeGroup (Fin n))) (es : List (FreeGroup (Fin n)))
    {j : ℕ} (hj : j < es.length) (hj0 : 0 < j) (hjk : j + 1 < es.length)
    (hm : j - 1 < es.length) (hconf : Confined (aggregateWords es) j)
    (hnotL : 2 * align ((es[j - 1]).toWord) ((es[j]).toWord) ≤ ((es[j]).toWord).length)
    (hnotR : 2 * align ((es[j]).toWord) ((es[j + 1]).toWord) ≤ ((es[j]).toWord).length)
    (hu : es[j + 1] = α (FreeGroup.of u)) :
    ∃ (B Y : List (Fin n × Bool)),
      (α (FreeGroup.of u)).toWord = FreeGroup.invRev B ++ Y := by
  have hbal := aggregate_balanced_element es hj hj0 hjk hm hconf hnotL hnotR
  exact witness_begin_invB es hj hm hjk hbal (α (FreeGroup.of u)) hu

/-- Balanced aggregate + right neighbour `= -(α(of u))` gives the
ends-with-`B` witness `w_u`. -/
theorem aggregate_witness_end_B {n : ℕ} {u : Fin n}
    (α : MulAut (FreeGroup (Fin n))) (es : List (FreeGroup (Fin n)))
    {j : ℕ} (hj : j < es.length) (hj0 : 0 < j) (hjk : j + 1 < es.length)
    (hm : j - 1 < es.length) (hconf : Confined (aggregateWords es) j)
    (hnotL : 2 * align ((es[j - 1]).toWord) ((es[j]).toWord) ≤ ((es[j]).toWord).length)
    (hnotR : 2 * align ((es[j]).toWord) ((es[j + 1]).toWord) ≤ ((es[j]).toWord).length)
    (hu : es[j + 1] = (α (FreeGroup.of u))⁻¹) :
    ∃ (B Y : List (Fin n × Bool)),
      (α (FreeGroup.of u)).toWord = Y ++ B := by
  have hbal := aggregate_balanced_element es hj hj0 hjk hm hconf hnotL hnotR
  exact witness_end_B es hj hm hjk hbal (α (FreeGroup.of u)) hu

end Submission.Nielsen
