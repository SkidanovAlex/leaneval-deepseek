import Submission.Work.RebalanceProtocol

open Submission.Nielsen
open Submission.FreeGroupAut
open Commons.GroupTheory.FreeGroup
open FreeGroup
set_option autoImplicit false

/-!
# Item 3, NoReappearance: what a surviving witness would have to look like

**The keystone lemma (to be formalised; statement fixed here).**  Let `S` be
an ordered state, `p` a row position whose element is *exactly-half absorbed*
via the witness `(m, j)` — middle factor `± α(a_{row p})` with word
`A ++ B` (`|A| = |B|`), the left neighbour covering `invRev A`, the right
neighbour covering `invRev B`.  The run's item-2 pass is over a coordinate
set `Q` (`Q` nodup, the balanced coordinate `c := row p` not in `Q`) at
`(c, A, B)` — **in the classical step `Q` is the set of *all* system
coordinates whose words end with `B` or begin with `B⁻¹`, and the pass is
iterated at fixed `p` until no such coordinate remains** (see
`FallTwoRunNotes.md`; the earlier "`Q` = the two neighbour factors" reading
is NOT the classical step — machine counterexample `FallTwoRunNotes.md`).  A
hypothetical surviving witness at a row position `i ≤ p` after the pass
would have to be an *entirely new aggregate* whose covering halves are built
from content created at the boundary of `Q`-words:

* the *old witness is destroyed*: the neighbour coordinates of the old
  witness are in the ends-with-`B` / begins-with-`B⁻¹` classes (from the
  covering word equations; `factor_inv_word_ends` / `factor_plus_word_begins`
  in `OldWitness.lean`), so the pass combines them against the unchanged
  balanced element (`c ∉ Q`, `item2Pass_fix` keeps `w_c = A ++ B`); the pass
  effects `item2Pass_apply_ends` / `item2Pass_apply_begins` below give the
  new neighbour words explicitly, and `PassLengths.pass_N_eq` the
  length-preservation of the balanced phase;
* *nothing else changed*: `item2Pass_fix` makes every non-`Q` coordinate —
  in particular every element at a row position `< p` that the run did not
  combine — inert.

The `B`-suffix of an ends-with-`B` element is replaced by `invRev A`, the
`B⁻¹`-prefix of a begins-with-`B⁻¹` element by `A` — content of length
`|A| = |B|` from the old balanced element.  The classical bound ("für diese
kommen nur Anfangs- und Endbestandteile bis zur Erzeugendenzahl von `A_p` in
Betracht, und solche sind keine neu entstanden, die nicht schon in `α_p`
vertreten waren", Nielsen 1919 p. 271) is exactly the assertion that such
new content cannot make an element at `i ≤ p` (which has reduced length at
most `2·|A|`) exactly-half absorbed; its faithful reduced-length
transcription is the remaining step.

**First real cases (proven in this module).**  The pass effects on the two
kinds of affected coordinates — the enumeration of everything a new witness
could be built from:

* `item2Pass_apply_ends`: a coordinate `q ∈ Q` whose word ends with `B` has
  new image `w_q · w_c⁻¹` after the pass (the `B`-suffix combined against the
  balanced element);
* `item2Pass_apply_begins`: a coordinate `q ∈ Q` whose word begins with
  `B⁻¹` (and does not end with `B`) has new image `w_c · w_q`.

Both are assembled from the product machinery (products fix what their
factors fix, `prod_fix`; a nodup list splits at its unique member,
`mem_split_unique`; the other entries fix both generators, hence their ratio
and product by `fix_ratio`/`fix_mul`) plus the elementary fixing and branch
identities of `RebalanceProtocol.item2`.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-- Products fix any element fixed by every factor. -/
theorem prod_fix {n : ℕ} (L : List (MulAut (FreeGroup (Fin n)))) (x : FreeGroup (Fin n))
    (hfix : ∀ σ ∈ L, σ x = x) : (List.prod L) x = x := by
  induction L with
  | nil => simp
  | cons σ t ih =>
      rw [List.prod_cons]
      change σ ((List.prod t) x) = x
      rw [ih (by
        intro τ hτ
        exact hfix τ (List.mem_cons.mpr (Or.inr hτ)))]
      exact hfix σ (by simp)

/-- A member of a nodup list splits the list around its unique occurrence. -/
lemma mem_split_unique {α : Type*} {L : List α} {σ : α} (h : σ ∈ L)
    (hnd : L.Nodup) : ∃ L₁ L₂ : List α, L = L₁ ++ σ :: L₂ ∧ σ ∉ L₁ ∧ σ ∉ L₂ := by
  induction L with
  | nil => cases h
  | cons τ t ih =>
      rw [List.mem_cons] at h
      rcases h with rfl | ht
      · refine ⟨[], t, rfl, ?_, ?_⟩
        · simp
        · exact (List.nodup_cons.mp hnd).1
      · have hndt : t.Nodup := (List.nodup_cons.mp hnd).2
        rcases ih ht hndt with ⟨L₁, L₂, hsplit, h1, h2⟩
        refine ⟨τ :: L₁, L₂, ?_, ?_, h2⟩
        · rw [hsplit]
          rfl
        · intro hmem
          rcases List.mem_cons.mp hmem with h | h'
          · exact (List.nodup_cons.mp hnd).1 (by simpa [h] using ht)
          · exact h1 h'

/-- An automorphism fixing two generators fixes their ratio. -/
lemma fix_ratio {n : ℕ} (σ : MulAut (FreeGroup (Fin n))) (q c : Fin n)
    (hq : σ (FreeGroup.of q) = FreeGroup.of q) (hc : σ (FreeGroup.of c) = FreeGroup.of c) :
    σ (FreeGroup.of q * (FreeGroup.of c)⁻¹) = FreeGroup.of q * (FreeGroup.of c)⁻¹ := by
  change ((σ : FreeGroup (Fin n) →* FreeGroup (Fin n)) (FreeGroup.of q * (FreeGroup.of c)⁻¹)) = _
  rw [(σ : FreeGroup (Fin n) →* FreeGroup (Fin n)).map_mul]
  rw [(σ : FreeGroup (Fin n) →* FreeGroup (Fin n)).map_inv]
  have hq' : (σ : FreeGroup (Fin n) →* FreeGroup (Fin n)) (FreeGroup.of q) = FreeGroup.of q := by
    simpa using hq
  have hc' : (σ : FreeGroup (Fin n) →* FreeGroup (Fin n)) (FreeGroup.of c) = FreeGroup.of c := by
    simpa using hc
  rw [hq', hc']

/-- An automorphism fixing two elements fixes their product. -/
lemma fix_mul {n : ℕ} (σ : MulAut (FreeGroup (Fin n))) (x y : FreeGroup (Fin n))
    (hx : σ x = x) (hy : σ y = y) : σ (x * y) = x * y := by
  change ((σ : FreeGroup (Fin n) →* FreeGroup (Fin n)) (x * y)) = x * y
  rw [(σ : FreeGroup (Fin n) →* FreeGroup (Fin n)).map_mul]
  have hx' : (σ : FreeGroup (Fin n) →* FreeGroup (Fin n)) x = x := by simpa using hx
  have hy' : (σ : FreeGroup (Fin n) →* FreeGroup (Fin n)) y = y := by simpa using hy
  rw [hx', hy']

/-- **Pass effect, ends-with-`B`.**  A coordinate `q ∈ Q` whose word ends
with `B` (the second half of the balanced element at `c`) has new image
`w_q · w_c⁻¹` after the item-2 pass over `Q`: the `B`-suffix is combined
against the balanced element, and every other coordinate of the pass fixes
the result. -/
theorem item2Pass_apply_ends {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (c : Fin n)
    (A B : List (Fin n × Bool)) (Q : List (Fin n))
    (hnd : Q.Nodup) {q : Fin n} (hq : q ∈ Q) (hqc : q ≠ c) (hcQ : c ∉ Q)
    (hE : ∃ Y : List (Fin n × Bool), (α (FreeGroup.of q)).toWord = Y ++ B) :
    (α * item2Pass α c A B Q) (FreeGroup.of q) =
      (α (FreeGroup.of q)) * (α (FreeGroup.of c))⁻¹ := by
  classical
  let f : Fin n → MulAut (FreeGroup (Fin n)) := fun q' => item2 α c q' A B
  let x : FreeGroup (Fin n) := FreeGroup.of q * (FreeGroup.of c)⁻¹
  rcases mem_split_unique hq hnd with ⟨Q₁, Q₂, hQ, hq1, hq2⟩
  have hfix2 : ∀ σ ∈ Q₂.map f, σ (FreeGroup.of q) = FreeGroup.of q := by
    intro σ hσ
    rcases List.mem_map.mp hσ with ⟨q'', hq'', rfl⟩
    exact item2_fix_generator α c q'' q A B (by
      intro heq
      exact hq2 (by simpa [heq] using hq''))
  have hfix2p := prod_fix (Q₂.map f) (FreeGroup.of q) hfix2
  have hfix1 : ∀ σ ∈ Q₁.map f, σ x = x := by
    intro σ hσ
    rcases List.mem_map.mp hσ with ⟨q'', hq'', rfl⟩
    have hqnc : q ≠ q'' := by
      intro heq
      exact hq1 (by simpa [heq] using hq'')
    have hcnc : c ≠ q'' := by
      intro heq
      exact hcQ (by
        rw [hQ]
        exact List.mem_append.mpr (Or.inl (by simpa [heq] using hq'')))
    have hfq : (item2 α c q'' A B) (FreeGroup.of q) = FreeGroup.of q :=
      item2_fix_generator α c q'' q A B hqnc
    have hfc : (item2 α c q'' A B) (FreeGroup.of c) = FreeGroup.of c :=
      item2_fix_generator α c q'' c A B hcnc
    exact fix_ratio (item2 α c q'' A B) q c hfq hfc
  have hfix1p := prod_fix (Q₁.map f) x hfix1
  have hmove : (item2 α c q A B) (FreeGroup.of q) = x := by
    rw [item2_eq_rhoNeg α hqc A B hE]
    have hself := rhoNeg_apply_self q c hqc
    simpa [x] using hself
  unfold item2Pass
  rw [hQ]
  rw [List.map_append, List.map_cons, List.prod_append, List.prod_cons]
  change α (((Q₁.map f).prod * (item2 α c q A B * (Q₂.map f).prod)) (FreeGroup.of q)) =
      (α (FreeGroup.of q)) * (α (FreeGroup.of c))⁻¹
  calc
    α (((Q₁.map f).prod * (item2 α c q A B * (Q₂.map f).prod)) (FreeGroup.of q))
        = α ((Q₁.map f).prod ((item2 α c q A B * (Q₂.map f).prod) (FreeGroup.of q))) := rfl
    _ = α ((Q₁.map f).prod ((item2 α c q A B) ((Q₂.map f).prod (FreeGroup.of q)))) := rfl
    _ = α ((Q₁.map f).prod ((item2 α c q A B) (FreeGroup.of q))) := by rw [hfix2p]
    _ = α ((Q₁.map f).prod x) := by rw [hmove]
    _ = α x := by rw [hfix1p]
    _ = (α (FreeGroup.of q)) * (α (FreeGroup.of c))⁻¹ := by
          change ((α : FreeGroup (Fin n) →* FreeGroup (Fin n)) (FreeGroup.of q * (FreeGroup.of c)⁻¹)) = _
          rw [(α : FreeGroup (Fin n) →* FreeGroup (Fin n)).map_mul]
          rw [(α : FreeGroup (Fin n) →* FreeGroup (Fin n)).map_inv]
          rfl

/-- **Pass effect, begins-with-`B⁻¹`.**  A coordinate `q ∈ Q` whose word
begins with `B⁻¹` (and does not end with `B`) has new image `w_c · w_q` after
the item-2 pass over `Q`: the `B⁻¹`-prefix is combined against the balanced
element, and every other coordinate of the pass fixes the result. -/
theorem item2Pass_apply_begins {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (c : Fin n)
    (A B : List (Fin n × Bool)) (Q : List (Fin n))
    (hnd : Q.Nodup) {q : Fin n} (hq : q ∈ Q) (hqc : q ≠ c) (hcQ : c ∉ Q)
    (hnoE : ¬ ∃ Y : List (Fin n × Bool), (α (FreeGroup.of q)).toWord = Y ++ B)
    (hB : ∃ Y : List (Fin n × Bool),
      (α (FreeGroup.of q)).toWord = FreeGroup.invRev B ++ Y) :
    (α * item2Pass α c A B Q) (FreeGroup.of q) =
      (α (FreeGroup.of c)) * (α (FreeGroup.of q)) := by
  classical
  let f : Fin n → MulAut (FreeGroup (Fin n)) := fun q' => item2 α c q' A B
  let x : FreeGroup (Fin n) := FreeGroup.of c * FreeGroup.of q
  rcases mem_split_unique hq hnd with ⟨Q₁, Q₂, hQ, hq1, hq2⟩
  have hfix2 : ∀ σ ∈ Q₂.map f, σ (FreeGroup.of q) = FreeGroup.of q := by
    intro σ hσ
    rcases List.mem_map.mp hσ with ⟨q'', hq'', rfl⟩
    exact item2_fix_generator α c q'' q A B (by
      intro heq
      exact hq2 (by simpa [heq] using hq''))
  have hfix2p := prod_fix (Q₂.map f) (FreeGroup.of q) hfix2
  have hfix1 : ∀ σ ∈ Q₁.map f, σ x = x := by
    intro σ hσ
    rcases List.mem_map.mp hσ with ⟨q'', hq'', rfl⟩
    have hqnc : q ≠ q'' := by
      intro heq
      exact hq1 (by simpa [heq] using hq'')
    have hcnc : c ≠ q'' := by
      intro heq
      exact hcQ (by
        rw [hQ]
        exact List.mem_append.mpr (Or.inl (by simpa [heq] using hq'')))
    have hfq : (item2 α c q'' A B) (FreeGroup.of q) = FreeGroup.of q :=
      item2_fix_generator α c q'' q A B hqnc
    have hfc : (item2 α c q'' A B) (FreeGroup.of c) = FreeGroup.of c :=
      item2_fix_generator α c q'' c A B hcnc
    exact fix_mul (item2 α c q'' A B) (FreeGroup.of c) (FreeGroup.of q) hfc hfq
  have hfix1p := prod_fix (Q₁.map f) x hfix1
  have hmove : (item2 α c q A B) (FreeGroup.of q) = x := by
    rw [item2_eq_lam α hqc A B hnoE hB]
    have hself := lam_apply_self q c hqc
    simpa [x] using hself
  unfold item2Pass
  rw [hQ]
  rw [List.map_append, List.map_cons, List.prod_append, List.prod_cons]
  change α (((Q₁.map f).prod * (item2 α c q A B * (Q₂.map f).prod)) (FreeGroup.of q)) =
      (α (FreeGroup.of c)) * (α (FreeGroup.of q))
  calc
    α (((Q₁.map f).prod * (item2 α c q A B * (Q₂.map f).prod)) (FreeGroup.of q))
        = α ((Q₁.map f).prod ((item2 α c q A B * (Q₂.map f).prod) (FreeGroup.of q))) := rfl
    _ = α ((Q₁.map f).prod ((item2 α c q A B) ((Q₂.map f).prod (FreeGroup.of q)))) := rfl
    _ = α ((Q₁.map f).prod ((item2 α c q A B) (FreeGroup.of q))) := by rw [hfix2p]
    _ = α ((Q₁.map f).prod x) := by rw [hmove]
    _ = α x := by rw [hfix1p]
    _ = (α (FreeGroup.of c)) * (α (FreeGroup.of q)) := by
          change ((α : FreeGroup (Fin n) →* FreeGroup (Fin n)) (FreeGroup.of c * FreeGroup.of q)) = _
          rw [(α : FreeGroup (Fin n) →* FreeGroup (Fin n)).map_mul]
          rfl

end Submission.Nielsen
