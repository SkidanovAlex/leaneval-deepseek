import Mathlib
import Submission.Work.IntLib.encodeNatBridge
import Submission.Work.Layout.SortDefs
import Submission.Work.Layout.Move
import Submission.Work.Layout.Base

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Definitions for the `mergePair` cost analysis

`mergePair` merges the two top runs of `SX`/`SY` (the lists `P`/`Q`) onto `T`/`D`, comparing *cached
key sizes*: each run stack has an associated "cache" stack (`SA` for `SX`, `SB` for `SY`) holding the
key sizes of the records, most recently exposed on top.

* `ksv v` is the cached value for the record `v`: `Val.int (bit-size of pairKey v)`.
* `cache P₁ P₂` is the cache for a run `P = P₁ ++ P₂` of which `P₁` has already been moved: the keys
  sizes of `P₁ ++ [P₂.head]` in reverse order (so the current front's size is on top).
* `cmpCost ks ls` is the ℕ-valued cost of the sequence of comparisons performed by the merge of the
  key lists `ks` and `ls` (one `(k.size).size + (l.size).size + 4` per comparison, where `4` accounts
  for the two `isz` constants); it is bounded by `Work.Layout.cmpCost_le`.
-/

namespace Work.Layout

open HvdH
open Work.Layout.Sk

/-- the cached value of a record: the bit-size of its key -/
def ksv (v : Val) : Val := Val.int (((pairKey v).toNat : ℕ).size : ℤ)

/-- the cache of a run `P = P₁ ++ P₂`: the key sizes of `P₁ ++ [P₂.head]`, current front on top -/
def cache (P₁ P₂ : List Val) : List Val := ((P₁ ++ P₂.take 1).map ksv).reverse

/-- the comparison cost of merging the key lists `ks`, `ls` (moves the head of `ls` when it is
smaller, else the head of `ks`, as `Sk.merge2` does) -/
def cmpCost : List ℕ → List ℕ → ℕ
  | k :: ks, l :: ls => (k.size).size + (l.size).size + 4 +
      (if l < k then cmpCost (k :: ks) ls else cmpCost ks (l :: ls))
  | _, _ => 0

/-! ## elementary facts about `Nat.size` -/

theorem size_le_self (n : ℕ) : n.size ≤ n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · exact Nat.size_le.mpr (by simpa using Nat.lt_two_pow_self (n := n))

theorem lt_of_size_lt {k' k : ℕ} (h : k'.size < k.size) : k' < k :=
  Nat.lt_of_lt_of_le (Nat.lt_size_self k') (Nat.lt_size.mp h)

/-! ## basic facts about records and caches -/

theorem pairKey_record (k : ℕ) (v' : Val) : pairKey (Val.cons (Val.int (k : ℤ)) v') = (k : ℤ) := rfl

theorem ksv_record (k : ℕ) (v' : Val) :
    ksv (Val.cons (Val.int (k : ℤ)) v') = Val.int (k.size : ℤ) := by
  simp [ksv, pairKey]

theorem isz_natCast (k : ℕ) : isz (k : ℤ) = k.size + 2 := by simp [isz]

theorem vsz_int (z : ℤ) : vsz (Val.int z) = isz z := Work.IntLib.vsz_int z

theorem vsz_record (k : ℕ) (v' : Val) :
    vsz (Val.cons (Val.int (k : ℤ)) v') = k.size + 3 + vsz v' := by
  have h : vsz (Val.cons (Val.int (k : ℤ)) v') = vsz (Val.int (k:ℤ)) + vsz v' + 1 := by
    simp only [vsz, Val.enc, List.length_cons, List.length_append, List.length_map,
      List.length_nil]
  rw [h, vsz_int, isz_natCast]; omega

theorem isz_le_vsz_record (k : ℕ) (v' : Val) :
    isz (k : ℤ) ≤ vsz (Val.cons (Val.int (k : ℤ)) v') := by
  rw [vsz_record, isz_natCast]; omega

theorem vsz_ksv (v : Val) : vsz (ksv v) = isz (((pairKey v).toNat : ℕ).size : ℤ) := by
  rw [ksv, vsz_int]

theorem vsz_ksv_record (k : ℕ) (v' : Val) :
    vsz (ksv (Val.cons (Val.int (k : ℤ)) v')) = isz (k.size : ℤ) := by
  rw [ksv_record, vsz_int]

theorem isz_ksv (k : ℕ) : isz (k.size : ℤ) = (k.size).size + 2 := isz_natCast _

theorem cache_nil (P₁ : List Val) : cache P₁ [] = (P₁.map ksv).reverse := by simp [cache]

theorem cache_take1 (P₁ P₂ : List Val) :
    cache P₁ P₂ = ((P₂.take 1).map ksv).reverse ++ (P₁.map ksv).reverse := by
  simp [cache, List.map_append, List.reverse_append]

theorem cache_cons (P₁ : List Val) (p : Val) (ps : List Val) :
    cache P₁ (p :: ps) = ksv p :: (P₁.map ksv).reverse := by
  rw [cache_take1]
  simp

theorem cache_move (P₁ : List Val) (p : Val) (ps : List Val) :
    cache (P₁ ++ [p]) ps = ((ps.take 1).map ksv).reverse ++ cache P₁ (p :: ps) := by
  rw [cache_take1, cache_take1]
  simp [List.map_append]

theorem encs_cache_cons (P₁ : List Val) (p : Val) (ps : List Val) :
    encs (cache P₁ (p :: ps)) = (ksv p).enc ++ encs ((P₁.map ksv).reverse) := by
  rw [cache_cons]; rfl

theorem encs_cache_nil (P₁ : List Val) : encs (cache P₁ []) = encs ((P₁.map ksv).reverse) := by
  rw [cache_nil]

theorem gMark_not_mem_encs_mg {vs : List Val} : gMark ∉ encs vs := by
  induction vs with
  | nil => simp [encs]
  | cons v vs ih =>
      simp only [encs, List.map_cons, List.flatten_cons, List.mem_append]
      exact fun h => h.elim (gMark_not_mem_enc v) ih

/-- `Sk.gMark` is not in any cache -/
theorem gMark_not_mem_cache (P₁ P₂ : List Val) : gMark ∉ encs (cache P₁ P₂) :=
  gMark_not_mem_encs_mg

/-! ## cost constants and the trace cost of the comparison phase -/

/-- the key of a record, as a natural number -/
def keyOf (v : Val) : ℕ := (pairKey v).toNat

/-- size of the cached value of `v` (the cost of pushing it) -/
def kszOf (v : Val) : ℕ := isz (((pairKey v).toNat : ℕ).size : ℤ)

/-- per-comparison coefficient -/
def cCmp (KLt : ℕ) : ℕ := 100 + 2 * KLt
/-- per-move coefficient -/
def cMov (KLt : ℕ) : ℕ := 300 + 3 * KLt
/-- per-exposed-record coefficient -/
def cExp (KSz : ℕ) : ℕ := 60 + KSz
/-- constant per-iteration overhead -/
def cK : ℕ := 800

/-- the coefficient in the bound on `mrgCost` -/
def MRC (KLt KSz : ℕ) : ℕ := 20 * cCmp KLt + cMov KLt + 2 * cExp KSz + cK + 4 * cExp KSz + 100

/-- the cost charged to one comparison step of the merge -/
def mrgStep (KLt KSz : ℕ) (p : Val) (ps : List Val) (q : Val) (qs : List Val) : ℕ :=
  cCmp KLt * ((keyOf p).size.size + (keyOf q).size.size + 4)
  + cMov KLt * (vsz (if keyOf q < keyOf p then q else p) + 1)
  + cExp KSz * (vsz (if keyOf q < keyOf p then (if qs = [] then Val.nil else qs.headD Val.nil)
                     else (if ps = [] then Val.nil else ps.headD Val.nil)) + 2)
  + cK

theorem le_mrgStep (KLt KSz : ℕ) (p : Val) (ps : List Val) (q : Val) (qs : List Val) :
    20 ≤ mrgStep KLt KSz p ps q qs := by
  unfold mrgStep cK
  omega

/-- the bound on one `Sk.mergeStep` (the loop overhead is charged separately) -/
def mrgStepCore (KLt KSz : ℕ) (p : Val) (ps : List Val) (q : Val) (qs : List Val) : ℕ :=
  mrgStep KLt KSz p ps q qs - 20

/-- the accumulated cost of the comparison phase of the merge (while both runs are nonempty) -/
def mrgCost (KLt KSz : ℕ) : List Val → List Val → ℕ
  | p :: ps, q :: qs => mrgStep KLt KSz p ps q qs +
      (if keyOf q < keyOf p then mrgCost KLt KSz (p :: ps) qs
         else mrgCost KLt KSz ps (q :: qs))
  | _, _ => 0

theorem keyOf_record (k : ℕ) (v' : Val) : keyOf (Val.cons (Val.int (k : ℤ)) v') = k := by
  simp [keyOf, pairKey]

theorem kszOf_record (k : ℕ) (v' : Val) :
    kszOf (Val.cons (Val.int (k : ℤ)) v') = isz (k.size : ℤ) := by
  simp [kszOf, keyOf, pairKey]

theorem kszOf_le_vsz (k : ℕ) (v' : Val) :
    kszOf (Val.cons (Val.int (k : ℤ)) v') ≤ vsz (Val.cons (Val.int (k : ℤ)) v') := by
  rw [kszOf_record, vsz_record]
  have h1 : isz (k.size : ℤ) = (k.size).size + 2 := isz_natCast (k.size)
  have h2 : (k.size).size ≤ k.size := size_le_self k.size
  omega


/-- for a record `v = cons (int k) v'`: the key size is at most its size -/
theorem isz_key_le_vsz (k : ℕ) (v' : Val) : isz (k : ℤ) ≤ vsz (Val.cons (Val.int (k : ℤ)) v') :=
  isz_le_vsz_record k v'

theorem keyOf_lt_of_lt {v w : Val} {k l : ℕ} (hv : keyOf v = k) (hw : keyOf w = l) (h : l < k) :
    l < k := h

/-! ## frame bookkeeping -/

/-- the stacks the merge loop may change -/
def loopTouched (SX SY T SA SB : Stk) : Finset Stk := {SX, SY, T, SA, SB}

/-- the stacks `Sk.mergeStep` may change -/
def stepTouched (SX SY SA SB T F1 F2 t d : Stk) : Finset Stk := {SX, SY, SA, SB, T, F1, F2, t, d, 0}

theorem not_mem_loopTouched {SX SY T SA SB k : Stk} (h : k ∉ loopTouched SX SY T SA SB) :
    k ≠ SX ∧ k ≠ SY ∧ k ≠ T ∧ k ≠ SA ∧ k ≠ SB := by
  simp only [loopTouched, Finset.mem_insert, Finset.mem_singleton] at h
  tauto

theorem not_mem_loopTouched_of {SX SY T SA SB k : Stk} (h1 : k ≠ SX) (h2 : k ≠ SY) (h3 : k ≠ T)
    (h4 : k ≠ SA) (h5 : k ≠ SB) : k ∉ loopTouched SX SY T SA SB := by
  simp only [loopTouched, Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- a frame condition for `mergeStep` plus the values of `F1,F2,t,d,0` gives a frame condition for
the merge loop -/
theorem frame_step_of_loop {X S : Stk → List Glyph} {SX SY T SA SB F1 F2 t d : Stk}
    (hstep : ∀ k', k' ∉ stepTouched SX SY SA SB T F1 F2 t d → X k' = S k')
    (hF1 : X F1 = S F1) (hF2 : X F2 = S F2) (ht : X t = S t) (hd : X d = S d) (h0 : X 0 = S 0)
    {k' : Stk} (hk : k' ∉ loopTouched SX SY T SA SB) : X k' = S k' := by
  by_cases hm : k' ∈ stepTouched SX SY SA SB T F1 F2 t d
  · obtain ⟨e1, e2, e3, e4, e5⟩ := not_mem_loopTouched hk
    simp only [stepTouched, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl e1
    · exact absurd rfl e2
    · exact absurd rfl e4
    · exact absurd rfl e5
    · exact absurd rfl e3
    · exact hF1
    · exact hF2
    · exact ht
    · exact hd
    · exact h0
  · exact hstep k' hm

theorem stepTouched_of_not_mem {SX SY T SA SB F1 F2 t d : Stk} {x : Stk}
    (h : x ∉ loopTouched SX SY T SA SB) (h1 : x ≠ F1) (h2 : x ≠ F2) (h3 : x ≠ t) (h4 : x ≠ d)
    (h5 : x ≠ 0) : x ∉ stepTouched SX SY SA SB T F1 F2 t d := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := not_mem_loopTouched h
  simp only [stepTouched, Finset.mem_insert, Finset.mem_singleton]
  tauto

/-! ## further cache facts -/

theorem cache_append_nil (P₁ : List Val) (p : Val) : cache (P₁ ++ [p]) [] = cache P₁ [p] := by
  simp [cache, List.map_append]

theorem pairKey_record_lt (k l : ℕ) (v' w' : Val) :
    (pairKey (Val.cons (Val.int (k : ℤ)) v') < pairKey (Val.cons (Val.int (l : ℤ)) w')) ↔ k < l := by
  simp [pairKey]

theorem keyOf_record_le_iff {k l : ℕ} {v' w' : Val} :
    (keyOf (Val.cons (Val.int (k : ℤ)) v') ≤ keyOf (Val.cons (Val.int (l : ℤ)) w')) ↔ k ≤ l := by
  simp [keyOf, pairKey]

theorem headD_encs_nil (A : List Glyph) :
    (encs ([] : List Val) ++ A).headD Glyph.eos = A.headD Glyph.eos := by
  simp [encs]

theorem mrgHeadD_encs_cons (v : Val) (vs : List Val) (A : List Glyph) :
    (encs (v :: vs) ++ A).headD Glyph.eos = v.enc.headD Glyph.eos := by
  have hv : v.enc ≠ [] := by
    cases v <;> simp [Val.enc]
  rw [show encs (v :: vs) ++ A = v.enc ++ (encs vs ++ A) by
    simp only [encs, List.map_cons, List.flatten_cons, List.append_assoc]]
  cases h : v.enc with
  | nil => exact absurd h hv
  | cons a t => simp [h, List.cons_append]

theorem encs_length (CL : List Val) : (encs CL).length = (CL.map vsz).sum := by
  induction CL with
  | nil => simp [encs]
  | cons v vs ih =>
      have hsplit : encs (v :: vs) = (Val.enc v) ++ encs vs := by
        simp only [encs, List.map_cons, List.flatten_cons]
      rw [hsplit, List.length_append, ih]
      rfl

theorem vsz_ksv_le_record (k : ℕ) (v' : Val) :
    vsz (ksv (Val.cons (Val.int (k : ℤ)) v')) ≤ vsz (Val.cons (Val.int (k : ℤ)) v') := by
  rw [ksv_record, vsz_int, isz_natCast, vsz_record]
  have h := size_le_self k.size
  omega

theorem sum_map_reverse (l : List Val) (f : Val → ℕ) : ((l.reverse).map f).sum = (l.map f).sum := by
  rw [List.map_reverse, List.sum_reverse]

theorem sum_map_le_of_pointwise {l : List Val} {F G : Val → ℕ} (h : ∀ v ∈ l, F v ≤ G v) :
    (l.map F).sum ≤ (l.map G).sum := by
  induction l with
  | nil => simp
  | cons v vs ih =>
      simp only [List.map_cons, List.sum_cons]
      have h1 := h v (by simp)
      have h2 := ih (fun w hw => h w (by simp [hw]))
      omega

theorem sum_take_one_le (l : List Val) (F : Val → ℕ) :
    ((l.take 1).map F).sum ≤ (l.map F).sum := by
  cases l with
  | nil => simp
  | cons v vs => simp

theorem sum_vsz_cache_le (P₁ P₂ : List Val)
    (hrec : ∀ v ∈ P₁ ++ P₂, ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v') :
    ((cache P₁ P₂).map vsz).sum ≤ ((P₁ ++ P₂).map vsz).sum + 2 * (P₁ ++ P₂).length := by
  simp only [cache_take1, List.map_append, List.sum_append]
  have hA : ((((P₂.take 1).map ksv).reverse).map vsz).sum ≤ (P₂.map vsz).sum := by
    simp only [List.map_reverse, List.sum_reverse, List.map_map]
    refine (sum_map_le_of_pointwise (fun v hv => ?_)).trans (sum_take_one_le P₂ vsz)
    obtain ⟨k, v', rfl⟩ := hrec v (List.mem_append_right _ (List.mem_of_mem_take hv))
    exact vsz_ksv_le_record k v'
  have hB : (((P₁.map ksv).reverse).map vsz).sum ≤ (P₁.map vsz).sum := by
    simp only [List.map_reverse, List.sum_reverse, List.map_map]
    exact sum_map_le_of_pointwise (fun v hv => by
      obtain ⟨k, v', rfl⟩ := hrec v (List.mem_append_left _ hv)
      exact vsz_ksv_le_record k v')
  have hlen : (P₂.take 1).length ≤ P₂.length := by
    cases P₂ with
    | nil => simp
    | cons v vs => simp
  have hlen' : (P₁ ++ P₂).length = P₁.length + P₂.length := List.length_append ..
  omega

theorem hdis_notMem {SX SY T SA SB F1 F2 t d : Stk}
    (hdis : ([SX, SY, T, SA, SB, F1, F2, t, d, 0] : List Stk).Nodup) :
    F1 ∉ loopTouched SX SY T SA SB ∧ F2 ∉ loopTouched SX SY T SA SB ∧
    t ∉ loopTouched SX SY T SA SB ∧ d ∉ loopTouched SX SY T SA SB ∧
    (0 : Stk) ∉ loopTouched SX SY T SA SB := by
  have hp := hdis
  rw [List.nodup_cons] at hp; obtain ⟨h1, hp⟩ := hp
  rw [List.nodup_cons] at hp; obtain ⟨h2, hp⟩ := hp
  rw [List.nodup_cons] at hp; obtain ⟨h3, hp⟩ := hp
  rw [List.nodup_cons] at hp; obtain ⟨h4, hp⟩ := hp
  rw [List.nodup_cons] at hp; obtain ⟨h5, _⟩ := hp
  have memtail : ∀ x : Stk, x ∈ [F1, F2, t, d, (0 : Stk)] →
      x ∈ ([SY, T, SA, SB, F1, F2, t, d, 0] : List Stk) ∧
      x ∈ ([T, SA, SB, F1, F2, t, d, 0] : List Stk) ∧
      x ∈ ([SA, SB, F1, F2, t, d, 0] : List Stk) ∧
      x ∈ ([SB, F1, F2, t, d, 0] : List Stk) ∧
      x ∈ ([F1, F2, t, d, 0] : List Stk) := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, List.mem_singleton] at hx
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      (simp only [List.mem_cons, List.not_mem_nil, List.mem_singleton]; tauto)
  have e1 : ∀ x, x ∈ [F1, F2, t, d, (0 : Stk)] → x ≠ SX := by
    intro x hx h
    subst h
    exact h1 (memtail x hx).1
  have e2 : ∀ x, x ∈ [F1, F2, t, d, (0 : Stk)] → x ≠ SY := by
    intro x hx h
    subst h
    exact h2 (memtail x hx).2.1
  have e3 : ∀ x, x ∈ [F1, F2, t, d, (0 : Stk)] → x ≠ T := by
    intro x hx h
    subst h
    exact h3 (memtail x hx).2.2.1
  have e4 : ∀ x, x ∈ [F1, F2, t, d, (0 : Stk)] → x ≠ SA := by
    intro x hx h
    subst h
    exact h4 (memtail x hx).2.2.2.1
  have e5 : ∀ x, x ∈ [F1, F2, t, d, (0 : Stk)] → x ≠ SB := by
    intro x hx h
    subst h
    exact h5 (memtail x hx).2.2.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact not_mem_loopTouched_of (e1 F1 (by simp)) (e2 F1 (by simp)) (e3 F1 (by simp))
      (e4 F1 (by simp)) (e5 F1 (by simp))
  · exact not_mem_loopTouched_of (e1 F2 (by simp)) (e2 F2 (by simp)) (e3 F2 (by simp))
      (e4 F2 (by simp)) (e5 F2 (by simp))
  · exact not_mem_loopTouched_of (e1 t (by simp)) (e2 t (by simp)) (e3 t (by simp))
      (e4 t (by simp)) (e5 t (by simp))
  · exact not_mem_loopTouched_of (e1 d (by simp)) (e2 d (by simp)) (e3 d (by simp))
      (e4 d (by simp)) (e5 d (by simp))
  · exact not_mem_loopTouched_of (e1 0 (by simp)) (e2 0 (by simp)) (e3 0 (by simp))
      (e4 0 (by simp)) (e5 0 (by simp))

theorem merge2_cons_of_lt {p q : Val} {ps qs : List Val} (h : pairKey q < pairKey p) :
    merge2 (p :: ps) (q :: qs) = q :: merge2 (p :: ps) qs := by
  simp only [merge2, if_pos h]

theorem merge2_cons_of_ge {p q : Val} {ps qs : List Val} (h : ¬ (pairKey q < pairKey p)) :
    merge2 (p :: ps) (q :: qs) = p :: merge2 ps (q :: qs) := by
  simp only [merge2, if_neg h]

theorem merge2_nil_left (Q : List Val) : merge2 [] Q = Q := by
  simp only [merge2]

theorem merge2_nil_right (P : List Val) : merge2 P [] = P := by
  cases P with
  | nil => simp only [merge2]
  | cons p ps => simp only [merge2]

theorem merge2_sum_vsz_aux (n : ℕ) : ∀ (P Q : List Val), P.length + Q.length = n →
    ((merge2 P Q).map vsz).sum = ((P ++ Q).map vsz).sum := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro P Q hlen
    cases P with
    | nil => rw [merge2_nil_left]; simp
    | cons p ps =>
      cases Q with
      | nil => rw [merge2_nil_right]; simp
      | cons q qs =>
        by_cases h : pairKey q < pairKey p
        · rw [merge2_cons_of_lt h, List.map_cons, List.sum_cons]
          rw [ih _ (by simp only [List.length_cons] at hlen ⊢; omega) (p :: ps) qs rfl]
          simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons]
          omega
        · rw [merge2_cons_of_ge h, List.map_cons, List.sum_cons]
          rw [ih _ (by simp only [List.length_cons] at hlen ⊢; omega) ps (q :: qs) rfl]
          simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons]
          omega

theorem merge2_sum_vsz (P Q : List Val) :
    ((merge2 P Q).map vsz).sum = ((P ++ Q).map vsz).sum :=
  merge2_sum_vsz_aux _ P Q rfl

theorem merge2_length_aux (n : ℕ) : ∀ (P Q : List Val), P.length + Q.length = n →
    (merge2 P Q).length = (P ++ Q).length := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro P Q hlen
    cases P with
    | nil => rw [merge2_nil_left]; simp
    | cons p ps =>
      cases Q with
      | nil => rw [merge2_nil_right]; simp
      | cons q qs =>
        by_cases h : pairKey q < pairKey p
        · rw [merge2_cons_of_lt h, List.length_cons,
            ih _ (by simp only [List.length_cons] at hlen ⊢; omega) (p :: ps) qs rfl]
          simp only [List.length_append, List.length_cons]
          omega
        · rw [merge2_cons_of_ge h, List.length_cons,
            ih _ (by simp only [List.length_cons] at hlen ⊢; omega) ps (q :: qs) rfl]
          simp only [List.length_append, List.length_cons]
          omega

theorem mrgMerge2_length (P Q : List Val) : (merge2 P Q).length = (P ++ Q).length :=
  merge2_length_aux _ P Q rfl

end Work.Layout
