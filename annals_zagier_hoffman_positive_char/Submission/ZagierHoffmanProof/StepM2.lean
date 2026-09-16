import Submission.ZagierHoffmanProof.StepM1

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step M2: the Init-comparison engine (`InitLt_of_head_gt`)

The type-3 outputs of the (2.14) chain have tuples `(s₁,…,s_{j−1}, s_j+1, τ…)`: they
agree with `s` below position `j−1`, are bigger at `j−1`, and (since `s_j < q`) both
tuples keep their first `j` entries `≤ q`.  ★ `InitLt_of_head_gt` is the pure-tuple
statement this feeds into: two such tuples compare lexicographically at their initial
segments (`Init(v) ≺ Init(u)`), which is the engine of the paper's Prop-3.2
termination argument (type-3 outputs strictly increase `Init`, bounded by `q{k}`).

Supporting facts (this module): `initListAux_append_le` (the ≤-q prefix commutes with
appending a `≤ q` front), `valueList_getElem` / `valueList_take_le` (front entries of
the value list are `≤ q` tuple entries), `take_succ_get` (the `take (i+1)` split), and
`valueList_take_eq_of_pad0_eq` (pad0-front agreement ⇒ equal `take`-fronts).
-/

namespace ZagierHoffmanPositiveChar
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- initListAux commutes with appending a ≤-q front. -/
lemma initListAux_append_le (q : ℕ) : ∀ (front rest : List ℕ),
    (∀ v ∈ front, v ≤ q) → initListAux q (front ++ rest) = front ++ initListAux q rest := by
  intro front
  induction front with
  | nil =>
      intro rest h; simp
  | cons a t ih =>
      intro rest hall
      have ha : a ≤ q := hall a (by simp)
      have htall : ∀ v ∈ t, v ≤ q := by
        intro v hv; exact hall v (by simp [hv])
      calc
        initListAux q ((a :: t) ++ rest) = initListAux q (a :: (t ++ rest)) := by rfl
        _ = a :: initListAux q (t ++ rest) := initListAux_cons_le q a (t ++ rest) ha
        _ = a :: (t ++ initListAux q rest) := by rw [ih rest htall]
        _ = (a :: t) ++ initListAux q rest := by rfl

/-- The value of a tuple at position `x` is the `x`-th entry of its value list. -/
lemma valueList_getElem {r : ℕ} (s : Fin r → ℕ+) (x : ℕ) (hx : x < r) :
    (valueList s)[x]'(by simp [valueList_length, hx]) = (s ⟨x, hx⟩ : ℕ) := by
  unfold valueList
  rw [List.getElem_ofFn]

/-- An entry of the front (first `j`) part of `valueList s` is a ≤-q entry of `s`,
given all pad0-entries below `j` are ≤ q. -/
lemma valueList_take_le {r : ℕ} (q : ℕ) (s : Fin r → ℕ+) (j : ℕ)
    (h : ∀ x : ℕ, x < j → pad0 s x ≤ q) :
    ∀ v ∈ (valueList s).take j, v ≤ q := by
  intro v hv
  rcases List.getElem_of_mem hv with ⟨i, hi, hvi⟩
  have hij : i < j := by
    have hlen := List.length_take (i := j) (l := valueList s)
    have : i < min j (valueList s).length := by simpa [hlen] using hi
    omega
  have hir : i < r := by
    have hmem : i < (valueList s).length := by
      have hle : ((valueList s).take j).length ≤ (valueList s).length := by
        rw [List.length_take]
        simp
      omega
    simpa [valueList_length] using hmem
  have hval : (valueList s)[i]'(by simpa [valueList_length] using hir) = v := by
    have hvt := List.getElem_take (xs := valueList s) (j := j) (i := i) (h := hi)
    rwa [← hvt]
  rw [← hval]
  have hvg := valueList_getElem s i hir
  rw [hvg]
  have hpad : pad0 s i = (s ⟨i, hir⟩ : ℕ) := by rw [pad0_of_lt s hir]
  rw [← hpad]
  exact h i hij

/-- `take (i+1) l` splits at position `i`. -/
lemma take_succ_get {α : Type} (l : List α) (i : ℕ) (hi : i < l.length) :
    l.take (i + 1) = l.take i ++ [l[i]'(hi)] := by
  rw [List.take_add_one]
  have hopt : l[i]? = some (l[i]'(hi)) := List.getElem?_eq_getElem hi
  simp [hopt]

/-- Front values equal: two tuples agreeing below `j−1` (pad0) have equal
`take (j−1)` value-lists (given `j−1` within both depths). -/
lemma valueList_take_eq_of_pad0_eq {r m : ℕ} (u : Fin r → ℕ+) (v : Fin m → ℕ+)
    (j : ℕ) (hj1 : 1 ≤ j) (hjr : j ≤ r) (hjm : j ≤ m)
    (heq : ∀ x : ℕ, x < j - 1 → pad0 u x = pad0 v x) :
    (valueList v).take (j - 1) = (valueList u).take (j - 1) := by
  apply List.ext_getElem
  · simp [List.length_take, valueList_length]
    omega
  · intro i hi1 hi2
    have hij : i < j - 1 := by
      have hh := List.length_take (i := j - 1) (l := valueList v)
      have : i < min (j - 1) (valueList v).length := by simpa [hh] using hi1
      omega
    have hivm : i < m := by
      have hh := List.length_take (i := j - 1) (l := valueList v)
      have : i < min (j - 1) (valueList v).length := by simpa [hh] using hi1
      have hm : m ≤ (valueList v).length := by simp [valueList_length]
      omega
    have hivr : i < r := by
      have hh := List.length_take (i := j - 1) (l := valueList u)
      have : i < min (j - 1) (valueList u).length := by simpa [hh] using hi2
      have hr : r ≤ (valueList u).length := by simp [valueList_length]
      omega
    have h1 := List.getElem_take (xs := valueList v) (j := j - 1) (i := i) (h := hi1)
    have h2 := List.getElem_take (xs := valueList u) (j := j - 1) (i := i) (h := hi2)
    have hgv := valueList_getElem v i hivm
    have hgu := valueList_getElem u i hivr
    calc
      ((valueList v).take (j - 1))[i]'(hi1) = (valueList v)[i]'(by simpa [valueList_length] using hivm) := by
        simp [h1]
      _ = (v ⟨i, hivm⟩ : ℕ) := hgv
      _ = pad0 v i := by
        rw [pad0_of_lt v hivm]
      _ = pad0 u i := (heq i hij).symm
      _ = (u ⟨i, hivr⟩ : ℕ) := by
        rw [pad0_of_lt u hivr]
      _ = (valueList u)[i]'(by simpa [valueList_length] using hivr) := hgu.symm
      _ = ((valueList u).take (j - 1))[i]'(hi2) := by
        simp [h2]

/-- ★ The type-3 Init engine: if `u` agrees with `v` before position `j−1`, has a
bigger entry at `j−1`, and both have their first `j` entries `≤ q` (so both initial
tuples reach position `j−1`), then `Init(v)` is lexicographically smaller than
`Init(u)`.  (Application: `v = s`, `u` a type-3 output of the (2.14) chain.) -/
lemma InitLt_of_head_gt (q : ℕ) {r m : ℕ} (u : Fin r → ℕ+) (v : Fin m → ℕ+)
    (j : ℕ) (hj1 : 1 ≤ j) (hjr : j ≤ r) (hjm : j ≤ m)
    (huq : ∀ x : ℕ, x < j → pad0 u x ≤ q)
    (hvq : ∀ x : ℕ, x < j → pad0 v x ≤ q)
    (heq : ∀ x : ℕ, x < j - 1 → pad0 u x = pad0 v x)
    (hgt : pad0 v (j - 1) < pad0 u (j - 1)) :
    InitLt q v u := by
  classical
  let lv := valueList v
  let lu := valueList u
  have hj1m : j - 1 < m := by omega
  have hj1r : j - 1 < r := by omega
  have hheadlt : (valueList v)[j - 1]'(by
        simp [valueList_length, hj1m]) <
      (valueList u)[j - 1]'(by simp [valueList_length, hj1r]) := by
    have h1 : pad0 v (j - 1) = (v ⟨j - 1, hj1m⟩ : ℕ) := pad0_of_lt v hj1m
    have h2 : pad0 u (j - 1) = (u ⟨j - 1, hj1r⟩ : ℕ) := pad0_of_lt u hj1r
    have hgv := valueList_getElem v (j - 1) hj1m
    have hgu := valueList_getElem u (j - 1) hj1r
    calc
      (valueList v)[j - 1]'(by simp [valueList_length, hj1m]) = (v ⟨j - 1, hj1m⟩ : ℕ) := hgv
      _ = pad0 v (j - 1) := by rw [h1]
      _ < pad0 u (j - 1) := hgt
      _ = (u ⟨j - 1, hj1r⟩ : ℕ) := by rw [h2]
      _ = (valueList u)[j - 1]'(by simp [valueList_length, hj1r]) := hgu.symm
  have hfront : (valueList v).take (j - 1) = (valueList u).take (j - 1) :=
    valueList_take_eq_of_pad0_eq u v j hj1 hjr hjm heq
  have hvle : ∀ w ∈ (valueList v).take j, w ≤ q := valueList_take_le q v j hvq
  have hule : ∀ w ∈ (valueList u).take j, w ≤ q := valueList_take_le q u j huq
  have htakesplit_v : (valueList v).take j = (valueList v).take (j - 1) ++
      [(valueList v)[j - 1]'(by simp [valueList_length, hj1m])] := by
    have hjj : j = (j - 1) + 1 := by omega
    calc
      (valueList v).take j = (valueList v).take ((j - 1) + 1) := by
            exact congrArg (fun n : ℕ => List.take n (valueList v)) hjj
      _ = (valueList v).take (j - 1) ++ [(valueList v)[j - 1]'(by simp [valueList_length, hj1m])] := by
            exact take_succ_get (valueList v) (j - 1) (by simp [valueList_length, hj1m])
  have htakesplit_u : (valueList u).take j = (valueList u).take (j - 1) ++
      [(valueList u)[j - 1]'(by simp [valueList_length, hj1r])] := by
    have hjj : j = (j - 1) + 1 := by omega
    calc
      (valueList u).take j = (valueList u).take ((j - 1) + 1) := by
            exact congrArg (fun n : ℕ => List.take n (valueList u)) hjj
      _ = (valueList u).take (j - 1) ++ [(valueList u)[j - 1]'(by simp [valueList_length, hj1r])] := by
            exact take_succ_get (valueList u) (j - 1) (by simp [valueList_length, hj1r])
  have hdec_v : initListAux q (valueList v) =
      (valueList v).take (j - 1) ++
        ((valueList v)[j - 1]'(by simp [valueList_length, hj1m]) ::
          initListAux q ((valueList v).drop j)) := by
    have hsplit : valueList v = (valueList v).take j ++ (valueList v).drop j :=
      (List.take_append_drop j (valueList v)).symm
    calc
      initListAux q (valueList v)
          = initListAux q ((valueList v).take j ++ (valueList v).drop j) := by
            exact congrArg (fun l : List ℕ => initListAux q l) hsplit
      _ = (valueList v).take j ++ initListAux q ((valueList v).drop j) := by
            exact initListAux_append_le q ((valueList v).take j) ((valueList v).drop j) hvle
      _ = ((valueList v).take (j - 1) ++
              [(valueList v)[j - 1]'(by simp [valueList_length, hj1m])]) ++
            initListAux q ((valueList v).drop j) := by
            exact congrArg (fun l : List ℕ => l ++ initListAux q ((valueList v).drop j)) htakesplit_v
      _ = (valueList v).take (j - 1) ++
              ((valueList v)[j - 1]'(by simp [valueList_length, hj1m]) ::
                initListAux q ((valueList v).drop j)) := by
            rw [List.append_assoc]
            rfl
  have hdec_u : initListAux q (valueList u) =
      (valueList u).take (j - 1) ++
        ((valueList u)[j - 1]'(by simp [valueList_length, hj1r]) ::
          initListAux q ((valueList u).drop j)) := by
    have hsplit : valueList u = (valueList u).take j ++ (valueList u).drop j :=
      (List.take_append_drop j (valueList u)).symm
    calc
      initListAux q (valueList u)
          = initListAux q ((valueList u).take j ++ (valueList u).drop j) := by
            exact congrArg (fun l : List ℕ => initListAux q l) hsplit
      _ = (valueList u).take j ++ initListAux q ((valueList u).drop j) := by
            exact initListAux_append_le q ((valueList u).take j) ((valueList u).drop j) hule
      _ = ((valueList u).take (j - 1) ++
              [(valueList u)[j - 1]'(by simp [valueList_length, hj1r])]) ++
            initListAux q ((valueList u).drop j) := by
            exact congrArg (fun l : List ℕ => l ++ initListAux q ((valueList u).drop j)) htakesplit_u
      _ = (valueList u).take (j - 1) ++
              ((valueList u)[j - 1]'(by simp [valueList_length, hj1r]) ::
                initListAux q ((valueList u).drop j)) := by
            rw [List.append_assoc]
            rfl
  change List.Lex (fun a b : ℕ => a < b)
    (initListAux q (valueList v)) (initListAux q (valueList u))
  rw [hdec_v, hdec_u, ← hfront]
  exact List.Lex.append_left (fun a b : ℕ => a < b) (List.Lex.rel hheadlt)
    ((valueList v).take (j - 1))

end ZagierHoffmanPositiveChar
