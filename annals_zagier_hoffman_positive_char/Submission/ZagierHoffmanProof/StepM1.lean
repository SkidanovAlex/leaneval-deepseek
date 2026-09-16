import Submission.ZagierHoffmanProof.StepC

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step M1: the §3 combinatorial notions — Init, lex, k-admissibility

The paper's Def 2.11 / Def 3.1 (§3 of the workspace = ND21's §2.3/3.1), 0-indexed:
  • `initList q s` (the initial tuple `Init(𝔰)`) — the longest prefix of the entries
    of `𝔰` all `≤ q`, as a `List ℕ` of values (`initListAux` implements it by plain
    list recursion, with `initRestAux` the complementary tail so
    `initListAux ++ initRestAux = the list`).
  • `InitLt`/`InitLe q s t` — the lexicographic order on initial tuples
    (`List.Lex (·<·)`, shorter-prefix-is-smaller).
  • `kAdmissible q s k` — (1) the zero-padded entries `s_1..s_k` are `≤ q`, and
    (2) `𝔰` is not of the form `(s₁..s_r)` with `r ≤ k`, all-but-last `≤ q`, last `= q`.
The paper's Prop-3.2 (H_k) algorithm and its termination argument (type-3 outputs
strictly increase `Init`, bounded by `q{k}`) run on these; the type-bound modules
(StepL31+) will consume `InitLt`/`kAdmissible`, and the theorem-A tail needs
`wAdmissible_weight_conds` (weight-`w` + `w`-admissible ⇒ the workspace `𝒯_w`
membership conditions: entries `≤ q`, last `< q`).
-/

namespace ZagierHoffmanPositiveChar
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## The ≤-q prefix of a list of values -/

/-- The longest prefix of a value-list whose entries are all ≤ `q`, as a list. -/
noncomputable def initListAux (q : ℕ) : List ℕ → List ℕ
  | [] => []
  | a :: t => if a ≤ q then a :: initListAux q t else []

/-- The tail left over after the ≤-q prefix (starts at the first entry > q). -/
noncomputable def initRestAux (q : ℕ) : List ℕ → List ℕ
  | [] => []
  | a :: t => if a ≤ q then initRestAux q t else a :: t

lemma initListAux_nil (q : ℕ) : initListAux q [] = [] := by rfl
lemma initRestAux_nil (q : ℕ) : initRestAux q [] = [] := by rfl

lemma initListAux_cons_le (q a : ℕ) (t : List ℕ) (ha : a ≤ q) :
    initListAux q (a :: t) = a :: initListAux q t := by
  simp [initListAux, ha]

lemma initRestAux_cons_le (q a : ℕ) (t : List ℕ) (ha : a ≤ q) :
    initRestAux q (a :: t) = initRestAux q t := by
  simp [initRestAux, ha]

lemma initListAux_cons_gt (q a : ℕ) (t : List ℕ) (ha : q < a) :
    initListAux q (a :: t) = [] := by
  simp [initListAux, ha]

lemma initRestAux_cons_gt (q a : ℕ) (t : List ℕ) (ha : q < a) :
    initRestAux q (a :: t) = a :: t := by
  simp [initRestAux, ha]

/-- Length of the ≤-q prefix is at most the length of the input. -/
lemma initListAux_length_le (q : ℕ) : ∀ (l : List ℕ),
    (initListAux q l).length ≤ l.length := by
  intro l
  induction l with
  | nil => simp [initListAux]
  | cons a t ih =>
      by_cases ha : a ≤ q
      · rw [initListAux_cons_le q a t ha]
        simp [Nat.succ_le_succ ih]
      · have hgt : q < a := lt_of_not_ge ha
        rw [initListAux_cons_gt q a t hgt]
        simp

/-- Every entry of the ≤-q prefix is ≤ q. -/
lemma initListAux_mem_le {q : ℕ} : ∀ (l : List ℕ),
    ∀ v ∈ initListAux q l, v ≤ q := by
  intro l
  induction l with
  | nil => intro v hv; simp [initListAux] at hv
  | cons a t ih =>
      intro v hv
      by_cases ha : a ≤ q
      · rw [initListAux_cons_le q a t ha] at hv
        simp at hv
        rcases hv with rfl | hv
        · exact ha
        · exact ih v hv
      · have hgt : q < a := lt_of_not_ge ha
        rw [initListAux_cons_gt q a t hgt] at hv
        simp at hv

/-- If every entry is ≤ q, the prefix is the whole list. -/
lemma initListAux_eq_self {q : ℕ} : ∀ (l : List ℕ),
    (∀ v ∈ l, v ≤ q) → initListAux q l = l := by
  intro l
  induction l with
  | nil => simp [initListAux]
  | cons a t ih =>
      intro hall
      have ha : a ≤ q := hall a (by simp)
      have htall : ∀ v ∈ t, v ≤ q := by
        intro v hv
        exact hall v (by simp [hv])
      rw [initListAux_cons_le q a t ha, ih htall]

/-- The ≤-q prefix stops at (or before) the first entry exceeding `q`: if the entry
at position `p` exceeds `q`, the prefix has length ≤ `p`. -/
lemma initListAux_length_le_of_gt {q : ℕ} : ∀ (l : List ℕ) (p : ℕ)
    (hp : p < l.length) (hgt : q < l[p]),
    (initListAux q l).length ≤ p := by
  intro l
  induction l with
  | nil =>
      intro p hp
      simp at hp
  | cons a t ih =>
      intro p hp hgt
      by_cases ha : a ≤ q
      · rw [initListAux_cons_le q a t ha]
        cases p with
        | zero =>
            simp at hgt
            omega
        | succ p =>
            have hlt : p < t.length := by
              simpa using (Nat.succ_lt_succ_iff.mp hp)
            have hgt' : q < t[p] := by
              simpa using hgt
            have hle := ih p hlt hgt'
            exact Nat.succ_le_succ hle
      · have hgt' : q < a := lt_of_not_ge ha
        rw [initListAux_cons_gt q a t hgt']
        simp

/-- The ≤-q prefix plus its complement is the whole list. -/
lemma init_append_rest {q : ℕ} : ∀ (l : List ℕ),
    initListAux q l ++ initRestAux q l = l := by
  intro l
  induction l with
  | nil => simp [initListAux, initRestAux]
  | cons a t ih =>
      by_cases ha : a ≤ q
      · rw [initListAux_cons_le q a t ha, initRestAux_cons_le q a t ha]
        simp [ih]
      · have hgt : q < a := lt_of_not_ge ha
        rw [initListAux_cons_gt q a t hgt, initRestAux_cons_gt q a t hgt]
        simp

/-! ## Init of a tuple and the lex order on initial tuples -/

/-- The values of a tuple, as a list. -/
noncomputable def valueList {r : ℕ} (s : Fin r → ℕ+) : List ℕ :=
  List.ofFn (fun i : Fin r => (s i : ℕ))

lemma valueList_length {r : ℕ} (s : Fin r → ℕ+) : (valueList s).length = r := by
  simp [valueList]

/-- The initial tuple `Init(𝔰)`: the longest prefix of entries all ≤ q. -/
noncomputable def initList (q : ℕ) {r : ℕ} (s : Fin r → ℕ+) : List ℕ :=
  initListAux q (valueList s)

/-- The length of the initial tuple. -/
noncomputable def initLen (q : ℕ) {r : ℕ} (s : Fin r → ℕ+) : ℕ :=
  (initList q s).length

/-- The depth of the initial tuple is at most the depth of `s`. -/
lemma initLen_le {r : ℕ} (q : ℕ) (s : Fin r → ℕ+) : initLen q s ≤ r := by
  have hl := initListAux_length_le q (valueList s)
  simpa [initLen, initList, valueList_length] using hl

/-- Every entry of the initial tuple is ≤ q. -/
lemma initList_mem_le {r : ℕ} (q : ℕ) (s : Fin r → ℕ+) :
    ∀ v ∈ initList q s, v ≤ q := by
  intro v hv
  exact initListAux_mem_le (valueList s) v hv

/-- If every entry of `s` is ≤ q, the initial tuple is all of `s`. -/
lemma initList_eq_valueList {r : ℕ} (q : ℕ) (s : Fin r → ℕ+)
    (hall : ∀ x : ℕ, (hx : x < r) → (s ⟨x, hx⟩ : ℕ) ≤ q) :
    initList q s = valueList s := by
  unfold initList
  apply initListAux_eq_self
  intro v hv
  rcases List.mem_ofFn.mp hv with ⟨i, rfl⟩
  exact hall (i : ℕ) i.isLt

/-- If the entry at position `p` exceeds `q`, the initial tuple has length ≤ `p`. -/
lemma initLen_le_of_gt {r : ℕ} (q : ℕ) (s : Fin r → ℕ+) (p : ℕ)
    (hp : p < r) (hgt : q < (s ⟨p, hp⟩ : ℕ)) : initLen q s ≤ p := by
  unfold initLen initList
  have hg0 : q < (valueList s)[p]'(by simpa [valueList_length] using hp) := by
    unfold valueList
    rw [List.getElem_ofFn]
    exact hgt
  have hl := initListAux_length_le_of_gt (valueList s) p (by
    simpa [valueList_length] using hp) hg0
  simpa [valueList_length] using hl

/-- The lexicographic order on initial tuples (shorter prefix is smaller). -/
def InitLt (q : ℕ) {r m : ℕ} (s : Fin r → ℕ+) (t : Fin m → ℕ+) : Prop :=
  List.Lex (fun a b : ℕ => a < b) (initList q s) (initList q t)

/-- The non-strict lex order on initial tuples. -/
def InitLe (q : ℕ) {r m : ℕ} (s : Fin r → ℕ+) (t : Fin m → ℕ+) : Prop :=
  InitLt q s t ∨ initList q s = initList q t

/-! ## k-admissibility (paper Def 3.1) -/

/-- `s` is `k`-admissible (paper Def 3.1): the zero-padded entries `s_1..s_k` are
`≤ q`, and `s` is not of the form `(s₁..s_r)` with `r ≤ k`, all-but-last `≤ q`,
last `= q`. -/
def kAdmissible (q : ℕ) {r : ℕ} (s : Fin r → ℕ+) (k : ℕ) : Prop :=
  (∀ x : ℕ, x < k → pad0 s x ≤ q) ∧
  ¬ (∃ hr1 : 1 ≤ r,
       r ≤ k ∧ (∀ x : ℕ, x < r - 1 → pad0 s x ≤ q) ∧
       (s ⟨r - 1, by omega⟩ : ℕ) = q)

/-- Condition (1): the zero-padded entries up to `k` are ≤ q. -/
lemma kAdmissible.pad0_le {r : ℕ} {q : ℕ} {s : Fin r → ℕ+} {k : ℕ}
    (hadm : kAdmissible q s k) (x : ℕ) (hx : x < k) : pad0 s x ≤ q :=
  hadm.1 x hx

/-- The weight of a tuple is at least its depth (entries are positive). -/
lemma weight_ge_depth (r : ℕ) (s : Fin r → ℕ+) : r ≤ weight r s := by
  change r ≤ (∑ i : Fin r, (s i : ℕ))
  have h1 : (∑ i : Fin r, (1 : ℕ)) ≤ (∑ i : Fin r, (s i : ℕ)) := by
    apply Finset.sum_le_sum
    intro i hi
    have hpos : 0 < (s i : ℕ) := (s i).pos
    omega
  have h2 : (∑ i : Fin r, (1 : ℕ)) = r := by simp
  omega

/-- ★ Weight-`w` + `w`-admissible ⇒ the workspace `𝒯_w` membership conditions:
all entries except the last are ≤ q and the last is < q. -/
lemma wAdmissible_weight_conds (q : ℕ) {r w : ℕ} (s : Fin r → ℕ+)
    (hr : 0 < r) (hw : weight r s = w) (hadm : kAdmissible q s w) :
    (∀ i : Fin r, (i : ℕ) < r - 1 → (s i : ℕ) ≤ q) ∧
      (s ⟨r - 1, by omega⟩ : ℕ) < q := by
  constructor
  · intro i hi
    have hrw : r ≤ w := by
      have hge := weight_ge_depth r s
      omega
    have hiw : (i : ℕ) < w := by
      have : (i : ℕ) < r := i.isLt
      omega
    have h := hadm.1 (i : ℕ) hiw
    rwa [pad0_of_lt s i.isLt] at h
  · by_contra hlt
    have hrw : r ≤ w := by
      have hge := weight_ge_depth r s
      omega
    have hge : q ≤ (s ⟨r - 1, by omega⟩ : ℕ) := le_of_not_gt hlt
    have hle : (s ⟨r - 1, by omega⟩ : ℕ) ≤ q := by
      have hxw : r - 1 < w := by omega
      have h := hadm.1 (r - 1) hxw
      have hxr : r - 1 < r := by omega
      rwa [pad0_of_lt s hxr] at h
    have heq : (s ⟨r - 1, by omega⟩ : ℕ) = q := le_antisymm hle hge
    apply hadm.2
    refine ⟨hr, ?_, ?_, heq⟩
    · exact hrw
    · intro x hx
      have hxw : x < w := by
        have : x < r := by omega
        omega
      have h := hadm.1 x hxw
      exact h

end ZagierHoffmanPositiveChar
