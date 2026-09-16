import Submission.ZagierHoffmanProof.StepM2
import Submission.ZagierHoffmanProof.StepM3

set_option autoImplicit false
set_option maxHeartbeats 4000000
open Polynomial RatFunc
open scoped BigOperators
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-!
# Step L168: `domLevel` — the tuple's OWN level, and the admissibility trichotomy

Paper §3 (ND21 Prop 3.2): for a tuple `s` of depth `r` that is NOT admissible at
every level, there is a unique level `k*` with
  `(k*−1)`-admissible ∧ ¬`k*`-admissible,  and  `k`-admissible ⟺ `k < k*`,
namely `k* = initLen+1` when the initial tuple does not exhaust `s` (the `> q`
entry case) and `k* = r = depth` when all entries are `≤ q` and the last is `= q`.
This is the level at which the paper's decomposition (Props 2.12/2.13) is applied.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar

/-! ## Admissibility is monotone (decreasing) in the level -/

lemma kAdmissible_mono_le {q : ℕ} {r : ℕ} (s : Fin r → ℕ+) {j k : ℕ} (hjk : j ≤ k)
    (h : kAdmissible q s k) : kAdmissible q s j := by
  refine ⟨fun x hx => h.1 x (lt_of_lt_of_le hx hjk), ?_⟩
  rintro ⟨hr1, hrk, hall, hlast⟩
  exact h.2 ⟨hr1, le_trans hrk hjk, hall, hlast⟩

/-- `s` is admissible at every level. -/
def AdmEverywhere (q : ℕ) {r : ℕ} (s : Fin r → ℕ+) : Prop := ∀ k, kAdmissible q s k

/-! ## The first `> q` entry -/

/-- The leftover tail after the `≤ q` prefix is either empty or starts with a
`> q` entry. -/
lemma initRestAux_eq_nil_or_head_gt (q : ℕ) : ∀ l : List ℕ,
    initRestAux q l = [] ∨ ∃ a t, initRestAux q l = a :: t ∧ q < a := by
  intro l
  induction l with
  | nil => exact Or.inl rfl
  | cons a t ih =>
      by_cases ha : a ≤ q
      · rw [initRestAux_cons_le q a t ha]; exact ih
      · have hlt : q < a := lt_of_not_ge ha
        exact Or.inr ⟨a, t, initRestAux_cons_gt q a t hlt, hlt⟩

/-- The leftover tail is the drop of the value list at the initial length. -/
lemma initRestAux_valueList (q : ℕ) {r : ℕ} (s : Fin r → ℕ+) :
    initRestAux q (valueList s) = (valueList s).drop (initLen q s) := by
  have happ := init_append_rest (q := q) (valueList s)
  have h2 : ((initListAux q (valueList s)) ++ initRestAux q (valueList s)).drop
      (initLen q s) = initRestAux q (valueList s) := by
    have := List.drop_left (l₁ := initListAux q (valueList s))
      (l₂ := initRestAux q (valueList s))
    simpa [initLen, initList] using this
  rw [happ] at h2
  exact h2.symm

/-- ★ The entry at position `initLen` (when it exists) exceeds `q`: the initial tuple
is exactly the maximal `≤ q` prefix. -/
lemma initLen_entry_gt (q : ℕ) {r : ℕ} (s : Fin r → ℕ+) (h : initLen q s < r) :
    q < (s ⟨initLen q s, h⟩ : ℕ) := by
  have hrest := initRestAux_valueList q s
  have hne : initRestAux q (valueList s) ≠ [] := by
    intro hnil
    have hlen : (initRestAux q (valueList s)).length = 0 := by simp [hnil]
    rw [hrest, List.length_drop, valueList_length] at hlen
    omega
  rcases initRestAux_eq_nil_or_head_gt q (valueList s) with hnil | ⟨a, t, heq, hgt⟩
  · exact absurd hnil hne
  · have hdrop2 : (valueList s).drop (initLen q s) = a :: t := by rw [← hrest, heq]
    have had : (valueList s)[initLen q s]'(by simp [valueList_length, h]) = a := by
      have hh := List.head_drop (l := valueList s) (i := initLen q s)
        (by rw [hdrop2]; simp)
      simp only [hdrop2, List.head_cons] at hh
      exact hh.symm
    have hvg := valueList_getElem s (initLen q s) h
    rw [hvg] at had
    rw [had]
    exact hgt

/-! ## The condition (1) characterization and the trichotomy -/

/-- Condition (1) of Definition 3.1 holds exactly up to the maximal `≤ q` prefix. -/
lemma cond1_iff (q : ℕ) {r : ℕ} (s : Fin r → ℕ+) (k : ℕ) :
    (∀ x : ℕ, x < k → pad0 s x ≤ q) ↔ min k r ≤ initLen q s := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    have hlt : initLen q s < r := by omega
    have hltk : initLen q s < k := by omega
    have hgt := initLen_entry_gt q s hlt
    have := h (initLen q s) hltk
    rw [pad0_of_lt s hlt] at this
    omega
  · intro h x hx
    by_cases hxr : x < r
    · have hxmin : x < min k r := by omega
      have hxinit : x < initLen q s := by omega
      rw [pad0_of_lt s hxr]
      by_contra hcon
      push Not at hcon
      have := initLen_le_of_gt q s x hxr hcon
      omega
    · have hge : r ≤ x := le_of_not_gt hxr
      rw [pad0_of_ge s hge]
      exact Nat.zero_le q

/-- Condition (2) of Definition 3.1, in terms of `initLen`. -/
lemma cond2_iff (q : ℕ) {r : ℕ} (s : Fin r → ℕ+) (k : ℕ) :
    (∃ hr1 : 1 ≤ r, r ≤ k ∧ (∀ x : ℕ, x < r - 1 → pad0 s x ≤ q) ∧
        (s ⟨r - 1, by omega⟩ : ℕ) = q)
      ↔ 1 ≤ r ∧ r ≤ k ∧ r - 1 ≤ initLen q s ∧ pad0 s (r - 1) = q := by
  constructor
  · rintro ⟨hr1, hrk, hall, hlast⟩
    refine ⟨hr1, hrk, ?_, ?_⟩
    · have h1 : min (r - 1) r ≤ initLen q s := (cond1_iff q s (r - 1)).mp hall
      omega
    · rw [pad0_of_lt s (by omega : r - 1 < r)]
      exact hlast
  · rintro ⟨hr1, hrk, hle, hpad⟩
    refine ⟨hr1, hrk, ?_, ?_⟩
    · have h1 : min (r - 1) r ≤ initLen q s := by omega
      exact (cond1_iff q s (r - 1)).mpr h1
    · rw [pad0_of_lt s (by omega : r - 1 < r)] at hpad
      exact hpad

/-- ★ The `k`-admissibility trichotomy (`q ≥ 1` only via `Nat`): `s` is `k`-admissible
iff `k` is below the first bad level. -/
theorem kAdmissible_iff (q : ℕ) {r : ℕ} (s : Fin r → ℕ+) (k : ℕ) :
    kAdmissible q s k ↔ min k r ≤ initLen q s ∧
      ¬ (1 ≤ r ∧ r ≤ k ∧ r - 1 ≤ initLen q s ∧ pad0 s (r - 1) = q) := by
  unfold kAdmissible
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(cond1_iff q s k).mp h1, ?_⟩
    rintro ⟨hr1, hrk, hle, hpad⟩
    exact h2 ((cond2_iff q s k).mpr ⟨hr1, hrk, hle, hpad⟩)
  · rintro ⟨h1, h2⟩
    refine ⟨(cond1_iff q s k).mpr h1, ?_⟩
    rintro hc2
    obtain ⟨hr1, hrk, hle, hpad⟩ := (cond2_iff q s k).mp hc2
    exact h2 ⟨hr1, hrk, hle, hpad⟩


/-- The tuple's OWN level. -/
noncomputable def domLevel (q : ℕ) {r : ℕ} (s : Fin r → ℕ+) : ℕ :=
  if initLen q s < r then initLen q s + 1 else r

lemma domLevel_eq_succ (q : ℕ) {r : ℕ} (s : Fin r → ℕ+) (h : initLen q s < r) :
    domLevel q s = initLen q s + 1 := by
  rw [domLevel, if_pos h]

lemma domLevel_eq_depth (q : ℕ) {r : ℕ} (s : Fin r → ℕ+) (h : r ≤ initLen q s) :
    domLevel q s = r := by
  rw [domLevel, if_neg (by omega)]

/-- ★★ THE ADMISSIBILITY TRICHOTOMY: for a tuple that is not admissible at every
level, `k`-admissibility is exactly `k < domLevel`. -/
theorem kAdmissible_iff_lt_domLevel (q : ℕ) {r : ℕ} (s : Fin r → ℕ+)
    (hnot : ¬ AdmEverywhere q s) (k : ℕ) :
    kAdmissible q s k ↔ k < domLevel q s := by
  classical
  by_cases hlt : initLen q s < r
  · -- CASE 1: the initial tuple does not exhaust `s`
    rw [domLevel_eq_succ q s hlt]
    rw [kAdmissible_iff]
    constructor
    · rintro ⟨h1, -⟩
      have hmin : min k r = k := by omega
      omega
    · intro hk
      refine ⟨?_, ?_⟩
      · have hmin : min k r = k := by omega
        omega
      · rintro ⟨hr1, hrk, hle, hpad⟩
        have hinit : initLen q s = r - 1 := by omega
        have hgt := initLen_entry_gt q s hlt
        have hpadr : pad0 s (r - 1) = (s ⟨r - 1, by omega⟩ : ℕ) := pad0_of_lt s (by omega)
        have hidx : (⟨r - 1, by omega⟩ : Fin r) = ⟨initLen q s, hlt⟩ := by
          apply Fin.ext
          simp only [Fin.val_mk]
          omega
        rw [hpadr, hidx] at hpad
        omega
  · -- CASE 2: all entries are `≤ q`
    have hge : r ≤ initLen q s := by omega
    rw [domLevel_eq_depth q s hge]
    -- `hnot` forces the last entry to be `q`
    have hlast : pad0 s (r - 1) = q := by
      by_contra hne
      apply hnot
      intro m
      rw [kAdmissible_iff]
      refine ⟨by omega, ?_⟩
      rintro ⟨hr1, -, -, hpad⟩
      exact hne hpad
    have hr1 : 1 ≤ r := by
      by_contra hcon
      have hr0 : r = 0 := by omega
      subst hr0
      exact hnot (fun m => ⟨fun x hx => by simp [pad0_of_ge s (Nat.zero_le x)],
        by rintro ⟨h1, -⟩; omega⟩)
    rw [kAdmissible_iff]
    constructor
    · rintro ⟨-, h2⟩
      by_contra hcon
      push Not at hcon
      exact h2 ⟨hr1, hcon, by omega, hlast⟩
    · intro hk
      refine ⟨by omega, ?_⟩
      rintro ⟨-, hrk, -, hpad⟩
      have hpad' : pad0 s (r - 1) = q := hpad
      rw [hlast] at hpad'
      omega

/-- `domLevel` is positive for a tuple that is not admissible everywhere. -/
lemma domLevel_pos (q : ℕ) {r : ℕ} (s : Fin r → ℕ+) (hnot : ¬ AdmEverywhere q s) :
    1 ≤ domLevel q s := by
  classical
  by_cases hlt : initLen q s < r
  · rw [domLevel_eq_succ q s hlt]; omega
  · rw [domLevel_eq_depth q s (by omega)]
    by_contra hcon
    have hr0 : r = 0 := by omega
    subst hr0
    refine hnot (fun m => ?_)
    refine ⟨?_, ?_⟩
    · intro x hx
      simp [pad0_of_ge s (Nat.zero_le x)]
    · rintro ⟨hr1, -⟩
      omega

/-- The tuple is `(domLevel−1)`-admissible. -/
lemma kAdmissible_domLevel_pred (q : ℕ) {r : ℕ} (s : Fin r → ℕ+)
    (hnot : ¬ AdmEverywhere q s) : kAdmissible q s (domLevel q s - 1) :=
  (kAdmissible_iff_lt_domLevel q s hnot _).mpr (by have := domLevel_pos q s hnot; omega)

/-- The tuple is NOT `domLevel`-admissible. -/
lemma not_kAdmissible_domLevel (q : ℕ) {r : ℕ} (s : Fin r → ℕ+)
    (hnot : ¬ AdmEverywhere q s) : ¬ kAdmissible q s (domLevel q s) :=
  fun h => by
    have := (kAdmissible_iff_lt_domLevel q s hnot _).mp h
    omega

/-- A tuple that is not `k`-admissible has `domLevel ≤ k`. -/
lemma domLevel_le_of_not_adm (q : ℕ) {r : ℕ} (s : Fin r → ℕ+) {k : ℕ}
    (hnot : ¬ kAdmissible q s k) : domLevel q s ≤ k := by
  by_contra hcon
  push Not at hcon
  exact hnot ((kAdmissible_iff_lt_domLevel q s
    (fun hall => hnot (hall k)) k).mpr hcon)

/-- In CASE 1 (a bad entry), `domLevel ≤ depth` and the `domLevel`-th entry exceeds `q`. -/
lemma domLevel_le_depth (q : ℕ) {r : ℕ} (s : Fin r → ℕ+) (h : initLen q s < r) :
    domLevel q s ≤ r := by
  rw [domLevel_eq_succ q s h]; omega

lemma domLevel_entry_gt (q : ℕ) {r : ℕ} (s : Fin r → ℕ+) (h : initLen q s < r) :
    q < pad0 s (domLevel q s - 1) := by
  rw [domLevel_eq_succ q s h]
  have h' : initLen q s + 1 - 1 = initLen q s := by omega
  rw [h']
  rw [pad0_of_lt s h]
  exact initLen_entry_gt q s h

/-- In CASE 2 (all entries `≤ q`), `domLevel = depth` and the last entry is `q`. -/
lemma domLevel_eq_depth_of_le (q : ℕ) {r : ℕ} (s : Fin r → ℕ+) (h : r ≤ initLen q s) :
    domLevel q s = r := domLevel_eq_depth q s h

lemma domLevel_last_eq (q : ℕ) {r : ℕ} (s : Fin r → ℕ+) (hnot : ¬ AdmEverywhere q s)
    (h : r ≤ initLen q s) : pad0 s (domLevel q s - 1) = q := by
  classical
  rw [domLevel_eq_depth q s h]
  by_contra hne
  apply hnot
  intro m
  rw [kAdmissible_iff]
  refine ⟨by omega, ?_⟩
  rintro ⟨hr1, -, -, hpad⟩
  exact hne hpad

end ZagierHoffmanPositiveChar
