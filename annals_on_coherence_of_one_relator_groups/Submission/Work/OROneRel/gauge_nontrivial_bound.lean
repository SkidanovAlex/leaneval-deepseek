import Mathlib
import Submission.Work.OROneRel.GaugeDefs
import Submission.Work.OROneRel.gauge_truncation
import Submission.Work.OROneRel.gaugeLevelDefs

/-!
# The number of decorated letters of non-trivial loop class

Let `c : α → ℤ` be a weight function and `u` a word.  The decorated word `decor c 0 (wordOf u)` is a
walk on the levels `ℤ`: its `k`-th letter runs from level `(lv c 0 M)[k]` to level `(lv c 0 M)[k+1]`
and carries the label `(lab M)[k]` (`M = wordOf u`), where `lv` is the list of levels and `lab` the
list of labels (`Submission/Work/OROneRel/gaugeLevelDefs.lean`); this is the content of the lemmas
`decor_get?_coverSrc`, `decor_get?_coverTgt` and `decor_get?_coverLetter` below.  The loop class of
that letter under a gauge `W` is `W (lv[k]) * lab[k] * (W (lv[k+1]))⁻¹` (`gauge_letter`).

The *first-arrival gauge* `gaugeIter L x` assigns to each level the product of the labels along the
chain of levels that first discovered it (`gaugeStep`, `gaugeIter`).  Every letter that arrives at a
level not visited before is then of trivial loop class (`gaugeIter_spec`,
`exists_gauge_kills_first`), so among the `N = (decor c 0 (wordOf u)).length` letters only the
letters arriving at a *revisited* level can have non-trivial loop class.  The number of revisited
positions is `N - (V - 1)`, where `V` is the number of distinct levels visited
(`card_revisit_positions'`); as at most one occurrence per distinct symbol is counted in the
statement, this bounds the number of distinct decorated letters of non-trivial loop class by
`N - (V - 1)`.  The set `{p.1.2}` of "stored levels" of the statement is contained in the set of
visited levels (`coverSrc_mem_lv`, `coverTgt_mem_lv`), which gives the final bound.
-/

namespace Work.OROneRel
universe u
variable {α : Type u}

/-- The zeroth entry of the level list is the starting level. -/
theorem lv_getD_zero (c : α → ℤ) (i : ℤ) (M : List (α × Bool)) : (lv c i M).getD 0 0 = i := by
  cases M with
  | nil => rfl
  | cons p M => rw [lv_cons, List.getD_cons_zero]

/-- The starting level is one of the levels. -/
theorem lv_head_mem (c : α → ℤ) (i : ℤ) (M : List (α × Bool)) : i ∈ lv c i M := by
  cases M with
  | nil => simp [lv]
  | cons p M => rw [lv_cons]; exact List.mem_cons_self

/-- **The source level of the `k`-th decorated letter is the `k`-th level.** -/
theorem decor_get?_coverSrc (c : α → ℤ) (i : ℤ) (M : List (α × Bool)) (k : ℕ)
    {p : (α × ℤ) × Bool} (hp : (decor c i M)[k]? = some p) :
    coverSrc c p = (lv c i M).getD k 0 := by
  induction M generalizing i k with
  | nil => simp [decor] at hp
  | cons q M ih =>
      obtain ⟨a, b⟩ := q
      cases b
      · cases k with
        | zero =>
            rw [show decor c i ((a, false) :: M) = ((a, i - c a), false) :: decor c (i - c a) M
                from rfl] at hp
            rw [List.getElem?_cons_zero, Option.some.injEq] at hp
            subst hp
            rw [lv_cons, List.getD_cons_zero]
            simp only [coverSrc, Bool.false_eq_true, if_false]
            ring
        | succ k =>
            rw [show decor c i ((a, false) :: M) = ((a, i - c a), false) :: decor c (i - c a) M
                from rfl] at hp
            rw [List.getElem?_cons_succ] at hp
            rw [lv_cons, List.getD_cons_succ]
            exact ih (i - c a) k hp
      · cases k with
        | zero =>
            rw [show decor c i ((a, true) :: M) = ((a, i), true) :: decor c (i + c a) M
                from rfl] at hp
            rw [List.getElem?_cons_zero, Option.some.injEq] at hp
            subst hp
            rw [lv_cons, List.getD_cons_zero]
            simp only [coverSrc, if_true]
        | succ k =>
            rw [show decor c i ((a, true) :: M) = ((a, i), true) :: decor c (i + c a) M
                from rfl] at hp
            rw [List.getElem?_cons_succ] at hp
            rw [lv_cons, List.getD_cons_succ]
            exact ih (i + c a) k hp

/-- **The target level of the `k`-th decorated letter is the `(k+1)`-st level.** -/
theorem decor_get?_coverTgt (c : α → ℤ) (i : ℤ) (M : List (α × Bool)) (k : ℕ)
    {p : (α × ℤ) × Bool} (hp : (decor c i M)[k]? = some p) :
    coverTgt c p = (lv c i M).getD (k + 1) 0 := by
  induction M generalizing i k with
  | nil => simp [decor] at hp
  | cons q M ih =>
      obtain ⟨a, b⟩ := q
      cases b
      · cases k with
        | zero =>
            rw [show decor c i ((a, false) :: M) = ((a, i - c a), false) :: decor c (i - c a) M
                from rfl] at hp
            rw [List.getElem?_cons_zero, Option.some.injEq] at hp
            subst hp
            rw [lv_cons, List.getD_cons_succ, lv_getD_zero]
            simp only [coverTgt, Bool.false_eq_true, if_false, linc]
            ring
        | succ k =>
            rw [show decor c i ((a, false) :: M) = ((a, i - c a), false) :: decor c (i - c a) M
                from rfl] at hp
            rw [List.getElem?_cons_succ] at hp
            rw [lv_cons, List.getD_cons_succ]
            exact ih (i - c a) k hp
      · cases k with
        | zero =>
            rw [show decor c i ((a, true) :: M) = ((a, i), true) :: decor c (i + c a) M
                from rfl] at hp
            rw [List.getElem?_cons_zero, Option.some.injEq] at hp
            subst hp
            rw [lv_cons, List.getD_cons_succ, lv_getD_zero]
            simp only [coverTgt, if_true, linc]
        | succ k =>
            rw [show decor c i ((a, true) :: M) = ((a, i), true) :: decor c (i + c a) M
                from rfl] at hp
            rw [List.getElem?_cons_succ] at hp
            rw [lv_cons, List.getD_cons_succ]
            exact ih (i + c a) k hp

/-- **The label of the `k`-th decorated letter is the `k`-th label.** -/
theorem decor_get?_coverLetter (c : α → ℤ) (i : ℤ) (M : List (α × Bool)) (k : ℕ)
    {p : (α × ℤ) × Bool} (hp : (decor c i M)[k]? = some p) :
    coverLetter p = (lab M).getD k 1 := by
  induction M generalizing i k with
  | nil => simp [decor] at hp
  | cons q M ih =>
      obtain ⟨a, b⟩ := q
      cases b
      · cases k with
        | zero =>
            rw [show decor c i ((a, false) :: M) = ((a, i - c a), false) :: decor c (i - c a) M
                from rfl] at hp
            rw [List.getElem?_cons_zero, Option.some.injEq] at hp
            subst hp
            rw [lab, List.map_cons, List.getD_cons_zero]
            simp only [coverLetter, Bool.false_eq_true, if_false]
        | succ k =>
            rw [show decor c i ((a, false) :: M) = ((a, i - c a), false) :: decor c (i - c a) M
                from rfl] at hp
            rw [List.getElem?_cons_succ] at hp
            rw [lab, List.map_cons, List.getD_cons_succ]
            exact ih (i - c a) k hp
      · cases k with
        | zero =>
            rw [show decor c i ((a, true) :: M) = ((a, i), true) :: decor c (i + c a) M
                from rfl] at hp
            rw [List.getElem?_cons_zero, Option.some.injEq] at hp
            subst hp
            rw [lab, List.map_cons, List.getD_cons_zero]
            simp only [coverLetter, if_true]
        | succ k =>
            rw [show decor c i ((a, true) :: M) = ((a, i), true) :: decor c (i + c a) M
                from rfl] at hp
            rw [List.getElem?_cons_succ] at hp
            rw [lab, List.map_cons, List.getD_cons_succ]
            exact ih (i + c a) k hp

theorem coverSrc_mem_lv (c : α → ℤ) (i : ℤ) (M : List (α × Bool)) {p : (α × ℤ) × Bool}
    (hp : p ∈ decor c i M) : coverSrc c p ∈ lv c i M := by
  induction M generalizing i with
  | nil => simp [decor] at hp
  | cons q M ih =>
      obtain ⟨a, b⟩ := q
      cases b
      · rw [show decor c i ((a, false) :: M) = ((a, i - c a), false) :: decor c (i - c a) M
            from rfl] at hp
        rw [lv_cons]
        rcases List.mem_cons.mp hp with h | h
        · subst h
          have hcv : coverSrc c ((a, i - c a), false) = i := by
            simp only [coverSrc, Bool.false_eq_true, if_false]; ring
          rw [hcv]
          simp only [linc, Bool.false_eq_true, if_false]
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih (i - c a) h)
      · rw [show decor c i ((a, true) :: M) = ((a, i), true) :: decor c (i + c a) M
            from rfl] at hp
        rw [lv_cons]
        rcases List.mem_cons.mp hp with h | h
        · subst h
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih (i + c a) h)

theorem coverTgt_mem_lv (c : α → ℤ) (i : ℤ) (M : List (α × Bool)) {p : (α × ℤ) × Bool}
    (hp : p ∈ decor c i M) : coverTgt c p ∈ lv c i M := by
  induction M generalizing i with
  | nil => simp [decor] at hp
  | cons q M ih =>
      obtain ⟨a, b⟩ := q
      cases b
      · rw [show decor c i ((a, false) :: M) = ((a, i - c a), false) :: decor c (i - c a) M
            from rfl] at hp
        rw [lv_cons]
        rcases List.mem_cons.mp hp with h | h
        · subst h
          have hcv : coverTgt c ((a, i - c a), false) = i - c a := rfl
          rw [hcv]
          exact List.mem_cons_of_mem _ (lv_head_mem c (i - c a) M)
        · exact List.mem_cons_of_mem _ (ih (i - c a) h)
      · rw [show decor c i ((a, true) :: M) = ((a, i), true) :: decor c (i + c a) M
            from rfl] at hp
        rw [lv_cons]
        rcases List.mem_cons.mp hp with h | h
        · subst h
          rw [show coverTgt c ((a, i), true) = i + c a from rfl]
          exact List.mem_cons_of_mem _ (lv_head_mem c (i + c a) M)
        · exact List.mem_cons_of_mem _ (ih (i + c a) h)


/-! ## The core (from ._gnb/core.lean) -/

noncomputable def gaugeStep (L : List ℤ) (x : List (FreeGroup α)) (m : ℕ)
    (W : ℤ → FreeGroup α) : ℤ → FreeGroup α :=
  fun i =>
    if L.getD (m + 1) 0 ∈ L.take (m + 1) then W i
    else if i = L.getD (m + 1) 0 then W (L.getD m 0) * x.getD m 1 else W i

noncomputable def gaugeIter (L : List ℤ) (x : List (FreeGroup α)) : ℕ → ℤ → FreeGroup α
  | 0 => fun _ => 1
  | (m + 1) => gaugeStep L x m (gaugeIter L x m)

theorem gaugeIter_succ_apply (L : List ℤ) (x : List (FreeGroup α)) (m : ℕ) (i : ℤ) :
    gaugeIter L x (m + 1) i =
      (if L.getD (m + 1) 0 ∈ L.take (m + 1) then gaugeIter L x m i
       else if i = L.getD (m + 1) 0 then gaugeIter L x m (L.getD m 0) * x.getD m 1
       else gaugeIter L x m i) := by
  simp only [gaugeIter, gaugeStep]

theorem gaugeIter_succ_of_mem (L : List ℤ) (x : List (FreeGroup α)) (m : ℕ)
    (h : L.getD (m + 1) 0 ∈ L.take (m + 1)) :
    gaugeIter L x (m + 1) = gaugeIter L x m := by
  funext i
  rw [gaugeIter_succ_apply, if_pos h]

theorem gaugeIter_succ_of_notMem (L : List ℤ) (x : List (FreeGroup α)) (m : ℕ)
    (h : L.getD (m + 1) 0 ∉ L.take (m + 1)) {i : ℤ} (hi : i ≠ L.getD (m + 1) 0) :
    gaugeIter L x (m + 1) i = gaugeIter L x m i := by
  rw [gaugeIter_succ_apply, if_neg h, if_neg hi]

theorem gaugeIter_succ_self (L : List ℤ) (x : List (FreeGroup α)) (m : ℕ)
    (h : L.getD (m + 1) 0 ∉ L.take (m + 1)) :
    gaugeIter L x (m + 1) (L.getD (m + 1) 0) =
      gaugeIter L x m (L.getD m 0) * x.getD m 1 := by
  rw [gaugeIter_succ_apply, if_neg h, if_pos rfl]

theorem getD_mem_take {L : List ℤ} {k m : ℕ} (hk : k < m) (hm : m ≤ L.length) :
    L.getD k 0 ∈ L.take m := by
  have hkL : k < L.length := lt_of_lt_of_le hk hm
  have h1 : k < (L.take m).length := by rw [List.length_take]; omega
  have h2 : (L.take m)[k] = L.getD k 0 := by
    rw [List.getElem_take, List.getD_eq_getElem _ _ hkL]
  rw [← h2]
  exact List.getElem_mem h1

theorem gaugeIter_spec (L : List ℤ) (x : List (FreeGroup α))
    (hlen : L.length = x.length + 1) (m : ℕ) (hm : m ≤ x.length) :
    gaugeIter L x m (L.getD 0 0) = 1 ∧
      ∀ k, k < m → L.getD (k + 1) 0 ∉ L.take (k + 1) →
        gaugeIter L x m (L.getD k 0) * x.getD k 1 *
          (gaugeIter L x m (L.getD (k + 1) 0))⁻¹ = 1 := by
  induction m with
  | zero =>
      refine ⟨rfl, ?_⟩
      intro k hk
      omega
  | succ m ih =>
      have hmle : m ≤ x.length := by omega
      have hLm : m + 1 ≤ L.length := by omega
      have ih' := ih hmle
      have hne : L.getD (m + 1) 0 ∉ L.take (m + 1) →
          ∀ k, k < m + 1 → L.getD k 0 ≠ L.getD (m + 1) 0 := by
        intro htake k hk hcon
        exact htake (hcon ▸ getD_mem_take (k := k) (m := m + 1) hk hLm)
      by_cases htake : L.getD (m + 1) 0 ∈ L.take (m + 1)
      · rw [gaugeIter_succ_of_mem L x m htake]
        refine ⟨ih'.1, ?_⟩
        intro k hk hkv
        by_cases hk' : k < m
        · exact ih'.2 k hk' hkv
        · have hkm : k = m := by omega
          exact absurd htake (hkm ▸ hkv)
      · have hne' := hne htake
        refine ⟨?_, ?_⟩
        · rw [gaugeIter_succ_of_notMem L x m htake (i := L.getD 0 0) (hne' 0 (by omega))]
          exact ih'.1
        · intro k hk hkv
          by_cases hk' : k < m
          · rw [gaugeIter_succ_of_notMem L x m htake (i := L.getD k 0) (hne' k (by omega)),
              gaugeIter_succ_of_notMem L x m htake (i := L.getD (k + 1) 0) (hne' (k + 1) (by omega))]
            exact ih'.2 k hk' hkv
          · have hkm : k = m := by omega
            rw [hkm]
            rw [gaugeIter_succ_self L x m htake,
              gaugeIter_succ_of_notMem L x m htake (i := L.getD m 0) (hne' m (by omega))]
            group

theorem exists_gauge_kills_first (L : List ℤ) (x : List (FreeGroup α))
    (hlen : L.length = x.length + 1) :
    ∃ W : ℤ → FreeGroup α, W (L.getD 0 0) = 1 ∧
      ∀ k, k < x.length → L.getD (k + 1) 0 ∉ L.take (k + 1) →
        W (L.getD k 0) * x.getD k 1 * (W (L.getD (k + 1) 0))⁻¹ = 1 := by
  refine ⟨gaugeIter L x x.length, (gaugeIter_spec L x hlen x.length le_rfl).1, ?_⟩
  intro k hk
  exact (gaugeIter_spec L x hlen x.length le_rfl).2 k hk

/-! ## Position of the first occurrence -/

/-- The position of the first occurrence of `p` in `D` (`0` if `p ∉ D`). -/
noncomputable def firstPos {σ : Type*} (D : List σ) (p : σ) : ℕ :=
  letI := Classical.decEq σ
  if h : p ∈ D then Classical.choose (List.mem_iff_getElem.mp h) else 0

theorem firstPos_lt {σ : Type*} (D : List σ) {p : σ} (hp : p ∈ D) :
    firstPos D p < D.length := by
  rw [firstPos, dif_pos hp]
  obtain ⟨hi, -⟩ := Classical.choose_spec (List.mem_iff_getElem.mp hp)
  exact hi

theorem firstPos_getD {σ : Type*} (D : List σ) {p : σ} (hp : p ∈ D) :
    D.getD (firstPos D p) p = p := by
  rw [firstPos, dif_pos hp]
  obtain ⟨hi, hget⟩ := Classical.choose_spec (List.mem_iff_getElem.mp hp)
  rw [List.getD_eq_getElem D p hi, hget]

theorem firstPos_injOn {σ : Type*} (D : List σ) :
    Set.InjOn (firstPos D) {p | p ∈ D} := by
  intro p hp q hq hpq
  have h1 : p = D.getD (firstPos D p) p := (firstPos_getD D hp).symm
  have h2 : D.getD (firstPos D p) p = D.getD (firstPos D q) p := by rw [hpq]
  have h3 : D.getD (firstPos D q) p = D.getD (firstPos D q) q := by
    rw [List.getD_eq_getElem D p (firstPos_lt D hq),
      List.getD_eq_getElem D q (firstPos_lt D hq)]
  have h4 : D.getD (firstPos D q) q = q := firstPos_getD D hq
  exact h1.trans (h2.trans (h3.trans h4))

/-- **Counting distinct bad letters by positions.** -/
theorem card_filter_toFinset_le {σ : Type*} [DecidableEq σ] (D : List σ) (bad : σ → Prop)
    [DecidablePred bad] (G : Finset ℕ) (hsub : ∀ p, p ∈ D → bad p → firstPos D p ∈ G) :
    (D.toFinset.filter bad).card ≤ G.card := by
  classical
  have hinj : Set.InjOn (firstPos D) ↑(D.toFinset.filter bad) := by
    intro p hp q hq hpq
    refine firstPos_injOn D ?_ ?_ hpq
    · rw [Finset.mem_coe, Finset.mem_filter, List.mem_toFinset] at hp
      exact hp.1
    · rw [Finset.mem_coe, Finset.mem_filter, List.mem_toFinset] at hq
      exact hq.1
  have hsub' : (D.toFinset.filter bad).image (firstPos D) ⊆ G := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨p, hp, rfl⟩ := hn
    rw [Finset.mem_filter, List.mem_toFinset] at hp
    exact hsub p hp.1 hp.2
  calc (D.toFinset.filter bad).card
      = ((D.toFinset.filter bad).image (firstPos D)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ G.card := Finset.card_le_card hsub'


/-- The least index at which `v` occurs in `L`, or `0` if `v` does not occur. -/
noncomputable def firstIdx (L : List ℤ) (v : ℤ) : ℕ := by
  classical
  exact if h : ∃ k, L[k]? = some v then Nat.find h else 0

theorem firstIdx_spec {L : List ℤ} {v : ℤ} (h : v ∈ L) : L[firstIdx L v]? = some v := by
  classical
  obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp h
  have hex : ∃ k, L[k]? = some v := ⟨k, by rw [List.getElem?_eq_getElem hk, hget]⟩
  rw [firstIdx, dif_pos hex]
  exact Nat.find_spec hex

theorem firstIdx_lt {L : List ℤ} {v : ℤ} (h : v ∈ L) : firstIdx L v < L.length := by
  obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp (firstIdx_spec h)
  exact hlt

theorem firstIdx_getD {L : List ℤ} {v : ℤ} (h : v ∈ L) : L.getD (firstIdx L v) 0 = v := by
  have hlt := firstIdx_lt h
  rw [List.getD_eq_getElem L 0 hlt]
  obtain ⟨_, hget⟩ := List.getElem?_eq_some_iff.mp (firstIdx_spec h)
  exact hget

theorem firstIdx_min {L : List ℤ} {v : ℤ} (h : v ∈ L) {j : ℕ} (hj : L[j]? = some v) :
    firstIdx L v ≤ j := by
  classical
  have hex : ∃ k, L[k]? = some v := ⟨j, hj⟩
  rw [firstIdx, dif_pos hex]
  exact Nat.find_min' hex hj

theorem firstIdx_firstVisit {L : List ℤ} {v : ℤ} (h : v ∈ L) :
    L.getD (firstIdx L v) 0 ∉ L.take (firstIdx L v) := by
  intro hmem
  obtain ⟨j, hjlt, hjeq⟩ := List.mem_take_iff_getElem.mp hmem
  have hlt := firstIdx_lt h
  have hjl : j < firstIdx L v := by
    have : j < min (firstIdx L v) L.length := hjlt
    omega
  have hjv : L[j]? = some v := by
    rw [List.getElem?_eq_getElem (lt_trans hjl hlt), hjeq, firstIdx_getD h]
  have hmin := firstIdx_min h hjv
  omega

theorem card_firstVisit (L : List ℤ) :
    ((Finset.range L.length).filter (fun k => L.getD k 0 ∉ L.take k)).card = L.toFinset.card := by
  classical
  set FV : Finset ℕ := (Finset.range L.length).filter (fun k => L.getD k 0 ∉ L.take k) with hFV
  have h1 : FV.card ≤ L.toFinset.card := by
    have hinj : Set.InjOn (fun k => L.getD k 0) ↑FV := by
      intro k hk k' hk' heq
      change L.getD k 0 = L.getD k' 0 at heq
      rw [Finset.mem_coe, hFV, Finset.mem_filter, Finset.mem_range] at hk hk'
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have hmem : L.getD k 0 ∈ L.take k' := by
          have hkk' : k < (L.take k').length := by rw [List.length_take]; omega
          have h2 : (L.take k')[k] = L.getD k 0 := by
            rw [List.getElem_take, List.getD_eq_getElem L 0 hk.1]
          rw [← h2]
          exact List.getElem_mem hkk'
        rw [heq] at hmem
        exact hk'.2 hmem
      · have hmem : L.getD k' 0 ∈ L.take k := by
          have hkk' : k' < (L.take k).length := by rw [List.length_take]; omega
          have h2 : (L.take k)[k'] = L.getD k' 0 := by
            rw [List.getElem_take, List.getD_eq_getElem L 0 hk'.1]
          rw [← h2]
          exact List.getElem_mem hkk'
        rw [← heq] at hmem
        exact hk.2 hmem
    calc FV.card = (FV.image (fun k => L.getD k 0)).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ L.toFinset.card := by
          refine Finset.card_le_card ?_
          intro x hx
          rw [Finset.mem_image] at hx
          obtain ⟨k, hk, rfl⟩ := hx
          rw [hFV, Finset.mem_filter, Finset.mem_range] at hk
          rw [List.mem_toFinset, List.getD_eq_getElem L 0 hk.1]
          exact List.getElem_mem hk.1
  have h2 : L.toFinset.card ≤ FV.card := by
    have hmap : ∀ v ∈ L.toFinset, firstIdx L v ∈ FV := by
      intro v hv
      rw [List.mem_toFinset] at hv
      rw [hFV, Finset.mem_filter, Finset.mem_range]
      exact ⟨firstIdx_lt hv, firstIdx_firstVisit hv⟩
    have hinj : Set.InjOn (firstIdx L) ↑L.toFinset := by
      intro v hv w hw heq
      rw [Finset.mem_coe, List.mem_toFinset] at hv hw
      have h1 : L.getD (firstIdx L v) 0 = v := firstIdx_getD hv
      have h2 : L.getD (firstIdx L w) 0 = w := firstIdx_getD hw
      rw [← h1, ← h2, heq]
    calc L.toFinset.card = (L.toFinset.image (firstIdx L)).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ FV.card := by
          refine Finset.card_le_card ?_
          intro x hx
          rw [Finset.mem_image] at hx
          obtain ⟨v, hv, rfl⟩ := hx
          exact hmap v hv
  omega

theorem card_revisit_positions' (L : List ℤ) :
    ((Finset.range (L.length - 1)).filter
        (fun k => L.getD (k + 1) 0 ∈ L.take (k + 1))).card
      = (L.length - 1) - (L.toFinset.card - 1) := by
  classical
  set FV : Finset ℕ := (Finset.range L.length).filter (fun k => L.getD k 0 ∉ L.take k) with hFV
  set rv : Finset ℕ := (Finset.range (L.length - 1)).filter
      (fun k => L.getD (k + 1) 0 ∈ L.take (k + 1)) with hrv
  have hfv : FV.card = L.toFinset.card := by rw [hFV]; exact card_firstVisit L
  have hpart : FV ∪ rv.image (fun k => k + 1) = Finset.range L.length := by
    ext j
    rw [Finset.mem_union, Finset.mem_image]
    constructor
    · rintro (hj | ⟨k, hk, rfl⟩)
      · rw [hFV, Finset.mem_filter] at hj
        exact hj.1
      · rw [hrv, Finset.mem_filter, Finset.mem_range] at hk
        rw [Finset.mem_range]
        omega
    · intro hj
      rw [Finset.mem_range] at hj
      by_cases h : L.getD j 0 ∈ L.take j
      · have hjpos : 1 ≤ j := by
          by_contra hlt
          have hj0 : j = 0 := by omega
          rw [hj0] at h
          simp at h
        refine Or.inr ⟨j - 1, ?_, by omega⟩
        rw [hrv, Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, ?_⟩
        rw [show j - 1 + 1 = j from by omega]
        exact h
      · exact Or.inl (by rw [hFV, Finset.mem_filter]; exact ⟨Finset.mem_range.mpr hj, h⟩)
  have hdisj : Disjoint FV (rv.image (fun k => k + 1)) := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb hab
    rw [hFV, Finset.mem_filter, Finset.mem_range] at ha
    rw [Finset.mem_image] at hb
    obtain ⟨k, hk, hkb⟩ := hb
    rw [hrv, Finset.mem_filter, Finset.mem_range] at hk
    have hka : a = k + 1 := by rw [hab, ← hkb]
    exact ha.2 (by rw [hka]; exact hk.2)
  have hsum : FV.card + rv.card = L.length := by
    have hun := Finset.card_union_of_disjoint hdisj
    rw [hpart, Finset.card_range] at hun
    have himg : (rv.image (fun k => k + 1)).card = rv.card := by
      refine Finset.card_image_of_injOn ?_
      intro a _ b _ hab
      change a + 1 = b + 1 at hab
      omega
    rw [himg] at hun
    omega
  have hle : L.toFinset.card ≤ L.length := List.toFinset_card_le L
  have hc1 : L.toFinset.card = 0 → L.length = 0 := by
    intro hc
    by_contra hL
    have hpos : 0 < L.length := Nat.pos_of_ne_zero hL
    obtain ⟨v, hv⟩ := List.length_pos_iff_exists_mem.mp hpos
    have hpos2 : 0 < L.toFinset.card := Finset.card_pos.mpr ⟨v, List.mem_toFinset.mpr hv⟩
    omega
  rcases Nat.eq_zero_or_pos L.toFinset.card with hc | hc
  · have hn0 := hc1 hc
    omega
  · omega


/-! ## Assembly -/

theorem ncard_le_revisit_bound {α : Type*} (c : α → ℤ) (M : List (α × Bool))
    (W : ℤ → FreeGroup α)
    (hkill : ∀ k, k < M.length → (lv c 0 M).getD (k + 1) 0 ∉ (lv c 0 M).take (k + 1) →
      W ((lv c 0 M).getD k 0) * (lab M).getD k 1 *
        (W ((lv c 0 M).getD (k + 1) 0))⁻¹ = 1) :
    {p : (α × ℤ) × Bool | p ∈ decor c 0 M ∧
      gaugeMap W c (if p.2 then FreeGroup.of p.1 else (FreeGroup.of p.1)⁻¹) ≠ 1}.ncard
      ≤ (decor c 0 M).length
        - ({i : ℤ | ∃ p ∈ decor c 0 M, p.1.2 = i}.ncard - 1) := by
  classical
  have hDlen : (decor c 0 M).length = M.length := decor_length c 0 M
  have hLlen : (lv c 0 M).length = M.length + 1 := lv_length c 0 M
  have hxlen : (lab M).length = M.length := lab_length M
  set F : Set ((α × ℤ) × Bool) := {p : (α × ℤ) × Bool | p ∈ decor c 0 M ∧
      gaugeMap W c (if p.2 then FreeGroup.of p.1 else (FreeGroup.of p.1)⁻¹) ≠ 1} with hF
  set T : Set ℤ := {i : ℤ | ∃ p ∈ decor c 0 M, p.1.2 = i} with hT
  set bad : (α × ℤ) × Bool → Prop := fun p =>
      gaugeMap W c (if p.2 then FreeGroup.of p.1 else (FreeGroup.of p.1)⁻¹) ≠ 1 with hbad
  set G : Finset ℕ := (Finset.range M.length).filter
      (fun k => (lv c 0 M).getD (k + 1) 0 ∈ (lv c 0 M).take (k + 1)) with hG
  -- every bad letter sits at a revisit position
  have hsub : ∀ p, p ∈ decor c 0 M → bad p → firstPos (decor c 0 M) p ∈ G := by
    intro p hpD hbad'
    set k := firstPos (decor c 0 M) p with hk
    have hkD : k < (decor c 0 M).length := firstPos_lt _ hpD
    have hkM : k < M.length := by rw [hDlen] at hkD; exact hkD
    have hletter : (decor c 0 M)[k]'hkD = p := by
      rw [← List.getD_eq_getElem (decor c 0 M) p hkD]
      exact firstPos_getD _ hpD
    have hp_some : (decor c 0 M)[k]? = some p := by
      rw [List.getElem?_eq_getElem hkD, hletter]
    rw [hG, Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr hkM, ?_⟩
    by_contra hrev
    have hkillk := hkill k hkM hrev
    have hbadk : gaugeMap W c (if ((decor c 0 M)[k]'hkD).2 then
          FreeGroup.of ((decor c 0 M)[k]'hkD).1
          else (FreeGroup.of ((decor c 0 M)[k]'hkD).1)⁻¹) ≠ 1 := by
      rw [hletter]
      exact hbad'
    have hgm : gaugeMap W c (if ((decor c 0 M)[k]'hkD).2 then
          FreeGroup.of ((decor c 0 M)[k]'hkD).1
          else (FreeGroup.of ((decor c 0 M)[k]'hkD).1)⁻¹)
        = W ((lv c 0 M).getD k 0) * (lab M).getD k 1 *
            (W ((lv c 0 M).getD (k + 1) 0))⁻¹ := by
      rw [gauge_letter W c ((decor c 0 M)[k]'hkD), hletter,
        decor_get?_coverSrc c 0 M k hp_some, decor_get?_coverTgt c 0 M k hp_some,
        decor_get?_coverLetter c 0 M k hp_some]
    exact hbadk (hgm.trans hkillk)
  have hFp : F.ncard = ((decor c 0 M).toFinset.filter bad).card := by
    have hFeq : F = ↑((decor c 0 M).toFinset.filter bad) := by
      ext p
      simp only [hF, hbad, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
        List.mem_toFinset]
    rw [hFeq, Set.ncard_coe_finset]
  have hFpG : ((decor c 0 M).toFinset.filter bad).card ≤ G.card :=
    card_filter_toFinset_le (decor c 0 M) bad G hsub
  have hGcard : G.card = M.length - ((lv c 0 M).toFinset.card - 1) := by
    have h := card_revisit_positions' (lv c 0 M)
    rw [lv_length] at h
    simp only [Nat.add_sub_cancel] at h
    rw [hG, h]
  have hTle : T.ncard ≤ (lv c 0 M).toFinset.card := by
    have hTsub : T ⊆ ↑(lv c 0 M).toFinset := by
      intro i hi
      simp only [hT, Set.mem_setOf_eq] at hi
      obtain ⟨p, hpD, hp2⟩ := hi
      rw [Finset.mem_coe, List.mem_toFinset]
      rcases p with ⟨⟨a, j⟩, b⟩
      cases b
      · have hcv : coverTgt c ((⟨a, j⟩, false) : (α × ℤ) × Bool) = j := rfl
        rw [show i = j from hp2.symm, ← hcv]
        exact coverTgt_mem_lv c 0 M hpD
      · have hcv : coverSrc c ((⟨a, j⟩, true) : (α × ℤ) × Bool) = j := rfl
        rw [show i = j from hp2.symm, ← hcv]
        exact coverSrc_mem_lv c 0 M hpD
    have hfin : T.Finite := (Finset.finite_toSet _).subset hTsub
    rw [Set.ncard_eq_toFinset_card T hfin]
    refine Finset.card_le_card ?_
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    exact hTsub hx
  rw [hDlen]
  calc F.ncard = ((decor c 0 M).toFinset.filter bad).card := hFp
    _ ≤ G.card := hFpG
    _ = M.length - ((lv c 0 M).toFinset.card - 1) := hGcard
    _ ≤ M.length - (T.ncard - 1) :=
        Nat.sub_le_sub_left (Nat.sub_le_sub_right hTle 1) M.length

/-! ## The target theorem -/

theorem gauge_nontrivial_bound {α : Type*} (c : α → ℤ) (u : FreeGroup α) :
    ∃ W : ℤ → FreeGroup α, W 0 = 1 ∧
      {p : (α × ℤ) × Bool | p ∈ decor c 0 (wordOf u) ∧
        gaugeMap W c (if p.2 then FreeGroup.of p.1 else (FreeGroup.of p.1)⁻¹) ≠ 1}.ncard
      ≤ (decor c 0 (wordOf u)).length
        - ({i : ℤ | ∃ p ∈ decor c 0 (wordOf u), p.1.2 = i}.ncard - 1) := by
  classical
  obtain ⟨W, hW, hkill⟩ := exists_gauge_kills_first (lv c 0 (wordOf u)) (lab (wordOf u))
    (by rw [lv_length, lab_length])
  rw [lab_length] at hkill
  refine ⟨W, ?_, ?_⟩
  · rw [← lv_getD_zero c 0 (wordOf u)]
    exact hW
  · exact ncard_le_revisit_bound c (wordOf u) W hkill

end Work.OROneRel
