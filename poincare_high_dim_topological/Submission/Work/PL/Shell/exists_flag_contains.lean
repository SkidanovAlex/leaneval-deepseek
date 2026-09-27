import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Shell.Basic
import Submission.Work.PL.Shell.flagEnum_mem
import Submission.Work.PL.Shell.flagEnum_sorted
import Submission.Work.PL.Shell.keyLt_suffix
import Submission.Work.PL.Shell.swap_adjacent
import Submission.Work.PL.Shell.exists_ascent

open Set Metric Finset

namespace Work.PL.Shell

variable {N : ℕ}

/-! ### Auxiliary order facts for `keyLt` -/

/-- `keyLt` is irreflexive. -/
private lemma keyLt_irrefl {α : Type*} [Preorder α] (a : List α) : ¬ keyLt a a := by
  rintro ⟨i, hi, ht, x, y, hx, hy, hlt⟩
  rw [hx] at hy
  exact (ne_of_lt hlt) (Option.some.inj hy)

/-- `keyLt` is transitive. -/
private lemma keyLt_trans {α : Type*} [Preorder α] {a b c : List α}
    (hab : keyLt a b) (hbc : keyLt b c) : keyLt a c := by
  obtain ⟨i, hi, htab, x, y, hai, hbi, hxy⟩ := hab
  obtain ⟨j, hj, htbc, x', y', hbj, hcj, hx'y'⟩ := hbc
  rcases lt_trichotomy i j with hij | hij | hji
  · have hbc_i : b.take i = c.take i := by
      have h := congrArg (fun l : List α => l.take i) htbc
      rw [List.take_take, List.take_take, Nat.min_eq_left (le_of_lt hij)] at h
      exact h
    have hbc_get : getElem? b i = getElem? c i := by
      have h := congrArg (fun l : List α => getElem? l i) htbc
      simp only [List.getElem?_take_of_lt hij] at h
      exact h
    exact ⟨i, hi, htab.trans hbc_i, x, y, hai, by rw [← hbc_get]; exact hbi, hxy⟩
  · subst hij
    refine ⟨i, hi, htab.trans htbc, x, y', hai, hcj, ?_⟩
    have hyx' : y = x' := by rw [hbi] at hbj; exact Option.some.inj hbj
    exact hxy.trans (hyx'.symm ▸ hx'y')
  · have hj_a : j < a.length := lt_trans hji hi
    have hab_j : a.take j = b.take j := by
      have h := congrArg (fun l : List α => l.take j) htab
      rw [List.take_take, List.take_take, Nat.min_eq_left (le_of_lt hji)] at h
      exact h
    have hab_get : getElem? a j = getElem? b j := by
      have h := congrArg (fun l : List α => getElem? l j) htab
      simp only [List.getElem?_take_of_lt hji] at h
      exact h
    exact ⟨j, hj_a, hab_j.trans htbc, x', y', by rw [hab_get]; exact hbj, hcj, hx'y'⟩

/-- `keyLt` is asymmetric. -/
private lemma keyLt_asymm {α : Type*} [Preorder α] {a b : List α}
    (hab : keyLt a b) (hba : keyLt b a) : False :=
  keyLt_irrefl a (keyLt_trans hab hba)

/-- In the lexicographic comparison `keyLt`, replacing an entry `v` (right after a common
prefix `p`) by a strictly larger entry `w` makes the list larger. -/
lemma keyLt_append_cons {α : Type*} [LT α] {p s t : List α} {v w : α} (h : v < w) :
    keyLt (p ++ v :: s) (p ++ w :: t) := by
  refine ⟨p.length, by simp, by simp, v, w, ?_, ?_, h⟩
  · rw [List.getElem?_append_right (le_refl _)]; simp
  · rw [List.getElem?_append_right (le_refl _)]; simp

/-! ### The enumeration is increasing in the `keyLt` order -/

/-- For two flags of `flagEnum vs`, being strictly earlier in the enumeration is the same as
being strictly smaller for the `keyLt` order on the reversed rank keys. -/
private theorem mem_take_keyLt {vs : List (PL.E N)} {rk : PL.E N → ℕ} (hvs : vs.Nodup)
    (hrk : (vs.map rk).Pairwise (· < ·)) {l l' : List (PL.E N)}
    (hl : l ∈ flagEnum vs) (hl' : l' ∈ flagEnum vs) :
    l' ∈ (flagEnum vs).take ((flagEnum vs).idxOf l)
      ↔ keyLt (l'.reverse.map rk) (l.reverse.map rk) := by
  rw [List.mem_take_iff_idxOf_lt hl']
  have hsorted := flagEnum_sorted hvs hrk
  have hp : (flagEnum vs).idxOf l' < (flagEnum vs).length := List.idxOf_lt_length_iff.mpr hl'
  have hq : (flagEnum vs).idxOf l < (flagEnum vs).length := List.idxOf_lt_length_iff.mpr hl
  obtain ⟨_, hgetp⟩ := List.getElem?_eq_some_iff.mp (List.getElem?_idxOf hl')
  obtain ⟨_, hgetq⟩ := List.getElem?_eq_some_iff.mp (List.getElem?_idxOf hl)
  constructor
  · intro h
    have h1 := hsorted.rel_getElem_of_lt hp hq h
    rw [hgetp, hgetq] at h1
    exact h1
  · intro h
    by_contra hcon
    rw [not_lt] at hcon
    rcases lt_or_eq_of_le hcon with hlt | heq
    · have h1 := hsorted.rel_getElem_of_lt hq hp hlt
      rw [hgetp, hgetq] at h1
      exact keyLt_asymm h h1
    · have hl'l : l' = l := ((List.idxOf_inj hl).mp heq).symm
      rw [hl'l] at h
      exact keyLt_irrefl _ h

/-! ### Prefix sets of `Nodup` lists -/

/-- Membership of `prefAt l j` among the prefix sets of `l'` is equivalent to the two
prefix *sets* being equal (for `Nodup` lists). -/
private theorem prefAt_mem_prefixes' {l l' : List (PL.E N)} (hl : l.Nodup) (hl' : l'.Nodup)
    {j : ℕ} (hj : j < l.length) (hj' : j < l'.length) :
    prefAt l j ∈ prefixes l' ↔ prefAt l' j = prefAt l j := by
  have key : ∀ {m : List (PL.E N)} (hm : m.Nodup) {k : ℕ} (hk : k < m.length),
      (prefAt m k).card = k + 1 := by
    intro m hm k hk
    unfold prefAt
    rw [List.toFinset_card_of_nodup]
    · rw [List.length_take]; omega
    · exact List.Nodup.sublist (List.take_sublist (k + 1) m) hm
  constructor
  · intro h
    rw [prefixes, Finset.mem_image] at h
    obtain ⟨i, hi, hii⟩ := h
    rw [Finset.mem_range] at hi
    have hij : i = j := by
      have h1 := key hl' hi
      have h2 := key hl hj
      rw [hii] at h1
      omega
    rw [hij] at hii
    exact hii
  · intro h
    rw [prefixes, Finset.mem_image]
    exact ⟨j, Finset.mem_range.mpr hj', h⟩

/-! ### The ascent indices of a flag -/

private lemma mem_ascIdxAux {rk : PL.E N → ℕ} {ps : List (PL.E N × PL.E N)} {i s : ℕ} :
    s ∈ ascIdxAux rk ps i ↔ ∃ (k : ℕ), s = i + k ∧ ∃ p : PL.E N × PL.E N,
      getElem? ps k = some p ∧ rk p.1 < rk p.2 := by
  induction ps generalizing i with
  | nil => simp [ascIdxAux]
  | cons q ps ih =>
    have hstep : ascIdxAux rk (q :: ps) i =
        (if rk q.1 < rk q.2 then insert i (ascIdxAux rk ps (i + 1))
         else ascIdxAux rk ps (i + 1)) := rfl
    rw [hstep]
    by_cases hc : rk q.1 < rk q.2
    · rw [if_pos hc]
      constructor
      · intro h
        rcases Finset.mem_insert.mp h with h | h
        · exact ⟨0, by simp [h], q, by simp, hc⟩
        · obtain ⟨k, hs, p, hp, hrk⟩ := ih.mp h
          exact ⟨k + 1, by omega, p, by rw [List.getElem?_cons_succ]; exact hp, hrk⟩
      · rintro ⟨k, hs, p, hp, hrk⟩
        rcases k with _ | k'
        · rw [Nat.add_zero] at hs
          exact Finset.mem_insert.mpr (Or.inl hs)
        · rw [List.getElem?_cons_succ] at hp
          refine Finset.mem_insert.mpr (Or.inr (ih.mpr ⟨k', ?_, p, hp, hrk⟩))
          omega
    · rw [if_neg hc]
      constructor
      · intro h
        obtain ⟨k, hs, p, hp, hrk⟩ := ih.mp h
        exact ⟨k + 1, by omega, p, by rw [List.getElem?_cons_succ]; exact hp, hrk⟩
      · rintro ⟨k, hs, p, hp, hrk⟩
        rcases k with _ | k'
        · rw [List.getElem?_cons_zero, Option.some.injEq] at hp
          rw [← hp] at hrk
          exact absurd hrk hc
        · rw [List.getElem?_cons_succ] at hp
          refine ih.mpr ⟨k', ?_, p, hp, hrk⟩
          omega

private lemma getElem?_zip_tail {l : List (PL.E N)} {k : ℕ} {p : PL.E N × PL.E N} :
    getElem? (l.zip l.tail) k = some p ↔
      getElem? l k = some p.1 ∧ getElem? l (k + 1) = some p.2 := by
  constructor
  · intro hp
    obtain ⟨hk, hkEq⟩ := List.getElem?_eq_some_iff.mp hp
    have hkl : k < l.length := List.lt_length_left_of_zip hk
    have hkt : k < l.tail.length := List.lt_length_right_of_zip hk
    have hk1 : k + 1 < l.length := by rw [List.length_tail] at hkt; omega
    have h2 : getElem l.tail k hkt = getElem l (k + 1) hk1 := List.getElem_tail hkt
    rw [List.getElem_zip, h2] at hkEq
    have hfst : l[k]'hkl = p.1 := by
      have := congrArg Prod.fst hkEq
      simpa using this
    have hsnd : l[k + 1]'hk1 = p.2 := by
      have := congrArg Prod.snd hkEq
      simpa using this
    exact ⟨by rw [List.getElem?_eq_getElem hkl, hfst],
           by rw [List.getElem?_eq_getElem hk1, hsnd]⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨hk1, hk1'⟩ := List.getElem?_eq_some_iff.mp h1
    obtain ⟨hk2, hk2'⟩ := List.getElem?_eq_some_iff.mp h2
    have hkt : k < l.tail.length := by rw [List.length_tail]; omega
    have hkz : k < (l.zip l.tail).length := by
      rw [List.length_zip, List.length_tail, Nat.min_def]
      split <;> omega
    rw [List.getElem?_eq_getElem hkz]
    rw [List.getElem_zip]
    rw [show getElem l.tail k (List.lt_length_right_of_zip hkz) = getElem l (k + 1) hk2 from
      List.getElem_tail (List.lt_length_right_of_zip hkz)]
    rw [hk1', hk2']

/-- Membership in `ascIdx`, in terms of `getElem?`. -/
private lemma mem_ascIdx_l {rk : PL.E N → ℕ} {l : List (PL.E N)} {s : ℕ} :
    s ∈ ascIdx rk l ↔ ∃ x y, getElem? l s = some x ∧ getElem? l (s + 1) = some y ∧ rk x < rk y := by
  rw [ascIdx, mem_ascIdxAux]
  constructor
  · rintro ⟨k, hs, p, hp, hrk⟩
    rw [Nat.zero_add] at hs
    subst hs
    obtain ⟨h1, h2⟩ := getElem?_zip_tail.mp hp
    exact ⟨p.1, p.2, h1, h2, hrk⟩
  · rintro ⟨x, y, h1, h2, hrk⟩
    exact ⟨s, by rw [Nat.zero_add], (x, y), getElem?_zip_tail.mpr ⟨h1, h2⟩, hrk⟩

/-- Membership in `ascIdx`, in the form used downstream. -/
private theorem ascIdx_mem' {rk : PL.E N → ℕ} {l : List (PL.E N)} {s : ℕ} :
    s ∈ ascIdx rk l ↔ ∃ (h : s + 1 < l.length),
      rk (l[s]'(Nat.lt_of_succ_lt h)) < rk (l[s + 1]'h) := by
  rw [mem_ascIdx_l]
  constructor
  · rintro ⟨x, y, h1, h2, hrk⟩
    obtain ⟨hx, hx'⟩ := List.getElem?_eq_some_iff.mp h1
    obtain ⟨hy, hy'⟩ := List.getElem?_eq_some_iff.mp h2
    refine ⟨hy, ?_⟩
    have e1 : l[s]'(Nat.lt_of_succ_lt hy) = x := hx'
    have e2 : l[s + 1]'hy = y := hy'
    rw [e1, e2]; exact hrk
  · rintro ⟨h, hrk⟩
    exact ⟨l[s]'(Nat.lt_of_succ_lt h), l[s + 1]'h,
      List.getElem?_eq_getElem (Nat.lt_of_succ_lt h), List.getElem?_eq_getElem h, hrk⟩

/-! ### The main argument -/

/-- `seqAt l rk t = rk (l[t])` when `t` is a valid index, and `0` otherwise. -/
private def seqAt (l : List (PL.E N)) (rk : PL.E N → ℕ) : ℕ → ℕ :=
  fun t => (getElem? l t).map rk |>.getD 0

/-- The core combinatorial statement, phrased in terms of permutations of `vs` and the
`keyLt` order rather than the enumeration `flagEnum`. -/
private theorem core {vs : List (PL.E N)} {rk : PL.E N → ℕ} (hvs : vs.Nodup)
    (hrk : (vs.map rk).Pairwise (· < ·)) {l : List (PL.E N)} (hlp : l.Perm vs)
    {J : Finset ℕ} (hJ : ∀ j ∈ J, j < l.length) :
    (∃ l' : List (PL.E N), l'.Perm vs ∧ keyLt (l'.reverse.map rk) (l.reverse.map rk) ∧
        ∀ j ∈ J, prefAt l j ∈ prefixes l')
      ↔ ¬ (ascIdx rk l ⊆ J) := by
  have hlnodup : l.Nodup := (List.Perm.nodup_iff hlp).mpr hvs
  constructor
  · -- ---------------------------------------------------------------- backward direction
    rintro ⟨l', hl'perm, hkey, hP⟩
    have hl'nodup : l'.Nodup := (List.Perm.nodup_iff hl'perm).mpr hvs
    have hlen : l'.length = l.length := by rw [hl'perm.length_eq, hlp.length_eq]
    obtain ⟨i, hi, hsuf, x, y, hx, hy, hlt⟩ := (keyLt_suffix hvs hrk hlp hl'perm).mp hkey
    have hxmem : x ∈ l' := List.mem_iff_getElem?.mpr ⟨i, hx⟩
    have hxvs : x ∈ vs := (List.Perm.mem_iff hl'perm).mp hxmem
    obtain ⟨p, hp, hpx⟩ := List.mem_iff_getElem.mp ((List.Perm.mem_iff hlp).mpr hxvs)
    have hpx_get : getElem? l p = some x := by rw [List.getElem?_eq_getElem hp, hpx]
    have hpi : p < i := by
      rcases lt_trichotomy p i with h | h | h
      · exact h
      · exfalso
        have hsome : (getElem? l p).map rk = (getElem? l i).map rk := by rw [h]
        rw [hpx_get, hy] at hsome
        exact absurd (Option.some.inj hsome) (ne_of_lt hlt)
      · exfalso
        have hp_lt : p < l'.length := by rw [hlen]; exact hp
        have hEq : getElem? l' i = getElem? l' p := by
          rw [hx, hsuf p h hp, List.getElem?_eq_getElem hp, hpx]
        exact (List.nodup_iff_getElem?_ne_getElem?.mp hl'nodup i p h hp_lt) hEq
    have hJcond : ∀ j ∈ J, j < i → j < p := by
      intro j hjJ hji
      have hjl : j < l.length := hJ j hjJ
      have hjl' : j < l'.length := by rw [hlen]; exact hjl
      have heq : prefAt l' j = prefAt l j :=
        (prefAt_mem_prefixes' hlnodup hl'nodup hjl hjl').mp (hP j hjJ)
      have hxnot : x ∉ prefAt l' j := by
        intro hmem
        rw [prefAt, List.mem_toFinset, List.mem_iff_getElem?] at hmem
        obtain ⟨q, hq⟩ := hmem
        have hq_lt : q < j + 1 := by
          by_contra hc
          push_neg at hc
          have hz : getElem? (l'.take (j + 1)) q = none := by
            rw [List.getElem?_take, if_neg (by omega)]
          rw [hz] at hq
          simp at hq
        have hqeq : getElem? l' q = some x := by
          rw [List.getElem?_take_of_lt hq_lt] at hq; exact hq
        exact (List.nodup_iff_getElem?_ne_getElem?.mp hl'nodup q i (by omega)
          (by rw [hlen]; exact hi)) (hqeq.trans hx.symm)
      rw [heq] at hxnot
      rw [prefAt, List.mem_toFinset, List.mem_iff_getElem?] at hxnot
      by_contra hnp
      push_neg at hnp
      refine hxnot ⟨p, ?_⟩
      rw [List.getElem?_take_of_lt (by omega : p < j + 1)]
      rw [List.getElem?_eq_getElem hp, hpx]
    have hlt' : seqAt l rk p < seqAt l rk i := by
      have e1 : seqAt l rk p = rk x := by simp [seqAt, hpx_get]
      have e2 : seqAt l rk i = rk y := by simp [seqAt, hy]
      rw [e1, e2]; exact hlt
    obtain ⟨s, hsp, hsi, hslt⟩ := exists_ascent hpi hlt'
    have hs1 : s + 1 < l.length := by omega
    have hsrk : rk (l[s]'(Nat.lt_of_succ_lt hs1)) < rk (l[s + 1]'hs1) := by
      have e1 : seqAt l rk s = rk (l[s]'(Nat.lt_of_succ_lt hs1)) := by
        simp [seqAt, List.getElem?_eq_getElem (Nat.lt_of_succ_lt hs1)]
      have e2 : seqAt l rk (s + 1) = rk (l[s + 1]'hs1) := by
        simp [seqAt, List.getElem?_eq_getElem hs1]
      rw [e1, e2] at hslt; exact hslt
    have hs_notJ : s ∉ J := by
      intro hsJ
      have h1 : s < p := hJcond s hsJ hsi
      omega
    exact Finset.not_subset.mpr ⟨s, ascIdx_mem'.mpr ⟨hs1, hsrk⟩, hs_notJ⟩
  · -- ---------------------------------------------------------------- forward direction
    intro hnotsub
    obtain ⟨s, hs_asc, hs_notJ⟩ := Finset.not_subset.mp hnotsub
    obtain ⟨hs1, hslt⟩ := ascIdx_mem'.mp hs_asc
    set a := l.take s with ha
    set b := l.drop (s + 2) with hb
    set x := l[s]'(Nat.lt_of_succ_lt hs1) with hx
    set y := l[s + 1]'hs1 with hy
    have hlist : l.take s ++ [l[s + 1]'hs1, l[s]'(Nat.lt_of_succ_lt hs1)] ++ l.drop (s + 2)
        = a ++ y :: x :: b := by simp [ha, hb, hx, hy]
    have hperm : (a ++ y :: x :: b).Perm l := by
      have hsw := (swap_adjacent hs1).1
      rwa [hlist] at hsw
    have hL : l = a ++ x :: y :: b := by
      have h1 : l.drop s = l[s]'(Nat.lt_of_succ_lt hs1) :: l.drop (s + 1) :=
        List.drop_eq_getElem_cons (Nat.lt_of_succ_lt hs1)
      have h2 : l.drop (s + 1) = l[s + 1]'hs1 :: l.drop (s + 2) :=
        List.drop_eq_getElem_cons hs1
      calc l = l.take s ++ l.drop s := (List.take_append_drop s l).symm
        _ = l.take s ++ (l[s]'(Nat.lt_of_succ_lt hs1) :: l.drop (s + 1)) := by rw [h1]
        _ = l.take s ++ (l[s]'(Nat.lt_of_succ_lt hs1) :: l[s + 1]'hs1 :: l.drop (s + 2)) := by
              rw [h2]
        _ = a ++ x :: y :: b := by simp [ha, hb, hx, hy]
    refine ⟨a ++ y :: x :: b, hperm.trans hlp, ?_, ?_⟩
    · have hKl' : (a ++ y :: x :: b).reverse.map rk
          = (b.reverse.map rk) ++ rk x :: rk y :: (a.reverse.map rk) := by
        simp [List.reverse_append, List.map_append]
      have hKl : l.reverse.map rk
          = (b.reverse.map rk) ++ rk y :: rk x :: (a.reverse.map rk) := by
        rw [hL]; simp [List.reverse_append, List.map_append]
      rw [hKl', hKl]
      exact keyLt_append_cons hslt
    · intro j hj
      have hjne : j ≠ s := fun h => hs_notJ (h ▸ hj)
      have hjl : j < l.length := hJ j hj
      have hjl' : j < (a ++ y :: x :: b).length := by rw [hperm.length_eq]; exact hjl
      refine Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hjl', ?_⟩
      have hsw := (swap_adjacent hs1).2 j hjne
      rwa [hlist] at hsw

theorem exists_flag_contains {vs : List (PL.E N)} {rk : PL.E N → ℕ} (hvs : vs.Nodup)
    (hrk : (vs.map rk).Pairwise (· < ·)) {l : List (PL.E N)} (hl : l ∈ Work.PL.Shell.flagEnum vs)
    {J : Finset ℕ} (hJ : ∀ j ∈ J, j < l.length) :
    (∃ l' ∈ (Work.PL.Shell.flagEnum vs).take ((Work.PL.Shell.flagEnum vs).idxOf l),
        ∀ j ∈ J, Work.PL.Shell.prefAt l j ∈ Work.PL.Shell.prefixes l')
      ↔ ¬ (Work.PL.Shell.ascIdx rk l ⊆ J) := by
  have hlp : l.Perm vs := flagEnum_mem.mp hl
  have hstep : (∃ l' ∈ (flagEnum vs).take ((flagEnum vs).idxOf l),
        ∀ j ∈ J, prefAt l j ∈ prefixes l')
      ↔ (∃ l' : List (PL.E N), l'.Perm vs ∧ keyLt (l'.reverse.map rk) (l.reverse.map rk) ∧
          ∀ j ∈ J, prefAt l j ∈ prefixes l') := by
    constructor
    · rintro ⟨l', hm, hP⟩
      exact ⟨l', flagEnum_mem.mp (List.mem_of_mem_take hm),
        (mem_take_keyLt hvs hrk hl (List.mem_of_mem_take hm)).mp hm, hP⟩
    · rintro ⟨l', hl'perm, hkey, hP⟩
      have hl'fe : l' ∈ flagEnum vs := flagEnum_mem.mpr hl'perm
      exact ⟨l', (mem_take_keyLt hvs hrk hl hl'fe).mpr hkey, hP⟩
  rw [hstep]
  exact core hvs hrk hlp hJ

end Work.PL.Shell
