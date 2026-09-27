import Mathlib
import Submission.Work.PL.Shell.Basic
import Submission.Work.PL.Shell.flagEnum_sorted
import Submission.Work.PL.Shell.flagEnum_mem

namespace Work.PL.Shell

variable {N : ℕ}

/-- `keyLt` is irreflexive: no list is smaller than itself in this sense. -/
private lemma keyLt_irrefl {α : Type*} [LinearOrder α] (a : List α) : ¬ keyLt a a := by
  rintro ⟨i, hi, ht, x, y, hx, hy, hlt⟩
  rw [hx] at hy
  exact absurd (Option.some.inj hy) (ne_of_lt hlt)

/-- `keyLt` is transitive: it is the lexicographic comparison of two lists at the first
position where they differ (`<` on the entries of that position). -/
private lemma keyLt_trans {α : Type*} [LinearOrder α] {a b d : List α}
    (hab : keyLt a b) (hbd : keyLt b d) : keyLt a d := by
  obtain ⟨i, hi, htab, x, y, hai, hbi, hxy⟩ := hab
  obtain ⟨j, hj, htbd, x', y', hbj, hdj, hx'y'⟩ := hbd
  rcases lt_trichotomy i j with hij | hij | hji
  · -- the first position where `a` and `d` differ is `i`
    have hbd_i : b.take i = d.take i := by
      have h := congrArg (fun l : List α => l.take i) htbd
      rw [List.take_take, List.take_take, Nat.min_eq_left (le_of_lt hij)] at h
      exact h
    have hbd_get : b[i]? = d[i]? := by
      have hb : (b.take j)[i]? = b[i]? := List.getElem?_take_of_lt hij
      have hd : (d.take j)[i]? = d[i]? := List.getElem?_take_of_lt hij
      have h := congrArg (fun l : List α => l[i]?) htbd
      exact hb.symm.trans (h.trans hd)
    exact ⟨i, hi, htab.trans hbd_i, x, y, hai, by rw [← hbd_get]; exact hbi, hxy⟩
  · -- the first position where `a` and `d` differ is `i = j`
    subst hij
    refine ⟨i, hi, htab.trans htbd, x, y', hai, hdj, ?_⟩
    have hyx' : y = x' := by
      rw [hbi] at hbj
      exact Option.some.inj hbj
    exact hxy.trans (hyx'.symm ▸ hx'y')
  · -- the first position where `a` and `d` differ is `j`
    have hj_a : j < a.length := lt_trans hji hi
    have hab_j : a.take j = b.take j := by
      have h := congrArg (fun l : List α => l.take j) htab
      rw [List.take_take, List.take_take, Nat.min_eq_left (le_of_lt hji)] at h
      exact h
    have hab_get : a[j]? = b[j]? := by
      have ha : (a.take i)[j]? = a[j]? := List.getElem?_take_of_lt hji
      have hb : (b.take i)[j]? = b[j]? := List.getElem?_take_of_lt hji
      have h := congrArg (fun l : List α => l[j]?) htab
      exact ha.symm.trans (h.trans hb)
    exact ⟨j, hj_a, hab_j.trans htbd, x', y', by rw [hab_get]; exact hbj, hdj, hx'y'⟩

theorem flagEnum_mem_take {vs : List (PL.E N)} {rk : PL.E N → ℕ} (hvs : vs.Nodup)
    (hrk : (vs.map rk).Pairwise (· < ·)) {l l' : List (PL.E N)}
    (hl : l ∈ Work.PL.Shell.flagEnum vs) (hl' : l' ∈ Work.PL.Shell.flagEnum vs) :
    l' ∈ (Work.PL.Shell.flagEnum vs).take ((Work.PL.Shell.flagEnum vs).idxOf l)
      ↔ Work.PL.Shell.keyLt (l'.reverse.map rk) (l.reverse.map rk) := by
  rw [List.mem_take_iff_idxOf_lt hl']
  have hsorted := flagEnum_sorted hvs hrk
  have hp : (flagEnum vs).idxOf l' < (flagEnum vs).length :=
    List.idxOf_lt_length_iff.mpr hl'
  have hq : (flagEnum vs).idxOf l < (flagEnum vs).length :=
    List.idxOf_lt_length_iff.mpr hl
  obtain ⟨_, hgetp⟩ := List.getElem?_eq_some_iff.mp (List.getElem?_idxOf hl')
  obtain ⟨_, hgetq⟩ := List.getElem?_eq_some_iff.mp (List.getElem?_idxOf hl)
  constructor
  · intro h
    have h1 := List.Pairwise.rel_getElem_of_lt hp hq hsorted h
    rwa [hgetp, hgetq] at h1
  · intro h
    by_contra hcon
    rw [not_lt] at hcon
    rcases lt_or_eq_of_le hcon with hlt | heq
    · have h1 := List.Pairwise.rel_getElem_of_lt hq hp hsorted hlt
      rw [hgetp, hgetq] at h1
      exact keyLt_irrefl _ (keyLt_trans h h1)
    · have hl'l : l' = l := (List.idxOf_inj hl').mp heq.symm
      rw [hl'l] at h
      exact keyLt_irrefl _ h

end Work.PL.Shell
