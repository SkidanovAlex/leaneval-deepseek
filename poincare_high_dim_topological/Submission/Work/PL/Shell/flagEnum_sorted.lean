import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Shell.Basic

namespace Work.PL.Shell

variable {N : ℕ}

private lemma keyLt_cons_of_keyLt {α : Type*} [LT α] {x : α} {a b : List α}
    (h : keyLt a b) : keyLt (x :: a) (x :: b) := by
  obtain ⟨i, hi, ht, y, z, ha, hb, hlt⟩ := h
  exact ⟨i+1, by simpa using Nat.succ_lt_succ hi,
    by simp [List.take_succ_cons, ht],
    y, z, by simpa using ha, by simpa using hb, hlt⟩

private lemma keyLt_of_lt_head {α : Type*} [LT α] {x y : α} {a b : List α}
    (h : x < y) : keyLt (x :: a) (y :: b) :=
  ⟨0, by simp, by simp, x, y, by simp, by simp, h⟩

theorem flagEnum_sorted {vs : List (PL.E N)} {rk : PL.E N → ℕ} (hvs : vs.Nodup)
    (hrk : (vs.map rk).Pairwise (· < ·)) :
    (Work.PL.Shell.flagEnum vs).Pairwise
      (fun a b => Work.PL.Shell.keyLt (a.reverse.map rk) (b.reverse.map rk)) := by
  induction vs using flagEnum.induct with
  | case1 =>
      rw [flagEnum.eq_1]
      exact List.Pairwise.cons (by simp) List.Pairwise.nil
  | case2 vs hne ih =>
      rw [flagEnum.eq_2 vs hne]
      rw [List.pairwise_flatMap]
      have hrk' : vs.Pairwise (fun a b => rk a < rk b) := List.pairwise_map.mp hrk
      refine ⟨?_, ?_⟩
      · intro m hm
        rw [List.pairwise_map]
        refine List.Pairwise.imp (fun {a b} hab => ?_)
          (ih m hm (hvs.erase m) (List.pairwise_map.mpr (List.Pairwise.erase m hrk')))
        simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
          List.map_cons]
        exact keyLt_cons_of_keyLt hab
      · refine List.Pairwise.imp (fun {a b} hab => ?_) hrk'
        intro x hx y hy
        obtain ⟨ta, _, rfl⟩ := List.mem_map.mp hx
        obtain ⟨tb, _, rfl⟩ := List.mem_map.mp hy
        simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
          List.map_cons]
        exact keyLt_of_lt_head hab

end Work.PL.Shell
