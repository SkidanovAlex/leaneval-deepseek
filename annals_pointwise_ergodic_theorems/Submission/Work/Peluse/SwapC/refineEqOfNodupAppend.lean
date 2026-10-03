import Mathlib
import Submission.Work.Peluse.SwapC.cprocNodup

namespace Work.Peluse.SwapC

/-- `refine` acts as the identity on a leaf list that does not contain the leaf to be split:
each leaf is left as the singleton list of itself. -/
private theorem refine_flatMap_eq_self {s : ℕ} (l : CLeaf s) :
    ∀ (Λ : List (CLeaf s)), l ∉ Λ →
      List.flatMap (fun l' => if he : l' = l then
        (if hh : l'.dep < s then l'.children hh else [l']) else [l']) Λ = Λ
  | [], _ => by simp
  | a :: t, h => by
    rw [List.flatMap_cons]
    have ha : ¬ (a = l) := fun h' => h (by rw [h']; exact List.mem_cons_self ..)
    rw [dif_neg ha]
    simp only [List.singleton_append]
    rw [refine_flatMap_eq_self l t (fun hmem => h (List.mem_cons_of_mem a hmem))]

theorem refineEqOfNodupAppend {s : ℕ} {P Q : List (Work.Peluse.SwapC.CLeaf s)}
    {l : Work.Peluse.SwapC.CLeaf s} (hn : (P ++ l :: Q).Nodup) (hl : l.dep < s) :
    Work.Peluse.SwapC.refine (P ++ l :: Q) l = P ++ l.children hl ++ Q := by
  -- `l` occurs exactly once in `P ++ l :: Q`, so it is absent from `P` and from `Q`
  obtain ⟨hPnod, hlQnod, hdisj⟩ := List.nodup_append.mp hn
  obtain ⟨hlQ, hQnod⟩ := List.nodup_cons.mp hlQnod
  have hlP : l ∉ P := fun hmem => (hdisj l hmem l (List.mem_cons_self ..)) rfl
  -- the `flatMap` of `refine` reduces to the children of `l` at `l`, and to the identity on `P`
  -- and on `Q`
  have hfl : (if he : l = l then if hh : l.dep < s then l.children hh else [l] else [l])
      = l.children hl := by simp [hl]
  rw [refine, List.flatMap_append, List.flatMap_cons, hfl,
    refine_flatMap_eq_self l P hlP, refine_flatMap_eq_self l Q hlQ,
    List.append_assoc]

end Work.Peluse.SwapC
