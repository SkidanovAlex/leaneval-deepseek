import Mathlib
import Submission.Work.OROneRel.walkDefs
import Submission.Work.OROneRel.decor_tlU_tlW_at

namespace Work.OROneRel

theorem walk_mk_decompose {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (N : ℤ) :
    FreeGroup.mk (Work.OROneRel.decor (Work.OROneRel.tlW p q) N
        (Work.OROneRel.wordOf (Work.OROneRel.tlU p q))) =
      Work.OROneRel.walkA p q N *
        FreeGroup.of ((0 : Fin 2), N + ((p : ℤ) - 1) * (q : ℤ)) *
        FreeGroup.of ((1 : Fin 2), N + (p : ℤ) * (q : ℤ)) * Work.OROneRel.walkB p q N := by
  cases p with
  | zero => omega
  | succ n =>
    cases q with
    | zero => omega
    | succ m =>
      rw [decor_tlU_tlW_at]
      rw [← FreeGroup.mul_mk]
      -- the `a`-block: all but the last `a`-symbol form `walkA`, the last one is the level
      -- `N + (p - 1) q` generator
      have hA : FreeGroup.mk (List.ofFn (fun j : Fin (n + 1) =>
            (((0 : Fin 2), N + (j : ℤ) * ((m + 1 : ℕ) : ℤ)), true)))
          = walkA (n + 1) (m + 1) N *
            FreeGroup.of ((0 : Fin 2), N + (n : ℤ) * ((m + 1 : ℕ) : ℤ)) := by
        have hl : List.ofFn (fun j : Fin (n + 1) =>
              (((0 : Fin 2), N + (j : ℤ) * ((m + 1 : ℕ) : ℤ)), true))
            = List.ofFn (fun j : Fin n =>
                (((0 : Fin 2), N + (j : ℤ) * ((m + 1 : ℕ) : ℤ)), true))
              ++ [(((0 : Fin 2), N + (n : ℤ) * ((m + 1 : ℕ) : ℤ)), true)] := by
          rw [List.ofFn_succ', List.concat_eq_append]
          congr 1
        rw [hl, walkA, FreeGroup.of, ← FreeGroup.mul_mk]
        rfl
      -- the `b`-block: the first `b`-symbol is the level `N + p q` generator, the remaining ones
      -- form `walkB`
      have hB : FreeGroup.mk (List.ofFn (fun k : Fin (m + 1) =>
            (((1 : Fin 2), N + ((n + 1 : ℕ) : ℤ) * ((m + 1 : ℕ) : ℤ) - (k : ℤ) * ((n + 1 : ℕ) : ℤ)), true)))
          = FreeGroup.of ((1 : Fin 2), N + ((n + 1 : ℕ) : ℤ) * ((m + 1 : ℕ) : ℤ)) *
            walkB (n + 1) (m + 1) N := by
        have hl : List.ofFn (fun k : Fin (m + 1) =>
              (((1 : Fin 2), N + ((n + 1 : ℕ) : ℤ) * ((m + 1 : ℕ) : ℤ) - (k : ℤ) * ((n + 1 : ℕ) : ℤ)), true))
            = [(((1 : Fin 2), N + ((n + 1 : ℕ) : ℤ) * ((m + 1 : ℕ) : ℤ)), true)]
              ++ List.ofFn (fun k : Fin m =>
                  (((1 : Fin 2), N + ((n + 1 : ℕ) : ℤ) * ((m + 1 : ℕ) : ℤ) - ((k : ℤ) + 1) * ((n + 1 : ℕ) : ℤ)), true)) := by
          rw [List.ofFn_succ, ← List.singleton_append]
          congr 1
          simp
        rw [hl, walkB, FreeGroup.of, FreeGroup.mul_mk]
        rfl
      have hcast : ((↑(n + 1) : ℤ) - 1) = (n : ℤ) := by push_cast; ring
      rw [hcast]
      rw [hA, hB]
      simp only [mul_assoc]

end Work.OROneRel
