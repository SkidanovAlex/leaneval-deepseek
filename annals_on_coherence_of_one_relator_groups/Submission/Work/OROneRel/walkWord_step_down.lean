import Mathlib
import Submission.Work.OROneRel.twoLetterTlDefs
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.GaugeDefs
import Submission.Work.OROneRel.wordOfDefs
import Submission.Work.OROneRel.MagnusGenDefs
import Submission.Work.OROneRel.decor_tlU_tlW_at
import Submission.Work.OROneRel.wordOf_pow_flatten
import Submission.Work.OROneRel.lsig_wordOf_eq_zero
import Submission.Work.OROneRel.letters_closure_iff
import Submission.Work.OROneRel.walkMid_a_mem
import Submission.Work.OROneRel.walkMid_b_mem
import Submission.Work.OROneRel.mk_decor_flatten_replicate

/-!
# The level-`(a-1)` walk word of the two-letter relator, and the step down

The window `[a, p q]` of the level graph of the two-letter relator `tlU p q = x ^ p * y ^ q` with
the weight `tlW p q` (`x ↦ q`, `y ↦ -p`).  The walk of `tlU p q` started at the level `a - 1` (one
level *below* the window) leaves the window exactly twice: its first step (`x` at level `a-1`, an
edge ending at level `a - 1 + q`), and its last step (`y` at level `a - 1 + p`, an edge ending at
level `a - 1`).  Everything between them stays inside the window:

  `mk (decor (tlW p q) (a-1) (wordOf (tlU p q)))
      = of ((x, a-1)) * mk (walkMid p q (a-1)) * of ((y, a-1+p))`

with every letter of `walkMid p q (a-1)` a symbol whose *edge* lies in `winE (tlW p q) a (p q)`.

Since the walk of `tlU p q` returns to its starting level (`lsig (tlW p q) (wordOf (tlU p q)) = 0`),
the walk of `tlU p q ^ l` is the `l`-fold repetition of the walk of `tlU p q` at the same levels, so
the walk word at level `a - 1` is the `l`-th power of the one-round walk word — which is the content
of the main theorem `Work.OROneRel.walkWord_step_down`.
-/

namespace Work.OROneRel

/-- **The middle of the decorated walk of `tlU p q`** at starting level `N`: the `x`-letters read at
the levels `N + q, N + 2q, …, N + (p-1)q` (all but the first) followed by the `y`-letters read at the
levels `N + p q, N + p q - p, …, N + 2p` (all but the last). -/
noncomputable def walkMid (p q : ℕ) (N : ℤ) : List ((Fin 2 × ℤ) × Bool) :=
  (List.ofFn fun j : Fin (p - 1) => (((0 : Fin 2), N + ((j : ℤ) + 1) * (q : ℤ)), true)) ++
  (List.ofFn fun k : Fin (q - 1) =>
    (((1 : Fin 2), N + (p : ℤ) * (q : ℤ) - (k : ℤ) * (p : ℤ)), true))

/-- **The weight `tlW p q` kills the reduced word of the two-letter relator**: reading `x ^ p` adds
`q` at each of the `p` copies of `x` and reading `y ^ q` subtracts `p` at each of the `q` copies of
`y`, and `p q - q p = 0`.  This is what makes the decorated walk of `tlU p q` *closed*, i.e. the
`l`-fold copy of the walk sits at the same levels in every round. -/
theorem lsig_wordOf_tlU (p q : ℕ) : lsig (tlW p q) (wordOf (tlU p q)) = 0 := by
  rw [wordOf_tlU, decor_lsig_append, lsig_replicate_true, lsig_replicate_true, tlW_zero, tlW_one]
  ring

/-! ## The decoration of the walk of `tlU p q` at level `N` splits off its first and last letter -/

/-- **The one-copy decomposition of the walk word.**  In the decorated walk of `tlU p q` started at
level `N`, the first symbol is the `x`-letter read at level `N` and the last symbol is the
`y`-letter read at level `N + p` (stepping back down to the level `N`); the product of the
remaining symbols is `mk (walkMid p q N)`. -/
theorem walkMid_decompose {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (N : ℤ) :
    FreeGroup.mk (decor (tlW p q) N (wordOf (tlU p q))) =
      FreeGroup.of ((0 : Fin 2), N) * FreeGroup.mk (walkMid p q N) *
        FreeGroup.of ((1 : Fin 2), N + (p : ℤ)) := by
  cases p with
  | zero => omega
  | succ n =>
    cases q with
    | zero => omega
    | succ m =>
      rw [decor_tlU_tlW_at]
      rw [← FreeGroup.mul_mk]
      have hA : FreeGroup.mk (List.ofFn (fun j : Fin (n + 1) =>
            (((0 : Fin 2), N + (j : ℤ) * ((m + 1 : ℕ) : ℤ)), true)))
          = FreeGroup.of ((0 : Fin 2), N) *
            FreeGroup.mk (List.ofFn (fun j : Fin n =>
              (((0 : Fin 2), N + ((j : ℤ) + 1) * ((m + 1 : ℕ) : ℤ)), true))) := by
        have hl : List.ofFn (fun j : Fin (n + 1) =>
              (((0 : Fin 2), N + (j : ℤ) * ((m + 1 : ℕ) : ℤ)), true))
            = [(((0 : Fin 2), N), true)] ++
              List.ofFn (fun j : Fin n =>
                (((0 : Fin 2), N + ((j : ℤ) + 1) * ((m + 1 : ℕ) : ℤ)), true)) := by
          rw [List.ofFn_succ, List.singleton_append]
          congr 1
          all_goals simp
        rw [hl, FreeGroup.of, FreeGroup.mul_mk]
      have hB : FreeGroup.mk (List.ofFn (fun k : Fin (m + 1) =>
            (((1 : Fin 2), N + ((n + 1 : ℕ) : ℤ) * ((m + 1 : ℕ) : ℤ) - (k : ℤ) * ((n + 1 : ℕ) : ℤ)), true)))
          = FreeGroup.mk (List.ofFn (fun k : Fin m =>
              (((1 : Fin 2), N + ((n + 1 : ℕ) : ℤ) * ((m + 1 : ℕ) : ℤ) - (k : ℤ) * ((n + 1 : ℕ) : ℤ)), true))) *
            FreeGroup.of ((1 : Fin 2), N + ((n + 1 : ℕ) : ℤ)) := by
        have hl : List.ofFn (fun k : Fin (m + 1) =>
              (((1 : Fin 2), N + ((n + 1 : ℕ) : ℤ) * ((m + 1 : ℕ) : ℤ) - (k : ℤ) * ((n + 1 : ℕ) : ℤ)), true))
            = List.ofFn (fun k : Fin m =>
                (((1 : Fin 2), N + ((n + 1 : ℕ) : ℤ) * ((m + 1 : ℕ) : ℤ) - (k : ℤ) * ((n + 1 : ℕ) : ℤ)), true)) ++
              [(((1 : Fin 2), N + ((n + 1 : ℕ) : ℤ)), true)] := by
          rw [List.ofFn_succ', List.concat_eq_append]
          congr 1
          all_goals (simp [Fin.val_last]; ring)
        rw [hl, FreeGroup.of, FreeGroup.mul_mk]
      rw [hA, hB]
      unfold walkMid
      rw [← FreeGroup.mul_mk]
      simp only [mul_assoc]
      rfl

/-- **Every letter of the middle lies in the window** `winE (tlW p q) a (p q)` when the walk is
started at the level `a - 1`: the `x`-letters read at the levels `a - 1 + q, …, a - 1 + (p-1) q`
(their edges end at the levels `a - 1 + 2q, …, a - 1 + p q ≤ p q`), and the `y`-letters read at the
levels `a - 1 + p q, …, a - 1 + 2p` (their edges end at the levels `a - 1 + p(q-1), …, a - 1 + p`),
all of which lie in `[a, p q]` because `a ≤ 1`. -/
theorem walkMid_mem {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (a : ℤ) (ha : a ≤ 1) :
    ∀ e ∈ walkMid p q (a - 1), e.1 ∈ winE (tlW p q) a ((p : ℤ) * (q : ℤ)) := by
  intro e he
  simp only [walkMid, List.mem_append] at he
  rcases he with he | he
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp he
    exact walkMid_a_mem hp hq a ha (j := (j : ℕ)) (by omega)
  · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp he
    exact walkMid_b_mem hp hq a ha (k := (k : ℕ)) (by omega)

/-! ## The step down -/

theorem walkWord_step_down {p q l : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (a : ℤ) (ha : a ≤ 1) :
    ∃ C : FreeGroup (Fin 2 × ℤ),
      C ∈ Subgroup.closure (FreeGroup.of '' Work.OROneRel.winE (Work.OROneRel.tlW p q) a ((p:ℤ)*(q:ℤ))) ∧
      FreeGroup.mk (Work.OROneRel.decor (Work.OROneRel.tlW p q) (a - 1)
          (Work.OROneRel.wordOf (Work.OROneRel.tlU p q ^ l))) =
        (FreeGroup.of ((0 : Fin 2), a - 1) * C *
          FreeGroup.of ((1 : Fin 2), a + (p : ℤ) - 1)) ^ l := by
  refine ⟨FreeGroup.mk (walkMid p q (a - 1)), ?_, ?_⟩
  · exact mk_mem_closure fun x b hb => walkMid_mem hp hq a ha (x, b) hb
  · rw [wordOf_pow_flatten (tlU p q) l (tlU_isCyclicallyReduced p q hp hq),
      mk_decor_flatten_replicate (tlW p q) (a - 1) (wordOf (tlU p q)) l
        (lsig_wordOf_tlU p q),
      walkMid_decompose hp hq (a - 1)]
    have hlev : (((1 : Fin 2), (a - 1) + (p : ℤ)) : Fin 2 × ℤ) =
        ((1 : Fin 2), a + (p : ℤ) - 1) := by
      congr 1
      ring
    rw [hlev]

end Work.OROneRel
