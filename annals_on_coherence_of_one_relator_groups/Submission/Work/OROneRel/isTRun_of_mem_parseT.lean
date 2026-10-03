import Mathlib
import Submission.Work.OROneRel.npsubstDefs

namespace Work.OROneRel

/-- A reduced word all of whose letters have first coordinate `t` is a run of `t`-letters. -/
theorem isTRun_of_isReduced {β : Type*} {t : β} {X : List (β × Bool)}
    (hred : FreeGroup.IsReduced X) (hfst : ∀ c ∈ X, c.1 = t) : IsTRun t X := by
  induction X with
  | nil => exact IsTRun.nil t
  | cons c rest ih =>
    have hc : c.1 = t := hfst c (List.mem_cons_self)
    have hred_rest : FreeGroup.IsReduced rest := by
      have h : List.IsChain (fun a b : β × Bool => a.1 = b.1 → a.2 = b.2) (c :: rest) := hred
      exact h.tail
    have hfst_rest : ∀ e ∈ rest, e.1 = t := fun e he => hfst e (List.mem_cons_of_mem c he)
    rcases rest with _ | ⟨d, rest'⟩
    · refine Or.inr ⟨1, c.2, ?_⟩
      rw [List.replicate_one]
      congr 1
      exact Prod.ext hc rfl
    · rcases ih hred_rest hfst_rest with hnil | ⟨n, b, hb⟩
      · simp at hnil
      have hd : d.1 = t := hfst_rest d (List.mem_cons_self)
      have hcd : c.2 = d.2 := (FreeGroup.isReduced_cons_cons.mp hred).1 (by rw [hc, hd])
      have hd_eq : d = (t, b) :=
        List.eq_of_mem_replicate (by rw [← hb]; exact List.mem_cons_self)
      have hcb : c = (t, b) := Prod.ext hc (hcd.trans (by rw [hd_eq]))
      refine Or.inr ⟨n + 1, b, ?_⟩
      rw [hb, hcb, List.replicate_succ]

theorem isTRun_of_mem_parseT {β : Type*} [DecidableEq β] {t : β} {L : List (β × Bool)}
    (hL : FreeGroup.IsReduced L) :
    ∀ q ∈ Work.OROneRel.parseT t L, Work.OROneRel.IsTRun t q.2 := by
  suffices key : ∀ (n : ℕ) (M : List (β × Bool)), M.length ≤ n → FreeGroup.IsReduced M →
      ∀ q ∈ parseT t M, IsTRun t q.2 by
    exact key L.length L le_rfl hL
  intro n
  induction n with
  | zero =>
    intro M hlen _ q hq
    have hM : M = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    subst hM
    simp at hq
  | succ k ih =>
    intro M hlen hred q hq
    rcases M with _ | ⟨c, rest⟩
    · simp at hq
    · have hlen_rest : rest.length ≤ k := by
        simp only [List.length_cons] at hlen
        omega
      have hred_rest : FreeGroup.IsReduced rest := by
        have h : List.IsChain (fun a b : β × Bool => a.1 = b.1 → a.2 = b.2) (c :: rest) := hred
        exact h.tail
      by_cases hc : c.1 = t
      · rw [parseT_cons_of_eq hc] at hq
        exact ih rest hlen_rest hred_rest q hq
      · rw [parseT_cons_of_ne hc] at hq
        rw [List.mem_cons] at hq
        rcases hq with hq | hq
        · subst hq
          refine isTRun_of_isReduced ?_ ?_
          · have h : List.IsChain (fun a b : β × Bool => a.1 = b.1 → a.2 = b.2) rest := hred_rest
            exact h.prefix (List.takeWhile_prefix (l := rest) (isT t))
          · exact startsNonT_takeWhile_all t rest
        · refine ih (rest.dropWhile (isT t)) ?_ ?_ q hq
          · exact le_trans (List.length_dropWhile_le _ _) hlen_rest
          · have h : List.IsChain (fun a b : β × Bool => a.1 = b.1 → a.2 = b.2) rest := hred_rest
            exact h.suffix (List.dropWhile_suffix (l := rest) (isT t))

end Work.OROneRel
