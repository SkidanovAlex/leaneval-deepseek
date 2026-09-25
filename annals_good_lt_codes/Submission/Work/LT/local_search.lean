import Mathlib
import Submission.Work.LT.lr_sound_defs
import Submission.Work.LT.local_search_defs
import Submission.Work.LT.changedSet_updateAt_le
import Submission.Work.LT.exists_of_no_descent

/-! `local_search`: existence of a locally optimal assignment reachable by single-vertex moves
within the changed-set budget.  The proof runs the descent principle `Work.LT.exists_of_no_descent`
on the measure `dispCount` with the invariant

  `P x` := `x` is a valid assignment, `#(changedSet x W0) ≤ dispCount W0 - dispCount x`, and
           `dispCount x ≤ dispCount W0`,

which holds at the starting assignment `W` by hypothesis and is preserved by a single-vertex move
decreasing `dispCount` (a move changes at most one vertex, hence `changedSet` grows by at most one,
while `dispCount` drops by at least one). -/

namespace Work.LT

open Classical

lemma local_search {G : Type} [Group G] [Fintype G] {Δ : ℕ} (A B : Fin Δ → G)
    (CA CB : Submodule (ZMod 2) (Fin Δ → ZMod 2))
    (W0 : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2))
    (hW0 : ∀ α β g, W0 α β g ∈ Work.LT.tensorCode CA CB) :
    ∀ W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2),
      (∀ α β g, W α β g ∈ Work.LT.tensorCode CA CB) →
      (Work.LT.changedSet W W0).card ≤ Work.LT.dispCount A B W0 - Work.LT.dispCount A B W →
      Work.LT.dispCount A B W ≤ Work.LT.dispCount A B W0 →
      ∃ W' : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2),
        (∀ α β g, W' α β g ∈ Work.LT.tensorCode CA CB) ∧
        Work.LT.IsLocalOpt A B CA CB W' ∧
        (Work.LT.changedSet W' W0).card ≤ Work.LT.dispCount A B W0 - Work.LT.dispCount A B W' ∧
        Work.LT.dispCount A B W' ≤ Work.LT.dispCount A B W0 := by
  intro W hW hcard hle
  -- The invariant `P` and the descent step producing a strictly improving single-vertex move.
  have hstep : ∀ x, ((∀ α β g, x α β g ∈ tensorCode CA CB) ∧
        (changedSet x W0).card ≤ dispCount A B W0 - dispCount A B x ∧
        dispCount A B x ≤ dispCount A B W0) →
      ¬ IsLocalOpt A B CA CB x → ∃ y, ((∀ α β g, y α β g ∈ tensorCode CA CB) ∧
        (changedSet y W0).card ≤ dispCount A B W0 - dispCount A B y ∧
        dispCount A B y ≤ dispCount A B W0) ∧ dispCount A B y < dispCount A B x := by
    intro x hx hxno
    obtain ⟨hxval, hxcard, hxle⟩ := hx
    -- Unpack the failure of local optimality into an explicit improving single-vertex move.
    simp only [IsLocalOpt, not_forall, not_le] at hxno
    obtain ⟨α, β, g, w, hw, hdec⟩ := hxno
    have hdec' : dispCount A B (updateAt x α β g w) < dispCount A B x := hdec
    exact ⟨updateAt x α β g w,
      ⟨updateAt_mem CA CB hxval hw α β g,
        by have := changedSet_updateAt_le x W0 α β g w; omega,
        le_trans (le_of_lt hdec') hxle⟩,
      hdec'⟩
  obtain ⟨x', hx'P, hx'Q⟩ :=
    exists_of_no_descent (dispCount A B)
      (fun x => (∀ α β g, x α β g ∈ tensorCode CA CB) ∧
        (changedSet x W0).card ≤ dispCount A B W0 - dispCount A B x ∧
        dispCount A B x ≤ dispCount A B W0)
      (IsLocalOpt A B CA CB) W ⟨hW, hcard, hle⟩ hstep
  exact ⟨x', hx'P.1, hx'Q, hx'P.2.1, hx'P.2.2⟩

end Work.LT
