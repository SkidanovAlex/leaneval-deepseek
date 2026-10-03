import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.DartGraph

namespace Work.HornSC.CellBoundaryJordan

/-- If every degree of `G` is even and `(a, b)` is a dart of `G`, then `b` carries an outgoing
dart `(b, c)` with `c ≠ a` (i.e. `b` has, besides the reversal of `(a, b)`, a further incident
edge).  Otherwise the only dart leaving `b` would be `(b, a)` and `deg b = 1` would be odd. -/
theorem exists_dart_ne {α : Type*} [DecidableEq α] (G : DartGraph α) (h : ∀ a, Even (G.deg a))
    {a b : α} (hab : (a, b) ∈ G.D) : ∃ c, (b, c) ∈ G.D ∧ c ≠ a := by
  by_contra hcon
  push Not at hcon
  have hba : (b, a) ∈ G.D := G.symm _ hab
  -- the darts leaving `b`
  set S : Finset (α × α) := G.D.filter (fun e => e.1 = b) with hS
  have hbaS : (b, a) ∈ S := by simp [hS, hba]
  -- if the only dart leaving `b` were `(b, a)`, then `S` would have a single element
  have hsub : S ⊆ ({(b, a)} : Finset (α × α)) := by
    intro e he
    rw [hS, Finset.mem_filter] at he
    obtain ⟨heD, he1⟩ := he
    have heq : e = (b, e.2) := by rw [← he1]
    rw [heq] at heD
    simp only [Finset.mem_singleton]
    rw [heq]
    simp [hcon e.2 heD]
  have hle : S.card ≤ 1 := by
    have := Finset.card_le_card hsub
    simpa using this
  have hge : 1 ≤ S.card := Finset.card_pos.mpr ⟨(b, a), hbaS⟩
  have h1 : G.deg b = 1 := by
    have : S.card = G.deg b := rfl
    omega
  have hb := h b
  rw [h1] at hb
  obtain ⟨k, hk⟩ := hb
  omega

end Work.HornSC.CellBoundaryJordan
