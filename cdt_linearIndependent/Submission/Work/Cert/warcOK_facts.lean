import Mathlib
import Submission.Work.Cert.WindDefs

/-!
# Facts extracted from the winding-arc checker `warcOK`

`warcOK a nx ny` is a conjunction of four `Bool` checks (see `WindDefs`):

* the first leaf of `a` starts at the arc's grid point `(a.Ex, a.Ey)`,
* `wchainOK nx ny a.leaves` — consecutive leaves share endpoints, the last one ends at `(nx, ny)`,
* `gridStep a.Ex a.Ey nx ny` — the grid point advances by the 4096-th root of unity `W`,
* `a.leaves.all (windLeafOK a.lab ·)` — every leaf carries a valid half-plane certificate.

This file unpacks that conjunction. The only non-trivial point is that `wchainOK` (on
`Leaf × ℤ`, using the witness component `l.2`) and `chainOK` (on plain `Leaf`, the definition
used by `arcOK`) have *literarily the same* recursion, so mapping a `wchainOK` chain with
`Prod.fst` gives a `chainOK` chain.
-/

namespace Work.Cert

/-- `wchainOK` is `chainOK` transported along `(·.1)`; equivalently, the `bU` witness of a
winding leaf plays no rôle in the chain check. -/
private theorem wchainOK_map_fst : ∀ (L : List (Leaf × ℤ)) (nx ny : Int),
    wchainOK nx ny L = true → chainOK nx ny (L.map (fun l : Leaf × ℤ => l.1)) = true := by
  intro L
  induction L with
  | nil => intro nx ny h; simp [wchainOK] at h
  | cons l t ih =>
    intro nx ny h
    cases t with
    | nil =>
      simp only [wchainOK, List.map_cons, List.map_nil, chainOK, Bool.and_eq_true,
        decide_eq_true_eq] at h ⊢
      exact h
    | cons m rest =>
      have h' := h
      rw [wchainOK] at h'
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
      obtain ⟨⟨h1, h2⟩, h3⟩ := h'
      simp only [List.map_cons, chainOK, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨h1, h2⟩, ih nx ny h3⟩

theorem warcOK_facts (a : WArc) (nx ny : Int) (h : warcOK a nx ny = true) :
    (∃ (l : Leaf × ℤ) (rest : List (Leaf × ℤ)), a.leaves = l :: rest ∧ l.1.Ax = a.Ex ∧ l.1.Ay = a.Ey) ∧
    wchainOK nx ny a.leaves = true ∧ chainOK nx ny (a.leaves.map (fun l : Leaf × ℤ => l.1)) = true ∧
    gridStep a.Ex a.Ey nx ny = true ∧
    (∀ l ∈ a.leaves, windLeafOK a.lab l.1 l.2 = true) := by
  have hd := h
  simp only [warcOK, Bool.and_eq_true] at hd
  obtain ⟨⟨⟨hfirst, hchain⟩, hgrid⟩, hall⟩ := hd
  refine ⟨?_, hchain, wchainOK_map_fst a.leaves nx ny hchain, hgrid, ?_⟩
  · cases hl : a.leaves with
    | nil => rw [hl] at hfirst; simp at hfirst
    | cons l rest =>
      rw [hl] at hfirst
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hfirst
      exact ⟨l, rest, rfl, hfirst.1, hfirst.2⟩
  · intro l hl
    exact List.all_eq_true.mp hall l hl

end Work.Cert
