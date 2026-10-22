import Mathlib
import Submission.Work.ATOM.ZS.Topo.Defs

open CategoryTheory Limits LightProfinite OnePoint

namespace Work.ATOM.ZS.Topo

/-- `T' = {(j,a_j) : j ∈ ℕ} ∪ {∞} × S` is a closed subset of `(ℕ∪{∞}) × S` (`Work.ATOM.tSet`).
Route: its complement is the open set `⋃ j, {p | p.1 = j} ∩ {p | p.2 ≠ a_j}`: the fibre of the
first projection over a finite point `j` is clopen (`isClopen_singleton_some`), and inside it the
complement of the singleton `a_j` is open.  The points over `∞` all lie in `T'`, and over a finite
`j` exactly `a_j` does, so the displayed union is precisely the complement. -/
theorem tSet_isClosed (S : LightProfinite.{0}) [Infinite S] :
    IsClosed (Work.ATOM.tSet S) := by
  rw [← isOpen_compl_iff]
  have hcompl : (Work.ATOM.tSet S)ᶜ
      = ⋃ j : ℕ, {p : ↥(Work.ATOM.NS S) | p.1 = ((j : ℕ) : ℕ∪{∞})}
          ∩ {p : ↥(Work.ATOM.NS S) | p.2 ≠ (Work.ATOM.levelData S).a j} := by
    ext p
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq,
      Work.ATOM.mem_tSet_iff, not_or, not_exists, not_and]
    constructor
    · rintro ⟨hinf, hall⟩
      obtain ⟨j, hj⟩ := OnePoint.ne_infty_iff_exists.mp hinf
      exact ⟨j, hj.symm, hall j hj.symm⟩
    · rintro ⟨j, hj, h2⟩
      exact ⟨fun h => OnePoint.coe_ne_infty j (hj.symm.trans h), fun i hi => by
        rw [hj] at hi
        rw [OnePoint.coe_eq_coe] at hi
        exact fun hcon => h2 (hi ▸ hcon)⟩
  rw [hcompl]
  apply isOpen_iUnion
  intro j
  apply IsOpen.inter
  · exact (Work.ATOM.isClopen_singleton_some j).2.preimage continuous_fst
  · exact isOpen_compl_singleton.preimage continuous_snd

end Work.ATOM.ZS.Topo
