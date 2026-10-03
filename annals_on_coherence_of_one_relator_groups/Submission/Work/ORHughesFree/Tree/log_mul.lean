import Mathlib
import Submission.Work.ORHughesFree.Tree.Log

namespace Work.ORHughesFree.Tree

open Work.ORHughesFree

/-- `log z = some b` exactly when `b` is the maximum of the family of `z`: it is a member of
`fam z` and dominates every member. -/
theorem log_eq_some_iff {z b : Tree} :
    log z = some b ↔ b ∈ fam z ∧ ∀ c ∈ fam z, Tree.le c b := by
  constructor
  · intro h
    exact (log_spec z).2.1 b h
  · rintro ⟨hmem, hmax⟩
    have hfamne : fam z ≠ 0 := fun h => by
      rw [h] at hmem
      exact absurd hmem (by simp)
    have hne : z ≠ 0 := fun hz => hfamne (Tree.fam_eq_zero_iff.mpr hz)
    obtain ⟨c, hc⟩ := (log_spec z).2.2 hne
    obtain ⟨hc_mem, hc_max⟩ := (log_spec z).2.1 c hc
    have hcb : Tree.le c b := hmax c hc_mem
    have hbc : Tree.le b c := hc_max b hmem
    have : c = b := Tree.le_antisymm hcb hbc
    rw [this] at hc
    exact hc

theorem log_mul {x y a b : Work.ORHughesFree.Tree}
    (hx : Work.ORHughesFree.Tree.log x = some a) (hy : Work.ORHughesFree.Tree.log y = some b) :
    Work.ORHughesFree.Tree.log (x * y) = some (a + b) := by
  obtain ⟨hax, hmaxx⟩ := (log_spec x).2.1 a hx
  obtain ⟨hby, hmaxy⟩ := (log_spec y).2.1 b hy
  rw [log_eq_some_iff]
  constructor
  · rw [Tree.fam_mul]
    exact mem_mulMs.mpr ⟨a, hax, b, hby, rfl⟩
  · intro c hc
    rw [Tree.fam_mul] at hc
    obtain ⟨a', ha', b', hb', rfl⟩ := mem_mulMs.mp hc
    exact Tree.le_add (hmaxx a' ha') (hmaxy b' hb')

end Work.ORHughesFree.Tree
