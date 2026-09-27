import Mathlib

namespace Work.Drive.Whitney

set_option linter.style.haveILetI false

/-- **Replacing a linearly independent prefix by another one with the same span.**

If `u` and `u'` are linearly independent families of the same length `r` spanning the same
submodule, then appending a common family `w` preserves linear independence in either direction.

The proof is the standard splitting of `Fin.append u w` along the identification
`Fin (r + k) ≃ Fin r ⊕ Fin k` together with `linearIndependent_sum`: a family is independent iff
its two halves are independent and the spans of the halves are disjoint.  The only point that
requires care is that `M` is assumed to be an `AddCommMonoid` (not an `AddCommGroup`), so the
`AddCommGroup` instance used by `linearIndependent_sum` is produced on the spot by
`Module.addCommMonoidToAddCommGroup`. -/
theorem appendSpanCongr {M : Type*} [AddCommMonoid M] [Module ℝ M] {r k : ℕ}
    {u u' : Fin r → M} (hu : LinearIndependent ℝ u) (hu' : LinearIndependent ℝ u')
    (hspan : Submodule.span ℝ (Set.range u) = Submodule.span ℝ (Set.range u')) (w : Fin k → M) :
    LinearIndependent ℝ (Fin.append u w) ↔ LinearIndependent ℝ (Fin.append u' w) := by
  letI : AddCommGroup M := Module.addCommMonoidToAddCommGroup ℝ
  -- The criterion: `append v w` is independent iff `v`, `w` are independent with disjoint spans.
  have key : ∀ v : Fin r → M,
      LinearIndependent ℝ (Fin.append v w) ↔
        LinearIndependent ℝ v ∧ LinearIndependent ℝ w ∧
          Disjoint (Submodule.span ℝ (Set.range v)) (Submodule.span ℝ (Set.range w)) := by
    intro v
    -- Reindex `Fin (r + k)` by `Fin r ⊕ Fin k`, where the criterion is `linearIndependent_sum`.
    have hiff : LinearIndependent ℝ (Sum.elim v w) ↔ LinearIndependent ℝ (Fin.append v w) :=
      linearIndependent_equiv' (finSumFinEquiv (m := r) (n := k))
        (Fin.append_comp_sumElim (xs := v) (ys := w))
    rw [← hiff]
    exact linearIndependent_sum
  rw [key u, key u', hspan]
  exact ⟨fun h => ⟨hu', h.2.1, h.2.2⟩, fun h => ⟨hu, h.2.1, h.2.2⟩⟩

end Work.Drive.Whitney
