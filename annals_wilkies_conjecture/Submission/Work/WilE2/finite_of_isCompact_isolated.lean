import Mathlib

namespace Work.WilE2

theorem finite_of_isCompact_isolated {S : Set ℝ}
    (hcomp : IsCompact S) (hiso : ∀ x ∈ S, ∃ ε > 0, ∀ y, dist y x < ε → y ∈ S → y = x) :
    S.Finite := by
  classical
  -- Pick, for every point of `S`, a radius whose ball contains no other point of `S`.
  choose r hr using fun x : S => hiso x.1 x.2
  -- These balls form an open cover of `S`.
  have hcover : S ⊆ ⋃ x : S, Metric.ball x.1 (r x) := by
    intro y hy
    exact Set.mem_iUnion.2 ⟨⟨y, hy⟩, by simp [Metric.mem_ball, (hr ⟨y, hy⟩).1]⟩
  -- Compactness yields a finite subcover; each member of it meets `S` in one point.
  obtain ⟨t, ht⟩ := hcomp.elim_finite_subcover (fun x : S => Metric.ball x.1 (r x))
      (fun _ => Metric.isOpen_ball) hcover
  have hsub : S ⊆ Subtype.val '' (↑t : Set S) := by
    intro y hy
    rcases Set.mem_iUnion₂.1 (ht hy) with ⟨x, hxt, hxy⟩
    have hxy' : y = x.1 := (hr x).2 y hxy hy
    rw [hxy']
    exact ⟨x, hxt, rfl⟩
  exact (t.finite_toSet.image Subtype.val).subset hsub

end Work.WilE2
