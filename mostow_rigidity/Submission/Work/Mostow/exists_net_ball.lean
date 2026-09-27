import Mathlib
import Submission.Work.Mostow.hlDefsAccess

namespace Work.Mostow

open Submission.Mostow

/-- A finite `r`-net of the closed hyperbolic unit ball around the base point `0`, with all net
points contained in the ball of radius `1 + r`.

This is the standard compactness fact: the closed `hdist`-ball `{v | hdist 0 v ≤ 1}` is compact
(`HypIsometryProp`), and for each point `y` of it the set `{u | hdist u y < r}` is open (continuity
of `hdist` and `hdist y y = 0`), so the family of these sets indexed by the compact ball has a
finite subcover. -/
theorem exists_net_ball (n : ℕ) (hI : Submission.Mostow.HypIsometryProp n)
    (r : ℝ) (hr : 0 < r) :
    ∃ P : Finset (Submission.Mostow.E n),
      (∀ y ∈ P, Submission.Mostow.hdist (0 : Submission.Mostow.E n) y ≤ 1 + r) ∧
      ∀ u : Submission.Mostow.E n, Submission.Mostow.hdist (0 : Submission.Mostow.E n) u ≤ 1 →
        ∃ y ∈ P, Submission.Mostow.hdist u y < r := by
  classical
  have hcont : Continuous (fun p : E n × E n => hdist p.1 p.2) := hI.2.2.2.2.1
  have hcompact : IsCompact {v : E n | hdist (0 : E n) v ≤ 1} := hI.2.2.2.2.2.1 0 1
  -- each `hdist`-ball of radius `r` is open
  have hUo : ∀ i : {v : E n // hdist (0 : E n) v ≤ 1},
      IsOpen {v : E n | hdist v i.1 < r} := fun i =>
    isOpen_Iio.preimage (hcont.comp (continuous_id.prodMk continuous_const))
  -- the compact unit ball is covered by the `hdist`-balls centred at its own points
  have hsU : {v : E n | hdist (0 : E n) v ≤ 1}
      ⊆ ⋃ (i : {v : E n // hdist (0 : E n) v ≤ 1}), {v : E n | hdist v i.1 < r} := by
    intro v hv
    refine Set.mem_iUnion.mpr ⟨⟨v, hv⟩, ?_⟩
    have h0 : hdist v v = 0 := (hI.2.2.1 v v).mpr rfl
    show hdist v v < r
    linarith
  obtain ⟨t, ht⟩ := hcompact.elim_finite_subcover
    (fun i : {v : E n // hdist (0 : E n) v ≤ 1} => {v : E n | hdist v i.1 < r}) hUo hsU
  refine ⟨t.image Subtype.val, ?_, ?_⟩
  · intro y hy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
    have hi : hdist (0 : E n) i.1 ≤ 1 := i.2
    linarith
  · intro u hu
    have hu' := ht hu
    simp only [Set.mem_iUnion] at hu'
    obtain ⟨i, hit, hiu⟩ := hu'
    exact ⟨i.1, Finset.mem_image.mpr ⟨i, hit, rfl⟩, hiu⟩

end Work.Mostow
