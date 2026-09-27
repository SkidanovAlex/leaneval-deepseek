import Mathlib
import Submission.Work.Noncompact.CompressionTube.LaneData

/-!
# Consecutive separation from an arbitrary trace set

`Work.Noncompact.CompressionTube.inter_image_subset_singleton_of_ball_trace` separates two
consecutive pieces of the corridor routing from a *chart ball* `B = c.symm '' ball (c σ) ρ`: the
arriving piece's visits to the corridor lie in `B` (`hPC`), and the two pieces' visits to `B` are
their germ windows (`hProot`, `hQroot`).

Reading the proof shows that the ball is used **only** through those three hypotheses — no property
of `B` itself is used anywhere.  This file records that: the same statement with `B` an arbitrary
subset.  The gain is that the trace can be taken to be the *neck*
`closure (h.C i ∩ h.C (i+1)) ∩ h.C i` (which is always available: the piece lies in `h.C i`, so its
visits to the next corridor are in the neck), instead of a chart ball — which removes the
`ball ⊇ neck` versus `ball ⊆ corridor` obstruction of `Routing/NOTES_posEngine_DESIGN.md` §4/§7.
-/

namespace Work.Routing

open Set Topology Function
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M]

/-- **Two consecutive pieces with a common straight germ meet only at the junction**, with the
trace condition phrased for an arbitrary set `B`. -/
theorem inter_subset_singleton_of_trace {P Q : ℝ → M} {C B : Set M}
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {σ : M} {w : EuclideanSpace ℝ (Fin n)} {e e' : ℝ}
    (hw : w ≠ 0) (he : 0 < e) (he' : 0 < e')
    (hP1 : P 1 = σ) (hQ0 : Q 0 = σ) (hsrc : σ ∈ c.source)
    (hPgerm : ∀ t : ℝ, 1 - e ≤ t → t ≤ 1 → P t = c.symm (c σ + (t - 1) • w))
    (hQgerm : ∀ t : ℝ, 0 ≤ t → t ≤ e' → Q t = c.symm (c σ + t • w))
    (hPtgt : ∀ t : ℝ, 1 - e ≤ t → t ≤ 1 → c σ + (t - 1) • w ∈ c.target)
    (hQtgt : ∀ t : ℝ, 0 ≤ t → t ≤ e' → c σ + t • w ∈ c.target)
    (hQC : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → Q t ∈ C)
    (hPC : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → P t ∈ C → P t ∈ B)
    (hProot : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → P t ∈ B → t ∈ Set.Icc (1 - e) 1)
    (hQroot : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → Q t ∈ B → t ∈ Set.Icc (0:ℝ) e') :
    P '' Set.Icc (0:ℝ) 1 ∩ Q '' Set.Icc (0:ℝ) 1 ⊆ {σ} := by
  rintro x ⟨⟨s, hs, rfl⟩, ⟨t, ht, hst⟩⟩
  have hxC : P s ∈ C := by rw [← hst]; exact hQC t ht
  have hsB : P s ∈ B := hPC s hs hxC
  have hsk : s ∈ Set.Icc (1 - e) 1 := hProot s hs hsB
  have htB : Q t ∈ B := by rw [hst]; exact hsB
  have htk : t ∈ Set.Icc (0:ℝ) e' := hQroot t ht htB
  have hg1 : P s = c.symm (c σ + (s - 1) • w) := hPgerm s hsk.1 hs.2
  have hg2 : Q t = c.symm (c σ + t • w) := hQgerm t htk.1 htk.2
  have harg1 : c σ + (s - 1) • w ∈ c.target := hPtgt s hsk.1 hs.2
  have harg2 : c σ + t • w ∈ c.target := hQtgt t htk.1 htk.2
  have heq : c σ + (s - 1) • w = c σ + t • w := by
    have hinj : Set.InjOn c.symm c.target := by
      have h := c.symm.injOn
      rwa [OpenPartialHomeomorph.symm_source] at h
    refine hinj harg1 harg2 ?_
    rw [← hg1, ← hg2]
    exact hst.symm
  have hzero : (s - 1 - t) • w = 0 := by
    have h1 : (s - 1) • w = t • w := add_left_cancel heq
    rw [sub_smul, h1, sub_self]
  have hst' : s - 1 - t = 0 := by
    rcases smul_eq_zero.mp hzero with h | h
    · exact h
    · exact absurd h hw
  have hs1 : s = 1 := by linarith [hst', hs.2, ht.1]
  rw [Set.mem_singleton_iff, hs1, hP1]

end Work.Routing
