import Mathlib
import Submission.Work.Mostow.KMCellDefs

namespace Work.Mostow

theorem cellCoverAlmostEq (k : ℕ) (hI : Submission.Mostow.HypIsometryProp k)
    (t : Finset (Submission.Mostow.E k)) (e : ℝ)
    (hnet : ∀ v : Submission.Mostow.E k, Submission.Mostow.hdist (0 : Submission.Mostow.E k) v ≤ 1 →
      ∃ j ∈ t, Submission.Mostow.hdist v j ≤ e)
    (i g h : LeanEval.Geometry.MostowRigidity.PO k 1) (r : ℝ)
    (hg : ∀ j ∈ t, Submission.Mostow.hdist (i • j) (g • j) < r)
    (hh : ∀ j ∈ t, Submission.Mostow.hdist (i • j) (h • j) < r) :
    ∀ u : Submission.Mostow.E k, Submission.Mostow.hdist (0 : Submission.Mostow.E k) u ≤ 1 →
      Submission.Mostow.hdist (g • u) (h • u) < 2 * e + 2 * r := by
  -- unpack the geometry toolkit
  have hsym : ∀ u v : Submission.Mostow.E k, Submission.Mostow.hdist u v = Submission.Mostow.hdist v u :=
    fun u v => hI.2.1 u v
  have htri : ∀ u v w : Submission.Mostow.E k,
      Submission.Mostow.hdist u w ≤ Submission.Mostow.hdist u v + Submission.Mostow.hdist v w :=
    fun u v w => hI.2.2.2.1 u v w
  have hiso : ∀ (γ : LeanEval.Geometry.MostowRigidity.PO k 1) (u v : Submission.Mostow.E k),
      Submission.Mostow.hdist (γ • u) (γ • v) = Submission.Mostow.hdist u v :=
    fun γ u v => hI.2.2.2.2.2.2.1 γ u v
  intro u hu
  obtain ⟨j, hjt, hju⟩ := hnet u hu
  -- distance from g•u to g•j is hdist u j ≤ e
  have hA : Submission.Mostow.hdist (g • u) (g • j) ≤ e := by
    rw [hiso g u j]; exact hju
  -- distance from h•j to h•u is hdist u j ≤ e
  have hC : Submission.Mostow.hdist (h • j) (h • u) ≤ e := by
    rw [hiso h j u, hsym j u]; exact hju
  -- middle term: hdist (g•j) (h•j) ≤ r + r
  have hgi : Submission.Mostow.hdist (g • j) (i • j) < r := by
    rw [hsym (g • j) (i • j)]; exact hg j hjt
  have hih : Submission.Mostow.hdist (i • j) (h • j) < r := hh j hjt
  have hB : Submission.Mostow.hdist (g • j) (h • j) < r + r := by
    have := htri (g • j) (i • j) (h • j); linarith
  -- chain
  have t1 : Submission.Mostow.hdist (g • u) (h • u) ≤
      Submission.Mostow.hdist (g • u) (g • j) + Submission.Mostow.hdist (g • j) (h • u) :=
    htri (g • u) (g • j) (h • u)
  have t2 : Submission.Mostow.hdist (g • j) (h • u) ≤
      Submission.Mostow.hdist (g • j) (h • j) + Submission.Mostow.hdist (h • j) (h • u) :=
    htri (g • j) (h • j) (h • u)
  linarith

end Work.Mostow
