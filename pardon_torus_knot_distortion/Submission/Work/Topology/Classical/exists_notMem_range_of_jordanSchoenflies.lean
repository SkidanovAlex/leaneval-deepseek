import Mathlib
import Submission.Work.Topology.Classical.Defs

/-!
# A point of `S²` missing finitely many pairwise disjoint Jordan curves

Given the Jordan–Schoenflies input `JordanSchoenfliesSphere` (which supplies, for each curve of a
finite pairwise disjoint family of Jordan curves on the round sphere, a pair of complementary
embedded discs and a *rank* witnessing that these discs are nested), a finite family of pairwise
disjoint Jordan curves on the round sphere cannot cover the sphere: some point is missed by all of
them.

The point is obtained from a curve of *minimal* rank.  If `i` has minimal rank and `z` is an
interior point of the disc `e i` of `i`, then `e i z` can lie on no curve `c j`: if it lay on `c j`
then the nesting clause of `JordanSchoenfliesSphere` would give `rank j < rank i`, contradicting
minimality.  Since the open disc of `i` is nonempty (it contains `e i 0`), this produces the
required point.
-/

namespace Work.Topology.Classical

open LeanEval.KnotTheory.PardonDistortion

theorem exists_notMem_range_of_jordanSchoenflies
    (h : Work.Topology.Classical.JordanSchoenfliesSphere)
    {ι : Type} [Fintype ι] {c : ι → ℝ → LeanEval.KnotTheory.PardonDistortion.R3}
    (hc : ∀ i : ι, Work.Topology.Classical.IsJordanCurveRound (c i))
    (hd : Pairwise fun i j : ι => Disjoint (Set.range (c i)) (Set.range (c j))) :
    ∃ p : LeanEval.KnotTheory.PardonDistortion.R3,
      p ∈ Work.Topology.Classical.RoundSphere ∧ ∀ i : ι, p ∉ Set.range (c i) := by
  classical
  by_cases hne : Nonempty ι
  · obtain ⟨i₀⟩ := hne
    obtain ⟨e, e', rank, he_inj, he'_inj, he_bd, he'_bd, he_mem, he'_mem, he_open,
      he'_open, he_cov, he_int, hrank⟩ := h ι c hc hd
    -- a curve of minimal rank
    obtain ⟨i₁, -, hmin⟩ :=
      Finset.exists_min_image Finset.univ rank ⟨i₀, Finset.mem_univ i₀⟩
    -- the centre of the disc of `i₁` is an interior point of that disc
    let z₀ : Work.InnermostDisk.Disc := ⟨0, by simp⟩
    refine ⟨e i₁ z₀, he_mem i₁ z₀, fun j hj => ?_⟩
    -- if it lay on the curve `j`, nesting would force `rank j < rank i₁`
    have hlt : rank j < rank i₁ := hrank i₁ j ⟨z₀, by simp [z₀], hj⟩
    have hle : rank i₁ ≤ rank j := hmin j (Finset.mem_univ j)
    omega
  · -- no curves at all: any point of the sphere will do
    exact ⟨EuclideanSpace.single 0 (1 : ℝ), by simp [RoundSphere], fun i _ => hne ⟨i⟩⟩

end Work.Topology.Classical
