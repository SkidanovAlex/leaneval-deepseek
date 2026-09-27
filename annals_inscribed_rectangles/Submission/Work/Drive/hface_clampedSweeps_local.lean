import Mathlib
import Submission.Work.Drive.bottomBdryMeet_clampedSweep_count
import Submission.Work.Drive.clampedSweepLevel
import Submission.Work.Drive.endLevelObstruction
import Submission.Work.Drive.hface_clampedSweeps

/-!
# The face condition for the clamped sweeps, with the cutoff only controlled on `[0,1]`

`Work.Drive.hface_clampedSweeps` (`Submission/Work/Drive/hface_clampedSweeps.lean`) derives the parity
engine's face condition at a boundary triple point of the three clamped radial sweeps from the collision
data, but under the hypothesis `hψ01 : ∀ t : ℝ, ψ t ∈ Set.Icc 0 1` on the cutoff `ψ`.

In the construction the cutoff is only a cutoff: it is `0` and `1` at the endpoints and `[0,1]`-valued
**on `[0,1]`** (see e.g. `Work.Drive.levelOf_clampedSweep_le_local`, whose hypotheses are exactly the
local ones).  This file repeats the derivation of `Work.Drive.hface_clampedSweeps` with that weaker
hypothesis `hψ01 : ∀ t ∈ Set.Icc (0:ℝ) 1, ψ t ∈ Set.Icc (0:ℝ) 1` (and without `hcont`/`hanti`, which
the derivation never uses).

The only step of the original proof that used the global hypothesis is
`Work.Drive.le_trunc_of_bottomTriple`, through `Work.Drive.le_levelOf_clampedSweep`.  The local form of
the level bound is already available as `Work.Drive.le_levelOf_clampedSweep_local`
(`Submission/Work/Drive/clampedSweepLevel.lean`, where the same observation is recorded); below we
localise the truncation-level comparison (`le_trunc_of_bottomTriple_local`) so that the value of `ψ` is
taken into account only at the (box-)parameters actually occurring.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-- **Only a block with a maximal truncation level can be the one on its bottom face at a triple
point** (local cutoffs).  Local form of `Work.Drive.le_trunc_of_bottomTriple`; the extra hypothesis
`hbox` records that the parameters do lie in the cube, which is all that the local cutoff data needs. -/
theorem le_trunc_of_bottomTriple_local (c : Fin 3 → ℝ) (hc : ∀ k, 0 < c k) (ψ : ℝ → ℝ)
    (hψ0 : ψ 0 = 1) (hψ01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), c k ≤ levelOf (P k y))
    (x : Fin 3 → EuclideanSpace ℝ (Fin 3))
    (hbox : ∀ k : Fin 3, x k 2 ∈ Set.Icc (0 : ℝ) 1)
    (h01 : clampedSweep (c 0) ψ (P 0) (x 0) = clampedSweep (c 1) ψ (P 1) (x 1))
    (h02 : clampedSweep (c 0) ψ (P 0) (x 0) = clampedSweep (c 2) ψ (P 2) (x 2))
    {k j : Fin 3} (hk : x k 2 = 0) :
    c j ≤ c k := by
  rw [← level_eq_of_bottomTriple c hc ψ hψ0 P x h01 h02 hk j]
  exact le_levelOf_clampedSweep_local (hc j) hψ01 (P j) (x j) (hbox j)
    (hlev j (mk2 (x j 0) (x j 1)))

open Manifold in
open scoped Manifold ContDiff in
theorem hface_clampedSweeps_local
    (c : Fin 3 → ℝ) (hcpos : ∀ k : Fin 3, 0 < c k) (hc1 : c 1 < c 0) (hc2 : c 2 < c 0)
    (ψ : ℝ → ℝ) (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hψ01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), c 0 < Work.Drive.levelOf (P k y))
    (q : Projectivization ℝ (Work.Drive.Eucl 3))
    (hy : ∀ k, ∃! y : EuclideanSpace ℝ (Fin 2), y ∈ Submission.Drive.unitBox 1 ∧
      (Work.Drive.cappingSpaceHomeoProj (P k y)).2 = q)
    (huniq : ∀ q' : Projectivization ℝ (Work.Drive.Eucl 3),
      (∀ k, ∃ y ∈ Submission.Drive.unitBox 1, (Work.Drive.cappingSpaceHomeoProj (P k y)).2 = q') → q' = q)
    (hyint : ∀ (k : Fin 3) (i : Fin 2), (hy k).choose i ∈ Set.Ioo (0 : ℝ) 1)
    (hrne : ∀ j k : Fin 3, j ≠ k →
      Work.Drive.levelOf (P j ((hy j).choose)) ≠ Work.Drive.levelOf (P k ((hy k).choose))) :
    ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
      (∀ k, x k ∈ Submission.Drive.unitBox 2) →
      Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0) = Work.Drive.clampedSweep (c 1) ψ (P 1) (x 1) →
      Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0) = Work.Drive.clampedSweep (c 2) ψ (P 2) (x 2) →
      (∃ k, x k ∈ Submission.Drive.unitBoxBdry 2) →
      ∃ k : Fin 3, (x k 2 = 0 ∨ x k 2 = 1) ∧
        (∀ j : Fin 3, j ≠ 2 → x k j ∈ Set.Ioo (0 : ℝ) 1) ∧
        (∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3, x k' j ∈ Set.Ioo (0 : ℝ) 1) := by
  intro x hbox h01 h02 hbdry
  -- ## Step 0: the classes of the three plane points all agree, and are the collision class `q`
  have hy_uniq : ∀ (k : Fin 3) (z : EuclideanSpace ℝ (Fin 2)),
      z ∈ Submission.Drive.unitBox 1 → (cappingSpaceHomeoProj (P k z)).2 = q →
      z = (hy k).choose := by
    intro k z hz hq
    exact (hy k).choose_spec.2 z ⟨hz, hq⟩
  have hmk2 : ∀ k : Fin 3, mk2 (x k 0) (x k 1) ∈ Submission.Drive.unitBox 1 := by
    intro k i
    fin_cases i
    · simpa using hbox k 0
    · simpa using hbox k 1
  have hD0 : ∀ k : Fin 3,
      clampedSweep (c k) ψ (P k) (x k) = clampedSweep (c 0) ψ (P 0) (x 0) := by
    intro k
    fin_cases k
    · rfl
    · exact h01.symm
    · exact h02.symm
  have hcls : ∀ k : Fin 3,
      (cappingSpaceHomeoProj (P k (mk2 (x k 0) (x k 1)))).2
        = (cappingSpaceHomeoProj (P 0 (mk2 (x 0 0) (x 0 1)))).2 := by
    intro k
    rw [← cls_clampedSweep_of_hface (c k) ψ (P k) (x k), hD0 k,
      cls_clampedSweep_of_hface (c 0) ψ (P 0) (x 0)]
  have hq0 : (cappingSpaceHomeoProj (P 0 (mk2 (x 0 0) (x 0 1)))).2 = q :=
    huniq _ (fun k => ⟨mk2 (x k 0) (x k 1), hmk2 k, hcls k⟩)
  have hclassq : ∀ k : Fin 3, (cappingSpaceHomeoProj (P k (mk2 (x k 0) (x k 1)))).2 = q :=
    fun k => (hcls k).trans hq0
  have hXy : ∀ k : Fin 3, mk2 (x k 0) (x k 1) = (hy k).choose :=
    fun k => hy_uniq k _ (hmk2 k) (hclassq k)
  have hx0 : ∀ k : Fin 3, x k 0 = (hy k).choose 0 := fun k => by
    have h := congrArg (fun u : EuclideanSpace ℝ (Fin 2) => u 0) (hXy k)
    simpa using h
  have hx1 : ∀ k : Fin 3, x k 1 = (hy k).choose 1 := fun k => by
    have h := congrArg (fun u : EuclideanSpace ℝ (Fin 2) => u 1) (hXy k)
    simpa using h
  -- ## Step 1: every *class* coordinate of a triple point is strictly interior
  have hint : ∀ (k : Fin 3) (i : Fin 3), i ≠ 2 → x k i ∈ Set.Ioo (0 : ℝ) 1 := by
    intro k i hi
    fin_cases i
    · show x k 0 ∈ Set.Ioo (0 : ℝ) 1
      rw [hx0 k]
      exact hyint k 0
    · show x k 1 ∈ Set.Ioo (0 : ℝ) 1
      rw [hx1 k]
      exact hyint k 1
    · exact absurd rfl hi
  -- ## Step 2: a boundary parameter is on the *radial* face: `x k 2 ∈ {0,1}`
  have hface2 : ∃ k : Fin 3, x k 2 = 0 ∨ x k 2 = 1 := by
    obtain ⟨kb, hkb⟩ := hbdry
    obtain ⟨-, ib, hib⟩ := hkb
    have hib2 : ib = 2 := by
      by_contra hne
      have hmem := hint kb ib hne
      rcases hib with h | h
      · rw [h] at hmem; exact lt_irrefl 0 hmem.1
      · rw [h] at hmem; exact lt_irrefl 1 hmem.2
    subst hib2
    exact ⟨kb, hib⟩
  -- ## Step 3: the level bookkeeping
  have hcle : ∀ k : Fin 3, c k ≤ c 0 := by
    intro k
    fin_cases k
    · exact le_rfl
    · exact le_of_lt hc1
    · exact le_of_lt hc2
  have hlevP : ∀ (k : Fin 3) (yy : EuclideanSpace ℝ (Fin 2)), c k ≤ levelOf (P k yy) :=
    fun k yy => le_trans (hcle k) (le_of_lt (hlev k yy))
  have hbox2 : ∀ k : Fin 3, x k 2 ∈ Set.Icc (0 : ℝ) 1 := fun k => hbox k 2
  have hzero : ∀ k : Fin 3, x k 2 = 0 → k = 0 := by
    intro k hk
    have hmax : c 0 ≤ c k :=
      le_trunc_of_bottomTriple_local c hcpos ψ hψ0 hψ01 P hlevP x hbox2 h01 h02 hk
    have hceq : c k = c 0 := le_antisymm (hcle k) hmax
    fin_cases k
    · rfl
    · exact absurd hceq (ne_of_lt hc1)
    · exact absurd hceq (ne_of_lt hc2)
  by_cases hbot : ∃ k : Fin 3, x k 2 = 0
  · -- ## Case A: some block is on its bottom face; then it is block `0`, with `x 0 2 = 0`
    obtain ⟨k0, hk0⟩ := hbot
    have hk0eq : k0 = 0 := hzero k0 hk0
    subst hk0eq
    have hL : ∀ k : Fin 3, levelOf (clampedSweep (c k) ψ (P k) (x k)) = c 0 := by
      intro k
      have hL0 : levelOf (clampedSweep (c 0) ψ (P 0) (x 0)) = c 0 := by
        rw [clampedSweep_face_zero (c 0) (hcpos 0) ψ (P 0) hψ0 (x 0) hk0, levelOf_shadow]
      rw [hD0 k, hL0]
    refine ⟨0, Or.inl hk0, (fun j hj => hint 0 j hj), ?_⟩
    intro k' hk' j
    fin_cases j
    · exact hint k' 0 (by decide)
    · exact hint k' 1 (by decide)
    · refine hface_mem_Ioo (hbox k' 2) (fun h => hk' (hzero k' h)) ?_
      intro h1
      have hval : levelOf (P k' ((hy k').choose)) = c 0 := by
        have h1' : clampedSweep (c k') ψ (P k') (x k') = P k' ((hy k').choose) := by
          rw [clampedSweep_face_one (c k') ψ (P k') hψ1 (x k') h1, hXy k']
        rw [← h1', hL k']
      exact absurd hval (ne_of_gt (hlev k' ((hy k').choose)))
  · -- ## Case B: no block is on its bottom face; then some block is on its top face
    push_neg at hbot
    obtain ⟨k1, hk1⟩ := hface2
    rcases hk1 with hk1 | hk1
    · exact absurd hk1 (hbot k1)
    · refine ⟨k1, Or.inr hk1, (fun j hj => hint k1 j hj), ?_⟩
      intro k' hk' j
      fin_cases j
      · exact hint k' 0 (by decide)
      · exact hint k' 1 (by decide)
      · refine hface_mem_Ioo (hbox k' 2) (hbot k') ?_
        intro h2
        have hL1 : levelOf (clampedSweep (c k1) ψ (P k1) (x k1))
            = levelOf (P k1 ((hy k1).choose)) := by
          rw [clampedSweep_face_one (c k1) ψ (P k1) hψ1 (x k1) hk1, hXy k1]
        have hLk' : levelOf (clampedSweep (c k') ψ (P k') (x k'))
            = levelOf (P k' ((hy k').choose)) := by
          rw [clampedSweep_face_one (c k') ψ (P k') hψ1 (x k') h2, hXy k']
        exact hrne k' k1 hk' (by rw [← hLk', hD0 k', ← hD0 k1, hL1])

end

end Work.Drive
