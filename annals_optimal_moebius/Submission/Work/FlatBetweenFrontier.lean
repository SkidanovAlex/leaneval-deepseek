import Submission.Work.RegionBetween
import Submission.Work.FrontierSeparation
import Submission.Work.FlatBetween

open OptimalMoebius Topology Filter
open scoped BigOperators Matrix Topology Metric

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-!
# Brick (A): frontier of the between-region inside the open strip

For pointwise-ordered chords (`hlt`), the frontier of
`betweenChord α₁β₁ α₂β₂` within the open strip is exactly the union of
the two bounding chords:

    frontier (betweenChord α₁ β₁ α₂ β₂) ∩ stripInterior
      = stripChord α₁ β₁ ∪ stripChord α₂ β₂

(⊇) an interior chord point `x` is not in the open between-region (its
height equals the boundary) and lies in its closure (add/subtract a small
vertical `t•e₁`).
(⊆) a frontier strip point is in the closure, so it cannot lie strictly
below the lower chord or strictly above the upper chord (continuity of
`sideH₁` would give a whole neighbourhood outside the between-region,
contradicting closure); since it is not in the between-region, it lies on
one of the two chords.

Build: `lake build Submission.Work.FlatBetweenFrontier` rc=0, zero sorry.
-/

noncomputable section
namespace Submission.PaperBand

/-- `‖(0,1)‖ = 1` in the plane. -/
lemma e1_norm : ‖(!₂[(0 : ℝ), 1] : ℝ²)‖ = 1 := by
  have hsq : ‖(!₂[(0 : ℝ), 1] : ℝ²)‖ ^ 2 = 1 ^ 2 := by
    rw [norm_sq_coord_sum]
    simp
  have h := (sq_eq_sq_iff_abs_eq_abs (‖(!₂[(0 : ℝ), 1] : ℝ²)‖) 1).1 hsq
  rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)] at h
  exact h

/-- Coordinates of `x + t•(0,1)`. -/
lemma add_smul_e1_coord {x : ℝ²} (t : ℝ) : (x + t • !₂[(0 : ℝ), 1]) 0 = x 0 := by
  simp [smul_eq_mul]

/-- Second coordinate of `x + t•(0,1)`. -/
lemma add_smul_e1_coord1 {x : ℝ²} (t : ℝ) : (x + t • !₂[(0 : ℝ), 1]) 1 = x 1 + t := by
  simp [smul_eq_mul]

/-- Coordinates of `x - t•(0,1)`. -/
lemma sub_smul_e1_coord0 {x : ℝ²} (t : ℝ) : (x - t • !₂[(0 : ℝ), 1]) 0 = x 0 := by
  simp [smul_eq_mul]

/-- Second coordinate of `x - t•(0,1)`. -/
lemma sub_smul_e1_coord1 {x : ℝ²} (t : ℝ) : (x - t • !₂[(0 : ℝ), 1]) 1 = x 1 - t := by
  simp [smul_eq_mul]

/-- Norm of `t•(0,1)`. -/
lemma norm_smul_e1 {t : ℝ} : ‖t • (!₂[(0 : ℝ), 1] : ℝ²)‖ = |t| := by
  rw [norm_smul, e1_norm, mul_one, Real.norm_eq_abs]

/-- The between-region of two chords is open. -/
lemma isOpen_betweenChord {α₁ β₁ α₂ β₂ : ℝ} : IsOpen (betweenChord α₁ β₁ α₂ β₂) := by
  have h1 : IsOpen {z : ℝ² | sideH₁ α₁ β₁ (z 0) < z 1} := by
    have hf : Continuous (fun z : ℝ² => sideH₁ α₁ β₁ (z 0)) := by
      dsimp [sideH₁]
      fun_prop
    have hg : Continuous (fun z : ℝ² => z 1) := by fun_prop
    exact isOpen_lt hf hg
  have h2 : IsOpen {z : ℝ² | z 1 < sideH₁ α₂ β₂ (z 0)} := by
    have hf : Continuous (fun z : ℝ² => sideH₁ α₂ β₂ (z 0)) := by
      dsimp [sideH₁]
      fun_prop
    have hg : Continuous (fun z : ℝ² => z 1) := by fun_prop
    exact isOpen_lt hg hf
  have hset : betweenChord α₁ β₁ α₂ β₂ =
      {z : ℝ² | sideH₁ α₁ β₁ (z 0) < z 1} ∩ {z : ℝ² | z 1 < sideH₁ α₂ β₂ (z 0)} ∩ stripInterior := by
    ext z
    rw [mem_betweenChord]
    simp [stripInterior]
    tauto
  rw [hset]
  exact h1.inter h2 |>.inter stripInterior_isOpen

/-- A point of the lower chord is not strictly above it. -/
lemma chord1_not_in_between {α₁ β₁ α₂ β₂ : ℝ} {x : ℝ²} (hx : x ∈ stripChord α₁ β₁) :
    x ∉ betweenChord α₁ β₁ α₂ β₂ := by
  rw [mem_stripChord] at hx
  intro h
  rw [mem_betweenChord] at h
  have hx1 : x 1 = sideH₁ α₁ β₁ (x 0) := hx.2
  rcases h with ⟨_, hgt, _⟩
  linarith

/-- A point of the upper chord is not strictly below it. -/
lemma chord2_not_in_between {α₁ β₁ α₂ β₂ : ℝ} {x : ℝ²} (hx : x ∈ stripChord α₂ β₂) :
    x ∉ betweenChord α₁ β₁ α₂ β₂ := by
  rw [mem_stripChord] at hx
  intro h
  rw [mem_betweenChord] at h
  have hx1 : x 1 = sideH₁ α₂ β₂ (x 0) := hx.2
  rcases h with ⟨_, _, hlt⟩
  linarith

/-- Interior points of the LOWER chord lie in the closure of the
between-region (for pointwise-ordered chords): push up by a small
vertical amount. -/
lemma chord1_mem_closure_between {α₁ β₁ α₂ β₂ : ℝ}
    (hlt : ∀ u : ℝ, u ∈ Set.Ioo 0 1 → sideH₁ α₁ β₁ u < sideH₁ α₂ β₂ u)
    {x : ℝ²} (hx : x ∈ stripChord α₁ β₁) :
    x ∈ closure (betweenChord α₁ β₁ α₂ β₂) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hx0 : x 0 ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [mem_stripChord] at hx
    rw [stripInterior] at hx
    exact hx.1
  have hx0gt : 0 < x 0 := (Set.mem_Ioo.mp hx0).1
  have hx0lt : x 0 < 1 := (Set.mem_Ioo.mp hx0).2
  have hx1 : x 1 = sideH₁ α₁ β₁ (x 0) := (mem_stripChord.mp hx).2
  have hgap : 0 < sideH₁ α₂ β₂ (x 0) - sideH₁ α₁ β₁ (x 0) := by linarith [hlt (x 0) hx0]
  let t : ℝ := min (ε / 2) ((sideH₁ α₂ β₂ (x 0) - sideH₁ α₁ β₁ (x 0)) / 2)
  have ht0 : 0 < t := lt_min (by linarith) (by linarith)
  have htε : t < ε := by
    have hle : t ≤ ε / 2 := min_le_left _ _
    linarith
  have htl : t < sideH₁ α₂ β₂ (x 0) - sideH₁ α₁ β₁ (x 0) := by
    have hle : t ≤ (sideH₁ α₂ β₂ (x 0) - sideH₁ α₁ β₁ (x 0)) / 2 := min_le_right _ _
    linarith
  let z : ℝ² := x + t • !₂[(0 : ℝ), 1]
  have hc0 : z 0 = x 0 := by
    dsimp [z]
    exact add_smul_e1_coord t
  have hc1 : z 1 = x 1 + t := by
    dsimp [z]
    exact add_smul_e1_coord1 t
  refine ⟨z, ?_, ?_⟩
  · rw [mem_betweenChord]
    constructor
    · rw [stripInterior]
      change z 0 ∈ Set.Ioo (0 : ℝ) 1
      rw [hc0]
      exact hx0
    constructor
    · rw [hc1, hx1, hc0]
      linarith
    · rw [hc1, hx1, hc0]
      linarith [hlt (x 0) hx0]
  · rw [dist_comm, dist_eq_norm]
    rw [show z - x = t • !₂[(0 : ℝ), 1] by
      dsimp [z]
      simp [sub_eq_add_neg, add_assoc]]
    rw [norm_smul_e1]
    rw [abs_of_nonneg (le_of_lt ht0)]
    exact htε

/-- Interior points of the UPPER chord lie in the closure of the
between-region: push down by a small vertical amount. -/
lemma chord2_mem_closure_between {α₁ β₁ α₂ β₂ : ℝ}
    (hlt : ∀ u : ℝ, u ∈ Set.Ioo 0 1 → sideH₁ α₁ β₁ u < sideH₁ α₂ β₂ u)
    {x : ℝ²} (hx : x ∈ stripChord α₂ β₂) :
    x ∈ closure (betweenChord α₁ β₁ α₂ β₂) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hx0 : x 0 ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [mem_stripChord] at hx
    rw [stripInterior] at hx
    exact hx.1
  have hx0gt : 0 < x 0 := (Set.mem_Ioo.mp hx0).1
  have hx0lt : x 0 < 1 := (Set.mem_Ioo.mp hx0).2
  have hx1 : x 1 = sideH₁ α₂ β₂ (x 0) := (mem_stripChord.mp hx).2
  have hgap : 0 < sideH₁ α₂ β₂ (x 0) - sideH₁ α₁ β₁ (x 0) := by linarith [hlt (x 0) hx0]
  let t : ℝ := min (ε / 2) ((sideH₁ α₂ β₂ (x 0) - sideH₁ α₁ β₁ (x 0)) / 2)
  have ht0 : 0 < t := lt_min (by linarith) (by linarith)
  have htε : t < ε := by
    have hle : t ≤ ε / 2 := min_le_left _ _
    linarith
  have htl : t < sideH₁ α₂ β₂ (x 0) - sideH₁ α₁ β₁ (x 0) := by
    have hle : t ≤ (sideH₁ α₂ β₂ (x 0) - sideH₁ α₁ β₁ (x 0)) / 2 := min_le_right _ _
    linarith
  let z : ℝ² := x - t • !₂[(0 : ℝ), 1]
  have hc0 : z 0 = x 0 := by
    dsimp [z]
    exact sub_smul_e1_coord0 t
  have hc1 : z 1 = x 1 - t := by
    dsimp [z]
    exact sub_smul_e1_coord1 t
  refine ⟨z, ?_, ?_⟩
  · rw [mem_betweenChord]
    constructor
    · rw [stripInterior]
      change z 0 ∈ Set.Ioo (0 : ℝ) 1
      rw [hc0]
      exact hx0
    constructor
    · rw [hc1, hx1, hc0]
      linarith [hlt (x 0) hx0]
    · rw [hc1, hx1, hc0]
      linarith
  · rw [dist_eq_norm]
    rw [show x - z = t • !₂[(0 : ℝ), 1] by
      dsimp [z]
      simp [sub_eq_add_neg, add_assoc]]
    rw [norm_smul_e1]
    rw [abs_of_nonneg (le_of_lt ht0)]
    exact htε

/-- Interior points of either bounding chord are frontier points of the
between-region. -/
lemma chord_mem_frontier_between {α₁ β₁ α₂ β₂ : ℝ}
    (hlt : ∀ u : ℝ, u ∈ Set.Ioo 0 1 → sideH₁ α₁ β₁ u < sideH₁ α₂ β₂ u)
    {x : ℝ²} :
    x ∈ stripChord α₁ β₁ ∪ stripChord α₂ β₂ →
      x ∈ frontier (betweenChord α₁ β₁ α₂ β₂) := by
  intro hx
  rw [frontier_eq_closure_inter_closure]
  rcases hx with hx1 | hx2
  · constructor
    · exact chord1_mem_closure_between hlt hx1
    · have hxnot : x ∉ betweenChord α₁ β₁ α₂ β₂ := chord1_not_in_between hx1
      exact subset_closure (s := (betweenChord α₁ β₁ α₂ β₂)ᶜ) (by simpa using hxnot)
  · constructor
    · exact chord2_mem_closure_between hlt hx2
    · have hxnot : x ∉ betweenChord α₁ β₁ α₂ β₂ := chord2_not_in_between hx2
      exact subset_closure (s := (betweenChord α₁ β₁ α₂ β₂)ᶜ) (by simpa using hxnot)

/-- Converse: a frontier point of the between-region inside the open
strip lies on one of the two bounding chords. -/
lemma frontier_between_subset_chords {α₁ β₁ α₂ β₂ : ℝ}
    (hlt : ∀ u : ℝ, u ∈ Set.Ioo 0 1 → sideH₁ α₁ β₁ u < sideH₁ α₂ β₂ u)
    {x : ℝ²} (hx : x ∈ frontier (betweenChord α₁ β₁ α₂ β₂) ∩ stripInterior) :
    x ∈ stripChord α₁ β₁ ∪ stripChord α₂ β₂ := by
  rcases hx with ⟨hxF, hxS⟩
  have hx0 : x 0 ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [stripInterior] at hxS
    exact hxS
  have hx0gt : 0 < x 0 := (Set.mem_Ioo.mp hx0).1
  have hx0lt : x 0 < 1 := (Set.mem_Ioo.mp hx0).2
  -- x is in the closure of betweenChord, hence not strictly below chord1:
  have hxcl : x ∈ closure (betweenChord α₁ β₁ α₂ β₂) := frontier_subset_closure hxF
  have hge1 : sideH₁ α₁ β₁ (x 0) ≤ x 1 := by
    by_contra hnot
    have hlt' : x 1 < sideH₁ α₁ β₁ (x 0) := lt_of_not_ge hnot
    -- x strictly below chord1; φ(z) = sideH₁α₁β₁(z0) − z1 > 0 at x, so positive on a
    -- neighbourhood of x, contradicting between-points (φ < 0) arbitrarily close.
    have hcont : Continuous (fun z : ℝ² => sideH₁ α₁ β₁ (z 0) - z 1) := by
      dsimp [sideH₁]
      fun_prop
    have hpos : 0 < sideH₁ α₁ β₁ (x 0) - x 1 := by linarith
    rcases (Metric.continuousAt_iff.mp (hcont.continuousAt)) (sideH₁ α₁ β₁ (x 0) - x 1) hpos with
      ⟨δ, hδ0, hδ⟩
    rw [Metric.mem_closure_iff] at hxcl
    rcases hxcl δ hδ0 with ⟨y, hyB, hyd⟩
    have hyd' : dist y x < δ := by simpa [dist_comm] using hyd
    have hφy : 0 < sideH₁ α₁ β₁ (y 0) - y 1 := by
      have hd : dist (sideH₁ α₁ β₁ (y 0) - y 1) (sideH₁ α₁ β₁ (x 0) - x 1) <
          sideH₁ α₁ β₁ (x 0) - x 1 := hδ (x := y) hyd'
      have hdabs : |(sideH₁ α₁ β₁ (y 0) - y 1) + x 1 - sideH₁ α₁ β₁ (x 0)| <
          sideH₁ α₁ β₁ (x 0) - x 1 := by
        simpa [Real.dist_eq] using hd
      have hle : -(sideH₁ α₁ β₁ (x 0) - x 1) < (sideH₁ α₁ β₁ (y 0) - y 1) + x 1 -
          sideH₁ α₁ β₁ (x 0) := neg_lt_of_abs_lt hdabs
      linarith
    rw [mem_betweenChord] at hyB
    linarith [hyB.2.1, hφy]
  have hle2 : x 1 ≤ sideH₁ α₂ β₂ (x 0) := by
    by_contra hnot
    have hgt' : sideH₁ α₂ β₂ (x 0) < x 1 := lt_of_not_ge hnot
    -- x strictly above chord2; ψ(z) = z1 − sideH₁α₂β₂(z0) > 0 at x, so positive on a
    -- neighbourhood of x, contradicting between-points (ψ < 0) arbitrarily close.
    have hcont : Continuous (fun z : ℝ² => z 1 - sideH₁ α₂ β₂ (z 0)) := by
      dsimp [sideH₁]
      fun_prop
    have hpos : 0 < x 1 - sideH₁ α₂ β₂ (x 0) := by linarith
    rcases (Metric.continuousAt_iff.mp (hcont.continuousAt)) (x 1 - sideH₁ α₂ β₂ (x 0)) hpos with
      ⟨δ, hδ0, hδ⟩
    rw [Metric.mem_closure_iff] at hxcl
    rcases hxcl δ hδ0 with ⟨y, hyB, hyd⟩
    have hyd' : dist y x < δ := by simpa [dist_comm] using hyd
    have hψy : 0 < y 1 - sideH₁ α₂ β₂ (y 0) := by
      have hd : dist (y 1 - sideH₁ α₂ β₂ (y 0)) (x 1 - sideH₁ α₂ β₂ (x 0)) <
          x 1 - sideH₁ α₂ β₂ (x 0) := hδ (x := y) hyd'
      have hdabs : |y 1 - sideH₁ α₂ β₂ (y 0) + sideH₁ α₂ β₂ (x 0) - x 1| <
          x 1 - sideH₁ α₂ β₂ (x 0) := by
        simpa [Real.dist_eq] using hd
      have hle : -(x 1 - sideH₁ α₂ β₂ (x 0)) < y 1 - sideH₁ α₂ β₂ (y 0) +
          sideH₁ α₂ β₂ (x 0) - x 1 := neg_lt_of_abs_lt hdabs
      linarith
    rw [mem_betweenChord] at hyB
    linarith [hyB.2.2, hψy]
  -- x is not in the open between-region (frontier of an open set):
  have hxnot : x ∉ betweenChord α₁ β₁ α₂ β₂ := by
    intro hxIn
    have hxint : x ∈ interior (betweenChord α₁ β₁ α₂ β₂) := by
      rw [isOpen_betweenChord.interior_eq]
      exact hxIn
    rw [frontier] at hxF
    exact hxF.2 hxint
  -- combine: not-both-strict, plus the two closure bounds, force x on a chord
  have hnots : ¬(sideH₁ α₁ β₁ (x 0) < x 1 ∧ x 1 < sideH₁ α₂ β₂ (x 0)) := by
    intro h
    exact hxnot (by
      rw [mem_betweenChord]
      exact ⟨hxS, h.1, h.2⟩)
  by_cases hc1 : sideH₁ α₁ β₁ (x 0) < x 1
  · have hnot2 : ¬ x 1 < sideH₁ α₂ β₂ (x 0) := by intro h2; exact hnots ⟨hc1, h2⟩
    have hge : sideH₁ α₂ β₂ (x 0) ≤ x 1 := le_of_not_gt hnot2
    have heq : x 1 = sideH₁ α₂ β₂ (x 0) := le_antisymm hle2 hge
    right
    rw [mem_stripChord]
    exact ⟨hxS, heq⟩
  · have hle1 : x 1 ≤ sideH₁ α₁ β₁ (x 0) := le_of_not_gt hc1
    have heq : x 1 = sideH₁ α₁ β₁ (x 0) := le_antisymm hle1 hge1
    left
    rw [mem_stripChord]
    exact ⟨hxS, heq⟩

/-- **Frontier of the between-region inside the strip = the two bounding
chords** (pointwise-ordered). -/
theorem frontier_betweenChord {α₁ β₁ α₂ β₂ : ℝ}
    (hlt : ∀ u : ℝ, u ∈ Set.Ioo 0 1 → sideH₁ α₁ β₁ u < sideH₁ α₂ β₂ u) :
    frontier (betweenChord α₁ β₁ α₂ β₂) ∩ stripInterior =
      stripChord α₁ β₁ ∪ stripChord α₂ β₂ := by
  ext x
  constructor
  · intro hx
    exact frontier_between_subset_chords hlt hx
  · intro hx
    rw [Set.mem_inter_iff]
    constructor
    · exact chord_mem_frontier_between hlt hx
    · rcases hx with hx1 | hx2
      · exact stripChord_subset_stripInterior (α := α₁) (β := β₁) hx1
      · exact stripChord_subset_stripInterior (α := α₂) (β := β₂) hx2

end Submission.PaperBand
