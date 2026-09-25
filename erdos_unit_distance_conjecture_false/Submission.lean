import Submission.Defs
import Submission.Work.Assembly.Construction
import Submission.Work.Falconer.Variant
import Submission.Work.CFTLib.Final
import Submission.Work.CFTLib.exists_tower_of_cftlib

open LeanEval.Combinatorics

namespace Submission

/-- The construction of planar point sets with many unit distances, in the complex plane:
there is `δ > 0` such that for every `N` there is a finite `P ⊆ ℂ` with `|P| ≥ N` and
`cDist P ≥ |P|^(1+δ)`. -/
private theorem construction_data :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, ∃ P : Finset ℂ,
      N ≤ P.card ∧ (P.card : ℝ) ^ (1 + δ) ≤ (Work.Defs.cDist P : ℝ) := by
  obtain ⟨C', hC'pos, hclass⟩ := Work.Interface.classNumber_le_rootDiscr
  obtain ⟨t, q, C, ht, hq, hqi, hq4, hC, hnum, hfam⟩ :=
    Work.CFTLib.exists_tower_of_cftlib Work.CFTLib.shafBound_proved
      Work.CFTLib.maximalClassCond_proved C' hC'pos
  exact Work.Assembly.Construction C' hC'pos hclass t q C ht hq hqi hq4 hC hnum hfam

/-- The isometry `ℂ ≃ ℝ²` preserves the number of unit-distance neighbours of a point. -/
private lemma card_unitNeighbours_image (P : Finset ℂ) (x : ℂ) :
    ((P.image (planeIso : ℂ → EuclideanSpace ℝ (Fin 2))).filter
        (fun y => dist (planeIso x) y = 1)).card =
      (P.filter (fun y => ‖x - y‖ = 1)).card := by
  classical
  have hset : (P.image (planeIso : ℂ → EuclideanSpace ℝ (Fin 2))).filter
        (fun y => dist (planeIso x) y = 1)
      = (P.filter (fun y => ‖x - y‖ = 1)).image
          (planeIso : ℂ → EuclideanSpace ℝ (Fin 2)) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hd⟩
      exact ⟨y, ⟨hy, by rwa [planeIso.dist_map, dist_eq_norm] at hd⟩, rfl⟩
    · rintro ⟨y, ⟨hy, hd⟩, rfl⟩
      exact ⟨⟨y, hy, rfl⟩, by rwa [planeIso.dist_map, dist_eq_norm]⟩
  rw [hset, Finset.card_image_of_injective _ planeIso.injective]

/-- **Erdős's unit-distance conjecture is false** (OpenAI 2026, Theorem 1.1): there is an
absolute `δ > 0` such that for every `N` there is a planar point set `P` with `|P| = n ≥ N`
points and at least `n ^ (1 + δ)` unit-distance pairs. -/
theorem erdos_unit_distance_conjecture_false :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ N : ℕ, ∃ (n : ℕ) (P : Finset (EuclideanSpace ℝ (Fin 2))),
        N ≤ n ∧ P.card = n ∧ (n : ℝ) ^ (1 + δ) ≤ (unitDist P : ℝ) := by
  obtain ⟨δ, hδ, hconcl⟩ := construction_data
  refine ⟨δ, hδ, fun N => ?_⟩
  obtain ⟨P, hNP, hν⟩ := hconcl N
  refine ⟨P.card, P.image (planeIso : ℂ → EuclideanSpace ℝ (Fin 2)), hNP, ?_, ?_⟩
  · exact Finset.card_image_of_injective _ planeIso.injective
  · rw [unitDist_image]; exact hν

/-- The Erdős–Falconer (1997) `k`-equidistant variant is also refuted: for every `k` there is a
planar point set in which every point has at least `k` neighbours at distance exactly one,
while the set has at least `k` points. -/
theorem erdos_falconer_variant :
    ∀ k : ℕ, ∃ Q : Finset (EuclideanSpace ℝ (Fin 2)), k ≤ Q.card ∧
      ∀ x ∈ Q, k ≤ (Q.filter (fun y => dist x y = 1)).card := by
  obtain ⟨δ, hδ, hconcl⟩ := construction_data
  intro k
  obtain ⟨Q, hkQ, hneigh⟩ := Work.Falconer.Variant δ hδ hconcl k
  refine ⟨Q.image (planeIso : ℂ → EuclideanSpace ℝ (Fin 2)), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ planeIso.injective]
    exact hkQ
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    rw [card_unitNeighbours_image]
    exact hneigh y hy

end Submission
