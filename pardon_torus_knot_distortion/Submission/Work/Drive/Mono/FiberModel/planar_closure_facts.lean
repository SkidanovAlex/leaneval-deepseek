import Mathlib
import Submission.Work.Drive.Mono.FiberModel.planar_pieces

/-!
# Tools for the plane pieces of the shadow chamber

`Z = planarImage = interior W ∩ chamber`, with `chamber = {|x₁ - a| > h ∨ lam ≤ x₂}` and `W` the
compact convex shadow of the closed box.  The pieces `wingPlus`, `wingMinus`, `cap0` are the
closures of the parts of `interior W` strictly beyond the two slab faces and strictly above the
level; `closure Z` is their union and `interior (closure Z)` is `interior W ∩ ({h < |x₁ - a|} ∪
{lam < x₂})` (this is the statement reviewed as `planar_closure_facts`; its proof is assembled from
the tools below and is not yet complete).

The tools proved here:

* inside an *open* set of the plane one may perturb a point up in the second coordinate or
  sidewards in the first coordinate by an arbitrarily small amount
  (`exists_perturbed_snd`, `exists_perturbed_fst_down`, `exists_perturbed_fst_up`) — this is what
  makes the `lam ≤ x₂` versus `lam < x₂` (and the slab-face) mismatches harmless;
* `chamber a h lam` is the union of the three half-planes `{a + h < x₁}`, `{x₁ < a - h}`,
  `{lam ≤ x₂}` (`chamber_eq`);
* the interior of the closure of an open convex set is the set itself
  (`interior_closure_eq_self_of_isOpen_convex`).
-/

open LeanEval.KnotTheory.PardonDistortion Set Filter
open scoped Topology

namespace Work.Drive.Mono.FiberModel

noncomputable section

/-! ## Perturbation helpers inside an open set -/

/-- Inside an open set one may move a point up in the second coordinate by an arbitrarily small
amount. -/
theorem exists_perturbed_snd {U : Set (ℝ × ℝ)} (hU : IsOpen U) {X : ℝ × ℝ} (hX : X ∈ U) :
    ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ (X.1, X.2 + ε) ∈ U := by
  have hcont : Continuous fun ε : ℝ => ((X.1, X.2 + ε) : ℝ × ℝ) :=
    continuous_const.prodMk (continuous_const.add continuous_id)
  have hX' : ((X.1, X.2 + 0) : ℝ × ℝ) ∈ U := by simpa using hX
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), ((X.1, X.2 + ε) : ℝ × ℝ) ∈ U :=
    (hcont.tendsto 0).eventually (hU.mem_nhds hX')
  obtain ⟨δ', hδ', hδ'U⟩ := Metric.eventually_nhds_iff.mp hev
  intro δ hδ
  refine ⟨min δ δ' / 2, by positivity, ?_, ?_⟩
  · have h : min δ δ' ≤ δ := min_le_left _ _
    linarith
  · apply hδ'U
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    have h : min δ δ' ≤ δ' := min_le_right _ _
    linarith

/-- Inside an open set one may move a point down in the first coordinate by an arbitrarily small
amount. -/
theorem exists_perturbed_fst_down {U : Set (ℝ × ℝ)} (hU : IsOpen U) {X : ℝ × ℝ} (hX : X ∈ U) :
    ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ (X.1 - ε, X.2) ∈ U := by
  have hcont : Continuous fun ε : ℝ => ((X.1 - ε, X.2) : ℝ × ℝ) :=
    (continuous_const.sub continuous_id).prodMk continuous_const
  have hX' : ((X.1 - 0, X.2) : ℝ × ℝ) ∈ U := by simpa using hX
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), ((X.1 - ε, X.2) : ℝ × ℝ) ∈ U :=
    (hcont.tendsto 0).eventually (hU.mem_nhds hX')
  obtain ⟨δ', hδ', hδ'U⟩ := Metric.eventually_nhds_iff.mp hev
  intro δ hδ
  refine ⟨min δ δ' / 2, by positivity, ?_, ?_⟩
  · have h : min δ δ' ≤ δ := min_le_left _ _
    linarith
  · apply hδ'U
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    have h : min δ δ' ≤ δ' := min_le_right _ _
    linarith

/-- Inside an open set one may move a point up in the first coordinate by an arbitrarily small
amount. -/
theorem exists_perturbed_fst_up {U : Set (ℝ × ℝ)} (hU : IsOpen U) {X : ℝ × ℝ} (hX : X ∈ U) :
    ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ (X.1 + ε, X.2) ∈ U := by
  have hcont : Continuous fun ε : ℝ => ((X.1 + ε, X.2) : ℝ × ℝ) :=
    (continuous_const.add continuous_id).prodMk continuous_const
  have hX' : ((X.1 + 0, X.2) : ℝ × ℝ) ∈ U := by simpa using hX
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), ((X.1 + ε, X.2) : ℝ × ℝ) ∈ U :=
    (hcont.tendsto 0).eventually (hU.mem_nhds hX')
  obtain ⟨δ', hδ', hδ'U⟩ := Metric.eventually_nhds_iff.mp hev
  intro δ hδ
  refine ⟨min δ δ' / 2, by positivity, ?_, ?_⟩
  · have h : min δ δ' ≤ δ := min_le_left _ _
    linarith
  · apply hδ'U
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    have h : min δ δ' ≤ δ' := min_le_right _ _
    linarith

/-! ## The chamber as a union of half-planes -/

theorem chamber_eq (a h lam : ℝ) (hh : 0 < h) :
    chamber a h lam = {X : ℝ × ℝ | a + h < X.1} ∪ {X : ℝ × ℝ | X.1 < a - h}
      ∪ {X : ℝ × ℝ | lam ≤ X.2} := by
  ext X
  simp only [chamber, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro (h1 | h1)
    · have h1' : h < |X.1 - a| := h1
      rcases lt_abs.mp h1' with h1' | h1'
      · exact Or.inl (Or.inl (by linarith))
      · exact Or.inl (Or.inr (by linarith))
    · exact Or.inr h1
  · rintro ((h1 | h1) | h1)
    · exact Or.inl (lt_abs.mpr (Or.inl (by linarith)))
    · exact Or.inl (lt_abs.mpr (Or.inr (by linarith)))
    · exact Or.inr h1

/-! ## The tools used in the assembly -/

/-- The interior of the closure of an open convex set is the set itself. -/
theorem interior_closure_eq_self_of_isOpen_convex {T : Set (ℝ × ℝ)} (hT : Convex ℝ T)
    (hTo : IsOpen T) : interior (closure T) = T := by
  by_cases hne : T.Nonempty
  · rw [Convex.interior_closure_eq_interior_of_nonempty_interior hT (by rwa [hTo.interior_eq])]
    exact hTo.interior_eq
  · rw [not_nonempty_iff_eq_empty.mp hne, closure_empty, interior_empty]

end

end Work.Drive.Mono.FiberModel
