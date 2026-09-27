import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.finite_nearStab

/-!
# The near-stabiliser of a compact set is finite

For a discrete subgroup `Γ ≤ PO n 1` and compact sets `K₁ K₂ ⊆ ℍⁿ` (in the chart model `E n`),
only finitely many `γ ∈ Γ` satisfy `γ • u = v` for some `u ∈ K₁`, `v ∈ K₂`.

The argument is the standard properness of the action, made explicit.

* A compact set `K` is *bounded* in the hyperbolic distance from the base point `0`: the function
  `x ↦ hdist 0 x` is continuous, hence bounded above on `K` (`IsCompact.bddAbove_image`).  Call the
  two bounds `M₁` (for `K₁`) and `M₂` (for `K₂`).
* If `γ • u = v` with `u ∈ K₁`, `v ∈ K₂`, then the triangle inequality and the fact that `γ` acts
  by isometries give
  `hdist 0 (γ • 0) ≤ hdist 0 (γ • u) + hdist (γ • u) (γ • 0) = hdist 0 v + hdist u 0 ≤ M₁ + M₂`.
* The set of `γ ∈ Γ` displacing `0` by at most `M₁ + M₂` is finite for a discrete `Γ`
  (`Work.Mostow.finite_nearStab`), and our set is contained in it.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped Topology

theorem finite_nearStab_compact {n : ℕ} (hA : Work.Mostow.POBasic n) (hI : Work.Mostow.HypIsoData n)
    {Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)}
    (hdisc : IsDiscrete (SetLike.coe Γ)) {K₁ K₂ : Set (Submission.Mostow.E n)}
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂) :
    {γ : Γ | ∃ u ∈ K₁, ∃ v ∈ K₂, ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) • u = v}.Finite := by
  -- Step 1: a compact set is bounded in the hyperbolic distance from `0`.
  have hbdd : ∀ {K : Set (E n)}, IsCompact K → ∃ M : ℝ, ∀ x ∈ K, hdist (0 : E n) x ≤ M := by
    intro K hK
    have hcont : ContinuousOn (fun x : E n => hdist (0 : E n) x) K :=
      (hI.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
    obtain ⟨M, hM⟩ := hK.bddAbove_image hcont
    exact ⟨M, fun x hx => hM ⟨x, hx, rfl⟩⟩
  obtain ⟨M₁, hM₁⟩ := hbdd hK₁
  obtain ⟨M₂, hM₂⟩ := hbdd hK₂
  -- Step 2: such a `γ` displaces the base point by at most `M₁ + M₂`.
  refine (finite_nearStab hA hI hdisc (M₁ + M₂)).subset ?_
  rintro γ ⟨u, hu, v, hv, huv⟩
  have htri := hI.triangle (0 : E n) (((γ : Γ) : PO n 1) • u)
    (((γ : Γ) : PO n 1) • (0 : E n))
  have hiso : hdist (((γ : Γ) : PO n 1) • u) (((γ : Γ) : PO n 1) • (0 : E n)) =
      hdist u (0 : E n) := hI.isom_smul _ _ _
  have h1 : hdist (0 : E n) (((γ : Γ) : PO n 1) • u) ≤ M₂ := by
    rw [huv]; exact hM₂ v hv
  have h2 : hdist u (0 : E n) ≤ M₁ := by
    rw [hI.symm u (0 : E n)]; exact hM₁ u hu
  calc hdist (0 : E n) (((γ : Γ) : PO n 1) • (0 : E n))
      ≤ hdist (0 : E n) (((γ : Γ) : PO n 1) • u) +
          hdist (((γ : Γ) : PO n 1) • u) (((γ : Γ) : PO n 1) • (0 : E n)) := htri
    _ = hdist (0 : E n) (((γ : Γ) : PO n 1) • u) + hdist u (0 : E n) := by rw [hiso]
    _ ≤ M₂ + M₁ := add_le_add h1 h2
    _ = M₁ + M₂ := by ring

end Work.Mostow
