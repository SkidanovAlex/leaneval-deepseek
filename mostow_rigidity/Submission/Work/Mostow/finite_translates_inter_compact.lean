import Mathlib
import Submission.Work.Mostow.HaarBase
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.properAction

/-!
# Finitely many translates of a compact set meet another compact set

For a discrete subgroup `Γ ≤ PO n 1` and compact sets `K₁ K₂ ⊆ ℍⁿ` (in the chart model `E n`),
only finitely many `γ ∈ Γ` satisfy `(γ • K₁) ∩ K₂ ≠ ∅`.

The point is that such a `γ` displaces the origin boundedly: if `γ • u = w` with `u ∈ K₁`,
`w ∈ K₂`, then
`hdist 0 (γ • 0) ≤ hdist 0 (γ • u) + hdist (γ • u) (γ • 0) = hdist 0 w + hdist u 0`,
and both terms are bounded on the compact sets `K₂`, `K₁`.  The near-stabiliser of the origin in
a discrete subgroup is finite (`Work.Mostow.nearStab_finite`).
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped Topology

/-- A set contained in a norm ball is contained in a hyperbolic ball around the base point:
`hdist 0 x = arcosh (tpart x) = arcosh (√(1+‖x‖²))`. -/
lemma hdist_zero_le_arcosh_sqrt {n : ℕ} (h0 : ∀ u v : E n, 0 ≤ hdist u v) {x : E n} {N : ℝ}
    (hN : ‖x‖ ≤ N) : hdist (0 : E n) x ≤ Real.arcosh (Real.sqrt (1 + (max N 0) ^ 2)) := by
  have hN' : ‖x‖ ≤ max N 0 := le_trans hN (le_max_left _ _)
  have harg : 1 ≤ Real.sqrt (1 + (max N 0) ^ 2) :=
    Real.one_le_sqrt.mpr (by nlinarith [le_max_right N 0, sq_nonneg (max N 0)])
  have hcosh : Real.cosh (hdist (0 : E n) x) ≤
      Real.cosh (Real.arcosh (Real.sqrt (1 + (max N 0) ^ 2))) := by
    rw [Real.cosh_arcosh harg, cosh_hdist_zero]
    simp only [tpart]
    exact Real.sqrt_le_sqrt (by nlinarith [norm_nonneg x])
  have h2 : |hdist (0 : E n) x| ≤ |Real.arcosh (Real.sqrt (1 + (max N 0) ^ 2))| :=
    Real.cosh_le_cosh.mp hcosh
  rw [abs_of_nonneg (h0 _ _), abs_of_nonneg (Real.arcosh_nonneg harg)] at h2
  exact h2

/-- A compact subset of the chart is bounded above in hyperbolic distance from the base point. -/
lemma exists_hdist_le_of_isCompact {n : ℕ} (hI : Submission.Mostow.HypIsometryProp n)
    {K : Set (Submission.Mostow.E n)} (hK : IsCompact K) :
    ∃ M : ℝ, ∀ x ∈ K, Submission.Mostow.hdist (0 : Submission.Mostow.E n) x ≤ M := by
  obtain ⟨N, hN⟩ := exists_norm_le_of_isCompact hK
  exact ⟨_, fun x hx => hdist_zero_le_arcosh_sqrt (HypIsoData.ofProp hI).nonneg (hN x hx)⟩

theorem finite_translates_inter_compact (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    {Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)}
    (hdisc : IsDiscrete (Γ : Set (LeanEval.Geometry.MostowRigidity.PO n 1)))
    {K₁ K₂ : Set (Submission.Mostow.E n)} (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂) :
    {γ : Γ | (((fun u : Submission.Mostow.E n =>
      (γ : LeanEval.Geometry.MostowRigidity.PO n 1) • u) '' K₁) ∩ K₂).Nonempty}.Finite := by
  let hId := HypIsoData.ofProp hI
  obtain ⟨M₁, hM₁⟩ := exists_hdist_le_of_isCompact hI hK₁
  obtain ⟨M₂, hM₂⟩ := exists_hdist_le_of_isCompact hI hK₂
  refine (nearStab_finite n Γ hdisc (M₁ + M₂)).subset ?_
  rintro γ ⟨w, ⟨u, huK, huw⟩, hwK⟩
  have huw' : (γ : PO n 1) • u = w := huw
  have htri := hId.triangle (0 : E n) ((γ : PO n 1) • u) ((γ : PO n 1) • (0 : E n))
  have h2 : Submission.Mostow.hdist ((γ : PO n 1) • u) ((γ : PO n 1) • (0 : E n)) =
      Submission.Mostow.hdist u (0 : E n) := hId.isom_smul _ _ _
  have h3 : Submission.Mostow.hdist (0 : E n) ((γ : PO n 1) • u) ≤ M₂ := by
    rw [huw']; exact hM₂ w hwK
  have h4 : Submission.Mostow.hdist u (0 : E n) ≤ M₁ := by
    rw [hId.symm u (0 : E n)]; exact hM₁ u huK
  calc Submission.Mostow.hdist (0 : E n) ((γ : PO n 1) • (0 : E n))
      ≤ Submission.Mostow.hdist (0 : E n) ((γ : PO n 1) • u) +
          Submission.Mostow.hdist ((γ : PO n 1) • u) ((γ : PO n 1) • (0 : E n)) := htri
    _ = Submission.Mostow.hdist (0 : E n) ((γ : PO n 1) • u) +
          Submission.Mostow.hdist u (0 : E n) := by rw [h2]
    _ ≤ M₂ + M₁ := add_le_add h3 h4
    _ = M₁ + M₂ := by ring

end Work.Mostow
