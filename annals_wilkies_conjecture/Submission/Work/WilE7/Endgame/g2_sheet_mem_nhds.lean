import Mathlib
import Submission.Work.WilE7.CoreStep.CoreLTSuccNodes

namespace Work.WilE7.Endgame

theorem g2_sheet_mem_nhds {n m k : ℕ} (C : Set (Fin n → ℝ)) (r : Fin k → (Fin n → ℝ) → (Fin (m + 1) → ℝ)) (j : Fin k) (hrcont : ContinuousOn (r j) C) (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ C) (O : Set (Fin (0 + (n + (m + 1))) → ℝ)) (hO : O ∈ nhds (Work.WilE7.CoreStep.absPtUp (n := n) (m := m) (Fin.append x₀ (r j x₀)))) : ∃ ρ > 0, ∀ x ∈ C, dist x x₀ < ρ → Work.WilE7.CoreStep.absPtUp (n := n) (m := m) (Fin.append x (r j x)) ∈ O := by
  -- `absPtUp` is a continuous linear reindexing.
  have hcontUp : Continuous (fun y : Fin (n + (m + 1)) → ℝ =>
      Work.WilE7.CoreStep.absPtUp (n := n) (m := m) y) := by
    apply continuous_pi
    intro i
    exact continuous_apply (Fin.cast (Nat.zero_add (n + (m + 1))) i)
  -- the sheet map `x ↦ absPtUp (Fin.append x (r j x))` is continuous on `C`.
  have hsheetcont : ContinuousOn (fun x : Fin n → ℝ =>
      Work.WilE7.CoreStep.absPtUp (n := n) (m := m) (Fin.append x (r j x))) C := by
    have h1 : ContinuousOn (fun x : Fin n → ℝ => (x, r j x)) C :=
      ContinuousOn.prodMk continuousOn_id hrcont
    have h2 : Continuous (fun p : (Fin n → ℝ) × (Fin (m + 1) → ℝ) =>
        Fin.append p.1 p.2) := Fin.continuous_append n (m + 1)
    exact hcontUp.comp_continuousOn (h2.comp_continuousOn h1)
  -- convert the `nhds`-membership at the image point into a relative neighbourhood.
  have hpre : (fun x : Fin n → ℝ =>
      Work.WilE7.CoreStep.absPtUp (n := n) (m := m) (Fin.append x (r j x))) ⁻¹' O
      ∈ nhdsWithin x₀ C :=
    (hsheetcont.continuousWithinAt hx₀).eventually hO
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hpre
  exact ⟨ε, hε, fun x hxC hdist => hsub ⟨Metric.mem_ball.mpr hdist, hxC⟩⟩

end Work.WilE7.Endgame
