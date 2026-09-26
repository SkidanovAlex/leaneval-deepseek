import Mathlib
import Submission.Work.TorusCover.Basic
import Submission.Work.Core.torusMap_eq_iff
import Submission.Work.CoreTopology.ncard_standardCurve_longitude

namespace Work.TorusCover

open LeanEval.KnotTheory.PardonDistortion Set

/-- The longitude circle of `Work.CoreTopology.standard` is `Work.Core.longitudeCircle`. -/
private lemma longitudeCurve_standard_coe' (φ : ℝ) :
    (Work.CoreTopology.longitudeCurve Work.CoreTopology.standard φ : ℝ → R3) =
      Work.Core.longitudeCircle φ := by
  funext θ
  simp only [Work.CoreTopology.longitudeCurve, Work.CoreTopology.ParamTorus.longitudeLoop_apply,
    Work.CoreTopology.standard_psi, Work.Core.longitudeCircle]

theorem ncard_standardTorusCurve_longitude (p q : ℕ) (hq : 0 < q) (φ : ℝ) :
    {t | t ∈ Set.Ico (0 : ℝ) (2 * Real.pi) ∧
      LeanEval.KnotTheory.PardonDistortion.standardTorusCurve p q t ∈
        Set.range (Work.Core.longitudeCircle φ)}.ncard = q := by
  have hcurve : ∀ t : ℝ,
      Work.CoreTopology.standardCurve p q t = standardTorusCurve p q t :=
    fun t => Work.CoreTopology.standardCurve_apply p q t
  have hrange : Set.range (Work.CoreTopology.longitudeCurve Work.CoreTopology.standard φ)
      = Set.range (Work.Core.longitudeCircle φ) := by
    rw [longitudeCurve_standard_coe' φ]
  have hset : {t : ℝ | t ∈ Set.Ico (0 : ℝ) (2 * Real.pi) ∧
        standardTorusCurve p q t ∈ Set.range (Work.Core.longitudeCircle φ)}
      = Set.Ico (0 : ℝ) (2 * Real.pi) ∩
        {t : ℝ | Work.CoreTopology.standardCurve p q t ∈
          Set.range (Work.CoreTopology.longitudeCurve Work.CoreTopology.standard φ)} := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [hcurve t, hrange]; exact h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [← hcurve t, ← hrange]; exact h2⟩
  rw [hset]
  exact Work.CoreTopology.ncard_standardCurve_longitude p q hq φ

end Work.TorusCover
