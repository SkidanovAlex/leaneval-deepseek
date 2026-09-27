import Mathlib
import Submission.Work.Drive.psgFamilyDefs
import Submission.Work.Drive.coreMeet_ncard_eq_famMeet_gen

namespace Work.Drive

/-!
# The two end slices of the path family `(psgLoopFam, psgChainFam)` are the counts `CntAt`

The path family of the parity-locality lemma (`Work.Drive.psgLoopFam`, `Work.Drive.psgChainFam`) has
`p 0 = s` as its family parameter along the ramped path from `A` to `B` and `p 0`-independent slices at
the two ends `s = 0`, `s = 1`.  Its meet sets at those two ends are exactly the design's counts

* `CntAt Ξ Q c wA (A.1 + τ₁, A.2 + τ₂)` at `s = 0`, where `wA` is the class of the lift `tA`;
* `CntAt Ξ Q c wB (B.1 + τ₁, B.2 + τ₂)` at `s = 1`, where `wB` is the class of the lift `tB`.

The content is a two-step identification, both steps already available:

1. `Work.Drive.psgLoopFam Ξ Q A B τ₁ = chartLoopFam (psgQFam Ξ Q A B τ₁)` and
   `Work.Drive.psgChainFam Ξ Q c A B tA tB τ₂ = sweepFam c (1 - ·) (psgPFam Ξ Q A B tA tB τ₂)` hold by
   definition;
2. at the two ends `psgPathL A B ·` (resp. `psgPathR A B ·`) is constantly `A.1` (resp. `A.2`) and
   `psgAngleClass tA tB ·` is constantly the class of the lift,
   so the family is the constant family of the design's chart pair — and for a *constant* family of
   charts the design's count `coreMeet` is the family meet set, which is
   `Work.Drive.coreMeet_ncard_eq_famMeet_gen` at `t = 0` (resp. `t = 1`).
-/

noncomputable section

variable {m : ℕ}

/-- The `s = 0` slice of the loop-chart family is the chart perturbed at `A.1 + τ₁`. -/
lemma psgQFam_zero (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ₁ : EuclideanSpace ℝ (Fin m)) :
    psgQFam Ξ Q A B τ₁ 0 = pertChart Ξ Q (A.1 + τ₁) := by
  funext z
  simp [psgQFam, pertChart]

/-- The `s = 1` slice of the loop-chart family is the chart perturbed at `B.1 + τ₁`. -/
lemma psgQFam_one (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ₁ : EuclideanSpace ℝ (Fin m)) :
    psgQFam Ξ Q A B τ₁ 1 = pertChart Ξ Q (B.1 + τ₁) := by
  funext z
  simp [psgQFam, pertChart]

/-- The `s = 0` slice of the plane-presentation family is the rotated perturbed chart at `A.2 + τ₂`,
at the angle `wA` (the class of the lift `tA`). -/
lemma psgPFam_zero (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (tA tB : ℝ) (τ₂ : EuclideanSpace ℝ (Fin m)) {wA : UnitAddCircle}
    (htA : ((tA : ℝ) : UnitAddCircle) = wA) :
    psgPFam Ξ Q A B tA tB τ₂ 0
      = rotPresentation (pertChart Ξ Q (A.2 + τ₂)) wA := by
  funext y
  simp only [psgPFam, psgPathR_zero, psgAngleClass_zero, htA]
  rfl

/-- The `s = 1` slice of the plane-presentation family is the rotated perturbed chart at `B.2 + τ₂`,
at the angle `wB` (the class of the lift `tB`). -/
lemma psgPFam_one (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (tA tB : ℝ) (τ₂ : EuclideanSpace ℝ (Fin m)) {wB : UnitAddCircle}
    (htB : ((tB : ℝ) : UnitAddCircle) = wB) :
    psgPFam Ξ Q A B tA tB τ₂ 1
      = rotPresentation (pertChart Ξ Q (B.2 + τ₂)) wB := by
  funext y
  simp only [psgPFam, psgPathR_one, psgAngleClass_one, htB]
  rfl

/-- **The `p 0 = 0` end of the path family is the count at `(A.1 + τ₁, A.2 + τ₂)`.** -/
lemma psg_famMeet_zero_ncard' (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (tA tB : ℝ) (τ₁ τ₂ : EuclideanSpace ℝ (Fin m)) {wA : UnitAddCircle}
    (htA : ((tA : ℝ) : UnitAddCircle) = wA) :
    (famMeet (psgLoopFam Ξ Q A B τ₁) (psgChainFam Ξ Q c A B tA tB τ₂) 0).ncard
      = CntAt Ξ Q c wA (A.1 + τ₁, A.2 + τ₂) := by
  rw [show famMeet (psgLoopFam Ξ Q A B τ₁) (psgChainFam Ξ Q c A B tA tB τ₂) 0
      = famMeet (chartLoopFam (psgQFam Ξ Q A B τ₁))
          (sweepFam c (fun s => 1 - s) (psgPFam Ξ Q A B tA tB τ₂)) 0 from rfl]
  rw [← coreMeet_ncard_eq_famMeet_gen (psgQFam Ξ Q A B τ₁) c
    (psgPFam Ξ Q A B tA tB τ₂) 0 (by norm_num)]
  simp only [CntAt, coreSideCount, psgQFam_zero, psgPFam_zero Ξ Q A B tA tB τ₂ htA]

/-- **The `p 0 = 1` end of the path family is the count at `(B.1 + τ₁, B.2 + τ₂)`.** -/
lemma psg_famMeet_one_ncard' (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (tA tB : ℝ) (τ₁ τ₂ : EuclideanSpace ℝ (Fin m)) {wB : UnitAddCircle}
    (htB : ((tB : ℝ) : UnitAddCircle) = wB) :
    (famMeet (psgLoopFam Ξ Q A B τ₁) (psgChainFam Ξ Q c A B tA tB τ₂) 1).ncard
      = CntAt Ξ Q c wB (B.1 + τ₁, B.2 + τ₂) := by
  rw [show famMeet (psgLoopFam Ξ Q A B τ₁) (psgChainFam Ξ Q c A B tA tB τ₂) 1
      = famMeet (chartLoopFam (psgQFam Ξ Q A B τ₁))
          (sweepFam c (fun s => 1 - s) (psgPFam Ξ Q A B tA tB τ₂)) 1 from rfl]
  rw [← coreMeet_ncard_eq_famMeet_gen (psgQFam Ξ Q A B τ₁) c
    (psgPFam Ξ Q A B tA tB τ₂) 1 (by norm_num)]
  simp only [CntAt, coreSideCount, psgQFam_one, psgPFam_one Ξ Q A B tA tB τ₂ htB]

theorem psg_famMeet_endpoints {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → Work.Drive.CappingSpace → Work.Drive.CappingSpace)
    (Q : ℂ → Work.Drive.CappingSpace) (c : ℝ)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (tA tB : ℝ) (τ₁ τ₂ : EuclideanSpace ℝ (Fin m)) {wA wB : UnitAddCircle}
    (htA : ((tA : ℝ) : UnitAddCircle) = wA) (htB : ((tB : ℝ) : UnitAddCircle) = wB) :
    ((Work.Drive.famMeet (Work.Drive.psgLoopFam Ξ Q A B τ₁)
        (Work.Drive.psgChainFam Ξ Q c A B tA tB τ₂) 0).ncard
      = Work.Drive.CntAt Ξ Q c wA (A.1 + τ₁, A.2 + τ₂)) ∧
    ((Work.Drive.famMeet (Work.Drive.psgLoopFam Ξ Q A B τ₁)
        (Work.Drive.psgChainFam Ξ Q c A B tA tB τ₂) 1).ncard
      = Work.Drive.CntAt Ξ Q c wB (B.1 + τ₁, B.2 + τ₂)) :=
  ⟨psg_famMeet_zero_ncard' Ξ Q c A B tA tB τ₁ τ₂ htA,
   psg_famMeet_one_ncard' Ξ Q c A B tA tB τ₁ τ₂ htB⟩

end

end Work.Drive
