import Mathlib
import Submission.Work.Drive.SmoothArc.arcSystem_manifold
import Submission.Work.Drive.exists_regular_zero_radius
import Submission.Work.Drive.zeros_finite_on_unitCircle

/-!
# The zero set of a `C^∞` function in the unit disc (the C^∞ twin)

The `C^∞` twin of `Submission/Work/Drive/arcSystem_setup.lean`: the zero set `Zset h` of `h` in the
closed unit disc, the zero set `Mset h R` in the open disc of radius `R`, and their basic topological
properties.  (The finite-boundary-zero lemma is *reused* from the `C¹` chapter, since it only needs
`ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)`, which follows from `ContDiff ℝ ⊤` by `ContDiff.of_le le_top`.)
-/

namespace Work.Drive.SmoothArc

open scoped Manifold ContDiff Topology
open Set Function Filter

noncomputable section

variable {h : EuclideanSpace ℝ (Fin 2) → ℝ}

/-- The zero set of `h` in the closed unit disc. -/
def Zset (h : EuclideanSpace ℝ (Fin 2) → ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {z | ‖z‖ ≤ 1 ∧ h z = 0}

/-- The zero set of `h` in the open disc of radius `R`. -/
def Mset (h : EuclideanSpace ℝ (Fin 2) → ℝ) (R : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {z | h z = 0 ∧ ‖z‖ < R}

lemma mem_Zset {z : EuclideanSpace ℝ (Fin 2)} : z ∈ Zset h ↔ ‖z‖ ≤ 1 ∧ h z = 0 := Iff.rfl

lemma mem_Mset {z : EuclideanSpace ℝ (Fin 2)} {R : ℝ} :
    z ∈ Mset h R ↔ h z = 0 ∧ ‖z‖ < R := Iff.rfl

/-- The zero set of `h` in the closed unit disc is compact. -/
theorem isCompact_Zset (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h) : IsCompact (Zset h) := by
  have hclosed : IsClosed (Zset h) :=
    (isClosed_le continuous_norm continuous_const).inter
      (isClosed_eq hh.continuous continuous_const)
  refine (Metric.isCompact_iff_isClosed_bounded).mpr ⟨hclosed, ?_⟩
  refine (Metric.isBounded_closedBall (x := 0) (r := 1)).subset ?_
  intro z hz
  simpa using hz.1

/-- For `1 ≤ R` the closed-disc zero set sits inside the open-disc zero set. -/
theorem Zset_subset_Mset {R : ℝ} (hR : 1 < R) : Zset h ⊆ Mset h R := by
  rintro z ⟨hz1, hz2⟩
  exact ⟨hz2, lt_of_le_of_lt hz1 hR⟩

/-- The boundary zeros of `h`: the points of `Zset h` on the unit circle. -/
def Eset (h : EuclideanSpace ℝ (Fin 2) → ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {z | h z = 0 ∧ ‖z‖ = 1}

lemma mem_Eset {z : EuclideanSpace ℝ (Fin 2)} : z ∈ Eset h ↔ h z = 0 ∧ ‖z‖ = 1 := Iff.rfl

/-- The boundary zeros are finite, by transversality. -/
theorem finite_Eset (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h)
    (htrans : ∀ z : EuclideanSpace ℝ (Fin 2), h z = 0 → ‖z‖ = 1 →
      ¬ ∃ c : ℝ, fderiv ℝ h z = c • fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 2) => ‖w‖ ^ 2) z) :
    (Eset h).Finite := Work.Drive.zeros_finite_on_unitCircle h (hh.of_le (by simp)) htrans

/-- Every connected component of `Zset h` that meets the unit circle contains a boundary zero. -/
lemma exists_norm_eq_one_of_not_subset_ball {C : Set (EuclideanSpace ℝ (Fin 2))}
    (_hC : C ⊆ Zset h) (hne : (C ∩ Eset h).Nonempty) :
    ∃ z ∈ C, ‖z‖ = 1 := by
  obtain ⟨z, hzC, hzE⟩ := hne
  exact ⟨z, hzC, (mem_Eset.mp hzE).2⟩

end

end Work.Drive.SmoothArc
