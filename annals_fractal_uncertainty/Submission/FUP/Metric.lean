import ChallengeDeps

open FractalUncertainty
open MeasureTheory FourierTransform Metric
open scoped ENNReal

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

section smul

lemma dist_smul_of_nonneg (s : ℝ) (hs : 0 ≤ s) (x y : ℝᵈ) :
    dist (s • x) (s • y) = s * dist x y := by
  rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]

lemma dist_smul₀' (s : ℝ) (x y : ℝᵈ) :
    dist (s • x) (s • y) = ‖s‖ * dist x y := by
  rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul]

lemma smul_mem_segment (s : ℝ) {u₁ u₂ x : ℝᵈ}
    (hx : x ∈ segment ℝ u₁ u₂) : s • x ∈ segment ℝ (s • u₁) (s • u₂) := by
  rw [segment_eq_image] at hx ⊢
  rcases hx with ⟨θ, hθ, rfl⟩
  refine ⟨θ, hθ, ?_⟩
  simp [smul_add, smul_smul, mul_comm]

lemma smul_segment_subset (s : ℝ) (u₁ u₂ : ℝᵈ) :
    (fun x : ℝᵈ => s • x) '' (segment ℝ u₁ u₂) ⊆ segment ℝ (s • u₁) (s • u₂) := by
  intro z hz
  rcases hz with ⟨x, hx, rfl⟩
  exact smul_mem_segment s hx

lemma add_smul_self (θ : ℝ) (a : ℝᵈ) : (1 - θ) • a + θ • a = a := by
  rw [← add_smul]
  norm_num

lemma add_smul_self' (θ : ℝ) (a : ℝᵈ) : θ • a + (1 - θ) • a = a := by
  rw [add_comm]
  exact add_smul_self θ a

lemma image_add_subset_segment {u₁ u₂ a x : ℝᵈ} (hx : x ∈ segment ℝ u₁ u₂) :
    a + x ∈ segment ℝ (a + u₁) (a + u₂) := by
  rw [segment_eq_image] at hx ⊢
  rcases hx with ⟨θ, hθ, rfl⟩
  refine ⟨θ, hθ, ?_⟩
  dsimp
  rw [smul_add, smul_add]
  conv_rhs => rw [← add_smul_self θ a]
  abel

end smul

section ball

/-- The set `A + B` (Minkowski sum). -/
def addSet (A B : Set ℝᵈ) : Set ℝᵈ := {z | ∃ a ∈ A, ∃ b ∈ B, z = a + b}

lemma mem_addSet {A B : Set ℝᵈ} {z : ℝᵈ} : z ∈ addSet A B ↔ ∃ a ∈ A, ∃ b ∈ B, z = a + b := by
  rfl

lemma addSet_assoc (A B C : Set ℝᵈ) : addSet (addSet A B) C = addSet A (addSet B C) := by
  ext z; constructor
  · rintro ⟨w, hw, c, hc, rfl⟩
    rcases hw with ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b + c, by exact ⟨b, hb, c, hc, rfl⟩, by abel⟩
  · rintro ⟨a, ha, w, hw, rfl⟩
    rcases hw with ⟨b, hb, c, hc, rfl⟩
    exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩, c, hc, by abel⟩

lemma addSet_translate (A : Set ℝᵈ) (a : ℝᵈ) :
    addSet A {a} = (fun x : ℝᵈ => x + a) '' A := by
  ext z; constructor
  · rintro ⟨x, hx, w, rfl, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, a, rfl, rfl⟩

lemma addSet_subset_closedBall {X : Set ℝᵈ} {r : ℝ} :
    addSet X (closedBall 0 r) = {z | ∃ y ∈ X, dist y z ≤ r} := by
  ext z
  constructor
  · rintro ⟨y, hy, b, hb, rfl⟩
    exact ⟨y, hy, by simpa [dist_eq_norm] using (Metric.mem_closedBall.mp hb : dist b 0 ≤ r)⟩
  · rintro ⟨y, hy, hz⟩
    refine ⟨y, hy, z - y, ?_, by abel⟩
    rw [Metric.mem_closedBall]
    rw [dist_eq_norm]
    calc
      ‖(z - y) - 0‖ = ‖y - z‖ := by
        rw [← norm_neg]
        congr 1
        abel
      _ ≤ r := by simpa [dist_eq_norm] using hz

end ball

end Submission.FUP
