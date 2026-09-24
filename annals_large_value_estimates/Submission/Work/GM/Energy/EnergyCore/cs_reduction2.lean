import Mathlib
import Submission.Work.GM.Energy.EnergyCore.Setup2

namespace Work.GM.Energy.EnergyCore

open Finset

/-- Cauchy–Schwarz for a finite family of reals: the third moment is at most the geometric mean of
the second and fourth moments, `Σ x³ ≤ √(Σ x²) · √(Σ x⁴)` (no sign hypothesis needed). -/
lemma cs_sum_cube_le_sqrt_mul_sqrt {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    (∑ i ∈ s, x i ^ 3) ≤ Real.sqrt (∑ i ∈ s, x i ^ 2) * Real.sqrt (∑ i ∈ s, x i ^ 4) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt s x (fun i => x i ^ 2)
  have e1 : ∀ i, x i * x i ^ 2 = x i ^ 3 := fun i => by ring
  have e2 : ∀ i, (x i ^ 2) ^ 2 = x i ^ 4 := fun i => by ring
  simpa only [e1, e2] using h

/-- Flattening identity: a triple sum with the last two index sets depending on the preceding
variables is a single sum over the nested sigma type. -/
lemma cs_sum_sigma_sigma {M α β γ : Type*} [AddCommMonoid M]
    (s : Finset α) (t : α → Finset β) (u : α → β → Finset γ)
    (f : (Σ _ : α, Σ _ : β, γ) → M) :
    (∑ x ∈ s.sigma (fun a => (t a).sigma (fun b => u a b)), f x)
      = ∑ a ∈ s, ∑ b ∈ t a, ∑ c ∈ u a b, f ⟨a, ⟨b, c⟩⟩ := by
  rw [Finset.sum_sigma]
  simp only [Finset.sum_sigma]

/-- Cauchy–Schwarz on the flattened family `(d,n₁,n₂) ↦ ‖R(n₁/n₂)‖`:
`Σ x³ ≤ √(Σ x²) · √(Σ x⁴)`, i.e. the third moment at all scales is at most the geometric mean
of the second and fourth moments at all scales. -/
theorem cs_reduction (N A : ℕ) (W : Finset ℝ) :
    (∑ d ∈ Finset.Icc A (2 * N),
      ∑ n1 ∈ Finset.Icc (Work.GM.Energy.EnergyCore.Md N d) (2 * Work.GM.Energy.EnergyCore.Md N d),
        ∑ n2 ∈ Finset.Icc (Work.GM.Energy.EnergyCore.Md N d) (2 * Work.GM.Energy.EnergyCore.Md N d),
          ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 3)
    ≤ Real.sqrt (∑ d ∈ Finset.Icc A (2 * N),
        ∑ n1 ∈ Finset.Icc (Work.GM.Energy.EnergyCore.Md N d) (2 * Work.GM.Energy.EnergyCore.Md N d),
          ∑ n2 ∈ Finset.Icc (Work.GM.Energy.EnergyCore.Md N d) (2 * Work.GM.Energy.EnergyCore.Md N d),
            ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 2)
      * Real.sqrt (∑ d ∈ Finset.Icc A (2 * N),
        ∑ n1 ∈ Finset.Icc (Work.GM.Energy.EnergyCore.Md N d) (2 * Work.GM.Energy.EnergyCore.Md N d),
          ∑ n2 ∈ Finset.Icc (Work.GM.Energy.EnergyCore.Md N d) (2 * Work.GM.Energy.EnergyCore.Md N d),
            ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 4) := by
  classical
  have key := cs_sum_cube_le_sqrt_mul_sqrt
    ((Finset.Icc A (2 * N)).sigma (fun d =>
      (Finset.Icc (Md N d) (2 * Md N d)).sigma (fun _ =>
        (Finset.Icc (Md N d) (2 * Md N d)))))
    (fun p : (Σ _ : ℕ, Σ _ : ℕ, ℕ) =>
      ‖Submission.GM.Rfun W ((p.2.1 : ℝ) / (p.2.2 : ℝ))‖)
  simp only [cs_sum_sigma_sigma] at key
  exact key

end Work.GM.Energy.EnergyCore
