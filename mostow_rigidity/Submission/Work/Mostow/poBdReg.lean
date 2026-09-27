import Mathlib
import Submission.Work.Mostow.poAux

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Matrix

/-! ## Boundary action regularity (`poBdReg`)

`bdO A ξ` is the null ray of `mat A` applied to the null vector `theta ξ = (ξ, 1)`, renormalised
by its time coordinate:

`bdO A ξ = toLp 2 (fun i => (mat A *ᵥ theta ξ) (inl i) / (mat A *ᵥ theta ξ) (inr 0))`.

Each numerator is a continuous (hence measurable) real function of `ξ`; on the sphere `Sph n` the
denominator never vanishes (`mat_mulVec_theta_ne_zero`), so the quotient is continuous there, and
it is always measurable. Transporting `Fin n → ℝ` to `E n = PiLp 2 (Fin n → ℝ)` along
`WithLp.toLp 2` (continuous and measurable) gives the two claims. -/

/-- The map `ξ ↦ theta ξ = (ξ, 1)` is continuous. -/
lemma poBdReg_continuous_theta (n : ℕ) : Continuous (fun ξ : E n => theta ξ) := by
  rw [continuous_pi_iff]
  intro a
  rcases a with i | j
  · exact PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    simpa [theta] using continuous_const

/-- `ξ ↦ mat A *ᵥ theta ξ` is continuous. -/
lemma poBdReg_continuous_mulVec_theta (n : ℕ) (A : O1 n) :
    Continuous (fun ξ : E n => mat A *ᵥ theta ξ) :=
  ((Matrix.mulVecLin (mat A)).continuous_of_finiteDimensional).comp
    (poBdReg_continuous_theta n)

/-- Explicit coordinate formula for the boundary action. -/
lemma poBdReg_bdO_form (n : ℕ) (A : O1 n) :
    bdO A = fun ξ : E n => WithLp.toLp 2 (fun i : Fin n =>
      (mat A *ᵥ theta ξ) (Sum.inl i) / (mat A *ᵥ theta ξ) (Sum.inr 0)) := by
  ext ξ i
  rfl

theorem poBdReg (n : ℕ) :
    (∀ A : O1 n, ContinuousOn (bdO A) (Sph n)) ∧ (∀ A : O1 n, Measurable (bdO A)) := by
  have hcont : ∀ A : O1 n, Continuous (fun ξ : E n => mat A *ᵥ theta ξ) :=
    fun A => poBdReg_continuous_mulVec_theta n A
  have hform : ∀ A : O1 n, bdO A = fun ξ : E n => WithLp.toLp 2 (fun i : Fin n =>
      (mat A *ᵥ theta ξ) (Sum.inl i) / (mat A *ᵥ theta ξ) (Sum.inr 0)) :=
    fun A => poBdReg_bdO_form n A
  constructor
  · intro A
    have hnum : ∀ i : Fin n, ContinuousOn
        (fun ξ : E n => (mat A *ᵥ theta ξ) (Sum.inl i)) (Sph n) :=
      fun i => ((continuous_apply (Sum.inl i)).comp (hcont A)).continuousOn
    have hden : ContinuousOn (fun ξ : E n => (mat A *ᵥ theta ξ) (Sum.inr 0)) (Sph n) :=
      ((continuous_apply (Sum.inr 0)).comp (hcont A)).continuousOn
    have hdiv : ∀ i : Fin n, ContinuousOn
        (fun ξ : E n => (mat A *ᵥ theta ξ) (Sum.inl i) / (mat A *ᵥ theta ξ) (Sum.inr 0))
        (Sph n) :=
      fun i => (hnum i).div hden (fun ξ hξ => mat_mulVec_theta_ne_zero A hξ)
    have hpi : ContinuousOn (fun ξ : E n => (fun i : Fin n =>
        (mat A *ᵥ theta ξ) (Sum.inl i) / (mat A *ᵥ theta ξ) (Sum.inr 0))) (Sph n) :=
      continuousOn_pi.2 hdiv
    rw [hform A]
    exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin n => ℝ)).comp_continuousOn hpi
  · intro A
    have hnum : ∀ i : Fin n, Measurable
        (fun ξ : E n => (mat A *ᵥ theta ξ) (Sum.inl i)) :=
      fun i => ((continuous_apply (Sum.inl i)).comp (hcont A)).measurable
    have hden : Measurable (fun ξ : E n => (mat A *ᵥ theta ξ) (Sum.inr 0)) :=
      ((continuous_apply (Sum.inr 0)).comp (hcont A)).measurable
    have hpi : Measurable (fun ξ : E n => (fun i : Fin n =>
        (mat A *ᵥ theta ξ) (Sum.inl i) / (mat A *ᵥ theta ξ) (Sum.inr 0))) :=
      measurable_pi_iff.2 (fun i => (hnum i).div hden)
    rw [hform A]
    exact (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp hpi

/-- The same regularity for the boundary action of `PO n 1` — the two boundary clauses of
`POActionProp` — an immediate corollary since `bd g = bdO (rep g)` by definition. -/
theorem poBdReg_PO (n : ℕ) :
    (∀ g : PO n 1, ContinuousOn (bd g) (Sph n)) ∧ (∀ g : PO n 1, Measurable (bd g)) :=
  ⟨fun g => (poBdReg n).1 (rep g), fun g => (poBdReg n).2 (rep g)⟩

end Work.Mostow
