import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

open scoped Topology
noncomputable section

namespace Commons.Analysis.MeasureTheory

abbrev ESph (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Sp (n : ℕ) := Metric.sphere (0 : ESph n) 1

/-- coordinate function on the unit sphere -/
def spherePolyCoord (n : ℕ) (i : Fin n) : C(Sp n, ℝ) :=
  ⟨fun θ : Sp n => (θ : ESph n) i, by fun_prop⟩

/-- algebra hom from multivariate polynomials to continuous functions on the unit sphere -/
def spherePolyToCont (n : ℕ) : MvPolynomial (Fin n) ℝ →ₐ[ℝ] C(Sp n, ℝ) :=
  MvPolynomial.aeval (spherePolyCoord n)

lemma spherePoly_X_eq_coord (n : ℕ) (i : Fin n) :
    spherePolyToCont n (MvPolynomial.X i) = spherePolyCoord n i := by
  simp [spherePolyToCont]

/-- evaluating a polynomial in the continuous-function algebra at a sphere point
is the same as evaluating it at the coordinates of the point -/
lemma spherePoly_apply_eval {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (θ : Sp n) :
    spherePolyToCont n P θ = MvPolynomial.eval (fun i : Fin n => (θ : ESph n) i) P := by
  let evθ : C(Sp n, ℝ) →ₐ[ℝ] ℝ := ContinuousMap.evalAlgHom ℝ ℝ θ
  calc
    spherePolyToCont n P θ = evθ (spherePolyToCont n P) := by
      simp [evθ]
    _ = evθ (MvPolynomial.aeval (spherePolyCoord n) P) := by rfl
    _ = MvPolynomial.aeval (fun i : Fin n => evθ (spherePolyCoord n i)) P := by
      exact MvPolynomial.comp_aeval_apply (R := ℝ) (S₁ := C(Sp n, ℝ)) (φ := evθ) (f := spherePolyCoord n) P
    _ = MvPolynomial.aeval (fun i : Fin n => (θ : ESph n) i) P := by
      apply congrArg (fun g : Fin n → ℝ => MvPolynomial.aeval g P)
      funext i
      simp [evθ, spherePolyCoord]
    _ = MvPolynomial.eval (fun i : Fin n => (θ : ESph n) i) P := by
      rfl

/-- The polynomial functions restricted to the unit sphere are uniformly dense among
continuous functions on the sphere. This is a direct application of the
Stone-Weierstrass theorem to the subalgebra of `C(Sp n, ℝ)` given by polynomial
evaluation, which separates points since the coordinate functions do. -/
theorem sphere_polynomial_uniform_dense
    {n : ℕ} (f : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ)
    (hfcont : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : MvPolynomial (Fin n) ℝ,
      ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        |f θ - (MvPolynomial.eval (fun i : Fin n => (θ : EuclideanSpace ℝ (Fin n)) i) P)| ≤ ε := by
  let A : Subalgebra ℝ C(Sp n, ℝ) := (spherePolyToCont n).range
  have hsep : A.SeparatesPoints := by
    change ∀ ⦃x y : Sp n⦄, x ≠ y →
      ∃ g : Sp n → ℝ,
        g ∈ ((fun h : C(Sp n, ℝ) => (h : Sp n → ℝ)) '' (A : Set C(Sp n, ℝ))) ∧ g x ≠ g y
    intro x y hxy
    have hxney : (x : ESph n) ≠ (y : ESph n) := Subtype.coe_injective.ne hxy
    have hdiff : ∃ i : Fin n, (x : ESph n) i ≠ (y : ESph n) i := by
      by_contra h
      apply hxney
      refine PiLp.ext ?_
      intro i
      by_contra hne
      exact h ⟨i, hne⟩
    rcases hdiff with ⟨i, hi⟩
    refine ⟨fun θ : Sp n => (θ : ESph n) i, ?_, hi⟩
    · refine ⟨spherePolyCoord n i, ?_, ?_⟩
      · change spherePolyCoord n i ∈ (spherePolyToCont n).range
        exact (AlgHom.mem_range (spherePolyToCont n)).mpr ⟨MvPolynomial.X i, spherePoly_X_eq_coord n i⟩
      · rfl
  obtain ⟨g, hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints
    (A := A) hsep f hfcont ε hε
  have hmem : (g : C(Sp n, ℝ)) ∈ (spherePolyToCont n).range := by
    simp [A]
  obtain ⟨P, hP⟩ := (AlgHom.mem_range (spherePolyToCont n)).mp hmem
  refine ⟨P, ?_⟩
  intro θ
  have hb : ‖(g : Sp n → ℝ) θ - f θ‖ < ε := hg θ
  have hgθ : (g : Sp n → ℝ) θ = MvPolynomial.eval (fun i : Fin n => (θ : ESph n) i) P := by
    calc
      (g : Sp n → ℝ) θ = (g : C(Sp n, ℝ)) θ := rfl
      _ = spherePolyToCont n P θ := by rw [hP]
      _ = MvPolynomial.eval (fun i : Fin n => (θ : ESph n) i) P := spherePoly_apply_eval P θ
  have hb' : |MvPolynomial.eval (fun i : Fin n => (θ : ESph n) i) P - f θ| < ε := by
    rw [← hgθ]
    simpa [Real.norm_eq_abs] using hb
  exact le_of_lt (by simpa [abs_sub_comm] using hb')

end Commons.Analysis.MeasureTheory