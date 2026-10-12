import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BoxTauGen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.BoxOpA` — the box-generic one-slot operators `boxOpG`, `boxOpZ`

The genuine ("Gen") box `τ`-operators of `BoxTauGen.lean` are, up to the prefactor `(√volA)⁻¹`,
two specialisations of a single one-slot operator

  `boxOpG A f h Ψ x = Σ_i 1_A(x_i) · f(x_i) · ∫_{z∈A} h z · Ψ(x_{i←z})`

(the box indicator sitting in the *created / annihilated* slot `i`), namely

* `boxTauAnnGen volA A g Ψ = (√volA)⁻¹ • boxOpG A 1 g Ψ`   (FS's `a₀†a(g)`),
* `boxTauDagGen volA A g Ψ = (√volA)⁻¹ • boxOpG A g 1 Ψ`   (FS's `a†(g)a₀`),

while `boxOpZ A f h Ψ x = Σ_i f(x_i) · ∫_{z∈A} h z · Ψ(x_{i←z})` is the same sum *without* the
box indicator.  `boxOpZ A h f` is the formal adjoint partner of `boxOpG A f h` in the sense of
`Work.BoseFixB1.boxOpG_adjoint` (proved in `boxOpG_adjoint.lean` by the one-slot peel).

This module only fixes the definitions and the two definitional bridges; the analytic lemmas live
in the sibling files `boxOpG_adjoint.lean`, `boxOpG_commutator.lean`,
`boxOpG_one_one_flatCount.lean` and `boxOpG_gg_nonneg.lean`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The box-generic one-slot operator with the box indicator in the created/annihilated slot**:
`Σ_i 1_A(x_i)·f(x_i)·∫_{z∈A} h z·Ψ(x_{i←z})`.  For `(f,h) = (1,g)` this is (up to
`(√volA)⁻¹`) the genuine `a₀†a(g)`, for `(f,h) = (g,1)` the genuine `a†(g)a₀`. -/
noncomputable def boxOpG {N : ℕ} (A : Set (EuclideanSpace ℝ (Fin 3)))
    (f h : EuclideanSpace ℝ (Fin 3) → ℝ) (Ψ : X N → ℝ) (x : X N) : ℝ :=
  ∑ i : Fin N, A.indicator (fun _ => (1 : ℝ)) (x i) * f (x i)
    * ∫ z in A, h z * Ψ (Function.update x i z)

/-- **The box-generic one-slot operator without the box indicator**, the formal adjoint partner of
`boxOpG`. -/
noncomputable def boxOpZ {N : ℕ} (A : Set (EuclideanSpace ℝ (Fin 3)))
    (f h : EuclideanSpace ℝ (Fin 3) → ℝ) (Ψ : X N → ℝ) (x : X N) : ℝ :=
  ∑ i : Fin N, f (x i) * ∫ z in A, h z * Ψ (Function.update x i z)

/-- The genuine box D1 annihilation operator is (up to `(√volA)⁻¹`) the `(1,g)`-specialisation of
`boxOpG`. -/
lemma boxTauAnnGen_eq_boxOpG {N : ℕ} (volA : ℝ)
    (A : Set (EuclideanSpace ℝ (Fin 3))) (g : EuclideanSpace ℝ (Fin 3) → ℝ)
    (Ψ : X N → ℝ) :
    boxTauAnnGen volA A g Ψ
      = fun x => (Real.sqrt volA)⁻¹ * boxOpG A (fun _ => (1 : ℝ)) g Ψ x := by
  funext x
  simp only [boxTauAnnGen, boxOpG]
  refine congrArg (fun t : ℝ => (Real.sqrt volA)⁻¹ * t) ?_
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- The genuine box D1 creation operator is (up to `(√volA)⁻¹`) the `(g,1)`-specialisation of
`boxOpG`. -/
lemma boxTauDagGen_eq_boxOpG {N : ℕ} (volA : ℝ)
    (A : Set (EuclideanSpace ℝ (Fin 3))) (g : EuclideanSpace ℝ (Fin 3) → ℝ)
    (Ψ : X N → ℝ) :
    boxTauDagGen volA A g Ψ
      = fun x => (Real.sqrt volA)⁻¹ * boxOpG A g (fun _ => (1 : ℝ)) Ψ x := by
  funext x
  simp only [boxTauDagGen, boxOpG]
  refine congrArg (fun t : ℝ => (Real.sqrt volA)⁻¹ * t) ?_
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

end Work.BoseFixB1
