import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.PerBoxNames
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.BoxTauGen` — the **genuine** FS box `τ`-operators and windowed modes

`Submission/Work/BoseFixB1/BoxTau.lean` defines `boxTauAnn` and `boxWinModeRe/Im` *without* the
box indicator in the "created/annihilated slot" position.  That is invisible on the centred cube
(the ambient box then forces `x_i ∈ A`), but it is **wrong for a general `A`**: the identity
`boxA2 = (2π)⁻³∫ pairW(q)·volA⁻¹·boxWinModeR(q)` is FALSE for `A ⊊ acube ℓ` — see the machine
independent counterexample (validated to 50 digits, 1D and 3D) in
`FINDING_boxPairForm_eq_boxWinModeR_FALSE.md`.

FS `lm:appbogolubov` uses

* `a₀†a(g) = |A|^{−1/2}Σ_i 1_A(x_i)∫_A g(z)·Ψ(x_{i←z})dz`  (the indicator is the constant-mode
  factor `1_A/√|A|` evaluated at the created particle's position), and
* the genuine mean-free projected mode `Q_A(χe^{−iq·})|_A = 1_A(z)(χ z e^{−i⟪q,z⟫} − ⨍_Aχe^{−i⟪q,·⟫})`.

This module provides those two objects (`…Gen`, for "genuine"), and the mode contents built from
them.  `boxTauDag` (the corpus one) is already genuine: `g` is supported in `A`, so the factor
`g(x_i)` already carries the indicator; `boxTauDagGen` makes that explicit and adds nothing.

**Use the `…Gen` objects for every general-box statement.**  The non-`Gen` ones in `BoxTau.lean`
must only be used at `A = acube ℓ`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The genuine D1 creation operator at a general box**: `a†(g)a₀` with `a₀` the box constant
mode `1_A/√|A|`, i.e. `(|A|)^{−1/2}Σ_i 1_A(x_i)g(x_i)∫_A Ψ(x_{i←z})dz`. -/
noncomputable def boxTauDagGen {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (g : EuclideanSpace ℝ (Fin 3) → ℝ) (Ψ : X N → ℝ) (x : X N) : ℝ :=
  (Real.sqrt volA)⁻¹ * ∑ i : Fin N,
    A.indicator (fun _ => (1 : ℝ)) (x i) * g (x i) * ∫ z in A, Ψ (Function.update x i z)

/-- **The genuine D1 annihilation operator at a general box**: `a₀†a(g)`, the genuine adjoint of
`boxTauDagGen` (the extra factor `1_A(x_i)` is the constant-mode factor at the created particle's
position). -/
noncomputable def boxTauAnnGen {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (g : EuclideanSpace ℝ (Fin 3) → ℝ) (Ψ : X N → ℝ) (x : X N) : ℝ :=
  (Real.sqrt volA)⁻¹ * ∑ i : Fin N,
    A.indicator (fun _ => (1 : ℝ)) (x i) * ∫ z in A, g z * Ψ (Function.update x i z)

/-- The `P`-content of the genuine box `τ`-operator at the mode `g`. -/
noncomputable def boxModePGen {N : ℕ} (a : ℝ) (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (g : EuclideanSpace ℝ (Fin 3) → ℝ) (Ψ : X N → ℝ) : ℝ :=
  ∫ x in abox N a, (boxTauAnnGen volA A g Ψ x) ^ 2

/-- The `R`-content of the genuine box `τ`-operator at the mode `g`. -/
noncomputable def boxModeRGen {N : ℕ} (a : ℝ) (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (g : EuclideanSpace ℝ (Fin 3) → ℝ) (Ψ : X N → ℝ) : ℝ :=
  ∫ x in abox N a, boxTauAnnGen volA A g Ψ x * boxTauDagGen volA A g Ψ x

/-- The `T`-content of the genuine box `τ`-operator at the mode `g`. -/
noncomputable def boxModeTGen {N : ℕ} (a : ℝ) (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (g : EuclideanSpace ℝ (Fin 3) → ℝ) (Ψ : X N → ℝ) : ℝ :=
  ∫ x in abox N a, (boxTauDagGen volA A g Ψ x) ^ 2

/-- The genuine real part of the mean-free windowed exponential on `A`:
`1_A(z)·(χ z cos⟪q,z⟫ − |A|⁻¹∫_A χ cos⟪q,·⟫)`. -/
noncomputable def boxWinModeReGen (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (χ : EuclideanSpace ℝ (Fin 3) → ℝ) (q z : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  A.indicator (fun _ => (1 : ℝ)) z
    * (χ z * Real.cos (inner ℝ q z)
        - volA⁻¹ * ∫ w in A, χ w * Real.cos (inner ℝ q w))

/-- The genuine imaginary part of the mean-free windowed exponential on `A`. -/
noncomputable def boxWinModeImGen (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (χ : EuclideanSpace ℝ (Fin 3) → ℝ) (q z : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  - (A.indicator (fun _ => (1 : ℝ)) z
      * (χ z * Real.sin (inner ℝ q z)
          - volA⁻¹ * ∫ w in A, χ w * Real.sin (inner ℝ q w)))

/-- The genuine windowed `q`-diagonal kinetic content at the box `A`. -/
noncomputable def boxWinModePGen {N : ℕ} (a volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (χ : EuclideanSpace ℝ (Fin 3) → ℝ) (Ψ : X N → ℝ)
    (q : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  boxModePGen a volA A (boxWinModeReGen volA A χ q) Ψ
    + boxModePGen a volA A (boxWinModeImGen volA A χ q) Ψ

/-- The genuine windowed pairing content at the box `A`. -/
noncomputable def boxWinModeRGen {N : ℕ} (a volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (χ : EuclideanSpace ℝ (Fin 3) → ℝ) (Ψ : X N → ℝ)
    (q : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  boxModeRGen a volA A (boxWinModeReGen volA A χ q) Ψ
    + boxModeRGen a volA A (boxWinModeImGen volA A χ q) Ψ

end Work.BoseFixB1
