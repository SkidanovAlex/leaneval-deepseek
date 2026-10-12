import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BoxD1Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.BoxD1Pair` — the box pair-density objects of the D1 chain

The box analogues of the corpus's `pairSlot`/`pairMean`/`pairFibreFun`/`pairFibreDens`
(`Submission.Work.SmallBoxPairIdent`, `Submission.Work.SmallBoxPairRelDecomp`,
`Submission.Work.SmallBoxPairMomentum`), with `acube ℓ ↦ A`, `chiScale ℓ ↦ χ` (a window
vanishing off `A`), `ℓ³ ↦ volA`, and the genuine box projections `boxPInd`/`boxQInd`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- The `(y,z)`-slot factor of the peeled box pair integrand (box `pairSlot`). -/
noncomputable def boxPairSlot {N : ℕ} (A : Set (EuclideanSpace ℝ (Fin 3)))
    (G : Submission.BoseGases.X (N + 2) → ℝ)
    (g g' : EuclideanSpace ℝ (Fin 3) → ℂ) (i : Fin (N + 2)) (j' : Fin (N + 1))
    (r2 : Submission.BoseGases.X N) : ℂ :=
  ∫ y in A, ∫ z in A, g y * g' z * ((G (Submission.BoseGases.ins2 i j' y z r2)) : ℂ)

/-- The `(u,w)`-slot mean of the peeled box pair integrand (box `pairMean`). -/
noncomputable def boxPairMean {N : ℕ} (A : Set (EuclideanSpace ℝ (Fin 3)))
    (G : Submission.BoseGases.X (N + 2) → ℝ) (i : Fin (N + 2)) (j' : Fin (N + 1))
    (r2 : Submission.BoseGases.X N) : ℂ :=
  ∫ y in A, ∫ z in A, ((G (Submission.BoseGases.ins2 i j' y z r2)) : ℂ)

/-- The peeled box pair fibre `P_iP_jΦ·Q_jQ_iΦ` in the relative slots (`pairFibreFun` at the
box).  Both factors are evaluated at the doubly-inserted configuration so that the box
indicators carried by `boxPInd`/`boxQInd` are retained. -/
noncomputable def boxPairFibreFun {N : ℕ} (volA ℓ : ℝ)
    (A : Set (EuclideanSpace ℝ (Fin 3))) (Φ : Submission.BoseGases.X (N + 2) → ℝ)
    (i j : Fin (N + 2)) (y z : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  if h : i ≠ j then
    ∫ r2 in Submission.BoseGases.abox N ℓ,
      (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ)
          (Submission.BoseGases.ins2 i (Submission.BoseGases.sucAboveInv i j h) y z r2))
        * (Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ)
            (Submission.BoseGases.ins2 i (Submission.BoseGases.sucAboveInv i j h) y z r2))
  else 0

/-- The box pair density in the relative coordinate `u = y − z` (`pairFibreDens` at the box). -/
noncomputable def boxPairDens {N : ℕ} (volA ℓ : ℝ)
    (A : Set (EuclideanSpace ℝ (Fin 3))) (χ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : Submission.BoseGases.X (N + 2) → ℝ) (i j : Fin (N + 2))
    (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∫ z in A, χ (z + u) * χ z * boxPairFibreFun volA ℓ A Φ i j (z + u) z

/-- The summed box pair density over the distinct ordered pairs. -/
noncomputable def boxPairDensSum {N : ℕ} (volA ℓ : ℝ)
    (A : Set (EuclideanSpace ℝ (Fin 3))) (χ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : Submission.BoseGases.X (N + 2) → ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∑ p ∈ Submission.BoseGases.pairSet (N + 2), boxPairDens volA ℓ A χ Φ p.1 p.2 u

/-- The momentum-space box pair content at `q`: the sum over ordered pairs of the double
`A`-integral of `χ(y)χ(z)e^{i⟪q,y−z⟫}` against the peeled pair fibre — the position-space form
of `𝓕(boxPairDensSum)(−(2π)⁻¹q)`. -/
noncomputable def boxPairDensFourier {N : ℕ} (volA ℓ : ℝ)
    (A : Set (EuclideanSpace ℝ (Fin 3))) (χ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : Submission.BoseGases.X (N + 2) → ℝ) (q : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  ∑ p ∈ Submission.BoseGases.pairSet (N + 2),
    ∫ y in A, ∫ z in A,
      (χ y : ℂ) * (χ z : ℂ)
        * Complex.exp (Complex.I * ((inner ℝ q (y - z) : ℝ) : ℂ))
        * ((boxPairFibreFun volA ℓ A Φ p.1 p.2 y z : ℝ) : ℂ)

end Work.BoseFixB1
