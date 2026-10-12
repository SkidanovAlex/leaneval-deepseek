import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBoxFock.bridge_defs` — the box → model compression `Φ ↦ Ψ`

The dictionary half (**BF3b**) of `box_to_model` needs a map from box states
`Φ : L²_sym(Λⁿ)` to model vectors `Ψ : RealFock m`.  The one-particle space of the
model is `Fin m → ℝ` with the hand-rolled pairing `Work.BoseB4.gram`, and by
`Work.BoseB4.ModeFock` its modes are the coordinate vectors of the *physical*
one-particle vectors in a real-orthonormal family
`e : Fin m → ℝ³ → ℂ` (`Work.BoseK15.corpusBox.realIP (e l) (e l') = δ_{ll'}`
— the realified `L²(ℂ)` inner product; the family is produced by
`Work.BoseBoxFock.modeONB` and satisfies `Σ_l (f k l) • e l = ℓ^{-3/2}qVec ...`).

Given such a family and a box state `Φ`, define

* `modeProd e α` — the (complex) symmetric mode product
  `Σ_{σ : modeMult σ = α} ∏_i e (σ i) (x i)` for a multi-index `α` of total degree `n`;
* `boxCoeff e n ℓ Φ α = ⟨modeProd e α, Φ⟩ / √(n!)`, the coefficient in the sense of
  `RealFock m`'s monomial convention (`bomb`-normalisation);
* `boxCompress e n ℓ Φ = Σ_{|α| = n} (boxCoeff α) • x^α`, the model vector.

The normalisation is the one of `BRIDGE_DESIGN.md` §2.2: with `M_α := modeProd e α`,
`Re⟪M_α, M_β⟫ = δ_{αβ} n!/α!` (`modeProd_realIP`), so the `bomb`-norm of the
compression is `Σ_α (boxCoeff α)² α! = Σ_α ⟪M_α,Φ⟫² α!/n! ≤ ‖Φ‖²` — the contraction
`bomb Ψ Ψ ≤ normB Φ` used by the arithmetic of the assembly.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

open _root_.BoseGases Submission.BoseGases Work.BoseBox Work.UBB

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The `n`-body analogue of `Work.BoseK15.corpusBox.realIP`: the real part of the
`L²(Λⁿ)` inner product of complex-valued functions on `X n`. -/
noncomputable def realIPn (n : ℕ) (f g : X n → ℂ) : ℝ :=
  ∫ x : X n, ((starRingEnd ℂ) (f x) * g x).re

/-- The **mode multiplicity** of a labelling `σ : Fin n → Fin m`: the occupation
multi-index `α` with `α l = #{i | σ i = l}`. -/
noncomputable def modeMult {m n : ℕ} (σ : Fin n → Fin m) : Fin m →₀ ℕ :=
  ∑ k : Fin m, Finsupp.single k ((Finset.univ.filter fun i => σ i = k).card)

/-- The **symmetric mode product** of the multi-index `α` in the mode family `e`:
`Σ_{σ : Fin n → Fin m, modeMult σ = α} ∏_i e (σ i) (x i)`.  (This is `modeExpand`
of `Work.BoseFixR.SecQuantBox` at the coefficient `Finsupp.single α 1`.) -/
noncomputable def modeProd {m : ℕ} (e : Fin m → ℝ³ → ℂ) (n : ℕ) (α : Fin m →₀ ℕ)
    (x : X n) : ℂ :=
  ∑ σ : Fin n → Fin m, (if modeMult σ = α then (1 : ℂ) else 0) * ∏ i : Fin n, e (σ i) (x i)

/-- The real symmetric mode expansion of a coefficient family:
`Σ_{|α| = n} c α · (modeProd e α x).re`. -/
noncomputable def modeExpandRe {m : ℕ} (e : Fin m → ℝ³ → ℂ) (n : ℕ)
    (c : (Fin m →₀ ℕ) →₀ ℝ) (x : X n) : ℝ :=
  ∑ α ∈ Finset.finsuppAntidiag (Finset.univ : Finset (Fin m)) n,
    c α * (modeProd e n α x).re

/-- The **model coefficient** of the box state `Φ` at the multi-index `α`:
`⟪modeProd e α, Φ⟫ / √(n!)`, the coefficient with respect to the normalised
monomial `x^α/√(α!)` of `RealFock m` (see `BRIDGE_DESIGN.md` §2.2). -/
noncomputable def boxCoeff {m : ℕ} (e : Fin m → ℝ³ → ℂ) (n : ℕ) (ℓ : ℝ)
    (Φ : X n → ℝ) (α : Fin m →₀ ℕ) : ℝ :=
  (∫ x in abox n ℓ, (modeProd e n α x).re * Φ x) / Real.sqrt (n.factorial : ℝ)

/-- **The compression of a box state to the model** (`BF3b`): the model vector with
the coefficients `boxCoeff`, i.e. `Ψ = Σ_{|α| = n} boxCoeff α • x^α`. -/
noncomputable def boxCompress {m : ℕ} (e : Fin m → ℝ³ → ℂ) (n : ℕ) (ℓ : ℝ)
    (Φ : X n → ℝ) : Work.BoseB4.RealFock m :=
  ∑ α ∈ Finset.finsuppAntidiag (Finset.univ : Finset (Fin m)) n,
    Finsupp.single α (boxCoeff e n ℓ Φ α)

end Work.BoseBoxFock
