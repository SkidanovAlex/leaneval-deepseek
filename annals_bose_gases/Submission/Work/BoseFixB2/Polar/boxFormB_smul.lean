import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.Defs
import Submission.Work.BoseKinLoc.Word.fsT_const_mul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB2.Polar.boxFormB_smul` — the box word is `2`-homogeneous

FS's box-restricted word `boxFormB n v g ℓ μ d s εT b` (the quadratic form of the box
Hamiltonian `H_Λ(μ)` on `L²(Λ^n)`, see `Work.BoseKinLoc.Defs`) is a **quadratic form** in the
state: scaling the state, `Φ ↦ t·Φ`, scales the word by `t²`,

    `boxFormB … (fun x => t * Φ x) = t² · boxFormB … Φ`.

Together with the parallelogram identity (`Polar.boxFormB_parallelogram`) this is what makes
the polarisation `polB` (`Work.BoseFixB2.polB`, FS §6 / `lem:LocMatrices`) a genuine symmetric
bilinear form: `4·polB Φ Ψ = wordB (Φ+Ψ) − wordB (Φ−Ψ)`.

## The proof

`boxFormB = kinFormB + ∫_{abox} Φ²·potWordU` (`Work.BoseKinLoc.boxFormB`), and the two parts
scale separately:

* the **potential part** `∫_{x∈abox} (Φ x)²·potWordU x`: the potential profile `potWordU` does
  not depend on the state, so the integrand of `t·Φ` is pointwise `t²` times that of `Φ` and
  `MeasureTheory.integral_const_mul` pulls the constant out of the box integral;
* the **kinetic part** `kinFormB = ℓ⁻³ Σᵢ ∫_{x∈abox} θ(xᵢ)·fsT(fibreᵢ Φ x)`
  (`Work.BoseKinLoc.kinFormB`): the slot-`i` fibre `fibreᵢ Φ x = z ↦ Φ(x with xᵢ = z)` is
  linear in the state, and FS `eq:DefT`'s one-body localised kinetic word `fsT` is
  `2`-homogeneous (`fsT_const_mul` below), so the integrand scales by `t²`; then
  `MeasureTheory.integral_const_mul` (for each slot, with respect to the restricted measure
  `volume.restrict (abox n ℓ)`), `Finset.mul_sum` (for the `n` slots) and one `ring` step
  (for the `ℓ⁻³`) finish.

## The four summands of `fsT` (unconditional `2`-homogeneity)

`fsT_const_mul` is the corpus's `Work.BoseKinLoc.Word.fsT_const_mul` without its (unused)
smoothness and compact-support hypotheses, which is what the present application needs — the
slot fibres of an `n`-body state are smooth at best, never compactly supported in the slot
variable.  Its four ingredients are the verified corpus lemmas

* `Work.BoseKinLoc.NeuFrac.neuFrac_const_mul` — the `sInf` of the Neumann-resolvent trial
  functional (the only non-elementary step; its `0 ≤ a²` hypothesis covers the degenerate
  `t = 0` case, where the trial values are nonnegative and `0` is attained);
* `Work.BoseKinLoc.Word.FsTAux.gapBare_const_mul` — the box-mean-free mass `∫(Q_uψ)²`;
* `Work.BoseKinLoc.Word.momForm_const_mul` — the large-momentum form (Fourier transform);
* `Work.BoseKinLoc.Word.bsOneBody_const_mul` — the windowed `[√−Δ−c]₊²` word.

All of them are unconditional identities of Bochner integrals.  Consequently **no** hypothesis
on the state, and in particular neither `hℓ` nor `hΦ` of the requested statement, is used: they
are carried only so that the statement is verbatim the one requested.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB2.Polar

open Submission.BoseGases Work.BoseKinLoc

set_option autoImplicit false
set_option linter.unusedVariables false

namespace SmulAux

/-! ## 1. The one-body localised kinetic word `fsT` is `2`-homogeneous -/

/-- FS `eq:DefT`'s one-body localised kinetic word `𝒯_u` is homogeneous of degree `2` in the
state.  (The same proof as `Work.BoseKinLoc.Word.fsT_const_mul`, whose auxiliary smoothness
and support hypotheses are not used; here there is no hypothesis at all.) -/
theorem fsT_const_mul {ℓ d s εT b c : ℝ} (u : EuclideanSpace ℝ (Fin 3))
    (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) :
    Work.BoseKinLoc.fsT ℓ d s εT b u (fun z => c * ψ z)
      = c ^ 2 * Work.BoseKinLoc.fsT ℓ d s εT b u ψ := by
  have ha2 : 0 ≤ (d * ℓ) ^ (-2 : ℤ) := by
    rw [zpow_neg]
    exact inv_nonneg.mpr (sq_nonneg _)
  have hQ : Work.BoseKinLoc.Qfree ℓ u (fun z => c * ψ z)
      = fun z => c * Work.BoseKinLoc.Qfree ℓ u ψ z :=
    Work.BoseKinLoc.Word.FsTAux.Qfree_const_mul ℓ u c ψ
  have hgap : Work.BoseKinLoc.gapWord ℓ b u (fun z => c * ψ z)
      = c ^ 2 * Work.BoseKinLoc.gapWord ℓ b u ψ := by
    unfold Work.BoseKinLoc.gapWord
    rw [Work.BoseKinLoc.Word.FsTAux.gapBare_const_mul]
    ring
  have hmom : Work.BoseKinLoc.momWord ℓ d εT b u (fun z => c * ψ z)
      = c ^ 2 * Work.BoseKinLoc.momWord ℓ d εT b u ψ := by
    unfold Work.BoseKinLoc.momWord
    rw [Work.BoseKinLoc.Word.momForm_const_mul u c ψ]
    ring
  have hmain : Work.BoseKinLoc.mainWord ℓ d s εT u (fun z => c * ψ z)
      = c ^ 2 * Work.BoseKinLoc.mainWord ℓ d s εT u ψ := by
    unfold Work.BoseKinLoc.mainWord
    rw [Work.BoseKinLoc.Word.bsOneBody_const_mul (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹)) u c ψ,
        Work.BoseKinLoc.Word.bsOneBody_const_mul (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹)) u c ψ]
    ring
  have hneu : Work.BoseKinLoc.neuWord ℓ d εT u (fun z => c * ψ z)
      = c ^ 2 * Work.BoseKinLoc.neuWord ℓ d εT u ψ := by
    unfold Work.BoseKinLoc.neuWord
    rw [hQ, Work.BoseKinLoc.NeuFrac.neuFrac_const_mul ha2 u (Work.BoseKinLoc.Qfree ℓ u ψ)]
    ring
  rw [Work.BoseKinLoc.fsT_eq_sum, Work.BoseKinLoc.fsT_eq_sum, hneu, hgap, hmom, hmain]
  ring

/-! ## 2. The slot fibre is linear in the state -/

/-- The slot-`i` fibre of a scaled state is the scaled fibre. -/
lemma fibre_const_mul (N : ℕ) (i : Fin N) (c : ℝ) (Φ : X N → ℝ) (x : X N) :
    Work.BoseKinLoc.fibre N i (fun y => c * Φ y) x
      = fun z => c * Work.BoseKinLoc.fibre N i Φ x z := rfl

/-! ## 3. The box-restricted kinetic and potential parts -/

/-- The box-restricted kinetic part of FS `eq:Def_HB` is `2`-homogeneous in the state. -/
theorem kinFormB_const_mul (N : ℕ) (ℓ d s εT b c : ℝ) (Φ : X N → ℝ) :
    Work.BoseKinLoc.kinFormB N ℓ d s εT b (fun x => c * Φ x)
      = c ^ 2 * Work.BoseKinLoc.kinFormB N ℓ d s εT b Φ := by
  have hterm : ∀ i : Fin N,
      (∫ x in abox N ℓ,
          Work.BoseKinLoc.indU ℓ 0 (x i)
            * Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre N i (fun y => c * Φ y) x))
        = c ^ 2 * ∫ x in abox N ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x i)
              * Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre N i Φ x) := by
    intro i
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [fibre_const_mul N i c Φ x, fsT_const_mul (u := 0)]
    ring
  have hsum : (∑ i : Fin N,
        (∫ x in abox N ℓ,
          Work.BoseKinLoc.indU ℓ 0 (x i)
            * Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre N i (fun y => c * Φ y) x)))
      = c ^ 2 * ∑ i : Fin N,
          (∫ x in abox N ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x i)
              * Work.BoseKinLoc.fsT ℓ d s εT b 0 (Work.BoseKinLoc.fibre N i Φ x)) := by
    rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum]
  unfold Work.BoseKinLoc.kinFormB
  rw [hsum]
  ring

/-- The box-restricted potential part `∫_{abox}(Φ x)²·potWordU x` is `2`-homogeneous in the
state (the potential profile does not depend on the state). -/
theorem potIntB_const_mul (N : ℕ) (v g : EuclideanSpace ℝ (Fin 3) → ℝ) (ℓ μ c : ℝ)
    (Φ : X N → ℝ) :
    (∫ x in abox N ℓ, (c * Φ x) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ 0 x)
      = c ^ 2 * ∫ x in abox N ℓ, (Φ x) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ 0 x := by
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  ring

end SmulAux

/-! ## 4. The box word -/

/-- **FS's box-restricted word is a quadratic form**: `boxFormB n v g ℓ μ d s εT b` is
`2`-homogeneous in the state. -/
theorem boxFormB_smul {v g : EuclideanSpace ℝ (Fin 3) → ℝ} {ℓ μ d s εT b t : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) : Work.BoseKinLoc.boxFormB n v g ℓ μ d s εT b (fun x => t * Φ x) = t ^ 2 * Work.BoseKinLoc.boxFormB n v g ℓ μ d s εT b Φ := by
  have hk := SmulAux.kinFormB_const_mul n ℓ d s εT b t Φ
  have hp := SmulAux.potIntB_const_mul n v g ℓ μ t Φ
  show Work.BoseKinLoc.kinFormB n ℓ d s εT b (fun x => t * Φ x)
      + (∫ x in Submission.BoseGases.abox n ℓ,
          (t * Φ x) ^ 2 * Work.BoseKinLoc.potWordU n v g ℓ μ 0 x)
      = t ^ 2 * (Work.BoseKinLoc.kinFormB n ℓ d s εT b Φ
          + ∫ x in Submission.BoseGases.abox n ℓ,
              (Φ x) ^ 2 * Work.BoseKinLoc.potWordU n v g ℓ μ 0 x)
  rw [hk, hp]
  ring

end Work.BoseFixB2.Polar
