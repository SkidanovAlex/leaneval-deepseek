import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.NeuFrac.bddBelow_trialSet
import Submission.Work.BoseKinLoc.NeuFrac.lamBox_subset_ball
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Word.fsT_nonneg` — the localised kinetic word `𝒯_u` is nonnegative

FS `eq:DefT` writes the localised kinetic operator as a **sum of four one-body pieces**

`𝒯_u = ½ε_T(dℓ)⁻²(−Δ^N_u)(−Δ^N_u+(dℓ)⁻²)⁻¹·Q_u + bℓ⁻²Q_u
        + bε_T(dℓ)⁻²Q_u 1_{(d⁻²ℓ⁻¹,∞)}(√−Δ)Q_u
        + Q_uχ_u{(1−ε_T)[√−Δ−½(sℓ)⁻¹]₊² + ε_T[√−Δ−½(dsℓ)⁻¹]₊²}χ_uQ_u`,

i.e. in the vocabulary of `Work.BoseKinLoc.Defs`,

`fsT ℓ d s εT b u ψ = neuWord ℓ d εT u ψ + gapWord ℓ b u ψ
                        + momWord ℓ d εT b u ψ + mainWord ℓ d s εT u ψ`.

The last three words are nonnegative for the elementary reason that they are products of a
nonnegative prefactor with an integral of squares (`Defs.gapWord_nonneg`, `Defs.momWord_nonneg`,
`Defs.mainWord_nonneg`).  The point of this file is the first word, whose prefactor
`½ε_T(dℓ)⁻²` is nonnegative but whose factor is the **variational infimum**

`neuFrac ℓ a² u φ = inf_g [ ‖φ‖²_Λ − 2a²⟨φ,g⟩_Λ + a²(‖∇g‖²_Λ + a²‖g‖²_Λ) ]`,  `Λ = Λ(u)`,

over globally smooth compactly supported trials `g`.  We show `0 ≤ neuFrac ℓ a² u φ` for every
`a² ≥ 0` and every `φ` whose **square is integrable on the box** `Λ`.

## The mathematics (one line)

For every trial `g`, *completing the square under the box integral*,

`∫_Λ φ² − 2a²∫_Λ φg + (a²)²∫_Λ g² = ∫_Λ (φ − a²g)² ≥ 0`,

and the kinetic piece `a²Σ_k∫_Λ (∂_kg)²` only adds to this, so every member of the defining set
is `≥ 0`; the set is nonempty (`g = 0`), whence `0 ≤ sInf`.  No spectral theory is used: the
"Neumann" content of `neuFrac_le_box`-type statements is *not* needed here, only that the two
mass terms combine into a square — this is where the inequality is much cheaper than the sharp
resolvent identity.

Integrability of `φ²` on `Λ` is what makes the completion of the square legitimate
(`integral_sq_sub_sq`); for the application `φ = Q_uψ` with `ψ` smooth of compact support it is
automatic, `Q_uψ` being continuous and `Λ` lying in a compact ball
(`NeuFrac.lamBox_subset_closedBall`).

## Contents

* `neuFrac_nonneg_of_integrableSq` — the infimum is `≥ 0`;
* `fsT_nonneg` — the requested statement.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Word

set_option linter.unusedVariables false

/-- **The box Neumann fraction is nonnegative.**  If `a² ≥ 0` and `φ` is square integrable on
the moving box `Λ(u)`, then every value of the defining trial functional is `≥ 0`, so the
infimum `neuFrac ℓ a² u φ` is `≥ 0`.

The proof is the elementary completing of the square: for a smooth compactly supported trial
`g`, `∫_Λ φ² − 2a²∫_Λ φg + a²(Σ_k∫_Λ(∂_kg)² + a²∫_Λ g²) = ∫_Λ(φ − a²g)² + a²Σ_k∫_Λ(∂_kg)²`. -/
theorem neuFrac_nonneg_of_integrableSq {ℓ a2 : ℝ} (ha2 : 0 ≤ a2)
    (u : EuclideanSpace ℝ (Fin 3)) {φ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hφ : MeasureTheory.Integrable (fun z => (φ z) ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
        (Work.BoseKinLoc.lamBox ℓ u))) :
    0 ≤ Work.BoseKinLoc.neuFrac ℓ a2 u φ := by
  unfold Work.BoseKinLoc.neuFrac
  -- the defining trial set is nonempty: the zero trial is admissible
  refine le_csInf ⟨_, (0 : EuclideanSpace ℝ (Fin 3) → ℝ), contDiff_const,
    HasCompactSupport.zero, rfl⟩ ?_
  -- and every member is `≥ 0` by completing the square
  rintro c ⟨g, hg, hgs, hcval⟩
  rw [hcval]
  set Λ := Work.BoseKinLoc.lamBox ℓ u with hΛ
  have hAint : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) => (φ z) ^ 2)
      (MeasureTheory.volume.restrict Λ) := by
    simpa only [hΛ] using hφ
  have hDint : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) => (g z) ^ 2)
      (MeasureTheory.volume.restrict Λ) :=
    Work.BoseKinLoc.NeuFrac.integrableOn_sq_of_contDiff hg hgs u
  have hA_nn : 0 ≤ ∫ z in Λ, (φ z) ^ 2 := integral_nonneg (fun z => sq_nonneg _)
  have hD_nn : 0 ≤ ∫ z in Λ, (g z) ^ 2 := integral_nonneg (fun z => sq_nonneg _)
  have hK_nn : 0 ≤ ∑ k : Fin 3, ∫ z in Λ,
      (fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)) ^ 2 :=
    Finset.sum_nonneg (fun k _ => integral_nonneg (fun z => sq_nonneg _))
  -- the completed square
  have key : 0 ≤ (∫ z in Λ, (φ z) ^ 2) - 2 * a2 * (∫ z in Λ, φ z * g z)
      + a2 ^ 2 * (∫ z in Λ, (g z) ^ 2) := by
    by_cases hint : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) => φ z * g z)
        (MeasureTheory.volume.restrict Λ)
    · rw [Work.BoseKinLoc.NeuFrac.integral_sq_sub_sq hAint hint hDint]
      exact integral_nonneg (fun z => sq_nonneg _)
    · rw [integral_undef hint]
      nlinarith [hA_nn, hD_nn, ha2, sq_nonneg a2]
  -- the kinetic term `a²Σ_k∫(∂_kg)²` absorbs the `a²·a²∫g²` correction
  have hle : a2 ^ 2 * (∫ z in Λ, (g z) ^ 2)
      ≤ a2 * ((∑ k : Fin 3, ∫ z in Λ,
            (fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)) ^ 2)
          + a2 * (∫ z in Λ, (g z) ^ 2)) := by
    have hmul : a2 * ((∑ k : Fin 3, ∫ z in Λ,
            (fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)) ^ 2)
          + a2 * (∫ z in Λ, (g z) ^ 2))
        = a2 * (∑ k : Fin 3, ∫ z in Λ,
              (fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)) ^ 2)
          + a2 * (a2 * (∫ z in Λ, (g z) ^ 2)) := by ring
    rw [hmul]
    nlinarith [mul_nonneg ha2 hK_nn]
  linarith [key, hle]

/-- The localised kinetic word `𝒯_u` of FS `eq:DefT` is nonnegative: it is the sum of the four
nonnegative pieces, the first of which (`neuWord`) is nonnegative because the box Neumann
fraction `neuFrac` of the mean-free state `Q_uψ` is nonnegative
(`neuFrac_nonneg_of_integrableSq`), and the remaining three by
`Defs.gapWord_nonneg`, `Defs.momWord_nonneg`, `Defs.mainWord_nonneg`. -/
theorem fsT_nonneg {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hs : 0 < s)
    (hεT : 0 ≤ εT) (hεT1 : εT ≤ 1) (hb : 0 ≤ b) (u : EuclideanSpace ℝ (Fin 3))
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    0 ≤ Work.BoseKinLoc.fsT ℓ d s εT b u ψ := by
  have hdℓ : 0 < d * ℓ := mul_pos hd hℓ
  -- `Q_uψ = ψ − (box mean)` is continuous, hence square integrable on the (bounded) box
  have hcont : Continuous (Work.BoseKinLoc.Qfree ℓ u ψ) :=
    hψ.continuous.sub continuous_const
  have hI : MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) => (Work.BoseKinLoc.Qfree ℓ u ψ z) ^ 2)
      (MeasureTheory.volume.restrict (Work.BoseKinLoc.lamBox ℓ u)) :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall (ℓ • u) (2 * (|ℓ| + 1)))
      (hcont.pow 2).continuousOn).mono_set
        (Work.BoseKinLoc.NeuFrac.lamBox_subset_closedBall ℓ u)
  -- the four words
  have hneu : 0 ≤ Work.BoseKinLoc.neuWord ℓ d εT u ψ := by
    have ha2 : 0 ≤ (d * ℓ) ^ (-2 : ℤ) := zpow_nonneg hdℓ.le _
    have hn := neuFrac_nonneg_of_integrableSq (ℓ := ℓ)
      (a2 := (d * ℓ) ^ (-2 : ℤ)) ha2 u hI
    unfold Work.BoseKinLoc.neuWord
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hεT) ha2) hn
  have hgap : 0 ≤ Work.BoseKinLoc.gapWord ℓ b u ψ :=
    Work.BoseKinLoc.gapWord_nonneg hb hℓ.le u ψ
  have hmom : 0 ≤ Work.BoseKinLoc.momWord ℓ d εT b u ψ :=
    Work.BoseKinLoc.momWord_nonneg hb hεT hdℓ.le u ψ
  have hmain : 0 ≤ Work.BoseKinLoc.mainWord ℓ d s εT u ψ :=
    Work.BoseKinLoc.mainWord_nonneg hεT hεT1 u ψ
  rw [Work.BoseKinLoc.fsT_eq_sum]
  linarith

end Work.BoseKinLoc.Word
