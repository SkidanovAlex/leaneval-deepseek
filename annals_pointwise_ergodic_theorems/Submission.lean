/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/

import ChallengeDeps
import Submission.ShiftHoleClosed
/-!
# Main Statements from Pointwise ergodic theorems for non-conventional bilinear polynomial averages

We formalise the statements of the main results from B. Krause, M. Mirek, and T. Tao,
`Pointwise ergodic theorems for non-conventional bilinear polynomial averages`,
Annals of Math, 195 (3) 2022.

The development is organised as follows.

* `Submission.Basic`, `Submission.Variational`, `Submission.VarNorm`, `Submission.VarSums`,
  `Submission.VarPrep` and `Submission.VarCoeff` contain the elementary theory of the averaging
  operator `A` and of the variational norm `V^r` (measurability, subadditivity, homogeneity,
  the "prepend zeros" estimate, the `ℓ¹` bound for the `L^r` norm, and the weighted-series
  estimate controlling the telescoping error term).
* `Submission.Transfer` and `Submission.Half` contain the dyadic block decomposition of the
  Cesàro average and the upper-half average `Ã_N`.
* `Submission.Telescope` proves the pointwise dyadic telescoping bound of Krause--Mirek--Tao,
  Proposition 3.1 (iii): the variational norm of the averages `A T (a n) X P f g` is bounded by
  the weighted sum of the variational norms of the halved averages at the rescaled scales
  `a n / 2^k`, plus a `∑_n ⌊a n⌋⁻¹ (log₂ ⌊a n⌋ + 1)` error.
* `Submission.Reduction` (with `Submission.AEMeasurable`, `Submission.LpMinkowski`,
  `Submission.LogSum` and the shared commons) turns this pointwise bound into the statement
  `VarEstHalf → VarEst`: the variational estimate for the halved averages implies the long
  variational estimate (Theorem 1.17 (iv)) for the full averages.
* `Submission.Reductions` formalises the rest of Proposition 3.1: the long variational estimate
  implies the maximal estimate (iii), the pointwise convergence (ii) and the norm convergence
  (i).  In this file we assemble the statements of the challenge and use those reductions.
* `Submission.VarClamp` contains the clamping lemmas for the variational norm (the variational
  norm of the sequence `n ↦ b (min n K)` increases to that of `b`) and the monotone-convergence
  form of `eLpNorm` needed to deduce an estimate for a supremum from estimates for a monotone
  family.
* `Submission.Transference` formalises the Calderón transference principle (Proposition 3.1
  (ii)): `varEst_of_varEstZ` deduces the long variational estimate for an arbitrary
  measure-preserving system `(X, μ, T)` from the corresponding estimate `VarEstZ` for the
  integer shift model `(ℤ, μ_ℤ, T_ℤ)`.  The proof has two halves: the fibre-by-fibre reduction
  from `ℤ` to the product system `(X × ℤ, μ × μ_ℤ, id × T_ℤ)` (`eLpNorm_prodSys_le`, via
  Tonelli's theorem and Hölder's inequality), and the testing-function argument
  (`prodVar_testFun_lower_lp` together with the fibre identity `A_prodSys_testFun_eq` and the
  normalisation `eLpNorm_testFun`) which pushes the product-system estimate back down to `X`.

* `Submission.TelescopeR` records the pointwise dyadic telescoping bound with the variational
  exponent `r` left general (it is `Submission.Telescope.variationalNorm_A_le` for `r = 3`), and
  `Submission.ReductionR` records the corresponding `Lp`-level assembly
  (`VarEstHalfR → VarEstR` for any `r ≥ 1`); the latter is used in `Submission.ShiftHole` to pass
  from the paper's estimate for the *halved* averages (Theorem "end-var") to the long estimate
  `VarEstZ` at the general exponent `r` required by Theorem 1.17(iv).

* `Submission.ShiftHole` isolates the *only* remaining gap: the variational ergodic theorem on
  the integers (Krause--Mirek--Tao, Theorem "end-var"), stated for the *upper-half* averages at
  *finite* `λ`-lacunary sets of scales, with a constant independent of the set (`VarEstHalfFin`);
  the variational estimate for an infinite `Λ`-lacunary sequence (`VarEstHalfR`) is then derived
  from it by clamping and monotone convergence, and the long variational estimate `VarEstZ` by the
  telescoping argument of Proposition 3.1 (iii)
  (`Submission.TelescopeR`/`Submission.ReductionR`).  The file also contains the elementary
  almost-everywhere machinery (the `T`-orbit of a null set is null, and the averages only see the
  a.e. class of `f` and `g`) that lets `Lᵖ`-classes be replaced by measurable representatives.

Everything in the paper *except* the integer-shift estimate is therefore proved: in
`theorem_1_17_iv` the measurable representatives of `f` and `g` are introduced, the
integer-shift estimate `VarEstZ` (with the Hölder exponent `p⁻¹ = p₁⁻¹ + p₂⁻¹` determined by
`p₁, p₂`) is obtained from `Submission.ShiftHole.exists_varEstZ_Cv` via the definition of
`Cᵢᵥ` below, and the Calderón transference principle
`Submission.Transference.varEst_of_varEstZ` then produces the estimate for `(X, μ, T)`.  The
single `sorry` of the development sits in `Submission.ShiftHole.exists_varEstHalfFin_Cv`
(Krause--Mirek--Tao, Theorem "end-var"), the paper's main analytic estimate for the halved
averages at finite `λ`-lacunary sets of scales.

The remaining gap is therefore exactly the paper's Theorem "end-var" for the halved averages
`Ã_N` at *finite* `λ`-lacunary sets of scales, formulated as `exists_varEstHalfFin_Cv` (uniformly
in the number of scales).  Everything else is formalised: the passage from finite sets of scales
to infinite `Λ`-lacunary sequences (the monotone-convergence step of Proposition 3.1 (i), via
clamping), the passage from the halved to the long averages (Proposition 3.1 (iii), formalised at
the general exponent `r ≥ 1` in `Submission.TelescopeR`/`Submission.ReductionR` and assembled in
`Submission.ShiftHole.varEstZ_of_varEstHalf`), Calderón transference (Proposition 3.1 (ii)) and
the derivation of the maximal, pointwise and `Lᵖ` statements from the long variational estimate.

The exponent in the halved estimate is `p := (p₁⁻¹ + p₂⁻¹)⁻¹`, the one determined by the Hölder
relation of Theorem 1.17; `theorem_1_17_iv` converts the hypothesis
`hp₁p₂p : p₁⁻¹ + p₂⁻¹ = p⁻¹` into this normalisation.

## A note on imports

`Solution.lean` is compared with `Challenge.lean` *syntactically* by the comparator, so the
statements of the theorems must elaborate to exactly the same terms in both modules.  Importing
more of Mathlib into the submission can perturb instance resolution (for example
`Mathlib.Analysis.CStarAlgebra.Classes` changes the `NormedCommRing ℂ` instance, and
`Mathlib.Order.CompletePartialOrder` changes the `SupSet ℝ≥0∞` instance), which makes the
statements of `Solution.lean` differ from those of `Challenge.lean`, and the comparator then
rejects the submission.  Hence:

* the imports of the submission are kept inside the closure of `ChallengeDeps`;
* `Submission/Basic.lean` restores the priority of `NormedField.toNormedCommRing` (needed
  because some commons lemmas used here import the C*-algebra hierarchy).

Please keep this constraint in mind when extending the development.
-/


namespace Submission

open _root_.PointwiseErgodicTheorems
set_option autoImplicit false

namespace PointwiseErgodicTheorems

open MeasureTheory Polynomial Finset Filter Topology

open scoped ENNReal NNReal PNat

/- We assume that `(X, μ, T)` is a Measure-preserving system. That is `(X, μ)` is a
`σ`-finite measure space, and `T : X → X` is an invertible bimeasurable map that is
measure preserving in the sense that `μ(T(E)) = μ(E)` for all measurable `E`.-/
variable {𝓧 : Type*} [σX : MeasurableSpace 𝓧] {μ : Measure 𝓧} [SigmaFinite μ]
  {T : 𝓧 ≃ᵐ 𝓧} (hT : MeasurePreserving T μ μ)

include hT

/- Let `P : ℤ[X]` be a polynomial with degree at least `2`. -/
variable {P : ℤ[X]} (hP : P.degree ≥ 2)

include hP

/- Let `p₁, p₂, p` be real numbers such that `1 < p₁, p₂ < ∞` and `p₁⁻¹ + p₂⁻¹ = p⁻¹ ≤ 1`. -/
variable {p₁ p₂ p : ℝ≥0∞} (h₁p₁ : 1 < p₁) (h₁p₂ : 1 < p₂) (h₂p₁ : p₁ < ∞) (h₂p₂ : p₂ < ∞)
  (hp₁p₂p : p₁⁻¹ + p₂⁻¹ = p⁻¹) (hp : p⁻¹ ≤ 1)

include h₁p₁ h₁p₂ h₂p₁ h₂p₂ hp₁p₂p hp

/-- The constant of Theorem 1.17 (iv).

The challenge leaves this constant unspecified (it is a `sorry` hole).  Following the reduction,
we define it to be ten times the constant of the integer-shift variational estimate: the general
estimate follows from the integer-shift estimate with a gain of a factor `10` by Calderón
transference (`Submission.Transference.varEst_of_varEstZ`); see `theorem_1_17_iv` below.  The
integer-shift constant is itself extracted, via `Classical.choose`, from the integer-shift
long variational estimate `Submission.ShiftHole.exists_varEstZ_Cv`, which is *derived* here from
the paper's main analytic estimate (Theorem "end-var") for the halved averages at finite lacunary
sets of scales, the single remaining `sorry` of the submission,
`Submission.ShiftHole.exists_varEstHalfFin_Cv`. -/
noncomputable def Cᵢᵥ (P : ℤ[X]) (p₁ p₂ : ℝ≥0∞) (r Λ : ℝ≥0) : ℝ≥0 := 10 * CvShift P p₁ p₂ r Λ

/--
Statement of Theorem 1.17(iv) (Long variational ergodic theorem):

For any `r > 2` and `Λ > 1`, there exists a constant `C ≥ 0` such that for any `f ∈ Lᵖ₁(X)`,
`g ∈ Lᵖ₂(X)` and `Λ`-lacunary sequence `a` such that `1 ≤ a n` for all `n ∈ ℕ`,
`‖A T (a n) X P f g‖_{Lᵖ(X;Vʳ)} ≤ C ‖f‖_{Lᵖ₁(X)} ‖g‖_{Lᵖ₂(X)}`.
-/
theorem theorem_1_17_iv (r Λ : ℝ≥0) (hr : r > 2) (hΛ : Λ > 1) {f g : 𝓧 → ℂ}
    (hf : MemLp f p₁ μ) (hg : MemLp g p₂ μ) (a : ℕ → ℝ≥0) (ha : Lacunary Λ a) (ha' : ∀ n, 1 ≤ a n) :
    eLpNorm (fun x ↦ variationalNorm r fun n ↦ A T (a n) X P f g x) p μ ≤
      Cᵢᵥ P p₁ p₂ r Λ * ‖hf.toLp‖ₑ * ‖hg.toLp‖ₑ := by
  -- Replace `f, g` by measurable representatives; this does not change the averages a.e.
  obtain ⟨f', hf'm, hff'⟩ := hf.aemeasurable
  obtain ⟨g', hg'm, hgg'⟩ := hg.aemeasurable
  -- The hypotheses of the integer-shift estimate.
  have hcond : (P.degree ≥ 2) ∧ (1 < p₁) ∧ (1 < p₂) ∧ (p₁ < ∞) ∧ (p₂ < ∞) ∧
      (p₁⁻¹ + p₂⁻¹ ≤ 1) ∧ (2 < r) :=
    ⟨hP, h₁p₁, h₁p₂, h₂p₁, h₂p₂, hp₁p₂p.le.trans hp, hr⟩
  -- The integer-shift estimate, at the Hölder exponent determined by `p₁, p₂`.
  have hZspec : VarEstZ P p₁ p₂ p r (CvShift P p₁ p₂ r) := by
    have h0 := varEstZ_CvShift P p₁ p₂ r hcond
    rwa [show (p₁⁻¹ + p₂⁻¹)⁻¹ = p from by rw [hp₁p₂p, inv_inv]] at h0
  -- Calderón transference to the arbitrary system `(X, μ, T)`.
  have hle := varEst_of_varEstZ (r := r)
    (le_trans (by norm_num : (1 : ℝ≥0) ≤ 2) (le_of_lt hr)) hZspec
    hT hΛ ha ha' hf'm hg'm
    (ne_zero_of_inv_add_eq h₁p₁ h₁p₂ hp₁p₂p)
    (ne_top_of_inv_add_eq h₂p₁ h₂p₂ hp₁p₂p)
    (one_le_of_inv_le_one hp) h₁p₁ h₂p₁.ne h₁p₂ h₂p₂.ne hp₁p₂p
  calc eLpNorm (fun x ↦ variationalNorm r fun n ↦ A T (a n) X P f g x) p μ
      = eLpNorm (fun x ↦ variationalNorm r fun n ↦ A T (a n) X P f' g' x) p μ :=
        eLpNorm_congr_ae (ae_variationalNorm_A_eq (r := r) hT hff' hgg')
    _ ≤ Cᵢᵥ P p₁ p₂ r Λ * eLpNorm f' p₁ μ * eLpNorm g' p₂ μ := hle
    _ = Cᵢᵥ P p₁ p₂ r Λ * ‖hf.toLp‖ₑ * ‖hg.toLp‖ₑ := by
        rw [eLpNorm_congr_ae hff'.symm, eLpNorm_congr_ae hgg'.symm,
          ← Lp.enorm_toLp hf, ← Lp.enorm_toLp hg]

/-- The long variational estimate of Theorem 1.17 (iv) is available for `r = 3` in the form used
by the reductions. -/
theorem variationalEstimate_of_theorem_1_17_iv :
    VarEst T μ P p₁ p₂ p (fun Λ => Cᵢᵥ P p₁ p₂ 3 Λ) := by
  intro f g hf hg a Λ hΛ hLac h1
  exact theorem_1_17_iv hT hP h₁p₁ h₁p₂ h₂p₁ h₂p₂ hp₁p₂p hp 3 Λ (by norm_num) hΛ hf hg a hLac h1

/-- The constant of Theorem 1.17 (iii). -/
noncomputable def Cᵢᵢᵢ (P : ℤ[X]) (p₁ p₂ : ℝ≥0∞) : ℝ≥0 := 2 * Cᵢᵥ P p₁ p₂ 3 (3 / 2)

/--
Statement of Theorem 1.17(i) (Mean ergodic theorem):

The averages `A T N X P f g` converge as `N → ∞` in `Lᵖ(X)` norm.
-/
theorem theorem_1_17_i {f g : 𝓧 → ℂ} (hf : MemLp f p₁ μ) (hg : MemLp g p₂ μ) :
    ∃ h : 𝓧 → ℂ, MemLp h p μ ∧
    Tendsto (fun N ↦ eLpNorm (A T N (X : ℤ[X]) P f g - h) p μ) atTop (𝓝 0) := by
  obtain ⟨h, hmem, _hae, hconv⟩ := exists_tendsto_eLpNorm_of_varEst (T := T) (μ := μ)
    (P := P) (p₁ := p₁) (p₂ := p₂) (p := p) (Cv := fun Λ => Cᵢᵥ P p₁ p₂ 3 Λ)
    (hT := hT)
    (hVar := variationalEstimate_of_theorem_1_17_iv hT hP h₁p₁ h₁p₂ h₂p₁ h₂p₂ hp₁p₂p hp)
    (hp0 := ne_zero_of_inv_add_eq h₁p₁ h₁p₂ hp₁p₂p)
    (hpT := ne_top_of_inv_add_eq h₂p₁ h₂p₂ hp₁p₂p) (hp1 := one_le_of_inv_le_one hp)
    (hp₁ne := h₂p₁.ne) (hp₂ne := h₂p₂.ne) (hf := hf) (hg := hg)
  exact ⟨h, hmem, hconv⟩

/--
Statement of Theorem 1.16(ii) (Pointwise ergodic theorem):

The averages `A T N X P f g` converge as `N → ∞` pointwise almost everywhere.
-/
theorem theorem_1_17_ii {f g : 𝓧 → ℂ} (hf : MemLp f p₁ μ) (hg : MemLp g p₂ μ) :
    ∃ h : 𝓧 → ℂ, MemLp h p μ ∧
    ∀ᵐ x ∂μ, Tendsto (fun N ↦ A T N (X : ℤ[X]) P f g x) atTop (𝓝 (h x)) := by
  obtain ⟨h, hmem, hae, _hconv⟩ := exists_tendsto_eLpNorm_of_varEst (T := T) (μ := μ)
    (P := P) (p₁ := p₁) (p₂ := p₂) (p := p) (Cv := fun Λ => Cᵢᵥ P p₁ p₂ 3 Λ)
    (hT := hT)
    (hVar := variationalEstimate_of_theorem_1_17_iv hT hP h₁p₁ h₁p₂ h₂p₁ h₂p₂ hp₁p₂p hp)
    (hp0 := ne_zero_of_inv_add_eq h₁p₁ h₁p₂ hp₁p₂p)
    (hpT := ne_top_of_inv_add_eq h₂p₁ h₂p₂ hp₁p₂p) (hp1 := one_le_of_inv_le_one hp)
    (hp₁ne := h₂p₁.ne) (hp₂ne := h₂p₂.ne) (hf := hf) (hg := hg)
  exact ⟨h, hmem, hae⟩

/--
Statement of Theorem 1.17(iii) (Maximal ergodic theorem):

There exists a constant `C ≥ 0` such that for any `f ∈ Lᵖ₁(X)` and `g ∈ Lᵖ₂(X)`,
`‖A T (N : ℕ+) X P f g‖_{Lᵖ(X;ℓ∞)} ≤ C ‖f‖_{Lᵖ₁(X)} ‖g‖_{Lᵖ₂(X)}`.
-/
theorem theorem_1_17_iii {f g : 𝓧 → ℂ} (hf : MemLp f p₁ μ) (hg : MemLp g p₂ μ) :
    eLpNorm (fun x ↦ ⨆ (N : ℕ+), ‖A T N (X : ℤ[X]) P f g x‖ₑ) p μ ≤
      Cᵢᵢᵢ P p₁ p₂ * ‖hf.toLp‖ₑ * ‖hg.toLp‖ₑ := by
  have h := eLpNorm_maximal_le_of_varEst (Cv := fun Λ => Cᵢᵥ P p₁ p₂ 3 Λ)
    (variationalEstimate_of_theorem_1_17_iv hT hP h₁p₁ h₁p₂ h₂p₁ h₂p₂ hp₁p₂p hp)
    (hp0 := ne_zero_of_inv_add_eq h₁p₁ h₁p₂ hp₁p₂p)
    (hpT := ne_top_of_inv_add_eq h₂p₁ h₂p₂ hp₁p₂p) hf hg
    (AEMeasurable.iSup fun N : ℕ+ => (aemeasurable_A_of_measurePreserving T hT N X P
      hf.aemeasurable hg.aemeasurable).enorm).aestronglyMeasurable
  refine h.trans (le_of_eq ?_)
  rw [Cᵢᵢᵢ]
  push_cast
  ring

end PointwiseErgodicTheorems

end Submission

/- The area development imports all of Mathlib, where `Mathlib.Order.CompletePartialOrder` makes
`CompletePartialOrder.toSupSet` the preferred `SupSet ℝ≥0∞` instance.  `Challenge.lean` (which
imports only `ChallengeDeps`) resolves it through `ConditionallyCompletePartialOrderSup.toSupSet`;
we raise that instance so that `Solution.lean`, which imports this module, elaborates the statement
of `theorem_1_17_iii` with exactly the same instances. -/
attribute [instance 9000] ConditionallyCompletePartialOrderSup.toSupSet
