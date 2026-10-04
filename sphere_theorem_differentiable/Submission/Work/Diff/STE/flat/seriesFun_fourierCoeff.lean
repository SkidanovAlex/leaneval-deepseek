import Mathlib
import Submission.Work.Diff.STE.LayerA
import Submission.Work.Diff.STE.summable_norm_of_CSq
import Submission.Work.Diff.STE.flat.fourierCoeff_seriesFun

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Fourier inversion on the flat torus: `seriesFun (fourierCoeff f) = f`

For a smooth (`C^∞`) function `f : (ι → ℝ) → ℂ` that is `1`-periodic in every coordinate, the
Fourier series of its Fourier coefficients reproduces `f` pointwise:

  `seriesFun (fourierCoeff f) x = f x`  for every `x`.

This is the "easy" (smooth) case of Fourier inversion on the unit torus, and it is the step that
identifies a Fourier/Galerkin expansion with the function it was built from.

The proof has three ingredients, all of which are already available in the STE toolkit:

1. **`ℓ¹` summability of the coefficients.**  `summable_weighted_fourierCoeff_of_contDiff` gives
   `Σ_k ⟨k⟩^{2s} ‖û(k)‖² < ∞` for every `s`; choosing `s` with `card ι < 2 s` and applying
   `summable_norm_of_CSq` (AM–GM against the summable dual weight `⟨k⟩^{-2s}`) yields
   `Summable (fun k => ‖û(k)‖)`.

2. **The series is a continuous, `1`-periodic function**, and its Fourier coefficients are the
   `û(k)` again.  Continuity is the Weierstrass M-test (`continuous_tsum`) with majorant
   `‖û(k)‖`, since `‖fourierExp k x‖ = 1`; periodicity is `periodicIn_fourierExp`; and the
   coefficient identity is `fourierCoeff_seriesFun` (the absolutely convergent half of inversion,
   proved in `flat/fourierCoeff_seriesFun.lean`).

3. **Uniqueness.**  The difference `f - seriesFun (fourierCoeff f)` is continuous, `1`-periodic,
   and has all Fourier coefficients `0` (linearity of the integral), so it vanishes identically by
   `eq_zero_of_fourierCoeff_eq_zero`.
-/

noncomputable section

namespace Work.Diff.STE.flat

open MeasureTheory Filter

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `seriesFun c` is continuous as soon as the coefficient family `c` is summable in `ℓ¹`:
the Weierstrass M-test with majorant `k ↦ ‖c k‖`, using `‖fourierExp k x‖ = 1`. -/
lemma continuous_seriesFun_of_summable (c : (ι → ℤ) → ℂ)
    (hc : Summable fun k : ι → ℤ => ‖c k‖) :
    Continuous (Work.Diff.STE.seriesFun c) := by
  change Continuous (fun x : ι → ℝ => ∑' k : ι → ℤ, c k * Work.Diff.STE.fourierExp k x)
  exact continuous_tsum (fun k => continuous_const.mul (Work.Diff.STE.continuous_fourierExp k))
    hc (fun k x => by rw [norm_mul, Work.Diff.STE.norm_fourierExp, mul_one])

/-- `seriesFun c` is `1`-periodic in every coordinate whenever `c` is a coefficient family:
each character `fourierExp k` is.  No summability is needed for this. -/
lemma periodic1_seriesFun (c : (ι → ℤ) → ℂ) :
    Work.Diff.STE.Periodic1 (Work.Diff.STE.seriesFun c) := by
  intro i x
  change (∑' k : ι → ℤ, c k * Work.Diff.STE.fourierExp k (x + Pi.single i 1))
      = ∑' k : ι → ℤ, c k * Work.Diff.STE.fourierExp k x
  exact tsum_congr fun k => by rw [Work.Diff.STE.periodicIn_fourierExp k i x]

omit [DecidableEq ι] in
/-- Linearity of `fourierCoeff` in the function for continuous entries. -/
lemma fourierCoeff_sub_of_continuous (f g : (ι → ℝ) → ℂ) (hf : Continuous f) (hg : Continuous g)
    (k : ι → ℤ) :
    Work.Diff.STE.fourierCoeff (fun x => f x - g x) k
      = Work.Diff.STE.fourierCoeff f k - Work.Diff.STE.fourierCoeff g k := by
  have h1 : Integrable (fun x : ι → ℝ => Work.Diff.STE.fourierExp (-k) x * f x)
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
    Work.Diff.STE.integrableOn_unitCube_of_continuous_cplx
      ((Work.Diff.STE.continuous_fourierExp (-k)).mul hf)
  have h2 : Integrable (fun x : ι → ℝ => Work.Diff.STE.fourierExp (-k) x * g x)
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
    Work.Diff.STE.integrableOn_unitCube_of_continuous_cplx
      ((Work.Diff.STE.continuous_fourierExp (-k)).mul hg)
  rw [Work.Diff.STE.fourierCoeff, Work.Diff.STE.fourierCoeff, Work.Diff.STE.fourierCoeff,
    ← MeasureTheory.integral_sub h1 h2]
  exact MeasureTheory.integral_congr_ae (Eventually.of_forall fun x => by ring)

theorem seriesFun_fourierCoeff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hper : Work.Diff.STE.Periodic1 f) :
    ∀ x, Work.Diff.STE.seriesFun (Work.Diff.STE.fourierCoeff f) x = f x := by
  classical
  obtain ⟨s, hscard⟩ : ∃ s : ℕ, Fintype.card ι < 2 * s :=
    ⟨Fintype.card ι + 1, by omega⟩
  let c : (ι → ℤ) → ℂ := Work.Diff.STE.fourierCoeff f
  have hCsq : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖c k‖ ^ 2) :=
    Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff f hf hper s
  have hsum : Summable (fun k : ι → ℤ => ‖c k‖) :=
    Work.Diff.STE.summable_norm_of_CSq s hscard c hCsq
  let g : (ι → ℝ) → ℂ := Work.Diff.STE.seriesFun c
  have hgcont : Continuous g := continuous_seriesFun_of_summable c hsum
  have hgper : Work.Diff.STE.Periodic1 g := periodic1_seriesFun c
  have hcoefg : ∀ k : ι → ℤ, Work.Diff.STE.fourierCoeff g k = c k :=
    fun k => fourierCoeff_seriesFun c hsum k
  have hcont : Continuous (fun x : ι → ℝ => f x - g x) := hf.continuous.sub hgcont
  have hper' : Work.Diff.STE.Periodic1 (fun x : ι → ℝ => f x - g x) := by
    intro i x
    show f (x + Pi.single i 1) - g (x + Pi.single i 1) = f x - g x
    rw [hper i x, hgper i x]
  have hcoef : ∀ k : ι → ℤ, Work.Diff.STE.fourierCoeff (fun x : ι → ℝ => f x - g x) k = 0 := by
    intro k
    rw [fourierCoeff_sub_of_continuous f g hf.continuous hgcont k, hcoefg k]
    ring
  intro x
  have hfx : f x = g x :=
    sub_eq_zero.mp (Work.Diff.STE.eq_zero_of_fourierCoeff_eq_zero (fun y : ι → ℝ => f y - g y)
      hcont hper' hcoef x)
  rw [hfx]

end Work.Diff.STE.flat
