import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Sard's theorem: the vocabulary

This file fixes the vocabulary of item 1 of the **Transversality** chapter: *critical points*,
*Sard's theorem in the rectangular case*, and its *parametric* form — the form actually used by the
transversality homotopy theorem of `Submission/Work/ThomBordism/Transversality/Homotopy.lean`.

## What Mathlib has, and what is proved here

Mathlib's Sard-type results are

* `MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero` — a differentiable map
  sends null sets to null sets;
* `MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` — **the equidimensional case of
  Sard**: if `det (fderiv ℝ f x) = 0` on `s`, then `f '' s` is null;
* `ContDiffOn.dimH_image_le`, `ContDiff.dimH_range_le` — the Hausdorff dimension of the image of a
  `C¹` map is at most the dimension of the source;
* `ContDiffOn.dense_compl_image_of_dimH_lt_finrank`, `ContDiff.dense_compl_range_of_finrank_lt_finrank`
  — regular values are dense.

The chapter builds on those:

* `volume_absolutelyContinuous_hausdorffMeasure`, `volume_eq_zero_of_dimH_lt` — a set of Hausdorff
  dimension `< d` in `ℝ^d` is Lebesgue-null;
* `volume_range_eq_zero_of_contDiff_finrank_lt` — **the low-dimensional case of Sard**: the image of
  a `C¹` map `ℝ^a → ℝ^b` with `a < b` is null;
* `volume_image_critical_eq_zero` — **the equidimensional case of Sard** in the form of this
  chapter (the image of the critical set of a differentiable endomorphism of `ℝ^n` is null);
* `dense_compl_range_of_finrank_lt` — the complement of the image of a `C¹` map `ℝ^a → ℝ^b`,
  `a < b`, is dense (so regular values exist).

What Mathlib does not have, and what this chapter builds, is the *rectangular* case (`a > b`, the
case needed for transversality): for a `C^∞` map `ℝ^a → ℝ^b` the image of the set
`{x | fderiv ℝ f x is not surjective}` has measure zero.  It is stated here as the named `Prop`
`SardRectangular` — **proved** in `Sard/Rectangular.lean` (`Sard.sardRectangular`, from the pieces in
`Sard/` and the non-flat step `Sard.notFlat_null`) — and `SardParametric` is the parametric form in
which the transversality homotopy theorem consumes it (the perturbation `x ↦ G x - χ x • t` of a map
`G` that is a submersion on its zero set is regular at `0` for almost every `t`).

All statements are given for the concrete spaces `EuclideanSpace ℝ (Fin n)`; the hypotheses are
those of the source, with `⊤ : ℕ∞` (written `∞` in the `ContDiff` scope) for `C^∞` — note that
`ContDiff ℝ ⊤` in this Mathlib means *analytic*, so the height must be named `((⊤ : ℕ∞) : ℕ∞ω)`.
-/

open scoped MeasureTheory ContDiff
open MeasureTheory Set Function

set_option autoImplicit false

namespace Work.ThomBordism.Transversality

noncomputable section

/-- A **critical point** of `f : E → F` in the sense of Sard's theorem: a point at which the
derivative of `f` is not surjective. -/
def IsCriticalPoint {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (x : E) : Prop :=
  ¬ Function.Surjective (fderiv ℝ f x)

/-- **Sard's theorem, rectangular case** (`a ≥ b`): for a `C^∞` map `ℝ^a → ℝ^b` the set of *critical
values* — the image of the set of points where the derivative is not surjective — has measure zero.

This is an input of the chapter (Mathlib has only the equidimensional case
`MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`, which is the special case `a = b`,
and the low-dimensional case `a < b` proved in this chapter). -/
def SardRectangular : Prop :=
  ∀ (a b : ℕ), b ≤ a → ∀ f : EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin b),
    ContDiff ℝ ((⊤ : ℕ∞) : ℕ∞ω) f → volume (f '' {x | IsCriticalPoint f x}) = 0

/-- **Parametric Sard**, the analytic core of the transversality homotopy theorem.

Let `G : ℝ^a → ℝ^b` be `C^∞` with `a ≥ b` (`b ≤ a`), suppose that `G` is a **submersion on its zero
set** (`∀ x, G x = 0 → fderiv ℝ G x` is surjective) and let `χ : ℝ^a → ℝ` be a `C^∞` **nonnegative**
function.  Then for almost every `t : ℝ^b` the map `x ↦ G x - χ x • t` has `0` as a *regular value*:
there is no `x` with `G x = χ x • t` at which that map is critical.

The perturbation `G ↦ G - χ • t` ("push the zero set of `G` in the direction `t`, damped by `χ`") is
the one used in the homotopy theorem, with `χ = 1` on the part of the source that has to be corrected
and `χ = 0` near the boundary (where `G` is already transverse).

**Proof.**  On the open set `U = {χ > 0}` put `u x := (χ x)⁻¹ • G x`.  For `x ∈ U`, the two
conditions `G x = χ x • t` and "*`x` is critical for `y ↦ G y - χ y • t`*" hold simultaneously
exactly when `t = u x` and `x` is a critical point of `u` (because
`fderiv ℝ (fun y => G y - χ y • (u x)) x = χ x • fderiv ℝ u x`); so the parameters arising from `U`
lie in `u '' {x | IsCriticalPoint u x}`, which is null by Sard (`SardEuclidOn a b U u`).  On
`{χ = 0}` the conditions are empty: `χ ≥ 0` forces `dχ x = 0` at a zero of `χ`, and if in addition
`G x = 0` then `dG x` is surjective by hypothesis (and if `G x ≠ 0` the first condition cannot be
met).

**History (a corrected statement).**  An earlier version of this `Prop` asked instead that the set of
parameters `t` for which *some* `x` is critical for the slice `x ↦ F (x,t)` be null.  That statement
is **false** — for `F (x,t) = x²` (`a = b = p = 1`) the point `x = 0` is critical for the slice for
every `t`, so the parameter set is all of `ℝ` — and the reduction recorded for it (rectangular Sard
for `(x,t) ↦ (F (x,t), t)` plus Fubini) yields only the statement about critical *values*, since the
projection of a null set need not be null.  The statement below is the correct parametric form, and
it is exactly what the homotopy theorem consumes. -/
def SardParametric : Prop :=
  ∀ (a b : ℕ), b ≤ a →
    ∀ (G : EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin b))
      (χ : EuclideanSpace ℝ (Fin a) → ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : ℕ∞ω) G → ContDiff ℝ ((⊤ : ℕ∞) : ℕ∞ω) χ → (∀ x, 0 ≤ χ x) →
      (∀ x, G x = 0 → Function.Surjective (fderiv ℝ G x)) →
      volume {t : EuclideanSpace ℝ (Fin b) |
        ∃ x, G x = χ x • t ∧
          IsCriticalPoint (fun y => G y - χ y • t) x} = 0

/-- The critical points of a map are all points of the source as soon as the source has smaller
dimension than the target: the derivative has rank `≤ a < b`, so it is never surjective. -/
theorem criticalPoint_univ_of_finrank_lt {a b : ℕ} (hab : a < b)
    (f : EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin b)) {x : EuclideanSpace ℝ (Fin a)} :
    IsCriticalPoint f x := by
  intro hsurj
  have htop : LinearMap.range ((fderiv ℝ f x).toLinearMap) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have h := LinearMap.finrank_range_add_finrank_ker ((fderiv ℝ f x).toLinearMap)
  rw [htop] at h
  rw [finrank_top] at h
  have hb : Module.finrank ℝ (EuclideanSpace ℝ (Fin b)) = b := by simp
  have ha : Module.finrank ℝ (EuclideanSpace ℝ (Fin a)) = a := by simp
  rw [hb, ha] at h
  omega

end

end Work.ThomBordism.Transversality
