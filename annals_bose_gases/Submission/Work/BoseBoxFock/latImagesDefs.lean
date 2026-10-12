import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.imagesAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.latImagesDefs` — the universal constant of `latImages_lintegral_le`

This tiny module only fixes the **universal constant** `latImgC` that appears in the bound of
`Work.BoseBoxFock.latImages_lintegral_le` and in its two intermediate steps
(`latImgTsum_le`, `latImg_lintegral_le`, `latImgLin_le`).

The constant has to absorb three *a priori* unrelated quantities:

* the trivial size of the corpus bump, `chiScale ℓ x ≤ chiSupAbs`
  (`Submission.BoseGases.chi_abs_le_sup`, with `chiSupAbs = (√ chiNormSq)⁻¹`);
* the **flatness constant** `chiImgC 12` of `Work.BoseBoxFock.chiScale_pair_image_le` (the
  `(R/ℓ)^12` decay of the *product* of the two bumps when the two arguments are `R`-close along
  a nonzero lattice vector);
* the number `1`, so that `latImgC ≥ 1` (needed to compare the `min 1 (ρ/ℓ)` form of the
  intermediate bounds with the `(ρ/ℓ)^12` form of the statement).

Nothing here depends on `ℓ`, `ρ`, `U`, `w`: the constant is *universal*, which is exactly what
the target theorem asks for.

## The proof plan of `latImages_lintegral_le` (for the sibling lemmas)

The target

    ∫⁻ z, ofReal (χ_ℓ(w) χ_ℓ(z) Σ'_{m ≠ 0} ‖U(w − z + ℓ•latVec m)‖)
      ≤ ofReal (C (ρ/ℓ)^12 ∫‖U‖ + C ∫_{ρ ≤ ‖u‖} ‖U‖)

is split into three independent bricks (all in namespace `Work.BoseBoxFock`):

1. **`latImgLin_le`** *(no geometry)*: from a pointwise majorant `hG` of the lattice sum one gets
   `∫⁻ v, G v * ofReal ‖U v‖ ≤ ofReal (latImgC (min 1 (ρ/ℓ))^12 ∫‖U‖ + latImgC ∫_{ρ ≤ ‖u‖} ‖U‖)`.
   Route: `lintegral_add_compl` for `S = {v | ‖v‖ ≤ ρ}`, `setLIntegral_le_lintegral`,
   `ofReal_integral_eq_lintegral_ofReal` (for `‖U·‖` on `volume` and on `volume.restrict Sᶜ`,
   with `Integrable.norm`, `Integrable.restrict`), `lintegral_const_mul''`,
   `ENNReal.ofReal_mul`, `ENNReal.ofReal_add`, `lintegral_mono`,
   `lintegral_mono_set`/`lintegral_mono`.  Pointwise for every `v`:
   `G v * ofReal ‖U v‖ ≤ ofReal c · 1_{‖v‖≤ρ} ‖U v‖ + ofReal latImgC · 1_{ρ≤‖v‖} ‖U v‖`
   with `c = latImgC (min 1 (ρ/ℓ))^12`.

2. **`latImg_lintegral_le`** *(no geometry)*: the measure-theoretic rewriting of the LHS of the
   target into the shape `∫⁻ v, (Σ'_{m} ofReal (χ_ℓ w χ_ℓ (w + ℓ•latVec m − v))) · ofReal ‖U v‖`.
   Route: pointwise `ofReal (χ_w χ_z T z) ≤ Σ'_m ofReal (χ_w χ_z b_m z)` where `T = Σ'_m b_m`,
   `b_m z = if m = 0 then 0 else ‖U (w − z + ℓ•latVec m)‖ ≥ 0` — case split on `Summable b`
   (`ENNReal.ofReal_tsum_of_nonneg` + `ENNReal.tsum_mul_left`, resp.
   `tsum_eq_zero_of_not_summable`); then `lintegral_mono`, `lintegral_tsum` (both directions) and,
   for each `m`, the measure-preserving substitution `z ↦ w + ℓ•latVec m − z`
   (`v = w + ℓ•latVec m − z` gives `w − z + ℓ•latVec m = v` and
   `χ_ℓ z = χ_ℓ (w + ℓ•latVec m − v)`): use `lintegral_add_left_eq_self` and
   `lintegral_neg_eq_self` on the function `F (y) = …(c + y)…`; finish with
   `ENNReal.tsum_mul_right`.

3. **`latImgTsum_le`** *(the geometry)*: the pointwise bound of the lattice series.  A term is
   nonzero only when `‖w‖ < ℓ/2` and `‖w + ℓ•latVec m − v‖ < ℓ/2`
   (`Submission.BoseGases.chi_eq_zero_of_half_le_norm` with `chiScale ℓ x = chi (ℓ⁻¹ • x)`), so two
   distinct indices would give `ℓ‖m − m'‖ = ‖(w + ℓ•latVec m − v) − (w + ℓ•latVec m' − v)‖ < ℓ`,
   contradicting `‖latVec m − latVec m'‖ ≥ 1` (see `Work.BoseBoxFock.intVec_norm_ge_one` /
   `imagesAux`).  Hence at most one term survives; bound it by `tsum_eq_single` and:
   * if `‖v‖ ≤ ρ` and `ρ ≤ ℓ`: the pair `x = w`, `y = w + ℓ•latVec m − v` is `ρ`-close along the
     *nonzero* lattice vector `−m` (indeed `w − y − ℓ•latVec (−m) = v`), so
     `Work.BoseBoxFock.chiScale_pair_image_le` gives `χ_ℓ w χ_ℓ y ≤ chiImgC 12 (ρ/ℓ)^12`
     (`ρ/ℓ = min 1 (ρ/ℓ)` here);
   * otherwise: bound the single term by `chiSupAbs ^ 2`
     (`Submission.BoseGases.chi_abs_le_sup`, `chi_nonneg`).
   The constant `latImgC` dominates both (`latImgC_ge_flat`, `latImgC_ge_sup`, `latImgC_one_le`).
-/

namespace Work.BoseBoxFock

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The universal constant of the lattice-images estimate: the maximum of `1`, the square of the
sup bound of the corpus bump, and the flatness constant `chiImgC 12`. -/
noncomputable def latImgC : ℝ :=
  max 1 (max (Submission.BoseGases.chiSupAbs ^ 2) (chiImgC 12))

lemma latImgC_nonneg : 0 ≤ latImgC := by
  rw [latImgC]
  exact le_trans zero_le_one (le_max_left _ _)

lemma latImgC_one_le : 1 ≤ latImgC := le_max_left _ _

lemma latImgC_ge_sup : Submission.BoseGases.chiSupAbs ^ 2 ≤ latImgC := by
  rw [latImgC]
  exact le_trans (le_max_left _ _) (le_max_right _ _)

lemma latImgC_ge_flat : chiImgC 12 ≤ latImgC := by
  rw [latImgC]
  exact le_trans (le_max_right _ _) (le_max_right _ _)

end Work.BoseBoxFock
