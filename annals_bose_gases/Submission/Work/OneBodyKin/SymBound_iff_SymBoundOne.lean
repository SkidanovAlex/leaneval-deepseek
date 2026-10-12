import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.OneBodyKin.BoxHat.boxHat_scale
import Submission.Work.OneBodyKin.SymD.symD_kinCoeff_scale
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.SymBound_iff_SymBoundOne`

The pointwise symbol bound `SymBound ℓ c` is **scale invariant**: it depends on the two parameters
`ℓ` (the box size of the moving-box family) and `c` (the FS cut-off) only through the product
`c·ℓ`.  Concretely,

    `SymBound ℓ c ↔ SymBoundOne (c·ℓ)`,

where `SymBoundOne C = SymBound 1 C` is the bound at box size `1`.

This is the content of `Scaled.symBound_iff_one` announced in `Defs.lean`: after the dilations
`q ↦ ℓ q` and `p ↦ ℓ p` inside the three symbol terms, every occurrence of `ℓ` in the symbol can
be absorbed into the cut-off `c ↦ c·ℓ`.

The mechanism is the exact identity

    `famSym 1 (fsKinCoeff (c·ℓ)) (ℓ • q) = ℓ² · famSym ℓ (fsKinCoeff c) q`    (`famSym_kinCoeff_scale`)

combined with `‖ℓ • q‖² = ℓ² ‖q‖²`.  It is proved from the three scaling laws of the symbol
terms:

* `symA`:  `symA ℓ (fsKinCoeff c) q = (ℓ²)⁻¹ · symA 1 (fsKinCoeff (c·ℓ)) (ℓ q)` — here the
  substitution `p ↦ ℓ p` is *not* needed, the two integrals are literally the same after the
  pointwise coefficient identity `[r/ℓ − c]₊² = ℓ⁻² [r − cℓ]₊²` (`fsKinCoeff_scale`, proved here);
* `symD`:  `symD 1 (fsKinCoeff (c·ℓ)) (ℓ q) = ℓ⁵ · symD ℓ (fsKinCoeff c) q`
  (the dilation substitution `p ↦ ℓ p`, volume factor `ℓ³`, times the coefficient homogeneity
  `ℓ²`; proved in `Work.OneBodyKin.SymD.symD_kinCoeff_scale`);
* `boxHat`: `boxHat ℓ q = ℓ³ · boxHat 1 (ℓ q)`
  (the substitution `z ↦ ℓ z` in `∫_{acube ℓ}`; proved in
  `Work.OneBodyKin.BoxHat.boxHat_scale`).

The three powers `ℓ⁻²`, `ℓ⁵`, `ℓ³` combine to the single overall factor `ℓ²` because the cross
term carries the product `boxHat · symD` (`ℓ⁻³·ℓ⁵ = ℓ²`) and the mass term carries
`(ℓ⁶)⁻¹·(boxHat ℓ q)²` (`ℓ⁻⁶·ℓ⁶ = 1`).
-/

noncomputable section

open MeasureTheory

namespace Work.OneBodyKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option maxHeartbeats 800000

/-! ## 1. The homogeneity of the FS cut-off -/

/-- **The cut-off `[r−c]₊²` is homogeneous of degree `2` in the pair `(c,r)`**: for `ℓ > 0`

    `[r−c]₊² = ℓ⁻² · [ℓ r − cℓ]₊²`,

i.e. `fsKinCoeff c r = (ℓ²)⁻¹ · fsKinCoeff (c·ℓ) (ℓ·r)`.  This is the pointwise identity that
lets the cut-off `c` be absorbed into the product `c·ℓ` when the momentum is dilated by `ℓ`. -/
lemma fsKinCoeff_scale {ℓ : ℝ} (hℓ : 0 < ℓ) (c r : ℝ) :
    fsKinCoeff c r = (ℓ ^ 2)⁻¹ * fsKinCoeff (c * ℓ) (ℓ * r) := by
  have h := mul_max_of_nonneg (r - c) (0 : ℝ) hℓ.le
  rw [mul_zero] at h
  rw [show ℓ * (r - c) = ℓ * r - c * ℓ by ring] at h
  unfold fsKinCoeff
  rw [← h, mul_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 (ne_of_gt hℓ)), one_mul]

/-! ## 2. The scaling of the three symbol terms -/

/-- **Scaling of the unprojected symbol term.**  For `ℓ > 0`,

    `symA ℓ (fsKinCoeff c) q = (ℓ²)⁻¹ · symA 1 (fsKinCoeff (c·ℓ)) (ℓ q)`.

No substitution is needed: `symA 1 G (ℓ q)` integrates the same function of `p` as
`symA ℓ (fsKinCoeff c) q`, with the coefficient argument `‖ℓ q + p‖ = ℓ‖q + ℓ⁻¹ p‖` converted by
the homogeneity `fsKinCoeff_scale`. -/
theorem symA_kinCoeff_scale {ℓ c : ℝ} (hℓ : 0 < ℓ) (q : ℝ³) :
    symA ℓ (fsKinCoeff c) q = (ℓ ^ 2)⁻¹ * symA 1 (fsKinCoeff (c * ℓ)) (ℓ • q) := by
  unfold symA
  simp only [inv_one, one_smul]
  have hpt : ∀ p : ℝ³, fsKinCoeff c ‖q + ℓ⁻¹ • p‖ * (profHat p) ^ 2
      = (ℓ ^ 2)⁻¹ * (fsKinCoeff (c * ℓ) ‖ℓ • q + p‖ * (profHat p) ^ 2) := by
    intro p
    have hdecomp : ℓ • q + p = ℓ • (q + ℓ⁻¹ • p) := by
      rw [smul_add, smul_smul, mul_inv_cancel₀ (ne_of_gt hℓ), one_smul]
    have hnorm : ‖ℓ • q + p‖ = ℓ * ‖q + ℓ⁻¹ • p‖ := by
      rw [hdecomp, norm_smul, Real.norm_eq_abs, abs_of_pos hℓ]
    rw [fsKinCoeff_scale hℓ c ‖q + ℓ⁻¹ • p‖, ← hnorm, mul_assoc]
  rw [show (∫ p : ℝ³, fsKinCoeff c ‖q + ℓ⁻¹ • p‖ * (profHat p) ^ 2)
        = ∫ p : ℝ³, (ℓ ^ 2)⁻¹ *
          (fsKinCoeff (c * ℓ) ‖ℓ • q + p‖ * (profHat p) ^ 2) from
      integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_const_mul]
  ring

/-! ## 3. The scaling of the symbol and the equivalence of the bounds -/

/-- **Scaling of the symbol of the projected moving-box family.**  For `ℓ > 0`,

    `famSym 1 (fsKinCoeff (c·ℓ)) (ℓ q) = ℓ² · famSym ℓ (fsKinCoeff c) q`.

This is the exact statement that only the product `c·ℓ` matters: it is the term-by-term
combination of `symA_kinCoeff_scale`, `Work.OneBodyKin.SymD.symD_kinCoeff_scale` and
`Work.OneBodyKin.BoxHat.boxHat_scale`. -/
theorem famSym_kinCoeff_scale {ℓ c : ℝ} (hℓ : 0 < ℓ) (q : ℝ³) :
    famSym 1 (fsKinCoeff (c * ℓ)) (ℓ • q) = ℓ ^ 2 * famSym ℓ (fsKinCoeff c) q := by
  -- the cross symbol in the inverse direction, from the dilation covariance
  have hD : symD ℓ (fsKinCoeff c) q
      = (ℓ ^ 5)⁻¹ * symD 1 (fsKinCoeff (c * ℓ)) (ℓ • q) := by
    rw [SymD.symD_kinCoeff_scale (c := c) hℓ q, ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero 5 (ne_of_gt hℓ)), one_mul]
  rw [famSym, famSym, symC, symC, symA_kinCoeff_scale (c := c) hℓ q,
    symA_kinCoeff_scale (c := c) hℓ 0, BoxHat.boxHat_scale hℓ q, hD, smul_zero]
  simp only [one_pow, inv_one, mul_one]
  field_simp

/-- **`SymBound` depends on `ℓ` and `c` only through the product `c·ℓ`.**

For `ℓ > 0`, the pointwise symbol bound `∀ q, famSym ℓ (fsKinCoeff c) q ≤ ‖q‖²` at box size `ℓ` is
equivalent to the same bound at box size `1` with the rescaled cut-off `c·ℓ`. -/
theorem SymBound_iff_SymBoundOne {ℓ c : ℝ} (hℓ : 0 < ℓ) :
    Work.OneBodyKin.SymBound ℓ c ↔ Work.OneBodyKin.SymBoundOne (c * ℓ) := by
  constructor
  · intro h ρ
    -- write `ρ = ℓ q`
    obtain ⟨q, rfl⟩ : ∃ q : ℝ³, ℓ • q = ρ :=
      ⟨ℓ⁻¹ • ρ, by rw [smul_smul, mul_inv_cancel₀ hℓ.ne', one_smul]⟩
    rw [famSym_kinCoeff_scale (c := c) hℓ q]
    calc ℓ ^ 2 * famSym ℓ (fsKinCoeff c) q ≤ ℓ ^ 2 * ‖q‖ ^ 2 :=
          mul_le_mul_of_nonneg_left (h q) (sq_nonneg ℓ)
      _ = ‖ℓ • q‖ ^ 2 := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hℓ, mul_pow]
  · intro h q
    have hle := h (ℓ • q)
    rw [famSym_kinCoeff_scale (c := c) hℓ q] at hle
    have hnorm : ‖ℓ • q‖ ^ 2 = ℓ ^ 2 * ‖q‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hℓ, mul_pow]
    rw [hnorm] at hle
    exact le_of_mul_le_mul_left hle (pow_pos hℓ 2)


/-- **The scale-free form is the usable one**: a bound at box size `1` with cut-off `C` gives the
bound at box size `ℓ` with any cut-off `c` satisfying `c·ℓ = C`.  (Immediate from
`SymBound_iff_SymBoundOne`.) -/
theorem SymBound_of_SymBoundOne {ℓ C c : ℝ} (hℓ : 0 < ℓ) (h : SymBoundOne C)
    (hc : c * ℓ = C) : SymBound ℓ c :=
  (SymBound_iff_SymBoundOne hℓ).mpr (by rwa [hc])

end Work.OneBodyKin
