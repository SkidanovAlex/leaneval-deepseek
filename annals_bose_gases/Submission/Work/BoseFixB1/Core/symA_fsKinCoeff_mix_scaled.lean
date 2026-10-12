import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.symA_fsKinCoeff_mix
import Submission.Work.BoseFixB1.symA_fsKinCoeff_near
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.symA_fsKinCoeff_mix_scaled` — the two-cut symbol comparison at scale `a`

The proved `Work.BoseFixB1.symA_fsKinCoeff_mix` (a three-region estimate in the *scaled*
variables) compares the *scale-`1`* symbol with the two-cut mixture.  The sliding comparison of
FS `eq:BSsliding2`'s kinetic core lives at scale `a = dℓ` (the small box), so this file scales
that theorem: for `a > 0`, `C > 0`, `0 ≤ d ≤ 1/2`, `0 ≤ ε ≤ 1/2` and the three inputs

* the bump moments `M₁ ≤ C`, `8M₂ ≤ (1−d)²C²`,
* the tail `symA 1 (fsKinCoeff (C/2)) 0 ≤ β`,

we get `∀q`, `symA a (fsKinCoeff (C/a)) q ≤ (1−ε)·fsKinCoeff (dC/(2a))‖q‖ + ε·fsKinCoeff (C/(2a))‖q‖ + β/a²`.

The scaling is `Work.OneBodyKin.symA_kinCoeff_scale` (proved),
`symA ℓ (fsKinCoeff c) q = ℓ⁻²·symA 1 (fsKinCoeff (c·ℓ)) (ℓ • q)`, plus the elementary
`fsKinCoeff e (a·r) = a²·fsKinCoeff (e/a) r` for `a > 0`.

At FS's parameters (`a = dℓ`, `c_sb = (dsℓ)⁻¹` so `C = c_sb·a = 1/s`) this is the comparison
`(SYM)` of `FINDING_slidingBC_reduction.md` §1(L5): the cutoff `C/a = c_sb` is the sliding one and
the two mixture cutoffs `dC/(2a) = 1/(2sℓ) = c₁`, `C/(2a) = 1/(2dsℓ) = c₂` are exactly FS's anchored
`eq:T'u` cutoffs of `mainWord`.
-/

noncomputable section

open MeasureTheory
open scoped Real Topology

namespace Work.BoseFixB1

local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-- **The cut-off scales homogeneously**: for `a > 0`, `fsKinCoeff e (a·r) = a²·fsKinCoeff (e/a) r`.
Both sides are `([·]₊)²` of `a·r − e = a·(r − e/a)`, and `max (a*x) 0 = a·max x 0` for `a > 0`. -/
lemma fsKinCoeff_mul_scale {a e : ℝ} (ha : 0 < a) (r : ℝ) :
    Submission.BoseGases.fsKinCoeff e (a * r)
      = a ^ 2 * Submission.BoseGases.fsKinCoeff (e / a) r := by
  unfold Submission.BoseGases.fsKinCoeff
  have h1 : max (a * r - e) 0 = a * max (r - e / a) 0 := by
    have h : a * (r - e / a) = a * r - e := by
      rw [mul_sub, mul_div_cancel₀ e (ne_of_gt ha)]
    rw [← h, mul_max_of_nonneg _ _ ha.le, mul_zero]
  rw [h1, mul_pow]

/-- **The two-cut symbol comparison at scale `a`.**  `Work.BoseFixB1.symA_fsKinCoeff_mix` at the
scaled momentum `a • q`, rescaled by `a⁻²` through `Work.OneBodyKin.symA_kinCoeff_scale`. -/
theorem symA_fsKinCoeff_mix_scaled {a C d ε β : ℝ} (ha : 0 < a) (hC : 0 < C) (hd0 : 0 ≤ d)
    (hd : d ≤ 1 / 2) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (hM1 : ((2 * Real.pi) ^ 3)⁻¹ * ∫ t : R3,
        (Work.OneBodyKin.profHat t) ^ 2 * ‖t‖ ≤ C)
    (hM2 : 8 * (((2 * Real.pi) ^ 3)⁻¹ * ∫ t : R3,
        (Work.OneBodyKin.profHat t) ^ 2 * ‖t‖ ^ 2) ≤ (1 - d) ^ 2 * C ^ 2)
    (htail : Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff (C / 2)) 0 ≤ β)
    (q : R3) :
    Work.OneBodyKin.symA a (Submission.BoseGases.fsKinCoeff (C / a)) q
      ≤ (1 - ε) * Submission.BoseGases.fsKinCoeff (d * C / (2 * a)) ‖q‖
        + ε * Submission.BoseGases.fsKinCoeff (C / (2 * a)) ‖q‖ + β / a ^ 2 := by
  have h := Work.BoseFixB1.symA_fsKinCoeff_mix (C := C) (d := d) (ε := ε) (β := β) hC hd0 hd hε0 hε
    (fun ρ => Work.BoseFixB1.symA_fsKinCoeff_near (C := C) hC.le ρ) hM1 hM2 htail (a • q)
  have hscale : Work.OneBodyKin.symA a (Submission.BoseGases.fsKinCoeff (C / a)) q
      = (a ^ 2)⁻¹ * Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff C) (a • q) := by
    rw [Work.OneBodyKin.symA_kinCoeff_scale (ℓ := a) (c := C / a) ha q]
    have hca : C / a * a = C := by
      rw [div_mul_cancel₀ _ (ne_of_gt ha)]
    rw [hca]
  have hnorm : ‖a • q‖ = a * ‖q‖ := by
    rw [norm_smul, Real.norm_of_nonneg ha.le]
  have h1 : Submission.BoseGases.fsKinCoeff (d * C / 2) ‖a • q‖
      = a ^ 2 * Submission.BoseGases.fsKinCoeff (d * C / (2 * a)) ‖q‖ := by
    rw [hnorm, fsKinCoeff_mul_scale (a := a) (e := d * C / 2) ha ‖q‖]
    congr 1
    ring
  have h2 : Submission.BoseGases.fsKinCoeff (C / 2) ‖a • q‖
      = a ^ 2 * Submission.BoseGases.fsKinCoeff (C / (2 * a)) ‖q‖ := by
    rw [hnorm, fsKinCoeff_mul_scale (a := a) (e := C / 2) ha ‖q‖]
    congr 1
    ring
  rw [h1, h2] at h
  have hexp : a ^ 2 * ((1 - ε) * Submission.BoseGases.fsKinCoeff (d * C / (2 * a)) ‖q‖
      + ε * Submission.BoseGases.fsKinCoeff (C / (2 * a)) ‖q‖ + β / a ^ 2)
      = (1 - ε) * (a ^ 2 * Submission.BoseGases.fsKinCoeff (d * C / (2 * a)) ‖q‖)
        + ε * (a ^ 2 * Submission.BoseGases.fsKinCoeff (C / (2 * a)) ‖q‖) + β := by
    have hβ : a ^ 2 * (β / a ^ 2) = β :=
      mul_div_cancel₀ β (pow_ne_zero 2 (ne_of_gt ha))
    rw [mul_add, mul_add, hβ]
    ring
  rw [hscale, inv_mul_le_iff₀ (by positivity : (0 : ℝ) < a ^ 2), hexp]
  exact h

end Work.BoseFixB1
