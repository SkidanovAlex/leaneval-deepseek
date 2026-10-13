/-
# `rgiClearing`

Elementary exponent clearing for the Green's-function series `radGreenI` of
`Submission.Work.FTS.PhiStar.Series.radGreenI_differentiableAt`.

The two integrands

* `rgiF1 α m c t = c t * t ^ ((2m+5)/α - 1)`  (`0..z` integral, `rgiA`),
* `rgiF2 α m c t = c t * t ^ (-(2m/α) - 1)`    (`Ioi z` integral, `rgiB`)

carry inverse powers of `t` which, on multiplication by the indicial factors
`z ^ (rgiSn α m) = z ^ (-(2m+5)/α)` resp. `z ^ (rgiSp α m) = z ^ (2m/α)` coming from the
Green's function, cancel exactly: for `z > 0`,

`z ^ 2 * z ^ (s⁻ - 1) * rgiF1 α m c z = c z`,  `z ^ 2 * z ^ (s⁺ - 1) * rgiF2 α m c z = c z`,

because `s⁻ + 1 + ((2m+5)/α - 1) = 0` and `s⁺ + 1 + (-(2m/α) - 1) = 0`.  The first four
conjuncts record the underlying `rpow` identities `z * z ^ (s-1) = z ^ s` and
`z ^ 2 * z ^ (s-2) = z ^ s`.

All the work is `Real.rpow_add` bookkeeping for the exponent identifications; the
elementary identities are isolated in the three private lemmas below.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.PhiStar.Series.radGreenI_differentiableAt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series.Deleg

/-- For `z > 0`: `z * z ^ (s - 1) = z ^ s` (`z = z ^ 1` and `Real.rpow_add`). -/
private lemma mul_rpow_sub_one {z s : ℝ} (hz : 0 < z) : z * z ^ (s - 1) = z ^ s := by
  calc z * z ^ (s - 1) = z ^ (1 : ℝ) * z ^ (s - 1) := by rw [Real.rpow_one]
    _ = z ^ ((1 : ℝ) + (s - 1)) := (Real.rpow_add hz 1 (s - 1)).symm
    _ = z ^ s := by congr 1; ring

/-- For `z > 0`: `z ^ 2 * z ^ (s - 2) = z ^ s` (`z ^ 2 = z ^ (2 : ℝ)` and `Real.rpow_add`). -/
private lemma sq_mul_rpow_sub_two {z s : ℝ} (hz : 0 < z) : z ^ 2 * z ^ (s - 2) = z ^ s := by
  calc z ^ 2 * z ^ (s - 2) = z ^ (2 : ℝ) * z ^ (s - 2) := by rw [(Real.rpow_two z).symm]
    _ = z ^ ((2 : ℝ) + (s - 2)) := (Real.rpow_add hz 2 (s - 2)).symm
    _ = z ^ s := by congr 1; ring

/-- For `z > 0` and `s + t = -1`: `z ^ 2 * z ^ (s - 1) * z ^ t = 1`.  Here
`z ^ 2 * z ^ (s - 1) = z ^ (s + 1)`, so the total exponent is `s + 1 + t = 0`.  This is the
exact cancellation behind the two `rgiF`-conjuncts, with `s = rgiSn α m` or `s = rgiSp α m`
and `t` the exponent of the corresponding integrand. -/
private lemma sq_mul_rpow_sub_one_mul {z s t : ℝ} (hz : 0 < z) (hst : s + t = -1) :
    z ^ 2 * z ^ (s - 1) * z ^ t = 1 := by
  have h2 : z ^ 2 * z ^ (s - 1) = z ^ (s + 1) := by
    have h := sq_mul_rpow_sub_two (z := z) (s := s + 1) hz
    have he : s + 1 - 2 = s - 1 := by ring
    rwa [he] at h
  have h3 : z ^ (s + 1) * z ^ t = 1 := by
    have he : s + 1 + t = 0 := by linarith only [hst]
    calc z ^ (s + 1) * z ^ t = z ^ ((s + 1) + t) := (Real.rpow_add hz (s + 1) t).symm
      _ = z ^ (0 : ℝ) := by rw [he]
      _ = 1 := Real.rpow_zero z
  rw [h2, h3]

theorem rgiClearing (α : ℝ) (m : ℕ) (c : ℝ → ℝ) :
    (∀ z : ℝ, 0 < z → z * z ^ (Work.FTS.PhiStar.Series.rgiSn α m - 1)
        = z ^ (Work.FTS.PhiStar.Series.rgiSn α m)) ∧
    (∀ z : ℝ, 0 < z → z ^ 2 * z ^ (Work.FTS.PhiStar.Series.rgiSn α m - 2)
        = z ^ (Work.FTS.PhiStar.Series.rgiSn α m)) ∧
    (∀ z : ℝ, 0 < z → z * z ^ (Work.FTS.PhiStar.Series.rgiSp α m - 1)
        = z ^ (Work.FTS.PhiStar.Series.rgiSp α m)) ∧
    (∀ z : ℝ, 0 < z → z ^ 2 * z ^ (Work.FTS.PhiStar.Series.rgiSp α m - 2)
        = z ^ (Work.FTS.PhiStar.Series.rgiSp α m)) ∧
    (∀ z : ℝ, 0 < z → z ^ 2 * z ^ (Work.FTS.PhiStar.Series.rgiSn α m - 1)
        * Work.FTS.PhiStar.Series.rgiF1 α m c z = c z) ∧
    (∀ z : ℝ, 0 < z → z ^ 2 * z ^ (Work.FTS.PhiStar.Series.rgiSp α m - 1)
        * Work.FTS.PhiStar.Series.rgiF2 α m c z = c z) := by
  have hSn : ∀ z : ℝ, 0 < z → z ^ 2 * z ^ (rgiSn α m - 1)
      * z ^ ((2 * (m : ℝ) + 5) / α - 1) = 1 := by
    intro z hz
    have hst : rgiSn α m + ((2 * (m : ℝ) + 5) / α - 1) = -1 := by
      simp only [rgiSn]; ring
    exact sq_mul_rpow_sub_one_mul hz hst
  have hSp : ∀ z : ℝ, 0 < z → z ^ 2 * z ^ (rgiSp α m - 1)
      * z ^ (-(2 * (m : ℝ) / α) - 1) = 1 := by
    intro z hz
    have hst : rgiSp α m + (-(2 * (m : ℝ) / α) - 1) = -1 := by
      simp only [rgiSp]; ring
    exact sq_mul_rpow_sub_one_mul hz hst
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz; exact mul_rpow_sub_one hz
  · intro z hz; exact sq_mul_rpow_sub_two hz
  · intro z hz; exact mul_rpow_sub_one hz
  · intro z hz; exact sq_mul_rpow_sub_two hz
  · intro z hz
    simp only [rgiF1]
    calc z ^ 2 * z ^ (rgiSn α m - 1) * (c z * z ^ ((2 * (m : ℝ) + 5) / α - 1))
        = c z * (z ^ 2 * z ^ (rgiSn α m - 1) * z ^ ((2 * (m : ℝ) + 5) / α - 1)) := by
          ring
      _ = c z * 1 := by rw [hSn z hz]
      _ = c z := by ring
  · intro z hz
    simp only [rgiF2]
    calc z ^ 2 * z ^ (rgiSp α m - 1) * (c z * z ^ (-(2 * (m : ℝ) / α) - 1))
        = c z * (z ^ 2 * z ^ (rgiSp α m - 1) * z ^ (-(2 * (m : ℝ) / α) - 1)) := by
          ring
      _ = c z * 1 := by rw [hSp z hz]
      _ = c z := by ring

end Work.FTS.PhiStar.Series.Deleg
