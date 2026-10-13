import Mathlib
import Submission.Work.DSG4c.ChartPushout.Defs

universe u

namespace Work.DSG2.Segre

theorem projChart_relation (A : Type u) [CommRing A] (n : ℕ) (i i' m : Fin (n+1)) :
    HomogeneousLocalization.awayMap (DSMap.PGr A n) (Work.DSG4c.X_mem A n i') rfl
        (Work.DSG4c.ChartPushout.chartElemAll A n i m)
      = HomogeneousLocalization.awayMap (DSMap.PGr A n) (Work.DSG4c.X_mem A n i)
          (mul_comm (MvPolynomial.X i) (MvPolynomial.X i'))
          (Work.DSG4c.ChartPushout.chartElemAll A n i' m)
        * HomogeneousLocalization.awayMap (DSMap.PGr A n) (Work.DSG4c.X_mem A n i') rfl
            (Work.DSG4c.ChartPushout.chartElemAll A n i i') := by
  -- All three entries are of the form `X k / X i` resp. `X k / X i'`; after rewriting along
  -- `awayMap` (which sends `a / f ^ n` to `a * g ^ n / (f * g) ^ n`) the claim becomes the
  -- identity `(X m * X i') / (X i * X i') = ((X m * X i) * (X i' * X i')) / (X i * X i')²`
  -- in the localization at `X i * X i'`, which holds by cross-multiplication.
  apply (HomogeneousLocalization.ext_iff_val _ _).mpr
  simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.awayMap_mk,
    Work.DSG4c.ChartPushout.chartElemAll]
  simp only [HomogeneousLocalization.Away.val_mk]
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, one_mul, Submonoid.coe_mul, pow_one]
  ring

end Work.DSG2.Segre
