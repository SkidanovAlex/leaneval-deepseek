import Mathlib
import Submission.Work.WilC5.S4ExpF.Bridge
import Submission.Work.WilC5.logFun_mul
import Submission.Work.WilC5.logFun_expE

namespace Work.WilC5.S4ExpF

/-- The definable logarithm of `1` is `0` in a model of `TE` (equivalently `log (exp 0) = 0`). -/
theorem logFun_one_eq_zero {K : Type} [WilkiesDesign.CG.LEc.Structure K] [Field K]
    [LinearOrder K] [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    (hTE : FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE)
    (hadd : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hone : (Work.WilC5.oneE : K) = 1) :
    Work.WilC5.logFun (1 : K) = 0 := by
  have h := Work.WilC5.logFun_expE hTE (Work.WilC5.zeroE : K)
  rw [expE_zeroE_of_model hTE, hone, zeroE_eq_zero hTE hadd] at h
  exact h

/-- **Multiplicativity of the definable logarithm on positive elements**, in field form:
`log (x * y) = log x + log y` for `0 < x`, `0 < y` in a model of `TE`. -/
theorem logFun_mul_of_pos {K : Type} [WilkiesDesign.CG.LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    (hTE : FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE)
    (hadd : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hmul : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hleneg : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y)
    {x y : K} (hx : 0 < x) (hy : 0 < y) :
    Work.WilC5.logFun (x * y) = Work.WilC5.logFun x + Work.WilC5.logFun y := by
  have hx' := (leE_zero_iff hTE hadd hleneg x).mpr hx
  have hy' := (leE_zero_iff hTE hadd hleneg y).mpr hy
  have h := Work.WilC5.logFun_mul hTE hx' hy'
  rwa [hmul x y, hadd (Work.WilC5.logFun x) (Work.WilC5.logFun y)] at h

theorem logFun_pow_nat {K : Type} [WilkiesDesign.CG.LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    (hTE : FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE)
    (hadd : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hmul : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hone : (Work.WilC5.oneE : K) = 1)
    (hleneg : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y)
    (x : K) (hx : 0 < x) (n : ℕ) :
    Work.WilC5.logFun (x ^ n) = (n : K) * Work.WilC5.logFun x := by
  induction n with
  | zero =>
    have h1 := logFun_one_eq_zero hTE hadd hone
    simpa using h1
  | succ n ih =>
    have hxn : (0 : K) < x ^ n := pow_pos hx n
    have hstep : Work.WilC5.logFun (x ^ n * x) =
        Work.WilC5.logFun (x ^ n) + Work.WilC5.logFun x :=
      logFun_mul_of_pos hTE hadd hmul hleneg hxn hx
    rw [pow_succ, hstep, ih]
    push_cast
    ring

end Work.WilC5.S4ExpF
