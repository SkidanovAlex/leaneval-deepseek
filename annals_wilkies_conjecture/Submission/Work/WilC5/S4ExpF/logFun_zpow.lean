/-
  WilC5 / S4ExpF — the definable logarithm is compatible with integral powers.

      `logFun (x ^ n) = n * logFun x`   for `0 < x`, `n : ℤ`.

  The proof is the additive law of `logFun` on *positive* elements
  (`Work.WilC5.logFun_mul`), together with the two facts

  * `logFun 1 = 0`, from `logFun (exp 0) = 0` (`Work.WilC5.logFun_expE`) and `exp 0 = 1`
    (`Work.WilC5.S4ExpF.expE_zeroE_of_model`), and
  * `logFun x⁻¹ = - logFun x`, which follows from `logFun (x * x⁻¹) = logFun 1 = 0`.

  For `n : ℕ` one inducts on `n` (`x ^ (n+1) = x ^ n * x`); for `n < 0` one writes
  `n = -(m : ℤ)` with `m : ℕ`, so that `x ^ n = (x ^ m)⁻¹` and the inverse law applies.

  The bridges `hadd`, `hmul`, `hone`, `hleneg` identify the `LEc`-symbols of `K` with the field
  structure (`Bridge.lean`), in particular `leE zeroE · ∧ ¬ leE · zeroE` is `0 < ·`
  (`Work.WilC5.S4ExpF.leE_zero_iff`), which is what `logFun_mul` needs.
-/
import Mathlib
import Submission.Work.WilC5.S4ExpF.Bridge
import Submission.Work.WilC5.logFun_mul
import Submission.Work.WilC5.logFun_expE
import Submission.Work.WilC5.LogDefSetModel
import Submission.Work.WilC5.ReductEmb

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilC5.S4ExpF

theorem logFun_zpow {K : Type} [WilkiesDesign.CG.LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    (hTE : FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE)
    (hadd : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hmul : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hone : (Work.WilC5.oneE : K) = 1)
    (hleneg : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y)
    (x : K) (hx : 0 < x) (n : ℤ) :
    Work.WilC5.logFun (x ^ n) = (n : K) * Work.WilC5.logFun x := by
  -- `0 < y` in the field is the `LEc`-positivity `leE zeroE y ∧ ¬ leE y zeroE`.
  have hpos : ∀ y : K, 0 < y →
      (Work.WilC5.leE Work.WilC5.zeroE y ∧ ¬ Work.WilC5.leE y Work.WilC5.zeroE) :=
    fun y hy => (leE_zero_iff hTE hadd hleneg y).mpr hy
  -- The additive law, in field notation.
  have hmul' : ∀ y z : K, 0 < y → 0 < z →
      Work.WilC5.logFun (y * z) = Work.WilC5.logFun y + Work.WilC5.logFun z := by
    intro y z hy hz
    rw [← hmul y z, Work.WilC5.logFun_mul hTE (hpos y hy) (hpos z hz), hadd]
  -- `log 1 = 0`.
  have hlog1 : Work.WilC5.logFun (1 : K) = 0 := by
    have h := Work.WilC5.logFun_expE hTE (Work.WilC5.zeroE : K)
    rw [expE_zeroE_of_model hTE, hone] at h
    rw [h, zeroE_eq_zero hTE hadd]
  -- `log y⁻¹ = - log y` for `y > 0`.
  have hinv : ∀ y : K, 0 < y → Work.WilC5.logFun y⁻¹ = -Work.WilC5.logFun y := by
    intro y hy
    have h := hmul' y y⁻¹ hy (inv_pos.mpr hy)
    rw [mul_inv_cancel₀ (ne_of_gt hy), hlog1] at h
    linarith [h]
  -- The natural-power case.
  have hnat : ∀ m : ℕ, Work.WilC5.logFun (x ^ m) = (m : K) * Work.WilC5.logFun x := by
    intro m
    induction m with
    | zero => simp [hlog1]
    | succ m ih =>
      rw [pow_succ, hmul', ih]
      · push_cast; ring
      · exact pow_pos hx m
      · exact hx
  rcases le_or_gt 0 n with hn | hn
  · -- `n = (m : ℤ)` with `m : ℕ`
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hn
    rw [hm, zpow_natCast, Int.cast_natCast]
    exact hnat m
  · -- `n = -(m : ℤ)` with `m : ℕ`, so `x ^ n = (x ^ m)⁻¹`
    have hm : (0 : ℤ) < -n := by omega
    obtain ⟨m, hmn⟩ := Int.eq_ofNat_of_zero_le (le_of_lt hm)
    have hn' : n = -(↑m : ℤ) := by omega
    rw [hn', zpow_neg, zpow_natCast, hinv (x ^ m) (pow_pos hx m), hnat m]
    push_cast
    ring

end Work.WilC5.S4ExpF
