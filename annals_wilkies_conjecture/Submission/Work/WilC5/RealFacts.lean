/-
  WilC5 — the `LEc`/`LRc` structures on `ℝ` and the definable restricted exponential.

  The `rexp`-reduct (`Bridge.lean`) of the standard `LEc`-structure on `ℝ` is the `LRc`-structure
  whose `rexp` symbol is the function `rexpFromExp`, i.e. `exp` on `[-1,1]` and `0` outside.  That
  is (semantically) exactly the `rexp` of the frozen vocabulary, so the `rexp`-reduct of `ℝ` is the
  standard model of `TR`.  This module records those facts.
-/
import Submission.Work.WilC5.Bridge
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-! ## 1. The semantic operations of the `LEc`-structure on `ℝ` -/

theorem addE_real (x y : ℝ) : addE x y = x + y := by
  show @Structure.funMap Language.ring ℝ _ 2 Ring.addFunc ![x, y] = x + y
  simp [Ring.CompatibleRing.funMap_add]

theorem mulE_real (x y : ℝ) : mulE x y = x * y := by
  show @Structure.funMap Language.ring ℝ _ 2 Ring.mulFunc ![x, y] = x * y
  simp [Ring.CompatibleRing.funMap_mul]

theorem negE_real (x : ℝ) : negE x = -x := by
  show @Structure.funMap Language.ring ℝ _ 1 Ring.negFunc ![x] = -x
  simp [Ring.CompatibleRing.funMap_neg, Matrix.cons_val_fin_one]

theorem zeroE_real : (zeroE : ℝ) = 0 := by
  show @Structure.funMap Language.ring ℝ _ 0 Ring.zeroFunc default = 0
  simp [Ring.CompatibleRing.funMap_zero]

theorem oneE_real : (oneE : ℝ) = 1 := by
  show @Structure.funMap Language.ring ℝ _ 0 Ring.oneFunc default = 1
  simp [Ring.CompatibleRing.funMap_one]

theorem expE_real (x : ℝ) : expE x = Real.exp x := by
  show Real.exp (![x] (0 : Fin 1)) = Real.exp x
  simp

theorem subE_real (x y : ℝ) : subE x y = x - y := by
  rw [subE, addE_real, negE_real]
  ring

/-! ## 2. Squares, `|x| ≤ 1` and the restricted exponential on `ℝ` -/

theorem isSquare_real (y : ℝ) : isSquare y ↔ 0 ≤ y := by
  rw [isSquare]
  simp only [mulE_real]
  constructor
  · rintro ⟨z, hz⟩
    rw [← hz]
    exact mul_self_nonneg z
  · intro h
    exact ⟨Real.sqrt y, by simpa [sq] using Real.sq_sqrt h⟩

theorem absLeOne_real (y : ℝ) : absLeOne y ↔ |y| ≤ 1 := by
  simp only [absLeOne, isSquare_real, subE_real, addE_real, oneE_real, abs_le]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨by linarith, by linarith⟩

/-- **The definable restricted exponential is `rexp` on `ℝ`.** -/
theorem rexpFromExp_real (y : ℝ) : rexpFromExp y = rexp y := by
  by_cases h : absLeOne y
  · simp only [rexpFromExp, rexp, h, (absLeOne_real y).mp h, expE_real, ↓reduceIte]
  · have h' : ¬ (|y| ≤ 1) := fun hh => h ((absLeOne_real y).mpr hh)
    simp [rexpFromExp, rexp, h, h', zeroE_real]

/-! ## 3. The `rexp`-reduct of `ℝ` is the standard `LRc`-structure on `ℝ` -/

/-- **The `rexp`-reduct of the standard `LEc`-structure on `ℝ` is the standard `LRc`-structure
on `ℝ`** (the one in which `rexp` is the restricted exponential of the frozen vocabulary). -/
theorem reductStruct_real_eq : reductStruct ℝ = (inferInstance : LRc.Structure ℝ) := by
  ext n f x
  · rcases f with (g | c)
    · rcases g with (g | r)
      · rfl
      · cases r
        show rexpFromExp (x 0) = rexp (x 0)
        exact rexpFromExp_real (x 0)
    · rfl
  · nomatch f

end Work.WilC5
