import Mathlib
import Submission.Work.Arithmetic.CMDefs

namespace Work.Arithmetic.PigeonholeAux

theorem uOf_mul_conj {K : Type*} [Field K] [NumberField K] [NumberField.IsCMField K]
    (x y : NumberField.RingOfIntegers K) (hx : x ≠ 0) (hy : y ≠ 0) :
    Work.Arithmetic.uOf x y * NumberField.IsCMField.complexConj K (Work.Arithmetic.uOf x y) = 1 := by
  have hxK : (x : K) ≠ 0 := by
    intro h; apply hx; exact Subtype.ext h
  have hyK : (y : K) ≠ 0 := by
    intro h; apply hy; exact Subtype.ext h
  have hinj : Function.Injective (NumberField.IsCMField.complexConj K) :=
    (NumberField.IsCMField.complexConj K).injective
  have hcx : NumberField.IsCMField.complexConj K (x : K) ≠ 0 := by
    intro h
    apply hxK
    have h0 := map_zero (NumberField.IsCMField.complexConj K)
    exact hinj (by rw [h, h0])
  have hcy : NumberField.IsCMField.complexConj K (y : K) ≠ 0 := by
    intro h
    apply hyK
    have h0 := map_zero (NumberField.IsCMField.complexConj K)
    exact hinj (by rw [h, h0])
  rw [Work.Arithmetic.uOf_def]
  simp only [map_mul, map_div₀, NumberField.IsCMField.complexConj_apply_apply]
  field_simp

end Work.Arithmetic.PigeonholeAux
