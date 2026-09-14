import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

open Set

namespace Commons.MeasureTheory.Integral

theorem absolutelyContinuousOnInterval_add_lipschitzWith {E : Type*} [NormedAddCommGroup E]
    {f g : Real → E} {a b : Real} {K : NNReal} (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : LipschitzWith K g) :
    AbsolutelyContinuousOnInterval (fun t : Real => f t + g t) a b := by
  have hg' : AbsolutelyContinuousOnInterval g a b :=
    (hg.lipschitzOnWith (s := uIcc a b)).absolutelyContinuousOnInterval
  have h := hf.add hg'
  rw [show (f + g) = (fun t : Real => f t + g t) from rfl] at h
  exact h

end Commons.MeasureTheory.Integral