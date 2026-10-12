import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Order.Group.Lattice
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S.FlatFib

open MeasureTheory

/-- Shifting a real function by a constant does not change the finiteness of the
integral of its absolute value on a set of finite measure: if `∫⁻ |f| = ⊤` on `A`
and `volume A ≠ ⊤`, then also `∫⁻ |f + c| = ⊤` on `A`. -/
theorem lintegralAbsAddConstEqTop {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hfin : (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) A ≠ ⊤)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : Measurable f)
    (htop : ∫⁻ z in A, ENNReal.ofReal |f z| = ⊤) (c : ℝ) :
    ∫⁻ z in A, ENNReal.ofReal |f z + c| = ⊤ := by
  -- pointwise: `|w| ≤ |w + c| + |c|`, lifted to `ℝ≥0∞`
  have hpt : ∀ w : ℝ, ENNReal.ofReal |w| ≤ ENNReal.ofReal |w + c| + ENNReal.ofReal |c| := by
    intro w
    rw [congrArg (fun t : ℝ => ENNReal.ofReal |t|) (show w = (w + c) + (-c) from by ring)]
    calc ENNReal.ofReal |(w + c) + (-c)| ≤ ENNReal.ofReal (|w + c| + |(-c)|) :=
            ENNReal.ofReal_le_ofReal (abs_add_le _ _)
      _ ≤ ENNReal.ofReal |w + c| + ENNReal.ofReal |(-c)| := ENNReal.ofReal_add_le
      _ = ENNReal.ofReal |w + c| + ENNReal.ofReal |c| := by rw [abs_neg]
  have hfmeas : Measurable (fun z => ENNReal.ofReal |f z + c|) :=
    ENNReal.continuous_ofReal.measurable.comp ((hf.add_const c).abs)
  have hmono : ∫⁻ z in A, ENNReal.ofReal |f z| ≤
      ∫⁻ z in A, (ENNReal.ofReal |f z + c| + ENNReal.ofReal |c|) := by
    apply lintegral_mono; intro z
    exact hpt (f z)
  rw [lintegral_add_left hfmeas] at hmono
  rw [setLIntegral_const] at hmono
  have hgoal : (∫⁻ z in A, ENNReal.ofReal |f z + c|) + ENNReal.ofReal |c| * volume A = ⊤ :=
    top_le_iff.mp (htop ▸ hmono)
  rcases ENNReal.add_eq_top.mp hgoal with h | h
  · exact h
  · exact absurd h (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin)

end Work.BoseFixB1S.FlatFib
