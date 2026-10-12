import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.Rb5Lin

open MeasureTheory

noncomputable section

/-- The translation action of the lattice `ℤ³` on `ℝ³`: `m +ᵥ x = x + m` (coordinatewise). -/
instance latticeVAdd : VAdd (Fin 3 → ℤ) (Fin 3 → ℝ) where
  vadd m x := x + fun i => (m i : ℝ)

/-- The translation action of the lattice `ℤ³` on `ℝ³` is an additive action. -/
instance latticeAddAction : AddAction (Fin 3 → ℤ) (Fin 3 → ℝ) where
  toVAdd := latticeVAdd
  zero_vadd x := by
    change x + (fun i => ((0 : Fin 3 → ℤ) i : ℝ)) = x
    ext i
    simp only [Pi.add_apply, Pi.zero_apply, Int.cast_zero, add_zero]
  add_vadd m n x := by
    change x + (fun i => ((m + n) i : ℝ)) = (x + fun i => (n i : ℝ)) + fun i => (m i : ℝ)
    ext i
    simp only [Pi.add_apply, Int.cast_add]
    ring

/-- Translates are measurable. -/
instance latticeMeasurableConstVAdd : MeasurableConstVAdd (Fin 3 → ℤ) (Fin 3 → ℝ) where
  measurable_const_vadd c := by
    show Measurable (fun x : Fin 3 → ℝ => x + fun i => (c i : ℝ))
    fun_prop

/-- Lebesgue measure on `ℝ³` is invariant under the lattice action. -/
instance latticeVAddInvariantMeasure : VAddInvariantMeasure (Fin 3 → ℤ) (Fin 3 → ℝ) volume where
  measure_preimage_vadd c s hs := by
    have h : (fun x : Fin 3 → ℝ => c +ᵥ x) = (fun x => x + fun i => (c i : ℝ)) := rfl
    rw [h]
    exact (measurePreserving_add_right volume _).measure_preimage hs.nullMeasurableSet

/-- The lattice point `m ∈ ℤ³` as a vector of `ℝ³`. -/
def latPoint (m : Fin 3 → ℤ) : Fin 3 → ℝ := fun i => (m i : ℝ)

/-- The fundamental box `(0,1]³` for the lattice `ℤ³` acting on `ℝ³`.
(This is the half-open box used by `UnitAddTorus.mFourierCoeff_eq_integral` with `a = 0`.) -/
def box3 : Set (Fin 3 → ℝ) := {x | ∀ i, x i ∈ Set.Ioc (0 : ℝ) (0 + 1)}

@[simp] lemma latPoint_apply (m : Fin 3 → ℤ) (i : Fin 3) : latPoint m i = (m i : ℝ) := rfl

@[simp] lemma vadd_eq_add_latPoint (m : Fin 3 → ℤ) (x : Fin 3 → ℝ) :
    m +ᵥ x = x + latPoint m := rfl

lemma mem_box3 {x : Fin 3 → ℝ} : x ∈ box3 ↔ ∀ i, x i ∈ Set.Ioc (0 : ℝ) (0 + 1) := Iff.rfl

end

end Work.BoseFixR.Rb5Lin
