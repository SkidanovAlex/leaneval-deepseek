import Mathlib.Probability.Independence.InfinitePi

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Commons.Probability.Independence

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Curry direction of independence for a two-parameter family of real random
variables: if the flat family `(X i j : Ω → ℝ)` indexed by pairs `(i, j)` is
independent, then the grouped family `i ↦ (j ↦ X i j)` (a family of random
variables with values in the product `κ → ℝ`) is independent.  (Non-dependent
`κ` version; used to make the rows of an independent-entry matrix independent.) -/
theorem iIndepFun_curry_flat_real {ι κ Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ι → κ → Ω → ℝ) (mX : ∀ i j, Measurable (X i j))
    (hflat : iIndepFun (fun p : ι × κ => X p.1 p.2) P) :
    iIndepFun (fun i ω => fun j : κ => X i j ω) P := by
  classical
  letI hP : IsProbabilityMeasure P := hflat.isProbabilityMeasure
  -- Flat joint law: independence of the flat family says its joint distribution is the
  -- infinite product of the coordinate laws.
  have hflat_joint :
      P.map (fun (ω) (p : ι × κ) => X p.1 p.2 ω) =
        Measure.infinitePi (fun p : ι × κ => P.map (fun ω => X p.1 p.2 ω)) := by
    exact (iIndepFun_iff_map_fun_eq_infinitePi_map (X := fun p : ι × κ => fun ω => X p.1 p.2 ω)
      (mX := fun p => mX p.1 p.2)).mp hflat
  -- Within each row: the entries `(X i j)_j` are independent, so the law of the row
  -- `(j ↦ X i j)` is the infinite product of its coordinate laws.
  have hrow_joint : ∀ i : ι,
      P.map (fun (ω) (j : κ) => X i j ω) =
        Measure.infinitePi (fun j : κ => P.map (fun ω => X i j ω)) := by
    intro i
    have hpre : iIndepFun (fun j : κ => fun ω => X i j ω) P := by
      have hinj : Function.Injective (fun j : κ => (i, j)) := by
        intro a b hab
        exact congrArg Prod.snd hab
      simpa using
        (iIndepFun.precomp (f := fun p : ι × κ => fun ω => X p.1 p.2 ω) hinj hflat)
    exact (iIndepFun_iff_map_fun_eq_infinitePi_map (X := fun j : κ => fun ω => X i j ω)
      (mX := fun j => mX i j)).mp hpre
  -- The rows are independent iff the law of the curried joint variable is the product of
  -- the row laws.  Currying commutes with taking the product measure (`infinitePi_map_curry`).
  refine (iIndepFun_iff_map_fun_eq_infinitePi_map
    (X := fun i : ι => (fun ω : Ω => fun j : κ => X i j ω))
    (mX := fun i => (measurable_pi_iff.mpr (fun j => mX i j)))).mpr ?_
  have hYmeas : Measurable (fun ω (p : ι × κ) => X p.1 p.2 ω) :=
    measurable_pi_iff.mpr (fun p : ι × κ => mX p.1 p.2)
  have hcurry_comp : (fun ω (i : ι) (j : κ) => X i j ω) =
      (MeasurableEquiv.curry ι κ ℝ) ∘ (fun ω (p : ι × κ) => X p.1 p.2 ω) := by
    ext ω i j
    simp
  calc
    P.map (fun ω (i : ι) (j : κ) => X i j ω)
        = (P.map (fun ω (p : ι × κ) => X p.1 p.2 ω)).map (MeasurableEquiv.curry ι κ ℝ) := by
          rw [hcurry_comp]
          rw [← Measure.map_map (MeasurableEquiv.curry ι κ ℝ).measurable hYmeas]
    _ = (Measure.infinitePi (fun p : ι × κ => P.map (fun ω => X p.1 p.2 ω))).map
          (MeasurableEquiv.curry ι κ ℝ) := by rw [hflat_joint]
    _ = Measure.infinitePi (fun i : ι =>
          Measure.infinitePi (fun j : κ => P.map (fun ω => X i j ω))) := by
          letI : ∀ i j, IsProbabilityMeasure (P.map (fun ω => X i j ω)) :=
            fun i j => Measure.isProbabilityMeasure_map (mX i j).aemeasurable
          simpa using (Measure.infinitePi_map_curry (X := ℝ)
            (μ := fun i j => P.map (fun ω => X i j ω)))
    _ = Measure.infinitePi (fun i : ι => P.map (fun (ω) (j : κ) => X i j ω)) := by
          apply congrArg Measure.infinitePi
          funext i
          rw [hrow_joint i]

end Commons.Probability.Independence