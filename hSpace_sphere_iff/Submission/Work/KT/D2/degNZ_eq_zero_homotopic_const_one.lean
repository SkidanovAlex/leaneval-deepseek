import Mathlib
import Submission.Work.KT.D2.Winding

namespace Work.KT.D2

/-- A nowhere-zero complex loop has winding number `0` exactly when the underlying loop of units
factors through the exponential, and then it is null-homotopic: the logarithmic lift `F` provides
the explicit homotopy `(t, x) ↦ exp ((1 - t) · F x)`, which at `t = 0` is `F`-exponentiated and at
`t = 1` is the constant loop `1`. -/
theorem degNZ_eq_zero_homotopic_const_one
    (f : C(Work.KT.Sph (EuclideanSpace ℝ (Fin 2)), ℂ)) (hf : ∀ x, f x ≠ 0)
    (h : Work.KT.D2.degNZ f hf = 0) :
    ContinuousMap.Homotopic (Work.KT.D2.toUnits f hf)
      (ContinuousMap.const (Work.KT.Sph (EuclideanSpace ℝ (Fin 2))) 1) := by
  obtain ⟨F, hF⟩ := (deg2_zero_iff (toUnits f hf)).mp h
  refine ⟨ContinuousMap.Homotopy.mk ?H ?h0 ?h1⟩
  · refine ⟨fun p => (unitsHomeomorphNeZero (G₀ := ℂ)).symm
        ⟨Complex.exp ((1 - (p.1 : ℝ)) * F p.2), Complex.exp_ne_zero _⟩, ?_⟩
    fun_prop
  · intro x
    apply Units.ext
    simp [unitsHomeo_symm_val, hF x]
  · intro x
    apply Units.ext
    simp [unitsHomeo_symm_val]

end Work.KT.D2
