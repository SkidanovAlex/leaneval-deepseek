import Mathlib

namespace Work.WilE2

/-- Mirror of `eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right`: a continuous function on
`[a, b]` that vanishes at the *right* endpoint `b` and whose left derivative is bounded by `K` times
its value must vanish on all of `[a, b]`.

Proof: reflect, i.e. apply the right-endpoint version to `t ↦ f (a + b - t)`. -/
lemma eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_left {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f f' : ℝ → E} {K a b : ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hf' : ∀ x ∈ Set.Ioc a b, HasDerivWithinAt f (f' x) (Set.Iic x) x)
    (hb : f b = 0) (bound : ∀ x ∈ Set.Ioc a b, ‖f' x‖ ≤ K * ‖f x‖) :
    ∀ x ∈ Set.Icc a b, f x = 0 := by
  -- the reflection `y ↦ a + b - y` maps `[a, b]` to itself
  have hmaps : Set.MapsTo (fun y : ℝ => a + b - y) (Set.Icc a b) (Set.Icc a b) := by
    intro y hy
    have hy1 : a ≤ y := (Set.mem_Icc.mp hy).1
    have hy2 : y ≤ b := (Set.mem_Icc.mp hy).2
    exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  have hcont : ContinuousOn (fun t : ℝ => f (a + b - t)) (Set.Icc a b) := by
    have hc : Continuous fun t : ℝ => a + b - t := by fun_prop
    simpa [Function.comp_def] using ContinuousOn.comp hf hc.continuousOn hmaps
  have hleft : ∀ y ∈ Set.Icc a b, f (a + b - y) = 0 := by
    apply eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
      (f := fun t : ℝ => f (a + b - t))
      (f' := fun t : ℝ => (-1 : ℝ) • f' (a + b - t))
    · exact hcont
    · intro t ht
      have ht1 : a ≤ t := (Set.mem_Ico.mp ht).1
      have ht2 : t < b := (Set.mem_Ico.mp ht).2
      have hu : a + b - t ∈ Set.Ioc a b := Set.mem_Ioc.mpr ⟨by linarith, by linarith⟩
      have hh : HasDerivWithinAt (fun y : ℝ => a + b - y) (-1) (Set.Ici t) t :=
        ((hasDerivAt_id t).const_sub (a + b)).hasDerivWithinAt
      have hst : Set.MapsTo (fun y : ℝ => a + b - y) (Set.Ici t) (Set.Iic (a + b - t)) := by
        intro y hy
        have hy' : t ≤ y := hy
        show a + b - y ≤ a + b - t
        linarith
      have hcomp := HasDerivWithinAt.scomp t (hf' (a + b - t) hu) hh hst
      simpa [Function.comp_def] using hcomp
    · simpa using hb
    · intro t ht
      have ht1 : a ≤ t := (Set.mem_Ico.mp ht).1
      have ht2 : t < b := (Set.mem_Ico.mp ht).2
      have hu : a + b - t ∈ Set.Ioc a b := Set.mem_Ioc.mpr ⟨by linarith, by linarith⟩
      simpa using bound (a + b - t) hu
  intro x hx
  have hx1 : a ≤ x := (Set.mem_Icc.mp hx).1
  have hx2 : x ≤ b := (Set.mem_Icc.mp hx).2
  have hy : a + b - x ∈ Set.Icc a b := Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  have h := hleft (a + b - x) hy
  rwa [show a + b - (a + b - x) = x by ring] at h

end Work.WilE2
