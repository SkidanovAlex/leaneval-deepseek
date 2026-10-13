import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.H2.DivQ.primIntegrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.H2.DivQ

/-- The `(k+1)`-st derivative of `f` is continuous on the *open* interval `(0,x₁)`, from
`ContDiffOn ℝ ⊤ f (Ioc 0 x₁)` (via `iteratedDerivWithin`). -/
private lemma continuousOn_iteratedDeriv_Ioo (k : ℕ) (x₁ : ℝ) (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioc 0 x₁)) :
    ContinuousOn (iteratedDeriv (k + 1) f) (Set.Ioo 0 x₁) := by
  have hIoo : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioo 0 x₁) := hf.mono Set.Ioo_subset_Ioc_self
  have hcW : ContinuousOn (iteratedDerivWithin (k + 1) f (Set.Ioo 0 x₁)) (Set.Ioo 0 x₁) :=
    hIoo.continuousOn_iteratedDerivWithin (by simp) (uniqueDiffOn_Ioo 0 x₁)
  exact hcW.congr (fun x hx => (iteratedDerivWithin_of_isOpen isOpen_Ioo hx).symm)

theorem primitiveDerivData (k : ℕ) (γ x₁ : ℝ) (hx₁ : 0 < x₁) (hγ : -1 < γ)
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioc 0 x₁))
    (hint : MeasureTheory.IntegrableOn
      (fun x : ℝ => x ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f x) ^ 2)
      (Set.Ioc 0 x₁)) :
    MeasureTheory.IntegrableOn (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s)
        (Set.Ioc 0 x₁) ∧
      ContinuousOn (fun t : ℝ => ∫ s in (0 : ℝ)..t, s ^ k * iteratedDeriv (k + 1) f s)
        (Set.Icc 0 x₁) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) x₁,
        HasDerivAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, s ^ k * iteratedDeriv (k + 1) f s)
          (t ^ k * iteratedDeriv (k + 1) f t) t) := by
  -- `f` is `C^∞` on the open interval `(0,x₁)`, so `s ↦ s^k·f^{(k+1)}(s)` is continuous there.
  have hc : ContinuousOn (iteratedDeriv (k + 1) f) (Set.Ioo 0 x₁) :=
    continuousOn_iteratedDeriv_Ioo k x₁ f hf
  have hcont : ContinuousOn (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s) (Set.Ioo 0 x₁) :=
    (continuousOn_id.pow k).mul hc
  -- First conjunct: the AM–GM/Cauchy–Schwarz argument of `primIntegrable`.
  have hIoc : MeasureTheory.IntegrableOn
      (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s) (Set.Ioc 0 x₁) :=
    primIntegrable k γ x₁ hx₁ hγ f hf hint
  -- The same integrability on the closed interval `[0,x₁]` (the two differ by the null set `{0}`).
  have hIcc : MeasureTheory.IntegrableOn
      (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s) (Set.Icc 0 x₁) :=
    hIoc.congr_set_ae (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := 0) (b := x₁)).symm
  refine ⟨hIoc, ?_, ?_⟩
  · -- Second conjunct: continuity of the primitive on `[0,x₁]`.
    have h := intervalIntegral.continuousOn_primitive_interval (a := (0 : ℝ)) (b := x₁)
      (μ := volume) (f := fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s)
      (by rwa [Set.uIcc_of_le hx₁.le])
    simpa [Set.uIcc_of_le hx₁.le] using h
  · -- Third conjunct: the fundamental theorem of calculus at an interior point.
    intro t ht
    have ht0 : 0 < t := ht.1
    have htx : t < x₁ := ht.2
    -- `IntervalIntegrable` on `0..t` reduces to `IntegrableOn (Ioc 0 t)`, which is contained in
    -- `Ioc 0 x₁`; the other half of the definition is an empty interval.
    have hII : IntervalIntegrable (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s)
        volume 0 t := by
      refine ⟨hIoc.mono_set (Set.Ioc_subset_Ioc_right htx.le), ?_⟩
      refine MeasureTheory.IntegrableOn.of_measure_zero ?_
      rw [Set.Ioc_eq_empty (not_lt.mpr ht0.le)]
      exact measure_empty
    -- Continuity of the integrand at `t`.
    have hcat : ContinuousAt (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s) t :=
      ((continuous_pow k).continuousAt).mul
        (hc.continuousAt (isOpen_Ioo.mem_nhds ⟨ht0, htx⟩))
    -- Local strong measurability, from continuity on a small subinterval of `(0,x₁)`.
    have hsl : StronglyMeasurableAtFilter (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s)
        (nhds t) volume := by
      refine ⟨Set.Ioo (t / 2) ((t + x₁) / 2), ?_, ?_⟩
      · exact IsOpen.mem_nhds isOpen_Ioo ⟨by linarith, by linarith⟩
      · refine (hcont.mono ?_).aestronglyMeasurable measurableSet_Ioo
        intro y hy
        exact ⟨by linarith [hy.1, ht0], by linarith [hy.2, htx]⟩
    exact intervalIntegral.integral_hasDerivAt_right hII hsl hcat

end Work.FTS.H2.DivQ
