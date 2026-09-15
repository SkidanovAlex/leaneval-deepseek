import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Convex.Contractible

namespace Commons.Analysis.Complex

open MeasureTheory Filter

/-- A one-variable entire function on `ℂ` which vanishes on the real axis is zero.
This is the identity theorem for analytic functions, in the form that zeroes accumulating at `0`
force the function to vanish identically. -/
lemma entire_eq_zero_of_eq_zero_on_real_axis {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h : ∀ x : ℝ, f (x : ℂ) = 0) : f = 0 := by
  have hcl : (0 : ℂ) ∈ closure ({z : ℂ | f z = 0} \ {0}) := by
    refine mem_closure_of_tendsto (b := atTop)
      (f := fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) ?_ ?_
    · have h1 : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) : ℝ)) atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      exact (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp h1
    · refine Eventually.of_forall fun n => ?_
      simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      exact ⟨h _, by simp only [Complex.ofReal_eq_zero]; positivity⟩
  have han : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hzero := han.eqOn_zero_of_preconnected_of_mem_closure (U := Set.univ)
    isPreconnected_univ (Set.mem_univ 0) hcl
  exact funext fun z => hzero (Set.mem_univ z)

/-- An entire function on `ℂ^d` which vanishes on the "real subspace" `ℝ^d` is zero. -/
lemma entire_eq_zero_of_eq_zero_on_real_coords {d : ℕ} {φ : (Fin d → ℂ) → ℂ}
    (hφ : Differentiable ℂ φ)
    (h : ∀ y : Fin d → ℝ, φ (fun i => (y i : ℂ)) = 0) : φ = 0 := by
  funext ζ
  set a : Fin d → ℝ := fun i => (ζ i).re with ha
  set w : Fin d → ℝ := fun i => (ζ i).im with hw
  set g : ℂ → ℂ := fun z => φ (fun i => (a i : ℂ) + z * (w i : ℂ)) with hg
  have hgdiff : Differentiable ℂ g := by
    rw [hg]
    exact hφ.comp (by fun_prop)
  have hgreal : ∀ x : ℝ, g (x : ℂ) = 0 := by
    intro x
    change φ (fun i => (a i : ℂ) + (x : ℂ) * (w i : ℂ)) = 0
    have hvec : (fun i => (a i : ℂ) + (x : ℂ) * (w i : ℂ))
        = fun i => ((a i + x * w i : ℝ) : ℂ) := by
      funext i; simp [Complex.ofReal_add, Complex.ofReal_mul]
    rw [hvec]
    exact h (fun i => a i + x * w i)
  have hgzero : g = 0 := entire_eq_zero_of_eq_zero_on_real_axis hgdiff hgreal
  have hval : φ (fun i => (a i : ℂ) + Complex.I * (w i : ℂ)) = 0 := by
    have h1 := congr_fun hgzero Complex.I
    rw [hg] at h1
    simpa using h1
  have harg : (fun i => (a i : ℂ) + Complex.I * (w i : ℂ)) = ζ := by
    funext i
    simp only [ha, hw]
    rw [mul_comm]
    exact Complex.re_add_im (ζ i)
  rwa [harg] at hval

/-- **Identity theorem, measure-theoretic form.**  An entire function on `ℂ^d` whose restriction to
the real subspace `ℝ^d ⊂ ℂ^d` vanishes almost everywhere (w.r.t. Lebesgue measure on `ℝ^d`) is
identically zero. -/
theorem differentiable_eq_zero_of_ae_eq_zero_on_real {d : ℕ} {φ : (Fin d → ℂ) → ℂ}
    (hφ : Differentiable ℂ φ)
    (h : (fun x : EuclideanSpace ℝ (Fin d) => φ (fun i => (x i : ℂ)))
          =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))] 0) :
    φ = 0 := by
  have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin d) => φ (fun i => (x i : ℂ))) := by
    refine hφ.continuous.comp ?_
    apply continuous_pi
    intro i
    exact Complex.continuous_ofReal.comp
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) i)
  have hzero : (fun x : EuclideanSpace ℝ (Fin d) => φ (fun i => (x i : ℂ))) = 0 :=
    (Continuous.ae_eq_iff_eq volume hcont continuous_const).mp h
  refine entire_eq_zero_of_eq_zero_on_real_coords hφ fun y => ?_
  have h1 := congr_fun hzero (WithLp.toLp 2 y)
  simpa using h1

end Commons.Analysis.Complex