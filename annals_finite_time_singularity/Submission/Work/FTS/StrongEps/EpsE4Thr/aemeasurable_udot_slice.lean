import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.EpsE4Thr.DiaDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `aemeasurable_udot_slice`

If a family `(σ, p) ↦ u σ p.1 p.2` has a.e.-measurable slices in `σ` and is, for a.e. `p`,
differentiable in `σ` on `(0,T)` with derivative `udot σ p.1 p.2`, then the time-derivative slice
`p ↦ udot τ p.1 p.2` is a.e.-measurable (for every `τ ∈ (0,T)`).

The proof is the classical "derivative = limit of difference quotients" argument: on the conull set
of `p` where the derivative exists at `τ`, the sequence of difference quotients
`(c k)⁻¹ * (u (τ + c k) p.1 p.2 - u τ p.1 p.2)` with `c k = ((T-τ)/2)/(k+1)` converges to
`udot τ p.1 p.2`; each term is a.e.-measurable (a fixed real multiple of a difference of two
a.e.-measurable slices), and an a.e. limit of a.e.-measurable functions is a.e.-measurable
(`aemeasurable_of_tendsto_metrizable_ae'`).  The sequence `c k` is scaled by `(T-τ)/2` so that
`τ + c k ∈ (0,T)` for *every* `k`, which is what lets us invoke the hypothesis `hu`.
-/

open MeasureTheory Filter
open scoped Topology

namespace Work.FTS.StrongEps.EpsE4Thr

/-- If `F` has derivative `f'` at `τ` and `d ≠ 0`, then the difference quotients along the
explicit sequence `d/(k+1) → 0` converge to `f'`. -/
private lemma tendsto_slope_nat {F : ℝ → ℝ} {f' τ d : ℝ} (hd : d ≠ 0)
    (h : HasDerivAt F f' τ) :
    Tendsto (fun k : ℕ => (d / ((k : ℝ) + 1))⁻¹ * (F (τ + d / ((k : ℝ) + 1)) - F τ))
      atTop (𝓝 f') := by
  have h0 : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h1 : Tendsto (fun k : ℕ => d * ((1 : ℝ) / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using h0.const_mul d
  have hne : ∀ᶠ k : ℕ in atTop, d * ((1 : ℝ) / ((k : ℝ) + 1)) ≠ 0 := by
    filter_upwards with k
    have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    exact mul_ne_zero hd (ne_of_gt hk)
  have hc : Tendsto (fun k : ℕ => d * ((1 : ℝ) / ((k : ℝ) + 1))) atTop (𝓝[≠] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨h1, hne⟩
  have hcomp : Tendsto (fun k : ℕ => (d * ((1 : ℝ) / ((k : ℝ) + 1)))⁻¹ *
      (F (τ + d * ((1 : ℝ) / ((k : ℝ) + 1))) - F τ)) atTop (𝓝 f') := by
    simpa [smul_eq_mul, Function.comp_def] using h.tendsto_slope_zero.comp hc
  have heq : (fun k : ℕ => (d / ((k : ℝ) + 1))⁻¹ * (F (τ + d / ((k : ℝ) + 1)) - F τ)) =
      fun k : ℕ => (d * ((1 : ℝ) / ((k : ℝ) + 1)))⁻¹ *
        (F (τ + d * ((1 : ℝ) / ((k : ℝ) + 1))) - F τ) := by
    funext k
    simp [one_div, div_eq_mul_inv]
  rw [heq]
  exact hcomp

theorem aemeasurable_udot_slice {u udot : ℝ → Work.FTS.Galerkin.Fn} {T τ : ℝ}
    (hI : τ ∈ Set.Ioo (0:ℝ) T)
    (hu : ∀ σ ∈ Set.Ioo (0:ℝ) T, AEMeasurable (fun p : ℝ × ℝ => u σ p.1 p.2) diaM)
    (hderiv : ∀ᵐ p ∂diaM, ∀ s ∈ Set.Ioo (0:ℝ) T,
      HasDerivAt (fun t : ℝ => u t p.1 p.2) (udot s p.1 p.2) s) :
    AEMeasurable (fun p : ℝ × ℝ => udot τ p.1 p.2) diaM := by
  have hd : (0:ℝ) < (T - τ)/2 := by linarith [hI.1, hI.2]
  have hdne : (T - τ)/2 ≠ 0 := ne_of_gt hd
  have hσmem : ∀ k : ℕ, τ + (T - τ)/2/((k:ℝ)+1) ∈ Set.Ioo (0:ℝ) T := by
    intro k
    have hk : (0:ℝ) < (k:ℝ) + 1 := by positivity
    have hcpos : (0:ℝ) < (T - τ)/2/((k:ℝ)+1) := div_pos hd hk
    have hcle : (T - τ)/2/((k:ℝ)+1) ≤ (T - τ)/2 := by
      rw [div_le_iff₀ hk]
      have h1 : (1:ℝ) ≤ (k:ℝ) + 1 := by
        have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
        linarith
      simpa using mul_le_mul_of_nonneg_left h1 (le_of_lt hd)
    exact ⟨by linarith [hI.1, hcpos], by linarith [hI.2, hcle]⟩
  refine aemeasurable_of_tendsto_metrizable_ae' (μ := diaM)
    (f := fun k (p : ℝ × ℝ) => ((T - τ)/2/((k:ℝ)+1))⁻¹ *
        (u (τ + (T - τ)/2/((k:ℝ)+1)) p.1 p.2 - u τ p.1 p.2)) ?_ ?_
  · intro k
    exact ((hu _ (hσmem k)).sub (hu τ hI)).const_mul _
  · filter_upwards [hderiv] with p hp
    simpa using tendsto_slope_nat hdne (hp τ hI)

end Work.FTS.StrongEps.EpsE4Thr
