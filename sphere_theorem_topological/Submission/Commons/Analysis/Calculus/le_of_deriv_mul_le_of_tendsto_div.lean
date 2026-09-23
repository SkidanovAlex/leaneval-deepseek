import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.Algebra.Module.ModuleTopology

open Filter
open scoped Topology

namespace Commons.Analysis.Calculus

theorem le_of_deriv_mul_le_of_tendsto_div {f g : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hf : ∀ t ∈ Set.Ioo 0 T, HasDerivAt f (deriv f t) t)
    (hg : ∀ t ∈ Set.Ioo 0 T, HasDerivAt g (deriv g t) t)
    (hgpos : ∀ t ∈ Set.Ioo 0 T, 0 < g t)
    (hineq : ∀ t ∈ Set.Ioo 0 T, deriv f t * g t ≤ deriv g t * f t)
    (hlim : Filter.Tendsto (fun t => f t / g t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)) :
    ∀ t ∈ Set.Ioo 0 T, f t ≤ g t := by
  intro t ht
  -- The quotient h = f / g is differentiable on (0, T) with derivative (f'g - fg')/g^2.
  have hderiv : ∀ s ∈ Set.Ioo (0:ℝ) T, HasDerivAt (f / g)
      ((deriv f s * g s - f s * deriv g s) / (g s) ^ 2) s := by
    intro s hs
    have hgs : g s ≠ 0 := ne_of_gt (hgpos s hs)
    exact (hf s hs).div (hg s hs) hgs
  -- That derivative is ≤ 0, so h is antitone on (0, T).
  have hderiv_nonpos : ∀ s ∈ Set.Ioo (0:ℝ) T, deriv (f / g) s ≤ 0 := by
    intro s hs
    rw [(hderiv s hs).deriv]
    have hnum : deriv f s * g s - f s * deriv g s ≤ 0 := by
      have := hineq s hs
      nlinarith [this]
    have hden : (0:ℝ) < (g s) ^ 2 := pow_pos (hgpos s hs) 2
    exact div_nonpos_of_nonpos_of_nonneg hnum (le_of_lt hden)
  have hanti : AntitoneOn (f / g) (Set.Ioo (0:ℝ) T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioo (0:ℝ) T)
    · intro s hs
      exact (hderiv s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ioo] at hs
      exact (hderiv s hs).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ioo] at hs
      exact hderiv_nonpos s hs
  -- Since h is antitone and tends to 1 as t → 0⁺, we must have h t ≤ 1.
  have hle1 : f t / g t ≤ 1 := by
    have ht0 : (0:ℝ) < t := ht.1
    have hev : ∀ᶠ s in (𝓝[>] (0:ℝ)), f t / g t ≤ f s / g s := by
      filter_upwards [Ioo_mem_nhdsGT ht0] with s hs
      exact hanti ⟨hs.1, lt_trans hs.2 ht.2⟩ ht (le_of_lt hs.2)
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim hev
  -- Finally multiply by g t > 0.
  have hgt : (0:ℝ) < g t := hgpos t ht
  have hstep : f t / g t * g t ≤ 1 * g t := mul_le_mul_of_nonneg_right hle1 (le_of_lt hgt)
  rw [div_mul_cancel₀ (f t) (ne_of_gt hgt), one_mul] at hstep
  exact hstep

end Commons.Analysis.Calculus