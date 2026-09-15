import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.NumberTheory.LSeries.RiemannZeta

open Filter
open scoped Topology

namespace Commons.NumberTheory.Zeta

theorem riemannZeta_inv_differentiableAt_imp_ne_zero {z : ℂ} (hz : z ≠ 0)
    (h : DifferentiableAt ℂ (fun u : ℂ => (riemannZeta (1 + u))⁻¹) z) :
    riemannZeta (1 + z) ≠ 0 := by
  intro hz0
  -- `1 + z ≠ 1`, so `riemannZeta` is analytic at `1 + z`
  have hw : (1 : ℂ) + z ≠ 1 := fun h1 => hz (by simpa using h1)
  have hzan : AnalyticAt ℂ riemannZeta (1 + z) := analyticOn_riemannZeta (1 + z) hw
  -- `ℂ \ {1}` is preconnected
  have hpre : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (E := ℂ)
      (Complex.rank_real_complex ▸ Nat.one_lt_ofNat) (1 : ℂ)).isPreconnected
  rcases hzan.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
  · -- `ζ` vanishes identically near `1 + z`: by the identity principle it vanishes
    -- on all of `ℂ \ {1}`, contradicting `ζ 0 = -1/2`.
    have hEqOn : Set.EqOn riemannZeta 0 ({1}ᶜ : Set ℂ) :=
      analyticOn_riemannZeta.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre hw hzero
    have h0 := hEqOn (by simp : (0 : ℂ) ∈ ({1}ᶜ : Set ℂ))
    rw [riemannZeta_zero] at h0
    exact (by norm_num : (-1 / 2 : ℂ) ≠ 0) h0
  · -- In a punctured neighbourhood of `z`, `(ζ (1+u))⁻¹ * ζ (1+u) = 1`.  On the other hand
    -- this product is continuous at `z` with value `(ζ (1+z))⁻¹ * ζ (1+z) = 0`.  Contradiction.
    have hcomp : Tendsto (fun u : ℂ => (1 : ℂ) + u) (𝓝[≠] z) (𝓝[≠] (1 + z)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have hc : Tendsto (fun u : ℂ => (1 : ℂ) + u) (𝓝 z) (𝓝 ((1 : ℂ) + z)) :=
          ((continuous_const : Continuous fun _ : ℂ => (1 : ℂ)).add continuous_id).tendsto z
        simpa using hc.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with u hu
        intro h1
        exact hu (add_left_cancel h1)
    have hne1 : ∀ᶠ u in 𝓝[≠] z, riemannZeta (1 + u) ≠ 0 := hcomp.eventually hne
    have hprod : ∀ᶠ u in 𝓝[≠] z,
        (riemannZeta (1 + u))⁻¹ * riemannZeta (1 + u) = 1 := by
      filter_upwards [hne1] with u hu
      exact inv_mul_cancel₀ hu
    have hg : DifferentiableAt ℂ (fun u : ℂ => riemannZeta (1 + u)) z :=
      (differentiableAt_riemannZeta hw).comp z
        ((differentiableAt_const (1 : ℂ)).add differentiableAt_id)
    have htend : Tendsto (fun u : ℂ => (riemannZeta (1 + u))⁻¹ * riemannZeta (1 + u))
        (𝓝[≠] z) (𝓝 ((riemannZeta (1 + z))⁻¹ * riemannZeta (1 + z))) :=
      (h.mul hg).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hone : (riemannZeta (1 + z))⁻¹ * riemannZeta (1 + z) = 1 :=
      tendsto_nhds_unique_of_eventuallyEq htend tendsto_const_nhds hprod
    rw [hz0, inv_zero, zero_mul] at hone
    exact zero_ne_one hone

end Commons.NumberTheory.Zeta