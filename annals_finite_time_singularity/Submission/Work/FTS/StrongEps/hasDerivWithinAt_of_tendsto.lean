import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Filter Set MeasureTheory
open scoped Topology

set_option linter.style.haveILetI false

namespace Work.FTS.StrongEps

/-!
# Derivative of a pointwise limit of `C¹` functions with uniformly bounded derivatives

If a sequence `g k` of functions on the interval `Icc 0 T` has derivatives `dk k` (within
`Icc 0 T`) which are continuous and uniformly bounded, and if `g k → G` and `dk k → D`
pointwise, then `G` has derivative `D` on `Icc 0 T`.

The proof goes through the integral representation: for each `k` the fundamental theorem of
calculus gives `∫ x in a..b, dk k x = g k b - g k a` on `Icc 0 T`; dominated convergence
(with the uniform bound `M` and the finite measure of `Icc 0 T`) lets `k → ∞`, producing
`G b - G a = ∫ x in a..b, D x`; the fundamental theorem of calculus for the continuous
integrand `D` then gives the one-sided derivative.
-/

/-- Fundamental theorem of calculus for each of the approximating functions. -/
private theorem ftc_each {T : ℝ} {g : ℕ → ℝ → ℝ} {dk : ℕ → ℝ → ℝ}
    (hderiv : ∀ k : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 T →
      HasDerivWithinAt (g k) (dk k τ) (Set.Icc 0 T) τ)
    (hcont : ∀ k : ℕ, ContinuousOn (dk k) (Set.Icc 0 T))
    (k : ℕ) {x y : ℝ} (hx : x ∈ Set.Icc 0 T) (hy : y ∈ Set.Icc 0 T) (hxy : x ≤ y) :
    ∫ s in x..y, dk k s = g k y - g k x := by
  have hsub : Set.Icc x y ⊆ Set.Icc 0 T := fun z hz =>
    ⟨le_trans hx.1 hz.1, le_trans hz.2 hy.2⟩
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hxy ?_ ?_ ?_
  · exact (HasDerivWithinAt.continuousOn (hderiv k)).mono hsub
  · intro z hz
    have hzT : z ∈ Set.Icc 0 T := ⟨le_trans hx.1 hz.1.le, le_trans hz.2.le hy.2⟩
    exact (hderiv k z hzT).hasDerivAt
      (Icc_mem_nhds (by linarith [hx.1, hz.1]) (by linarith [hy.2, hz.2]))
  · exact ((hcont k).mono (by rw [Set.uIcc_of_le hxy]; exact hsub)).intervalIntegrable

/-- Dominated convergence for the interval integrals of the derivatives. -/
private theorem tendsto_intervalIntegral {T : ℝ} {dk : ℕ → ℝ → ℝ} {D : ℝ → ℝ}
    (hcont : ∀ k : ℕ, ContinuousOn (dk k) (Set.Icc 0 T))
    (hbdd : ∃ M : ℝ, ∀ k : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 T → |dk k τ| ≤ M)
    (hd : ∀ τ : ℝ, τ ∈ Set.Icc 0 T →
      Filter.Tendsto (fun k : ℕ => dk k τ) Filter.atTop (nhds (D τ)))
    {x y : ℝ} (hx : x ∈ Set.Icc 0 T) (hy : y ∈ Set.Icc 0 T) (hxy : x ≤ y) :
    Filter.Tendsto (fun k : ℕ => ∫ s in x..y, dk k s) Filter.atTop
      (nhds (∫ s in x..y, D s)) := by
  obtain ⟨M, hM⟩ := hbdd
  have hsub : Set.Ioc x y ⊆ Set.Icc 0 T := fun z hz =>
    ⟨le_trans hx.1 hz.1.le, le_trans hz.2 hy.2⟩
  have hbound_int : Integrable (fun _ : ℝ => M) (volume.restrict (Set.Ioc x y)) := by
    rw [MeasureTheory.integrable_const_iff]
    right
    refine ⟨?_⟩
    rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hmain := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Set.Ioc x y)) (F := dk) (f := D) (fun _ : ℝ => M)
    (fun k => ((hcont k).mono hsub).aestronglyMeasurable measurableSet_Ioc)
    hbound_int
    (fun k => by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with a ha
      rw [Real.norm_eq_abs]
      exact hM k a (hsub ha))
    (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with a ha
      exact hd a (hsub ha))
  simpa only [intervalIntegral.integral_of_le hxy] using hmain

/-- The limit function `G` satisfies the integral identity `G b - G a = ∫ x in a..b, D x`. -/
private theorem G_sub_eq_integral {T : ℝ} {g : ℕ → ℝ → ℝ} {G D : ℝ → ℝ}
    {dk : ℕ → ℝ → ℝ}
    (hderiv : ∀ k : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 T →
      HasDerivWithinAt (g k) (dk k τ) (Set.Icc 0 T) τ)
    (hcont : ∀ k : ℕ, ContinuousOn (dk k) (Set.Icc 0 T))
    (hbdd : ∃ M : ℝ, ∀ k : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 T → |dk k τ| ≤ M)
    (hg : ∀ τ : ℝ, τ ∈ Set.Icc 0 T →
      Filter.Tendsto (fun k : ℕ => g k τ) Filter.atTop (nhds (G τ)))
    (hd : ∀ τ : ℝ, τ ∈ Set.Icc 0 T →
      Filter.Tendsto (fun k : ℕ => dk k τ) Filter.atTop (nhds (D τ)))
    {x y : ℝ} (hx : x ∈ Set.Icc 0 T) (hy : y ∈ Set.Icc 0 T) (hxy : x ≤ y) :
    G y - G x = ∫ s in x..y, D s := by
  have h1 : Filter.Tendsto (fun k : ℕ => g k y - g k x) Filter.atTop (nhds (G y - G x)) :=
    (hg y hy).sub (hg x hx)
  have h2 : Filter.Tendsto (fun k : ℕ => g k y - g k x) Filter.atTop
      (nhds (∫ s in x..y, D s)) := by
    have h3 := tendsto_intervalIntegral hcont hbdd hd hx hy hxy
    rw [show (fun k : ℕ => g k y - g k x) = fun k : ℕ => ∫ s in x..y, dk k s from
      funext fun k => (ftc_each hderiv hcont k hx hy hxy).symm]
    exact h3
  exact tendsto_nhds_unique h1 h2

/-- The fundamental theorem of calculus for the continuous limit derivative `D`: the map
`u ↦ ∫ s in 0..u, D s` has derivative `D τ` within `Icc 0 T` at `τ`. -/
private theorem hasDerivWithinAt_integral {T : ℝ} {D : ℝ → ℝ}
    (hDc : ContinuousOn D (Set.Icc 0 T)) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 T) :
    HasDerivWithinAt (fun u => ∫ s in (0 : ℝ)..u, D s) (D τ) (Set.Icc 0 T) τ := by
  haveI : Fact (τ ∈ Set.Icc 0 T) := ⟨hτ⟩
  have hsub : Set.uIcc 0 τ ⊆ Set.Icc 0 T := by
    rw [Set.uIcc_of_le hτ.1]
    exact fun z hz => ⟨hz.1, le_trans hz.2 hτ.2⟩
  refine intervalIntegral.integral_hasDerivWithinAt_right (f := D)
    (s := Set.Icc 0 T) (t := Set.Icc 0 T)
    ((hDc.mono hsub).intervalIntegrable) ?_ (hDc.continuousWithinAt hτ)
  exact ⟨Set.Icc 0 T, self_mem_nhdsWithin, hDc.aestronglyMeasurable measurableSet_Icc⟩

theorem hasDerivWithinAt_of_tendsto {T : ℝ} (hT : 0 ≤ T) {g : ℕ → ℝ → ℝ} {G D : ℝ → ℝ}
    {dk : ℕ → ℝ → ℝ}
    (hderiv : ∀ k : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 T →
      HasDerivWithinAt (g k) (dk k τ) (Set.Icc 0 T) τ)
    (hcont : ∀ k : ℕ, ContinuousOn (dk k) (Set.Icc 0 T))
    (hbdd : ∃ M : ℝ, ∀ k : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 T → |dk k τ| ≤ M)
    (hDc : ContinuousOn D (Set.Icc 0 T))
    (hg : ∀ τ : ℝ, τ ∈ Set.Icc 0 T → Filter.Tendsto (fun k : ℕ => g k τ) Filter.atTop (nhds (G τ)))
    (hd : ∀ τ : ℝ, τ ∈ Set.Icc 0 T → Filter.Tendsto (fun k : ℕ => dk k τ) Filter.atTop (nhds (D τ))) :
    ∀ τ : ℝ, τ ∈ Set.Icc 0 T → HasDerivWithinAt G (D τ) (Set.Icc 0 T) τ := by
  intro τ hτ
  have h0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT⟩
  have hG : ∀ y ∈ Set.Icc 0 T, G y = G 0 + ∫ s in (0 : ℝ)..y, D s := by
    intro y hy
    have h := G_sub_eq_integral hderiv hcont hbdd hg hd h0 hy hy.1
    linarith
  have hF := (hasDerivWithinAt_integral hDc hτ).const_add (G 0)
  exact hF.congr (fun y hy => hG y hy) (hG τ hτ)

end Work.FTS.StrongEps
