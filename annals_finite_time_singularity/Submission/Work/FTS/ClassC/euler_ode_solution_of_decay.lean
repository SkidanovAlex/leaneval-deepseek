import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Filter Set

namespace Work.FTS.ClassC

/-- First-order reduction of the Euler-type ODE
`α ^ 2 * z ^ 2 * u''(z) + α * (5 + α) * z * u'(z) = 0` on `(0, ∞)`:
the function `z ↦ z ^ ((5 + α) / α) * u'(z)` is constant. -/
private lemma euler_ode_weighted_deriv_const {α : ℝ} {u : ℝ → ℝ} (hα : 0 < α)
    (hu : ContDiffOn ℝ 2 u (Set.Ioi (0 : ℝ)))
    (hode : ∀ z ∈ Set.Ioi (0 : ℝ),
      α ^ 2 * z ^ 2 * deriv (fun z' => deriv u z') z + α * (5 + α) * z * deriv u z = 0) :
    ∃ K : ℝ, ∀ z ∈ Set.Ioi (0 : ℝ), z ^ ((5 + α) / α) * deriv u z = K := by
  -- the ODE, divided by `α * z`, reads `z * u''(z) + ((5 + α) / α) * u'(z) = 0`
  have hderiv2 : ∀ z ∈ Set.Ioi (0 : ℝ),
      z * deriv (deriv u) z + ((5 + α) / α) * deriv u z = 0 := by
    intro z hz
    have hh : α ^ 2 * z ^ 2 * deriv (deriv u) z + α * (5 + α) * z * deriv u z = 0 := hode z hz
    have hα' : α ≠ 0 := ne_of_gt hα
    have h' : α * z * (α * (z * deriv (deriv u) z) + (5 + α) * deriv u z) = 0 := by
      nlinarith [hh]
    have h'' : α * (z * deriv (deriv u) z) + (5 + α) * deriv u z = 0 := by
      rcases mul_eq_zero.mp h' with h1 | h1
      · exact absurd h1 (ne_of_gt (mul_pos hα hz))
      · exact h1
    field_simp
    linarith
  -- `u'` is differentiable on `(0, ∞)`
  have hdiff : DifferentiableOn ℝ (deriv u) (Set.Ioi 0) :=
    (hu.deriv_of_isOpen (m := 1) isOpen_Ioi (by norm_num)).differentiableOn (by norm_num)
  have hpow : DifferentiableOn ℝ (fun z : ℝ => z ^ ((5 + α) / α)) (Set.Ioi 0) :=
    fun z hz =>
      (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hz))).differentiableAt.differentiableWithinAt
  have hfdiff : DifferentiableOn ℝ ((fun z : ℝ => z ^ ((5 + α) / α)) * (deriv u))
      (Set.Ioi 0) := hpow.mul hdiff
  -- whose `z ^ ((5 + α) / α)`-weighted version has vanishing derivative
  have hzero : (Set.Ioi 0).EqOn (deriv ((fun x : ℝ => x ^ ((5 + α) / α)) * (deriv u))) 0 := by
    intro z hz
    simp only [Pi.zero_apply]
    have hA : HasDerivAt (fun x : ℝ => x ^ ((5 + α) / α))
        (((5 + α) / α) * z ^ (((5 + α) / α) - 1)) z :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hz))
    have hB : HasDerivAt (deriv u) (deriv (deriv u) z) z :=
      hdiff.hasDerivAt (isOpen_Ioi.mem_nhds hz)
    rw [(hA.mul hB).deriv]
    have h1 := hderiv2 z hz
    have hz' : z ≠ 0 := ne_of_gt hz
    have h1z : z * deriv (deriv u) z = -(((5 + α) / α) * deriv u z) := by linarith
    have h2 : deriv (deriv u) z = -(((5 + α) / α) * deriv u z) / z := by
      rw [eq_div_iff hz', mul_comm]
      linarith
    rw [h2]
    have hzpow : z ^ ((5 + α) / α - 1) = z ^ ((5 + α) / α) / z := by
      rw [Real.rpow_sub hz, Real.rpow_one]
    rw [hzpow]
    field_simp
    ring
  obtain ⟨K, hK⟩ :=
    isOpen_Ioi.exists_is_const_of_deriv_eq_zero isPreconnected_Ioi hfdiff hzero
  exact ⟨K, fun z hz => hK z hz⟩

/-- If `z ↦ z ^ ((5 + α) / α) * u'(z)` is the constant `K` on `(0, ∞)` and `u → 0` at `+∞`,
then `u` is (a constant) times `z ^ (-(5 / α))`; the decay forces the constant to vanish. -/
private lemma euler_ode_eq_rpow_of_decay {α : ℝ} {u : ℝ → ℝ} (hα : 0 < α)
    (hu : ContDiffOn ℝ 2 u (Set.Ioi (0 : ℝ)))
    (K : ℝ) (hK : ∀ z ∈ Set.Ioi (0 : ℝ), z ^ ((5 + α) / α) * deriv u z = K)
    (hdec : Filter.Tendsto u Filter.atTop (nhds 0)) :
    ∃ B : ℝ, ∀ z ∈ Set.Ioi (0 : ℝ), u z = B * z ^ (-(5 / α)) := by
  have h₁c : 1 - (5 + α) / α = -(5 / α) := by field_simp; ring
  have h1cne : 1 - (5 + α) / α ≠ 0 := by
    rw [h₁c]
    exact neg_ne_zero.mpr (div_ne_zero (by norm_num) (ne_of_gt hα))
  set B : ℝ := K / (1 - (5 + α) / α) with hBdef
  have hBmul : B * (1 - (5 + α) / α) = K := by
    rw [hBdef]; field_simp
  have hdiffu : DifferentiableOn ℝ u (Set.Ioi 0) := hu.differentiableOn (by norm_num)
  -- the candidate solution `g z = u 1 + B * (z ^ (1 - (5 + α) / α) - 1)`
  have hgd : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z : ℝ => u 1 + B * (z ^ (1 - (5 + α) / α) - 1))
        (B * ((1 - (5 + α) / α) * z ^ (1 - (5 + α) / α - 1))) z := by
    intro z hz
    exact (((Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hz))).sub_const 1).const_mul B).const_add
      (u 1)
  have hdiffg : DifferentiableOn ℝ (fun z : ℝ => u 1 + B * (z ^ (1 - (5 + α) / α) - 1))
      (Set.Ioi 0) := fun z hz => (hgd z hz).differentiableAt.differentiableWithinAt
  have hderiv_eq : (Set.Ioi 0).EqOn (deriv u)
      (deriv (fun z : ℝ => u 1 + B * (z ^ (1 - (5 + α) / α) - 1))) := by
    intro z hz
    have hz' : z ≠ 0 := ne_of_gt hz
    rw [(hgd z hz).deriv]
    have hdu : deriv u z = K * z ^ (-((5 + α) / α)) := by
      have h := hK z hz
      have hzpowne : z ^ ((5 + α) / α) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hz _)
      have h2 : deriv u z = K / z ^ ((5 + α) / α) := by
        rw [eq_div_iff hzpowne, mul_comm]
        exact h
      rw [h2, div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hz)]
    rw [hdu, show (1 - (5 + α) / α - 1 : ℝ) = -((5 + α) / α) by ring]
    rw [← hBmul]
    ring
  have heq : (Set.Ioi 0).EqOn u (fun z : ℝ => u 1 + B * (z ^ (1 - (5 + α) / α) - 1)) :=
    isOpen_Ioi.eqOn_of_deriv_eq isPreconnected_Ioi hdiffu hdiffg hderiv_eq (x := 1)
      (by norm_num) (by rw [Real.one_rpow]; ring)
  have huv : ∀ z ∈ Set.Ioi (0 : ℝ), u z = u 1 + B * (z ^ (1 - (5 + α) / α) - 1) :=
    fun z hz => heq hz
  have hrpow : Tendsto (fun z : ℝ => z ^ (1 - (5 + α) / α)) atTop (nhds 0) := by
    have := tendsto_rpow_neg_atTop (y := 5 / α) (by positivity)
    simpa [h₁c] using this
  have hlim2 : Tendsto (fun z : ℝ => (u 1 - B) + B * z ^ (1 - (5 + α) / α)) atTop
      (nhds ((u 1 - B) + B * 0)) := tendsto_const_nhds.add (hrpow.const_mul B)
  have hevent : u =ᶠ[atTop] (fun z : ℝ => (u 1 - B) + B * z ^ (1 - (5 + α) / α)) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
    rw [huv z (lt_of_lt_of_le zero_lt_one hz)]
    ring
  have hlim_A : Tendsto (fun z : ℝ => (u 1 - B) + B * z ^ (1 - (5 + α) / α)) atTop (nhds 0) :=
    hdec.congr' hevent
  have hA0' : (u 1 - B) + B * 0 = 0 := tendsto_nhds_unique hlim2 hlim_A
  have hA0 : u 1 - B = 0 := by simpa using hA0'
  refine ⟨B, fun z hz => ?_⟩
  rw [huv z hz, show z ^ (1 - (5 + α) / α) = z ^ (-(5 / α)) by rw [h₁c]]
  have hu1 : u 1 = B := by linarith
  rw [hu1]; ring

theorem euler_ode_solution_of_decay {α : ℝ} {u : ℝ → ℝ} (hα : 0 < α)
    (hu : ContDiffOn ℝ 2 u (Set.Ioi (0 : ℝ)))
    (hode : ∀ z ∈ Set.Ioi (0 : ℝ),
      α ^ 2 * z ^ 2 * deriv (fun z' => deriv u z') z + α * (5 + α) * z * deriv u z = 0)
    (hdec : Filter.Tendsto u Filter.atTop (nhds 0)) :
    ∃ B : ℝ, ∀ z ∈ Set.Ioi (0 : ℝ), u z = B * z ^ (-(5 / α)) := by
  obtain ⟨K, hK⟩ := euler_ode_weighted_deriv_const hα hu hode
  exact euler_ode_eq_rpow_of_decay hα hu K hK hdec

end Work.FTS.ClassC
