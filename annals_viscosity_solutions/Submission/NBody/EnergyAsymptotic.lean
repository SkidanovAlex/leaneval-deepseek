import ChallengeDeps
import Submission.NBody.Flow
import Submission.Commons.Analysis.Asymptotics.tendsto_sum_norm_sq_div_sq
import Submission.Commons.Analysis.Asymptotics.tendsto_div_sq_of_iteratedDeriv_two
import Mathlib

/-!
# The energy of a hyperbolic motion with prescribed asymptotics is `h`

Capstone of the classical loop.  If `y` is a collision-free motion escaping along the limit
shape `a` (`‖a‖ₘ = 1`) with speed `√(2h)`,

    `y(t) = (√(2h)·t) • a + o(t)`   as `t → +∞`,

then the conserved energy equals the prescribed level:  `energy m y t = h` for every `t > 0`.

Route: `I(t) = ∑ᵢ mᵢ‖yᵢ(t)‖²` satisfies (i) `I(t)/t² → c²` with `c = √(2h)` (from the
asymptotics), (ii) `I''(t) = 4E + 2U(y(t)) → 4E` (Lagrange–Jacobi + `U → 0`), and
(iii) `f'' → M ⟹ f/t² → M/2`; comparing the two limits gives `c² = 2E`, i.e. `E = h`.

Everything here is fully proved.
-/

open ViscositySolutions
open Filter Gradient Real Set
open scoped BigOperators
open scoped Topology
open InnerProductSpace

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- The inertia of a `C²` motion is `C²`. -/
lemma contDiffOn_inertia (m : Fin N → ℝ) {y : ℝ → EN E N} (hy : ContDiffOn ℝ 2 y (Ioi 0)) :
    ContDiffOn ℝ 2 (inertia m y) (Ioi 0) := by
  have hsum : ContDiffOn ℝ 2 (fun t : ℝ => ∑ i : Fin N, m i * ‖y t i‖ ^ 2) (Ioi 0) := by
    refine ContDiffOn.sum (s := Finset.univ) ?_
    intro i _
    have hcomp : ContDiffOn ℝ 2 (fun t : ℝ => y t i) (Ioi 0) := by
      have h : (fun t : ℝ => y t i)
          = (fun t : ℝ => (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin N => E) i) (y t)) := by
        funext t
        rw [PiLp.proj_apply]
      rw [h]
      exact ((PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin N => E) i).contDiff).comp_contDiffOn hy
    simpa using ContDiffOn.const_smul (𝕜 := ℝ) (m i) (ContDiffOn.norm_sq ℝ hcomp)
  have hfeq : (fun t : ℝ => ∑ i : Fin N, m i * ‖y t i‖ ^ 2) = inertia m y := rfl
  rw [← hfeq]
  exact hsum

/-- **The energy of a hyperbolic motion is the prescribed `h`.** -/
theorem energy_eq_of_hyperbolic (m : Fin N → ℝ) (hm : ∀ i, m i ≠ 0) {a : EN E N}
    (a_nc : WithoutCollisions a) (a_norm : ‖a‖_[m] = 1) {h : ℝ} (h_pos : 0 < h)
    {y : ℝ → EN E N} {o : ℝ → EN E N} (hy : IsNBodySolution m y)
    (hnc : ∀ t > 0, WithoutCollisions (y t))
    (ho : o =o[atTop] fun t : ℝ => t)
    (hasym : ∀ᶠ t in atTop, y t = (sqrt (2 * h) * t) • a + o t) :
    ∀ t > 0, energy m y t = h := by
  have hcpos : 0 < sqrt (2 * h) := Real.sqrt_pos.mpr (by positivity)
  have hcne : sqrt (2 * h) ≠ 0 := ne_of_gt hcpos
  -- the normalisation `‖a‖ₘ = 1` gives `∑ᵢ mᵢ‖aᵢ‖² = 1`
  have ha : (∑ i, m i * ‖a i‖ ^ 2) = 1 := by
    have h1 : sqrt (∑ i, m i * ‖a i‖ ^ 2) = 1 := by
      simpa [weightedNorm] using a_norm
    exact Real.sqrt_eq_one.mp h1
  -- (i) `I(t)/t² → c²`
  have hnorm : (∑ i, m i * ‖(sqrt (2 * h) • a) i‖ ^ 2) = 2 * h := by
    have hone : ∀ i : Fin N, ‖(sqrt (2 * h) • a) i‖ ^ 2 = (2 * h) * ‖a i‖ ^ 2 := by
      intro i
      have h1 : (sqrt (2 * h) • a) i = sqrt (2 * h) • a i := by simp
      rw [h1, norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hcpos), mul_pow,
        Real.sq_sqrt (le_of_lt (by positivity : (0 : ℝ) < 2 * h))]
    calc (∑ i, m i * ‖(sqrt (2 * h) • a) i‖ ^ 2)
        = ∑ i, m i * ((2 * h) * ‖a i‖ ^ 2) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hone i]
      _ = (2 * h) * ∑ i, m i * ‖a i‖ ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
      _ = 2 * h := by rw [ha, mul_one]
  have hI : Tendsto (fun t : ℝ => inertia m y t / t ^ 2) atTop (𝓝 (2 * h)) := by
    have hbase := Commons.Analysis.Asymptotics.tendsto_sum_norm_sq_div_sq (E := E) m hcne a ho hasym
    rw [hnorm] at hbase
    simpa [inertia] using hbase
  -- (ii) `I'' → 4E`
  have hU : Tendsto (fun t : ℝ => U m (y t)) atTop (𝓝 0) :=
    tendsto_U_atTop_zero m a a_nc hcpos ho hasym
  have hI2 : Tendsto (fun t : ℝ => iteratedDeriv 2 (inertia m y) t) atTop
      (𝓝 (4 * energy m y 1)) := by
    have heq : (fun t : ℝ => iteratedDeriv 2 (inertia m y) t) =ᶠ[atTop]
        (fun t : ℝ => 4 * energy m y 1 + 2 * U m (y t)) := by
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
      rw [iteratedDeriv_two_inertia m hm hy hnc ht,
        energy_eq_of_pos m hm hy hnc ht (by norm_num : (0 : ℝ) < 1)]
    refine Tendsto.congr' heq.symm ?_
    have h2 : Tendsto (fun t : ℝ => 4 * energy m y 1 + 2 * U m (y t)) atTop
        (𝓝 (4 * energy m y 1)) := by
      have h3 := Filter.Tendsto.const_add (4 * energy m y 1) (Filter.Tendsto.const_mul 2 hU)
      simpa using h3
    exact h2
  -- (iii) `I(t)/t² → (4E)/2 = 2E`
  have hI3 : Tendsto (fun t : ℝ => inertia m y t / t ^ 2) atTop (𝓝 (2 * energy m y 1)) := by
    have hcont : ContDiffOn ℝ 2 (inertia m y) (Ici (1 / 2 : ℝ)) :=
      (contDiffOn_inertia m hy.contDiff).mono (fun x hx => by
        simp only [Set.mem_Ici] at hx
        exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hx)
    have hbase := Commons.Analysis.Asymptotics.tendsto_div_sq_of_iteratedDeriv_two hcont hI2
    rwa [show 4 * energy m y 1 / 2 = 2 * energy m y 1 by ring] at hbase
  -- compare the two limits
  have hlim : 2 * h = 2 * energy m y 1 := tendsto_nhds_unique hI hI3
  intro t ht
  rw [energy_eq_of_pos m hm hy hnc ht (by norm_num : (0 : ℝ) < 1)]
  linarith

/-- **The energy of an escaping motion.**  If a collision-free `N`-body solution satisfies
`y t = (c * t) • a + o t` as `t → +∞`, with `c > 0` and `a` collision-free, then its (constant)
energy equals the asymptotic kinetic energy `½ c² ‖a‖ₘ²`. -/
theorem energy_eq_of_asymptotic (m : Fin N → ℝ) (hm : ∀ i, m i ≠ 0) {a : EN E N}
    (a_nc : WithoutCollisions a) {c : ℝ} (hc : 0 < c) {y : ℝ → EN E N} {o : ℝ → EN E N}
    (hy : IsNBodySolution m y) (hnc : ∀ t > 0, WithoutCollisions (y t))
    (ho : o =o[atTop] fun t : ℝ => t)
    (hasym : ∀ᶠ t in atTop, y t = (c * t) • a + o t) :
    ∀ t > 0, energy m y t = (1 / 2) * c ^ 2 * (∑ i, m i * ‖a i‖ ^ 2) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have hnorm : (∑ i, m i * ‖(c • a) i‖ ^ 2) = c ^ 2 * (∑ i, m i * ‖a i‖ ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have h1 : (c • a) i = c • a i := by simp
    rw [h1, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc.le, mul_pow]
    ring
  have hI : Tendsto (fun t : ℝ => inertia m y t / t ^ 2) atTop
      (𝓝 (c ^ 2 * (∑ i, m i * ‖a i‖ ^ 2))) := by
    have hbase := Commons.Analysis.Asymptotics.tendsto_sum_norm_sq_div_sq (E := E) m hcne a ho hasym
    rw [hnorm] at hbase
    simpa [inertia] using hbase
  have hU : Tendsto (fun t : ℝ => U m (y t)) atTop (𝓝 0) :=
    tendsto_U_atTop_zero m a a_nc hc ho hasym
  have hI2 : Tendsto (fun t : ℝ => iteratedDeriv 2 (inertia m y) t) atTop
      (𝓝 (4 * energy m y 1)) := by
    have heq : (fun t : ℝ => iteratedDeriv 2 (inertia m y) t) =ᶠ[atTop]
        (fun t : ℝ => 4 * energy m y 1 + 2 * U m (y t)) := by
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
      rw [iteratedDeriv_two_inertia m hm hy hnc ht,
        energy_eq_of_pos m hm hy hnc ht (by norm_num : (0 : ℝ) < 1)]
    refine Tendsto.congr' heq.symm ?_
    have h2 : Tendsto (fun t : ℝ => 4 * energy m y 1 + 2 * U m (y t)) atTop
        (𝓝 (4 * energy m y 1)) := by
      have h3 := Filter.Tendsto.const_add (4 * energy m y 1) (Filter.Tendsto.const_mul 2 hU)
      simpa using h3
    exact h2
  have hI3 : Tendsto (fun t : ℝ => inertia m y t / t ^ 2) atTop (𝓝 (2 * energy m y 1)) := by
    have hcont : ContDiffOn ℝ 2 (inertia m y) (Ici (1 / 2 : ℝ)) :=
      (contDiffOn_inertia m hy.contDiff).mono (fun x hx => by
        simp only [Set.mem_Ici] at hx
        exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hx)
    have hbase := Commons.Analysis.Asymptotics.tendsto_div_sq_of_iteratedDeriv_two hcont hI2
    rwa [show 4 * energy m y 1 / 2 = 2 * energy m y 1 by ring] at hbase
  have hlim : c ^ 2 * (∑ i, m i * ‖a i‖ ^ 2) = 2 * energy m y 1 := tendsto_nhds_unique hI hI3
  intro t ht
  rw [energy_eq_of_pos m hm hy hnc ht (by norm_num : (0 : ℝ) < 1)]
  linarith

end Submission.NBody
