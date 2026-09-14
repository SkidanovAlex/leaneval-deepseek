import Submission.NBody.MarchalMultiEnergy
import Submission.NBody.MarchalMultiEnergyBound
import Submission.NBody.MarchalMultiJolt

/-!
# `K ≤ c · Ï`: the interface `hKin` of the sum-level Sundman analysis

Ferrario--Terracini (`eq:nice`) need the total kinetic energy to be controlled by the *second
derivative* of the total moment of inertia of the colliding clusters.  Their proof goes through the
asymptotics; here it is obtained directly from the conservation of energy, which is much cheaper:

* `kinetic = energy + U` and `U = multiPotential + multiRestPotential` (definitional);
* the interaction plus outside potential `multiRestPotential` is bounded (separation), and the
  energy is conserved, so `kinetic ≤ |E₀| + multiPotential + C`;
* the Lagrange--Jacobi identity `Ï = 4E^{rel} + 2·multiPotential + 2·multiCrossWork` with the energy
  and work bounds gives `2·multiPotential - 6C ≤ Ï`;
* `multiPotential → ∞` (Sperner), so for small `t` the bound `kinetic ≤ 2·Ï` holds.

Hence `hKin` can be discharged with the constant `cU = 2`.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- **The kinetic energy is bounded by twice the second derivative of the total inertia**, near a
simultaneous collision.  This discharges the `hKin` hypothesis of
`multiInertia_second_deriv_asymptotic` / `multiInertia_kinetic_bound` with `cU = 2`. -/
theorem eventually_kinetic_le_multiSecondDeriv {m : Fin N → ℝ}
    {ks : Finset (Finset (Fin N))} {x : ℝ → EN E N} {ε C : ℝ} (hε : 0 < ε)
    (hC : 0 < C)
    (hH : ∀ t ∈ Ioo (0:ℝ) ε, energy m x t = energy m x (ε / 2))
    (hRest : ∀ t ∈ Ioo (0:ℝ) ε, multiRestPotential m ks (x t) ≤ C)
    (hE : ∀ t ∈ Ioo (0:ℝ) ε, |multiRelEnergy m ks (x t) (deriv x t)| ≤ C)
    (hW : ∀ t ∈ Ioo (0:ℝ) ε, |multiCrossWork m ks (x t)| ≤ C)
    (hLJ : ∀ t ∈ Ioo (0:ℝ) ε,
      deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t
        = 4 * multiRelEnergy m ks (x t) (deriv x t) + 2 * multiPotential m ks (x t)
          + 2 * multiCrossWork m ks (x t))
    (hU : Tendsto (fun t : ℝ => multiPotential m ks (x t)) (𝓝[>] (0:ℝ)) atTop) :
    ∀ᶠ t in 𝓝[>] (0:ℝ),
      kinetic m (deriv x t) ≤ 2 * deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t := by
  classical
  have hE0 : 0 ≤ |energy m x (ε / 2)| := abs_nonneg _
  -- for large enough potential the inequality holds pointwise
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ),
      |energy m x (ε / 2)| + 14 * C ≤ multiPotential m ks (x t) :=
    hU.eventually (eventually_ge_atTop _)
  filter_upwards [hev, Ioo_mem_nhdsGT hε] with t hUt ht
  have hUge : 14 * C ≤ multiPotential m ks (x t) := by linarith only [hE0, hUt]
  have hUpos : 0 < multiPotential m ks (x t) := by linarith only [hC, hUge]
  -- first bound: `kinetic ≤ 2 * multiPotential - C`
  have hk1 : kinetic m (deriv x t) ≤ 2 * multiPotential m ks (x t) - C := by
    have h1 : kinetic m (deriv x t) = energy m x t + U m (x t) := by
      rw [energy, kinetic]; ring
    have h2 : U m (x t) = multiPotential m ks (x t) + multiRestPotential m ks (x t) := by
      rw [multiRestPotential]; ring
    have h3 : energy m x t ≤ |energy m x (ε / 2)| := by
      rw [hH t ht]; exact le_abs_self _
    have h4 : multiRestPotential m ks (x t) ≤ C := hRest t ht
    linarith only [h1, h2, h3, h4, hUt, hC]
  -- second bound: `2 * multiPotential - 6 * C ≤ Ï`
  have hk2 : 2 * multiPotential m ks (x t) - 6 * C
      ≤ deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t := by
    have h5 := hLJ t ht
    have h6 : -C ≤ multiRelEnergy m ks (x t) (deriv x t) := (abs_le.mp (hE t ht)).1
    have h7 : -C ≤ multiCrossWork m ks (x t) := (abs_le.mp (hW t ht)).1
    linarith only [h5, h6, h7]
  linarith only [hk1, hk2, hUt, hC, hE0]

/-- **The `hPerr` interface** of the sum-level Sundman analysis: the interaction work and the
relative energy only shift the Lagrange--Jacobi identity by the constant `6C`. -/
theorem two_multiPotential_le_multiSecondDeriv {m : Fin N → ℝ} {ks : Finset (Finset (Fin N))}
    {x : ℝ → EN E N} {C t : ℝ}
    (hE : |multiRelEnergy m ks (x t) (deriv x t)| ≤ C)
    (hW : |multiCrossWork m ks (x t)| ≤ C)
    (hLJ : deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t
      = 4 * multiRelEnergy m ks (x t) (deriv x t) + 2 * multiPotential m ks (x t)
        + 2 * multiCrossWork m ks (x t)) :
    2 * multiPotential m ks (x t) ≤ deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t
      + 6 * C := by
  have h6 : -C ≤ multiRelEnergy m ks (x t) (deriv x t) := (abs_le.mp hE).1
  have h7 : -C ≤ multiCrossWork m ks (x t) := (abs_le.mp hW).1
  linarith only [hLJ, h6, h7]

/-- **The `hP1` interface**: eventually the second derivative of the total inertia exceeds `1`
(it is bounded below by the diverging potential). -/
theorem eventually_one_le_multiSecondDeriv {m : Fin N → ℝ} {ks : Finset (Finset (Fin N))}
    {x : ℝ → EN E N} {ε C : ℝ} (hε : 0 < ε) (hC : 0 < C)
    (hE : ∀ t ∈ Ioo (0:ℝ) ε, |multiRelEnergy m ks (x t) (deriv x t)| ≤ C)
    (hW : ∀ t ∈ Ioo (0:ℝ) ε, |multiCrossWork m ks (x t)| ≤ C)
    (hLJ : ∀ t ∈ Ioo (0:ℝ) ε,
      deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t
        = 4 * multiRelEnergy m ks (x t) (deriv x t) + 2 * multiPotential m ks (x t)
          + 2 * multiCrossWork m ks (x t))
    (hU : Tendsto (fun t : ℝ => multiPotential m ks (x t)) (𝓝[>] (0:ℝ)) atTop) :
    ∀ᶠ t in 𝓝[>] (0:ℝ), 1 ≤ deriv (deriv (fun s : ℝ => multiInertia m ks (x s))) t := by
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), (6 * C + 1) / 2 ≤ multiPotential m ks (x t) :=
    hU.eventually (eventually_ge_atTop _)
  filter_upwards [hev, Ioo_mem_nhdsGT hε] with t hUt ht
  have h1 := two_multiPotential_le_multiSecondDeriv (m := m) (ks := ks) (x := x) (t := t)
    (C := C) (hE t ht) (hW t ht) (hLJ t ht)
  linarith only [h1, hUt]

/-- **The interaction work of a cluster is bounded near a collision**, in the
centre-of-mass-relative *position* form in which the Lagrange--Jacobi identity of
`deriv_deriv_clusterInertia_curve_eq` presents it. -/
theorem exists_crossWork_position_bound {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε ν γ : ℝ} (hm : ∀ i, 0 < m i) (hν : 0 < ν) (hγ0 : 0 ≤ γ)
    (hsep : ∀ t ∈ Ioo (0:ℝ) ε, ClusterSeparatedWeak k (x t) ν)
    (hI : ∀ t ∈ Ioo (0:ℝ) ε, clusterInertia m k (x t) ≤ γ) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Ioo (0:ℝ) ε, |crossWork m k (x t) (cmRel m k (x t))| ≤ C := by
  refine ⟨2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k) * Real.sqrt γ,
    ?_, fun t ht => ?_⟩
  · have h1 : 0 ≤ (ν⁻¹) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ ∑ j : Fin N, m j := Finset.sum_nonneg fun j _ => (hm j).le
    have h3 : 0 ≤ Real.sqrt (clusterMass m k) := Real.sqrt_nonneg _
    have h4 : 0 ≤ Real.sqrt γ := Real.sqrt_nonneg _
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h1) h2) h3) h4
  · have h1 := abs_crossWork_cmRel_le (m := m) (k := k) (x := x t) (v := x t) (ν := ν) hm hν
      (hsep t ht)
    have h2 : clusterRelKinetic m k (x t) = clusterInertia m k (x t) :=
      clusterRelKinetic_eq_clusterInertia m k (x t)
    rw [h2] at h1
    refine le_trans h1 ?_
    have h3 : Real.sqrt (clusterInertia m k (x t)) ≤ Real.sqrt γ :=
      Real.sqrt_le_sqrt (hI t ht)
    have h4 : 0 ≤ 2 * (ν⁻¹) ^ 2 * (∑ j : Fin N, m j) * Real.sqrt (clusterMass m k) := by
      have ha : 0 ≤ (ν⁻¹) ^ 2 := sq_nonneg _
      have hb : 0 ≤ ∑ j : Fin N, m j := Finset.sum_nonneg fun j _ => (hm j).le
      have hc : 0 ≤ Real.sqrt (clusterMass m k) := Real.sqrt_nonneg _
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha) hb) hc
    exact mul_le_mul_of_nonneg_left h3 h4

end Submission.NBody
