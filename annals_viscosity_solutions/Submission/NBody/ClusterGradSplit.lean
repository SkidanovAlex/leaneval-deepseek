import Submission.NBody.ClusterCentralConfig
import Submission.NBody.MarchalClusterBound

/-!
# The force on a body of a cluster: internal and exterior parts

For a body `i` of the cluster `k`, the mass-weighted force `∇ₘU(x)ᵢ` splits into the force of the
*other bodies of the cluster* — which is exactly the mass-gradient `clusterGrad m k xᵢ` of the
cluster potential — and an *exterior* part, the sum of the pulls of the bodies outside `k`.

The exterior part is bounded by `(∑_{j∉k} mⱼ)/ν²` as soon as the cluster is `ν`-separated from the
other bodies (`ClusterSeparatedWeak k x ν`): each exterior pair contributes a vector of norm
`mⱼ/‖xⱼ-xᵢ‖² ≤ mⱼ/ν²`.

Together with `clusterGrad_cmRel` and `clusterGrad_smul` this gives the structural identity

    `cmRel m k (∇ₘU(x))ᵢ = φ⁻² (∇ₘU_k(s))ᵢ + (bounded)`   (`q = cmRel m k x`, `s = q/φ`)

which is the algebraic content of Ferrario--Terracini's `propo:cent_conf`.

Everything in this file is fully proved.
-/

open ViscositySolutions
open Filter Gradient Real Set
open scoped BigOperators Topology
open InnerProductSpace

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- The exterior part of the force on the body `i` of the cluster `k`. -/
noncomputable def clusterExtForce (m : Fin N → ℝ) (k : Finset (Fin N)) (x : EN E N) (i : Fin N) : E :=
  ∑ j ∈ Finset.univ.filter (fun j => j ∉ k), (m j * (‖x j - x i‖ ^ 3)⁻¹) • (x j - x i)

/-- The cluster-internal part of the force on `i ∈ k` is the mass-gradient of the cluster
potential, and the remainder is the exterior force. -/
lemma weightedGrad_U_eq_clusterGrad_add_ext {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N}
    (hm : ∀ i, m i ≠ 0) (hnc : WithoutCollisions x) {i : Fin N} (hi : i ∈ k) :
    (weightedGrad m (U m) x) i = (clusterGrad m k x) i + clusterExtForce m k x i := by
  have hkk : ∀ a ∈ k, ∀ b ∈ k, a ≠ b → x a ≠ x b := by
    intro a _ b _ hab hcon
    exact hnc a b hab (by rw [r_eq_norm_sub, hcon, sub_self, norm_zero])
  rw [weightedGrad_U_coord m hm x hnc i, clusterGrad_apply_of_mem hm hkk hi, clusterExtForce]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.erase i) (fun j => j ∈ k)
    (fun j => (m j * (‖x j - x i‖ ^ 3)⁻¹) • (x j - x i))]
  have hset1 : (Finset.univ.erase i).filter (fun j => j ∈ k) = k.erase i := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
  have hset2 : (Finset.univ.erase i).filter (fun j => j ∉ k)
      = Finset.univ.filter (fun j => j ∉ k) := by
    ext j
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_erase]
    by_cases hji : j = i
    · rw [hji]
      simp [hi]
    · simp [hji]
  rw [hset1, hset2]

/-- Each exterior pair contributes a vector of norm `mⱼ/‖xⱼ-xᵢ‖²`. -/
lemma norm_smul_inv_cube_le {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N} {ν : ℝ}
    (hm : ∀ i, 0 ≤ m i) (hν : 0 < ν) (hsep : ClusterSeparatedWeak k x ν) {i j : Fin N}
    (hi : i ∈ k) (hj : j ∉ k) :
    ‖(m j * (‖x j - x i‖ ^ 3)⁻¹) • (x j - x i)‖ ≤ m j / ν ^ 2 := by
  have hij : i ≠ j := fun h => hj (h ▸ hi)
  have hr : ν ≤ ‖x j - x i‖ := by
    have h := hsep i hi j hj
    rw [r_eq_norm_sub, norm_sub_rev] at h
    exact h
  have ha : 0 < ‖x j - x i‖ := lt_of_lt_of_le hν hr
  have hane : (‖x j - x i‖ : ℝ) ≠ 0 := ne_of_gt ha
  have h1 : ‖(m j * (‖x j - x i‖ ^ 3)⁻¹) • (x j - x i)‖
      = m j * ((‖x j - x i‖ ^ 3)⁻¹ * ‖x j - x i‖) := by
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hm j) (inv_nonneg.mpr (by positivity))), mul_assoc]
  have h2 : (‖x j - x i‖ ^ 3)⁻¹ * ‖x j - x i‖ = (‖x j - x i‖ ^ 2)⁻¹ := by
    rw [mul_comm]
    field_simp
  rw [h1, h2, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (by nlinarith)) (hm j)

/-- The exterior force is bounded by `(∑_{j∉k} mⱼ)/ν²`. -/
lemma norm_clusterExtForce_le {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N} {ν : ℝ}
    (hm : ∀ i, 0 ≤ m i) (hν : 0 < ν) (hsep : ClusterSeparatedWeak k x ν) {i : Fin N} (hi : i ∈ k) :
    ‖clusterExtForce m k x i‖ ≤ (∑ j ∈ Finset.univ.filter (fun j => j ∉ k), m j) / ν ^ 2 := by
  rw [clusterExtForce]
  calc ‖∑ j ∈ Finset.univ.filter (fun j => j ∉ k), (m j * (‖x j - x i‖ ^ 3)⁻¹) • (x j - x i)‖
      ≤ ∑ j ∈ Finset.univ.filter (fun j => j ∉ k),
          ‖(m j * (‖x j - x i‖ ^ 3)⁻¹) • (x j - x i)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j => j ∉ k), m j / ν ^ 2 :=
        Finset.sum_le_sum fun j hj =>
          norm_smul_inv_cube_le hm hν hsep hi (Finset.mem_filter.mp hj).2
    _ = (∑ j ∈ Finset.univ.filter (fun j => j ∉ k), m j) / ν ^ 2 := (Finset.sum_div _ _ _).symm

end Submission.NBody
