import Submission.NBody.MarchalClusterFull
import Submission.Commons.Analysis.Calculus.hasDerivAt_inv_cube_norm_smul
import Submission.Commons.Analysis.Calculus.norm_inv_cube_norm_smul_deriv_le

/-!
# Third-derivative estimates for a colliding cluster

The refinement of Sundman's analysis (`lemma:bach` in Ferrario–Terracini) which pins down the
*second* derivative of the moment of inertia of a colliding cluster needs a bound on the third
derivative of `I_k` in terms of the second one:

    `|I_k'''| ≤ e (I_k'')^{(2b-3)/(b-2)}`  (with `b = 4`, exponent `5/2`).

Since `I_k = ∑_{i∈k} mᵢ‖qᵢ‖²`, its third derivative is `∑_{i∈k} mᵢ(4⟪q̇ᵢ,q̈ᵢ⟫ + 2⟪qᵢ,q⃛ᵢ⟫)`, so
it suffices to bound the acceleration `q̈ᵢ` and the jolt `q⃛ᵢ` of a body of the cluster in terms of
the internal potential `U_k`:

* `‖q̈ᵢ‖ ≤ A U_k²`  (the force is a sum of `mⱼ rᵢⱼ^{-2}`, and `rᵢⱼ^{-1} ≤ U_k/(mᵢmⱼ)`);
* `‖q⃛ᵢ‖ ≤ A K^{1/2} U_k³`  (the derivative of the force brings one more factor `rᵢⱼ^{-1}` and a
  velocity factor).

Together with `2U_k ≤ I_k'' + 6C` and `2K_k ≤ I_k'' + d` this yields the required bound.

Everything in this file is fully proved.
-/

open ViscositySolutions
open Filter Gradient Real Set
open scoped BigOperators Topology
open InnerProductSpace

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-! ## The pair term of the potential dominates `1/r` -/

lemma inv_norm_sub_le_clusterPotential {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N}
    (hm : ∀ i, 0 < m i) {i j : Fin N} (hi : i ∈ k) (hj : j ∈ k) (hij : i ≠ j) :
    (‖x i - x j‖)⁻¹ ≤ clusterPotential m k x / (m i * m j) := by
  have hmem : ∀ a b : Fin N, a < b → a ∈ k → b ∈ k →
      (a, b) ∈ (pairFinset N).filter (fun p : Fin N × Fin N => p.1 ∈ k ∧ p.2 ∈ k) := by
    intro a b hab ha hb
    rw [Finset.mem_filter, pairFinset, Finset.mem_filter]
    exact ⟨⟨Finset.mem_univ _, hab⟩, ha, hb⟩
  have hterm : ∀ a b : Fin N, a < b → a ∈ k → b ∈ k →
      m a * m b * (‖x a - x b‖)⁻¹
        ≤ ∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => p.1 ∈ k ∧ p.2 ∈ k),
            m p.1 * m p.2 * (r x p.1 p.2)⁻¹ := by
    intro a b hab ha hb
    have h1 := Finset.single_le_sum
      (f := fun p : Fin N × Fin N => m p.1 * m p.2 * (r x p.1 p.2)⁻¹)
      (fun p _ => mul_nonneg (mul_nonneg (hm p.1).le (hm p.2).le)
        (inv_nonneg.mpr dist_nonneg)) (hmem a b hab ha hb)
    rwa [r_eq_norm_sub] at h1
  have hpos : 0 < m i * m j := mul_pos (hm i) (hm j)
  have key : m i * m j * (‖x i - x j‖)⁻¹ ≤ clusterPotential m k x := by
    rw [clusterPotential]
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hterm i j hlt hi hj
    · have h := hterm j i hgt hj hi
      rw [norm_sub_rev] at h
      rwa [mul_comm (m j) (m i)] at h
  rw [le_div_iff₀ hpos]
  calc (‖x i - x j‖)⁻¹ * (m i * m j) = m i * m j * (‖x i - x j‖)⁻¹ := by ring
    _ ≤ clusterPotential m k x := key

/-- The sum of `mⱼ/rᵢⱼ²` over the bodies `j ∈ k`, `j ≠ i`, of the cluster is bounded by a
constant times the square of the internal potential. -/
lemma sum_inv_sq_le {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N} {κ : ℝ}
    (hm : ∀ i, 0 < m i) (hκ : ∀ i, κ ≤ m i) (hκpos : 0 < κ) {i : Fin N} (hi : i ∈ k) :
    (∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∈ k),
        m j * ((‖x j - x i‖)⁻¹) ^ 2)
      ≤ (N : ℝ) * (clusterPotential m k x ^ 2 / κ ^ 3) := by
  have hU0 : 0 ≤ clusterPotential m k x := by
    rw [clusterPotential]
    exact Finset.sum_nonneg fun p _ =>
      mul_nonneg (mul_nonneg (hm p.1).le (hm p.2).le) (inv_nonneg.mpr dist_nonneg)
  have hterm : ∀ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∈ k),
      m j * ((‖x j - x i‖)⁻¹) ^ 2 ≤ clusterPotential m k x ^ 2 / κ ^ 3 := by
    intro j hj
    obtain ⟨hji, hjk⟩ := Finset.mem_filter.mp hj
    have hjne : j ≠ i := (Finset.mem_erase.mp hji).1
    have hinv : (‖x j - x i‖)⁻¹ ≤ clusterPotential m k x / (m i * m j) := by
      have h : (‖x j - x i‖)⁻¹ ≤ clusterPotential m k x / (m j * m i) :=
        inv_norm_sub_le_clusterPotential hm hjk hi hjne
      rwa [mul_comm (m j) (m i)] at h
    have hmj : 0 < m j := hm j
    have h1 : ((‖x j - x i‖)⁻¹) ^ 2 ≤ (clusterPotential m k x / (m i * m j)) ^ 2 :=
      pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) hinv 2
    have h2 : m j * ((‖x j - x i‖)⁻¹) ^ 2 ≤ m j * (clusterPotential m k x / (m i * m j)) ^ 2 :=
      mul_le_mul_of_nonneg_left h1 hmj.le
    have h3 : m j * (clusterPotential m k x / (m i * m j)) ^ 2
        ≤ clusterPotential m k x ^ 2 / κ ^ 3 := by
      have hmi : κ ≤ m i := hκ i
      have hstep : m j * (clusterPotential m k x / (m i * m j)) ^ 2
          = clusterPotential m k x ^ 2 / (m i ^ 2 * m j) := by
        field_simp
      rw [hstep]
      have h5 : κ ^ 3 ≤ m i ^ 2 * m j := by
        have h1 : κ ^ 2 ≤ m i ^ 2 := pow_le_pow_left₀ hκpos.le hmi 2
        have h2 : κ ^ 3 = κ ^ 2 * κ := by ring
        rw [h2]
        exact mul_le_mul h1 (hκ j) hκpos.le (sq_nonneg (m i))
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) h5
    linarith [h2, h3]
  have hX0 : 0 ≤ clusterPotential m k x ^ 2 / κ ^ 3 := by positivity
  calc (∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∈ k),
        m j * ((‖x j - x i‖)⁻¹) ^ 2)
      ≤ ((Finset.univ.erase i).filter (fun j : Fin N => j ∈ k)).card
          • (clusterPotential m k x ^ 2 / κ ^ 3) := Finset.sum_le_card_nsmul _ _ _ hterm
    _ = (((Finset.univ.erase i).filter (fun j : Fin N => j ∈ k)).card : ℝ)
          * (clusterPotential m k x ^ 2 / κ ^ 3) := by rw [nsmul_eq_mul]
    _ ≤ (N : ℝ) * (clusterPotential m k x ^ 2 / κ ^ 3) := by
        refine mul_le_mul_of_nonneg_right ?_ hX0
        have h1 : ((Finset.univ.erase i).filter (fun j : Fin N => j ∈ k)).card
            ≤ (Finset.univ : Finset (Fin N)).card :=
          Finset.card_le_card ((Finset.filter_subset _ _).trans
            (Finset.erase_subset i (Finset.univ)))
        have h2 : ((Finset.univ : Finset (Fin N)).card : ℝ) = (N : ℝ) := by simp
        calc (((Finset.univ.erase i).filter (fun j : Fin N => j ∈ k)).card : ℝ)
            ≤ ((Finset.univ : Finset (Fin N)).card : ℝ) := by exact_mod_cast h1
          _ = (N : ℝ) := h2

/-- The mass-weighted gradient of the potential at a body of a cluster is bounded by the square of
the internal potential plus a constant. -/
lemma norm_weightedGrad_coord_le {m : Fin N → ℝ} {k : Finset (Fin N)} {ν : ℝ}
    (hm : ∀ i, 0 < m i) (hν : 0 < ν) (hk : k.Nonempty) :
    ∃ A : ℝ, 0 < A ∧ ∀ x : EN E N, ClusterSeparatedWeak k x ν → WithoutCollisions x →
      ∀ i ∈ k, ‖(∇_[m] (U m) x) i‖ ≤ A * (clusterPotential m k x ^ 2 + 1) := by
  obtain ⟨κ, hκpos, hκ⟩ : ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ m i := by
    obtain ⟨i₀, hi₀⟩ := hk
    obtain ⟨i₁, -, hi₁⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin N)) m
      ⟨i₀, Finset.mem_univ i₀⟩
    exact ⟨m i₁, hm i₁, fun i => hi₁ i (Finset.mem_univ i)⟩
  refine ⟨max ((N : ℝ) / κ ^ 3) ((∑ j : Fin N, m j) * (ν⁻¹) ^ 2) + 1,
    by positivity, fun x hsep hnc i hi => ?_⟩
  have hmne : ∀ i, m i ≠ 0 := fun i => ne_of_gt (hm i)
  have hU0 : 0 ≤ clusterPotential m k x := by
    rw [clusterPotential]
    exact Finset.sum_nonneg fun p _ =>
      mul_nonneg (mul_nonneg (hm p.1).le (hm p.2).le) (inv_nonneg.mpr dist_nonneg)
  rw [weightedGrad_U_coord m hmne x hnc i]
  have hterm : ∀ j ∈ Finset.univ.erase i, ‖(m j * (‖x j - x i‖ ^ 3)⁻¹) • (x j - x i)‖
      = m j * ((‖x j - x i‖)⁻¹) ^ 2 := by
    intro j _
    have h3 : (‖x j - x i‖ ^ 3)⁻¹ * ‖x j - x i‖ = ((‖x j - x i‖)⁻¹) ^ 2 := by
      rw [inv_mul_eq_div, pow_succ]
      field_simp
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hm j).le (by positivity)), mul_assoc, h3]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.sum_congr rfl hterm,
    ← Finset.sum_filter_add_sum_filter_not (Finset.univ.erase i) (fun j : Fin N => j ∈ k)
      (fun j : Fin N => m j * ((‖x j - x i‖)⁻¹) ^ 2)]
  have hint : (∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∈ k),
      m j * ((‖x j - x i‖)⁻¹) ^ 2) ≤ (N : ℝ) * (clusterPotential m k x ^ 2 / κ ^ 3) :=
    sum_inv_sq_le hm hκ hκpos hi
  have hcross : (∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k),
      m j * ((‖x j - x i‖)⁻¹) ^ 2) ≤ (∑ j : Fin N, m j) * (ν⁻¹) ^ 2 := by
    have hstep : ∀ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k),
        m j * ((‖x j - x i‖)⁻¹) ^ 2 ≤ m j * (ν⁻¹) ^ 2 := by
      intro j hj
      obtain ⟨hji, hjk⟩ := Finset.mem_filter.mp hj
      have hjne : j ≠ i := (Finset.mem_erase.mp hji).1
      have hdist : ν ≤ ‖x j - x i‖ := by
        have h := hsep i hi j hjk
        rwa [r_eq_norm_sub, norm_sub_rev] at h
      have hnorm : 0 < ‖x j - x i‖ := lt_of_lt_of_le hν hdist
      have hinv : ((‖x j - x i‖)⁻¹) ^ 2 ≤ (ν⁻¹) ^ 2 := by
        have h2 : (‖x j - x i‖)⁻¹ ≤ ν⁻¹ := (inv_le_inv₀ hnorm hν).mpr hdist
        exact pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) h2 2
      exact mul_le_mul_of_nonneg_left hinv (hm j).le
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro j hj
      rw [Finset.mem_filter] at hj
      simp [hj.1]
    · intro j _ _
      exact mul_nonneg (hm j).le (sq_nonneg _)
  set M : ℝ := max ((N : ℝ) / κ ^ 3) ((∑ j : Fin N, m j) * (ν⁻¹) ^ 2) with hM
  have hM0 : 0 ≤ M := le_trans (by positivity) (le_max_left _ _)
  have h1 : (N : ℝ) * (clusterPotential m k x ^ 2 / κ ^ 3) ≤ M * clusterPotential m k x ^ 2 := by
    have heq : (N : ℝ) * (clusterPotential m k x ^ 2 / κ ^ 3)
        = ((N : ℝ) / κ ^ 3) * clusterPotential m k x ^ 2 := by ring
    rw [heq, hM]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
  have h2 : (∑ j : Fin N, m j) * (ν⁻¹) ^ 2 ≤ M := by
    rw [hM]; exact le_max_right _ _
  refine le_trans (add_le_add hint hcross) ?_
  nlinarith [h1, h2, hM0, sq_nonneg (clusterPotential m k x)]

/-- The sum of `mⱼ/rᵢⱼ³` over the bodies `j ∈ k`, `j ≠ i`, of the cluster is bounded by a
constant times the cube of the internal potential. -/
lemma sum_inv_cube_le {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N} {κ : ℝ}
    (hm : ∀ i, 0 < m i) (hκ : ∀ i, κ ≤ m i) (hκpos : 0 < κ) {i : Fin N} (hi : i ∈ k) :
    (∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∈ k),
        m j * ((‖x j - x i‖)⁻¹) ^ 3)
      ≤ (N : ℝ) * ((clusterPotential m k x) ^ 3 / κ ^ 5) := by
  have hU0 : 0 ≤ clusterPotential m k x := by
    rw [clusterPotential]
    exact Finset.sum_nonneg fun p _ =>
      mul_nonneg (mul_nonneg (hm p.1).le (hm p.2).le) (inv_nonneg.mpr dist_nonneg)
  have hterm : ∀ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∈ k),
      m j * ((‖x j - x i‖)⁻¹) ^ 3 ≤ (clusterPotential m k x) ^ 3 / κ ^ 5 := by
    intro j hj
    obtain ⟨hji, hjk⟩ := Finset.mem_filter.mp hj
    have hjne : j ≠ i := (Finset.mem_erase.mp hji).1
    have hinv : (‖x j - x i‖)⁻¹ ≤ clusterPotential m k x / (m i * m j) := by
      have h : (‖x j - x i‖)⁻¹ ≤ clusterPotential m k x / (m j * m i) :=
        inv_norm_sub_le_clusterPotential hm hjk hi hjne
      rwa [mul_comm (m j) (m i)] at h
    have hmi : κ ≤ m i := hκ i
    have hmj : 0 < m j := hm j
    have hcube : ((‖x j - x i‖)⁻¹) ^ 3 ≤ (clusterPotential m k x / (m i * m j)) ^ 3 :=
      pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) hinv 3
    have h2 : m j * ((‖x j - x i‖)⁻¹) ^ 3
        ≤ m j * (clusterPotential m k x / (m i * m j)) ^ 3 :=
      mul_le_mul_of_nonneg_left hcube hmj.le
    have h3 : m j * (clusterPotential m k x / (m i * m j)) ^ 3
        = clusterPotential m k x ^ 3 / (m i ^ 3 * m j ^ 2) := by
      field_simp
    have h5 : κ ^ 5 ≤ m i ^ 3 * m j ^ 2 := by
      have h6 : κ ^ 3 ≤ m i ^ 3 := pow_le_pow_left₀ hκpos.le hmi 3
      have h7 : κ ^ 2 ≤ m j ^ 2 := pow_le_pow_left₀ hκpos.le (hκ j) 2
      have h8 : κ ^ 5 = κ ^ 3 * κ ^ 2 := by ring
      rw [h8]
      exact mul_le_mul h6 h7 (sq_nonneg κ) (pow_nonneg (le_trans hκpos.le hmi) 3)
    have h4 : clusterPotential m k x ^ 3 / (m i ^ 3 * m j ^ 2)
        ≤ clusterPotential m k x ^ 3 / κ ^ 5 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) h5
    linarith [h2, h3 ▸ h4]
  have hX0 : 0 ≤ (clusterPotential m k x) ^ 3 / κ ^ 5 := by positivity
  calc (∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∈ k),
        m j * ((‖x j - x i‖)⁻¹) ^ 3)
      ≤ ((Finset.univ.erase i).filter (fun j : Fin N => j ∈ k)).card
          • ((clusterPotential m k x) ^ 3 / κ ^ 5) := Finset.sum_le_card_nsmul _ _ _ hterm
    _ = (((Finset.univ.erase i).filter (fun j : Fin N => j ∈ k)).card : ℝ)
          * ((clusterPotential m k x) ^ 3 / κ ^ 5) := by rw [nsmul_eq_mul]
    _ ≤ (N : ℝ) * ((clusterPotential m k x) ^ 3 / κ ^ 5) := by
        refine mul_le_mul_of_nonneg_right ?_ hX0
        have h1 : ((Finset.univ.erase i).filter (fun j : Fin N => j ∈ k)).card
            ≤ (Finset.univ : Finset (Fin N)).card :=
          Finset.card_le_card ((Finset.filter_subset _ _).trans
            (Finset.erase_subset i (Finset.univ)))
        have h2 : ((Finset.univ : Finset (Fin N)).card : ℝ) = (N : ℝ) := by simp
        calc (((Finset.univ.erase i).filter (fun j : Fin N => j ∈ k)).card : ℝ)
            ≤ ((Finset.univ : Finset (Fin N)).card : ℝ) := by exact_mod_cast h1
          _ = (N : ℝ) := h2

/-! ## The relative acceleration of a body of the cluster -/

/-- The acceleration of a body of the cluster relative to the centre of mass of the cluster is
bounded by the square of the internal potential. -/
lemma exists_norm_accel_rel_le {m : Fin N → ℝ} {k : Finset (Fin N)} {ν : ℝ}
    (hm : ∀ i, 0 < m i) (hν : 0 < ν) (hk : k.Nonempty) :
    ∃ A : ℝ, 0 < A ∧ ∀ x : EN E N, ClusterSeparatedWeak k x ν → WithoutCollisions x →
      1 ≤ clusterPotential m k x →
      ∀ i ∈ k, ‖(∇_[m] (U m) x) i - clusterCM m k (∇_[m] (U m) x)‖
        ≤ A * clusterPotential m k x ^ 2 := by
  obtain ⟨A1, hA1pos, hA1⟩ := norm_weightedGrad_coord_le (E := E) (N := N) hm hν hk
  refine ⟨2 * (A1 + (clusterMass m k)⁻¹
      * ((∑ i ∈ k, ∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m i * m j)
          * (ν⁻¹) ^ 2)) + 1, by
    have := inv_nonneg.mpr (clusterMass_nonneg (fun i => (hm i).le) k)
    have h2 : 0 ≤ (∑ i ∈ k, ∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m i * m j) :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        mul_nonneg (hm i).le (hm j).le
    positivity, fun x hsep hnc hU i hi => ?_⟩
  set X : ℝ := (clusterMass m k)⁻¹
    * ((∑ i ∈ k, ∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m i * m j) * (ν⁻¹) ^ 2)
    with hX
  have hX0 : 0 ≤ X := by
    rw [hX]
    exact mul_nonneg (inv_nonneg.mpr (clusterMass_nonneg (fun i => (hm i).le) k))
      (mul_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        mul_nonneg (hm i).le (hm j).le) (sq_nonneg _))
  have hcm := norm_clusterCM_weightedGrad_le (E := E) (N := N) (m := m) (k := k) (x := x)
    (ν := ν) hm hν hsep hnc
  rw [← hX] at hcm
  have hcoord := hA1 x hsep hnc i hi
  have hsum : ‖(∇_[m] (U m) x) i - clusterCM m k (∇_[m] (U m) x)‖
      ≤ A1 * (clusterPotential m k x ^ 2 + 1) + X :=
    le_trans (norm_sub_le _ _) (add_le_add hcoord hcm)
  refine le_trans hsum ?_
  have hU2 : 1 ≤ clusterPotential m k x ^ 2 := by nlinarith [hU]
  have h1 : A1 * (clusterPotential m k x ^ 2 + 1) + X
      ≤ (A1 + X) * (clusterPotential m k x ^ 2 + 1) := by nlinarith [hX0, sq_nonneg (clusterPotential m k x)]
  have h2 : (A1 + X) * (clusterPotential m k x ^ 2 + 1)
      ≤ (2 * (A1 + X) + 1) * clusterPotential m k x ^ 2 := by
    nlinarith [hU2, hX0, hA1pos, sq_nonneg (clusterPotential m k x)]
  linarith [h1, h2]

/-! ## The derivative of the force along the motion -/

/-- The derivative of the mass-weighted gradient at a body of the cluster along the motion. -/
lemma hasDerivAt_weightedGrad_coord {m : Fin N → ℝ} {x : ℝ → EN E N} {ε t : ℝ}
    (hmne : ∀ i, m i ≠ 0) (ht : t ∈ Ioo (0:ℝ) ε)
    (hx : ∀ s ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x s) s)
    (hnc : ∀ s ∈ Ioo (0:ℝ) ε, WithoutCollisions (x s)) (i : Fin N) :
    HasDerivAt (fun s : ℝ => (∇_[m] (U m) (x s)) i)
      (∑ j ∈ Finset.univ.erase i,
        ((m j * (‖x t j - x t i‖ ^ 3)⁻¹) • (deriv x t j - deriv x t i)
        - (3 * (m j * ((‖x t j - x t i‖ ^ 5)⁻¹
            * inner ℝ (x t j - x t i) (deriv x t j - deriv x t i)))) • (x t j - x t i))) t := by
  have hx_t := hx t ht
  have hnc_t := hnc t ht
  have hevent : (fun s : ℝ => (∇_[m] (U m) (x s)) i) =ᶠ[𝓝 t]
      (fun s : ℝ => ∑ j ∈ Finset.univ.erase i,
        (m j * (‖x s j - x s i‖ ^ 3)⁻¹) • (x s j - x s i)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact weightedGrad_U_coord m (fun j => hmne j) (x s) (hnc s hs) i
  have hG : HasDerivAt (fun s : ℝ => ∑ j ∈ Finset.univ.erase i,
        (m j * (‖x s j - x s i‖ ^ 3)⁻¹) • (x s j - x s i))
      (∑ j ∈ Finset.univ.erase i,
        ((m j * (‖x t j - x t i‖ ^ 3)⁻¹) • (deriv x t j - deriv x t i)
        - (3 * (m j * ((‖x t j - x t i‖ ^ 5)⁻¹
            * inner ℝ (x t j - x t i) (deriv x t j - deriv x t i)))) • (x t j - x t i))) t := by
    have hfeq : (fun s : ℝ => ∑ j ∈ Finset.univ.erase i,
        (m j * (‖x s j - x s i‖ ^ 3)⁻¹) • (x s j - x s i))
        = ∑ j ∈ Finset.univ.erase i, (fun s : ℝ =>
            (m j * (‖x s j - x s i‖ ^ 3)⁻¹) • (x s j - x s i)) := by
      funext s
      simp only [Finset.sum_apply]
    rw [hfeq]
    refine HasDerivAt.sum fun j hj => ?_
    have hjne : j ≠ i := (Finset.mem_erase.mp hj).1
    have hu : HasDerivAt (fun s : ℝ => x s j - x s i) (deriv x t j - deriv x t i) t :=
      (hasDerivAt_apply hx_t j).sub (hasDerivAt_apply hx_t i)
    have hne : x t j - x t i ≠ 0 := by
      have h1 : r (x t) j i ≠ 0 := hnc_t j i hjne
      rw [r_eq_norm_sub] at h1
      intro hcon
      exact h1 (by rw [hcon, norm_zero])
    have hker := Commons.Analysis.Calculus.hasDerivAt_inv_cube_norm_smul
      (u := fun s : ℝ => x s j - x s i) (u' := deriv x t j - deriv x t i) hu hne
    have hres := hker.const_smul (m j)
    have hfun : (m j • fun s : ℝ => (‖x s j - x s i‖ ^ 3)⁻¹ • (x s j - x s i))
        = (fun s : ℝ => (m j * (‖x s j - x s i‖ ^ 3)⁻¹) • (x s j - x s i)) := by
      funext s
      simp only [Pi.smul_apply, mul_smul]
    rw [hfun] at hres
    refine hres.congr_deriv ?_
    simp only [smul_sub, mul_smul]
    module
  exact hG.congr_of_eventuallyEq hevent

/-! ## The jolt of a body of the cluster -/

/-- Termwise norm bound for the derivative of the force. -/
lemma norm_force_deriv_term_le {m : Fin N → ℝ} {x z : EN E N} {i j : Fin N} (hmj : 0 ≤ m j) :
    ‖(m j * (‖x j - x i‖ ^ 3)⁻¹) • (z j - z i)
      - (3 * (m j * ((‖x j - x i‖ ^ 5)⁻¹ * inner ℝ (x j - x i) (z j - z i)))) • (x j - x i)‖
      ≤ 4 * m j * ‖z j - z i‖ * (‖x j - x i‖ ^ 3)⁻¹ := by
  have h := Commons.Analysis.Calculus.norm_inv_cube_norm_smul_deriv_le
    (u := x j - x i) (u' := z j - z i)
  have hfun : m j • ((‖x j - x i‖ ^ 3)⁻¹ • (z j - z i)
      - (3 * ((‖x j - x i‖ ^ 5)⁻¹ * inner ℝ (x j - x i) (z j - z i))) • (x j - x i))
      = (m j * (‖x j - x i‖ ^ 3)⁻¹) • (z j - z i)
        - (3 * (m j * ((‖x j - x i‖ ^ 5)⁻¹ * inner ℝ (x j - x i) (z j - z i)))) • (x j - x i) := by
    rw [smul_sub]
    congr 1
    · rw [mul_smul]
    · rw [smul_smul]
      congr 1
      ring
  rw [← hfun, norm_smul, Real.norm_eq_abs, abs_of_nonneg hmj]
  calc m j * ‖(‖x j - x i‖ ^ 3)⁻¹ • (z j - z i)
        - (3 * ((‖x j - x i‖ ^ 5)⁻¹ * inner ℝ (x j - x i) (z j - z i))) • (x j - x i)‖
      ≤ m j * (4 * ‖z j - z i‖ * (‖x j - x i‖ ^ 3)⁻¹) :=
        mul_le_mul_of_nonneg_left h hmj
    _ = 4 * m j * ‖z j - z i‖ * (‖x j - x i‖ ^ 3)⁻¹ := by ring

/-- **The jolt of a body of the cluster is bounded** by the kinetic energy and the internal
potential. -/
lemma exists_norm_jolt_le {m : Fin N → ℝ} {k : Finset (Fin N)} {ν Cv : ℝ}
    (hm : ∀ i, 0 < m i) (hν : 0 < ν) (hCv : 0 ≤ Cv) (hk : k.Nonempty) :
    ∃ A : ℝ, 0 < A ∧ ∀ (x z : EN E N), ClusterSeparatedWeak k x ν → WithoutCollisions x →
      1 ≤ clusterPotential m k x →
      (∀ j ∈ k, ‖z j‖ ≤ Cv * Real.sqrt (clusterPotential m k x)) →
      (∀ j ∉ k, ‖z j‖ ≤ Cv * Real.sqrt (clusterPotential m k x)) →
      ∀ i ∈ k, ‖∑ j ∈ Finset.univ.erase i,
        ((m j * (‖x j - x i‖ ^ 3)⁻¹) • (z j - z i)
        - (3 * (m j * ((‖x j - x i‖ ^ 5)⁻¹
            * inner ℝ (x j - x i) (z j - z i)))) • (x j - x i))‖
      ≤ A * Cv * Real.sqrt (clusterPotential m k x) * clusterPotential m k x ^ 3 := by
  obtain ⟨κ, hκpos, hκ⟩ : ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ m i := by
    obtain ⟨i₀, hi₀⟩ := hk
    obtain ⟨i₁, -, hi₁⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin N)) m
      ⟨i₀, Finset.mem_univ i₀⟩
    exact ⟨m i₁, hm i₁, fun i => hi₁ i (Finset.mem_univ i)⟩
  set A : ℝ := 8 * ((N : ℝ) / κ ^ 5 + (∑ j : Fin N, m j) * (ν⁻¹) ^ 3) + 1 with hA
  have hApos : 0 < A := by
    rw [hA]
    have h1 : 0 ≤ ((N : ℝ) / κ ^ 5) := by positivity
    have h2 : 0 ≤ (∑ j : Fin N, m j) * (ν⁻¹) ^ 3 :=
      mul_nonneg (Finset.sum_nonneg fun j _ => (hm j).le) (by positivity)
    linarith
  refine ⟨A, hApos, fun x z hsep hnc hU hzk hzc i hi => ?_⟩
  have hU1 : (1:ℝ) ≤ clusterPotential m k x := hU
  have hsU1 : 1 ≤ Real.sqrt (clusterPotential m k x) := Real.one_le_sqrt.mpr hU1
  have hsUnn : 0 ≤ Real.sqrt (clusterPotential m k x) := Real.sqrt_nonneg _
  have hterm : ∀ j ∈ Finset.univ.erase i,
      ‖(m j * (‖x j - x i‖ ^ 3)⁻¹) • (z j - z i)
        - (3 * (m j * ((‖x j - x i‖ ^ 5)⁻¹
            * inner ℝ (x j - x i) (z j - z i)))) • (x j - x i)‖
      ≤ 8 * Cv * Real.sqrt (clusterPotential m k x) * (m j * ((‖x j - x i‖)⁻¹) ^ 3) := by
    intro j _
    have hinv : (‖x j - x i‖ ^ 3)⁻¹ = ((‖x j - x i‖)⁻¹) ^ 3 := (inv_pow _ 3).symm
    refine le_trans (norm_force_deriv_term_le (hm j).le) ?_
    rw [hinv]
    have h1 : ‖z j - z i‖ ≤ ‖z j‖ + ‖z i‖ := norm_sub_le _ _
    have h2 : ‖z j‖ + ‖z i‖
        ≤ 2 * Cv * Real.sqrt (clusterPotential m k x) := by
      by_cases hj : j ∈ k
      · have h3 := hzk j hj
        have h4 := hzk i hi
        linarith
      · have h3 := hzc j hj
        have h4 := hzk i hi
        linarith
    have h3 : 4 * m j * ‖z j - z i‖ * ((‖x j - x i‖)⁻¹) ^ 3
        ≤ 4 * m j * (2 * Cv * Real.sqrt (clusterPotential m k x)) * ((‖x j - x i‖)⁻¹) ^ 3 := by
      refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) 3)
      exact mul_le_mul_of_nonneg_left (le_trans h1 h2) (mul_nonneg (by norm_num) (hm j).le)
    refine le_trans h3 (le_of_eq ?_)
    ring
  calc ‖∑ j ∈ Finset.univ.erase i,
        ((m j * (‖x j - x i‖ ^ 3)⁻¹) • (z j - z i)
        - (3 * (m j * ((‖x j - x i‖ ^ 5)⁻¹
            * inner ℝ (x j - x i) (z j - z i)))) • (x j - x i))‖
      ≤ ∑ j ∈ Finset.univ.erase i,
          ‖(m j * (‖x j - x i‖ ^ 3)⁻¹) • (z j - z i)
            - (3 * (m j * ((‖x j - x i‖ ^ 5)⁻¹
                * inner ℝ (x j - x i) (z j - z i)))) • (x j - x i)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.univ.erase i,
          8 * Cv * Real.sqrt (clusterPotential m k x) * (m j * ((‖x j - x i‖)⁻¹) ^ 3) :=
        Finset.sum_le_sum hterm
    _ = 8 * Cv * Real.sqrt (clusterPotential m k x)
          * (∑ j ∈ Finset.univ.erase i, m j * ((‖x j - x i‖)⁻¹) ^ 3) := by
        rw [Finset.mul_sum]
    _ ≤ 8 * Cv * Real.sqrt (clusterPotential m k x)
          * ((∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∈ k),
              m j * ((‖x j - x i‖)⁻¹) ^ 3)
            + (∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k),
              m j * ((‖x j - x i‖)⁻¹) ^ 3)) := by
        rw [Finset.sum_filter_add_sum_filter_not]
    _ ≤ 8 * Cv * Real.sqrt (clusterPotential m k x)
          * ((N : ℝ) * ((clusterPotential m k x) ^ 3 / κ ^ 5)
            + (∑ j : Fin N, m j) * (ν⁻¹) ^ 3) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by positivity)
        · exact sum_inv_cube_le hm hκ hκpos hi
        · have hcross : ∀ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k),
              m j * ((‖x j - x i‖)⁻¹) ^ 3 ≤ m j * (ν⁻¹) ^ 3 := by
            intro j hj
            obtain ⟨hji, hjk⟩ := Finset.mem_filter.mp hj
            have hjne : j ≠ i := (Finset.mem_erase.mp hji).1
            have hdist : ν ≤ ‖x j - x i‖ := by
              have h := hsep i hi j hjk
              rwa [r_eq_norm_sub, norm_sub_rev] at h
            have hnorm : 0 < ‖x j - x i‖ := lt_of_lt_of_le hν hdist
            have hinv : (‖x j - x i‖)⁻¹ ≤ ν⁻¹ := (inv_le_inv₀ hnorm hν).mpr hdist
            have h3 : ((‖x j - x i‖)⁻¹) ^ 3 ≤ (ν⁻¹) ^ 3 :=
              pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) hinv 3
            exact mul_le_mul_of_nonneg_left h3 (hm j).le
          refine le_trans (Finset.sum_le_sum hcross) ?_
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro j hj
            rw [Finset.mem_filter] at hj
            simp [hj.1]
          · intro j _ _
            exact mul_nonneg (hm j).le (by positivity)
    _ ≤ A * Cv * Real.sqrt (clusterPotential m k x) * clusterPotential m k x ^ 3 := by
        rw [hA]
        have hS : 0 ≤ Real.sqrt (clusterPotential m k x) := hsUnn
        have hU3 : 1 ≤ clusterPotential m k x ^ 3 := by
          simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hU1 3
        have hY0 : 0 ≤ (∑ j : Fin N, m j) * (ν⁻¹) ^ 3 :=
          mul_nonneg (Finset.sum_nonneg fun j _ => (hm j).le) (by positivity)
        have hYU : (∑ j : Fin N, m j) * (ν⁻¹) ^ 3
            ≤ (∑ j : Fin N, m j) * (ν⁻¹) ^ 3 * clusterPotential m k x ^ 3 :=
          le_mul_of_one_le_right hY0 hU3
        have hN1 : (↑N * (clusterPotential m k x ^ 3 / κ ^ 5))
            = ((N : ℝ) / κ ^ 5) * clusterPotential m k x ^ 3 := by ring
        have hc : 0 ≤ 8 * Cv * Real.sqrt (clusterPotential m k x) := by positivity
        calc 8 * Cv * Real.sqrt (clusterPotential m k x)
              * ((↑N * (clusterPotential m k x ^ 3 / κ ^ 5))
                + (∑ j : Fin N, m j) * (ν⁻¹) ^ 3)
            = 8 * Cv * Real.sqrt (clusterPotential m k x)
              * (((N : ℝ) / κ ^ 5) * clusterPotential m k x ^ 3
                + (∑ j : Fin N, m j) * (ν⁻¹) ^ 3) := by rw [hN1]
          _ ≤ 8 * Cv * Real.sqrt (clusterPotential m k x)
              * (((N : ℝ) / κ ^ 5) * clusterPotential m k x ^ 3
                + (∑ j : Fin N, m j) * (ν⁻¹) ^ 3 * clusterPotential m k x ^ 3) := by
              refine mul_le_mul_of_nonneg_left ?_ hc
              linarith [hYU]
          _ = 8 * Cv * Real.sqrt (clusterPotential m k x)
              * (((N : ℝ) / κ ^ 5 + (∑ j : Fin N, m j) * (ν⁻¹) ^ 3)
                * clusterPotential m k x ^ 3) := by ring
          _ ≤ (8 * ((N : ℝ) / κ ^ 5 + (∑ j : Fin N, m j) * (ν⁻¹) ^ 3) + 1)
              * Cv * Real.sqrt (clusterPotential m k x) * clusterPotential m k x ^ 3 := by
              have hz : 0 ≤ Cv * Real.sqrt (clusterPotential m k x)
                  * clusterPotential m k x ^ 3 := by positivity
              nlinarith [hz]

end Submission.NBody
