import Submission.NBody.MarchalSundmanApply
import Submission.NBody.SpernerBound
import Mathlib

/-!
# The a priori bound `U_k ≥ c/√I_k` for a cluster

The classical a priori bound of Sperner–Wintner relating the Newtonian potential to the moment of
inertia, here in the form needed for a *cluster* `k`: for every collision-free configuration,

    `U_k(x) ≥ c / √(I_k(x))`,   `I_k = ∑_{i∈k} mᵢ‖xᵢ - x_{cm,k}‖²`,

with a constant `c > 0` depending only on the masses.  It is the estimate which, combined with the
Lagrange–Jacobi identity, forces the collision rate `|t - t₀|^{2/3}`.

The proof is the same as for the whole system (`Submission.NBody.exists_const_div_sqrt_inertia_le_U`):
each body of the cluster is within `√(I_k/κ)` of the centre of mass, so each pair distance is at
most `2√(I_k/κ)`, and the single pair term `mᵢmⱼ/rᵢⱼ` already dominates `c/√I_k`.

Everything here is fully proved.
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

/-- **The a priori bound `U_k ≥ c/√I_k` for a cluster.** -/
theorem exists_const_le_clusterPotential {m : Fin N → ℝ} (hm : ∀ i, 0 < m i)
    (k : Finset (Fin N)) (hk2 : 2 ≤ k.card) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : EN E N, WithoutCollisions x →
      c / Real.sqrt (clusterInertia m k x) ≤ clusterPotential m k x := by
  classical
  obtain ⟨i₁, hi₁⟩ : ∃ i, i ∈ k := by
    rcases Finset.eq_empty_or_nonempty k with h | ⟨i, hi⟩
    · rw [h] at hk2
      simp at hk2
    · exact ⟨i, hi⟩
  obtain ⟨j₁, hj₁, hij₁⟩ : ∃ j ∈ k, i₁ ≠ j := by
    by_contra h
    push Not at h
    have hsub : k ⊆ {i₁} := fun j hj => Finset.mem_singleton.mpr (h j hj).symm
    have := Finset.card_le_card hsub
    simp at this
    omega
  obtain ⟨κ, hκpos, hκ⟩ : ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ m i := by
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin N)) m
      ⟨i₁, Finset.mem_univ _⟩
    exact ⟨m i₀, hm i₀, fun i => hi₀ i (Finset.mem_univ i)⟩
  have hpairpos : 0 < m i₁ * m j₁ := mul_pos (hm i₁) (hm j₁)
  set c : ℝ := m i₁ * m j₁ * Real.sqrt κ / 2 with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]
    have : (0:ℝ) < Real.sqrt κ := Real.sqrt_pos.mpr hκpos
    positivity
  refine ⟨c, hcpos, fun x hx => ?_⟩
  set cm : E := clusterCM m k x with hcmdef
  set I : ℝ := clusterInertia m k x with hIdef
  have hIdef' : I = ∑ i ∈ k, m i * ‖x i - cm‖ ^ 2 := rfl
  have hInn : 0 ≤ I := clusterInertia_nonneg (fun i => (hm i).le) k x
  -- the pair `(i₁,j₁)` is collision free
  have hdist_pos : 0 < dist (x i₁) (x j₁) :=
    dist_pos.mpr fun heq => hx i₁ j₁ hij₁ (by rw [r, dist_eq_zero]; exact heq)
  have hIpos : 0 < I := by
    have hsub : ({i₁, j₁} : Finset (Fin N)) ⊆ k := by
      intro i hi
      rw [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact hi₁
      · exact hj₁
    have h1 : m i₁ * ‖x i₁ - cm‖ ^ 2 + m j₁ * ‖x j₁ - cm‖ ^ 2 ≤ I := by
      have hle := Finset.sum_le_sum_of_subset_of_nonneg
        (f := fun i : Fin N => m i * ‖x i - cm‖ ^ 2)
        (s := ({i₁, j₁} : Finset (Fin N))) (t := k) hsub
        (fun i _ _ => mul_nonneg (hm i).le (sq_nonneg _))
      rw [Finset.sum_pair hij₁] at hle
      rw [hIdef']
      exact hle
    have h2 : 0 < ‖x i₁ - cm‖ ^ 2 + ‖x j₁ - cm‖ ^ 2 := by
      have h3 : (0:ℝ) < ‖x i₁ - x j₁‖ := by
        rw [← dist_eq_norm]; exact hdist_pos
      have h4 : ‖x i₁ - x j₁‖ ≤ ‖x i₁ - cm‖ + ‖x j₁ - cm‖ := by
        have h5 : x i₁ - x j₁ = (x i₁ - cm) - (x j₁ - cm) := by abel
        rw [h5]
        exact norm_sub_le _ _
      nlinarith [norm_nonneg (x i₁ - cm), norm_nonneg (x j₁ - cm),
        sq_nonneg (‖x i₁ - cm‖ - ‖x j₁ - cm‖)]
    have h5 : κ * (‖x i₁ - cm‖ ^ 2 + ‖x j₁ - cm‖ ^ 2)
        ≤ m i₁ * ‖x i₁ - cm‖ ^ 2 + m j₁ * ‖x j₁ - cm‖ ^ 2 := by
      nlinarith [hκ i₁, hκ j₁, sq_nonneg (‖x i₁ - cm‖), sq_nonneg (‖x j₁ - cm‖)]
    nlinarith [h1, h2, h5, hκpos]
  have hcoord : ∀ i ∈ k, ‖x i - cm‖ ^ 2 ≤ I / κ := by
    intro i hi
    have h1 : m i * ‖x i - cm‖ ^ 2 ≤ I := by
      rw [hIdef']
      exact Finset.single_le_sum (f := fun k : Fin N => m k * ‖x k - cm‖ ^ 2)
        (fun k _ => mul_nonneg (hm k).le (sq_nonneg _)) hi
    rw [le_div_iff₀ hκpos]
    calc ‖x i - cm‖ ^ 2 * κ ≤ ‖x i - cm‖ ^ 2 * m i :=
          mul_le_mul_of_nonneg_left (hκ i) (sq_nonneg _)
      _ = m i * ‖x i - cm‖ ^ 2 := by ring
      _ ≤ I := h1
  have hdist : ∀ i ∈ k, ∀ j ∈ k, dist (x i) (x j) ≤ 2 * Real.sqrt (I / κ) := by
    intro i hi j hj
    have h1 : ‖x i - x j‖ ≤ ‖x i - cm‖ + ‖x j - cm‖ := by
      have h5 : x i - x j = (x i - cm) - (x j - cm) := by abel
      rw [h5]
      exact norm_sub_le _ _
    have h2 : ‖x i - cm‖ ≤ Real.sqrt (I / κ) := by
      rw [← Real.sqrt_sq (norm_nonneg _)]
      exact Real.sqrt_le_sqrt (hcoord i hi)
    have h3 : ‖x j - cm‖ ≤ Real.sqrt (I / κ) := by
      rw [← Real.sqrt_sq (norm_nonneg _)]
      exact Real.sqrt_le_sqrt (hcoord j hj)
    rw [dist_eq_norm]
    linarith
  have hinv : ∀ i ∈ k, ∀ j ∈ k, i ≠ j →
      Real.sqrt κ / (2 * Real.sqrt I) ≤ (dist (x i) (x j))⁻¹ := by
    intro i hi j hj hij
    have hpos : 0 < dist (x i) (x j) :=
      dist_pos.mpr fun heq => hx i j hij (by rw [r, dist_eq_zero]; exact heq)
    have h2 : dist (x i) (x j) ≤ 2 * Real.sqrt I / Real.sqrt κ := by
      have h3 : 2 * Real.sqrt (I / κ) = 2 * Real.sqrt I / Real.sqrt κ := by
        rw [Real.sqrt_div (x := I) hInn κ, mul_div_assoc]
      rw [← h3]
      exact hdist i hi j hj
    have hBpos : 0 < 2 * Real.sqrt I / Real.sqrt κ := by
      have h1 : 0 < Real.sqrt I := Real.sqrt_pos.mpr hIpos
      have h2 : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκpos
      positivity
    have h4 : (2 * Real.sqrt I / Real.sqrt κ)⁻¹ ≤ (dist (x i) (x j))⁻¹ :=
      (inv_le_inv₀ hBpos hpos).mpr h2
    have h5 : (2 * Real.sqrt I / Real.sqrt κ)⁻¹ = Real.sqrt κ / (2 * Real.sqrt I) := by
      rw [inv_div]
    rwa [h5] at h4
  -- a single pair term of the cluster potential dominates
  rw [clusterPotential]
  have hterm : m i₁ * m j₁ * (Real.sqrt κ / (2 * Real.sqrt I))
      ≤ m i₁ * m j₁ * (dist (x i₁) (x j₁))⁻¹ :=
    mul_le_mul_of_nonneg_left (hinv i₁ hi₁ j₁ hj₁ hij₁) (mul_nonneg (hm i₁).le (hm j₁).le)
  have hsum : ∀ p : Fin N × Fin N, 0 ≤ m p.1 * m p.2 * (r x p.1 p.2)⁻¹ :=
    fun p => mul_nonneg (mul_nonneg (hm p.1).le (hm p.2).le) (inv_nonneg.mpr dist_nonneg)
  have hgoal : c / Real.sqrt I = m i₁ * m j₁ * (Real.sqrt κ / (2 * Real.sqrt I)) := by
    rw [hcdef]; ring
  rw [hgoal]
  rcases lt_or_gt_of_ne hij₁ with hlt | hgt
  · have hmem : (i₁, j₁) ∈ (pairFinset N).filter
        (fun p => p.1 ∈ k ∧ p.2 ∈ k) := by
      rw [Finset.mem_filter, pairFinset, Finset.mem_filter]
      exact ⟨⟨Finset.mem_univ _, hlt⟩, hi₁, hj₁⟩
    exact le_trans hterm (Finset.single_le_sum (fun p _ => hsum p) hmem)
  · have hmem : (j₁, i₁) ∈ (pairFinset N).filter
        (fun p => p.1 ∈ k ∧ p.2 ∈ k) := by
      rw [Finset.mem_filter, pairFinset, Finset.mem_filter]
      exact ⟨⟨Finset.mem_univ _, hgt⟩, hj₁, hi₁⟩
    have hterm2 : m i₁ * m j₁ * (Real.sqrt κ / (2 * Real.sqrt I))
        ≤ m j₁ * m i₁ * (dist (x j₁) (x i₁))⁻¹ := by
      have h := mul_le_mul_of_nonneg_left (hinv j₁ hj₁ i₁ hi₁ (Ne.symm hij₁))
        (mul_nonneg (hm j₁).le (hm i₁).le)
      calc m i₁ * m j₁ * (Real.sqrt κ / (2 * Real.sqrt I))
          = m j₁ * m i₁ * (Real.sqrt κ / (2 * Real.sqrt I)) := by ring
        _ ≤ m j₁ * m i₁ * (dist (x j₁) (x i₁))⁻¹ := h
    refine le_trans ?_ (Finset.single_le_sum (fun p _ => hsum p) hmem)
    calc m i₁ * m j₁ * (Real.sqrt κ / (2 * Real.sqrt I))
        ≤ m j₁ * m i₁ * (dist (x j₁) (x i₁))⁻¹ := hterm2
      _ = m j₁ * m i₁ * (r x j₁ i₁)⁻¹ := by rw [r]

end Submission.NBody
