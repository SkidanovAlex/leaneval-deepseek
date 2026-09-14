import Submission.NBody.MarchalThirdDeriv
import Submission.Commons.Analysis.Calculus.second_deriv_asymptotic_of_third_deriv_bound

/-!
# The third derivative of the moment of inertia of a colliding cluster

The refinement of Sundman's analysis (Ferrario–Terracini, `lemma:bach`) needs a bound on the third
derivative of the moment of inertia of a colliding cluster in terms of the second:

    `|I_k'''| ≤ e (I_k'')^{5/2}`.

This file contains the pure-calculus identity

    `I_k''' = 6 ⟪q̇, q̈⟫_m + 2 ⟪q, q⃛⟫_m`

for `q = cmRel m k ∘ x`, together with the elementary norm estimates which turn the bounds on the
relative acceleration and the relative jolt of a body of the cluster into that inequality.

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

/-! ## The third derivative of the moment of inertia -/

/-- **The third derivative of the moment of inertia of a cluster along a curve.** -/
theorem deriv_deriv_deriv_clusterInertia_eq {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε t : ℝ} (ht : t ∈ Ioo (0:ℝ) ε)
    (hx : ∀ s ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x s) s)
    (hd2 : ∀ s ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (deriv (deriv x) s) s)
    (hd3 : ∀ s ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv (deriv x)) (deriv (deriv (deriv x)) s) s) :
    deriv (deriv (deriv (fun s : ℝ => clusterInertia m k (x s)))) t
      = 6 * massInner m (cmRel m k (deriv x t)) (cmRel m k (deriv (deriv x) t))
        + 2 * massInner m (cmRel m k (x t)) (cmRel m k (deriv (deriv (deriv x)) t)) := by
  set G1 : ℝ → ℝ := fun s => massInner m (cmRel m k (x s)) (cmRel m k (x s)) with hG1def
  set G2 : ℝ → ℝ := fun s => 2 * massInner m (cmRel m k (x s)) (cmRel m k (deriv x s))
    with hG2def
  set G3 : ℝ → ℝ := fun s => 2 * massInner m (cmRel m k (deriv x s)) (cmRel m k (deriv x s))
      + 2 * massInner m (cmRel m k (x s)) (cmRel m k (deriv (deriv x) s)) with hG3def
  have hG1eq : (fun s : ℝ => clusterInertia m k (x s)) = G1 := by
    funext s
    rw [hG1def, clusterInertia_eq_massInner]
  have hxloc : ∀ᶠ s in 𝓝 t, HasDerivAt x (deriv x s) s :=
    Filter.eventually_iff_exists_mem.mpr
      ⟨Set.Ioo (0:ℝ) ε, isOpen_Ioo.mem_nhds ht, fun s hs => hx s hs⟩
  have hG2eq : G2 = fun u => 2 * massInner m (cmRel m k (x u)) (cmRel m k (deriv x u)) := by
    funext u; rw [hG2def]
  have hG3eq : G3 = fun u => 2 * massInner m (cmRel m k (deriv x u)) (cmRel m k (deriv x u))
      + 2 * massInner m (cmRel m k (x u)) (cmRel m k (deriv (deriv x) u)) := by
    funext u; rw [hG3def]
  have hdG1 : deriv G1 =ᶠ[𝓝 t] G2 := by
    have h := deriv_clusterInertia_eq m k hxloc
    rw [← hG1eq]
    filter_upwards [h] with s hs
    rw [hG2def]
    exact hs
  have hdG2 : deriv G2 =ᶠ[𝓝 t] G3 := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    have hpair := (hasDerivAt_inertia_pair m k (hx s hs) (hd2 s hs)).const_mul 2
    rw [hG2eq, hpair.deriv]
    rw [hG3def]
    ring
  have hdG3 : HasDerivAt G3
      (6 * massInner m (cmRel m k (deriv x t)) (cmRel m k (deriv (deriv x) t))
        + 2 * massInner m (cmRel m k (x t)) (cmRel m k (deriv (deriv (deriv x)) t))) t := by
    have h1 : HasDerivAt (fun s => massInner m (cmRel m k (deriv x s))
          (cmRel m k (deriv x s)))
        (massInner m (cmRel m k (deriv (deriv x) t)) (cmRel m k (deriv x t))
          + massInner m (cmRel m k (deriv x t)) (cmRel m k (deriv (deriv x) t))) t :=
      hasDerivAt_inertia_pair m k (hd2 t ht) (hd2 t ht)
    have h2 : HasDerivAt (fun s => massInner m (cmRel m k (x s))
          (cmRel m k (deriv (deriv x) s)))
        (massInner m (cmRel m k (deriv x t)) (cmRel m k (deriv (deriv x) t))
          + massInner m (cmRel m k (x t)) (cmRel m k (deriv (deriv (deriv x)) t))) t :=
      hasDerivAt_inertia_pair m k (hx t ht) (hd3 t ht)
    have h := (h1.const_mul 2).add (h2.const_mul 2)
    rw [hG3eq]
    refine h.congr_deriv ?_
    rw [massInner_comm m (cmRel m k (deriv (deriv x) t)) (cmRel m k (deriv x t))]
    ring
  rw [hG1eq]
  rw [Filter.EventuallyEq.deriv_eq (Filter.EventuallyEq.deriv hdG1),
    Filter.EventuallyEq.deriv_eq hdG2]
  exact hdG3.deriv



/-! ## The pair kernel of the jolt -/

/-- The pair contribution to the derivative of the force (the "jolt" kernel).  Its sum over `j`,
weighted by `m j`, is the third derivative of the body `i` along the motion. -/
noncomputable def pairJolt {N : ℕ} (x v : EN E N) (j i : Fin N) : E :=
  ((‖x j - x i‖ ^ 3)⁻¹) • (v j - v i)
    - (3 * ((‖x j - x i‖ ^ 5)⁻¹ * inner ℝ (x j - x i) (v j - v i))) • (x j - x i)

lemma smul_pairJolt {N : ℕ} (a : ℝ) (x v : EN E N) (j i : Fin N) :
    a • pairJolt x v j i
      = (a * (‖x j - x i‖ ^ 3)⁻¹) • (v j - v i)
        - (3 * (a * ((‖x j - x i‖ ^ 5)⁻¹ * inner ℝ (x j - x i) (v j - v i))))
          • (x j - x i) := by
  have hsc : a * (3 * ((‖x j - x i‖ ^ 5)⁻¹ * inner ℝ (x j - x i) (v j - v i)))
      = 3 * (a * ((‖x j - x i‖ ^ 5)⁻¹ * inner ℝ (x j - x i) (v j - v i))) := by ring
  rw [pairJolt, smul_sub, smul_smul, smul_smul, hsc]

lemma pairJolt_swap {N : ℕ} (x v : EN E N) (j i : Fin N) :
    pairJolt x v j i = - pairJolt x v i j := by
  have hrs : ‖x i - x j‖ = ‖x j - x i‖ := (norm_sub_rev _ _).symm
  have hss : inner ℝ (x i - x j) (v i - v j) = inner ℝ (x j - x i) (v j - v i) := by
    rw [show x i - x j = -(x j - x i) by abel, show v i - v j = -(v j - v i) by abel,
      inner_neg_left, inner_neg_right, neg_neg]
  simp only [pairJolt, hrs, hss]
  rw [show v i - v j = -(v j - v i) by abel, show x i - x j = -(x j - x i) by abel]
  simp only [smul_neg]
  abel

lemma inner_pairJolt {N : ℕ} (x v : EN E N) (j i : Fin N) :
    inner ℝ (x j - x i) (pairJolt x v j i)
      = -2 * ((‖x j - x i‖ ^ 3)⁻¹) * inner ℝ (x j - x i) (v j - v i) := by
  rw [pairJolt, inner_sub_right, real_inner_smul_right, real_inner_smul_right]
  rw [real_inner_self_eq_norm_sq]
  have h : (3 * ((‖x j - x i‖ ^ 5)⁻¹ * inner ℝ (x j - x i) (v j - v i)))
        * ‖x j - x i‖ ^ 2
      = 3 * ((‖x j - x i‖ ^ 3)⁻¹) * inner ℝ (x j - x i) (v j - v i) := by
    by_cases hr : ‖x j - x i‖ = 0
    · rw [hr]; simp
    · field_simp
  rw [h]
  ring

/-- The coordinate of the third derivative of the curve along a motion. -/
lemma iteratedDeriv_three_apply {m : Fin N → ℝ} {x : ℝ → EN E N} {ε t : ℝ}
    (hmne : ∀ i, m i ≠ 0) (ht : t ∈ Ioo (0:ℝ) ε)
    (hx : ∀ s ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x s) s)
    (hd3 : HasDerivAt (deriv (deriv x)) (deriv (deriv (deriv x)) t) t)
    (hode : ∀ s ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x s = ∇_[m] (U m) (x s))
    (hnc : ∀ s ∈ Ioo (0:ℝ) ε, WithoutCollisions (x s)) (i : Fin N) :
    deriv (deriv (deriv x)) t i
      = ∑ j ∈ Finset.univ.erase i, m j • pairJolt (x t) (deriv x t) j i := by
  have heq : (deriv (deriv x)) =ᶠ[𝓝 t] (fun s : ℝ => ∇_[m] (U m) (x s)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    rw [← hode s hs]
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  have hd3' : HasDerivAt (fun s : ℝ => ∇_[m] (U m) (x s)) (deriv (deriv (deriv x)) t) t :=
    hd3.congr_of_eventuallyEq heq.symm
  have hcoord : deriv (fun s : ℝ => (∇_[m] (U m) (x s)) i) t = deriv (deriv (deriv x)) t i :=
    (hasDerivAt_apply hd3' i).deriv
  rw [← hcoord]
  have hmain := hasDerivAt_weightedGrad_coord (E := E) (N := N) (m := m) (x := x) (ε := ε)
    (t := t) hmne ht hx hnc i
  rw [hmain.deriv]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_pairJolt]


lemma pairJolt_self {N : ℕ} (x v : EN E N) (i : Fin N) : pairJolt x v i i = 0 := by
  simp [pairJolt]

lemma sum_erase_eq_sum_of_zero {N : ℕ} {M : Type*} [AddCommMonoid M] {k : Finset (Fin N)}
    {i : Fin N} {f : Fin N → M} (hi : i ∈ k) (hzero : f i = 0) :
    (∑ j ∈ k.erase i, f j) = ∑ j ∈ k, f j := by
  have h := Finset.sum_erase_add (s := k) (a := i) (f := f) hi
  rw [hzero, add_zero] at h
  exact h

/-- **The third derivative of the moment of inertia, as a pair sum.**  The internal pairs combine
(the antisymmetric kernel pairs up) into the "jolt work" sum, while the interaction with the bodies
outside `k` is a separate sum of the expected size. -/
theorem massInner_cmRel_third_eq {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N} {ε t : ℝ}
    (ht : t ∈ Ioo (0:ℝ) ε)
    (hx : ∀ s ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x s) s)
    (hd3 : HasDerivAt (deriv (deriv x)) (deriv (deriv (deriv x)) t) t)
    (hode : ∀ s ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x s = ∇_[m] (U m) (x s))
    (hnc : ∀ s ∈ Ioo (0:ℝ) ε, WithoutCollisions (x s))
    (hm : ∀ i, m i ≠ 0) (hmk : clusterMass m k ≠ 0) :
    massInner m (cmRel m k (x t)) (cmRel m k (deriv (deriv (deriv x)) t))
      = (∑ i ∈ k, ∑ j ∈ k, m i * m j * ((‖x t i - x t j‖ ^ 3)⁻¹)
            * inner ℝ (x t i - x t j) (deriv x t i - deriv x t j))
        - (∑ i ∈ k, ∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k),
            m i * m j * inner ℝ ((cmRel m k (x t)) i)
              (pairJolt (x t) (deriv x t) i j)) := by
  classical
  rw [massInner_cmRel_cmRel_eq m k (x t) (deriv (deriv (deriv x)) t) hmk,
    massInner_cmRel_eq' m k (x t) (deriv (deriv (deriv x)) t)]
  set X : Fin N → Fin N → ℝ := fun i j => m i * m j * ((‖x t i - x t j‖ ^ 3)⁻¹)
    * inner ℝ (x t i - x t j) (deriv x t i - deriv x t j) with hX
  set Q : ℝ := ∑ i ∈ k, ∑ j ∈ k, X i j with hQ
  set A : Fin N → Fin N → ℝ := fun i j => m i * m j *
    inner ℝ ((cmRel m k (x t)) i) (pairJolt (x t) (deriv x t) i j) with hA
  set G : Fin N → Fin N → ℝ := fun i j => m i * m j *
    inner ℝ ((cmRel m k (x t)) i) (pairJolt (x t) (deriv x t) j i) with hG
  have hanti : ∀ i j, G i j = - A i j := by
    intro i j
    simp only [hG, hA, pairJolt_swap (x t) (deriv x t) j i, inner_neg_right]
    ring
  have hsym : ∀ i ∈ k, ∀ j ∈ k, A i j + A j i = -2 * X i j := by
    intro i hi j hj
    have hqq : (cmRel m k (x t)) i - (cmRel m k (x t)) j = x t i - x t j := by
      rw [cmRel_apply_of_mem hi, cmRel_apply_of_mem hj]; abel
    have hkey : A i j + A j i = m i * m j *
        (inner ℝ ((cmRel m k (x t)) i) (pairJolt (x t) (deriv x t) i j)
          - inner ℝ ((cmRel m k (x t)) j) (pairJolt (x t) (deriv x t) i j)) := by
      simp only [hA, pairJolt_swap (x t) (deriv x t) j i, inner_neg_right]
      ring
    rw [hkey, ← inner_sub_left, hqq, inner_pairJolt, hX]
    ring
  have hsumA : (∑ i ∈ k, ∑ j ∈ k, A i j) = -Q := by
    have hcomm : (∑ i ∈ k, ∑ j ∈ k, (A i j + A j i))
        = (∑ i ∈ k, ∑ j ∈ k, A i j) + (∑ i ∈ k, ∑ j ∈ k, A j i) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
    have hval : (∑ i ∈ k, ∑ j ∈ k, (A i j + A j i)) = -2 * Q := by
      rw [Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => hsym i hi j hj)),
        hQ]
      have h1 : ∀ i ∈ k, (∑ j ∈ k, -2 * X i j) = -2 * (∑ j ∈ k, X i j) := by
        intro i _
        rw [Finset.mul_sum]
      rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
    rw [hcomm, Finset.sum_comm (s := k) (t := k) (f := fun i j => A j i)] at hval
    linarith [hval]
  have hsumG : (∑ i ∈ k, ∑ j ∈ k, G i j) = Q := by
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hanti i j))]
    have h2 : ∀ i ∈ k, (∑ j ∈ k, - (A i j)) = - (∑ j ∈ k, A i j) :=
      fun i _ => Finset.sum_neg_distrib (fun j => A i j)
    rw [Finset.sum_congr rfl h2, Finset.sum_neg_distrib, hsumA]
    ring
  -- Step 1: substitute the third derivative
  have hterm : ∀ i ∈ k, m i * inner ℝ ((x t) i - clusterCM m k (x t))
      ((deriv (deriv (deriv x)) t) i) = ∑ j ∈ Finset.univ.erase i, G i j := by
    intro i hi
    rw [show (x t) i - clusterCM m k (x t) = (cmRel m k (x t)) i from
        (cmRel_apply_of_mem hi).symm,
      iteratedDeriv_three_apply (m := m) (x := x) (ε := ε) (t := t) hm ht hx hd3 hode hnc i,
      inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hG, real_inner_smul_right]
    ring
  rw [Finset.sum_congr rfl hterm]
  -- Step 2: split the inner sum into the internal and the external part
  have hsplit : ∀ i ∈ k, (∑ j ∈ Finset.univ.erase i, G i j)
      = (∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∈ k), G i j)
        + (∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k), G i j) := by
    intro i _
    rw [Finset.sum_filter_add_sum_filter_not]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  have hint1 : (∑ i ∈ k, ∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∈ k), G i j)
      = ∑ i ∈ k, (∑ j ∈ k, G i j) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hfilter : (Finset.univ.erase i).filter (fun j : Fin N => j ∈ k) = k.erase i := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ]
      tauto
    rw [hfilter]
    exact sum_erase_eq_sum_of_zero hi (by simp only [hG]; simp [pairJolt])
  have hext : (∑ i ∈ k, ∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k), G i j)
      = - (∑ i ∈ k, ∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k), A i j) := by
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hanti i j))]
    have h2 : ∀ i ∈ k, (∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k), - (A i j))
        = - (∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k), A i j) :=
      fun i _ => Finset.sum_neg_distrib (fun j => A i j)
    rw [Finset.sum_congr rfl h2, Finset.sum_neg_distrib]
  rw [hint1, hsumG, hext]
  ring

/-! ## Bounds for the two sums -/

lemma clusterPotential_nonneg {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (k : Finset (Fin N))
    (x : EN E N) : 0 ≤ clusterPotential m k x := by
  rw [clusterPotential]
  exact Finset.sum_nonneg fun p _ =>
    mul_nonneg (mul_nonneg (hm p.1) (hm p.2)) (inv_nonneg.mpr dist_nonneg)

lemma abs_inv_cube_inner_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u w : E) :
    |((‖u‖ ^ 3)⁻¹) * inner ℝ u w| ≤ ((‖u‖)⁻¹) ^ 2 * ‖w‖ := by
  have h1 : |inner ℝ u w| ≤ ‖u‖ * ‖w‖ := abs_real_inner_le_norm u w
  rw [abs_mul, abs_of_nonneg (by positivity)]
  calc ((‖u‖ ^ 3)⁻¹) * |inner ℝ u w| ≤ ((‖u‖^3)⁻¹) * (‖u‖ * ‖w‖) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ((‖u‖)⁻¹) ^ 2 * ‖w‖ := by
        rcases eq_or_ne (‖u‖) 0 with h | h
        · rw [h]; simp
        · field_simp

/-- Termwise bound for the internal pair sum. -/
lemma abs_pair_term_le {m : Fin N → ℝ} {x v : EN E N} {U : ℝ}
    {i j : Fin N} (hmij : 0 < m i * m j) (hb : (‖x i - x j‖)⁻¹ ≤ U / (m i * m j)) :
    |m i * m j * ((‖x i - x j‖ ^ 3)⁻¹) * inner ℝ (x i - x j) (v i - v j)|
      ≤ U ^ 2 * ‖v i - v j‖ / (m i * m j) := by
  have hp : 0 < m i * m j := hmij
  have h2 : |((‖x i - x j‖ ^ 3)⁻¹) * inner ℝ (x i - x j) (v i - v j)|
      ≤ ((‖x i - x j‖)⁻¹) ^ 2 * ‖v i - v j‖ :=
    abs_inv_cube_inner_le _ _
  have h3 : ((‖x i - x j‖)⁻¹) ^ 2 ≤ (U / (m i * m j)) ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) hb 2
  have h4 : (m i * m j) * (((‖x i - x j‖)⁻¹) ^ 2 * ‖v i - v j‖)
      ≤ (m i * m j) * ((U / (m i * m j)) ^ 2 * ‖v i - v j‖) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 (norm_nonneg _)) hp.le
  have h5 : (m i * m j) * ((U / (m i * m j)) ^ 2 * ‖v i - v j‖)
      = U ^ 2 * ‖v i - v j‖ / (m i * m j) := by
    field_simp
  have habs : |m i * m j * ((‖x i - x j‖ ^ 3)⁻¹) * inner ℝ (x i - x j) (v i - v j)|
      = (m i * m j)
        * |((‖x i - x j‖ ^ 3)⁻¹) * inner ℝ (x i - x j) (v i - v j)| := by
    rw [mul_assoc, abs_mul, abs_of_nonneg hp.le]
  rw [habs]
  calc (m i * m j) * |((‖x i - x j‖ ^ 3)⁻¹) * inner ℝ (x i - x j) (v i - v j)|
      ≤ (m i * m j) * (((‖x i - x j‖)⁻¹) ^ 2 * ‖v i - v j‖) :=
        mul_le_mul_of_nonneg_left h2 hp.le
    _ ≤ (m i * m j) * ((U / (m i * m j)) ^ 2 * ‖v i - v j‖) := h4
    _ = U ^ 2 * ‖v i - v j‖ / (m i * m j) := h5

/-- Termwise bound for the interaction with the bodies outside `k`. -/
lemma abs_inner_pairJolt_le {x v q : EN E N} {ν : ℝ} (hν : 0 < ν)
    {i j : Fin N} (hij : ν ≤ ‖x i - x j‖) :
    |inner ℝ (q i) (pairJolt x v i j)| ≤ 4 * ‖q i‖ * ‖v i - v j‖ * (ν⁻¹) ^ 3 := by
  have hr : 0 < ‖x i - x j‖ := lt_of_lt_of_le hν hij
  have hinv : (‖x i - x j‖)⁻¹ ≤ ν⁻¹ := (inv_le_inv₀ hr hν).mpr hij
  have h3 : ((‖x i - x j‖)⁻¹) ^ 3 ≤ (ν⁻¹) ^ 3 :=
    pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) hinv 3
  set a := ((‖x i - x j‖)⁻¹) ^ 3 * ‖q i‖ * ‖v i - v j‖ with ha
  set A := ((‖x i - x j‖ ^ 3)⁻¹) * inner ℝ (q i) (v i - v j) with hAdef
  set B := (3 * ((‖x i - x j‖ ^ 5)⁻¹ * inner ℝ (x i - x j) (v i - v j)))
    * inner ℝ (q i) (x i - x j) with hBdef
  have hA : |A| ≤ a := by
    rw [hAdef, ha, abs_mul, abs_of_nonneg (by positivity), ← inv_pow]
    calc ((‖x i - x j‖)⁻¹) ^ 3 * |inner ℝ (q i) (v i - v j)|
        ≤ ((‖x i - x j‖)⁻¹) ^ 3 * (‖q i‖ * ‖v i - v j‖) :=
          mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by positivity)
      _ = ((‖x i - x j‖)⁻¹) ^ 3 * ‖q i‖ * ‖v i - v j‖ := by ring
  have hB : |B| ≤ 3 * a := by
    have h2 : |((‖x i - x j‖ ^ 5)⁻¹ * inner ℝ (x i - x j) (v i - v j))|
        ≤ ((‖x i - x j‖)⁻¹) ^ 5 * (‖x i - x j‖ * ‖v i - v j‖) := by
      rw [abs_mul, abs_of_nonneg (by positivity), ← inv_pow]
      exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by positivity)
    have h4 : |inner ℝ (q i) (x i - x j)| ≤ ‖q i‖ * ‖x i - x j‖ :=
      abs_real_inner_le_norm _ _
    rw [hBdef, ha, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3)]
    refine le_trans (mul_le_mul (mul_le_mul_of_nonneg_left h2 (by norm_num)) h4
      (abs_nonneg _) (by positivity)) (le_of_eq ?_)
    rw [show ((‖x i - x j‖)⁻¹) ^ 5 * (‖x i - x j‖ * ‖v i - v j‖)
        = ((‖x i - x j‖)⁻¹) ^ 4 * ‖v i - v j‖ by
      rw [show ((‖x i - x j‖)⁻¹)^5 = ((‖x i - x j‖)⁻¹)^4 * ((‖x i - x j‖)⁻¹) by ring,
        mul_assoc]
      congr 1
      rw [← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]]
    field_simp
  calc |inner ℝ (q i) (pairJolt x v i j)|
      = |A - B| := by
        rw [hAdef, hBdef, pairJolt, inner_sub_right, real_inner_smul_right,
          real_inner_smul_right]
    _ ≤ |A| + |B| := by
        have h := abs_sub_le A 0 B
        rwa [sub_zero, zero_sub, abs_neg] at h
    _ ≤ a + 3 * a := add_le_add hA hB
    _ = 4 * (((‖x i - x j‖)⁻¹) ^ 3 * ‖q i‖ * ‖v i - v j‖) := by
        rw [ha]; ring
    _ ≤ 4 * ((ν⁻¹) ^ 3 * ‖q i‖ * ‖v i - v j‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h3 (norm_nonneg _)) (norm_nonneg _)
    _ = 4 * ‖q i‖ * ‖v i - v j‖ * (ν⁻¹) ^ 3 := by ring

/-- Bound for the internal pair sum (the "jolt work"). -/
lemma abs_internal_pair_sum_le {m : Fin N → ℝ} {k : Finset (Fin N)} {x v : EN E N}
    {κ Cv M : ℝ} (hm : ∀ i, 0 < m i) (hκ : ∀ i, κ ≤ m i) (hκpos : 0 < κ)
    (hCv : 0 ≤ Cv) (hvel : ∀ j, ‖v j‖ ≤ Cv * Real.sqrt M) :
    |∑ i ∈ k, ∑ j ∈ k, m i * m j * ((‖x i - x j‖ ^ 3)⁻¹) * inner ℝ (x i - x j) (v i - v j)|
      ≤ (clusterPotential m k x) ^ 2
        * (2 * (k.card : ℝ) ^ 2 * (κ⁻¹) ^ 2 * Cv * Real.sqrt M) := by
  have hstep1 : |∑ i ∈ k, ∑ j ∈ k, m i * m j * ((‖x i - x j‖ ^ 3)⁻¹)
        * inner ℝ (x i - x j) (v i - v j)|
      ≤ ∑ i ∈ k, ∑ j ∈ k, (clusterPotential m k x) ^ 2 * ‖v i - v j‖ / (m i * m j) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun i hi => ?_
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun j hj => ?_
    by_cases hij : i = j
    · subst hij
      simp
    · exact abs_pair_term_le (mul_pos (hm i) (hm j))
        (inv_norm_sub_le_clusterPotential hm hi hj hij)
  have hstep2 : (∑ i ∈ k, ∑ j ∈ k, (clusterPotential m k x) ^ 2 * ‖v i - v j‖ / (m i * m j))
      ≤ ∑ i ∈ k, ∑ j ∈ k, (clusterPotential m k x) ^ 2
          * ((κ⁻¹) ^ 2 * ‖v i - v j‖) := by
    refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
    have hmij : 0 < m i * m j := mul_pos (hm i) (hm j)
    have hκ2 : κ ^ 2 ≤ m i * m j := by
      have h1 : κ * κ ≤ m i * m j := mul_le_mul (hκ i) (hκ j) hκpos.le (le_trans hκpos.le (hκ i))
      simpa [pow_two] using h1
    have hκ2pos : 0 < κ ^ 2 := by positivity
    have hinv : (m i * m j)⁻¹ ≤ (κ⁻¹) ^ 2 := by
      rw [inv_pow]
      exact (inv_le_inv₀ hmij hκ2pos).mpr hκ2
    have h5 : 0 ≤ (clusterPotential m k x) ^ 2 * ‖v i - v j‖ := by
      have := clusterPotential_nonneg (fun i => (hm i).le) k x
      positivity
    calc (clusterPotential m k x) ^ 2 * ‖v i - v j‖ / (m i * m j)
        = (clusterPotential m k x) ^ 2 * ‖v i - v j‖ * (m i * m j)⁻¹ := by ring
      _ ≤ (clusterPotential m k x) ^ 2 * ‖v i - v j‖ * (κ⁻¹) ^ 2 :=
          mul_le_mul_of_nonneg_left hinv h5
      _ = (clusterPotential m k x) ^ 2 * ((κ⁻¹) ^ 2 * ‖v i - v j‖) := by ring
  have hstep3 : (∑ i ∈ k, ∑ j ∈ k, (clusterPotential m k x) ^ 2
        * ((κ⁻¹) ^ 2 * ‖v i - v j‖))
      ≤ ∑ i ∈ k, ∑ j ∈ k, (clusterPotential m k x) ^ 2
          * ((κ⁻¹) ^ 2 * (2 * (Cv * Real.sqrt M))) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have h2c : 0 ≤ 2 * (Cv * Real.sqrt M) := by positivity
    have hvv : ‖v i - v j‖ ≤ 2 * (Cv * Real.sqrt M) := by
      calc ‖v i - v j‖ ≤ ‖v i‖ + ‖v j‖ := norm_sub_le _ _
        _ ≤ Cv * Real.sqrt M + Cv * Real.sqrt M := add_le_add (hvel i) (hvel j)
        _ = 2 * (Cv * Real.sqrt M) := by ring
    have hU2 : 0 ≤ (clusterPotential m k x) ^ 2 := by
      have := clusterPotential_nonneg (fun i => (hm i).le) k x
      positivity
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hvv (by positivity)) hU2
  calc |∑ i ∈ k, ∑ j ∈ k, m i * m j * ((‖x i - x j‖ ^ 3)⁻¹)
        * inner ℝ (x i - x j) (v i - v j)|
      ≤ ∑ i ∈ k, ∑ j ∈ k, (clusterPotential m k x) ^ 2 * ‖v i - v j‖ / (m i * m j) := hstep1
    _ ≤ ∑ i ∈ k, ∑ j ∈ k, (clusterPotential m k x) ^ 2 * ((κ⁻¹) ^ 2 * ‖v i - v j‖) := hstep2
    _ ≤ ∑ i ∈ k, ∑ j ∈ k, (clusterPotential m k x) ^ 2
          * ((κ⁻¹) ^ 2 * (2 * (Cv * Real.sqrt M))) := hstep3
    _ = (clusterPotential m k x) ^ 2
          * (2 * (k.card : ℝ) ^ 2 * (κ⁻¹) ^ 2 * Cv * Real.sqrt M) := by
        rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
        ring

/-- Bound for the interaction sum with the bodies outside `k`. -/
lemma abs_external_pair_sum_le {m : Fin N → ℝ} {k : Finset (Fin N)} {x v : EN E N}
    {Cv M ν : ℝ} (hm : ∀ i, 0 < m i) (hCv : 0 ≤ Cv)
    (hvel : ∀ j, ‖v j‖ ≤ Cv * Real.sqrt M) (hν : 0 < ν)
    (hsep : ClusterSeparatedWeak k x ν) :
    |∑ i ∈ k, ∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k),
        m i * m j * inner ℝ ((cmRel m k x) i) (pairJolt x v i j)|
      ≤ 4 * (ν⁻¹) ^ 3 * (∑ i ∈ k, m i * ‖(cmRel m k x) i‖)
          * (∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m j)
          * (2 * (Cv * Real.sqrt M)) := by
  set c : ℝ := 4 * (ν⁻¹) ^ 3 * (2 * (Cv * Real.sqrt M)) with hc
  have hcpos : 0 ≤ c := by rw [hc]; positivity
  have hT : ∀ i : Fin N, (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k)
      ⊆ Finset.univ.filter (fun j : Fin N => j ∉ k) := by
    intro i j hj
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and] at hj ⊢
    exact hj.2
  have hstep1 : |∑ i ∈ k, ∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k),
        m i * m j * inner ℝ ((cmRel m k x) i) (pairJolt x v i j)|
      ≤ ∑ i ∈ k, ∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k),
          4 * (ν⁻¹) ^ 3 * ‖(cmRel m k x) i‖ * ‖v i - v j‖ * (m i * m j) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun i hi => ?_
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun j hj => ?_
    obtain ⟨hji, hjk⟩ := Finset.mem_filter.mp hj
    have hij : ν ≤ ‖x i - x j‖ := by
      have h := hsep i hi j hjk
      rwa [r_eq_norm_sub] at h
    have h1 : |inner ℝ ((cmRel m k x) i) (pairJolt x v i j)|
        ≤ 4 * ‖(cmRel m k x) i‖ * ‖v i - v j‖ * (ν⁻¹) ^ 3 :=
      abs_inner_pairJolt_le hν hij
    have hp : 0 ≤ m i * m j := mul_nonneg (hm i).le (hm j).le
    rw [abs_mul, abs_of_nonneg hp]
    calc (m i * m j) * |inner ℝ ((cmRel m k x) i) (pairJolt x v i j)|
        ≤ (m i * m j) * (4 * ‖(cmRel m k x) i‖ * ‖v i - v j‖ * (ν⁻¹) ^ 3) :=
          mul_le_mul_of_nonneg_left h1 hp
      _ = 4 * (ν⁻¹) ^ 3 * ‖(cmRel m k x) i‖ * ‖v i - v j‖ * (m i * m j) := by ring
  have hstep2 : (∑ i ∈ k, ∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k),
          4 * (ν⁻¹) ^ 3 * ‖(cmRel m k x) i‖ * ‖v i - v j‖ * (m i * m j))
      ≤ ∑ i ∈ k, ∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k),
          (m i * ‖(cmRel m k x) i‖) * (m j * c) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have hv : ‖v i - v j‖ ≤ 2 * (Cv * Real.sqrt M) := by
      calc ‖v i - v j‖ ≤ ‖v i‖ + ‖v j‖ := norm_sub_le _ _
        _ ≤ Cv * Real.sqrt M + Cv * Real.sqrt M := add_le_add (hvel i) (hvel j)
        _ = 2 * (Cv * Real.sqrt M) := by ring
    have hq : 0 ≤ ‖(cmRel m k x) i‖ := norm_nonneg _
    have hc' : 0 ≤ 4 * (ν⁻¹) ^ 3 := by positivity
    have hp : 0 ≤ m i * m j := mul_nonneg (hm i).le (hm j).le
    rw [hc]
    have hmain : 4 * (ν⁻¹) ^ 3 * ‖(cmRel m k x) i‖ * ‖v i - v j‖ * (m i * m j)
        ≤ 4 * (ν⁻¹) ^ 3 * ‖(cmRel m k x) i‖ * (2 * (Cv * Real.sqrt M)) * (m i * m j) := by
      have hpos : 0 ≤ 4 * (ν⁻¹) ^ 3 * ‖(cmRel m k x) i‖ * (m i * m j) := by positivity
      calc 4 * (ν⁻¹) ^ 3 * ‖(cmRel m k x) i‖ * ‖v i - v j‖ * (m i * m j)
          = (4 * (ν⁻¹) ^ 3 * ‖(cmRel m k x) i‖ * (m i * m j)) * ‖v i - v j‖ := by ring
        _ ≤ (4 * (ν⁻¹) ^ 3 * ‖(cmRel m k x) i‖ * (m i * m j)) * (2 * (Cv * Real.sqrt M)) :=
            mul_le_mul_of_nonneg_left hv hpos
        _ = 4 * (ν⁻¹) ^ 3 * ‖(cmRel m k x) i‖ * (2 * (Cv * Real.sqrt M)) * (m i * m j) := by ring
    calc 4 * (ν⁻¹) ^ 3 * ‖(cmRel m k x) i‖ * ‖v i - v j‖ * (m i * m j)
        ≤ 4 * (ν⁻¹) ^ 3 * ‖(cmRel m k x) i‖ * (2 * (Cv * Real.sqrt M)) * (m i * m j) := hmain
      _ = (m i * ‖(cmRel m k x) i‖) * (m j * (4 * (ν⁻¹) ^ 3 * (2 * (Cv * Real.sqrt M)))) := by
          ring
  have hstep3 : (∑ i ∈ k, ∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k),
          (m i * ‖(cmRel m k x) i‖) * (m j * c))
      ≤ (∑ i ∈ k, m i * ‖(cmRel m k x) i‖)
          * (∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m j) * c := by
    have h1 : ∀ i ∈ k, (∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k),
          (m i * ‖(cmRel m k x) i‖) * (m j * c))
        ≤ (m i * ‖(cmRel m k x) i‖)
            * ((∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m j) * c) := by
      intro i _
      rw [← Finset.mul_sum, ← Finset.sum_mul]
      have hsub : (∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k), m j)
          ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m j :=
        Finset.sum_le_sum_of_subset_of_nonneg (hT i) (fun j _ _ => (hm j).le)
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsub hcpos)
        (mul_nonneg (hm i).le (norm_nonneg _))
    calc (∑ i ∈ k, ∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k),
          (m i * ‖(cmRel m k x) i‖) * (m j * c))
        ≤ ∑ i ∈ k, (m i * ‖(cmRel m k x) i‖)
            * ((∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m j) * c) :=
          Finset.sum_le_sum h1
      _ = (∑ i ∈ k, m i * ‖(cmRel m k x) i‖)
            * (∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m j) * c := by
          rw [← Finset.sum_mul]
          ring
  calc |∑ i ∈ k, ∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k),
        m i * m j * inner ℝ ((cmRel m k x) i) (pairJolt x v i j)|
      ≤ ∑ i ∈ k, ∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k),
          4 * (ν⁻¹) ^ 3 * ‖(cmRel m k x) i‖ * ‖v i - v j‖ * (m i * m j) := hstep1
    _ ≤ ∑ i ∈ k, ∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin N => j ∉ k),
          (m i * ‖(cmRel m k x) i‖) * (m j * c) := hstep2
    _ ≤ (∑ i ∈ k, m i * ‖(cmRel m k x) i‖)
          * (∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m j) * c := hstep3
    _ = 4 * (ν⁻¹) ^ 3 * (∑ i ∈ k, m i * ‖(cmRel m k x) i‖)
          * (∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m j)
          * (2 * (Cv * Real.sqrt M)) := by
        rw [hc]; ring

lemma abs_sub_le_abs_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  simpa using abs_sub_le a 0 b

/-- Cauchy–Schwarz for the mass-weighted lengths of a configuration. -/
lemma sum_mass_norm_le_sqrt {m : Fin N → ℝ} {k : Finset (Fin N)} {v : EN E N}
    (hm : ∀ i, 0 ≤ m i) :
    (∑ i ∈ k, m i * ‖v i‖)
      ≤ Real.sqrt (clusterMass m k * clusterKineticSq m k v) := by
  have h1 : (∑ i ∈ k, m i * ‖v i‖) ^ 2
      ≤ (∑ i ∈ k, m i) * (∑ i ∈ k, m i * ‖v i‖ ^ 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq k (fun i => Real.sqrt (m i))
      (fun i => Real.sqrt (m i) * ‖v i‖)
    have h2 : ∀ i ∈ k, Real.sqrt (m i) * (Real.sqrt (m i) * ‖v i‖)
        = m i * ‖v i‖ := by
      intro i _
      rw [← mul_assoc, Real.mul_self_sqrt (hm i)]
    have h3 : ∀ i ∈ k, (Real.sqrt (m i)) ^ 2 = m i :=
      fun i _ => Real.sq_sqrt (hm i)
    have h4 : ∀ i ∈ k, (Real.sqrt (m i) * ‖v i‖) ^ 2 = m i * ‖v i‖ ^ 2 := by
      intro i _
      rw [mul_pow, Real.sq_sqrt (hm i)]
    rw [Finset.sum_congr rfl h2, Finset.sum_congr rfl h3,
      Finset.sum_congr rfl h4] at h
    exact h
  have hnn : 0 ≤ ∑ i ∈ k, m i * ‖v i‖ :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hm i) (norm_nonneg _)
  rw [← Real.sqrt_sq hnn, clusterMass, clusterKineticSq]
  exact Real.sqrt_le_sqrt h1

/-- **The third derivative of the moment of inertia of a colliding cluster is bounded by
`Φ^{5/2}`.** -/
theorem abs_third_deriv_clusterInertia_le {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {ε t Φ A C Cv M κ ν : ℝ}
    (hm : ∀ i, 0 < m i) (hκ : ∀ i, κ ≤ m i) (hκpos : 0 < κ) (hk : k.Nonempty)
    (htm : t ∈ Ioo (0:ℝ) ε)
    (hx : ∀ s ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x s) s)
    (hd2 : ∀ s ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (deriv (deriv x) s) s)
    (hd3 : ∀ s ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv (deriv x)) (deriv (deriv (deriv x)) s) s)
    (hode : ∀ s ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x s = ∇_[m] (U m) (x s))
    (hnc : ∀ s ∈ Ioo (0:ℝ) ε, WithoutCollisions (x s))
    (hΦ : 1 ≤ Φ) (hA : 0 ≤ A) (hC : 0 ≤ C) (hCv : 0 ≤ Cv) (hν : 0 < ν)
    (hsep : ClusterSeparatedWeak k (x t) ν)
    (hacc : ∀ i ∈ k, ‖(cmRel m k (deriv (deriv x) t)) i‖ ≤ A * Φ ^ 2)
    (hvel : ∀ j, ‖deriv x t j‖ ≤ Cv * Real.sqrt M)
    (hR : clusterKineticSq m k (cmRel m k (deriv x t)) ≤ M)
    (hM0 : 0 ≤ M) (hMΦ : M ≤ Φ)
    (hU : clusterPotential m k (x t) ≤ Φ)
    (hI : clusterInertia m k (x t) ≤ C) :
    |deriv (deriv (deriv (fun s : ℝ => clusterInertia m k (x s)))) t|
      ≤ (6 * A * Real.sqrt (clusterMass m k)
          + 2 * (2 * (k.card : ℝ) ^ 2 * (κ⁻¹) ^ 2 * Cv
            + 4 * (ν⁻¹) ^ 3 * Real.sqrt (clusterMass m k * C) * (∑ j : Fin N, m j) * (2 * Cv))
          + 2) * (Φ ^ 2 * Real.sqrt Φ) := by
  classical
  have hΦ0 : 0 ≤ Φ := le_trans zero_le_one hΦ
  have hsΦ0 : 0 ≤ Real.sqrt Φ := Real.sqrt_nonneg _
  have hsΦ1 : 1 ≤ Real.sqrt Φ := Real.one_le_sqrt.mpr hΦ
  have hss : Real.sqrt M ≤ Real.sqrt Φ := Real.sqrt_le_sqrt hMΦ
  have hmk0 : 0 ≤ clusterMass m k := clusterMass_nonneg (fun i => (hm i).le) k
  have hmk : clusterMass m k ≠ 0 := ne_of_gt (clusterMass_pos hm hk)
  have hU0 : 0 ≤ clusterPotential m k (x t) := clusterPotential_nonneg (fun i => (hm i).le) k (x t)
  set A1 := massInner m (cmRel m k (deriv x t)) (cmRel m k (deriv (deriv x) t)) with hA1
  set A2 := massInner m (cmRel m k (x t)) (cmRel m k (deriv (deriv (deriv x)) t)) with hA2
  have hid : deriv (deriv (deriv (fun s : ℝ => clusterInertia m k (x s)))) t
      = 6 * A1 + 2 * A2 := by
    rw [hA1, hA2]
    exact deriv_deriv_deriv_clusterInertia_eq (m := m) (k := k) (x := x) (ε := ε) (t := t)
      htm hx hd2 hd3
  -- Bound the first term
  have hb1 : |A1| ≤ A * Φ ^ 2 * (Real.sqrt (clusterMass m k) * Real.sqrt Φ) := by
    rw [hA1, massInner]
    have hterm : ∀ i : Fin N, |m i * inner ℝ ((cmRel m k (deriv x t)) i)
          ((cmRel m k (deriv (deriv x) t)) i)|
        ≤ m i * (‖(cmRel m k (deriv x t)) i‖ * (A * Φ ^ 2)) := by
      intro i
      have h1 : |inner ℝ ((cmRel m k (deriv x t)) i) ((cmRel m k (deriv (deriv x) t)) i)|
          ≤ ‖(cmRel m k (deriv x t)) i‖ * (A * Φ ^ 2) := by
        by_cases hi : i ∈ k
        · calc |inner ℝ ((cmRel m k (deriv x t)) i) ((cmRel m k (deriv (deriv x) t)) i)|
              ≤ ‖(cmRel m k (deriv x t)) i‖ * ‖(cmRel m k (deriv (deriv x) t)) i‖ :=
                abs_real_inner_le_norm _ _
            _ ≤ ‖(cmRel m k (deriv x t)) i‖ * (A * Φ ^ 2) :=
                mul_le_mul_of_nonneg_left (hacc i hi) (norm_nonneg _)
        · simp [cmRel_apply, hi]
      calc |m i * inner ℝ ((cmRel m k (deriv x t)) i)
            ((cmRel m k (deriv (deriv x) t)) i)|
          = m i * |inner ℝ ((cmRel m k (deriv x t)) i)
              ((cmRel m k (deriv (deriv x) t)) i)| := by
            rw [abs_mul, abs_of_nonneg (hm i).le]
        _ ≤ m i * (‖(cmRel m k (deriv x t)) i‖ * (A * Φ ^ 2)) :=
            mul_le_mul_of_nonneg_left h1 (hm i).le
    have hterm2 : ∀ i : Fin N, m i * (‖(cmRel m k (deriv x t)) i‖ * (A * Φ ^ 2))
        = A * Φ ^ 2 * (m i * ‖(cmRel m k (deriv x t)) i‖) := fun i => by ring
    calc |∑ i, m i * inner ℝ ((cmRel m k (deriv x t)) i)
          ((cmRel m k (deriv (deriv x) t)) i)|
        ≤ ∑ i, m i * (‖(cmRel m k (deriv x t)) i‖ * (A * Φ ^ 2)) := by
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
          exact Finset.sum_le_sum fun i _ => hterm i
      _ = A * Φ ^ 2 * (∑ i, m i * ‖(cmRel m k (deriv x t)) i‖) := by
          rw [Finset.sum_congr rfl (fun i _ => hterm2 i), Finset.mul_sum]
      _ = A * Φ ^ 2 * (∑ i ∈ k, m i * ‖(cmRel m k (deriv x t)) i‖) := by
          congr 1
          exact (Finset.sum_subset (Finset.subset_univ k) (fun i _ hi => by
            rw [cmRel_apply_of_notMem (by simpa using hi)]; simp)).symm
      _ ≤ A * Φ ^ 2
            * Real.sqrt (clusterMass m k * clusterKineticSq m k (cmRel m k (deriv x t))) := by
          refine mul_le_mul_of_nonneg_left (sum_mass_norm_le_sqrt (fun i => (hm i).le))
            (by positivity)
      _ ≤ A * Φ ^ 2 * (Real.sqrt (clusterMass m k) * Real.sqrt Φ) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [Real.sqrt_mul hmk0]
          exact mul_le_mul_of_nonneg_left (le_trans (Real.sqrt_le_sqrt hR) hss)
            (Real.sqrt_nonneg _)
  -- The two sums
  have hthird := massInner_cmRel_third_eq (m := m) (k := k) (x := x) (ε := ε) (t := t)
    htm hx (hd3 t htm) hode hnc (fun i => ne_of_gt (hm i)) hmk
  have hQ := abs_internal_pair_sum_le (m := m) (k := k) (x := x t) (v := deriv x t)
    hm hκ hκpos hCv hvel
  have hE := abs_external_pair_sum_le (m := m) (k := k) (x := x t) (v := deriv x t)
    hm hCv hvel hν hsep
  have hCS2 : (∑ i ∈ k, m i * ‖(cmRel m k (x t)) i‖) ≤ Real.sqrt (clusterMass m k * C) := by
    refine le_trans (sum_mass_norm_le_sqrt (m := m) (k := k)
      (v := cmRel m k (x t)) (fun i => (hm i).le)) ?_
    rw [show clusterKineticSq m k (cmRel m k (x t))
        = massInner m (cmRel m k (x t)) (cmRel m k (x t)) from
      clusterKineticSq_eq_massInner m k (x t),
      ← clusterInertia_eq_massInner]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hI hmk0)
  have hsumj : (∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m j)
      ≤ ∑ j : Fin N, m j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j _ _ => (hm j).le)
  -- assemble
  have hcoef1 : 0 ≤ 2 * (k.card : ℝ) ^ 2 * (κ⁻¹) ^ 2 * Cv := by positivity
  have hcoef2 : 0 ≤ 4 * (ν⁻¹) ^ 3 * Real.sqrt (clusterMass m k * C) * (∑ j : Fin N, m j)
      * (2 * Cv) := by
    have h1 : (0:ℝ) ≤ 4 := by norm_num
    have h2 : (0:ℝ) ≤ (ν⁻¹) ^ 3 := by positivity
    have h3 : (0:ℝ) ≤ Real.sqrt (clusterMass m k * C) := Real.sqrt_nonneg _
    have h4 : (0:ℝ) ≤ ∑ j : Fin N, m j := Finset.sum_nonneg fun j _ => (hm j).le
    have h5 : (0:ℝ) ≤ 2 * Cv := by linarith
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4) h5
  have hA2b : |A2| ≤ (clusterPotential m k (x t)) ^ 2
        * (2 * (k.card : ℝ) ^ 2 * (κ⁻¹) ^ 2 * Cv * Real.sqrt M)
      + 4 * (ν⁻¹) ^ 3 * Real.sqrt (clusterMass m k * C) * (∑ j : Fin N, m j)
          * (2 * (Cv * Real.sqrt M)) := by
    rw [hA2, hthird]
    refine le_trans (abs_sub_le_abs_add _ _) ?_
    refine add_le_add hQ ?_
    refine le_trans hE ?_
    have h1 : Real.sqrt (clusterMass m k * C)
          * (∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m j)
        ≤ Real.sqrt (clusterMass m k * C) * (∑ j : Fin N, m j) :=
      mul_le_mul_of_nonneg_left hsumj (Real.sqrt_nonneg _)
    have hsm : 0 ≤ ∑ j : Fin N, m j := Finset.sum_nonneg fun j _ => (hm j).le
    have h4 : 0 ≤ 4 * (ν⁻¹) ^ 3 := by positivity
    have h5 : 0 ≤ 2 * (Cv * Real.sqrt M) := by positivity
    calc 4 * (ν⁻¹) ^ 3 * (∑ i ∈ k, m i * ‖(cmRel m k (x t)) i‖)
          * (∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m j) * (2 * (Cv * Real.sqrt M))
        = (4 * (ν⁻¹) ^ 3 * (2 * (Cv * Real.sqrt M)))
            * ((∑ i ∈ k, m i * ‖(cmRel m k (x t)) i‖)
              * (∑ j ∈ Finset.univ.filter (fun j : Fin N => j ∉ k), m j)) := by ring
      _ ≤ (4 * (ν⁻¹) ^ 3 * (2 * (Cv * Real.sqrt M)))
            * (Real.sqrt (clusterMass m k * C) * (∑ j : Fin N, m j)) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg h4 h5)
          exact mul_le_mul hCS2 hsumj (Finset.sum_nonneg fun j _ => (hm j).le)
            (Real.sqrt_nonneg _)
      _ = 4 * (ν⁻¹) ^ 3 * Real.sqrt (clusterMass m k * C) * (∑ j : Fin N, m j)
            * (2 * (Cv * Real.sqrt M)) := by ring
  have hmain : |deriv (deriv (deriv (fun s : ℝ => clusterInertia m k (x s)))) t|
      ≤ 6 * (A * Φ ^ 2 * (Real.sqrt (clusterMass m k) * Real.sqrt Φ))
        + 2 * ((clusterPotential m k (x t)) ^ 2
            * (2 * (k.card : ℝ) ^ 2 * (κ⁻¹) ^ 2 * Cv * Real.sqrt M)
          + 4 * (ν⁻¹) ^ 3 * Real.sqrt (clusterMass m k * C) * (∑ j : Fin N, m j)
              * (2 * (Cv * Real.sqrt M))) := by
    rw [hid]
    refine le_trans (abs_add_le _ _) ?_
    refine add_le_add ?_ ?_
    · calc |6 * A1| = 6 * |A1| := by rw [abs_mul, abs_of_nonneg (by norm_num)]
        _ ≤ 6 * (A * Φ ^ 2 * (Real.sqrt (clusterMass m k) * Real.sqrt Φ)) :=
            mul_le_mul_of_nonneg_left hb1 (by norm_num)
    · calc |2 * A2| = 2 * |A2| := by rw [abs_mul, abs_of_nonneg (by norm_num)]
        _ ≤ 2 * ((clusterPotential m k (x t)) ^ 2
              * (2 * (k.card : ℝ) ^ 2 * (κ⁻¹) ^ 2 * Cv * Real.sqrt M)
            + 4 * (ν⁻¹) ^ 3 * Real.sqrt (clusterMass m k * C) * (∑ j : Fin N, m j)
                * (2 * (Cv * Real.sqrt M))) :=
            mul_le_mul_of_nonneg_left hA2b (by norm_num)
  refine le_trans hmain ?_
  have hsqM : Real.sqrt M ^ 2 = M := Real.sq_sqrt hM0
  have hsqΦ : Real.sqrt Φ ^ 2 = Φ := Real.sq_sqrt hΦ0
  have hU2 : (clusterPotential m k (x t)) ^ 2 ≤ Φ ^ 2 := by nlinarith [hU, hU0, hΦ0]
  have hsM2 : Real.sqrt M ≤ Φ ^ 2 * Real.sqrt Φ := by
    have h1 : Real.sqrt Φ ≤ Φ ^ 2 * Real.sqrt Φ := by nlinarith [hsΦ0, hsΦ1, hsqΦ]
    exact le_trans hss h1
  have hP1 : (clusterPotential m k (x t)) ^ 2
        * (2 * (k.card : ℝ) ^ 2 * (κ⁻¹) ^ 2 * Cv * Real.sqrt M)
      ≤ (2 * (k.card : ℝ) ^ 2 * (κ⁻¹) ^ 2 * Cv) * (Φ ^ 2 * Real.sqrt Φ) := by
    have h2 : (clusterPotential m k (x t)) ^ 2 * Real.sqrt M ≤ Φ ^ 2 * Real.sqrt Φ :=
      mul_le_mul hU2 hss (Real.sqrt_nonneg _) (by positivity)
    calc (clusterPotential m k (x t)) ^ 2
          * (2 * (k.card : ℝ) ^ 2 * (κ⁻¹) ^ 2 * Cv * Real.sqrt M)
        = (2 * (k.card : ℝ) ^ 2 * (κ⁻¹) ^ 2 * Cv)
            * ((clusterPotential m k (x t)) ^ 2 * Real.sqrt M) := by ring
      _ ≤ (2 * (k.card : ℝ) ^ 2 * (κ⁻¹) ^ 2 * Cv) * (Φ ^ 2 * Real.sqrt Φ) :=
          mul_le_mul_of_nonneg_left h2 hcoef1
  have hP2 : 4 * (ν⁻¹) ^ 3 * Real.sqrt (clusterMass m k * C) * (∑ j : Fin N, m j)
        * (2 * (Cv * Real.sqrt M))
      ≤ (4 * (ν⁻¹) ^ 3 * Real.sqrt (clusterMass m k * C) * (∑ j : Fin N, m j) * (2 * Cv))
          * (Φ ^ 2 * Real.sqrt Φ) := by
    calc 4 * (ν⁻¹) ^ 3 * Real.sqrt (clusterMass m k * C) * (∑ j : Fin N, m j)
          * (2 * (Cv * Real.sqrt M))
        = (4 * (ν⁻¹) ^ 3 * Real.sqrt (clusterMass m k * C) * (∑ j : Fin N, m j) * (2 * Cv))
            * Real.sqrt M := by ring
      _ ≤ (4 * (ν⁻¹) ^ 3 * Real.sqrt (clusterMass m k * C) * (∑ j : Fin N, m j) * (2 * Cv))
            * (Φ ^ 2 * Real.sqrt Φ) :=
          mul_le_mul_of_nonneg_left hsM2 hcoef2
  have hfinal : 6 * (A * Φ ^ 2 * (Real.sqrt (clusterMass m k) * Real.sqrt Φ))
        + 2 * ((clusterPotential m k (x t)) ^ 2
            * (2 * (k.card : ℝ) ^ 2 * (κ⁻¹) ^ 2 * Cv * Real.sqrt M)
          + 4 * (ν⁻¹) ^ 3 * Real.sqrt (clusterMass m k * C) * (∑ j : Fin N, m j)
              * (2 * (Cv * Real.sqrt M)))
      ≤ ((6 * A * Real.sqrt (clusterMass m k)
          + 2 * (2 * (k.card : ℝ) ^ 2 * (κ⁻¹) ^ 2 * Cv
            + 4 * (ν⁻¹) ^ 3 * Real.sqrt (clusterMass m k * C) * (∑ j : Fin N, m j) * (2 * Cv))
          + 2) * (Φ ^ 2 * Real.sqrt Φ)) := by
    have h1 : (clusterPotential m k (x t)) ^ 2
          * (2 * (k.card : ℝ) ^ 2 * (κ⁻¹) ^ 2 * Cv * Real.sqrt M)
        + 4 * (ν⁻¹) ^ 3 * Real.sqrt (clusterMass m k * C) * (∑ j : Fin N, m j)
            * (2 * (Cv * Real.sqrt M))
        ≤ (2 * (k.card : ℝ) ^ 2 * (κ⁻¹) ^ 2 * Cv
            + 4 * (ν⁻¹) ^ 3 * Real.sqrt (clusterMass m k * C) * (∑ j : Fin N, m j) * (2 * Cv))
          * (Φ ^ 2 * Real.sqrt Φ) := by
      rw [add_mul]
      exact add_le_add hP1 hP2
    have h2 : 6 * (A * Φ ^ 2 * (Real.sqrt (clusterMass m k) * Real.sqrt Φ))
        = (6 * A * Real.sqrt (clusterMass m k)) * (Φ ^ 2 * Real.sqrt Φ) := by ring
    have hsqn : 0 ≤ Φ ^ 2 * Real.sqrt Φ := by positivity
    rw [h2]
    nlinarith [mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 2), hsqn]
  exact hfinal

/-- **The `HasDerivAt` form of the third derivative.**  The second derivative of the moment of
inertia along the curve is differentiable, with derivative the third derivative. -/
lemma hasDerivAt_deriv_deriv_clusterInertia_curve {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε t : ℝ} (ht : t ∈ Ioo (0:ℝ) ε)
    (hx : ∀ s ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x s) s)
    (hd2 : ∀ s ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (deriv (deriv x) s) s)
    (hd3 : ∀ s ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv (deriv x)) (deriv (deriv (deriv x)) s) s) :
    HasDerivAt (deriv (deriv (fun s : ℝ => clusterInertia m k (x s))))
      (deriv (deriv (deriv (fun s : ℝ => clusterInertia m k (x s)))) t) t := by
  set G2 : ℝ → ℝ := fun s => 2 * massInner m (cmRel m k (x s)) (cmRel m k (deriv x s))
    with hG2def
  set G3 : ℝ → ℝ := fun s => 2 * massInner m (cmRel m k (deriv x s)) (cmRel m k (deriv x s))
      + 2 * massInner m (cmRel m k (x s)) (cmRel m k (deriv (deriv x) s)) with hG3def
  have hG2eq : G2 = fun u => 2 * massInner m (cmRel m k (x u)) (cmRel m k (deriv x u)) := by
    funext u; rw [hG2def]
  have hG3eq : G3 = fun u => 2 * massInner m (cmRel m k (deriv x u)) (cmRel m k (deriv x u))
      + 2 * massInner m (cmRel m k (x u)) (cmRel m k (deriv (deriv x) u)) := by
    funext u; rw [hG3def]
  have hder1 : deriv (fun s : ℝ => clusterInertia m k (x s)) =ᶠ[𝓝 t] G2 := by
    have h := deriv_clusterInertia_eq m k
      (Filter.eventually_iff_exists_mem.mpr
        ⟨Set.Ioo (0:ℝ) ε, isOpen_Ioo.mem_nhds ht, fun s hs => hx s hs⟩)
    filter_upwards [h] with s hs
    rw [hG2def]
    exact hs
  have hder2 : deriv G2 =ᶠ[𝓝 t] G3 := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    have hpair := (hasDerivAt_inertia_pair m k (hx s hs) (hd2 s hs)).const_mul 2
    rw [hG2eq, hpair.deriv, hG3def]
    ring
  have hderiv2 : deriv (deriv (fun s : ℝ => clusterInertia m k (x s))) =ᶠ[𝓝 t] G3 :=
    (Filter.EventuallyEq.deriv hder1).trans hder2
  have hG3 : HasDerivAt G3
      (6 * massInner m (cmRel m k (deriv x t)) (cmRel m k (deriv (deriv x) t))
        + 2 * massInner m (cmRel m k (x t)) (cmRel m k (deriv (deriv (deriv x)) t))) t := by
    have h1 : HasDerivAt (fun s => massInner m (cmRel m k (deriv x s))
          (cmRel m k (deriv x s)))
        (massInner m (cmRel m k (deriv (deriv x) t)) (cmRel m k (deriv x t))
          + massInner m (cmRel m k (deriv x t)) (cmRel m k (deriv (deriv x) t))) t :=
      hasDerivAt_inertia_pair m k (hd2 t ht) (hd2 t ht)
    have h2 : HasDerivAt (fun s => massInner m (cmRel m k (x s))
          (cmRel m k (deriv (deriv x) s)))
        (massInner m (cmRel m k (deriv x t)) (cmRel m k (deriv (deriv x) t))
          + massInner m (cmRel m k (x t)) (cmRel m k (deriv (deriv (deriv x)) t))) t :=
      hasDerivAt_inertia_pair m k (hx t ht) (hd3 t ht)
    have h := (h1.const_mul 2).add (h2.const_mul 2)
    rw [hG3eq]
    refine h.congr_deriv ?_
    rw [massInner_comm m (cmRel m k (deriv (deriv x) t)) (cmRel m k (deriv x t))]
    ring
  have hval : deriv (deriv (deriv (fun s : ℝ => clusterInertia m k (x s)))) t
      = 6 * massInner m (cmRel m k (deriv x t)) (cmRel m k (deriv (deriv x) t))
        + 2 * massInner m (cmRel m k (x t)) (cmRel m k (deriv (deriv (deriv x)) t)) :=
    deriv_deriv_deriv_clusterInertia_eq ht hx hd2 hd3
  have := hG3.congr_of_eventuallyEq hderiv2
  rwa [hval]

end Submission.NBody
