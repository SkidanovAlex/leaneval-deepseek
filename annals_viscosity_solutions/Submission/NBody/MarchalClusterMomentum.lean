import Submission.NBody.EnergyAe
import Submission.NBody.MarchalClusterAccel
import Submission.NBody.FirstVariation
import Submission.NBody.MarchalBumpRest
import Submission.NBody.MarchalBumpF5
import Submission.NBody.MarchalCollisionSolutionData
import Submission.Commons.Analysis.Calculus.ae_eq_add_intervalIntegral_of_forall_integral_inner_deriv_add_eq_zero_smooth
import Submission.Commons.Analysis.Calculus.inv_norm_add_taylor
import Submission.Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_ae_differentiableAt_vector
import Submission.Commons.MeasureTheory.Integral.intervalIntegrable_deriv_of_absolutelyContinuousOnInterval
import Submission.Commons.MeasureTheory.Integral.intervalIntegral_eq_integral_of_tsupport_subset

/-!
# The rigid-translation variation of a cluster, and the boundedness of its momentum

Ferrario--Terracini's `propo:gen_sol` shows that a minimiser of the action has the "generalized
solution" property: the quantities attached to a cluster which does not collide with its complement
are absolutely continuous.  The essential analytic input is a *variational* identity obtained by
translating the cluster as a rigid body.

This module proves that identity: for a cluster `k` which does not collide with its complement on
`[a,b]`, and every `ψ ∈ C¹_c((a,b))` and every `w`,

  `∫ ψ' ⟪p_k, w⟫ + ∫ ψ ⟪F_k, w⟫ = 0`,

where `p_k = ∑_{i∈k} mᵢ γ̇ᵢ` is the momentum of the cluster and `F_k` its external force.  The key
point is that a rigid translation leaves the *internal* separations of `k` unchanged, so the
internal potential contributes **nothing**; only the (well separated, hence `C²`) cross terms do.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-! ## 1. The rigid translation of a cluster, and the external force -/

/-- The vector which equals `w` on the indices of `k` and `0` outside. -/
noncomputable def clusterTransVec (k : Finset (Fin N)) (w : E) : EN E N :=
  WithLp.toLp 2 fun i => if i ∈ k then w else 0

@[simp] lemma clusterTransVec_ofLp (k : Finset (Fin N)) (w : E) :
    (clusterTransVec k w).ofLp = fun i => if i ∈ k then w else 0 :=
  WithLp.ofLp_toLp 2 _

lemma clusterTransVec_apply_of_mem {k : Finset (Fin N)} {w : E} {i : Fin N} (hi : i ∈ k) :
    clusterTransVec k w i = w := by
  rw [show clusterTransVec k w i = (clusterTransVec k w).ofLp i from rfl, clusterTransVec_ofLp]
  simp [hi]

lemma clusterTransVec_apply_of_notMem {k : Finset (Fin N)} {w : E} {i : Fin N} (hi : i ∉ k) :
    clusterTransVec k w i = 0 := by
  rw [show clusterTransVec k w i = (clusterTransVec k w).ofLp i from rfl, clusterTransVec_ofLp]
  simp [hi]

/-- The total momentum of the cluster `k`. -/
noncomputable def clusterMomentum (m : Fin N → ℝ) (k : Finset (Fin N)) (v : EN E N) : E :=
  ∑ i ∈ k, m i • v i

lemma massInner_clusterTransVec {m : Fin N → ℝ} (k : Finset (Fin N)) (v : EN E N) (w : E) :
    massInner m v (clusterTransVec k w) = inner ℝ (clusterMomentum m k v) w := by
  have h1 : massInner m v (clusterTransVec k w) = ∑ i ∈ k, m i * inner ℝ (v i) w := by
    rw [massInner]
    rw [← Finset.sum_subset (Finset.subset_univ k)]
    · exact Finset.sum_congr rfl fun i hi => by rw [clusterTransVec_apply_of_mem hi]
    · intro i _ hi
      rw [clusterTransVec_apply_of_notMem hi, inner_zero_right, mul_zero]
  have h2 : inner ℝ (clusterMomentum m k v) w = ∑ i ∈ k, m i * inner ℝ (v i) w := by
    rw [clusterMomentum, sum_inner]
    exact Finset.sum_congr rfl fun i _ => by rw [real_inner_smul_left]
  rw [h1, h2]

lemma clusterCM_eq_inv_smul_clusterMomentum {m : Fin N → ℝ} (k : Finset (Fin N)) (v : EN E N) :
    clusterCM m k v = (clusterMass m k)⁻¹ • clusterMomentum m k v := by
  rw [clusterCM, clusterMomentum]

/-! ## 2. The perturbation of the curve by a rigid translation of the cluster -/

/-- The curve obtained from `γ` by translating the bodies of `k` by `ε ψ(t)` in the direction `w`
(the other bodies are kept fixed). -/
noncomputable def clusterPert (k : Finset (Fin N)) (w : E) (c : ℝ → ℝ) (γ : ℝ → EN E N)
    (ε t : ℝ) : EN E N :=
  γ t + (ε * c t) • clusterTransVec k w

lemma clusterPert_apply {k : Finset (Fin N)} {w : E} {c : ℝ → ℝ} {γ : ℝ → EN E N} {ε t : ℝ}
    (i : Fin N) :
    clusterPert k w c γ ε t i = γ t i + (ε * c t) • (if i ∈ k then w else 0) := by
  rw [clusterPert, PiLp.add_apply, PiLp.smul_apply, clusterTransVec_ofLp]

lemma clusterPert_apply_of_mem {k : Finset (Fin N)} {w : E} {c : ℝ → ℝ} {γ : ℝ → EN E N}
    {ε t : ℝ} {i : Fin N} (hi : i ∈ k) :
    clusterPert k w c γ ε t i = γ t i + (ε * c t) • w := by
  rw [clusterPert_apply, if_pos hi]

lemma clusterPert_apply_of_notMem {k : Finset (Fin N)} {w : E} {c : ℝ → ℝ} {γ : ℝ → EN E N}
    {ε t : ℝ} {i : Fin N} (hi : i ∉ k) :
    clusterPert k w c γ ε t i = γ t i := by
  rw [clusterPert_apply, if_neg hi, smul_zero, add_zero]

lemma clusterPert_sub_of_mem {k : Finset (Fin N)} {w : E} {c : ℝ → ℝ} {γ : ℝ → EN E N}
    {ε t : ℝ} {i j : Fin N} (hi : i ∈ k) (hj : j ∈ k) :
    clusterPert k w c γ ε t i - clusterPert k w c γ ε t j = γ t i - γ t j := by
  rw [clusterPert_apply_of_mem hi, clusterPert_apply_of_mem hj]
  abel

lemma clusterPert_sub_of_notMem {k : Finset (Fin N)} {w : E} {c : ℝ → ℝ} {γ : ℝ → EN E N}
    {ε t : ℝ} {i j : Fin N} (hi : i ∉ k) (hj : j ∉ k) :
    clusterPert k w c γ ε t i - clusterPert k w c γ ε t j = γ t i - γ t j := by
  rw [clusterPert_apply_of_notMem hi, clusterPert_apply_of_notMem hj]

lemma clusterPert_sub_of_mem_notMem {k : Finset (Fin N)} {w : E} {c : ℝ → ℝ} {γ : ℝ → EN E N}
    {ε t : ℝ} {i j : Fin N} (hi : i ∈ k) (hj : j ∉ k) :
    clusterPert k w c γ ε t i - clusterPert k w c γ ε t j = (γ t i - γ t j) + (ε * c t) • w := by
  rw [clusterPert_apply_of_mem hi, clusterPert_apply_of_notMem hj]
  abel

lemma absolutelyContinuousOnInterval_clusterPert {k : Finset (Fin N)} {w : E} {c : ℝ → ℝ}
    {γ : ℝ → EN E N} {a b ε : ℝ} (hac : AbsolutelyContinuousOnInterval γ a b)
    (hc : ContDiff ℝ 1 c) :
    AbsolutelyContinuousOnInterval (fun t => clusterPert k w c γ ε t) a b := by
  have h1 : (fun t => clusterPert k w c γ ε t)
      = (fun t => γ t) + fun t => (ε * c t) • clusterTransVec k w := by
    funext t; rw [clusterPert]; rfl
  rw [h1]
  refine hac.add ?_
  have h2 : ContDiff ℝ 1 (fun t : ℝ => (ε * c t) • clusterTransVec k w) := by fun_prop
  exact h2.contDiffOn.absolutelyContinuousOnInterval

lemma deriv_clusterPert {k : Finset (Fin N)} {w : E} {c : ℝ → ℝ} {γ : ℝ → EN E N} {ε t : ℝ}
    (hdγ : DifferentiableAt ℝ γ t) (hc : ContDiff ℝ 1 c) :
    deriv (fun s => clusterPert k w c γ ε s) t
      = deriv γ t + (ε * deriv c t) • clusterTransVec k w := by
  have hder : HasDerivAt (fun s : ℝ => (ε * c s) • clusterTransVec k w)
      ((ε * deriv c t) • clusterTransVec k w) t := by
    have h1 : HasDerivAt (fun s : ℝ => ε * c s) (ε * deriv c t) t :=
      (hc.differentiable (by norm_num) t).hasDerivAt.const_mul ε
    exact h1.smul_const (clusterTransVec k w)
  have htot : HasDerivAt (fun s : ℝ => clusterPert k w c γ ε s)
      (deriv γ t + (ε * deriv c t) • clusterTransVec k w) t := by
    have heq : (fun s : ℝ => clusterPert k w c γ ε s)
        = (fun s : ℝ => γ s) + fun s : ℝ => (ε * c s) • clusterTransVec k w := by
      funext s; rw [Pi.add_apply, clusterPert]
    rw [heq]
    exact hdγ.hasDerivAt.add hder
  exact htot.deriv

/-! ## 3. The external force acting on a cluster (pair form) -/

/-- The cross pairs of `k` (pairs with exactly one body in `k`). -/
noncomputable def crossPairs (k : Finset (Fin N)) : Finset (Fin N × Fin N) :=
  (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k) ∧ (p.1 ∈ k ∨ p.2 ∈ k))

/-- The rest pairs of `k` (pairs not internal to `k`). -/
noncomputable def restPairs (k : Finset (Fin N)) : Finset (Fin N × Fin N) :=
  (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k))

lemma crossPairs_subset_restPairs (k : Finset (Fin N)) : crossPairs k ⊆ restPairs k := by
  intro p hp
  simp only [crossPairs, restPairs, Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.1⟩

/-- The (pair-form) external force acting on the cluster `k`. -/
noncomputable def clusterCrossForceVec (m : Fin N → ℝ) (k : Finset (Fin N)) (x : EN E N) : E :=
  ∑ p ∈ crossPairs k,
    (m p.1 * m p.2 * (r x p.1 p.2 ^ 3)⁻¹) • (if p.1 ∈ k then x p.2 - x p.1 else x p.1 - x p.2)

lemma continuousOn_clusterCrossForceVec {m : Fin N → ℝ} {k : Finset (Fin N)} {ν : ℝ}
    (hν : 0 < ν) :
    ContinuousOn (clusterCrossForceVec m k)
      {x : EN E N | ClusterSeparatedWeak k x ν} := by
  have hunfold : clusterCrossForceVec m k = fun x : EN E N =>
      ∑ p ∈ crossPairs k,
        (m p.1 * m p.2 * (r x p.1 p.2 ^ 3)⁻¹) •
          (if p.1 ∈ k then x p.2 - x p.1 else x p.1 - x p.2) := rfl
  rw [hunfold]
  refine continuousOn_finsetSum _ fun p hp => ?_
  have hp' : p ∈ crossPairs k := hp
  rw [crossPairs, Finset.mem_filter] at hp'
  have hmem : (p.1 ∈ k ∧ p.2 ∉ k) ∨ (p.1 ∉ k ∧ p.2 ∈ k) := by
    rcases hp'.2.2 with h | h
    · exact Or.inl ⟨h, fun h2 => hp'.2.1 ⟨h, h2⟩⟩
    · exact Or.inr ⟨fun h2 => hp'.2.1 ⟨h2, h⟩, h⟩
  have hne : ∀ x ∈ {x : EN E N | ClusterSeparatedWeak k x ν}, x p.1 ≠ x p.2 := by
    intro x hx
    rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hr : r x p.1 p.2 ≠ 0 := ne_of_gt (lt_of_lt_of_le hν (hx p.1 h1 p.2 h2))
      rw [r_eq_norm_sub] at hr
      exact sub_ne_zero.mp (norm_ne_zero_iff.mp hr)
    · have hr : r x p.2 p.1 ≠ 0 := ne_of_gt (lt_of_lt_of_le hν (hx p.2 h2 p.1 h1))
      rw [r_eq_norm_sub, norm_sub_rev] at hr
      exact sub_ne_zero.mp (norm_ne_zero_iff.mp hr)
  have hsub : {x : EN E N | ClusterSeparatedWeak k x ν} ⊆ {x : EN E N | x p.1 ≠ x p.2} := hne
  have h1 : ContinuousOn (fun x : EN E N => (r x p.1 p.2 ^ 3)⁻¹)
      {x : EN E N | ClusterSeparatedWeak k x ν} := by
    have h2 : ContinuousOn (fun x : EN E N => ((r x p.1 p.2)⁻¹) ^ 3)
        {x : EN E N | ClusterSeparatedWeak k x ν} :=
      ((continuousOn_inv_r p.1 p.2).mono hsub).pow 3
    refine h2.congr fun x _ => ?_
    show (r x p.1 p.2 ^ 3)⁻¹ = (r x p.1 p.2)⁻¹ ^ 3
    rw [inv_pow]
  have hcont2 : ContinuousOn
      (fun x : EN E N => (if p.1 ∈ k then x p.2 - x p.1 else x p.1 - x p.2))
      {x : EN E N | ClusterSeparatedWeak k x ν} := by
    by_cases h1 : p.1 ∈ k
    · simp only [h1, if_true]; fun_prop
    · simp only [h1, if_false]; fun_prop
  exact (continuousOn_const.mul h1).smul hcont2

/-! ## 4. The second-order expansion of the interaction potential under a cluster translation -/

/-- **Expansion of the interaction potential.**  Translating the bodies of `k` by the *same*
vector `e` leaves the internal potential of `k` unchanged, so the variation of the potential is the
variation of the interaction with the complement; the latter is `C²` because the cross pairs are
separated by `ν`.  We obtain the first-order term `⟪F, e⟫` (with `F` the external force) with a
second-order remainder `O(‖e‖²)`. -/
lemma abs_clusterPotentialRest_sub_sub_inner_le {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i)
    {k : Finset (Fin N)} {x y : EN E N} {ν : ℝ} (hν : 0 < ν)
    (hsep : ClusterSeparatedWeak k x ν) (hclose : ∀ j ∉ k, y j = x j) {e : E}
    (hpert : ∀ j ∈ k, y j = x j + e) (he : 2 * ‖e‖ ≤ ν) :
    |clusterPotentialRest m k y - clusterPotentialRest m k x
        - inner ℝ (clusterCrossForceVec m k x) e|
      ≤ (∑ p ∈ crossPairs k, m p.1 * m p.2) * (32 * ‖e‖ ^ 2 / ν ^ 3) := by
  classical
  have hsum : clusterPotentialRest m k y - clusterPotentialRest m k x
      = ∑ p ∈ restPairs k,
          (m p.1 * m p.2 * (r y p.1 p.2)⁻¹ - m p.1 * m p.2 * (r x p.1 p.2)⁻¹) := by
    rw [clusterPotentialRest, clusterPotentialRest, ← Finset.sum_sub_distrib]
    rfl
  have hzero : ∀ p ∈ restPairs k, p ∉ crossPairs k →
      m p.1 * m p.2 * (r y p.1 p.2)⁻¹ - m p.1 * m p.2 * (r x p.1 p.2)⁻¹ = 0 := by
    intro p hp hpc
    rw [restPairs, Finset.mem_filter] at hp
    have hboth : ¬ (p.1 ∈ k ∨ p.2 ∈ k) := by
      by_contra hcon
      exact hpc (by rw [crossPairs, Finset.mem_filter]; exact ⟨hp.1, hp.2, hcon⟩)
    rw [not_or] at hboth
    have hryx : r y p.1 p.2 = r x p.1 p.2 := by
      rw [r_eq_norm_sub, r_eq_norm_sub, hclose p.1 hboth.1, hclose p.2 hboth.2]
    rw [hryx, sub_self]
  rw [hsum, ← Finset.sum_subset (crossPairs_subset_restPairs k) hzero]
  have hper : ∀ p ∈ crossPairs k,
      |m p.1 * m p.2 * (r y p.1 p.2)⁻¹ - m p.1 * m p.2 * (r x p.1 p.2)⁻¹
        - inner ℝ ((m p.1 * m p.2 * (r x p.1 p.2 ^ 3)⁻¹) •
            (if p.1 ∈ k then x p.2 - x p.1 else x p.1 - x p.2)) e|
      ≤ m p.1 * m p.2 * (32 * ‖e‖ ^ 2 / ν ^ 3) := by
    intro p hp
    rw [crossPairs, Finset.mem_filter] at hp
    obtain ⟨hp1, hpmemk, hdisj⟩ := hp
    have hsepν : ν ≤ ‖x p.1 - x p.2‖ := by
      rcases hdisj with h1 | h2
      · have h2' : p.2 ∉ k := fun h => hpmemk ⟨h1, h⟩
        have h := hsep p.1 h1 p.2 h2'
        rwa [r_eq_norm_sub] at h
      · have h1' : p.1 ∉ k := fun h => hpmemk ⟨h, h2⟩
        have h := hsep p.2 h2 p.1 h1'
        rw [r_eq_norm_sub, norm_sub_rev] at h
        exact h
    have hy : y p.1 - y p.2 = (x p.1 - x p.2) + (if p.1 ∈ k then e else -e) := by
      by_cases h1 : p.1 ∈ k
      · have h2 : p.2 ∉ k := fun h2 => hpmemk ⟨h1, h2⟩
        rw [hpert p.1 h1, hclose p.2 h2, if_pos h1]
        abel
      · have h2 : p.2 ∈ k := by
          rcases hdisj with h | h
          · exact absurd h h1
          · exact h
        rw [hclose p.1 h1, hpert p.2 h2, if_neg h1]
        abel
    have hyr : r y p.1 p.2 = ‖(x p.1 - x p.2) + (if p.1 ∈ k then e else -e)‖ := by
      rw [r_eq_norm_sub, hy]
    have hne : 2 * ‖(if p.1 ∈ k then e else -e)‖ ≤ ν := by
      by_cases h1 : p.1 ∈ k <;> simp only [h1, if_true, if_false, norm_neg] <;> exact he
    have hhn : ‖(if p.1 ∈ k then e else -e)‖ = ‖e‖ := by
      by_cases h1 : p.1 ∈ k <;> simp only [h1, if_true, if_false, norm_neg]
    have htay := Commons.Analysis.Calculus.inv_norm_add_taylor (v := x p.1 - x p.2)
      (h := (if p.1 ∈ k then e else -e)) hν hsepν hne
    have hρ : |(r y p.1 p.2)⁻¹ - (r x p.1 p.2)⁻¹
        + inner ℝ (x p.1 - x p.2) (if p.1 ∈ k then e else -e) / (r x p.1 p.2) ^ 3|
        ≤ 32 * ‖e‖ ^ 2 / ν ^ 3 := by
      rw [hyr, r_eq_norm_sub x p.1 p.2]
      simpa only [hhn] using htay
    have hlin : -m p.1 * m p.2 * inner ℝ (x p.1 - x p.2) (if p.1 ∈ k then e else -e)
          / (r x p.1 p.2) ^ 3
        = inner ℝ ((m p.1 * m p.2 * (r x p.1 p.2 ^ 3)⁻¹) •
            (if p.1 ∈ k then x p.2 - x p.1 else x p.1 - x p.2)) e := by
      rw [r_eq_norm_sub x p.1 p.2]
      by_cases h1 : p.1 ∈ k
      · have hv : (if p.1 ∈ k then x p.2 - x p.1 else x p.1 - x p.2)
            = -(x p.1 - x p.2) := by rw [if_pos h1]; abel
        rw [if_pos h1, hv]
        simp only [h1, if_true, real_inner_smul_left, inner_neg_left]
        field_simp
      · rw [if_neg h1]
        simp only [h1, if_false, real_inner_smul_left, inner_neg_right]
        field_simp
    have hstep : m p.1 * m p.2 * (r y p.1 p.2)⁻¹ - m p.1 * m p.2 * (r x p.1 p.2)⁻¹
        = inner ℝ ((m p.1 * m p.2 * (r x p.1 p.2 ^ 3)⁻¹) •
            (if p.1 ∈ k then x p.2 - x p.1 else x p.1 - x p.2)) e
          + m p.1 * m p.2 *
            ((r y p.1 p.2)⁻¹ - (r x p.1 p.2)⁻¹
              + inner ℝ (x p.1 - x p.2) (if p.1 ∈ k then e else -e) / (r x p.1 p.2) ^ 3) := by
      rw [← hlin]
      ring
    rw [hstep, add_sub_cancel_left]
    refine le_trans (le_of_eq (abs_mul _ _)) ?_
    rw [abs_of_nonneg (mul_nonneg (hm p.1) (hm p.2))]
    exact mul_le_mul_of_nonneg_left hρ (mul_nonneg (hm p.1) (hm p.2))
  have hsum2 : (∑ p ∈ crossPairs k,
        (m p.1 * m p.2 * (r y p.1 p.2)⁻¹ - m p.1 * m p.2 * (r x p.1 p.2)⁻¹))
      = (∑ p ∈ crossPairs k,
          inner ℝ ((m p.1 * m p.2 * (r x p.1 p.2 ^ 3)⁻¹) •
            (if p.1 ∈ k then x p.2 - x p.1 else x p.1 - x p.2)) e)
        + ∑ p ∈ crossPairs k,
            ((m p.1 * m p.2 * (r y p.1 p.2)⁻¹ - m p.1 * m p.2 * (r x p.1 p.2)⁻¹)
              - inner ℝ ((m p.1 * m p.2 * (r x p.1 p.2 ^ 3)⁻¹) •
                  (if p.1 ∈ k then x p.2 - x p.1 else x p.1 - x p.2)) e) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p hp => by ring
  have hcrossid : (∑ p ∈ crossPairs k,
      inner ℝ ((m p.1 * m p.2 * (r x p.1 p.2 ^ 3)⁻¹) •
          (if p.1 ∈ k then x p.2 - x p.1 else x p.1 - x p.2)) e)
      = inner ℝ (clusterCrossForceVec m k x) e := by
    rw [clusterCrossForceVec, sum_inner]
  rw [hsum2, hcrossid, add_sub_cancel_left]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum hper


/-! ## 5. Basic consequences of the perturbation -/

/-- The perturbation leaves the left endpoint fixed. -/
lemma clusterPert_eq_left_of_tsupport_subset {k : Finset (Fin N)} {w : E} {ψ : ℝ → ℝ}
    {γ : ℝ → EN E N} {a b ε : ℝ} (hts : tsupport ψ ⊆ Ioo a b) :
    clusterPert k w ψ γ ε a = γ a := by
  have ha : ψ a = 0 := image_eq_zero_of_notMem_tsupport (fun h => (hts h).1.ne rfl)
  rw [clusterPert, ha, mul_zero, zero_smul, add_zero]

/-- The perturbation leaves the right endpoint fixed. -/
lemma clusterPert_eq_right_of_tsupport_subset {k : Finset (Fin N)} {w : E} {ψ : ℝ → ℝ}
    {γ : ℝ → EN E N} {a b ε : ℝ} (hts : tsupport ψ ⊆ Ioo a b) :
    clusterPert k w ψ γ ε b = γ b := by
  have hb : ψ b = 0 := image_eq_zero_of_notMem_tsupport (fun h => (hts h).2.ne rfl)
  rw [clusterPert, hb, mul_zero, zero_smul, add_zero]

/-- The rigid translation of the cluster does not create collisions. -/
lemma withoutCollisions_clusterPert {k : Finset (Fin N)} {w : E} {ψ : ℝ → ℝ} {γ : ℝ → EN E N}
    {ν : ℝ} (hν : 0 < ν) {Mψ : ℝ} (hMψ : ∀ t, |ψ t| ≤ Mψ)
    {ε t : ℝ} (hε : 3 * (|ε| * (Mψ * ‖w‖)) ≤ ν)
    (hsep : ClusterSeparatedWeak k (γ t) ν) (hnc : WithoutCollisions (γ t)) :
    WithoutCollisions (clusterPert k w ψ γ ε t) := by
  intro i j hij hcon
  have hεψ : |ε| * (Mψ * ‖w‖) ≤ ν / 3 := by linarith
  have hψw : ‖(ε * ψ t) • w‖ ≤ ν / 3 := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul]
    calc |ε| * |ψ t| * ‖w‖ = |ε| * (|ψ t| * ‖w‖) := by ring
      _ ≤ |ε| * (Mψ * ‖w‖) := by
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg ε)
            exact mul_le_mul_of_nonneg_right (hMψ t) (norm_nonneg w)
      _ ≤ ν / 3 := hεψ
  have hpos : (0:ℝ) < ν - ν / 3 := by linarith
  rw [r_eq_norm_sub] at hcon
  by_cases hi : i ∈ k
  · by_cases hj : j ∈ k
    · rw [clusterPert_sub_of_mem hi hj] at hcon
      exact hnc i j hij (by rw [r_eq_norm_sub]; exact hcon)
    · rw [clusterPert_sub_of_mem_notMem hi hj] at hcon
      have hbase : ν ≤ ‖γ t i - γ t j‖ := by
        rw [← r_eq_norm_sub]; exact hsep i hi j hj
      have h1 : ‖γ t i - γ t j‖ ≤ ‖(γ t i - γ t j) + (ε * ψ t) • w‖ + ‖(ε * ψ t) • w‖ := by
        calc ‖γ t i - γ t j‖ = ‖((γ t i - γ t j) + (ε * ψ t) • w) - (ε * ψ t) • w‖ := by
              rw [add_sub_cancel_right]
          _ ≤ _ := norm_sub_le _ _
      rw [hcon] at h1
      linarith
  · have hj : j ∈ k := by
      by_contra hj
      rw [clusterPert_sub_of_notMem hi hj] at hcon
      exact hnc i j hij (by rw [r_eq_norm_sub]; exact hcon)
    have hjm : clusterPert k w ψ γ ε t j - clusterPert k w ψ γ ε t i
        = (γ t j - γ t i) + (ε * ψ t) • w := clusterPert_sub_of_mem_notMem hj hi
    have hneg : clusterPert k w ψ γ ε t i - clusterPert k w ψ γ ε t j
        = -((γ t j - γ t i) + (ε * ψ t) • w) := by
      rw [show clusterPert k w ψ γ ε t i - clusterPert k w ψ γ ε t j
          = -(clusterPert k w ψ γ ε t j - clusterPert k w ψ γ ε t i) by abel, hjm]
    rw [hneg, norm_neg] at hcon
    have hbase : ν ≤ ‖γ t j - γ t i‖ := by
      have h := hsep j hj i hi
      rwa [r_eq_norm_sub] at h
    have h1 : ‖γ t j - γ t i‖ ≤ ‖(γ t j - γ t i) + (ε * ψ t) • w‖ + ‖(ε * ψ t) • w‖ := by
      calc ‖γ t j - γ t i‖ = ‖((γ t j - γ t i) + (ε * ψ t) • w) - (ε * ψ t) • w‖ := by
            rw [add_sub_cancel_right]
        _ ≤ _ := norm_sub_le _ _
    rw [hcon] at h1
    linarith

/-! ## 6. The kinetic energy of a perturbation -/

/-- The kinetic energy is a quadratic form. -/
lemma kinetic_add (m : Fin N → ℝ) (v h : EN E N) :
    kinetic m (v + h) = kinetic m v + massInner m v h + kinetic m h := by
  have h2 : ∀ i : Fin N, m i * ‖(v + h) i‖ ^ 2
      = m i * ‖v i‖ ^ 2 + 2 * (m i * inner ℝ (v i) (h i)) + m i * ‖h i‖ ^ 2 := by
    intro i
    rw [PiLp.add_apply, norm_add_sq_real]
    ring
  have key : (∑ i, m i * ‖(v + h) i‖ ^ 2)
      = (∑ i, m i * ‖v i‖ ^ 2) + 2 * (∑ i, m i * inner ℝ (v i) (h i))
        + (∑ i, m i * ‖h i‖ ^ 2) := by
    rw [Finset.sum_congr rfl (fun i _ => h2 i), Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum]
  simp only [kinetic, massInner]
  rw [key]
  ring

/-- A crude upper bound for the kinetic energy of a sum. -/
lemma kinetic_add_le (m : Fin N → ℝ) (hm : ∀ i, 0 ≤ m i) (v h : EN E N) :
    kinetic m (v + h) ≤ 2 * kinetic m v + 2 * kinetic m h := by
  have h2 : ∀ i : Fin N, ‖(v + h) i‖ ^ 2 ≤ 2 * ‖v i‖ ^ 2 + 2 * ‖h i‖ ^ 2 := by
    intro i
    have h1 : ‖(v + h) i‖ ≤ ‖v i‖ + ‖h i‖ := by
      rw [PiLp.add_apply]; exact norm_add_le _ _
    have h1' : (‖v i‖ + ‖h i‖) ^ 2 ≤ 2 * ‖v i‖ ^ 2 + 2 * ‖h i‖ ^ 2 := by
      nlinarith [sq_nonneg (‖v i‖ - ‖h i‖)]
    have h2' : ‖(v + h) i‖ ^ 2 ≤ (‖v i‖ + ‖h i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    linarith
  have key : (∑ i, m i * ‖(v + h) i‖ ^ 2) ≤ 2 * (∑ i, m i * ‖v i‖ ^ 2)
      + 2 * (∑ i, m i * ‖h i‖ ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have h3 := h2 i
    have h4 := hm i
    nlinarith [sq_nonneg (‖v i‖), sq_nonneg (‖h i‖)]
  simp only [kinetic]
  linarith [key]

/-- The a.e. derivative of the perturbation. -/
lemma ae_deriv_clusterPert {k : Finset (Fin N)} {w : E} {ψ : ℝ → ℝ} {γ : ℝ → EN E N}
    {a b ε : ℝ} (hac : AbsolutelyContinuousOnInterval γ a b) (hψ : ContDiff ℝ 1 ψ) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
      deriv (fun s => clusterPert k w ψ γ ε s) t
        = deriv γ t + (ε * deriv ψ t) • clusterTransVec k w := by
  have hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIcc a b → DifferentiableAt ℝ γ t :=
    Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_ae_differentiableAt_vector hac
  filter_upwards [hd.filter_mono (MeasureTheory.ae_mono MeasureTheory.Measure.restrict_le_self),
    MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht hmem
  exact deriv_clusterPert (ht (Set.mem_uIcc.mpr (Or.inl ⟨hmem.1.le, hmem.2⟩)))
    (hψ.of_le (by norm_num))


/-! ## 7. The internal potential is unchanged, and the domination of the perturbed Lagrangian -/

/-- The internal potential of `k` is unchanged by the rigid translation. -/
lemma clusterPotential_clusterPert {m : Fin N → ℝ} {k : Finset (Fin N)} {w : E} {ψ : ℝ → ℝ}
    {γ : ℝ → EN E N} {ε t : ℝ} :
    clusterPotential m k (clusterPert k w ψ γ ε t) = clusterPotential m k (γ t) := by
  rw [clusterPotential, clusterPotential]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' := (Finset.mem_filter.mp hp).2
  have hr : r (clusterPert k w ψ γ ε t) p.1 p.2 = r (γ t) p.1 p.2 := by
    rw [r_eq_norm_sub, r_eq_norm_sub, clusterPert_sub_of_mem hp'.1 hp'.2]
  rw [hr]

/-- The kinetic energy of a multiple of the translation vector. -/
lemma kinetic_smul_clusterTransVec (m : Fin N → ℝ) (k : Finset (Fin N)) (w : E) (s : ℝ) :
    kinetic m (s • clusterTransVec k w) = clusterMass m k * s ^ 2 * ‖w‖ ^ 2 / 2 := by
  rw [kinetic, clusterMass]
  rw [← Finset.sum_subset (Finset.subset_univ k)]
  · have hS : (∑ x ∈ k, m x * ‖(s • clusterTransVec k w) x‖ ^ 2)
        = (∑ x ∈ k, m x) * (s ^ 2 * ‖w‖ ^ 2) := by
      rw [Finset.sum_congr rfl (fun i hi => by
        rw [PiLp.smul_apply, clusterTransVec_apply_of_mem hi, norm_smul, Real.norm_eq_abs,
          mul_pow, sq_abs])]
      rw [Finset.sum_mul]
    rw [hS]
    ring
  · intro i _ hi
    rw [PiLp.smul_apply, clusterTransVec_apply_of_notMem hi, smul_zero, norm_zero]
    ring

/-- **Domination of the perturbed Lagrangian.**  The rigid translation changes the Lagrangian only
by a bounded amount, so the perturbation is dominated by an integrable function. -/
lemma lagR_clusterPert_ae_le {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {h : ℝ}
    {γ : ℝ → EN E N} {a b : ℝ} (hac : AbsolutelyContinuousOnInterval γ a b)
    {k : Finset (Fin N)} {w : E} {ψ : ℝ → ℝ} {ν Mψ Md : ℝ} (hν : 0 < ν)
    (hψc : ContDiff ℝ 1 ψ) (hMψ0 : 0 ≤ Mψ) (hMψ : ∀ t, |ψ t| ≤ Mψ) (hMd : ∀ t, |deriv ψ t| ≤ Md)
    (hsep : ∀ t ∈ Icc a b, ClusterSeparatedWeak k (γ t) ν)
    {ε : ℝ} (hε4 : 4 * (|ε| * (Mψ * ‖w‖)) ≤ ν) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
      lagR m h (clusterPert k w ψ γ ε t) (deriv (fun s => clusterPert k w ψ γ ε s) t)
        ≤ 2 * kinetic m (deriv γ t) + U m (γ t)
          + (h + (clusterMass m k * (|ε| * Md * ‖w‖) ^ 2 / 2 + (clusterMass m k * (|ε| * Md * ‖w‖) ^ 2 / 2))
              + (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)), m p.1 * m p.2) * (2 * (|ε| * Mψ * ‖w‖) / ν ^ 2)) := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  filter_upwards [ae_deriv_clusterPert hac hψc,
    MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t hder hmem
  have htIcc : t ∈ Icc a b := ⟨hmem.1.le, hmem.2⟩
  rw [hder]
  rw [show lagR m h (clusterPert k w ψ γ ε t)
        (deriv γ t + (ε * deriv ψ t) • clusterTransVec k w)
      = kinetic m (deriv γ t + (ε * deriv ψ t) • clusterTransVec k w)
        + U m (clusterPert k w ψ γ ε t) + h from rfl]
  -- the kinetic part
  have hK : kinetic m (deriv γ t + (ε * deriv ψ t) • clusterTransVec k w)
      ≤ 2 * kinetic m (deriv γ t)
        + 2 * (clusterMass m k * ((|ε| * Md) * ‖w‖) ^ 2 / 2) := by
    refine (kinetic_add_le m (fun i => (hm i).le) _ _).trans ?_
    have h1 : kinetic m ((ε * deriv ψ t) • clusterTransVec k w)
        ≤ clusterMass m k * ((|ε| * Md) * ‖w‖) ^ 2 / 2 := by
      rw [kinetic_smul_clusterTransVec]
      have h3 : (ε * deriv ψ t) ^ 2 ≤ (|ε| * Md) ^ 2 := by
        have h6 : |ε * deriv ψ t| ≤ |ε| * Md := by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hMd t) (abs_nonneg ε)
        calc (ε * deriv ψ t) ^ 2 = |ε * deriv ψ t| ^ 2 := (sq_abs _).symm
          _ ≤ (|ε| * Md) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h6 2
      have h4 : 0 ≤ ‖w‖ ^ 2 := sq_nonneg _
      have h5 : 0 ≤ clusterMass m k := clusterMass_nonneg (fun i => (hm i).le) k
      calc clusterMass m k * (ε * deriv ψ t) ^ 2 * ‖w‖ ^ 2 / 2
          ≤ clusterMass m k * (|ε| * Md) ^ 2 * ‖w‖ ^ 2 / 2 := by
            refine div_le_div_of_nonneg_right ?_ (by norm_num)
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h3 h5) h4
        _ = clusterMass m k * ((|ε| * Md) * ‖w‖) ^ 2 / 2 := by ring
    linarith
  -- the potential part
  have hU : U m (clusterPert k w ψ γ ε t)
      ≤ U m (γ t) + (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)), m p.1 * m p.2) * (2 * (|ε| * Mψ * ‖w‖) / ν ^ 2) := by
    have hsplit := U_eq_clusterPotential_add_rest m k (clusterPert k w ψ γ ε t)
    have hsplit0 := U_eq_clusterPotential_add_rest m k (γ t)
    have hint := clusterPotential_clusterPert (m := m) (k := k) (w := w) (ψ := ψ)
      (γ := γ) (ε := ε) (t := t)
    have hρ : (0:ℝ) ≤ |ε| * Mψ * ‖w‖ := by
      exact mul_nonneg (mul_nonneg (abs_nonneg ε) hMψ0) (norm_nonneg w)
    have hρν : 2 * (|ε| * Mψ * ‖w‖) ≤ ν := by linarith
    have hbound := clusterPotentialRest_diff_le (m := m) (k := k) (x := γ t)
      (y := clusterPert k w ψ γ ε t) (ν := ν) (ρ := |ε| * Mψ * ‖w‖)
      (fun i => (hm i).le) hν hρ hρν (hsep t htIcc)
      (fun j hj => clusterPert_apply_of_notMem hj)
      (fun j hj => by
        rw [clusterPert_apply_of_mem hj, add_sub_cancel_left]
        rw [norm_smul, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hMψ t) (abs_nonneg ε)) (norm_nonneg w))
    rw [hsplit, hsplit0, hint]
    linarith
  linarith

/-- The perturbation has finite action whenever `γ` does. -/
lemma actionOn_clusterPert_lt_top {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {h : ℝ} (hh : 0 ≤ h)
    {γ : ℝ → EN E N} {a b : ℝ} (hab : a ≤ b) (hac : AbsolutelyContinuousOnInterval γ a b)
    (hnc : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), WithoutCollisions (γ t))
    (hfin : actionOn m h γ a b < ⊤)
    {k : Finset (Fin N)} {w : E} {ψ : ℝ → ℝ} {ν Mψ Md : ℝ} (hν : 0 < ν)
    (hψc : ContDiff ℝ 1 ψ) (hMψ0 : 0 ≤ Mψ) (hMψ : ∀ t, |ψ t| ≤ Mψ)
    (hMd : ∀ t, |deriv ψ t| ≤ Md)
    (hsep : ∀ t ∈ Icc a b, ClusterSeparatedWeak k (γ t) ν) {ε : ℝ}
    (hε4 : 4 * (|ε| * (Mψ * ‖w‖)) ≤ ν) :
    actionOn m h (fun t => clusterPert k w ψ γ ε t) a b < ⊤ := by
  letI : MeasurableSpace (EN E N) := borel (EN E N)
  haveI : BorelSpace (EN E N) := ⟨rfl⟩
  have hm0 : ∀ i, 0 ≤ m i := fun i => (hm i).le
  set Cc : ℝ := (clusterMass m k * (|ε| * Md * ‖w‖) ^ 2 / 2
    + (clusterMass m k * (|ε| * Md * ‖w‖) ^ 2 / 2)
    + (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)), m p.1 * m p.2) * (2 * (|ε| * Mψ * ‖w‖) / ν ^ 2)) with hCc
  -- the bridge for `γ`
  have hbridge : (∫⁻ t in Set.Ioc a b, ENNReal.ofReal (lagR m h (γ t) (deriv γ t)))
      = actionOn m h γ a b := by
    rw [actionOn]
    exact (lintegral_congr_ae (by
      filter_upwards [hnc] with t ht
      exact lagrangian_eq_ofReal_lagR ht)).symm
  have hlagRnn : ∀ t, 0 ≤ lagR m h (γ t) (deriv γ t) := by
    intro t
    rw [show lagR m h (γ t) (deriv γ t) = kinetic m (deriv γ t) + U m (γ t) + h from rfl]
    have h1 := kinetic_nonneg m hm0 (deriv γ t)
    have h2 := U_nonneg hm0 (γ t)
    linarith
  have hK1 : (∫⁻ t in Set.Ioc a b, ENNReal.ofReal (kinetic m (deriv γ t))) < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono_ae ?_) (hbridge ▸ hfin)
    filter_upwards with t
    rw [ENNReal.ofReal_le_ofReal_iff (hlagRnn t)]
    rw [show lagR m h (γ t) (deriv γ t) = kinetic m (deriv γ t) + U m (γ t) + h from rfl]
    have h1 := kinetic_nonneg m hm0 (deriv γ t)
    have h2 := U_nonneg hm0 (γ t)
    linarith
  have hU1 : (∫⁻ t in Set.Ioc a b, ENNReal.ofReal (U m (γ t))) < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono_ae ?_) (hbridge ▸ hfin)
    filter_upwards with t
    rw [ENNReal.ofReal_le_ofReal_iff (hlagRnn t)]
    rw [show lagR m h (γ t) (deriv γ t) = kinetic m (deriv γ t) + U m (γ t) + h from rfl]
    have h1 := kinetic_nonneg m hm0 (deriv γ t)
    have h2 := U_nonneg hm0 (γ t)
    linarith
  -- the pointwise domination of the Lagrangian
  have hpt : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
      lagrangian m h (clusterPert k w ψ γ ε t) (deriv (fun s => clusterPert k w ψ γ ε s) t)
        ≤ ENNReal.ofReal (2 * kinetic m (deriv γ t) + U m (γ t) + (h + Cc)) := by
    filter_upwards [lagR_clusterPert_ae_le (m := m) (h := h) hm hac hν hψc hMψ0 hMψ hMd hsep hε4,
      hnc, MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t hle hncγ hmem
    have hncε : WithoutCollisions (clusterPert k w ψ γ ε t) :=
      withoutCollisions_clusterPert hν hMψ (by linarith : 3 * (|ε| * (Mψ * ‖w‖)) ≤ ν)
        (hsep t ⟨hmem.1.le, hmem.2⟩) hncγ
    have hbound : lagR m h (clusterPert k w ψ γ ε t)
          (deriv (fun s => clusterPert k w ψ γ ε s) t)
        ≤ 2 * kinetic m (deriv γ t) + U m (γ t) + (h + Cc) := by
      refine hle.trans (le_of_eq ?_)
      rw [hCc]
      ring
    rw [lagrangian, if_pos hncε]
    exact ENNReal.ofReal_le_ofReal hbound
  -- measurability of the dominating functions
  have hKmeas : AEMeasurable (fun t => ENNReal.ofReal (kinetic m (deriv γ t)))
      (volume.restrict (Set.Ioc a b)) := by
    have hd := Commons.MeasureTheory.Integral.aestronglyMeasurable_deriv_of_absolutelyContinuousOnInterval
      hac
    have h1 : AEMeasurable (fun t => kinetic m (deriv γ t)) (volume.restrict (Set.Ioc a b)) :=
      (continuous_kinetic m).measurable.comp_aemeasurable hd.aemeasurable
    exact ENNReal.measurable_ofReal.comp_aemeasurable h1
  have hUmeas : AEMeasurable (fun t => ENNReal.ofReal (U m (γ t)))
      (volume.restrict (Set.Ioc a b)) := by
    have hγmeas : AEMeasurable γ (volume.restrict (Set.Ioc a b)) :=
      ((hac.continuousOn.mono (fun t ht =>
        Set.mem_uIcc.mpr (Or.inl ⟨ht.1.le, ht.2⟩))).aestronglyMeasurable
        measurableSet_Ioc).aemeasurable
    have h1 : AEMeasurable (fun t => U m (γ t)) (volume.restrict (Set.Ioc a b)) :=
      (measurable_U m).comp_aemeasurable hγmeas
    exact ENNReal.measurable_ofReal.comp_aemeasurable h1
  have hK2meas : AEMeasurable (fun t => ENNReal.ofReal (2 * kinetic m (deriv γ t)))
      (volume.restrict (Set.Ioc a b)) := by
    have hpoint : (fun t => ENNReal.ofReal (2 * kinetic m (deriv γ t)))
        = fun t => (2 : ℝ≥0∞) * ENNReal.ofReal (kinetic m (deriv γ t)) := by
      funext t
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    rw [hpoint]
    exact hKmeas.const_mul 2
  have h2' : (∫⁻ t in Set.Ioc a b, ENNReal.ofReal (2 * kinetic m (deriv γ t))) < ⊤ := by
    have hpoint : (fun t => ENNReal.ofReal (2 * kinetic m (deriv γ t)))
        = fun t => (2 : ℝ≥0∞) * ENNReal.ofReal (kinetic m (deriv γ t)) := by
      funext t
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    rw [hpoint, MeasureTheory.lintegral_const_mul' (2 : ℝ≥0∞) _ (by simp)]
    exact ENNReal.mul_lt_top (by norm_num) hK1
  have h3' : (∫⁻ t in Set.Ioc a b, ENNReal.ofReal (h + Cc)) < ⊤ := by
    rw [MeasureTheory.lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by simp)
  have hc1 : (∫⁻ t in Set.Ioc a b,
      ENNReal.ofReal (2 * kinetic m (deriv γ t) + U m (γ t) + (h + Cc))) < ⊤ := by
    have hle : (∫⁻ t in Set.Ioc a b,
          ENNReal.ofReal (2 * kinetic m (deriv γ t) + U m (γ t) + (h + Cc)))
        ≤ ∫⁻ t in Set.Ioc a b, (ENNReal.ofReal (2 * kinetic m (deriv γ t))
            + ENNReal.ofReal (U m (γ t)) + ENNReal.ofReal (h + Cc)) := by
      refine lintegral_mono_ae ?_
      filter_upwards with t
      calc ENNReal.ofReal (2 * kinetic m (deriv γ t) + U m (γ t) + (h + Cc))
          ≤ ENNReal.ofReal (2 * kinetic m (deriv γ t) + U m (γ t)) + ENNReal.ofReal (h + Cc) :=
            ENNReal.ofReal_add_le
        _ ≤ (ENNReal.ofReal (2 * kinetic m (deriv γ t)) + ENNReal.ofReal (U m (γ t)))
              + ENNReal.ofReal (h + Cc) :=
            add_le_add_left ENNReal.ofReal_add_le _
    have hAB : AEMeasurable (fun t => ENNReal.ofReal (2 * kinetic m (deriv γ t))
        + ENNReal.ofReal (U m (γ t))) (volume.restrict (Set.Ioc a b)) :=
      hK2meas.add hUmeas
    refine lt_of_le_of_lt hle ?_
    rw [MeasureTheory.lintegral_add_left' hAB (fun t => ENNReal.ofReal (h + Cc)),
      MeasureTheory.lintegral_add_left' hK2meas (fun t => ENNReal.ofReal (U m (γ t)))]
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨h2', hU1⟩, h3'⟩
  calc actionOn m h (fun t => clusterPert k w ψ γ ε t) a b
      = ∫⁻ t in Set.Ioc a b,
          lagrangian m h (clusterPert k w ψ γ ε t) (deriv (fun s => clusterPert k w ψ γ ε s) t) :=
        rfl
    _ ≤ ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (2 * kinetic m (deriv γ t) + U m (γ t) + (h + Cc)) :=
        lintegral_mono_ae hpt
    _ < ⊤ := hc1


/-! ## 8. The pointwise expansion of the Lagrangian -/

/-- **The a.e. pointwise expansion of the Lagrangian.**  Under the rigid translation of `k`, the
Lagrangian changes by `ε` times the work of the momentum and of the external force, up to a
second-order remainder. -/
lemma lagR_clusterPert_sub_expansion_ae {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {h : ℝ}
    {γ : ℝ → EN E N} {a b : ℝ} (hac : AbsolutelyContinuousOnInterval γ a b)
    {k : Finset (Fin N)} {w : E} {ψ : ℝ → ℝ} {ν Mψ Md : ℝ} (hν : 0 < ν)
    (hψc : ContDiff ℝ 1 ψ) (hMψ0 : 0 ≤ Mψ) (hMψ : ∀ t, |ψ t| ≤ Mψ)
    (hMd : ∀ t, |deriv ψ t| ≤ Md)
    (hsep : ∀ t ∈ Icc a b, ClusterSeparatedWeak k (γ t) ν) {ε : ℝ}
    (hε4 : 4 * (|ε| * (Mψ * ‖w‖)) ≤ ν) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
      |lagR m h (clusterPert k w ψ γ ε t) (deriv (fun s => clusterPert k w ψ γ ε s) t)
        - lagR m h (γ t) (deriv γ t)
        - ε * (deriv ψ t * inner ℝ (clusterMomentum m k (deriv γ t)) w
            + ψ t * inner ℝ (clusterCrossForceVec m k (γ t)) w)|
      ≤ ε ^ 2 * (Md ^ 2 * (clusterMass m k * ‖w‖ ^ 2) / 2
          + (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
              m p.1 * m p.2) * (32 * Mψ ^ 2 * ‖w‖ ^ 2 / ν ^ 3)) := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  filter_upwards [ae_deriv_clusterPert hac hψc,
    MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t hder hmem
  have htIcc : t ∈ Icc a b := ⟨hmem.1.le, hmem.2⟩
  rw [hder]
  rw [show lagR m h (clusterPert k w ψ γ ε t)
        (deriv γ t + (ε * deriv ψ t) • clusterTransVec k w)
      = kinetic m (deriv γ t + (ε * deriv ψ t) • clusterTransVec k w)
        + U m (clusterPert k w ψ γ ε t) + h from rfl]
  rw [show lagR m h (γ t) (deriv γ t) = kinetic m (deriv γ t) + U m (γ t) + h from rfl]
  -- the kinetic part
  have hK : kinetic m (deriv γ t + (ε * deriv ψ t) • clusterTransVec k w)
      = kinetic m (deriv γ t) + ε * deriv ψ t * inner ℝ (clusterMomentum m k (deriv γ t)) w
        + ε ^ 2 * (deriv ψ t) ^ 2 * (clusterMass m k * ‖w‖ ^ 2) / 2 := by
    rw [kinetic_add, massInner_smul_right, massInner_clusterTransVec,
      kinetic_smul_clusterTransVec]
    ring
  -- the potential part
  have hUt : U m (clusterPert k w ψ γ ε t) - U m (γ t)
      = clusterPotentialRest m k (clusterPert k w ψ γ ε t) - clusterPotentialRest m k (γ t) := by
    rw [U_eq_clusterPotential_add_rest m k (clusterPert k w ψ γ ε t),
      U_eq_clusterPotential_add_rest m k (γ t), clusterPotential_clusterPert]
    ring
  have he : ‖(ε * ψ t) • w‖ = |ε| * |ψ t| * ‖w‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul]
  have hU : |U m (clusterPert k w ψ γ ε t) - U m (γ t)
        - (ε * ψ t) * inner ℝ (clusterCrossForceVec m k (γ t)) w|
      ≤ (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
          m p.1 * m p.2) * (32 * (ε ^ 2 * ψ t ^ 2 * ‖w‖ ^ 2) / ν ^ 3) := by
    have hpert : ∀ j ∈ k, clusterPert k w ψ γ ε t j = γ t j + (ε * ψ t) • w :=
      fun j hj => clusterPert_apply_of_mem hj
    have hclose : ∀ j ∉ k, clusterPert k w ψ γ ε t j = γ t j :=
      fun j hj => clusterPert_apply_of_notMem hj
    have h2e : 2 * ‖(ε * ψ t) • w‖ ≤ ν := by
      rw [he]
      have h2a : |ε| * (|ψ t| * ‖w‖) ≤ |ε| * (Mψ * ‖w‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg ε)
        exact mul_le_mul_of_nonneg_right (hMψ t) (norm_nonneg w)
      have hε4' : 4 * (|ε| * (Mψ * ‖w‖)) ≤ ν := hε4
      linarith
    have hkey := abs_clusterPotentialRest_sub_sub_inner_le (m := m) (fun i => (hm i).le)
      (k := k) (x := γ t) (y := clusterPert k w ψ γ ε t) hν (hsep t htIcc) hclose hpert h2e
    have hinner : inner ℝ (clusterCrossForceVec m k (γ t)) ((ε * ψ t) • w)
        = (ε * ψ t) * inner ℝ (clusterCrossForceVec m k (γ t)) w :=
      real_inner_smul_right _ _ _
    have hnormsq : ‖(ε * ψ t) • w‖ ^ 2 = ε ^ 2 * ψ t ^ 2 * ‖w‖ ^ 2 := by
      rw [he, mul_pow, mul_pow, sq_abs, sq_abs]
    rw [hinner, hnormsq] at hkey
    rw [hUt]
    refine hkey.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro p hp
      simp only [crossPairs, Finset.mem_filter] at hp
      simp only [Finset.mem_filter]
      exact ⟨hp.1, hp.2.1⟩
    · intro p _ _
      exact mul_nonneg (hm p.1).le (hm p.2).le
  -- combine
  have htot : kinetic m (deriv γ t + (ε * deriv ψ t) • clusterTransVec k w)
        + U m (clusterPert k w ψ γ ε t) + h
      - (kinetic m (deriv γ t) + U m (γ t) + h)
      - ε * (deriv ψ t * inner ℝ (clusterMomentum m k (deriv γ t)) w
          + ψ t * inner ℝ (clusterCrossForceVec m k (γ t)) w)
      = (ε ^ 2 * (deriv ψ t) ^ 2 * (clusterMass m k * ‖w‖ ^ 2) / 2)
        + (U m (clusterPert k w ψ γ ε t) - U m (γ t)
            - (ε * ψ t) * inner ℝ (clusterCrossForceVec m k (γ t)) w) := by
    rw [hK]
    ring
  rw [htot]
  have hA : 0 ≤ ε ^ 2 * (deriv ψ t) ^ 2 * (clusterMass m k * ‖w‖ ^ 2) / 2 := by
    have h1 : 0 ≤ clusterMass m k := clusterMass_nonneg (fun i => (hm i).le) k
    have h2 : 0 ≤ ‖w‖ ^ 2 := sq_nonneg _
    positivity
  have hb1' : |ε ^ 2 * (deriv ψ t) ^ 2 * (clusterMass m k * ‖w‖ ^ 2) / 2|
      ≤ ε ^ 2 * (Md ^ 2 * (clusterMass m k * ‖w‖ ^ 2) / 2) := by
    rw [abs_of_nonneg hA]
    have h1 : (deriv ψ t) ^ 2 ≤ Md ^ 2 := by
      have h2 : |deriv ψ t| ≤ Md := hMd t
      calc (deriv ψ t) ^ 2 = |deriv ψ t| ^ 2 := (sq_abs _).symm
        _ ≤ Md ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
    have h3 : 0 ≤ clusterMass m k * ‖w‖ ^ 2 :=
      mul_nonneg (clusterMass_nonneg (fun i => (hm i).le) k) (sq_nonneg _)
    have h4 : 0 ≤ ε ^ 2 := sq_nonneg ε
    have h6 : ε ^ 2 * (deriv ψ t) ^ 2 ≤ ε ^ 2 * Md ^ 2 := mul_le_mul_of_nonneg_left h1 h4
    have h7 : ε ^ 2 * (deriv ψ t) ^ 2 * (clusterMass m k * ‖w‖ ^ 2)
        ≤ ε ^ 2 * Md ^ 2 * (clusterMass m k * ‖w‖ ^ 2) := mul_le_mul_of_nonneg_right h6 h3
    calc ε ^ 2 * (deriv ψ t) ^ 2 * (clusterMass m k * ‖w‖ ^ 2) / 2
        ≤ ε ^ 2 * Md ^ 2 * (clusterMass m k * ‖w‖ ^ 2) / 2 := by linarith
      _ = ε ^ 2 * (Md ^ 2 * (clusterMass m k * ‖w‖ ^ 2) / 2) := by ring
  have hb2 : (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
          m p.1 * m p.2) * (32 * (ε ^ 2 * ψ t ^ 2 * ‖w‖ ^ 2) / ν ^ 3)
      ≤ ε ^ 2 * ((∑ p ∈ (pairFinset N).filter
            (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)), m p.1 * m p.2)
          * (32 * Mψ ^ 2 * ‖w‖ ^ 2 / ν ^ 3)) := by
    have h1 : ψ t ^ 2 ≤ Mψ ^ 2 := by
      calc ψ t ^ 2 = |ψ t| ^ 2 := (sq_abs _).symm
        _ ≤ Mψ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hMψ t) 2
    have h2 : 0 ≤ ∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
        m p.1 * m p.2 :=
      Finset.sum_nonneg fun p _ => mul_nonneg (hm p.1).le (hm p.2).le
    have h3 : 0 ≤ ‖w‖ ^ 2 := sq_nonneg _
    have h4 : 32 * (ε ^ 2 * ψ t ^ 2 * ‖w‖ ^ 2) / ν ^ 3
        ≤ ε ^ 2 * (32 * Mψ ^ 2 * ‖w‖ ^ 2 / ν ^ 3) := by
      have h5 : 32 * (ψ t ^ 2 * ‖w‖ ^ 2) ≤ 32 * (Mψ ^ 2 * ‖w‖ ^ 2) := by
        nlinarith [h1, h3]
      calc 32 * (ε ^ 2 * ψ t ^ 2 * ‖w‖ ^ 2) / ν ^ 3
          = ε ^ 2 * (32 * (ψ t ^ 2 * ‖w‖ ^ 2)) / ν ^ 3 := by ring
        _ ≤ ε ^ 2 * (32 * (Mψ ^ 2 * ‖w‖ ^ 2)) / ν ^ 3 := by
              refine div_le_div_of_nonneg_right ?_ (by positivity)
              exact mul_le_mul_of_nonneg_left h5 (sq_nonneg ε)
        _ = ε ^ 2 * (32 * Mψ ^ 2 * ‖w‖ ^ 2 / ν ^ 3) := by ring
    calc (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
            m p.1 * m p.2) * (32 * (ε ^ 2 * ψ t ^ 2 * ‖w‖ ^ 2) / ν ^ 3)
        ≤ (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
            m p.1 * m p.2) * (ε ^ 2 * (32 * Mψ ^ 2 * ‖w‖ ^ 2 / ν ^ 3)) :=
          mul_le_mul_of_nonneg_left h4 h2
      _ = ε ^ 2 * ((∑ p ∈ (pairFinset N).filter
              (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)), m p.1 * m p.2)
            * (32 * Mψ ^ 2 * ‖w‖ ^ 2 / ν ^ 3)) := by ring
  calc |ε ^ 2 * (deriv ψ t) ^ 2 * (clusterMass m k * ‖w‖ ^ 2) / 2
        + (U m (clusterPert k w ψ γ ε t) - U m (γ t)
            - (ε * ψ t) * inner ℝ (clusterCrossForceVec m k (γ t)) w)|
      ≤ |ε ^ 2 * (deriv ψ t) ^ 2 * (clusterMass m k * ‖w‖ ^ 2) / 2|
        + |U m (clusterPert k w ψ γ ε t) - U m (γ t)
            - (ε * ψ t) * inner ℝ (clusterCrossForceVec m k (γ t)) w| := abs_add_le _ _
    _ ≤ ε ^ 2 * (Md ^ 2 * (clusterMass m k * ‖w‖ ^ 2) / 2)
        + (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
            m p.1 * m p.2) * (32 * (ε ^ 2 * ψ t ^ 2 * ‖w‖ ^ 2) / ν ^ 3) :=
        add_le_add hb1' hU
    _ ≤ ε ^ 2 * (Md ^ 2 * (clusterMass m k * ‖w‖ ^ 2) / 2)
        + ε ^ 2 * ((∑ p ∈ (pairFinset N).filter
              (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)), m p.1 * m p.2)
            * (32 * Mψ ^ 2 * ‖w‖ ^ 2 / ν ^ 3)) := add_le_add le_rfl hb2
    _ = ε ^ 2 * (Md ^ 2 * (clusterMass m k * ‖w‖ ^ 2) / 2
          + (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
              m p.1 * m p.2) * (32 * Mψ ^ 2 * ‖w‖ ^ 2 / ν ^ 3)) := by ring


/-! ## 9. The variation identity -/

/-- **The rigid-translation variation identity.**  For an `h`-minimiser and a cluster which does not
collide with its complement on `[a,b]`, the first variation of the action under a rigid translation
of the cluster vanishes:

  `∫ ψ' · ⟪p_k, w⟫ + ∫ ψ · ⟪F_k, w⟫ = 0`,

where `p_k = ∑_{i∈k} mᵢ γ̇ᵢ` is the momentum of the cluster and `F_k` the external force acting on
it.  The key point is that a rigid translation leaves the internal separations of `k` unchanged, so
the internal potential of `k` contributes nothing to the first variation. -/
theorem cluster_translation_variation {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {h : ℝ} (hh : 0 < h)
    {γ : ℝ → EN E N} {a b : ℝ} (hab : a < b)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hmin : IsHMinimizer m h γ a b) (hfin : actionPot m h (γ a) (γ b) < ⊤)
    {k : Finset (Fin N)} {ν : ℝ} (hν : 0 < ν)
    (hsep : ∀ t ∈ Icc a b, ClusterSeparatedWeak k (γ t) ν)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hψcs : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ Ioo a b) (w : E) :
    (∫ t in a..b, deriv ψ t * inner ℝ (clusterMomentum m k (deriv γ t)) w)
      + ∫ t in a..b, ψ t * inner ℝ (clusterCrossForceVec m k (γ t)) w = 0 := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  have hψc1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  have hdψcont : Continuous (deriv ψ) := hψ.continuous_deriv (by decide)
  obtain ⟨M₀, hM₀⟩ := hψcs.exists_bound_of_continuous hψ.continuous
  obtain ⟨M₁, hM₁⟩ := hψcs.deriv.exists_bound_of_continuous hdψcont
  set Mψ : ℝ := max M₀ 1 with hMψdef
  set Md : ℝ := max M₁ 1 with hMddef
  have hMψ0 : 0 < Mψ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hMd0 : 0 < Md := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hMψnn : 0 ≤ Mψ := hMψ0.le
  have hMdnn : 0 ≤ Md := hMd0.le
  have hMψ : ∀ t, |ψ t| ≤ Mψ := fun t => by
    have h1 := hM₀ t
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (le_max_left _ _)
  have hMd : ∀ t, |deriv ψ t| ≤ Md := fun t => by
    have h1 := hM₁ t
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (le_max_left _ _)
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  set ε₀ : ℝ := ν / (4 * (Mψ * ‖w‖)) with hε₀def
  have hMwpos : 0 < Mψ * ‖w‖ := mul_pos hMψ0 hwpos
  have hMwne : Mψ * ‖w‖ ≠ 0 := ne_of_gt hMwpos
  have hε₀pos : 0 < ε₀ := by
    rw [hε₀def]
    exact div_pos hν (by positivity)
  have hε₀le : ∀ ε : ℝ, |ε| ≤ ε₀ → 4 * (|ε| * (Mψ * ‖w‖)) ≤ ν := by
    intro ε hε
    have h1 : |ε| * (Mψ * ‖w‖) ≤ ε₀ * (Mψ * ‖w‖) :=
      mul_le_mul_of_nonneg_right hε hMwpos.le
    have h2 : ε₀ * (Mψ * ‖w‖) = ν / 4 := by
      rw [hε₀def]
      field_simp
    linarith
  have hcm : 0 ≤ clusterMass m k := clusterMass_nonneg (fun i => (hm i).le) k
  set Cp : ℝ := Md ^ 2 * (clusterMass m k * ‖w‖ ^ 2) / 2
    + (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
        m p.1 * m p.2) * (32 * Mψ ^ 2 * ‖w‖ ^ 2 / ν ^ 3) with hCpdef
  have hCpnn : 0 ≤ Cp := by
    rw [hCpdef]
    refine add_nonneg (by positivity) ?_
    refine mul_nonneg (Finset.sum_nonneg fun p _ => mul_nonneg (hm p.1).le (hm p.2).le) ?_
    positivity
  set J : ℝ := (∫ t in a..b, deriv ψ t * inner ℝ (clusterMomentum m k (deriv γ t)) w)
      + ∫ t in a..b, ψ t * inner ℝ (clusterCrossForceVec m k (γ t)) w with hJdef
  have hm0 : ∀ i, 0 ≤ m i := fun i => (hm i).le
  have hh0 : 0 ≤ h := hh.le
  have hmin' : actionOn m h γ a b = actionPot m h (γ a) (γ b) := hmin
  have hOn : actionOn m h γ a b < ⊤ := by rw [hmin']; exact hfin
  have hncγ : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), WithoutCollisions (γ t) :=
    ae_withoutCollisions_of_actionOn_lt_top hac hOn
  have hderγ : IntegrableOn (deriv γ) (Set.Ioc a b) volume :=
    (Commons.MeasureTheory.Integral.intervalIntegrable_deriv_of_absolutelyContinuousOnInterval
      (f := γ) (a := a) (b := b) hac).1
  have hproj : ∀ i : Fin N, IntegrableOn (fun t => (deriv γ t).ofLp i) (Set.Ioc a b) volume :=
    fun i => (PiLp.proj (𝕜 := ℝ) (2 : ℝ≥0∞) (fun _ : Fin N => E) i).integrableOn_comp hderγ
  have hmom : IntegrableOn (fun t => clusterMomentum m k (deriv γ t)) (Set.Ioc a b) volume := by
    have h1 : Integrable (fun t => ∑ i ∈ k, m i • (deriv γ t).ofLp i)
        (volume.restrict (Set.Ioc a b)) :=
      integrable_finsetSum k fun i _ => (hproj i).smul (m i)
    exact h1
  have hinner : IntegrableOn (fun t => inner ℝ (clusterMomentum m k (deriv γ t)) w)
      (Set.Ioc a b) volume := by
    have h1 : IntegrableOn ((innerSL ℝ w) ∘ fun t => clusterMomentum m k (deriv γ t))
        (Set.Ioc a b) volume := (innerSL ℝ w).integrableOn_comp hmom
    refine h1.congr_fun ?_ measurableSet_Ioc
    intro t _
    simp only [Function.comp_apply, innerSL_apply_apply]
    rw [real_inner_comm]
  have hIa : IntegrableOn (fun t => deriv ψ t * inner ℝ (clusterMomentum m k (deriv γ t)) w)
      (Set.Ioc a b) volume := by
    have h1 : IntervalIntegrable
        (fun t => inner ℝ (clusterMomentum m k (deriv γ t)) w * deriv ψ t) volume a b :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mpr hinner).mul_continuousOn
        hdψcont.continuousOn
    refine ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mp h1).congr_fun ?_
      measurableSet_Ioc
    intro t _
    ring
  have hγcont : ContinuousOn γ (Set.uIcc a b) := hac.continuousOn
  have hFcont : ContinuousOn (fun t => clusterCrossForceVec m k (γ t)) (Set.uIcc a b) :=
    (continuousOn_clusterCrossForceVec (m := m) (k := k) hν).comp hγcont
      (fun t ht => hsep t (by rwa [Set.uIcc_of_le hab.le] at ht))
  have hbcont : ContinuousOn (fun t => ψ t * inner ℝ (clusterCrossForceVec m k (γ t)) w)
      (Set.uIcc a b) :=
    hψ.continuous.continuousOn.mul (hFcont.inner continuousOn_const)
  have hIb : IntegrableOn (fun t => ψ t * inner ℝ (clusterCrossForceVec m k (γ t)) w)
      (Set.Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mp hbcont.intervalIntegrable
  -- the two-sided estimate
  have hAux : ∀ η : ℝ, 0 < |η| → |η| ≤ ε₀ →
      (0 ≤ (∫ t in Set.Ioc a b, lagR m h (clusterPert k w ψ γ η t)
                (deriv (fun s => clusterPert k w ψ γ η s) t))
             - ∫ t in Set.Ioc a b, lagR m h (γ t) (deriv γ t))
      ∧ |(∫ t in Set.Ioc a b, lagR m h (clusterPert k w ψ γ η t)
                (deriv (fun s => clusterPert k w ψ γ η s) t))
             - (∫ t in Set.Ioc a b, lagR m h (γ t) (deriv γ t))
          - η * J| ≤ η ^ 2 * ((b - a) * Cp) := by
    intro η hηpos hηle
    have hη4 : 4 * (|η| * (Mψ * ‖w‖)) ≤ ν := hε₀le η hηle
    have hρnn : 0 ≤ |η| * (Mψ * ‖w‖) := by positivity
    have hacη : AbsolutelyContinuousOnInterval (fun t => clusterPert k w ψ γ η t) a b :=
      absolutelyContinuousOnInterval_clusterPert hac hψc1
    have hncη : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
        WithoutCollisions (clusterPert k w ψ γ η t) := by
      filter_upwards [hncγ, MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht hmem
      exact withoutCollisions_clusterPert hν hMψ (by linarith) (hsep t ⟨hmem.1.le, hmem.2⟩) ht
    have hfinη : actionOn m h (fun t => clusterPert k w ψ γ η t) a b < ⊤ :=
      actionOn_clusterPert_lt_top hm hh0 hab.le hac hncγ hOn hν hψc1 hMψnn hMψ hMd hsep hη4
    have hbrγ : actionOn m h γ a b
        = ENNReal.ofReal (∫ t in a..b, lagR m h (γ t) (deriv γ t)) :=
      actionOn_eq_ofReal_integral_lagR_of_ae hab.le hm0 hh0 hac hncγ hOn
    have hbrη : actionOn m h (fun t => clusterPert k w ψ γ η t) a b
        = ENNReal.ofReal (∫ t in a..b, lagR m h (clusterPert k w ψ γ η t)
            (deriv (fun s => clusterPert k w ψ γ η s) t)) :=
      actionOn_eq_ofReal_integral_lagR_of_ae hab.le hm0 hh0 hacη hncη hfinη
    have hminη : actionPot m h (γ a) (γ b)
        ≤ actionOn m h (fun t => clusterPert k w ψ γ η t) a b :=
      actionPot_le_of_interval (m := m) (h := h) (x := γ a) (y := γ b) hab
        (clusterPert_eq_left_of_tsupport_subset hts)
        (clusterPert_eq_right_of_tsupport_subset hts) hacη
    have hLΓnn : ∀ t, 0 ≤ lagR m h (clusterPert k w ψ γ η t)
        (deriv (fun s => clusterPert k w ψ γ η s) t) := by
      intro t
      rw [show lagR m h (clusterPert k w ψ γ η t)
            (deriv (fun s => clusterPert k w ψ γ η s) t)
          = kinetic m (deriv (fun s => clusterPert k w ψ γ η s) t)
            + U m (clusterPert k w ψ γ η t) + h from rfl]
      have h1 := kinetic_nonneg m hm0 (deriv (fun s => clusterPert k w ψ γ η s) t)
      have h2 := U_nonneg hm0 (clusterPert k w ψ γ η t)
      linarith
    have hIntF : Integrable (fun t => lagR m h (clusterPert k w ψ γ η t)
        (deriv (fun s => clusterPert k w ψ γ η s) t))
        (volume.restrict (Set.Ioc a b)) :=
      integrable_lagR_of_actionOn_lt_top_of_ae hm0 hh0 hacη hncη hfinη
    have hIntG : Integrable (fun t => lagR m h (γ t) (deriv γ t))
        (volume.restrict (Set.Ioc a b)) :=
      integrable_lagR_of_actionOn_lt_top_of_ae hm0 hh0 hac hncγ hOn
    have hgeI : (∫ t in a..b, lagR m h (γ t) (deriv γ t))
        ≤ ∫ t in a..b, lagR m h (clusterPert k w ψ γ η t)
            (deriv (fun s => clusterPert k w ψ γ η s) t) := by
      have h1 : ENNReal.ofReal (∫ t in a..b, lagR m h (γ t) (deriv γ t))
          ≤ ENNReal.ofReal (∫ t in a..b, lagR m h (clusterPert k w ψ γ η t)
              (deriv (fun s => clusterPert k w ψ γ η s) t)) := by
        rw [← hmin', hbrγ, hbrη] at hminη
        exact hminη
      have hz : 0 ≤ ∫ t in a..b, lagR m h (clusterPert k w ψ γ η t)
          (deriv (fun s => clusterPert k w ψ γ η s) t) := by
        rw [intervalIntegral.integral_of_le hab.le]
        exact setIntegral_nonneg measurableSet_Ioc fun t _ => hLΓnn t
      exact (ENNReal.ofReal_le_ofReal_iff hz).mp h1
    have hpt : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
        |lagR m h (clusterPert k w ψ γ η t)
            (deriv (fun s => clusterPert k w ψ γ η s) t) - lagR m h (γ t) (deriv γ t)
          - η * (deriv ψ t * inner ℝ (clusterMomentum m k (deriv γ t)) w
              + ψ t * inner ℝ (clusterCrossForceVec m k (γ t)) w)|
        ≤ η ^ 2 * Cp := by
      have h := lagR_clusterPert_sub_expansion_ae (m := m) (h := h) hm hac hν hψc1 hMψnn hMψ hMd
        hsep hη4
      filter_upwards [h] with t ht
      rw [hCpdef]
      exact ht
    have hIηg : Integrable (fun t => η * (deriv ψ t
        * inner ℝ (clusterMomentum m k (deriv γ t)) w
          + ψ t * inner ℝ (clusterCrossForceVec m k (γ t)) w))
        (volume.restrict (Set.Ioc a b)) := (hIa.add hIb).const_mul η
    have hIabs : Integrable (fun t => |lagR m h (clusterPert k w ψ γ η t)
            (deriv (fun s => clusterPert k w ψ γ η s) t) - lagR m h (γ t) (deriv γ t)
          - η * (deriv ψ t * inner ℝ (clusterMomentum m k (deriv γ t)) w
              + ψ t * inner ℝ (clusterCrossForceVec m k (γ t)) w)|)
        (volume.restrict (Set.Ioc a b)) :=
      ((hIntF.sub hIntG).sub hIηg).abs
    have hmono : (∫ t in Set.Ioc a b, |lagR m h (clusterPert k w ψ γ η t)
            (deriv (fun s => clusterPert k w ψ γ η s) t) - lagR m h (γ t) (deriv γ t)
          - η * (deriv ψ t * inner ℝ (clusterMomentum m k (deriv γ t)) w
              + ψ t * inner ℝ (clusterCrossForceVec m k (γ t)) w)|)
        ≤ ∫ t in Set.Ioc a b, η ^ 2 * Cp :=
      integral_mono_ae hIabs (integrable_const _) hpt
    have hconstval : (∫ t in Set.Ioc a b, η ^ 2 * Cp) = η ^ 2 * ((b - a) * Cp) := by
      rw [setIntegral_const, smul_eq_mul, Measure.real_def, Real.volume_Ioc,
        ENNReal.toReal_ofReal (by linarith)]
      ring
    have hJ1 : (∫ t in a..b, deriv ψ t * inner ℝ (clusterMomentum m k (deriv γ t)) w)
        = ∫ t in Set.Ioc a b, deriv ψ t * inner ℝ (clusterMomentum m k (deriv γ t)) w :=
      intervalIntegral.integral_of_le hab.le
    have hJ2 : (∫ t in a..b, ψ t * inner ℝ (clusterCrossForceVec m k (γ t)) w)
        = ∫ t in Set.Ioc a b, ψ t * inner ℝ (clusterCrossForceVec m k (γ t)) w :=
      intervalIntegral.integral_of_le hab.le
    have hJ3 : J = ∫ t in Set.Ioc a b, (deriv ψ t
          * inner ℝ (clusterMomentum m k (deriv γ t)) w
        + ψ t * inner ℝ (clusterCrossForceVec m k (γ t)) w) := by
      rw [hJdef, hJ1, hJ2]
      exact (integral_add hIa hIb).symm
    have e1 : (∫ t in Set.Ioc a b, lagR m h (clusterPert k w ψ γ η t)
          (deriv (fun s => clusterPert k w ψ γ η s) t))
        - (∫ t in Set.Ioc a b, lagR m h (γ t) (deriv γ t))
        = ∫ t in Set.Ioc a b, (lagR m h (clusterPert k w ψ γ η t)
            (deriv (fun s => clusterPert k w ψ γ η s) t)
            - lagR m h (γ t) (deriv γ t)) := (integral_sub hIntF hIntG).symm
    have e3 : η * (∫ t in Set.Ioc a b, (deriv ψ t
          * inner ℝ (clusterMomentum m k (deriv γ t)) w
        + ψ t * inner ℝ (clusterCrossForceVec m k (γ t)) w))
        = ∫ t in Set.Ioc a b, η * (deriv ψ t
            * inner ℝ (clusterMomentum m k (deriv γ t)) w
          + ψ t * inner ℝ (clusterCrossForceVec m k (γ t)) w) :=
      (integral_const_mul η (fun t => deriv ψ t
        * inner ℝ (clusterMomentum m k (deriv γ t)) w
        + ψ t * inner ℝ (clusterCrossForceVec m k (γ t)) w)).symm
    have e4 : (∫ t in Set.Ioc a b, (lagR m h (clusterPert k w ψ γ η t)
            (deriv (fun s => clusterPert k w ψ γ η s) t) - lagR m h (γ t) (deriv γ t)))
        - (∫ t in Set.Ioc a b, η * (deriv ψ t
            * inner ℝ (clusterMomentum m k (deriv γ t)) w
          + ψ t * inner ℝ (clusterCrossForceVec m k (γ t)) w))
        = ∫ t in Set.Ioc a b, ((lagR m h (clusterPert k w ψ γ η t)
            (deriv (fun s => clusterPert k w ψ γ η s) t) - lagR m h (γ t) (deriv γ t))
          - η * (deriv ψ t * inner ℝ (clusterMomentum m k (deriv γ t)) w
              + ψ t * inner ℝ (clusterCrossForceVec m k (γ t)) w)) :=
      (integral_sub (hIntF.sub hIntG) hIηg).symm
    refine ⟨?_, ?_⟩
    · have hge1 : (∫ t in a..b, lagR m h (γ t) (deriv γ t))
          = ∫ t in Set.Ioc a b, lagR m h (γ t) (deriv γ t) :=
        intervalIntegral.integral_of_le hab.le
      have hge2 : (∫ t in a..b, lagR m h (clusterPert k w ψ γ η t)
            (deriv (fun s => clusterPert k w ψ γ η s) t))
          = ∫ t in Set.Ioc a b, lagR m h (clusterPert k w ψ γ η t)
              (deriv (fun s => clusterPert k w ψ γ η s) t) :=
        intervalIntegral.integral_of_le hab.le
      rw [hge1, hge2] at hgeI
      linarith
    · rw [e1, hJ3, e3, e4]
      refine (abs_integral_le_integral_abs).trans ?_
      exact hmono.trans (le_of_eq hconstval)
  have hkey : ∀ η : ℝ, 0 < |η| → |η| ≤ ε₀ → |η * J| ≤ η ^ 2 * ((b - a) * Cp) := by
    intro η hηpos hηle
    obtain ⟨hDnn, hDb⟩ := hAux η hηpos hηle
    obtain ⟨hDnn', hDb'⟩ := hAux (-η) (by rwa [abs_neg]) (by rwa [abs_neg])
    have h2 : (-η) ^ 2 * ((b - a) * Cp) = η ^ 2 * ((b - a) * Cp) := by ring
    rw [h2] at hDb'
    obtain ⟨hlo, hhi⟩ := abs_le.mp hDb
    obtain ⟨hlo', hhi'⟩ := abs_le.mp hDb'
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith
    · linarith
  have hJ0 : |J| ≤ 0 := by
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have hBnn : 0 ≤ (b - a) * Cp := mul_nonneg (by linarith) hCpnn
    set η : ℝ := min (ε₀ / 2) (δ / (2 * ((b - a) * Cp + 1))) with hηdef
    have hηpos : 0 < η := lt_min (by linarith) (by positivity)
    have hηle : η ≤ ε₀ := le_trans (min_le_left _ _) (by linarith)
    have h1 := hkey η (abs_pos.mpr (ne_of_gt hηpos)) (by rwa [abs_of_pos hηpos])
    rw [abs_mul, abs_of_pos hηpos] at h1
    have h2 : |J| ≤ η * ((b - a) * Cp) := by
      have h3 : η * |J| ≤ η * (η * ((b - a) * Cp)) := by
        calc η * |J| ≤ η ^ 2 * ((b - a) * Cp) := h1
          _ = η * (η * ((b - a) * Cp)) := by ring
      exact le_of_mul_le_mul_left h3 hηpos
    have h4 : η * ((b - a) * Cp) ≤ δ := by
      have h5 : 0 < 2 * ((b - a) * Cp + 1) := by positivity
      have h6 : η * ((b - a) * Cp)
          ≤ (δ / (2 * ((b - a) * Cp + 1))) * ((b - a) * Cp) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hBnn
      refine h6.trans ?_
      rw [div_mul_eq_mul_div, div_le_iff₀ h5]
      nlinarith [hδ.le, hBnn]
    linarith [h2.trans h4]
  have hJz : J = 0 := abs_eq_zero.mp (le_antisymm hJ0 (abs_nonneg J))
  rw [hJdef] at hJz
  exact hJz

/-! ## 10. Boundedness of the momentum of a separated cluster -/

/-- The momentum of a cluster, as a continuous linear map. -/
noncomputable def clusterMomentumCLM (m : Fin N → ℝ) (k : Finset (Fin N)) : EN E N →L[ℝ] E :=
  ∑ i ∈ k, (m i) • (PiLp.proj (𝕜 := ℝ) (2 : ℝ≥0∞) (fun _ : Fin N => E) i)

lemma clusterMomentumCLM_apply (m : Fin N → ℝ) (k : Finset (Fin N)) (v : EN E N) :
    clusterMomentumCLM m k v = clusterMomentum m k v := by
  rw [clusterMomentumCLM, clusterMomentum]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, PiLp.proj_apply]

lemma continuousAt_clusterMomentum {m : Fin N → ℝ} {k : Finset (Fin N)} {v : ℝ → EN E N} {t : ℝ}
    (h : ContinuousAt v t) : ContinuousAt (fun s => clusterMomentum m k (v s)) t := by
  have h1 : ContinuousAt (fun s => clusterMomentumCLM m k (v s)) t :=
    (clusterMomentumCLM m k).continuous.continuousAt.comp h
  exact h1.congr (Eventually.of_forall fun s => clusterMomentumCLM_apply m k (v s))

/-- The momentum of a cluster along an absolutely continuous curve is locally integrable on the
interior of the interval. -/
lemma locallyIntegrableOn_clusterMomentum_deriv {m : Fin N → ℝ} {k : Finset (Fin N)}
    {γ : ℝ → EN E N} {a b : ℝ} (hac : AbsolutelyContinuousOnInterval γ a b) :
    LocallyIntegrableOn (fun t => clusterMomentum m k (deriv γ t)) (Set.Ioo a b) volume := by
  have hder : IntegrableOn (deriv γ) (Set.Ioc a b) volume :=
    (Commons.MeasureTheory.Integral.intervalIntegrable_deriv_of_absolutelyContinuousOnInterval
      (f := γ) (a := a) (b := b) hac).1
  have h1 : LocallyIntegrableOn (deriv γ) (Set.Ioc a b) volume := hder.locallyIntegrableOn
  have h2 : LocallyIntegrableOn ((clusterMomentumCLM m k) ∘ deriv γ) (Set.Ioc a b) volume :=
    (clusterMomentumCLM m k).locallyIntegrableOn_comp h1
  refine (h2.mono_set Set.Ioo_subset_Ioc_self).congr ?_
  filter_upwards with t
  rw [Function.comp_apply, clusterMomentumCLM_apply]

/-- **Boundedness of the momentum of a separated cluster.**  If `γ` is an `h`-minimiser on `[a,b]`
and the cluster `k` stays `ν`-separated from its complement on `[a,b]`, then the momentum
`p_k = ∑_{i∈k} mᵢ γ̇ᵢ` is bounded at every collision-free interior point.  This is the first
variation of the action under a rigid translation of `k`, integrated via the du Bois--Reymond
lemma. -/
theorem exists_norm_clusterMomentum_le {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {h : ℝ} (hh : 0 < h)
    {γ : ℝ → EN E N} {a b : ℝ} (hab : a < b)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hmin : IsHMinimizer m h γ a b) (hfin : ∀ x y : EN E N, actionPot m h x y < ⊤)
    {k : Finset (Fin N)} {ν : ℝ} (hν : 0 < ν)
    (hsep : ∀ t ∈ Icc a b, ClusterSeparatedWeak k (γ t) ν) :
    ∃ C : ℝ, ∀ t ∈ Ioo a b, WithoutCollisions (γ t) →
      ‖clusterMomentum m k (deriv γ t)‖ ≤ C := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  have hsep' : ∀ t ∈ Set.uIcc a b, ClusterSeparatedWeak k (γ t) ν := by
    intro t ht
    exact hsep t (by rwa [Set.uIcc_of_le hab.le] at ht)
  have hgU : ContinuousOn (fun t => clusterCrossForceVec m k (γ t)) (Set.uIcc a b) :=
    (continuousOn_clusterCrossForceVec (m := m) (k := k) hν).comp hac.continuousOn hsep'
  have hgI : ContinuousOn (fun t => clusterCrossForceVec m k (γ t)) (Set.Icc a b) := by
    rwa [Set.uIcc_of_le hab.le] at hgU
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hgI
  obtain ⟨c, hc⟩ :=
    Commons.Analysis.Calculus.ae_eq_add_intervalIntegral_of_forall_integral_inner_deriv_add_eq_zero_smooth
      (f := fun t => clusterMomentum m k (deriv γ t))
      (g := fun t => clusterCrossForceVec m k (γ t)) hab
      (locallyIntegrableOn_clusterMomentum_deriv hac) hgI (fun ψ w hψ hψcs hts => by
        have hts1 : tsupport (fun t => deriv ψ t
            * inner ℝ (clusterMomentum m k (deriv γ t)) w) ⊆ Set.Ioo a b := by
          have h1 : (fun t => deriv ψ t * inner ℝ (clusterMomentum m k (deriv γ t)) w)
              = (deriv ψ) * (fun t => inner ℝ (clusterMomentum m k (deriv γ t)) w) := by
            funext t; rw [Pi.mul_apply]
          rw [h1]
          exact tsupport_mul_subset_left.trans (tsupport_deriv_subset.trans hts)
        have hts2 : tsupport (fun t => ψ t
            * inner ℝ (clusterCrossForceVec m k (γ t)) w) ⊆ Set.Ioo a b := by
          have h1 : (fun t => ψ t * inner ℝ (clusterCrossForceVec m k (γ t)) w)
              = ψ * (fun t => inner ℝ (clusterCrossForceVec m k (γ t)) w) := by
            funext t; rw [Pi.mul_apply]
          rw [h1]
          exact tsupport_mul_subset_left.trans hts
        have e1 : MeasureTheory.integral volume
              (fun t => deriv ψ t * inner ℝ (clusterMomentum m k (deriv γ t)) w)
            = ∫ t in a..b, deriv ψ t * inner ℝ (clusterMomentum m k (deriv γ t)) w :=
          (Commons.MeasureTheory.Integral.intervalIntegral_eq_integral_of_tsupport_subset
            hab.le hts1).symm
        have e2 : MeasureTheory.integral volume
              (fun t => ψ t * inner ℝ (clusterCrossForceVec m k (γ t)) w)
            = ∫ t in a..b, ψ t * inner ℝ (clusterCrossForceVec m k (γ t)) w :=
          (Commons.MeasureTheory.Integral.intervalIntegral_eq_integral_of_tsupport_subset
            hab.le hts2).symm
        rw [e1, e2]
        exact cluster_translation_variation hm hh hab hac hmin (hfin (γ a) (γ b)) hν hsep
          hψ hψcs hts w)
  have hMnn : 0 ≤ M := (norm_nonneg _).trans (hM a ⟨le_rfl, hab.le⟩)
  refine ⟨‖c‖ + M * (b - a), fun t ht hnc => ?_⟩
  -- an open neighbourhood of `t` on which `γ` is collision free and inside `(a,b)`
  have hnc_open : IsOpen {x : EN E N | WithoutCollisions x} := by
    simpa [Set.compl_ofPred] using isClosed_collisions.isOpen_compl
  have hγc : ContinuousAt γ t := by
    refine hac.continuousOn.continuousAt ?_
    rw [Set.uIcc_of_le hab.le]
    exact Icc_mem_nhds ht.1 ht.2
  have hnbd : {s : ℝ | s ∈ Set.Ioo a b ∧ WithoutCollisions (γ s)} ∈ 𝓝 t :=
    inter_mem (Ioo_mem_nhds ht.1 ht.2)
      (hγc.preimage_mem_nhds (hnc_open.mem_nhds hnc))
  obtain ⟨U, hUsub, hUopen, htU⟩ := _root_.mem_nhds_iff.mp hnbd
  have hUae : (fun s => clusterMomentum m k (deriv γ s)) =ᵐ[volume.restrict U]
      (fun s => c + ∫ x in a..s, clusterCrossForceVec m k (γ x)) :=
    ae_restrict_of_ae_restrict_of_subset (fun s hs => (hUsub hs).1) hc
  have hsol := exists_solution_data_of_minimizer (m := m) (h := h) hm hh hab hac hmin hfin
    (S := {s : ℝ | s ∈ Set.Ioo a b ∧ WithoutCollisions (γ s)}) (fun s hs => hs.1)
    (fun s hs => hs.2)
  have hfcont : ContinuousOn (fun s => clusterMomentum m k (deriv γ s)) U := by
    intro s hs
    have hd : ContinuousAt (deriv γ) s :=
      ((hsol s ⟨(hUsub hs).1, (hUsub hs).2⟩).2.1).continuousAt
    exact (continuousAt_clusterMomentum hd).continuousWithinAt
  have hg'cont : ContinuousOn (fun s => c + ∫ x in a..s, clusterCrossForceVec m k (γ x)) U := by
    intro s hs
    have hsI : s ∈ Set.Ioo a b := (hUsub hs).1
    have hsub : Set.uIcc a s ⊆ Set.uIcc a b := by
      rw [Set.uIcc_of_le hsI.1.le, Set.uIcc_of_le hab.le]
      exact Set.Icc_subset_Icc le_rfl hsI.2.le
    have hii : IntervalIntegrable (fun x => clusterCrossForceVec m k (γ x)) volume a s :=
      (hgU.mono hsub).intervalIntegrable
    have hcG : ContinuousAt (fun x => clusterCrossForceVec m k (γ x)) s :=
      hgI.continuousAt (Icc_mem_nhds hsI.1 hsI.2)
    have hsm : StronglyMeasurableAtFilter (fun x => clusterCrossForceVec m k (γ x))
        (𝓝 s) volume :=
      (hgI.mono Set.Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo s hsI
    have hder : HasDerivAt (fun u => ∫ x in a..u, clusterCrossForceVec m k (γ x))
        (clusterCrossForceVec m k (γ s)) s :=
      intervalIntegral.integral_hasDerivAt_right hii hsm hcG
    exact (hder.continuousAt.const_add c).continuousWithinAt
  have heq : clusterMomentum m k (deriv γ t) = c + ∫ x in a..t, clusterCrossForceVec m k (γ x) :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq hUae hUopen hfcont hg'cont htU
  have hbound : ‖∫ x in a..t, clusterCrossForceVec m k (γ x)‖ ≤ M * (b - a) := by
    have h1 : ‖∫ x in a..t, clusterCrossForceVec m k (γ x)‖ ≤ M * |t - a| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (C := M) fun x hx => by
        refine hM x ?_
        rw [Set.uIoc_of_le ht.1.le] at hx
        exact ⟨hx.1.le, hx.2.trans ht.2.le⟩
    have h2 : |t - a| ≤ b - a := by
      rw [abs_of_nonneg (by linarith [ht.1])]
      linarith [ht.1, ht.2]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hMnn)
  calc ‖clusterMomentum m k (deriv γ t)‖
      = ‖c + ∫ x in a..t, clusterCrossForceVec m k (γ x)‖ := by rw [heq]
    _ ≤ ‖c‖ + ‖∫ x in a..t, clusterCrossForceVec m k (γ x)‖ := norm_add_le _ _
    _ ≤ ‖c‖ + M * (b - a) := add_le_add le_rfl hbound

end Submission.NBody
