import Submission.NBody.MarchalForce
import Submission.NBody.Virial
import Submission.NBody.Scaling
import Submission.NBody.EulerLagrange

/-!
# Central configurations of a cluster

A *central configuration* of the cluster `k` is a critical point of the cluster potential `U_k`
restricted to a level set of the inertia `I_k`.  Equivalently (Ferrario--Terracini,
`eq:cent_conf`) there is `c ∈ ℝ` with `(∇ₘ U_k)(x)ᵢ = c xᵢ` for every `i`, where `∇ₘ` is the
mass-gradient `ChallengeDeps.weightedGrad`.

We set up the definition, the componentwise formula for the mass-gradient of `U_k` (inside and
outside the cluster), its behaviour under scaling, and the Euler identity
`⟪∇ₘU_k(x), x⟫ₘ = -U_k(x)`.

The key device is that `U_k` is `U` computed with the *truncated masses* `mk j = if j ∈ k then m j
else 0`.  The only collision-freeness needed for the gradient formulas is *inside* the cluster;
this matters because we shall evaluate the formula at `q = x - x_{cm,k}` and at `s = q/√I_k`,
whose coordinates *outside* `k` all vanish and hence collide.

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

/-- The mass vector truncated to the cluster `k`. -/
noncomputable def clusterIndicatorMass (m : Fin N → ℝ) (k : Finset (Fin N)) : Fin N → ℝ :=
  fun j => if j ∈ k then m j else 0

lemma clusterIndicatorMass_of_mem {m : Fin N → ℝ} {k : Finset (Fin N)} {j : Fin N}
    (hj : j ∈ k) : clusterIndicatorMass m k j = m j := by
  simp [clusterIndicatorMass, hj]

lemma clusterIndicatorMass_of_notMem {m : Fin N → ℝ} {k : Finset (Fin N)} {j : Fin N}
    (hj : j ∉ k) : clusterIndicatorMass m k j = 0 := by
  simp [clusterIndicatorMass, hj]

/-- The cluster potential is the full Newtonian potential computed with the truncated masses. -/
lemma U_clusterIndicatorMass (m : Fin N → ℝ) (k : Finset (Fin N)) (x : EN E N) :
    U (clusterIndicatorMass m k) x = clusterPotential m k x := by
  rw [U_eq_pairFinset, clusterPotential, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : p.1 ∈ k ∧ p.2 ∈ k
  · rw [if_pos h, clusterIndicatorMass_of_mem h.1, clusterIndicatorMass_of_mem h.2]
  · rw [if_neg h]
    rcases not_and_or.mp h with h1 | h2
    · rw [clusterIndicatorMass_of_notMem h1, zero_mul, zero_mul]
    · rw [clusterIndicatorMass_of_notMem h2, mul_zero, zero_mul]

lemma clusterPotential_eq_U (m : Fin N → ℝ) (k : Finset (Fin N)) :
    (clusterPotential m k : EN E N → ℝ) = U (clusterIndicatorMass m k) := by
  funext x
  exact (U_clusterIndicatorMass m k x).symm

/-- The mass-gradient of the cluster potential. -/
noncomputable def clusterGrad (m : Fin N → ℝ) (k : Finset (Fin N)) (x : EN E N) : EN E N :=
  weightedGrad m (clusterPotential m k) x

/-- `x` is a *central configuration* of the cluster `k` if `∇ₘU_k(x) = c x` for some `c`. -/
def IsCentralConfig (m : Fin N → ℝ) (k : Finset (Fin N)) (x : EN E N) : Prop :=
  ∃ c : ℝ, clusterGrad m k x = c • x

/-- The derivative of the cluster potential at a configuration that is collision-free *inside the
cluster* (the outside coordinates are irrelevant). -/
lemma hasFDerivAt_clusterPotential (m : Fin N → ℝ) (k : Finset (Fin N)) (x : EN E N)
    (hkk : ∀ i ∈ k, ∀ j ∈ k, i ≠ j → x i ≠ x j) :
    HasFDerivAt (clusterPotential m k)
      (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => p.1 ∈ k ∧ p.2 ∈ k),
        (m p.1 * m p.2) • (-((‖x p.1 - x p.2‖ ^ 3)⁻¹) •
          ((innerSL ℝ (x p.1 - x p.2)).comp (pairMap p.1 p.2)))) x := by
  classical
  have hterm : ∀ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => p.1 ∈ k ∧ p.2 ∈ k),
      HasFDerivAt (fun y : EN E N => m p.1 * m p.2 * (r y p.1 p.2)⁻¹)
        ((m p.1 * m p.2) • (-((‖x p.1 - x p.2‖ ^ 3)⁻¹) •
          ((innerSL ℝ (x p.1 - x p.2)).comp (pairMap p.1 p.2)))) x := by
    intro p hp
    have hmem := (Finset.mem_filter.mp hp).2
    have hlt : p.1 < p.2 := by
      have := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
      simpa [pairFinset] using this
    refine hasFDerivAt_U_pair_term m p.1 p.2 x ?_
    rw [r_eq_norm_sub, norm_ne_zero_iff]
    exact sub_ne_zero.mpr (hkk p.1 hmem.1 p.2 hmem.2 (ne_of_lt hlt))
  have hsum : HasFDerivAt
      (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => p.1 ∈ k ∧ p.2 ∈ k),
        (fun y : EN E N => m p.1 * m p.2 * (r y p.1 p.2)⁻¹))
      (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => p.1 ∈ k ∧ p.2 ∈ k),
        (m p.1 * m p.2) • (-((‖x p.1 - x p.2‖ ^ 3)⁻¹) •
          ((innerSL ℝ (x p.1 - x p.2)).comp (pairMap p.1 p.2)))) x :=
    HasFDerivAt.sum hterm
  have hfeq : clusterPotential m k = (∑ p ∈ (pairFinset N).filter
      (fun p : Fin N × Fin N => p.1 ∈ k ∧ p.2 ∈ k),
        (fun y : EN E N => m p.1 * m p.2 * (r y p.1 p.2)⁻¹)) := by
    funext y
    rw [Finset.sum_apply, clusterPotential]
  rw [hfeq]
  exact hsum

lemma fderiv_clusterPotential_apply (m : Fin N → ℝ) (k : Finset (Fin N)) (x d : EN E N)
    (hkk : ∀ i ∈ k, ∀ j ∈ k, i ≠ j → x i ≠ x j) :
    (fderiv ℝ (clusterPotential m k) x) d
      = ∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => p.1 ∈ k ∧ p.2 ∈ k),
          m p.1 * m p.2 * (-((‖x p.1 - x p.2‖ ^ 3)⁻¹) *
            inner ℝ (x p.1 - x p.2) (d p.1 - d p.2)) := by
  have hf := (hasFDerivAt_clusterPotential m k x hkk).fderiv
  rw [hf]
  let ev : (EN E N →L[ℝ] ℝ) →+ ℝ :=
    { toFun := fun (φ : EN E N →L[ℝ] ℝ) => φ d
      map_zero' := by simp
      map_add' := by intro f g; rfl }
  change ev (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => p.1 ∈ k ∧ p.2 ∈ k),
      ((m p.1 * m p.2) • (-((‖x p.1 - x p.2‖ ^ 3)⁻¹) •
        ((innerSL ℝ (x p.1 - x p.2)).comp (pairMap p.1 p.2))))) =
      ∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => p.1 ∈ k ∧ p.2 ∈ k),
          m p.1 * m p.2 * (-((‖x p.1 - x p.2‖ ^ 3)⁻¹) *
            inner ℝ (x p.1 - x p.2) (d p.1 - d p.2))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro p hp
  dsimp [ev]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  rw [pairMap_apply d p.1 p.2]
  rfl


lemma gradient_clusterPotential_apply_of_mem {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N}
    (hkk : ∀ i ∈ k, ∀ j ∈ k, i ≠ j → x i ≠ x j) {i : Fin N} (hi : i ∈ k) :
    (gradient (clusterPotential m k) x) i
      = ∑ j ∈ k.erase i, (m i * m j * (‖x j - x i‖ ^ 3)⁻¹) • (x j - x i) := by
  classical
  apply (toDual ℝ E).injective
  ext v
  change inner ℝ ((gradient (clusterPotential m k) x) i) v
    = inner ℝ (∑ j ∈ k.erase i, (m i * m j * (‖x j - x i‖ ^ 3)⁻¹) • (x j - x i)) v
  have h1 : inner ℝ ((gradient (clusterPotential m k) x) i) v
      = (fderiv ℝ (clusterPotential m k) x) (singleBodyVec i v) := by
    rw [← inner_singleBody (gradient (clusterPotential m k) x) i v, inner_gradient_eq_fderiv]
  have h2 : fderiv ℝ (clusterPotential m k) x
      = (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => p.1 ∈ k ∧ p.2 ∈ k),
          (m p.1 * m p.2) • (-((‖x p.1 - x p.2‖ ^ 3)⁻¹) •
            ((innerSL ℝ (x p.1 - x p.2)).comp (pairMap p.1 p.2)))) :=
    (hasFDerivAt_clusterPotential m k x hkk).fderiv
  set F : Fin N × Fin N → ℝ := fun p => m p.1 * m p.2 *
    (-((‖x p.1 - x p.2‖ ^ 3)⁻¹) * inner ℝ (x p.1 - x p.2)
      ((singleBodyVec i v) p.1 - (singleBodyVec i v) p.2)) with hF
  have happly : (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => p.1 ∈ k ∧ p.2 ∈ k),
        ((m p.1 * m p.2) • (-((‖x p.1 - x p.2‖ ^ 3)⁻¹) •
          ((innerSL ℝ (x p.1 - x p.2)).comp (pairMap p.1 p.2))))) (singleBodyVec i v)
      = ∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => p.1 ∈ k ∧ p.2 ∈ k), F p := by
    let ev : (EN E N →L[ℝ] ℝ) →+ ℝ :=
      { toFun := fun (φ : EN E N →L[ℝ] ℝ) => φ (singleBodyVec i v)
        map_zero' := by simp
        map_add' := by intro f g; rfl }
    change ev (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => p.1 ∈ k ∧ p.2 ∈ k),
        ((m p.1 * m p.2) • (-((‖x p.1 - x p.2‖ ^ 3)⁻¹) •
          ((innerSL ℝ (x p.1 - x p.2)).comp (pairMap p.1 p.2))))) = ∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => p.1 ∈ k ∧ p.2 ∈ k), F p
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro p hp
    dsimp [ev, F]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
    rw [pairMap_apply]
    rfl
  rw [h1, h2, happly]
  set H : Fin N → ℝ := fun j => m i * m j * (‖x j - x i‖ ^ 3)⁻¹ * inner ℝ (x j - x i) v with hH
  have htarget : inner ℝ (∑ j ∈ k.erase i, (m i * m j * (‖x j - x i‖ ^ 3)⁻¹) • (x j - x i)) v
      = ∑ j ∈ k.erase i, H j := by
    rw [sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_left]
    rfl
  rw [htarget]
  have hzero : ∀ p : Fin N × Fin N, p.1 ≠ i → p.2 ≠ i → F p = 0 := by
    intro p h1i h2i
    simp only [hF]
    rw [singleBodyVec_of_ne h1i, singleBodyVec_of_ne h2i, sub_zero, inner_zero_right, mul_zero,
      mul_zero]
  set G : Fin N → Fin N → ℝ := fun a b => if a ∈ k ∧ b ∈ k then F (a, b) else 0 with hG
  have hGi : ∀ a : Fin N, G a i = if a ∈ k then F (a, i) else 0 := by
    intro a
    rw [hG]
    simp only
    by_cases hak : a ∈ k
    · rw [if_pos ⟨hak, hi⟩, if_pos hak]
    · rw [if_neg (fun h => hak h.1), if_neg hak]
  have hGj : ∀ b : Fin N, G i b = if b ∈ k then F (i, b) else 0 := by
    intro b
    rw [hG]
    simp only
    by_cases hbk : b ∈ k
    · rw [if_pos ⟨hi, hbk⟩, if_pos hbk]
    · rw [if_neg (fun h => hbk h.2), if_neg hbk]
  have hsetIio : (Finset.Iio i).filter (fun a => a ∈ k) = k.filter (fun a => a < i) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_Iio]
    tauto
  have hsetIoi : (Finset.Ioi i).filter (fun b => b ∈ k) = k.filter (fun b => i < b) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_Ioi]
    tauto
  have hmain : ∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => p.1 ∈ k ∧ p.2 ∈ k), F p
      = ∑ a ∈ k.filter (fun a => a < i), F (a, i) + ∑ b ∈ k.filter (fun b => i < b), F (i, b) := by
    rw [Finset.sum_filter]
    rw [show (∑ p ∈ pairFinset N, (if p.1 ∈ k ∧ p.2 ∈ k then F p else 0))
        = ∑ p ∈ pairFinset N, G p.1 p.2 from rfl]
    rw [pairFinset, Commons.Data.Fin.pairSum_k_partition i G]
    rw [show (∑ a ∈ Finset.Iio i, G a i) = ∑ a ∈ k.filter (fun a => a < i), F (a, i) from
      calc (∑ a ∈ Finset.Iio i, G a i)
          = ∑ a ∈ Finset.Iio i, (if a ∈ k then F (a, i) else 0) :=
            Finset.sum_congr rfl (fun a _ => hGi a)
        _ = ∑ a ∈ (Finset.Iio i).filter (fun a => a ∈ k), F (a, i) := (Finset.sum_filter _ _).symm
        _ = ∑ a ∈ k.filter (fun a => a < i), F (a, i) := by rw [hsetIio]]
    rw [show (∑ b ∈ Finset.Ioi i, G i b) = ∑ b ∈ k.filter (fun b => i < b), F (i, b) from
      calc (∑ b ∈ Finset.Ioi i, G i b)
          = ∑ b ∈ Finset.Ioi i, (if b ∈ k then F (i, b) else 0) :=
            Finset.sum_congr rfl (fun b _ => hGj b)
        _ = ∑ b ∈ (Finset.Ioi i).filter (fun b => b ∈ k), F (i, b) := (Finset.sum_filter _ _).symm
        _ = ∑ b ∈ k.filter (fun b => i < b), F (i, b) := by rw [hsetIoi]]
    have hrest : (∑ p ∈ (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)).filter
        (fun p : Fin N × Fin N => p.1 ≠ i ∧ p.2 ≠ i), G p.1 p.2) = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      have hpi := (Finset.mem_filter.mp hp).2
      rw [hG]
      simp only
      by_cases hc : p.1 ∈ k ∧ p.2 ∈ k
      · rw [if_pos hc]; exact hzero p hpi.1 hpi.2
      · rw [if_neg hc]
    rw [hrest, add_zero]
  rw [hmain]
  have hF1 : ∀ a ∈ k.filter (fun a => a < i), F (a, i) = H a := by
    intro a ha
    have haa : a < i := (Finset.mem_filter.mp ha).2
    have hne : a ≠ i := ne_of_lt haa
    simp only [hF, hH]
    rw [singleBodyVec_of_ne hne v, singleBodyVec_self i v, zero_sub, inner_neg_right]
    ring
  have hF2 : ∀ b ∈ k.filter (fun b => i < b), F (i, b) = H b := by
    intro b hb
    have hib : i < b := (Finset.mem_filter.mp hb).2
    have hne : b ≠ i := ne_of_gt hib
    simp only [hF, hH]
    rw [singleBodyVec_self i v, singleBodyVec_of_ne hne v, sub_zero]
    rw [show x i - x b = -(x b - x i) by abel, norm_neg, inner_neg_left]
    ring
  rw [Finset.sum_congr rfl hF1, Finset.sum_congr rfl hF2]
  rw [← Finset.sum_union]
  · congr 1
    ext j
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro (⟨hj1, hj2⟩ | ⟨hj1, hj2⟩)
      · exact ⟨by omega, hj1⟩
      · exact ⟨by omega, hj1⟩
    · rintro ⟨hne, hjk⟩
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl ⟨hjk, h⟩
      · exact Or.inr ⟨hjk, h⟩
  · rw [Finset.disjoint_left]
    intro j hj1 hj2
    simp only [Finset.mem_filter] at hj1 hj2
    omega


/-- The gradient of the cluster potential vanishes outside the cluster. -/
lemma gradient_clusterPotential_apply_of_notMem {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N}
    (hkk : ∀ i ∈ k, ∀ j ∈ k, i ≠ j → x i ≠ x j) {i : Fin N} (hi : i ∉ k) :
    (gradient (clusterPotential m k) x) i = 0 := by
  classical
  apply (toDual ℝ E).injective
  ext v
  change inner ℝ ((gradient (clusterPotential m k) x) i) v = inner ℝ (0 : E) v
  rw [inner_zero_left]
  have h1 : inner ℝ ((gradient (clusterPotential m k) x) i) v
      = (fderiv ℝ (clusterPotential m k) x) (singleBodyVec i v) := by
    rw [← inner_singleBody (gradient (clusterPotential m k) x) i v, inner_gradient_eq_fderiv]
  rw [h1, fderiv_clusterPotential_apply m k x (singleBodyVec i v) hkk]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hmem := (Finset.mem_filter.mp hp).2
  rw [singleBodyVec_of_ne (fun h : p.1 = i => hi (h ▸ hmem.1)) v,
    singleBodyVec_of_ne (fun h : p.2 = i => hi (h ▸ hmem.2)) v, sub_zero, inner_zero_right]
  ring

/-- **Componentwise formula** for the mass-gradient of the cluster potential, inside the cluster. -/
lemma clusterGrad_apply_of_mem {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N}
    (hm : ∀ i, m i ≠ 0) (hkk : ∀ i ∈ k, ∀ j ∈ k, i ≠ j → x i ≠ x j) {i : Fin N} (hi : i ∈ k) :
    (clusterGrad m k x) i = ∑ j ∈ k.erase i, (m j * (‖x j - x i‖ ^ 3)⁻¹) • (x j - x i) := by
  have hcoord : (clusterGrad m k x) i
      = (m i)⁻¹ • (gradient (clusterPotential m k) x) i := by
    simp only [clusterGrad, weightedGrad]
  rw [hcoord, gradient_clusterPotential_apply_of_mem hkk hi, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [smul_smul]
  congr 1
  rw [← mul_assoc, inv_mul_cancel_left₀ (hm i)]

/-- The mass-gradient of the cluster potential vanishes outside the cluster. -/
lemma clusterGrad_apply_of_notMem {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N}
    (hkk : ∀ i ∈ k, ∀ j ∈ k, i ≠ j → x i ≠ x j) {i : Fin N} (hi : i ∉ k) :
    (clusterGrad m k x) i = 0 := by
  have hcoord : (clusterGrad m k x) i
      = (m i)⁻¹ • (gradient (clusterPotential m k) x) i := by
    simp only [clusterGrad, weightedGrad]
  rw [hcoord, gradient_clusterPotential_apply_of_notMem hkk hi, smul_zero]

/-- **Translation invariance**: replacing every body of the cluster by its displacement from the
centre of mass does not change the mass-gradient of the cluster potential. -/
lemma clusterGrad_cmRel {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N}
    (hm : ∀ i, m i ≠ 0) (hkk : ∀ i ∈ k, ∀ j ∈ k, i ≠ j → x i ≠ x j) :
    clusterGrad m k (cmRel m k x) = clusterGrad m k x := by
  have hkk' : ∀ i ∈ k, ∀ j ∈ k, i ≠ j → (cmRel m k x) i ≠ (cmRel m k x) j := by
    intro a ha b hb hab hcon
    rw [cmRel_apply_of_mem ha, cmRel_apply_of_mem hb] at hcon
    exact hkk a ha b hb hab (by
      have h2 := congrArg (fun w : E => w + clusterCM m k x) hcon
      simpa using h2)
  ext i
  by_cases hi : i ∈ k
  · rw [clusterGrad_apply_of_mem hm hkk' hi, clusterGrad_apply_of_mem hm hkk hi]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [cmRel_apply_of_mem hi, cmRel_apply_of_mem (Finset.mem_of_mem_erase hj)]
    rw [show (x j - clusterCM m k x) - (x i - clusterCM m k x) = x j - x i by abel]
  · rw [clusterGrad_apply_of_notMem hkk' hi, clusterGrad_apply_of_notMem hkk hi]

/-- **Scaling of the mass-gradient of the cluster potential** (the gradient of a degree `-1`
homogeneous function is homogeneous of degree `-2`).  Only collision-freeness *inside* the cluster
is needed. -/
lemma clusterGrad_smul {m : Fin N → ℝ} {k : Finset (Fin N)} {c : ℝ} (hc : 0 < c)
    (hm : ∀ i, m i ≠ 0) (x : EN E N) (hkk : ∀ i ∈ k, ∀ j ∈ k, i ≠ j → x i ≠ x j) :
    clusterGrad m k (c • x) = (c ^ 2)⁻¹ • clusterGrad m k x := by
  have hkk' : ∀ i ∈ k, ∀ j ∈ k, i ≠ j → (c • x) i ≠ (c • x) j := by
    intro a ha b hb hab hcon
    refine hkk a ha b hb hab ?_
    rw [show (c • x) a = c • x a from rfl, show (c • x) b = c • x b from rfl] at hcon
    exact (smul_right_injective E (ne_of_gt hc)) hcon
  ext i
  by_cases hi : i ∈ k
  · show (clusterGrad m k (c • x)) i = (c ^ 2)⁻¹ • (clusterGrad m k x) i
    rw [clusterGrad_apply_of_mem hm hkk' hi, clusterGrad_apply_of_mem hm hkk hi, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hsub : (c • x) j - (c • x) i = c • (x j - x i) := by
      rw [show (c • x) j = c • x j from rfl, show (c • x) i = c • x i from rfl, smul_sub]
    have hne : ‖x j - x i‖ ≠ 0 := by
      have h := hkk j (Finset.mem_of_mem_erase hj) i hi (Finset.mem_erase.mp hj).1
      exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)
    have hscal : m j * ((c * ‖x j - x i‖) ^ 3)⁻¹ * c
        = (c ^ 2)⁻¹ * (m j * (‖x j - x i‖ ^ 3)⁻¹) := by
      have hcne : c ≠ 0 := ne_of_gt hc
      field_simp
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hc, smul_smul, smul_smul, hscal]
  · show (clusterGrad m k (c • x)) i = (c ^ 2)⁻¹ • (clusterGrad m k x) i
    rw [clusterGrad_apply_of_notMem hkk' hi, clusterGrad_apply_of_notMem hkk hi, smul_zero]

/-- **Euler homogeneity of the mass-gradient of the cluster potential.** -/
lemma euler_clusterGrad {m : Fin N → ℝ} {k : Finset (Fin N)} {x : EN E N}
    (hm : ∀ i, 0 < m i) (hx : WithoutCollisions x) :
    massInner m (clusterGrad m k x) x = - clusterPotential m k x := by
  have hpoint : ∀ i : Fin N, inner ℝ (x i) ((gradient (U (clusterIndicatorMass m k)) x) i)
      = m i * inner ℝ (x i) ((clusterGrad m k x) i) := by
    intro i
    have h1 : (gradient (U (clusterIndicatorMass m k)) x) i = m i • (clusterGrad m k x) i := by
      have h2 : (clusterGrad m k x) i
          = (m i)⁻¹ • (gradient (U (clusterIndicatorMass m k)) x) i := by
        simp only [clusterGrad, weightedGrad, clusterPotential_eq_U]
      rw [h2, smul_smul, mul_inv_cancel₀ (ne_of_gt (hm i)), one_smul]
    rw [h1, inner_smul_right]
  rw [massInner]
  have hthis : ∑ i, m i * inner ℝ ((clusterGrad m k x) i) (x i)
      = ∑ i : Fin N, inner ℝ (x i) ((gradient (U (clusterIndicatorMass m k)) x) i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm (x i) ((clusterGrad m k x) i), ← hpoint i]
  rw [hthis, euler_homogeneity_U (clusterIndicatorMass m k) x hx, U_clusterIndicatorMass]

/-- The cluster potential is homogeneous of degree `-1` under scaling. -/
lemma clusterPotential_smul (m : Fin N → ℝ) (k : Finset (Fin N)) (c : ℝ) (x : EN E N) :
    clusterPotential m k (c • x) = |c|⁻¹ * clusterPotential m k x := by
  rw [clusterPotential_eq_U, U_smul]

end Submission.NBody
