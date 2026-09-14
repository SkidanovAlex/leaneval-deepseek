import Submission.NBody.MarchalBumpTransfer
import Submission.NBody.MarchalBumpRest
import Submission.Commons.Analysis.Calculus.intervalIntegrable_of_continuousOn_Ioo_of_bound

/-!
# Integrability of the six pieces of the transfer identity

`Submission.NBody.bump_real_action_eq` expresses the action difference of the symmetric bump as a
combination of six interval integrals; this module discharges the integrability hypotheses that
the splitting of the integrals requires, in the geometric situation of the blow-up.

All results in this file are fully proved.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-! ## Elementary facts about the blow-up and its perturbation -/

/-- Moving `u` by a nonnegative multiple of `δ` in a direction making an acute angle with `u`
does not decrease the norm. -/
lemma norm_le_norm_add_smul_of_inner_nonneg {u δ : E} {φ : ℝ} (hφ : 0 ≤ φ)
    (h : 0 ≤ inner ℝ u δ) : ‖u‖ ≤ ‖u + φ • δ‖ := by
  have h2 : ‖u‖ ^ 2 ≤ ‖u + φ • δ‖ ^ 2 := by
    have hsq : ‖u + φ • δ‖ ^ 2 = ‖u‖ ^ 2 + 2 * (φ * inner ℝ u δ) + φ ^ 2 * ‖δ‖ ^ 2 := by
      rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [hsq]
    have h3 : 0 ≤ 2 * (φ * inner ℝ u δ) := by positivity
    have h4 : 0 ≤ φ ^ 2 * ‖δ‖ ^ 2 := by positivity
    linarith
  calc ‖u‖ = Real.sqrt (‖u‖ ^ 2) := (Real.sqrt_sq (norm_nonneg u)).symm
    _ ≤ Real.sqrt (‖u + φ • δ‖ ^ 2) := Real.sqrt_le_sqrt h2
    _ = ‖u + φ • δ‖ := Real.sqrt_sq (norm_nonneg _)

/-- The outward condition gives monotonicity of the cluster potential under the standard
variation. -/
lemma clusterPotential_add_stdPert_le {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {k : Finset (Fin N)}
    {i₀ : Fin N} (hi₀ : i₀ ∈ k) (δ : E) (T t : ℝ) (q : EN E N)
    (hnc : ∀ j ∈ k.erase i₀, q i₀ ≠ q j)
    (hsgn : ∀ j ∈ k.erase i₀, 0 ≤ inner ℝ (q i₀ - q j) δ) :
    clusterPotential m k (q + stdPert m k i₀ δ T t) ≤ clusterPotential m k q := by
  have hdiff := clusterPotential_bump_diff m k hi₀ q δ T t
  have hsub : clusterPotential m k (q + stdPert m k i₀ δ T t) - clusterPotential m k q ≤ 0 := by
    rw [hdiff]
    refine Finset.sum_nonpos fun j hj => ?_
    have hmm : 0 ≤ m i₀ * m j := by
      have h1 := hm i₀; have h2 := hm j; positivity
    have hφ : 0 ≤ stdCoef δ T t := stdCoef_nonneg δ T t
    have hu : q i₀ - q j ≠ 0 := sub_ne_zero.mpr (hnc j hj)
    have hun : 0 < ‖q i₀ - q j‖ := norm_pos_iff.mpr hu
    have hle : ‖q i₀ - q j‖ ≤ ‖(q i₀ - q j) + stdVar δ T t‖ := by
      rw [stdVar]
      exact norm_le_norm_add_smul_of_inner_nonneg hφ (hsgn j hj)
    have hinv : (‖(q i₀ - q j) + stdVar δ T t‖)⁻¹ - (‖q i₀ - q j‖)⁻¹ ≤ 0 := by
      have hb : 0 < ‖(q i₀ - q j) + stdVar δ T t‖ := lt_of_lt_of_le hun hle
      have h3 := (inv_le_inv₀ hb hun).mpr hle
      linarith
    exact mul_nonpos_of_nonneg_of_nonpos hmm hinv
  linarith

/-- A configuration is collision free inside `k`. -/
def ClusterNoColl (k : Finset (Fin N)) (x : EN E N) : Prop :=
  ∀ i ∈ k, ∀ j ∈ k, i ≠ j → x i ≠ x j

lemma ne_of_r_ne_zero {x : EN E N} {i j : Fin N} (h : r x i j ≠ 0) : x i ≠ x j := by
  have h2 : x i - x j ≠ 0 := by
    rw [r_eq_norm_sub] at h
    exact norm_ne_zero_iff.mp h
  exact sub_ne_zero.mp h2

lemma cmRel_sub_of_mem {m : Fin N → ℝ} {k : Finset (Fin N)} (v : EN E N) {i j : Fin N}
    (hi : i ∈ k) (hj : j ∈ k) : cmRel m k v i - cmRel m k v j = v i - v j := by
  rw [cmRel_apply_of_mem hi, cmRel_apply_of_mem hj]
  abel

lemma clusterNoColl_cmRel {m : Fin N → ℝ} {k : Finset (Fin N)} {v : EN E N}
    (h : ClusterNoColl k v) : ClusterNoColl k (cmRel m k v) := by
  intro i hi j hj hij hEq
  have h2 : cmRel m k v i - cmRel m k v j = 0 := by rw [hEq, sub_self]
  rw [cmRel_sub_of_mem v hi hj] at h2
  exact h i hi j hj hij (sub_eq_zero.mp h2)

lemma clusterNoColl_of_withoutCollisions {k : Finset (Fin N)} {v : EN E N}
    (h : WithoutCollisions v) : ClusterNoColl k v :=
  fun i _ j _ hij => ne_of_r_ne_zero (h i j hij)

lemma clusterNoColl_smul {c : ℝ} {k : Finset (Fin N)} {v : EN E N} (hc : c ≠ 0)
    (h : ClusterNoColl k v) : ClusterNoColl k (c • v) := by
  intro i hi j hj hij hEq
  rw [PiLp.smul_apply, PiLp.smul_apply] at hEq
  have h2 : c • (v i - v j) = 0 := by rw [smul_sub, hEq, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact hc h3
  · exact h i hi j hj hij (sub_eq_zero.mp h3)

/-- The standard variation keeps the cluster collision free, thanks to the outward condition. -/
lemma clusterNoColl_add_stdPert {m : Fin N → ℝ} {k : Finset (Fin N)} {i₀ : Fin N} (hi₀ : i₀ ∈ k)
    {δ : E} {T t : ℝ} {q : EN E N} (hnc : ClusterNoColl k q)
    (hsgn : ∀ j ∈ k.erase i₀, 0 ≤ inner ℝ (q i₀ - q j) δ) :
    ClusterNoColl k (q + stdPert m k i₀ δ T t) := by
  have hqsub : ∀ a b A B : E, (a + A) - (b + B) = (a - b) + (A - B) := fun a b A B => by abel
  have hqsub2 : ∀ a b A B : E, (b + B) - (a + A) = (b - a) + (B - A) := fun a b A B => by abel
  have key₁ : ∀ j ∈ k, j ≠ i₀ →
      (q + stdPert m k i₀ δ T t) i₀ - (q + stdPert m k i₀ δ T t) j
        = (q i₀ - q j) + stdVar δ T t := by
    intro j hj hjne
    have h1 : stdCoef δ T t • (stdPertVec m k i₀ δ) i₀
        - stdCoef δ T t • (stdPertVec m k i₀ δ) j = stdVar δ T t := by
      rw [stdVar, ← smul_sub, stdPertVec_sub_i₀ hi₀ hj hjne]
    simp only [PiLp.add_apply, stdPert_eq_smul_stdPertVec, PiLp.smul_apply]
    rw [hqsub, h1]
  have key₂ : ∀ j ∈ k, j ≠ i₀ →
      (q + stdPert m k i₀ δ T t) j - (q + stdPert m k i₀ δ T t) i₀
        = (q j - q i₀) - stdVar δ T t := by
    intro j hj hjne
    have hbase : (stdPertVec m k i₀ δ) j - (stdPertVec m k i₀ δ) i₀ = -δ := by
      rw [← neg_sub, stdPertVec_sub_i₀ hi₀ hj hjne]
    have h1 : stdCoef δ T t • (stdPertVec m k i₀ δ) j
        - stdCoef δ T t • (stdPertVec m k i₀ δ) i₀ = -stdVar δ T t := by
      rw [stdVar, ← smul_sub, hbase, smul_neg]
    simp only [PiLp.add_apply, stdPert_eq_smul_stdPertVec, PiLp.smul_apply]
    rw [hqsub2, h1]
    abel
  have key₃ : ∀ i ∈ k, ∀ j ∈ k, i ≠ i₀ → j ≠ i₀ →
      (q + stdPert m k i₀ δ T t) i - (q + stdPert m k i₀ δ T t) j = q i - q j := by
    intro i hi j hj hii hjj
    have hb : (stdPertVec m k i₀ δ) i - (stdPertVec m k i₀ δ) j = 0 := by
      rw [stdPertVec_sub_of_notMem hi hj hii hjj, sub_self]
    have h1 : stdCoef δ T t • (stdPertVec m k i₀ δ) i
        - stdCoef δ T t • (stdPertVec m k i₀ δ) j = 0 := by
      rw [← smul_sub, hb, smul_zero]
    simp only [PiLp.add_apply, stdPert_eq_smul_stdPertVec, PiLp.smul_apply]
    rw [hqsub, h1, add_zero]
  have hzero : ∀ u v : E, ‖u‖ ≤ ‖v‖ → v = 0 → u = 0 := by
    intro u v huv hv
    have h2 : ‖u‖ = 0 :=
      le_antisymm (by rw [hv, norm_zero] at huv; exact huv) (norm_nonneg u)
    exact norm_eq_zero.mp h2
  intro i hi j hj hij hEq
  by_cases hji : j = i₀
  · have hne : i ≠ i₀ := fun hh => hij (by rw [hh, hji])
    have h0 : (q + stdPert m k i₀ δ T t) i - (q + stdPert m k i₀ δ T t) j = 0 :=
      sub_eq_zero.mpr hEq
    rw [hji, key₂ i hi hne] at h0
    have hφ : 0 ≤ stdCoef δ T t := stdCoef_nonneg δ T t
    have hs : 0 ≤ inner ℝ (q i - q i₀) (-δ) := by
      rw [inner_neg_right, ← inner_neg_left, neg_sub]
      exact hsgn i (Finset.mem_erase.mpr ⟨hne, hi⟩)
    have hle : ‖q i - q i₀‖ ≤ ‖(q i - q i₀) - stdVar δ T t‖ := by
      have h1 : (q i - q i₀) - stdVar δ T t = (q i - q i₀) + stdCoef δ T t • (-δ) := by
        rw [stdVar, smul_neg, sub_eq_add_neg]
      rw [h1]
      exact norm_le_norm_add_smul_of_inner_nonneg hφ hs
    exact hnc i hi i₀ hi₀ hne (sub_eq_zero.mp (hzero _ _ hle h0))
  · by_cases hii : i = i₀
    · have h0 : (q + stdPert m k i₀ δ T t) i - (q + stdPert m k i₀ δ T t) j = 0 :=
        sub_eq_zero.mpr hEq
      rw [hii, key₁ j hj hji] at h0
      have hφ : 0 ≤ stdCoef δ T t := stdCoef_nonneg δ T t
      have hle : ‖q i₀ - q j‖ ≤ ‖(q i₀ - q j) + stdVar δ T t‖ := by
        rw [stdVar]
        exact norm_le_norm_add_smul_of_inner_nonneg hφ (hsgn j (Finset.mem_erase.mpr ⟨hji, hj⟩))
      exact hnc i₀ hi₀ j hj (Ne.symm hji) (sub_eq_zero.mp (hzero _ _ hle h0))
    · have h0 : (q + stdPert m k i₀ δ T t) i - (q + stdPert m k i₀ δ T t) j = 0 :=
        sub_eq_zero.mpr hEq
      rw [key₃ i hi j hj hii hji] at h0
      exact hnc i hi j hj hij (sub_eq_zero.mp h0)

/-- A configuration is collision free inside `k`. -/
lemma continuousOn_clusterPotential (m : Fin N → ℝ) (k : Finset (Fin N)) :
    ContinuousOn (clusterPotential m k) {x : EN E N | ClusterNoColl k x} := by
  have hunfold : clusterPotential m k = fun x : EN E N =>
      ∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => p.1 ∈ k ∧ p.2 ∈ k),
        m p.1 * m p.2 * (r x p.1 p.2)⁻¹ := rfl
  rw [hunfold]
  refine continuousOn_finsetSum _ fun p hp => ?_
  have hp' : p.1 ≠ p.2 := by
    have := (Finset.mem_filter.mp hp).1
    exact ne_of_lt (Finset.mem_filter.mp this).2
  have hsub : {x : EN E N | ClusterNoColl k x} ⊆ {x : EN E N | x p.1 ≠ x p.2} :=
    fun x hx => hx p.1 (Finset.mem_filter.mp hp).2.1 p.2 (Finset.mem_filter.mp hp).2.2 hp'
  exact continuousOn_const.mul ((continuousOn_inv_r p.1 p.2).mono hsub)

lemma continuousOn_clusterPotentialRest (m : Fin N → ℝ) (k : Finset (Fin N)) {ν : ℝ} (hν : 0 < ν) :
    ContinuousOn (clusterPotentialRest m k) {x : EN E N | ClusterSeparated k x ν} := by
  have hunfold : clusterPotentialRest m k = fun x : EN E N =>
      ∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
        m p.1 * m p.2 * (r x p.1 p.2)⁻¹ := rfl
  rw [hunfold]
  refine continuousOn_finsetSum _ fun p hp => ?_
  have hpp : p.1 ≠ p.2 := by
    have := (Finset.mem_filter.mp hp).1
    exact ne_of_lt (Finset.mem_filter.mp this).2
  have hnc : ¬ (p.1 ∈ k ∧ p.2 ∈ k) := (Finset.mem_filter.mp hp).2
  have hsub : {x : EN E N | ClusterSeparated k x ν} ⊆ {x : EN E N | x p.1 ≠ x p.2} :=
    fun x hx => ne_of_r_ne_zero (ne_of_gt (lt_of_lt_of_le hν (hx p.1 p.2 hpp hnc)))
  exact continuousOn_const.mul ((continuousOn_inv_r p.1 p.2).mono hsub)

/-- **The interaction potential is continuous under one-sided separation and the non-collision of
the pairs outside the cluster.**  This is the form needed when only the one-sided separation is
available (the pairs with both bodies outside `k` then get their non-degeneracy from the
collision-freeness of the curve, not from the separation hypothesis). -/
lemma continuousOn_clusterPotentialRest_of_weak (m : Fin N → ℝ) (k : Finset (Fin N)) {ν : ℝ}
    (hν : 0 < ν) :
    ContinuousOn (clusterPotentialRest m k)
      {x : EN E N | ClusterSeparatedWeak k x ν ∧ ∀ i ∉ k, ∀ j ∉ k, i ≠ j → x i ≠ x j} := by
  have hunfold : clusterPotentialRest m k = fun x : EN E N =>
      ∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
        m p.1 * m p.2 * (r x p.1 p.2)⁻¹ := rfl
  rw [hunfold]
  refine continuousOn_finsetSum _ fun p hp => ?_
  have hpp : p.1 ≠ p.2 := by
    have := (Finset.mem_filter.mp hp).1
    exact ne_of_lt (Finset.mem_filter.mp this).2
  have hnc : ¬ (p.1 ∈ k ∧ p.2 ∈ k) := (Finset.mem_filter.mp hp).2
  have hsub : {x : EN E N | ClusterSeparatedWeak k x ν ∧ ∀ i ∉ k, ∀ j ∉ k, i ≠ j → x i ≠ x j}
      ⊆ {x : EN E N | x p.1 ≠ x p.2} := by
    rintro x ⟨hweak, hout⟩
    rcases em (p.1 ∈ k) with h1 | h1
    · have h2 : p.2 ∉ k := fun h2 => hnc ⟨h1, h2⟩
      exact ne_of_r_ne_zero (ne_of_gt (lt_of_lt_of_le hν (hweak p.1 h1 p.2 h2)))
    · rcases em (p.2 ∈ k) with h2 | h2
      · have h3 : ν ≤ r x p.2 p.1 := hweak p.2 h2 p.1 h1
        exact fun heq => ne_of_r_ne_zero (ne_of_gt (lt_of_lt_of_le hν h3)) (by rw [heq])
      · exact hout p.1 h1 p.2 h2 hpp
  exact continuousOn_const.mul ((continuousOn_inv_r p.1 p.2).mono hsub)

/-- A continuous function on an open interval, dominated by an interval-integrable function, is
interval integrable. -/
lemma intervalIntegrable_of_continuousOn_Ioo_of_le {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Set.Ioo a b)) (hg : IntervalIntegrable g volume a b)
    (hle : ∀ x ∈ Set.Ioo a b, |f x| ≤ g x) : IntervalIntegrable f volume a b := by
  have hIoo_ae : Set.Ioo a b =ᵐ[(volume : Measure ℝ)] Set.Ioc a b := Ioo_ae_eq_Ioc
  have hae : ∀ᵐ x ∂(volume.restrict (Set.Ioc a b)), x ∈ Set.Ioo a b := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    have h : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ b := by
      rw [MeasureTheory.ae_iff]; simp
    filter_upwards [h] with x hx hxIoc
    exact ⟨hxIoc.1, lt_of_le_of_ne hxIoc.2 hx⟩
  have hmeas : AEStronglyMeasurable f (volume.restrict (Set.uIoc a b)) := by
    have h1 : AEStronglyMeasurable f (volume.restrict (Set.Ioo a b)) :=
      hcont.aestronglyMeasurable measurableSet_Ioo
    rw [Measure.restrict_congr_set hIoo_ae] at h1
    rw [Set.uIoc_of_le hab]
    exact h1
  refine hg.mono_fun' hmeas ?_
  rw [Set.uIoc_of_le hab]
  filter_upwards [hae] with x hx
  rw [Real.norm_eq_abs]
  exact hle x hx


lemma abs_massInner_le_weightedNorm_mul (m : Fin N → ℝ) (hm : ∀ i, 0 ≤ m i) (v w : EN E N) :
    |massInner m v w| ≤ ‖v‖_[m] * ‖w‖_[m] := by
  rw [abs_le]
  refine ⟨?_, massInner_le_weightedNorm_mul m hm v w⟩
  have h1 := neg_massInner_le_weightedNorm_mul m hm v w
  linarith

/-- A mass-norm bound for the almost-everywhere derivative of the standard variation. -/
lemma weightedNorm_stdVarVecDeriv_le {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {k : Finset (Fin N)}
    {i₀ : Fin N} {δ : E} (hδ : δ ≠ 0) (T s : ℝ) :
    ‖stdVarVecDeriv m k i₀ δ T s‖_[m] ≤ ‖stdPertVec m k i₀ δ‖_[m] * ‖δ‖⁻¹ := by
  have hd : (0:ℝ) < ‖δ‖ := norm_pos_iff.mpr hδ
  rw [stdVarVecDeriv]
  by_cases hsc : s ≤ T - ‖δ‖
  · rw [if_pos hsc, weightedNorm_zero]
    exact mul_nonneg (weightedNorm_nonneg m _) (inv_nonneg.mpr (norm_nonneg δ))
  · rw [if_neg hsc, weightedNorm_smul (fun i => (hm i).le), abs_neg,
      abs_of_pos (inv_pos.mpr hd), mul_comm]

/-! ## The integrability theorem -/

/-- **Integrability of the six pieces of the transfer identity.**  In the geometric situation of the
blow-up of a colliding cluster (the rescaled configuration is collision free inside `k`, bounded in
velocity, with the two-sided pair bounds and the outward sign condition, and the interaction
potential is separated), all six integrands occurring in `bump_real_action_eq` are interval
integrable. -/
theorem bump_pieces_intervalIntegrable {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {k : Finset (Fin N)}
    {i₀ : Fin N} (hi₀ : i₀ ∈ k) {δ : E} (hδ : δ ≠ 0) {lam T t₀ : ℝ} (hlam : 0 < lam)
    (hT : 0 < T) {γ : ℝ → EN E N}
    (hac : AbsolutelyContinuousOnInterval γ t₀ (t₀ + lam * T))
    (hncI : ∀ t ∈ Ioo t₀ (t₀ + lam * T), WithoutCollisions (γ t))
    {Cd Cp ν : ℝ} (hCd : 0 ≤ Cd) (hCp : 0 ≤ Cp) (hν : 0 < ν)
    (hvel : ∀ t ∈ Ioc (0:ℝ) T,
      ‖deriv (bumpRescaled m k γ t₀ lam) t‖_[m] ≤ Cd * t ^ (-(1:ℝ)/3))
    (hUpot : ∀ t ∈ Ioc (0:ℝ) T,
      clusterPotential m k (bumpRescaled m k γ t₀ lam t) ≤ Cp * t ^ (-(2:ℝ)/3))
    (hsgn : ∀ t ∈ Ioc (0:ℝ) T, ∀ j ∈ k.erase i₀,
      0 ≤ inner ℝ (bumpRescaled m k γ t₀ lam t i₀ - bumpRescaled m k γ t₀ lam t j) δ)
    (hsep : ∀ t ∈ Ioc (0:ℝ) T, ClusterSeparated k (γ (t₀ + lam * t)) ν)
    (hsmall : 4 * (lam ^ ((2:ℝ)/3) * ‖δ‖) ≤ ν) :
    IntervalIntegrable (fun s : ℝ => massInner m (deriv (bumpRescaled m k γ t₀ lam) s)
        (deriv (stdVarVec m k i₀ δ T) s)) volume (0:ℝ) T ∧
      IntervalIntegrable (fun s : ℝ => ‖deriv (stdVarVec m k i₀ δ T) s‖_[m] ^ 2)
        volume (0:ℝ) T ∧
      IntervalIntegrable (fun s : ℝ => clusterPotential m k
        (bumpRescaled m k γ t₀ lam s + stdVarVec m k i₀ δ T s)) volume (0:ℝ) T ∧
      IntervalIntegrable (fun s : ℝ => clusterPotential m k
        (bumpRescaled m k γ t₀ lam s)) volume (0:ℝ) T ∧
      IntervalIntegrable (fun s : ℝ => clusterPotentialRest m k
        (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s))) volume (0:ℝ) T ∧
      IntervalIntegrable (fun s : ℝ => clusterPotentialRest m k
        (γ (t₀ + lam * s))) volume (0:ℝ) T := by
  classical
  have hρnn : 0 ≤ lam ^ ((2:ℝ)/3) * ‖δ‖ :=
    mul_nonneg (Real.rpow_nonneg hlam.le _) (norm_nonneg δ)
  have hshift : ∀ s : ℝ, bumpRescaled m k γ t₀ lam s
      = lam ^ (-(2:ℝ)/3) • (cmRel m k (γ (t₀ + s * lam))) := by
    intro s
    rw [bumpRescaled, rescaledCentered, shiftCurve_apply]
  have hγs : ContinuousOn (fun s : ℝ => γ (t₀ + s * lam)) (Ioo (0:ℝ) T) := by
    refine hac.continuousOn.comp (by fun_prop) fun s hs => ?_
    refine Set.mem_uIcc.mpr (Or.inl ⟨?_, ?_⟩)
    · have : 0 < s * lam := mul_pos hs.1 hlam
      linarith
    · have h1 : s * lam < lam * T := by
        rw [mul_comm s lam]
        exact mul_lt_mul_of_pos_left hs.2 hlam
      linarith
  have hγs2 : ContinuousOn (fun s : ℝ => γ (t₀ + lam * s)) (Ioo (0:ℝ) T) :=
    hγs.congr fun s _ => by rw [mul_comm]
  have hqcont : ContinuousOn (fun s : ℝ => bumpRescaled m k γ t₀ lam s) (Ioo (0:ℝ) T) := by
    have h2 : ContinuousOn (fun s : ℝ => cmRel m k (γ (t₀ + s * lam))) (Ioo (0:ℝ) T) :=
      (cmRelL m k).continuous.comp_continuousOn hγs
    have h3 := (continuousOn_const (c := lam ^ (-(2:ℝ)/3))).smul h2
    refine h3.congr fun s _ => ?_
    exact (hshift s).symm
  have hcontCoef : Continuous (stdCoef δ T) := by
    have h1 : Continuous (fun t : ℝ => (T - t) / ‖δ‖) := by fun_prop
    exact continuous_const.min (continuous_const.max h1)
  have hdcont : Continuous (fun s : ℝ => stdVarVec m k i₀ δ T s) := by
    have hC : Continuous (fun s : ℝ => stdCoef δ T s • stdPertVec m k i₀ δ) :=
      hcontCoef.smul continuous_const
    refine hC.congr fun s => ?_
    rw [stdVarVec_eq_stdPert, stdPert, stdVar, stdPertVec_smul_apply]
  have hnn : ∀ t ∈ Ioo (0:ℝ) T, ClusterNoColl k (bumpRescaled m k γ t₀ lam t) := by
    intro t ht
    have hpos : t₀ < t₀ + t * lam := by
      have : 0 < t * lam := mul_pos ht.1 hlam
      linarith
    have hlt : t₀ + t * lam < t₀ + lam * T := by
      have h1 : t * lam < lam * T := by
        rw [mul_comm t lam]
        exact mul_lt_mul_of_pos_left ht.2 hlam
      linarith
    have h1 := clusterNoColl_of_withoutCollisions (k := k) (hncI _ ⟨hpos, hlt⟩)
    have h2 := clusterNoColl_cmRel (m := m) h1
    rw [hshift t]
    exact clusterNoColl_smul (Real.rpow_pos_of_pos hlam _).ne' h2
  set A : ℝ := ‖stdPertVec m k i₀ δ‖_[m] * ‖δ‖⁻¹ with hA
  set Cu : ℝ := ∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
    m p.1 * m p.2 with hCu
  have hmajpow : ∀ c r : ℝ, -1 < r → IntervalIntegrable (fun s : ℝ => c * s ^ r) volume (0:ℝ) T :=
    fun c r hr => (intervalIntegral.intervalIntegrable_rpow' (a := (0:ℝ)) (b := T) (r := r) hr).const_mul c
  have hpiece1 : IntervalIntegrable (fun s : ℝ => massInner m
      (deriv (bumpRescaled m k γ t₀ lam) s) (deriv (stdVarVec m k i₀ δ T) s))
      volume (0:ℝ) T := by
    have hmaj : IntervalIntegrable (fun s : ℝ => Cd * A * s ^ (-(1:ℝ)/3)) volume (0:ℝ) T := by
      have h := hmajpow (Cd * A) (-(1:ℝ)/3) (by norm_num)
      simpa only [mul_assoc] using h
    refine hmaj.mono_fun' ?_ ?_
    · have hco : Continuous (fun p : EN E N × EN E N => massInner m p.1 p.2) := by
        unfold massInner
        fun_prop
      have h1m : Measurable (deriv (bumpRescaled m k γ t₀ lam)) := measurable_deriv _
      have h2m : Measurable (deriv (stdVarVec m k i₀ δ T)) := measurable_deriv _
      exact (hco.measurable.comp (h1m.prodMk h2m)).aestronglyMeasurable
    · have hae := deriv_stdVarVec_ae m k i₀ δ T hδ
      rw [Set.uIoc_of_le hT.le]
      filter_upwards [hae, MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs hsIoc
      rw [hs, Real.norm_eq_abs, hA]
      calc |massInner m (deriv (bumpRescaled m k γ t₀ lam) s) (stdVarVecDeriv m k i₀ δ T s)|
          ≤ ‖deriv (bumpRescaled m k γ t₀ lam) s‖_[m]
              * ‖stdVarVecDeriv m k i₀ δ T s‖_[m] :=
            abs_massInner_le_weightedNorm_mul m (fun i => (hm i).le) _ _
        _ ≤ (Cd * s ^ (-(1:ℝ)/3)) * (‖stdPertVec m k i₀ δ‖_[m] * ‖δ‖⁻¹) :=
            mul_le_mul (hvel s hsIoc)
              (weightedNorm_stdVarVecDeriv_le (m := m) (k := k) (i₀ := i₀) hm hδ T s)
              (weightedNorm_nonneg m _)
              (mul_nonneg hCd (Real.rpow_nonneg hsIoc.1.le _))
        _ = Cd * (‖stdPertVec m k i₀ δ‖_[m] * ‖δ‖⁻¹) * s ^ (-(1:ℝ)/3) := by ring
  have hpiece2 : IntervalIntegrable (fun s : ℝ => ‖deriv (stdVarVec m k i₀ δ T) s‖_[m] ^ 2)
      volume (0:ℝ) T := by
    have hmaj : IntervalIntegrable (fun _ : ℝ => A ^ 2) volume (0:ℝ) T := intervalIntegrable_const
    refine hmaj.mono_fun' ?_ ?_
    · have hco : Continuous (fun v : EN E N => ‖v‖_[m] ^ 2) := (continuous_weightedNorm' m).pow 2
      have h1m : Measurable (deriv (stdVarVec m k i₀ δ T)) := measurable_deriv _
      exact (hco.measurable.comp h1m).aestronglyMeasurable
    · have hae := deriv_stdVarVec_ae m k i₀ δ T hδ
      rw [Set.uIoc_of_le hT.le]
      filter_upwards [hae] with s hs
      rw [hs, Real.norm_eq_abs, hA]
      have hb := weightedNorm_stdVarVecDeriv_le (m := m) (k := k) (i₀ := i₀) hm hδ T s
      rw [abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (weightedNorm_nonneg m _) hb 2
  have hpiece3 : IntervalIntegrable (fun s : ℝ => clusterPotential m k
      (bumpRescaled m k γ t₀ lam s + stdVarVec m k i₀ δ T s)) volume (0:ℝ) T := by
    refine intervalIntegrable_of_continuousOn_Ioo_of_le (g := fun s : ℝ => Cp * s ^ (-(2:ℝ)/3)) hT.le ?_ ?_ ?_
    · refine (continuousOn_clusterPotential m k).comp
        (hqcont.add (hdcont.continuousOn.mono (Set.subset_univ _))) ?_
      intro s hs
      have hh := clusterNoColl_add_stdPert (m := m) (k := k) (i₀ := i₀) (T := T) (t := s) hi₀ (hnn s hs)
        (fun j hj => hsgn s ⟨hs.1, le_of_lt hs.2⟩ j hj)
      simpa [stdVarVec_eq_stdPert] using hh
    · exact hmajpow Cp (-(2:ℝ)/3) (by norm_num)
    · intro t ht
      have htIoc : t ∈ Ioc (0:ℝ) T := ⟨ht.1, le_of_lt ht.2⟩
      rw [abs_of_nonneg (clusterPotential_nonneg (fun i => (hm i).le) k _)]
      have hle := clusterPotential_add_stdPert_le hm hi₀ δ T t _
        (fun j hj => hnn t ht i₀ hi₀ j (Finset.mem_erase.mp hj).2
          (Ne.symm (Finset.mem_erase.mp hj).1))
        (fun j hj => hsgn t htIoc j hj)
      simpa [stdVarVec_eq_stdPert] using hle.trans (hUpot t htIoc)
  have hpiece4 : IntervalIntegrable (fun s : ℝ => clusterPotential m k
      (bumpRescaled m k γ t₀ lam s)) volume (0:ℝ) T := by
    refine intervalIntegrable_of_continuousOn_Ioo_of_le (g := fun s : ℝ => Cp * s ^ (-(2:ℝ)/3)) hT.le ?_ ?_ ?_
    · exact (continuousOn_clusterPotential m k).comp hqcont fun s hs => hnn s hs
    · exact hmajpow Cp (-(2:ℝ)/3) (by norm_num)
    · intro t ht
      have htIoc : t ∈ Ioc (0:ℝ) T := ⟨ht.1, le_of_lt ht.2⟩
      rw [abs_of_nonneg (clusterPotential_nonneg (fun i => (hm i).le) k _)]
      exact hUpot t htIoc
  have hsep2 : ∀ t ∈ Ioo (0:ℝ) T,
      ClusterSeparated k (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * t)) (ν / 2) := by
    intro t ht
    have htIoc : t ∈ Ioc (0:ℝ) T := ⟨ht.1, le_of_lt ht.2⟩
    have hpert : ∀ j : Fin N, ‖bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * t) j
        - γ (t₀ + lam * t) j‖ ≤ lam ^ ((2:ℝ)/3) * ‖δ‖ := by
      intro j
      by_cases hj : j ∈ k
      · exact bumpCurve_pert_le hm hi₀ hlam ht.1.le hj
      · rw [bumpCurve_eq_of_notMem (m := m) (k := k) hlam ht.1.le hj, sub_self, norm_zero]
        exact hρnn
    intro i j hij hpmem
    have hbase : ν ≤ r (γ (t₀ + lam * t)) i j := hsep t htIoc i j hij hpmem
    rw [r_eq_norm_sub] at hbase
    rw [r_eq_norm_sub]
    have h2 : lam ^ ((2:ℝ)/3) * ‖δ‖ ≤ ν / 4 := by linarith
    have h1 : ‖γ (t₀ + lam * t) i - γ (t₀ + lam * t) j‖ ≤
        ‖bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * t) i
          - bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * t) j‖
        + ‖bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * t) i - γ (t₀ + lam * t) i‖
        + ‖bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * t) j - γ (t₀ + lam * t) j‖ := by
      have he : γ (t₀ + lam * t) i - γ (t₀ + lam * t) j
          = (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * t) i
              - bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * t) j)
            - ((bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * t) i - γ (t₀ + lam * t) i)
              - (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * t) j - γ (t₀ + lam * t) j)) := by
        abel
      rw [he]
      have h3 := norm_sub_le (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * t) i
          - bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * t) j)
        ((bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * t) i - γ (t₀ + lam * t) i)
          - (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * t) j - γ (t₀ + lam * t) j))
      have h5 := norm_sub_le
        (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * t) i - γ (t₀ + lam * t) i)
        (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * t) j - γ (t₀ + lam * t) j)
      linarith [h3, h5]
    linarith [hbase, h1, hpert i, hpert j, h2]
  have hpiece5 : IntervalIntegrable (fun s : ℝ => clusterPotentialRest m k
      (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s))) volume (0:ℝ) T := by
    refine intervalIntegrable_of_continuousOn_Ioo_of_le (g := fun s : ℝ => Cu / (ν / 2)) hT.le ?_ ?_ ?_
    · have hbumpcont : Continuous (fun s : ℝ => bumpPert δ T lam t₀ (stdPertVec m k i₀ δ) s) := by
        have heq : (fun s : ℝ => bumpPert δ T lam t₀ (stdPertVec m k i₀ δ) s)
            = fun s : ℝ => stdCoef δ T (|s - t₀| / lam)
                • (lam ^ ((2:ℝ)/3) • stdPertVec m k i₀ δ) := rfl
        rw [heq]
        exact (hcontCoef.comp
          ((continuous_abs.comp (continuous_id.sub continuous_const)).div_const lam)).smul
          continuous_const
      have hbc : ContinuousOn (fun s : ℝ => bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s))
          (Ioo (0:ℝ) T) := by
        have h2 : Continuous (fun s : ℝ =>
            bumpPert δ T lam t₀ (stdPertVec m k i₀ δ) (t₀ + lam * s)) :=
          hbumpcont.comp (by fun_prop)
        exact hγs2.add h2.continuousOn
      exact (continuousOn_clusterPotentialRest m k (by linarith : (0:ℝ) < ν / 2)).comp hbc
        (fun s hs => hsep2 s hs)
    · exact intervalIntegrable_const
    · intro t ht
      have hle := clusterPotentialRest_le (m := m) (k := k) (x :=
        bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * t)) (fun i => (hm i).le)
        (by linarith : (0:ℝ) < ν / 2) (hsep2 t ht)
      rw [abs_of_nonneg (clusterPotentialRest_nonneg (fun i => (hm i).le) k _)]
      calc clusterPotentialRest m k (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * t))
          ≤ Cu / (ν / 2) := by rw [hCu]; exact hle
        _ = Cu / (ν / 2) := rfl
  have hpiece6 : IntervalIntegrable (fun s : ℝ => clusterPotentialRest m k
      (γ (t₀ + lam * s))) volume (0:ℝ) T := by
    refine intervalIntegrable_of_continuousOn_Ioo_of_le (g := fun s : ℝ => Cu / ν) hT.le ?_ ?_ ?_
    · refine (continuousOn_clusterPotentialRest m k hν).comp hγs2 ?_
      intro s hs
      exact hsep s ⟨hs.1, le_of_lt hs.2⟩
    · exact intervalIntegrable_const
    · intro t ht
      have hle := clusterPotentialRest_le (m := m) (k := k)
        (x := γ (t₀ + lam * t)) (fun i => (hm i).le) hν (hsep t ⟨ht.1, le_of_lt ht.2⟩)
      rw [abs_of_nonneg (clusterPotentialRest_nonneg (fun i => (hm i).le) k _)]
      calc clusterPotentialRest m k (γ (t₀ + lam * t)) ≤ Cu / ν := by rw [hCu]; exact hle
        _ = Cu / ν := rfl
  exact ⟨hpiece1, hpiece2, hpiece3, hpiece4, hpiece5, hpiece6⟩

end Submission.NBody
