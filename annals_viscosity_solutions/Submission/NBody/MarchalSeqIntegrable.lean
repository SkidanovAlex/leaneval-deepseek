import Submission.NBody.MarchalBumpIntegrable
import Submission.NBody.MarchalSeqBump

/-!
# Integrability of the six pieces of the transfer identity, good-direction version

The module `Submission.NBody.MarchalBumpIntegrable` discharges the six integrability hypotheses of
`bump_real_action_eq` in the *outward sign* geometry (route A).  The circle-average route (route B)
has no sign condition; the bumped configuration is only known to be *quantitatively separated*
(`seq_bumped_pair_lower`), which provides exactly the two inputs used in piece 3: the absence of
collisions inside the cluster and the potential bound `Cp2 t^{-2/3}`.
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

theorem bump_pieces_intervalIntegrable_good {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {k : Finset (Fin N)}
    {i₀ : Fin N} (hi₀ : i₀ ∈ k) {δ : E} (hδ : δ ≠ 0) {lam T t₀ : ℝ} (hlam : 0 < lam)
    (hT : 0 < T) {γ : ℝ → EN E N}
    (hac : AbsolutelyContinuousOnInterval γ t₀ (t₀ + lam * T))
    (hncI : ∀ t ∈ Ioo t₀ (t₀ + lam * T), WithoutCollisions (γ t))
    {Cd Cp Cp2 ν : ℝ} (hCd : 0 ≤ Cd) (hCp : 0 ≤ Cp) (hCp2 : 0 ≤ Cp2) (hν : 0 < ν)
    (hvel : ∀ t ∈ Ioc (0:ℝ) T,
      ‖deriv (bumpRescaled m k γ t₀ lam) t‖_[m] ≤ Cd * t ^ (-(1:ℝ)/3))
    (hUpot : ∀ t ∈ Ioc (0:ℝ) T,
      clusterPotential m k (bumpRescaled m k γ t₀ lam t) ≤ Cp * t ^ (-(2:ℝ)/3))
    (hnnB : ∀ t ∈ Ioo (0:ℝ) T, ClusterNoColl k
      (bumpRescaled m k γ t₀ lam t + stdVarVec m k i₀ δ T t))
    (hUpotB : ∀ t ∈ Ioc (0:ℝ) T,
      clusterPotential m k (bumpRescaled m k γ t₀ lam t + stdVarVec m k i₀ δ T t)
        ≤ Cp2 * t ^ (-(2:ℝ)/3))
    (hsep : ∀ t ∈ Ioc (0:ℝ) T, ClusterSeparatedWeak k (γ (t₀ + lam * t)) ν)
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
        (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s))
          - clusterPotentialRest m k (γ (t₀ + lam * s))) volume (0:ℝ) T := by
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
    refine intervalIntegrable_of_continuousOn_Ioo_of_le
      (g := fun s : ℝ => Cp2 * s ^ (-(2:ℝ)/3)) hT.le ?_ ?_ ?_
    · refine (continuousOn_clusterPotential m k).comp
        (hqcont.add (hdcont.continuousOn.mono (Set.subset_univ _))) ?_
      intro s hs
      exact hnnB s hs
    · exact hmajpow Cp2 (-(2:ℝ)/3) (by norm_num)
    · intro t ht
      have htIoc : t ∈ Ioc (0:ℝ) T := ⟨ht.1, le_of_lt ht.2⟩
      rw [abs_of_nonneg (clusterPotential_nonneg (fun i => (hm i).le) k _)]
      exact hUpotB t htIoc
  have hpiece4 : IntervalIntegrable (fun s : ℝ => clusterPotential m k
      (bumpRescaled m k γ t₀ lam s)) volume (0:ℝ) T := by
    refine intervalIntegrable_of_continuousOn_Ioo_of_le (g := fun s : ℝ => Cp * s ^ (-(2:ℝ)/3)) hT.le ?_ ?_ ?_
    · exact (continuousOn_clusterPotential m k).comp hqcont fun s hs => hnn s hs
    · exact hmajpow Cp (-(2:ℝ)/3) (by norm_num)
    · intro t ht
      have htIoc : t ∈ Ioc (0:ℝ) T := ⟨ht.1, le_of_lt ht.2⟩
      rw [abs_of_nonneg (clusterPotential_nonneg (fun i => (hm i).le) k _)]
      exact hUpot t htIoc
  have hν2 : (0:ℝ) < ν / 2 := by linarith
  have hρν : 2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) ≤ ν := by linarith
  have hρν2 : 2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) ≤ ν / 2 := by linarith
  have hsep2 : ∀ t ∈ Ioo (0:ℝ) T,
      ClusterSeparatedWeak k (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * t)) (ν / 2) := by
    intro t ht i hi j hj
    have htIoc : t ∈ Ioc (0:ℝ) T := ⟨ht.1, le_of_lt ht.2⟩
    have hpert : ∀ j : Fin N, ‖bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * t) j
        - γ (t₀ + lam * t) j‖ ≤ lam ^ ((2:ℝ)/3) * ‖δ‖ := by
      intro j
      by_cases hj : j ∈ k
      · exact bumpCurve_pert_le hm hi₀ hlam ht.1.le hj
      · rw [bumpCurve_eq_of_notMem (m := m) (k := k) hlam ht.1.le hj, sub_self, norm_zero]
        exact hρnn
    have hbase : ν ≤ r (γ (t₀ + lam * t)) i j := hsep t htIoc i hi j hj
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
  -- the collision-freeness of the shifted curve, in the `Ioo 0 T` parametrisation
  have hncI' : ∀ s ∈ Ioo (0:ℝ) T, WithoutCollisions (γ (t₀ + lam * s)) := by
    intro s hs
    have h1 : t₀ < t₀ + lam * s := by
      have : 0 < lam * s := mul_pos hlam hs.1
      linarith
    have h2 : t₀ + lam * s < t₀ + lam * T := by
      have : lam * s < lam * T := mul_lt_mul_of_pos_left hs.2 hlam
      linarith
    exact hncI _ ⟨h1, h2⟩
  -- the interaction-potential difference is interval integrable (its individual pieces need not be)
  have hpiece56 : IntervalIntegrable (fun s : ℝ => clusterPotentialRest m k
      (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s))
        - clusterPotentialRest m k (γ (t₀ + lam * s))) volume (0:ℝ) T := by
    refine intervalIntegrable_of_continuousOn_Ioo_of_le
      (g := fun _ : ℝ => Cu * (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / (ν / 2) ^ 2)) hT.le ?_
      intervalIntegrable_const ?_
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
      have h1 : ContinuousOn (fun s : ℝ => clusterPotentialRest m k
          (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s))) (Ioo (0:ℝ) T) :=
        (continuousOn_clusterPotentialRest_of_weak m k hν2).comp hbc (fun s hs =>
          ⟨hsep2 s hs, fun i hi j hj hij => by
            rw [bumpCurve_eq_of_notMem (m := m) (k := k) hlam hs.1.le hi,
              bumpCurve_eq_of_notMem (m := m) (k := k) hlam hs.1.le hj]
            exact ne_of_r_ne_zero (hncI' s hs i j hij)⟩)
      have h2 : ContinuousOn (fun s : ℝ => clusterPotentialRest m k (γ (t₀ + lam * s)))
          (Ioo (0:ℝ) T) :=
        (continuousOn_clusterPotentialRest_of_weak m k hν).comp hγs2 (fun s hs =>
          ⟨hsep s ⟨hs.1, le_of_lt hs.2⟩,
            fun i _ j _ hij => ne_of_r_ne_zero (hncI' s hs i j hij)⟩)
      exact h1.sub h2
    · intro t ht
      have htIoc : t ∈ Ioc (0:ℝ) T := ⟨ht.1, le_of_lt ht.2⟩
      have hup := clusterPotentialRest_diff_le (m := m) (k := k) (x := γ (t₀ + lam * t))
        (y := bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * t)) (ν := ν)
        (ρ := lam ^ ((2:ℝ)/3) * ‖δ‖) (fun i => (hm i).le) hν hρnn hρν
        (hsep t htIoc) (fun j hj => bumpCurve_eq_of_notMem (m := m) (k := k) hlam ht.1.le hj)
        (fun j hj => bumpCurve_pert_le hm hi₀ hlam ht.1.le hj)
      have hlo := clusterPotentialRest_diff_le (m := m) (k := k)
        (x := bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * t))
        (y := γ (t₀ + lam * t)) (ν := ν / 2) (ρ := lam ^ ((2:ℝ)/3) * ‖δ‖)
        (fun i => (hm i).le) hν2 hρnn hρν2 (hsep2 t ht)
        (fun j hj => (bumpCurve_eq_of_notMem (m := m) (k := k) hlam ht.1.le hj).symm)
        (fun j hj => by rw [norm_sub_rev]; exact bumpCurve_pert_le hm hi₀ hlam ht.1.le hj)
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · rw [neg_le, neg_sub]
        calc clusterPotentialRest m k (γ (t₀ + lam * t))
              - clusterPotentialRest m k (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * t))
            ≤ (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
                m p.1 * m p.2) * (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / (ν / 2) ^ 2) := hlo
          _ = Cu * (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / (ν / 2) ^ 2) := by rw [hCu]
      · calc clusterPotentialRest m k (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * t))
              - clusterPotentialRest m k (γ (t₀ + lam * t))
            ≤ (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
                m p.1 * m p.2) * (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / ν ^ 2) := hup
          _ ≤ Cu * (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / (ν / 2) ^ 2) := by
              rw [hCu]
              refine mul_le_mul_of_nonneg_left ?_
                (Finset.sum_nonneg fun p _ => mul_nonneg (hm _).le (hm _).le)
              exact div_le_div_of_nonneg_left (by linarith : (0:ℝ) ≤ 2 * (lam ^ ((2:ℝ)/3) * ‖δ‖))
                (by positivity) (by nlinarith [hν])
  exact ⟨hpiece1, hpiece2, hpiece3, hpiece4, hpiece56⟩

end Submission.NBody
