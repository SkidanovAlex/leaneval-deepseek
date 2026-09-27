import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLContract.Lemmas.Gamma3Facts
import Submission.Work.EKLComp.Misiurewicz.Defs
import Submission.Work.EKLComp.Core
import Submission.Work.EKLComp.Entropy
import Submission.Work.EKLComp.polishSpace_X3
import Submission.Work.EKLNonExc.VFacts
import Submission.Work.Misiurewicz.exists_V_mul_inv_subset
import Submission.Work.Misiurewicz.Vball_mem_nhds
import Submission.Work.Misiurewicz.vMove_lt_iff
import Submission.Work.Misiurewicz.closure_Vball_subset_vMove_le
import Submission.Work.Misiurewicz.exists_null_frontier_Vball_radius
import Submission.Work.Misiurewicz.exists_fine_null_frontier_partition
import Submission.Work.Misiurewicz.Hfam_sum_le
import Submission.Work.Misiurewicz.Hfam_joinSets_add
import Submission.Work.Misiurewicz.Hfam_winJoin_grid
import Submission.Work.Misiurewicz.Hfam_unifMeasure_eq_log
import Submission.Work.Misiurewicz.integral_misAvg_diff_le
import Submission.Work.Misiurewicz.window_sum_lower_bound
import Submission.Work.Misiurewicz.tendsto_Hfam_of_tendsto_of_null_frontier
import Submission.Work.Misiurewicz.misAvgMeasure_prob_supp
import Submission.Work.Misiurewicz.frontier_joinSets_smulMap_eq_zero
import Submission.Work.Misiurewicz.exists_weak_limit_misAvg

/-!
# C4a: the Misiurewicz construction (P_Misiurewicz)

Misiurewicz (Walters, Thm 8.6): positive topological entropy on a compact forward-invariant set
produces an invariant measure of positive Kolmogorov-Sinai entropy.
-/

namespace Work.EKLComp

open MeasureTheory Filter Topology
open Work.EKLContract
open scoped ENNReal
open BoundedContinuousFunction

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

noncomputable section

/-- Iterates of `smulMap g` preserve a forward invariant set. -/
theorem smulMap_iterate_mem {g : SL3} {K : Set X3} (hgK : forall x, x ∈ K -> g • x ∈ K) :
    forall n : ℕ, forall x, x ∈ K -> (smulMap g)^[n] x ∈ K := by
  intro n
  induction n with
  | zero => intro x hx; simpa using hx
  | succ m ih =>
      intro x hx
      rw [Function.iterate_succ_apply]
      exact ih _ (hgK x hx)

/-- The entropy of the uniform measure on `E` with respect to the join of an eps-fine partition
along `N` iterates equals `log |E|`, provided the points of `E` are (N,eps)-separated. -/
theorem Hfam_unifMeasure_joinSets_eq_log {g : SL3} {K : Set X3}
    (hgK : forall x, x ∈ K -> g • x ∈ K) {ε : ℝ} (hε : 0 < ε) {P : FinPart X3}
    (hP : forall i, (P.parts i ∩ K).Nonempty -> Fine ε (P.parts i))
    {N : ℕ} {E : Finset X3} (hEK : (E : Set X3) ⊆ K) (hsep : IsSeparated g N ε E) :
    Hfam (unifMeasure E) (joinSets (smulMap g) P N) = Real.log (E.card : ℝ) := by
  have hT : Measurable (smulMap g) := (continuous_smulMap g).measurable
  refine Work.Misiurewicz.Hfam_unifMeasure_eq_log E (joinSets (smulMap g) P N) ?_ ?_ ?_ ?_
  · exact joinSets_pairwise (smulMap g) P N
  · exact joinSets_iUnion (smulMap g) P N
  · intro w
    exact Work.EKLComp.Core.joinSets_measurable hT P N w
  · intro x hx y hy hxy
    by_contra hne
    obtain ⟨n, hn, hsep1⟩ := hsep x hx y hy hne
    obtain ⟨w, hwx⟩ : ∃ w, x ∈ joinSets (smulMap g) P N w := by
      rw [← Set.mem_iUnion, joinSets_iUnion]; exact Set.mem_univ x
    have hwy : y ∈ joinSets (smulMap g) P N w := (hxy w).mp hwx
    have hwx2 : ∀ k : Fin N, (smulMap g)^[k] x ∈ P.parts (w k) := by
      simpa only [joinSets, Set.mem_preimage, Set.mem_iInter] using hwx
    have hwy2 : ∀ k : Fin N, (smulMap g)^[k] y ∈ P.parts (w k) := by
      simpa only [joinSets, Set.mem_preimage, Set.mem_iInter] using hwy
    have hnx : (smulMap g)^[n] x ∈ P.parts (w ⟨n, hn⟩) := hwx2 ⟨n, hn⟩
    have hny : (smulMap g)^[n] y ∈ P.parts (w ⟨n, hn⟩) := hwy2 ⟨n, hn⟩
    have hxK : (smulMap g)^[n] x ∈ K := smulMap_iterate_mem hgK n x (hEK hx)
    have hfine := hP (w ⟨n, hn⟩) ⟨_, hnx, hxK⟩
    apply hsep1
    simpa only [smulMap_iterate_apply] using hfine _ hnx _ hny

/-- **C4a**: the Misiurewicz half of the variational principle. -/
theorem prove_Misiurewicz : Work.EKLContract.P_Misiurewicz := by
  classical
  haveI hGcl : IsClosed (Γ3 : Set SL3) := Work.EKLContract.Lemmas.isClosed_Γ3
  haveI hT2 : T2Space X3 := inferInstance
  intro g K hK hgK hpos
  obtain ⟨ε, hε, cc, hcc, hspec⟩ := hpos
  have hex : forall j : ℕ, ∃ N : ℕ, j + 1 ≤ N ∧ ∃ E : Finset X3,
      (E : Set X3) ⊆ K ∧ IsSeparated g N ε E ∧ Real.exp (cc * (N : ℝ)) ≤ (E.card : ℝ) :=
    fun j => hspec (j + 1)
  choose a ha hE using hex
  choose E hEK hEsep hEcard using hE
  have ha1 : forall j : ℕ, 1 ≤ a j := by
    intro j
    have h := ha j
    omega
  have hEne : forall j : ℕ, (E j).Nonempty := by
    intro j
    have h1 : (1 : ℝ) ≤ ((E j).card : ℝ) := by
      have h2 : (1 : ℝ) ≤ Real.exp (cc * (a j : ℝ)) := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by positivity)
      linarith [hEcard j]
    exact Finset.card_pos.mp (by exact_mod_cast h1)
  have hatend : Tendsto a atTop atTop :=
    tendsto_atTop_mono (fun j => ha j) (tendsto_add_atTop_nat 1)
  obtain ⟨ν, hνprob, φ, hφmono, hνK, hνinv, hνlim⟩ :=
    Work.Misiurewicz.exists_weak_limit_misAvg K hK g hgK a hatend E hEK hEne
  haveI := hνprob
  obtain ⟨P, hPfine, hPfront⟩ :=
    Work.Misiurewicz.exists_fine_null_frontier_partition K hK ε hε ν hνK
  have hT : Measurable (smulMap g) := (continuous_smulMap g).measurable
  have hprobU : forall j : ℕ, IsProbabilityMeasure (unifMeasure (E j)) :=
    fun j => ⟨Work.Misiurewicz.unifMeasure_univ (E j) (hEne j)⟩
  have hlog : forall j : ℕ, cc * (a j : ℝ) ≤ Real.log ((E j).card : ℝ) := by
    intro j
    have h2 : Real.log (Real.exp (cc * (a j : ℝ))) ≤ Real.log ((E j).card : ℝ) :=
      Real.log_le_log (Real.exp_pos _) (hEcard j)
    rwa [Real.log_exp] at h2
  have hstep : forall j : ℕ, Hfam (unifMeasure (E j)) (joinSets (smulMap g) P (a j)) =
      Real.log ((E j).card : ℝ) :=
    fun j => Hfam_unifMeasure_joinSets_eq_log hgK hε hPfine (hEK j) (hEsep j)
  have hkey : forall (M : ℕ), 1 ≤ M -> forall j : ℕ, 2 * M ≤ a j ->
      (M : ℝ) * cc - (2 * (M : ℝ) * ((M : ℝ) - 1) * Real.log (P.n : ℝ)) / (a j : ℝ) ≤
        Hfam (misAvgMeasure g (a j) (unifMeasure (E j))) (joinSets (smulMap g) P M) := by
    intro M hM j hj
    have hposj : (0 : ℝ) < (a j : ℝ) := by
      have h := ha1 j
      positivity
    have hwin : (M : ℝ) * (cc * (a j : ℝ) - 2 * ((M : ℝ) - 1) * Real.log (P.n : ℝ)) ≤
        ∑ k ∈ Finset.range (a j), Hfam (unifMeasure (E j)) (winJoin (smulMap g) P k M) :=
      haveI : IsProbabilityMeasure (unifMeasure (E j)) := hprobU j
      Work.Misiurewicz.window_sum_lower_bound (unifMeasure (E j)) (smulMap g) hT P M
        (a j) hM hj (cc * (a j : ℝ)) (by rw [hstep j]; exact hlog j)
    have hwin2 : (M : ℝ) * (cc * (a j : ℝ) - 2 * ((M : ℝ) - 1) * Real.log (P.n : ℝ)) ≤
        ∑ k : Fin (a j), Hfam (unifMeasure (E j)) (winJoin (smulMap g) P (k : ℕ) M) := by
      rw [Finset.sum_range] at hwin
      exact hwin
    have hc1 : (∑ _k : Fin (a j), ((a j : ℝ))⁻¹) ≤ 1 := by
      have hne : (a j : ℝ) ≠ 0 := by
        have h : (1 : ℝ) ≤ (a j : ℝ) := by exact_mod_cast ha1 j
        linarith
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_inv_cancel₀ hne]
    haveI hmap_prob : forall k : Fin (a j),
        IsProbabilityMeasure (Measure.map (smulMap (g ^ (k : ℕ))) (unifMeasure (E j))) :=
      fun k => inferInstance
    have hconc : ∑ k : Fin (a j), ((a j : ℝ))⁻¹ *
          Hfam (Measure.map (smulMap (g ^ (k : ℕ))) (unifMeasure (E j)))
            (joinSets (smulMap g) P M)
        ≤ Hfam (∑ k : Fin (a j), ENNReal.ofReal ((a j : ℝ))⁻¹ •
            Measure.map (smulMap (g ^ (k : ℕ))) (unifMeasure (E j)))
          (joinSets (smulMap g) P M) :=
      Work.Misiurewicz.Hfam_sum_le (joinSets (smulMap g) P M)
        (fun _ : Fin (a j) => ((a j : ℝ))⁻¹) (fun _ => by positivity) hc1
        (fun k : Fin (a j) => Measure.map (smulMap (g ^ (k : ℕ))) (unifMeasure (E j)))
    have hmap : forall k : Fin (a j),
        Hfam (Measure.map (smulMap (g ^ (k : ℕ))) (unifMeasure (E j)))
            (joinSets (smulMap g) P M) =
          Hfam (unifMeasure (E j)) (winJoin (smulMap g) P (k : ℕ) M) := by
      intro k
      unfold Hfam
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [Measure.map_apply (continuous_smulMap (g ^ (k : ℕ))).measurable
        (Work.EKLComp.Core.joinSets_measurable hT P M w)]
      congr 1
      rw [winJoin_eq_preimage, smulMap_iterate]
    have hmeasure : (∑ k : Fin (a j), ENNReal.ofReal ((a j : ℝ))⁻¹ •
            Measure.map (smulMap (g ^ (k : ℕ))) (unifMeasure (E j)))
        = misAvgMeasure g (a j) (unifMeasure (E j)) := by
      have hsum : (∑ k : Fin (a j), Measure.map (smulMap (g ^ (k : ℕ))) (unifMeasure (E j)))
          = ∑ k ∈ Finset.range (a j), Measure.map (smulMap (g ^ (k : ℕ))) (unifMeasure (E j)) := by
        rw [Finset.sum_range]
      rw [← Finset.smul_sum, hsum, misAvgMeasure, ENNReal.ofReal_inv_of_pos (by positivity),
        ENNReal.ofReal_natCast]
    have hmix : ((a j : ℝ))⁻¹ * (∑ k : Fin (a j),
          Hfam (unifMeasure (E j)) (winJoin (smulMap g) P (k : ℕ) M))
        ≤ Hfam (misAvgMeasure g (a j) (unifMeasure (E j))) (joinSets (smulMap g) P M) := by
      have h3 : ((a j : ℝ))⁻¹ * (∑ k : Fin (a j),
            Hfam (unifMeasure (E j)) (winJoin (smulMap g) P (k : ℕ) M))
          = ∑ k : Fin (a j), ((a j : ℝ))⁻¹ *
            Hfam (Measure.map (smulMap (g ^ (k : ℕ))) (unifMeasure (E j)))
              (joinSets (smulMap g) P M) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by rw [hmap k]
      rw [h3]
      rw [hmeasure] at hconc
      exact hconc
    have halg : ((a j : ℝ))⁻¹ * ((M : ℝ) * (cc * (a j : ℝ) -
        2 * ((M : ℝ) - 1) * Real.log (P.n : ℝ))) =
        (M : ℝ) * cc - (2 * (M : ℝ) * ((M : ℝ) - 1) * Real.log (P.n : ℝ)) / (a j : ℝ) := by
      field_simp
      try ring
    have hstep2 := mul_le_mul_of_nonneg_left hwin2 (by positivity : (0 : ℝ) ≤ ((a j : ℝ))⁻¹)
    rw [halg] at hstep2
    linarith [hstep2, hmix]
  have hφge : forall j : ℕ, j ≤ φ j := by
    intro j
    induction j with
    | zero => exact Nat.zero_le _
    | succ m ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hφmono (Nat.lt_succ_self m)))
  have htransfer : forall M : ℕ, 1 ≤ M -> (M : ℝ) * cc ≤ Hfam ν (joinSets (smulMap g) P M) := by
    intro M hM
    have hnull := Work.Misiurewicz.frontier_joinSets_smulMap_eq_zero ν g hνinv P hPfront
    have hφj_prob : forall j : ℕ,
        IsProbabilityMeasure (misAvgMeasure g (a (φ j)) (unifMeasure (E (φ j)))) :=
      fun j => (Work.Misiurewicz.misAvgMeasure_prob_supp g K hgK (E (φ j)) (hEK (φ j))
        (hEne (φ j)) (lt_of_lt_of_le (by norm_num) (ha1 (φ j)))).1
    let νjPM : ℕ -> ProbabilityMeasure X3 := fun j =>
      ⟨misAvgMeasure g (a (φ j)) (unifMeasure (E (φ j))), hφj_prob j⟩
    let νPM : ProbabilityMeasure X3 := ⟨ν, hνprob⟩
    have hsub : Tendsto νjPM atTop (nhds νPM) := by
      refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr fun f => ?_
      simpa only [νjPM, νPM, ProbabilityMeasure.toMeasure] using hνlim f
    have htend := Work.Misiurewicz.tendsto_Hfam_of_tendsto_of_null_frontier νPM νjPM hsub
      (joinSets (smulMap g) P M) (hnull M)
    have hbound : ∀ᶠ j in atTop, (M : ℝ) * cc - (2 * (M : ℝ) * ((M : ℝ) - 1) *
        Real.log (P.n : ℝ)) / (a (φ j) : ℝ)
          ≤ Hfam (νjPM j : Measure X3) (joinSets (smulMap g) P M) := by
      filter_upwards [Filter.eventually_ge_atTop (2 * M)] with j hj
      have h2M : 2 * M ≤ a (φ j) := by
        have h1 := ha (φ j)
        have h2 := hφge j
        omega
      exact hkey M hM (φ j) h2M
    have hconst : Tendsto (fun j => (M : ℝ) * cc - (2 * (M : ℝ) * ((M : ℝ) - 1) *
        Real.log (P.n : ℝ)) / (a (φ j) : ℝ)) atTop (nhds ((M : ℝ) * cc)) := by
      have h1 : Tendsto (fun j => ((a (φ j) : ℕ) : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_iff.mpr (hatend.comp hφmono.tendsto_atTop)
      have h2 : Tendsto (fun j => (2 * (M : ℝ) * ((M : ℝ) - 1) * Real.log (P.n : ℝ)) /
          (a (φ j) : ℝ)) atTop (nhds 0) :=
        Filter.Tendsto.div_atTop tendsto_const_nhds h1
      simpa using (tendsto_const_nhds.sub h2)
    exact le_of_tendsto_of_tendsto hconst htend hbound
  have hhPart : cc ≤ hPart ν (smulMap g) P := by
    refine le_ciInf fun N => ?_
    have hN1 : 1 ≤ N + 1 := Nat.succ_le_succ (Nat.zero_le N)
    have h1 := htransfer (N + 1) hN1
    have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    rw [le_div_iff₀ hpos]
    push_cast at h1 ⊢
    linarith
  refine ⟨ν, hνprob, hνK, hνinv, ?_⟩
  have hpos2 : (0 : ℝ) < hPart ν (smulMap g) P := lt_of_lt_of_le hcc hhPart
  calc (0 : ℝ≥0∞) < ENNReal.ofReal (hPart ν (smulMap g) P) := by
        rw [ENNReal.ofReal_pos]; exact hpos2
    _ ≤ ent ν (smulMap g) :=
        le_iSup (fun Q : FinPart X3 => ENNReal.ofReal (hPart ν (smulMap g) Q)) P

end

end Work.EKLComp
