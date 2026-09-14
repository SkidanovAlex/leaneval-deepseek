import Submission.NBody.MarchalClusterMomentum
import Submission.NBody.MarchalMultiEnergy
import Submission.NBody.MarchalCollisionSolutionData
import Submission.NBody.EnergyAe
import Submission.NBody.EnergyLevel
import Submission.NBody.Action
import Submission.NBody.LYZIoc

/-!
# A lower bound for the relative energy of a family of colliding clusters

The hypothesis `hE` of the isolatedness argument (`isolated_of_local_min_multi`) requires a uniform
lower bound for the *sum* of the relative energies of the collision classes near a locally minimal
collision.  We obtain it from the energy identity together with the boundedness of the "slow"
quantities:

* at a collision-free point of an `h`-minimiser the energy equals the level `h`
  (`energy_eq_level_at`);
* the momentum of every cluster which is separated from its complement is bounded
  (`exists_norm_clusterMomentum_le`), which bounds the velocity of each body outside the colliding
  classes, of each colliding cluster, and the velocity of the centre of mass of each cluster;
* the interaction potential of the pairs which are not internal to a class is non-negative.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-! ## 1. The energy at a collision-free point -/

/-- **The energy of an `h`-minimiser at a collision-free interior point is `h`.**  Around a
collision-free point the motion is collision free on a whole interval, so the minimiser restricted
to it has constant energy (and the energy is continuous there). -/
theorem energy_eq_level_at {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N} {a b t : ℝ}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hab : a < b)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hmin : IsHMinimizer m h γ a b) (hfin : ∀ x y : EN E N, actionPot m h x y < ⊤)
    (ht : t ∈ Ioo a b) (hnc : WithoutCollisions (γ t)) :
    energy m γ t = h := by
  classical
  have hγcont : ContinuousOn γ (Set.Icc a b) := by
    have h := hac.continuousOn
    rwa [Set.uIcc_of_le hab.le] at h
  have hγc : ContinuousAt γ t := hγcont.continuousAt (Icc_mem_nhds ht.1 ht.2)
  have hnc_open : IsOpen {x : EN E N | WithoutCollisions x} := by
    simpa [Set.compl_ofPred] using isClosed_collisions.isOpen_compl
  have hnbd : {s : ℝ | s ∈ Set.Ioo a b ∧ WithoutCollisions (γ s)} ∈ 𝓝 t :=
    inter_mem (Ioo_mem_nhds ht.1 ht.2) (hγc.preimage_mem_nhds (hnc_open.mem_nhds hnc))
  obtain ⟨δ, hδpos, hδsub⟩ : ∃ δ > 0, ∀ s, |s - t| < δ →
      s ∈ Set.Ioo a b ∧ WithoutCollisions (γ s) := by
    obtain ⟨U, hUsub, hUopen, htU⟩ := _root_.mem_nhds_iff.mp hnbd
    obtain ⟨δ, hδpos, hδball⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds htU)
    exact ⟨δ, hδpos, fun s hs => hUsub (hδball (by simpa [Metric.mem_ball, Real.dist_eq] using hs))⟩
  -- a half-length which keeps the interval inside `(a,b)`
  set δ' : ℝ := min (δ / 2) (min ((b - t) / 2) ((t - a) / 2)) with hδ'def
  have hδ'pos : 0 < δ' :=
    lt_min (by linarith) (lt_min (by linarith [ht.2]) (by linarith [ht.1]))
  have hδ'le : δ' ≤ δ / 2 := min_le_left _ _
  have hδ'b : t + δ' < b := by
    have h1 : δ' ≤ (b - t) / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hδ'a : a < t - δ' := by
    have h1 : δ' ≤ (t - a) / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  have hIcc : ∀ s ∈ Set.Icc (t - δ') (t + δ'),
      s ∈ Set.Ioo a b ∧ WithoutCollisions (γ s) := by
    intro s hs
    refine hδsub s ?_
    have h1 : |s - t| ≤ δ' := by
      rw [abs_le]
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    linarith [hδ'le, hδpos]
  have hacI : AbsolutelyContinuousOnInterval γ (t - δ') (t + δ') :=
    hac.mono (by
      rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le hab.le]
      exact Set.Icc_subset_Icc (le_of_lt hδ'a) (le_of_lt hδ'b))
  have hOn : actionOn m h γ a b < ⊤ := by rw [hmin]; exact hfin (γ a) (γ b)
  have hminI : IsHMinimizer m h γ (t - δ') (t + δ') :=
    hmin.sub hac hOn (by linarith [ht.1, hδ'pos]) (by linarith [hδ'pos]) (by linarith [ht.2, hδ'pos])
  -- shift to `[0, 2 δ']`
  set x : ℝ → EN E N := fun u => γ (u + (t - δ')) with hxdef
  have hacx : AbsolutelyContinuousOnInterval x 0 (2 * δ') := by
    have h := Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_comp_affine
      (f := γ) (a := t - δ') (b := t + δ') (c := 1) (d := t - δ') one_ne_zero hacI
    have h2 : (fun u : ℝ => γ (1 * u + (t - δ'))) = x := by
      funext u; rw [hxdef]; ring_nf
    rw [h2] at h
    simp only [div_one] at h
    rw [show t - δ' - (t - δ') = 0 by ring,
      show t + δ' - (t - δ') = 2 * δ' by ring] at h
    exact h
  have hncx : ∀ u ∈ Set.Icc 0 (2 * δ'), WithoutCollisions (x u) := by
    intro u hu
    have hu' : u + (t - δ') ∈ Set.Icc (t - δ') (t + δ') :=
      ⟨by linarith [hu.1], by linarith [hu.2]⟩
    rw [hxdef]
    exact (hIcc _ hu').2
  have hminx : IsHMinimizer m h x 0 (2 * δ') := by
    have h1 : actionOn m h x 0 (2 * δ') = actionOn m h γ (t - δ') (t + δ') := by
      have h := actionOn_comp_add_const' (m := m) (h := h) (γ := γ)
        (c := t - δ') (d := t + δ')
      have h2 : (fun u : ℝ => γ (u + (t - δ'))) = x := by
        funext u; rw [hxdef]
      rw [h2] at h
      rw [show (t + δ') - (t - δ') = 2 * δ' from by ring] at h
      exact h
    have hx0 : x 0 = γ (t - δ') := by rw [hxdef]; simp
    have hx2 : x (2 * δ') = γ (t + δ') := by rw [hxdef]; congr 1; ring_nf
    show actionOn m h x 0 (2 * δ') = actionPot m h (x 0) (x (2 * δ'))
    rw [h1, hx0, hx2]
    exact hminI
  have hfinx : actionPot m h (x 0) (x (2 * δ')) < ⊤ := hfin _ _
  have hδ'mem : δ' ∈ Set.Ioo (0:ℝ) (2 * δ') := ⟨hδ'pos, by linarith [hδ'pos]⟩
  have henergy := minimizer_energy_eq_level hm hh (by linarith [hδ'pos]) hacx hncx hminx hfinx δ' hδ'mem
  have hxmid : x δ' = γ t := by rw [hxdef]; congr 1; ring_nf
  have hdxmid : deriv x δ' = deriv γ t := by
    rw [hxdef, deriv_comp_add_const]
    congr 1
    ring_nf
  have henergy' : energy m x δ' = energy m γ t := by
    rw [energy, energy, hxmid, hdxmid]
  rw [henergy'] at henergy
  exact henergy

/-! ## 2. The lower bound for the sum of the relative energies -/

/-- **A lower bound for the sum of the relative energies of a family of clusters.**  Near a
collision of the clusters `ks`, at every point where the clusters are (internally) non-degenerate
and the motion is collision free, the sum of the centre-of-mass-relative energies is bounded below.
The proof uses the conservation of energy, the boundedness of the momentum of the cluster and of
each body outside it (which bounds the centre-of-mass and outside velocities), and the
non-negativity of the interaction potential of the pairs which are not internal to a cluster. -/
theorem exists_multiRelEnergy_lower_bound {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N}
    {a b A B ν : ℝ} {ks : Finset (Finset (Fin N))}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hab : a < b)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hmin : IsHMinimizer m h γ a b) (hfin : ∀ x y : EN E N, actionPot m h x y < ⊤)
    (hAB : A < B) (hAsub : a < A) (hBsub : B < b)
    (hν : 0 < ν) (hne : ∀ k ∈ ks, k.Nonempty)
    (hedj : ∀ k ∈ ks, ∀ k' ∈ ks, k ≠ k' → Disjoint k k')
    (hsep : ∀ t ∈ Icc A B, ∀ k ∈ ks, ClusterSeparatedWeak k (γ t) ν)
    (hsepT : ∀ t ∈ Icc A B, ∀ i ∉ multiUnion ks, ∀ j ∉ multiUnion ks, i ≠ j → ν ≤ r (γ t) i j)
    (hncW : ∀ t ∈ Ioo A B, 0 < multiInertia m ks (γ t) → WithoutCollisions (γ t)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo A B, 0 < multiInertia m ks (γ t) →
      -C ≤ multiRelEnergy m ks (γ t) (deriv γ t) := by
  classical
  have hacI : AbsolutelyContinuousOnInterval γ A B :=
    hac.mono (by
      rw [Set.uIcc_of_le hAB.le, Set.uIcc_of_le hab.le]
      exact Set.Icc_subset_Icc (le_of_lt hAsub) (le_of_lt hBsub))
  have hOn : actionOn m h γ a b < ⊤ := by rw [hmin]; exact hfin (γ a) (γ b)
  have hminI : IsHMinimizer m h γ A B := hmin.sub hac hOn hAsub hAB hBsub
  -- the velocity of every body outside the clusters is bounded
  have hCi : ∀ i : Fin N, ∃ C : ℝ, i ∉ multiUnion ks → ∀ t ∈ Ioo A B,
      WithoutCollisions (γ t) → ‖deriv γ t i‖ ≤ C := by
    intro i
    by_cases hi : i ∈ multiUnion ks
    · exact ⟨0, fun hi' => False.elim (hi' hi)⟩
    · have hsepi : ∀ t ∈ Icc A B, ClusterSeparatedWeak ({i} : Finset (Fin N)) (γ t) ν := by
        intro t ht j hj l hl
        simp only [Finset.mem_singleton] at hj hl
        rw [hj]
        by_cases hl' : l ∈ multiUnion ks
        · obtain ⟨k, hk, hlk⟩ := Finset.mem_biUnion.mp hl'
          have h1 : ν ≤ r (γ t) l i :=
            hsep t ht k hk l hlk i (fun hik => hi (Finset.mem_biUnion.mpr ⟨k, hk, hik⟩))
          rwa [show r (γ t) l i = r (γ t) i l from by
            rw [r_eq_norm_sub, r_eq_norm_sub, norm_sub_rev]] at h1
        · exact hsepT t ht i hi l hl' (Ne.symm hl)
      obtain ⟨C, hC⟩ :=
        exists_norm_clusterMomentum_le hm hh hAB hacI hminI hfin hν hsepi
      refine ⟨C / m i, fun _ t ht hnc => ?_⟩
      have h1 := hC t ht hnc
      have h2 : clusterMomentum m ({i} : Finset (Fin N)) (deriv γ t) = m i • deriv γ t i := by
        show (∑ j ∈ ({i} : Finset (Fin N)), m j • deriv γ t j) = m i • deriv γ t i
        rw [Finset.sum_singleton]
      rw [h2, norm_smul, Real.norm_eq_abs, abs_of_pos (hm i)] at h1
      rw [le_div_iff₀ (hm i)]
      linarith
  choose Ci hCi using hCi
  -- the kinetic energy of the centre of mass of every cluster is bounded
  have hCk : ∀ k : Finset (Fin N), ∃ C : ℝ, k ∈ ks → ∀ t ∈ Ioo A B,
      WithoutCollisions (γ t) → clusterMass m k * ‖clusterCM m k (deriv γ t)‖ ^ 2 ≤ C := by
    intro k
    by_cases hk : k ∈ ks
    · obtain ⟨C, hC⟩ := exists_norm_clusterMomentum_le hm hh hAB hacI hminI hfin hν
        (fun t ht => hsep t ht k hk)
      refine ⟨C ^ 2 / clusterMass m k, fun _ t ht hnc => ?_⟩
      have hmk : 0 < clusterMass m k := Finset.sum_pos (fun i _ => hm i) (hne k hk)
      have h1 := hC t ht hnc
      have h2 : clusterCM m k (deriv γ t)
          = (clusterMass m k)⁻¹ • clusterMomentum m k (deriv γ t) :=
        clusterCM_eq_inv_smul_clusterMomentum k (deriv γ t)
      rw [h2, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hmk)]
      have h3 : clusterMass m k * ((clusterMass m k)⁻¹ * ‖clusterMomentum m k (deriv γ t)‖) ^ 2
          ≤ clusterMass m k * ((clusterMass m k)⁻¹ * C) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ hmk.le
        refine pow_le_pow_left₀ (by positivity) ?_ 2
        exact mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hmk.le)
      refine h3.trans (le_of_eq ?_)
      rw [eq_div_iff (ne_of_gt hmk)]
      field_simp
    · exact ⟨0, fun hk' => absurd hk' hk⟩
  choose Ck hCk using hCk
  set Cbig : ℝ := (∑ i ∈ (multiUnion ks)ᶜ, m i * Ci i ^ 2) / 2
      + (∑ k ∈ ks, max (Ck k) 0) / 2 with hCbigdef
  have hCbignn : 0 ≤ Cbig := by
    rw [hCbigdef]
    refine add_nonneg (div_nonneg ?_ (by norm_num)) (div_nonneg ?_ (by norm_num))
    · exact Finset.sum_nonneg fun i _ => mul_nonneg (hm i).le (sq_nonneg _)
    · exact Finset.sum_nonneg fun k _ => le_max_right _ _
  refine ⟨max 0 (Cbig - h), le_max_left _ _, fun t ht hFt => ?_⟩
  have hnc : WithoutCollisions (γ t) := hncW t ht hFt
  have henergy : energy m γ t = h :=
    energy_eq_level_at hm hh hab hac hmin hfin
      ⟨by linarith [hAsub, ht.1], by linarith [hBsub, ht.2]⟩ hnc
  have hout : multiOutsideKineticSq m ks (deriv γ t) / 2
      ≤ (∑ i ∈ (multiUnion ks)ᶜ, m i * Ci i ^ 2) / 2 := by
    rw [show multiOutsideKineticSq m ks (deriv γ t)
        = ∑ i ∈ (multiUnion ks)ᶜ, m i * ‖deriv γ t i‖ ^ 2 from rfl]
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    refine Finset.sum_le_sum fun i hi => ?_
    have h1 : ‖deriv γ t i‖ ≤ Ci i := hCi i (Finset.mem_compl.mp hi) t ht hnc
    have h2 : ‖deriv γ t i‖ ^ 2 ≤ Ci i ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    exact mul_le_mul_of_nonneg_left h2 (hm i).le
  have hcm : multiCMKineticSq m ks (deriv γ t) / 2
      ≤ (∑ k ∈ ks, max (Ck k) 0) / 2 := by
    rw [show multiCMKineticSq m ks (deriv γ t)
        = ∑ k ∈ ks, clusterMass m k * ‖clusterCM m k (deriv γ t)‖ ^ 2 from rfl]
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    refine Finset.sum_le_sum fun k hk => ?_
    exact (hCk k hk t ht hnc).trans (le_max_left _ _)
  have hrest : 0 ≤ multiRestPotential m ks (γ t) := by
    rw [multiRestPotential_eq hedj]
    refine Finset.sum_nonneg fun p _ => ?_
    exact mul_nonneg (mul_nonneg (hm p.1).le (hm p.2).le)
      (inv_nonneg.mpr (by rw [r_eq_norm_sub]; exact norm_nonneg _))
  rw [multiRelEnergy_eq m ks hm hne hedj γ t, henergy, hCbigdef]
  linarith [hout, hcm, hrest, le_max_left (0:ℝ) (Cbig - h), le_max_right (0:ℝ) (Cbig - h)]

end Submission.NBody
