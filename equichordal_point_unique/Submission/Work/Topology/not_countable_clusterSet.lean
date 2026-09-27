import Mathlib
import Submission.Work.Topology.not_countable_of_isPreconnected_isCompact
import Submission.Work.Topology.isPreconnected_iInter_of_antitone_isCompact

namespace Work.Topology

open Filter Set

/-- The basic left-neighbourhoods `(1 - 1/(n+1), 1)` of `1` belong to `𝓝[<] 1`. -/
lemma Ioo_mem_nhdsWithin_Iio_one (n : ℕ) :
    Set.Ioo (1 - 1 / ((n : ℝ) + 1)) 1 ∈ nhdsWithin 1 (Set.Iio 1) :=
  (nhdsLT_basis 1).mem_iff.mpr
    ⟨1 - 1 / ((n : ℝ) + 1), sub_lt_self 1 (by positivity), subset_rfl⟩

/-- Every left-neighbourhood of `1` contains one of the intervals `(1 - 1/(n+1), 1)`. -/
lemma exists_Ioo_subset_of_mem_nhdsWithin_Iio_one {W : Set ℝ}
    (hW : W ∈ nhdsWithin 1 (Set.Iio 1)) :
    ∃ n : ℕ, Set.Ioo (1 - 1 / ((n : ℝ) + 1)) 1 ⊆ W := by
  obtain ⟨b, hb1, hbW⟩ := (nhdsLT_basis 1).mem_iff.mp hW
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (1 - b))
  refine ⟨N, fun x hx => hbW ⟨?_, hx.2⟩⟩
  have hb1' : (0 : ℝ) < 1 - b := by linarith
  have hN' : 1 / (1 - b) < (N : ℝ) + 1 := by linarith
  have hinv : 1 / ((N : ℝ) + 1) < 1 - b := by
    rw [div_lt_iff₀ (by positivity), mul_comm]
    exact (div_lt_iff₀ hb1').mp hN'
  linarith [hinv, hx.1]

theorem not_countable_clusterSet {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {γ : ℝ → X} (hcont : ContinuousOn γ (Set.Iio 1))
    (hlim : ¬ ∃ x : X, Filter.Tendsto γ (nhdsWithin 1 (Set.Iio 1)) (nhds x)) :
    ¬ ({x : X | MapClusterPt x (nhdsWithin 1 (Set.Iio 1)) γ} : Set X).Countable := by
  classical
  let K : ℕ → Set X := fun n => closure (γ '' Set.Ioo (1 - 1 / ((n : ℝ) + 1)) 1)
  have hKcpt : ∀ n, IsCompact (K n) := fun _ => isClosed_closure.isCompact
  have hKpre : ∀ n, IsPreconnected (K n) := by
    intro n
    have hI : IsPreconnected (Set.Ioo (1 - 1 / ((n : ℝ) + 1)) (1 : ℝ)) := isPreconnected_Ioo
    have hcont' : ContinuousOn γ (Set.Ioo (1 - 1 / ((n : ℝ) + 1)) (1 : ℝ)) :=
      hcont.mono (fun _ hx => hx.2)
    exact (hI.image γ hcont').closure
  have hKmono : Antitone K := by
    intro m n hmn
    apply closure_mono
    apply Set.image_mono
    intro x hx
    refine ⟨?_, hx.2⟩
    have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith [hx.1, hle]
  -- the cluster set is the decreasing intersection of the tail closures
  have hCsubK : ∀ n, {x : X | MapClusterPt x (nhdsWithin 1 (Set.Iio 1)) γ} ⊆ K n := by
    intro n x hx
    have hmem : γ '' Set.Ioo (1 - 1 / ((n : ℝ) + 1)) 1
        ∈ map γ (nhdsWithin 1 (Set.Iio 1)) := by
      rw [Filter.mem_map]
      exact mem_of_superset (Ioo_mem_nhdsWithin_Iio_one n) (subset_preimage_image γ _)
    have hx' : ClusterPt x (map γ (nhdsWithin 1 (Set.Iio 1))) := hx
    exact clusterPt_iff_forall_mem_closure.mp hx' _ hmem
  have hKsubC : (⋂ n, K n) ⊆ {x : X | MapClusterPt x (nhdsWithin 1 (Set.Iio 1)) γ} := by
    intro x hx
    have hx' : ∀ n, x ∈ K n := Set.mem_iInter.mp hx
    change ClusterPt x (map γ (nhdsWithin 1 (Set.Iio 1)))
    apply clusterPt_iff_forall_mem_closure.mpr
    intro s hs
    rw [Filter.mem_map] at hs
    obtain ⟨n, hnW⟩ := exists_Ioo_subset_of_mem_nhdsWithin_Iio_one hs
    refine (closure_mono ?_) (hx' n)
    exact (Set.image_mono hnW).trans (Set.image_preimage_subset γ s)
  have hCeq : {x : X | MapClusterPt x (nhdsWithin 1 (Set.Iio 1)) γ} = ⋂ n, K n := by
    apply Set.Subset.antisymm
    · intro x hx
      exact Set.mem_iInter.mpr (fun n => hCsubK n hx)
    · exact hKsubC
  have hpre : IsPreconnected {x : X | MapClusterPt x (nhdsWithin 1 (Set.Iio 1)) γ} := by
    rw [hCeq]
    exact isPreconnected_iInter_of_antitone_isCompact hKmono hKcpt hKpre
  have hcpt : IsCompact ({x : X | MapClusterPt x (nhdsWithin 1 (Set.Iio 1)) γ} : Set X) :=
    (isClosed_setOfPred_clusterPt (f := map γ (nhdsWithin 1 (Set.Iio 1)))).isCompact
  have hne : ({x : X | MapClusterPt x (nhdsWithin 1 (Set.Iio 1)) γ} : Set X).Nonempty := by
    haveI : NeBot (nhdsWithin (1 : ℝ) (Set.Iio (1 : ℝ))) := inferInstance
    obtain ⟨p, -, hp⟩ := (isCompact_univ (X := X)).exists_mapClusterPt
      (f := nhdsWithin 1 (Set.Iio 1)) (u := γ) (by rw [principal_univ]; exact le_top)
    exact ⟨p, hp⟩
  intro hcount
  obtain ⟨p, hp⟩ := hne
  have hsingle : ∀ x : X, MapClusterPt x (nhdsWithin 1 (Set.Iio 1)) γ → x = p := by
    intro x hx
    by_contra hxp
    refine (not_countable_of_isPreconnected_isCompact hpre hcpt ⟨p, hp, x, hx, ?_⟩) hcount
    exact fun h => hxp h.symm
  exact hlim ⟨p, tendsto_nhds_of_unique_mapClusterPt (f := γ)
    (l := nhdsWithin 1 (Set.Iio 1)) (y := p) hsingle⟩

end Work.Topology
