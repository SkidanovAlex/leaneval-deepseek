import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Order.CompletePartialOrder

namespace Commons.Topology.Plane

open Set Metric
open Filter
open scoped Topology

/-- In a compact Hausdorff space, a point outside the connected component of `x` is separated
from it by a clopen set. -/
lemma exists_isClopen_connectedComponent_separating {X : Type*} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] (x y : X) (hy : y ∉ connectedComponent x) :
    ∃ S : Set X, IsClopen S ∧ x ∈ S ∧ y ∉ S := by
  have h := connectedComponent_eq_iInter_isClopen x
  have hyi : y ∉ ⋂ s : { s : Set X // IsClopen s ∧ x ∈ s }, (s : Set X) := by
    rw [← h]; exact hy
  rw [Set.mem_iInter] at hyi
  push_neg at hyi
  obtain ⟨s, hs⟩ := hyi
  exact ⟨s.1, s.2.1, s.2.2, hs⟩

/-- **Boundary bumping.** In a compact connected metric space, if `U` is a proper open set and
`q` lies in the closure of `U`, then the connected component of `q` in `closure U` meets the
frontier of `U`. -/
lemma componentIn_closure_meets_frontier {X : Type*} [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] {U : Set X} (hUo : IsOpen U) (hUne : U ≠ Set.univ) {q : X}
    (hq : q ∈ closure U) :
    (connectedComponentIn (closure U) q ∩ frontier U).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hAcl : IsClosed (closure U) := isClosed_closure
  haveI : CompactSpace ↥(closure U) := isCompact_iff_compactSpace.mp hAcl.isCompact
  set qA : ↥(closure U) := ⟨q, hq⟩ with hqA
  have hCsubU : connectedComponentIn (closure U) q ⊆ U := by
    intro z hz
    have hzA : z ∈ closure U := connectedComponentIn_subset (closure U) q hz
    have hzfr : z ∉ frontier U := fun hzf => (Set.eq_empty_iff_forall_notMem.mp h) z ⟨hz, hzf⟩
    rw [closure_eq_self_union_frontier] at hzA
    rcases hzA with hzU | hzf
    · exact hzU
    · exact absurd hzf hzfr
  have sep : ∀ y : ↥(closure U), (y : X) ∉ U →
      ∃ S : Set ↥(closure U), IsClopen S ∧ qA ∈ S ∧ y ∉ S := by
    intro y hyU
    have hyc : (y : X) ∉ connectedComponentIn (closure U) q := fun hc => hyU (hCsubU hc)
    have hyc' : y ∉ connectedComponent qA := by
      intro hmem
      apply hyc
      rw [connectedComponentIn_eq_image hq]
      exact mem_image_of_mem _ hmem
    obtain ⟨S, hScl, hqS, hyS⟩ := exists_isClopen_connectedComponent_separating qA y hyc'
    exact ⟨S, hScl, hqS, hyS⟩
  set G : Set ↥(closure U) := {y | (y : X) ∉ U} with hG
  have hGcl : IsClosed G := (hUo.isClosed_compl.preimage continuous_subtype_val)
  have hGcomp : IsCompact G := hGcl.isCompact
  let Sfun : G → Set ↥(closure U) := fun y => Classical.choose (sep (y : ↥(closure U)) y.2)
  have Sfun_spec : ∀ y : G, IsClopen (Sfun y) ∧ qA ∈ Sfun y ∧ (y : ↥(closure U)) ∉ Sfun y :=
    fun y => Classical.choose_spec (sep (y : ↥(closure U)) y.2)
  have hcover : G ⊆ ⋃ y : G, (Sfun y)ᶜ := by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, (Sfun_spec ⟨y, hy⟩).2.2⟩
  obtain ⟨t, ht⟩ := hGcomp.elim_finite_subcover (fun y : G => (Sfun y)ᶜ)
    (fun y => (Sfun_spec y).1.isClosed.isOpen_compl) hcover
  set S : Set ↥(closure U) := ⋂ y ∈ t, Sfun y with hSdef
  have hScl : IsClopen S := isClopen_biInter_finset (fun y _ => (Sfun_spec y).1)
  have hqS : qA ∈ S := mem_iInter₂.mpr (fun y _ => (Sfun_spec y).2.1)
  have hSG : S ∩ G = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro y ⟨hyS, hyG⟩
    obtain ⟨y', hy't, hy'c⟩ := mem_iUnion₂.mp (ht hyG)
    exact hy'c (mem_iInter₂.mp hyS y' hy't)
  set W : Set X := (Subtype.val) '' S with hW
  have hWU : W ⊆ U := by
    rintro x ⟨y, hyS, rfl⟩
    by_contra hxU
    exact (Set.eq_empty_iff_forall_notMem.mp hSG) y ⟨hyS, hxU⟩
  have hWmem : q ∈ W := ⟨qA, hqS, rfl⟩
  have hWclosed : IsClosed W := (hScl.isClosed.isCompact.image continuous_subtype_val).isClosed
  obtain ⟨V, hVo, hVeq⟩ := _root_.Topology.IsInducing.subtypeVal.isOpen_iff.mp hScl.isOpen
  have hWopen : IsOpen W := by
    have hWUV : W = U ∩ V := by
      rw [hW]
      ext x
      constructor
      · rintro ⟨y, hyS, rfl⟩
        refine ⟨hWU ⟨y, hyS, rfl⟩, ?_⟩
        rw [← hVeq] at hyS
        exact hyS
      · rintro ⟨hxU, hxV⟩
        exact ⟨⟨x, subset_closure hxU⟩, by rw [← hVeq]; exact hxV, rfl⟩
    rw [hWUV]; exact hUo.inter hVo
  have hWclopen : IsClopen W := ⟨hWclosed, hWopen⟩
  have hWuniv : W = Set.univ := by
    have hpu : IsPreconnected (Set.univ : Set X) := isPreconnected_univ
    rcases hpu.subset_or_subset hWopen hWclosed.isOpen_compl disjoint_compl_right
        (by intro z _; by_cases hz : z ∈ W <;> simp) with h | h
    · exact eq_univ_of_forall (fun z => h (mem_univ z))
    · exact absurd hWmem (h (mem_univ q))
  have : (Set.univ : Set X) ⊆ U := hWuniv ▸ hWU
  exact hUne (eq_univ_of_forall (fun z => this (mem_univ z)))


theorem componentIn_of_finite_fibers {X : Type*} [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] (p : X) (f : X → ℝ) (hf : Continuous f)
    (hfin : ∀ c : ℝ, {x | f x = c}.Finite)
    (hfin2 : ∀ t r : ℝ, {x | f x = t ∧ dist x p = r}.Finite)
    {ε : ℝ} (hε : 0 < ε) (hsep : {x | f x = f p} ∩ Metric.ball p ε = {p}) :
    ∃ δ > 0, ∀ q : X, dist q p < δ → q ∈ connectedComponentIn (Metric.ball p ε) p := by
  by_contra hgoal
  push_neg at hgoal
  have hδle : ∀ n : ℕ, ε / (2 * ((n:ℝ) + 1)) ≤ ε / 2 := by
    intro n
    apply div_le_div_of_nonneg_left hε.le (by norm_num)
    have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith
  have hex : ∀ n : ℕ, ∃ q : X, dist q p < ε / (2 * ((n:ℝ) + 1)) ∧
      q ∉ connectedComponentIn (Metric.ball p ε) p := by
    intro n
    exact hgoal _ (by positivity)
  choose q hq using hex
  set B : Set X := Metric.closedBall p (ε/2) with hBdef
  set D : ℕ → Set X := fun n => connectedComponentIn B (q n) with hDdef
  have hqB : ∀ n, q n ∈ B := by
    intro n
    rw [hBdef, Metric.mem_closedBall]
    linarith [(hq n).1, hδle n]
  have hDsubB : ∀ n, D n ⊆ B := fun n => connectedComponentIn_subset B (q n)
  have hqD : ∀ n, q n ∈ D n := fun n => mem_connectedComponentIn (hqB n)
  have hDpre : ∀ n, IsPreconnected (D n) := fun n => isPreconnected_connectedComponentIn
  have hDball : ∀ n, D n ⊆ Metric.ball p ε :=
    fun n => (hDsubB n).trans (Metric.closedBall_subset_ball (by linarith))
  have hpD : ∀ n, p ∉ D n := by
    intro n hp
    have hsub : D n ⊆ connectedComponentIn (Metric.ball p ε) p :=
      IsPreconnected.subset_connectedComponentIn (hDpre n) hp (hDball n)
    exact (hq n).2 (hsub (hqD n))
  -- limit helpers
  have hqlim : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n, N ≤ n → dist (q n) p < η := by
    intro η hη
    obtain ⟨N, hN⟩ := exists_nat_gt (ε / (2 * η))
    refine ⟨N, fun n hn => ?_⟩
    have hNle : (N:ℝ) ≤ (n:ℝ) := Nat.cast_le.mpr hn
    have hkey : ε / (2 * η) < (n:ℝ) + 1 := by linarith
    have h2η : (0:ℝ) < 2 * η := by linarith
    have hlt : ε < ((n:ℝ) + 1) * (2 * η) := (div_lt_iff₀ h2η).mp hkey
    have hpos : (0:ℝ) < 2 * ((n:ℝ) + 1) := by positivity
    have hmain : ε / (2 * ((n:ℝ) + 1)) < η := by
      rw [div_lt_iff₀ hpos]; nlinarith
    linarith [(hq n).1, hmain]
  have hflim : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n, N ≤ n → |f (q n) - f p| < η := by
    intro η hη
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp hf.continuousAt η hη
    obtain ⟨N, hN⟩ := hqlim δ hδ
    exact ⟨N, fun n hn => by simpa [Real.dist_eq] using hδ' (hN n hn)⟩
  -- the bullet
  have bullet : ∀ t : ℝ, t ≠ f p → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ y ∈ D n, f y ≠ t := by
    intro t ht
    have hEfin : {n : ℕ | ∃ y ∈ D n, f y = t}.Finite := by
      set S : Set X := {x | f x = t} with hS
      have hSfin : S.Finite := hfin t
      have hEeq : {n : ℕ | ∃ y ∈ D n, f y = t} = ⋃ u ∈ S, {n : ℕ | u ∈ D n} := by
        ext n
        simp only [mem_setOf_eq, mem_iUnion, exists_prop]
        constructor
        · rintro ⟨y, hy, hfy⟩; exact ⟨y, hfy, hy⟩
        · rintro ⟨u, hfu, hu⟩; exact ⟨u, hu, hfu⟩
      by_contra hne
      rw [Set.not_finite] at hne
      have hexist : ∃ u ∈ S, ({n : ℕ | u ∈ D n}).Infinite := by
        by_contra hc
        rw [not_exists] at hc
        have hc' : ∀ u ∈ S, ({n : ℕ | u ∈ D n}).Finite := by
          intro u hu
          by_contra hinf
          exact hc u ⟨hu, hinf⟩
        have hU : (⋃ u ∈ S, {n : ℕ | u ∈ D n}).Finite := hSfin.biUnion hc'
        rw [← hEeq] at hU
        exact hne hU
      obtain ⟨u, huS, huinf⟩ := hexist
      have hfu : f u = t := huS
      have huB : u ∈ B := by
        obtain ⟨n, hn⟩ := huinf.nonempty
        exact hDsubB n hn
      have hDu_eq : ∀ n : ℕ, u ∈ D n → D n = connectedComponentIn B u :=
        fun n hn => connectedComponentIn_eq hn
      have hpcl : p ∈ closure (connectedComponentIn B u) := by
        rw [Metric.mem_closure_iff]
        intro η hη
        obtain ⟨N, hN⟩ := hqlim η hη
        obtain ⟨n, hn, hNn⟩ := huinf.exists_gt N
        exact ⟨q n, by rw [← hDu_eq n hn]; exact hqD n, by rw [dist_comm]; exact hN n (le_of_lt hNn)⟩
      obtain ⟨n0, hn0⟩ := huinf.nonempty
      have hDn0 : D n0 = connectedComponentIn B u := hDu_eq n0 hn0
      have hpre : IsPreconnected (insert p (connectedComponentIn B u)) :=
        IsPreconnected.subset_closure isPreconnected_connectedComponentIn (subset_insert _ _)
          (fun z hz => by
            rcases mem_insert_iff.mp hz with rfl | hz'
            · exact hpcl
            · exact subset_closure hz')
      have hsubins : insert p (connectedComponentIn B u) ⊆ Metric.ball p ε := by
        intro z hz
        rcases mem_insert_iff.mp hz with rfl | hz'
        · exact mem_ball_self hε
        · exact (hDn0 ▸ hDball n0) hz'
      have hsubC : insert p (connectedComponentIn B u) ⊆
          connectedComponentIn (Metric.ball p ε) p :=
        IsPreconnected.subset_connectedComponentIn hpre (mem_insert p _) hsubins
      exact (hq n0).2 (hsubC (mem_insert_of_mem p (hDn0 ▸ hqD n0)))
    obtain ⟨N, hN⟩ := hEfin.bddAbove
    refine ⟨N + 1, fun n hn y hy hfy => ?_⟩
    exact absurd (hN ⟨y, hy, hfy⟩) (by omega)
  have hfD : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n, N ≤ n → ∀ y ∈ D n, |f y - f p| < η := by
    intro η hη
    obtain ⟨N1, hN1⟩ := bullet (f p + η) (by linarith)
    obtain ⟨N2, hN2⟩ := bullet (f p - η) (by linarith)
    obtain ⟨N3, hN3⟩ := hflim η hη
    refine ⟨max (max N1 N2) N3, fun n hn y hy => ?_⟩
    have hn1 : N1 ≤ n := le_trans (le_trans (le_max_left N1 N2) (le_max_left _ N3)) hn
    have hn2 : N2 ≤ n := le_trans (le_trans (le_max_right N1 N2) (le_max_left _ N3)) hn
    have hn3 : N3 ≤ n := le_trans (le_max_right _ N3) hn
    have hy1 : f y < f p + η := by
      by_contra hle
      push_neg at hle
      have hmem : f p + η ∈ f '' (D n) := by
        have hiv := IsPreconnected.intermediate_value (hDpre n) (hqD n) hy hf.continuousOn
        exact hiv ⟨by have h3 := hN3 n hn3; rw [abs_lt] at h3; linarith [h3.1], hle⟩
      obtain ⟨z, hz, hfz⟩ := hmem
      exact hN1 n hn1 z hz hfz
    have hy2 : f p - η < f y := by
      by_contra hle
      push_neg at hle
      have hmem : f p - η ∈ f '' (D n) := by
        have hiv := IsPreconnected.intermediate_value (hDpre n) hy (hqD n) hf.continuousOn
        exact hiv ⟨hle, by have h3 := hN3 n hn3; rw [abs_lt] at h3; linarith [h3.1]⟩
      obtain ⟨z, hz, hfz⟩ := hmem
      exact hN2 n hn2 z hz hfz
    rw [abs_lt]; constructor <;> linarith
  -- each D n meets the sphere of radius ε/2
  have hUne : Metric.ball p (ε/2) ≠ Set.univ := by
    intro h
    have hBuniv : B = Set.univ := by
      apply eq_univ_of_forall
      intro x
      exact Metric.ball_subset_closedBall
        (show x ∈ Metric.ball p (ε/2) by rw [h]; exact mem_univ x)
    have hD0 : D 0 = Set.univ := by
      have h1 : D 0 = connectedComponentIn Set.univ (q 0) := by rw [hDdef, hBuniv]
      rw [h1, isPreconnected_univ.connectedComponentIn (mem_univ (q 0))]
    exact (hpD 0) (hD0.symm ▸ mem_univ p)
  have hDsphere : ∀ n, (D n ∩ Metric.sphere p (ε/2)).Nonempty := by
    intro n
    have hqA : q n ∈ closure (Metric.ball p (ε/2)) :=
      subset_closure (Metric.mem_ball.mpr (lt_of_lt_of_le (hq n).1 (hδle n)))
    obtain ⟨z, hz1, hz2⟩ :=
      componentIn_closure_meets_frontier Metric.isOpen_ball hUne hqA
    refine ⟨z, ?_, Metric.frontier_ball_subset_sphere hz2⟩
    exact connectedComponentIn_mono (q n) Metric.closure_ball_subset_closedBall hz1
  choose w hw using hDsphere
  have hfw : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n, N ≤ n → |f (w n) - f p| < η := by
    intro η hη
    obtain ⟨N, hN⟩ := hfD η hη
    exact ⟨N, fun n hn => hN n hn (w n) (hw n).1⟩
  have hfwp : Tendsto (fun n : ℕ => f (w n)) atTop (nhds (f p)) := by
    rw [Metric.tendsto_atTop]
    intro η hη
    obtain ⟨N, hN⟩ := hfw η hη
    exact ⟨N, fun n hn => by simpa [Real.dist_eq] using hN n hn⟩
  have hScomp : IsCompact (Metric.sphere p (ε/2)) := Metric.isClosed_sphere.isCompact
  obtain ⟨a, haS, φ, hφmono, hφtend⟩ := hScomp.tendsto_subseq (fun n => (hw n).2)
  have h1 : Tendsto (fun k : ℕ => f (w (φ k))) atTop (nhds (f p)) := hfwp.comp hφmono.tendsto_atTop
  have h2 : Tendsto (fun k : ℕ => f (w (φ k))) atTop (nhds (f a)) := (hf.tendsto a).comp hφtend
  have hfa : f a = f p := tendsto_nhds_unique h2 h1
  have ha_ball : a ∈ Metric.ball p ε := by
    rw [Metric.mem_ball]
    have := Metric.mem_sphere.mp haS
    linarith
  have hmem : a ∈ ({x | f x = f p} ∩ Metric.ball p ε) := ⟨hfa, ha_ball⟩
  rw [hsep] at hmem
  have hd : dist a p = ε/2 := Metric.mem_sphere.mp haS
  rw [hmem] at hd
  simp at hd
  linarith [hε]

end Commons.Topology.Plane