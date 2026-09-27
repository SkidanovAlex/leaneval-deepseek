import Mathlib

/-!
# Complements of finite sets in charted spaces of dimension at least two

In a connected Hausdorff space locally modelled on `ℝ^n` with `n ≥ 2` the complement of a finite
set is path connected.  This is the standard "there is enough room to walk around finitely many
points" argument.

The two geometric inputs are

* `isPreconnected_ball_diff_singleton`: the punctured ball in a normed space of dimension `> 1` is
  preconnected.  Indeed it is the union, over the spheres around the centre together with one
  radial ray, of preconnected sets which all meet the ray;
* `isPreconnected_diff_singleton`: removing a point `p` from a preconnected open set `T` keeps it
  preconnected, provided `p` has an open neighbourhood inside `T` whose punctured version is
  preconnected.

Charts provide such neighbourhoods (images of small balls), and iterating the second lemma over a
finite set gives preconnectedness of the complement; the complement is open, so local path
connectedness (also a consequence of the charts) upgrades preconnected to path connected.
-/

open Set Metric Filter
open scoped Topology

set_option linter.style.haveILetI false

namespace Work.Whitney.PathTools

section PuncturedBall

/-- `ℝ^n` has dimension greater than one as soon as `n ≥ 2`. -/
lemma one_lt_rank_euclidean {n : ℕ} (hn : 2 ≤ n) :
    1 < Module.rank ℝ (EuclideanSpace ℝ (Fin n)) := by
  have hn' : (1 : ℕ) < n := by omega
  rw [(WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).rank_eq, rank_fin_fun]
  exact_mod_cast hn'

/-- In a normed space of dimension greater than `1`, the punctured ball is preconnected.
It is the union over the spheres of radius `s ∈ (0, r)` around the centre of the sphere together
with a fixed radial ray; all these sets meet the radial ray. -/
lemma isPreconnected_ball_diff_singleton {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hrank : 1 < Module.rank ℝ E) (c : E) {r : ℝ} :
    IsPreconnected (Metric.ball c r \ {c}) := by
  rcases le_or_gt r 0 with hr | hr
  · rw [Metric.ball_eq_empty.mpr hr, Set.empty_sdiff]
    exact isPreconnected_empty (α := E)
  have hnt : Nontrivial E := (rank_pos_iff_nontrivial (R := ℝ)).1 (zero_lt_one.trans hrank)
  obtain ⟨v, hv⟩ : ∃ v : E, v ≠ 0 := by
    obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
    exact ⟨a - b, sub_ne_zero.mpr hab⟩
  let u : E := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by
    rw [show u = ‖v‖⁻¹ • v from rfl, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  have hu_ne : u ≠ 0 := by
    intro h
    rw [h] at hu
    simp at hu
  let R : Set E := (fun t : ℝ => c + t • u) '' Set.Ioo (0 : ℝ) r
  have hRpre : IsPreconnected R :=
    isPreconnected_Ioo.image (fun t : ℝ => c + t • u)
      (by fun_prop : ContinuousOn (fun t : ℝ => c + t • u) (Set.Ioo (0 : ℝ) r))
  have hmemR : c + (r / 2) • u ∈ R := ⟨r / 2, ⟨by linarith, by linarith⟩, rfl⟩
  let A : Set.Ioo (0 : ℝ) r → Set E := fun s => Metric.sphere c s.1 ∪ R
  have hUnion : (⋃ s, A s) = Metric.ball c r \ {c} := by
    ext y
    constructor
    · intro hy
      rw [Set.mem_iUnion] at hy
      obtain ⟨s, hs⟩ := hy
      rcases hs with hs | hs
      · rw [Metric.mem_sphere] at hs
        refine ⟨Metric.mem_ball.mpr ?_, ?_⟩
        · rw [hs]; exact s.2.2
        · intro hy'
          rw [hy', dist_self] at hs
          linarith [s.2.1]
      · obtain ⟨t, ht, rfl⟩ := hs
        refine ⟨Metric.mem_ball.mpr ?_, ?_⟩
        · rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hu, mul_one,
            Real.norm_of_nonneg (le_of_lt ht.1)]
          exact ht.2
        · intro hy'
          have h1 : t • u = 0 := by
            have := congrArg (fun z : E => z - c) hy'
            simpa using this
          exact smul_ne_zero ht.1.ne' hu_ne h1
    · rintro ⟨hyb, hyc⟩
      rw [Set.mem_iUnion]
      exact ⟨⟨dist y c, dist_pos.mpr hyc, Metric.mem_ball.mp hyb⟩,
        Or.inl (Metric.mem_sphere.mpr rfl)⟩
  rw [← hUnion]
  refine isPreconnected_iUnion ?_ ?_
  · refine ⟨c + (r / 2) • u, ?_⟩
    rw [Set.mem_iInter]
    exact fun s => Or.inr hmemR
  · intro s
    refine (isPreconnected_sphere hrank c s.1).union' ⟨c + s.1 • u, ?_, ?_⟩ hRpre
    · rw [Metric.mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_smul, hu, mul_one,
        Real.norm_of_nonneg (le_of_lt s.2.1)]
    · exact ⟨s.1, ⟨s.2.1, s.2.2⟩, rfl⟩

/-- In a nontrivial normed space, balls of positive radius are infinite: they contain an affine
copy of the interval `(0, 1)`. -/
lemma infinite_ball_of_nontrivial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hE : Nontrivial E) (x : E) {r : ℝ} (hr : 0 < r) : (Metric.ball x r).Infinite := by
  obtain ⟨v, hv⟩ : ∃ v : E, v ≠ 0 := by
    obtain ⟨a, b, hab⟩ := hE.exists_pair_ne
    exact ⟨a - b, sub_ne_zero.mpr hab⟩
  let u : E := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by
    rw [show u = ‖v‖⁻¹ • v from rfl, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  have hu_ne : u ≠ 0 := by
    intro h
    rw [h] at hu
    simp at hu
  have key : ∀ a b : ℝ, a • u = b • u → a = b := by
    intro a b hab
    have h : (a - b) • u = 0 := by rw [sub_smul, hab, sub_self]
    rcases smul_eq_zero.mp h with h' | h'
    · exact sub_eq_zero.mp h'
    · exact absurd h' hu_ne
  have hr2 : r / 2 ≠ 0 := by linarith
  have hinj : Set.InjOn (fun a : ℝ => x + (a * (r / 2)) • u) (Set.Ioo (0 : ℝ) 1) := by
    intro a ha b hb hab
    have h1 : (a * (r / 2)) • u = (b * (r / 2)) • u := by
      have := add_left_cancel hab
      simpa using this
    exact mul_right_cancel₀ hr2 (key _ _ h1)
  have hmaps : Set.MapsTo (fun a : ℝ => x + (a * (r / 2)) • u) (Set.Ioo (0 : ℝ) 1)
      (Metric.ball x r) := by
    intro a ha
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hu, mul_one,
      Real.norm_of_nonneg (le_of_lt (mul_pos ha.1 (by linarith)))]
    nlinarith [ha.1, ha.2, hr]
  exact Set.infinite_of_injOn_mapsTo hinj hmaps (Set.Ioo_infinite (show (0 : ℝ) < 1 by norm_num))

end PuncturedBall

section Removal

/-- Removing a point `p` from a preconnected open set `T` keeps it preconnected, provided `p`
admits an open neighbourhood `V ⊆ T` whose punctured version is preconnected. -/
lemma isPreconnected_diff_singleton {X : Type*} [TopologicalSpace X] {T : Set X}
    (hT : IsPreconnected T) (hTo : IsOpen T) {p : X} (hp : IsClosed ({p} : Set X))
    {V : Set X} (hVo : IsOpen V) (hpV : p ∈ V) (hVT : V ⊆ T)
    (hVp : IsPreconnected (V \ {p})) : IsPreconnected (T \ {p}) := by
  rw [isPreconnected_iff_subset_of_disjoint] at hT
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv huv huvdisj
  have hVsub : V \ {p} ⊆ u ∪ v := fun x hx => huv ⟨hVT hx.1, hx.2⟩
  have hVdisj : (V \ {p}) ∩ (u ∩ v) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hx1, hx2⟩
    exact Set.eq_empty_iff_forall_notMem.mp huvdisj x ⟨⟨hVT hx1.1, hx1.2⟩, hx2⟩
  have hAo : IsOpen ((T \ {p}) ∩ u) := by
    rw [Set.sdiff_eq]
    exact (hTo.inter hp.isOpen_compl).inter hu
  have hBo : IsOpen ((T \ {p}) ∩ v) := by
    rw [Set.sdiff_eq]
    exact (hTo.inter hp.isOpen_compl).inter hv
  rcases (isPreconnected_iff_subset_of_disjoint.mp hVp) u v hu hv hVsub hVdisj with hVu | hVv
  · have hcov : T ⊆ (((T \ {p}) ∩ u) ∪ V) ∪ ((T \ {p}) ∩ v) := by
      intro x hxT
      rcases eq_or_ne x p with rfl | hxp
      · exact Or.inl (Or.inr hpV)
      · have hx' : x ∈ T \ {p} := ⟨hxT, hxp⟩
        rcases huv hx' with hxu | hxv
        · exact Or.inl (Or.inl ⟨hx', hxu⟩)
        · exact Or.inr ⟨hx', hxv⟩
    have hdisj : T ∩ ((((T \ {p}) ∩ u) ∪ V) ∩ ((T \ {p}) ∩ v)) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro x ⟨hxT, hx1, hx2⟩
      rcases hx1 with ⟨hx1a, hxu⟩ | hxV
      · exact Set.eq_empty_iff_forall_notMem.mp huvdisj x ⟨hx1a, hxu, hx2.2⟩
      · exact Set.eq_empty_iff_forall_notMem.mp hVdisj x
          ⟨⟨hxV, hx2.1.2⟩, hVu ⟨hxV, hx2.1.2⟩, hx2.2⟩
    rcases hT _ _ (hAo.union hVo) hBo hcov hdisj with h | h
    · left
      intro x hx
      rcases h hx.1 with ⟨hx', hxu⟩ | hxV
      · exact hxu
      · exact hVu ⟨hxV, hx.2⟩
    · right
      exact fun x hx => (h hx.1).2
  · have hcov : T ⊆ (((T \ {p}) ∩ v) ∪ V) ∪ ((T \ {p}) ∩ u) := by
      intro x hxT
      rcases eq_or_ne x p with rfl | hxp
      · exact Or.inl (Or.inr hpV)
      · have hx' : x ∈ T \ {p} := ⟨hxT, hxp⟩
        rcases huv hx' with hxu | hxv
        · exact Or.inr ⟨hx', hxu⟩
        · exact Or.inl (Or.inl ⟨hx', hxv⟩)
    have hdisj : T ∩ ((((T \ {p}) ∩ v) ∪ V) ∩ ((T \ {p}) ∩ u)) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro x ⟨hxT, hx1, hx2⟩
      rcases hx1 with ⟨hx1a, hxv⟩ | hxV
      · exact Set.eq_empty_iff_forall_notMem.mp huvdisj x ⟨hx1a, hx2.2, hxv⟩
      · exact Set.eq_empty_iff_forall_notMem.mp hVdisj x
          ⟨⟨hxV, hx2.1.2⟩, hx2.2, hVv ⟨hxV, hx2.1.2⟩⟩
    rcases hT _ _ (hBo.union hVo) hAo hcov hdisj with h | h
    · right
      intro x hx
      rcases h hx.1 with ⟨hx', hxv⟩ | hxV
      · exact hxv
      · exact hVv ⟨hxV, hx.2⟩
    · left
      exact fun x hx => (h hx.1).2

end Removal

/-- A charted space over `ℝ^n`, `n ≥ 2`, is infinite: a chart maps the points of a small ball
injectively into the space. -/
lemma infinite_of_chartedSpace {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (hn : 2 ≤ n) (x : M) : Infinite M := by
  let E := EuclideanSpace ℝ (Fin n)
  let c := chartAt E x
  have hx : x ∈ c.source := mem_chart_source E x
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (c.open_target.mem_nhds (c.map_source hx))
  have hnt : Nontrivial E :=
    (rank_pos_iff_nontrivial (R := ℝ)).1 (zero_lt_one.trans (one_lt_rank_euclidean hn))
  have hB : (Metric.ball (c x) ε).Infinite := infinite_ball_of_nontrivial hnt (c x) hε
  have hinj : Set.InjOn c.symm (Metric.ball (c x) ε) := by
    intro a ha b hb hab
    have ha' : a ∈ (c.symm).source := by
      rw [OpenPartialHomeomorph.symm_source]; exact hεsub ha
    have hb' : b ∈ (c.symm).source := by
      rw [OpenPartialHomeomorph.symm_source]; exact hεsub hb
    exact (c.symm).injOn ha' hb' hab
  have himg : (c.symm '' Metric.ball (c x) ε).Infinite := (Set.infinite_image_iff hinj).mpr hB
  exact Set.infinite_univ_iff.mp (himg.mono (Set.subset_univ _))

/-- Every point of a charted space has arbitrarily small open neighbourhoods whose punctured
version is preconnected, as soon as the model has dimension at least `2`, and these may be chosen
to avoid a prescribed finite set. -/
lemma exists_open_punctured_preconnected {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (hn : 2 ≤ n) {p : M} {F : Set M}
    (hF : F.Finite) (hpF : p ∉ F) :
    ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ Disjoint V F ∧ IsPreconnected (V \ {p}) := by
  let E := EuclideanSpace ℝ (Fin n)
  let c := chartAt E p
  have hcp : p ∈ c.source := mem_chart_source E p
  have hrank : 1 < Module.rank ℝ E := one_lt_rank_euclidean hn
  have hKfin : (c '' (F ∩ c.source)).Finite := (hF.subset Set.inter_subset_left).image c
  have hKcl : IsClosed (c '' (F ∩ c.source)) := hKfin.isClosed
  have hpc : c p ∉ c '' (F ∩ c.source) := by
    rintro ⟨y, hy, hyc⟩
    exact hpF ((c.injOn hy.2 hcp hyc : y = p) ▸ hy.1)
  have hnhds : (c '' (F ∩ c.source))ᶜ ∩ c.target ∈ 𝓝 (c p) :=
    Filter.inter_mem (hKcl.isOpen_compl.mem_nhds hpc) (c.open_target.mem_nhds (c.map_source hcp))
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hnhds
  have hεtarget : Metric.ball (c p) ε ⊆ c.target := fun z hz => (hεsub hz).2
  let V : Set M := c.symm '' Metric.ball (c p) ε
  refine ⟨V, ?_, ?_, ?_, ?_⟩
  · exact c.isOpen_image_symm_of_subset_target Metric.isOpen_ball hεtarget
  · exact ⟨c p, Metric.mem_ball_self hε, c.left_inv hcp⟩
  · rw [Set.disjoint_left]
    rintro y ⟨z, hz, rfl⟩ hyF
    refine (hεsub hz).1 ⟨c.symm z, ⟨hyF, ?_⟩, c.right_inv ((hεsub hz).2)⟩
    have := (c.symm).map_source (show z ∈ (c.symm).source from by
      rw [OpenPartialHomeomorph.symm_source]; exact (hεsub hz).2)
    rwa [OpenPartialHomeomorph.symm_target] at this
  · have heq : V \ {p} = c.symm '' (Metric.ball (c p) ε \ {c p}) := by
      ext y
      constructor
      · intro hy
        obtain ⟨⟨z, hz, hzy⟩, hne⟩ := hy
        rw [← hzy]
        refine ⟨z, ⟨hz, ?_⟩, rfl⟩
        rintro rfl
        exact hne (by rw [← hzy]; exact c.left_inv hcp)
      · intro hy
        obtain ⟨z, hz, hzy⟩ := hy
        obtain ⟨hz, hzcp⟩ := hz
        rw [← hzy]
        refine ⟨⟨z, hz, rfl⟩, fun h => hzcp ?_⟩
        have h1 : c.symm z = c.symm (c p) := by rw [h]; exact (c.left_inv hcp).symm
        exact (c.symm).injOn
          (by rw [OpenPartialHomeomorph.symm_source]; exact (hεsub hz).2)
          (by rw [OpenPartialHomeomorph.symm_source]; exact c.map_source hcp) h1
    rw [heq]
    exact (isPreconnected_ball_diff_singleton hrank (c p)).image c.symm
      (c.continuousOn_symm.mono (Set.sdiff_subset.trans hεtarget))

/-- A charted space over a normed space is locally path connected: images of balls under charts
form a basis of path connected neighbourhoods. -/
lemma locallyPathConnectedSpace_chartedSpace {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] : LocallyPathConnectedSpace M := by
  refine ⟨fun x => ?_⟩
  rw [Filter.hasBasis_self]
  intro t ht
  let E := EuclideanSpace ℝ (Fin n)
  let c := chartAt E x
  have hcx : x ∈ c.source := mem_chart_source E x
  have h1 : t ∩ c.source ∈ 𝓝 x := Filter.inter_mem ht (c.open_source.mem_nhds hcx)
  have h2 : c '' (t ∩ c.source) ∈ 𝓝 (c x) := c.image_mem_nhds hcx h1
  have h3 : c.target ∈ 𝓝 (c x) := c.open_target.mem_nhds (c.map_source hcx)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem h2 h3)
  have hεtarget : Metric.ball (c x) ε ⊆ c.target := fun z hz => (hεsub hz).2
  refine ⟨c.symm '' Metric.ball (c x) ε, ?_, ?_, ?_⟩
  · have hb : Metric.ball (c x) ε ∈ 𝓝 (c x) := Metric.ball_mem_nhds _ hε
    have hsrc : c x ∈ (c.symm).source := by
      rw [OpenPartialHomeomorph.symm_source]; exact c.map_source hcx
    have hmem := (c.symm).image_mem_nhds hsrc hb
    rwa [c.left_inv hcx] at hmem
  · exact (Metric.isPathConnected_ball hε).image' (c.continuousOn_symm.mono hεtarget)
  · intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    rcases (hεsub hz).1 with ⟨w, hw, hwz⟩
    rw [← hwz, c.left_inv hw.2]
    exact hw.1

/-- The complement of a finite set in a connected Hausdorff charted space of dimension `n ≥ 2`
is preconnected. -/
lemma isPreconnected_compl_finite {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (hn : 2 ≤ n) (S : Set M) (hS : S.Finite) : IsPreconnected (Sᶜ : Set M) := by
  refine Set.Finite.induction_on (motive := fun s (_ : s.Finite) => IsPreconnected (sᶜ : Set M))
    S hS ?_ ?_
  · rw [Set.compl_empty]
    exact isPreconnected_univ
  · intro a s has hs ih
    have heq : ((insert a s : Set M))ᶜ = (sᶜ : Set M) \ {a} := by
      ext x
      simp [Set.sdiff_eq]
      tauto
    rw [heq]
    obtain ⟨V, hVo, haV, hdisj, hVp⟩ := exists_open_punctured_preconnected (n := n) hn hs has
    exact isPreconnected_diff_singleton ih (hs.isClosed.isOpen_compl)
      (isClosed_singleton (x := a)) hVo haV (fun y hy => Set.disjoint_left.mp hdisj hy) hVp

theorem isPathConnected_compl_finite {n : ℕ} (hn : 2 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (S : Set M) (hS : S.Finite) : IsPathConnected (Sᶜ : Set M) := by
  letI : Infinite M := infinite_of_chartedSpace hn (Classical.choice (inferInstance : Nonempty M))
  letI : LocallyPathConnectedSpace M := locallyPathConnectedSpace_chartedSpace (n := n)
  have hcl : IsClosed (S : Set M) := hS.isClosed
  exact hcl.isOpen_compl.isConnected_iff_isPathConnected.mp
    ⟨(hS.infinite_compl).nonempty, isPreconnected_compl_finite (n := n) hn S hS⟩

end Work.Whitney.PathTools
