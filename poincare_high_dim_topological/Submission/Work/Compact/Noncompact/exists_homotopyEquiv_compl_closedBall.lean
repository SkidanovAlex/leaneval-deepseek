import Mathlib
import Submission.Work.Compact.Noncompact.Basic
import Submission.Work.Geo.Euclid.EuclidPush
import Submission.Work.Compact.Noncompact.ChartPush

/-!
# The complement of a small closed ball in a chart

This file proves `Work.Compact.Noncompact.exists_homotopyEquiv_compl_closedBall`: for a chart
`e` of an `n`-manifold, a centre `c`, a radius `ρ > 0` with `B(c,ρ) ⊆ e.target`, and a point
`y` of the chart source with `dist (e y) c < ρ/4`, the inclusion of the complement of
`K = e.source ∩ e⁻¹' (closedBall c (ρ/2))` into the complement of `{y}` is a homotopy
equivalence.

The construction is the chart conjugate of the Euclidean radial push away from `p = e y` with
threshold `L = 3ρ/4` (`Work.Geo.Radial.pushGen`): points of the chart source whose image is
closer to `p` than `L` are pushed radially out to distance `L`, everything else is fixed.
Since `dist p c + ρ/2 < L`, the push of any point other than `y` lands outside
`closedBall c (ρ/2)` but inside `e.target`, so it induces a map `{y}ᶜ → Kᶜ`; the inclusion
`Kᶜ → {y}ᶜ` goes the other way and the radial homotopy exhibits the required homotopy
equivalence.
-/

set_option maxHeartbeats 1000000

open Set Metric
open scoped Topology unitInterval

open Work.Geo.Radial

namespace Work.Compact.Noncompact

/-- **Joint continuity of the chart push.**  If `e` is a chart, `y ∈ e.source` with `e y = p`,
`L > 0`, the closed ball of radius `L` about `p` lies in the chart target, and the radial push
`pushGen p L s` maps the chart target into itself for every `s ∈ [0,1]`, then the chart push
`(s,z) ↦ chartPush e p L s z` is continuous on `univ ×ˢ {y}ᶜ`.

The only discontinuity of `pushGen p L s` is at `p` itself, and `e` is injective on its source, so
`{y}ᶜ` is exactly the set where the chart conjugate is well behaved.  The proof is a pasting
argument: `{y}ᶜ` is covered by the open set `e.source ∩ {y}ᶜ` (where the push is the conjugate of
`pushGen`) and the open set which is the complement of the compact core
`e.symm '' closedBall p L` (where the chart push is the identity, because `pushGen` fixes
everything at distance `≥ L` from `p`). -/
theorem continuousOn_chartPush_aux {M : Type*} [TopologicalSpace M] [T2Space M]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (e : OpenPartialHomeomorph M E) (p : E) (L : ℝ) {y : M}
    (hy : y ∈ e.source) (hyp : e y = p) (hLpos : 0 < L)
    (hball : Metric.closedBall p L ⊆ e.target)
    (hmap : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ e.target, x ≠ p →
      Work.Geo.Radial.pushGen p L s x ∈ e.target) :
    ContinuousOn (fun q : I × M => Work.Compact.Noncompact.chartPush e p L (q.1 : ℝ) q.2)
      (Set.univ ×ˢ ({y}ᶜ : Set M)) := by
  classical
  have hne : ∀ {z : M}, z ∈ e.source → z ≠ y → e z ≠ p := by
    intro z hz hzy hcon
    exact hzy (e.injOn hz hy (by rw [hcon, hyp]))
  have hcompact : IsCompact (e.symm '' Metric.closedBall p L) :=
    (isCompact_closedBall p L).image_of_continuousOn (e.continuousOn_symm.mono hball)
  have hclosedA : IsClosed (e.symm '' Metric.closedBall p L) := hcompact.isClosed
  have hS1open : IsOpen (e.source ∩ ({y}ᶜ : Set M)) :=
    e.open_source.inter isOpen_compl_singleton
  have hcover : ({y}ᶜ : Set M) ⊆ (e.source ∩ ({y}ᶜ : Set M)) ∪ (e.symm '' Metric.closedBall p L)ᶜ := by
    intro z hz
    by_cases hzs : z ∈ e.source
    · exact Or.inl ⟨hzs, hz⟩
    · refine Or.inr (fun hmem => hzs ?_)
      obtain ⟨x, hx, rfl⟩ := hmem
      exact e.map_target (hball hx)
  have h1 : ContinuousOn (fun q : I × M => Work.Compact.Noncompact.chartPush e p L (q.1 : ℝ) q.2)
      (univ ×ˢ (e.source ∩ ({y}ᶜ : Set M))) := by
    have hA : ContinuousOn (fun q : I × M => ((q.1, e q.2) : I × E))
        (univ ×ˢ (e.source ∩ ({y}ᶜ : Set M))) :=
      continuous_fst.continuousOn.prodMk
        (e.continuousOn.comp continuousOn_snd (fun q hq => hq.2.1))
    have hpush : ContinuousOn (fun q : I × M => Work.Geo.Radial.pushGen p L (q.1 : ℝ) (e q.2))
        (univ ×ˢ (e.source ∩ ({y}ᶜ : Set M))) := by
      exact ContinuousOn.comp
        (g := fun r : I × E => Work.Geo.Radial.pushGen p L (r.1 : ℝ) r.2)
        (f := fun q : I × M => ((q.1, e q.2) : I × E))
        (t := univ ×ˢ {x : E | x ≠ p})
        (s := univ ×ˢ (e.source ∩ ({y}ᶜ : Set M)))
        (Work.Geo.Radial.continuousOn_pushGen_I (E := E) p L) hA
        (fun q hq => ⟨trivial, hne hq.2.1 (by simpa using hq.2.2)⟩)
    have htgt : MapsTo (fun q : I × M => Work.Geo.Radial.pushGen p L (q.1 : ℝ) (e q.2))
        (univ ×ˢ (e.source ∩ ({y}ᶜ : Set M))) e.target := by
      intro q hq
      exact hmap (q.1 : ℝ) q.1.2 (e q.2) (e.map_source hq.2.1)
        (hne hq.2.1 (by simpa using hq.2.2))
    refine (e.continuousOn_symm.comp hpush htgt).congr ?_
    intro q hq
    exact Work.Compact.Noncompact.chartPush_of_mem hq.2.1
  have h2 : ContinuousOn (fun q : I × M => Work.Compact.Noncompact.chartPush e p L (q.1 : ℝ) q.2)
      (univ ×ˢ (e.symm '' Metric.closedBall p L)ᶜ) := by
    refine continuousOn_snd.congr ?_
    intro q hq
    dsimp only
    have hqA : q.2 ∉ e.symm '' Metric.closedBall p L := hq.2
    by_cases hzs : q.2 ∈ e.source
    · have hzL : L ≤ dist (e q.2) p := by
        by_contra hcon
        exact hqA ⟨e q.2, Metric.mem_closedBall.mpr (le_of_lt (lt_of_not_ge hcon)),
          e.left_inv hzs⟩
      rw [Work.Compact.Noncompact.chartPush_of_mem hzs,
        Work.Geo.Radial.pushGen_id_of_le hLpos hzL, e.left_inv hzs]
    · rw [Work.Compact.Noncompact.chartPush_of_notMem hzs]
  refine (h1.union_of_isOpen h2 (isOpen_univ.prod hS1open)
    (isOpen_univ.prod hclosedA.isOpen_compl)).mono ?_
  intro q hq
  rcases hcover hq.2 with h | h
  · exact Or.inl ⟨trivial, h⟩
  · exact Or.inr ⟨trivial, h⟩


/-- **The complement of a small closed ball in a chart is homotopy equivalent to the complement of
the centre point, by the inclusion.**  With `e` a chart of an `n`-manifold, `ρ > 0` such that the
chart target contains `B(c,ρ)`, and `y` a point of the chart source whose image is within `ρ/4` of
`c`: the inclusion `Kᶜ ↪ {y}ᶜ`, `K = e.source ∩ e⁻¹' (closedBall c (ρ/2))`, is the forward map of a
homotopy equivalence. -/
theorem exists_homotopyEquiv_compl_closedBall {n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    {c : EuclideanSpace ℝ (Fin n)} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : Metric.ball c ρ ⊆ e.target)
    {y : M} (hy : y ∈ e.source) (hyd : dist (e y) c < ρ / 4) :
    ∃ Φ : ContinuousMap.HomotopyEquiv ↥((e.source ∩ e ⁻¹' Metric.closedBall c (ρ / 2))ᶜ)
        ↥(({y}ᶜ : Set M)),
      ∀ z, ((Φ.toFun z : ↥({y}ᶜ : Set M)) : M) = (z : M) := by
  classical
  set p : EuclideanSpace ℝ (Fin n) := e y with hp
  set L : ℝ := 3 * ρ / 4 with hL
  set K : Set M := e.source ∩ e ⁻¹' Metric.closedBall c (ρ / 2) with hK
  have hLpos : 0 < L := by rw [hL]; linarith
  have hpc : dist p c < ρ / 4 := by rw [hp]; exact hyd
  have hpc2 : dist p c < ρ / 2 := by linarith
  have hsum : dist p c + ρ / 2 < L := by rw [hL]; linarith
  have hsum' : dist p c + L < ρ := by rw [hL]; linarith
  have hconv : Convex ℝ (Metric.closedBall c (ρ / 2)) := convex_closedBall c (ρ / 2)
  have hpC : p ∈ Metric.closedBall c (ρ / 2) := by
    rw [Metric.mem_closedBall]; exact le_of_lt hpc2
  have hyK : y ∈ K := by
    rw [hK]
    refine ⟨hy, ?_⟩
    simp only [Set.mem_preimage]
    exact hpC
  -- the closed ball of radius `L` about `p` sits inside the chart target
  have hball : Metric.closedBall p L ⊆ e.target := by
    intro x hx
    refine hsub ?_
    rw [Metric.mem_ball]
    have h1 : dist x p ≤ L := Metric.mem_closedBall.mp hx
    have h2 : dist x c ≤ dist x p + dist p c := dist_triangle _ _ _
    rw [hL] at h1
    linarith
  have hne : ∀ {z : M}, z ∈ e.source → z ≠ y → e z ≠ p := by
    intro z hz hzy hcon
    exact hzy (e.injOn hz hy (by rw [hcon, hp]))
  -- the push of a point of the target (other than `p`) stays in the target
  have hmem_target : ∀ (s : ℝ), s ∈ Icc (0 : ℝ) 1 →
      ∀ x : EuclideanSpace ℝ (Fin n), x ∈ e.target → x ≠ p → pushGen p L s x ∈ e.target := by
    intro s hs x hxt hx
    rcases lt_or_ge (dist x p) L with h | h
    · refine hsub ?_
      rw [Metric.mem_ball]
      exact pushGen_mem_ball_of_lt hs hLpos.le hsum' h
    · rw [pushGen_id_of_le hLpos h]
      exact hxt
  -- the push preserves the complement of `K`
  have hKcompl : ∀ (s : ℝ), s ∈ Icc (0 : ℝ) 1 → ∀ z : M, z ∈ Kᶜ →
      chartPush e p L s z ∈ Kᶜ := by
    intro s hs z hz
    rw [Set.mem_compl_iff] at hz ⊢
    by_cases hzs : z ∈ e.source
    · have hzy : z ≠ y := fun h => hz (h ▸ hyK)
      have hzp : e z ≠ p := hne hzs hzy
      exact chartPush_notMem_compl (C := Metric.closedBall c (ρ / 2)) hzs
        (hmem_target s hs (e z) (e.map_source hzs) hzp)
        (pushGen_notMem_convex hconv hpC (fun h => hz ⟨hzs, h⟩) hs)
    · rw [chartPush_of_notMem hzs]
      exact hz
  -- the push preserves the complement of the point `y`
  have hYcompl : ∀ (s : ℝ), s ∈ Icc (0 : ℝ) 1 → ∀ z : M, z ∈ ({y}ᶜ : Set M) →
      chartPush e p L s z ∈ ({y}ᶜ : Set M) := by
    intro s hs z hz
    rw [Set.mem_compl_iff] at hz ⊢
    simp only [Set.mem_singleton_iff] at hz ⊢
    by_cases hzs : z ∈ e.source
    · have hzp : e z ≠ p := hne hzs hz
      exact chartPush_ne hzs (hmem_target s hs (e z) (e.map_source hzs) hzp)
        (pushGen_ne_p hs hzp) hp.symm
    · rw [chartPush_of_notMem hzs]
      exact hz
  -- the push at time `0` lands in the complement of `K`, on the whole complement of `y`
  have hK1 : ∀ z : M, z ∈ ({y}ᶜ : Set M) → chartPush e p L 0 z ∈ Kᶜ := by
    intro z hz
    rw [Set.mem_compl_iff]
    by_cases hzs : z ∈ e.source
    · have hzy : z ≠ y := by simpa using hz
      have hzp : e z ≠ p := hne hzs hzy
      exact chartPush_notMem_compl (C := Metric.closedBall c (ρ / 2)) hzs
        (hmem_target 0 ⟨le_refl 0, zero_le_one⟩ (e z) (e.map_source hzs) hzp)
        (push_notMem_closedBall hzp hsum)
    · rw [chartPush_of_notMem hzs]
      exact fun hmem => hzs hmem.1
  -- `Kᶜ` sits inside `{y}ᶜ`
  have hsubKY : Kᶜ ⊆ ({y}ᶜ : Set M) := by
    intro z hz
    rw [Set.mem_compl_iff] at hz
    intro hzy
    exact hz (hzy ▸ hyK)
  -- joint continuity of the chart push on the complement of `y`
  have hcont : ContinuousOn (fun q : I × M => chartPush e p L (q.1 : ℝ) q.2)
      (univ ×ˢ ({y}ᶜ : Set M)) :=
    continuousOn_chartPush_aux e p L hy hp.symm hLpos hball hmem_target
  have hcont_inv : Continuous (fun z : ↥(({y}ᶜ : Set M)) => chartPush e p L 0 z.1) := by
    have hf : Continuous (fun z : ↥(({y}ᶜ : Set M)) => (((0 : I), z.1) : I × M)) :=
      continuous_const.prodMk continuous_subtype_val
    refine (hcont.comp_continuous hf ?_).congr ?_
    · intro z
      exact ⟨trivial, z.2⟩
    · intro z
      rfl
  have hcont_left : Continuous (fun q : I × ↥(Kᶜ) => chartPush e p L (q.1 : ℝ) q.2.1) := by
    have hf : Continuous (fun q : I × ↥(Kᶜ) => ((q.1, q.2.1) : I × M)) :=
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
    refine (hcont.comp_continuous hf ?_).congr ?_
    · intro q
      exact ⟨trivial, hsubKY q.2.2⟩
    · intro q
      rfl
  have hcont_right : Continuous (fun q : I × ↥(({y}ᶜ : Set M)) =>
      chartPush e p L (q.1 : ℝ) q.2.1) := by
    have hf : Continuous (fun q : I × ↥(({y}ᶜ : Set M)) => ((q.1, q.2.1) : I × M)) :=
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
    refine (hcont.comp_continuous hf ?_).congr ?_
    · intro q
      exact ⟨trivial, q.2.2⟩
    · intro q
      rfl
  let htoFun : C(↥(Kᶜ), ↥(({y}ᶜ : Set M))) :=
    ⟨Set.inclusion hsubKY, continuous_inclusion hsubKY⟩
  let hinvFun : C(↥(({y}ᶜ : Set M)), ↥(Kᶜ)) :=
    ⟨fun z => ⟨chartPush e p L 0 z.1, hK1 z z.2⟩,
      Continuous.subtype_mk hcont_inv (fun z => hK1 z z.2)⟩
  have hleft : (hinvFun.comp htoFun).Homotopic (ContinuousMap.id ↥(Kᶜ)) := by
    refine ⟨{ toContinuousMap := ?_, map_zero_left := ?_, map_one_left := ?_ }⟩
    · exact ⟨fun q : I × ↥(Kᶜ) =>
          ⟨chartPush e p L (q.1 : ℝ) q.2.1, hKcompl (q.1 : ℝ) q.1.2 q.2.1 q.2.2⟩,
        Continuous.subtype_mk hcont_left
          (fun q => hKcompl (q.1 : ℝ) q.1.2 q.2.1 q.2.2)⟩
    · intro x
      exact Subtype.ext rfl
    · intro x
      exact Subtype.ext (chartPush_one p L x.1)
  have hright : (htoFun.comp hinvFun).Homotopic (ContinuousMap.id ↥(({y}ᶜ : Set M))) := by
    refine ⟨{ toContinuousMap := ?_, map_zero_left := ?_, map_one_left := ?_ }⟩
    · exact ⟨fun q : I × ↥(({y}ᶜ : Set M)) =>
          ⟨chartPush e p L (q.1 : ℝ) q.2.1, hYcompl (q.1 : ℝ) q.1.2 q.2.1 q.2.2⟩,
        Continuous.subtype_mk hcont_right
          (fun q => hYcompl (q.1 : ℝ) q.1.2 q.2.1 q.2.2)⟩
    · intro x
      exact Subtype.ext rfl
    · intro x
      exact Subtype.ext (chartPush_one p L x.1)
  refine ⟨{ toFun := htoFun, invFun := hinvFun, left_inv := hleft, right_inv := hright }, ?_⟩
  intro z
  change (htoFun z : M) = (z : M)
  rfl

end Work.Compact.Noncompact
