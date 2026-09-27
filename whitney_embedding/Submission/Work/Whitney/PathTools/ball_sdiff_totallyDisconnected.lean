import Mathlib
import Submission.Work.Whitney.PathTools.RemovabilityAux

universe u

namespace Work.Whitney.PathTools

open Set Metric Topology

/-!
# Removing a compact zero-dimensional set from a ball

Let `E` be a finite dimensional real inner product space with `2 ≤ finrank ℝ E`, let `K ⊆ E` be
compact and totally disconnected, and let `K` lie in an open ball `ball c r`.  Then
`ball c r \ K` is path connected: a compact zero-dimensional set is removable in a ball of
dimension `≥ 2`.

The substance is the *global* removability theorem
`Work.Whitney.PathTools.isPathConnected_compl_of_isCompact_isTotallyDisconnected'`: in a real inner
product space of dimension `≥ 2`, a compact totally disconnected set does not separate two points of
its complement (Sierpiński's theorem, transported to a two-plane through the two points).

The ball version is deduced from the global one by the radial parametrisation of the ball,
`ψ z = c + (r / (1 + ‖z‖)) • z`.  The map `ψ` is a continuous bijection of `E` onto
`Metric.ball c r` (its inverse on the ball is `w ↦ (r - ‖w - c‖)⁻¹ • (w - c)`).  The preimage
`K' = ψ ⁻¹' K` of a compact totally disconnected `K ⊆ ball c r` is again compact -- `K` keeps a
positive distance from the sphere `S(c, r)`, which bounds `‖z‖` for `z ∈ K'` -- and totally
disconnected, because `ψ` is injective.  Hence `E \ K'` is path connected, and its image under `ψ`
is `ball c r \ K`.

The first part of the file contains the elementary geometric material collected on the way; the
assembly is at the end.
-/

/-- **Escape ray.**  From a point `p` outside the closed ball `closedBall a ρ`, the ray in the
direction `p - a` (radially away from the centre) never meets the ball. -/
theorem escape_ray_avoid_closedBall {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {a p : E} {ρ : ℝ} (hp : p ∉ closedBall a ρ) :
    ∀ t : ℝ, 0 ≤ t → p + t • (p - a) ∉ closedBall a ρ := by
  have hlt : ρ < ‖p - a‖ := by
    rw [mem_closedBall, dist_eq_norm] at hp; exact lt_of_not_ge hp
  intro t ht hmem
  rw [mem_closedBall, dist_eq_norm] at hmem
  have hsplit : p + t • (p - a) - a = (1 + t) • (p - a) := by module
  rw [hsplit, norm_smul, Real.norm_of_nonneg (by linarith)] at hmem
  nlinarith [norm_nonneg (p - a), hlt]

/-- **Disjointification.**  A finite cover by relatively clopen sets can be replaced by a
pairwise disjoint one with the same index set, each new piece contained in the corresponding old
one and still covering. -/
theorem exists_isClopen_partition_of_cover {X : Type*} [TopologicalSpace X] {ι : Type*}
    [Fintype ι] [LinearOrder ι] {V : ι → Set X} (hV : ∀ i, IsClopen (V i)) :
    ∃ W : ι → Set X, (∀ i, IsClopen (W i)) ∧ (∀ i, W i ⊆ V i) ∧
      (∀ i j, i ≠ j → Disjoint (W i) (W j)) ∧ (⋃ i, V i) ⊆ ⋃ i, W i := by
  classical
  refine ⟨fun k => V k \ ⋃ j ∈ (Finset.univ.filter (fun j => j < k) : Set ι), V j,
    ?_, ?_, ?_, ?_⟩
  · intro k
    refine (hV k).diff ?_
    exact (Finset.finite_toSet _).isClopen_biUnion (fun j _ => hV j)
  · intro k; exact diff_subset
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    rcases lt_or_gt_of_ne hij with h | h
    · exact hxj.2 (by
        simp only [mem_iUnion, Finset.mem_coe, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact ⟨i, h, hxi.1⟩)
    · exact hxi.2 (by
        simp only [mem_iUnion, Finset.mem_coe, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact ⟨j, h, hxj.1⟩)
  · intro x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    have hne : (Finset.univ.filter (fun j : ι => x ∈ V j)).Nonempty :=
      ⟨k, by simp [hk]⟩
    obtain ⟨k₀, hk₀mem, hk₀min⟩ :=
      Finset.exists_min_image (Finset.univ.filter (fun j : ι => x ∈ V j)) (fun j => j) hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk₀mem
    simp only [mem_iUnion]
    refine ⟨k₀, hk₀mem, ?_⟩
    simp only [mem_iUnion, not_exists, not_and]
    intro j hj hxj
    have hjlt : j < k₀ := by simpa using hj
    have hmem : j ∈ Finset.univ.filter (fun j : ι => x ∈ V j) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hxj
    have hle := hk₀min j hmem
    exact absurd (lt_of_lt_of_le hjlt hle) (lt_irrefl _)

/-- **Zero-dimensionality.**  In a compact totally disconnected metric space, for every `ε > 0`
there is a finite family of relatively clopen sets of diameter `< ε` covering the space.  Combined
with the Lebesgue number of this cover and a disjointification, it yields `δ > 0` such that any two
points joined by a `δ`-chain lie in one piece of the cover, hence are at distance `< ε`. -/
theorem exists_finite_clopen_cover_small {X : Type u} [MetricSpace X] [CompactSpace X]
    [TotallyDisconnectedSpace X] {ε : ℝ} (hε : 0 < ε) :
    ∃ (ι : Type u) (_ : Fintype ι) (V : ι → Set X), (∀ i, IsClopen (V i)) ∧ univ ⊆ ⋃ i, V i ∧
      ∀ i, ∀ x ∈ V i, ∀ y ∈ V i, dist x y < ε := by
  have key : ∀ x : X, ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ V ⊆ ball x (ε / 2) := by
    intro x
    obtain ⟨V, hV, hxV, hVsub⟩ :=
      compact_exists_isClopen_in_isOpen (x := x) (U := ball x (ε / 2)) isOpen_ball
        (mem_ball_self (by linarith))
    exact ⟨V, hV, hxV, hVsub⟩
  choose V hVcl hxV hVsub using key
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover V (fun x => (hVcl x).isOpen)
    (fun x _ => mem_iUnion.mpr ⟨x, hxV x⟩)
  refine ⟨{x : X // x ∈ t}, inferInstance, fun i => V i.1, fun i => hVcl i.1, ?_, ?_⟩
  · intro x _
    have hx : x ∈ ⋃ i ∈ t, V i := ht (mem_univ x)
    simp only [mem_iUnion] at hx ⊢
    obtain ⟨i, hi, hxi⟩ := hx
    exact ⟨⟨i, hi⟩, hxi⟩
  · intro i x hx y hy
    have h1 : dist x (i.1 : X) < ε / 2 := hVsub i.1 hx
    have h2 : dist y (i.1 : X) < ε / 2 := hVsub i.1 hy
    have h3 : dist x y ≤ dist x (i.1 : X) + dist (i.1 : X) y := dist_triangle _ _ _
    have h4 : dist (i.1 : X) y < ε / 2 := by rwa [dist_comm] at h2
    linarith

/-- **Uniform 0-dimensionality.**  In a compact totally disconnected metric space, for every
`ε > 0` there is `δ > 0` such that any two points joined by a `δ`-chain lie in a common piece of
a finite clopen partition, hence are at distance `< ε`. -/
theorem exists_chain_gap {X : Type u} [MetricSpace X] [CompactSpace X]
    [TotallyDisconnectedSpace X] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : X, Relation.ReflTransGen (fun a b : X => dist a b < δ) x y →
      dist x y < ε := by
  classical
  -- a finite clopen cover by sets of diameter < ε/2
  obtain ⟨ι, hfin, V, hVcl, hVcov, hVdiam⟩ := exists_finite_clopen_cover_small
    (X := X) (ε := ε / 2) (by linarith)
  haveI := hfin
  -- reindex along `Fintype.equivFin` so that we have a linear order
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  set V' : Fin (Fintype.card ι) → Set X := fun k => V (e.symm k) with hV'
  have hV'cl : ∀ k, IsClopen (V' k) := fun k => hVcl _
  have hV'cov : univ ⊆ ⋃ k, V' k := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hVcov hx)
    exact mem_iUnion.mpr ⟨e i, by simpa [hV'] using hi⟩
  -- disjointify
  obtain ⟨W, hWcl, hWsub, hWdisj, hWcov⟩ := exists_isClopen_partition_of_cover hV'cl
  have hWcovtot : univ ⊆ ⋃ k, W k := hV'cov.trans hWcov
  -- Lebesgue number of the disjointified (still open) cover
  obtain ⟨δ, hδpos, hδ⟩ := lebesgue_number_lemma_of_metric (s := (univ : Set X))
    isCompact_univ (fun k => (hWcl k).isOpen) hWcovtot
  refine ⟨δ, hδpos, ?_⟩
  -- a step of the chain keeps us in one piece
  have hstep : ∀ a b : X, dist a b < δ → ∃ k, a ∈ W k ∧ b ∈ W k := by
    intro a b hab
    obtain ⟨k, hk⟩ := hδ a (mem_univ a)
    exact ⟨k, hk (mem_ball_self hδpos), hk (by simpa [dist_comm] using hab)⟩
  -- hence the whole chain stays in one piece
  have key : ∀ x y : X, Relation.ReflTransGen (fun a b : X => dist a b < δ) x y →
      ∃ k, x ∈ W k ∧ y ∈ W k := by
    intro x y hxy
    induction hxy with
    | refl =>
        obtain ⟨k, hk⟩ := mem_iUnion.mp (hWcovtot (mem_univ x))
        exact ⟨k, hk, hk⟩
    | tail hab hb ih =>
        obtain ⟨k, hxk, hzk⟩ := ih
        obtain ⟨m, hzm, hym⟩ := hstep _ _ hb
        have hkm : k = m := by
          by_contra hkm
          exact Set.disjoint_left.mp (hWdisj k m hkm) hzk hzm
        exact ⟨k, hxk, hkm ▸ hym⟩
  intro x y hxy
  obtain ⟨k, hxk, hyk⟩ := key x y hxy
  have hd : dist x y < ε / 2 := by
    have h1 : x ∈ V (e.symm k) := hWsub k hxk
    have h2 : y ∈ V (e.symm k) := hWsub k hyk
    exact hVdiam (e.symm k) x h1 y h2
  linarith

/-- **Exterior of a closed ball.**  In a real inner product space of dimension `> 1`, the
complement of a closed ball is the continuous image of `(ρ,∞) ×ˢ sphere 0 1`, hence path
connected. -/
theorem isPathConnected_compl_closedBall {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (hE : 1 < Module.rank ℝ E) (a : E) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    IsPathConnected ((closedBall a ρ)ᶜ : Set E) := by
  have hI : IsPathConnected (Ioi ρ) := (convex_Ioi ρ).isPathConnected ⟨ρ + 1, by simp⟩
  have hS : IsPathConnected (sphere (0:E) 1) := isPathConnected_sphere hE 0 (by norm_num)
  have hprod : IsPathConnected ((Ioi ρ) ×ˢ (sphere (0:E) 1)) := hI.prod hS
  have hcont : Continuous (fun p : ℝ × E => a + p.1 • p.2) :=
    continuous_const.add (continuous_fst.smul continuous_snd)
  have himg : IsPathConnected ((fun p : ℝ × E => a + p.1 • p.2)
      '' ((Ioi ρ) ×ˢ (sphere (0:E) 1))) := hprod.image hcont
  have hset : (fun p : ℝ × E => a + p.1 • p.2) '' ((Ioi ρ) ×ˢ (sphere (0:E) 1))
      = (closedBall a ρ)ᶜ := by
    ext z
    constructor
    · rintro ⟨⟨s, u⟩, ⟨hs, hu⟩, rfl⟩
      simp only [mem_Ioi] at hs
      simp only [mem_sphere, dist_eq_norm, sub_zero] at hu
      simp only [mem_compl_iff, mem_closedBall, dist_eq_norm]
      have : a + s • u - a = s • u := by abel
      rw [this, norm_smul, hu, mul_one, Real.norm_of_nonneg (le_of_lt (lt_of_le_of_lt hρ hs))]
      linarith
    · intro hz
      rw [mem_compl_iff, mem_closedBall, dist_eq_norm] at hz
      have hlt : ρ < ‖z - a‖ := lt_of_not_ge hz
      have hne : ‖z - a‖ ≠ 0 := ne_of_gt (lt_of_le_of_lt hρ hlt)
      refine ⟨(‖z - a‖, (‖z - a‖)⁻¹ • (z - a)), ⟨hlt, ?_⟩, ?_⟩
      · simp only [mem_sphere, dist_eq_norm, sub_zero]
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hne]
      · simp only
        rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
        abel
  rw [hset] at himg
  exact himg

/-- **The closed annulus is path connected** (dimension `> 1`): the image of
`Icc ρ r ×ˢ sphere 0 1` under `(s, u) ↦ c + s • u`.  When `K ⊆ ball c ρ`, every point of the closed
annulus `{ρ ≤ dist · c ≤ r}` is outside `K`. -/
theorem isPathConnected_closedAnnulus {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hE : 1 < Module.rank ℝ E) (c : E) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) :
    IsPathConnected {z : E | ρ ≤ dist z c ∧ dist z c ≤ r} := by
  have hS : IsPathConnected (Metric.sphere (0 : E) 1) := isPathConnected_sphere hE 0 (by norm_num)
  have hne : (Set.Icc ρ r).Nonempty := ⟨ρ, ⟨le_rfl, hρr⟩⟩
  have hI : IsPathConnected (Set.Icc ρ r) := (convex_Icc ρ r).isPathConnected hne
  have hpr : IsPathConnected (Set.Icc ρ r ×ˢ Metric.sphere (0 : E) 1) := hI.prod hS
  have hcont : Continuous (fun p : ℝ × E => c + p.1 • p.2) :=
    continuous_const.add (continuous_fst.smul continuous_snd)
  have himg : IsPathConnected ((fun p : ℝ × E => c + p.1 • p.2)
      '' (Set.Icc ρ r ×ˢ Metric.sphere (0 : E) 1)) := hpr.image hcont
  have hset : (fun p : ℝ × E => c + p.1 • p.2) '' (Set.Icc ρ r ×ˢ Metric.sphere (0 : E) 1)
      = {z : E | ρ ≤ dist z c ∧ dist z c ≤ r} := by
    ext z
    constructor
    · rintro ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩
      have hu' : ‖u‖ = 1 := by
        rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hu
        exact hu
      have ht0 : (0 : ℝ) ≤ t := le_trans (le_of_lt hρ) ht.1
      have h1 : c + t • u - c = t • u := by abel
      have h2 : dist (c + t • u) c = t := by
        rw [dist_eq_norm, h1, norm_smul, hu', mul_one, Real.norm_of_nonneg ht0]
      exact ⟨by rw [h2]; exact ht.1, by rw [h2]; exact ht.2⟩
    · rintro ⟨h1, h2⟩
      rw [dist_eq_norm] at h1 h2
      have hpos : 0 < ‖z - c‖ := lt_of_lt_of_le hρ h1
      have hne' : ‖z - c‖ ≠ 0 := ne_of_gt hpos
      refine ⟨(‖z - c‖, (‖z - c‖)⁻¹ • (z - c)), ⟨⟨h1, h2⟩, ?_⟩, ?_⟩
      · simp only [Metric.mem_sphere, dist_eq_norm, sub_zero]
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hne']
      · simp only
        rw [smul_smul, mul_inv_cancel₀ hne', one_smul]
        abel
  rw [hset] at himg
  exact himg

/-- **Two points in a common preconnected piece.**  A set is preconnected as soon as every two of
its points lie in a common preconnected subset of it. -/
theorem isPreconnected_of_forall_exists_common {X : Type*} [TopologicalSpace X] {S : Set X}
    (h : ∀ x ∈ S, ∀ y ∈ S, ∃ T : Set X, T ⊆ S ∧ IsPreconnected T ∧ x ∈ T ∧ y ∈ T) :
    IsPreconnected S := by
  intro u v hu hv huv hxu hxv
  obtain ⟨x, hxS, hxu'⟩ := hxu
  obtain ⟨y, hyS, hyv'⟩ := hxv
  obtain ⟨T, hTS, hTpre, hxT, hyT⟩ := h x hxS y hyS
  have hTuv : T ⊆ u ∪ v := fun z hz => huv (hTS hz)
  have h1 : (T ∩ u).Nonempty := ⟨x, hxT, hxu'⟩
  have h2 : (T ∩ v).Nonempty := ⟨y, hyT, hyv'⟩
  obtain ⟨z, hzT, hzu, hzv⟩ := hTpre u v hu hv hTuv h1 h2
  exact ⟨z, hTS hzT, hzu, hzv⟩

/-- **Radial transport of the global removability theorem into a ball.**  If `0 < r` and `K` is a
compact totally disconnected subset of the ball `ball c r` in a space of dimension `≥ 2`, then
`ball c r \ K` is path connected. -/
theorem ball_sdiff_isPathConnected_radial {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hm : 2 ≤ Module.finrank ℝ E) {c : E} {r : ℝ} (hr : 0 < r)
    {K : Set E} (hK : IsCompact K) (hsub : K ⊆ Metric.ball c r)
    (htd : IsTotallyDisconnected K) : IsPathConnected (Metric.ball c r \ K) := by
  classical
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E
  -- the radial parametrisation of the ball
  set ψ : E → E := fun z => c + (r / (1 + ‖z‖)) • z with hψdef
  have hψapply : ∀ z : E, ψ z = c + (r / (1 + ‖z‖)) • z := fun z => by rw [hψdef]
  have hψcont : Continuous ψ := by
    rw [hψdef]
    have h1 : Continuous fun z : E => (1 : ℝ) + ‖z‖ := continuous_const.add continuous_norm
    have h2 : Continuous fun z : E => r / (1 + ‖z‖) :=
      Continuous.div continuous_const h1 (by intro z; positivity)
    exact continuous_const.add (h2.smul continuous_id)
  -- distance of `ψ z` from the centre
  have hψmem : ∀ z : E, ‖ψ z - c‖ = r * ‖z‖ / (1 + ‖z‖) := by
    intro z
    rw [hψapply z, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ r / (1 + ‖z‖))]
    ring
  -- `ψ` maps into the ball
  have hψlt : ∀ z : E, ψ z ∈ Metric.ball c r := by
    intro z
    rw [Metric.mem_ball, dist_eq_norm, hψmem z]
    rw [div_lt_iff₀ (by positivity : (0:ℝ) < 1 + ‖z‖)]
    nlinarith [norm_nonneg z]
  -- `ψ` is onto the ball
  have hψsurj : ∀ w ∈ Metric.ball c r, ∃ z : E, ψ z = w := by
    intro w hw
    have hd : ‖w - c‖ < r := by
      have h := Metric.mem_ball.mp hw
      rwa [dist_eq_norm] at h
    have hposd : 0 < r - ‖w - c‖ := by linarith
    by_cases h0 : w - c = 0
    · have hwc : w = c := sub_eq_zero.mp h0
      refine ⟨0, ?_⟩
      rw [hψapply, hwc]
      simp
    · refine ⟨(r - ‖w - c‖)⁻¹ • (w - c), ?_⟩
      have hne : r - ‖w - c‖ ≠ 0 := ne_of_gt hposd
      have hznorm : ‖(r - ‖w - c‖)⁻¹ • (w - c)‖ = ‖w - c‖ / (r - ‖w - c‖) := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_eq_div]
      have hkey : r / (1 + ‖w - c‖ / (r - ‖w - c‖)) = r - ‖w - c‖ := by
        rw [div_eq_iff (by positivity : (1:ℝ) + ‖w - c‖ / (r - ‖w - c‖) ≠ 0)]
        field_simp
        ring
      rw [hψapply, hznorm, hkey, smul_smul, mul_inv_cancel₀ hne, one_smul]
      abel
  -- `ψ` is injective
  have hψinj : Function.Injective ψ := by
    intro z z' h
    have hdeq : r * ‖z‖ / (1 + ‖z‖) = r * ‖z'‖ / (1 + ‖z'‖) := by
      rw [← hψmem z, ← hψmem z', h]
    have h1 : 1 + ‖z‖ ≠ 0 := by positivity
    have h2 : 1 + ‖z'‖ ≠ 0 := by positivity
    have hnorm : ‖z‖ = ‖z'‖ := by
      have h3 : r * ‖z‖ * (1 + ‖z'‖) = r * ‖z'‖ * (1 + ‖z‖) := by
        rw [div_eq_div_iff h1 h2] at hdeq
        exact hdeq
      nlinarith [hr]
    have ha : (r / (1 + ‖z‖)) • z = (r / (1 + ‖z'‖)) • z' := by
      have h' := h
      rw [hψapply z, hψapply z'] at h'
      exact add_left_cancel h'
    rw [hnorm] at ha
    have hane : r / (1 + ‖z'‖) ≠ 0 := div_ne_zero (ne_of_gt hr) h2
    have h5 : (r / (1 + ‖z'‖)) • (z - z') = 0 := by rw [smul_sub, ha, sub_self]
    rcases smul_eq_zero.mp h5 with h6 | h6
    · exact absurd h6 hane
    · exact sub_eq_zero.mp h6
  -- the preimage of `K` under `ψ`
  set K' : Set E := ψ ⁻¹' K with hK'def
  have hK'mem : ∀ z : E, z ∈ K' ↔ ψ z ∈ K := fun z => Iff.rfl
  have hK'closed : IsClosed K' := hK.isClosed.preimage hψcont
  -- `K` keeps a positive distance from the sphere; equivalently, `K'` is bounded
  obtain ⟨δ, hδpos, hδle⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ w ∈ K, ‖w - c‖ ≤ r - δ := by
    rcases K.eq_empty_or_nonempty with h | hne
    · exact ⟨r / 2, by linarith, by simp [h]⟩
    · obtain ⟨w₀, hw₀, hmin⟩ := hK.exists_isMinOn hne
        (continuous_const.sub (continuous_id.sub continuous_const).norm).continuousOn
      have hval : 0 < r - ‖w₀ - c‖ := by
        have h1 := hsub hw₀
        rw [Metric.mem_ball, dist_eq_norm] at h1
        linarith
      exact ⟨r - ‖w₀ - c‖, hval, fun w hw => by
        have h2 : r - ‖w₀ - c‖ ≤ r - ‖w - c‖ := hmin hw
        linarith⟩
  have hK'bdd : Bornology.IsBounded K' := by
    refine (Metric.isBounded_iff_subset_closedBall (0 : E)).mpr ⟨(r - δ) / δ, ?_⟩
    intro z hz
    have hzK : ψ z ∈ K := (hK'mem z).mp hz
    have h1 : ‖ψ z - c‖ ≤ r - δ := hδle (ψ z) hzK
    rw [hψmem z, div_le_iff₀ (by positivity : (0:ℝ) < 1 + ‖z‖)] at h1
    rw [Metric.mem_closedBall, dist_zero_right, le_div_iff₀ hδpos]
    nlinarith [h1, norm_nonneg z]
  have hK'cpt : IsCompact K' := Metric.isCompact_iff_isClosed_bounded.mpr ⟨hK'closed, hK'bdd⟩
  have hK'td : IsTotallyDisconnected K' := by
    intro S hSK hSpre
    have himg : IsPreconnected (ψ '' S) := hSpre.image ψ hψcont.continuousOn
    have hsubK : ψ '' S ⊆ K := by
      rintro w ⟨z, hz, rfl⟩
      exact (hK'mem z).mp (hSK hz)
    have hsing : (ψ '' S).Subsingleton := htd (ψ '' S) hsubK himg
    intro z hz z' hz'
    exact hψinj (hsing ⟨z, hz, rfl⟩ ⟨z', hz', rfl⟩)
  -- the global theorem, transported along `ψ`
  have hpc : IsPathConnected (K'ᶜ) :=
    isPathConnected_compl_of_isCompact_isTotallyDisconnected' hm hK'cpt hK'td
  have himgpc : IsPathConnected (ψ '' (K'ᶜ)) := hpc.image hψcont
  have hset : ψ '' (K'ᶜ) = Metric.ball c r \ K := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hψlt z, fun hmem => hz ((hK'mem z).mpr hmem)⟩
    · intro hw
      obtain ⟨z, hz⟩ := hψsurj w hw.1
      exact ⟨z, fun hzK => hw.2 (hz ▸ (hK'mem z).mp hzK), hz⟩
  rwa [hset] at himgpc

/-- In a finite dimensional real inner product space of dimension `≥ 2`, an open ball minus a
compact totally disconnected set is path connected.  ("A compact 0-dimensional set is removable in
a ball of dimension ≥ 2.")

This is `ball_sdiff_isPathConnected_radial`: the global removability theorem
`isPathConnected_compl_of_isCompact_isTotallyDisconnected'` (a compact totally disconnected set in
dimension `≥ 2` does not separate) is transported to the ball along the radial parametrisation
`z ↦ c + (r / (1 + ‖z‖)) • z` of the ball. -/
theorem ball_sdiff_totallyDisconnected {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hm : 2 ≤ Module.finrank ℝ E)
    {c : E} {r : ℝ} (hr : 0 < r)
    {K : Set E} (hK : IsCompact K)
    (hsub : K ⊆ Metric.ball c r) (htd : IsTotallyDisconnected K) :
    IsPathConnected (Metric.ball c r \ K) :=
  ball_sdiff_isPathConnected_radial hm hr hK hsub htd

end Work.Whitney.PathTools
