import Mathlib
import Submission.Work.Whitney.PathTools.isPathConnected_sdiff_arc_empty
import Submission.Work.Whitney.PathTools.minimal_separator_no_cut_point
import Submission.Work.Whitney.PathTools.plane_arc_nonseparation
import Submission.Work.Whitney.PathTools.isPreconnected_sdiff_of_local_room
import Submission.Work.Whitney.PathTools.isPreconnected_sdiff_of_room_of_open

/-!
# Removing a half-open arc with a free end from an open preconnected set

`Work.Noncompact.CompressionTube.spike_removal`:  if `C` is an open preconnected subset of an
`n`-manifold with `n ≥ 2`, `σ : ℝ → M` is continuous and injective on `[0,1]`, the slit
`σ '' (0,1]` lies in `C` and the free end `σ 0` does *not* lie in `C`, then `C \ σ '' (0,1]` is
again preconnected.

Since `σ 0 ∉ C`, one has `C \ σ '' Ioc 0 1 = C \ σ '' Icc 0 1`, i.e. one removes from `C` the
part of the compact arc `σ '' Icc 0 1` that lies in `C`.

## The two arguments

* **`n ≥ 3`** (`spike_removal_ge3`).  Apply the local-room criterion
  `Work.Whitney.PathTools.isPreconnected_sdiff_of_local_room` with `T := C` and
  `Y := σ '' Icc 0 1`.  The required local rooms — arbitrarily small open `O ∋ y` with
  `O \ Y` nonempty and preconnected — exist at *every* point of the arc by
  `Work.Whitney.PathTools.room_at_arc_manifold` (there is enough room in dimension `≥ 3` to walk
  around a point of a one-dimensional arc).

* **`n = 2`** (`spike_removal_two`).  Here the local rooms of the previous paragraph do **not**
  exist (a disc minus an arc through its centre is disconnected), so we peel the arc instead, using
  its free end.  The parametrisation is reversed, `τ u := σ (1 - u)`, so that the slit becomes
  `τ '' Ico 0 1 = σ '' Ioc 0 1`, with its *included* end `τ 0 = σ 1` in the interior of `C` and its
  excluded end `τ 1 = σ 0` outside `C`.  For `c ∈ [0,1]` put `R c := C \ τ '' Icc c 1`, so that
  `R 1 = C` and `R 0 = C \ σ '' Ioc 0 1`; we show that `S := {c ∈ [0,1] | IsPreconnected (R c)}`
  contains `0`.

  The *step* goes from `s ∈ S` down to `c < s`: `R s \ τ '' Ico c s = R c`, and a room `U` around
  the half-open slit `τ '' Ico c s` with `γ '' Ico c s ⊆ U ⊆ R s` and `U \ (slit)` preconnected is
  provided by `room_of_arc_piece`.  Inside a chart containing the *short* piece `τ '' Icc c s`, the
  room is the inverse image under the chart of the connected component `Ωp` of `e (τ c)` in
  `e '' (R s ∩ e.source)`; the slit `τ '' Ico c s` lies in `Ωp` while its far end `τ s` does not
  (it is removed by `R s`), so the planar theorem `planar_slit_free_end` below says that `Ωp` minus
  the slit is preconnected.  The room criterion
  `Work.Whitney.PathTools.isPreconnected_sdiff_of_room_of_open` then gives the step.

  Finally `0 ∈ S`: if `sstar := sInf S` were positive, a chart at `τ sstar`, an `s ∈ S` just above
  `sstar` (for `sstar ∈ S`) and then the same step applied with `c := max 0 (sstar - δ/2)`
  contradict the definition of `sInf`.

## A note on imports

The relevant parts of the shared library live in two mutually incompatible import cones (the
auxiliary constant `Work.Whitney.PathTools.Grid.isPreconnected_insert_of_mem_closure` is declared
both in `planar_local_room_build` and in
`sphere_sdiff_isCompact_totallyDisconnected_isPreconnected`), so the planar tools used here —
`plane_arc_nonseparation`, `Grid.janis_singleton_plane` — are taken from modules compatible with
`room_at_arc_manifold`, and the two planar lemmas `janis_compact_closed_singleton` and
`planar_slit_free_end` below are ported into this file.  (`planar_slit_free_end` is the statement
proved as `Work.Whitney.PathTools.EndpointRoom.isPreconnected_sdiff_Ico_of_component` in
`Submission/Work/Whitney/PathTools/endpoint_room_aux.lean`, on the other side of that split.)
-/

namespace Work.Noncompact.CompressionTube

open Set Metric Topology
open scoped Topology

/-- **Janiszewski's two-piece lemma, compact against closed, one common point** (plane).

If `A` is compact, `B` is closed and `A ∩ B = {p}`, then two points `x, y ∉ A ∪ B` which can be
joined in the complement of `A` and in the complement of `B` can be joined in the complement of
`A ∪ B`.

The proof reduces the closed obstacle to a compact one by cutting it off with a large closed ball
and adding the boundary sphere; the resulting compact obstacles `A` and `L` meet exactly in `p`, so
the compact-compact single-point theorem `Grid.janis_singleton_plane` applies.  The sphere keeps the
resulting path inside the ball, where it avoids all of `B`. -/
theorem janis_compact_closed_singleton {A B : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : IsCompact A) (hB : IsClosed B) {p : EuclideanSpace ℝ (Fin 2)} (hAB : A ∩ B = {p})
    {x y : EuclideanSpace ℝ (Fin 2)} (hx : x ∉ A ∪ B) (hy : y ∉ A ∪ B)
    (h₁ : JoinedIn (Aᶜ) x y) (h₂ : JoinedIn (Bᶜ) x y) :
    JoinedIn ((A ∪ B)ᶜ) x y := by
  classical
  have hp : p ∈ A ∩ B := by rw [hAB]; exact Set.mem_singleton p
  obtain ⟨σ₂, hσ₂⟩ := h₂
  obtain ⟨R₁, hR₁⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace ℝ (Fin 2))).mp hA.isBounded
  obtain ⟨R₂, hR₂⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace ℝ (Fin 2))).mp
      (isCompact_univ.image σ₂.continuous).isBounded
  set R : ℝ := |R₁| + |R₂| + ‖x‖ + ‖y‖ + 1 with hRdef
  have hxR : ‖x‖ < R := by
    rw [hRdef]
    linarith [abs_nonneg R₁, abs_nonneg R₂, norm_nonneg y]
  have hyR : ‖y‖ < R := by
    rw [hRdef]
    linarith [abs_nonneg R₁, abs_nonneg R₂, norm_nonneg x]
  have hAR : A ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R := by
    intro z hz
    have h1 : ‖z‖ ≤ R₁ := by
      have := hR₁ hz
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    rw [Metric.mem_ball, dist_zero_right]
    linarith [h1, le_abs_self R₁, abs_nonneg R₂, norm_nonneg x, norm_nonneg y]
  have hσ₂R : ∀ t, σ₂ t ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R := by
    intro t
    have h1 : ‖σ₂ t‖ ≤ R₂ := by
      have := hR₂ ⟨t, Set.mem_univ t, rfl⟩
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    rw [Metric.mem_ball, dist_zero_right]
    linarith [h1, le_abs_self R₂, abs_nonneg R₁, norm_nonneg x, norm_nonneg y]
  have hpR : p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R :=
    Metric.ball_subset_closedBall (hAR hp.1)
  set K : Set (EuclideanSpace ℝ (Fin 2)) := A with hK
  set L : Set (EuclideanSpace ℝ (Fin 2)) :=
    (B ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R)
      ∪ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) R with hL
  have hKcpt : IsCompact K := by rw [hK]; exact hA
  have hLcpt : IsCompact L := by
    rw [hL]
    exact ((isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) R).inter_left hB).union
      (isCompact_sphere (0 : EuclideanSpace ℝ (Fin 2)) R)
  have hKL : K ∩ L = {p} := by
    rw [hK, hL]
    refine Set.Subset.antisymm ?_ ?_
    · rintro z ⟨hzA, hzL⟩
      rcases hzL with hzB | hzS
      · exact Set.mem_singleton_iff.mp (hAB ▸ ⟨hzA, hzB.1⟩)
      · exfalso
        rw [Metric.mem_sphere, dist_zero_right] at hzS
        have hb := Metric.mem_ball.mp (hAR hzA)
        rw [dist_zero_right] at hb
        linarith
    · rintro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨hp.1, Or.inl ⟨hp.2, hpR⟩⟩
  have hxKL : x ∉ K ∪ L := by
    rw [Set.mem_union, not_or]
    refine ⟨?_, ?_⟩
    · rw [hK]; exact fun h => hx (Or.inl h)
    · rw [hL, Set.mem_union, not_or]
      refine ⟨?_, ?_⟩
      · exact fun h => hx (Or.inr h.1)
      · exact fun h => absurd h (by
          rw [Metric.mem_sphere, dist_zero_right]; exact ne_of_lt hxR)
  have hyKL : y ∉ K ∪ L := by
    rw [Set.mem_union, not_or]
    refine ⟨?_, ?_⟩
    · rw [hK]; exact fun h => hy (Or.inl h)
    · rw [hL, Set.mem_union, not_or]
      refine ⟨?_, ?_⟩
      · exact fun h => hy (Or.inr h.1)
      · exact fun h => absurd h (by
          rw [Metric.mem_sphere, dist_zero_right]; exact ne_of_lt hyR)
  have h₁' : JoinedIn (Kᶜ) x y := by rw [hK]; exact h₁
  have h₂' : JoinedIn (Lᶜ) x y := by
    refine ⟨σ₂, fun t => ?_⟩
    rw [Set.mem_compl_iff, hL, Set.mem_union, not_or]
    refine ⟨fun h => hσ₂ t h.1, ?_⟩
    exact fun h => absurd h (by
      rw [Metric.mem_sphere, dist_zero_right]
      exact ne_of_lt (by simpa using Metric.mem_ball.mp (hσ₂R t)))
  obtain ⟨σ, hσ⟩ :=
    Work.Whitney.PathTools.Grid.janis_singleton_plane hKcpt hLcpt hKL hxKL hyKL h₁' h₂'
  have hrange_sub : Set.range σ ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R
      ∪ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R)ᶜ := by
    rintro _ ⟨t, rfl⟩
    by_cases hz : σ t ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R
    · by_cases hz2 : σ t ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R
      · exact Or.inl hz2
      · exfalso
        have hsphere : σ t ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) R := by
          rw [Metric.mem_sphere, dist_zero_right]
          rw [Metric.mem_closedBall, dist_zero_right] at hz
          rw [Metric.mem_ball, dist_zero_right] at hz2
          exact le_antisymm hz (le_of_not_gt hz2)
        exact hσ t (Or.inr (by rw [hL]; exact Or.inr hsphere))
    · exact Or.inr hz
  have hdisj : Set.range σ ∩ (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R
      ∩ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R)ᶜ) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨-, h1, h2⟩
    exact h2 (Metric.ball_subset_closedBall h1)
  have hpre : IsPreconnected (Set.range σ) := by
    rw [← Set.image_univ]
    exact isPreconnected_univ.image σ σ.continuous.continuousOn
  have hσball : ∀ t, σ t ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R := by
    rcases (isPreconnected_iff_subset_of_disjoint.mp hpre)
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R)
      ((Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R))ᶜ
      Metric.isOpen_ball Metric.isClosed_closedBall.isOpen_compl hrange_sub hdisj with h | h
    · exact fun t => h ⟨t, rfl⟩
    · exfalso
      have hxball : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R := by
        rw [Metric.mem_ball, dist_zero_right]; exact hxR
      have hthis : σ 0 ∈ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R)ᶜ :=
        h ⟨0, rfl⟩
      rw [Set.mem_compl_iff, σ.source] at hthis
      exact hthis (Metric.ball_subset_closedBall hxball)
  have hσB : ∀ t, σ t ∉ B := by
    intro t htB
    refine hσ t (Or.inr ?_)
    rw [hL]
    exact Or.inl ⟨htB, Metric.ball_subset_closedBall (hσball t)⟩
  refine ⟨σ, fun t => ?_⟩
  rw [Set.mem_compl_iff, Set.mem_union, not_or]
  exact ⟨fun hA' => hσ t (Or.inl (by rw [hK]; exact hA')), hσB t⟩

/-- **A slit with a free end does not separate** (plane).

Let `Ω ⊆ ℝ²` be open and preconnected, let `h : ℝ → ℝ²` be continuous and injective on `[0,c]`,
suppose `h '' [0,c'] ⊆ Ω` for every `c' < c` and `h c ∉ Ω`.  Then `Ω` with the half-open slit
`h '' [0,c)` removed is preconnected.

The slit is the part of the compact arc `K := h '' Icc 0 c` lying in `Ω` (they differ only by the
point `h c ∉ Ω`), and `K ∩ Ωᶜ = {h c}` is a single point, so Janiszewski
(`janis_compact_closed_singleton`, together with the Jordan arc theorem
`plane_arc_nonseparation`) joins any two points of `Ω \ K` inside `Ω \ K`. -/
theorem planar_slit_free_end {Ω : Set (EuclideanSpace ℝ (Fin 2))}
    (hΩo : IsOpen Ω) (hΩpre : IsPreconnected Ω)
    {h : ℝ → EuclideanSpace ℝ (Fin 2)} {c : ℝ} (hc : 0 < c)
    (hcont : ContinuousOn h (Set.Icc 0 c)) (hinj : Set.InjOn h (Set.Icc 0 c))
    (hsub : ∀ c' < c, h '' Set.Icc 0 c' ⊆ Ω) (hout : h c ∉ Ω) :
    IsPreconnected (Ω \ h '' Set.Ico (0:ℝ) c) := by
  have hIcc : h '' Set.Icc (0:ℝ) c = h '' Set.Ico (0:ℝ) c ∪ {h c} := by
    have h1 : Set.Icc (0:ℝ) c = Set.Ico (0:ℝ) c ∪ {c} := by
      ext t
      simp only [Set.mem_Icc, Set.mem_Ico, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · rintro ⟨h1, h2⟩
        rcases lt_or_eq_of_le h2 with h2' | h2'
        · exact Or.inl ⟨h1, h2'⟩
        · exact Or.inr h2'
      · rintro (⟨h1, h2⟩ | rfl)
        · exact ⟨h1, h2.le⟩
        · exact ⟨hc.le, le_rfl⟩
    calc h '' Set.Icc (0:ℝ) c = h '' (Set.Ico (0:ℝ) c ∪ {c}) := by rw [h1]
      _ = h '' Set.Ico (0:ℝ) c ∪ h '' {c} := by rw [Set.image_union]
      _ = h '' Set.Ico (0:ℝ) c ∪ {h c} := by rw [Set.image_singleton]
  have hEq : Ω \ h '' Set.Icc (0:ℝ) c = Ω \ h '' Set.Ico (0:ℝ) c := by
    rw [hIcc]
    ext z
    constructor
    · rintro ⟨hz, hz'⟩
      exact ⟨hz, fun h1 => hz' (Or.inl h1)⟩
    · rintro ⟨hz, h1⟩
      exact ⟨hz, fun h => h.elim h1 (fun h2 => hout (h2 ▸ hz))⟩
  rw [← hEq]
  by_cases hne : (Ω \ h '' Set.Icc (0:ℝ) c).Nonempty
  · obtain ⟨w, hw⟩ := hne
    have hpc : IsPathConnected (Ω \ h '' Set.Icc (0:ℝ) c) := by
      have hAeq : h '' Set.Icc (0:ℝ) c ∩ Ωᶜ = {h c} := by
        refine Set.Subset.antisymm ?_ ?_
        · rintro z ⟨hzA, hzB⟩
          obtain ⟨t, ht, rfl⟩ := hzA
          have ht_eq : t = c := by
            rcases lt_or_eq_of_le ht.2 with h' | h'
            · exact absurd (hsub t h' ⟨t, ⟨ht.1, le_refl t⟩, rfl⟩) hzB
            · exact h'
          rw [ht_eq]
          exact Set.mem_singleton_iff.mpr rfl
        · rintro z hz
          rw [Set.mem_singleton_iff] at hz
          subst hz
          exact ⟨⟨c, ⟨hc.le, le_rfl⟩, rfl⟩, hout⟩
      have hAsub : (h '' Set.Icc (0:ℝ) c ∩ Ωᶜ).Subsingleton := by
        rw [hAeq]; exact Set.subsingleton_singleton
      refine ⟨w, hw, fun y hy => ?_⟩
      have hyΩ : y ∈ Ω := hy.1
      have hyA : y ∉ h '' Set.Icc (0:ℝ) c := hy.2
      have hwΩ : w ∈ Ω := hw.1
      have hwA : w ∉ h '' Set.Icc (0:ℝ) c := hw.2
      have h₁ : JoinedIn ((h '' Set.Icc (0:ℝ) c)ᶜ) w y :=
        (Work.Whitney.PathTools.plane_arc_nonseparation isCompact_Icc hcont hinj).joinedIn w
          (by simpa using hwA) y (by simpa using hyA)
      have hΩpc : IsPathConnected Ω :=
        hΩo.isConnected_iff_isPathConnected.mp ⟨⟨w, hwΩ⟩, hΩpre⟩
      have h₂ : JoinedIn ((Ωᶜ : Set (EuclideanSpace ℝ (Fin 2)))ᶜ) w y := by
        rw [compl_compl]
        exact hΩpc.joinedIn w hwΩ y hyΩ
      have hmain := janis_compact_closed_singleton
        (isCompact_Icc.image_of_continuousOn hcont) hΩo.isClosed_compl hAeq
        (fun h => h.elim hwA (fun h' => h' hwΩ))
        (fun h => h.elim hyA (fun h' => h' hyΩ)) h₁ h₂
      have hEq2 : (((h '' Set.Icc (0:ℝ) c) ∪ Ωᶜ)ᶜ : Set (EuclideanSpace ℝ (Fin 2)))
          = Ω \ h '' Set.Icc (0:ℝ) c := by
        rw [Set.compl_union, compl_compl, Set.sdiff_eq, Set.inter_comm]
      rwa [hEq2] at hmain
    exact hpc.isConnected.2
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    exact isPreconnected_empty

/-- For a partial homeomorphism, `e.symm '' (s \ e '' a) = (e.symm '' s) \ a`. -/
theorem symm_image_sdiff_of_subset' {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (e : OpenPartialHomeomorph α β) {s : Set β} (hs : s ⊆ e.target) {a : Set α}
    (ha : a ⊆ e.source) : e.symm '' (s \ e '' a) = (e.symm '' s) \ a := by
  apply subset_antisymm
  · rintro z ⟨w, ⟨hw, hwe⟩, hwz⟩
    constructor
    · exact ⟨w, hw, hwz⟩
    · intro hza
      refine hwe (Exists.intro z (And.intro hza ?_))
      rw [← hwz]
      exact e.right_inv (hs hw)
  · rintro z ⟨hz, hza⟩
    obtain ⟨w, hw, hwz⟩ := hz
    refine ⟨w, ⟨hw, ?_⟩, hwz⟩
    rintro ⟨a', ha', haw⟩
    refine hza ?_
    rw [← hwz, ← haw, e.left_inv (ha ha')]
    exact ha'

/-- **Room around a piece of an arc inside an open set (surface case).**

Let `M` be a surface, `T ⊆ M` open, `γ : ℝ → M` continuous and injective on `[0,1]`, and let
`c < s` be points of `[0,1]` such that the piece `γ '' Icc c s` lies in the source of a chart `e`.
Suppose moreover that the half-open slit `γ '' Ico c s` lies in `T` while its far end `γ s` does
not.  Then there is an open `U` with

`γ '' Ico c s ⊆ U ⊆ T`  and  `U \ γ '' Ico c s` preconnected.

Inside the chart, the room is the connected component `Ωp` of `e (γ c)` in `e '' (T ∩ e.source)`.
The slit's far end `e (γ s) ∉ Ω` cuts the room at the far end, while the free end `γ c` is wrapped:
this is the classical "pacman" room, and preconnectedness of `Ωp` minus the slit image is the
planar theorem `planar_slit_free_end`. -/
theorem room_of_arc_piece {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    {T : Set M} (hTo : IsOpen T) {γ : ℝ → M} (hγ : Continuous γ)
    (hinj : Set.InjOn γ (Set.Icc (0:ℝ) 1))
    {c s : ℝ} (hc : c ∈ Set.Icc (0:ℝ) 1) (hs : s ∈ Set.Icc (0:ℝ) 1) (hcs : c < s)
    {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))}
    (hesrc : ∀ t ∈ Set.Icc c s, γ t ∈ e.source)
    (hpiece : γ '' Set.Ico c s ⊆ T) (hsT : γ s ∉ T) :
    ∃ U : Set M, IsOpen U ∧ γ '' Set.Ico c s ⊆ U ∧ U ⊆ T ∧
      IsPreconnected (U \ γ '' Set.Ico c s) := by
  classical
  haveI : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 2)) M
  have hcsIcc01 : Set.Icc c s ⊆ Set.Icc (0:ℝ) 1 :=
    fun t ht => ⟨le_trans hc.1 ht.1, le_trans ht.2 hs.2⟩
  have hcsIco01 : Set.Ico c s ⊆ Set.Icc (0:ℝ) 1 :=
    fun t ht => ⟨le_trans hc.1 ht.1, le_trans ht.2.le hs.2⟩
  set h : ℝ → EuclideanSpace ℝ (Fin 2) := fun t => e (γ t) with hhdef
  have hhcont : ContinuousOn h (Set.Icc c s) := e.continuousOn.comp hγ.continuousOn hesrc
  have hhinj : Set.InjOn h (Set.Icc c s) := by
    intro t₁ ht₁ t₂ ht₂ h12
    exact hinj (hcsIcc01 ht₁) (hcsIcc01 ht₂) (e.injOn (hesrc t₁ ht₁) (hesrc t₂ ht₂) h12)
  set Ω : Set (EuclideanSpace ℝ (Fin 2)) := e '' (T ∩ e.source) with hΩdef
  have hΩopen : IsOpen Ω :=
    e.isOpen_image_of_subset_source (hTo.inter e.open_source) Set.inter_subset_right
  have hcT : γ c ∈ T := hpiece ⟨c, ⟨le_rfl, hcs⟩, rfl⟩
  have hcsrc : γ c ∈ e.source := hesrc c ⟨le_rfl, hcs.le⟩
  have hcΩ : e (γ c) ∈ Ω := ⟨γ c, ⟨hcT, hcsrc⟩, rfl⟩
  set Ωp : Set (EuclideanSpace ℝ (Fin 2)) := connectedComponentIn Ω (e (γ c)) with hΩpdef
  have hΩpsub : Ωp ⊆ Ω := connectedComponentIn_subset Ω _
  have hΩpopen : IsOpen Ωp := hΩopen.connectedComponentIn
  have hΩppre : IsPreconnected Ωp := isPreconnected_connectedComponentIn
  have hcΩp : e (γ c) ∈ Ωp := mem_connectedComponentIn hcΩ
  have hΩptgt : Ωp ⊆ e.target := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := hΩpsub hz
    exact e.map_source hv.2
  -- the piece of the arc inside the chart lies in the component `Ωp`
  have hpieceΩp : ∀ t ∈ Set.Ico c s, h '' Set.Icc c t ⊆ Ωp := by
    intro t ht
    refine IsPreconnected.subset_connectedComponentIn
      ((isPreconnected_Icc).image h (hhcont.mono (fun u hu => ⟨hu.1, le_trans hu.2 ht.2.le⟩)))
      ⟨c, ⟨le_rfl, ht.1⟩, rfl⟩ ?_
    rintro z ⟨u, hu, rfl⟩
    exact Set.mem_image_of_mem e
      ⟨hpiece ⟨u, ⟨hu.1, lt_of_le_of_lt hu.2 ht.2⟩, rfl⟩,
        hesrc u ⟨hu.1, le_trans hu.2 ht.2.le⟩⟩
  have hpieceΩ : ∀ t ∈ Set.Ico c s, h t ∈ Ω := by
    intro t ht
    exact Set.mem_image_of_mem e
      ⟨hpiece ⟨t, ⟨ht.1, ht.2⟩, rfl⟩, hesrc t ⟨ht.1, ht.2.le⟩⟩
  set U : Set M := e.symm '' Ωp with hUdef
  have hUopen : IsOpen U := e.isOpen_image_symm_of_subset_target hΩpopen hΩptgt
  have hγsubU : γ '' Set.Ico c s ⊆ U := by
    rintro z ⟨t, ht, rfl⟩
    exact ⟨h t, hpieceΩp t ht ⟨t, ⟨ht.1, le_rfl⟩, rfl⟩,
      e.left_inv (hesrc t ⟨ht.1, ht.2.le⟩)⟩
  have hUsubT : U ⊆ T := by
    rintro z ⟨z', hz', rfl⟩
    obtain ⟨v, hv, hvz⟩ := hΩpsub hz'
    rw [← hvz, e.left_inv hv.2]
    exact hv.1
  -- the planar input, with the piece reparametrised to `[0,1]`
  set g : ℝ → EuclideanSpace ℝ (Fin 2) := fun u => h (c + u * (s - c)) with hgdef
  have hsc : 0 < s - c := sub_pos.mpr hcs
  have hg1 : g 1 = h s := by rw [hgdef]; norm_num
  have hgc : g 0 = e (γ c) := by rw [hgdef, hhdef]; norm_num
  have hgcont : ContinuousOn g (Set.Icc 0 1) := by
    rw [hgdef]
    refine hhcont.comp (by fun_prop) ?_
    intro u hu
    exact ⟨by nlinarith [hu.1, hsc], by nlinarith [hu.2, hsc]⟩
  have hginj : Set.InjOn g (Set.Icc 0 1) := by
    intro u₁ hu₁ u₂ hu₂ huv
    have h1 : c + u₁ * (s - c) = c + u₂ * (s - c) := by
      refine hhinj ⟨by nlinarith [hu₁.1, hsc], by nlinarith [hu₁.2, hsc]⟩
        ⟨by nlinarith [hu₂.1, hsc], by nlinarith [hu₂.2, hsc]⟩ huv
    have h2 : u₁ * (s - c) = u₂ * (s - c) := by linarith
    exact mul_right_cancel₀ (ne_of_gt hsc) h2
  have hgsub : ∀ c' < 1, g '' Set.Icc 0 c' ⊆ Ωp := by
    intro c' hc'
    by_cases hc'0 : 0 ≤ c'
    swap
    · rintro z ⟨u, hu, rfl⟩
      exact absurd (le_trans hu.1 hu.2) hc'0
    refine IsPreconnected.subset_connectedComponentIn
      ((isPreconnected_Icc).image g (hgcont.mono (fun u hu => ⟨hu.1, le_trans hu.2 hc'.le⟩)))
      ⟨0, ⟨le_rfl, hc'0⟩, hgc⟩ ?_
    rintro z ⟨u, hu, rfl⟩
    exact hpieceΩ (c + u * (s - c))
      ⟨by nlinarith [hu.1, hsc], by nlinarith [hu.2, hc', hsc]⟩
  have hgout : g 1 ∉ Ωp := by
    rw [hg1]
    intro hmem
    obtain ⟨v, hv, hve⟩ := hΩpsub hmem
    have hvs : v = γ s := e.injOn hv.2 (hesrc s ⟨hcs.le, le_rfl⟩) hve
    exact hsT (hvs ▸ hv.1)
  have hslit : IsPreconnected (Ωp \ g '' Set.Ico (0:ℝ) 1) :=
    planar_slit_free_end hΩpopen hΩppre one_pos hgcont hginj hgsub hgout
  have hgIco : g '' Set.Ico (0:ℝ) 1 = h '' Set.Ico c s := by
    rw [hgdef]
    ext z; constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨c + u * (s - c), ⟨by nlinarith [hu.1, hsc], by nlinarith [hu.2, hsc]⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      refine ⟨(t - c) / (s - c), ⟨div_nonneg (by linarith [ht.1]) hsc.le, ?_⟩, ?_⟩
      · rw [div_lt_one hsc]; linarith [ht.2]
      · show h (c + (t - c) / (s - c) * (s - c)) = h t
        congr 1
        field_simp
        ring
  have hpre : IsPreconnected (Ωp \ h '' Set.Ico c s) := by
    rw [← hgIco]; exact hslit
  have hsrcIco : γ '' Set.Ico c s ⊆ e.source := by
    rintro z ⟨t, ht, rfl⟩
    exact hesrc t ⟨ht.1, ht.2.le⟩
  have himg : e '' (γ '' Set.Ico c s) = h '' Set.Ico c s := by
    rw [hhdef, Set.image_image]
  have hUeq : U \ γ '' Set.Ico c s = e.symm '' (Ωp \ h '' Set.Ico c s) := by
    rw [hUdef, ← symm_image_sdiff_of_subset' e hΩptgt hsrcIco, himg]
  refine ⟨U, hUopen, hγsubU, hUsubT, ?_⟩
  rw [hUeq]
  exact hpre.image e.symm (e.continuousOn_symm.mono (fun z hz => hΩptgt hz.1))

/-- **The `n = 2` case of `spike_removal`.**  The arc is peeled from its free end `σ 1` towards
its other end `σ 0 ∉ C`. -/
theorem spike_removal_two {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    {C : Set M} (hC : IsOpen C) (hCpre : IsPreconnected C)
    {σ : ℝ → M} (hσc : Continuous σ) (hσinj : Set.InjOn σ (Set.Icc (0:ℝ) 1))
    (hσC : σ '' Set.Ioc (0:ℝ) 1 ⊆ C) (hσ0 : σ 0 ∉ C) :
    IsPreconnected (C \ σ '' Set.Ioc (0:ℝ) 1) := by
  classical
  set τ : ℝ → M := fun u => σ (1 - u) with hτdef
  have hτc : Continuous τ := by
    rw [hτdef]
    exact hσc.comp (continuous_const.sub continuous_id)
  have hτinj : Set.InjOn τ (Set.Icc (0:ℝ) 1) := by
    intro u hu v hv huv
    have h2 : 1 - u = 1 - v :=
      hσinj ⟨by linarith [hu.2], by linarith [hu.1]⟩
        ⟨by linarith [hv.2], by linarith [hv.1]⟩ huv
    linarith
  have hτ1 : τ 1 = σ 0 := by rw [hτdef]; norm_num
  have hτC : ∀ t ∈ Set.Ico (0:ℝ) 1, τ t ∈ C := by
    intro t ht
    have h1 : (1:ℝ) - t ∈ Set.Ioc (0:ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have h2 : τ t = σ (1 - t) := by rw [hτdef]
    rw [h2]
    exact hσC ⟨1 - t, h1, rfl⟩
  -- the peeling step: from `s` down to `c < s`
  have step : ∀ (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) {c s : ℝ},
      c ∈ Set.Icc (0:ℝ) 1 → s ∈ Set.Icc (0:ℝ) 1 → c < s →
      (∀ t ∈ Set.Icc c s, τ t ∈ e.source) →
      IsPreconnected (C \ τ '' Set.Icc s 1) → IsPreconnected (C \ τ '' Set.Icc c 1) := by
    intro e c s hc hs hcs hesrc hT
    have hTo : IsOpen (C \ τ '' Set.Icc s 1) :=
      hC.sdiff (isCompact_Icc.image hτc).isClosed
    have hpiece : τ '' Set.Ico c s ⊆ C \ τ '' Set.Icc s 1 := by
      rintro z ⟨t, ht, rfl⟩
      refine ⟨hτC t ⟨le_trans hc.1 ht.1, lt_of_lt_of_le ht.2 hs.2⟩, ?_⟩
      rintro ⟨u, hu, hue⟩
      have hut : u = t :=
        hτinj ⟨le_trans hs.1 hu.1, hu.2⟩
          ⟨le_trans hc.1 ht.1, le_of_lt (lt_of_lt_of_le ht.2 hs.2)⟩ hue
      rw [hut] at hu
      exact absurd hu.1 (not_le.mpr ht.2)
    have hsT : τ s ∉ C \ τ '' Set.Icc s 1 :=
      fun h => h.2 ⟨s, ⟨le_rfl, hs.2⟩, rfl⟩
    obtain ⟨U, hUo, hCcU, hUT, hUp⟩ :=
      room_of_arc_piece hTo hτc hτinj hc hs hcs hesrc hpiece hsT
    have hkey : (C \ τ '' Set.Icc s 1) \ (τ '' Set.Ico c s) = C \ τ '' Set.Icc c 1 := by
      have hunion : Set.Icc s 1 ∪ Set.Ico c s = Set.Icc c 1 := by
        ext t; simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ico]
        constructor
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · exact ⟨le_trans hcs.le h1, h2⟩
          · exact ⟨h1, le_trans h2.le hs.2⟩
        · rintro ⟨h1, h2⟩
          rcases lt_or_ge t s with h | h
          · exact Or.inr ⟨h1, h⟩
          · exact Or.inl ⟨h, h2⟩
      rw [Set.sdiff_sdiff, ← Set.image_union, hunion]
    have hopen : IsOpen ((C \ τ '' Set.Icc s 1) \ (τ '' Set.Ico c s)) := by
      rw [hkey]; exact hC.sdiff (isCompact_Icc.image hτc).isClosed
    have hres :=
      Work.Whitney.PathTools.isPreconnected_sdiff_of_room_of_open hT hopen hUo hCcU hUT hUp
    rwa [hkey] at hres
  -- the descending induction on the level
  set S : Set ℝ := {c | c ∈ Set.Icc (0:ℝ) 1 ∧ IsPreconnected (C \ τ '' Set.Icc c 1)}
    with hSdef
  have h1S : (1:ℝ) ∈ S := by
    have h1 : C \ τ '' Set.Icc (1:ℝ) 1 = C := by
      have h2 : τ '' Set.Icc (1:ℝ) 1 = {τ 1} := by
        rw [Set.Icc_self, Set.image_singleton]
      rw [h2, hτ1]
      exact Set.sdiff_singleton_eq_self hσ0
    exact ⟨by norm_num, h1.symm ▸ hCpre⟩
  have hSne : S.Nonempty := ⟨1, h1S⟩
  have hSbdd : BddBelow S := ⟨0, fun s hs => hs.1.1⟩
  set sstar : ℝ := sInf S with hstardef
  have hstar_le : sstar ≤ 1 := by rw [hstardef]; exact csInf_le hSbdd h1S
  have hstar_ge : 0 ≤ sstar := by rw [hstardef]; exact le_csInf hSne (fun s hs => hs.1.1)
  have hstar01 : sstar ∈ Set.Icc (0:ℝ) 1 := ⟨hstar_ge, hstar_le⟩
  have hstar_mem : sstar ∈ S := by
    rcases lt_or_eq_of_le hstar_le with hlt | heq
    · set e := chartAt (EuclideanSpace ℝ (Fin 2)) (τ sstar) with hedef
      have hγs : τ sstar ∈ e.source := mem_chart_source _ _
      have hcont : τ ⁻¹' e.source ∈ 𝓝 sstar :=
        hτc.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds hγs)
      obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hcont
      obtain ⟨s, hsS, hsl⟩ :=
        exists_lt_of_csInf_lt (b := sstar + δ / 2) hSne (by rw [← hstardef]; linarith [hδ])
      have hsδ : ∀ t ∈ Set.Icc sstar s, τ t ∈ e.source := by
        intro t ht
        apply hδsub
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        exact ⟨by linarith [ht.1, hδ], by linarith [ht.2, hsl, hδ]⟩
      have hsge : sstar ≤ s := by rw [hstardef]; exact csInf_le hSbdd hsS
      rcases lt_or_eq_of_le hsge with hgt | heq'
      · exact ⟨hstar01, step e hstar01 hsS.1 hgt (fun t ht => hsδ t ht) hsS.2⟩
      · exact heq' ▸ hsS
    · exact heq ▸ h1S
  have h0 : (0:ℝ) ∈ S := by
    by_cases hpos : 0 < sstar
    · exfalso
      set e := chartAt (EuclideanSpace ℝ (Fin 2)) (τ sstar) with hedef
      have hγs : τ sstar ∈ e.source := mem_chart_source _ _
      have hcont : τ ⁻¹' e.source ∈ 𝓝 sstar :=
        hτc.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds hγs)
      obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hcont
      set c : ℝ := max 0 (sstar - δ / 2) with hcdef
      have hclt : c < sstar := by
        rw [hcdef]
        exact max_lt hpos (by linarith)
      have hc01 : c ∈ Set.Icc (0:ℝ) 1 := ⟨le_max_left _ _, le_trans hclt.le hstar_le⟩
      have hcgt : sstar - δ < c := by
        rw [hcdef]
        rcases le_total (sstar - δ / 2) 0 with h | h
        · rw [max_eq_left h]; linarith
        · rw [max_eq_right h]; linarith
      have hcsrc : ∀ t ∈ Set.Icc c sstar, τ t ∈ e.source := by
        intro t ht
        apply hδsub
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        exact ⟨by linarith [hcgt, ht.1], by linarith [ht.2, hδ]⟩
      have hcpre' : IsPreconnected (C \ τ '' Set.Icc c 1) :=
        step e hc01 hstar01 hclt hcsrc hstar_mem.2
      have hle : sstar ≤ c := by rw [hstardef]; exact csInf_le hSbdd ⟨hc01, hcpre'⟩
      linarith
    · have h0' : sstar = 0 := le_antisymm (le_of_not_gt hpos) hstar_ge
      exact h0' ▸ hstar_mem
  have hfinal : IsPreconnected (C \ τ '' Set.Icc (0:ℝ) 1) := h0.2
  have hτIcc : τ '' Set.Icc (0:ℝ) 1 = σ '' Set.Icc (0:ℝ) 1 := by
    ext x; constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
      rw [hτdef]
    · rintro ⟨t, ht, rfl⟩
      refine ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
      show τ (1 - t) = σ t
      rw [hτdef]
      congr 1
      ring_nf
  have hgoal_eq : C \ τ '' Set.Icc (0:ℝ) 1 = C \ σ '' Set.Ioc (0:ℝ) 1 := by
    rw [hτIcc]
    ext x; constructor
    · rintro ⟨hxC, hxI⟩
      refine ⟨hxC, ?_⟩
      rintro ⟨t, ht, htx⟩
      exact hxI ⟨t, ⟨ht.1.le, ht.2⟩, htx⟩
    · rintro ⟨hxC, hxI⟩
      refine ⟨hxC, fun h => ?_⟩
      obtain ⟨t, ht, htx⟩ := h
      rcases eq_or_lt_of_le ht.1 with h0 | h0
      · refine hσ0 ?_
        rw [h0, htx]
        exact hxC
      · exact hxI ⟨t, ⟨h0, ht.2⟩, htx⟩
  exact hgoal_eq ▸ hfinal

/-- **The `n ≥ 3` case of `spike_removal`**, via the local-room criterion. -/
theorem spike_removal_ge3 {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {C : Set M} (hC : IsOpen C) (hCpre : IsPreconnected C)
    {σ : ℝ → M} (hσc : Continuous σ) (hσinj : Set.InjOn σ (Set.Icc (0:ℝ) 1))
    (hσC : σ '' Set.Ioc (0:ℝ) 1 ⊆ C) (hσ0 : σ 0 ∉ C) :
    IsPreconnected (C \ σ '' Set.Ioc (0:ℝ) 1) := by
  have hY : IsClosed (σ '' Set.Icc (0:ℝ) 1) := (isCompact_Icc.image hσc).isClosed
  have hloc : ∀ y ∈ σ '' Set.Icc (0:ℝ) 1, ∀ N ∈ 𝓝 y,
      ∃ O : Set M, IsOpen O ∧ y ∈ O ∧ O ⊆ N ∧ (O \ σ '' Set.Icc (0:ℝ) 1).Nonempty ∧
        IsPreconnected (O \ σ '' Set.Icc (0:ℝ) 1) := by
    rintro y ⟨s, hs, rfl⟩ N hN
    obtain ⟨O, hOo, hOs, hON, hOpc⟩ :=
      Work.Whitney.PathTools.room_at_arc_manifold (n := n) hn hσc hσinj hs hN
    exact ⟨O, hOo, hOs, hON, hOpc.nonempty, hOpc.isConnected.isPreconnected⟩
  have hmain : IsPreconnected (C \ σ '' Set.Icc (0:ℝ) 1) :=
    Work.Whitney.PathTools.isPreconnected_sdiff_of_local_room hCpre hC hY hloc
  have heq : C \ σ '' Set.Icc (0:ℝ) 1 = C \ σ '' Set.Ioc (0:ℝ) 1 := by
    ext x; constructor
    · rintro ⟨hxC, hxI⟩
      refine ⟨hxC, ?_⟩
      rintro ⟨t, ht, htx⟩
      exact hxI ⟨t, ⟨ht.1.le, ht.2⟩, htx⟩
    · rintro ⟨hxC, hxI⟩
      refine ⟨hxC, fun h => ?_⟩
      obtain ⟨t, ht, htx⟩ := h
      rcases eq_or_lt_of_le ht.1 with h0 | h0
      · refine hσ0 ?_
        rw [h0, htx]
        exact hxC
      · exact hxI ⟨t, ⟨h0, ht.2⟩, htx⟩
  rwa [heq] at hmain

/-- Removing a half-open arc "slit with a free end" from an open preconnected `C` of an
`n`-manifold (`n ≥ 2`) keeps it preconnected.  Here `σ 0 ∉ C` is the free end and
`σ '' Ioc 0 1 ⊆ C` the slit, whose other end is an interior point of `C`.  Since
`σ '' Icc 0 1 = {σ 0} ∪ σ '' Ioc 0 1` and `σ 0 ∉ C`, this is `IsPreconnected (C \ σ '' Icc 0 1)`. -/
theorem spike_removal {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {C : Set M} (hC : IsOpen C) (hCpre : IsPreconnected C)
    {σ : ℝ → M} (hσc : Continuous σ) (hσinj : Set.InjOn σ (Set.Icc (0:ℝ) 1))
    (hσC : σ '' Set.Ioc (0:ℝ) 1 ⊆ C) (hσ0 : σ 0 ∉ C) :
    IsPreconnected (C \ σ '' Set.Ioc (0:ℝ) 1) := by
  rcases eq_or_lt_of_le hn with h2 | h3
  · subst h2
    exact spike_removal_two hC hCpre hσc hσinj hσC hσ0
  · exact spike_removal_ge3 (n := n) (by omega) hC hCpre hσc hσinj hσC hσ0

end Work.Noncompact.CompressionTube
