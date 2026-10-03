import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.Basins.basin_forward
import Submission.Work.Horn.Basins.existsUnique_petal_index
import Submission.Work.Horn.Basins.enters_petal_of_mem_component
import Submission.Work.Horn.Basins.isCompact_inter_preimage_of_isCompact

/-!
# Immediate basins attached to a family of petals

Given a map `f` holomorphic on the open set `D`, with `f 0 = 0` and `0` **not** in the parabolic
basin `P = MandelDim.ParabolicBasin f D`, suppose we are given `q` disjoint forward-invariant
"petals" `V i ⊆ D`, each connected with `0 ∈ closure (V i)`, on which `f` is injective, which
together *capture* every orbit of the basin, and such that the set of petals entered by an orbit is
locally constant on the basin (`hVindex`).  Assume also that the basin is proper over itself
(`hprop`) — the compactness hypothesis of `IsImmediateBasin`.

Then the connected components of the basin that contain the petals are *distinct* immediate basins
`B i` with `V i ⊆ B i`.

Proof outline:

* `P` is open (directly from its definition), `P ⊆ D`, and every petal lies in `P` (use `hVreach`
  with `n = 1`).
* Each orbit of `P` enters exactly one petal (`hVcapture` + disjointness/invariance).
* `B i := connectedComponentIn P (v i)`, where `v i ∈ V i`; it is open (`IsOpen.connectedComponentIn`)
  and connected, lies in `P`, and is maximal among preconnected subsets of `P` meeting it.
* `B i` is closed inside `P`: a limit point `y ∈ P` of `B i` makes `B i ∪ {y}` preconnected, whence
  contained in the component `B i` (`IsPreconnected.subset_closure`).
* `f '' B i ⊆ B i` because `f '' B i` is preconnected (image of a preconnected set under a
  continuous map) inside `P` and contains `f (v i) ∈ V i ⊆ B i`.
* `f` is not constant on `B i` (a constant value `c` would satisfy `c = lim f^n (v i) = 0`, so
  `0 ∈ V i ⊆ P`, contradicting `0 ∉ P`), so the open mapping theorem makes `f '' B i` open; with
  `hprop` one shows that `f '' B i` is also closed in `B i`, whence `f '' B i = B i`.
* The disjointness of the `B i` follows from `hVindex`: the "entered petal" index is locally
  constant on `P` and hence constant on each preconnected `B i`, while `v i ∈ B i` enters the petal
  `V i`; distinct indices therefore force distinct components.
-/

namespace Work.Horn

noncomputable section

open MandelDim Filter Set Metric Topology
open scoped Topology

namespace ImmBasins

/-- The parabolic basin is open (immediate from the definition). -/
theorem parabolicBasin_isOpen {f : ℂ → ℂ} {D : Set ℂ} :
    IsOpen (MandelDim.ParabolicBasin f D) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  obtain ⟨U, hU, hiter, hconv⟩ := hz
  obtain ⟨V, hVU, hVopen, hzV⟩ := _root_.mem_nhds_iff.mp hU
  refine Filter.mem_of_superset (hVopen.mem_nhds hzV) ?_
  intro w hw
  exact ⟨U, Filter.mem_of_superset (hVopen.mem_nhds hw) hVU, hiter, hconv⟩

/-- The basin is contained in `D` (take the `n = 0` iterate of the defining neighbourhood). -/
theorem parabolicBasin_subset_D {f : ℂ → ℂ} {D : Set ℂ} :
    MandelDim.ParabolicBasin f D ⊆ D := by
  intro z hz
  obtain ⟨U, hU, hiter, -⟩ := hz
  simpa using hiter 0 (mem_of_mem_nhds hU)

/-- All iterates of a basin point stay in `D`. -/
theorem parabolicBasin_iterate_mem_D {f : ℂ → ℂ} {D : Set ℂ} {z : ℂ}
    (hz : z ∈ MandelDim.ParabolicBasin f D) (n : ℕ) : f^[n] z ∈ D := by
  obtain ⟨U, hU, hiter, -⟩ := hz
  exact hiter n (mem_of_mem_nhds hU)

/-- The iterates of a basin point converge to `0` (the pointwise form of the defining uniform
convergence). -/
theorem parabolicBasin_tendsto_zero {f : ℂ → ℂ} {D : Set ℂ} {z : ℂ}
    (hz : z ∈ MandelDim.ParabolicBasin f D) :
    Tendsto (fun n : ℕ => f^[n] z) atTop (𝓝 0) := by
  obtain ⟨U, hU, hiter, hunif⟩ := hz
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hunif ε hε)
  exact ⟨N, fun n hn => by
    have := hN n hn z (mem_of_mem_nhds hU)
    simpa [dist_comm] using this⟩

/-- Every petal is contained in the parabolic basin, by the "reach" hypothesis with `n = 1`. -/
theorem petal_subset_parabolicBasin {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {V : Fin q → Set ℂ}
    (hVsub : ∀ i, V i ⊆ D) (hVmap : ∀ i, ∀ z ∈ V i, f z ∈ V i)
    (hVreach : ∀ z ∈ D, (∃ n : ℕ, (∀ k < n, f^[k] z ∈ D) ∧ f^[n] z ∈ ⋃ i, V i) →
      z ∈ MandelDim.ParabolicBasin f D) :
    ∀ i, V i ⊆ MandelDim.ParabolicBasin f D := by
  intro i z hz
  refine hVreach z (hVsub i hz) ⟨1, ?_, ?_⟩
  · intro k hk
    rw [Nat.lt_one_iff.mp hk]
    exact hVsub i hz
  · simpa using Set.mem_iUnion.mpr ⟨i, hVmap i z hz⟩

/-- A connected component of `F` is closed inside `F`: a point of `F` in the closure of the
component can be adjoined to it, and the resulting set is still preconnected, hence lies in the
maximal preconnected subset of `F` containing the base point. -/
theorem connectedComponentIn_of_mem_closure {F : Set ℂ} {x y : ℂ} (hx : x ∈ F) (hy : y ∈ F)
    (hcl : y ∈ closure (connectedComponentIn F x)) : y ∈ connectedComponentIn F x := by
  have ht : IsPreconnected (connectedComponentIn F x ∪ {y}) := by
    refine IsPreconnected.subset_closure (s := connectedComponentIn F x)
      (t := connectedComponentIn F x ∪ {y}) isPreconnected_connectedComponentIn ?_ ?_
    · exact subset_union_left
    · intro z hz
      rcases hz with hz | hz
      · exact subset_closure hz
      · rw [Set.mem_singleton_iff.mp hz]; exact hcl
  have hxmem : x ∈ connectedComponentIn F x ∪ {y} := Or.inl (mem_connectedComponentIn hx)
  have hsub : connectedComponentIn F x ∪ {y} ⊆ F := by
    intro z hz
    rcases hz with hz | hz
    · exact connectedComponentIn_subset F x hz
    · rw [Set.mem_singleton_iff.mp hz]; exact hy
  exact IsPreconnected.subset_connectedComponentIn ht hxmem hsub (Or.inr rfl)

/-- **Compactness step.**  If `B ⊆ P` is closed inside the parabolic basin `P = ParabolicBasin f D`
and `f` is proper over `P` (so that `P ∩ f ⁻¹' K` is compact for compact `K ⊆ P`), then every point
of `B` that is a limit of points of `f '' B` already lies in `f '' B`.

Indeed, take a closed ball `L = closedBall z r ⊆ P` around such a point `z`, pull the approximating
points `f (w n) ∈ L` back: the `w n` lie in the compact `P ∩ f ⁻¹' L`, so a subsequence converges to
some `a ∈ P`; then `a ∈ closure B` and `z = f a`. -/
theorem mem_image_of_mem_closure {f : ℂ → ℂ} {D B : Set ℂ}
    (hD : IsOpen D) (hf : DifferentiableOn ℂ f D)
    (hprop : ∀ K : Set ℂ, K ⊆ MandelDim.ParabolicBasin f D → IsCompact K →
      IsCompact (MandelDim.ParabolicBasin f D ∩ f ⁻¹' K))
    (hBsub : B ⊆ MandelDim.ParabolicBasin f D)
    (hBcl : ∀ y ∈ MandelDim.ParabolicBasin f D, y ∈ closure B → y ∈ B)
    {z : ℂ} (hzB : z ∈ B) (hzcl : z ∈ closure (f '' B)) :
    z ∈ f '' B := by
  have hbasin_open : IsOpen (MandelDim.ParabolicBasin f D) := parabolicBasin_isOpen
  have hbasin_sub : MandelDim.ParabolicBasin f D ⊆ D := parabolicBasin_subset_D
  -- a closed ball around `z` contained in the (open) basin
  obtain ⟨r, hr, hrsub⟩ : ∃ r : ℝ, 0 < r ∧ closedBall z r ⊆ MandelDim.ParabolicBasin f D := by
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hbasin_open.mem_nhds (hBsub hzB))
    refine ⟨ε / 2, by linarith, fun y hy => hεsub ?_⟩
    have hy' : dist z y ≤ ε / 2 := by simpa [dist_comm] using hy
    have hlt : dist y z < ε := by rw [dist_comm]; linarith
    simpa [Metric.mem_ball] using hlt
  set L : Set ℂ := closedBall z r with hL
  have hLc : IsCompact L := isCompact_closedBall z r
  have hKc : IsCompact (MandelDim.ParabolicBasin f D ∩ f ⁻¹' L) := hprop L hrsub hLc
  -- approximating preimages, kept inside the compact set
  have hseq : ∀ n : ℕ, ∃ w ∈ B, dist (f w) z < min (1 / (n + 1 : ℝ)) r := by
    intro n
    obtain ⟨y, hy, hyd⟩ := Metric.mem_closure_iff.mp hzcl (min (1 / (n + 1 : ℝ)) r)
      (lt_min (by positivity) hr)
    obtain ⟨w, hwB, rfl⟩ := hy
    exact ⟨w, hwB, by rwa [dist_comm] at hyd⟩
  choose w hwB hwd using hseq
  have hwK : ∀ n : ℕ, w n ∈ MandelDim.ParabolicBasin f D ∩ f ⁻¹' L := by
    intro n
    refine ⟨hBsub (hwB n), ?_⟩
    rw [Set.mem_preimage, Metric.mem_closedBall]
    exact le_of_lt (lt_of_lt_of_le (hwd n) (min_le_right _ _))
  -- pass to a convergent subsequence
  obtain ⟨a, haK, φ, hφmono, hφlim⟩ := hKc.tendsto_subseq (fun n => hwK n)
  have haB : a ∈ B := by
    refine hBcl a haK.1 (mem_closure_of_tendsto hφlim ?_)
    exact Eventually.of_forall (fun n => hwB (φ n))
  have hcont : ContinuousAt f a := hf.continuousOn.continuousAt (hD.mem_nhds (hbasin_sub haK.1))
  have hlim1 : Tendsto (fun n : ℕ => f (w (φ n))) atTop (𝓝 (f a)) := hcont.tendsto.comp hφlim
  have hlim2 : Tendsto (fun n : ℕ => f (w (φ n))) atTop (𝓝 z) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    refine ⟨N, fun n hn => ?_⟩
    have hid : n ≤ φ n := hφmono.id_le n
    have h1 : (1 : ℝ) / (φ n + 1) ≤ 1 / (n + 1 : ℝ) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.succ_le_succ hid
    have h2 : dist (f (w (φ n))) z ≤ 1 / (φ n + 1 : ℝ) :=
      le_of_lt (lt_of_lt_of_le (hwd (φ n)) (min_le_left _ _))
    have h3 : (1 : ℝ) / (n + 1) ≤ 1 / (N + 1 : ℝ) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.succ_le_succ hn
    calc dist (f (w (φ n))) z ≤ 1 / (φ n + 1 : ℝ) := h2
      _ ≤ 1 / (n + 1 : ℝ) := h1
      _ ≤ 1 / (N + 1 : ℝ) := h3
      _ < ε := hN
  exact ⟨a, haB, tendsto_nhds_unique hlim1 hlim2⟩

/-- **Invariance of a component.**  Let `B` be open, preconnected and closed inside the parabolic
basin `P = ParabolicBasin f D`, with `f` proper over `P` and `f '' B ⊆ B`.  If moreover `f` is not
constant on `B`, then `f '' B = B`.

`f '' B ⊆ B` holds by hypothesis.  For the reverse inclusion, `f '' B` is open (open mapping
theorem, using the non-constancy on the preconnected open set `B`) and closed inside `B` by
`mem_image_of_mem_closure`; a nonempty subset of the preconnected set `B` that is both open and
closed in `B` is all of `B`. -/
theorem image_eq_self_of_isPreconnected {f : ℂ → ℂ} {D B : Set ℂ}
    (hD : IsOpen D) (hf : DifferentiableOn ℂ f D)
    (hprop : ∀ K : Set ℂ, K ⊆ MandelDim.ParabolicBasin f D → IsCompact K →
      IsCompact (MandelDim.ParabolicBasin f D ∩ f ⁻¹' K))
    (hBne : Set.Nonempty B) (hBopen : IsOpen B) (hBpre : IsPreconnected B)
    (hBsub : B ⊆ MandelDim.ParabolicBasin f D)
    (hBcl : ∀ y ∈ MandelDim.ParabolicBasin f D, y ∈ closure B → y ∈ B)
    (hmap : Set.MapsTo f B B) (hnconst : ¬ ∃ c : ℂ, ∀ z ∈ B, f z = c) :
    Set.image f B = B := by
  have hmapsTo : f '' B ⊆ B := Set.mapsTo_iff_image_subset.mp hmap
  have hBsubD : B ⊆ D := fun z hz => parabolicBasin_subset_D (hBsub hz)
  have hopen : IsOpen (f '' B) := by
    rcases (hf.mono hBsubD).analyticOnNhd hBopen |>.is_constant_or_isOpen hBpre with hc | ho
    · exact absurd hc hnconst
    · exact ho B subset_rfl hBopen
  have hle : B ⊆ f '' B := by
    refine IsPreconnected.subset_left_of_subset_union hopen isClosed_closure.isOpen_compl
      (disjoint_compl_right.mono_left subset_closure) ?_ ?_ hBpre
    · intro z hz
      by_cases hzc : z ∈ closure (f '' B)
      · exact Or.inl (mem_image_of_mem_closure hD hf hprop hBsub hBcl hz hzc)
      · exact Or.inr hzc
    · obtain ⟨z, hz⟩ := hBne
      exact ⟨f z, hmapsTo ⟨z, hz, rfl⟩, ⟨z, hz, rfl⟩⟩
  exact Set.Subset.antisymm hmapsTo hle

end ImmBasins

theorem immediate_basins_of_petals {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {V : Fin q → Set ℂ}
    (hq : 1 ≤ q) (hD : IsOpen D) (hf : DifferentiableOn ℂ f D) (hfix : f 0 = 0)
    (hnc : ∃ z ∈ D, deriv f z ≠ 0)
    (h0out : (0 : ℂ) ∉ MandelDim.ParabolicBasin f D)
    (hsurj : ∀ z ∈ MandelDim.ParabolicBasin f D, ∃ w ∈ D, f w = z)
    (hprop : ∀ L : Set ℂ, L ⊆ MandelDim.ParabolicBasin f D → IsCompact L →
      IsCompact (MandelDim.ParabolicBasin f D ∩ f ⁻¹' L))
    (hVopen : ∀ i, IsOpen (V i)) (hVconn : ∀ i, IsConnected (V i))
    (hVsub : ∀ i, V i ⊆ D) (hVmap : ∀ i, ∀ z ∈ V i, f z ∈ V i)
    (hVdisj : ∀ i j : Fin q, i ≠ j → Disjoint (V i) (V j))
    (hVcl : ∀ i, (0 : ℂ) ∈ closure (V i))
    (hVinj : ∀ i, Set.InjOn f (V i))
    (hVcapture : ∀ z ∈ MandelDim.ParabolicBasin f D, ∃ n : ℕ, f^[n] z ∈ ⋃ i, V i)
    (hVreach : ∀ z ∈ D, (∃ n : ℕ, (∀ k < n, f^[k] z ∈ D) ∧ f^[n] z ∈ ⋃ i, V i) →
      z ∈ MandelDim.ParabolicBasin f D)
    (hVindex : ∀ z ∈ MandelDim.ParabolicBasin f D, ∃ U ∈ nhds z, ∀ w ∈ U, ∀ i : Fin q,
      ((∃ n : ℕ, f^[n] z ∈ V i) ↔ (∃ n : ℕ, f^[n] w ∈ V i))) :
    ∃ B : Fin q → Set ℂ,
      (∀ i, MandelDim.IsImmediateBasin f D (B i)) ∧
      (∀ i, V i ⊆ B i) ∧ (∀ i, (B i).Nonempty) ∧
      (∀ i j : Fin q, i ≠ j → Disjoint (B i) (B j)) := by
  have hbasin_open : IsOpen (MandelDim.ParabolicBasin f D) := ImmBasins.parabolicBasin_isOpen
  have hbasin_sub : MandelDim.ParabolicBasin f D ⊆ D := ImmBasins.parabolicBasin_subset_D
  have hpetal : ∀ i, V i ⊆ MandelDim.ParabolicBasin f D :=
    ImmBasins.petal_subset_parabolicBasin hVsub hVmap hVreach
  have hfwd : ∀ z ∈ MandelDim.ParabolicBasin f D, f z ∈ MandelDim.ParabolicBasin f D :=
    Basins.basin_forward hVmap hVcapture hVreach
  choose v hv using fun i : Fin q => (hVconn i).nonempty
  have hvbasin : ∀ i, v i ∈ MandelDim.ParabolicBasin f D := fun i => hpetal i (hv i)
  have hvB : ∀ i, v i ∈ connectedComponentIn (MandelDim.ParabolicBasin f D) (v i) :=
    fun i => mem_connectedComponentIn (hvbasin i)
  have hpetalB : ∀ i, V i ⊆ connectedComponentIn (MandelDim.ParabolicBasin f D) (v i) := by
    intro i
    exact IsPreconnected.subset_connectedComponentIn (s := V i) (x := v i)
      (F := MandelDim.ParabolicBasin f D) (hVconn i).isPreconnected (hv i) (hpetal i)
  refine ⟨fun i => connectedComponentIn (MandelDim.ParabolicBasin f D) (v i), ?_, ?_, ?_, ?_⟩
  · intro i
    have hBsub : connectedComponentIn (MandelDim.ParabolicBasin f D) (v i) ⊆
        MandelDim.ParabolicBasin f D := connectedComponentIn_subset _ _
    have hBcl : ∀ y ∈ MandelDim.ParabolicBasin f D,
        y ∈ closure (connectedComponentIn (MandelDim.ParabolicBasin f D) (v i)) →
        y ∈ connectedComponentIn (MandelDim.ParabolicBasin f D) (v i) :=
      fun y hy hcl =>
        ImmBasins.connectedComponentIn_of_mem_closure (x := v i) (hvbasin i) hy hcl
    have hBopen : IsOpen (connectedComponentIn (MandelDim.ParabolicBasin f D) (v i)) :=
      hbasin_open.connectedComponentIn
    have hpre : IsPreconnected
        (connectedComponentIn (MandelDim.ParabolicBasin f D) (v i)) :=
      isPreconnected_connectedComponentIn
    have himgsub : f '' connectedComponentIn (MandelDim.ParabolicBasin f D) (v i) ⊆
        MandelDim.ParabolicBasin f D := by
      rintro y ⟨z, hz, rfl⟩
      exact hfwd z (hBsub hz)
    have himg1 : f '' connectedComponentIn (MandelDim.ParabolicBasin f D) (v i) ⊆
        connectedComponentIn (MandelDim.ParabolicBasin f D) (f (v i)) := by
      refine IsPreconnected.subset_connectedComponentIn (s := f '' connectedComponentIn
          (MandelDim.ParabolicBasin f D) (v i)) (x := f (v i))
        (F := MandelDim.ParabolicBasin f D) ?_ ?_ himgsub
      · exact hpre.image f ((hf.mono (hBsub.trans hbasin_sub)).continuousOn)
      · exact ⟨v i, hvB i, rfl⟩
    have himg : f '' connectedComponentIn (MandelDim.ParabolicBasin f D) (v i) ⊆
        connectedComponentIn (MandelDim.ParabolicBasin f D) (v i) := by
      have heq : connectedComponentIn (MandelDim.ParabolicBasin f D) (f (v i)) =
          connectedComponentIn (MandelDim.ParabolicBasin f D) (v i) :=
        (connectedComponentIn_eq (hpetalB i (hVmap i (v i) (hv i)))).symm
      rwa [heq] at himg1
    have hnonconst : ¬ ∃ c : ℂ,
        ∀ z ∈ connectedComponentIn (MandelDim.ParabolicBasin f D) (v i), f z = c := by
      rintro ⟨c, hc⟩
      have hvc : f (v i) ∈ connectedComponentIn (MandelDim.ParabolicBasin f D) (v i) :=
        himg ⟨v i, hvB i, rfl⟩
      have hcB : c ∈ connectedComponentIn (MandelDim.ParabolicBasin f D) (v i) := by
        rw [← hc (v i) (hvB i)]; exact hvc
      have hiter : ∀ n : ℕ, f^[n + 1] (v i) = c := by
        intro n
        induction n with
        | zero => simpa using hc (v i) (hvB i)
        | succ k ih =>
            rw [Function.iterate_succ_apply', ih]
            exact hc c hcB
      have hlim : Tendsto (fun n : ℕ => f^[n] (v i)) atTop (𝓝 0) :=
        ImmBasins.parabolicBasin_tendsto_zero (hvbasin i)
      have hlim1 : Tendsto (fun n : ℕ => f^[n + 1] (v i)) atTop (𝓝 0) :=
        hlim.comp (tendsto_add_atTop_nat 1)
      have hlimc : Tendsto (fun n : ℕ => f^[n + 1] (v i)) atTop (𝓝 c) :=
        tendsto_const_nhds.congr' (Filter.Eventually.of_forall (fun n => (hiter n).symm))
      have hc0 : c = 0 := tendsto_nhds_unique hlimc hlim1
      exact h0out (by rw [← hc0]; exact hBsub hcB)
    have himg_eq : f '' connectedComponentIn (MandelDim.ParabolicBasin f D) (v i) =
        connectedComponentIn (MandelDim.ParabolicBasin f D) (v i) :=
      ImmBasins.image_eq_self_of_isPreconnected hD hf hprop ⟨v i, hvB i⟩ hBopen hpre hBsub hBcl
        (Set.mapsTo_iff_image_subset.mpr himg) hnonconst
    refine ⟨hBopen, isConnected_connectedComponentIn_iff.mpr (hvbasin i), hBsub, ?_, ?_, ?_, ?_⟩
    · intro C hCpre hCsub hCne
      obtain ⟨y, hyB, hyC⟩ := hCne
      have hsub := IsPreconnected.subset_connectedComponentIn (s := C) (x := y)
        (F := MandelDim.ParabolicBasin f D) hCpre hyC hCsub
      rwa [← connectedComponentIn_eq hyB] at hsub
    · exact Set.mapsTo_iff_image_subset.mpr (le_of_eq himg_eq)
    · rw [himg_eq]
    · intro L hLB hLc
      exact Basins.isCompact_inter_preimage_of_isCompact hprop hBsub hBcl hLB hLc
  · intro i
    exact hpetalB i
  · intro i
    exact ⟨v i, hvB i⟩
  · intro i j hij
    refine Set.disjoint_left.mpr fun x hx hx' => ?_
    have hxi : ∃ n : ℕ, f^[n] x ∈ V i :=
      Basins.enters_petal_of_mem_component hVmap hVdisj hVcapture hVindex (hv i) (hvbasin i) x hx
    have hxj : ∃ n : ℕ, f^[n] x ∈ V j :=
      Basins.enters_petal_of_mem_component hVmap hVdisj hVcapture hVindex (hv j) (hvbasin j) x hx'
    have huniq := Basins.existsUnique_petal_index hVmap hVdisj hVcapture x
      (connectedComponentIn_subset _ _ hx)
    exact hij (huniq.unique hxi hxj)

end

end Work.Horn
