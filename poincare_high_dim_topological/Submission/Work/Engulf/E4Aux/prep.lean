import Mathlib
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.Auxi.exists_subdiv_affine
import Submission.Work.Engulf.Auxi.SimplexCover
import Submission.Work.Engulf.Auxi.locally_affine_of_convex
import Submission.Work.Cells.Connell.cubeChart_isOpen_image_openCube
import Submission.Work.Geo.Radial.ChartImage
import Submission.Work.Geo.Radial.continuousOn_chartInv
import Submission.Work.Engulf.E4Aux.tietze
import Submission.Work.Engulf.E4Aux.continuousOn_ite_of_closure
import Submission.Work.Engulf.E4Aux.affine_on_face_of_smoothChart

namespace Work.Engulf.E4Aux

open Set Metric Filter
open scoped Topology

universe u

/-! ## Auxiliary lemmas used by `E4a` -/

/-- Coordinatewise clamp of `ℝⁿ` into the cube `closedCube r`. -/
noncomputable def clampCube {n : ℕ} (r : ℝ) (y : PL.E n) : PL.E n :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => max (-r) (min r (y i)))

theorem clampCube_apply {n : ℕ} (r : ℝ) (y : PL.E n) (i : Fin n) :
    clampCube r y i = max (-r) (min r (y i)) := rfl

theorem continuous_clampCube {n : ℕ} (r : ℝ) : Continuous (clampCube (n := n) r) := by
  unfold clampCube
  refine (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous.comp (continuous_pi fun i => ?_)
  exact continuous_const.max (continuous_const.min (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i))

theorem clampCube_mem {n : ℕ} {r : ℝ} (hr : 0 ≤ r) (y : PL.E n) :
    clampCube r y ∈ PL.closedCube r := by
  intro i
  rw [clampCube_apply, abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem clampCube_eq_self {n : ℕ} {r : ℝ} (hr : 0 ≤ r) {y : PL.E n}
    (hy : y ∈ PL.closedCube r) : clampCube r y = y := by
  ext i
  rw [clampCube_apply]
  have h := hy i
  rw [abs_le] at h
  rw [min_eq_right h.2, max_eq_right h.1]

/-- A compact set contained in the interior of a closed set has an open neighbourhood whose
closure is contained in that closed set. -/
theorem exists_isOpen_closure_subset {N : ℕ} {K C : Set (PL.E N)} (hK : IsCompact K)
    (hC : IsClosed C) (hKC : K ⊆ interior C) :
    ∃ W : Set (PL.E N), IsOpen W ∧ K ⊆ W ∧ closure W ⊆ C := by
  obtain ⟨δ, hδpos, hδ⟩ := hK.exists_thickening_subset_open isOpen_interior hKC
  refine ⟨Metric.thickening δ K, Metric.isOpen_thickening, fun x hx => ?_, ?_⟩
  · rw [Metric.mem_thickening_iff]
    exact ⟨x, hx, by simpa using hδpos⟩
  · exact (closure_mono hδ).trans hC.closure_interior_subset


/-- **`E4a` (Newman Lemma 7 Case 1, preparation).**  From an `L7c` instance (`L7Hyp` + a smoothing chart `ψ` in which the join simplex `Δ = τ₀ ∪ τ₁` lives) produce, for every `ε > 0`: a subdivision level `r`, the shelling `ord` of `Δ` in `Γ₁ := sdIter r Γ` from the floor `floorOf τ₀ τ₁ = ⋃_{w ∈ τ₁} simp (Δ.erase w)` (contract G4, with the explicit attaching facet given by `SubdivTools.shell`), and a map `g₁ : E N → M`, continuous on `Γ.space`, with `g₁ = f` on `L`, `dist (g₁ x) (f x) < ε` on `Γ.space`, `X ∪ g₁ '' K ⊆ V`, and `g₁` `ψ`-affine (with chart coordinates in the open unit cube) on every shelled simplex `simp ord[i]`.

Construction (uses only the `Tools` bundle, no extra hypotheses): let `L₀ := ⋃{s ∈ Γ.faces : simp s ⊆ L ∧ f '' simp s ⊆ ψ '' openCube (3/4)}` (the `3/4`-safe frozen faces; `IsSubSp Γ L₀`), let `f_c : E N → E n` be a Tietze extension to `Γ.space` of `ψ⁻¹ ∘ f` on `C := {x ∈ Γ.space : f x ∈ ψ '' closedCube (3/4)}` agreeing with `ψ⁻¹ ∘ f` on `C`, and apply `PlApproxFrozenForm` with `K := Γ`, `L := L₀`, `α = 11/16`, `β = 23/32`: its affinity hypothesis holds because a face `simp s ⊆ L₀` is covered by `3/4`-safe `L`-faces, so `f` is locally `ψ`-affine at every point of it and `locally_affine_of_convex` glues --- obtaining `r` and `g`.  Then take a continuous `χ : Γ.space → [0,1]` (Urysohn) with `χ = 1` on `simp Δ` and `χ = 0` on the closed set `(L \ L₀) ∪ (Γ.space \ U)`, where `U` is an open neighbourhood of `simp Δ` with `f '' U ⊆ ψ '' openCube (1/2)`; put `g₁ := ψ((1-χ) • f_c + χ • g)` (chart-local convex combination; `ψ.toFun` is total on `E n`, values stay in `openCube 1` on `supp χ`).  Then `g₁ = f` on `L` (either `χ = 0`, or `x ∈ L₀`, `g x = f_c x`, so `ψ(g x) = f x` since `f_c x = ψ⁻¹(f x)` on `L₀`), `g₁ = ψ ∘ g` on `simp Δ` hence affine on each `ord[i]` (they meet the `α`-cube because `f '' simp Δ ⊆ ψ '' openCube ½`), the distance bound comes from uniform continuity of `ψ` on a small neighbourhood of `f_c(supp χ)`, and `X ∪ g₁ '' K ⊆ V` from `X ∪ f '' K ⊆ V` (`K` compact, `f '' K` compact in the open `V`) plus a small tolerance. -/
theorem prep {n p q N : ℕ} {M : Type u} [MetricSpace M]
    {V X : Set M} {Γ : PL.Cx N} {K L : Set (PL.E N)} {f : PL.E N → M}
    {τ₀ τ₁ : Finset (PL.E N)}
    (T : Work.Engulf.ToolsAll.{u} n) (ψ : PL.CubeChart n M)
    (hAmb : Work.Engulf.Amb n p M V)
    (hL7 : Work.Engulf.L7Hyp n p q V X Γ K L f τ₀ τ₁)
    (hψ : Work.Engulf.SmoothChart p X Γ L f ψ)
    (hchart : f '' PL.simp (τ₀ ∪ τ₁) ⊆ ψ.toFun '' PL.openCube (1 / 2 : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (r : ℕ) (ord : List (Finset (PL.E N))) (g₁ : PL.E N → M),
      ord.Nodup ∧
      (∀ τ ∈ ord, τ ∈ ((T N).subdiv.sdIter r Γ hL7.cfg.fin).faces ∧
        τ.card = (τ₀ ∪ τ₁).card ∧ PL.simp τ ⊆ PL.simp (τ₀ ∪ τ₁)) ∧
      (⋃ τ ∈ ord, PL.simp τ) = PL.simp (τ₀ ∪ τ₁) ∧
      (∀ i (hi : i < ord.length), ∃ τ₁' : Finset (PL.E N), τ₁'.Nonempty ∧ τ₁' ⊂ ord[i] ∧
        PL.simp ord[i] ∩ ((⋃ w ∈ τ₁, PL.simp ((τ₀ ∪ τ₁).erase w)) ∪
          ⋃ j ∈ Finset.range i, ⋃ (hj : j < ord.length), PL.simp ord[j]) =
          ⋃ w ∈ τ₁', PL.simp ((ord[i]).erase w)) ∧
      ContinuousOn g₁ Γ.space ∧ Set.EqOn g₁ f L ∧
      (∀ x ∈ Γ.space, dist (g₁ x) (f x) < ε) ∧
      X ∪ g₁ '' K ⊆ V ∧
      (∀ i (hi : i < ord.length), ∃ A : PL.E N →ᵃ[ℝ] PL.E n,
        (∀ x ∈ PL.simp ord[i], A x ∈ PL.openCube 1) ∧
        (∀ x ∈ PL.simp ord[i], g₁ x = ψ.toFun (A x))) := by
  classical
  have hΓfin : Γ.faces.Finite := hL7.cfg.fin
  have hΔmem : τ₀ ∪ τ₁ ∈ Γ.faces := hL7.mem
  have hcont : ContinuousOn f Γ.space := hL7.cfg.cont
  have hsubL : IsSubSp Γ L := hL7.cfg.subL
  have hspC : IsClosed (Γ.space : Set (PL.E N)) := isClosed_space hΓfin
  have hΔsp : PL.simp (τ₀ ∪ τ₁) ⊆ Γ.space :=
    Geometry.SimplicialComplex.convexHull_subset_space hΔmem
  have hΔne : (PL.simp (τ₀ ∪ τ₁)).Nonempty :=
    simp_nonempty (Γ.nonempty_of_mem_faces hΔmem)
  -- ### cube inclusions used repeatedly
  have h1_2_3_4 : PL.openCube (n := n) (1 / 2 : ℝ) ⊆ PL.closedCube (n := n) (3 / 4 : ℝ) :=
    (openCube_mono (N := n) (by norm_num)).trans (openCube_subset_closedCube (N := n) (3 / 4))
  have h3_4_1 : PL.closedCube (n := n) (3 / 4 : ℝ) ⊆ PL.openCube (n := n) (1 : ℝ) :=
    closedCube_subset_openCube (N := n) (by norm_num)
  -- ### margins
  have hKc : IsCompact K := isCompact_of_isSubSp hΓfin hL7.subK
  have hfKc : IsCompact (f '' K) := hKc.image_of_continuousOn (hcont.mono hL7.subK.subset_space)
  obtain ⟨δV, hδVpos, hδVsub⟩ :=
    hfKc.exists_thickening_subset_open hAmb.Vo (fun y hy => hL7.engK (Or.inr hy))
  have hηpos : 0 < min ε δV := lt_min hε hδVpos
  have hucψ : UniformContinuousOn ψ.toFun (PL.closedCube (13/16 : ℝ)) :=
    (isCompact_closedCube (13/16)).uniformContinuousOn_of_continuous
      (ψ.cont.mono (closedCube_subset_openCube (by norm_num)))
  obtain ⟨θ, hθpos, hθ⟩ := Metric.uniformContinuousOn_iff.mp hucψ (min ε δV) hηpos
  obtain ⟨ε₁, hε₁pos, hε₁θ, hε₁16⟩ : ∃ e : ℝ, 0 < e ∧ e < θ ∧ e ≤ 1/16 :=
    ⟨min (θ/2) (1/16), lt_min (by linarith) (by norm_num),
      lt_of_le_of_lt (min_le_left _ _) (by linarith), min_le_right _ _⟩
  -- ### the `3/4`-safe frozen faces and their union `L₀`
  set T₀ : Finset (Finset (PL.E N)) := hΓfin.toFinset.filter (fun t =>
      PL.simp t ⊆ L ∧ f '' PL.simp t ⊆ ψ.toFun '' PL.openCube (3 / 4 : ℝ)) with hT₀def
  set L₀ : Set (PL.E N) := ⋃ t ∈ T₀, PL.simp t with hL₀def
  have hT₀mem : ∀ t : Finset (PL.E N), t ∈ T₀ ↔ t ∈ Γ.faces ∧ PL.simp t ⊆ L ∧
      f '' PL.simp t ⊆ ψ.toFun '' PL.openCube (3 / 4 : ℝ) := by
    intro t
    rw [hT₀def, Finset.mem_filter, Set.Finite.mem_toFinset hΓfin]
  have hT₀faces : ∀ t ∈ T₀, t ∈ Γ.faces := fun t ht => ((hT₀mem t).1 ht).1
  have hT₀L : ∀ t ∈ T₀, PL.simp t ⊆ L := fun t ht => ((hT₀mem t).1 ht).2.1
  have hT₀3 : ∀ t ∈ T₀, f '' PL.simp t ⊆ ψ.toFun '' PL.openCube (3 / 4 : ℝ) :=
    fun t ht => ((hT₀mem t).1 ht).2.2
  have hL₀sp : IsSubSp Γ L₀ := isSubSp_of_faces hT₀faces
  have hL₀cl : IsClosed L₀ := isClosed_of_isSubSp hΓfin hL₀sp
  have hLcl : IsClosed L := isClosed_of_isSubSp hΓfin hsubL
  -- ### the chart cubes `C`, `O`
  set C : Set (PL.E N) := Γ.space ∩ f ⁻¹' (ψ.toFun '' PL.closedCube (3 / 4 : ℝ)) with hCdef
  set O : Set (PL.E N) := Γ.space ∩ f ⁻¹' (ψ.toFun '' PL.openCube (3 / 4 : ℝ)) with hOdef
  have hAcl : IsClosed (ψ.toFun '' PL.closedCube (3 / 4 : ℝ)) :=
    (Work.Geo.Radial.isCompact_image_closedCube ψ (3/4) (by norm_num)).isClosed
  have hCcl : IsClosed C := by
    rw [hCdef]
    exact ContinuousOn.preimage_isClosed_of_isClosed hcont hspC hAcl
  have hOC : O ⊆ C := by
    intro x hx
    rw [hOdef] at hx
    rw [hCdef]
    exact ⟨hx.1, Set.image_mono (openCube_subset_closedCube (3/4)) hx.2⟩
  have hL₀C : L₀ ⊆ C := by
    intro x hx
    rw [hL₀def] at hx
    obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hx
    exact ⟨Geometry.SimplicialComplex.convexHull_subset_space (hT₀faces t ht) hxt,
      Set.image_mono (openCube_subset_closedCube (3/4)) (hT₀3 t ht ⟨x, hxt, rfl⟩)⟩
  -- ### `L ∩ simp Δ ⊆ L₀`
  have hLsimpΔL₀ : L ∩ PL.simp (τ₀ ∪ τ₁) ⊆ L₀ := by
    intro x hx
    obtain ⟨hxL, hxΔ⟩ := hx
    obtain ⟨s, hsΓ, hxs, hsL⟩ := hsubL.2 x hxL
    have hne : (s ∩ (τ₀ ∪ τ₁)).Nonempty := by
      have hmem : x ∈ PL.simp (s ∩ (τ₀ ∪ τ₁)) := by
        rw [← simp_inter hsΓ hΔmem]
        exact ⟨hxs, hxΔ⟩
      exact simp_nonempty_iff.mp ⟨x, hmem⟩
    have hface : s ∩ (τ₀ ∪ τ₁) ∈ Γ.faces := Γ.down_closed hΔmem Finset.inter_subset_right hne
    have hxmem : x ∈ PL.simp (s ∩ (τ₀ ∪ τ₁)) := by
      rw [← simp_inter hsΓ hΔmem]
      exact ⟨hxs, hxΔ⟩
    have hsub2 : PL.simp (s ∩ (τ₀ ∪ τ₁)) ⊆ L :=
      (simp_mono Finset.inter_subset_left).trans hsL
    have hsub3 : f '' PL.simp (s ∩ (τ₀ ∪ τ₁)) ⊆ ψ.toFun '' PL.openCube (3 / 4 : ℝ) :=
      (Set.image_mono (simp_mono Finset.inter_subset_right)).trans
        (hchart.trans (Set.image_mono (openCube_mono (by norm_num))))
    rw [hL₀def]
    exact Set.mem_iUnion₂.mpr ⟨s ∩ (τ₀ ∪ τ₁), (hT₀mem _).2 ⟨hface, hsub2, hsub3⟩, hxmem⟩
  -- ### the Tietze extension `f_c` of the chart coordinate, clamped into `closedCube (3/4)`
  have hchartInv_cont : ContinuousOn (fun x => Work.Geo.Radial.chartInv ψ (f x)) C := by
    refine (Work.Geo.Radial.continuousOn_chartInv ψ).comp (hcont.mono ?_) ?_
    · rw [hCdef]; exact Set.inter_subset_left
    · intro x hx
      rw [hCdef] at hx
      rw [Work.Geo.Radial.chartImage]
      exact Set.image_mono h3_4_1 hx.2
  obtain ⟨fc0, hfc0cont, hfc0eq⟩ := tietze hCcl hchartInv_cont
  set f_c : PL.E N → PL.E n := fun x => clampCube (3/4) (fc0 x) with hfcdef
  have hfc_cont : Continuous f_c := by
    simp only [hfcdef]
    exact (continuous_clampCube (n := n) (3/4)).comp hfc0cont
  have hfc_mem : ∀ x : PL.E N, f_c x ∈ PL.closedCube (3/4 : ℝ) := by
    intro x
    simp only [hfcdef]
    exact clampCube_mem (by norm_num) (fc0 x)
  have hfcI : ∀ {x : PL.E N}, x ∈ C →
      Work.Geo.Radial.chartInv ψ (f x) ∈ PL.closedCube (3/4 : ℝ) := by
    intro x hx
    have hx' := hx
    rw [hCdef] at hx'
    obtain ⟨y, hy, hyψ⟩ := hx'.2
    have hmem : f x ∈ Work.Geo.Radial.chartImage ψ := by
      rw [Work.Geo.Radial.chartImage]
      exact ⟨y, h3_4_1 hy, hyψ⟩
    have h1 : Work.Geo.Radial.chartInv ψ (f x) ∈ PL.openCube (n := n) 1 :=
      Work.Geo.Radial.chartInv_mem ψ hmem
    have h2 : y ∈ PL.openCube (n := n) 1 := h3_4_1 hy
    have h3 : y = Work.Geo.Radial.chartInv ψ (f x) :=
      Work.Geo.Radial.toFun_injOn_openCube ψ h2 h1
        (by rw [hyψ, Work.Geo.Radial.chartInv_toFun ψ hmem])
    rw [← h3]
    exact hy
  have hfc_C : Set.EqOn f_c (fun x => Work.Geo.Radial.chartInv ψ (f x)) C := by
    intro x hx
    simp only [hfcdef]
    rw [hfc0eq hx, clampCube_eq_self (by norm_num) (hfcI hx)]
  -- ### the affinity hypothesis of `PlApproxFrozenForm`
  have haff : ∀ s ∈ Γ.faces, PL.simp s ⊆ L₀ →
      (∃ x ∈ PL.simp s, f_c x ∈ PL.closedCube (23/32 : ℝ)) →
      ∃ A : PL.E N →ᵃ[ℝ] PL.E n, Set.EqOn f_c A (PL.simp s) := by
    intro s hs hsL₀ _
    obtain ⟨A, hAcl, hAeq⟩ :=
      affine_on_face_of_smoothChart ψ hψ T₀ hT₀faces hT₀L hT₀3 hs hsL₀
    refine ⟨A, fun x hxs => ?_⟩
    have hxC : x ∈ C := hL₀C (hsL₀ hxs)
    have hx' := hxC
    rw [hCdef] at hx'
    obtain ⟨y, hy, hyψ⟩ := hx'.2
    have hmem : f x ∈ Work.Geo.Radial.chartImage ψ := by
      rw [Work.Geo.Radial.chartImage]
      exact ⟨y, h3_4_1 hy, hyψ⟩
    have hAopen : A x ∈ PL.openCube (n := n) 1 :=
      closedCube_subset_openCube (by norm_num) (hAcl x hxs)
    have h1 : Work.Geo.Radial.chartInv ψ (f x) = A x :=
      Work.Geo.Radial.toFun_injOn_openCube ψ (Work.Geo.Radial.chartInv_mem ψ hmem) hAopen
        (by rw [Work.Geo.Radial.chartInv_toFun ψ hmem, hAeq hxs])
    simp only [hfcdef]
    rw [hfc0eq hxC, clampCube_eq_self (by norm_num) (hfcI hxC), h1]
  -- ### the frozen PL approximation
  obtain ⟨r, g, hg_cont, hg_near, hg_eqL₀, _hg_off, hg_aff⟩ :=
    (T N).plApprox Γ hΓfin L₀ hL₀sp f_c hfc_cont.continuousOn (11/16) (23/32)
      (by norm_num) (by norm_num) (by norm_num) haff ε₁ hε₁pos
  -- ### the shelling of `Δ` in `sdIter r Γ`
  have hτ₁ss : τ₁ ⊂ τ₀ ∪ τ₁ := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_right, ?_⟩
    intro hEq
    obtain ⟨u, hu⟩ := hL7.ne₀
    have hu' : u ∈ τ₁ := by rw [hEq]; exact Finset.mem_union_left τ₁ hu
    exact (Finset.disjoint_left.mp hL7.disj hu) hu'
  obtain ⟨ord, hord_nodup, hord_faces, hord_cover, hord_shell⟩ :=
    (T N).subdiv.shell r Γ hΓfin (τ₀ ∪ τ₁) τ₁ hΔmem hL7.ne₁ hτ₁ss
  -- ### an open neighbourhood `W` of `simp Δ` whose closure (meeting `Γ.space`) lies in `C`
  set F : Set (PL.E N) := closure (Γ.space \ C) with hFdef
  have hFcl : IsClosed F := by rw [hFdef]; exact isClosed_closure
  have hΔF : Disjoint (PL.simp (τ₀ ∪ τ₁)) F := by
    rw [Set.disjoint_left]
    intro x hxΔ hxF
    have hfx1 : f x ∈ ψ.toFun '' PL.openCube (3 / 4 : ℝ) :=
      Set.image_mono (openCube_mono (by norm_num)) (hchart ⟨x, hxΔ, rfl⟩)
    have hUo : IsOpen (ψ.toFun '' PL.openCube (3 / 4 : ℝ)) :=
      Work.Cells.Connell.cubeChart_isOpen_image_openCube ψ (by norm_num) (by norm_num)
    have hev : ∀ᶠ y in 𝓝[Γ.space] x, f y ∈ ψ.toFun '' PL.openCube (3 / 4 : ℝ) :=
      (hcont.continuousWithinAt (hΔsp hxΔ)).eventually (hUo.mem_nhds hfx1)
    simp only [Filter.eventually_iff, Metric.mem_nhdsWithin_iff] at hev
    obtain ⟨δ, hδpos, hδ⟩ := hev
    rw [hFdef, Metric.mem_closure_iff] at hxF
    obtain ⟨y, hy, hyδ⟩ := hxF δ hδpos
    obtain ⟨hyΓ, hyC⟩ := hy
    exact hyC ⟨hyΓ, Set.image_mono (openCube_subset_closedCube (3/4))
      (hδ ⟨Metric.mem_ball.mpr (by rwa [dist_comm] at hyδ), hyΓ⟩)⟩
  obtain ⟨δW, hδWpos, hδWdisj⟩ :=
    hΔF.exists_cthickenings (isCompact_simp _) hFcl
  set W : Set (PL.E N) := Metric.thickening (δW/2) (PL.simp (τ₀ ∪ τ₁)) with hWdef
  have hWopen : IsOpen W := by rw [hWdef]; exact Metric.isOpen_thickening
  have hΔW : PL.simp (τ₀ ∪ τ₁) ⊆ W := by
    intro x hx
    rw [hWdef, Metric.mem_thickening_iff]
    exact ⟨x, hx, by rw [dist_self]; linarith⟩
  have hclWC : closure W ∩ Γ.space ⊆ C := by
    intro y hy
    obtain ⟨hyW, hyΓ⟩ := hy
    have hycth : y ∈ Metric.cthickening δW (PL.simp (τ₀ ∪ τ₁)) :=
      Metric.cthickening_mono (show δW/2 ≤ δW by linarith) _
        (Metric.closure_thickening_subset_cthickening _ _ (by rwa [hWdef] at hyW))
    by_contra hyC
    have hyF : y ∈ F := by
      rw [hFdef]
      exact subset_closure ⟨hyΓ, hyC⟩
    exact (Set.disjoint_left.mp hδWdisj hycth) (Metric.self_subset_cthickening _ hyF)
  -- ### Urysohn's `χ`
  set Z : Set (PL.E N) := closure (L \ (PL.simp (τ₀ ∪ τ₁) ∪ (O ∩ W))) ∪ Wᶜ with hZdef
  have hZcl : IsClosed Z := by
    rw [hZdef]
    exact isClosed_closure.union hWopen.isClosed_compl
  have hZdisj : Disjoint Z (PL.simp (τ₀ ∪ τ₁)) := by
    rw [Set.disjoint_left]
    intro x hxZ hxΔ
    rw [hZdef] at hxZ
    rcases hxZ with hxcl | hxWc
    · have hfx1 : f x ∈ ψ.toFun '' PL.openCube (3 / 4 : ℝ) :=
        Set.image_mono (openCube_mono (by norm_num)) (hchart ⟨x, hxΔ, rfl⟩)
      have hUo : IsOpen (ψ.toFun '' PL.openCube (3 / 4 : ℝ)) :=
        Work.Cells.Connell.cubeChart_isOpen_image_openCube ψ (by norm_num) (by norm_num)
      have hev : ∀ᶠ y in 𝓝[Γ.space] x, f y ∈ ψ.toFun '' PL.openCube (3 / 4 : ℝ) :=
        (hcont.continuousWithinAt (hΔsp hxΔ)).eventually (hUo.mem_nhds hfx1)
      simp only [Filter.eventually_iff, Metric.mem_nhdsWithin_iff] at hev
      obtain ⟨δ, hδpos, hδ⟩ := hev
      rw [Metric.mem_closure_iff] at hxcl
      obtain ⟨y, hy, hyd⟩ := hxcl (min δ (δW/2)) (lt_min hδpos (by linarith))
      have hyΓ : y ∈ Γ.space := hsubL.subset_space hy.1
      have hyO : y ∈ O := by
        refine ⟨hyΓ, hδ ⟨?_, hyΓ⟩⟩
        rw [Metric.mem_ball, ← dist_comm]
        exact lt_of_lt_of_le hyd (min_le_left _ _)
      have hyW : y ∈ W := by
        rw [hWdef, Metric.mem_thickening_iff]
        refine ⟨x, hxΔ, ?_⟩
        rw [dist_comm]
        exact lt_of_lt_of_le hyd (min_le_right _ _)
      exact hy.2 (Or.inr ⟨hyO, hyW⟩)
    · exact hxWc (hΔW hxΔ)
  obtain ⟨χ, hχ0, hχ1, hχrange⟩ :=
    exists_continuous_zero_one_of_isClosed hZcl (isClosed_simp _) hZdisj
  have hχνeW : ∀ x ∈ Γ.space, χ x ≠ 0 → x ∈ W := by
    intro x _ hχ
    by_contra hxW
    exact hχ (hχ0 (by rw [hZdef]; exact Or.inr hxW))
  have hχC : ∀ x ∈ Γ.space, χ x ≠ 0 → x ∈ C := by
    intro x hx hχ
    exact hclWC ⟨subset_closure (hχνeW x hx hχ), hx⟩
  have hLχ : ∀ x ∈ L, χ x ≠ 0 → x ∈ PL.simp (τ₀ ∪ τ₁) ∨ x ∈ O ∩ W := by
    intro x hxL hχ
    by_contra hcon
    push_neg at hcon
    exact hχ (hχ0 (by rw [hZdef]; exact Or.inl (subset_closure ⟨hxL, fun hh => hh.elim hcon.1 hcon.2⟩)))
  -- ### the branch function `P` on `S = simp Δ ∪ closure (L ∩ O ∩ W)`
  set cl : Set (PL.E N) := closure (L ∩ O ∩ W) with hcldef
  have hclcl : IsClosed cl := by rw [hcldef]; exact isClosed_closure
  have hclL : cl ⊆ L := closure_minimal (fun _ hy => hy.1.1) hLcl
  have hclC : cl ⊆ C := by
    intro x hx
    rw [hcldef] at hx
    have hxcl : x ∈ closure (O ∩ W) :=
      closure_mono (show L ∩ O ∩ W ⊆ O ∩ W from fun _ hy => ⟨hy.1.2, hy.2⟩) hx
    have hxΓ : x ∈ Γ.space := closure_minimal (fun _ hy => hy.1.1) hspC hxcl
    refine ⟨hxΓ, ?_⟩
    have h1 : f x ∈ closure (f '' (O ∩ W)) := by
      rw [Metric.mem_closure_iff]
      intro e he
      have hcw : ContinuousWithinAt f Γ.space x := hcont.continuousWithinAt hxΓ
      have hev := hcw.eventually (Metric.ball_mem_nhds (f x) he)
      simp only [Filter.eventually_iff, Metric.mem_nhdsWithin_iff] at hev
      obtain ⟨δ, hδpos, hδ⟩ := hev
      rw [Metric.mem_closure_iff] at hxcl
      obtain ⟨y, hy, hyd⟩ := hxcl δ hδpos
      exact ⟨f y, ⟨y, hy, rfl⟩, by
        rw [dist_comm]
        exact hδ ⟨Metric.mem_ball.mpr (by rwa [dist_comm] at hyd), hy.1.1⟩⟩
    have h2 : f '' (O ∩ W) ⊆ ψ.toFun '' PL.openCube (3 / 4 : ℝ) := by
      rintro z ⟨y, hy, rfl⟩
      exact hy.1.2
    exact closure_minimal (h2.trans (Set.image_mono (openCube_subset_closedCube (3/4)))) hAcl h1
  set S : Set (PL.E N) := PL.simp (τ₀ ∪ τ₁) ∪ cl with hSdef
  have hScl : IsClosed S := by rw [hSdef]; exact (isClosed_simp _).union hclcl
  set P : PL.E N → PL.E n := fun x =>
    if x ∈ PL.simp (τ₀ ∪ τ₁) then g x else Work.Geo.Radial.chartInv ψ (f x) with hPdef
  have hPcont : ContinuousOn P S := by
    rw [hSdef]
    refine ContinuousOn.union_of_isClosed ?_ ?_ (isClosed_simp _) hclcl
    · refine (hg_cont.mono hΔsp).congr (fun x hx => ?_)
      simp only [hPdef, hx, if_true]
    · refine (hchartInv_cont.mono hclC).congr (fun x hx => ?_)
      by_cases hxΔ : x ∈ PL.simp (τ₀ ∪ τ₁)
      · simp only [hPdef, hxΔ, if_true]
        rw [hg_eqL₀ (hLsimpΔL₀ ⟨hclL hx, hxΔ⟩), hfc_C (hclC hx)]
      · simp only [hPdef, hxΔ, if_false]
  have hPmem : ∀ x ∈ S, P x - f_c x ∈ Metric.closedBall (0 : PL.E n) ε₁ := by
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm]
    by_cases hxΔ : x ∈ PL.simp (τ₀ ∪ τ₁)
    · simp only [hPdef, hxΔ, if_true]
      simpa only [dist_eq_norm, sub_zero] using (hg_near x (hΔsp hxΔ)).le
    · have hxcl : x ∈ cl := by
        rw [hSdef] at hx
        exact hx.resolve_left hxΔ
      simp only [hPdef, hxΔ, if_false]
      rw [hfc_C (hclC hxcl)]
      simp only [sub_self, zero_sub, norm_zero]
      exact hε₁pos.le
  haveI : TietzeExtension ↥(Metric.closedBall (0 : PL.E n) ε₁) :=
    Metric.instTietzeExtensionClosedBall ℝ (0 : PL.E n) hε₁pos
  obtain ⟨η, hηmem, hηeq⟩ := ContinuousMap.exists_forall_mem_restrict_eq hScl
    ⟨S.domRestrict (fun x => P x - f_c x),
      (hPcont.sub hfc_cont.continuousOn).domRestrict⟩ (fun x => hPmem x.1 x.2)
  have hηeq' : ∀ x ∈ S, η x = P x - f_c x := by
    intro x hx
    have := congrFun (congrArg DFunLike.coe hηeq) ⟨x, hx⟩
    simpa using this
  have hηnorm : ∀ x, ‖η x‖ ≤ ε₁ := by
    intro x
    have h := hηmem x
    rw [Metric.mem_closedBall, dist_eq_norm] at h
    simpa using h
  set B : PL.E N → PL.E n := fun x => f_c x + η x with hBdef
  have hBeq : ∀ x ∈ S, B x = P x := by
    intro x hx
    simp only [hBdef, hηeq' x hx]
    abel
  -- ### the convex-combination branch and `g₁`
  set comb : PL.E N → PL.E n := fun x => f_c x + χ x • η x with hcombdef
  have hcomb_cont : ContinuousOn comb Γ.space := by
    simp only [hcombdef]
    exact hfc_cont.continuousOn.add (χ.continuous.smul η.continuous).continuousOn
  have hcomb_fc : ∀ x, χ x = 0 → comb x = f_c x := by
    intro x hx
    simp only [hcombdef, hx, zero_smul, add_zero]
  have hcomb_B : ∀ x, χ x = 1 → comb x = B x := by
    intro x hx
    simp only [hcombdef, hBdef, hx, one_smul]
  have hcomb_dist : ∀ x, dist (comb x) (f_c x) ≤ ε₁ := by
    intro x
    have hχ := hχrange x
    rw [Set.mem_Icc] at hχ
    have hsub : comb x - f_c x = χ x • η x := by
      simp only [hcombdef]
      abel
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs]
    calc |χ x| * ‖η x‖ ≤ 1 * ε₁ :=
          mul_le_mul (abs_le.mpr ⟨by linarith [hχ.1], hχ.2⟩) (hηnorm x) (norm_nonneg _) zero_le_one
      _ = ε₁ := one_mul _
  have hcomb_cube : ∀ x, comb x ∈ PL.closedCube (13/16 : ℝ) := by
    intro x
    have hχ := hχrange x
    rw [Set.mem_Icc] at hχ
    have hηi : ∀ i, |η x i| ≤ ε₁ := by
      intro i
      have h := PiLp.norm_apply_le (η x) i
      rw [Real.norm_eq_abs] at h
      exact h.trans (hηnorm x)
    intro i
    have hcoord : comb x i = f_c x i + χ x * η x i := by
      simp only [hcombdef]
      rfl
    rw [hcoord]
    calc |f_c x i + χ x * η x i| ≤ |f_c x i| + |χ x * η x i| := abs_add_le _ _
      _ = |f_c x i| + |χ x| * |η x i| := by rw [abs_mul]
      _ ≤ 3/4 + 1 * ε₁ := add_le_add (hfc_mem x i)
          (mul_le_mul (abs_le.mpr ⟨by linarith [hχ.1], hχ.2⟩) (hηi i) (abs_nonneg _) zero_le_one)
      _ ≤ 13/16 := by linarith [hε₁16]
  set g₁ : PL.E N → M := fun x => if χ x = 0 then f x else ψ.toFun (comb x) with hg₁def
  have hGcont : ContinuousOn (fun x => ψ.toFun (comb x)) Γ.space :=
    ψ.cont.comp hcomb_cont (fun x _ => closedCube_subset_openCube (by norm_num) (hcomb_cube x))
  have hagree : ∀ x ∈ Γ.space, χ x = 0 →
      x ∈ closure (Γ.space ∩ {y | χ y ≠ 0}) → ψ.toFun (comb x) = f x := by
    intro x hxΓ hx0 hxcl
    have hxclW : x ∈ closure W :=
      closure_mono (fun y hy => hχνeW y hy.1 hy.2) hxcl
    have hxC : x ∈ C := hclWC ⟨hxclW, hxΓ⟩
    rw [hcomb_fc x hx0, hfc_C hxC]
    exact Work.Geo.Radial.chartInv_toFun ψ (by
      rw [Work.Geo.Radial.chartImage]
      exact Set.image_mono h3_4_1 hxC.2)
  have hg₁cont : ContinuousOn g₁ Γ.space := by
    simp only [hg₁def]
    exact continuousOn_ite_of_closure χ.continuous hcont hGcont hagree
  have hg₁L : Set.EqOn g₁ f L := by
    intro x hxL
    simp only [hg₁def]
    by_cases hχ : χ x = 0
    · simp only [hχ, if_true]
    · simp only [hχ, if_false]
      by_cases hxΔ : x ∈ PL.simp (τ₀ ∪ τ₁)
      · have hχ1' : χ x = 1 := hχ1 hxΔ
        have hxS : x ∈ S := Or.inl hxΔ
        have hcombx : comb x = g x := by
          rw [hcomb_B x hχ1', hBeq x hxS]
          simp only [hPdef, hxΔ, if_true]
        rw [hcombx, hg_eqL₀ (hLsimpΔL₀ ⟨hxL, hxΔ⟩)]
        have hxC : x ∈ C := ⟨hΔsp hxΔ, Set.image_mono h1_2_3_4 (hchart ⟨x, hxΔ, rfl⟩)⟩
        rw [hfc_C hxC]
        exact Work.Geo.Radial.chartInv_toFun ψ (by
          rw [Work.Geo.Radial.chartImage]
          exact Set.image_mono h3_4_1 hxC.2)
      · have hxOW : x ∈ O ∩ W := by
          rcases hLχ x hxL hχ with h | h
          · exact absurd h hxΔ
          · exact h
        have hxcl : x ∈ cl := subset_closure ⟨⟨hxL, hxOW.1⟩, hxOW.2⟩
        have hxS : x ∈ S := Or.inr hxcl
        have hηx : η x = 0 := by
          rw [hηeq' x hxS]
          simp only [hPdef, hxΔ, if_false]
          rw [hfc_C (hOC hxOW.1), sub_self]
        have hcombx : comb x = f_c x := by
          simp only [hcombdef, hηx, smul_zero, add_zero]
        rw [hcombx]
        have hxC : x ∈ C := hOC hxOW.1
        rw [hfc_C hxC]
        exact Work.Geo.Radial.chartInv_toFun ψ (by
          rw [Work.Geo.Radial.chartImage]
          exact Set.image_mono h3_4_1 hxC.2)
  have hg₁dist : ∀ x ∈ Γ.space, dist (g₁ x) (f x) < ε := by
    intro x hxΓ
    simp only [hg₁def]
    by_cases hχ : χ x = 0
    · simp only [hχ, if_true]
      simpa using hε
    · simp only [hχ, if_false]
      have hxC : x ∈ C := hχC x hxΓ hχ
      have hfx : ψ.toFun (f_c x) = f x := by
        rw [hfc_C hxC]
        exact Work.Geo.Radial.chartInv_toFun ψ (by
          rw [Work.Geo.Radial.chartImage]
          exact Set.image_mono h3_4_1 hxC.2)
      calc dist (ψ.toFun (comb x)) (f x)
          = dist (ψ.toFun (comb x)) (ψ.toFun (f_c x)) := by rw [hfx]
        _ < min ε δV := hθ (comb x) (hcomb_cube x) (f_c x)
            (closedCube_mono (by norm_num) (hfc_mem x))
            (lt_of_le_of_lt (hcomb_dist x) hε₁θ)
        _ ≤ ε := min_le_left _ _
  have hg₁V : X ∪ g₁ '' K ⊆ V := by
    rintro y (hy | ⟨x, hxK, rfl⟩)
    · exact hL7.engK (Or.inl hy)
    · simp only [hg₁def]
      by_cases hχ : χ x = 0
      · simp only [hχ, if_true]
        exact hL7.engK (Or.inr ⟨x, hxK, rfl⟩)
      · simp only [hχ, if_false]
        have hxΓ : x ∈ Γ.space := hL7.subK.subset_space hxK
        have hxC : x ∈ C := hχC x hxΓ hχ
        have hfx : ψ.toFun (f_c x) = f x := by
          rw [hfc_C hxC]
          exact Work.Geo.Radial.chartInv_toFun ψ (by
            rw [Work.Geo.Radial.chartImage]
            exact Set.image_mono h3_4_1 hxC.2)
        have hd : dist (ψ.toFun (comb x)) (f x) < δV := by
          calc dist (ψ.toFun (comb x)) (f x)
              = dist (ψ.toFun (comb x)) (ψ.toFun (f_c x)) := by rw [hfx]
            _ < min ε δV := hθ (comb x) (hcomb_cube x) (f_c x)
                (closedCube_mono (by norm_num) (hfc_mem x))
                (lt_of_le_of_lt (hcomb_dist x) hε₁θ)
            _ ≤ δV := min_le_right _ _
        exact hδVsub (Metric.mem_thickening_iff.mpr ⟨f x, ⟨x, hxK, rfl⟩, hd⟩)
  have hg₁aff : ∀ i (hi : i < ord.length), ∃ A : PL.E N →ᵃ[ℝ] PL.E n,
      (∀ x ∈ PL.simp ord[i], A x ∈ PL.openCube 1) ∧
      (∀ x ∈ PL.simp ord[i], g₁ x = ψ.toFun (A x)) := by
    intro i hi
    obtain ⟨hface, _hcard, hsub⟩ := hord_faces ord[i] (List.get_mem ord ⟨i, hi⟩)
    have hne : (PL.simp ord[i]).Nonempty :=
      simp_nonempty (((T N).subdiv.sdIter r Γ hΓfin).nonempty_of_mem_faces hface)
    obtain ⟨x₀, hx₀⟩ := hne
    have hx₀Δ : x₀ ∈ PL.simp (τ₀ ∪ τ₁) := hsub hx₀
    have hx₀C : x₀ ∈ C :=
      ⟨hΔsp hx₀Δ, Set.image_mono h1_2_3_4 (hchart ⟨x₀, hx₀Δ, rfl⟩)⟩
    have hgα : g x₀ ∈ PL.closedCube (11/16 : ℝ) := by
      intro j
      have hhalf : |f_c x₀ j| ≤ 1/2 := by
        rw [show f_c x₀ = Work.Geo.Radial.chartInv ψ (f x₀) from hfc_C hx₀C]
        obtain ⟨u, hu, huψ⟩ := hchart ⟨x₀, hx₀Δ, rfl⟩
        have humem : f x₀ ∈ Work.Geo.Radial.chartImage ψ := by
          rw [Work.Geo.Radial.chartImage]
          exact ⟨u, h3_4_1 (h1_2_3_4 hu), huψ⟩
        have h1 : Work.Geo.Radial.chartInv ψ (f x₀) ∈ PL.openCube (n := n) 1 :=
          Work.Geo.Radial.chartInv_mem ψ humem
        have h2 : u ∈ PL.openCube (n := n) 1 := openCube_mono (by norm_num) hu
        have h3 : u = Work.Geo.Radial.chartInv ψ (f x₀) :=
          Work.Geo.Radial.toFun_injOn_openCube ψ h2 h1
            (by rw [huψ, Work.Geo.Radial.chartInv_toFun ψ humem])
        rw [← h3]
        exact le_of_lt (hu j)
      have hnorm : ‖g x₀ - f_c x₀‖ < ε₁ := by
        rw [← dist_eq_norm]
        exact hg_near x₀ (hΔsp hx₀Δ)
      calc |g x₀ j| ≤ |g x₀ j - f_c x₀ j| + |f_c x₀ j| := by
            conv_lhs => rw [show g x₀ j = (g x₀ j - f_c x₀ j) + f_c x₀ j by ring]
            exact abs_add_le _ _
        _ ≤ ‖g x₀ - f_c x₀‖ + 1/2 := by
            refine add_le_add ?_ hhalf
            have h := PiLp.norm_apply_le (g x₀ - f_c x₀) j
            rw [Real.norm_eq_abs] at h
            exact h
        _ ≤ 11/16 := by linarith [hε₁16]
    obtain ⟨A, hA⟩ := hg_aff ord[i] hface ⟨x₀, hx₀, hgα⟩
    refine ⟨A, ?_, ?_⟩
    · intro x hx
      rw [← hA hx]
      intro j
      have hnorm : ‖g x - f_c x‖ < ε₁ := by
        rw [← dist_eq_norm]
        exact hg_near x (hΔsp (hsub hx))
      have hhalf : |f_c x j| ≤ 1/2 := by
        have hx' : x ∈ C := ⟨hΔsp (hsub hx), Set.image_mono h1_2_3_4 (hchart ⟨x, hsub hx, rfl⟩)⟩
        rw [show f_c x = Work.Geo.Radial.chartInv ψ (f x) from hfc_C hx']
        obtain ⟨u, hu, huψ⟩ := hchart ⟨x, hsub hx, rfl⟩
        have humem : f x ∈ Work.Geo.Radial.chartImage ψ := by
          rw [Work.Geo.Radial.chartImage]
          exact ⟨u, h3_4_1 (h1_2_3_4 hu), huψ⟩
        have h1 : Work.Geo.Radial.chartInv ψ (f x) ∈ PL.openCube (n := n) 1 :=
          Work.Geo.Radial.chartInv_mem ψ humem
        have h2 : u ∈ PL.openCube (n := n) 1 := openCube_mono (by norm_num) hu
        have h3 : u = Work.Geo.Radial.chartInv ψ (f x) :=
          Work.Geo.Radial.toFun_injOn_openCube ψ h2 h1
            (by rw [huψ, Work.Geo.Radial.chartInv_toFun ψ humem])
        rw [← h3]
        exact le_of_lt (hu j)
      calc |g x j| ≤ |g x j - f_c x j| + |f_c x j| := by
            conv_lhs => rw [show g x j = (g x j - f_c x j) + f_c x j by ring]
            exact abs_add_le _ _
        _ ≤ ‖g x - f_c x‖ + 1/2 := by
            refine add_le_add ?_ hhalf
            have h := PiLp.norm_apply_le (g x - f_c x) j
            rw [Real.norm_eq_abs] at h
            exact h
        _ < 1 := by linarith [hε₁16]
    · intro x hx
      simp only [hg₁def]
      have hχx : χ x = 1 := hχ1 (hsub hx)
      have hxS : x ∈ S := Or.inl (hsub hx)
      have hcombx : comb x = g x := by
        rw [hcomb_B x hχx, hBeq x hxS]
        simp only [hPdef, hsub hx, if_true]
      rw [if_neg (by rw [hχx]; norm_num), hcombx, hA hx]
  exact ⟨r, ord, g₁, hord_nodup, hord_faces, hord_cover, hord_shell, hg₁cont, hg₁L,
    hg₁dist, hg₁V, hg₁aff⟩

end Work.Engulf.E4Aux
