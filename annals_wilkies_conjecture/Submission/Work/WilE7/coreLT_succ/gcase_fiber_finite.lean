/-
  `Work.WilE7.coreLT_succ.gcase_fiber_finite`: **finiteness of the fibres of a `Good` absolute
  stratum of full `π_n`-rank over the part of the base on which its closure adds no points.**

  `T : Stratum 0 (n + (m + 1))` is a `Good` absolute stratum whose tangent space projects
  isomorphically to `ℝ^n` at every point (`hrank`).  By the local form of the implicit function
  theorem (`Work.WilE7.CoreStep.localGraph_on_branch`) `absSet T` is, near each of its points,
  the graph of a function over `π_n`; hence *`π_n` is locally injective on `absSet T`*, so every
  fibre of `absSet T` over `ℝ^n` is a discrete subset of the cube `[-1,1]^{m+1}`.  The hypothesis
  `hclosed` says that over the base set `C` the closure of `absSet T` adds nothing, which turns
  each such fibre into a *closed* (hence compact) subset of the cube.  A compact discrete set is
  finite, which is the conclusion.

  The purely point-set content of the argument is isolated in
  `fiber_finite_of_closed_locallyInj` below, stated for an arbitrary bounded `X ⊆ ℝ^{p+q}` that is
  closed over `C` inside its closure and locally injective for `projFirst` at its `C`-points.
-/
import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.CoreStep.localGraph_on_branch
import Submission.Work.WilE7.CoreStep.fibre_locallyConnected
import Submission.Work.CoreStep.hcof_of_pairCovers

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open scoped Topology

namespace Work.WilE7.coreLT_succ

open WilkiesDesign WilkiesDesign.E

/-- `y ↦ Fin.append x y` is continuous, for arbitrary fibre dimension `q`. -/
theorem continuous_append_of {p q : ℕ} (x : Fin p → ℝ) :
    Continuous fun y : Fin q → ℝ => Fin.append x y :=
  (Fin.continuous_append (X := ℝ) p q).comp
    ((continuous_const : Continuous fun _ : Fin q → ℝ => x).prodMk continuous_id)

/-- **A bounded set that is closed over `C` inside its closure and locally injective for
`projFirst` at its `C`-points has finite fibres over `C`.**

Proof.  Fix `x ∈ C` and let `F := fiber X x ⊆ ℝ^q`.

* `F` is *closed*: if `y ∈ closure F` then `Fin.append x y ∈ closure X` (continuity of
  `y ↦ Fin.append x y`), and `π (Fin.append x y) = x ∈ C`, so `hclosed` gives
  `Fin.append x y ∈ X`, i.e. `y ∈ F`.
* `F` is *bounded* (`X` lives in the cube), hence compact.
* Each point `y ∈ F` is *isolated in `F`*: `hLoc` at `z = Fin.append x y` produces a
  neighbourhood `V ∋ z` on which `projFirst` is injective on `X ∩ V`; the preimage of `V` under
  `y' ↦ Fin.append x y'` is an open neighbourhood of `y` meeting `F` only in `y`.
* A compact set in which every point is isolated is finite. -/
theorem fiber_finite_of_closed_locallyInj {p q : ℕ} (X : Set (Fin (p + q) → ℝ))
    (C : Set (Fin p → ℝ))
    (hbdd : X ⊆ WilkiesDesign.E.cubeC (p + q))
    (hclosed : ∀ z ∈ closure X, WilkiesDesign.E.projFirst p q z ∈ C → z ∈ X)
    (hLoc : ∀ z ∈ X, WilkiesDesign.E.projFirst p q z ∈ C → ∃ V ∈ nhds z,
      ∀ w ∈ X ∩ V, ∀ w' ∈ X ∩ V,
        WilkiesDesign.E.projFirst p q w = WilkiesDesign.E.projFirst p q w' → w = w') :
    ∀ x ∈ C, (WilkiesDesign.E.fiber X x).Finite := by
  intro x hxC
  have hφcont : Continuous fun y : Fin q → ℝ => Fin.append x y :=
    continuous_append_of x
  have hproj : ∀ y : Fin q → ℝ, WilkiesDesign.E.projFirst p q (Fin.append x y) = x := by
    intro y
    funext i
    simp [WilkiesDesign.E.projFirst, Fin.append_left]
  -- `F` is closed
  have hFclosed : IsClosed (WilkiesDesign.E.fiber X x) := by
    rw [← closure_subset_iff_isClosed]
    intro y hy
    have hycl : Fin.append x y ∈ closure X := by
      have h1 : Fin.append x y ∈ closure
          ((fun y' : Fin q → ℝ => Fin.append x y') '' WilkiesDesign.E.fiber X x) :=
        image_closure_subset_closure_image hφcont (Set.mem_image_of_mem _ hy)
      refine closure_mono ?_ h1
      rintro _ ⟨y', hy', rfl⟩
      exact hy'
    exact hclosed _ hycl (by rw [hproj y]; exact hxC)
  -- `F` is bounded
  have hFsub : WilkiesDesign.E.fiber X x ⊆ WilkiesDesign.E.cubeC q := by
    intro y hy j
    have h2 := hbdd hy (Fin.natAdd p j)
    rwa [Fin.append_right] at h2
  have hFcompact : IsCompact (WilkiesDesign.E.fiber X x) :=
    (Work.CoreStep.cubeC_isCompact' q).of_isClosed_subset hFclosed hFsub
  -- every point of `F` is isolated in `F`
  have hiso : ∀ y : Fin q → ℝ, y ∈ WilkiesDesign.E.fiber X x →
      ∃ U : Set (Fin q → ℝ), IsOpen U ∧ y ∈ U ∧
        U ∩ WilkiesDesign.E.fiber X x ⊆ {y} := by
    intro y hy
    have hzX : Fin.append x y ∈ X := hy
    obtain ⟨V, hVnhds, hVinj⟩ := hLoc _ hzX (by rw [hproj y]; exact hxC)
    obtain ⟨U, hUsub, hUopen, hzU⟩ := mem_nhds_iff.mp hVnhds
    refine ⟨(fun y' : Fin q → ℝ => Fin.append x y') ⁻¹' U,
      hφcont.isOpen_preimage U hUopen, hzU, ?_⟩
    intro y' hy'
    rw [Set.mem_singleton_iff]
    have hy'U : Fin.append x y' ∈ U := hy'.1
    have hy'F : y' ∈ WilkiesDesign.E.fiber X x := hy'.2
    have hinj := hVinj (Fin.append x y') ⟨hy'F, hUsub hy'U⟩ (Fin.append x y)
      ⟨hzX, hUsub hzU⟩ (by rw [hproj y', hproj y])
    funext j
    have := congrFun hinj (Fin.natAdd p j)
    simpa [Fin.append_right] using this
  -- a finite subcover of the isolating neighbourhoods, using compactness
  have hU : ∀ y : {y // y ∈ WilkiesDesign.E.fiber X x},
      ∃ U : Set (Fin q → ℝ), IsOpen U ∧ (y : Fin q → ℝ) ∈ U ∧
        U ∩ WilkiesDesign.E.fiber X x ⊆ {(y : Fin q → ℝ)} :=
    fun y => hiso y y.2
  choose U hUopen hyU hUiso using hU
  have hcov : WilkiesDesign.E.fiber X x ⊆
      ⋃ y : {y // y ∈ WilkiesDesign.E.fiber X x}, U y := by
    intro y hy
    exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hyU ⟨y, hy⟩⟩
  obtain ⟨t, ht⟩ := hFcompact.elim_finite_subcover U hUopen hcov
  refine Set.Finite.subset (t.image (fun y : {y // y ∈ WilkiesDesign.E.fiber X x} =>
      (y : Fin q → ℝ))).finite_toSet ?_
  intro y hy
  rw [Finset.mem_coe, Finset.mem_image]
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (ht hy)
  obtain ⟨hit, hyi⟩ := Set.mem_iUnion.mp hi
  exact ⟨i, hit, (Set.mem_singleton_iff.mp (hUiso i ⟨hyi, hy⟩)).symm⟩

/-- **`gcase_fiber_finite`.**  For a `Good` absolute stratum `T` of full `π_n`-rank, the
`π_n`-fibres of `absSet T` over a base set `C` on which the closure of `absSet T` adds no point
are finite.

The local injectivity hypothesis of `fiber_finite_of_closed_locallyInj` is supplied by the local
graph form of the implicit function theorem, `Work.WilE7.CoreStep.localGraph_on_branch`: two
points `w, w'` of `absSet T` in a suitable neighbourhood of `z = absPt u₀` with the same `π_n`
image satisfy `projSnd w = g (π_n w) = g (π_n w') = projSnd w'`, and both are the gluing
`Fin.append (π_n ·) (projSnd ·)` of their projections. -/
theorem gcase_fiber_finite {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (hT : WilkiesDesign.E.Stratum.Good T)
    (hrank : ∀ z ∈ T.X.set, Work.WilE7.MainDesign.projRank T z = n + (m + 1) - T.j)
    (C : Set (Fin n → ℝ))
    (hclosed : ∀ z ∈ closure (Work.WilE7.MainDesign.absSet T),
      WilkiesDesign.E.projFirst n (m + 1) z ∈ C → z ∈ Work.WilE7.MainDesign.absSet T) :
    ∀ x ∈ C, (WilkiesDesign.E.fiber (Work.WilE7.MainDesign.absSet T) x).Finite := by
  refine fiber_finite_of_closed_locallyInj (Work.WilE7.MainDesign.absSet T) C
    (Work.CoreStep.absSet_subset_cubeC T) hclosed ?_
  intro z hzX hzC
  obtain ⟨u₀, hu₀, hweq⟩ := hzX
  subst hweq
  obtain ⟨V, hVnhds, g, -, -, hgw⟩ :=
    Work.WilE7.CoreStep.localGraph_on_branch T hT hrank u₀ hu₀
  refine ⟨V, hVnhds, ?_⟩
  intro w hw w' hw' hproj
  have h1 : g (WilkiesDesign.E.projFirst n (m + 1) w)
      = WilkiesDesign.E.projSnd n (m + 1) w := hgw w hw
  have h2 : g (WilkiesDesign.E.projFirst n (m + 1) w')
      = WilkiesDesign.E.projSnd n (m + 1) w' := hgw w' hw'
  rw [hproj] at h1
  have hsnd : WilkiesDesign.E.projSnd n (m + 1) w
      = WilkiesDesign.E.projSnd n (m + 1) w' := h1.symm.trans h2
  calc w = Fin.append (WilkiesDesign.E.projFirst n (m + 1) w)
            (WilkiesDesign.E.projSnd n (m + 1) w) :=
        (Work.WilE7.append_projFirst_projSnd w).symm
    _ = Fin.append (WilkiesDesign.E.projFirst n (m + 1) w')
            (WilkiesDesign.E.projSnd n (m + 1) w') := by rw [hproj, hsnd]
    _ = w' := Work.WilE7.append_projFirst_projSnd w'

end Work.WilE7.coreLT_succ
