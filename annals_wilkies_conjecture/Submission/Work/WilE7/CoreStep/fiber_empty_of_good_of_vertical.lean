/-
  `Work.WilE7.CoreStep.fiber_empty_of_good_of_vertical`
  (S50 §6 of `NOTES_S50_vertical_row_G_case.md`).

  **The `Σ`-free (`G`) vertical row is vacuous.**  Let `T` be a `Good` absolute stratum of
  `ℝ^{0+(n+(m+1))}` (base `ℝ^n`, fibre `ℝ^{m+1}`, vertical coordinate = the LAST fibre
  coordinate) satisfying

  * `himm`: `π_{n+1} = (.init, vertCoord)` is an *immersion* on the tangent space of `T`
    (its rank on `ker (jac T z)` equals `dim T = n + (m+1) - T.j` at every `z ∈ T.X.set`), and
  * `hvert`: the `π_n`-rank on the tangent space is `dim T - 1` (one-dimensional `π_n`-fibres),

  and let `C` be a base cell *avoiding* the projection of the topological frontier of `T`
  (`hclosed`).  Then no point of `C` lies under `T`:

      ∀ x ∈ C, ¬ (fiber (absSet T) x).Nonempty.

  Since a fibre over `x ∈ C` is closed (`hclosed`) and bounded (it lies in the cube), it is
  compact, so `vertCoord` attains a maximum at some `y₀`.  The stratum is locally the level set
  of its defining equations (`Good`), so via the implicit function theorem the fibre over `x` is
  a one-dimensional manifold **without boundary** near `y₀` (`hvert` gives rank `dim ker - 1`),
  while `himm` says that `vertCoord` has **no critical point** on it.  A continuous function on a
  compact boundaryless one-manifold attains its maximum at an interior point, where its
  derivative must vanish — contradiction.  (`T.j < n + (m+1)`, i.e. `hjd`, is essential: without
  it the two rank conditions are vacuous for a zero-dimensional `T`.)

  The single analytic input, `Work.WilE7.CoreStep.exists_implicit_curve_of_constant_rank`, is a
  corank-one constant-rank implicit function theorem (an implicit *curve* with prescribed
  tangent vector), proved separately.
-/
import Mathlib
import Submission.Work.WilE7.CoreStep.VerticalG
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.DimAPI.absSet_local_levelSet
import Submission.Work.WilE7.DimAPI.ProjRankAux
import Submission.Work.WilE7.DimAPI.range_fderiv_good_eq_top
import Submission.Work.WilE7.DimAPI.jac_eq_fderiv
import Submission.Work.WilE7.Auxiliary.analyticLevelSetChart
import Submission.Work.WilE7.Nondrop.analyticLevelSetChartRange
import Submission.Work.WilE7.CoreStep.exists_implicit_curve_of_constant_rank

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open scoped Topology

namespace Work.WilE7.CoreStep

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.DimAPI

/-- `eqMap` in the explicit lambda form used by `range_fderiv_good_eq_top` and `jac_eq_fderiv`. -/
theorem eqMap_eq_fun {N : ℕ} (S : WilkiesDesign.E.Stratum 0 N) :
    eqMap S = (fun w a => eaEval S.X.c (S.h a) w) := rfl

/-! ## Elementary bridges between the absolute stratum coordinates and `ℝ^N` -/

/-- The lift of a base point `x` and a fibre point `y` to the coordinates `Fin (0 + N)` of an
absolute stratum (`p = 0`). -/
def absLift {n m : ℕ} (x : Fin n → ℝ) (y : Fin (m + 1) → ℝ) : Fin (0 + (n + (m + 1))) → ℝ :=
  Fin.append (0 : Fin 0 → ℝ) (Fin.append x y)

/-- The vertical (last) coordinate, in the coordinates of an absolute stratum. -/
def verT {n m : ℕ} (z : Fin (0 + (n + (m + 1))) → ℝ) : ℝ :=
  z (Fin.natAdd 0 (Fin.natAdd n (Fin.last m)))

/-- `verT` is the last coordinate of the reindexing `absPt`. -/
theorem verT_absPt {n m : ℕ} (z : Fin (0 + (n + (m + 1))) → ℝ) :
    verT z = absPt z (Fin.natAdd n (Fin.last m)) := by
  rw [verT, absPt_apply_natAdd]

/-- `absPt` of a lift is the expected appending. -/
theorem absPt_absLift {n m : ℕ} (x : Fin n → ℝ) (y : Fin (m + 1) → ℝ) :
    absPt (absLift x y) = Fin.append x y :=
  absPt_append (0 : Fin 0 → ℝ) (Fin.append x y)

/-- The first `n` coordinates of `absPt z` are the linear base projection. -/
theorem projFirst_absPt {n m : ℕ} (z : Fin (0 + (n + (m + 1))) → ℝ) :
    projFirst n (m + 1) (absPt z) = basePrLin n (m + 1) z := by
  funext i
  rw [basePrLin, LinearMap.funLeft_apply]
  rfl

/-- The base projection of a lift is the base point. -/
theorem basePrLin_absLift {n m : ℕ} (x : Fin n → ℝ) (y : Fin (m + 1) → ℝ) :
    basePrLin n (m + 1) (absLift x y) = x := by
  rw [absLift, ← projFirst_absPt (Fin.append (0 : Fin 0 → ℝ) (Fin.append x y)),
    absPt_append]
  exact Work.WilE7.projFirst_append x y

/-- The vertical coordinate of a lift is `vertCoord` of the fibre point. -/
theorem verT_absLift {n m : ℕ} (x : Fin n → ℝ) (y : Fin (m + 1) → ℝ) :
    verT (absLift x y) = vertCoord y := by
  rw [absLift, verT, Fin.append_right, Fin.append_right]
  rfl

/-- The first `n` components of `π_{n+1}` on the tangent space of an absolute stratum. -/
theorem projTopLin_absPtLin_init {n m : ℕ} (v : Fin (0 + (n + (m + 1))) → ℝ) :
    Fin.init (projTopLin n m (absPtLin (n + (m + 1)) v)) = basePrLin n (m + 1) v := by
  rw [projTopLin_apply, absPtLin_apply, projTop_init]
  funext i
  rw [basePrLin, LinearMap.funLeft_apply]
  rfl

/-- The last component of `π_{n+1}` on the tangent space of an absolute stratum. -/
theorem projTopLin_absPtLin_last {n m : ℕ} (v : Fin (0 + (n + (m + 1))) → ℝ) :
    projTopLin n m (absPtLin (n + (m + 1)) v) (Fin.last n) = verT v := by
  rw [projTopLin_apply, absPtLin_apply, projTop_last]
  show projSnd n (m + 1) (absPt v) (Fin.last m) = verT v
  rw [verT]
  show absPt v (Fin.natAdd n (Fin.last m)) = v (Fin.natAdd 0 (Fin.natAdd n (Fin.last m)))
  rw [absPt_apply_natAdd]

/-! ## A rank criterion, and a one-sided mean value consequence -/

/-- A linear map of maximal rank on a submodule `K` is injective on `K`. -/
theorem eq_bot_inf_ker_of_finrank_map_eq {N M : ℕ} {K : Submodule ℝ (Fin N → ℝ)}
    (f : (Fin N → ℝ) →ₗ[ℝ] (Fin M → ℝ))
    (h : Module.finrank ℝ (K.map f) = Module.finrank ℝ K) : K ⊓ f.ker = ⊥ := by
  have h1 : Module.finrank ℝ (K.map f) + Module.finrank ℝ ↥(K ⊓ f.ker) = Module.finrank ℝ K := by
    have h2 := LinearMap.finrank_range_add_finrank_ker (f.comp K.subtype)
    rw [LinearMap.range_comp, Submodule.range_subtype, LinearMap.ker_comp,
      ← Submodule.finrank_map_subtype_eq K (Submodule.comap K.subtype f.ker),
      Submodule.map_comap_subtype] at h2
    exact h2
  have h0 : Module.finrank ℝ ↥(K ⊓ f.ker) = 0 := by omega
  exact Submodule.finrank_eq_zero.mp h0

/-- The injectivity form of the rank criterion above. -/
theorem eq_zero_of_mem_of_apply_eq_zero {N M : ℕ} {K : Submodule ℝ (Fin N → ℝ)}
    (f : (Fin N → ℝ) →ₗ[ℝ] (Fin M → ℝ))
    (h : Module.finrank ℝ (K.map f) = Module.finrank ℝ K)
    {v : Fin N → ℝ} (hv : v ∈ K) (hv0 : f v = 0) : v = 0 := by
  have hbot := eq_bot_inf_ker_of_finrank_map_eq f h
  have : v ∈ K ⊓ f.ker := ⟨hv, LinearMap.mem_ker.mpr hv0⟩
  rw [hbot] at this
  simpa using this

/-- If `f` has non-zero derivative `c` at `0`, then `f` takes values larger than `f 0`
arbitrarily close to `0`. -/
theorem exists_lt_of_hasDerivAt_ne {f : ℝ → ℝ} {c ε : ℝ} (h : HasDerivAt f c 0)
    (hc : c ≠ 0) (hε : 0 < ε) : ∃ t : ℝ, |t| < ε ∧ f 0 < f t := by
  have hslope : Tendsto (slope f 0) (𝓝[≠] (0 : ℝ)) (𝓝 c) := h.tendsto_slope
  have hmul : ∀ t : ℝ, t ≠ 0 → f t - f 0 = t * slope f 0 t := by
    intro t ht
    rw [slope_def_field]
    field_simp
    ring
  rcases lt_or_gt_of_ne hc.symm with hpos | hneg
  · -- `0 < c`: a small positive `t`
    have h1 : ∀ᶠ t in 𝓝[≠] (0 : ℝ), 0 < slope f 0 t :=
      hslope.eventually (eventually_gt_nhds hpos)
    rw [eventually_nhdsWithin_iff] at h1
    obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp h1
    refine ⟨min ε δ / 2, ?_, ?_⟩
    · have h2 : 0 < min ε δ := lt_min hε hδpos
      rw [abs_of_pos (by linarith)]
      linarith [min_le_left ε δ]
    · have h2 : 0 < min ε δ := lt_min hε hδpos
      have htne : (min ε δ / 2 : ℝ) ≠ 0 := by positivity
      have hdist : dist (min ε δ / 2) (0 : ℝ) < δ := by
        rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
        linarith [min_le_right ε δ]
      have hs : 0 < slope f 0 (min ε δ / 2) := hδ hdist htne
      have h4 := hmul (min ε δ / 2) htne
      have h5 : 0 < (min ε δ / 2) * slope f 0 (min ε δ / 2) := mul_pos (by linarith) hs
      linarith
  · -- `c < 0`: a small negative `t`
    have h1 : ∀ᶠ t in 𝓝[≠] (0 : ℝ), slope f 0 t < 0 :=
      hslope.eventually (eventually_lt_nhds hneg)
    rw [eventually_nhdsWithin_iff] at h1
    obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp h1
    refine ⟨-(min ε δ / 2), ?_, ?_⟩
    · have h2 : 0 < min ε δ := lt_min hε hδpos
      rw [abs_neg, abs_of_pos (by linarith)]
      linarith [min_le_left ε δ]
    · have h2 : 0 < min ε δ := lt_min hε hδpos
      have htne : (-(min ε δ / 2) : ℝ) ≠ 0 := by linarith
      have hdist : dist (-(min ε δ / 2)) (0 : ℝ) < δ := by
        rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by linarith)]
        linarith [min_le_right ε δ]
      have hs : slope f 0 (-(min ε δ / 2)) < 0 := hδ hdist htne
      have h4 := hmul (-(min ε δ / 2)) htne
      have h5 : 0 < (-(min ε δ / 2)) * slope f 0 (-(min ε δ / 2)) :=
        mul_pos_of_neg_of_neg (by linarith) hs
      linarith

/-! ## The main theorem -/

theorem fiber_empty_of_good_of_vertical {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (C : Set (Fin n → ℝ)) (hGood : T.Good) (hjd : T.j < n + (m + 1))
    (himm : ∀ z ∈ T.X.set,
      Module.finrank ℝ
          ↥(Submodule.map (Work.WilE7.CoreStep.projTopLin n m ∘ₗ Work.WilE7.CoreStep.absPtLin (n + (m + 1))) (Work.WilE7.MainDesign.jac T z).ker) =
        n + (m + 1) - T.j)
    (hvert : ∀ z ∈ T.X.set, Work.WilE7.MainDesign.projRank T z = n + (m + 1) - T.j - 1)
    (hclosed : ∀ z ∈ closure (Work.WilE7.MainDesign.absSet T),
      WilkiesDesign.E.projFirst n (m + 1) z ∈ C → z ∈ Work.WilE7.MainDesign.absSet T) :
    ∀ x ∈ C, ¬ (WilkiesDesign.E.fiber (Work.WilE7.MainDesign.absSet T) x).Nonempty := by
  intro x hxC hne
  -- ## Step 1. The fibre over `x` is closed, bounded, hence compact.
  set F : Set (Fin (m + 1) → ℝ) := fiber (absSet T) x with hFdef
  have hFclosed : IsClosed F := by
    rw [← closure_subset_iff_isClosed]
    intro y hy
    have hcont : Continuous (fun y : Fin (m + 1) → ℝ => Fin.append x y) :=
      continuous_iff_continuousAt.mpr fun y =>
        (Work.WilE7.Nondrop.fnpAppend_hasFDerivAt x y).continuousAt
    have hsub : (fun y : Fin (m + 1) → ℝ => Fin.append x y) '' F ⊆ absSet T := by
      rintro z ⟨y, hy, rfl⟩
      exact hy
    have happ : Fin.append x y ∈ closure (absSet T) :=
      closure_mono hsub (image_closure_subset_closure_image hcont ⟨y, hy, rfl⟩)
    have hπ : projFirst n (m + 1) (Fin.append x y) = x := Work.WilE7.projFirst_append x y
    exact hclosed _ happ (by rw [hπ]; exact hxC)
  have hFbdd : Bornology.IsBounded F := by
    have hsub : F ⊆ Metric.closedBall (0 : Fin (m + 1) → ℝ) 1 := by
      intro y hy
      rw [Metric.mem_closedBall, dist_zero_right]
      rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
      intro i
      have h1 : Fin.append x y ∈ absSet T := hy
      have h2 := absSet_subset_cubeC T h1 (Fin.natAdd n i)
      rw [Fin.append_right] at h2
      simpa [Real.norm_eq_abs] using h2
    exact Metric.isBounded_closedBall.subset hsub
  have hFcompact : IsCompact F :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨hFclosed, hFbdd⟩
  obtain ⟨y₀, hy₀F, hy₀max⟩ :=
    hFcompact.exists_isMaxOn hne (continuous_apply (Fin.last m)).continuousOn
  -- ## Step 2. The chart of the stratum at the lift of `(x, y₀)`.
  set w₀ : Fin (0 + (n + (m + 1))) → ℝ := absLift x y₀ with hw₀def
  have hy₀ : Fin.append x y₀ ∈ absSet T := hy₀F
  have hw₀X : w₀ ∈ T.X.set := by
    rw [absSet, Set.mem_image] at hy₀
    obtain ⟨w, hw, hweq⟩ := hy₀
    have h1 : w₀ = w := by
      rw [hw₀def, absLift, ← hweq]
      exact append_absPt (0 : Fin 0 → ℝ) w
    rw [h1]
    exact hw
  have hw₀base : basePrLin n (m + 1) w₀ = x := by
    rw [hw₀def]; exact basePrLin_absLift x y₀
  have hw₀vert : verT w₀ = vertCoord y₀ := by
    rw [hw₀def]; exact verT_absLift x y₀
  have hGan : ∀ w : Fin (0 + (n + (m + 1))) → ℝ, AnalyticAt ℝ (eqMap T) w := fun w =>
    analyticAt_eqMap T w
  have hGsurj : (fderiv ℝ (eqMap T) w₀).range = ⊤ := by
    rw [eqMap_eq_fun T]
    exact range_fderiv_good_eq_top T hGood hw₀X
  obtain ⟨γ, V, U, χ, hVopen, hUopen, h0V, hw₀U, hγ0, hγan, hγVU, hGγ, hchart, hInj,
    hγrange, hχan, hχspec⟩ :=
    Work.WilE7.Nondrop.analyticLevelSetChartRange (eqMap T) w₀ hGan hGsurj
  have hG0 : eqMap T w₀ = 0 := eqMap_eq_zero_of_good T hGood hw₀X
  -- the locality clause of `Good` at `w₀`, with the (automatic) base condition removed
  have hgood_ev : ∀ᶠ z in 𝓝 w₀, eqMap T z = 0 → z ∈ T.X.set := by
    have hl := Work.WilE5.Stratum.good_local hGood hw₀X
    filter_upwards [hl] with z hz hG
    exact hz (Subsingleton.elim _ _) (fun a => congrFun hG a)
  -- the set of parameters on which all the chart facts are available
  set W : Set (fderiv ℝ (eqMap T) w₀).ker :=
    {v | v ∈ V ∧ γ v ∈ U ∧ γ v ∈ T.X.set ∧ eqMap T (γ v) = eqMap T w₀ ∧
      AnalyticAt ℝ γ v ∧ AnalyticAt ℝ χ (γ v)} with hWdef
  have hWmem : W ∈ 𝓝 (0 : (fderiv ℝ (eqMap T) w₀).ker) := by
    have hγcont : ContinuousAt γ 0 := hγan.continuousAt
    have hVmem : ∀ᶠ v in 𝓝 (0 : (fderiv ℝ (eqMap T) w₀).ker), v ∈ V :=
      hVopen.mem_nhds h0V
    have hUmem : ∀ᶠ v in 𝓝 0, γ v ∈ U :=
      hγcont.eventually (hUopen.mem_nhds (by rw [hγ0]; exact hw₀U))
    have hXmem : ∀ᶠ v in 𝓝 0, γ v ∈ T.X.set := by
      have hgood' : ∀ᶠ z in 𝓝 (γ 0), eqMap T z = 0 → z ∈ T.X.set := by
        rw [hγ0]; exact hgood_ev
      filter_upwards [hVmem, hγcont.eventually hgood'] with v hvV hv
      exact hv ((hGγ v hvV).trans hG0)
    have hGmem : ∀ᶠ v in 𝓝 0, eqMap T (γ v) = eqMap T w₀ := by
      filter_upwards [hVmem] with v hvV; exact hGγ v hvV
    have hγan_ev : ∀ᶠ v in 𝓝 0, AnalyticAt ℝ γ v := hγan.eventually_analyticAt
    have hχan_ev : ∀ᶠ v in 𝓝 0, AnalyticAt ℝ χ (γ v) := by
      have hχ' : ∀ᶠ z in 𝓝 (γ 0), AnalyticAt ℝ χ z := by
        rw [hγ0]; exact hχan.eventually_analyticAt
      exact hγcont.eventually hχ'
    rw [hWdef]
    filter_upwards [hVmem, hUmem, hXmem, hGmem, hγan_ev, hχan_ev]
      with v h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  have hWan : ∀ v ∈ W, AnalyticAt ℝ γ v := fun v hv => hv.2.2.2.2.1
  have hWX : ∀ v ∈ W, γ v ∈ T.X.set := fun v hv => hv.2.2.1
  have hWV : ∀ v ∈ W, v ∈ V := fun v hv => hv.1
  have h0W : (0 : (fderiv ℝ (eqMap T) w₀).ker) ∈ W := by
    rw [hWdef]
    refine ⟨h0V, hγVU 0 h0V, ?_, ?_, hγan, ?_⟩
    · rw [hγ0]; exact hw₀X
    · rw [hγ0]
    · rw [hγ0]; exact hχan
  -- ## Step 3. Chart facts.
  have hχγ : ∀ u ∈ V, χ (γ u) = u := by
    intro u hu
    obtain ⟨h1, h2⟩ := hχspec (γ u) (hγVU u hu) (hGγ u hu)
    exact (hInj hu h1 h2.symm).symm
  have hdγ_inj : ∀ v ∈ W, Function.Injective (fderiv ℝ γ v) := by
    intro v hv
    obtain ⟨hvV, hvU, hvX, hvG, hγanv, hχanv⟩ := hv
    have hev : (fun u => χ (γ u)) =ᶠ[𝓝 v] id := by
      filter_upwards [hVopen.mem_nhds hvV] with u hu
      exact hχγ u hu
    have hfd : fderiv ℝ (fun u => χ (γ u)) v = ContinuousLinearMap.id ℝ _ := by
      rw [hev.fderiv_eq]
      exact fderiv_id
    have hcomp : fderiv ℝ (fun u => χ (γ u)) v
        = (fderiv ℝ χ (γ v)).comp (fderiv ℝ γ v) :=
      (hχanv.hasStrictFDerivAt.hasFDerivAt.comp v
        hγanv.hasStrictFDerivAt.hasFDerivAt).fderiv
    have hkey : (fderiv ℝ χ (γ v)).comp (fderiv ℝ γ v) = ContinuousLinearMap.id ℝ _ := by
      rw [← hcomp, hfd]
    intro a b hab
    have h1 : a - b = 0 := by
      have h2 := congrArg
        (fun (L : (fderiv ℝ (eqMap T) w₀).ker →L[ℝ] (fderiv ℝ (eqMap T) w₀).ker) =>
          L (a - b)) hkey
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, map_sub, hab,
        sub_self, map_zero] at h2
      exact h2.symm
    exact sub_eq_zero.mp h1
  have him_le : ∀ v ∈ W,
      (fderiv ℝ γ v).range ≤ (fderiv ℝ (eqMap T) (γ v)).ker := by
    intro v hv
    obtain ⟨hvV, hvU, hvX, hvG, hγanv, hχanv⟩ := hv
    have hev : (fun u => eqMap T (γ u)) =ᶠ[𝓝 v] (fun _ => eqMap T w₀) := by
      filter_upwards [hVopen.mem_nhds hvV] with u hu
      exact hGγ u hu
    have hcomp : fderiv ℝ (fun u => eqMap T (γ u)) v
        = (fderiv ℝ (eqMap T) (γ v)).comp (fderiv ℝ γ v) :=
      ((hGan (γ v)).hasStrictFDerivAt.hasFDerivAt.comp v
        hγanv.hasStrictFDerivAt.hasFDerivAt).fderiv
    have hzero : (fderiv ℝ (eqMap T) (γ v)).comp (fderiv ℝ γ v) = 0 := by
      rw [← hcomp, hev.fderiv_eq]
      simp
    intro w hw
    obtain ⟨u, rfl⟩ := hw
    rw [LinearMap.mem_ker]
    have h2 := congrArg
      (fun (L : (fderiv ℝ (eqMap T) w₀).ker →L[ℝ] (Fin T.j → ℝ)) => L u) hzero
    simpa using h2
  -- dimensions: `dim ker (d eqMap) = n + (m+1) - T.j` on the chart image
  have hkerdim : ∀ v ∈ W,
      Module.finrank ℝ (fderiv ℝ (eqMap T) (γ v)).ker = n + (m + 1) - T.j := by
    intro v hv
    have htop : (fderiv ℝ (eqMap T) (γ v)).range = ⊤ := by
      rw [eqMap_eq_fun T]
      exact range_fderiv_good_eq_top T hGood (hWX v hv)
    have h1 := LinearMap.finrank_range_add_finrank_ker
      ((fderiv ℝ (eqMap T) (γ v) : (Fin (0 + (n + (m + 1))) → ℝ) →L[ℝ] (Fin T.j → ℝ)) :
        (Fin (0 + (n + (m + 1))) → ℝ) →ₗ[ℝ] (Fin T.j → ℝ))
    rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card,
      Module.finrank_fintype_fun_eq_card] at h1
    simp only [Fintype.card_fin] at h1
    omega
  have hker_w₀ : Module.finrank ℝ (fderiv ℝ (eqMap T) w₀).ker = n + (m + 1) - T.j := by
    have h1 := LinearMap.finrank_range_add_finrank_ker
      ((fderiv ℝ (eqMap T) w₀ : (Fin (0 + (n + (m + 1))) → ℝ) →L[ℝ] (Fin T.j → ℝ)) :
        (Fin (0 + (n + (m + 1))) → ℝ) →ₗ[ℝ] (Fin T.j → ℝ))
    rw [hGsurj, finrank_top, Module.finrank_fintype_fun_eq_card,
      Module.finrank_fintype_fun_eq_card] at h1
    simp only [Fintype.card_fin] at h1
    omega
  -- the tangent space of the chart image is exactly the kernel of the defining equations
  have him_eq : ∀ v ∈ W, (fderiv ℝ γ v).range = (fderiv ℝ (eqMap T) (γ v)).ker := by
    intro v hv
    have hle := him_le v hv
    have h1 : Module.finrank ℝ (fderiv ℝ γ v).range = n + (m + 1) - T.j := by
      rw [LinearMap.finrank_range_of_inj (hdγ_inj v hv), hker_w₀]
    exact Submodule.eq_of_le_of_finrank_eq hle (h1.trans (hkerdim v hv).symm)
  -- the rank of the base projection on the tangent space
  have hprojRank : ∀ v ∈ W,
      Module.finrank ℝ ↥((fderiv ℝ (eqMap T) (γ v)).ker.map (basePrLin n (m + 1)))
        = n + (m + 1) - T.j - 1 := by
    intro v hv
    have h1 : projRank T (γ v) = Module.finrank ℝ
        ↥((fderiv ℝ (eqMap T) (γ v)).ker.map (basePrLin n (m + 1))) := by
      show Module.finrank ℝ ↥((jac T (γ v)).ker.map (basePrLin n (m + 1))) = _
      rw [jac_eq_fderiv]
      rfl
    rw [← h1]
    exact hvert (γ v) (hWX v hv)
  -- `himm` gives injectivity of `π_{n+1}` on the tangent space at `w₀`
  have himm_inj : ∀ v ∈ (fderiv ℝ (eqMap T) w₀).ker,
      projTopLin n m (absPtLin (n + (m + 1)) v) = 0 → v = 0 := by
    intro v hv hv0
    have h1 : Module.finrank ℝ
        ↥(Submodule.map (projTopLin n m ∘ₗ absPtLin (n + (m + 1)))
          (fderiv ℝ (eqMap T) w₀).ker) = n + (m + 1) - T.j := by
      have h := himm w₀ hw₀X
      rwa [jac_eq_fderiv] at h
    have h3 : Module.finrank ℝ
        ↥(Submodule.map (projTopLin n m ∘ₗ absPtLin (n + (m + 1)))
          (fderiv ℝ (eqMap T) w₀).ker) = Module.finrank ℝ (fderiv ℝ (eqMap T) w₀).ker := by
      rw [h1, hker_w₀]
    exact eq_zero_of_mem_of_apply_eq_zero _ h3 hv hv0
  -- ## Step 4. A non-zero `v₀` killed by the base projection, not by `verT`.
  set Sg : Submodule ℝ (Fin (0 + (n + (m + 1))) → ℝ) :=
    (fderiv ℝ (eqMap T) w₀).ker ⊓ (basePrLin n (m + 1)).ker with hSgdef
  have hSg_finrank : Module.finrank ℝ Sg = 1 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker
      ((basePrLin n (m + 1)).domRestrict (fderiv ℝ (eqMap T) w₀).ker)
    rw [LinearMap.range_domRestrict] at h1
    have h2 : Module.finrank ℝ
        ↥(Submodule.map (basePrLin n (m + 1)) (fderiv ℝ (eqMap T) w₀).ker)
        = n + (m + 1) - T.j - 1 := by
      have h3 : Module.finrank ℝ
          ↥(Submodule.map (basePrLin n (m + 1)) (fderiv ℝ (eqMap T) w₀).ker)
          = projRank T w₀ := by
        show _ = Module.finrank ℝ ↥((jac T w₀).ker.map (basePrLin n (m + 1)))
        rw [jac_eq_fderiv]
        rfl
      rw [h3, hvert w₀ hw₀X]
    have h4 : Module.finrank ℝ ↥((basePrLin n (m + 1)).domRestrict
        (fderiv ℝ (eqMap T) w₀).ker).ker = Module.finrank ℝ Sg := by
      rw [LinearMap.ker_domRestrict,
        ← Submodule.finrank_map_subtype_eq (fderiv ℝ (eqMap T) w₀).ker
          (Submodule.comap (fderiv ℝ (eqMap T) w₀).ker.subtype (basePrLin n (m + 1)).ker),
        Submodule.map_comap_subtype, hSgdef]
    rw [h2, h4, hker_w₀] at h1
    omega
  have hSg_ne_bot : Sg ≠ ⊥ := by
    intro h
    have h1 := hSg_finrank
    rw [h] at h1
    have h2 : Module.finrank ℝ (⊥ : Submodule ℝ (Fin (0 + (n + (m + 1))) → ℝ)) = 0 :=
      Submodule.finrank_eq_zero.mpr rfl
    rw [h2] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨v₀, hv₀Sg, hv₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hSg_ne_bot
  have hv₀kerG : v₀ ∈ (fderiv ℝ (eqMap T) w₀).ker := hv₀Sg.1
  have hv₀kerB : v₀ ∈ (basePrLin n (m + 1)).ker := hv₀Sg.2
  have hbasev₀ : basePrLin n (m + 1) v₀ = 0 := LinearMap.mem_ker.mp hv₀kerB
  have hv₀vert : verT v₀ ≠ 0 := by
    intro h0
    refine hv₀ne ?_
    refine himm_inj v₀ hv₀kerG ?_
    ext i
    refine Fin.lastCases ?_ ?_ i
    · rw [projTopLin_absPtLin_last]
      exact h0
    · intro i'
      change Fin.init (projTopLin n m (absPtLin (n + (m + 1)) v₀)) i' = 0
      rw [projTopLin_absPtLin_init, hbasev₀]
      rfl
  -- ## Step 5. Transfer to `ℝ^q` (`q = dim ker (d eqMap)`) and apply the constant-rank
  -- implicit curve theorem.
  set q : ℕ := n + (m + 1) - T.j with hqdef
  have hq1 : 1 ≤ q := by omega
  let e : (Fin q → ℝ) ≃ₗ[ℝ] (fderiv ℝ (eqMap T) w₀).ker :=
    LinearEquiv.ofFinrankEq (Fin q → ℝ) (fderiv ℝ (eqMap T) w₀).ker (by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, hqdef]
      exact hker_w₀.symm)
  let eclm : (Fin q → ℝ) →L[ℝ] (fderiv ℝ (eqMap T) w₀).ker :=
    ((e : (Fin q → ℝ) →ₗ[ℝ] (fderiv ℝ (eqMap T) w₀).ker)).toContinuousLinearMap
  let Γ : (Fin q → ℝ) → (Fin (0 + (n + (m + 1))) → ℝ) := fun u => γ (e u)
  let ψ : (Fin q → ℝ) → (Fin n → ℝ) := fun u => basePrLin n (m + 1) (Γ u) - x
  have heclm : ∀ u : Fin q → ℝ, eclm u = e u := fun u => rfl
  have hWq : e ⁻¹' W ∈ 𝓝 (0 : Fin q → ℝ) :=
    eclm.continuous.continuousAt.preimage_mem_nhds (by simpa using hWmem)
  have h0Wq : (0 : Fin q → ℝ) ∈ e ⁻¹' W := by
    show e 0 ∈ W
    rw [map_zero]
    exact h0W
  -- the derivative of `Γ = γ ∘ e`
  have hΓdiff : ∀ u ∈ e ⁻¹' W, HasFDerivAt Γ ((fderiv ℝ γ (e u)).comp eclm) u := by
    intro u hu
    have heu : e u ∈ W := hu
    have h1 : HasFDerivAt γ (fderiv ℝ γ (e u)) (e u) :=
      (hWan (e u) heu).hasStrictFDerivAt.hasFDerivAt
    exact h1.comp u eclm.hasFDerivAt
  have hψder : ∀ u ∈ e ⁻¹' W, fderiv ℝ ψ u
      = (basePrLin n (m + 1)).toContinuousLinearMap.comp (fderiv ℝ Γ u) := by
    intro u hu
    have hd : HasFDerivAt Γ (fderiv ℝ Γ u) u := (hΓdiff u hu).fderiv.symm ▸ hΓdiff u hu
    have h1 : HasFDerivAt (fun u : Fin q → ℝ => basePrLin n (m + 1) (Γ u))
        ((basePrLin n (m + 1)).toContinuousLinearMap.comp (fderiv ℝ Γ u)) u :=
      ((basePrLin n (m + 1)).toContinuousLinearMap.hasFDerivAt).comp u hd
    have h2 : HasFDerivAt ψ
        ((basePrLin n (m + 1)).toContinuousLinearMap.comp (fderiv ℝ Γ u)) u := by
      have h3 := h1.sub_const x
      simpa [ψ] using h3
    exact h2.fderiv
  have hψan : ∀ u ∈ e ⁻¹' W, AnalyticAt ℝ ψ u := by
    intro u hu
    have heu : e u ∈ W := hu
    have h1 : AnalyticAt ℝ Γ u := (hWan (e u) heu).comp (eclm.analyticAt u)
    have h2 : AnalyticAt ℝ (fun u : Fin q → ℝ => basePrLin n (m + 1) (Γ u)) u :=
      ((basePrLin n (m + 1)).toContinuousLinearMap.analyticAt _).comp h1
    exact h2.sub analyticAt_const
  have hψrank : ∀ u ∈ e ⁻¹' W, Module.finrank ℝ (fderiv ℝ ψ u).range = q - 1 := by
    intro u hu
    have heu : e u ∈ W := hu
    have hM : (fderiv ℝ ψ u).range
        = ((fderiv ℝ γ (e u)).range).map (basePrLin n (m + 1)) := by
      rw [hψder u hu, (hΓdiff u hu).fderiv]
      refine le_antisymm ?_ ?_
      · rintro z ⟨v, rfl⟩
        exact ⟨(fderiv ℝ γ (e u)) (eclm v), ⟨eclm v, rfl⟩, rfl⟩
      · rintro z ⟨w, ⟨v, rfl⟩, rfl⟩
        refine ⟨e.symm v, ?_⟩
        show (basePrLin n (m + 1)) ((fderiv ℝ γ (e u)) (eclm (e.symm v)))
          = (basePrLin n (m + 1)) ((fderiv ℝ γ (e u)) v)
        rw [heclm (e.symm v), e.apply_symm_apply]
    rw [hM, him_eq (e u) heu]
    exact hprojRank (e u) heu
  have hψ0 : ψ 0 = 0 := by
    simp only [ψ, Γ, map_zero, hγ0, hw₀base, sub_self]
  -- the direction `vh` with `dΓ 0 vh = v₀`
  have hΓrange : (fderiv ℝ Γ 0).range = (fderiv ℝ (eqMap T) w₀).ker := by
    have h1 : (fderiv ℝ Γ 0).range = (fderiv ℝ γ 0).range := by
      have h0 : fderiv ℝ Γ 0 = (fderiv ℝ γ 0).comp eclm := by
        have h := (hΓdiff 0 h0Wq).fderiv
        rw [show e 0 = 0 from map_zero e] at h
        exact h
      rw [h0]
      refine le_antisymm ?_ ?_
      · rintro z ⟨v, rfl⟩
        exact ⟨e v, rfl⟩
      · rintro z ⟨w, rfl⟩
        refine ⟨e.symm w, ?_⟩
        show (fderiv ℝ γ 0) (eclm (e.symm w)) = (fderiv ℝ γ 0) w
        rw [heclm (e.symm w), e.apply_symm_apply]
    rw [h1]
    exact hγrange
  obtain ⟨vh, hvh⟩ : ∃ vh : Fin q → ℝ, fderiv ℝ Γ 0 vh = v₀ := by
    have hmem : v₀ ∈ (fderiv ℝ Γ 0).range := by
      rw [hΓrange]
      exact hv₀kerG
    exact LinearMap.mem_range.mp hmem
  have hψvh : fderiv ℝ ψ 0 vh = 0 := by
    rw [hψder 0 h0Wq, ContinuousLinearMap.comp_apply, hvh]
    exact hbasev₀
  -- the implicit curve
  obtain ⟨c, hc0, hcder, hcev⟩ :=
    exists_implicit_curve_of_constant_rank hq1 ψ (e ⁻¹' W) hWq hψan hψrank hψ0 vh hψvh
  -- ## Step 6. The curve contradicts the maximality of `y₀`.
  have hcevW : ∀ᶠ t in 𝓝 (0 : ℝ), c t ∈ e ⁻¹' W :=
    (hcder.continuousAt).preimage_mem_nhds (by rw [hc0]; exact hWq)
  obtain ⟨ε, hεpos, hε⟩ := Metric.eventually_nhds_iff.mp (hcev.and hcevW)
  let i₀ : Fin (0 + (n + (m + 1))) := Fin.natAdd 0 (Fin.natAdd n (Fin.last m))
  have hv₀i : v₀ i₀ ≠ 0 := hv₀vert
  have hder : HasDerivAt (fun t : ℝ => Γ (c t) i₀) (v₀ i₀) 0 := by
    have hΓc : HasDerivAt (fun t : ℝ => Γ (c t)) v₀ 0 := by
      have hd : HasFDerivAt Γ ((fderiv ℝ γ (e 0)).comp eclm) (c 0) := by
        rw [hc0]
        exact hΓdiff 0 h0Wq
      have h1 : HasDerivAt (fun t : ℝ => Γ (c t)) (((fderiv ℝ γ (e 0)).comp eclm) vh) 0 :=
        hd.comp_hasDerivAt 0 hcder
      have h2 : ((fderiv ℝ γ (e 0)).comp eclm) vh = v₀ := by
        rw [← (hΓdiff 0 h0Wq).fderiv]
        exact hvh
      rw [h2] at h1
      exact h1
    exact (ContinuousLinearMap.proj i₀).hasFDerivAt.comp_hasDerivAt 0 hΓc
  obtain ⟨t, htε, hgt⟩ := exists_lt_of_hasDerivAt_ne hder hv₀i hεpos
  have ht : ψ (c t) = 0 ∧ c t ∈ e ⁻¹' W := hε (by rw [Real.dist_eq, sub_zero]; exact htε)
  have hztX : Γ (c t) ∈ T.X.set := hWX (e (c t)) ht.2
  have hzbase : basePrLin n (m + 1) (Γ (c t)) = x := sub_eq_zero.mp ht.1
  set yt : Fin (m + 1) → ℝ := projSnd n (m + 1) (absPt (Γ (c t))) with hytdef
  have hytF : yt ∈ fiber (absSet T) x := by
    have h1 : absPt (Γ (c t)) = Fin.append x (projSnd n (m + 1) (absPt (Γ (c t)))) := by
      rw [← hzbase, ← projFirst_absPt (Γ (c t))]
      exact (Work.WilE7.Nondrop.fnpAppend_proj _).symm
    show Fin.append x yt ∈ absSet T
    rw [hytdef, ← h1]
    exact ⟨Γ (c t), hztX, rfl⟩
  have hytval : vertCoord yt = Γ (c t) i₀ := by
    show projSnd n (m + 1) (absPt (Γ (c t))) (Fin.last m) = Γ (c t) i₀
    rw [show projSnd n (m + 1) (absPt (Γ (c t))) (Fin.last m)
      = absPt (Γ (c t)) (Fin.natAdd n (Fin.last m)) from rfl, absPt_apply_natAdd]
  have hw₀i : vertCoord y₀ = w₀ i₀ := by
    rw [← hw₀vert]
    rfl
  have hΓ0i : Γ (c 0) i₀ = w₀ i₀ := by
    show γ (e (c 0)) i₀ = w₀ i₀
    rw [hc0, map_zero, hγ0]
  have hcontr : vertCoord yt ≤ vertCoord y₀ := hy₀max hytF
  have hle : Γ (c t) i₀ ≤ Γ (c 0) i₀ := by
    rw [← hytval, hΓ0i, ← hw₀i]
    exact hcontr
  exact absurd hle (not_le.mpr hgt)

end Work.WilE7.CoreStep
