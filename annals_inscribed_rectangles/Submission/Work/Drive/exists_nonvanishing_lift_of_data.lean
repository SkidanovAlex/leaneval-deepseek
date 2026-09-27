import Mathlib
import Submission.Work.Drive.projCharted
import Submission.Work.Drive.ProjectiveTopology
import Submission.Work.Drive.ProjectiveChartDefs
import Submission.Work.Drive.exists_contDiff_extension_box
import Submission.Work.Drive.exists_contDiff_flattening
import Submission.Work.Drive.exists_localModel_projCharted
import Submission.Work.Drive.isCoveringMap_projOfUnitSphere
import Submission.Work.Drive.contMDiffAt_projCharted_iff
import Submission.Work.ManifoldParity.exists_parallel_smooth_field

/-!
# A globally smooth, nowhere vanishing lift of a smooth-on-a-box map into `ℝP³`

If `h : ℝ² → ℝP³` is `C^∞` (Whitney) on the closed box `[a,b] × [c,d]` (`a < b`, `c < d`), and
if `h` is *locally* the restriction of a genuinely smooth map (hypothesis `hloc`, which is
`Work.Drive.exists_localModel_projCharted`), then there is a globally `C^∞`, nowhere vanishing
`V : ℝ² → ℝ⁴` whose projective class agrees with `h` on the box.

The proof has four steps.

* The box is convex, hence contractible and locally path connected, so the covering map
  `projOfUnitSphere : S³ → ℝP³` (`hcov`) lifts the restriction `h|_box` to a continuous,
  nowhere vanishing `V₀ : box → ℝ⁴` with `[V₀ x] = h x` on the box
  (this is `exists_continuous_lift_box`).
* `V₀` is extended to a total function `U₀ : ℝ² → ℝ⁴` by composing with the coordinatewise clamp
  onto the box, and the local smooth models of `hloc`, pushed through the projective charts, are
  glued by a partition of unity into a global smooth `V` which is a nowhere vanishing multiple of
  `U₀` on the box (`exists_parallel_smooth_field4`, an adaptation of
  `Work.ManifoldParity.exists_parallel_smooth_field` to the vector-valued target `ℝ⁴`).
* `V` is smooth and nonvanishing on the box, so `{V ≠ 0}` is an open neighbourhood of the compact
  box; a thickening of the box of some radius `δ` lies in it.
* The plane is flattened into that thickening by a smooth map `Ψ` which is the identity on the box
  (`exists_contDiff_flattening_box`), and the final lift is `V ∘ Ψ`.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff LinearAlgebra.Projectivization Topology
open scoped InnerProductSpace
open Set Filter

noncomputable section

set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000

/-! ## Euclidean helpers on `ℝ²` -/

private lemma eucl_two_norm_le_coords (z : EuclideanSpace ℝ (Fin 2)) :
    ‖z‖ ≤ |z 0| + |z 1| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  nlinarith [sq_abs (z 0), sq_abs (z 1), abs_nonneg (z 0), abs_nonneg (z 1),
    sq_nonneg (|z 0| + |z 1|)]

/-! ## The box and its clamp -/

/-- The closed box `[a,b] × [c,d]` inside `ℝ²`. -/
private def boxSet (a b c d : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {q | q 0 ∈ Set.Icc a b ∧ q 1 ∈ Set.Icc c d}

/-- The coordinatewise clamp of a point of `ℝ²` into the box `[a,b] × [c,d]`. -/
private def clampPt (a b c d : ℝ) (q : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then max a (min b (q 0)) else max c (min d (q 1)))

private lemma clampPt_apply_zero (a b c d : ℝ) (q : EuclideanSpace ℝ (Fin 2)) :
    clampPt a b c d q 0 = max a (min b (q 0)) := by simp [clampPt]

private lemma clampPt_apply_one (a b c d : ℝ) (q : EuclideanSpace ℝ (Fin 2)) :
    clampPt a b c d q 1 = max c (min d (q 1)) := by simp [clampPt]

private lemma clampPt_mem (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (q : EuclideanSpace ℝ (Fin 2)) : clampPt a b c d q ∈ boxSet a b c d := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [clampPt_apply_zero]; exact le_max_left _ _
  · rw [clampPt_apply_zero]; exact max_le hab (min_le_left _ _)
  · rw [clampPt_apply_one]; exact le_max_left _ _
  · rw [clampPt_apply_one]; exact max_le hcd (min_le_left _ _)

private lemma clampPt_eq_self {a b c d : ℝ} {q : EuclideanSpace ℝ (Fin 2)}
    (hq : q ∈ boxSet a b c d) : clampPt a b c d q = q := by
  have hq0 : q 0 ∈ Set.Icc a b := hq.1
  have hq1 : q 1 ∈ Set.Icc c d := hq.2
  have hfun : (fun i : Fin 2 => if i = 0 then max a (min b (q 0)) else max c (min d (q 1)))
      = q.ofLp := by
    funext i
    by_cases h : i = 0
    · rw [if_pos h, h, min_eq_right hq0.2, max_eq_right hq0.1]
    · have h1 : i = 1 := by revert h; revert i; decide
      rw [if_neg h, h1, min_eq_right hq1.2, max_eq_right hq1.1]
  calc clampPt a b c d q = WithLp.toLp 2 (fun i : Fin 2 =>
        if i = 0 then max a (min b (q 0)) else max c (min d (q 1))) := rfl
    _ = WithLp.toLp 2 q.ofLp := by rw [hfun]
    _ = q := WithLp.toLp_ofLp 2 q

private lemma continuous_clampPt (a b c d : ℝ) : Continuous (clampPt a b c d) := by
  let e := (EuclideanSpace.equiv (Fin 2) ℝ).trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  have h : clampPt a b c d = fun q : EuclideanSpace ℝ (Fin 2) =>
      e.symm (max a (min b (q 0)), max c (min d (q 1))) := by
    funext q
    ext i
    fin_cases i <;> simp [clampPt, e]
  rw [h]; fun_prop

private lemma boxSet_nonempty (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) :
    (boxSet a b c d).Nonempty :=
  ⟨clampPt a b c d 0, clampPt_mem a b c d hab hcd 0⟩

/-- The box is compact. -/
private lemma isCompact_boxSet (a b c d : ℝ) : IsCompact (boxSet a b c d) := by
  let e := (EuclideanSpace.equiv (Fin 2) ℝ).trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  have h : boxSet a b c d = e ⁻¹' (Set.Icc a b ×ˢ Set.Icc c d) := by
    ext q
    simp only [boxSet, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod, Set.mem_Icc]
    exact Iff.rfl
  rw [h]
  exact (Homeomorph.isCompact_preimage e.toHomeomorph).mpr (isCompact_Icc.prod isCompact_Icc)

/-! ## Step 1: the continuous nowhere vanishing lift of `h` on the box -/

/-- The box is convex. -/
private lemma convex_boxSet (a b c d : ℝ) : Convex ℝ (boxSet a b c d) := by
  intro x hx y hy p q hp hq hpq
  constructor
  · have h := (convex_Icc a b) hx.1 hy.1 hp hq hpq
    have hxy : (p • x + q • y) 0 = p * (x 0) + q * (y 0) := by
      simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rwa [hxy]
  · have h := (convex_Icc c d) hx.2 hy.2 hp hq hpq
    have hxy : (p • x + q • y) 1 = p * (x 1) + q * (y 1) := by
      simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rwa [hxy]

/-- **The continuous nowhere vanishing lift of `h` on the box**, obtained from the covering map
`projOfUnitSphere : S³ → ℝP³` and the contractibility of the box. -/
private theorem exists_continuous_lift_box (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    {h : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (EuclideanSpace ℝ (Fin 4))}
    (hc : ContinuousOn h (boxSet a b c d))
    (hcov : IsCoveringMap (Work.Drive.projOfUnitSphere (n := 3))) :
    ∃ V : {q : EuclideanSpace ℝ (Fin 2) // q ∈ boxSet a b c d} → EuclideanSpace ℝ (Fin 4),
      Continuous V ∧ (∀ x, V x ≠ 0) ∧
      (∀ x (hV : V x ≠ 0), Projectivization.mk ℝ (V x) hV = h x) := by
  have hconv : Convex ℝ (boxSet a b c d) := convex_boxSet a b c d
  have hpt : clampPt a b c d 0 ∈ boxSet a b c d := clampPt_mem a b c d hab.le hcd.le 0
  haveI : ContractibleSpace {q : EuclideanSpace ℝ (Fin 2) // q ∈ boxSet a b c d} :=
    hconv.contractibleSpace ⟨_, hpt⟩
  haveI : LocallyPathConnectedSpace {q : EuclideanSpace ℝ (Fin 2) // q ∈ boxSet a b c d} :=
    hconv.locallyPathConnectedSpace
  let f : C({q : EuclideanSpace ℝ (Fin 2) // q ∈ boxSet a b c d},
      Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) :=
    ⟨fun x => h x, hc.domRestrict⟩
  let x₀ : {q : EuclideanSpace ℝ (Fin 2) // q ∈ boxSet a b c d} := ⟨clampPt a b c d 0, hpt⟩
  obtain ⟨e₀, he₀⟩ := Work.Drive.surjective_projOfUnitSphere (h x₀)
  obtain ⟨F, ⟨hF0, hFlift⟩, -⟩ := hcov.existsUnique_continuousMap_lifts f x₀ e₀ he₀
  refine ⟨fun x => (F x).1, continuous_subtype_val.comp F.continuous, ?_, ?_⟩
  · intro x
    have h : ‖(F x).1‖ = 1 := Work.Drive.norm_coe_unitSphere (F x)
    exact norm_ne_zero_iff.mp (by rw [h]; exact one_ne_zero)
  · intro x hV
    have h1 : Work.Drive.projOfUnitSphere (F x) = h x := congr_fun hFlift x
    exact (Work.Drive.projectivizationMk_congr ℝ (EuclideanSpace ℝ (Fin 4))
      (v := (F x).1)).symm.trans h1

/-! ## Step 2: the flattening of the plane onto a thickening of the box -/

/-- **A smooth flattening of `ℝ²` into a thickening of the box.**  For `a < b`, `c < d` and
`ε > 0` there is a globally `C^∞` map of `ℝ²` which is the identity on the box and whose values all
lie at distance `< ε` from the box. -/
private theorem exists_contDiff_flattening_box (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Ψ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ ∧
      (∀ x, x ∈ boxSet a b c d → Ψ x = x) ∧
      ∀ x, ∃ y : EuclideanSpace ℝ (Fin 2), y ∈ boxSet a b c d ∧ dist (Ψ x) y < ε := by
  obtain ⟨φ₁, hφ₁, hid₁, him₁⟩ :=
    Work.Drive.exists_contDiff_flattening a b hab (ε/4) (by linarith)
  obtain ⟨φ₂, hφ₂, hid₂, him₂⟩ :=
    Work.Drive.exists_contDiff_flattening c d hcd (ε/4) (by linarith)
  let e := (EuclideanSpace.equiv (Fin 2) ℝ).trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  refine ⟨fun x => e.symm (φ₁ ((e x).1), φ₂ ((e x).2)), ?_, ?_, ?_⟩
  · fun_prop
  · intro x hx
    change e.symm (φ₁ ((e x).1), φ₂ ((e x).2)) = x
    have h1 : φ₁ ((e x).1) = (e x).1 := hid₁ ((e x).1) hx.1
    have h2 : φ₂ ((e x).2) = (e x).2 := hid₂ ((e x).2) hx.2
    rw [h1, h2]
    have : ((e x).1, (e x).2) = e x := rfl
    rw [this, e.symm_apply_apply]
  · intro x
    set u := φ₁ ((e x).1) with hu
    set v := φ₂ ((e x).2) with hv
    have h1 : a - ε/4 < u ∧ u < b + ε/4 := him₁ _
    have h2 : c - ε/4 < v ∧ v < d + ε/4 := him₂ _
    refine ⟨e.symm (max a (min b u), max c (min d v)), ?_, ?_⟩
    · have hy0 : (e.symm (max a (min b u), max c (min d v))) 0 = max a (min b u) := by simp [e]
      have hy1 : (e.symm (max a (min b u), max c (min d v))) 1 = max c (min d v) := by simp [e]
      refine ⟨?_, ?_⟩
      · rw [hy0]
        exact ⟨le_max_left _ _, by
          rcases le_or_gt u b with h | h
          · rw [min_eq_right h]; exact max_le hab.le h
          · rw [min_eq_left h.le]; exact max_le hab.le le_rfl⟩
      · rw [hy1]
        exact ⟨le_max_left _ _, by
          rcases le_or_gt v d with h | h
          · rw [min_eq_right h]; exact max_le hcd.le h
          · rw [min_eq_left h.le]; exact max_le hcd.le le_rfl⟩
    · rw [dist_eq_norm]
      have hsub0 : ((e.symm (φ₁ ((e x).1), φ₂ ((e x).2))
          - e.symm (max a (min b u), max c (min d v))) 0) = u - max a (min b u) := by
        simp [e, hu, PiLp.sub_apply]
      have hsub1 : ((e.symm (φ₁ ((e x).1), φ₂ ((e x).2))
          - e.symm (max a (min b u), max c (min d v))) 1) = v - max c (min d v) := by
        simp [e, hv, PiLp.sub_apply]
      have hb1 : |u - max a (min b u)| < ε/4 := by
        rcases le_or_gt u b with h | h
        · rw [min_eq_right h]
          rcases le_or_gt a u with h2 | h2
          · rw [max_eq_right h2, sub_self, abs_zero]; linarith
          · rw [max_eq_left h2.le, abs_of_nonpos (by linarith)]; linarith
        · rw [min_eq_left h.le, max_eq_right hab.le, abs_of_pos (by linarith)]; linarith
      have hb2 : |v - max c (min d v)| < ε/4 := by
        rcases le_or_gt v d with h | h
        · rw [min_eq_right h]
          rcases le_or_gt c v with h2 | h2
          · rw [max_eq_right h2, sub_self, abs_zero]; linarith
          · rw [max_eq_left h2.le, abs_of_nonpos (by linarith)]; linarith
        · rw [min_eq_left h.le, max_eq_right hcd.le, abs_of_pos (by linarith)]; linarith
      calc ‖(e.symm (φ₁ ((e x).1), φ₂ ((e x).2))
            - e.symm (max a (min b u), max c (min d v)))‖
          ≤ |((e.symm (φ₁ ((e x).1), φ₂ ((e x).2))
              - e.symm (max a (min b u), max c (min d v))) 0)|
            + |((e.symm (φ₁ ((e x).1), φ₂ ((e x).2))
              - e.symm (max a (min b u), max c (min d v))) 1)| := eucl_two_norm_le_coords _
        _ = |u - max a (min b u)| + |v - max c (min d v)| := by rw [hsub0, hsub1]
        _ < ε/4 + ε/4 := add_lt_add hb1 hb2
        _ < ε := by linarith

/-! ## Step 3: the local smooth nonzero lifts coming from the projective charts -/

/-- **A smooth nonvanishing vector lift near a point, from a smooth map into `ℝP³`.**  If `H` is
`C^∞` on an open `U` for the transparent projective structure, then near every point of `U` it is
the projective class of a smooth nowhere vanishing vector field. -/
private lemma exists_chart_lift
    {H : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (EuclideanSpace ℝ (Fin 4))}
    {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsOpen U)
    (hH : letI := Work.Drive.projCharted 3
      ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞) H U)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ U) :
    ∃ (V : Set (EuclideanSpace ℝ (Fin 2))) (L : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4)),
      IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) L V ∧
      (∀ y ∈ V, L y ≠ 0) ∧
      ∀ y ∈ V, ∃ hL : L y ≠ 0, Projectivization.mk ℝ (L y) hL = H y := by
  letI := Work.Drive.projCharted 3
  haveI hman : IsManifold (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) := Work.Drive.isManifold_projCharted 3
  obtain ⟨i, hi⟩ := Work.Drive.exists_mem_projChartSource (H x)
  have hsrc_open : IsOpen (Work.Drive.projChartSource i) := by
    rw [← Work.Drive.projChart_source]; exact (Work.Drive.projChart i).open_source
  have hcont : ContinuousAt H x := hH.continuousOn.continuousAt (hU.mem_nhds hx)
  have hmem : U ∩ H ⁻¹' (Work.Drive.projChartSource i) ∈ 𝓝 x :=
    Filter.inter_mem (hU.mem_nhds hx) (hcont.preimage_mem_nhds (hsrc_open.mem_nhds hi))
  obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp hmem
  have hLsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => Work.Drive.projSection i (Work.Drive.projChartMap i (H z))) V := by
    have hgpt : ∀ z ∈ V, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w => Work.Drive.projChartMap i (H w)) z := by
      intro z hz
      have h1 : ContMDiffAt (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun w => Work.Drive.projChartMap i (H w)) z :=
        ((Work.Drive.contMDiffAt_projCharted_iff H z i (hVsub hz).2).mp
          (hH.contMDiffAt (hU.mem_nhds (hVsub hz).1))).2
      exact contMDiffAt_iff_contDiffAt.mp h1
    have hgsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z => Work.Drive.projChartMap i (H z)) V := fun z hz => (hgpt z hz).contDiffWithinAt
    have hcoord : ∀ j : Fin 3, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z => (Work.Drive.projChartMap i (H z)).ofLp j) V :=
      fun j => (contDiff_piLp_apply (p := 2) (𝕜 := ℝ) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
        (E := fun _ : Fin 3 => ℝ) (i := j)).comp_contDiffOn hgsm
    have hpi : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z => WithLp.toLp 2 (fun k : Fin 4 =>
          (Work.Drive.projSection i (Work.Drive.projChartMap i (H z))).ofLp k)) V := by
      rw [contDiffOn_piLp]
      intro k
      rcases eq_or_ne k i with rfl | hk
      · simpa using contDiffOn_const
      · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
        simpa [Work.Drive.projSection_apply_succAbove] using hcoord j
    refine hpi.congr (fun z _ => ?_)
    exact (WithLp.toLp_ofLp 2
      (Work.Drive.projSection i (Work.Drive.projChartMap i (H z)))).symm
  exact ⟨V, _, hVopen, hxV, fun y hy => (hVsub hy).1, hLsm,
    fun y hy => Work.Drive.projSection_ne_zero i _,
    fun y hy => ⟨Work.Drive.projSection_ne_zero i _,
      Work.Drive.projChartInv_projChartMap (hVsub hy).2⟩⟩

/-! ## Step 4: patching the local models -/

/-- **Smoothness of a bump times a function that is smooth on an open set containing the support
of the bump.** -/
private lemma contDiff_smul_of_contDiffOn_of_support_subset
    {O S : Set (EuclideanSpace ℝ (Fin 2))} (hO : IsOpen O) (hS : IsClosed S) (hSO : S ⊆ O)
    {u : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4)}
    (hu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u O)
    {χ : EuclideanSpace ℝ (Fin 2) → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hsupp : Function.support χ ⊆ S) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => χ x • u x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ S
  · exact ((hχ.contDiffAt (x := x)).smul (hu.contDiffAt (hO.mem_nhds (hSO hx))))
  · have hopen : Sᶜ ∈ 𝓝 x := hS.isOpen_compl.mem_nhds hx
    refine (contDiffAt_const (c := (0 : EuclideanSpace ℝ (Fin 4)))).congr_of_eventuallyEq ?_
    filter_upwards [hopen] with y hy
    have hy' : χ y = 0 := by
      by_contra hc
      exact hy (hsupp (by simpa [Function.mem_support] using hc))
    rw [hy', zero_smul]

/-- **A globally smooth model, parallel to `U₀` near a point of the box.**  Combining the local
chart lift with a bump function. -/
private lemma exists_local_global_lift (a b c d : ℝ)
    {h : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (EuclideanSpace ℝ (Fin 4))}
    {U₀ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4)}
    (hU₀ : ∀ y ∈ boxSet a b c d, ∃ hy : U₀ y ≠ 0, Projectivization.mk ℝ (U₀ y) hy = h y)
    (hloc : ∀ x : EuclideanSpace ℝ (Fin 2), x ∈ boxSet a b c d →
      ∃ U ∈ nhds x, ∃ H : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (EuclideanSpace ℝ (Fin 4)),
        (letI := Work.Drive.projCharted 3
         ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
           (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞) H U) ∧
        ∀ y ∈ U, y ∈ boxSet a b c d → H y = h y)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ boxSet a b c d) :
    ∃ (W : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
      (U : Set (EuclideanSpace ℝ (Fin 2))),
      IsOpen U ∧ x ∈ U ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W ∧
      ∀ y ∈ U, y ∈ boxSet a b c d → ∃ c : ℝ, c ≠ 0 ∧ W y = c • U₀ y := by
  letI := Work.Drive.projCharted 3
  obtain ⟨U₁, hU₁mem, H, hHsm, hHeq⟩ := hloc x hx
  obtain ⟨V', hV'sub, hV'open, hxV'⟩ := mem_nhds_iff.mp hU₁mem
  obtain ⟨V, L, hVopen, hxV, hVsub, hLsm, hLne, hLmk⟩ :=
    exists_chart_lift (H := H) hV'open (hHsm.mono hV'sub) hxV'
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp hVopen x hxV
  set χ : ContDiffBump x := ⟨r / 4, r / 2, by linarith, by linarith⟩ with hχ
  refine ⟨fun y => χ y • L y, Metric.ball x (r / 4), Metric.isOpen_ball,
    Metric.mem_ball_self (by linarith), ?_, ?_⟩
  · refine contDiff_smul_of_contDiffOn_of_support_subset (S := Metric.closedBall x (r / 2))
      hVopen Metric.isClosed_closedBall
      (fun y hy => hrV (lt_of_le_of_lt (Metric.mem_closedBall.mp hy) (by linarith)))
      hLsm (χ.contDiff (n := ⊤)) ?_
    intro y hy
    have hy1 : y ∈ tsupport (χ : EuclideanSpace ℝ (Fin 2) → ℝ) := subset_tsupport _ hy
    rwa [show tsupport (χ : EuclideanSpace ℝ (Fin 2) → ℝ) = Metric.closedBall x (r / 2) from
      ContDiffBump.tsupport_eq χ] at hy1
  · intro y hyB hyK
    have hyd : dist y x < r / 4 := Metric.mem_ball.mp hyB
    have hχ1 : χ y = 1 := ContDiffBump.one_of_mem_closedBall χ (Metric.mem_closedBall.mpr hyd.le)
    have hyV : y ∈ V := hrV (lt_of_lt_of_le hyd (by linarith))
    have hyU₁ : y ∈ U₁ := hV'sub (hVsub hyV)
    have hHy : H y = h y := hHeq y hyU₁ hyK
    obtain ⟨hLy, hLmky⟩ := hLmk y hyV
    obtain ⟨hU₀y, hU₀mky⟩ := hU₀ y hyK
    have hEq : Projectivization.mk ℝ (L y) hLy = Projectivization.mk ℝ (U₀ y) hU₀y := by
      rw [hLmky, hHy, ← hU₀mky]
    obtain ⟨c, hc⟩ :=
      (Projectivization.mk_eq_mk_iff' ℝ (L y) (U₀ y) hLy hU₀y).mp hEq
    have hcne : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact hLy hc.symm
    refine ⟨c, hcne, ?_⟩
    show χ y • L y = c • U₀ y
    rw [hχ1, one_smul]
    exact hc.symm

/-- **Gluing lemma for a vector-valued field.**  This is
`Work.ManifoldParity.exists_parallel_smooth_field` with the target space of the field changed from
`ℝⁿ` to `ℝ⁴`: from a continuous nowhere vanishing `U₀` on a compact `K ⊆ ℝ²` and local smooth
models which are nowhere vanishing multiples of `U₀` on `K`, build a smooth field which is a
nowhere vanishing multiple of `U₀` on `K`. -/
private theorem exists_parallel_smooth_field4 (K : Set (EuclideanSpace ℝ (Fin 2))) (hK : IsCompact K)
    (U₀ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (hU₀c : ContinuousOn U₀ K) (hU₀ne : ∀ x ∈ K, U₀ x ≠ 0)
    (hloc : ∀ x ∈ K, ∃ (W : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
        (U : Set (EuclideanSpace ℝ (Fin 2))),
        IsOpen U ∧ x ∈ U ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W ∧
        ∀ y ∈ K ∩ U, ∃ c : ℝ, c ≠ 0 ∧ W y = c • U₀ y) :
    ∃ V : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V ∧ (∀ x ∈ K, V x ≠ 0) ∧
      (∀ x ∈ K, ∃ c : ℝ, c ≠ 0 ∧ V x = c • U₀ x) := by
  classical
  have hdata : ∀ p : {x : EuclideanSpace ℝ (Fin 2) // x ∈ K},
      ∃ (W : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
        (U : Set (EuclideanSpace ℝ (Fin 2))) (ρ σ : ℝ),
        0 < ρ ∧ IsOpen U ∧ p.1 ∈ U ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W ∧
        (∀ y ∈ K ∩ U, ∃ c : ℝ, c ≠ 0 ∧ W y = c • U₀ y) ∧
        Metric.closedBall p.1 (2 * ρ) ⊆ U ∧
        (σ = 1 ∨ σ = -1) ∧
        (∀ z ∈ K, dist z p.1 ≤ 2 * ρ → 0 < σ * inner ℝ (U₀ z) (W z)) := by
    intro p
    obtain ⟨W, U, hUopen, hpU, hWsmooth, hpar⟩ := hloc p.1 p.2
    obtain ⟨c₀, hc₀, hWp⟩ := hpar p.1 ⟨p.2, hpU⟩
    have hU0p : U₀ p.1 ≠ 0 := hU₀ne p.1 p.2
    have hinnerp : (0 : ℝ) < inner ℝ (U₀ p.1) (U₀ p.1) := real_inner_self_pos.mpr hU0p
    have hgne : inner ℝ (U₀ p.1) (W p.1) ≠ 0 := by
      rw [hWp, real_inner_smul_right]
      exact mul_ne_zero hc₀ (ne_of_gt hinnerp)
    have hcont : ContinuousOn (fun z => inner ℝ (U₀ z) (W z)) K :=
      hU₀c.inner hWsmooth.continuous.continuousOn
    obtain ⟨δ, hδ, hsign⟩ := Work.ManifoldParity.eventually_sign_eq K hcont p.2 hgne
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hUopen p.1 hpU
    refine ⟨W, U, min (ε / 4) (δ / 4),
      if 0 < inner ℝ (U₀ p.1) (W p.1) then 1 else -1,
      lt_min (by linarith) (by linarith), hUopen, hpU, hWsmooth, hpar, ?_, ?_, ?_⟩
    · intro z hz
      refine hεU ?_
      have h2 : 2 * min (ε / 4) (δ / 4) ≤ ε / 2 := by
        have := min_le_left (ε / 4) (δ / 4); linarith
      have h3 : dist z p.1 ≤ 2 * min (ε / 4) (δ / 4) := Metric.mem_closedBall.mp hz
      have : dist z p.1 < ε := lt_of_le_of_lt (le_trans h3 h2) (by linarith)
      simpa [Metric.mem_ball, dist_comm] using this
    · split_ifs <;> simp
    · intro z hz hzd
      refine hsign z hz ?_
      have h2 : 2 * min (ε / 4) (δ / 4) < δ := by
        have := min_le_right (ε / 4) (δ / 4); linarith
      exact lt_of_le_of_lt hzd h2
  choose W U ρ σ hρ hUopen hpU hWsmooth hpar hball hσ hsign using hdata
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun p : {x : EuclideanSpace ℝ (Fin 2) // x ∈ K} =>
      Metric.ball p.1 (ρ p)) (fun p => Metric.isOpen_ball) (fun x hx => by
        refine mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
        exact Metric.mem_ball_self (hρ ⟨x, hx⟩))
  let bump : ∀ p : {x : EuclideanSpace ℝ (Fin 2) // x ∈ K}, ContDiffBump p.1 := fun p =>
    ⟨ρ p, 2 * ρ p, hρ p, by linarith [hρ p]⟩
  let χ : ∀ p : {x : EuclideanSpace ℝ (Fin 2) // x ∈ K}, EuclideanSpace ℝ (Fin 2) → ℝ :=
    fun p => (bump p : EuclideanSpace ℝ (Fin 2) → ℝ)
  let V₀ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4) :=
    fun z => ∑ p ∈ t, χ p z • (σ p • W p z)
  have hV₀smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V₀ := by
    refine ContDiff.sum (f := fun (p : {x : EuclideanSpace ℝ (Fin 2) // x ∈ K})
      (z : EuclideanSpace ℝ (Fin 2)) => χ p z • (σ p • W p z)) fun p hp => ?_
    refine ContDiff.smul ((bump p).contDiff (n := ⊤)) ?_
    exact ContDiff.const_smul (σ p) (hWsmooth p)
  have hmultiples : ∀ x ∈ K, ∃ a : ℝ, 0 < a ∧ V₀ x = a • U₀ x := by
    intro x hx
    have key : ∀ p ∈ t, ∃ μ : ℝ, 0 ≤ μ ∧ (χ p x ≠ 0 → 0 < μ) ∧
        χ p x • (σ p • W p x) = (χ p x * μ) • U₀ x := by
      intro p hp
      by_cases hχ : χ p x = 0
      · exact ⟨0, le_refl 0, fun h => (h hχ).elim, by rw [hχ, zero_mul, zero_smul, zero_smul]⟩
      · have hxts : x ∈ tsupport (χ p) := subset_tsupport _ (Function.mem_support.mpr hχ)
        rw [show tsupport (χ p) = Metric.closedBall p.1 (2 * ρ p) from
          ContDiffBump.tsupport_eq (bump p)] at hxts
        have hxd : dist x p.1 ≤ 2 * ρ p := Metric.mem_closedBall.mp hxts
        have hxU : x ∈ U p := hball p (Metric.mem_closedBall.mpr hxd)
        obtain ⟨c, hc, hparx⟩ := hpar p x ⟨hx, hxU⟩
        have hinnerU : (0 : ℝ) < inner ℝ (U₀ x) (U₀ x) :=
          real_inner_self_pos.mpr (hU₀ne x hx)
        have hsc : 0 < σ p * c := by
          have h1 : 0 < σ p * (c * inner ℝ (U₀ x) (U₀ x)) := by
            have h0 := hsign p x hx hxd
            rwa [hparx, real_inner_smul_right] at h0
          have h2 : 0 < (σ p * c) * inner ℝ (U₀ x) (U₀ x) := by
            rwa [← mul_assoc] at h1
          exact pos_of_mul_pos_left h2 hinnerU.le
        refine ⟨σ p * c, hsc.le, fun _ => hsc, ?_⟩
        rw [hparx, smul_smul, smul_smul, mul_assoc]
    choose μ hμ hμpos hμeq using key
    set M : {x : EuclideanSpace ℝ (Fin 2) // x ∈ K} → ℝ :=
      fun p => if hp : p ∈ t then μ p hp else 0 with hM
    have hMapp : ∀ (p : {x : EuclideanSpace ℝ (Fin 2) // x ∈ K}) (hp : p ∈ t),
        M p = μ p hp := fun p hp => by simp only [hM, dif_pos hp]
    have hxcover : x ∈ ⋃ p ∈ t, Metric.ball p.1 (ρ p) := ht hx
    simp only [mem_iUnion, exists_prop] at hxcover
    obtain ⟨p₀, hp₀t, hp₀x⟩ := hxcover
    have hχp₀ : χ p₀ x = 1 := by
      refine ContDiffBump.one_of_mem_closedBall (bump p₀) ?_
      exact Metric.mem_closedBall.mpr (Metric.mem_ball.mp hp₀x).le
    have h1 : ∀ p ∈ t, χ p x • (σ p • W p x) = (χ p x * M p) • U₀ x := by
      intro p hp
      rw [hMapp p hp]
      exact hμeq p hp
    have hV₀x : V₀ x = (∑ p ∈ t, χ p x * M p) • U₀ x := by
      show (∑ p ∈ t, χ p x • (σ p • W p x)) = (∑ p ∈ t, χ p x * M p) • U₀ x
      rw [Finset.sum_congr rfl h1, Finset.sum_smul]
    have hcoeff : 0 < ∑ p ∈ t, χ p x * M p := by
      refine Finset.sum_pos' (fun q hq => mul_nonneg (bump q).nonneg ?_) ⟨p₀, hp₀t, ?_⟩
      · rw [hMapp q hq]; exact hμ q hq
      · rw [hχp₀, one_mul, hMapp p₀ hp₀t]
        exact hμpos p₀ hp₀t (by rw [hχp₀]; norm_num)
    exact ⟨_, hcoeff, hV₀x⟩
  refine ⟨V₀, hV₀smooth, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨a, ha, haeq⟩ := hmultiples x hx
    rw [haeq]
    exact smul_ne_zero (ne_of_gt ha) (hU₀ne x hx)
  · obtain ⟨a, ha, haeq⟩ := hmultiples x hx
    exact ⟨a, ne_of_gt ha, haeq⟩

/-- Transporting a projective class along an equality of (nonzero) vectors. -/
private lemma mk_eq_of_eq {v w : EuclideanSpace ℝ (Fin 4)} (hvw : v = w) {hv : v ≠ 0} {hw : w ≠ 0}
    {p : Projectivization ℝ (EuclideanSpace ℝ (Fin 4))}
    (hp : Projectivization.mk ℝ w hw = p) : Projectivization.mk ℝ v hv = p := by
  cases hvw
  exact (Work.Drive.projectivizationMk_congr ℝ (EuclideanSpace ℝ (Fin 4))).trans hp

/-! ## The main theorem -/

theorem exists_nonvanishing_lift_of_data (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    {h : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (EuclideanSpace ℝ (Fin 4))}
    (hh : letI := Work.Drive.projCharted 3
      ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞) h
        {q : EuclideanSpace ℝ (Fin 2) | q 0 ∈ Set.Icc a b ∧ q 1 ∈ Set.Icc c d})
    (hloc : ∀ x : EuclideanSpace ℝ (Fin 2), x 0 ∈ Set.Icc a b → x 1 ∈ Set.Icc c d →
      ∃ U ∈ nhds x, ∃ H : EuclideanSpace ℝ (Fin 2) →
          Projectivization ℝ (EuclideanSpace ℝ (Fin 4)),
        (letI := Work.Drive.projCharted 3
         ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
           (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞) H U) ∧
        ∀ y ∈ U, y 0 ∈ Set.Icc a b → y 1 ∈ Set.Icc c d → H y = h y)
    (hcov : IsCoveringMap (Work.Drive.projOfUnitSphere (n := 3))) :
    ∃ (V : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4)) (hV : ∀ x, V x ≠ 0),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V ∧
      ∀ x : EuclideanSpace ℝ (Fin 2), x 0 ∈ Set.Icc a b → x 1 ∈ Set.Icc c d →
        Projectivization.mk ℝ (V x) (hV x) = h x := by
  letI := Work.Drive.projCharted 3
  classical
  have hcont : ContinuousOn h (boxSet a b c d) := hh.continuousOn
  obtain ⟨V₀, hV₀cont, hV₀ne, hV₀⟩ := exists_continuous_lift_box a b c d hab hcd hcont hcov
  -- the total extension `U₀` of `V₀`, obtained by clamping into the box
  let U₀ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4) :=
    fun q => V₀ ⟨clampPt a b c d q, clampPt_mem a b c d hab.le hcd.le q⟩
  have hU₀cont : Continuous U₀ :=
    hV₀cont.comp (Continuous.subtype_mk (continuous_clampPt a b c d) _)
  have hU₀x : ∀ x (hx : x ∈ boxSet a b c d), U₀ x = V₀ ⟨x, hx⟩ := by
    intro x hx
    simp only [U₀]
    congr 1
    exact Subtype.ext (clampPt_eq_self hx)
  have hU₀ne : ∀ x ∈ boxSet a b c d, U₀ x ≠ 0 := by
    intro x hx
    rw [hU₀x x hx]
    exact hV₀ne ⟨x, hx⟩
  have hU₀mk : ∀ x (hx : x ∈ boxSet a b c d) (hne : U₀ x ≠ 0),
      Projectivization.mk ℝ (U₀ x) hne = h x :=
    fun x hx _ => mk_eq_of_eq (hU₀x x hx) (hV₀ ⟨x, hx⟩ (hV₀ne ⟨x, hx⟩))
  -- the local smooth models, in the form needed for the gluing lemma
  have hlocI : ∀ x ∈ boxSet a b c d, ∃ U ∈ nhds x,
      ∃ H : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (EuclideanSpace ℝ (Fin 4)),
        (letI := Work.Drive.projCharted 3
         ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
           (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞) H U) ∧
        ∀ y ∈ U, y ∈ boxSet a b c d → H y = h y := by
    intro x hx
    obtain ⟨U, hUmem, H, hHsm, hHeq⟩ := hloc x hx.1 hx.2
    exact ⟨U, hUmem, H, hHsm, fun y hyU hyK => hHeq y hyU hyK.1 hyK.2⟩
  have hloc' : ∀ x ∈ boxSet a b c d, ∃ (W : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
      (U : Set (EuclideanSpace ℝ (Fin 2))),
      IsOpen U ∧ x ∈ U ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W ∧
      ∀ y ∈ boxSet a b c d ∩ U, ∃ c : ℝ, c ≠ 0 ∧ W y = c • U₀ y := by
    intro x hx
    obtain ⟨W, U, hUopen, hxU, hWsm, hW⟩ :=
      exists_local_global_lift a b c d
        (fun y hy => ⟨hU₀ne y hy, hU₀mk y hy _⟩)
        hlocI x hx
    exact ⟨W, U, hUopen, hxU, hWsm, fun y hy => hW y hy.2 hy.1⟩
  obtain ⟨V, hVsm, hVne, hVpar⟩ :=
    exists_parallel_smooth_field4 (boxSet a b c d) (isCompact_boxSet a b c d) U₀
      hU₀cont.continuousOn hU₀ne hloc'
  -- the box has an open neighbourhood on which `V` does not vanish
  have hOpen : IsOpen {x : EuclideanSpace ℝ (Fin 2) | V x ≠ 0} := by
    rw [show {x : EuclideanSpace ℝ (Fin 2) | V x ≠ 0}
        = V ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 4))) from rfl]
    exact (isClosed_singleton.isOpen_compl).preimage hVsm.continuous
  obtain ⟨δ, hδ, hδsub⟩ :=
    (isCompact_boxSet a b c d).exists_thickening_subset_open hOpen (fun x hx => hVne x hx)
  -- a smooth flattening of the plane into that thickening
  obtain ⟨Ψ, hΨsm, hΨid, hΨim⟩ := exists_contDiff_flattening_box a b c d hab hcd δ hδ
  have hΨmem : ∀ x : EuclideanSpace ℝ (Fin 2), Ψ x ∈ Metric.thickening δ (boxSet a b c d) := by
    intro x
    rw [Metric.mem_thickening_iff]
    obtain ⟨y, hy, hd⟩ := hΨim x
    exact ⟨y, hy, hd⟩
  refine ⟨fun x => V (Ψ x), fun x => hδsub (hΨmem x), hVsm.comp hΨsm, ?_⟩
  intro x hx0 hx1
  have hxK : x ∈ boxSet a b c d := ⟨hx0, hx1⟩
  have hΨx : Ψ x = x := hΨid x hxK
  obtain ⟨c, hc, hcpar⟩ := hVpar x hxK
  have hVx : V (Ψ x) = c • V₀ ⟨x, hxK⟩ := by
    rw [hΨx, hcpar, hU₀x x hxK]
  have hmk : Projectivization.mk ℝ (V (Ψ x)) (hδsub (hΨmem x))
      = Projectivization.mk ℝ (V₀ ⟨x, hxK⟩) (hV₀ne ⟨x, hxK⟩) :=
    mk_eq_of_eq hVx (Work.Drive.mk_smul_eq_mk c hc (V₀ ⟨x, hxK⟩) (hV₀ne ⟨x, hxK⟩))
  exact hmk.trans (hV₀ ⟨x, hxK⟩ (hV₀ne ⟨x, hxK⟩))

end

end Work.Drive
