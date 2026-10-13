/-
  `Work.WilE2.Cb` — the generic-slope lemma `exists_generic_slope`.

  ## Mathematics

  Let `F : ℝ^k → ℝ` be `C²` with `0` a regular value, fix a coordinate `i₀` and let `χ` be the
  *slope map* of the level set `{F = 0}`: in the coordinates `j ≠ i₀`,

      χ_j(x) = ∂_j F(x) / ∂_{i₀} F(x).

  A slope `c` is *bad* if the level set meets the zero set of `∂_j F - c_j ∂_{i₀} F` (`j ≠ i₀`)
  at a point where the augmented system `(F, ∂_j F - c_j ∂_{i₀} F)` is *degenerate*.  The content
  of `exists_generic_slope` is that the bad slopes form a Lebesgue-null set, so that a slope can
  be chosen in any prescribed ball.

  ## Proof

  Fix a point `x₀` of the level set with `∂_{i₀}F(x₀) ≠ 0`; by the implicit function theorem the
  level set is near `x₀` the graph `u ↦ insertNth i₀ (h u) u` of a `C¹` function `h`
  (`local_graph_level_set`), and the slope map is the `C¹` map `graphSlope F i₀ h` on `ℝⁿ`
  (`n = k - 1`).  At a point `u` of the graph with `∂_{i₀}F ≠ 0`, the degenerate points of slope
  `graphSlope u` are exactly the critical points of `graphSlope`
  (`not_injective_fderiv_graphSlope`); this combines the quotient rule
  (`fderiv_pderiv_sub_eq`) with the fact that a tangent vector of the level set is a derivative
  of the parametrisation (`exists_param_preimage`) and with the chain rule
  (`hasFDerivAt_graphSlope_coord`).  Therefore the bad slopes produced near `x₀` are the critical
  *values* of the `C¹` map `graphSlope`, hence null by Sard's lemma in the square case
  (`MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`, applied to the extension
  of `graphSlope` by `0` outside a ball).

  Covering the level set by countably many such neighbourhoods gives that the bad slopes are
  null, and any null set misses a point of the prescribed ball (`avoid_null`).
-/
import Mathlib
import Submission.Work.WilE2.sard_square
import Submission.Work.WilE2.avoid_null
import Submission.Work.WilE9G.Sard.Basic
import Submission.Work.WilE2.Cb.local_graph_level_set
import Submission.Work.WilE2.Cb.fderiv_pderiv_sub_eq
import Submission.Work.WilE2.Cb.hasFDerivAt_graphSlope_coord
import Submission.Work.WilE2.Cb.exists_param_preimage

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Classical
open Filter
open scoped Topology
open MeasureTheory

namespace Work.WilE2.Cb

/-! ### Vocabulary (the slope map of a level set) -/

/-- The `i`-th partial derivative of `F`, as a function of the base point. -/
def pderiv {k : ℕ} (F : (Fin k → ℝ) → ℝ) (i : Fin k) (x : Fin k → ℝ) : ℝ :=
  fderiv ℝ F x (Pi.single i 1)

@[simp] theorem pderiv_apply {k : ℕ} (F : (Fin k → ℝ) → ℝ) (i : Fin k) (x : Fin k → ℝ) :
    pderiv F i x = fderiv ℝ F x (Pi.single i 1) := rfl

/-- If `F` is `C²` then each of its partial derivatives is `C¹`. -/
theorem contDiff_one_pderiv {k : ℕ} (F : (Fin k → ℝ) → ℝ) (hF : ContDiff ℝ 2 F) (i : Fin k) :
    ContDiff ℝ 1 (pderiv F i) := by
  change ContDiff ℝ 1 (fun x : Fin k → ℝ => fderiv ℝ F x (Pi.single i 1))
  have h1 : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (m := 1) (by norm_num)
  exact h1.clm_apply contDiff_const

/-- A differential vanishes when all partial derivatives vanish. -/
theorem fderiv_eq_zero_of_forall_pderiv_eq_zero {k : ℕ} {F : (Fin k → ℝ) → ℝ}
    {x : Fin k → ℝ} (h : ∀ i, pderiv F i x = 0) : fderiv ℝ F x = 0 := by
  ext v
  rw [zero_apply]
  have hv : v = ∑ i, v i • (Pi.single i (1 : ℝ) : Fin k → ℝ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply, Finset.mem_univ]
  conv_lhs => rw [hv]
  rw [map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_smul, smul_eq_mul,
    show (fderiv ℝ F x) (Pi.single i 1) = 0 from h i, mul_zero]

/-- The graph of the local solution `h`. -/
def graphMap {m : ℕ} (i : Fin (m+1)) (h : (Fin m → ℝ) → ℝ) :
    (Fin m → ℝ) → (Fin (m+1) → ℝ) :=
  fun u => Fin.insertNth i (h u) u

@[simp] theorem graphMap_apply {m : ℕ} (i : Fin (m+1)) (h : (Fin m → ℝ) → ℝ) (u : Fin m → ℝ) :
    graphMap i h u = Fin.insertNth i (h u) u := rfl

/-- The slope condition at a point `x`: the slope of the level set in the directions `≠ i` is `c`. -/
def SlopeCond {m : ℕ} (F : (Fin (m+1) → ℝ) → ℝ) (i : Fin (m+1)) (c : Fin m → ℝ)
    (x : Fin (m+1) → ℝ) : Prop :=
  ∀ l : Fin m, pderiv F (i.succAbove l) x = c l * pderiv F i x

/-- The degeneracy condition at a point `x` with slope `c`: some nonzero tangent vector to the
level set is annihilated by the derivative of all the differences `∂_j F - c_j ∂_i F`. -/
def BadAt {m : ℕ} (F : (Fin (m+1) → ℝ) → ℝ) (i : Fin (m+1)) (c : Fin m → ℝ)
    (x : Fin (m+1) → ℝ) : Prop :=
  SlopeCond F i c x ∧ ∃ v : Fin (m+1) → ℝ, v ≠ 0 ∧ fderiv ℝ F x v = 0 ∧
    ∀ l : Fin m,
      fderiv ℝ (fun y => pderiv F (i.succAbove l) y - c l * pderiv F i y) x v = 0

/-- The set of "bad" slopes: those `c` for which the level set `{F = 0}` has a degenerate point
of slope `c`. -/
def badSlope {m : ℕ} (F : (Fin (m+1) → ℝ) → ℝ) (i : Fin (m+1)) : Set (Fin m → ℝ) :=
  {c | ∃ x : Fin (m+1) → ℝ, F x = 0 ∧ BadAt F i c x}

/-- The part of the bad set generated in a ball of radius `R` around `x₀`. -/
def locBad {m : ℕ} (F : (Fin (m+1) → ℝ) → ℝ) (i : Fin (m+1)) (x₀ : Fin (m+1) → ℝ)
    (R : ℝ) : Set (Fin m → ℝ) :=
  {c | ∃ x : Fin (m+1) → ℝ, dist x x₀ < R ∧ F x = 0 ∧ BadAt F i c x}

/-- The slope map computed on the graph of `h`. -/
def graphSlope {m : ℕ} (F : (Fin (m+1) → ℝ) → ℝ) (i : Fin (m+1))
    (h : (Fin m → ℝ) → ℝ) : (Fin m → ℝ) → (Fin m → ℝ) :=
  fun u l => pderiv F (i.succAbove l) (graphMap i h u) / pderiv F i (graphMap i h u)

@[simp] theorem graphSlope_apply {m : ℕ} (F : (Fin (m+1) → ℝ) → ℝ) (i : Fin (m+1))
    (h : (Fin m → ℝ) → ℝ) (u : Fin m → ℝ) (l : Fin m) :
    graphSlope F i h u l = pderiv F (i.succAbove l) (graphMap i h u)
      / pderiv F i (graphMap i h u) := rfl

/-- **The slope condition determines the slope.**  If `x` is a zero of `F` at which the slope
condition for `c` holds, then `∂_i F x ≠ 0`, so that `c` is the slope of `x`. -/
theorem pderiv_ne_zero_of_slopeCond {m : ℕ} (F : (Fin (m+1) → ℝ) → ℝ)
    (hreg : ∀ z, F z = 0 → fderiv ℝ F z ≠ 0) {i : Fin (m+1)} {x : Fin (m+1) → ℝ}
    (hx : F x = 0) {c : Fin m → ℝ} (hc : SlopeCond F i c x) : pderiv F i x ≠ 0 := by
  intro h0
  refine hreg x hx (fderiv_eq_zero_of_forall_pderiv_eq_zero fun j => ?_)
  rcases Fin.eq_self_or_eq_succAbove i j with h | ⟨l, hl⟩
  · rw [h]; exact h0
  · rw [hl, hc l, h0, mul_zero]

/-! ### The bad points are critical points of the slope map -/

/-- **The slope condition determines the slope (on the graph).** -/
lemma graphSlope_eq_of_slopeCond {m : ℕ} (F : (Fin (m+1) → ℝ) → ℝ) (i : Fin (m+1))
    {h : (Fin m → ℝ) → ℝ} {u : Fin m → ℝ} (hne : pderiv F i (graphMap i h u) ≠ 0)
    {c : Fin m → ℝ} (hc : SlopeCond F i c (graphMap i h u)) :
    c = graphSlope F i h u := by
  funext l
  rw [graphSlope_apply, eq_div_iff hne]
  exact (hc l).symm

/-- **The quotient rule for the slope.**  The derivative of `∂_j F - (∂_j F(x)/∂_i F(x)) ∂_i F`
at `x` is `∂_i F(x)` times the derivative of the slope `∂_j F / ∂_i F`. -/
lemma fderiv_slope_coord_eq {m : ℕ} (F : (Fin (m+1) → ℝ) → ℝ) (hF : ContDiff ℝ 2 F)
    (i : Fin (m+1)) (l : Fin m) {x : Fin (m+1) → ℝ} (hne : pderiv F i x ≠ 0)
    (v : Fin (m+1) → ℝ) :
    fderiv ℝ (fun y => pderiv F (i.succAbove l) y
        - (pderiv F (i.succAbove l) x / pderiv F i x) * pderiv F i y) x v
      = pderiv F i x * fderiv ℝ (fun y => pderiv F (i.succAbove l) y / pderiv F i y) x v := by
  have h := fderiv_pderiv_sub_eq F hF i (i.succAbove l) (x := x) hne
  have h2 := congrArg (fun (T : (Fin (m+1) → ℝ) →L[ℝ] ℝ) => T v) h
  simpa only [pderiv, smul_apply, smul_eq_mul] using h2

/-- **The bad points are critical points of the slope map on the graph.** -/
lemma not_injective_fderiv_graphSlope {m : ℕ} (F : (Fin (m+1) → ℝ) → ℝ) (hF : ContDiff ℝ 2 F)
    (i : Fin (m+1)) {h : (Fin m → ℝ) → ℝ} {A : Set (Fin m → ℝ)} (hA : IsOpen A)
    (hhcd : ContDiffOn ℝ 1 h A) (hgraph : ∀ u ∈ A, F (graphMap i h u) = 0)
    {u : Fin m → ℝ} (hu : u ∈ A) (hne : pderiv F i (graphMap i h u) ≠ 0)
    {c : Fin m → ℝ} (hc : BadAt F i c (graphMap i h u)) :
    ¬ Function.Injective (fderiv ℝ (graphSlope F i h) u) := by
  obtain ⟨hsl, v, hv0, hFv, hderiv⟩ := hc
  -- differentiability of the graph map
  have hhd : DifferentiableAt ℝ h u :=
    (hhcd.contDiffAt (hA.mem_nhds hu)).differentiableAt (by norm_num)
  have hzero : ∀ᶠ u' in nhds u, F (Fin.insertNth i (h u') u') = 0 :=
    Filter.mem_of_superset (hA.mem_nhds hu) (fun u' hu' => by
      show F (Fin.insertNth i (h u') u') = 0
      simpa only [graphMap] using hgraph u' hu')
  -- a tangent vector of the level set is a derivative of the parametrisation
  obtain ⟨z, hz⟩ := exists_param_preimage F hF i hhd hzero
    (by simpa only [graphMap, pderiv] using hne) (by simpa only [graphMap] using hFv)
  have hz' : (fderiv ℝ (fun u' : Fin m → ℝ => graphMap i h u') u) z = v := by
    simpa only [graphMap] using hz
  -- the slope map and its coordinate derivatives
  have hw : HasFDerivAt (graphSlope F i h)
      (ContinuousLinearMap.pi fun l : Fin m =>
        (fderiv ℝ (fun y => pderiv F (i.succAbove l) y / pderiv F i y) (graphMap i h u)).comp
          (fderiv ℝ (fun u' : Fin m → ℝ => graphMap i h u') u)) u := by
    apply (hasFDerivAt_pi (φ := fun (l : Fin m) (u' : Fin m → ℝ) =>
        pderiv F (i.succAbove l) (graphMap i h u') / pderiv F i (graphMap i h u'))
      (φ' := fun l : Fin m =>
        (fderiv ℝ (fun y => pderiv F (i.succAbove l) y / pderiv F i y) (graphMap i h u)).comp
          (fderiv ℝ (fun u' : Fin m → ℝ => graphMap i h u') u))).mpr
    intro l
    have h4 := hasFDerivAt_graphSlope_coord F hF i hA hhcd hu
      (by simpa only [graphMap, pderiv] using hne) l
    simpa only [pderiv, graphMap] using h4
  -- the quotient-rule step: the bad direction kills the derivative of every coordinate of `χ`
  have hchi : ∀ l : Fin m,
      fderiv ℝ (fun y => pderiv F (i.succAbove l) y / pderiv F i y) (graphMap i h u) v = 0 := by
    intro l
    have hcl : c l = pderiv F (i.succAbove l) (graphMap i h u) / pderiv F i (graphMap i h u) := by
      rw [eq_div_iff hne]
      exact (hsl l).symm
    have h2 := fderiv_slope_coord_eq F hF i l hne v
    have hdl := hderiv l
    rw [hcl, h2] at hdl
    exact (mul_eq_zero.mp hdl).resolve_left hne
  -- assemble: the derivative of the slope map kills `z`
  have hz0 : (fderiv ℝ (graphSlope F i h) u) z = 0 := by
    rw [hw.fderiv]
    funext l
    rw [ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply, hz', hchi l,
      Pi.zero_apply]
  have hzne : z ≠ 0 := by
    intro hz''
    refine hv0 ?_
    rw [← hz', hz'', map_zero]
  intro hinj
  exact hzne (hinj (by rw [hz0, map_zero]))

/-! ### The local nullity statement -/

/-- **Local nullity of the bad slopes.**  At a point `x₀` of the level set with `∂_{i₀}F(x₀) ≠ 0`,
the slopes generated by bad points in a small ball around `x₀` form a null set. -/
theorem locBad_null {m : ℕ} (F : (Fin (m+1) → ℝ) → ℝ) (hF : ContDiff ℝ 2 F)
    (hreg : ∀ z, F z = 0 → fderiv ℝ F z ≠ 0) (i : Fin (m+1)) (x₀ : Fin (m+1) → ℝ)
    (h0 : F x₀ = 0) (hx : pderiv F i x₀ ≠ 0) :
    ∃ R > 0, MeasureTheory.volume (locBad F i x₀ R) = 0 := by
  classical
  obtain ⟨h, A, hAopen, hu₀A, hhcd, hhu₀, hgraph, B, hBopen, hx₀B, huniq⟩ :=
    local_graph_level_set F hF i x₀ h0 (by simpa only [pderiv] using hx)
  set u₀ : Fin m → ℝ := x₀ ∘ Fin.succAbove i with hu₀def
  have hgraph_u₀ : graphMap i h u₀ = x₀ := by
    rw [graphMap_apply, hu₀def, hhu₀]
    exact Work.WilE9G.Sard.ins_del i x₀
  -- continuity of the graph map and of the denominator at `u₀`
  have hcont_graph : ContinuousAt (fun u' : Fin m → ℝ => graphMap i h u') u₀ := by
    have hh : ContinuousAt h u₀ := hhcd.continuousOn.continuousAt (hAopen.mem_nhds hu₀A)
    have hpair : ContinuousAt (fun u' : Fin m → ℝ => (h u', u')) u₀ := hh.prodMk continuousAt_id
    have hins : ContinuousAt (fun u' : Fin m → ℝ =>
        (Work.WilE9G.Sard.insCLM m i) (h u', u')) u₀ :=
      (Work.WilE9G.Sard.insCLM m i).continuous.continuousAt.comp hpair
    simpa only [Work.WilE9G.Sard.insCLM_apply, graphMap] using hins
  have hcont_den : ContinuousAt (fun u' : Fin m → ℝ => pderiv F i (graphMap i h u')) u₀ :=
    (contDiff_one_pderiv F hF i).continuous.continuousAt.comp hcont_graph
  have hden₀ : pderiv F i (graphMap i h u₀) ≠ 0 := by rw [hgraph_u₀]; exact hx
  have hden_nhds : ∀ᶠ u in nhds u₀, pderiv F i (graphMap i h u) ≠ 0 :=
    hcont_den.preimage_mem_nhds (isOpen_ne.mem_nhds hden₀)
  -- a ball on which everything is defined
  obtain ⟨r₁, hr₁pos, hr₁⟩ := Metric.mem_nhds_iff.mp (hAopen.mem_nhds hu₀A)
  obtain ⟨r₂, hr₂pos, hr₂⟩ := Metric.mem_nhds_iff.mp hden_nhds
  obtain ⟨r₃, hr₃pos, hr₃⟩ := Metric.mem_nhds_iff.mp (hBopen.mem_nhds hx₀B)
  set r : ℝ := min r₁ r₂ / 2 with hrdef
  have hrpos : 0 < r := by
    rw [hrdef]; have := lt_min hr₁pos hr₂pos; linarith
  have hrr₁ : r < r₁ := by
    rw [hrdef]; have := lt_min hr₁pos hr₂pos; linarith [min_le_left r₁ r₂]
  have hrr₂ : r < r₂ := by
    rw [hrdef]; have := lt_min hr₁pos hr₂pos; linarith [min_le_right r₁ r₂]
  set R : ℝ := min r r₃ with hRdef
  have hRpos : 0 < R := by
    rw [hRdef]; exact lt_min hrpos hr₃pos
  -- the domain of the slope map and its set of critical points
  set U : Set (Fin m → ℝ) := Metric.ball u₀ r with hUdef
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hUsubA : U ⊆ A := fun u hu => hr₁ (lt_trans (Metric.mem_ball.mp hu) hrr₁)
  have hUden : ∀ u ∈ U, pderiv F i (graphMap i h u) ≠ 0 :=
    fun u hu => hr₂ (lt_trans (Metric.mem_ball.mp hu) hrr₂)
  have hwdiff : ∀ u ∈ U, HasFDerivAt (graphSlope F i h) (fderiv ℝ (graphSlope F i h) u) u := by
    intro u hu
    have hpi : HasFDerivAt (graphSlope F i h)
        (ContinuousLinearMap.pi fun l : Fin m =>
          (fderiv ℝ (fun y => pderiv F (i.succAbove l) y / pderiv F i y) (graphMap i h u)).comp
            (fderiv ℝ (fun u' : Fin m → ℝ => graphMap i h u') u)) u := by
      apply (hasFDerivAt_pi (φ := fun (l : Fin m) (u' : Fin m → ℝ) =>
          pderiv F (i.succAbove l) (graphMap i h u') / pderiv F i (graphMap i h u'))
        (φ' := fun l : Fin m =>
          (fderiv ℝ (fun y => pderiv F (i.succAbove l) y / pderiv F i y) (graphMap i h u)).comp
            (fderiv ℝ (fun u' : Fin m → ℝ => graphMap i h u') u))).mpr
      intro l
      have h4 := hasFDerivAt_graphSlope_coord F hF i hAopen hhcd (hUsubA hu) (hUden u hu) l
      simpa only [pderiv, graphMap] using h4
    rwa [hpi.fderiv]
  set s : Set (Fin m → ℝ) := {u | u ∈ U ∧ ¬ Function.Injective (fderiv ℝ (graphSlope F i h) u)}
    with hsdef
  -- Sard: the critical values of the slope map are null
  have hsard : MeasureTheory.volume (graphSlope F i h '' s) = 0 := by
    set Ψ : (Fin m → ℝ) → (Fin m → ℝ) := U.indicator (graphSlope F i h) with hΨdef
    have himg : Ψ '' s = graphSlope F i h '' s := by
      apply Set.image_congr
      intro u hu
      rw [hΨdef]
      exact Set.indicator_of_mem hu.1 (graphSlope F i h)
    rw [← himg]
    refine MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
      (μ := MeasureTheory.volume) (s := s) (f := Ψ)
      (f' := fun u => fderiv ℝ (graphSlope F i h) u) ?_ ?_
    · intro u hu
      have hev : graphSlope F i h =ᶠ[nhds u] Ψ := by
        filter_upwards [hUopen.mem_nhds hu.1] with u' hu'
        rw [hΨdef]
        exact (Set.indicator_of_mem hu' (graphSlope F i h)).symm
      exact ((hwdiff u hu.1).congr_of_eventuallyEq hev.symm).hasFDerivWithinAt
    · intro u hu
      have hker : (fderiv ℝ (graphSlope F i h) u).ker ≠ ⊥ := fun hbot =>
        hu.2 (LinearMap.ker_eq_bot.mp hbot)
      rw [ContinuousLinearMap.det]
      exact (LinearMap.det_eq_zero_iff_ker_ne_bot (f :=
        (fderiv ℝ (graphSlope F i h) u).toLinearMap)).2 hker
  -- bad slopes near `x₀` are critical values of the slope map
  refine ⟨R, hRpos, ?_⟩
  refine measure_mono_null ?_ hsard
  intro c hc
  obtain ⟨x, hxR, hFx, hbad⟩ := hc
  have hxR₃ : dist x x₀ < r₃ := lt_of_lt_of_le hxR (min_le_right r r₃)
  have hxRr : dist x x₀ < r := lt_of_lt_of_le hxR (min_le_left r r₃)
  have hxB : x ∈ B := hr₃ hxR₃
  have hxgraph : x = graphMap i h (x ∘ Fin.succAbove i) := by
    simpa only [graphMap] using huniq x hxB hFx
  set u : Fin m → ℝ := x ∘ Fin.succAbove i with hudef
  have huU : u ∈ U := by
    rw [hUdef, Metric.mem_ball]
    refine lt_of_le_of_lt ?_ hxRr
    rw [dist_pi_le_iff dist_nonneg]
    intro l
    exact dist_le_pi_dist x x₀ (i.succAbove l)
  have hune : pderiv F i (graphMap i h u) ≠ 0 := hUden u huU
  have hbad' : BadAt F i c (graphMap i h u) := by
    rw [hudef]
    rw [← hxgraph]
    exact hbad
  refine ⟨u, ⟨huU, ?_⟩, ?_⟩
  · exact not_injective_fderiv_graphSlope F hF i hAopen hhcd hgraph (hUsubA huU) hune hbad'
  · exact (graphSlope_eq_of_slopeCond F i hune hbad'.1).symm

/-! ### The main theorem -/

theorem exists_generic_slope {k : ℕ} (F : (Fin k → ℝ) → ℝ) (hF : ContDiff ℝ 2 F)
    (hreg : ∀ z, F z = 0 → fderiv ℝ F z ≠ 0) (i₀ : Fin k)
    (c₀ : Fin k → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : Fin k → ℝ, (∀ j, |c j - c₀ j| < ε) ∧
      ∀ x : Fin k → ℝ, F x = 0 →
        (∀ j : Fin k, j ≠ i₀ → fderiv ℝ F x (Pi.single j 1) = c j * fderiv ℝ F x (Pi.single i₀ 1)) →
        fderiv ℝ F x (Pi.single i₀ 1) ≠ 0 →
        ∀ v : Fin k → ℝ, v ≠ 0 → fderiv ℝ F x v = 0 →
          ∃ j : Fin k, j ≠ i₀ ∧
            fderiv ℝ (fun y => fderiv ℝ F y (Pi.single j 1) - c j * fderiv ℝ F y (Pi.single i₀ 1)) x v
              ≠ 0 := by
  cases k with
  | zero => exact Fin.elim0 i₀
  | succ m =>
    -- `k = m + 1`.  The slopes are the elements of `ℝᵐ` (`i₀.succAbove`).
    -- Step 1: the local nullity statements, and the countable cover of the level set.
    have hloc : ∀ x : {z : Fin (m+1) → ℝ | F z = 0 ∧ pderiv F i₀ z ≠ 0},
        ∃ R : ℝ, 0 < R ∧ volume (locBad F i₀ (x : Fin (m+1) → ℝ) R) = 0 :=
      fun x => locBad_null F hF hreg i₀ (x : Fin (m+1) → ℝ) x.2.1 x.2.2
    choose ρ hρpos hρnull using hloc
    obtain ⟨T, hTcount, hTcover⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun x : {z : Fin (m+1) → ℝ | F z = 0 ∧ pderiv F i₀ z ≠ 0} =>
        Metric.ball (x : Fin (m+1) → ℝ) (ρ x / 2))
      (fun x => Metric.isOpen_ball)
    have hsubset : badSlope F i₀ ⊆ ⋃ x : T, locBad F i₀ (x : Fin (m+1) → ℝ) (ρ x) := by
      intro c hc
      obtain ⟨x, hFx, hbad⟩ := hc
      have hxne : pderiv F i₀ x ≠ 0 := pderiv_ne_zero_of_slopeCond F hreg hFx hbad.1
      have hxN : x ∈ {z : Fin (m+1) → ℝ | F z = 0 ∧ pderiv F i₀ z ≠ 0} := ⟨hFx, hxne⟩
      have hcov : x ∈ ⋃ y : {z : Fin (m+1) → ℝ | F z = 0 ∧ pderiv F i₀ z ≠ 0},
          Metric.ball (y : Fin (m+1) → ℝ) (ρ y / 2) :=
        Set.mem_iUnion.mpr ⟨⟨x, hxN⟩, Metric.mem_ball_self (by linarith [hρpos ⟨x, hxN⟩])⟩
      have hcovT : x ∈ ⋃ y ∈ T, Metric.ball (y : Fin (m+1) → ℝ) (ρ y / 2) := by
        rw [hTcover]
        exact hcov
      simp only [Set.mem_iUnion] at hcovT
      obtain ⟨y, hyT, hyball⟩ := hcovT
      refine Set.mem_iUnion.mpr ⟨⟨y, hyT⟩, x, ?_, hFx, hbad⟩
      show dist x (↑y) < ρ y
      have h1 : dist x (↑y) < ρ y / 2 := Metric.mem_ball.mp hyball
      have h2 : 0 < ρ y := hρpos y
      linarith
    have hbadnull : volume (badSlope F i₀) = 0 := by
      refine measure_mono_null hsubset ?_
      haveI : Countable T := hTcount.to_subtype
      exact measure_iUnion_null fun x => hρnull x
    -- Step 2: choose the slope outside the bad set.
    obtain ⟨c', hc'dist, hc'mem⟩ :=
      Work.WilE2.avoid_null (n := m) hbadnull (fun l => c₀ (i₀.succAbove l)) hε
    refine ⟨Fin.insertNth i₀ (c₀ i₀) c', ?_, ?_⟩
    · intro j
      rcases Fin.eq_self_or_eq_succAbove i₀ j with h | ⟨l, hl⟩
      · subst h
        rw [Fin.insertNth_apply_same, sub_self, abs_zero]
        exact hε
      · subst hl
        rw [Fin.insertNth_apply_succAbove]
        have := (dist_pi_lt_iff hε).mp hc'dist l
        simpa [Real.dist_eq] using this
    · intro x hFx hslope hxne v hv0 hFv
      by_contra hcon
      have hcon' : ∀ j : Fin (m+1), j ≠ i₀ →
          fderiv ℝ (fun y => fderiv ℝ F y (Pi.single j 1)
            - ((Fin.insertNth i₀ (c₀ i₀) c' : Fin (m+1) → ℝ) j) * fderiv ℝ F y (Pi.single i₀ 1)) x v = 0 := by
        intro j hj
        by_contra hne
        exact hcon ⟨j, hj, hne⟩
      refine hc'mem ⟨x, hFx, ?_⟩
      refine ⟨fun l => ?_, v, hv0, hFv, fun l => ?_⟩
      · have := hslope (i₀.succAbove l) (Fin.succAbove_ne i₀ l)
        simpa only [pderiv, Fin.insertNth_apply_succAbove] using this
      · have := hcon' (i₀.succAbove l) (Fin.succAbove_ne i₀ l)
        simpa only [pderiv, Fin.insertNth_apply_succAbove] using this

end Work.WilE2.Cb
