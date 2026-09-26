import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.planeIndexGeom

namespace Work.Smooth.SphereJordan

open Set Filter
open scoped Topology

noncomputable section

/-!
# A continuous logarithm on the complement of a "cut" from `0` to `∞`

Let `γ : [0,1] → ℂ ∪ {∞}` be a *continuous* path in the Riemann sphere from `0` to `∞` (no
injectivity is assumed).  Then `ℂ \ range γ` carries a continuous logarithm for the identity: a
continuous `f` with `Complex.exp (f z) = z`.

The path `γ` is a "branch cut" joining the two points the exponential map distinguishes, so no loop
in its complement can wind around `0`: this is the winding lemma
`loopIndex_eq_zero_of_avoids_range` below (proved by local constancy of the winding number along
the connected trace of `γ`).  Consequently the identity of `ℂ*` restricted to the complement
lifts through the covering map `Complex.exp`; because the complement may be *disconnected* (a path
may trace out a closed curve before escaping to `∞`), the lift is built one connected component at
a time and glued.
-/

/-- The finite part of a point of the Riemann sphere (with `∞` sent to `0`). -/
def finPart (z : OnePoint ℂ) : ℂ := z.elim 0 (fun w => w)

lemma finPart_coe (w : ℂ) : finPart ((w : ℂ) : OnePoint ℂ) = w := rfl

lemma finPart_spec {z : OnePoint ℂ} (hz : z ≠ OnePoint.infty) :
    ((finPart z : ℂ) : OnePoint ℂ) = z := by
  induction z using OnePoint.rec with
  | infty => exact absurd rfl hz
  | coe w => rfl

lemma finPart_continuousAt (w : ℂ) : ContinuousAt finPart ((w : ℂ) : OnePoint ℂ) := by
  rw [ContinuousAt, OnePoint.nhds_coe_eq]
  have hcomp : (finPart ∘ (fun v : ℂ => ((v : ℂ) : OnePoint ℂ))) = id := by
    funext v; rfl
  exact Filter.tendsto_map' (by rw [hcomp]; exact tendsto_id)

/-- The winding number of the loop `c` about the point `w`, as a function of `w`. -/
def windPhi (c : C(unitInterval, ℂ)) : ℂ → ℤ :=
  fun w => loopIndex (c - ContinuousMap.const unitInterval w)

/-- The same function, extended to the Riemann sphere by `0` at `∞` (the winding number about
`∞` vanishes). -/
def windPsi (c : C(unitInterval, ℂ)) : OnePoint ℂ → ℤ :=
  fun a => a.elim 0 (windPhi c)

/-- The set of points of the Riemann sphere that are either `∞` or have modulus `> R` (a
neighbourhood of `∞`). -/
def farSet (R : ℝ) : Set (OnePoint ℂ) :=
  {a | a.elim True (fun w => R < ‖w‖)}

/-- **The winding number is constant along a segment avoiding the trace.** -/
theorem loopIndex_segment {c : C(unitInterval, ℂ)} (hloop : c 0 = c 1) {x y : ℂ}
    (hx : ∀ t, c t ≠ x) (hy : ∀ t, c t ≠ y)
    (hseg : ∀ t s, s ∈ Set.Icc (0 : ℝ) 1 → c t ≠ (1 - s) * x + s * y) :
    loopIndex (c - ContinuousMap.const unitInterval y) =
      loopIndex (c - ContinuousMap.const unitInterval x) := by
  have hne_y : ∀ t, (c - ContinuousMap.const unitInterval y) t ≠ 0 := fun t => by
    rw [ContinuousMap.sub_apply, ContinuousMap.const_apply]; exact sub_ne_zero.mpr (hy t)
  have hne_x : ∀ t, (c - ContinuousMap.const unitInterval x) t ≠ 0 := fun t => by
    rw [ContinuousMap.sub_apply, ContinuousMap.const_apply]; exact sub_ne_zero.mpr (hx t)
  have hloop_y : (c - ContinuousMap.const unitInterval y) 0
      = (c - ContinuousMap.const unitInterval y) 1 := by
    rw [ContinuousMap.sub_apply, ContinuousMap.sub_apply, ContinuousMap.const_apply,
      ContinuousMap.const_apply, hloop]
  have hloop_x : (c - ContinuousMap.const unitInterval x) 0
      = (c - ContinuousMap.const unitInterval x) 1 := by
    rw [ContinuousMap.sub_apply, ContinuousMap.sub_apply, ContinuousMap.const_apply,
      ContinuousMap.const_apply, hloop]
  refine loopIndex_eq_of_pointwise_div_mem_slitPlane
    (c - ContinuousMap.const unitInterval y) (c - ContinuousMap.const unitInterval x)
    hne_y hne_x hloop_y hloop_x ?_
  intro t
  rw [ContinuousMap.sub_apply, ContinuousMap.sub_apply, ContinuousMap.const_apply,
    ContinuousMap.const_apply]
  exact div_sub_mem_slitPlane_of_notMem_segment (fun s hs => hseg t s hs)

/-- **The winding number of a loop avoiding a connected set joining `0` to `∞` vanishes.**

If the image of `p` is a connected subset of the Riemann sphere containing both `0` and `∞`, then
every closed loop avoiding it has index `0` about the origin.  The proof uses the local constancy
of the winding number `w ↦ loopIndex (c - w)` on the complement of the trace of `c`: it is `0` in a
neighbourhood of `∞`, hence — the trace of `p` being connected — equal to `0` at `0`. -/
theorem loopIndex_eq_zero_of_avoids_range
    {p : C(unitInterval, OnePoint ℂ)}
    (h0 : ((0 : ℂ) : OnePoint ℂ) ∈ Set.range p)
    (hinf : (OnePoint.infty : OnePoint ℂ) ∈ Set.range p)
    {c : C(unitInterval, ℂ)}
    (hav : ∀ t, ((c t : ℂ) : OnePoint ℂ) ∉ Set.range p) :
    loopIndex c = 0 := by
  classical
  by_cases hcl : (∀ t, c t ≠ 0) ∧ c 0 = c 1
  · obtain ⟨hne, hloop⟩ := hcl
    -- `R` bounds the trace of `c`
    obtain ⟨ρ, hρ⟩ := (isCompact_range c.continuous).isBounded.subset_closedBall (0 : ℂ)
    set R : ℝ := max ρ 0 with hRdef
    have hR0 : 0 ≤ R := le_max_right _ _
    have hRbound : ∀ t : unitInterval, ‖c t‖ ≤ R := by
      intro t
      have h := hρ (Set.mem_range_self t)
      rw [Metric.mem_closedBall, dist_zero_right] at h
      exact le_trans h (le_max_left _ _)
    -- far away from the trace the index vanishes
    have hfar : ∀ w : ℂ, R < ‖w‖ → windPhi c w = 0 := by
      intro w hw
      have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (lt_of_le_of_lt hR0 hw))
      have hneW : ∀ t, c t ≠ w := by
        intro t h
        have h2 := hRbound t
        rw [h] at h2
        linarith
      refine loopIndex_eq_zero_of_avoids_ray (ω := w) _
        (fun t => ?_) (?_ : (c - ContinuousMap.const unitInterval w) 0
            = (c - ContinuousMap.const unitInterval w) 1) hw0 (fun t r hr hcon => ?_)
      · rw [ContinuousMap.sub_apply, ContinuousMap.const_apply]
        exact sub_ne_zero.mpr (hneW t)
      · rw [ContinuousMap.sub_apply, ContinuousMap.sub_apply, ContinuousMap.const_apply,
          ContinuousMap.const_apply, hloop]
      · rw [ContinuousMap.sub_apply, ContinuousMap.const_apply] at hcon
        have hct : c t = ((1 + r : ℝ) : ℂ) * w := by
          rw [show ((1 + r : ℝ) : ℂ) = 1 + (r : ℂ) by push_cast; ring]
          linear_combination hcon
        have h1 : ‖c t‖ = (1 + r) * ‖w‖ := by
          rw [hct, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + r)]
        have h2 := hRbound t
        nlinarith [norm_nonneg w]
    -- `farSet R` is a neighbourhood of `∞` on which the index vanishes
    have hUcompl : (farSet R)ᶜ = ((↑) '' Metric.closedBall (0 : ℂ) R : Set (OnePoint ℂ)) := by
      ext a
      induction a using OnePoint.rec with
      | infty => simp [farSet]
      | coe w => simp [farSet, Metric.mem_closedBall, dist_eq_norm]
    have hUopen : IsOpen (farSet R) :=
      isClosed_compl_iff.mp (by
        rw [hUcompl]
        exact ((isCompact_closedBall (0 : ℂ) R).image OnePoint.continuous_coe).isClosed)
    have hUpsi : ∀ a ∈ farSet R, windPsi c a = 0 := by
      intro a ha
      rw [farSet] at ha
      induction a using OnePoint.rec with
      | infty => rfl
      | coe w => exact hfar w ha
    -- local constancy of the index along the connected set `range p`
    have hloc : IsLocallyConstant (fun z : ↥(Set.range p) => windPsi c (z : OnePoint ℂ)) := by
      rw [IsLocallyConstant.iff_eventually_eq]
      intro z
      obtain ⟨a, ha⟩ := z
      induction a using OnePoint.rec with
      | infty =>
        have hmem : {y : ↥(Set.range p) | ((y : OnePoint ℂ)) ∈ farSet R}
            ∈ nhds (⟨OnePoint.infty, ha⟩ : ↥(Set.range p)) := by
          apply IsOpen.mem_nhds (hUopen.preimage continuous_subtype_val)
          simp [farSet]
        refine Filter.mem_of_superset hmem (fun y hy => ?_)
        show windPsi c (y : OnePoint ℂ) = windPsi c (OnePoint.infty)
        rw [hUpsi _ hy]
        rfl
      | coe x =>
        have hxS : x ∉ Set.range c := by
          rintro ⟨t, ht⟩
          exact hav t (by rw [ht]; exact ha)
        obtain ⟨t₀, -, hmin⟩ := IsCompact.exists_isMinOn (isCompact_univ) (Set.univ_nonempty)
          (by fun_prop : ContinuousOn (fun t : unitInterval => ‖c t - x‖) Set.univ)
        set m : ℝ := ‖c t₀ - x‖ with hmdef
        have hmpos : 0 < m := by
          rw [hmdef]
          exact norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hxS ⟨t₀, h⟩))
        have hmin' : ∀ t : unitInterval, m ≤ ‖c t - x‖ := by
          intro t
          rw [hmdef]
          exact hmin (Set.mem_univ t)
        have hmem : {y : ↥(Set.range p) |
              ((y : OnePoint ℂ)) ∈ ((↑) '' Metric.ball x (m / 2) : Set (OnePoint ℂ))}
            ∈ nhds (⟨((x : ℂ) : OnePoint ℂ), ha⟩ : ↥(Set.range p)) := by
          apply IsOpen.mem_nhds
            ((OnePoint.isOpenMap_coe _ Metric.isOpen_ball).preimage continuous_subtype_val)
          exact ⟨x, Metric.mem_ball_self (by linarith), rfl⟩
        refine Filter.mem_of_superset hmem (fun y hy => ?_)
        obtain ⟨w, hw, hwy⟩ := hy
        have hwball : ‖w - x‖ < m / 2 := by
          rw [← dist_eq_norm]; exact Metric.mem_ball.mp hw
        have hwx : ∀ t, c t ≠ w := by
          intro t hcon
          have h1 : ‖c t - x‖ = ‖w - x‖ := by rw [hcon]
          have h2 := hmin' t
          rw [h1] at h2
          linarith
        have hseg : ∀ t s, s ∈ Set.Icc (0 : ℝ) 1 → c t ≠ (1 - s) * x + s * w := by
          intro t s hs hcon
          have h1 : ‖c t - x‖ = s * ‖w - x‖ := by
            rw [hcon, show (1 - s) * x + s * w - x = s * (w - x) by ring, norm_mul,
              Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
          have h2 := hmin' t
          rw [h1] at h2
          have h3 : s * ‖w - x‖ ≤ ‖w - x‖ := by
            nlinarith [norm_nonneg (w - x), hs.1, hs.2]
          linarith
        have hseg2 := loopIndex_segment hloop (x := x) (y := w) (fun t h => hxS ⟨t, h⟩) hwx hseg
        show windPsi c (y : OnePoint ℂ) = windPsi c ((x : ℂ) : OnePoint ℂ)
        rw [show (y : OnePoint ℂ) = ((w : ℂ) : OnePoint ℂ) from hwy.symm]
        exact hseg2
    have hpre : PreconnectedSpace ↥(Set.range p) :=
      isPreconnected_iff_preconnectedSpace.mp (isPreconnected_range p.continuous)
    have hconst := hloc.apply_eq_of_preconnectedSpace
      (⟨((0 : ℂ) : OnePoint ℂ), h0⟩ : ↥(Set.range p)) (⟨OnePoint.infty, hinf⟩ : ↥(Set.range p))
    have hφ0 : windPhi c 0 = 0 := hconst
    have hcongr : loopIndex c = windPhi c 0 :=
      loopIndex_congr
        (c := c) (d := c - ContinuousMap.const unitInterval 0)
        (fun t => by rw [ContinuousMap.sub_apply, ContinuousMap.const_apply, sub_zero])
        hne
        (fun t => by
          rw [ContinuousMap.sub_apply, ContinuousMap.const_apply]
          exact sub_ne_zero.mpr (hne t))
        hloop
        (by rw [ContinuousMap.sub_apply, ContinuousMap.sub_apply, ContinuousMap.const_apply,
          ContinuousMap.const_apply, hloop])
    rw [hcongr, hφ0]
  · unfold loopIndex
    rw [dif_neg hcl]


/-- **Lifting through the exponential on a path-connected domain.**

Let `A` be path-connected and locally path-connected, `g : A → ℂ` continuous and nowhere zero, and
suppose every closed loop in the image of `g` has index `0`.  Then `g` has a continuous logarithm.

This is the lifting criterion for the covering map `Complex.exp : ℂ → ℂ*`, together with the
explicit null-homotopy of the relevant loops: a loop of index `0` lifts to a *closed* path in `ℂ`,
and contracting that path in the (contractible) plane and applying `exp` contracts the loop. -/
theorem exists_exp_lift {A : Type*} [TopologicalSpace A] [PathConnectedSpace A]
    [LocallyPathConnectedSpace A] (g : C(A, ℂ)) (hg : ∀ a, g a ≠ 0)
    (hW : ∀ c : C(unitInterval, ℂ), (∀ t, ∃ a : A, c t = g a) → c 0 = c 1 →
      loopIndex c = 0) :
    ∃ F : C(A, ℂ), ∀ a, Complex.exp (F a) = g a := by
  classical
  let X' : Type := {z : ℂ // z ≠ 0}
  let pel : ℂ → X' := fun w => ⟨Complex.exp w, Complex.exp_ne_zero w⟩
  have cov : IsCoveringMap pel := Complex.isCoveringMap_exp
  let f : C(A, X') := ⟨fun a => ⟨g a, hg a⟩, Continuous.subtype_mk g.continuous hg⟩
  let a₀ : A := Classical.choice (inferInstance : Nonempty A)
  let e₀ : ℂ := Complex.log (g a₀)
  have he : pel e₀ = f a₀ := Subtype.ext (Complex.exp_log (hg a₀))
  have hmap : FundamentalGroup.map f a₀ = 1 := by
    refine MonoidHom.ext fun γ => ?_
    change (FundamentalGroup.map f a₀) γ = 1
    revert γ
    refine Path.Homotopic.Quotient.ind (x := a₀) (y := a₀)
      (motive := fun γ => (FundamentalGroup.map f a₀) γ = 1) ?_
    intro q
    rw [FundamentalGroup.map_apply]
    have hq0 : q 0 = a₀ := Path.source q
    have hq1 : q 1 = a₀ := Path.target q
    let qX : C(unitInterval, X') := (q.map f.continuous).toContinuousMap
    have hqmap : ∀ t, qX t = f (q t) := fun t => rfl
    have hqX0 : qX 0 = pel e₀ := by rw [hqmap, hq0]; exact he.symm
    let Γ : C(unitInterval, ℂ) := cov.liftPath qX e₀ hqX0
    have hΓ0 : Γ 0 = e₀ := cov.liftPath_zero qX e₀ hqX0
    have hΓlifts : ∀ t, pel (Γ t) = qX t :=
      fun t => congrFun (cov.liftPath_lifts qX e₀ hqX0) t
    let c : C(unitInterval, ℂ) :=
      ⟨fun t => (qX t : X').val, continuous_subtype_val.comp qX.continuous⟩
    have hc0 : ∀ t, c t ≠ 0 := fun t => (qX t).2
    have hclift : ∀ t, Complex.exp (Γ t) = c t :=
      fun t => congrArg Subtype.val (hΓlifts t)
    have hcloop : c 0 = c 1 := by
      have h : qX 0 = qX 1 := by rw [hqmap, hqmap, hq0, hq1]
      exact congrArg Subtype.val h
    have hcimg : ∀ t, ∃ a : A, c t = g a := by
      intro t
      exact ⟨q t, by rw [show c t = (qX t : X').val from rfl, hqmap]; rfl⟩
    have hLI : loopIndex c = 0 := hW c hcimg hcloop
    have hΓ1 : Γ 1 = e₀ := by
      have h := loopIndex_spec c hc0 hcloop Γ hclift
      rw [hLI] at h
      simp only [Int.cast_zero, zero_mul] at h
      rw [sub_eq_zero] at h
      exact h.trans hΓ0
    have hHom : Path.Homotopic (q.map f.continuous) (Path.refl (f a₀)) := by
      let Hmap : unitInterval × unitInterval → X' := fun ts =>
        ⟨Complex.exp ((1 - (ts.1 : ℝ)) * Γ ts.2 + (ts.1 : ℝ) * Γ 0), Complex.exp_ne_zero _⟩
      have hHcont : Continuous Hmap := by
        refine Continuous.subtype_mk ?_ _
        exact Complex.continuous_exp.comp (by fun_prop)
      have hH0 : ∀ s : unitInterval, Hmap (0, s) = (q.map f.continuous) s := by
        intro s
        refine Subtype.ext ?_
        show Complex.exp ((1 - ((0 : unitInterval) : ℝ)) * Γ s
          + ((0 : unitInterval) : ℝ) * Γ 0) = (qX s).val
        have harg : (1 - ((0 : unitInterval) : ℝ)) * Γ s + ((0 : unitInterval) : ℝ) * Γ 0
            = Γ s := by norm_num
        rw [harg]
        exact congrArg Subtype.val (hΓlifts s)
      have hH1 : ∀ s : unitInterval, Hmap (1, s) = (Path.refl (f a₀)) s := by
        intro s
        refine Subtype.ext ?_
        show Complex.exp ((1 - ((1 : unitInterval) : ℝ)) * Γ s
          + ((1 : unitInterval) : ℝ) * Γ 0) = ((f a₀ : X') : ℂ)
        have harg : (1 - ((1 : unitInterval) : ℝ)) * Γ s + ((1 : unitInterval) : ℝ) * Γ 0
            = e₀ := by
          rw [hΓ0]; norm_num
        rw [harg]
        exact Complex.exp_log (hg a₀)
      have hHprop : ∀ t : unitInterval, ∀ s ∈ ({0, 1} : Set unitInterval),
          Hmap (t, s) = (q.map f.continuous) s := by
        intro t s hs
        rcases hs with hs | hs
        · subst hs
          refine Subtype.ext ?_
          show Complex.exp ((1 - (t : ℝ)) * Γ (0 : unitInterval) + (t : ℝ) * Γ 0)
            = (qX 0).val
          have harg : (1 - (t : ℝ)) * Γ (0 : unitInterval) + (t : ℝ) * Γ 0 = e₀ := by
            rw [hΓ0]; ring
          rw [harg, hqmap, hq0]
          exact Complex.exp_log (hg a₀)
        · subst hs
          refine Subtype.ext ?_
          show Complex.exp ((1 - (t : ℝ)) * Γ (1 : unitInterval) + (t : ℝ) * Γ 0)
            = (qX 1).val
          have harg : (1 - (t : ℝ)) * Γ (1 : unitInterval) + (t : ℝ) * Γ 0 = e₀ := by
            rw [hΓ1, hΓ0]; ring
          rw [harg, hqmap, hq1]
          exact Complex.exp_log (hg a₀)
      exact ⟨{ toHomotopy := ContinuousMap.Homotopy.mk ⟨Hmap, hHcont⟩ hH0 hH1,
               prop' := fun t s hs => hHprop t s hs }⟩
    rw [← Path.Homotopic.Quotient.mk_map q f, FundamentalGroup.one_def]
    exact Path.Homotopic.Quotient.eq.mpr hHom
  have hle : (FundamentalGroup.map f a₀).range
      ≤ (FundamentalGroup.mapOfEq ⟨pel, cov.continuous⟩ he).range := by
    rw [hmap, MonoidHom.range_one]
    exact bot_le
  obtain ⟨F, hF, -⟩ := cov.existsUnique_continuousMap_lifts_of_range_le he hle
  refine ⟨F, fun a => ?_⟩
  exact congrArg Subtype.val (congrFun hF.2 a)


/-- **A continuous logarithm on the complement of a cut from `0` to `∞`.**

For any continuous path `γ : [0,1] → ℂ ∪ {∞}` with `γ 0 = 0` and `γ 1 = ∞`, the identity of
`ℂ*` restricted to `ℂ \ range γ` has a continuous logarithm. -/
theorem log_compl_cut {γ : C(unitInterval, RiemannSphere)}
    (h0 : γ 0 = ((0:ℂ) : RiemannSphere)) (h1 : γ 1 = OnePoint.infty) :
    ∃ f : {z : ℂ // (z : RiemannSphere) ∈ (Set.range γ)ᶜ} → ℂ,
      Continuous f ∧ ∀ z, Complex.exp (f z) = (z : ℂ) := by
  classical
  have h0range : ((0 : ℂ) : OnePoint ℂ) ∈ Set.range γ := ⟨0, h0⟩
  have hinftyrange : (OnePoint.infty : OnePoint ℂ) ∈ Set.range γ := ⟨1, h1⟩
  set B : Set ℂ := {z : ℂ | ((z : ℂ) : OnePoint ℂ) ∈ (Set.range γ)ᶜ} with hBdef
  have hopenB : IsOpen B := by
    rw [hBdef]
    exact ((isCompact_range γ.continuous).isClosed.isOpen_compl).preimage OnePoint.continuous_coe
  haveI hB_lpc : LocallyPathConnectedSpace ↥B := hopenB.locallyPathConnectedSpace
  have hB0 : ∀ z ∈ B, z ≠ 0 := by
    intro z hz hz0
    rw [hBdef] at hz
    exact hz ⟨0, by rw [h0, hz0]⟩
  have hBmem : ∀ z : ℂ, z ∈ B → ((z : ℂ) : OnePoint ℂ) ∈ (Set.range γ)ᶜ := by
    intro z hz
    rwa [hBdef] at hz
  -- a continuous logarithm on each connected component
  have hlift_data : ∀ z : ↥B, ∃ φ : C(↥(connectedComponent z), ℂ),
      ∀ w, Complex.exp (φ w) = ((w : ↥B) : ℂ) := by
    intro z
    haveI hCopen : IsOpen (connectedComponent z) := isOpen_connectedComponent
    haveI hClpc : LocallyPathConnectedSpace ↥(connectedComponent z) :=
      hCopen.locallyPathConnectedSpace
    haveI hCconn : ConnectedSpace ↥(connectedComponent z) :=
      isConnected_iff_connectedSpace.mp isConnected_connectedComponent
    haveI hCpc : PathConnectedSpace ↥(connectedComponent z) :=
      PathConnectedSpace.of_locallyPathConnectedSpace
    refine exists_exp_lift ⟨fun w : ↥(connectedComponent z) => ((w : ↥B) : ℂ), by fun_prop⟩ ?_ ?_
    · intro w
      exact hB0 (w.1.1) (w.1.2)
    · intro c hc _
      refine loopIndex_eq_zero_of_avoids_range h0range hinftyrange (fun t => ?_)
      obtain ⟨a, ha⟩ := hc t
      rw [ha]
      exact hBmem ((a : ↥B) : ℂ) (a : ↥B).2
  -- the cover by connected components, and the glued lift
  let D : ConnectedComponents ↥B → Set ↥B := fun c => ConnectedComponents.mk ⁻¹' {c}
  have hD_eq : ∀ z : ↥B, D (ConnectedComponents.mk z) = connectedComponent z :=
    fun z => connectedComponents_preimage_singleton
  -- a logarithm on each component, extended to the whole space (uniform type)
  have hcompLift : ∀ c : ConnectedComponents ↥B, ∃ φ : ↥B → ℂ,
      ContinuousOn φ (D c) ∧ ∀ w ∈ D c, Complex.exp (φ w) = ((w : ↥B) : ℂ) := by
    intro c
    obtain ⟨z, rfl⟩ := ConnectedComponents.surjective_coe c
    rw [hD_eq z]
    obtain ⟨ψ, hψ⟩ := hlift_data z
    refine ⟨fun w => if h : w ∈ connectedComponent z then ψ ⟨w, h⟩ else 0, ?_, ?_⟩
    · refine continuousOn_iff_continuous_domRestrict.mpr ?_
      refine ψ.continuous.congr ?_
      intro w
      show ψ w = (if h : (w : ↥B) ∈ connectedComponent z then
        ψ ⟨(w : ↥B), h⟩ else 0)
      rw [dif_pos w.2]
    · intro w hw
      show Complex.exp (if h : w ∈ connectedComponent z then ψ ⟨w, h⟩ else 0) = ((w : ↥B) : ℂ)
      rw [dif_pos hw]
      exact hψ ⟨w, hw⟩
  let F : ↥B → ℂ := fun z => (Classical.choose (hcompLift (ConnectedComponents.mk z))) z
  have hFexp : ∀ z : ↥B, Complex.exp (F z) = ((z : ↥B) : ℂ) := by
    intro z
    exact (Classical.choose_spec (hcompLift (ConnectedComponents.mk z))).2 z
      (by rw [hD_eq z]; exact mem_connectedComponent)
  have hFcont : Continuous F := by
    refine continuous_of_cover_nhds (s := D) ?_ ?_
    · intro x
      refine ⟨ConnectedComponents.mk x, ?_⟩
      rw [hD_eq x]
      exact IsOpen.mem_nhds isOpen_connectedComponent mem_connectedComponent
    · intro c
      obtain ⟨z, rfl⟩ := ConnectedComponents.surjective_coe c
      refine ContinuousOn.congr (Classical.choose_spec (hcompLift (ConnectedComponents.mk z))).1 ?_
      intro w hw
      have hmk : ConnectedComponents.mk w = ConnectedComponents.mk z := by
        have h2 := hw
        simp only [D, Set.mem_preimage, Set.mem_singleton_iff] at h2
        exact h2
      show (Classical.choose (hcompLift (ConnectedComponents.mk w))) w =
        (Classical.choose (hcompLift (ConnectedComponents.mk z))) w
      rw [hmk]
  refine ⟨F, hFcont, ?_⟩
  intro z
  exact hFexp z
end

end Work.Smooth.SphereJordan
