import Mathlib
import Submission.Work.RPB1a.Caratheodory.Brouwer.brouwer_fixed_point_square
import Submission.Work.RPB1a.Caratheodory.Brouwer.brouwer_fixed_point_square_scaled
import Submission.Work.RPB1a.Caratheodory.Brouwer.exists_arc_Icc_exp
import Submission.Work.RPB1a.Caratheodory.Brouwer.exists_continuous_retraction_of_arc
import Submission.Work.RPB1a.Caratheodory.Brouwer.exists_square_boundary_subset_of_isCompact_isUnbounded_component

set_option autoImplicit false

namespace Work.RPB1a.Caratheodory.Brouwer

open Set Metric

/-! ## The sup-norm square around a point

Everything below works with the sup-norm `sm p y = max |y.1 - p.1| |y.2 - p.2|`, whose closed
unit ball is an axis-parallel square.  This keeps the fixed point argument in the same
coordinates as `brouwer_fixed_point_square`. -/

/-- The sup-norm distance from `y` to `p` (in the two coordinate directions). -/
private def sm (p y : ℝ × ℝ) : ℝ := max |y.1 - p.1| |y.2 - p.2|

/-- The closed square with centre `p` and "radius" `R` in the sup norm. -/
private def sq (p : ℝ × ℝ) (R : ℝ) : Set (ℝ × ℝ) := {y | sm p y ≤ R}

/-- The boundary of the square `sq p R`. -/
private def sqB (p : ℝ × ℝ) (R : ℝ) : Set (ℝ × ℝ) := {y | sm p y = R}

/-- Radial projection from `p` to the boundary of the square of radius `R`. -/
private noncomputable def proj (p : ℝ × ℝ) (R : ℝ) (y : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 + (R / sm p y) * (y.1 - p.1), p.2 + (R / sm p y) * (y.2 - p.2))

/-- The same radial projection, cut off below by `δ > 0` so that it is continuous everywhere. -/
private noncomputable def projSafe (p : ℝ × ℝ) (R δ : ℝ) (y : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 + (R / max (sm p y) δ) * (y.1 - p.1),
   p.2 + (R / max (sm p y) δ) * (y.2 - p.2))

/-- The half-turn of the plane about `p`. -/
private def half (p : ℝ × ℝ) (y : ℝ × ℝ) : ℝ × ℝ := (2 * p.1 - y.1, 2 * p.2 - y.2)

private lemma continuous_sm (p : ℝ × ℝ) : Continuous fun y : ℝ × ℝ => sm p y := by
  simp only [sm]
  fun_prop

private lemma sm_nonneg (p y : ℝ × ℝ) : 0 ≤ sm p y := le_max_of_le_left (abs_nonneg _)

private lemma sm_self (p : ℝ × ℝ) : sm p p = 0 := by simp [sm]

private lemma sm_eq_zero {p y : ℝ × ℝ} (h : sm p y = 0) : y = p := by
  have h1 : |y.1 - p.1| = 0 :=
    le_antisymm (le_trans (le_max_left _ _) (le_of_eq h)) (abs_nonneg _)
  have h2 : |y.2 - p.2| = 0 :=
    le_antisymm (le_trans (le_max_right _ _) (le_of_eq h)) (abs_nonneg _)
  rw [abs_eq_zero, sub_eq_zero] at h1 h2
  exact Prod.ext h1 h2

private lemma sm_pos_of_ne {p y : ℝ × ℝ} (h : y ≠ p) : 0 < sm p y :=
  lt_of_le_of_ne (sm_nonneg p y) (fun h' => h (sm_eq_zero h'.symm))

private lemma isClosed_sq (p : ℝ × ℝ) (R : ℝ) : IsClosed (sq p R) :=
  isClosed_Iic.preimage (continuous_sm p)

private lemma sq_bound (p : ℝ × ℝ) (R : ℝ) : Bornology.IsBounded (sq p R) := by
  refine (Metric.isBounded_iff_subset_ball (0 : ℝ × ℝ)).mpr
    ⟨|p.1| + |p.2| + |R| + 2, fun y hy => ?_⟩
  have h1 : |y.1 - p.1| ≤ sm p y := le_max_left _ _
  have h2 : |y.2 - p.2| ≤ sm p y := le_max_right _ _
  have h3 : sm p y ≤ R := hy
  rw [Metric.mem_ball, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  have h4 : |y.1| ≤ |p.1| + |R| + 1 := by
    calc |y.1| ≤ |y.1 - p.1| + |p.1| := by
          calc |y.1| = |(y.1 - p.1) + p.1| := by ring_nf
            _ ≤ |y.1 - p.1| + |p.1| := abs_add_le _ _
      _ ≤ R + |p.1| := add_le_add (le_trans h1 h3) le_rfl
      _ ≤ |p.1| + |R| + 1 := by linarith [le_abs_self R]
  have h5 : |y.2| ≤ |p.2| + |R| + 1 := by
    calc |y.2| ≤ |y.2 - p.2| + |p.2| := by
          calc |y.2| = |(y.2 - p.2) + p.2| := by ring_nf
            _ ≤ |y.2 - p.2| + |p.2| := abs_add_le _ _
      _ ≤ R + |p.2| := add_le_add (le_trans h2 h3) le_rfl
      _ ≤ |p.2| + |R| + 1 := by linarith [le_abs_self R]
  have h6 : max |y.1| |y.2| ≤ |p.1| + |p.2| + |R| + 1 := by
    refine max_le (h4.trans ?_) (h5.trans ?_) <;>
      linarith [abs_nonneg p.1, abs_nonneg p.2, abs_nonneg R]
  linarith [h6]

private lemma isCompact_sq (p : ℝ × ℝ) (R : ℝ) : IsCompact (sq p R) :=
  Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_sq p R, sq_bound p R⟩

private lemma sm_proj {p : ℝ × ℝ} {R : ℝ} (hR : 0 < R) {y : ℝ × ℝ} (hy : y ≠ p) :
    sm p (proj p R y) = R := by
  have hm : 0 < sm p y := sm_pos_of_ne hy
  have hRdiv : (0:ℝ) < R / max |y.1 - p.1| |y.2 - p.2| := by
    rw [show max |y.1 - p.1| |y.2 - p.2| = sm p y from rfl]
    exact div_pos hR hm
  have hsm : sm p (proj p R y)
      = max ((R / sm p y) * |y.1 - p.1|) ((R / sm p y) * |y.2 - p.2|) := by
    simp only [proj, sm, add_sub_cancel_left, abs_mul, abs_of_pos hRdiv]
  rw [hsm, ← mul_max_of_nonneg _ _ (le_of_lt (div_pos hR hm)),
    show max |y.1 - p.1| |y.2 - p.2| = sm p y from rfl]
  exact div_mul_cancel₀ R (ne_of_gt hm)

private lemma proj_eq_self {p : ℝ × ℝ} {R : ℝ} (hR : 0 < R) {y : ℝ × ℝ}
    (hy : sm p y = R) : proj p R y = y := by
  have hne : sm p y ≠ 0 := by rw [hy]; exact ne_of_gt hR
  have hdiv : R / sm p y = 1 := by rw [← hy, div_self hne]
  simp only [proj, hdiv, one_mul]
  exact Prod.ext (by ring) (by ring)

private lemma projSafe_eq_proj {p : ℝ × ℝ} {R δ : ℝ} {y : ℝ × ℝ} (h : δ ≤ sm p y) :
    projSafe p R δ y = proj p R y := by
  rw [projSafe, proj, max_eq_left h]

private lemma continuous_projSafe (p : ℝ × ℝ) (R : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Continuous (projSafe p R δ) := by
  have hne : ∀ y : ℝ × ℝ, max (sm p y) δ ≠ 0 := fun y =>
    ne_of_gt (lt_of_lt_of_le hδ (le_max_right _ _))
  have h1 : Continuous fun y : ℝ × ℝ => R / max (sm p y) δ :=
    continuous_const.div ((continuous_sm p).max continuous_const) hne
  change Continuous fun y : ℝ × ℝ =>
    (p.1 + (R / max (sm p y) δ) * (y.1 - p.1),
     p.2 + (R / max (sm p y) δ) * (y.2 - p.2))
  exact ((continuous_const.add (h1.mul (continuous_fst.sub continuous_const))).prodMk
    (continuous_const.add (h1.mul (continuous_snd.sub continuous_const))))

private lemma sm_half (p y : ℝ × ℝ) : sm p (half p y) = sm p y := by
  simp only [half, sm]
  rw [show (2 * p.1 - y.1) - p.1 = -(y.1 - p.1) by ring,
      show (2 * p.2 - y.2) - p.2 = -(y.2 - p.2) by ring, abs_neg, abs_neg]

private lemma half_ne_self {p y : ℝ × ℝ} {R : ℝ} (hR : 0 < R) (hy : sm p y = R) :
    half p y ≠ y := by
  intro h
  have h1 : 2 * p.1 - y.1 = y.1 := congrArg Prod.fst h
  have h2 : 2 * p.2 - y.2 = y.2 := congrArg Prod.snd h
  have hy1 : y.1 = p.1 := by linarith
  have hy2 : y.2 = p.2 := by linarith
  have : sm p y = 0 := by rw [show y = p from Prod.ext hy1 hy2, sm_self]
  rw [this] at hy
  linarith

private lemma frontier_closure_subset {X : Type*} [TopologicalSpace X] (s : Set X) :
    frontier (closure s) ⊆ frontier s := by
  have hsub : (closure s)ᶜ ⊆ sᶜ := by
    intro y hy
    simp only [mem_compl_iff] at hy ⊢
    exact fun hyU => hy (subset_closure hyU)
  intro x hx
  rw [frontier_eq_closure_inter_closure] at hx
  rw [frontier_eq_closure_inter_closure]
  exact ⟨by simpa only [closure_closure] using hx.1, closure_mono hsub hx.2⟩

private lemma continuous_half (p : ℝ × ℝ) : Continuous (half p) := by
  change Continuous fun y : ℝ × ℝ => (2 * p.1 - y.1, 2 * p.2 - y.2)
  fun_prop

/-- **Brouwer contraption.**  A continuous self-map `f` of the square `sq p R` which misses the
centre `p` and fixes every point of the boundary is impossible: composing with the radial
projection onto the boundary and then the half-turn about `p` would give a fixed-point free
self-map of the square. -/
private lemma no_fixed_point_free_selfmap
    (p : ℝ × ℝ) {R : ℝ} (hR : 0 < R) (f : ℝ × ℝ → ℝ × ℝ) (hf : Continuous f)
    (hsub : ∀ y, sm p y ≤ R → sm p (f y) ≤ R)
    (hne : ∀ y, sm p y ≤ R → f y ≠ p)
    (hfix : ∀ y, sm p y = R → f y = y) : False := by
  -- a positive lower bound for `sm p (f y)` on the square
  have hDcomp : IsCompact (sq p R) := isCompact_sq p R
  have himage : IsCompact (f '' sq p R) := hDcomp.image hf
  have hne' : (f '' sq p R).Nonempty :=
    ⟨f p, p, by show sm p p ≤ R; rw [sm_self]; exact le_of_lt hR, rfl⟩
  have hp_not : p ∉ f '' sq p R := by
    rintro ⟨y, hy, hyf⟩
    exact hne y hy hyf
  obtain ⟨z₀, hz₀mem, hz₀min⟩ := himage.exists_isMinOn hne' (continuous_sm p).continuousOn
  set δ := sm p z₀ with hδdef
  have hδpos : 0 < δ := by
    rcases lt_or_eq_of_le (sm_nonneg p z₀) with h | h
    · exact h
    · have hzp : z₀ = p := sm_eq_zero h.symm
      exact absurd (hzp ▸ hz₀mem) hp_not
  have hδle : ∀ y, sm p y ≤ R → δ ≤ sm p (f y) := fun y hy => hz₀min ⟨y, hy, rfl⟩
  have h0 : sm p p ≤ R := by rw [sm_self]; exact le_of_lt hR
  have hδR : δ ≤ R := (hδle p h0).trans (hsub p h0)
  -- the fixed-point free self-map of the square
  let F : ℝ × ℝ → ℝ × ℝ := fun y => half p (projSafe p R δ (f y))
  have hFcont : Continuous F := by
    simp only [F]
    exact ((continuous_half p).comp (continuous_projSafe p R hδpos)).comp hf
  have hFmaps : ∀ y, sm p y ≤ R → sm p (F y) ≤ R := by
    intro y hy
    have hfy : f y ≠ p := hne y hy
    have h1 : sm p (projSafe p R δ (f y)) = R := by
      rw [projSafe_eq_proj (hδle y hy), sm_proj hR hfy]
    simp only [F, sm_half]
    linarith [h1]
  obtain ⟨y, hyD, hyfix⟩ := brouwer_fixed_point_square_scaled p hR F hFcont hFmaps
  have hyB : sm p y = R := by
    have h1 : sm p (F y) = R := by
      have hfy : f y ≠ p := hne y hyD
      simp only [F, sm_half]
      rw [projSafe_eq_proj (hδle y hyD), sm_proj hR hfy]
    rwa [hyfix] at h1
  have hfy : f y = y := hfix y hyB
  have hFy : F y = half p y := by
    simp only [F]
    rw [hfy, projSafe_eq_proj (by rw [hyB]; exact hδR), proj_eq_self hR hyB]
  have : half p y = y := by rw [← hFy]; exact hyfix
  exact half_ne_self hR hyB this

/-- If the complement of a Jordan curve has a bounded component, then every component of the
complement of the curve has the curve as its frontier.

Route (Gauld, Lemma 5.6): let `U` be a component and `p` a point of a bounded component (of `U`
itself if `U` is bounded).  Since `∂U ⊆ range γ` and a proper closed subset of a circle is
contained in a proper subarc, take an arc `A ⊊ range γ` containing `∂U`.  Let `D` be a large disc
around `p` containing the curve.  Tietze's extension theorem (an arc is an absolute retract) gives
`r : D → A` with `r = id` on `A`; glue `r` on one side of the curve with the identity on the other
to get `f : D → D \ {p}`; composing with the outward projection from `p`, then with a half-turn of
`∂D`, contradicts `brouwer_fixed_point_square`.

WARNING: do NOT import `Submission.Work.RPB1a.Caratheodory.jordan_separation` (it is downstream of
this development). -/
theorem frontier_component_eq_of_bounded
    (γ : Circle → ℝ × ℝ) (hγ : Continuous γ) (hinj : Function.Injective γ)
    (hbdd : ∃ x : ℝ × ℝ, x ∉ Set.range γ ∧
      Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) x)) :
    ∀ x : ℝ × ℝ, x ∉ Set.range γ →
      frontier (connectedComponentIn ((Set.range γ)ᶜ) x) = Set.range γ := by
  classical
  intro x₀ hx₀
  set K : Set (ℝ × ℝ) := Set.range γ with hKdef
  have hKcomp : IsCompact K := isCompact_range hγ
  have hKclosed : IsClosed K := hKcomp.isClosed
  set U : Set (ℝ × ℝ) := connectedComponentIn (Kᶜ) x₀ with hUdef
  have hx₀G : x₀ ∈ Kᶜ := by rw [hKdef]; exact hx₀
  have hx₀U : x₀ ∈ U := by rw [hUdef]; exact mem_connectedComponentIn hx₀G
  have hUsub : U ⊆ Kᶜ := by rw [hUdef]; exact connectedComponentIn_subset _ _
  have hUopen : IsOpen U := by
    rw [hUdef]; exact hKclosed.isOpen_compl.connectedComponentIn
  -- a component is relatively closed in the complement of the curve
  have hUcl : Kᶜ ∩ closure U ⊆ U := by
    intro y hy
    by_contra hyU
    set V : Set (ℝ × ℝ) := connectedComponentIn (Kᶜ) y with hVdef
    have hVy : y ∈ V := by rw [hVdef]; exact mem_connectedComponentIn hy.1
    have hVopen : IsOpen V := by
      rw [hVdef]; exact hKclosed.isOpen_compl.connectedComponentIn
    obtain ⟨w, hwV, hwU⟩ := mem_closure_iff.mp hy.2 V hVopen hVy
    have h1 : V = U := by
      rw [hVdef, hUdef]
      exact (connectedComponentIn_eq hwV).trans ((connectedComponentIn_eq hwU).symm)
    exact hyU (h1 ▸ hVy)
  -- the frontier of a component is contained in the curve
  have hfrsub : frontier U ⊆ K := by
    intro z hz
    by_contra hzK
    have hznotU : z ∉ U := by
      have h := hz
      rw [hUopen.frontier_eq] at h
      exact h.2
    exact hznotU (hUcl ⟨by simpa using hzK, frontier_subset_closure hz⟩)
  by_contra hgoal
  -- a point of the curve outside the frontier, and an arc containing the frontier
  obtain ⟨zst, hzst⟩ : ∃ z : Circle, γ z ∉ frontier U := by
    by_contra h
    push_neg at h
    exact hgoal (Subset.antisymm hfrsub fun y hy => by
      rw [hKdef] at hy
      obtain ⟨z, rfl⟩ := hy
      exact h z)
  set D₀ : Set Circle := {z | γ z ∈ frontier U} with hD₀def
  have hD₀closed : IsClosed D₀ := isClosed_frontier.preimage hγ
  have hD₀ne : D₀ ≠ Set.univ := by
    intro h
    have hmem : zst ∈ D₀ := by rw [h]; exact mem_univ zst
    rw [hD₀def] at hmem
    exact hzst hmem
  obtain ⟨a, b, hab, hb2, hD₀sub⟩ := exists_arc_Icc_exp D₀ hD₀closed hD₀ne
  set u : ℝ → ℝ × ℝ := fun t => γ (Circle.exp t) with hudef
  have hucont : Continuous u := hγ.comp Circle.exp.continuous
  have hinj_u : Set.InjOn u (Set.Icc a b) := by
    intro s hs t ht hst
    exact Circle.exp_injOn_Icc hb2 hs ht (hinj hst)
  obtain ⟨r, hrcont, hrfix, hrrange⟩ := exists_continuous_retraction_of_arc u hucont hab hinj_u
  have hAfr : frontier U ⊆ u '' Set.Icc a b := by
    intro y hy
    have hyK : y ∈ K := hfrsub hy
    rw [hKdef] at hyK
    obtain ⟨z, rfl⟩ := hyK
    have hzD : z ∈ D₀ := hy
    obtain ⟨t, ht, rfl⟩ := hD₀sub hzD
    exact ⟨t, ht, rfl⟩
  have hAK : u '' Set.Icc a b ⊆ K := by
    rintro y ⟨t, ht, rfl⟩
    rw [hKdef]
    exact ⟨Circle.exp t, rfl⟩
  rcases hbdd with ⟨x₁, hx₁, hbdd₁⟩
  have hx₁G : x₁ ∈ Kᶜ := by rw [hKdef]; exact hx₁
  by_cases hUb : Bornology.IsBounded U
  · -- Case 1: the component `U` is bounded; use a point of `U` as centre.
    have hScomp : IsCompact (closure U ∪ K) := hUb.isCompact_closure.union hKcomp
    have hSne : (closure U ∪ K).Nonempty := by
      refine ⟨γ 1, Or.inr ?_⟩
      rw [hKdef]; exact ⟨1, rfl⟩
    obtain ⟨y₀, -, hy₀max⟩ := hScomp.exists_isMaxOn hSne (continuous_sm x₀).continuousOn
    set R : ℝ := sm x₀ y₀ + 1 with hRdef
    have hRpos : 0 < R := by rw [hRdef]; linarith [sm_nonneg x₀ y₀]
    have hSle : ∀ y ∈ closure U ∪ K, sm x₀ y < R := by
      intro y hy
      have h : sm x₀ y ≤ sm x₀ y₀ := by
        have := hy₀max hy
        simpa only [mem_setOf_eq] using this
      rw [hRdef]
      linarith
    let f : ℝ × ℝ → ℝ × ℝ := fun y => if y ∈ closure U then r y else y
    have hfcont : Continuous f := by
      have hfront : ∀ y ∈ frontier (closure U), r y = id y := by
        intro y hy
        obtain ⟨t, ht, hty⟩ := hAfr (frontier_closure_subset U hy)
        rw [← hty]
        exact hrfix t ht
      have h := continuous_if (p := fun y : ℝ × ℝ => y ∈ closure U) hfront
        hrcont.continuousOn continuous_id.continuousOn
      exact h
    refine no_fixed_point_free_selfmap x₀ hRpos f hfcont ?_ ?_ ?_
    · intro y hy
      by_cases hyU : y ∈ closure U
      · have hfy : f y = r y := by simp only [f]; rw [if_pos hyU]
        rw [hfy]
        exact le_of_lt (hSle _ (Or.inr (hAK (hrrange y))))
      · have hfy : f y = y := by simp only [f]; rw [if_neg hyU]
        rw [hfy]
        exact hy
    · intro y hy
      by_cases hyU : y ∈ closure U
      · have hfy : f y = r y := by simp only [f]; rw [if_pos hyU]
        rw [hfy]
        intro hcon
        have hKmem : x₀ ∈ K := hcon ▸ hAK (hrrange y)
        rw [hKdef] at hKmem
        exact hx₀ hKmem
      · have hfy : f y = y := by simp only [f]; rw [if_neg hyU]
        rw [hfy]
        intro hcon
        exact hyU (hcon ▸ subset_closure hx₀U)
    · intro y hy
      have hyU : y ∉ closure U := by
        intro hc
        have h := hSle y (Or.inl hc)
        linarith
      simp only [f]
      rw [if_neg hyU]
  · -- Case 2: the component `U` is unbounded; use a point of the bounded component.
    have hU₁disj : (connectedComponentIn (Kᶜ) x₁) ∩ closure U = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro y ⟨hy₁, hycl⟩
      have hy_nU : y ∉ U := by
        intro hyU
        have hcomp : connectedComponentIn (Kᶜ) x₁ = U := by
          rw [hUdef]
          exact (connectedComponentIn_eq hy₁).trans ((connectedComponentIn_eq hyU).symm)
        exact hUb (hcomp ▸ hbdd₁)
      have hyfr : y ∈ frontier U := by
        rw [hUopen.frontier_eq]
        exact ⟨hycl, hy_nU⟩
      have hyKc : y ∈ Kᶜ := connectedComponentIn_subset _ _ hy₁
      rw [mem_compl_iff] at hyKc
      exact hyKc (hfrsub hyfr)
    obtain ⟨R, hRpos, hKR, hbdy⟩ :=
      exists_square_boundary_subset_of_isCompact_isUnbounded_component K hKcomp x₁ hx₀G hUb
    let f : ℝ × ℝ → ℝ × ℝ := fun y => if y ∈ closure U then y else r y
    have hfcont : Continuous f := by
      have hfront : ∀ y ∈ frontier (closure U), id y = r y := by
        intro y hy
        obtain ⟨t, ht, hty⟩ := hAfr (frontier_closure_subset U hy)
        rw [← hty]
        exact (hrfix t ht).symm
      have h := continuous_if (p := fun y : ℝ × ℝ => y ∈ closure U) hfront
        continuous_id.continuousOn hrcont.continuousOn
      exact h
    refine no_fixed_point_free_selfmap x₁ hRpos f hfcont ?_ ?_ ?_
    · intro y hy
      by_cases hyU : y ∈ closure U
      · have hfy : f y = y := by simp only [f]; rw [if_pos hyU]
        rw [hfy]
        exact hy
      · have hfy : f y = r y := by simp only [f]; rw [if_neg hyU]
        rw [hfy]
        exact le_of_lt (hKR (hAK (hrrange y)))
    · intro y hy
      by_cases hyU : y ∈ closure U
      · have hfy : f y = y := by simp only [f]; rw [if_pos hyU]
        rw [hfy]
        intro hcon
        have hmem : x₁ ∈ (connectedComponentIn (Kᶜ) x₁) ∩ closure U :=
          ⟨mem_connectedComponentIn hx₁G, hcon ▸ hyU⟩
        rw [hU₁disj] at hmem
        exact hmem
      · have hfy : f y = r y := by simp only [f]; rw [if_neg hyU]
        rw [hfy]
        intro hcon
        have hKmem : x₁ ∈ K := hcon ▸ hAK (hrrange y)
        rw [hKdef] at hKmem
        exact hx₁ hKmem
    · intro y hy
      have hyU : y ∈ closure U := subset_closure (show y ∈ U from hbdy hy)
      simp only [f]
      rw [if_pos hyU]

end Work.RPB1a.Caratheodory.Brouwer
