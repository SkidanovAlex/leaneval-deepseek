import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.bumpSideV
import Submission.Work.Smooth.SphereJordan.jsepExterior
import Submission.Work.SphereJordan.windToolkit
import Submission.Work.Smooth.SphereJordan.atMostTwo_components_of_embeddedCircle
import Submission.Work.Smooth.SphereJordan.disc_complement_preconnected

/-!
# A crosscut splits the disc into two components

An embedded arc `α` in the closed disc `closedBall c ρ`, with endpoints on the boundary circle
`sphere c ρ` and interior in the open disc `ball c ρ` (a *crosscut*), separates the open disc into
exactly two connected components.

The proof is the classical one.  The arc `α` together with each of the two boundary arcs cut out by
its endpoints is a simple closed curve: with parameters `s < t < s + 2π` of the endpoints on
`circleCurve`, these boundary arcs are `ArcA = arcPath hcont s t` (from `a` to `b`) and
`ArcB = arcPath hcont t (s + 2π)` (from `b` to `a`).  Writing `P1` for `α` and `P2`, `P3` for
`ArcB`, `revArc ArcA`, the two Jordan curves are `J₁ = loopCurve (P1.trans P2)` and
`J₂ = loopCurve (P1.trans P3)`.

The *argument increment* `incOn` (the toolkit `Submission.Work.SphereJordan.argIncrement`) gives
the winding identity: over a full period the `α`-halves of `J₁` and `J₂` cancel, and the remaining
difference is the increment of the circle over a full period, which is `2πi` because the circle
winds once around each interior point (`windNumberCircleCurve`).  Hence, off the trace,

`windNumber J₂ x = windNumber J₁ x - 1`,

so a point of the open disc on the *unbounded* side of `J₁` lies on the *bounded* side of `J₂` and
conversely: the two bounded sides `V₁`, `V₂` are preconnected, contained in `ball c ρ \ range α`,
and cover it.  A point of `U₁` in the open disc (found near the interior of `ArcA`) and a point of
`V₁` lie in different components, so the complement has exactly two components.
-/

open Set

namespace Work.Smooth.SphereJordan

noncomputable section

/-! ## 0. Coercions of `Path.trans` and `revArc` -/

theorem trans_coe_apply_left {X : Type*} [TopologicalSpace X] {x y z : X} (p : Path x y)
    (q : Path y z) (v : unitInterval) (hv : (v : ℝ) ≤ 1 / 2) :
    (↑(p.trans q) : C(unitInterval, X)) v =
      (↑p : C(unitInterval, X)) ⟨2 * (v : ℝ), ⟨by linarith [v.2.1], by linarith [v.2.2, hv]⟩⟩ := by
  show (p.trans q) v = p ⟨2 * (v : ℝ), ⟨by linarith [v.2.1], by linarith [v.2.2, hv]⟩⟩
  rw [Path.trans_apply, dif_pos hv]

theorem trans_coe_apply_right {X : Type*} [TopologicalSpace X] {x y z : X} (p : Path x y)
    (q : Path y z) (v : unitInterval) (hv : 1 / 2 < (v : ℝ)) :
    (↑(p.trans q) : C(unitInterval, X)) v =
      (↑q : C(unitInterval, X)) ⟨2 * (v : ℝ) - 1, ⟨by linarith [hv], by linarith [v.2.2]⟩⟩ := by
  show (p.trans q) v = q ⟨2 * (v : ℝ) - 1, ⟨by linarith [hv], by linarith [v.2.2]⟩⟩
  rw [Path.trans_apply, dif_neg (not_le.mpr hv)]

theorem trans_coe_apply_mid {X : Type*} [TopologicalSpace X] {x y z : X} (p : Path x y)
    (q : Path y z) (v : unitInterval) (hv : (v : ℝ) = 1 / 2) :
    (↑(p.trans q) : C(unitInterval, X)) v = y := by
  show (p.trans q) v = y
  rw [show (p.trans q) v =
      p ⟨2 * (v : ℝ), ⟨by linarith [v.2.1], by linarith [v.2.2, le_of_eq hv]⟩⟩ from by
    rw [Path.trans_apply, dif_pos (le_of_eq hv)]]
  have h2 : (2 : ℝ) * (v : ℝ) = 1 := by rw [hv]; norm_num
  rw [show (⟨2 * (v : ℝ), ⟨by linarith [v.2.1], by linarith [v.2.2, le_of_eq hv]⟩⟩ : unitInterval)
      = ⟨1, by norm_num⟩ from Subtype.ext h2]
  exact Path.target p

theorem revArc_coe_eq (Q : C(Set.Icc (0 : ℝ) 1, ℂ)) :
    (↑(revArc Q) : Set.Icc (0 : ℝ) 1 → ℂ) = fun v => Q (unitInterval.symm v) := rfl

/-! ## 1. The circle of centre `c` and radius `ρ` -/

/-- The positively oriented circle of centre `c` and radius `ρ`. -/
def circCurve (c : ℂ) (ρ : ℝ) : ℝ → ℂ := fun t => c + (ρ : ℂ) * circleCurve.γ t

theorem circCurve_apply (c : ℂ) (ρ : ℝ) (t : ℝ) :
    circCurve c ρ t = c + (ρ : ℂ) * circleCurve.γ t := rfl

theorem continuous_circCurve (c : ℂ) (ρ : ℝ) : Continuous (circCurve c ρ) :=
  continuous_const.add (continuous_const.mul circleCurve.cont)

theorem periodic_circCurve (c : ℂ) (ρ : ℝ) :
    Function.Periodic (circCurve c ρ) (2 * Real.pi) := by
  intro t
  simp only [circCurve, circleCurve.periodic_apply]

/-- A point of the circle is at distance `ρ` from the centre. -/
theorem norm_circCurve (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ) (t : ℝ) :
    ‖circCurve c ρ t - c‖ = ρ := by
  simp only [circCurve]
  rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ,
    norm_circleCurve_apply, mul_one]

theorem circCurve_injOn {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ) :
    Set.InjOn (circCurve c ρ) (Set.Ico 0 (2 * Real.pi)) := by
  intro s hs t ht h
  have hρne : (ρ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hρ)
  have h' : circleCurve.γ s = circleCurve.γ t := by
    have h2 : (ρ : ℂ) * circleCurve.γ s = (ρ : ℂ) * circleCurve.γ t := by
      have h3 := h
      simp only [circCurve] at h3
      exact add_left_cancel h3
    exact mul_left_cancel₀ hρne h2
  have h4 : Circle.exp s = Circle.exp t := by
    apply Subtype.ext
    rw [Circle.coe_exp, Circle.coe_exp]
    have h5 := h'
    rw [circleCurve_apply, Work.Smooth.Jordan.circlePoint_coe] at h5
    exact h5
  exact Circle.exp_injOn_Ico (by linarith [Real.two_pi_pos]) hs ht h4

theorem range_circCurve {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ) :
    Set.range (circCurve c ρ) = Metric.sphere c ρ := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    rw [Metric.mem_sphere, dist_eq_norm]
    exact norm_circCurve c hρ t
  · intro hz
    rw [Metric.mem_sphere, dist_eq_norm] at hz
    have hnorm : ‖(z - c) / (ρ : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ, hz,
        div_self (ne_of_gt hρ)]
    obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq
      ⟨(z - c) / (ρ : ℂ), by rw [Metric.mem_closedBall, dist_zero_right, hnorm]⟩ hnorm
    refine ⟨θ, ?_⟩
    have h2 : ((circlePoint θ : Disc) : ℂ) = (z - c) / (ρ : ℂ) :=
      congrArg (fun w : Disc => (w : ℂ)) hθ
    have hρne : (ρ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hρ)
    show c + (ρ : ℂ) * circleCurve.γ θ = z
    rw [circleCurve_apply, h2]
    field_simp
    ring

/-- **The increment of the argument of the circle over one period is `2πi`.** -/
theorem incOn_circCurve_period {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ) {x : ℂ} (hx : ‖x - c‖ < ρ)
    (a : ℝ) :
    Work.SphereJordan.incOn (circCurve c ρ) (continuous_circCurve c ρ) x a (a + 2 * Real.pi) =
      2 * (Real.pi : ℂ) * Complex.I := by
  set y : ℂ := (x - c) / (ρ : ℂ) with hy_def
  have hρne : (ρ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hρ)
  have hy : ‖y‖ < 1 := by
    rw [hy_def, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ, div_lt_one hρ]
    exact hx
  have hyne : ∀ t : ℝ, circleCurve.γ t ≠ y := by
    intro t hcon
    have h1 := norm_circleCurve_apply t
    rw [← hcon, h1] at hy
    exact lt_irrefl 1 hy
  have hmain : Work.SphereJordan.incOn (circCurve c ρ) (continuous_circCurve c ρ) x a
      (a + 2 * Real.pi) =
      Work.SphereJordan.pathIncTot (ContinuousMap.const unitInterval (ρ : ℂ) *
        ⟨fun t : unitInterval =>
          circleCurve.γ (a + (t : ℝ) * ((a + 2 * Real.pi) - a)) - y, by fun_prop⟩) := by
    unfold Work.SphereJordan.incOn
    refine Work.SphereJordan.pathIncTot_congr (fun t => ?_)
    simp only [ContinuousMap.coe_mk, ContinuousMap.mul_apply, ContinuousMap.const_apply]
    show circCurve c ρ (a + (t : ℝ) * ((a + 2 * Real.pi) - a)) - x =
      (ρ : ℂ) * (circleCurve.γ (a + (t : ℝ) * ((a + 2 * Real.pi) - a)) - y)
    rw [hy_def, circCurve]
    field_simp
    ring
  have hq : Work.SphereJordan.pathIncTot
      ⟨fun t : unitInterval =>
        circleCurve.γ (a + (t : ℝ) * ((a + 2 * Real.pi) - a)) - y, by fun_prop⟩ =
      Work.SphereJordan.incOn circleCurve.γ circleCurve.cont y a (a + 2 * Real.pi) := rfl
  rw [hmain, Work.SphereJordan.pathIncTot_const_mul (ρ : ℂ) hρne, hq,
    Work.SphereJordan.incOn_period circleCurve.cont circleCurve.periodic y hyne a,
    Work.Smooth.SphereJordan.windNumberCircleCurve y hy]
  norm_num

/-- **The circle winds once around each interior point.** -/
theorem windNumber_circCurve {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ) {x : ℂ} (hx : ‖x - c‖ < ρ) :
    Work.Smooth.SphereJordan.windNumber (circCurve c ρ) (continuous_circCurve c ρ) x = 1 := by
  have hxne : ∀ t : ℝ, circCurve c ρ t ≠ x := by
    intro t hcon
    have h1 := norm_circCurve c hρ t
    rw [hcon] at h1
    linarith [hx, h1]
  have h := Work.SphereJordan.incOn_period (continuous_circCurve c ρ) (periodic_circCurve c ρ)
    x hxne 0
  have hw : (Work.Smooth.SphereJordan.windNumber (circCurve c ρ) (continuous_circCurve c ρ) x : ℂ)
      = 1 := by
    apply mul_right_cancel₀ (Work.Smooth.SphereJordan.two_pi_I_ne_zero)
    rw [one_mul, ← h, incOn_circCurve_period hρ hx 0]
  have hw' : (Work.Smooth.SphereJordan.windNumber (circCurve c ρ) (continuous_circCurve c ρ) x : ℂ)
      = ((1 : ℤ) : ℂ) := by rw [hw]; norm_num
  exact Int.cast_inj.mp hw'

/-! ## 2. A `loopCurve` on the closed interval -/

/-- On the closed interval `[0, 2π]` the `2π`-periodic curve attached to a closed path is the path
itself, reparametrised by `x ↦ x / 2π` (with the endpoint `2π` read as `1 ≡ 0`). -/
theorem loopCurve_apply_Icc_aux (p : C(Set.Icc (0 : ℝ) 1, ℂ))
    (hp : p ⟨0, by norm_num⟩ = p ⟨1, by norm_num⟩) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    (Work.Smooth.SphereJordan.loopCurve p hp).γ x =
      p ⟨x / (2 * Real.pi),
        ⟨div_nonneg hx.1 (by positivity), (div_le_one (by positivity)).mpr hx.2⟩⟩ := by
  rcases lt_or_eq_of_le hx.2 with hlt | heq
  · rw [Work.Smooth.SphereJordan.loopCurve_apply_of_Ico p hp ⟨hx.1, hlt⟩,
      Work.Smooth.SphereJordan.loopFn_of_mem p hx]
  · subst heq
    have h1 : (Work.Smooth.SphereJordan.loopCurve p hp).γ (2 * Real.pi) =
        (Work.Smooth.SphereJordan.loopCurve p hp).γ 0 := by
      simpa using (Work.Smooth.SphereJordan.loopCurve p hp).periodic_apply 0
    rw [h1, Work.Smooth.SphereJordan.loopCurve_apply_of_Ico p hp
        (Set.left_mem_Ico.mpr Real.two_pi_pos), Work.Smooth.SphereJordan.loopFn_zero]
    have h2 : (⟨(2 * Real.pi) / (2 * Real.pi),
        ⟨div_nonneg (by positivity) (by positivity), (div_le_one (by positivity)).mpr le_rfl⟩⟩
        : Set.Icc (0 : ℝ) 1) = ⟨1, by norm_num⟩ := by
      apply Subtype.ext
      field_simp
    rw [h2]
    simpa using hp

/-! ## 2b. The complement of a simple closed plane curve, split in two pieces -/

/-- **The complement of a simple closed plane curve split into the unbounded piece `U` and the
rest `W`.**  The winding number vanishes on `U`, `U` contains the complement of any closed disc
containing the trace, and `U` is *maximal* among the preconnected subsets of the complement that
meet it (it is the connected component of a far-away point).  The second piece need not be
non-empty; a witness for it is supplied by the caller. -/
structure TwoPieces (γ : Work.Smooth.Jordan.PlaneCurve) (hγ : γ.IsSimple) (c : ℂ) (ρ : ℝ) where
  /-- the unbounded piece -/
  U : Set ℂ
  /-- the other piece -/
  W : Set ℂ
  preconn_U : IsPreconnected U
  preconn_W : IsPreconnected W
  nonempty_U : U.Nonempty
  union_eq : U ∪ W = γ.traceᶜ
  disjoint_UW : Disjoint U W
  /-- the winding number vanishes on the unbounded piece -/
  wind_zero_U : ∀ x ∈ U, Work.Smooth.SphereJordan.windNumber γ.γ γ.cont x = 0
  /-- the exterior of the disc is contained in the unbounded piece -/
  compl_closedBall_subset_U : (Metric.closedBall c ρ)ᶜ ⊆ U
  /-- the unbounded piece is a connected component of the complement -/
  maximal_U : ∀ {S : Set ℂ}, IsPreconnected S → S ⊆ γ.traceᶜ → (S ∩ U).Nonempty → S ⊆ U

namespace TwoPieces

variable {γ : Work.Smooth.Jordan.PlaneCurve} {hγ : γ.IsSimple} {c : ℂ} {ρ : ℝ}

theorem notMem_trace (tw : TwoPieces γ hγ c ρ) {x : ℂ} (hx : x ∈ γ.trace) :
    x ∉ tw.U ∧ x ∉ tw.W := by
  constructor
  · intro hxU
    have h : x ∈ tw.U ∪ tw.W := Or.inl hxU
    rw [tw.union_eq] at h
    exact h hx
  · intro hxW
    have h : x ∈ tw.U ∪ tw.W := Or.inr hxW
    rw [tw.union_eq] at h
    exact h hx

theorem subset_or (tw : TwoPieces γ hγ c ρ) {S : Set ℂ} (hS : IsPreconnected S)
    (hsub : S ⊆ γ.traceᶜ) : S ⊆ tw.U ∨ S ⊆ tw.W := by
  by_cases h : (S ∩ tw.U).Nonempty
  · exact Or.inl (tw.maximal_U hS hsub h)
  · refine Or.inr fun x hx => ?_
    have hxT : x ∈ γ.traceᶜ := hsub hx
    have hxmem : x ∈ tw.U ∪ tw.W := by rw [tw.union_eq]; exact hxT
    rcases hxmem with h1 | h1
    · exact absurd ⟨x, hx, h1⟩ h
    · exact h1

theorem notMem_U_of_wind_ne_zero (tw : TwoPieces γ hγ c ρ) {x : ℂ}
    (h : Work.Smooth.SphereJordan.windNumber γ.γ γ.cont x ≠ 0) : x ∉ tw.U :=
  fun hx => h (tw.wind_zero_U x hx)

theorem mem_W_of_wind_ne_zero (tw : TwoPieces γ hγ c ρ) {x : ℂ}
    (hxT : x ∉ γ.trace)
    (h : Work.Smooth.SphereJordan.windNumber γ.γ γ.cont x ≠ 0) : x ∈ tw.W := by
  have h' : x ∈ tw.U ∪ tw.W := by rw [tw.union_eq]; exact hxT
  rcases h' with h' | h'
  · exact absurd (tw.wind_zero_U x h') h
  · exact h'

end TwoPieces

/-- **Existence of the two pieces.**  The unbounded piece is the connected component of a far-away
point, so the winding number vanishes on it; the other piece is preconnected because of the
"at most two components" theorem `Work.Topology.PlaneCurve.compl_jordan_atMostTwo`. -/
theorem exists_twoPieces (γ : Work.Smooth.Jordan.PlaneCurve) (hγ : γ.IsSimple) {c : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hsub : γ.trace ⊆ Metric.closedBall c ρ) : Nonempty (TwoPieces γ hγ c ρ) := by
  classical
  obtain ⟨Rt, hRt⟩ := γ.isCompact_trace.isBounded.exists_norm_le
  have hRt0 : 0 ≤ Rt := le_trans (norm_nonneg (γ.γ 0)) (hRt _ (γ.mem_trace 0))
  set R : ℝ := max Rt 1 with hRdef
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hRle : ∀ z ∈ γ.trace, ‖z‖ ≤ R := fun z hz => le_trans (hRt z hz) (le_max_left _ _)
  set p₀ : ℂ := -(((R + 1 : ℝ)) : ℂ) with hp₀def
  have hp₀norm : ‖p₀‖ = R + 1 := by
    rw [hp₀def, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hp₀off : p₀ ∉ γ.trace := by
    intro hcon
    have h1 := hRle p₀ hcon
    rw [hp₀norm] at h1
    linarith
  set U : Set ℂ := connectedComponentIn γ.traceᶜ p₀ with hUdef
  have hUsub : U ⊆ γ.traceᶜ := connectedComponentIn_subset _ _
  have hUpre : IsPreconnected U := isPreconnected_connectedComponentIn
  have hp₀U : p₀ ∈ U := mem_connectedComponentIn hp₀off
  set W : Set ℂ := γ.traceᶜ \ U with hWdef
  have hunion : U ∪ W = γ.traceᶜ := by
    rw [hWdef]
    exact Set.union_sdiff_cancel hUsub
  have hdisj : Disjoint U W := by
    rw [hWdef]
    exact Set.disjoint_left.mpr fun x hxU hxW => hxW.2 hxU
  have hwind0 : ∀ x ∈ U, Work.Smooth.SphereJordan.windNumber γ.γ γ.cont x = 0 := by
    intro x hx
    have hbdd : ∀ t : ℝ, ‖γ.γ t‖ ≤ R := fun t => hRle _ (γ.mem_trace t)
    have hp₀zero : Work.Smooth.SphereJordan.windNumber γ.γ γ.cont p₀ = 0 :=
      Work.Smooth.SphereJordan.windNumber_eq_zero_of_norm_gt γ.cont γ.periodic hbdd
        (by rw [hp₀norm]; linarith)
    rw [Work.Smooth.SphereJordan.windNumber_eq_of_preconnected γ hUpre hUsub hx hp₀U, hp₀zero]
  have hmaxU : ∀ {S : Set ℂ}, IsPreconnected S → S ⊆ γ.traceᶜ → (S ∩ U).Nonempty →
      S ⊆ U := by
    intro S hS hsubS hmeet
    obtain ⟨x, hxS, hxU⟩ := hmeet
    have hxU' : x ∈ connectedComponentIn γ.traceᶜ p₀ := hxU
    have h1 : connectedComponentIn γ.traceᶜ p₀ = connectedComponentIn γ.traceᶜ x :=
      connectedComponentIn_eq hxU'
    have h2 : S ⊆ connectedComponentIn γ.traceᶜ x := hS.subset_connectedComponentIn hxS hsubS
    intro y hy
    have hy2 : y ∈ connectedComponentIn γ.traceᶜ p₀ := by
      rw [h1]
      exact h2 hy
    exact hy2
  have hfarU : ∀ z : ℂ, R < ‖z‖ → z ∈ U := by
    intro z hz
    have hpre : IsPreconnected {w : ℂ | R < ‖w‖} :=
      Work.Smooth.SphereJordan.isPreconnected_far hRpos
    have hsub' : {w : ℂ | R < ‖w‖} ⊆ γ.traceᶜ := by
      intro w hw hwt
      have h1 := hRle w hwt
      have h2 : R < ‖w‖ := hw
      linarith
    have hmem : p₀ ∈ {w : ℂ | R < ‖w‖} := by
      rw [Set.mem_ofPred_eq, hp₀norm]; linarith
    exact hpre.subset_connectedComponentIn hmem hsub' hz
  have hcompl : (Metric.closedBall c ρ)ᶜ ⊆ U := by
    have hpre : IsPreconnected (Metric.closedBall c ρ)ᶜ :=
      Work.Smooth.SphereJordan.isPreconnected_compl_closedBall c hρ
    have hsub' : (Metric.closedBall c ρ)ᶜ ⊆ γ.traceᶜ := by
      intro z hz hzt
      have h1 : ‖z - c‖ ≤ ρ := by
        have := hsub hzt
        rwa [Metric.mem_closedBall, dist_eq_norm] at this
      have h2 : ρ < ‖z - c‖ := by
        rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, not_le] at hz
        exact hz
      linarith
    have hfar : ((Metric.closedBall c ρ)ᶜ ∩ U).Nonempty := by
      refine ⟨(((R + 1 + 2 * ‖c‖ + 2 * ρ : ℝ)) : ℂ), ?_, ?_⟩
      · rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_eq_norm]
        have hz : ‖(((R + 1 + 2 * ‖c‖ + 2 * ρ : ℝ)) : ℂ)‖ = R + 1 + 2 * ‖c‖ + 2 * ρ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have h3 : ‖(((R + 1 + 2 * ‖c‖ + 2 * ρ : ℝ)) : ℂ)‖ - ‖c‖ ≤
            ‖(((R + 1 + 2 * ‖c‖ + 2 * ρ : ℝ)) : ℂ) - c‖ :=
          le_trans (le_abs_self _) (abs_norm_sub_norm_le _ _)
        linarith [norm_nonneg c]
      · apply hfarU
        have hz : ‖(((R + 1 + 2 * ‖c‖ + 2 * ρ : ℝ)) : ℂ)‖ = R + 1 + 2 * ‖c‖ + 2 * ρ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        rw [hz]
        linarith [norm_nonneg c]
    exact hmaxU hpre hsub' hfar
  have hWpre : IsPreconnected W := by
    rcases Set.eq_empty_or_nonempty W with hemp | ⟨x₀, hx₀⟩
    · rw [hemp]; exact isPreconnected_empty
    · have hx₀' := hx₀
      rw [hWdef] at hx₀'
      have hx₀T : x₀ ∈ γ.traceᶜ := hx₀'.1
      have key : ∀ x ∈ W, ∀ y ∈ W,
          connectedComponentIn γ.traceᶜ x = connectedComponentIn γ.traceᶜ y := by
        intro x hx y hy
        have hx' := hx
        rw [hWdef] at hx'
        have hy' := hy
        rw [hWdef] at hy'
        rcases Work.Topology.PlaneCurve.compl_jordan_atMostTwo γ.cont γ.periodic hγ
          hx'.1 hy'.1 hp₀off with h | h | h
        · exact h
        · exfalso
          have hxU : x ∈ U := by
            have hh : x ∈ connectedComponentIn (Set.range γ.γ)ᶜ p₀ := by
              rw [← h]
              exact mem_connectedComponentIn hx'.1
            exact hh
          exact hx'.2 hxU
        · exfalso
          have hyU : y ∈ U := by
            have hh : y ∈ connectedComponentIn (Set.range γ.γ)ᶜ p₀ := by
              rw [← h]
              exact mem_connectedComponentIn hy'.1
            exact hh
          exact hy'.2 hyU
      have hWeq : W = connectedComponentIn γ.traceᶜ x₀ := by
        refine Set.Subset.antisymm ?_ ?_
        · intro z hz
          have hzT : z ∈ γ.traceᶜ := by
            have h := hz; rw [hWdef] at h; exact h.1
          rw [← key z hz x₀ hx₀]
          exact mem_connectedComponentIn hzT
        · intro z hz
          rw [hWdef]
          refine ⟨connectedComponentIn_subset _ _ hz, ?_⟩
          intro hzU
          have h1 : connectedComponentIn γ.traceᶜ z = connectedComponentIn γ.traceᶜ p₀ :=
            (connectedComponentIn_eq hzU).symm
          have h2 : connectedComponentIn γ.traceᶜ z = connectedComponentIn γ.traceᶜ x₀ :=
            (connectedComponentIn_eq hz).symm
          have h3 : connectedComponentIn γ.traceᶜ p₀ = connectedComponentIn γ.traceᶜ x₀ :=
            h1.symm.trans h2
          have h4 : x₀ ∈ connectedComponentIn γ.traceᶜ p₀ := by
            rw [h3]; exact mem_connectedComponentIn hx₀T
          exact hx₀'.2 h4
      rw [hWeq]
      exact isPreconnected_connectedComponentIn
  exact ⟨U, W, hUpre, hWpre, ⟨p₀, hp₀U⟩, hunion, hdisj, hwind0, hcompl, hmaxU⟩

/-! ## 3. The crosscut theorem -/

theorem crosscutComponents {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    {α : C(Set.Icc (0 : ℝ) 1, ℂ)} (hα : Function.Injective α)
    (hαsub : Set.range α ⊆ Metric.closedBall c ρ)
    (hα₀ : α ⟨0, by norm_num⟩ ∈ Metric.sphere c ρ) (hα₁ : α ⟨1, by norm_num⟩ ∈ Metric.sphere c ρ)
    (hαne : α ⟨0, by norm_num⟩ ≠ α ⟨1, by norm_num⟩)
    (hαint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → α t ∈ Metric.ball c ρ) :
    ∃ P Q : Set ℂ, P.Nonempty ∧ Q.Nonempty ∧ IsOpen P ∧ IsOpen Q ∧
      IsPreconnected P ∧ IsPreconnected Q ∧
      Metric.ball c ρ \ Set.range α = P ∪ Q ∧ Disjoint P Q := by
  classical
  set a : ℂ := α ⟨0, by norm_num⟩ with ha_def
  set b : ℂ := α ⟨1, by norm_num⟩ with hb_def
  have hab : a ≠ b := by rw [ha_def, hb_def]; exact hαne
  have hρ0 : ρ ≠ 0 := ne_of_gt hρ
  have hcont : Continuous (circCurve c ρ) := continuous_circCurve c ρ
  have hper : Function.Periodic (circCurve c ρ) (2 * Real.pi) := periodic_circCurve c ρ
  have hinj : Set.InjOn (circCurve c ρ) (Set.Ico 0 (2 * Real.pi)) := circCurve_injOn hρ
  have hrange : Set.range (circCurve c ρ) = Metric.sphere c ρ := range_circCurve hρ
  have ha_mem : a ∈ Set.range (circCurve c ρ) := by rw [hrange, ha_def]; exact hα₀
  have hb_mem : b ∈ Set.range (circCurve c ρ) := by rw [hrange, hb_def]; exact hα₁
  obtain ⟨s, t, hst, hts, hs, ht⟩ := exists_param_pair hper ha_mem hb_mem hab
  have htle : t ≤ s + 2 * Real.pi := by linarith
  -- the two boundary arcs
  set ArcA : C(Set.Icc (0 : ℝ) 1, ℂ) := arcPath hcont s t with hArcA_def
  set ArcB : C(Set.Icc (0 : ℝ) 1, ℂ) := arcPath hcont t (s + 2 * Real.pi) with hArcB_def
  have hArcA0 : ArcA ⟨0, by norm_num⟩ = a := by rw [hArcA_def, arcPath_zero]; exact hs
  have hArcA1 : ArcA ⟨1, by norm_num⟩ = b := by rw [hArcA_def, arcPath_one]; exact ht
  have hArcB0 : ArcB ⟨0, by norm_num⟩ = b := by rw [hArcB_def, arcPath_zero]; exact ht
  have hArcB1 : ArcB ⟨1, by norm_num⟩ = a := by
    rw [hArcB_def, arcPath_one, hper s]
    exact hs
  have hArcAinj : Function.Injective ArcA := by
    rw [hArcA_def]; exact arcPath_injective hcont hper hinj hst hts
  have hArcBinj : Function.Injective ArcB := by
    rw [hArcB_def]; exact arcPath_injective hcont hper hinj (by linarith) (by linarith)
  have hArcArange : Set.range ArcA = circCurve c ρ '' Set.Icc s t := by
    rw [hArcA_def]; exact range_arcPath hcont hst.le
  have hArcBrange : Set.range ArcB = circCurve c ρ '' Set.Icc t (s + 2 * Real.pi) := by
    rw [hArcB_def]; exact range_arcPath hcont htle
  have hArcAsub : Set.range ArcA ⊆ Metric.sphere c ρ := by
    rw [hArcArange, ← hrange]
    exact Set.image_subset_range _ _
  have hArcBsub : Set.range ArcB ⊆ Metric.sphere c ρ := by
    rw [hArcBrange, ← hrange]
    exact Set.image_subset_range _ _
  have hArcAsub' : Set.range ArcA ⊆ Set.range (circCurve c ρ) := by
    rw [hArcArange]; exact Set.image_subset_range _ _
  have hsplit := arcSplit hcont hper hinj (δ := ArcA) hArcAinj hArcAsub'
    hst hts (by rw [hArcA0]; exact hs) (by rw [hArcA1]; exact ht)
  have hArcInter : Set.range ArcA ∩ Set.range ArcB = {a, b} := by
    have h := hsplit.2.1
    rw [← hArcArange, ← hArcBrange, hArcA0, hArcA1] at h
    exact h
  have hsphere_union : Metric.sphere c ρ = Set.range ArcA ∪ Set.range ArcB := by
    have h := hsplit.1
    rw [← hArcArange, ← hArcBrange, hrange] at h
    exact h
  -- the trace of `α` meets the sphere exactly in the endpoints
  have hαsphere : Set.range α ∩ Metric.sphere c ρ = {a, b} := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro z ⟨⟨u, rfl⟩, hz⟩
      rw [Metric.mem_sphere, dist_eq_norm] at hz
      rcases eq_or_lt_of_le u.2.1 with h0 | h0
      · left
        have hu : u = ⟨0, by norm_num⟩ := Subtype.ext h0.symm
        rw [hu]
      · rcases eq_or_lt_of_le u.2.2 with h1 | h1
        · right
          have hu : u = ⟨1, by norm_num⟩ := Subtype.ext h1
          rw [hu]
          exact Set.mem_singleton_iff.mpr hb_def.symm
        · exfalso
          have hmem := hαint u ⟨h0, h1⟩
          rw [Metric.mem_ball, dist_eq_norm] at hmem
          linarith
    · intro z hz
      refine ⟨?_, ?_⟩
      · rcases hz with h | h
        · rw [h]; exact ⟨⟨0, by norm_num⟩, ha_def.symm⟩
        · rw [Set.mem_singleton_iff] at h
          rw [h]; exact ⟨⟨1, by norm_num⟩, hb_def.symm⟩
      · rcases hz with h | h
        · rw [h, ha_def]; exact hα₀
        · rw [Set.mem_singleton_iff] at h
          rw [h, hb_def]; exact hα₁
  have hαArcA : Set.range α ∩ Set.range ArcA = {a, b} := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro z ⟨h1, h2⟩
      have h3 : z ∈ Set.range α ∩ Metric.sphere c ρ := ⟨h1, hArcAsub h2⟩
      rwa [hαsphere] at h3
    · intro z hz
      refine ⟨?_, ?_⟩
      · rcases hz with h | h
        · rw [h]; exact ⟨⟨0, by norm_num⟩, ha_def.symm⟩
        · rw [Set.mem_singleton_iff] at h
          rw [h]; exact ⟨⟨1, by norm_num⟩, hb_def.symm⟩
      · rcases hz with h | h
        · rw [h]; exact ⟨⟨0, by norm_num⟩, hArcA0⟩
        · rw [Set.mem_singleton_iff] at h
          rw [h]; exact ⟨⟨1, by norm_num⟩, hArcA1⟩
  have hαArcB : Set.range α ∩ Set.range ArcB = {a, b} := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro z ⟨h1, h2⟩
      have h3 : z ∈ Set.range α ∩ Metric.sphere c ρ := ⟨h1, hArcBsub h2⟩
      rwa [hαsphere] at h3
    · intro z hz
      refine ⟨?_, ?_⟩
      · rcases hz with h | h
        · rw [h]; exact ⟨⟨0, by norm_num⟩, ha_def.symm⟩
        · rw [Set.mem_singleton_iff] at h
          rw [h]; exact ⟨⟨1, by norm_num⟩, hb_def.symm⟩
      · rcases hz with h | h
        · rw [h]; exact ⟨⟨1, by norm_num⟩, hArcB1⟩
        · rw [Set.mem_singleton_iff] at h
          rw [h]; exact ⟨⟨0, by norm_num⟩, hArcB0⟩
  -- the two loops and the two Jordan curves
  set P1 : Path a b := ⟨α, ha_def.symm, hb_def.symm⟩ with hP1def
  set P2 : Path b a := ⟨ArcB, hArcB0, hArcB1⟩ with hP2def
  set P3 : Path b a := ⟨revArc ArcA,
    by show (↑(revArc ArcA) : Set.Icc (0:ℝ) 1 → ℂ) (0 : unitInterval) = b
       rw [revArc_coe_eq]
       show ArcA (unitInterval.symm (0 : unitInterval)) = b
       rw [unitInterval.symm_zero]
       exact hArcA1,
    by show (↑(revArc ArcA) : Set.Icc (0:ℝ) 1 → ℂ) (1 : unitInterval) = a
       rw [revArc_coe_eq]
       show ArcA (unitInterval.symm (1 : unitInterval)) = a
       rw [unitInterval.symm_one]
       exact hArcA0⟩ with hP3def
  have hP1inj : Function.Injective P1 := by rw [hP1def]; exact hα
  have hP2inj : Function.Injective P2 := by rw [hP2def]; exact hArcBinj
  have hP3inj : Function.Injective P3 := by
    rw [hP3def]
    show Function.Injective (↑(revArc ArcA) : Set.Icc (0:ℝ) 1 → ℂ)
    exact revArc_injective hArcAinj
  set L1 : C(Set.Icc (0 : ℝ) 1, ℂ) := ↑(P1.trans P2) with hL1def
  set L2 : C(Set.Icc (0 : ℝ) 1, ℂ) := ↑(P1.trans P3) with hL2def
  have hcl1 : L1 (0 : unitInterval) = L1 (1 : unitInterval) := by
    rw [hL1def]
    exact (Path.source (P1.trans P2)).trans (Path.target (P1.trans P2)).symm
  have hcl2 : L2 (0 : unitInterval) = L2 (1 : unitInterval) := by
    rw [hL2def]
    exact (Path.source (P1.trans P3)).trans (Path.target (P1.trans P3)).symm
  set J₁ : Work.Smooth.Jordan.PlaneCurve := Work.Smooth.SphereJordan.loopCurve L1 hcl1
    with hJ₁def
  set J₂ : Work.Smooth.Jordan.PlaneCurve := Work.Smooth.SphereJordan.loopCurve L2 hcl2
    with hJ₂def
  have hJ₁simple : J₁.IsSimple := by
    rw [hJ₁def]
    refine Work.Smooth.SphereJordan.loopCurve_isSimple _ _ ?_
    rw [hL1def]
    have hr1 : Set.range (⇑P1) = Set.range (⇑α) := by rw [hP1def]; rfl
    have hr2 : Set.range (⇑P2) = Set.range (⇑ArcB) := by rw [hP2def]; rfl
    refine path_injOn_trans_loop P1 P2 hP1inj hP2inj ?_
    intro z hz
    rw [hr1, hr2] at hz
    rw [hαArcB] at hz
    exact hz
  have hJ₂simple : J₂.IsSimple := by
    rw [hJ₂def]
    refine Work.Smooth.SphereJordan.loopCurve_isSimple _ _ ?_
    rw [hL2def]
    have hr1 : Set.range (⇑P1) = Set.range (⇑α) := by rw [hP1def]; rfl
    have hr3 : Set.range (⇑P3) = Set.range (revArc ArcA) := by rw [hP3def]; rfl
    refine path_injOn_trans_loop P1 P3 hP1inj hP3inj ?_
    intro z hz
    rw [hr1, hr3] at hz
    have hz2 : z ∈ Set.range ArcA := by
      have h := hz.2
      rw [range_revArc] at h
      exact h
    have hmem : z ∈ Set.range α ∩ Set.range ArcA := ⟨hz.1, hz2⟩
    rw [hαArcA] at hmem
    exact hmem
  have hJ₁trace : J₁.trace = Set.range α ∪ Set.range ArcB := by
    rw [hJ₁def, Work.Smooth.Jordan.PlaneCurve.trace,
      Work.Smooth.SphereJordan.range_loopCurve, hL1def]
    have hpt : Set.range (⇑(P1.trans P2)) = Set.range (⇑P1) ∪ Set.range (⇑P2) :=
      path_range_trans P1 P2
    have hr1 : Set.range (⇑P1) = Set.range (⇑α) := by rw [hP1def]; rfl
    have hr2 : Set.range (⇑P2) = Set.range (⇑ArcB) := by rw [hP2def]; rfl
    rw [hr1, hr2] at hpt
    exact hpt
  have hJ₂trace : J₂.trace = Set.range α ∪ Set.range ArcA := by
    rw [hJ₂def, Work.Smooth.Jordan.PlaneCurve.trace,
      Work.Smooth.SphereJordan.range_loopCurve, hL2def]
    have hpt : Set.range (⇑(P1.trans P3)) = Set.range (⇑P1) ∪ Set.range (⇑P3) :=
      path_range_trans P1 P3
    have hr1 : Set.range (⇑P1) = Set.range (⇑α) := by rw [hP1def]; rfl
    have hr3 : Set.range (⇑P3) = Set.range (revArc ArcA) := by rw [hP3def]; rfl
    rw [hr1, hr3, range_revArc] at hpt
    exact hpt
  have htrace1_ball : J₁.trace ⊆ Metric.closedBall c ρ := by
    rw [hJ₁trace]
    exact Set.union_subset hαsub (hArcBsub.trans Metric.sphere_subset_closedBall)
  have htrace2_ball : J₂.trace ⊆ Metric.closedBall c ρ := by
    rw [hJ₂trace]
    exact Set.union_subset hαsub (hArcAsub.trans Metric.sphere_subset_closedBall)
  obtain ⟨tw₁⟩ := exists_twoPieces J₁ hJ₁simple hρ htrace1_ball
  obtain ⟨tw₂⟩ := exists_twoPieces J₂ hJ₂simple hρ htrace2_ball
  have hU₁ext : (Metric.closedBall c ρ)ᶜ ⊆ tw₁.U := tw₁.compl_closedBall_subset_U
  have hU₂ext : (Metric.closedBall c ρ)ᶜ ⊆ tw₂.U := tw₂.compl_closedBall_subset_U
  -- ## the winding number identity
  have key : ∀ x : ℂ, x ∈ Metric.ball c ρ → x ∉ Set.range α →
      Work.Smooth.SphereJordan.windNumber J₂.γ J₂.cont x =
        Work.Smooth.SphereJordan.windNumber J₁.γ J₁.cont x - 1 := by
    intro x hxball hxα
    have hxd : ‖x - c‖ < ρ := by rwa [Metric.mem_ball, dist_eq_norm] at hxball
    have hxsp : x ∉ Metric.sphere c ρ := by
      intro hcon
      rw [Metric.mem_sphere, dist_eq_norm] at hcon
      linarith
    have hxJ1 : ∀ u : ℝ, J₁.γ u ≠ x := by
      intro u hcon
      have hmem : x ∈ J₁.trace := ⟨u, hcon⟩
      rw [hJ₁trace] at hmem
      rcases hmem with h | h
      · exact hxα h
      · exact hxsp (hArcBsub h)
    have hxJ2 : ∀ u : ℝ, J₂.γ u ≠ x := by
      intro u hcon
      have hmem : x ∈ J₂.trace := ⟨u, hcon⟩
      rw [hJ₂trace] at hmem
      rcases hmem with h | h
      · exact hxα h
      · exact hxsp (hArcAsub h)
    have hxκ : ∀ u : ℝ, circCurve c ρ u ≠ x := by
      intro u hcon
      have h1 := norm_circCurve c hρ u
      rw [hcon] at h1
      linarith
    have hInOn1 : Work.SphereJordan.incOn J₁.γ J₁.cont x 0 (2 * Real.pi) =
        Work.SphereJordan.incOn J₁.γ J₁.cont x 0 Real.pi +
          Work.SphereJordan.incOn J₁.γ J₁.cont x Real.pi (2 * Real.pi) :=
      Work.SphereJordan.incOn_add J₁.cont (le_of_lt Real.pi_pos)
        (by linarith [Real.pi_pos]) (fun u _ => hxJ1 u)
    have hInOn2 : Work.SphereJordan.incOn J₂.γ J₂.cont x 0 (2 * Real.pi) =
        Work.SphereJordan.incOn J₂.γ J₂.cont x 0 Real.pi +
          Work.SphereJordan.incOn J₂.γ J₂.cont x Real.pi (2 * Real.pi) :=
      Work.SphereJordan.incOn_add J₂.cont (le_of_lt Real.pi_pos)
        (by linarith [Real.pi_pos]) (fun u _ => hxJ2 u)
    have hAgree : Work.SphereJordan.incOn J₁.γ J₁.cont x 0 Real.pi =
        Work.SphereJordan.incOn J₂.γ J₂.cont x 0 Real.pi := by
      refine Work.SphereJordan.incOn_congr J₁.cont J₂.cont (le_of_lt Real.pi_pos) ?_
      intro u hu
      have hu2 : u ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := ⟨hu.1, by linarith [hu.2, Real.pi_pos]⟩
      have hdiv : (0 : ℝ) ≤ u / (2 * Real.pi) := div_nonneg hu.1 (by positivity)
      have hle1 : u / (2 * Real.pi) ≤ 1 := (div_le_one (by positivity)).mpr hu2.2
      have hdiv1 : u / (2 * Real.pi) ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
        linarith [hu.2, Real.pi_pos]
      have e1 : J₁.γ u = L1 ⟨u / (2 * Real.pi), hdiv, hle1⟩ := by
        rw [hJ₁def, loopCurve_apply_Icc_aux L1 hcl1 hu2, hL1def]
      have e2 : J₂.γ u = L2 ⟨u / (2 * Real.pi), hdiv, hle1⟩ := by
        rw [hJ₂def, loopCurve_apply_Icc_aux L2 hcl2 hu2, hL2def]
      have e3 := trans_coe_apply_left P1 P2 ⟨u / (2 * Real.pi), hdiv, hle1⟩ hdiv1
      have e4 := trans_coe_apply_left P1 P3 ⟨u / (2 * Real.pi), hdiv, hle1⟩ hdiv1
      rw [e1, e2, hL1def, hL2def, e3, e4]
    have hArc1 : Work.SphereJordan.incOn J₁.γ J₁.cont x Real.pi (2 * Real.pi) =
        Work.SphereJordan.incOn (circCurve c ρ) (continuous_circCurve c ρ) x t (s + 2 * Real.pi) := by
      refine Work.SphereJordan.incOn_eq_of_forall' J₁.cont (continuous_circCurve c ρ) (fun u => ?_)
      have hmem : Real.pi + (u : ℝ) * (2 * Real.pi - Real.pi) ∈ Set.Icc (0 : ℝ) (2 * Real.pi) :=
        ⟨by nlinarith [u.2.1, Real.pi_pos], by nlinarith [u.2.2, Real.pi_pos]⟩
      have hdiv : (0 : ℝ) ≤
          (Real.pi + (u : ℝ) * (2 * Real.pi - Real.pi)) / (2 * Real.pi) :=
        div_nonneg hmem.1 (by positivity)
      have hle1 : (Real.pi + (u : ℝ) * (2 * Real.pi - Real.pi)) / (2 * Real.pi) ≤ 1 :=
        (div_le_one (by positivity)).mpr hmem.2
      have hvdef : (Real.pi + (u : ℝ) * (2 * Real.pi - Real.pi)) / (2 * Real.pi)
          = (1 + (u : ℝ)) / 2 := by
        field_simp; ring
      have e1 : J₁.γ (Real.pi + (u : ℝ) * (2 * Real.pi - Real.pi)) =
          L1 ⟨(Real.pi + (u : ℝ) * (2 * Real.pi - Real.pi)) / (2 * Real.pi), hdiv, hle1⟩ := by
        rw [hJ₁def, loopCurve_apply_Icc_aux L1 hcl1 hmem, hL1def]
      rw [e1, hL1def]
      by_cases hc : (Real.pi + (u : ℝ) * (2 * Real.pi - Real.pi)) / (2 * Real.pi) ≤ 1 / 2
      · have hu0 : (u : ℝ) = 0 := by
          have h2 : (u : ℝ) ≤ 0 := by
            rw [hvdef] at hc
            linarith
          linarith [u.2.1]
        have hmid : (Real.pi + (u : ℝ) * (2 * Real.pi - Real.pi)) / (2 * Real.pi) = 1 / 2 := by
          rw [hvdef, hu0]; norm_num
        rw [trans_coe_apply_mid P1 P2
          ⟨(Real.pi + (u : ℝ) * (2 * Real.pi - Real.pi)) / (2 * Real.pi), hdiv, hle1⟩ hmid]
        have hueq : u = (⟨0, by norm_num⟩ : unitInterval) := Subtype.ext hu0
        have h0c : ((⟨0, by norm_num⟩ : unitInterval) : ℝ) = 0 := rfl
        rw [hueq, h0c, zero_mul, add_zero]
        exact ht.symm
      · have hgt : 1 / 2 < (Real.pi + (u : ℝ) * (2 * Real.pi - Real.pi)) / (2 * Real.pi) :=
          lt_of_not_ge hc
        have e3 := trans_coe_apply_right P1 P2
          ⟨(Real.pi + (u : ℝ) * (2 * Real.pi - Real.pi)) / (2 * Real.pi), hdiv, hle1⟩ hgt
        rw [e3]
        set W : unitInterval :=
          ⟨2 * (↑(⟨(Real.pi + (u : ℝ) * (2 * Real.pi - Real.pi)) / (2 * Real.pi), hdiv, hle1⟩ : unitInterval)) - 1,
            ⟨by linarith [hgt], by linarith [hle1]⟩⟩ with hW_def
        show (↑P2 : C(Set.Icc (0 : ℝ) 1, ℂ)) W =
          circCurve c ρ (t + (u : ℝ) * ((s + 2 * Real.pi) - t))
        have hP2coe : (↑P2 : C(Set.Icc (0 : ℝ) 1, ℂ)) = ArcB := rfl
        rw [hP2coe, hArcB_def, arcPath_apply]
        have harg : W = (⟨(u : ℝ), u.2.1, u.2.2⟩ : unitInterval) := by
          apply Subtype.ext
          show 2 * ((Real.pi + (u : ℝ) * (2 * Real.pi - Real.pi)) / (2 * Real.pi)) - 1 = (u : ℝ)
          rw [hvdef]
          ring
        rw [harg]
    have hArc2 : Work.SphereJordan.incOn J₂.γ J₂.cont x Real.pi (2 * Real.pi) =
        -Work.SphereJordan.incOn (circCurve c ρ) (continuous_circCurve c ρ) x s t := by
      have hrev : Work.SphereJordan.incOn J₂.γ J₂.cont x Real.pi (2 * Real.pi) =
          -Work.SphereJordan.incOn J₂.γ J₂.cont x (2 * Real.pi) Real.pi := by
        have h := Work.SphereJordan.incIn_rev_neg J₂.cont (z := x) (a := Real.pi)
          (b := 2 * Real.pi)
        rw [h]; ring
      rw [hrev, neg_inj]
      refine Work.SphereJordan.incOn_eq_of_forall' J₂.cont (continuous_circCurve c ρ) (fun u => ?_)
      have hmem : 2 * Real.pi + (u : ℝ) * (Real.pi - 2 * Real.pi) ∈ Set.Icc (0 : ℝ) (2 * Real.pi) :=
        ⟨by nlinarith [u.2.2, Real.pi_pos], by nlinarith [u.2.1, Real.pi_pos]⟩
      have hdiv : (0 : ℝ) ≤
          (2 * Real.pi + (u : ℝ) * (Real.pi - 2 * Real.pi)) / (2 * Real.pi) :=
        div_nonneg hmem.1 (by positivity)
      have hle1 : (2 * Real.pi + (u : ℝ) * (Real.pi - 2 * Real.pi)) / (2 * Real.pi) ≤ 1 :=
        (div_le_one (by positivity)).mpr hmem.2
      have hvdef : (2 * Real.pi + (u : ℝ) * (Real.pi - 2 * Real.pi)) / (2 * Real.pi)
          = 1 - (u : ℝ) / 2 := by
        field_simp; ring
      have e1 : J₂.γ (2 * Real.pi + (u : ℝ) * (Real.pi - 2 * Real.pi)) =
          L2 ⟨(2 * Real.pi + (u : ℝ) * (Real.pi - 2 * Real.pi)) / (2 * Real.pi), hdiv, hle1⟩ := by
        rw [hJ₂def, loopCurve_apply_Icc_aux L2 hcl2 hmem, hL2def]
      rw [e1, hL2def]
      by_cases hc : (2 * Real.pi + (u : ℝ) * (Real.pi - 2 * Real.pi)) / (2 * Real.pi) ≤ 1 / 2
      · have hu1 : (u : ℝ) = 1 := by
          have h2 : 1 ≤ (u : ℝ) := by
            rw [hvdef] at hc
            linarith
          linarith [u.2.2]
        have hmid : (2 * Real.pi + (u : ℝ) * (Real.pi - 2 * Real.pi)) / (2 * Real.pi) = 1 / 2 := by
          rw [hvdef, hu1]; norm_num
        rw [trans_coe_apply_mid P1 P3
          ⟨(2 * Real.pi + (u : ℝ) * (Real.pi - 2 * Real.pi)) / (2 * Real.pi), hdiv, hle1⟩ hmid]
        have hueq : u = (⟨1, by norm_num⟩ : unitInterval) := Subtype.ext hu1
        have h1c : ((⟨1, by norm_num⟩ : unitInterval) : ℝ) = 1 := rfl
        rw [hueq, h1c, one_mul]
        rw [show s + (t - s) = t from by ring]
        exact ht.symm
      · have hgt : 1 / 2 < (2 * Real.pi + (u : ℝ) * (Real.pi - 2 * Real.pi)) / (2 * Real.pi) :=
          lt_of_not_ge hc
        have e3 := trans_coe_apply_right P1 P3
          ⟨(2 * Real.pi + (u : ℝ) * (Real.pi - 2 * Real.pi)) / (2 * Real.pi), hdiv, hle1⟩ hgt
        rw [e3]
        set W : unitInterval :=
          ⟨2 * (↑(⟨(2 * Real.pi + (u : ℝ) * (Real.pi - 2 * Real.pi)) / (2 * Real.pi), hdiv, hle1⟩ : unitInterval)) - 1,
            ⟨by linarith [hgt], by linarith [hle1]⟩⟩ with hW_def
        show (↑P3 : C(Set.Icc (0 : ℝ) 1, ℂ)) W =
          circCurve c ρ (s + (u : ℝ) * (t - s))
        have hP3coe : (↑P3 : C(Set.Icc (0 : ℝ) 1, ℂ)) = revArc ArcA := rfl
        have harg : unitInterval.symm W = u := by
          apply Subtype.ext
          rw [unitInterval.coe_symm_eq]
          show (1 : ℝ) - (2 * ((2 * Real.pi + (u : ℝ) * (Real.pi - 2 * Real.pi)) / (2 * Real.pi)) - 1)
            = (u : ℝ)
          rw [hvdef]
          ring
        rw [hP3coe, revArc_coe_eq]
        change ArcA (unitInterval.symm W) = circCurve c ρ (s + (u : ℝ) * (t - s))
        rw [harg, hArcA_def, arcPath_apply]
    have hSplit : Work.SphereJordan.incOn (circCurve c ρ) (continuous_circCurve c ρ) x s
        (s + 2 * Real.pi) =
        Work.SphereJordan.incOn (circCurve c ρ) (continuous_circCurve c ρ) x s t +
          Work.SphereJordan.incOn (circCurve c ρ) (continuous_circCurve c ρ) x t
            (s + 2 * Real.pi) :=
      Work.SphereJordan.incOn_add (continuous_circCurve c ρ) hst.le htle
        (fun u _ => hxκ u)
    have hPeriod : Work.SphereJordan.incOn (circCurve c ρ) (continuous_circCurve c ρ) x s
        (s + 2 * Real.pi) = Work.SphereJordan.kap := by
      rw [Work.SphereJordan.kap]
      exact incOn_circCurve_period hρ hxd s
    have hdiff : ((Work.Smooth.SphereJordan.windNumber J₁.γ J₁.cont x : ℤ) : ℂ) *
          Work.SphereJordan.kap -
        ((Work.Smooth.SphereJordan.windNumber J₂.γ J₂.cont x : ℤ) : ℂ) *
          Work.SphereJordan.kap = Work.SphereJordan.kap := by
      have hw1 := Work.SphereJordan.windNumber_incOn_period J₁ hxJ1
      have hw2 := Work.SphereJordan.windNumber_incOn_period J₂ hxJ2
      rw [hw1, hw2, hInOn1, hInOn2, hAgree, hArc1, hArc2, ← hPeriod, hSplit]
      ring
    have hdiff2 : (((Work.Smooth.SphereJordan.windNumber J₁.γ J₁.cont x -
        Work.Smooth.SphereJordan.windNumber J₂.γ J₂.cont x : ℤ)) : ℂ) = ((1 : ℤ) : ℂ) := by
      apply mul_right_cancel₀ Work.SphereJordan.kap_ne_zero
      rw [Int.cast_sub, sub_mul, Int.cast_one, one_mul]
      exact hdiff
    have hw : Work.Smooth.SphereJordan.windNumber J₁.γ J₁.cont x -
        Work.Smooth.SphereJordan.windNumber J₂.γ J₂.cont x = 1 := Int.cast_inj.mp hdiff2
    omega
  -- ## the boundaries of the two sides
  have hU1V2 : ∀ x : ℂ, x ∈ Metric.ball c ρ → x ∉ Set.range α → x ∈ tw₁.U → x ∈ tw₂.W := by
    intro x hxball hxα hxU
    have hxsp : x ∉ Metric.sphere c ρ := by
      intro hcon
      rw [Metric.mem_sphere, dist_eq_norm] at hcon
      rw [Metric.mem_ball, dist_eq_norm] at hxball
      linarith
    have hxT1 : x ∉ J₁.trace := by
      rw [hJ₁trace]
      rintro (h | h)
      · exact hxα h
      · exact hxsp (hArcBsub h)
    have hxT2 : x ∉ J₂.trace := by
      rw [hJ₂trace]
      rintro (h | h)
      · exact hxα h
      · exact hxsp (hArcAsub h)
    have h0 : Work.Smooth.SphereJordan.windNumber J₁.γ J₁.cont x = 0 :=
      tw₁.wind_zero_U x hxU
    have h2 : Work.Smooth.SphereJordan.windNumber J₂.γ J₂.cont x = -1 := by
      have hk := key x hxball hxα
      rw [h0] at hk
      omega
    have hne : Work.Smooth.SphereJordan.windNumber J₂.γ J₂.cont x ≠ 0 := by
      rw [h2]; norm_num
    have hmem : x ∈ tw₂.U ∪ tw₂.W := by
      rw [tw₂.union_eq, Set.mem_compl_iff]
      exact hxT2
    rcases hmem with h | h
    · exact absurd (tw₂.wind_zero_U x h) hne
    · exact h
  have hcover : Metric.ball c ρ \ Set.range α ⊆ tw₁.W ∪ tw₂.W := by
    rintro x ⟨hxball, hxα⟩
    have hxsp : x ∉ Metric.sphere c ρ := by
      intro hcon
      rw [Metric.mem_sphere, dist_eq_norm] at hcon
      rw [Metric.mem_ball, dist_eq_norm] at hxball
      linarith
    have hxT1 : x ∉ J₁.trace := by
      rw [hJ₁trace]
      rintro (h | h)
      · exact hxα h
      · exact hxsp (hArcBsub h)
    have hmem : x ∈ tw₁.U ∪ tw₁.W := by
      rw [tw₁.union_eq, Set.mem_compl_iff]
      exact hxT1
    rcases hmem with h | h
    · exact Or.inr (hU1V2 x hxball hxα h)
    · exact Or.inl h
  have hW1sub : tw₁.W ⊆ Metric.ball c ρ \ Set.range α := by
    intro x hxV
    have hxT1 : x ∉ J₁.trace := by
      intro hcon
      have : x ∈ tw₁.U ∪ tw₁.W := Or.inr hxV
      rw [tw₁.union_eq] at this
      exact this hcon
    refine ⟨?_, ?_⟩
    · have hxcb : ‖x - c‖ ≤ ρ := by
        by_contra hcon
        have hcon' : x ∈ (Metric.closedBall c ρ)ᶜ := by
          rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_eq_norm]; exact hcon
        exact Set.disjoint_left.mp tw₁.disjoint_UW (hU₁ext hcon') hxV
      have hxsp : ‖x - c‖ ≠ ρ := by
        intro hcon
        obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp J₁.isOpen_compl_trace x hxT1
        rcases tw₁.subset_or Metric.isPreconnected_ball hball with h | h
        · exact Set.disjoint_left.mp tw₁.disjoint_UW (h (Metric.mem_ball_self hε)) hxV
        · exfalso
          set q : ℂ := x + (((ε / (2 * ρ) : ℝ)) : ℂ) * (x - c) with hq_def
          have hqx : q - x = (((ε / (2 * ρ) : ℝ)) : ℂ) * (x - c) := by rw [hq_def]; ring
          have hqball : q ∈ Metric.ball x ε := by
            have hsc : ‖((( ε / (2 * ρ) : ℝ)) : ℂ)‖ = ε / (2 * ρ) := by
              rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
            rw [Metric.mem_ball, dist_eq_norm, hqx, norm_mul, hsc, hcon]
            have h2 : ε / (2 * ρ) * ρ = ε / 2 := by field_simp
            rw [h2]; linarith
          have hqext : q ∈ (Metric.closedBall c ρ)ᶜ := by
            rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_eq_norm]
            have hqc : q - c = (1 + (((ε / (2 * ρ) : ℝ)) : ℂ)) * (x - c) := by rw [hq_def]; ring
            have hsc : ‖(1 + (((ε / (2 * ρ) : ℝ)) : ℂ))‖ = 1 + ε / (2 * ρ) := by
              have h : (1 + (((ε / (2 * ρ) : ℝ)) : ℂ)) = ((1 + ε / (2 * ρ) : ℝ) : ℂ) := by
                push_cast; ring
              rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
            rw [hqc, norm_mul, hsc, hcon]
            have h2 : (1 + ε / (2 * ρ)) * ρ = ρ + ε / 2 := by field_simp
            rw [h2]; linarith
          exact Set.disjoint_left.mp tw₁.disjoint_UW (hU₁ext hqext) (h hqball)
      rw [Metric.mem_ball, dist_eq_norm]
      exact lt_of_le_of_ne hxcb hxsp
    · intro hcon
      have : x ∈ J₁.trace := by rw [hJ₁trace]; exact Or.inl hcon
      exact hxT1 this
  have hW2sub : tw₂.W ⊆ Metric.ball c ρ \ Set.range α := by
    intro x hxV
    have hxT2 : x ∉ J₂.trace := by
      intro hcon
      have : x ∈ tw₂.U ∪ tw₂.W := Or.inr hxV
      rw [tw₂.union_eq] at this
      exact this hcon
    refine ⟨?_, ?_⟩
    · have hxcb : ‖x - c‖ ≤ ρ := by
        by_contra hcon
        have hcon' : x ∈ (Metric.closedBall c ρ)ᶜ := by
          rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_eq_norm]; exact hcon
        exact Set.disjoint_left.mp tw₂.disjoint_UW (hU₂ext hcon') hxV
      have hxsp : ‖x - c‖ ≠ ρ := by
        intro hcon
        obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp J₂.isOpen_compl_trace x hxT2
        rcases tw₂.subset_or Metric.isPreconnected_ball hball with h | h
        · exact Set.disjoint_left.mp tw₂.disjoint_UW (h (Metric.mem_ball_self hε)) hxV
        · exfalso
          set q : ℂ := x + (((ε / (2 * ρ) : ℝ)) : ℂ) * (x - c) with hq_def
          have hqx : q - x = (((ε / (2 * ρ) : ℝ)) : ℂ) * (x - c) := by rw [hq_def]; ring
          have hqball : q ∈ Metric.ball x ε := by
            have hsc : ‖((( ε / (2 * ρ) : ℝ)) : ℂ)‖ = ε / (2 * ρ) := by
              rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
            rw [Metric.mem_ball, dist_eq_norm, hqx, norm_mul, hsc, hcon]
            have h2 : ε / (2 * ρ) * ρ = ε / 2 := by field_simp
            rw [h2]; linarith
          have hqext : q ∈ (Metric.closedBall c ρ)ᶜ := by
            rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_eq_norm]
            have hqc : q - c = (1 + (((ε / (2 * ρ) : ℝ)) : ℂ)) * (x - c) := by rw [hq_def]; ring
            have hsc : ‖(1 + (((ε / (2 * ρ) : ℝ)) : ℂ))‖ = 1 + ε / (2 * ρ) := by
              have h : (1 + (((ε / (2 * ρ) : ℝ)) : ℂ)) = ((1 + ε / (2 * ρ) : ℝ) : ℂ) := by
                push_cast; ring
              rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
            rw [hqc, norm_mul, hsc, hcon]
            have h2 : (1 + ε / (2 * ρ)) * ρ = ρ + ε / 2 := by field_simp
            rw [h2]; linarith
          exact Set.disjoint_left.mp tw₂.disjoint_UW (hU₂ext hqext) (h hqball)
      rw [Metric.mem_ball, dist_eq_norm]
      exact lt_of_le_of_ne hxcb hxsp
    · intro hcon
      have : x ∈ J₂.trace := by rw [hJ₂trace]; exact Or.inl hcon
      exact hxT2 this
  -- ## a point of `U₁` inside the disc
  have hx0 : ∃ x₀ : ℂ, x₀ ∈ Metric.ball c ρ ∧ x₀ ∈ tw₁.U ∧ x₀ ∈ tw₂.W := by
    set z : ℂ := ArcA ⟨1 / 2, by norm_num⟩ with hz_def
    have hz_sphere : z ∈ Metric.sphere c ρ := hArcAsub ⟨⟨1 / 2, by norm_num⟩, hz_def.symm⟩
    have hzsp : ‖z - c‖ = ρ := by
      rw [Metric.mem_sphere, dist_eq_norm] at hz_sphere
      exact hz_sphere
    have hz_ne_a : z ≠ a := by
      intro hcon
      have h1 : ArcA ⟨1 / 2, by norm_num⟩ = ArcA ⟨0, by norm_num⟩ := by
        rw [hz_def] at hcon; rw [hcon, hArcA0]
      have h2 : ((1 / 2 : ℝ)) = 0 := congrArg Subtype.val (hArcAinj h1)
      norm_num at h2
    have hz_ne_b : z ≠ b := by
      intro hcon
      have h1 : ArcA ⟨1 / 2, by norm_num⟩ = ArcA ⟨1, by norm_num⟩ := by
        rw [hz_def] at hcon; rw [hcon, hArcA1]
      have h2 : ((1 / 2 : ℝ)) = 1 := congrArg Subtype.val (hArcAinj h1)
      norm_num at h2
    have hz_notα : z ∉ Set.range α := by
      intro hcon
      have hmem : z ∈ Set.range α ∩ Metric.sphere c ρ := ⟨hcon, hz_sphere⟩
      rw [hαsphere] at hmem
      rcases hmem with h | h
      · exact hz_ne_a h
      · exact hz_ne_b h
    have hz_notT : z ∉ J₁.trace := by
      rw [hJ₁trace]
      rintro (h | h)
      · exact hz_notα h
      · have hmem : z ∈ Set.range ArcA ∩ Set.range ArcB :=
          ⟨⟨⟨1 / 2, by norm_num⟩, hz_def.symm⟩, h⟩
        rw [hArcInter] at hmem
        rcases hmem with h' | h'
        · exact hz_ne_a h'
        · exact hz_ne_b h'
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp J₁.isOpen_compl_trace z hz_notT
    have hBU : Metric.ball z ε ⊆ tw₁.U := by
      rcases tw₁.subset_or Metric.isPreconnected_ball hball with h | h
      · exact h
      · exfalso
        set q : ℂ := z + (((ε / (2 * ρ) : ℝ)) : ℂ) * (z - c) with hq_def
        have hqx : q - z = (((ε / (2 * ρ) : ℝ)) : ℂ) * (z - c) := by rw [hq_def]; ring
        have hqball : q ∈ Metric.ball z ε := by
          have hsc : ‖((( ε / (2 * ρ) : ℝ)) : ℂ)‖ = ε / (2 * ρ) := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
          rw [Metric.mem_ball, dist_eq_norm, hqx, norm_mul, hsc, hzsp]
          have h2 : ε / (2 * ρ) * ρ = ε / 2 := by field_simp
          rw [h2]; linarith
        have hqext : q ∈ (Metric.closedBall c ρ)ᶜ := by
          rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_eq_norm]
          have hqc : q - c = (1 + (((ε / (2 * ρ) : ℝ)) : ℂ)) * (z - c) := by rw [hq_def]; ring
          have hsc : ‖(1 + (((ε / (2 * ρ) : ℝ)) : ℂ))‖ = 1 + ε / (2 * ρ) := by
            have h : (1 + (((ε / (2 * ρ) : ℝ)) : ℂ)) = ((1 + ε / (2 * ρ) : ℝ) : ℂ) := by
              push_cast; ring
            rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
          rw [hqc, norm_mul, hsc, hzsp]
          have h2 : (1 + ε / (2 * ρ)) * ρ = ρ + ε / 2 := by field_simp
          rw [h2]; linarith
        exact Set.disjoint_left.mp tw₁.disjoint_UW (hU₁ext hqext) (h hqball)
    set δ : ℝ := min (ε / 2) (ρ / 2) with hδ_def
    have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
    have hδlt : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    set x₀ : ℂ := z - (((δ / ρ : ℝ)) : ℂ) * (z - c) with hx₀_def
    have hx₀mem : x₀ ∈ Metric.ball z ε := by
      have h1 : x₀ - z = -((((δ / ρ : ℝ)) : ℂ)) * (z - c) := by rw [hx₀_def]; ring
      have hsc : ‖-((((δ / ρ : ℝ)) : ℂ))‖ = δ / ρ := by
        rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hδpos hρ)]
      rw [Metric.mem_ball, dist_eq_norm, h1, norm_mul, hsc, hzsp]
      have h2 : δ / ρ * ρ = δ := by field_simp
      rw [h2]; exact hδlt
    have hδρ : δ < ρ := by
      rw [hδ_def]
      exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hx₀ball : x₀ ∈ Metric.ball c ρ := by
      have h1 : x₀ - c = (1 - (((δ / ρ : ℝ)) : ℂ)) * (z - c) := by rw [hx₀_def]; ring
      have hsc : ‖(1 - (((δ / ρ : ℝ)) : ℂ))‖ = 1 - δ / ρ := by
        have h : (1 - (((δ / ρ : ℝ)) : ℂ)) = ((1 - δ / ρ : ℝ) : ℂ) := by push_cast; ring
        have h1' : (0 : ℝ) < 1 - δ / ρ := by
          have := (div_lt_one hρ).mpr hδρ
          linarith
        rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1']
      rw [Metric.mem_ball, dist_eq_norm, h1, norm_mul, hsc, hzsp]
      have h2 : (1 - δ / ρ) * ρ = ρ - δ := by field_simp
      rw [h2]; linarith
    have hx₀notα : x₀ ∉ Set.range α := by
      intro hcon
      have hmem : x₀ ∈ J₁.trace := by rw [hJ₁trace]; exact Or.inl hcon
      exact (hball hx₀mem) hmem
    exact ⟨x₀, hx₀ball, hBU hx₀mem, hU1V2 x₀ hx₀ball hx₀notα (hBU hx₀mem)⟩
  have hx1 : ∃ y₀ : ℂ, y₀ ∈ Metric.ball c ρ ∧ y₀ ∈ tw₁.W ∧ y₀ ∈ tw₂.U := by
    set z : ℂ := ArcB ⟨1 / 2, by norm_num⟩ with hz_def
    have hz_sphere : z ∈ Metric.sphere c ρ := hArcBsub ⟨⟨1 / 2, by norm_num⟩, hz_def.symm⟩
    have hzsp : ‖z - c‖ = ρ := by
      rw [Metric.mem_sphere, dist_eq_norm] at hz_sphere
      exact hz_sphere
    have hz_ne_a : z ≠ a := by
      intro hcon
      have h1 : ArcB ⟨1 / 2, by norm_num⟩ = ArcB ⟨1, by norm_num⟩ := by
        rw [hz_def] at hcon; rw [hcon, hArcB1]
      have h2 : ((1 / 2 : ℝ)) = 1 := congrArg Subtype.val (hArcBinj h1)
      norm_num at h2
    have hz_ne_b : z ≠ b := by
      intro hcon
      have h1 : ArcB ⟨1 / 2, by norm_num⟩ = ArcB ⟨0, by norm_num⟩ := by
        rw [hz_def] at hcon; rw [hcon, hArcB0]
      have h2 : ((1 / 2 : ℝ)) = 0 := congrArg Subtype.val (hArcBinj h1)
      norm_num at h2
    have hz_notα : z ∉ Set.range α := by
      intro hcon
      have hmem : z ∈ Set.range α ∩ Metric.sphere c ρ := ⟨hcon, hz_sphere⟩
      rw [hαsphere] at hmem
      rcases hmem with h | h
      · exact hz_ne_a h
      · exact hz_ne_b h
    have hz_notT : z ∉ J₂.trace := by
      rw [hJ₂trace]
      rintro (h | h)
      · exact hz_notα h
      · have hmem : z ∈ Set.range ArcA ∩ Set.range ArcB :=
          ⟨h, ⟨⟨1 / 2, by norm_num⟩, hz_def.symm⟩⟩
        rw [hArcInter] at hmem
        rcases hmem with h' | h'
        · exact hz_ne_a h'
        · exact hz_ne_b h'
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp J₂.isOpen_compl_trace z hz_notT
    have hBU : Metric.ball z ε ⊆ tw₂.U := by
      rcases tw₂.subset_or Metric.isPreconnected_ball hball with h | h
      · exact h
      · exfalso
        set q : ℂ := z + (((ε / (2 * ρ) : ℝ)) : ℂ) * (z - c) with hq_def
        have hqx : q - z = (((ε / (2 * ρ) : ℝ)) : ℂ) * (z - c) := by rw [hq_def]; ring
        have hqball : q ∈ Metric.ball z ε := by
          have hsc : ‖((( ε / (2 * ρ) : ℝ)) : ℂ)‖ = ε / (2 * ρ) := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
          rw [Metric.mem_ball, dist_eq_norm, hqx, norm_mul, hsc, hzsp]
          have h2 : ε / (2 * ρ) * ρ = ε / 2 := by field_simp
          rw [h2]; linarith
        have hqext : q ∈ (Metric.closedBall c ρ)ᶜ := by
          rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_eq_norm]
          have hqc : q - c = (1 + (((ε / (2 * ρ) : ℝ)) : ℂ)) * (z - c) := by rw [hq_def]; ring
          have hsc : ‖(1 + (((ε / (2 * ρ) : ℝ)) : ℂ))‖ = 1 + ε / (2 * ρ) := by
            have h : (1 + (((ε / (2 * ρ) : ℝ)) : ℂ)) = ((1 + ε / (2 * ρ) : ℝ) : ℂ) := by
              push_cast; ring
            rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
          rw [hqc, norm_mul, hsc, hzsp]
          have h2 : (1 + ε / (2 * ρ)) * ρ = ρ + ε / 2 := by field_simp
          rw [h2]; linarith
        exact Set.disjoint_left.mp tw₂.disjoint_UW (hU₂ext hqext) (h hqball)
    set δ : ℝ := min (ε / 2) (ρ / 2) with hδ_def
    have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
    have hδlt : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    set y₀ : ℂ := z - (((δ / ρ : ℝ)) : ℂ) * (z - c) with hy₀_def
    have hy₀mem : y₀ ∈ Metric.ball z ε := by
      have h1 : y₀ - z = -((((δ / ρ : ℝ)) : ℂ)) * (z - c) := by rw [hy₀_def]; ring
      have hsc : ‖-((((δ / ρ : ℝ)) : ℂ))‖ = δ / ρ := by
        rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hδpos hρ)]
      rw [Metric.mem_ball, dist_eq_norm, h1, norm_mul, hsc, hzsp]
      have h2 : δ / ρ * ρ = δ := by field_simp
      rw [h2]; exact hδlt
    have hδρ : δ < ρ := by
      rw [hδ_def]
      exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hy₀ball : y₀ ∈ Metric.ball c ρ := by
      have h1 : y₀ - c = (1 - (((δ / ρ : ℝ)) : ℂ)) * (z - c) := by rw [hy₀_def]; ring
      have hsc : ‖(1 - (((δ / ρ : ℝ)) : ℂ))‖ = 1 - δ / ρ := by
        have h : (1 - (((δ / ρ : ℝ)) : ℂ)) = ((1 - δ / ρ : ℝ) : ℂ) := by push_cast; ring
        have h1' : (0 : ℝ) < 1 - δ / ρ := by
          have := (div_lt_one hρ).mpr hδρ
          linarith
        rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1']
      rw [Metric.mem_ball, dist_eq_norm, h1, norm_mul, hsc, hzsp]
      have h2 : (1 - δ / ρ) * ρ = ρ - δ := by field_simp
      rw [h2]; linarith
    have hy₀notα : y₀ ∉ Set.range α := by
      intro hcon
      have hmem : y₀ ∈ J₂.trace := by rw [hJ₂trace]; exact Or.inl hcon
      exact (hball hy₀mem) hmem
    have hy₀W : y₀ ∈ tw₁.W := by
      have hyT1 : y₀ ∉ J₁.trace := by
        rw [hJ₁trace]
        rintro (h | h)
        · exact hy₀notα h
        · have h1 := hArcBsub h
          rw [Metric.mem_sphere, dist_eq_norm] at h1
          rw [Metric.mem_ball, dist_eq_norm] at hy₀ball
          linarith
      have hwind1 : Work.Smooth.SphereJordan.windNumber J₁.γ J₁.cont y₀ = 1 := by
        have hk := key y₀ hy₀ball hy₀notα
        have h0 : Work.Smooth.SphereJordan.windNumber J₂.γ J₂.cont y₀ = 0 :=
          tw₂.wind_zero_U y₀ (hBU hy₀mem)
        omega
      exact tw₁.mem_W_of_wind_ne_zero hyT1 (by rw [hwind1]; norm_num)
    exact ⟨y₀, hy₀ball, hy₀W, hBU hy₀mem⟩

  obtain ⟨x₀, hx₀ball, hx₀U, hx₀W₂⟩ := hx0
  obtain ⟨y₀, hy₀ball, hy₀W, hy₀U₂⟩ := hx1
  have hx₀notα : x₀ ∉ Set.range α := (hW2sub hx₀W₂).2
  have hx₀M : x₀ ∈ Metric.ball c ρ \ Set.range α := ⟨hx₀ball, hx₀notα⟩
  have hy₀M : y₀ ∈ Metric.ball c ρ \ Set.range α := hW1sub hy₀W
  have hMopen : IsOpen (Metric.ball c ρ \ Set.range α) :=
    Metric.isOpen_ball.sdiff (isCompact_range α.continuous).isClosed
  have hAtMost : ∀ z ∈ Metric.ball c ρ \ Set.range α,
      connectedComponentIn (Metric.ball c ρ \ Set.range α) z =
          connectedComponentIn (Metric.ball c ρ \ Set.range α) x₀ ∨
        connectedComponentIn (Metric.ball c ρ \ Set.range α) z =
          connectedComponentIn (Metric.ball c ρ \ Set.range α) y₀ := by
    intro z hz
    rcases hcover hz with hz1 | hz2
    · have hsub : tw₁.W ⊆ connectedComponentIn (Metric.ball c ρ \ Set.range α) y₀ :=
        tw₁.preconn_W.subset_connectedComponentIn hy₀W hW1sub
      exact Or.inr (connectedComponentIn_eq (hsub hz1)).symm
    · have hsub : tw₂.W ⊆ connectedComponentIn (Metric.ball c ρ \ Set.range α) x₀ :=
        tw₂.preconn_W.subset_connectedComponentIn hx₀W₂ hW2sub
      exact Or.inl (connectedComponentIn_eq (hsub hz2)).symm
  have hne : connectedComponentIn (Metric.ball c ρ \ Set.range α) x₀ ≠
      connectedComponentIn (Metric.ball c ρ \ Set.range α) y₀ := by
    intro hcon
    set M := Metric.ball c ρ \ Set.range α with hM_def
    have hCsub : connectedComponentIn M x₀ ⊆ M := connectedComponentIn_subset M x₀
    have hCpre : IsPreconnected (connectedComponentIn M x₀) := isPreconnected_connectedComponentIn
    have hy₀C : y₀ ∈ connectedComponentIn M x₀ := by
      rw [hcon]; exact mem_connectedComponentIn hy₀M
    have hCtrace : connectedComponentIn M x₀ ⊆ J₁.traceᶜ := by
      intro w hw hwt
      have hwM := hCsub hw
      rw [hJ₁trace] at hwt
      rcases hwt with h | h
      · exact hwM.2 h
      · have hwball := hwM.1
        rw [Metric.mem_ball, dist_eq_norm] at hwball
        have h1 := hArcBsub h
        rw [Metric.mem_sphere, dist_eq_norm] at h1
        linarith
    have hUV1 : IsPreconnected (connectedComponentIn M x₀ ∪ tw₁.W) :=
      IsPreconnected.union y₀ hy₀C hy₀W hCpre tw₁.preconn_W
    have hUV1sub : connectedComponentIn M x₀ ∪ tw₁.W ⊆ J₁.traceᶜ := by
      intro w hw
      rcases hw with hw | hw
      · exact hCtrace hw
      · intro hwt
        have h2 : w ∈ tw₁.U ∪ tw₁.W := Or.inr hw
        rw [tw₁.union_eq] at h2
        exact h2 hwt
    have hCV : connectedComponentIn M x₀ ⊆ tw₁.W := by
      rcases tw₁.subset_or hUV1 hUV1sub with h | h
      · exfalso
        exact Set.disjoint_left.mp tw₁.disjoint_UW (h (Set.mem_union_right _ hy₀W)) hy₀W
      · exact Set.subset_union_left.trans h
    have hUV2 : IsPreconnected (connectedComponentIn M x₀ ∪ tw₁.U) :=
      IsPreconnected.union x₀ (mem_connectedComponentIn hx₀M) hx₀U hCpre tw₁.preconn_U
    have hUV2sub : connectedComponentIn M x₀ ∪ tw₁.U ⊆ J₁.traceᶜ := by
      intro w hw
      rcases hw with hw | hw
      · exact hCtrace hw
      · intro hwt
        have h2 : w ∈ tw₁.U ∪ tw₁.W := Or.inl hw
        rw [tw₁.union_eq] at h2
        exact h2 hwt
    have hCU : connectedComponentIn M x₀ ⊆ tw₁.U := by
      rcases tw₁.subset_or hUV2 hUV2sub with h | h
      · exact Set.subset_union_left.trans h
      · exfalso
        exact Set.disjoint_left.mp tw₁.disjoint_UW hx₀U (h (Set.mem_union_right _ hx₀U))
    exact Set.disjoint_left.mp tw₁.disjoint_UW hx₀U (hCV (mem_connectedComponentIn hx₀M))
  refine ⟨connectedComponentIn (Metric.ball c ρ \ Set.range α) x₀,
    connectedComponentIn (Metric.ball c ρ \ Set.range α) y₀, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨x₀, mem_connectedComponentIn hx₀M⟩
  · exact ⟨y₀, mem_connectedComponentIn hy₀M⟩
  · exact isOpen_connectedComponentIn_of_isOpen hMopen x₀
  · exact isOpen_connectedComponentIn_of_isOpen hMopen y₀
  · exact isPreconnected_connectedComponentIn
  · exact isPreconnected_connectedComponentIn
  · refine Set.Subset.antisymm ?_ ?_
    · intro z hz
      rcases hAtMost z hz with h | h
      · left; rw [← h]; exact mem_connectedComponentIn hz
      · right; rw [← h]; exact mem_connectedComponentIn hz
    · intro z hz
      rcases hz with h | h
      · exact connectedComponentIn_subset _ _ h
      · exact connectedComponentIn_subset _ _ h
  · rw [Set.disjoint_left]
    intro z hzx hzy
    exact hne ((connectedComponentIn_eq hzx).trans (connectedComponentIn_eq hzy).symm)

end

end Work.Smooth.SphereJordan
