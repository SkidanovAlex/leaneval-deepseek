import Mathlib
import Submission.Work.SphereJordan.SpanHyp
import Submission.Work.SphereJordan.tgtUpPC_isSimple
import Submission.Work.SphereJordan.incrOn
import Submission.Work.Smooth.SphereJordan.BoundedSide
import Submission.Work.Smooth.SphereJordan.loopIndex_eq_of_homotopy

/-!
# The paths of the two-cuts pairing identities

This module sets up the objects needed for `Work.SphereJordan.windNumber_pairing_identities`:
the four loops of the four-arc curves, their four branch pieces each, the outer circle loop and the
`γ`-period loop, together with the elementary non-vanishing facts and the basic calculus of the
argument increment.
-/

open Set
open Classical

namespace Work.SphereJordan

noncomputable section

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-- The number `2πI`. -/
def kappa : ℂ := 2 * (Real.pi : ℂ) * Complex.I

theorem kappa_ne_zero : kappa ≠ 0 := by
  rw [kappa]
  exact Work.Smooth.SphereJordan.two_pi_I_ne_zero

/-! ## The increment of a path, made total -/

/-- The increment of a path, made total by setting it to `0` on a path that vanishes. -/
def incr' (c : C(unitInterval, ℂ)) : ℂ :=
  if h : ∀ t, c t ≠ 0 then incr h else 0

theorem incr'_eq {c : C(unitInterval, ℂ)} (h : ∀ t, c t ≠ 0) : incr' c = incr h := by
  rw [incr', dif_pos h]

theorem incr'_zero {c : C(unitInterval, ℂ)} (h : ¬ ∀ t, c t ≠ 0) : incr' c = 0 := by
  rw [incr', dif_neg h]

theorem incr'_congr {c d : C(unitInterval, ℂ)} (h : ∀ t, c t = d t) : incr' c = incr' d := by
  by_cases hc : ∀ t, c t ≠ 0
  · have hd : ∀ t, d t ≠ 0 := fun t => by rw [← h t]; exact hc t
    rw [incr'_eq hc, incr'_eq hd]
    exact incr_congr hc hd h
  · have hd : ¬ ∀ t, d t ≠ 0 := by
      intro hd
      exact hc fun t => by rw [h t]; exact hd t
    rw [incr'_zero hc, incr'_zero hd]

theorem revI_val (t : unitInterval) : ((revI t : unitInterval) : ℝ) = 1 - (t : ℝ) := by
  change (1 : ℝ) + (0 - 1) * (t : ℝ) = 1 - (t : ℝ)
  ring

theorem revI_involutive (t : unitInterval) : revI (revI t) = t := by
  apply Subtype.ext
  rw [revI_val, revI_val]
  simp

theorem incr'_rev (c : C(unitInterval, ℂ)) : incr' (c.comp revI) = -incr' c := by
  by_cases hc : ∀ t, c t ≠ 0
  · have hcomp : ∀ t, c.comp revI t ≠ 0 := fun t => hc _
    rw [incr'_eq hc, incr'_eq hcomp]
    exact incr_rev hc
  · have hcomp : ¬ ∀ t, c.comp revI t ≠ 0 := by
      intro hcomp
      refine hc fun t => ?_
      have h := hcomp (revI t)
      rwa [ContinuousMap.comp_apply, revI_involutive] at h
    rw [incr'_zero hc, incr'_zero hcomp]
    simp

/-- **Increment of a reparametrised path**, in terms of any chosen lift of the path. -/
theorem incr'_comp {c : C(unitInterval, ℂ)} (hc : ∀ t, c t ≠ 0)
    (σ : C(unitInterval, unitInterval)) :
    incr' (c.comp σ) = liftOf hc (σ 1) - liftOf hc (σ 0) := by
  have hcomp : ∀ t, c.comp σ t ≠ 0 := fun t => hc (σ t)
  rw [incr'_eq hcomp]
  exact incr_comp hc σ

/-- **Additivity of the increment over a concatenation described by two reparametrisations.** -/
theorem incr'_comp_add {c : C(unitInterval, ℂ)} (hc : ∀ t, c t ≠ 0)
    {σ τ : C(unitInterval, unitInterval)} (h : τ 1 = σ 0) :
    incr' (c.comp σ) + incr' (c.comp τ) = liftOf hc (σ 1) - liftOf hc (τ 0) := by
  rw [incr'_comp hc σ, incr'_comp hc τ, h]
  ring

/-! ## The two `1/2` reparametrisations -/

/-- The first half of the unit interval. -/
def half1 : C(unitInterval, unitInterval) :=
  linMap 0 (1/2) (linMap_mem 0 (1/2) (by norm_num) (by norm_num) (by norm_num))

/-- The second half of the unit interval. -/
def half2 : C(unitInterval, unitInterval) :=
  linMap (1/2) 1 (linMap_mem (1/2) 1 (by norm_num) (by norm_num) (by norm_num))

theorem half1_zero : half1 0 = 0 := by
  apply Subtype.ext
  change (0 : ℝ) + (1/2 - 0) * (((0 : unitInterval)) : ℝ) = 0
  norm_num

theorem half1_one : half1 1 = (⟨1/2, by norm_num⟩ : unitInterval) := by
  apply Subtype.ext
  change (0 : ℝ) + (1/2 - 0) * (((1 : unitInterval)) : ℝ) = 1/2
  norm_num

theorem half2_zero : half2 0 = (⟨1/2, by norm_num⟩ : unitInterval) := by
  apply Subtype.ext
  change (1/2 : ℝ) + (1 - 1/2) * (((0 : unitInterval)) : ℝ) = 1/2
  norm_num

theorem half2_one : half2 1 = 1 := by
  apply Subtype.ext
  change (1/2 : ℝ) + (1 - 1/2) * (((1 : unitInterval)) : ℝ) = 1
  norm_num

theorem half1_val (t : unitInterval) : ((half1 t : unitInterval) : ℝ) = (t : ℝ) / 2 := by
  change (0 : ℝ) + (1/2 - 0) * (t : ℝ) = (t : ℝ) / 2
  ring

theorem half2_val (t : unitInterval) : ((half2 t : unitInterval) : ℝ) = (t : ℝ) / 2 + 1/2 := by
  change (1/2 : ℝ) + (1 - 1/2) * (t : ℝ) = (t : ℝ) / 2 + 1/2
  ring

/-! ## The loops of the four four-arc curves -/

section Defs

variable {hh : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
  {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}

/-- The loop of the upper target curve about `x`, with pairing flag `b`. -/
def upLoop (H : SpanHyp hh hs hball S) (x : ℂ) (b : Bool) : C(unitInterval, ℂ) :=
  Work.Smooth.SphereJordan.curveLoop (fun t => (H.upPC b).γ t - x)
    ((H.upPC b).cont.sub continuous_const)

/-- The loop of the lower target curve about `x`, with pairing flag `b`. -/
def dnLoop (H : SpanHyp hh hs hball S) (x : ℂ) (b : Bool) : C(unitInterval, ℂ) :=
  Work.Smooth.SphereJordan.curveLoop (fun t => (H.dnPC b).γ t - x)
    ((H.dnPC b).cont.sub continuous_const)

/-- `windNumber` of the upper target curve is the index of its loop. -/
theorem windNumber_upLoop (H : SpanHyp hh hs hball S) (x : ℂ) (b : Bool) :
    Work.Smooth.SphereJordan.windNumber (H.upPC b).γ (H.upPC b).cont x
      = Work.Smooth.SphereJordan.loopIndex (upLoop H x b) := rfl

/-- `windNumber` of the lower target curve is the index of its loop. -/
theorem windNumber_dnLoop (H : SpanHyp hh hs hball S) (x : ℂ) (b : Bool) :
    Work.Smooth.SphereJordan.windNumber (H.dnPC b).γ (H.dnPC b).cont x
      = Work.Smooth.SphereJordan.loopIndex (dnLoop H x b) := rfl

/-- The first piece of the upper loop: the upper outer semicircle. -/
def upP1 (H : SpanHyp hh hs hball S) (x : ℂ) : C(unitInterval, ℂ) :=
  ⟨fun t => Work.Smooth.SphereJordan.srcOuterUp S (t : ℝ) - x,
    ((continuous_srcOuterUp S).comp continuous_subtype_val).sub continuous_const⟩

/-- The second piece of the upper loop: the second crosscut, inward. -/
def upP2 (H : SpanHyp hh hs hball S) (x : ℂ) : C(unitInterval, ℂ) :=
  ⟨fun t => Work.Smooth.SphereJordan.tgtCut₂ S H.t₂ H.s₂ (t : ℝ) - x,
    ((continuous_tgtCut₂ S H.t₂ H.s₂).comp continuous_subtype_val).sub continuous_const⟩

/-- The third piece of the upper loop: the `γ`-arc selected by `b`. -/
def upP3 (H : SpanHyp hh hs hball S) (x : ℂ) (b : Bool) : C(unitInterval, ℂ) :=
  ⟨fun t => (if b then γ.γ (H.θ₂ + (t : ℝ) * (H.θ₁ - H.θ₂))
      else γ.γ (H.θ₂ + (t : ℝ) * (H.θ₁ - H.θ₂ - 2 * Real.pi))) - x, by
    cases b
    · exact (γ.cont.comp (continuous_const.add (continuous_subtype_val.mul continuous_const))).sub
        continuous_const
    · exact (γ.cont.comp (continuous_const.add (continuous_subtype_val.mul continuous_const))).sub
        continuous_const⟩

/-- The fourth piece of the upper loop: the first crosscut, outward. -/
def upP4 (H : SpanHyp hh hs hball S) (x : ℂ) : C(unitInterval, ℂ) :=
  ⟨fun t => Work.Smooth.SphereJordan.tgtCut₁ S H.t₁ H.s₁ (1 - (t : ℝ)) - x,
    ((continuous_tgtCut₁ S H.t₁ H.s₁).comp (continuous_const.sub continuous_subtype_val)).sub
      continuous_const⟩

/-- The first piece of the lower loop: the lower outer semicircle. -/
def dnP1 (H : SpanHyp hh hs hball S) (x : ℂ) : C(unitInterval, ℂ) :=
  ⟨fun t => Work.Smooth.SphereJordan.srcOuterDn S (t : ℝ) - x,
    ((continuous_srcOuterDn S).comp continuous_subtype_val).sub continuous_const⟩

/-- The second piece of the lower loop: the first crosscut, inward. -/
def dnP2 (H : SpanHyp hh hs hball S) (x : ℂ) : C(unitInterval, ℂ) :=
  ⟨fun t => Work.Smooth.SphereJordan.tgtCut₁ S H.t₁ H.s₁ (t : ℝ) - x,
    ((continuous_tgtCut₁ S H.t₁ H.s₁).comp continuous_subtype_val).sub continuous_const⟩

/-- The third piece of the lower loop: the `γ`-arc selected by `b`. -/
def dnP3 (H : SpanHyp hh hs hball S) (x : ℂ) (b : Bool) : C(unitInterval, ℂ) :=
  ⟨fun t => (if b then γ.γ (H.θ₁ - 2 * Real.pi + (t : ℝ) * (H.θ₂ - H.θ₁ + 2 * Real.pi))
      else γ.γ (H.θ₁ + (t : ℝ) * (H.θ₂ - H.θ₁))) - x, by
    cases b
    · exact (γ.cont.comp (continuous_const.add (continuous_subtype_val.mul continuous_const))).sub
        continuous_const
    · exact (γ.cont.comp (continuous_const.add (continuous_subtype_val.mul continuous_const))).sub
        continuous_const⟩

/-- The fourth piece of the lower loop: the second crosscut, outward. -/
def dnP4 (H : SpanHyp hh hs hball S) (x : ℂ) : C(unitInterval, ℂ) :=
  ⟨fun t => Work.Smooth.SphereJordan.tgtCut₂ S H.t₂ H.s₂ (1 - (t : ℝ)) - x,
    ((continuous_tgtCut₂ S H.t₂ H.s₂).comp (continuous_const.sub continuous_subtype_val)).sub
      continuous_const⟩

/-! ## The circle loop and the `γ`-period loop -/

/-- The full unit circle, traversed once from `cutDir S`, about `x`. -/
def outerLoop (H : SpanHyp hh hs hball S) (x : ℂ) : C(unitInterval, ℂ) :=
  ⟨fun t => Work.Smooth.SphereJordan.cutDir S *
      Complex.exp ((((2 * Real.pi * (t : ℝ) : ℝ)) : ℂ) * Complex.I) - x, by fun_prop⟩

/-- The standard exponential loop `t ↦ e^{2πit}`. -/
def expLoop : C(unitInterval, ℂ) :=
  ⟨fun t => Complex.exp ((((2 * Real.pi * (t : ℝ) : ℝ)) : ℂ) * Complex.I), by fun_prop⟩

/-- The "small" loop `t ↦ cutDir S - x e^{-2πit}`. -/
def starLoop (H : SpanHyp hh hs hball S) (x : ℂ) : C(unitInterval, ℂ) :=
  ⟨fun t => Work.Smooth.SphereJordan.cutDir S -
      x * Complex.exp ((((-(2 * Real.pi * (t : ℝ)) : ℝ)) : ℂ) * Complex.I), by fun_prop⟩

/-- The `γ`-loop over the period starting at `θ₁`. -/
def gammaLoop (H : SpanHyp hh hs hball S) (x : ℂ) : C(unitInterval, ℂ) :=
  ⟨fun t => γ.γ (H.θ₁ + 2 * Real.pi * (t : ℝ)) - x,
    (γ.cont.comp (continuous_const.add (continuous_const.mul continuous_subtype_val))).sub
      continuous_const⟩

end Defs


/-! ## Non-vanishing of the pieces: elementary facts about the points of the configuration -/

section Nonvan

/-- A point of the bounded side is off the trace. -/
theorem notMem_trace_of_mem_V (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {x : ℂ}
    (hx : x ∈ S.V) : x ∉ γ.trace := by
  intro htr
  have hsub : S.V ⊆ γ.traceᶜ := by
    intro y hy
    have h : y ∈ S.U ∪ S.V := Or.inr hy
    rwa [S.union_eq] at h
  exact hsub hx htr

/-- A point of the bounded side of a curve inside the open disc has norm `< 1`. -/
theorem norm_lt_one_of_mem_V (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {x : ℂ} (hx : x ∈ S.V) : ‖x‖ < 1 := by
  have hle : ‖x‖ ≤ 1 :=
    Work.Smooth.SphereJordan.planeSeparation_V_subset_closedBall S.toPlaneSeparation hball x hx
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp S.isOpen_V x hx
    set y : ℂ := (((1 + ε / 2 : ℝ)) : ℂ) * x with hy
    have hxy : y ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      have h1 : y - x = (((ε / 2 : ℝ)) : ℂ) * x := by rw [hy]; push_cast; ring
      rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ ε / 2), heq, mul_one]
      linarith
    have hyV : y ∈ S.V := hb hxy
    have hnorm : ‖y‖ = 1 + ε / 2 := by
      rw [hy, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + ε / 2), heq, mul_one]
    have h2 := Work.Smooth.SphereJordan.planeSeparation_V_subset_closedBall
      S.toPlaneSeparation hball y hyV
    rw [hnorm] at h2
    linarith

/-- A point of the trace is not `x`. -/
theorem gamma_ne (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {x : ℂ} (hx : x ∈ S.V)
    (r : ℝ) : γ.γ r ≠ x :=
  fun h => notMem_trace_of_mem_V S hx ⟨r, h⟩

/-- The lower outer semicircle lies on the unit circle. -/
theorem norm_srcOuterDn (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (r : ℝ) :
    ‖Work.Smooth.SphereJordan.srcOuterDn S r‖ = 1 := by
  rw [Work.Smooth.SphereJordan.srcOuterDn, norm_mul, norm_neg,
    Work.Smooth.SphereJordan.norm_cutDir, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem srcOuterUp_ne (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {x : ℂ} (hx : ‖x‖ < 1)
    (r : ℝ) : Work.Smooth.SphereJordan.srcOuterUp S r ≠ x := by
  intro h
  have h1 := norm_srcOuterUp S r
  rw [h] at h1
  rw [h1] at hx
  exact lt_irrefl 1 hx

theorem srcOuterDn_ne (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {x : ℂ} (hx : ‖x‖ < 1)
    (r : ℝ) : Work.Smooth.SphereJordan.srcOuterDn S r ≠ x := by
  intro h
  have h1 := norm_srcOuterDn S r
  rw [h] at h1
  rw [h1] at hx
  exact lt_irrefl 1 hx

/-- The parameter of the second branch lies in `[0,1]`. -/
theorem mem_Icc_div_pi_half {σ : ℝ} (h1 : Real.pi / 2 ≤ σ) (h2 : σ ≤ Real.pi) :
    (σ - Real.pi / 2) / (Real.pi / 2) ∈ Set.Icc (0 : ℝ) 1 := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  constructor
  · exact div_nonneg (by linarith) hpi.le
  · rw [div_le_one hpi]; linarith

/-- The parameter of the fourth branch lies in `[0,1]`. -/
theorem mem_Icc_one_sub_div_pi_half {σ : ℝ} (h1 : 3 * Real.pi / 2 ≤ σ)
    (h2 : σ ≤ 2 * Real.pi) :
    1 - (σ - 3 * Real.pi / 2) / (Real.pi / 2) ∈ Set.Icc (0 : ℝ) 1 := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  have hd : 0 ≤ (σ - 3 * Real.pi / 2) / (Real.pi / 2) := div_nonneg (by linarith) hpi.le
  constructor
  · rw [sub_nonneg, div_le_one hpi]; linarith
  · linarith

/-- No point of the closed first crosscut is `x`. -/
theorem tgtCut₁_ne {hh : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp hh hs hball S) {x : ℂ} (hx : x ∈ S.V) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    Work.Smooth.SphereJordan.tgtCut₁ S H.t₁ H.s₁ r ≠ x := by
  set σ : ℝ := H.s₁ + r * (H.t₁ - H.s₁) with hσdef
  have hval : Work.Smooth.SphereJordan.tgtCut₁ S H.t₁ H.s₁ r =
      (Work.Smooth.SphereJordan.base S : ℂ) + (σ : ℂ) * Work.Smooth.SphereJordan.cutDir S := rfl
  intro hcon
  have hxσ : (Work.Smooth.SphereJordan.base S : ℂ) + (σ : ℂ) * Work.Smooth.SphereJordan.cutDir S
      = x := by rw [← hval]; exact hcon
  rcases lt_or_eq_of_le hr.2 with hrl | hr1
  · rcases eq_or_lt_of_le hr.1 with hr0 | hrpos
    · -- `r = 0`: the value is `cutDir S`
      have hσ : σ = H.s₁ := by rw [hσdef, ← hr0]; ring
      have hxu : x = Work.Smooth.SphereJordan.cutDir S := by
        rw [← hxσ, hσ, H.hout₁]
      have hnorm : ‖x‖ = 1 := by rw [hxu, Work.Smooth.SphereJordan.norm_cutDir]
      have := norm_lt_one_of_mem_V S hball hx
      rw [hnorm] at this
      exact lt_irrefl 1 this
    · -- `0 < r < 1`: the value lies in the open crosscut
      have hpos1 : 0 < 1 - r := by linarith
      have hpos2 : 0 < H.s₁ - H.t₁ := by linarith [H.ht₁s₁]
      have hlt1 : H.t₁ < σ := by
        rw [hσdef]; nlinarith [mul_pos hpos1 hpos2]
      have hlt2 : σ < H.s₁ := by
        rw [hσdef]; nlinarith [H.ht₁s₁, hrpos]
      have hmem := H.hseg₁ σ hlt1 hlt2
      rw [hxσ] at hmem
      exact hmem.2 hx
  · -- `r = 1`: the value is `γ θ₁`
    have hσ : σ = H.t₁ := by rw [hσdef, hr1]; ring
    have hγ : γ.γ H.θ₁ = x := by rw [H.hθ₁, ← hσ]; exact hxσ
    exact gamma_ne S hx H.θ₁ hγ

/-- No point of the closed second crosscut is `x`. -/
theorem tgtCut₂_ne {hh : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp hh hs hball S) {x : ℂ} (hx : x ∈ S.V) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    Work.Smooth.SphereJordan.tgtCut₂ S H.t₂ H.s₂ r ≠ x := by
  set σ : ℝ := H.s₂ + r * (H.t₂ - H.s₂) with hσdef
  have hval : Work.Smooth.SphereJordan.tgtCut₂ S H.t₂ H.s₂ r =
      (Work.Smooth.SphereJordan.base S : ℂ) - (σ : ℂ) * Work.Smooth.SphereJordan.cutDir S := rfl
  intro hcon
  have hxσ : (Work.Smooth.SphereJordan.base S : ℂ) - (σ : ℂ) * Work.Smooth.SphereJordan.cutDir S
      = x := by rw [← hval]; exact hcon
  rcases lt_or_eq_of_le hr.2 with hrl | hr1
  · rcases eq_or_lt_of_le hr.1 with hr0 | hrpos
    · -- `r = 0`: the value is `-cutDir S`
      have hσ : σ = H.s₂ := by rw [hσdef, ← hr0]; ring
      have hxu : x = -Work.Smooth.SphereJordan.cutDir S := by
        rw [← hxσ, hσ, H.hout₂]
      have hnorm : ‖x‖ = 1 := by
        rw [hxu, norm_neg, Work.Smooth.SphereJordan.norm_cutDir]
      have := norm_lt_one_of_mem_V S hball hx
      rw [hnorm] at this
      exact lt_irrefl 1 this
    · have hlt1 : H.t₂ < σ := by rw [hσdef]; nlinarith [H.ht₂s₂]
      have hlt2 : σ < H.s₂ := by rw [hσdef]; nlinarith [H.ht₂s₂]
      have hmem := H.hseg₂ σ hlt1 hlt2
      rw [hxσ] at hmem
      exact hmem.2 hx
  · have hσ : σ = H.t₂ := by rw [hσdef, hr1]; ring
    have hγ : γ.γ H.θ₂ = x := by rw [H.hθ₂, ← hσ]; exact hxσ
    exact gamma_ne S hx H.θ₂ hγ

/-! ## Non-vanishing of the pieces -/

theorem upP1_ne {hh : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp hh hs hball S) {x : ℂ} (hx : x ∈ S.V) : ∀ t, upP1 H x t ≠ 0 := by
  intro t h
  exact srcOuterUp_ne S (norm_lt_one_of_mem_V S hball hx) (t : ℝ) (sub_eq_zero.mp h)

theorem upP2_ne {hh : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp hh hs hball S) {x : ℂ} (hx : x ∈ S.V) : ∀ t, upP2 H x t ≠ 0 := by
  intro t h
  exact tgtCut₂_ne H hx ⟨t.2.1, t.2.2⟩ (sub_eq_zero.mp h)

theorem upP3_ne {hh : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp hh hs hball S) {x : ℂ} (hx : x ∈ S.V) (b : Bool) :
    ∀ t, upP3 H x b t ≠ 0 := by
  intro t
  cases b
  · show γ.γ (H.θ₂ + (t : ℝ) * (H.θ₁ - H.θ₂ - 2 * Real.pi)) - x ≠ 0
    intro h
    exact gamma_ne S hx _ (sub_eq_zero.mp h)
  · show γ.γ (H.θ₂ + (t : ℝ) * (H.θ₁ - H.θ₂)) - x ≠ 0
    intro h
    exact gamma_ne S hx _ (sub_eq_zero.mp h)

theorem upP4_ne {hh : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp hh hs hball S) {x : ℂ} (hx : x ∈ S.V) : ∀ t, upP4 H x t ≠ 0 := by
  intro t h
  exact tgtCut₁_ne H hx ⟨by linarith [t.2.2], by linarith [t.2.1]⟩ (sub_eq_zero.mp h)

theorem dnP1_ne {hh : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp hh hs hball S) {x : ℂ} (hx : x ∈ S.V) : ∀ t, dnP1 H x t ≠ 0 := by
  intro t h
  exact srcOuterDn_ne S (norm_lt_one_of_mem_V S hball hx) (t : ℝ) (sub_eq_zero.mp h)

theorem dnP2_ne {hh : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp hh hs hball S) {x : ℂ} (hx : x ∈ S.V) : ∀ t, dnP2 H x t ≠ 0 := by
  intro t h
  exact tgtCut₁_ne H hx ⟨t.2.1, t.2.2⟩ (sub_eq_zero.mp h)

theorem dnP3_ne {hh : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp hh hs hball S) {x : ℂ} (hx : x ∈ S.V) (b : Bool) :
    ∀ t, dnP3 H x b t ≠ 0 := by
  intro t
  cases b
  · show γ.γ (H.θ₁ + (t : ℝ) * (H.θ₂ - H.θ₁)) - x ≠ 0
    intro h
    exact gamma_ne S hx _ (sub_eq_zero.mp h)
  · show γ.γ (H.θ₁ - 2 * Real.pi + (t : ℝ) * (H.θ₂ - H.θ₁ + 2 * Real.pi)) - x ≠ 0
    intro h
    exact gamma_ne S hx _ (sub_eq_zero.mp h)

theorem dnP4_ne {hh : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp hh hs hball S) {x : ℂ} (hx : x ∈ S.V) : ∀ t, dnP4 H x t ≠ 0 := by
  intro t h
  exact tgtCut₂_ne H hx ⟨by linarith [t.2.2], by linarith [t.2.1]⟩ (sub_eq_zero.mp h)

/-! ## Non-vanishing of the loops -/

theorem upLoop_ne {hh : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp hh hs hball S) {x : ℂ} (hx : x ∈ S.V) (b : Bool) :
    ∀ t, upLoop H x b t ≠ 0 := by
  intro t h
  have hxlt := norm_lt_one_of_mem_V S hball hx
  have ht : Work.Smooth.SphereJordan.tgtUpB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
      (2 * Real.pi * (t : ℝ)) = x := by
    have h1 : (H.upPC b).γ (2 * Real.pi * (t : ℝ)) = x := sub_eq_zero.mp h
    rwa [SpanHyp.upPC_apply] at h1
  rw [Work.SphereJordan.tgtUpB_eq] at ht
  set σ : ℝ := Work.Smooth.SphereJordan.perPt (2 * Real.pi * (t : ℝ)) with hσdef
  have hσmem : σ ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
    have := Work.SphereJordan.perPt_mem (2 * Real.pi * (t : ℝ))
    exact ⟨this.1, le_of_lt this.2⟩
  by_cases h1 : σ ≤ Real.pi / 2
  · rw [Work.SphereJordan.tgtUpBun, if_pos h1] at ht
    exact srcOuterUp_ne S hxlt (σ / (Real.pi / 2)) ht
  · by_cases h2 : σ ≤ Real.pi
    · rw [Work.SphereJordan.tgtUpBun, if_neg h1, if_pos h2] at ht
      exact tgtCut₂_ne H hx (mem_Icc_div_pi_half (not_le.mp h1).le h2) ht
    · by_cases h3 : σ ≤ 3 * Real.pi / 2
      · rw [Work.SphereJordan.tgtUpBun, if_neg h1, if_neg h2, if_pos h3] at ht
        split_ifs at ht
        · exact gamma_ne S hx _ ht
        · exact gamma_ne S hx _ ht
      · rw [Work.SphereJordan.tgtUpBun, if_neg h1, if_neg h2, if_neg h3] at ht
        exact tgtCut₁_ne H hx (mem_Icc_one_sub_div_pi_half (not_le.mp h3).le hσmem.2) ht

theorem dnLoop_ne {hh : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp hh hs hball S) {x : ℂ} (hx : x ∈ S.V) (b : Bool) :
    ∀ t, dnLoop H x b t ≠ 0 := by
  intro t h
  have hxlt := norm_lt_one_of_mem_V S hball hx
  have ht : Work.Smooth.SphereJordan.tgtDnB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
      (2 * Real.pi * (t : ℝ)) = x := by
    have h1 : (H.dnPC b).γ (2 * Real.pi * (t : ℝ)) = x := sub_eq_zero.mp h
    rwa [SpanHyp.dnPC_apply] at h1
  rw [Work.SphereJordan.tgtDnB_eq] at ht
  set σ : ℝ := Work.Smooth.SphereJordan.perPt (2 * Real.pi * (t : ℝ)) with hσdef
  have hσmem : σ ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
    have := Work.SphereJordan.perPt_mem (2 * Real.pi * (t : ℝ))
    exact ⟨this.1, le_of_lt this.2⟩
  by_cases h1 : σ ≤ Real.pi / 2
  · rw [Work.SphereJordan.tgtDnBun, if_pos h1] at ht
    exact srcOuterDn_ne S hxlt (σ / (Real.pi / 2)) ht
  · by_cases h2 : σ ≤ Real.pi
    · rw [Work.SphereJordan.tgtDnBun, if_neg h1, if_pos h2] at ht
      exact tgtCut₁_ne H hx (mem_Icc_div_pi_half (not_le.mp h1).le h2) ht
    · by_cases h3 : σ ≤ 3 * Real.pi / 2
      · rw [Work.SphereJordan.tgtDnBun, if_neg h1, if_neg h2, if_pos h3] at ht
        split_ifs at ht
        · exact gamma_ne S hx _ ht
        · exact gamma_ne S hx _ ht
      · rw [Work.SphereJordan.tgtDnBun, if_neg h1, if_neg h2, if_neg h3] at ht
        exact tgtCut₂_ne H hx (mem_Icc_one_sub_div_pi_half (not_le.mp h3).le hσmem.2) ht

end Nonvan


/-! ## The increment of a closed loop, and the quarter reparametrisations -/

theorem incr'_eq_loopIndex {c : C(unitInterval, ℂ)} (hc : ∀ t, c t ≠ 0) (hcl : c 0 = c 1) :
    incr' c = (Work.Smooth.SphereJordan.loopIndex c : ℂ) * kappa := by
  rw [incr'_eq hc, kappa]
  exact incr_eq_loopIndex hc hcl

theorem q1_val (t : unitInterval) : ((q1 t : unitInterval) : ℝ) = (t : ℝ) / 4 := by
  change (0 : ℝ) + (1/4 - 0) * (t : ℝ) = (t : ℝ) / 4
  ring

theorem q2_val (t : unitInterval) : ((q2 t : unitInterval) : ℝ) = (t : ℝ) / 4 + 1/4 := by
  change (1/4 : ℝ) + (1/2 - 1/4) * (t : ℝ) = (t : ℝ) / 4 + 1/4
  ring

theorem q3_val (t : unitInterval) : ((q3 t : unitInterval) : ℝ) = (t : ℝ) / 4 + 1/2 := by
  change (1/2 : ℝ) + (3/4 - 1/2) * (t : ℝ) = (t : ℝ) / 4 + 1/2
  ring

theorem q4_val (t : unitInterval) : ((q4 t : unitInterval) : ℝ) = (t : ℝ) / 4 + 3/4 := by
  change (3/4 : ℝ) + (1 - 3/4) * (t : ℝ) = (t : ℝ) / 4 + 3/4
  ring

/-- `2π` times the first-quarter parameter, in normal form. -/
theorem two_pi_q1 (t : unitInterval) :
    2 * Real.pi * ((q1 t : unitInterval) : ℝ) = Real.pi * (t : ℝ) / 2 := by
  rw [q1_val]; ring

theorem two_pi_q2 (t : unitInterval) :
    2 * Real.pi * ((q2 t : unitInterval) : ℝ) = Real.pi / 2 + Real.pi * (t : ℝ) / 2 := by
  rw [q2_val]; ring

theorem two_pi_q3 (t : unitInterval) :
    2 * Real.pi * ((q3 t : unitInterval) : ℝ) = Real.pi + Real.pi * (t : ℝ) / 2 := by
  rw [q3_val]; ring

theorem two_pi_q4 (t : unitInterval) :
    2 * Real.pi * ((q4 t : unitInterval) : ℝ) = 3 * Real.pi / 2 + Real.pi * (t : ℝ) / 2 := by
  rw [q4_val]; ring

end

end Work.SphereJordan
