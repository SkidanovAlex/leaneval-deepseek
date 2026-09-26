import Mathlib
import Submission.Work.Smooth.SphereJordan.PCopy.SpanHyp
import Submission.Work.Smooth.SphereJordan.PCopy.tgtUpPC_isSimple
import Submission.Work.SphereJordan.incrOn
import Submission.Work.Smooth.SphereJordan.BoundedSide
import Submission.Work.Smooth.SphereJordan.loopIndex_eq_of_homotopy

/-!
# The paths of the two-pccuts pairing identities

This module sets up the objects needed for `Work.SphereJordan.pcwindNumber_pairing_identities`:
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
def pckappa : ℂ := 2 * (Real.pi : ℂ) * Complex.I

theorem pckappa_ne_zero : pckappa ≠ 0 := by
  rw [pckappa]
  exact Work.Smooth.SphereJordan.two_pi_I_ne_zero

/-! ## The increment of a path, made total -/

/-- The increment of a path, made total by setting it to `0` on a path that vanishes. -/
def pcincr' (c : C(unitInterval, ℂ)) : ℂ :=
  if h : ∀ t, c t ≠ 0 then incr h else 0

theorem pcincr'_eq {c : C(unitInterval, ℂ)} (h : ∀ t, c t ≠ 0) : pcincr' c = incr h := by
  rw [pcincr', dif_pos h]

theorem pcincr'_zero {c : C(unitInterval, ℂ)} (h : ¬ ∀ t, c t ≠ 0) : pcincr' c = 0 := by
  rw [pcincr', dif_neg h]

theorem pcincr'_congr {c d : C(unitInterval, ℂ)} (h : ∀ t, c t = d t) : pcincr' c = pcincr' d := by
  by_cases hc : ∀ t, c t ≠ 0
  · have hd : ∀ t, d t ≠ 0 := fun t => by rw [← h t]; exact hc t
    rw [pcincr'_eq hc, pcincr'_eq hd]
    exact incr_congr hc hd h
  · have hd : ¬ ∀ t, d t ≠ 0 := by
      intro hd
      exact hc fun t => by rw [h t]; exact hd t
    rw [pcincr'_zero hc, pcincr'_zero hd]

theorem pcrevI_val (t : unitInterval) : ((revI t : unitInterval) : ℝ) = 1 - (t : ℝ) := by
  change (1 : ℝ) + (0 - 1) * (t : ℝ) = 1 - (t : ℝ)
  ring

theorem pcrevI_involutive (t : unitInterval) : revI (revI t) = t := by
  apply Subtype.ext
  rw [pcrevI_val, pcrevI_val]
  simp

theorem pcincr'_rev (c : C(unitInterval, ℂ)) : pcincr' (c.comp revI) = -pcincr' c := by
  by_cases hc : ∀ t, c t ≠ 0
  · have hcomp : ∀ t, c.comp revI t ≠ 0 := fun t => hc _
    rw [pcincr'_eq hc, pcincr'_eq hcomp]
    exact incr_rev hc
  · have hcomp : ¬ ∀ t, c.comp revI t ≠ 0 := by
      intro hcomp
      refine hc fun t => ?_
      have h := hcomp (revI t)
      rwa [ContinuousMap.comp_apply, pcrevI_involutive] at h
    rw [pcincr'_zero hc, pcincr'_zero hcomp]
    simp

/-- **Increment of a reparametrised path**, in terms of any chosen lift of the path. -/
theorem pcincr'_comp {c : C(unitInterval, ℂ)} (hc : ∀ t, c t ≠ 0)
    (σ : C(unitInterval, unitInterval)) :
    pcincr' (c.comp σ) = liftOf hc (σ 1) - liftOf hc (σ 0) := by
  have hcomp : ∀ t, c.comp σ t ≠ 0 := fun t => hc (σ t)
  rw [pcincr'_eq hcomp]
  exact incr_comp hc σ

/-- **Additivity of the increment over a concatenation described by two reparametrisations.** -/
theorem pcincr'_comp_add {c : C(unitInterval, ℂ)} (hc : ∀ t, c t ≠ 0)
    {σ τ : C(unitInterval, unitInterval)} (h : τ 1 = σ 0) :
    pcincr' (c.comp σ) + pcincr' (c.comp τ) = liftOf hc (σ 1) - liftOf hc (τ 0) := by
  rw [pcincr'_comp hc σ, pcincr'_comp hc τ, h]
  ring

/-! ## The two `1/2` reparametrisations -/

/-- The first half of the unit interval. -/
def pchalf1 : C(unitInterval, unitInterval) :=
  linMap 0 (1/2) (linMap_mem 0 (1/2) (by norm_num) (by norm_num) (by norm_num))

/-- The second half of the unit interval. -/
def pchalf2 : C(unitInterval, unitInterval) :=
  linMap (1/2) 1 (linMap_mem (1/2) 1 (by norm_num) (by norm_num) (by norm_num))

theorem pchalf1_zero : pchalf1 0 = 0 := by
  apply Subtype.ext
  change (0 : ℝ) + (1/2 - 0) * (((0 : unitInterval)) : ℝ) = 0
  norm_num

theorem pchalf1_one : pchalf1 1 = (⟨1/2, by norm_num⟩ : unitInterval) := by
  apply Subtype.ext
  change (0 : ℝ) + (1/2 - 0) * (((1 : unitInterval)) : ℝ) = 1/2
  norm_num

theorem pchalf2_zero : pchalf2 0 = (⟨1/2, by norm_num⟩ : unitInterval) := by
  apply Subtype.ext
  change (1/2 : ℝ) + (1 - 1/2) * (((0 : unitInterval)) : ℝ) = 1/2
  norm_num

theorem pchalf2_one : pchalf2 1 = 1 := by
  apply Subtype.ext
  change (1/2 : ℝ) + (1 - 1/2) * (((1 : unitInterval)) : ℝ) = 1
  norm_num

theorem pchalf1_val (t : unitInterval) : ((pchalf1 t : unitInterval) : ℝ) = (t : ℝ) / 2 := by
  change (0 : ℝ) + (1/2 - 0) * (t : ℝ) = (t : ℝ) / 2
  ring

theorem pchalf2_val (t : unitInterval) : ((pchalf2 t : unitInterval) : ℝ) = (t : ℝ) / 2 + 1/2 := by
  change (1/2 : ℝ) + (1 - 1/2) * (t : ℝ) = (t : ℝ) / 2 + 1/2
  ring

/-! ## The loops of the four four-arc curves -/

section Defs

variable {hh : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
  {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}

/-- The loop of the upper target curve about `x`, with pairing flag `b`. -/
def pcupLoop (H : pcSpanHyp hh hs hball S) (x : ℂ) (b : Bool) : C(unitInterval, ℂ) :=
  Work.Smooth.SphereJordan.curveLoop (fun t => (H.pcupPC b).γ t - x)
    ((H.pcupPC b).cont.sub continuous_const)

/-- The loop of the lower target curve about `x`, with pairing flag `b`. -/
def pcdnLoop (H : pcSpanHyp hh hs hball S) (x : ℂ) (b : Bool) : C(unitInterval, ℂ) :=
  Work.Smooth.SphereJordan.curveLoop (fun t => (H.pcdnPC b).γ t - x)
    ((H.pcdnPC b).cont.sub continuous_const)

/-- `windNumber` of the upper target curve is the index of its loop. -/
theorem pcwindNumber_upLoop (H : pcSpanHyp hh hs hball S) (x : ℂ) (b : Bool) :
    Work.Smooth.SphereJordan.windNumber (H.pcupPC b).γ (H.pcupPC b).cont x
      = Work.Smooth.SphereJordan.loopIndex (pcupLoop H x b) := rfl

/-- `windNumber` of the lower target curve is the index of its loop. -/
theorem pcwindNumber_dnLoop (H : pcSpanHyp hh hs hball S) (x : ℂ) (b : Bool) :
    Work.Smooth.SphereJordan.windNumber (H.pcdnPC b).γ (H.pcdnPC b).cont x
      = Work.Smooth.SphereJordan.loopIndex (pcdnLoop H x b) := rfl

/-- The first piece of the upper loop: the upper outer semicircle. -/
def pcupP1 (H : pcSpanHyp hh hs hball S) (x : ℂ) : C(unitInterval, ℂ) :=
  ⟨fun t => Work.Smooth.SphereJordan.pcsrcOuterUp S (t : ℝ) - x,
    ((pccontinuous_srcOuterUp S).comp continuous_subtype_val).sub continuous_const⟩

/-- The second piece of the upper loop: the second crosscut, inward. -/
def pcupP2 (H : pcSpanHyp hh hs hball S) (x : ℂ) : C(unitInterval, ℂ) :=
  ⟨fun t => Work.Smooth.SphereJordan.pctgtCut₂ S H.t₂ H.s₂ (t : ℝ) - x,
    ((pccontinuous_tgtCut₂ S H.t₂ H.s₂).comp continuous_subtype_val).sub continuous_const⟩

/-- The third piece of the upper loop: the `γ`-arc selected by `b`. -/
def pcupP3 (H : pcSpanHyp hh hs hball S) (x : ℂ) (b : Bool) : C(unitInterval, ℂ) :=
  ⟨fun t => (if b then γ.γ (H.θ₂ + (t : ℝ) * (H.θ₁ - H.θ₂))
      else γ.γ (H.θ₂ + (t : ℝ) * (H.θ₁ - H.θ₂ - 2 * Real.pi))) - x, by
    cases b
    · exact (γ.cont.comp (continuous_const.add (continuous_subtype_val.mul continuous_const))).sub
        continuous_const
    · exact (γ.cont.comp (continuous_const.add (continuous_subtype_val.mul continuous_const))).sub
        continuous_const⟩

/-- The fourth piece of the upper loop: the first crosscut, outward. -/
def pcupP4 (H : pcSpanHyp hh hs hball S) (x : ℂ) : C(unitInterval, ℂ) :=
  ⟨fun t => Work.Smooth.SphereJordan.pctgtCut₁ S H.t₁ H.s₁ (1 - (t : ℝ)) - x,
    ((pccontinuous_tgtCut₁ S H.t₁ H.s₁).comp (continuous_const.sub continuous_subtype_val)).sub
      continuous_const⟩

/-- The first piece of the lower loop: the lower outer semicircle. -/
def pcdnP1 (H : pcSpanHyp hh hs hball S) (x : ℂ) : C(unitInterval, ℂ) :=
  ⟨fun t => Work.Smooth.SphereJordan.pcsrcOuterDn S (t : ℝ) - x,
    ((pccontinuous_srcOuterDn S).comp continuous_subtype_val).sub continuous_const⟩

/-- The second piece of the lower loop: the first crosscut, inward. -/
def pcdnP2 (H : pcSpanHyp hh hs hball S) (x : ℂ) : C(unitInterval, ℂ) :=
  ⟨fun t => Work.Smooth.SphereJordan.pctgtCut₁ S H.t₁ H.s₁ (t : ℝ) - x,
    ((pccontinuous_tgtCut₁ S H.t₁ H.s₁).comp continuous_subtype_val).sub continuous_const⟩

/-- The third piece of the lower loop: the `γ`-arc selected by `b`. -/
def pcdnP3 (H : pcSpanHyp hh hs hball S) (x : ℂ) (b : Bool) : C(unitInterval, ℂ) :=
  ⟨fun t => (if b then γ.γ (H.θ₁ - 2 * Real.pi + (t : ℝ) * (H.θ₂ - H.θ₁ + 2 * Real.pi))
      else γ.γ (H.θ₁ + (t : ℝ) * (H.θ₂ - H.θ₁))) - x, by
    cases b
    · exact (γ.cont.comp (continuous_const.add (continuous_subtype_val.mul continuous_const))).sub
        continuous_const
    · exact (γ.cont.comp (continuous_const.add (continuous_subtype_val.mul continuous_const))).sub
        continuous_const⟩

/-- The fourth piece of the lower loop: the second crosscut, outward. -/
def pcdnP4 (H : pcSpanHyp hh hs hball S) (x : ℂ) : C(unitInterval, ℂ) :=
  ⟨fun t => Work.Smooth.SphereJordan.pctgtCut₂ S H.t₂ H.s₂ (1 - (t : ℝ)) - x,
    ((pccontinuous_tgtCut₂ S H.t₂ H.s₂).comp (continuous_const.sub continuous_subtype_val)).sub
      continuous_const⟩

/-! ## The circle loop and the `γ`-period loop -/

/-- The full unit circle, traversed once from `pccutDir S`, about `x`. -/
def pcouterLoop (H : pcSpanHyp hh hs hball S) (x : ℂ) : C(unitInterval, ℂ) :=
  ⟨fun t => Work.Smooth.SphereJordan.pccutDir S *
      Complex.exp ((((2 * Real.pi * (t : ℝ) : ℝ)) : ℂ) * Complex.I) - x, by fun_prop⟩

/-- The standard exponential loop `t ↦ e^{2πit}`. -/
def pcexpLoop : C(unitInterval, ℂ) :=
  ⟨fun t => Complex.exp ((((2 * Real.pi * (t : ℝ) : ℝ)) : ℂ) * Complex.I), by fun_prop⟩

/-- The "small" loop `t ↦ pccutDir S - x e^{-2πit}`. -/
def pcstarLoop (H : pcSpanHyp hh hs hball S) (x : ℂ) : C(unitInterval, ℂ) :=
  ⟨fun t => Work.Smooth.SphereJordan.pccutDir S -
      x * Complex.exp ((((-(2 * Real.pi * (t : ℝ)) : ℝ)) : ℂ) * Complex.I), by fun_prop⟩

/-- The `γ`-loop over the period starting at `θ₁`. -/
def pcgammaLoop (H : pcSpanHyp hh hs hball S) (x : ℂ) : C(unitInterval, ℂ) :=
  ⟨fun t => γ.γ (H.θ₁ + 2 * Real.pi * (t : ℝ)) - x,
    (γ.cont.comp (continuous_const.add (continuous_const.mul continuous_subtype_val))).sub
      continuous_const⟩

end Defs


/-! ## Non-vanishing of the pieces: elementary facts about the points of the configuration -/

section Nonvan

/-- A point of the bounded side is off the trace. -/
theorem pcnotMem_trace_of_mem_V (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {x : ℂ}
    (hx : x ∈ S.V) : x ∉ γ.trace := by
  intro htr
  have hsub : S.V ⊆ γ.traceᶜ := by
    intro y hy
    have h : y ∈ S.U ∪ S.V := Or.inr hy
    rwa [S.union_eq] at h
  exact hsub hx htr

/-- A point of the bounded side of a curve inside the open disc has norm `< 1`. -/
theorem pcnorm_lt_one_of_mem_V (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
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
theorem pcgamma_ne (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {x : ℂ} (hx : x ∈ S.V)
    (r : ℝ) : γ.γ r ≠ x :=
  fun h => pcnotMem_trace_of_mem_V S hx ⟨r, h⟩

/-- The lower outer semicircle lies on the unit circle. -/
theorem pcnorm_srcOuterDn (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (r : ℝ) :
    ‖Work.Smooth.SphereJordan.pcsrcOuterDn S r‖ = 1 := by
  rw [Work.Smooth.SphereJordan.pcsrcOuterDn, norm_mul, norm_neg,
    Work.Smooth.SphereJordan.pcnorm_cutDir, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem pcsrcOuterUp_ne (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {x : ℂ} (hx : ‖x‖ < 1)
    (r : ℝ) : Work.Smooth.SphereJordan.pcsrcOuterUp S r ≠ x := by
  intro h
  have h1 := pcnorm_srcOuterUp S r
  rw [h] at h1
  rw [h1] at hx
  exact lt_irrefl 1 hx

theorem pcsrcOuterDn_ne (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {x : ℂ} (hx : ‖x‖ < 1)
    (r : ℝ) : Work.Smooth.SphereJordan.pcsrcOuterDn S r ≠ x := by
  intro h
  have h1 := pcnorm_srcOuterDn S r
  rw [h] at h1
  rw [h1] at hx
  exact lt_irrefl 1 hx

/-- The parameter of the second branch lies in `[0,1]`. -/
theorem pcmem_Icc_div_pi_half {σ : ℝ} (h1 : Real.pi / 2 ≤ σ) (h2 : σ ≤ Real.pi) :
    (σ - Real.pi / 2) / (Real.pi / 2) ∈ Set.Icc (0 : ℝ) 1 := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  constructor
  · exact div_nonneg (by linarith) hpi.le
  · rw [div_le_one hpi]; linarith

/-- The parameter of the fourth branch lies in `[0,1]`. -/
theorem pcmem_Icc_one_sub_div_pi_half {σ : ℝ} (h1 : 3 * Real.pi / 2 ≤ σ)
    (h2 : σ ≤ 2 * Real.pi) :
    1 - (σ - 3 * Real.pi / 2) / (Real.pi / 2) ∈ Set.Icc (0 : ℝ) 1 := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  have hd : 0 ≤ (σ - 3 * Real.pi / 2) / (Real.pi / 2) := div_nonneg (by linarith) hpi.le
  constructor
  · rw [sub_nonneg, div_le_one hpi]; linarith
  · linarith

/-- No point of the closed first crosscut is `x`. -/
theorem pctgtCut₁_ne {hh : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp hh hs hball S) {x : ℂ} (hx : x ∈ S.V) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    Work.Smooth.SphereJordan.pctgtCut₁ S H.t₁ H.s₁ r ≠ x := by
  set σ : ℝ := H.s₁ + r * (H.t₁ - H.s₁) with hσdef
  have hval : Work.Smooth.SphereJordan.pctgtCut₁ S H.t₁ H.s₁ r =
      (Work.Smooth.SphereJordan.pcbase S : ℂ) + (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S := rfl
  intro hcon
  have hxσ : (Work.Smooth.SphereJordan.pcbase S : ℂ) + (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S
      = x := by rw [← hval]; exact hcon
  rcases lt_or_eq_of_le hr.2 with hrl | hr1
  · rcases eq_or_lt_of_le hr.1 with hr0 | hrpos
    · -- `r = 0`: the value is `pccutDir S`
      have hσ : σ = H.s₁ := by rw [hσdef, ← hr0]; ring
      have hxu : x = Work.Smooth.SphereJordan.pccutDir S := by
        rw [← hxσ, hσ, H.hout₁]
      have hnorm : ‖x‖ = 1 := by rw [hxu, Work.Smooth.SphereJordan.pcnorm_cutDir]
      have := pcnorm_lt_one_of_mem_V S hball hx
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
    exact pcgamma_ne S hx H.θ₁ hγ

/-- No point of the closed second crosscut is `x`. -/
theorem pctgtCut₂_ne {hh : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp hh hs hball S) {x : ℂ} (hx : x ∈ S.V) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    Work.Smooth.SphereJordan.pctgtCut₂ S H.t₂ H.s₂ r ≠ x := by
  set σ : ℝ := H.s₂ + r * (H.t₂ - H.s₂) with hσdef
  have hval : Work.Smooth.SphereJordan.pctgtCut₂ S H.t₂ H.s₂ r =
      (Work.Smooth.SphereJordan.pcbase S : ℂ) - (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S := rfl
  intro hcon
  have hxσ : (Work.Smooth.SphereJordan.pcbase S : ℂ) - (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S
      = x := by rw [← hval]; exact hcon
  rcases lt_or_eq_of_le hr.2 with hrl | hr1
  · rcases eq_or_lt_of_le hr.1 with hr0 | hrpos
    · -- `r = 0`: the value is `-pccutDir S`
      have hσ : σ = H.s₂ := by rw [hσdef, ← hr0]; ring
      have hxu : x = -Work.Smooth.SphereJordan.pccutDir S := by
        rw [← hxσ, hσ, H.hout₂]
      have hnorm : ‖x‖ = 1 := by
        rw [hxu, norm_neg, Work.Smooth.SphereJordan.pcnorm_cutDir]
      have := pcnorm_lt_one_of_mem_V S hball hx
      rw [hnorm] at this
      exact lt_irrefl 1 this
    · have hlt1 : H.t₂ < σ := by rw [hσdef]; nlinarith [H.ht₂s₂]
      have hlt2 : σ < H.s₂ := by rw [hσdef]; nlinarith [H.ht₂s₂]
      have hmem := H.hseg₂ σ hlt1 hlt2
      rw [hxσ] at hmem
      exact hmem.2 hx
  · have hσ : σ = H.t₂ := by rw [hσdef, hr1]; ring
    have hγ : γ.γ H.θ₂ = x := by rw [H.hθ₂, ← hσ]; exact hxσ
    exact pcgamma_ne S hx H.θ₂ hγ

/-! ## Non-vanishing of the pieces -/

theorem pcupP1_ne {hh : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp hh hs hball S) {x : ℂ} (hx : x ∈ S.V) : ∀ t, pcupP1 H x t ≠ 0 := by
  intro t h
  exact pcsrcOuterUp_ne S (pcnorm_lt_one_of_mem_V S hball hx) (t : ℝ) (sub_eq_zero.mp h)

theorem pcupP2_ne {hh : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp hh hs hball S) {x : ℂ} (hx : x ∈ S.V) : ∀ t, pcupP2 H x t ≠ 0 := by
  intro t h
  exact pctgtCut₂_ne H hx ⟨t.2.1, t.2.2⟩ (sub_eq_zero.mp h)

theorem pcupP3_ne {hh : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp hh hs hball S) {x : ℂ} (hx : x ∈ S.V) (b : Bool) :
    ∀ t, pcupP3 H x b t ≠ 0 := by
  intro t
  cases b
  · show γ.γ (H.θ₂ + (t : ℝ) * (H.θ₁ - H.θ₂ - 2 * Real.pi)) - x ≠ 0
    intro h
    exact pcgamma_ne S hx _ (sub_eq_zero.mp h)
  · show γ.γ (H.θ₂ + (t : ℝ) * (H.θ₁ - H.θ₂)) - x ≠ 0
    intro h
    exact pcgamma_ne S hx _ (sub_eq_zero.mp h)

theorem pcupP4_ne {hh : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp hh hs hball S) {x : ℂ} (hx : x ∈ S.V) : ∀ t, pcupP4 H x t ≠ 0 := by
  intro t h
  exact pctgtCut₁_ne H hx ⟨by linarith [t.2.2], by linarith [t.2.1]⟩ (sub_eq_zero.mp h)

theorem pcdnP1_ne {hh : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp hh hs hball S) {x : ℂ} (hx : x ∈ S.V) : ∀ t, pcdnP1 H x t ≠ 0 := by
  intro t h
  exact pcsrcOuterDn_ne S (pcnorm_lt_one_of_mem_V S hball hx) (t : ℝ) (sub_eq_zero.mp h)

theorem pcdnP2_ne {hh : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp hh hs hball S) {x : ℂ} (hx : x ∈ S.V) : ∀ t, pcdnP2 H x t ≠ 0 := by
  intro t h
  exact pctgtCut₁_ne H hx ⟨t.2.1, t.2.2⟩ (sub_eq_zero.mp h)

theorem pcdnP3_ne {hh : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp hh hs hball S) {x : ℂ} (hx : x ∈ S.V) (b : Bool) :
    ∀ t, pcdnP3 H x b t ≠ 0 := by
  intro t
  cases b
  · show γ.γ (H.θ₁ + (t : ℝ) * (H.θ₂ - H.θ₁)) - x ≠ 0
    intro h
    exact pcgamma_ne S hx _ (sub_eq_zero.mp h)
  · show γ.γ (H.θ₁ - 2 * Real.pi + (t : ℝ) * (H.θ₂ - H.θ₁ + 2 * Real.pi)) - x ≠ 0
    intro h
    exact pcgamma_ne S hx _ (sub_eq_zero.mp h)

theorem pcdnP4_ne {hh : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp hh hs hball S) {x : ℂ} (hx : x ∈ S.V) : ∀ t, pcdnP4 H x t ≠ 0 := by
  intro t h
  exact pctgtCut₂_ne H hx ⟨by linarith [t.2.2], by linarith [t.2.1]⟩ (sub_eq_zero.mp h)

/-! ## Non-vanishing of the loops -/

theorem pcupLoop_ne {hh : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp hh hs hball S) {x : ℂ} (hx : x ∈ S.V) (b : Bool) :
    ∀ t, pcupLoop H x b t ≠ 0 := by
  intro t h
  have hxlt := pcnorm_lt_one_of_mem_V S hball hx
  have ht : Work.Smooth.SphereJordan.pctgtUpB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
      (2 * Real.pi * (t : ℝ)) = x := by
    have h1 : (H.pcupPC b).γ (2 * Real.pi * (t : ℝ)) = x := sub_eq_zero.mp h
    rwa [pcSpanHyp.pcupPC_apply] at h1
  rw [Work.SphereJordan.pctgtUpB_eq] at ht
  set σ : ℝ := Work.Smooth.SphereJordan.pcperPt (2 * Real.pi * (t : ℝ)) with hσdef
  have hσmem : σ ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
    have := Work.SphereJordan.pcperPt_mem (2 * Real.pi * (t : ℝ))
    exact ⟨this.1, le_of_lt this.2⟩
  by_cases h1 : σ ≤ Real.pi / 2
  · rw [Work.SphereJordan.pctgtUpBun, if_pos h1] at ht
    exact pcsrcOuterUp_ne S hxlt (σ / (Real.pi / 2)) ht
  · by_cases h2 : σ ≤ Real.pi
    · rw [Work.SphereJordan.pctgtUpBun, if_neg h1, if_pos h2] at ht
      exact pctgtCut₂_ne H hx (pcmem_Icc_div_pi_half (not_le.mp h1).le h2) ht
    · by_cases h3 : σ ≤ 3 * Real.pi / 2
      · rw [Work.SphereJordan.pctgtUpBun, if_neg h1, if_neg h2, if_pos h3] at ht
        split_ifs at ht
        · exact pcgamma_ne S hx _ ht
        · exact pcgamma_ne S hx _ ht
      · rw [Work.SphereJordan.pctgtUpBun, if_neg h1, if_neg h2, if_neg h3] at ht
        exact pctgtCut₁_ne H hx (pcmem_Icc_one_sub_div_pi_half (not_le.mp h3).le hσmem.2) ht

theorem pcdnLoop_ne {hh : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp hh hs hball S) {x : ℂ} (hx : x ∈ S.V) (b : Bool) :
    ∀ t, pcdnLoop H x b t ≠ 0 := by
  intro t h
  have hxlt := pcnorm_lt_one_of_mem_V S hball hx
  have ht : Work.Smooth.SphereJordan.pctgtDnB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
      (2 * Real.pi * (t : ℝ)) = x := by
    have h1 : (H.pcdnPC b).γ (2 * Real.pi * (t : ℝ)) = x := sub_eq_zero.mp h
    rwa [pcSpanHyp.pcdnPC_apply] at h1
  rw [Work.SphereJordan.pctgtDnB_eq] at ht
  set σ : ℝ := Work.Smooth.SphereJordan.pcperPt (2 * Real.pi * (t : ℝ)) with hσdef
  have hσmem : σ ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
    have := Work.SphereJordan.pcperPt_mem (2 * Real.pi * (t : ℝ))
    exact ⟨this.1, le_of_lt this.2⟩
  by_cases h1 : σ ≤ Real.pi / 2
  · rw [Work.SphereJordan.pctgtDnBun, if_pos h1] at ht
    exact pcsrcOuterDn_ne S hxlt (σ / (Real.pi / 2)) ht
  · by_cases h2 : σ ≤ Real.pi
    · rw [Work.SphereJordan.pctgtDnBun, if_neg h1, if_pos h2] at ht
      exact pctgtCut₁_ne H hx (pcmem_Icc_div_pi_half (not_le.mp h1).le h2) ht
    · by_cases h3 : σ ≤ 3 * Real.pi / 2
      · rw [Work.SphereJordan.pctgtDnBun, if_neg h1, if_neg h2, if_pos h3] at ht
        split_ifs at ht
        · exact pcgamma_ne S hx _ ht
        · exact pcgamma_ne S hx _ ht
      · rw [Work.SphereJordan.pctgtDnBun, if_neg h1, if_neg h2, if_neg h3] at ht
        exact pctgtCut₂_ne H hx (pcmem_Icc_one_sub_div_pi_half (not_le.mp h3).le hσmem.2) ht

end Nonvan


/-! ## The increment of a closed loop, and the quarter reparametrisations -/

theorem pcincr'_eq_loopIndex {c : C(unitInterval, ℂ)} (hc : ∀ t, c t ≠ 0) (hcl : c 0 = c 1) :
    pcincr' c = (Work.Smooth.SphereJordan.loopIndex c : ℂ) * pckappa := by
  rw [pcincr'_eq hc, pckappa]
  exact incr_eq_loopIndex hc hcl

theorem pcq1_val (t : unitInterval) : ((q1 t : unitInterval) : ℝ) = (t : ℝ) / 4 := by
  change (0 : ℝ) + (1/4 - 0) * (t : ℝ) = (t : ℝ) / 4
  ring

theorem pcq2_val (t : unitInterval) : ((q2 t : unitInterval) : ℝ) = (t : ℝ) / 4 + 1/4 := by
  change (1/4 : ℝ) + (1/2 - 1/4) * (t : ℝ) = (t : ℝ) / 4 + 1/4
  ring

theorem pcq3_val (t : unitInterval) : ((q3 t : unitInterval) : ℝ) = (t : ℝ) / 4 + 1/2 := by
  change (1/2 : ℝ) + (3/4 - 1/2) * (t : ℝ) = (t : ℝ) / 4 + 1/2
  ring

theorem pcq4_val (t : unitInterval) : ((q4 t : unitInterval) : ℝ) = (t : ℝ) / 4 + 3/4 := by
  change (3/4 : ℝ) + (1 - 3/4) * (t : ℝ) = (t : ℝ) / 4 + 3/4
  ring

/-- `2π` times the first-quarter parameter, in normal form. -/
theorem pctwo_pi_q1 (t : unitInterval) :
    2 * Real.pi * ((q1 t : unitInterval) : ℝ) = Real.pi * (t : ℝ) / 2 := by
  rw [pcq1_val]; ring

theorem pctwo_pi_q2 (t : unitInterval) :
    2 * Real.pi * ((q2 t : unitInterval) : ℝ) = Real.pi / 2 + Real.pi * (t : ℝ) / 2 := by
  rw [pcq2_val]; ring

theorem pctwo_pi_q3 (t : unitInterval) :
    2 * Real.pi * ((q3 t : unitInterval) : ℝ) = Real.pi + Real.pi * (t : ℝ) / 2 := by
  rw [pcq3_val]; ring

theorem pctwo_pi_q4 (t : unitInterval) :
    2 * Real.pi * ((q4 t : unitInterval) : ℝ) = 3 * Real.pi / 2 + Real.pi * (t : ℝ) / 2 := by
  rw [pcq4_val]; ring

end

end Work.SphereJordan
