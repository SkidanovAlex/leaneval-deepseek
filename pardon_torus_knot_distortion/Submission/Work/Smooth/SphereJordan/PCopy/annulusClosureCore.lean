import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.Jordan.All
import Submission.Work.Smooth.SphereJordan.PCopy.Setup
import Submission.Work.Smooth.SphereJordan.PCopy.interior_closure_V_eq
import Submission.Work.Smooth.SphereJordan.PCopy.strictClause_of_closureClause
import Submission.Work.Smooth.SphereJordan.OpenImageAux
import Submission.Work.Smooth.SphereJordan.brouwer_disc
import Submission.Work.Smooth.SphereJordan.ballHomeo_of_circleHomeo
import Submission.Work.Smooth.SphereJordan.planeTwoDiscs
import Submission.Work.Smooth.SphereJordan.Pasting
import Submission.Work.Smooth.SphereJordan.Twist
import Submission.Work.Smooth.SphereJordan.disc_spans_schoenflies_clean
import Submission.Work.Smooth.SphereJordan.discEmbedding_surjective

/-!
# The closure clause of the planar pcannulus theorem

`Work.Smooth.SphereJordan.annulusClosureCore`: for a simple closed plane curve `γ` whose trace lies
in the open unit disc, a planar Schoenflies datum `S` for it, there is a homeomorphism `Θ` of the
model disc `𝔻` which fixes the boundary circle pointwise and carries `closure S.V` onto the closed
half-disc `{‖z‖ ≤ 1/2}`.

## The reduction

The geometric content is isolated in the companion module
`Submission/Work/Smooth/SphereJordan/annulusInjectionCore.lean`
(`Work.Smooth.SphereJordan.annulusInjectionCore`): a *continuous injection* `F` of `𝔻` which fixes
`∂𝔻` pointwise and carries the *half-circle* `(1/2) e^{iθ}` to the curve `γ(θ)`.

From such an `F` the theorem follows in three steps.

* `pcG := F ∘ (z ↦ z/2)` is again an injection with boundary circle `γ` in the given
  parametrisation, so `disc_spans_schoenflies_clean` (the *uniqueness* of the spanning disc of a
  simple closed curve, a consequence of Brouwer's invariance of domain) shows
  `F ({‖z‖ ≤ 1/2}) = closure S.V` and `F ({‖z‖ < 1/2}) = S.V`.
* `F` is a *homeomorphism* of `𝔻`: it fixes `∂𝔻` pointwise and maps the open disc into itself
  (a point of the boundary has norm `1`, hence is `F` of a boundary point, hence by injectivity has
  norm `1`), so `discEmbedding_surjective` (Brouwer) gives surjectivity.
* `Θ := F⁻¹` therefore fixes `∂𝔻` pointwise and
  `x ∈ closure S.V ↔ Θ x ∈ Θ(closure S.V) = {‖z‖ ≤ 1/2}`, which is the statement.
-/

namespace Work.Smooth.SphereJordan

noncomputable section

open Set

/-- The halving map of the model disc, `z ↦ z/2`. -/
def pchalfMapFun : C(Disc, Disc) :=
  ⟨fun z => ⟨(1 / 2 : ℂ) * (z : ℂ), by
      have h := z.2
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_mul,
        show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
      linarith⟩, by fun_prop⟩

theorem pchalfMapFun_coe (z : Disc) :
    ((pchalfMapFun z : Disc) : ℂ) = (1 / 2 : ℂ) * (z : ℂ) := rfl

theorem pchalfMapFun_circlePoint (θ : ℝ) : pchalfMapFun (circlePoint θ) = halfCirclePoint θ := by
  apply Subtype.ext
  rw [pchalfMapFun_coe, halfCirclePoint_coe]

theorem pcnorm_halfMapFun (z : Disc) : ‖((pchalfMapFun z : Disc) : ℂ)‖ ≤ 1 / 2 := by
  rw [pchalfMapFun_coe, norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
  have h : ‖(z : ℂ)‖ ≤ 1 := by
    have h := z.2; rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
  linarith

theorem pchalfMapFun_injective : Function.Injective pchalfMapFun := by
  intro a b hab
  have hc := congrArg (fun w : Disc => ((w : Disc) : ℂ)) hab
  simp only [pchalfMapFun_coe] at hc
  have h3 : (a : ℂ) = (b : ℂ) := by
    calc (a : ℂ) = 2 * ((1 / 2 : ℂ) * (a : ℂ)) := by ring
      _ = 2 * ((1 / 2 : ℂ) * (b : ℂ)) := by rw [hc]
      _ = (b : ℂ) := by ring
  exact Subtype.ext h3

/-- The doubling map, as a map of the half-disc into the disc. -/
def pccoreDblMap (w : Disc) (hw : ‖(w : ℂ)‖ ≤ 1 / 2) : Disc :=
  ⟨2 * (w : ℂ), by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_mul,
      show ‖(2 : ℂ)‖ = 2 by norm_num]
    linarith⟩

theorem pccoreDblMap_coe (w : Disc) (hw : ‖(w : ℂ)‖ ≤ 1 / 2) :
    ((pccoreDblMap w hw : Disc) : ℂ) = 2 * (w : ℂ) := rfl

theorem pchalfMapFun_dblMap (w : Disc) (hw : ‖(w : ℂ)‖ ≤ 1 / 2) :
    pchalfMapFun (pccoreDblMap w hw) = w := by
  apply Subtype.ext
  rw [pchalfMapFun_coe, pccoreDblMap_coe]
  ring

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-- **Reduction.**  A continuous injection `F` of the model disc which fixes the boundary circle
pointwise and carries the (possibly reversed) half-circle `(1/2) e^{i s θ}` to the curve `γ(θ)`
yields the closure clause of the planar pcannulus theorem. -/
theorem pcannulusClosureCore_of_injection
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1)
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (F : C(Disc, Disc)) (s : ℝ) (hs : s = 1 ∨ s = -1) (hFinj : Function.Injective F)
    (hFbd : ∀ θ : ℝ, F (circlePoint θ) = circlePoint θ)
    (hFim : ∀ θ : ℝ, ((F (halfCirclePoint (s * θ)) : Disc) : ℂ) = γ.γ θ) :
    ∃ Θ : Disc ≃ₜ Disc,
      (∀ θ : ℝ, Θ (circlePoint θ) = circlePoint θ) ∧
      (∀ x : Disc, (((x : Disc) : ℂ) ∈ closure S.V) ↔ ‖((Θ x : Disc) : ℂ)‖ ≤ 1 / 2) := by
  -- absorb the orientation sign with the twist and halve
  set pcG : C(Disc, Disc) := F.comp (pchalfMapFun.comp (twistFun s)) with hGdef
  have hGinj : Function.Injective pcG :=
    hFinj.comp (pchalfMapFun_injective.comp (twistFun_injective hs))
  have hGbd : ∀ θ : ℝ, ((pcG (circlePoint θ) : Disc) : ℂ) = γ.γ θ := by
    intro θ
    have h1 : pcG (circlePoint θ) = F (halfCirclePoint (s * θ)) := by
      simp only [hGdef, ContinuousMap.comp_apply]
      rw [twistFun_circlePoint hs, pchalfMapFun_circlePoint]
    rw [h1]
    exact hFim θ
  obtain ⟨hrange, -⟩ := disc_spans_schoenflies_clean hball S hGinj hGbd
  have hFimage : ∀ x : Disc,
      x ∈ F '' {w : Disc | ‖((w : Disc) : ℂ)‖ ≤ 1 / 2} ↔
        (((x : Disc) : ℂ) ∈ closure S.V) := by
    intro x
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [← hrange]
      obtain ⟨z, hz⟩ := twistFun_surjective hs (pccoreDblMap w hw)
      refine ⟨z, ?_⟩
      show ((F (pchalfMapFun (twistFun s z)) : Disc) : ℂ) = ((F w : Disc) : ℂ)
      rw [hz, pchalfMapFun_dblMap]
    · intro hx
      rw [← hrange] at hx
      obtain ⟨z, hz⟩ := hx
      refine ⟨pchalfMapFun (twistFun s z), pcnorm_halfMapFun _, ?_⟩
      apply Subtype.ext
      show ((F (pchalfMapFun (twistFun s z)) : Disc) : ℂ) = ((x : Disc) : ℂ)
      rw [← hz]
      rfl
  have hint : ∀ z : Disc, ‖((z : Disc) : ℂ)‖ < 1 → ‖((F z : Disc) : ℂ)‖ < 1 := by
    intro z hz
    by_contra hcon
    have hle : ‖((F z : Disc) : ℂ)‖ ≤ 1 := by
      have h := (F z).2; rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
    have heq : ‖((F z : Disc) : ℂ)‖ = 1 := le_antisymm hle (not_lt.mp hcon)
    obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq (F z) heq
    have h1 : F (circlePoint θ) = F z := by
      rw [hFbd θ]
      exact hθ
    have h2 : circlePoint θ = z := hFinj h1
    rw [← h2] at hz
    rw [Work.Smooth.Jordan.circlePoint_coe, Complex.norm_exp_ofReal_mul_I] at hz
    exact lt_irrefl 1 hz
  have hsurj : Function.Surjective F := discEmbedding_surjective hFinj hFbd hint
  let e : Disc ≃ Disc := Equiv.ofBijective F ⟨hFinj, hsurj⟩
  have hec : Continuous (⇑e) := F.continuous
  let Θ : Disc ≃ₜ Disc := Continuous.homeoOfEquivCompactToT2 (f := e) hec
  have hFsymm : ∀ y : Disc, F (Θ.symm y) = y := by
    intro y
    show e (Θ.symm y) = y
    exact Θ.apply_symm_apply y
  refine ⟨Θ.symm, ?_, ?_⟩
  · intro θ
    apply hFinj
    rw [hFsymm, hFbd θ]
  · intro x
    have h1 : x ∈ F '' {w : Disc | ‖((w : Disc) : ℂ)‖ ≤ 1 / 2} ↔
        ‖((Θ.symm x : Disc) : ℂ)‖ ≤ 1 / 2 := by
      constructor
      · rintro ⟨w, hw, hwF⟩
        have h2 : w = Θ.symm x := hFinj (by rw [hwF, hFsymm x])
        rw [h2] at hw
        exact hw
      · intro hx
        exact ⟨Θ.symm x, hx, hFsymm x⟩
    rw [← hFimage x]
    exact h1

end

end Work.Smooth.SphereJordan
