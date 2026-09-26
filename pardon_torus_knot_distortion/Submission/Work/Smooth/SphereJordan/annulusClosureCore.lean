import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.Jordan.All
import Submission.Work.Smooth.SphereJordan.annulus_of_planeHypothesis
import Submission.Work.Smooth.SphereJordan.interior_closure_V_eq
import Submission.Work.Smooth.SphereJordan.strictClause_of_closureClause
import Submission.Work.Smooth.SphereJordan.OpenImageAux
import Submission.Work.Smooth.SphereJordan.brouwer_disc
import Submission.Work.Smooth.SphereJordan.ballHomeo_of_circleHomeo
import Submission.Work.Smooth.SphereJordan.planeTwoDiscs
import Submission.Work.Smooth.SphereJordan.Pasting
import Submission.Work.Smooth.SphereJordan.Twist
import Submission.Work.Smooth.SphereJordan.disc_spans_schoenflies_clean
import Submission.Work.Smooth.SphereJordan.discEmbedding_surjective
import Submission.Work.Smooth.SphereJordan.PCopy.annulusInjectionTwoCutsAlt

/-!
# The closure clause of the planar annulus theorem

`Work.Smooth.SphereJordan.annulusClosureCore`: for a simple closed plane curve `γ` whose trace lies
in the open unit disc, a planar Schoenflies datum `S` for it, there is a homeomorphism `Θ` of the
model disc `𝔻` which fixes the boundary circle pointwise and carries `closure S.V` onto the closed
half-disc `{‖z‖ ≤ 1/2}`.

## The reduction

The geometric content is the *injection form* of the planar annulus theorem
(`Work.Smooth.SphereJordan.pcannulusInjectionTwoCutsAlt`, the completed "two cuts" construction): there
is a *continuous injection* `F : 𝔻 → 𝔻`, with a sign `s = ± 1`, which fixes `∂𝔻` pointwise and
carries the (possibly reversed) half-circle `(1/2) e^{i s θ}` to the curve `γ(θ)`.

From such an `F` the theorem follows in three steps.

* `G := F ∘ (z ↦ z/2) ∘ twist_s` is again an injection whose boundary circle is `γ` in the given
  parametrisation, so `disc_spans_schoenflies_clean` (the *uniqueness* of the spanning disc of a
  simple closed curve, a consequence of Brouwer's invariance of domain) shows
  `F ({‖z‖ ≤ 1/2}) = closure S.V` (and `F ({‖z‖ < 1/2}) = S.V`).
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
def halfMapFun : C(Disc, Disc) :=
  ⟨fun z => ⟨(1 / 2 : ℂ) * (z : ℂ), by
      have h := z.2
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_mul,
        show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
      linarith⟩, by fun_prop⟩

theorem halfMapFun_coe (z : Disc) :
    ((halfMapFun z : Disc) : ℂ) = (1 / 2 : ℂ) * (z : ℂ) := rfl

theorem halfMapFun_circlePoint (θ : ℝ) : halfMapFun (circlePoint θ) = halfCirclePoint θ := by
  apply Subtype.ext
  rw [halfMapFun_coe, halfCirclePoint_coe]

theorem norm_halfMapFun (z : Disc) : ‖((halfMapFun z : Disc) : ℂ)‖ ≤ 1 / 2 := by
  rw [halfMapFun_coe, norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
  have h : ‖(z : ℂ)‖ ≤ 1 := by
    have h := z.2; rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
  linarith

theorem halfMapFun_injective : Function.Injective halfMapFun := by
  intro a b hab
  have hc := congrArg (fun w : Disc => ((w : Disc) : ℂ)) hab
  simp only [halfMapFun_coe] at hc
  have h3 : (a : ℂ) = (b : ℂ) := by
    calc (a : ℂ) = 2 * ((1 / 2 : ℂ) * (a : ℂ)) := by ring
      _ = 2 * ((1 / 2 : ℂ) * (b : ℂ)) := by rw [hc]
      _ = (b : ℂ) := by ring
  exact Subtype.ext h3

/-- The doubling map, as a map of the half-disc into the disc. -/
def coreDblMap (w : Disc) (hw : ‖(w : ℂ)‖ ≤ 1 / 2) : Disc :=
  ⟨2 * (w : ℂ), by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_mul,
      show ‖(2 : ℂ)‖ = 2 by norm_num]
    linarith⟩

theorem coreDblMap_coe (w : Disc) (hw : ‖(w : ℂ)‖ ≤ 1 / 2) :
    ((coreDblMap w hw : Disc) : ℂ) = 2 * (w : ℂ) := rfl

theorem halfMapFun_dblMap (w : Disc) (hw : ‖(w : ℂ)‖ ≤ 1 / 2) :
    halfMapFun (coreDblMap w hw) = w := by
  apply Subtype.ext
  rw [halfMapFun_coe, coreDblMap_coe]
  ring

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-- **Reduction.**  A continuous injection `F` of the model disc which fixes the boundary circle
pointwise and carries the (possibly reversed) half-circle `(1/2) e^{i s θ}` to the curve `γ(θ)`
yields the closure clause of the planar annulus theorem. -/
theorem annulusClosureCore_of_injection
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1)
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (F : C(Disc, Disc)) (s : ℝ) (hs : s = 1 ∨ s = -1) (hFinj : Function.Injective F)
    (hFbd : ∀ θ : ℝ, F (circlePoint θ) = circlePoint θ)
    (hFim : ∀ θ : ℝ, ((F (halfCirclePoint (s * θ)) : Disc) : ℂ) = γ.γ θ) :
    ∃ Θ : Disc ≃ₜ Disc,
      (∀ θ : ℝ, Θ (circlePoint θ) = circlePoint θ) ∧
      (∀ x : Disc, (((x : Disc) : ℂ) ∈ closure S.V) ↔ ‖((Θ x : Disc) : ℂ)‖ ≤ 1 / 2) := by
  -- absorb the orientation sign with the twist and halve
  set G : C(Disc, Disc) := F.comp (halfMapFun.comp (twistFun s)) with hGdef
  have hGinj : Function.Injective G :=
    hFinj.comp (halfMapFun_injective.comp (twistFun_injective hs))
  have hGbd : ∀ θ : ℝ, ((G (circlePoint θ) : Disc) : ℂ) = γ.γ θ := by
    intro θ
    have h1 : G (circlePoint θ) = F (halfCirclePoint (s * θ)) := by
      simp only [hGdef, ContinuousMap.comp_apply]
      rw [twistFun_circlePoint hs, halfMapFun_circlePoint]
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
      obtain ⟨z, hz⟩ := twistFun_surjective hs (coreDblMap w hw)
      refine ⟨z, ?_⟩
      show ((F (halfMapFun (twistFun s z)) : Disc) : ℂ) = ((F w : Disc) : ℂ)
      rw [hz, halfMapFun_dblMap]
    · intro hx
      rw [← hrange] at hx
      obtain ⟨z, hz⟩ := hx
      refine ⟨halfMapFun (twistFun s z), norm_halfMapFun _, ?_⟩
      apply Subtype.ext
      show ((F (halfMapFun (twistFun s z)) : Disc) : ℂ) = ((x : Disc) : ℂ)
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

/-- **The closure clause of the planar annulus theorem.**

For a simple closed plane curve `γ` whose trace lies in the open unit disc and a planar Schoenflies
datum `S` for it, the closure of the bounded side `S.V` is carried onto the closed half-disc by a
homeomorphism of `𝔻` fixing the boundary circle pointwise. -/
theorem annulusClosureCore (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    {γ : Work.Smooth.Jordan.PlaneCurve} (hs : γ.IsSimple) (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1)
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    ∃ Θ : Work.Smooth.SphereJordan.Disc ≃ₜ Work.Smooth.SphereJordan.Disc,
      (∀ θ : ℝ, Θ (Work.Smooth.SphereJordan.circlePoint θ) = Work.Smooth.SphereJordan.circlePoint θ) ∧
      (∀ x : Work.Smooth.SphereJordan.Disc,
        (((x : Work.Smooth.SphereJordan.Disc) : ℂ) ∈ closure S.V) ↔
        ‖((Θ x : Work.Smooth.SphereJordan.Disc) : ℂ)‖ ≤ 1 / 2) := by
  obtain ⟨F, s, hs1, hFinj, hFbd, hFim⟩ :=
    Work.Smooth.SphereJordan.pcannulusInjectionTwoCutsAlt h hs hball S
  exact annulusClosureCore_of_injection hball S F s hs1 hFinj hFbd hFim

end

end Work.Smooth.SphereJordan
