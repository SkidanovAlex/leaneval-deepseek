import Submission.Work.Smooth.SphereJordan.Pasting

/-!
# The twist of the model disc

For a sign `s ∈ {1, -1}` the **twist** `twistFun s : 𝔻 → 𝔻` is the identity for `s = 1` and the
conjugation `z ↦ z̄` (in the coordinate of `ℂ`) for `s = -1`.  It is a continuous involution of the
model disc which preserves the norm, hence maps every concentric circle onto itself, and it realises
the reparametrisation `θ ↦ s θ` of each of those circles.

It is used to absorb the *orientation sign* of the annulus form of Schoenflies
(`Work.Smooth.SphereJordan.AnnulusSchoenflies`): the Schoenflies homeomorphism of an embedded disc
`h : 𝔻 → 𝔻` (with boundary circle in the open disc) maps the boundary circle of `h` onto the circle
of radius `1/2`, either preserving or reversing the parametrisation — which of the two happens is
the "orientation" of `h`, and it cannot be prescribed, because a homeomorphism of `𝔻` fixing `∂𝔻`
pointwise is orientation-preserving.  Composing with `twistFun s` converts the reversed case into
the forward one, so a construction expecting a *forward* parametrised boundary can consume the
sign-carrying statement `AnnulusSchoenflies` directly (this is how the cut-and-paste of
`Work.Smooth.SphereJordan.PastingDerive` handles the second application of the annulus theorem).

Nothing outside `Submission/Work/Smooth/SphereJordan/` is modified.
-/

open Set
open LeanEval.KnotTheory.PardonDistortion

namespace Work.Smooth.SphereJordan

noncomputable section

/-! ## Conjugation of the model disc -/

/-- **Conjugation of the model disc**, `z ↦ z̄` (in the coordinate of `ℂ`). -/
def conjDisc (z : Disc) : Disc :=
  ⟨(starRingEnd ℂ) ((z : Disc) : ℂ), by
    have hz := z.2
    rw [Metric.mem_closedBall, dist_zero_right] at hz ⊢
    rwa [Complex.norm_conj]⟩

theorem conjDisc_coe (z : Disc) :
    ((conjDisc z : Disc) : ℂ) = (starRingEnd ℂ) ((z : Disc) : ℂ) := rfl

theorem continuous_conjDisc : Continuous conjDisc :=
  Continuous.subtype_mk (Complex.continuous_conj.comp continuous_subtype_val) (fun z => by
    have hz := z.2
    rw [Metric.mem_closedBall, dist_zero_right] at hz ⊢
    show ‖(starRingEnd ℂ) ((z : Disc) : ℂ)‖ ≤ 1
    rwa [Complex.norm_conj])

/-- **Conjugation of the model disc** as a continuous map. -/
def conjDiscFun : C(Disc, Disc) := ⟨conjDisc, continuous_conjDisc⟩

theorem conjDiscFun_apply (z : Disc) : conjDiscFun z = conjDisc z := rfl

theorem conjDiscFun_coe (z : Disc) :
    ((conjDiscFun z : Disc) : ℂ) = (starRingEnd ℂ) ((z : Disc) : ℂ) := rfl

theorem conjDiscFun_norm (z : Disc) :
    ‖((conjDiscFun z : Disc) : ℂ)‖ = ‖((z : Disc) : ℂ)‖ := by
  rw [conjDiscFun_coe, Complex.norm_conj]

theorem conjDiscFun_injective : Function.Injective conjDiscFun := by
  intro a b hab
  have h : (starRingEnd ℂ) ((a : Disc) : ℂ) = (starRingEnd ℂ) ((b : Disc) : ℂ) := by
    rw [← conjDiscFun_coe, ← conjDiscFun_coe, hab]
  exact Subtype.ext ((starRingEnd ℂ).injective h)

theorem conjDiscFun_involutive : Function.Involutive conjDiscFun := by
  intro z
  apply Subtype.ext
  rw [conjDiscFun_coe, conjDiscFun_coe]
  exact Complex.conj_conj ((z : Disc) : ℂ)

/-- Conjugation carries the boundary circle of the model disc onto itself, reversing the
parametrisation. -/
theorem conjDiscFun_circlePoint (θ : ℝ) :
    conjDiscFun (circlePoint θ) = circlePoint (-θ) := by
  apply Subtype.ext
  rw [conjDiscFun_coe, Work.Smooth.Jordan.circlePoint_coe,
    Work.Smooth.Jordan.circlePoint_coe, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I, Complex.ofReal_neg]
  congr 1
  ring

/-! ## The twist -/

/-- **The twist of the model disc**: the identity for `s = 1` and the conjugation for `s = -1`. -/
def twistFun (s : ℝ) : C(Disc, Disc) :=
  if s = 1 then ContinuousMap.id Disc else conjDiscFun

theorem twistFun_apply (s : ℝ) (z : Disc) :
    twistFun s z = if s = 1 then z else conjDiscFun z := by
  unfold twistFun
  by_cases h : s = 1
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h]

theorem twistFun_eq_one (h : (1 : ℝ) = 1) : twistFun 1 = ContinuousMap.id Disc := by
  rw [twistFun, if_pos h]

theorem twistFun_norm (s : ℝ) (z : Disc) :
    ‖((twistFun s z : Disc) : ℂ)‖ = ‖((z : Disc) : ℂ)‖ := by
  rw [twistFun_apply]
  by_cases h : s = 1
  · rw [if_pos h]
  · rw [if_neg h]
    exact conjDiscFun_norm z

theorem twistFun_circlePoint {s : ℝ} (hs : s = 1 ∨ s = -1) (θ : ℝ) :
    twistFun s (circlePoint θ) = circlePoint (s * θ) := by
  rw [twistFun_apply]
  rcases hs with h | h
  · rw [if_pos h, h, one_mul]
  · rw [if_neg (by rw [h]; norm_num), h, neg_one_mul]
    exact conjDiscFun_circlePoint θ

/-- Conjugation of `1/2` (the radius of the half-circle): the real number `1/2` is fixed by
conjugation. -/
theorem conj_half : (starRingEnd ℂ) (1 / 2 : ℂ) = (1 / 2 : ℂ) := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]

theorem twistFun_halfCirclePoint {s : ℝ} (hs : s = 1 ∨ s = -1) (θ : ℝ) :
    twistFun s (halfCirclePoint θ) = halfCirclePoint (s * θ) := by
  rw [twistFun_apply]
  rcases hs with h | h
  · rw [if_pos h, h, one_mul]
  · rw [if_neg (by rw [h]; norm_num), h, neg_one_mul]
    apply Subtype.ext
    rw [conjDiscFun_coe, halfCirclePoint_coe, halfCirclePoint_coe, map_mul, conj_half,
      ← conjDiscFun_coe, conjDiscFun_circlePoint]

theorem twistFun_injective {s : ℝ} (hs : s = 1 ∨ s = -1) : Function.Injective (twistFun s) := by
  rcases hs with h | h
  · rw [h, show twistFun 1 = ContinuousMap.id Disc from twistFun_eq_one rfl]
    exact Function.injective_id
  · rw [h, show twistFun (-1) = conjDiscFun from by
      rw [twistFun, if_neg (by norm_num : (-1 : ℝ) ≠ 1)]]
    exact conjDiscFun_injective

theorem twistFun_involutive {s : ℝ} (hs : s = 1 ∨ s = -1) : Function.Involutive (twistFun s) := by
  intro z
  rcases hs with h | h
  · rw [h, show twistFun 1 = ContinuousMap.id Disc from twistFun_eq_one rfl]
    rfl
  · rw [h, show twistFun (-1) = conjDiscFun from by
      rw [twistFun, if_neg (by norm_num : (-1 : ℝ) ≠ 1)]]
    exact conjDiscFun_involutive z

theorem twistFun_surjective {s : ℝ} (hs : s = 1 ∨ s = -1) : Function.Surjective (twistFun s) :=
  (twistFun_involutive hs).surjective

theorem range_twistFun {s : ℝ} (hs : s = 1 ∨ s = -1) :
    Set.range (twistFun s) = Set.univ :=
  Set.range_eq_univ.mpr (twistFun_surjective hs)

/-- The twist preserves the closed half-disc (and, by the norm identity, the open one). -/
theorem twistFun_mem_half {s : ℝ} (hs : s = 1 ∨ s = -1) {z : Disc}
    (hz : ‖((z : Disc) : ℂ)‖ ≤ 1 / 2) :
    ‖((twistFun s z : Disc) : ℂ)‖ ≤ 1 / 2 := by
  rw [twistFun_norm]; exact hz

end

end Work.Smooth.SphereJordan
