import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.CoreTopology.MustBeInessentialStandard
import Submission.Work.CoreTopology.IntersectionNumberDiffeomorphic
import Submission.Work.Smooth.Morse.Defs
import Submission.Work.CoreTopology.Transport
import Submission.Work.CoreTopology.compressing_winding_dichotomy

/-!
# The intersection lower bound `min p q ≤ |α ∩ β|` for WEAK compressing loops

`Work.CoreTopology.compressing_winding_dichotomy` and
`Work.CoreTopology.min_le_encard_inter_standardCurve` assume that the loop `α` of the
standard torus of revolution bounds an **embedded** disc (`BoundsDiskInComplement`).
Their proofs never use the injectivity of that disc, only its continuity, its boundary
values and the fact that its open part avoids the torus.

This file replays the two results with the injectivity hypothesis dropped, i.e. for
`Work.Drive.BoundsDiskInComplementW`, and transports the resulting counting bound to the
torus `F = ψ(F_std)` of the challenge, where `β = ψ(β_std)` is the image of the standard
`(p,q)`-curve and `α` is a simple essential loop of `F` bounding a weak disc in the
complement of `F`:

* `compressing_winding_dichotomyW` — a weak compressing essential loop of the standard
  torus has a winding vector with a vanishing component;
* `min_le_encard_inter_standardCurveW` — hence it meets `β_std` in at least `min p q`
  points;
* `min_le_encard_inter_of_boundsDiskW` — the statement of this file, obtained by pulling
  the loop back along the homeomorphism `ψ` (the intersection count is unchanged), so that
  the conclusion is stated for the original loop `α` and the knot `K` with
  `Set.range K.curve = Set.range β`.

## Main statement

`Work.CoreTopology.min_le_encard_inter_of_boundsDiskW`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.CoreTopology

noncomputable section

/-! ## Pulling a weak bounding disc back along a homeomorphism of `ℝ³` -/

/-- If `γ` is a closed curve of the torus `ψ(F_std)` which bounds a weak disc in the
complement of `ψ(F_std)`, then its pull-back `ψ⁻¹ ∘ γ` bounds a weak disc in the complement
of the standard torus: postcompose the disc with `ψ⁻¹`. -/
private theorem boundsDiskInComplementW_pullback (ψ : R3 ≃ₜ R3)
    (γ : ClosedCurve (ParamTorus.mapHomeomorph ψ))
    (hb : Work.Drive.BoundsDiskInComplementW (ParamTorus.mapHomeomorph ψ) γ) :
    Work.Drive.BoundsDiskInComplementW standard (ClosedCurve.mapHomeomorphInv ψ γ) := by
  obtain ⟨e, hbd, hoff⟩ := hb
  refine ⟨(homeomorphCMap ψ.symm).comp e, ?_, ?_⟩
  · intro θ
    show ψ.symm (e (circlePoint θ)) = ψ.symm (γ.γ θ)
    rw [hbd θ]
  · intro z hz hmem
    exact hoff z hz ((mem_carrier_mapHomeomorph_iff' ψ (e z)).mpr hmem)

/-! ## The classification of weak compressing loops and the counting bound on `F_std` -/

/-- **The classification of weak compressing loops on the standard torus.** Let `α` be an
essential closed curve of the standard torus of revolution which bounds a *continuous* disc
in `ℝ³` whose interior is disjoint from the torus. Then `α` is homotopic in the torus to a
multiple of the meridian or of the longitude: one component of the winding vector vanishes
for every lift.

This is `Work.CoreTopology.compressing_winding_dichotomy` with the injectivity of the disc
dropped; the proof uses only the continuity of the disc, its boundary values and the fact
that its open part avoids the torus, so it transplants verbatim. -/
private theorem compressing_winding_dichotomyW (α : ClosedCurve standard)
    (hess : IsEssential standard α) (hb : Work.Drive.BoundsDiskInComplementW standard α) :
    (∀ L : LiftOf standard α, (L.winding).2 = 0) ∨
      (∀ L : LiftOf standard α, (L.winding).1 = 0) := by
  obtain ⟨e, hbd, hoff⟩ := hb
  -- the height function on the closed disc misses the value `1` on the open disc, because
  -- the open part of the disc avoids `F`, the level set `{torusHeight = 1}`
  have hHcont : Continuous fun z : Metric.closedBall (0 : ℂ) 1 => torusHeight (e z) :=
    continuous_torusHeight.comp e.continuous
  have hne : ∀ z : Metric.closedBall (0 : ℂ) 1, ‖(z : ℂ)‖ < 1 → torusHeight (e z) ≠ 1 := by
    intro z hz h1
    exact hoff z hz ((torusHeight_eq_one_iff (e z)).mp h1)
  -- hence the open disc lies entirely in one of the two components of the complement
  rcases disk_sign_dichotomy (fun z => torusHeight (e z)) hHcont hne with hout | hin
  · -- the disc lies in the exterior component `{1 < torusHeight}`: the meridian coordinate
    -- `Φ` of any lift is a loop, so the second component of the winding vector vanishes
    left
    intro L
    have hW0 : ∀ z : Metric.closedBall (0 : ℂ) 1, meridVec (e z) ≠ 0 :=
      meridVec_ne_zero_of_disc α e hbd hout
    have hlift : ∀ t : ℝ,
        normCircle (meridVec (e (circlePoint t))) (hW0 (circlePoint t)) = Circle.exp (L.Φ t) := by
      intro t
      apply Subtype.ext
      rw [normCircle_coe, Circle.coe_exp]
      rw [show e (circlePoint t) = α.γ t from hbd t,
        show α.γ t = Work.Core.torusMap (L.Θ t) (L.Φ t) from (L.lifts t).symm]
      exact meridVec_torusMap_div_norm (L.Θ t) (L.Φ t)
    have hloop : L.Φ (2 * Real.pi) = L.Φ 0 :=
      circle_lift_eq_of_extends_disk_of_normCircle (fun z => meridVec (e z))
        (continuous_meridVec.comp e.continuous) hW0 L.Φ L.contΦ hlift
    have hspec := L.winding_spec.2
    have hmul : ((L.winding).2 : ℝ) * (2 * Real.pi) = 0 := by linarith [hspec]
    rcases mul_eq_zero.mp hmul with h | h
    · exact_mod_cast h
    · exact absurd h two_pi_ne_zero
  · -- the disc lies in the bounded component `{torusHeight < 1}`: the longitude coordinate
    -- `Θ` of any lift is a loop, so the first component of the winding vector vanishes
    right
    intro L
    have hW0 : ∀ z : Metric.closedBall (0 : ℂ) 1, horizVec (e z) ≠ 0 :=
      horizVec_ne_zero_of_disc α e hbd hin
    have hlift : ∀ t : ℝ,
        normCircle (horizVec (e (circlePoint t))) (hW0 (circlePoint t)) = Circle.exp (L.Θ t) := by
      intro t
      apply Subtype.ext
      rw [normCircle_coe, Circle.coe_exp]
      rw [show e (circlePoint t) = α.γ t from hbd t,
        show α.γ t = Work.Core.torusMap (L.Θ t) (L.Φ t) from (L.lifts t).symm]
      exact horizVec_torusMap_div_norm (L.Θ t) (L.Φ t)
    have hloop : L.Θ (2 * Real.pi) = L.Θ 0 :=
      circle_lift_eq_of_extends_disk_of_normCircle (fun z => horizVec (e z))
        (continuous_horizVec.comp e.continuous) hW0 L.Θ L.contΘ hlift
    have hspec := L.winding_spec.1
    have hmul : ((L.winding).1 : ℝ) * (2 * Real.pi) = 0 := by linarith [hspec]
    rcases mul_eq_zero.mp hmul with h | h
    · exact_mod_cast h
    · exact absurd h two_pi_ne_zero

/-- **The intersection lower bound for weak compressing loops of the standard torus.**  A
simple essential loop of the standard torus bounding a *continuous* disc in the complement
meets the standard `(p,q)`-curve (for `p, q > 0` coprime) in at least `min p q` points. -/
private theorem min_le_encard_inter_standardCurveW (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (α : ClosedCurve standard) (hsimple : IsSimple standard α)
    (hess : IsEssential standard α) (hb : Work.Drive.BoundsDiskInComplementW standard α) :
    (Nat.min p q : ℕ∞) ≤ Set.encard (Set.range α.γ ∩ Set.range (standardCurve p q).γ) := by
  rcases compressing_winding_dichotomyW α hess hb with h | h
  · obtain ⟨L, hw⟩ := hess
    exact min_le_encard_inter_standardCurve p q hp hq hc α hsimple L hw (Or.inr (h L))
  · obtain ⟨L, hw⟩ := hess
    exact min_le_encard_inter_standardCurve p q hp hq hc α hsimple L hw (Or.inl (h L))

/-! ## Transport to the torus of the challenge -/

/-- **The intersection lower bound for weak compressing loops of `F = ψ(F_std)`.**

Let `p, q > 0` be coprime, `F = ψ(F_std)` the image of the standard torus of revolution
under a diffeomorphism `ψ` of `ℝ³`, and let `K` be a knot whose curve has the same range as
`β = ψ(β_std)`, the image of the standard `(p,q)`-curve.  Then every simple essential loop
`α` of `F` which bounds a *continuous* disc in the complement of `F` meets `K` in at least
`min p q` points.

Indeed `ψ⁻¹ ∘ α` is a simple essential loop of the standard torus bounding the pulled-back
weak disc, so `min_le_encard_inter_standardCurveW` gives
`min p q ≤ |ψ⁻¹(α) ∩ β_std| = |α ∩ ψ(β_std)| = |α ∩ K|`. -/
theorem min_le_encard_inter_of_boundsDiskW
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    {ψ : Submission.Diffeo} {K : LeanEval.KnotTheory.PardonDistortion.Knot}
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    {α : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ)}
    (hsimple : Work.CoreTopology.IsSimple (Work.Smooth.Morse.torus ψ) α)
    (hess : Work.CoreTopology.IsEssential (Work.Smooth.Morse.torus ψ) α)
    (hb : Work.Drive.BoundsDiskInComplementW (Work.Smooth.Morse.torus ψ) α) :
    (Nat.min p q : ℕ∞) ≤ Set.encard (Set.range α.γ ∩ Set.range K.curve) := by
  have hsimple' : IsSimple standard (ClosedCurve.mapHomeomorphInv ψ.toHomeomorph α) :=
    (ClosedCurve.isSimple_mapHomeomorphInv_iff ψ.toHomeomorph α).mpr hsimple
  have hess' : IsEssential standard (ClosedCurve.mapHomeomorphInv ψ.toHomeomorph α) :=
    (ClosedCurve.isEssential_mapHomeomorphInv_iff ψ.toHomeomorph α).mpr hess
  have hb' : Work.Drive.BoundsDiskInComplementW standard
      (ClosedCurve.mapHomeomorphInv ψ.toHomeomorph α) :=
    boundsDiskInComplementW_pullback ψ.toHomeomorph α hb
  have h1 := min_le_encard_inter_standardCurveW p q hp hq hc _
    hsimple' hess' hb'
  rw [encard_inter_mapHomeomorphInv ψ.toHomeomorph α (standardCurve p q)] at h1
  rwa [← himg] at h1

end

end Work.CoreTopology
