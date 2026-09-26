import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.BoxShrink.Pinch.Defs
import Submission.Work.PinchCounted.not_exists_compressingLoop_of_counts
import Submission.Work.CoreTopology.compressing_winding_dichotomy
import Submission.Work.CoreTopology.min_le_encard_inter_standardCurve

/-!
# Pardon's counting bound for the WEAK compressing loops

The strong statement `Work.PinchCounted.not_exists_compressingLoop_of_counts` forbids an
essential simple loop `α` of the torus that bounds an *embedded* disc in the complement and
meets the knot `K` only on the boundary sphere `∂PBox s c σ`, whose intersection with `K` is
counted by `hcount`.  Its proof uses Pardon's invariant `I(F, β) = min p q` through
`pardonsI_le`, whose input is `BoundsDiskInComplement`.

Here the disc is allowed to be an arbitrary *continuous* map of the closed disc with boundary
`α` and open part off the torus (`Work.Drive.BoundsDiskInComplementW`); no injectivity is
required.  The whole proof transplants, because the only topological input,
`compressing_winding_dichotomy`, never uses injectivity of the disc: we replay it verbatim
(`compressing_winding_dichotomyW`), deduce the intersection lower bound
`min p q ≤ |α ∩ β|` for weak compressing loops (`min_le_encard_inter_standardCurveW`), and
transport it to the diffeomorphic torus of the challenge
(`min_le_encard_inter_of_boundsDiskW`).  The final counting argument is that of the strong
statement, word for word.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.Drive

open Work.CoreTopology

set_option linter.unusedVariables false

noncomputable section

/-! ## Transport of weak bounding discs under an ambient homeomorphism -/

/-- Pushing the weak bounding disc of `α` forward along `ψ` gives a weak bounding disc of
the image curve. -/
theorem isBoundingDiskW_mapHomeomorph (ψ : R3 ≃ₜ R3) (α : ClosedCurve standard)
    (e : C(Metric.closedBall (0 : ℂ) 1, R3)) (he : IsBoundingDiskW standard α e) :
    IsBoundingDiskW (ParamTorus.mapHomeomorph ψ) (ClosedCurve.mapHomeomorph ψ α)
      ((homeomorphCMap ψ).comp e) := by
  obtain ⟨hcircle, hint⟩ := he
  refine ⟨?_, ?_⟩
  · intro θ
    show ψ (e (circlePoint θ)) = ψ (α.γ θ)
    rw [hcircle θ]
  · intro z hz
    show ψ (e z) ∉ (ParamTorus.mapHomeomorph ψ).carrier
    rw [mem_carrier_mapHomeomorph_iff]
    exact hint z hz

/-- Pulling a weak bounding disc of the image curve back along `ψ` gives a weak bounding disc
of `α`. -/
theorem isBoundingDiskW_mapHomeomorph_inv (ψ : R3 ≃ₜ R3) (α : ClosedCurve standard)
    (e : C(Metric.closedBall (0 : ℂ) 1, R3))
    (he : IsBoundingDiskW (ParamTorus.mapHomeomorph ψ) (ClosedCurve.mapHomeomorph ψ α) e) :
    IsBoundingDiskW standard α ((homeomorphCMap ψ.symm).comp e) := by
  obtain ⟨hcircle, hint⟩ := he
  refine ⟨?_, ?_⟩
  · intro θ
    have h : e (circlePoint θ) = ψ (α.γ θ) := by
      simpa only [ClosedCurve.mapHomeomorph_apply] using hcircle θ
    show ψ.symm (e (circlePoint θ)) = α.γ θ
    rw [h, ψ.symm_apply_apply]
  · intro z hz
    show ψ.symm (e z) ∉ standard.carrier
    intro hmem
    exact hint z hz ((mem_carrier_mapHomeomorph_iff' ψ (e z)).mpr hmem)

/-- Bounding a weak disc in the complement of the torus transports along `ψ`. -/
theorem boundsDiskInComplementW_mapHomeomorph_iff (ψ : R3 ≃ₜ R3) (α : ClosedCurve standard) :
    BoundsDiskInComplementW (ParamTorus.mapHomeomorph ψ) (ClosedCurve.mapHomeomorph ψ α) ↔
      BoundsDiskInComplementW standard α := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨(homeomorphCMap ψ.symm).comp e, isBoundingDiskW_mapHomeomorph_inv ψ α e he⟩
  · rintro ⟨e, he⟩
    exact ⟨(homeomorphCMap ψ).comp e, isBoundingDiskW_mapHomeomorph ψ α e he⟩

/-- A curve on the image torus bounds a weak disc in the complement iff its pull-back does. -/
theorem boundsDiskInComplementW_mapHomeomorphInv_iff (ψ : R3 ≃ₜ R3)
    (γ : ClosedCurve (ParamTorus.mapHomeomorph ψ)) :
    BoundsDiskInComplementW standard (ClosedCurve.mapHomeomorphInv ψ γ) ↔
      BoundsDiskInComplementW (ParamTorus.mapHomeomorph ψ) γ := by
  have h := boundsDiskInComplementW_mapHomeomorph_iff ψ (ClosedCurve.mapHomeomorphInv ψ γ)
  rw [ClosedCurve.mapHomeomorph_mapHomeomorphInv ψ γ] at h
  exact h.symm

/-! ## The weak compressing-loop classification and the intersection lower bound -/

/-- **The classification of weak compressing loops on the standard torus.** Let `α` be an
essential closed curve on the standard torus of revolution which bounds a *continuous* disc in
`ℝ³` whose interior is disjoint from the torus. Then `α` is homotopic in the torus to a multiple
of the meridian or of the longitude.

This is `Work.CoreTopology.compressing_winding_dichotomy` with the injectivity of the disc
dropped: the proof only ever uses the continuity of the disc, its boundary values and the fact
that its open part avoids the torus. -/
theorem compressing_winding_dichotomyW (α : ClosedCurve standard)
    (hess : IsEssential standard α) (hb : BoundsDiskInComplementW standard α) :
    (∀ L : LiftOf standard α, (L.winding).2 = 0) ∨
      (∀ L : LiftOf standard α, (L.winding).1 = 0) := by
  obtain ⟨e, hbd, hoff⟩ := hb
  have hHcont : Continuous fun z : Metric.closedBall (0 : ℂ) 1 => torusHeight (e z) :=
    continuous_torusHeight.comp e.continuous
  have hne : ∀ z : Metric.closedBall (0 : ℂ) 1, ‖(z : ℂ)‖ < 1 → torusHeight (e z) ≠ 1 := by
    intro z hz h1
    exact hoff z hz ((torusHeight_eq_one_iff (e z)).mp h1)
  rcases disk_sign_dichotomy (fun z => torusHeight (e z)) hHcont hne with hout | hin
  · left
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
  · right
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
theorem min_le_encard_inter_standardCurveW (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (α : ClosedCurve standard) (hsimple : IsSimple standard α)
    (hess : IsEssential standard α) (hb : BoundsDiskInComplementW standard α) :
    (Nat.min p q : ℕ∞) ≤ Set.encard (Set.range α.γ ∩ Set.range (standardCurve p q).γ) := by
  rcases compressing_winding_dichotomyW α hess hb with h | h
  · obtain ⟨L, hw⟩ := hess
    exact min_le_encard_inter_standardCurve p q hp hq hc α hsimple L hw (Or.inr (h L))
  · obtain ⟨L, hw⟩ := hess
    exact min_le_encard_inter_standardCurve p q hp hq hc α hsimple L hw (Or.inl (h L))

/-! ## Transport to the torus of the challenge -/

/-- **The intersection lower bound on the transported torus.**  For the torus `F = ψ(F_std)`
image of the standard torus under a diffeomorphism and `β = ψ(β_std)` the image of the standard
`(p,q)`-curve, every simple essential loop `α` of `F` bounding a weak disc in the complement
meets `ψ(β_std)` in at least `min p q` points. -/
theorem min_le_encard_inter_of_boundsDiskW
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot)
    (himg : Set.range K.curve = Set.range
      (ClosedCurve.mapHomeomorph ψ.toHomeomorph (standardCurve p q)).γ)
    {α : ClosedCurve (Work.Smooth.Morse.torus ψ)}
    (hsimple : IsSimple (Work.Smooth.Morse.torus ψ) α)
    (hess : IsEssential (Work.Smooth.Morse.torus ψ) α)
    (hb : BoundsDiskInComplementW (Work.Smooth.Morse.torus ψ) α) :
    (Nat.min p q : ℕ∞) ≤ Set.encard (Set.range α.γ ∩ Set.range K.curve) := by
  have hsimple' : IsSimple standard (ClosedCurve.mapHomeomorphInv ψ.toHomeomorph α) :=
    (ClosedCurve.isSimple_mapHomeomorphInv_iff ψ.toHomeomorph α).mpr hsimple
  have hess' : IsEssential standard (ClosedCurve.mapHomeomorphInv ψ.toHomeomorph α) :=
    (ClosedCurve.isEssential_mapHomeomorphInv_iff ψ.toHomeomorph α).mpr hess
  have hb' : BoundsDiskInComplementW standard (ClosedCurve.mapHomeomorphInv ψ.toHomeomorph α) :=
    (boundsDiskInComplementW_mapHomeomorphInv_iff ψ.toHomeomorph α).mpr hb
  have h1 := min_le_encard_inter_standardCurveW p q hp hq hc _
    hsimple' hess' hb'
  rw [encard_inter_mapHomeomorphInv ψ.toHomeomorph α (standardCurve p q)] at h1
  rwa [← himg] at h1

/-! ## The counting argument -/

/-- The intersections of the knot `K` with the boundary sphere `∂PBox s c σ` are hit by
parameters in the fundamental period `[0, 2π)`. -/
private theorem encard_range_inter_sphereSet_le_param
    (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ) :
    Set.encard (Set.range K.curve ∩ Work.BoxShrink.Core.sphereSet c σ s) ≤
      Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s} := by
  refine le_trans (Set.encard_le_encard ?_) (Set.encard_image_le K.curve _)
  rintro y ⟨⟨t, rfl⟩, hyS⟩
  have hnorm : Submission.boxNorm c σ (K.curve t) = s :=
    Work.BoxShrink.Core.mem_sphereSet.mp hyS
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  set n : ℤ := ⌊t / (2 * Real.pi)⌋ with hn
  have hnle : (n : ℝ) ≤ t / (2 * Real.pi) := by
    rw [hn]; exact Int.floor_le _
  have hnlt : t / (2 * Real.pi) < (n : ℝ) + 1 := by
    rw [hn]; exact Int.lt_floor_add_one _
  have hle : 0 ≤ t - (n : ℝ) * (2 * Real.pi) := by
    have := (le_div_iff₀ hpos).mp hnle
    linarith
  have hlt : t - (n : ℝ) * (2 * Real.pi) < 2 * Real.pi := by
    have := (div_lt_iff₀ hpos).mp hnlt
    linarith
  have hper : Function.Periodic K.curve (2 * Real.pi) := K.periodic
  have hcurve : K.curve (t - (n : ℝ) * (2 * Real.pi)) = K.curve t :=
    hper.sub_int_mul_eq n
  exact ⟨t - (n : ℝ) * (2 * Real.pi),
    ⟨⟨hle, hlt⟩, by rw [hcurve]; exact hnorm⟩, hcurve⟩

/-- **Pardon's counting bound forbids weak compressing loops in the sphere slice.**  Under the
hypotheses of the challenge (set-up, distortion hypothesis and the count `hcount`), no essential
simple loop of `F = ψ(F_std)` can bound a *continuous* disc in the complement of `F` while lying
on the boundary sphere `∂PBox s c σ`; indeed such a loop would meet the knot at least `min p q`
times, while the knot meets the sphere in fewer than `min p q` points. -/
theorem not_exists_weakCompressingLoop_of_counts
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : LeanEval.KnotTheory.PardonDistortion.Knot) {d : ℝ} (hd : 0 ≤ d)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    {s : ℝ} (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3))
    (hcount : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d))) :
    ¬ ∃ α : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ),
        Work.CoreTopology.IsSimple (Work.Smooth.Morse.torus ψ) α ∧
        Work.CoreTopology.IsEssential (Work.Smooth.Morse.torus ψ) α ∧
        Work.Drive.BoundsDiskInComplementW (Work.Smooth.Morse.torus ψ) α ∧
        ∀ t : ℝ, α.γ t ∈ Work.BoxShrink.Core.sphereSet c σ s := by
  rintro ⟨α, hsimple, hess, hb, hαS⟩
  -- every simple weak-compressing essential loop of the torus meets the knot at least
  -- `min p q` times
  have hle : (Nat.min p q : ℕ∞) ≤ Set.encard (Set.range α.γ ∩ Set.range K.curve) :=
    min_le_encard_inter_of_boundsDiskW p q hp hq hc ψ K himg hsimple hess hb
  -- those intersections lie on the boundary sphere, which itself meets the knot only at the
  -- parameters counted by `hcount`
  have hmono : Set.encard (Set.range α.γ ∩ Set.range K.curve) ≤
      Set.encard (Set.range K.curve ∩ Work.BoxShrink.Core.sphereSet c σ s) := by
    refine Set.encard_le_encard ?_
    rintro y ⟨⟨t, rfl⟩, hyK⟩
    exact ⟨hyK, hαS t⟩
  have hcount_lt : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
      Submission.boxNorm c σ (K.curve t) = s} < (Nat.min p q : ℕ∞) :=
    Work.BoxShrink.Core.encard_lt_of_coe_le_ofReal (n := Nat.min p q) (ne_of_gt (lt_min hp hq))
      hcount (Work.BoxShrink.Core.ten_coeff_mul_lt_min hp hq hd hsmall)
  exact absurd (le_trans hle (le_trans hmono (encard_range_inter_sphereSet_le_param K c σ s)))
    (not_le.mpr hcount_lt)

end

end Work.Drive
