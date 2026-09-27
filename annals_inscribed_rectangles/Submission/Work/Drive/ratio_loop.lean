import Mathlib
import Submission.Work.Drive.WindingNumber
import Submission.Work.Drive.smooth_jordan_separation

/-!
# The chord-ratio loop of a closed plane curve

For a closed plane curve `γ : ℝ/ℤ → ℝ²` and two points `p`, `p'` off it, the **ratio loop**
`ratioLoop γ p p'` is the doubled direction of the ratio of the two chords from `p` and from `p'` to
the running point `γ u`:

`u ↦ dirZ ((γ u - p)/(γ u - p'))`.

It is continuous (`continuous_ratioLoop`) and its degree computes the *difference* of the winding
numbers of `γ` about `p` and about `p'` (`winding_sub_eq_degree_ratioLoop`): this is the
`ℝ/ℤ`-parametrised form of `Work.Drive.windG_sub_eq_degree`.

The main use is the "two-sided" input of the capping step (`Work.Drive.exists_winding_ne_zero`): at a
regular point of a smooth embedded closed curve, the two points on the normal on either side of the
curve have different winding numbers, because the ratio loop of the two chord families from them has
degree `2` (the argument of the ratio sweeps from `-π` to `π` across the point).

`degree_comp_add_right` records the invariance of the degree under rotating the parameter of the
circle: `degree (u ↦ f (u + c)) = degree f`.
-/

namespace Work.Drive

open scoped Topology

noncomputable section

/-- The **chord-ratio loop** of a closed plane curve: the doubled direction of the ratio of the two
chords from `p` and from `p'` to the running point of the curve. -/
def ratioLoop (γ : UnitAddCircle → ℝ × ℝ) (p p' : ℝ × ℝ) : UnitAddCircle → UnitAddCircle :=
  fun u => dirZ (cpx (γ u - p) / cpx (γ u - p'))

lemma ratioLoop_apply (γ : UnitAddCircle → ℝ × ℝ) (p p' : ℝ × ℝ) (u : UnitAddCircle) :
    ratioLoop γ p p' u = dirZ (cpx (γ u - p) / cpx (γ u - p')) := rfl

/-- The ratio loop of a curve about two points off it is continuous. -/
theorem continuous_ratioLoop (γ : UnitAddCircle → ℝ × ℝ) (hγ : Continuous γ) {p p' : ℝ × ℝ}
    (hp : p ∉ Set.range γ) (hp' : p' ∉ Set.range γ) : Continuous (ratioLoop γ p p') := by
  have hval : ∀ u : UnitAddCircle, γ u ≠ p ∧ γ u ≠ p' := fun u =>
    ⟨fun h => hp ⟨u, h⟩, fun h => hp' ⟨u, h⟩⟩
  have hnum : Continuous fun u : UnitAddCircle => cpx (γ u - p) :=
    continuous_cpx.comp (hγ.sub continuous_const)
  have hden : Continuous fun u : UnitAddCircle => cpx (γ u - p') :=
    continuous_cpx.comp (hγ.sub continuous_const)
  have hne : ∀ u : UnitAddCircle, cpx (γ u - p') ≠ 0 := fun u => by
    rw [cpx_ne_zero_iff, sub_ne_zero]; exact (hval u).2
  have hratio : Continuous fun u : UnitAddCircle => cpx (γ u - p) / cpx (γ u - p') :=
    hnum.div hden hne
  have hpair : Continuous fun u : UnitAddCircle =>
      ((cpx (γ u - p) / cpx (γ u - p')).re, (cpx (γ u - p) / cpx (γ u - p')).im) :=
    Continuous.prodMk (Complex.continuous_re.comp hratio) (Complex.continuous_im.comp hratio)
  have hneR : ∀ u : UnitAddCircle, cpx (γ u - p) / cpx (γ u - p') ≠ 0 := by
    intro u
    refine div_ne_zero ?_ ?_ <;> rw [cpx_ne_zero_iff, sub_ne_zero] <;>
      [exact (hval u).1; exact (hval u).2]
  have hne' : ∀ u : UnitAddCircle,
      ((cpx (γ u - p) / cpx (γ u - p')).re, (cpx (γ u - p) / cpx (γ u - p')).im) ≠ 0 := by
    intro u h
    refine hneR u ?_
    rw [← cpx_mk (cpx (γ u - p) / cpx (γ u - p')), h, cpx_zero]
  have hpairC : ContinuousOn (fun u : UnitAddCircle =>
      ((cpx (γ u - p) / cpx (γ u - p')).re, (cpx (γ u - p) / cpx (γ u - p')).im)) Set.univ :=
    hpair.continuousOn
  have hc := Submission.Configuration.continuousOn_dirC.comp hpairC (fun x _ => hne' x)
  have hfun : ratioLoop γ p p' = fun u : UnitAddCircle =>
      Submission.Collision.dirC ((cpx (γ u - p) / cpx (γ u - p')).re,
        (cpx (γ u - p) / cpx (γ u - p')).im) := by
    funext u
    exact dirZ_eq_dirC _
  rw [hfun]
  exact continuousOn_univ.mp hc

/-- **The difference of the winding numbers about two points is the degree of the ratio loop.** -/
theorem winding_sub_eq_degree_ratioLoop (γ : UnitAddCircle → ℝ × ℝ) (hγ : Continuous γ)
    {p p' : ℝ × ℝ} (hp : p ∉ Set.range γ) (hp' : p' ∉ Set.range γ) :
    winding γ hγ hp - winding γ hγ hp'
      = degree (ratioLoop γ p p') (continuous_ratioLoop γ hγ hp hp') := by
  have hfun : dirCurve γ hγ p hp - dirCurve γ hγ p' hp' = ratioLoop γ p p' := by
    funext u
    rw [Pi.sub_apply]
    exact dirC_sub_eq _ _ (fun h => hp ⟨u, sub_eq_zero.mp h⟩) (fun h => hp' ⟨u, sub_eq_zero.mp h⟩)
  have hA : degree (dirCurve γ hγ p hp - dirCurve γ hγ p' hp')
      ((continuous_dirCurve γ hγ p hp).sub (continuous_dirCurve γ hγ p' hp'))
      = degree (ratioLoop γ p p') (continuous_ratioLoop γ hγ hp hp') :=
    degree_congr_fun hfun _ _
  have hB : degree (dirCurve γ hγ p hp - dirCurve γ hγ p' hp')
      ((continuous_dirCurve γ hγ p hp).sub (continuous_dirCurve γ hγ p' hp'))
      = degree (dirCurve γ hγ p hp) (continuous_dirCurve γ hγ p hp)
        - degree (dirCurve γ hγ p' hp') (continuous_dirCurve γ hγ p' hp') := by
    have hadd := degree_add (dirCurve γ hγ p' hp')
      (dirCurve γ hγ p hp - dirCurve γ hγ p' hp')
      (continuous_dirCurve γ hγ p' hp')
      ((continuous_dirCurve γ hγ p hp).sub (continuous_dirCurve γ hγ p' hp'))
    have hsum : dirCurve γ hγ p' hp' + (dirCurve γ hγ p hp - dirCurve γ hγ p' hp')
        = dirCurve γ hγ p hp := by
      funext u; simp [Pi.sub_apply]
    have hcon := degree_congr_fun hsum
      ((continuous_dirCurve γ hγ p' hp').add
        ((continuous_dirCurve γ hγ p hp).sub (continuous_dirCurve γ hγ p' hp')))
      (continuous_dirCurve γ hγ p hp)
    rw [hcon] at hadd
    omega
  simp only [winding]
  rw [← hB, hA]

/-- **The degree is invariant under rotating the parameter of the circle.** -/
theorem degree_comp_add_right (f : UnitAddCircle → UnitAddCircle) (hf : Continuous f)
    (c : UnitAddCircle) :
    degree (fun u : UnitAddCircle => f (u + c))
        (hf.comp (continuous_id.add continuous_const)) = degree f hf := by
  obtain ⟨c', hc'⟩ : ∃ c' : ℝ, (c' : UnitAddCircle) = c := by
    refine ⟨(AddCircle.equivIco (1 : ℝ) 0 c : ℝ), ?_⟩
    exact AddCircle.coe_equivIco (p := (1 : ℝ)) (a := 0) (y := c)
  let G : ℝ → ℝ := fun t => liftOf f hf (t + c')
  have hGc : Continuous G := (liftOf_continuous f hf).comp (continuous_id.add continuous_const)
  have hlift : ∀ t : ℝ,
      ((G t : ℝ) : UnitAddCircle) = (fun u : UnitAddCircle => f (u + c)) (t : UnitAddCircle) := by
    intro t
    show ((liftOf f hf (t + c') : ℝ) : UnitAddCircle) = f ((t : UnitAddCircle) + c)
    rw [liftOf_lifts, AddCircle.coe_add, hc']
  have hmono : ∀ t : ℝ, G (t + 1) = G t + ((degree f hf : ℤ) : ℝ) := by
    intro t
    show liftOf f hf (t + 1 + c') = liftOf f hf (t + c') + ((degree f hf : ℤ) : ℝ)
    have h := liftOf_add_one f hf (t + c')
    rwa [show t + c' + 1 = t + 1 + c' by ring] at h
  exact (degree_eq_of_lift (hf.comp (continuous_id.add continuous_const)) hGc hlift
    (n := degree f hf) hmono).symm

end

end Work.Drive
