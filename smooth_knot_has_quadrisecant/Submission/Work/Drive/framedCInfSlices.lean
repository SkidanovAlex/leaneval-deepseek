import Mathlib
import Submission.Work.Drive.framedPolarDefs
import Submission.Work.Drive.isSmoothKnot_framedCurve
import Submission.Work.Drive.cInfKnot

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

/-!
# The framed polar slices are `C^∞` knots when the polar data is `C^∞`

`Work.Drive.framedStarShapedPolarGraph` (and its assembly partner
`Work.Drive.framedPolarGraph_unknotted`) consume *analytic* polar data
(`ContDiff ℝ ⊤ lam`, `ContDiff ℝ ⊤ psi`).  The smoothed sweep produces only `C^∞` data
(`ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)`, via convolution with a bump), so the framed machinery
has to be available at the `C^∞` order as well.  `ContDiff ℝ ⊤` is *analyticity* in this
Mathlib, so this is a genuine (if mechanical) strengthening of the hypothesis.

Everything in the proofs below is the corresponding analytic proof with the order replaced;
the two places where analyticity was used are exactly the differentiability of `lam`, `psi`
(supplied as well by `C^∞`) and the joint regularity of the framed slice (the proof of the
analytic version never used more than the order).

* `Work.Drive.framedSlice_contDiff_cInf` — joint `C^∞` of the framed slice in `(t, s)`;
* `Work.Drive.framedCurve_contDiff_time_cInf` — the `t`-slices are `C^∞`;
* `Work.Drive.framedCurve_velocity_ne_zero_cInf` — the `t`-slices are regular;
* `Work.Drive.isCInfKnot_framedCurve_cInf` — hence they are `C^∞` **knots**
  (`Work.Drive.IsCInfKnot`) for `s ∈ [0,1]`.

Together with `Work.Drive.framedCurve_injOn` (which uses no differentiability at all) and
`Work.Drive.framedCurve_periodic`, this is exactly what the smoothing kit
`Work.Drive.isUnknotted_of_cInf_knotPath` needs in order to consume a `C^∞` lens.
-/

namespace Work.Drive

/-- The `C^∞` order in `WithTop ℕ∞` (whereas `⊤` is analyticity). -/
abbrev cInfT : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

lemma cInfT_ne_zero : cInfT ≠ 0 := by simp [cInfT]

lemma one_le_cInfT : (1 : WithTop ℕ∞) ≤ cInfT := WithTop.coe_le_coe.mpr le_top

/-- The framed star-shaped slice depends `C^∞`-ly on both parameters (the `C^∞` analogue of
`Work.Drive.contDiff_framedSliceFamily`; the proof is the same after replacing the order). -/
theorem framedSlice_contDiff_cInf {lam psi : ℝ → ℝ} (c : LeanEval.KnotTheory.Quadrisecant.Space)
    {g : ℝ → LeanEval.KnotTheory.Quadrisecant.Space × LeanEval.KnotTheory.Quadrisecant.Space}
    (hlam : ContDiff ℝ cInfT lam) (hpsi : ContDiff ℝ cInfT psi) (hg : ContDiff ℝ cInfT g) :
    ContDiff ℝ cInfT (fun p : ℝ × ℝ => Work.Drive.framedSlice lam psi c g p.2 p.1) := by
  simp only [framedSlice, starRad, starAngle]
  rw [contDiff_piLp (p := 2)]
  intro i
  fin_cases i <;> simp <;> fun_prop

/-- The `t`-slices of the framed polar curve are `C^∞` for `C^∞` polar data. -/
theorem framedCurve_contDiff_time_cInf {lam psi : ℝ → ℝ}
    (c u v : LeanEval.KnotTheory.Quadrisecant.Space) (s : ℝ)
    (hlam : ContDiff ℝ cInfT lam) (hpsi : ContDiff ℝ cInfT psi) :
    ContDiff ℝ cInfT (fun t : ℝ => framedCurve lam psi c u v s t) := by
  have h := framedSlice_contDiff_cInf (lam := lam) (psi := psi) c
    (g := fun _ : ℝ => (u, v)) hlam hpsi contDiff_const
  have h2 : ContDiff ℝ cInfT (fun p : ℝ × ℝ => framedCurve lam psi c u v p.2 p.1) := by
    simpa [framedSlice_eq_framedCurve] using h
  exact h2.comp (contDiff_id.prodMk contDiff_const)

/-- **The framed slices are regular for `C^∞` polar data.**  The velocity is
`ρ • (θ' • tangent) + ρ' • direction`, and pairing it with the unit tangent `frameTan` at `t`
gives the strictly positive number `ρ t * θ' t`.  (`C^∞` analogue of
`Work.Drive.framedCurve_velocity_ne_zero`.) -/
theorem framedCurve_velocity_ne_zero_cInf {lam psi : ℝ → ℝ} {c u v : Space}
    (h1 : ‖u‖ = 1) (h2 : ‖v‖ = 1) (hperp : inner ℝ u v = 0)
    (hlam : ContDiff ℝ cInfT lam) (hpsi : ContDiff ℝ cInfT psi)
    (hlampos : ∀ t : ℝ, 0 < lam t) (hpsideriv : ∀ t : ℝ, 0 < deriv psi t)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (t : ℝ) :
    velocity (fun x : ℝ => framedCurve lam psi c u v s x) t ≠ 0 := by
  set θt : ℝ := starAngle psi s t with hθt
  set w : Space := frameTan u v θt with hw
  have hg : DifferentiableAt ℝ (fun x : ℝ => framedCurve lam psi c u v s x) t :=
    ((framedCurve_contDiff_time_cInf c u v s hlam hpsi).differentiable cInfT_ne_zero).differentiableAt
  have hin : ∀ x : ℝ, inner ℝ w (framedCurve lam psi c u v s x)
      = inner ℝ w ((1 - s) • c) + starRad lam s x * Real.sin (starAngle psi s x - θt) := by
    intro x
    rw [framedCurve_eq, hw]
    simp only [inner_add_right, inner_smul_right,
      frameTan_inner_frameDir (u := u) (v := v) (θt := θt) (θ := starAngle psi s x) h1 h2 hperp]
  have hderiv : deriv (fun x : ℝ => inner ℝ w (framedCurve lam psi c u v s x)) t
      = starRad lam s t * ((1 - s) * deriv psi t + s) := by
    have hfun : (fun x : ℝ => inner ℝ w (framedCurve lam psi c u v s x))
        = fun x => inner ℝ w ((1 - s) • c)
            + starRad lam s x * Real.sin (starAngle psi s x - θt) := funext hin
    have hρ : HasDerivAt (starRad lam s) ((1 - s) * deriv lam t) t :=
      (((hlam.differentiable cInfT_ne_zero).differentiableAt.hasDerivAt).const_mul (1 - s)).add_const s
    have hθ : HasDerivAt (starAngle psi s) ((1 - s) * deriv psi t + s) t := by
      change HasDerivAt (fun y : ℝ => (1 - s) * psi y + s * y) ((1 - s) * deriv psi t + s) t
      have h1' : HasDerivAt (fun y : ℝ => (1 - s) * psi y) ((1 - s) * deriv psi t) t :=
        ((hpsi.differentiable cInfT_ne_zero).differentiableAt.hasDerivAt).const_mul (1 - s)
      have h2' : HasDerivAt (fun y : ℝ => s * y) s t := by
        simpa using (hasDerivAt_id t).const_mul s
      exact h1'.add h2'
    have hsin : HasDerivAt (fun y : ℝ => Real.sin (starAngle psi s y - θt))
        (Real.cos (starAngle psi s t - θt) * ((1 - s) * deriv psi t + s)) t :=
      (hθ.sub_const θt).sin
    have hd : HasDerivAt (fun x : ℝ => inner ℝ w ((1 - s) • c)
          + starRad lam s x * Real.sin (starAngle psi s x - θt))
        (starRad lam s t * ((1 - s) * deriv psi t + s)) t := by
      have hmul := hρ.mul hsin
      simpa [Pi.mul_apply, ← hθt] using hmul.const_add (inner ℝ w ((1 - s) • c))
    rw [hfun]
    exact hd.deriv
  have hchain : deriv (fun x : ℝ => inner ℝ w (framedCurve lam psi c u v s x)) t
      = inner ℝ w (deriv (fun x : ℝ => framedCurve lam psi c u v s x) t) := by
    have h := deriv_inner_apply ℝ (f := fun _ : ℝ => w)
      (g := fun x : ℝ => framedCurve lam psi c u v s x) (x := t) (differentiableAt_const w) hg
    simpa only [deriv_const, inner_zero_left, add_zero] using h
  have hρpos : 0 < starRad lam s t := starRad_pos hlampos hs0 hs1 t
  have hθpos : 0 < (1 - s) * deriv psi t + s := by
    rcases lt_or_eq_of_le hs1 with hs | hs
    · have hlt : 0 < 1 - s := sub_pos.mpr hs
      have := mul_pos hlt (hpsideriv t)
      linarith
    · rw [hs]; norm_num
  intro hzero
  have hzero' : deriv (fun x : ℝ => framedCurve lam psi c u v s x) t = 0 := hzero
  have hval : deriv (fun x : ℝ => inner ℝ w (framedCurve lam psi c u v s x)) t = 0 := by
    rw [hchain, hzero']
    simp
  rw [hderiv] at hval
  exact absurd hval (ne_of_gt (mul_pos hρpos hθpos))

/-- **The `C^∞` framed slices are `C^∞` knots.**  Assembles the `C^∞` slice regularity, the
periodicity (`Work.Drive.framedCurve_periodic`, which needs no differentiability), the
injectivity (`Work.Drive.framedCurve_injOn`, which needs only `StrictMono psi`) and the
regularity above. -/
theorem isCInfKnot_framedCurve_cInf {lam psi : ℝ → ℝ} {c u v : Space}
    (h1 : ‖u‖ = 1) (h2 : ‖v‖ = 1) (hperp : inner ℝ u v = 0)
    (hlam : ContDiff ℝ cInfT lam) (hpsi : ContDiff ℝ cInfT psi)
    (hlampos : ∀ t : ℝ, 0 < lam t) (hlamper : Function.Periodic lam period)
    (hψ : StrictMono psi) (hpsishift : ∀ t : ℝ, psi (t + period) = psi t + period)
    (hpsideriv : ∀ t : ℝ, 0 < deriv psi t)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    IsCInfKnot (fun t : ℝ => framedCurve lam psi c u v s t) :=
  ⟨framedCurve_contDiff_time_cInf c u v s hlam hpsi,
    framedCurve_periodic c u v s hlamper hpsishift,
    framedCurve_injOn h1 h2 hperp hψ hlampos hpsishift hs0 hs1,
    fun t => framedCurve_velocity_ne_zero_cInf h1 h2 hperp hlam hpsi hlampos hpsideriv hs0 hs1 t⟩

end Work.Drive
