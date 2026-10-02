/-
# Continuity in the parameter of the dilatation of the MNS twist `ℓ_t`

`Work.FQC.ell t` is the piecewise-affine shear `(x, y) ↦ (x, y + t · saw x)` of the Écalle
cylinder.  Off the corner lines `Re w ∈ 1/4 + (1/2)ℤ` it is *locally real-affine*, with the
slope `s = ±2` of the triangle wave at `Re w` fixed independently of `t`:

`ℓ_t =ᶠ[𝓝 w] v ↦ (1 + i·t·s/2)·v + (i·t·s/2)·v̄ + c_t`.

Consequently its complex dilatation is the explicit rational function of `t`

`Work.MRMT.beltramiOf (ℓ_t) w = (i·t·s/2) / (1 + i·t·s/2)`,

whose denominator has real part `1` and never vanishes; this is continuous in `t`.  That is the
statement proved here: for fixed `w` off the corner lines, `t ↦ beltramiOf (ell t) w` is
continuous.  (The companion estimate `‖beltramiOf (ell t) w‖ ≤ |t|/√(1+t²)` is
`Work.FQC.ell_beltrami_of_good`.)

The key point for the applications is that the local affine model has the *same* slope `s` for all
`t`, so the parameter enters only linearly.
-/
import Mathlib
import Submission.Work.FQC.Defs
import Submission.Work.FQC.ell_beltrami

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Topology

noncomputable section

namespace Work.FQCInputs

/-- Off the corner lines, `ℓ_t` is locally real-affine with slope `s` at `Re w`, so its
dilatation at `w` is the explicit rational expression in `t` (with `s` fixed). -/
lemma beltramiOf_ell_eq_of_eventually_affine (t : ℝ) (w : ℂ) {s : ℝ}
    (hs : ∀ᶠ y in 𝓝 w.re, Work.FQC.saw y = Work.FQC.saw w.re + s * (y - w.re)) :
    Work.MRMT.beltramiOf (Work.FQC.ell t) w =
      Complex.I * ((t * s / 2 : ℝ) : ℂ) / (1 + Complex.I * ((t * s / 2 : ℝ) : ℂ)) := by
  set a : ℂ := 1 + Complex.I * ((t * s / 2 : ℝ) : ℂ) with ha
  set b : ℂ := Complex.I * ((t * s / 2 : ℝ) : ℂ) with hb
  set c : ℂ := Complex.I * (t : ℂ) * ((Work.FQC.saw w.re : ℂ) - (s : ℂ) * (w.re : ℂ)) with hc
  have hcast : ∀ z : ℂ, ((z.re : ℝ) : ℂ) = (z + star z) / 2 := by
    intro z
    rw [show z + star z = ((2 * z.re : ℝ) : ℂ) from Complex.add_conj z]
    push_cast; ring
  have hev : Work.FQC.ell t =ᶠ[𝓝 w] fun v => a * v + b * star v + c := by
    have hs' : Work.FQC.saw =ᶠ[𝓝 w.re]
        (fun y : ℝ => Work.FQC.saw w.re + s * (y - w.re)) := hs
    have hcomp : (fun v : ℂ => Work.FQC.saw v.re) =ᶠ[𝓝 w]
        fun v => Work.FQC.saw w.re + s * (v.re - w.re) := by
      simpa [Function.comp_def] using hs'.comp_tendsto Complex.continuous_re.continuousAt
    filter_upwards [hcomp] with v hv
    rw [Work.FQC.ell_apply, hv]
    simp only [ha, hb, hc]
    push_cast
    rw [hcast v, hcast w]
    ring
  rw [Work.FQC.beltramiOf_congr hev, Work.MRMT.beltramiOf_affine_star, ha, hb]

/-- For fixed `w` off the corner lines of the triangle wave, the complex dilatation of the
MNS twist `ℓ_t` at `w` is continuous in the parameter `t`. -/
theorem continuous_beltramiOf_ell_of_good (w : ℂ)
    (h0 : Int.fract (w.re + 1 / 4) ≠ 0) (h2 : Int.fract (w.re + 1 / 4) ≠ 1 / 2) :
    Continuous fun t : ℝ => Work.MRMT.beltramiOf (Work.FQC.ell t) w := by
  obtain ⟨s, hsabs, hs⟩ := Work.FQC.saw_eventually_affine h0 h2
  have hpt : ∀ t : ℝ, Work.MRMT.beltramiOf (Work.FQC.ell t) w =
      Complex.I * ((t * s / 2 : ℝ) : ℂ) / (1 + Complex.I * ((t * s / 2 : ℝ) : ℂ)) :=
    fun t => beltramiOf_ell_eq_of_eventually_affine t w hs
  have hnum : Continuous fun t : ℝ => Complex.I * ((t * s / 2 : ℝ) : ℂ) :=
    continuous_const.mul
      (Complex.continuous_ofReal.comp ((continuous_id.mul continuous_const).div_const 2))
  have hden : Continuous fun t : ℝ => (1 : ℂ) + Complex.I * ((t * s / 2 : ℝ) : ℂ) :=
    continuous_const.add hnum
  have hne : ∀ t : ℝ, (1 : ℂ) + Complex.I * ((t * s / 2 : ℝ) : ℂ) ≠ 0 := by
    intro t h
    have hre : ((1 : ℂ) + Complex.I * ((t * s / 2 : ℝ) : ℂ)).re = 1 := by simp
    rw [h] at hre
    norm_num at hre
  exact (hnum.div hden hne).congr (fun t => (hpt t).symm)

end Work.FQCInputs

end
