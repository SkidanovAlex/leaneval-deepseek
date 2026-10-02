/-
# `Work.FQC.ell_beltrami_of_differentiableAt`

Pointwise form of `Work.FQC.ell_beltrami`: at every point `w` at which the MNS cylinder twist
`ell t` is real-differentiable, its complex dilatation is bounded by `|t| / √(1 + t²)`.

The twist `ell t (x + iy) = x + i (y + t · saw x)` is locally real-affine off the *corner lines*
`Re w ∈ 1/4 + (1/2)ℤ` of the triangle wave `saw`, where the desired bound is exactly the
computation of `Work.FQC.ell_beltrami_of_good`.  On a corner line, however, `saw` has a genuine
kink — locally it is `saw x + 2|u|` (resp. `saw x - 2|u|`) — so for `t ≠ 0` the map `ell t` fails
to be real-differentiable there, and the hypothesis `DifferentiableAt ℝ (ell t) w` rules the
corners out.  For `t = 0` the twist degenerates to the identity, whose dilatation vanishes.

Two ingredients are proved here: the local shape of `saw` at each family of corners
(`saw_eventuallyEq_zero`, `saw_eventuallyEq_half`), and the resulting failure of
differentiability of `ell t` at those corners
(`not_differentiableAt_ell_of_fract_zero`, `not_differentiableAt_ell_of_fract_half`).
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


open Filter MeasureTheory
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.FQC

/-! ## 1. The local shape of `saw` at its corner lines

`saw x = 1/2 - 2·|frac (x + 1/4) - 1/2|`.  On the corner lines `frac (x + 1/4) = 0` and
`frac (x + 1/4) = 1/2` it has a kink: to first order it is `saw x ± 2|u|`. -/

/-- At a corner `frac (x + 1/4) = 0`, `saw` behaves like `saw x + 2|u|`. -/
lemma saw_eventuallyEq_zero {x : ℝ} (h : Int.fract (x + 1/4) = 0) :
    (fun u : ℝ => saw (x + u)) =ᶠ[𝓝 (0:ℝ)] (fun u => saw x + 2 * |u|) := by
  have hxfl : x + 1/4 = (⌊x + 1/4⌋ : ℝ) := by
    have := Int.fract_add_floor (x + 1/4)
    rw [h, zero_add] at this
    exact this.symm
  have hxsaw : saw x = -1/2 := by
    rw [saw_apply, h]; norm_num
  filter_upwards [isOpen_Ioo.mem_nhds (by constructor <;> norm_num : (0:ℝ) ∈ Set.Ioo (-1/4) (1/4))]
    with u hu
  obtain ⟨hu1, hu2⟩ := hu
  rw [hxsaw]
  by_cases hu0 : 0 ≤ u
  · have hfu : Int.fract (x + u + 1/4) = u := by
      have heq : x + u + 1/4 = u + ((⌊x + 1/4⌋ : ℤ) : ℝ) := by linarith [hxfl]
      rw [heq, Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨hu0, by linarith⟩]
    rw [saw_apply, hfu, abs_of_neg (by linarith : u - 1/2 < 0), abs_of_nonneg hu0]
    ring
  · have hu0' : u < 0 := not_le.mp hu0
    have hfu : Int.fract (x + u + 1/4) = 1 + u := by
      have heq : x + u + 1/4 = (1 + u) + (((⌊x + 1/4⌋ - 1 : ℤ)) : ℝ) := by
        have h1 : (((⌊x + 1/4⌋ - 1 : ℤ)) : ℝ) = (⌊x + 1/4⌋ : ℝ) - 1 := by push_cast; ring
        rw [h1]; linarith [hxfl]
      rw [heq, Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
    rw [saw_apply, hfu, abs_of_pos (by linarith : (0:ℝ) < 1 + u - 1/2), abs_of_neg hu0']
    ring

/-- At a corner `frac (x + 1/4) = 1/2`, `saw` behaves like `saw x - 2|u|`. -/
lemma saw_eventuallyEq_half {x : ℝ} (h : Int.fract (x + 1/4) = 1/2) :
    (fun u : ℝ => saw (x + u)) =ᶠ[𝓝 (0:ℝ)] (fun u => saw x - 2 * |u|) := by
  have hxfl : x + 1/4 = (⌊x + 1/4⌋ : ℝ) + 1/2 := by
    have := Int.fract_add_floor (x + 1/4)
    rw [h] at this
    linarith
  have hxsaw : saw x = 1/2 := by
    rw [saw_apply, h]; norm_num
  filter_upwards [isOpen_Ioo.mem_nhds (by constructor <;> norm_num : (0:ℝ) ∈ Set.Ioo (-1/4) (1/4))]
    with u hu
  obtain ⟨hu1, hu2⟩ := hu
  rw [hxsaw]
  have hfu : Int.fract (x + u + 1/4) = 1/2 + u := by
    have heq : x + u + 1/4 = (1/2 + u) + ((⌊x + 1/4⌋ : ℤ) : ℝ) := by linarith [hxfl]
    rw [heq, Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
  rw [saw_apply, hfu, show (1/2 + u - 1/2 : ℝ) = u by ring]

/-! ## 2. `ell t` is not real-differentiable on the corner lines (`t ≠ 0`)

Restricted to the real direction through `w`, the map `ell t` has imaginary part
`u ↦ w.im + t·saw (w.re + u)`, which near a corner of `saw` is a nonzero multiple of `u ↦ |u|` and
hence not differentiable. -/

/-- For `t ≠ 0`, `ell t` is not real-differentiable at a point with `frac (Re w + 1/4) = 0`. -/
lemma not_differentiableAt_ell_of_fract_zero {t : ℝ} (ht : t ≠ 0) {w : ℂ}
    (h : Int.fract (w.re + 1/4) = 0) : ¬ DifferentiableAt ℝ (ell t) w := by
  intro hd
  have hcurve : DifferentiableAt ℝ (fun u : ℝ => w + (u:ℂ)) 0 := by fun_prop
  have hd' : DifferentiableAt ℝ (ell t) ((fun u : ℝ => w + (u:ℂ)) 0) := by simpa using hd
  have hF : DifferentiableAt ℝ (fun u : ℝ => ell t (w + (u:ℂ))) 0 :=
    DifferentiableAt.comp (f := fun u : ℝ => w + (u:ℂ)) 0 hd' hcurve
  have him : DifferentiableAt ℝ (fun u : ℝ => (ell t (w + (u:ℂ))).im) 0 :=
    DifferentiableAt.comp (f := fun u : ℝ => ell t (w + (u:ℂ))) 0
      Complex.imCLM.differentiableAt hF
  have h1 : (fun u : ℝ => (ell t (w + (u:ℂ))).im)
      = fun u => w.im + t * saw (w.re + u) := by
    funext u
    simp [ell]
  rw [h1] at him
  have h3 : DifferentiableAt ℝ (fun u : ℝ => t * saw (w.re + u)) 0 := by
    have := him.sub_const w.im; simpa using this
  have h4 : DifferentiableAt ℝ (fun u : ℝ => saw (w.re + u)) 0 := by
    have := h3.div_const t; simpa [ht] using this
  have h5 : DifferentiableAt ℝ (fun u : ℝ => saw w.re + 2 * |u|) 0 :=
    h4.congr_of_eventuallyEq (saw_eventuallyEq_zero h).symm
  have h6 : DifferentiableAt ℝ (fun u : ℝ => 2 * |u|) 0 := by
    have := h5.sub_const (saw w.re); simpa using this
  have h7 : DifferentiableAt ℝ (fun u : ℝ => |u|) 0 := by
    have := h6.div_const 2; simpa using this
  exact not_differentiableAt_abs_zero (by simpa using h7)

/-- For `t ≠ 0`, `ell t` is not real-differentiable at a point with `frac (Re w + 1/4) = 1/2`. -/
lemma not_differentiableAt_ell_of_fract_half {t : ℝ} (ht : t ≠ 0) {w : ℂ}
    (h : Int.fract (w.re + 1/4) = 1/2) : ¬ DifferentiableAt ℝ (ell t) w := by
  intro hd
  have hcurve : DifferentiableAt ℝ (fun u : ℝ => w + (u:ℂ)) 0 := by fun_prop
  have hd' : DifferentiableAt ℝ (ell t) ((fun u : ℝ => w + (u:ℂ)) 0) := by simpa using hd
  have hF : DifferentiableAt ℝ (fun u : ℝ => ell t (w + (u:ℂ))) 0 :=
    DifferentiableAt.comp (f := fun u : ℝ => w + (u:ℂ)) 0 hd' hcurve
  have him : DifferentiableAt ℝ (fun u : ℝ => (ell t (w + (u:ℂ))).im) 0 :=
    DifferentiableAt.comp (f := fun u : ℝ => ell t (w + (u:ℂ))) 0
      Complex.imCLM.differentiableAt hF
  have h1 : (fun u : ℝ => (ell t (w + (u:ℂ))).im)
      = fun u => w.im + t * saw (w.re + u) := by
    funext u
    simp [ell]
  rw [h1] at him
  have h3 : DifferentiableAt ℝ (fun u : ℝ => t * saw (w.re + u)) 0 := by
    have := him.sub_const w.im; simpa using this
  have h4 : DifferentiableAt ℝ (fun u : ℝ => saw (w.re + u)) 0 := by
    have := h3.div_const t; simpa [ht] using this
  have h5 : DifferentiableAt ℝ (fun u : ℝ => saw w.re - 2 * |u|) 0 :=
    h4.congr_of_eventuallyEq (saw_eventuallyEq_half h).symm
  have h6 : DifferentiableAt ℝ (fun u : ℝ => -2 * |u|) 0 := by
    have := h5.sub_const (saw w.re); simpa using this
  have h7 : DifferentiableAt ℝ (fun u : ℝ => |u|) 0 := by
    have := h6.div_const (-2); simpa using this
  exact not_differentiableAt_abs_zero (by simpa using h7)

/-! ## 3. The pointwise bound -/

theorem ell_beltrami_of_differentiableAt {t : ℝ} {w : ℂ} (hd : DifferentiableAt ℝ (Work.FQC.ell t) w) : ‖Work.MRMT.beltramiOf (Work.FQC.ell t) w‖ ≤ |t| / Real.sqrt (1 + t ^ 2) := by
  rcases eq_or_ne t 0 with rfl | ht
  · have hell : Work.FQC.ell 0 = id := by funext v; simp [ell]
    rw [hell]
    simp
  · exact ell_beltrami_of_good t
      (fun h0 => not_differentiableAt_ell_of_fract_zero ht h0 hd)
      (fun h2 => not_differentiableAt_ell_of_fract_half ht h2 hd)

end Work.FQC

end
