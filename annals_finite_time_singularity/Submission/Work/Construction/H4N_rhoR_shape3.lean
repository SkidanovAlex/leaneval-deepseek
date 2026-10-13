import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.Construction.GammaTermAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The shape of the third `D_z`-iterate of `ρ(z) = z²/(1+z)⁴`

`Work.Construction.rhoR z = z²/(1+z)⁴` is the radial factor of the `Γ`-term of the
`N₀` nonlinearity (`Work.Construction.GammaTermAux`).  Its `D_z`-iterates are the
`Work.Spaces.Zop`-iterates (`Zop u = fun z ↦ z * u'(z)`), and the third one is

`Zop^[3] rhoR = fun z ↦ z²·(8 - 52z + 52z² - 8z³)/(1+z)⁷`  on `z ≠ -1`.

The proof is a three-step computation: each iterate has the shape
`z²·Q(z)/(1+z)^m` with `Q` a cubic, and one application of `Zop` replaces
`(Q, m)` by `(Q', m+1)`.  The general step is isolated as `Zop_div_pow`:

`Zop (w ↦ u w / (1+w)^m) z = (z·u'·(1+z) - m·z·u z)/(1+z)^(m+1)`

for `z ≠ -1` and `HasDerivAt u u' z`; the three instances are `step1`, `step2`,
`step3`.  The only place where the restriction `z ≠ -1` enters the iteration is
the transfer of the pointwise value to the next derivative (`Zop_congr_off`):
two functions that agree off `-1` have the same derivative at `z ≠ -1`.
-/

open scoped Real Topology
open Filter

namespace Work.Construction

/-- One step of `Zop` on functions of the shape `w ↦ u w / (1+w)^m`. -/
lemma Zop_div_pow (m : ℕ) (hm : 1 ≤ m) (u : ℝ → ℝ) (u' z : ℝ)
    (hu : HasDerivAt u u' z) (hz : z ≠ -1) :
    Work.Spaces.Zop (fun w => u w / (1+w)^m) z
      = (z * u' * (1+z) - (m:ℝ) * z * u z) / (1+z)^(m+1) := by
  have h1z : (1:ℝ) + z ≠ 0 := by intro h; exact hz (by linarith)
  unfold Work.Spaces.Zop
  have hd : HasDerivAt (fun w : ℝ => u w / (1+w)^m)
      ((u' * (1+z)^m - u z * ((m:ℝ) * (1+z)^(m-1))) / ((1+z)^m)^2) z := by
    apply HasDerivAt.div
    · exact hu
    · have h0 : HasDerivAt (fun w : ℝ => 1 + w) (1:ℝ) z := (hasDerivAt_id z).const_add 1
      have h := h0.pow m
      convert h using 1
      ring
    · exact pow_ne_zero m h1z
  rw [hd.deriv]
  have hB : (1+z)^m = (1+z)^(m-1) * (1+z) := by
    conv_lhs => rw [← Nat.sub_add_cancel hm]
    rw [pow_succ']; ring
  have hAB : (1+z)^(m+1) = (1+z)^(m-1) * (1+z) * (1+z) := by
    rw [pow_succ', hB]; ring
  field_simp
  rw [hAB, hB]
  ring

/-- `Zop` only depends on the values of the function away from `-1`, at points `≠ -1`. -/
lemma Zop_congr_off (u f g : ℝ → ℝ) (hu : ∀ w, w ≠ -1 → u w = f w)
    (hf : ∀ w, w ≠ -1 → Work.Spaces.Zop f w = g w) :
    ∀ z, z ≠ -1 → Work.Spaces.Zop u z = g z := by
  intro z hz
  have hev : u =ᶠ[𝓝 z] f := by
    filter_upwards [isOpen_ne.mem_nhds hz] with w hw
    exact hu w hw
  have h1 : deriv u z = deriv f z := hev.deriv_eq
  unfold Work.Spaces.Zop
  rw [h1]
  exact hf z hz

/-- `Zop rhoR = fun z ↦ z²(2 - 2z)/(1+z)⁵` off `-1`. -/
lemma Zop_rhoR_step1 : ∀ z : ℝ, z ≠ -1 →
    Work.Spaces.Zop (fun w : ℝ => w^2 / (1+w)^4) z = z^2 * (2 - 2*z)/(1+z)^5 := by
  intro z hz
  have hderiv : HasDerivAt (fun w : ℝ => w^2) (2*z) z := by
    have h' : HasDerivAt (fun w : ℝ => w^2) (↑2 * z^(2-1)) z := hasDerivAt_pow 2 z
    have he : (↑2 * z^(2-1) : ℝ) = 2*z := by ring
    rw [he] at h'
    exact h'
  have h := Zop_div_pow 4 (by norm_num) (fun w : ℝ => w^2) (2*z) z hderiv hz
  refine h.trans ?_
  field_simp
  ring

/-- The second iterate: `Zop (z²(2-2z)/(1+z)⁵) = z²(4 - 12z + 4z²)/(1+z)⁶` off `-1`. -/
lemma Zop_rhoR_step2 : ∀ z : ℝ, z ≠ -1 →
    Work.Spaces.Zop (fun w : ℝ => w^2 * (2 - 2*w) / (1+w)^5) z
      = z^2 * (4 - 12*z + 4*z^2)/(1+z)^6 := by
  intro z hz
  have hderiv : HasDerivAt (fun w : ℝ => w^2 * (2 - 2*w)) (4*z - 6*z^2) z := by
    have h2 : HasDerivAt (fun w : ℝ => 2 - 2*w) (-2) z := by
      have h' : HasDerivAt (fun w : ℝ => 2 - 2*w) (-(2*1)) z :=
        ((hasDerivAt_id' z).const_mul (2:ℝ)).const_sub (2:ℝ)
      have he : (-(2*1) : ℝ) = -2 := by ring
      rw [he] at h'
      exact h'
    have h' : HasDerivAt (fun w : ℝ => w^2 * (2 - 2*w))
        ((↑2 * z^(2-1)) * (2 - 2*z) + z^2 * (-2)) z := (hasDerivAt_pow 2 z).mul h2
    have he : ((↑2 * z^(2-1)) * (2 - 2*z) + z^2 * (-2) : ℝ) = 4*z - 6*z^2 := by ring
    rw [he] at h'
    exact h'
  have h := Zop_div_pow 5 (by norm_num) (fun w : ℝ => w^2 * (2 - 2*w)) (4*z - 6*z^2) z hderiv hz
  refine h.trans ?_
  field_simp
  ring

/-- The third iterate, in the shape requested by `H4N_rhoR_shape3`. -/
lemma Zop_rhoR_step3 : ∀ z : ℝ, z ≠ -1 →
    Work.Spaces.Zop (fun w : ℝ => w^2 * (4 - 12*w + 4*w^2) / (1+w)^6) z
      = z^2 * (8 - 52*z + 52*z^2 - 8*z^3)/(1+z)^7 := by
  intro z hz
  have hderiv : HasDerivAt (fun w : ℝ => w^2 * (4 - 12*w + 4*w^2)) (8*z - 36*z^2 + 16*z^3) z := by
    have h2 : HasDerivAt (fun w : ℝ => 4 - 12*w + 4*w^2) (-12 + 8*z) z := by
      have h' : HasDerivAt (fun w : ℝ => 4 - 12*w + 4*w^2)
          (-(12*1) + 4*(↑2 * z^(2-1))) z :=
        (((hasDerivAt_id' z).const_mul (12:ℝ)).const_sub (4:ℝ)).add
          ((hasDerivAt_pow 2 z).const_mul (4:ℝ))
      have he : (-(12*1) + 4*(↑2 * z^(2-1)) : ℝ) = -12 + 8*z := by ring
      rw [he] at h'
      exact h'
    have h' : HasDerivAt (fun w : ℝ => w^2 * (4 - 12*w + 4*w^2))
        ((↑2 * z^(2-1)) * (4 - 12*z + 4*z^2) + z^2 * (-12 + 8*z)) z :=
      (hasDerivAt_pow 2 z).mul h2
    have he : ((↑2 * z^(2-1)) * (4 - 12*z + 4*z^2) + z^2 * (-12 + 8*z) : ℝ)
        = 8*z - 36*z^2 + 16*z^3 := by ring
    rw [he] at h'
    exact h'
  have h := Zop_div_pow 6 (by norm_num) (fun w : ℝ => w^2 * (4 - 12*w + 4*w^2))
    (8*z - 36*z^2 + 16*z^3) z hderiv hz
  refine h.trans ?_
  field_simp
  ring

theorem H4N_rhoR_shape3 :
    ∀ z : ℝ, z ≠ -1 → (Work.Spaces.Zop^[3] Work.Construction.rhoR) z
        = z^2 * (8 - 52*z + 52*z^2 - 8*z^3) / (1 + z)^7 := by
  intro z hz
  have hAC := Zop_congr_off (Work.Spaces.Zop (fun w : ℝ => w^2 / (1+w)^4))
    (fun w : ℝ => w^2 * (2 - 2*w) / (1+w)^5)
    (fun w : ℝ => w^2 * (4 - 12*w + 4*w^2) / (1+w)^6) Zop_rhoR_step1 Zop_rhoR_step2
  have hAD := Zop_congr_off (Work.Spaces.Zop (Work.Spaces.Zop (fun w : ℝ => w^2 / (1+w)^4)))
    (fun w : ℝ => w^2 * (4 - 12*w + 4*w^2) / (1+w)^6)
    (fun w : ℝ => w^2 * (8 - 52*w + 52*w^2 - 8*w^3) / (1+w)^7) hAC Zop_rhoR_step3
  have e : (Work.Spaces.Zop^[3] Work.Construction.rhoR) z
      = Work.Spaces.Zop (Work.Spaces.Zop (Work.Spaces.Zop
          (fun w : ℝ => w^2 / (1+w)^4))) z := by
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rfl
  rw [e]
  exact hAD z hz

end Work.Construction
