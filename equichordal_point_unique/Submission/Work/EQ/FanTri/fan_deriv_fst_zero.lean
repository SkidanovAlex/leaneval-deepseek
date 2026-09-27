import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.FanDefs
import Submission.Work.EQ.germC_facts
import Submission.Work.EQ.charVal_main
import Submission.Work.EQ.fan_step_deriv
import Submission.Work.EQ.walk_bounds
import Submission.Work.EQ.FanTri.analytic_invBranch
import Submission.Work.EQ.FanSep.axis_walk

/-!
# The abscissa derivative of the stable fan vanishes at the origin

The stable fan `fan a h ε` of a branch word `ε` (Rychlik §5.13) starts at the centre
`A₁ = (-1/2, 0)` on the real axis.  Its **first** (abscissa) coordinate has vanishing derivative
at `u = 0`: the fan curve is tangent at `A₁` to the line `x = -1/2` (only its `y`-coordinate
moves to first order, which is the content of the characteristic-value product formula).

The proof is by induction on the word `ε`, and rests on two ingredients:

* `invBranch_axis_fst_deriv`: at an axis point `(x, 0)` (`x + a/2 ≠ 0`) the first row of the
  Jacobian of the backward branch `invBranch a s` is `(-1, 0)`.  I.e. for paths `F, G`
  differentiable at `0` with `F 0 = x`, `G 0 = 0`, the map `u ↦ (invBranch a s (F u, G u)).1`
  has derivative `-F'`.  (The second column vanishes because the radicand
  `(F u + a/2)^2 + (G u)^2` of the square root has derivative `2(x + a/2)F'` at `0`, the `G`-term
  being multiplied by `G 0 = 0`.)

* the invariance `invBranch a true (germC a h (λ u)) = germC a h u` of the stable germ (`germC_facts`),
  which for `ε = []` gives `d = -λ d` for `d = deriv (fun u => (germC a h u).1) 0`, hence `d = 0`.

Since the recursion `fan a h (s :: ε) u = invBranch a s (fan a h ε (λ u))` scales the parameter by
`λ`, the induction step multiplies the abscissa derivative by `(-λ)`, so it stays `0`.
-/

namespace Work.EQ.FanTri

open Work.EQ Complex Filter
open scoped Topology

noncomputable section

/-- Algebra with the principal square root: for real `y ≠ 0` and any `w : ℂ`,
`(↑y)^2 * ((↑y)^2)^(1/2 - 1) * w = w * ↑|y|`. -/
private lemma ofReal_sq_mul_cpow_half_sub_one {y : ℝ} (hy : y ≠ 0) (w : ℂ) :
    ((y : ℂ) ^ 2 * (((y : ℂ) ^ 2) ^ ((1 : ℂ) / 2 - 1))) * w = w * ((|y| : ℝ) : ℂ) := by
  have hroot : ((y : ℂ) ^ 2) ^ ((1 : ℂ) / 2) = ((|y| : ℝ) : ℂ) := cpow_half_ofReal_sq y
  have hpow : ((y : ℂ) ^ 2) ^ ((1 : ℂ) / 2 - 1) = (((|y| : ℝ) : ℂ))⁻¹ := by
    rw [show ((1 : ℂ) / 2 - 1) = -((1 : ℂ) / 2) by norm_num, Complex.cpow_neg, hroot]
  have hcore : (y : ℂ) ^ 2 * (((|y| : ℝ) : ℂ))⁻¹ = ((|y| : ℝ) : ℂ) := by
    have hreal : y ^ 2 / |y| = |y| := by
      have hy' : |y| ≠ 0 := abs_ne_zero.mpr hy
      field_simp
      rw [sq_abs]
    have hc : (y : ℂ) ^ 2 * (((|y| : ℝ) : ℂ))⁻¹ = ((y ^ 2 / |y| : ℝ) : ℂ) := by
      rw [Complex.ofReal_div, Complex.ofReal_pow, div_eq_mul_inv]
    rw [hc, hreal]
  rw [hpow, hcore]
  ring

/-- **The first coordinate of the backward branch at an axis point has derivative `-F'`.**
If `F, G : ℂ → ℂ` are paths through the axis point `(x, 0)` (with `x + a/2 ≠ 0`, so the radicand
`(x + a/2)^2` of `invBranch` is nonzero) which are differentiable at `0`, then
`u ↦ (invBranch a s (F u, G u)).1` is differentiable at `0` with derivative `-F'`: on the axis the
first row of the Jacobian of `invBranch a s` is `(-1, 0)`, the vertical `G`-direction contributing
nothing because the radicand has derivative `2(x + a/2)F'` and `ρ 0 = |x + a/2|`.  This upgrades
the first component of `Work.EQ.invBranch_axis_deriv` (which only gives differentiability) to the
explicit derivative. -/
lemma invBranch_axis_fst_deriv {a : ℝ} {s : Bool} {F G : ℂ → ℂ} {F' G' : ℂ} {x : ℝ}
    (hF : HasDerivAt F F' 0) (hG : HasDerivAt G G' 0)
    (hF0 : F 0 = (x : ℂ)) (hG0 : G 0 = 0) (hx : x + a / 2 ≠ 0) :
    HasDerivAt (fun u => (invBranch a s (F u, G u)).1) (-F') 0 := by
  have hR : ((|x + a / 2| : ℝ) : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_zero, ne_eq, Complex.ofReal_inj]
    exact abs_ne_zero.mpr hx
  let c : ℂ := ((a / 2 : ℝ) : ℂ)
  let D : ℂ → ℂ := fun u => (F u + c) ^ 2 + G u ^ 2
  let ρ : ℂ → ℂ := fun u => D u ^ ((1 : ℂ) / 2)
  let sg : ℂ := (if s then (1 : ℂ) else -1)
  let D' : ℂ := ↑(2 : ℕ) * (F 0 + c) ^ (2 - 1) * F' + ↑(2 : ℕ) * G 0 ^ (2 - 1) * G'
  have hD0 : D 0 = (((x + a / 2) ^ 2 : ℝ) : ℂ) := by
    change (F 0 + c) ^ 2 + G 0 ^ 2 = (((x + a / 2) ^ 2 : ℝ) : ℂ)
    rw [hF0, hG0]
    rw [show (x : ℂ) + c = ((x + a / 2 : ℝ) : ℂ) by
          change (x : ℂ) + ((a / 2 : ℝ) : ℂ) = ((x + a / 2 : ℝ) : ℂ); push_cast; ring]
    rw [show (0 : ℂ) ^ 2 = 0 by norm_num, add_zero, ← Complex.ofReal_pow]
  have hslit : D 0 ∈ Complex.slitPlane := by
    rw [hD0, Complex.mem_slitPlane_iff]
    exact Or.inl (by rw [Complex.ofReal_re]; exact sq_pos_of_ne_zero hx)
  have hρ0 : ρ 0 = ((|x + a / 2| : ℝ) : ℂ) := by
    change D 0 ^ ((1 : ℂ) / 2) = ((|x + a / 2| : ℝ) : ℂ)
    rw [hD0, Complex.ofReal_pow]
    exact cpow_half_ofReal_sq (x + a / 2)
  have hρ0ne : ρ 0 ≠ 0 := by rw [hρ0]; exact hR
  have hD' : HasDerivAt D D' 0 := by
    have h1 : HasDerivAt (fun u : ℂ => (F u + c) ^ 2)
        (↑(2 : ℕ) * (F 0 + c) ^ (2 - 1) * F') 0 := (hF.add_const c).pow 2
    have h2 : HasDerivAt (fun u : ℂ => G u ^ 2) (↑(2 : ℕ) * G 0 ^ (2 - 1) * G') 0 := hG.pow 2
    exact h1.add h2
  have hρ' : HasDerivAt ρ (((1 : ℂ) / 2) * D 0 ^ ((1 : ℂ) / 2 - 1) * D') 0 :=
    hD'.cpow_const hslit
  have hfst : HasDerivAt (fun u : ℂ => -(F u) + sg * (F u + c) / ρ u)
      (-F' + (sg * F' * ρ 0
        - sg * (F 0 + c) * (((1 : ℂ) / 2) * D 0 ^ ((1 : ℂ) / 2 - 1) * D')) / ρ 0 ^ 2) 0 :=
    hF.neg.add (((hF.add_const c).const_mul sg).div hρ' hρ0ne)
  have hfun : (fun u : ℂ => (invBranch a s (F u, G u)).1)
      = fun u : ℂ => -(F u) + sg * (F u + c) / ρ u := by
    funext u
    rfl
  rw [hfun]
  have hgoal : -F' + (sg * F' * ρ 0
        - sg * (F 0 + c) * (((1 : ℂ) / 2) * D 0 ^ ((1 : ℂ) / 2 - 1) * D')) / ρ 0 ^ 2 = -F' := by
    have hY : (F 0 + c) = ((x + a / 2 : ℝ) : ℂ) := by
      rw [hF0]
      change (x : ℂ) + ((a / 2 : ℝ) : ℂ) = ((x + a / 2 : ℝ) : ℂ)
      push_cast; ring
    have hD'val : D' = 2 * ((x + a / 2 : ℝ) : ℂ) * F' := by
      change (↑(2 : ℕ) * (F 0 + c) ^ (2 - 1) * F' + ↑(2 : ℕ) * G 0 ^ (2 - 1) * G')
        = 2 * ((x + a / 2 : ℝ) : ℂ) * F'
      rw [hY, hG0]
      norm_num
    have hnum : sg * F' * ρ 0
        - sg * (F 0 + c) * (((1 : ℂ) / 2) * D 0 ^ ((1 : ℂ) / 2 - 1) * D') = 0 := by
      rw [hY, hD'val, hρ0, hD0, Complex.ofReal_pow]
      have hX : ((x + a / 2 : ℝ) : ℂ) * ((1 : ℂ) / 2 * (((x + a / 2 : ℝ) : ℂ) ^ 2) ^ ((1 : ℂ) / 2 - 1) *
            (2 * ((x + a / 2 : ℝ) : ℂ) * F')) = F' * ((|x + a / 2| : ℝ) : ℂ) := by
        calc ((x + a / 2 : ℝ) : ℂ) * ((1 : ℂ) / 2 * (((x + a / 2 : ℝ) : ℂ) ^ 2) ^ ((1 : ℂ) / 2 - 1) *
              (2 * ((x + a / 2 : ℝ) : ℂ) * F'))
            = (((x + a / 2 : ℝ) : ℂ) ^ 2 * ((((x + a / 2 : ℝ) : ℂ) ^ 2) ^ ((1 : ℂ) / 2 - 1))) * F' := by
              ring
          _ = F' * ((|x + a / 2| : ℝ) : ℂ) := ofReal_sq_mul_cpow_half_sub_one hx F'
      have hthis : sg * F' * ((|x + a / 2| : ℝ) : ℂ)
          = sg * (((x + a / 2 : ℝ) : ℂ) * ((1 : ℂ) / 2 * (((x + a / 2 : ℝ) : ℂ) ^ 2) ^
              ((1 : ℂ) / 2 - 1) * (2 * ((x + a / 2 : ℝ) : ℂ) * F'))) := by
        rw [hX]; ring
      rw [hthis]
      ring
    rw [hnum, zero_div, add_zero]
  rw [hgoal] at hfst
  exact hfst

/-- **The abscissa of the stable germ has vanishing derivative at `0`.**  Differentiating the
invariance `invBranch a true (germC a h (λ u)) = germC a h u` (`germC_facts`) at `u = 0` and
computing the left-hand side with `invBranch_axis_fst_deriv` gives `d = -λ d` for
`d = deriv (fun u => (germC a h u).1) 0`; since `1 + λ ≠ 0`, `d = 0`. -/
lemma germC_fst_deriv_zero {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    deriv (fun u : ℂ => (germC a h u).1) 0 = 0 := by
  obtain ⟨hd1, hd2, -, δ, hδpos, hinv⟩ := germC_diff_at_zero ha0 ha1 hh
  have hg0 : germC a h 0 = ((-1 / 2 : ℂ), (0 : ℂ)) := germC_value ha0 ha1 hh
  have hev : (fun u : ℂ => (invBranch a true (germC a h (((eqLam a : ℝ) : ℂ) * u))).1)
      =ᶠ[𝓝 (0 : ℂ)] (fun u : ℂ => (germC a h u).1) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hδpos] with u hu
    rw [hinv u hu]
  have hderiv_eq : deriv (fun u : ℂ => (invBranch a true (germC a h (((eqLam a : ℝ) : ℂ) * u))).1)
      0 = deriv (fun u : ℂ => (germC a h u).1) 0 := Filter.EventuallyEq.deriv_eq hev
  have hlin : HasDerivAt (fun u : ℂ => ((eqLam a : ℝ) : ℂ) * u) (((eqLam a : ℝ) : ℂ)) 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_mul (((eqLam a : ℝ) : ℂ))
  have hF : HasDerivAt (fun u : ℂ => (germC a h (((eqLam a : ℝ) : ℂ) * u)).1)
      (deriv (fun u : ℂ => (germC a h u).1) 0 * ((eqLam a : ℝ) : ℂ)) 0 :=
    HasDerivAt.comp (x := 0) (h := fun u : ℂ => ((eqLam a : ℝ) : ℂ) * u)
      (h₂ := fun z : ℂ => (germC a h z).1) (h' := ((eqLam a : ℝ) : ℂ))
      (h₂' := deriv (fun u : ℂ => (germC a h u).1) 0)
      (by simpa only [mul_zero] using hd1.hasDerivAt) hlin
  have hG : HasDerivAt (fun u : ℂ => (germC a h (((eqLam a : ℝ) : ℂ) * u)).2)
      (deriv (fun u : ℂ => (germC a h u).2) 0 * ((eqLam a : ℝ) : ℂ)) 0 :=
    HasDerivAt.comp (x := 0) (h := fun u : ℂ => ((eqLam a : ℝ) : ℂ) * u)
      (h₂ := fun z : ℂ => (germC a h z).2) (h' := ((eqLam a : ℝ) : ℂ))
      (h₂' := deriv (fun u : ℂ => (germC a h u).2) 0)
      (by simpa only [mul_zero] using hd2.hasDerivAt) hlin
  have hF0 : (fun u : ℂ => (germC a h (((eqLam a : ℝ) : ℂ) * u)).1) 0 = ((-1 / 2 : ℝ) : ℂ) := by
    change (germC a h (((eqLam a : ℝ) : ℂ) * 0)).1 = ((-1 / 2 : ℝ) : ℂ)
    rw [mul_zero, hg0]
    norm_num
  have hG0 : (fun u : ℂ => (germC a h (((eqLam a : ℝ) : ℂ) * u)).2) 0 = 0 := by
    change (germC a h (((eqLam a : ℝ) : ℂ) * 0)).2 = 0
    rw [mul_zero, hg0]
  have hx : (-1 / 2 : ℝ) + a / 2 ≠ 0 := by
    have h : (-1 / 2 : ℝ) + a / 2 = (a - 1) / 2 := by ring
    rw [h]
    exact div_ne_zero (by linarith) (by norm_num)
  have hstep := invBranch_axis_fst_deriv (a := a) (s := true) (x := (-1 / 2 : ℝ)) hF hG hF0 hG0 hx
  have hderivval : deriv (fun u : ℂ =>
        (invBranch a true (germC a h (((eqLam a : ℝ) : ℂ) * u))).1) 0
      = -(deriv (fun u : ℂ => (germC a h u).1) 0 * ((eqLam a : ℝ) : ℂ)) := hstep.deriv
  have key : deriv (fun u : ℂ => (germC a h u).1) 0
      = -(deriv (fun u : ℂ => (germC a h u).1) 0 * ((eqLam a : ℝ) : ℂ)) :=
    hderiv_eq.symm.trans hderivval
  have hone : (1 : ℂ) + ((eqLam a : ℝ) : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.ofReal_ne_zero]
    have hl0 := eqLam_pos' ha0 ha1
    linarith
  have hsum : deriv (fun u : ℂ => (germC a h u).1) 0 * (1 + ((eqLam a : ℝ) : ℂ)) = 0 := by
    linear_combination key
  exact (mul_eq_zero.mp hsum).resolve_right hone

/-- The first (abscissa) coordinate of the fan has vanishing derivative at `u = 0`, for every
branch word `ε`.  Route: `deriv (fun u => (fan a h ε u).1) 0 = (-λ)^{|ε|} * deriv (fun u =>
(germC a h u).1) 0` by induction (the Jacobian of `invBranch a s` at an axis point `(c,0)` has
`∂₁ = -1` and `∂₂ = 0` in the first coordinate: `Work.EQ.invBranch_axis_deriv` gives
differentiability of that coordinate and its derivative is `-F'`), and
`deriv (fun u => (germC a h u).1) 0 = 0` from the invariance
`invBranch a true (germC a h (λ u)) = germC a h u` (`germC_facts`) which gives `d = -λ d`. -/
theorem fan_deriv_fst_zero {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) (ε : List Bool) :
    deriv (fun u : ℂ => (Work.EQ.fan a h ε u).1) 0 = 0 := by
  induction ε with
  | nil => exact germC_fst_deriv_zero ha0 ha1 hh
  | cons s ε ih =>
    obtain ⟨hd1, hd2, hc, -⟩ := fan_aux ha0 ha1 hh ε
    have hx : stCtr (stAux ε.reverse 0) + a / 2 ≠ 0 := (walk_bounds ha0 ha1).2.2.1 _
    have hlin : HasDerivAt (fun u : ℂ => ((eqLam a : ℝ) : ℂ) * u) (((eqLam a : ℝ) : ℂ)) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul (((eqLam a : ℝ) : ℂ))
    have hF : HasDerivAt (fun u : ℂ => (fan a h ε (((eqLam a : ℝ) : ℂ) * u)).1)
        (deriv (fun u : ℂ => (fan a h ε u).1) 0 * ((eqLam a : ℝ) : ℂ)) 0 :=
      HasDerivAt.comp (x := 0) (h := fun u : ℂ => ((eqLam a : ℝ) : ℂ) * u)
        (h₂ := fun z : ℂ => (fan a h ε z).1) (h' := ((eqLam a : ℝ) : ℂ))
        (h₂' := deriv (fun u : ℂ => (fan a h ε u).1) 0)
        (by simpa only [mul_zero] using hd1.hasDerivAt) hlin
    have hG : HasDerivAt (fun u : ℂ => (fan a h ε (((eqLam a : ℝ) : ℂ) * u)).2)
        (deriv (fun u : ℂ => (fan a h ε u).2) 0 * ((eqLam a : ℝ) : ℂ)) 0 :=
      HasDerivAt.comp (x := 0) (h := fun u : ℂ => ((eqLam a : ℝ) : ℂ) * u)
        (h₂ := fun z : ℂ => (fan a h ε z).2) (h' := ((eqLam a : ℝ) : ℂ))
        (h₂' := deriv (fun u : ℂ => (fan a h ε u).2) 0)
        (by simpa only [mul_zero] using hd2.hasDerivAt) hlin
    have hF0 : (fun u : ℂ => (fan a h ε (((eqLam a : ℝ) : ℂ) * u)).1) 0
        = ((stCtr (stAux ε.reverse 0) : ℝ) : ℂ) := by
      change (fan a h ε (((eqLam a : ℝ) : ℂ) * 0)).1 = _
      rw [mul_zero, hc]
    have hG0 : (fun u : ℂ => (fan a h ε (((eqLam a : ℝ) : ℂ) * u)).2) 0 = 0 := by
      change (fan a h ε (((eqLam a : ℝ) : ℂ) * 0)).2 = 0
      rw [mul_zero, hc]
    have hstep := invBranch_axis_fst_deriv (a := a) (s := s) (x := stCtr (stAux ε.reverse 0))
      hF hG hF0 hG0 hx
    have hderivval : deriv (fun u : ℂ => (fan a h (s :: ε) u).1) 0
        = -(deriv (fun u : ℂ => (fan a h ε u).1) 0 * ((eqLam a : ℝ) : ℂ)) := hstep.deriv
    rw [hderivval, ih]
    ring

end

end Work.EQ.FanTri
