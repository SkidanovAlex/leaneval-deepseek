/-
# The `D_θ`- and `D_z`-commutators of `𝓛̂` on the *open* quadrant `(0,∞) × (0,π/2)`

The clean operator of the node-N2 fix (`Submission/Work/FTS/CoercivityFix/Basic.lean`) is

  `𝓛̂ f = 𝓛 f − Transport f = f + D_z f − 2f/(1+z) − 3 D_θ f/(1+z)`,

and its two commutator identities are

* `D_θ(𝓛̂ f) = 𝓛̂(D_θ f)` (no commutator at all),
* `D_z(𝓛̂ f) = 𝓛̂(D_z f) + Ê₂ f`, `Ê₂ f = (2zf + 3zD_θf)/(1+z)²`.

They are proved in `Submission/Work/FTS/CoercivityFix/LhatCalc/Dth_Lhat.lean` and
`.../Dz_Lhat.lean` for a datum of class `Work.FTS.LocData.SmoothQuad`, i.e. `C^∞` on the
*whole* open quadrant `(-1,∞) × (0,π/2)`.  The strong-persistence chapter however only has
`Work.FTS.EllipticEst.SmoothOpen h`, i.e. `C^∞` on the smaller open quadrant

  `Q0 = (0,∞) × (0,π/2)`    (`= Work.Construction.Qd`, definitionally),

which is *not* a neighbourhood of the closed quadrant and does **not** imply `SmoothQuad h`
(nothing at all is known about `h` for `z ≤ 0`).

This file removes the mismatch.  Both identities are *local*: they only involve the germ of
`h` at the point in question and one derivative of each slice there, so they hold for any
datum which is `C^∞` on an arbitrary **open** set `V` containing `(z,θ)`:

* `Dth_Lhat_of_open`, `Dz_Lhat_of_open`.

The proofs are the proofs of `LhatCalc.Dth_Lhat` and `LhatCalc.Dz_Lhat` with the fixed
quadrant `quadU` replaced by the variable open set `V` (the public helper lemmas
`LhatCalc.DthAux.contDiffOn_uncurry_pz_sm`, `..._pth_sm`, `...pth_L_of_smooth`,
`...pth_Dth_eq` are already stated for a general open set).  Specialising to `V = Q0`
(`isOpen_Q0`) and using `Work.Construction.Qd = Q0` gives the requested `LhatCommOpen`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.FTS.CoercivityFix.LhatCalc.Dth_Lhat
import Submission.Work.FTS.CoercivityFix.LhatCalc.Dz_Lhat
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Aux

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.FTS.CoercivityFix.LhatCalc.DthAux

/-! ## The `D_θ`-commutator on an arbitrary open set -/

/-- **`D_θ` commutes exactly with `𝓛̂ = 𝓛 − Transport`** for a datum which is `C^∞` on an
arbitrary open set `V ∋ (z,θ)` (in particular on the open quadrant `(0,∞) × (0,π/2)` of the
strong-persistence estimates).  There is no commutator term, no nonlocal contribution and no
zero-mode hypothesis: this is `LhatCalc.Dth_Lhat` with the fixed quadrant replaced by `V`. -/
theorem Dth_Lhat_of_open {f : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hcd : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) V) {z θ : ℝ}
    (hmem : (z, θ) ∈ V) :
    Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ
      = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f) z θ := by
  have hcf : ContDiffAt ℝ Work.Stability.smoothOrder (Function.uncurry f) (z, θ) :=
    hcd.contDiffAt (hV.mem_nhds hmem)
  have hfθ : DifferentiableAt ℝ (fun θ' => f z θ') θ :=
    Work.Spaces.differentiableAt_curry_right (hcf.differentiableAt smoothOrder_ne_zero)
  have hpz_sm : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pz f)) V := contDiffOn_uncurry_pz_sm hV hcd
  have hpzθ : DifferentiableAt ℝ (fun θ' => Work.Spaces.pz f z θ') θ :=
    Work.Spaces.differentiableAt_curry_right
      ((hpz_sm.contDiffAt (hV.mem_nhds hmem)).differentiableAt smoothOrder_ne_zero)
  have hpth_sm : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pth f)) V := contDiffOn_uncurry_pth_sm hV hcd
  have hpthθ : DifferentiableAt ℝ (fun θ' => Work.Spaces.pth f z θ') θ :=
    Work.Spaces.differentiableAt_curry_right
      ((hpth_sm.contDiffAt (hV.mem_nhds hmem)).differentiableAt smoothOrder_ne_zero)
  have dL : DifferentiableAt ℝ (fun θ' => Work.Coercivity.L f z θ') θ := by
    rw [show (fun θ' => Work.Coercivity.L f z θ')
        = (fun θ' => f z θ' + z * Work.Spaces.pz f z θ' - (2 / (1 + z)) * f z θ') from by
      funext θ'; simp only [Work.Coercivity.L, Work.Spaces.Dz]; ring]
    exact (hfθ.add (hpzθ.const_mul z)).sub (hfθ.const_mul (2 / (1 + z)))
  have hDθ : DifferentiableAt ℝ (fun θ' => Work.Spaces.Dth f z θ') θ := by
    rw [show (fun θ' => Work.Spaces.Dth f z θ')
        = (fun θ' => Real.sin (2 * θ') * Work.Spaces.pth f z θ') from by
      funext θ'; simp only [Work.Spaces.Dth]]
    exact ((hasDerivAt_sin_two θ).differentiableAt).mul hpthθ
  have dTr : DifferentiableAt ℝ (fun θ' => Work.Coercivity.Transport f z θ') θ := by
    rw [show (fun θ' => Work.Coercivity.Transport f z θ')
        = (fun θ' => (3 / (1 + z)) * Work.Spaces.Dth f z θ') from by
      funext θ'; simp only [Work.Coercivity.Transport]; ring]
    exact hDθ.const_mul (3 / (1 + z))
  have hpth : Work.Spaces.pth (Work.FTS.CoercivityFix.Lhat f) z θ
      = Work.Spaces.pth (Work.Coercivity.L f) z θ
        - Work.Spaces.pth (Work.Coercivity.Transport f) z θ := by
    show deriv (fun θ' => Work.FTS.CoercivityFix.Lhat f z θ') θ = _
    rw [show (fun θ' => Work.FTS.CoercivityFix.Lhat f z θ')
        = ((fun θ' => Work.Coercivity.L f z θ')
            - fun θ' => Work.Coercivity.Transport f z θ') from by
      funext θ'; simp only [Work.FTS.CoercivityFix.Lhat, Pi.sub_apply]]
    rw [deriv_sub dL dTr]
    rfl
  rw [show Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.FTS.CoercivityFix.Lhat f) z θ from rfl]
  rw [hpth]
  rw [Work.FTS.CoercivityFix.Lhat_eq (Work.Spaces.Dth f) z θ]
  rw [pth_L_of_smooth hV hcd hmem, Work.Coercivity.pth_Transport]
  rw [show Work.Spaces.Dz (Work.Spaces.Dth f) z θ
      = z * Work.Spaces.pz (Work.Spaces.Dth f) z θ from rfl]
  rw [Work.Coercivity.pz_Dth_val]
  rw [show Work.Spaces.Dth (Work.Spaces.Dth f) z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.Dth f) z θ from rfl]
  rw [show Work.Spaces.Dth f z θ = Real.sin (2 * θ) * Work.Spaces.pth f z θ from rfl]
  rw [pth_Dth_eq (g := f) hpthθ]
  ring

/-! ## The smoothness of the partials at a point of `V` -/

section Slices

variable {f : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}

/-- The `z`-slices of `f` are differentiable at a point of the open set `V`. -/
private lemma diff_z_self (hV : IsOpen V)
    (hcd : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) V) {z θ : ℝ}
    (hmem : (z, θ) ∈ V) : DifferentiableAt ℝ (fun z' => f z' θ) z :=
  Work.Spaces.differentiableAt_curry_left
    ((hcd.contDiffAt (hV.mem_nhds hmem)).differentiableAt smoothOrder_ne_zero)

/-- The `z`-slices of `∂_z f` are differentiable at a point of the open set `V`. -/
private lemma diff_z_pz (hV : IsOpen V)
    (hcd : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) V) {z θ : ℝ}
    (hmem : (z, θ) ∈ V) : DifferentiableAt ℝ (fun z' => Work.Spaces.pz f z' θ) z :=
  Work.Spaces.differentiableAt_curry_left
    (((contDiffOn_uncurry_pz_sm hV hcd).contDiffAt (hV.mem_nhds hmem)).differentiableAt
      smoothOrder_ne_zero)

/-- The `θ`-slices of `∂_z f` are differentiable at a point of the open set `V`. -/
private lemma diff_th_pz (hV : IsOpen V)
    (hcd : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) V) {z θ : ℝ}
    (hmem : (z, θ) ∈ V) : DifferentiableAt ℝ (fun θ' => Work.Spaces.pz f z θ') θ :=
  Work.Spaces.differentiableAt_curry_right
    (((contDiffOn_uncurry_pz_sm hV hcd).contDiffAt (hV.mem_nhds hmem)).differentiableAt
      smoothOrder_ne_zero)

/-- The `z`-slices of `∂_θ f` are differentiable at a point of the open set `V`. -/
private lemma diff_z_pth (hV : IsOpen V)
    (hcd : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) V) {z θ : ℝ}
    (hmem : (z, θ) ∈ V) : DifferentiableAt ℝ (fun z' => Work.Spaces.pth f z' θ) z :=
  Work.Spaces.differentiableAt_curry_left
    (((contDiffOn_uncurry_pth_sm hV hcd).contDiffAt (hV.mem_nhds hmem)).differentiableAt
      smoothOrder_ne_zero)

end Slices

/-! ## The plain `z`-derivatives of the pieces -/

private lemma deriv_z_self {f : ℝ → ℝ → ℝ} {z θ : ℝ} :
    deriv (fun z' => f z' θ) z = Work.Spaces.pz f z θ := rfl

private lemma deriv_z_mul_pz {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hpzz : DifferentiableAt ℝ (fun z' => Work.Spaces.pz f z' θ) z) :
    deriv (fun z' : ℝ => z' * Work.Spaces.pz f z' θ) z
      = Work.Spaces.pz f z θ + z * Work.Spaces.pz (Work.Spaces.pz f) z θ := by
  have hh := (hasDerivAt_id z).mul hpzz.hasDerivAt
  have h2 : deriv (fun z' : ℝ => z' * Work.Spaces.pz f z' θ) z
      = deriv (id * fun z' : ℝ => Work.Spaces.pz f z' θ) z := rfl
  rw [h2, hh.deriv]
  simp only [id_eq, one_mul]
  rfl

private lemma deriv_z_two_div {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hfz : DifferentiableAt ℝ (fun z' => f z' θ) z) :
    deriv (fun z' : ℝ => 2 * f z' θ / (1 + z')) z
      = 2 * Work.Spaces.pz f z θ / (1 + z) - 2 * f z θ / (1 + z) ^ 2 := by
  have hden : (1 + z : ℝ) ≠ 0 := by positivity
  have hh := (hfz.hasDerivAt.const_mul (2 : ℝ)).div
    ((hasDerivAt_const (x := z) (1 : ℝ)).add (hasDerivAt_id z)) (by simpa using hden)
  have h2 : deriv (fun z' : ℝ => 2 * f z' θ / (1 + z')) z
      = deriv ((fun y : ℝ => 2 * f y θ) / ((fun _ : ℝ => (1 : ℝ)) + (id : ℝ → ℝ))) z := rfl
  rw [h2, hh.deriv]
  simp only [Pi.add_apply, id_eq, zero_add]
  rw [deriv_z_self]
  field_simp
  try ring_nf

private lemma deriv_z_three_div {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hpthz : DifferentiableAt ℝ (fun z' => Work.Spaces.pth f z' θ) z) :
    deriv (fun z' : ℝ => 3 * (Real.sin (2 * θ) * Work.Spaces.pth f z' θ) / (1 + z')) z
      = 3 * (Real.sin (2 * θ) * Work.Spaces.pz (Work.Spaces.pth f) z θ) / (1 + z)
        - 3 * (Real.sin (2 * θ) * Work.Spaces.pth f z θ) / (1 + z) ^ 2 := by
  have hden : (1 + z : ℝ) ≠ 0 := by positivity
  have hh := (((hasDerivAt_const (x := z) (Real.sin (2 * θ))).mul hpthz.hasDerivAt).const_mul
    (3 : ℝ)).div ((hasDerivAt_const (x := z) (1 : ℝ)).add (hasDerivAt_id z))
    (by simpa using hden)
  have h2 : deriv (fun z' : ℝ => 3 * (Real.sin (2 * θ) * Work.Spaces.pth f z' θ) / (1 + z')) z
      = deriv ((fun y : ℝ => (fun _ : ℝ => (3 : ℝ)) y
            * ((fun _ : ℝ => Real.sin (2 * θ)) * fun z' => Work.Spaces.pth f z' θ) y)
          / ((fun _ : ℝ => (1 : ℝ)) + (id : ℝ → ℝ))) z := rfl
  rw [h2, hh.deriv]
  simp only [Pi.add_apply, Pi.mul_apply, id_eq, zero_add, zero_mul]
  rw [show deriv (fun z' => Work.Spaces.pth f z' θ) z
      = Work.Spaces.pz (Work.Spaces.pth f) z θ from rfl]
  field_simp
  try ring_nf

private lemma deriv_z_Dz {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hpzz : DifferentiableAt ℝ (fun z' => Work.Spaces.pz f z' θ) z) :
    deriv (fun z' => Work.Spaces.Dz f z' θ) z
      = Work.Spaces.pz f z θ + z * Work.Spaces.pz (Work.Spaces.pz f) z θ := by
  have hh := (hasDerivAt_id z).mul hpzz.hasDerivAt
  have h1 : (fun z' => Work.Spaces.Dz f z' θ)
      = (id * fun z' : ℝ => Work.Spaces.pz f z' θ) := by
    funext z'; rfl
  rw [h1, hh.deriv]
  simp only [id_eq, one_mul]
  rfl

private lemma deriv_th_Dz {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hpzθ : DifferentiableAt ℝ (fun θ' => Work.Spaces.pz f z θ') θ) :
    deriv (fun θ' => Work.Spaces.Dz f z θ') θ = z * Work.Spaces.pth (Work.Spaces.pz f) z θ := by
  have hh := (hasDerivAt_const (x := θ) z).mul hpzθ.hasDerivAt
  have h1 : (fun θ' => Work.Spaces.Dz f z θ')
      = ((fun _ : ℝ => z) * fun θ' => Work.Spaces.pz f z θ') := by
    funext θ'; rfl
  rw [h1, hh.deriv]
  simp only [zero_mul, zero_add]
  rfl

/-! ## The `z`-derivatives of the slices of `𝓛 f` and of `Transport f` -/

private lemma pz_L_eq {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hfz : DifferentiableAt ℝ (fun z' => f z' θ) z)
    (hpzz : DifferentiableAt ℝ (fun z' => Work.Spaces.pz f z' θ) z) :
    Work.Spaces.pz (Work.Coercivity.L f) z θ
      = Work.Spaces.pz f z θ + (Work.Spaces.pz f z θ + z * Work.Spaces.pz (Work.Spaces.pz f) z θ)
        - 2 * Work.Spaces.pz f z θ / (1 + z) + 2 * f z θ / (1 + z) ^ 2 := by
  show deriv (fun z' => Work.Coercivity.L f z' θ) z = _
  have hden : (1 + z : ℝ) ≠ 0 := by positivity
  have hid : DifferentiableAt ℝ (id * fun z' : ℝ => Work.Spaces.pz f z' θ) z :=
    differentiableAt_id.mul hpzz
  have hq : DifferentiableAt ℝ
      ((fun y : ℝ => 2 * f y θ) / ((fun _ : ℝ => (1 : ℝ)) + (id : ℝ → ℝ))) z :=
    (hfz.const_mul 2).div ((differentiableAt_const _).add differentiableAt_id)
      (by simpa using hden)
  have h1 : (fun z' => Work.Coercivity.L f z' θ)
      = (((fun z' : ℝ => f z' θ) + (id * fun z' : ℝ => Work.Spaces.pz f z' θ))
          - ((fun y : ℝ => 2 * f y θ) / ((fun _ : ℝ => (1 : ℝ)) + (id : ℝ → ℝ)))) := by
    funext z'; rfl
  rw [h1, deriv_sub (hfz.add hid) hq, deriv_add hfz hid]
  rw [show deriv (id * fun z' : ℝ => Work.Spaces.pz f z' θ) z
      = deriv (fun z' : ℝ => z' * Work.Spaces.pz f z' θ) z from rfl]
  rw [show deriv ((fun y : ℝ => 2 * f y θ) / ((fun _ : ℝ => (1 : ℝ)) + (id : ℝ → ℝ))) z
      = deriv (fun z' : ℝ => 2 * f z' θ / (1 + z')) z from rfl]
  rw [deriv_z_mul_pz hpzz, deriv_z_two_div hz hfz, deriv_z_self]
  ring

private lemma pz_Transport_eq {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hpthz : DifferentiableAt ℝ (fun z' => Work.Spaces.pth f z' θ) z) :
    Work.Spaces.pz (Work.Coercivity.Transport f) z θ
      = 3 * (Real.sin (2 * θ) * Work.Spaces.pz (Work.Spaces.pth f) z θ) / (1 + z)
        - 3 * (Real.sin (2 * θ) * Work.Spaces.pth f z θ) / (1 + z) ^ 2 := by
  show deriv (fun z' => Work.Coercivity.Transport f z' θ) z = _
  have h1 : (fun z' => Work.Coercivity.Transport f z' θ)
      = (fun z' : ℝ => 3 * (Real.sin (2 * θ) * Work.Spaces.pth f z' θ) / (1 + z')) := by
    funext z'; rfl
  rw [h1, deriv_z_three_div hz hpthz]

private lemma diff_slice_L {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hfz : DifferentiableAt ℝ (fun z' => f z' θ) z)
    (hpzz : DifferentiableAt ℝ (fun z' => Work.Spaces.pz f z' θ) z) :
    DifferentiableAt ℝ (fun z' => Work.Coercivity.L f z' θ) z := by
  have hden : (1 + z : ℝ) ≠ 0 := by positivity
  rw [show (fun z' => Work.Coercivity.L f z' θ)
      = (fun z' => f z' θ + z' * Work.Spaces.pz f z' θ - 2 * f z' θ / (1 + z')) from by
    funext z'; rfl]
  exact (hfz.add (differentiableAt_id.mul hpzz)).sub
    ((hfz.const_mul 2).div ((differentiableAt_const _).add differentiableAt_id)
      (by simpa using hden))

private lemma diff_slice_Transport {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hpthz : DifferentiableAt ℝ (fun z' => Work.Spaces.pth f z' θ) z) :
    DifferentiableAt ℝ (fun z' => Work.Coercivity.Transport f z' θ) z := by
  have hden : (1 + z : ℝ) ≠ 0 := by positivity
  rw [show (fun z' => Work.Coercivity.Transport f z' θ)
      = (fun z' => 3 * (Real.sin (2 * θ) * Work.Spaces.pth f z' θ) / (1 + z')) from by
    funext z'; rfl]
  exact (((differentiableAt_const (c := Real.sin (2 * θ))).mul hpthz).const_mul 3).div
    ((differentiableAt_const (c := (1 : ℝ))).add differentiableAt_id) (by simpa using hden)

/-! ## The `D_z`-commutator on an arbitrary open set -/

/-- **The `D_z`-commutator of the clean operator** `𝓛̂ = 𝓛 − Transport` for a datum which is
`C^∞` on an arbitrary open set `V ∋ (z,θ)`:

  `D_z(𝓛̂ f) = 𝓛̂(D_z f) + Ê₂ f`,   `Ê₂ f = (2zf + 3z D_θ f)/(1+z)²`.

This is `LhatCalc.Dz_Lhat` with the fixed quadrant `quadU = (-1,∞) × (0,π/2)` replaced by the
variable open set `V`; the hypothesis `0 < z` is only there because `𝓛` divides by `1+z`. -/
theorem Dz_Lhat_of_open {f : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hcd : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) V) {z θ : ℝ}
    (hmem : (z, θ) ∈ V) (hz : 0 < z) :
    Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ
      = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) z θ
        + Work.FTS.CoercivityFix.E2hat f z θ := by
  have hden : (1 + z : ℝ) ≠ 0 := by positivity
  have hfz := diff_z_self hV hcd hmem
  have hpzz := diff_z_pz hV hcd hmem
  have hpzθ := diff_th_pz hV hcd hmem
  have hpthz := diff_z_pth hV hcd hmem
  have hLz := diff_slice_L (θ := θ) hz hfz hpzz
  have hTz := diff_slice_Transport (θ := θ) hz hpthz
  -- the plain `z`-derivatives of the two summands of `𝓛̂`
  have hpzL := pz_L_eq (θ := θ) hz hfz hpzz
  have hpzT := pz_Transport_eq (θ := θ) hz hpthz
  have hpzLhat : Work.Spaces.pz (Work.FTS.CoercivityFix.Lhat f) z θ
      = Work.Spaces.pz (Work.Coercivity.L f) z θ
        - Work.Spaces.pz (Work.Coercivity.Transport f) z θ := by
    show deriv (fun z' => Work.FTS.CoercivityFix.Lhat f z' θ) z = _
    have h1 : (fun z' => Work.FTS.CoercivityFix.Lhat f z' θ)
        = ((fun z' => Work.Coercivity.L f z' θ)
            - fun z' => Work.Coercivity.Transport f z' θ) := by
      funext z'; rfl
    rw [h1, deriv_sub hLz hTz]
    rfl
  have hLHS : Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ
      = z * (Work.Spaces.pz (Work.Coercivity.L f) z θ
          - Work.Spaces.pz (Work.Coercivity.Transport f) z θ) := by
    show z * deriv (fun z' => Work.FTS.CoercivityFix.Lhat f z' θ) z = _
    rw [show deriv (fun z' => Work.FTS.CoercivityFix.Lhat f z' θ) z
        = Work.Spaces.pz (Work.FTS.CoercivityFix.Lhat f) z θ from rfl, hpzLhat]
  -- the right-hand side
  have hDzDz : Work.Spaces.Dz (Work.Spaces.Dz f) z θ
      = z * (Work.Spaces.pz f z θ + z * Work.Spaces.pz (Work.Spaces.pz f) z θ) := by
    show z * deriv (fun z' => Work.Spaces.Dz f z' θ) z = _
    rw [deriv_z_Dz hpzz]
  have hDthDz : Work.Spaces.Dth (Work.Spaces.Dz f) z θ
      = Real.sin (2 * θ) * (z * Work.Spaces.pth (Work.Spaces.pz f) z θ) := by
    show Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.Dz f z θ') θ = _
    rw [deriv_th_Dz hpzθ]
  have hRHS : Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) z θ
        + Work.FTS.CoercivityFix.E2hat f z θ
      = (z * Work.Spaces.pz f z θ
          + z * (Work.Spaces.pz f z θ + z * Work.Spaces.pz (Work.Spaces.pz f) z θ)
          - 2 * (z * Work.Spaces.pz f z θ) / (1 + z)
          - 3 * (Real.sin (2 * θ) * (z * Work.Spaces.pth (Work.Spaces.pz f) z θ)) / (1 + z))
        + (2 * z * f z θ + 3 * z * (Real.sin (2 * θ) * Work.Spaces.pth f z θ)) / (1 + z) ^ 2 := by
    rw [Work.FTS.CoercivityFix.Lhat_eq (Work.Spaces.Dz f), Work.FTS.CoercivityFix.E2hat_eq]
    rw [hDzDz, hDthDz]
    rw [show Work.Spaces.Dz f z θ = z * Work.Spaces.pz f z θ from rfl,
      show Work.Spaces.Dth f z θ = Real.sin (2 * θ) * Work.Spaces.pth f z θ from rfl]
  -- Clairaut's theorem finishes the identification `∂_θ∂_z f = ∂_z∂_θ f`
  have hcd2 : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ) :=
    (hcd.contDiffAt (hV.mem_nhds hmem)).of_le (by simp [Work.Stability.smoothOrder])
  have hcl := Work.Spaces.pz_pth_comm hcd2
  rw [hLHS, hRHS, hpzL, hpzT, hcl]
  field_simp
  try ring_nf

/-! ## The requested statement -/

/-- **Both commutator identities of `𝓛̂` on the open quadrant `Qd = (0,∞) × (0,π/2)`**: for a
datum `h` that is `C^∞` on the open quadrant `(0,∞) × (0,π/2)` (the class
`Work.FTS.EllipticEst.SmoothOpen`) and every interior point `(z,θ) ∈ Qd`,

* `D_θ(𝓛̂ h) = 𝓛̂(D_θ h)`,
* `D_z(𝓛̂ h) = 𝓛̂(D_z h) + Ê₂ h`. -/
theorem LhatCommOpen {h : ℝ → ℝ → ℝ} (hs : Work.FTS.EllipticEst.SmoothOpen h) :
    (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat h) z θ
        = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth h) z θ) ∧
    (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat h) z θ
        = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz h) z θ
          + Work.FTS.CoercivityFix.E2hat h z θ) := by
  have hs' : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry h)
      (Work.FTS.EllipticEst.Q0) := hs
  refine ⟨fun z θ hzθ => Dth_Lhat_of_open Work.FTS.EllipticEst.isOpen_Q0 hs' hzθ,
    fun z θ hzθ => Dz_Lhat_of_open Work.FTS.EllipticEst.isOpen_Q0 hs' hzθ ?_⟩
  have h := hzθ
  rw [Work.Construction.Qd, Set.mem_prod, Set.mem_Ioi] at h
  exact h.1

end Work.FTS.StrongPersist.H6Aux
