/-
# `PkgK5/uopPointwiseIdentityRefute` — `uopPointwiseIdentity` is FALSE as stated

The requested identity (`Submission/Work/FTS/EllSol/PkgK5/uopPointwiseIdentity.lean`)

  `Uop α (EllResid α g Φg) / sin 2θ
     = -3·(ellShift α g Φg / sin 2θ) - α·(D_z(ellShift α g Φg) / sin 2θ)
        - (2·Ḡ(α,g) + (3/4)·F_*(g))`

carries **no hypothesis on `Φg`**, and `D_z` is the *totalised* `z·∂_z`: Mathlib's `deriv` is
`0` at every point where the `z`-slice fails to be differentiable
(`deriv_zero_of_not_differentiableAt`).  Writing

  `X := ellShift α g Φg`,  `Ξ := EllResid α g Φg = X - Ḡ·sin 2θ`  (`Ḡ := Gbar α g`),

the identity is equivalent to

  `α·(D_z X - D_z Ξ) = sin 2θ · (-5·Ḡ - (3/4)·F_*)`,

i.e. to `D_z X = D_z Ξ + sin 2θ·D_z Ḡ`: it uses the additivity of `z·∂_z` and hence the
differentiability of the `z`-slices of `Φg` (true for a smooth `Φg`, false in general).  When the
`z`-slice of `Φg` is *not* differentiable, the totalised `deriv` of *both* slices is `0`, and the
identity degenerates to `5·Ḡ α g z + (3/4)·F_*(g)(z) = 0`.

## Contents

* `uopi_deriv_eq_zero_of_not_differentiableAt`, `uopi_deriv_eq_zero_of_add_of_not`,
  `uopi_deriv_eq_zero_of_sub_of_not`, `uopi_not_differentiableAt_abs_sub` — the elementary
  calculus facts about the totalised `deriv` used by the refutation;
* `uopi_diff_reduction`, `uopi_iff_reduction` — under `pz X = pz Ξ = 0` the two sides differ by
  exactly `5·Ḡ + (3/4)·F_*`, so the identity holds there **iff** `5·Ḡ + (3/4)·F_* = 0`;
* `uopPointwiseIdentity_false_of_nonconstant_Gbar` — the **refutation** (machine-checked): if
  `ClassC α g` (`α ≤ 1`) and `∂_z(Ḡ α g) z₀ ≠ 0` for some `z₀ > 0`, then the requested
  identity fails for the datum `Φg z θ = |z - z₀|` at `(z₀, θ)` for any `θ ∈ (0,π/2)`.  It uses
  only the tree's proved `CexK5.Gbar_deriv_rel`
  `α z ∂_z(Ḡ α g) z = -5Ḡ α g z - (3/4)F_*(g)(z)`;
* `uopPointwiseIdentity_repaired` — the statement with the missing hypothesis `SmoothOpen Φg`
  (and `α ≤ 1`, an artefact of `Cert.Jfun_hasDerivAt_of_Fstar`), **proved**: this exhibits the
  exact gap and gives the consumers a usable form.

## The counterexample datum (`ClassC` with `Ḡ` not locally constant)

Take `χ : ℝ → ℝ` smooth, `χ ≥ 0`, `χ ≠ 0`, compactly supported in `(0,∞)`, set
`ψ(r) := r·χ'(r)` (so `ψ` is smooth, compactly supported in `(0,∞)`,
`∫_0^∞ ψ(r)/r dr = ∫_0^∞ χ'(r) dr = 0`, and
`∫_0^∞ s^{(5-α)/α} ψ(s) ds = -(5/α)∫_0^∞ s^{(5-α)/α} χ(s) ds ≠ 0`), and let

  `g z θ := normTh ((15/4)·ψ(z)·sin 2θ)`  on `[0,∞) × [0,π/2]`.

Then `F_*(g) = ψ` (because `∫_0^{π/2} sin 2θ·sin θ cos²θ dθ = 4/15`), and each of the seven
fields of `ClassC α g` is elementary: `norm` by construction; `reg` because `ψ` is smooth on
`(0,∞)`; `mem` (`HkMem α 7 g`) and `tr` (`BdryTraces α 6 g`) because every `D_z^j`-derivative of
`ψ` is compactly supported in `(0,∞)` (all radial limits vanish, and the angular conditions reduce
to `sin(2θ)^{3-γ}·(bounded)² → 0`, `γ < 3/2`); `fsm` because `F_*(g) = ψ` is `C^∞` on `(0,∞)`;
`axis` because `ψ ≡ 0` near `0`; `l12` because `L₁₂(g)(0) = 3∫_0^∞ ψ(r)/r dr = 0`.  This is the
same witness family as the one documented for the sibling refutations of this directory
(`NOTES_uopTransferK5_FALSE.md` §3, `PkgK_counterexample.lean`), with compact support instead of
power decay.  For it,

  `Ḡ α g z = -(3/(4α))·z^{-5/α}·∫_0^z s^{(5-α)/α} ψ(s) ds = -(3/(4α))·C·z^{-5/α}`  (`z` beyond
  `supp ψ`, `C ≠ 0`),

so `∂_z(Ḡ α g) z ≠ 0` for every such `z` — and the identity fails there.
-/
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllSol.PkgK5.CexK5
import Submission.Work.FTS.EllSol.ClassC
import Submission.Work.FTS.EllSol.Defs
import Submission.Work.FTS.EllipticEst.FstarDivOpen.fstar_div_integrable_of_smoothOpen
import Submission.Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts
import Submission.Work.FTS.EllipticEst.Cert.Jfun_hasDerivAt_of_Fstar

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5

set_option autoImplicit false

/-! ## 0. Elementary facts about the totalised `deriv` -/

/-- The (totalised) derivative of a function that fails to be differentiable is `0`. -/
theorem uopi_deriv_eq_zero_of_not_differentiableAt (f : ℝ → ℝ) {x : ℝ}
    (h : ¬ DifferentiableAt ℝ f x) : deriv f x = 0 :=
  deriv_zero_of_not_differentiableAt h

/-- `deriv` of `A + B` vanishes when `A` is not differentiable and `B` is. -/
theorem uopi_deriv_eq_zero_of_add_of_not (A B : ℝ → ℝ) {x : ℝ} (hB : DifferentiableAt ℝ B x)
    (hA : ¬ DifferentiableAt ℝ A x) :
    deriv (fun z => A z + B z) x = 0 := by
  have h : ¬ DifferentiableAt ℝ (fun z => A z + B z) x := by
    intro hh
    have h' : DifferentiableAt ℝ A x := by
      have h2 : DifferentiableAt ℝ (fun z => (A z + B z) - B z) x := hh.sub hB
      have hfun : (fun z => (A z + B z) - B z) = A := by funext z; ring
      rwa [hfun] at h2
    exact hA h'
  exact uopi_deriv_eq_zero_of_not_differentiableAt _ h

/-- `deriv` of `A - B` vanishes when `A` is not differentiable and `B` is. -/
theorem uopi_deriv_eq_zero_of_sub_of_not (A B : ℝ → ℝ) {x : ℝ} (hB : DifferentiableAt ℝ B x)
    (hA : ¬ DifferentiableAt ℝ A x) :
    deriv (fun z => A z - B z) x = 0 := by
  have h : ¬ DifferentiableAt ℝ (fun z => A z - B z) x := by
    intro hh
    have h' : DifferentiableAt ℝ A x := by
      have h2 : DifferentiableAt ℝ (fun z => (A z - B z) + B z) x := hh.add hB
      have hfun : (fun z => (A z - B z) + B z) = A := by funext z; ring
      rwa [hfun] at h2
    exact hA h'
  exact uopi_deriv_eq_zero_of_not_differentiableAt _ h

/-- `z ↦ |z - z₀|` is not differentiable at `z₀` (it is `abs` up to the translation
`z ↦ z + z₀`, and `abs` is not differentiable at `0`: `not_differentiableAt_abs_zero`). -/
theorem uopi_not_differentiableAt_abs_sub (z₀ : ℝ) :
    ¬ DifferentiableAt ℝ (fun z : ℝ => |z - z₀|) z₀ := by
  intro h
  have hg : DifferentiableAt ℝ (fun y : ℝ => y + z₀) 0 :=
    ((hasDerivAt_id (0 : ℝ)).add_const z₀).differentiableAt
  have h' : DifferentiableAt ℝ (fun z : ℝ => |z - z₀|) (0 + z₀) := by simpa using h
  have h1 : DifferentiableAt ℝ ((fun z : ℝ => |z - z₀|) ∘ fun y : ℝ => y + z₀) 0 :=
    h'.comp 0 hg
  have h2 : ((fun z : ℝ => |z - z₀|) ∘ fun y : ℝ => y + z₀) = abs := by
    funext y
    simp only [Function.comp_apply]
    rw [show y + z₀ - z₀ = y from by ring]
  rw [h2] at h1
  exact not_differentiableAt_abs_zero h1

/-! ## 1. The algebraic reduction of the requested identity -/

/-- **The reduction.**  Under `pz (ellShift …) = 0` and `pz (EllResid …) = 0` (which is exactly
what the totalised `deriv` returns once the `z`-slice of `Φg` is not differentiable at `z`),
the target identity differs from its claimed right-hand side by `5·Ḡ + (3/4)·F_*`. -/
theorem uopi_diff_reduction (α : ℝ) (g Φg : Work.FTS.Galerkin.Fn) (z θ : ℝ)
    (hσ : Real.sin (2 * θ) ≠ 0)
    (hX : Work.Spaces.pz (Work.FTS.EllSol.ellShift α g Φg) z θ = 0)
    (hΞ : Work.Spaces.pz (Work.Elliptic.EllResid α g Φg) z θ = 0) :
    Work.FTS.EllipticEst.Uop α (Work.Elliptic.EllResid α g Φg) z θ / Real.sin (2 * θ)
      = -3 * (Work.FTS.EllSol.ellShift α g Φg z θ / Real.sin (2 * θ))
        - α * (Work.Spaces.Dz (Work.FTS.EllSol.ellShift α g Φg) z θ / Real.sin (2 * θ))
        - (2 * Work.Elliptic.Gbar α g z + (3 / 4) * Work.Elliptic.Fstar g z)
        + (5 * Work.Elliptic.Gbar α g z + (3 / 4) * Work.Elliptic.Fstar g z) := by
  have hDzX : Work.Spaces.Dz (Work.FTS.EllSol.ellShift α g Φg) z θ = 0 := by
    simp only [Work.Spaces.Dz, hX, mul_zero]
  have hU : Work.FTS.EllipticEst.Uop α (Work.Elliptic.EllResid α g Φg) z θ
      = -3 * (Work.Elliptic.EllResid α g Φg) z θ := by
    simp only [Work.FTS.EllipticEst.Uop, hΞ, mul_zero, sub_zero]
  rw [hU, hDzX]
  simp only [Work.FTS.EllSol.ellShift, Work.Elliptic.EllResid, Work.Elliptic.Gsing,
    Work.Elliptic.Gstar]
  field_simp
  ring

/-- **The equivalence.**  Under those two degenerate hypotheses the claimed identity holds
*iff* `5·Ḡ α g z + (3/4)·F_*(g)(z) = 0` — equivalently (`CexK5.Gbar_deriv_rel`) iff
`∂_z(Ḡ α g) z = 0`. -/
theorem uopi_iff_reduction (α : ℝ) (g Φg : Work.FTS.Galerkin.Fn) (z θ : ℝ)
    (hσ : Real.sin (2 * θ) ≠ 0)
    (hX : Work.Spaces.pz (Work.FTS.EllSol.ellShift α g Φg) z θ = 0)
    (hΞ : Work.Spaces.pz (Work.Elliptic.EllResid α g Φg) z θ = 0) :
    (Work.FTS.EllipticEst.Uop α (Work.Elliptic.EllResid α g Φg) z θ / Real.sin (2 * θ)
        = -3 * (Work.FTS.EllSol.ellShift α g Φg z θ / Real.sin (2 * θ))
          - α * (Work.Spaces.Dz (Work.FTS.EllSol.ellShift α g Φg) z θ / Real.sin (2 * θ))
          - (2 * Work.Elliptic.Gbar α g z + (3 / 4) * Work.Elliptic.Fstar g z))
      ↔ 5 * Work.Elliptic.Gbar α g z + (3 / 4) * Work.Elliptic.Fstar g z = 0 := by
  rw [uopi_diff_reduction α g Φg z θ hσ hX hΞ]
  constructor
  · intro h
    linarith
  · intro h
    rw [h, add_zero]

/-! ## 2. The refutation -/

/-- **`uopPointwiseIdentity` fails** whenever `Ḡ α g` has a non-vanishing `z`-derivative at some
`z₀ > 0`.  The counterexample is `Φg z θ = |z - z₀|`, whose `z`-slices are not differentiable at
`z₀`, so that the totalised `pz` of *both* `ellShift α g Φg` and `EllResid α g Φg` vanishes at
`(z₀, θ)`; the identity then reduces (`uopi_iff_reduction`) to
`5·Ḡ α g z₀ + (3/4)·F_*(g)(z₀) = 0`, which contradicts `CexK5.Gbar_deriv_rel` and
`∂_z(Ḡ α g) z₀ ≠ 0`. -/
theorem uopPointwiseIdentity_false_of_nonconstant_Gbar {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {g : Work.FTS.Galerkin.Fn} (hC : Work.FTS.EllSol.ClassC α g) {z₀ : ℝ} (hz₀ : 0 < z₀)
    (hderiv : deriv (Work.Elliptic.Gbar α g) z₀ ≠ 0) :
    ¬ (∀ (Φg : Work.FTS.Galerkin.Fn) (z θ : ℝ), 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.EllipticEst.Uop α (Work.Elliptic.EllResid α g Φg) z θ / Real.sin (2 * θ)
        = -3 * (Work.FTS.EllSol.ellShift α g Φg z θ / Real.sin (2 * θ))
          - α * (Work.Spaces.Dz (Work.FTS.EllSol.ellShift α g Φg) z θ / Real.sin (2 * θ))
          - (2 * Work.Elliptic.Gbar α g z + (3 / 4) * Work.Elliptic.Fstar g z)) := by
  intro H
  -- ## the analytic facts on `F_*`, `L₁₂`, `Ḡ`, `Gsing` supplied by `ClassC`
  have hFsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar g) (Set.Ioi 0) := hC.fsm
  have hFint : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar g r / r)
      (Set.Ioi 0) :=
    Work.FTS.EllipticEst.FstarDivOpen.fstar_div_integrable_of_smoothOpen α 7 g hC.reg hC.mem
  have hL12 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.L12 g) (-(3 * Work.Elliptic.Fstar g z / z)) z :=
    Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts g hFsm hFint
  have hJ : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' => ∫ s in (0 : ℝ)..z', s ^ ((5 - α) / α) * Work.Elliptic.Fstar g s)
        (z ^ ((5 - α) / α) * Work.Elliptic.Fstar g z) z :=
    Work.FTS.EllipticEst.Cert.Jfun_hasDerivAt_of_Fstar α g hFsm hFint hα hα1
  have hJz : HasDerivAt (Work.Elliptic.Jfun α g)
      (z₀ ^ ((5 - α) / α) * Work.Elliptic.Fstar g z₀) z₀ := by
    have h := hJ z₀ hz₀
    have hfun : (fun z' => ∫ s in (0 : ℝ)..z',
        s ^ ((5 - α) / α) * Work.Elliptic.Fstar g s) = Work.Elliptic.Jfun α g := rfl
    rw [hfun] at h
    exact h
  have hGbarDeriv : HasDerivAt (Work.Elliptic.Gbar α g) (Work.Elliptic.DGbar α g z₀) z₀ :=
    CexK5.hasDerivAt_Gbar_DGbar α g hz₀ hJz
  have hGbar_diff : DifferentiableAt ℝ (Work.Elliptic.Gbar α g) z₀ :=
    hGbarDeriv.differentiableAt
  have hGstar_diff : DifferentiableAt ℝ (Work.Elliptic.Gstar α g) z₀ := by
    have h1 : Work.Elliptic.Gstar α g
        = fun z : ℝ => (-(1 / (4 * α))) * Work.Elliptic.L12 g z := rfl
    rw [h1]
    exact (differentiableAt_const _).mul (hL12 z₀ hz₀).differentiableAt
  have hGsing_diff : DifferentiableAt ℝ (Work.Elliptic.Gsing α g) z₀ := by
    have h1 : Work.Elliptic.Gsing α g
        = Work.Elliptic.Gstar α g + Work.Elliptic.Gbar α g := rfl
    rw [h1]
    exact hGstar_diff.add hGbar_diff
  -- ## the counterexample datum and the angle
  refine absurd ?_ hderiv
  set Φg : Work.FTS.Galerkin.Fn := fun z _ => |z - z₀| with hΦg
  set θ : ℝ := Real.pi / 4 with hθ
  have hθpos : 0 < θ := by rw [hθ]; positivity
  have hθlt : θ < Real.pi / 2 := by rw [hθ]; linarith [Real.pi_pos]
  have hσ : Real.sin (2 * θ) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθlt, Real.pi_pos]))
  -- ## the two `pz` values vanish by the totalised-`deriv` convention
  have hX : Work.Spaces.pz (Work.FTS.EllSol.ellShift α g Φg) z₀ θ = 0 := by
    have hB : DifferentiableAt ℝ
        (fun z : ℝ => Work.Elliptic.Gsing α g z * Real.sin (2 * θ)) z₀ :=
      hGsing_diff.mul_const _
    have h := uopi_deriv_eq_zero_of_add_of_not (fun z : ℝ => |z - z₀|)
      (fun z : ℝ => Work.Elliptic.Gsing α g z * Real.sin (2 * θ)) hB
      (uopi_not_differentiableAt_abs_sub z₀)
    simpa only [Work.Spaces.pz, Work.FTS.EllSol.ellShift, hΦg] using h
  have hΞ : Work.Spaces.pz (Work.Elliptic.EllResid α g Φg) z₀ θ = 0 := by
    have hB : DifferentiableAt ℝ
        (fun z : ℝ => (1 / (4 * α)) * Real.sin (2 * θ) * Work.Elliptic.L12 g z) z₀ :=
      (differentiableAt_const _).mul (hL12 z₀ hz₀).differentiableAt
    have h := uopi_deriv_eq_zero_of_sub_of_not (fun z : ℝ => |z - z₀|)
      (fun z : ℝ => (1 / (4 * α)) * Real.sin (2 * θ) * Work.Elliptic.L12 g z) hB
      (uopi_not_differentiableAt_abs_sub z₀)
    simpa only [Work.Spaces.pz, Work.Elliptic.EllResid, hΦg] using h
  -- ## the identity would force `5·Ḡ + (3/4)·F_* = 0`
  have hkey : 5 * Work.Elliptic.Gbar α g z₀ + (3 / 4) * Work.Elliptic.Fstar g z₀ = 0 :=
    (uopi_iff_reduction α g Φg z₀ θ hσ hX hΞ).mp (H Φg z₀ θ hz₀ hθpos hθlt)
  -- ## which contradicts the first-order relation of `Ḡ`
  have hrel := CexK5.Gbar_deriv_rel α g hα hL12
    (fun z hz => (((hFsm 1).differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hz)).hasDerivAt) hJ z₀ hz₀
  rw [← hGbarDeriv.deriv] at hrel
  have hzero : α * (z₀ * deriv (Work.Elliptic.Gbar α g) z₀) = 0 := by linarith
  have hαne : α ≠ 0 := ne_of_gt hα
  have hz₀ne : z₀ ≠ 0 := ne_of_gt hz₀
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd h hαne
  · rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hz₀ne
    · exact h'

end Work.FTS.EllSol.PkgK5

namespace Work.FTS.EllSol.PkgK5

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- **The repaired identity (proved).**  The requested statement becomes true as soon as the
`z`-slices of `Φg` are differentiable — here supplied by `SmoothOpen Φg`; the shape of the
proof is precisely `D_z X = D_z Ξ + sin 2θ · D_z Ḡ` followed by the tree's proved
`CexK5.Gbar_deriv_rel`.  (`α ≤ 1` is an artefact of
`Cert.Jfun_hasDerivAt_of_Fstar`; the identity itself is true for every `α > 0`.) -/
theorem uopPointwiseIdentity_repaired (α : ℝ) (g Φg : Work.FTS.Galerkin.Fn) (hα : 0 < α)
    (hα1 : α ≤ 1) (hC : Work.FTS.EllSol.ClassC α g)
    (hΦg : Work.FTS.EllipticEst.SmoothOpen Φg) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.EllipticEst.Uop α (Work.Elliptic.EllResid α g Φg) z θ / Real.sin (2 * θ)
        = -3 * (Work.FTS.EllSol.ellShift α g Φg z θ / Real.sin (2 * θ))
          - α * (Work.Spaces.Dz (Work.FTS.EllSol.ellShift α g Φg) z θ / Real.sin (2 * θ))
          - (2 * Work.Elliptic.Gbar α g z + (3 / 4) * Work.Elliptic.Fstar g z) := by
  intro z θ hz hθ hθ2
  have hσ : Real.sin (2 * θ) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθ2, Real.pi_pos]))
  -- ## the analytic facts of `ClassC`
  have hFsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar g) (Set.Ioi 0) := hC.fsm
  have hFint : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar g r / r)
      (Set.Ioi 0) :=
    Work.FTS.EllipticEst.FstarDivOpen.fstar_div_integrable_of_smoothOpen α 7 g hC.reg hC.mem
  have hL12 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.L12 g) (-(3 * Work.Elliptic.Fstar g z / z)) z :=
    Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts g hFsm hFint
  have hJ : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' => ∫ s in (0 : ℝ)..z', s ^ ((5 - α) / α) * Work.Elliptic.Fstar g s)
        (z ^ ((5 - α) / α) * Work.Elliptic.Fstar g z) z :=
    Work.FTS.EllipticEst.Cert.Jfun_hasDerivAt_of_Fstar α g hFsm hFint hα hα1
  have hJz : HasDerivAt (Work.Elliptic.Jfun α g)
      (z ^ ((5 - α) / α) * Work.Elliptic.Fstar g z) z := by
    have h := hJ z hz
    have hfun : (fun z' => ∫ s in (0 : ℝ)..z',
        s ^ ((5 - α) / α) * Work.Elliptic.Fstar g s) = Work.Elliptic.Jfun α g := rfl
    rw [hfun] at h
    exact h
  have hGbarDeriv : HasDerivAt (Work.Elliptic.Gbar α g) (Work.Elliptic.DGbar α g z) z :=
    CexK5.hasDerivAt_Gbar_DGbar α g hz hJz
  have hGbar_diff : DifferentiableAt ℝ (Work.Elliptic.Gbar α g) z := hGbarDeriv.differentiableAt
  have hGstar_diff : DifferentiableAt ℝ (Work.Elliptic.Gstar α g) z := by
    have h1 : Work.Elliptic.Gstar α g
        = fun z' : ℝ => (-(1 / (4 * α))) * Work.Elliptic.L12 g z' := rfl
    rw [h1]
    exact (differentiableAt_const _).mul (hL12 z hz).differentiableAt
  have hGsing_diff : DifferentiableAt ℝ (Work.Elliptic.Gsing α g) z := by
    have h1 : Work.Elliptic.Gsing α g
        = Work.Elliptic.Gstar α g + Work.Elliptic.Gbar α g := rfl
    rw [h1]
    exact hGstar_diff.add hGbar_diff
  have hL12diff : DifferentiableAt ℝ (Work.Elliptic.L12 g) z := (hL12 z hz).differentiableAt
  -- ## the `z`-slice derivatives (this is the step that needs `SmoothOpen Φg`)
  have hΦgs : HasDerivAt (fun z' : ℝ => Φg z' θ) (Work.Spaces.pz Φg z θ) z :=
    hΦg.hasDerivAt_slice ⟨hθ, hθ2⟩ hz
  have hGsingd : HasDerivAt (fun z' : ℝ => Work.Elliptic.Gsing α g z')
      (deriv (Work.Elliptic.Gsing α g) z) z := hGsing_diff.hasDerivAt
  have hXslice : HasDerivAt (fun z' : ℝ => Work.FTS.EllSol.ellShift α g Φg z' θ)
      (Work.Spaces.pz Φg z θ + deriv (Work.Elliptic.Gsing α g) z * Real.sin (2 * θ)) z := by
    have h := hΦgs.add (hGsingd.mul_const (Real.sin (2 * θ)))
    have hfun : ((fun z' : ℝ => Φg z' θ)
        + fun y : ℝ => Work.Elliptic.Gsing α g y * Real.sin (2 * θ))
        = fun z' : ℝ => Work.FTS.EllSol.ellShift α g Φg z' θ := by
      funext z'
      simp only [Pi.add_apply, Work.FTS.EllSol.ellShift]
    rwa [hfun] at h
  have hΞslice : HasDerivAt (fun z' : ℝ => Work.Elliptic.EllResid α g Φg z' θ)
      (Work.Spaces.pz Φg z θ
        - (1 / (4 * α)) * Real.sin (2 * θ) * deriv (Work.Elliptic.L12 g) z) z := by
    have h := hΦgs.sub (hL12diff.hasDerivAt.const_mul ((1 / (4 * α)) * Real.sin (2 * θ)))
    have hfun : ((fun z' : ℝ => Φg z' θ)
        - fun y : ℝ => (1 / (4 * α)) * Real.sin (2 * θ) * Work.Elliptic.L12 g y)
        = fun z' : ℝ => Work.Elliptic.EllResid α g Φg z' θ := by
      funext z'
      simp only [Pi.sub_apply, Work.Elliptic.EllResid]
    rwa [hfun] at h
  have hpzX : Work.Spaces.pz (Work.FTS.EllSol.ellShift α g Φg) z θ
      = Work.Spaces.pz Φg z θ + deriv (Work.Elliptic.Gsing α g) z * Real.sin (2 * θ) := by
    simpa only [Work.Spaces.pz] using hXslice.deriv
  have hpzΞ : Work.Spaces.pz (Work.Elliptic.EllResid α g Φg) z θ
      = Work.Spaces.pz Φg z θ
        - (1 / (4 * α)) * Real.sin (2 * θ) * deriv (Work.Elliptic.L12 g) z := by
    simpa only [Work.Spaces.pz] using hΞslice.deriv
  -- ## `∂_z Ḡ = ∂_z Gsing + (1/(4α))·∂_z L₁₂` (the two singular parts add up to `Ḡ`)
  have hGbar_deriv : deriv (Work.Elliptic.Gbar α g) z
      = deriv (Work.Elliptic.Gsing α g) z
        + (1 / (4 * α)) * deriv (Work.Elliptic.L12 g) z := by
    have h := hGsingd.add (hL12diff.hasDerivAt.const_mul (1 / (4 * α)))
    have hfun : (Work.Elliptic.Gsing α g
        + fun y : ℝ => (1 / (4 * α)) * Work.Elliptic.L12 g y) = Work.Elliptic.Gbar α g := by
      funext y
      simp only [Pi.add_apply, Work.Elliptic.Gsing, Work.Elliptic.Gstar]
      ring
    rw [hfun] at h
    exact h.deriv
  -- ## the key relation between the two `pz`'s
  have hpz_rel : Work.Spaces.pz (Work.FTS.EllSol.ellShift α g Φg) z θ
      = Work.Spaces.pz (Work.Elliptic.EllResid α g Φg) z θ
        + Real.sin (2 * θ) * deriv (Work.Elliptic.Gbar α g) z := by
    rw [hpzX, hpzΞ, hGbar_deriv]
    ring
  -- ## the scaled identity
  have hrel := CexK5.Gbar_deriv_rel α g hα hL12
    (fun z hz => (((hFsm 1).differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hz)).hasDerivAt) hJ z hz
  rw [← hGbarDeriv.deriv] at hrel
  have hscaled : Work.FTS.EllipticEst.Uop α (Work.Elliptic.EllResid α g Φg) z θ
      = -3 * Work.FTS.EllSol.ellShift α g Φg z θ
        - α * Work.Spaces.Dz (Work.FTS.EllSol.ellShift α g Φg) z θ
        - Real.sin (2 * θ) * (2 * Work.Elliptic.Gbar α g z
            + (3 / 4) * Work.Elliptic.Fstar g z) := by
    have hU : Work.FTS.EllipticEst.Uop α (Work.Elliptic.EllResid α g Φg) z θ
        = -3 * Work.Elliptic.EllResid α g Φg z θ
          - α * Work.Spaces.Dz (Work.Elliptic.EllResid α g Φg) z θ := by
      simp only [Work.FTS.EllipticEst.Uop, Work.Spaces.Dz]
      ring
    have hXeq : Work.FTS.EllSol.ellShift α g Φg z θ
        = Work.Elliptic.EllResid α g Φg z θ
          + Work.Elliptic.Gbar α g z * Real.sin (2 * θ) := by
      simp only [Work.FTS.EllSol.ellShift, Work.Elliptic.EllResid, Work.Elliptic.Gsing,
        Work.Elliptic.Gstar]
      ring
    have hDzX : Work.Spaces.Dz (Work.FTS.EllSol.ellShift α g Φg) z θ
        = Work.Spaces.Dz (Work.Elliptic.EllResid α g Φg) z θ
          + Real.sin (2 * θ) * z * deriv (Work.Elliptic.Gbar α g) z := by
      simp only [Work.Spaces.Dz, hpz_rel]
      ring
    rw [hU, hDzX, hXeq]
    have hσrel : Real.sin (2 * θ) * (α * (z * deriv (Work.Elliptic.Gbar α g) z))
        = Real.sin (2 * θ) * (-5 * Work.Elliptic.Gbar α g z
            - (3 / 4) * Work.Elliptic.Fstar g z) := by rw [hrel]
    linear_combination hσrel
  -- ## divide by `sin 2θ`
  rw [hscaled]
  field_simp

end Work.FTS.EllSol.PkgK5
