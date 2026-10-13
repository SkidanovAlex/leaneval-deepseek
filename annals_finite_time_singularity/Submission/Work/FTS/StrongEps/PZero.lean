/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/PZero.lean` — the projection `P₀` of the design's §(B)

The lead's design (`FTS_HARD_DESIGN.md`, §(B)) specifies the scheme

  `∂_τ g = P₀ J_ε [𝓛 + 𝓡] (P₀ J_ε g)`,   `P₀ f = f − L₁₂(f)(0) · b`,

*so that `L₁₂(g)(0) = 0` is preserved* — which is exactly the `l12` clause of the elliptic layer's
source class `Work.FTS.ClassC.ClassC` and of the level-six context `StrongPersist.H6Adm` (both
consumed by `EpsDatum`, `L6Ctx`, `hEll`, `EllLimOK`, `MuLamOK`).  The statement file
`FTS_HARD_STMTS.lean.txt` omits the projection `P₀`, and without it the clause is **false** along
the scheme: the log-coordinate mollifier `J_ε` is a *two-dimensional* convolution, whose angular
half is a multiplicative shift of `tan θ`, and the angular weight `K(θ)dθ` of `L₁₂` is not invariant
under that shift.  See `NOTES_Pzero.md` for the elementary mechanism and for the (independent)
counterexample that a prover produced for the un-projected `EpsLocal`.

This module fixes the *vocabulary* of the repair: the normalising constant `pzNorm`, the
correction profile `bump` (the explicit smooth bump of `BumpDefs.lean`, supported in
`[1/2,1] × [π/4,3π/8] ⊂ Q0`), and the projection `Pz`.  The analytic lemmas about it live in
`Submission/Work/FTS/StrongEps/PZeroAux/`:

* `pzNorm_pos` — `0 < pzNorm` (the `L₁₂`-integral of the bump is strictly positive);
* `L12dens_integrable_of_hon` — the `L₁₂`-density of an honest profile is integrable, so that
  `L₁₂` is *linear* there (this is the only place the junk-integral convention matters);
* `Pz_l12` — `L₁₂(Pz f)(0) = 0`;
* `softClass_Pz` / `classC_Pz` — the class clauses of `Pz f` (the projection keeps `ClassC`);
* `hkNorm_Pz_le` — `‖Pz f‖_{ℋᵏ} ≤ C‖f‖_{ℋᵏ}` with a *fixed* constant `C` (via the proved zero-mode
  bound `OpenPkg.l12zero_field`, `|L₁₂ f 0| ≤ 3 |f|_{ℋ⁴}`).

Everything below is `sorry`-free.
-/
import Mathlib.Algebra.GroupWithZero.Action.Pi
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.BumpDefs
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## The normalising constant and the projection -/

/-- The normalising constant of `P₀`: the `L₁₂`-value of the correction profile `bump` at `z = 0`.
It is strictly positive (`pzNorm_pos`, `PZeroAux/PzNormPos.lean`). -/
noncomputable def pzNorm : ℝ := Work.Construction.L12 bump 0

/-- **The projection `P₀` of the design's §(B)**: `P₀ f = f − (L₁₂ f 0 / L₁₂(bump)(0)) • bump`.

Its defining property is `L₁₂(P₀ f)(0) = 0` (`Pz_l12`), which is what the `l12` clause of
`ClassC`/`H6Adm` needs; `P₀` is the identity on profiles with `L₁₂ f 0 = 0` (`Pz_self_of_l12`). -/
noncomputable def Pz (f : Fn) : Fn :=
  f - (Work.Construction.L12 f 0 / pzNorm) • bump

/-- The pointwise form of `Pz`. -/
theorem Pz_apply (f : Fn) (z θ : ℝ) :
    Pz f z θ = f z θ - (Work.Construction.L12 f 0 / pzNorm) * bump z θ := by
  simp only [Pz, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

/-- `P₀` is the identity on the profiles whose `L₁₂`-zero-mode vanishes — the reason the projection
is invisible on the *limiting* right-hand side (the μ̄-identity) and on class-`C` profiles. -/
theorem Pz_self_of_l12 {f : Fn} (h : Work.Construction.L12 f 0 = 0) : Pz f = f := by
  simp only [Pz, h, zero_div, zero_smul, sub_zero]

/-- The projection annihilates the correction profile itself. -/
theorem Pz_bump (hpz : pzNorm ≠ 0) : Pz bump = 0 := by
  have h : Work.Construction.L12 bump 0 / pzNorm = 1 := by
    rw [show Work.Construction.L12 bump 0 = pzNorm from rfl, div_self hpz]
  rw [Pz, h, one_smul, sub_self]

/-- Two profiles with the same `L₁₂`-zero-mode differ by the same amount after projection. -/
theorem Pz_sub_eq_of_l12_eq {f g : Fn} (h : Work.Construction.L12 f 0 = Work.Construction.L12 g 0) :
    Pz f - Pz g = f - g := by
  funext z θ
  simp only [Pi.sub_apply, Pz_apply, h]
  ring

/-- The projection is *injective* modulo the `L₁₂`-zero-mode: if `Pz f = Pz g` and the two
zero-modes agree, then `f = g`. -/
theorem eq_of_Pz_eq_of_l12_eq {f g : Fn} (hp : Pz f = Pz g)
    (h : Work.Construction.L12 f 0 = Work.Construction.L12 g 0) : f = g := by
  have hsub : f - g = 0 := by
    rw [← Pz_sub_eq_of_l12_eq h, hp, sub_self]
  funext z θ
  have := congrFun (congrFun hsub z) θ
  simpa using sub_eq_zero.mp this

end Work.FTS.StrongEps
