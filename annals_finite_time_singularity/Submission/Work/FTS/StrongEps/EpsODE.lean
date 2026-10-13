/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsODE.lean` — **E2**, **E3**, **E4**: the `ε`-scheme

The three existence/estimate items of the `ε`-route of `FTS_HARD_DESIGN.md` (B) that come *before*
the limit `E5`:

* **`EpsAprioriBdd`** — the a-priori bound of the scheme (the hypothesis under which the scheme is
  known to stay in its small ball);
* **E2**, `IsEpsSol.exists_of_apriori` — Picard–Lindelöf in the weighted space `X` for the
  (nonlocal, mollified) right-hand side `J_ε[𝓛 + 𝓡](J_ε ·)`, plus the continuation argument that
  turns the a-priori bound into existence on the whole `[0,T]`;
* **E3**, `EpsSol_HkSq_deriv_le` — the `ε`-energy inequality: along an `ε`-solution whose
  *mollified* slices are of `ℋ⁴`-size `≤ C₀α²`, the level-six energy `e(τ) = |g(τ)|²_{ℋ⁶}`
  satisfies the one-sided differential inequality `e′ ≤ Λ(1 + e)`, with `Λ` depending only on
  `α, C₀` (the level-four version of `S4` plus the commutator term `Cε‖g‖_{ℋ⁵}‖g‖_{ℋ⁴}`, which is
  what makes the constant uniform in `ε`); Grönwall then gives the uniform `ℋ⁶`-bound;
* **E4**, `EpsUniform_of_data` — the bootstrap: for data in the small class, the uniform `ε`-bounds
  `EpsUniform` hold, i.e. the *hypothesis* of `global_strong2` (`Assembly.lean`) is produced.

**Status.**  The three theorems of this module are *stated* here with the interfaces through which
they compose with `IsepsSol`/`EpsUniform` (verbatim from the lead's statement file) and with each
other; they are the remaining analytic work of the scheme (the design's items E2, E3, E4).  `E1`
(the mollifier chapter) is proved in `Basic.lean`/`Kernel.lean`/`Weights.lean`/`Commute.lean` and
its sub-lemmas; see `Submission/Work/FTS/StrongEps/NOTES.md`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsODEDefs
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.EllSol.ClassC
import Submission.Work.FTS.StrongEps.EpsLimitDefs

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

/-! ## E2 — existence for the scheme -/

/-- **E2 — existence for the `ε`-scheme** (Galerkin/energy route).

*The mathematics.*  The scheme is `∂_τ g = J_ε[𝓛(J_ε g) + 𝓡(Ψ(J_ε g), J_ε g)]` in the space of
profiles: one approximates `g` by a finite-dimensional (Galerkin) family, where the projected ODE
is well-posed by Picard–Lindelöf, uses the **ε-level energy inequalities of the projected system**
to obtain a uniform bound in the discretisation parameter, extracts a limit by compactness
(`exists_locUnif_subseq_of_uniform_H6`, `LocUnif/`) and identifies it with an `ε`-solution on
`[0,T]` (no blow-up can occur before `T`: the a-priori bound is exactly what rules it out).

**There is no single-norm Picard.**  The right-hand side contains the unbounded `z∂_z`
(the design's `𝓛_Γ^T`), so `‖rhs u − rhs v‖_{ℋ⁴} ≲ ‖u − v‖_{ℋ⁵}` and no `ℋ⁴`-contraction exists;
and the mollifier does **not** recover the lost derivative `ε`-uniformly — `HkSq_Jeps_succ_le` is
**false** (`NOTES_HkSq_Jeps_succ_le_FALSE.md`), so the `ε^{-1}`-gain route is closed.  See
`NOTES.md` §"third stretch" and §"the `E2` hypothesis".

*Statement note (finding of this stretch).*  `hAp : EpsAprioriBdd` bounds **genuine `ε`-solutions
only**, so it cannot be consumed by the Galerkin argument, which needs the bound for the
*approximants*; that bound must come from the projected system's own energy estimates (the
ε-level analogue of the frozen `Apriori.galerkin_bound_explicit`).  The statement below therefore
records the design's target, and the honest hypothesis (energy data for the projected system) is
the one a proof will need; see `NOTES.md` for the frozen template
(`Work.FTS.Galerkin.{GalerkinODE, Existence, ODEApply, Compactness, Limit}`).

`IsEpsSol` itself is the honest *pointwise* statement (a `HasDerivWithinAt` of the `τ`-slice at
every point of the open quadrant); the limit of the approximants is transferred to it because the
mollified right-hand side is continuous and the identity holds a.e.

**NOT proved, and refuted in this shape.**  On the *un-projected* scheme the class-`C`/`axis`
invariant cannot be preserved: the scheme's right-hand side is *minus* the paper's stationary
residual, so `profRHS(0)(z,θ)/z → −4αΓ(θ)/c < 0`, which violates `axis` for every small `τ > 0`
(`EpsLocalPStar/StatResidual.lean`, `profRHS_eq_neg_dynLHS`, `sorry`-free; see `NOTES_session16.md`
§7).  The `sorry` on the theorem below is therefore a **record of a false statement**, not a gap to
be filled as it stands: the E2a re-design is the projected small-ball shape (`EpsLocalPStar`,
`EpsLocalPSmall`, `StarPkgo2`), and `EpsE2`'s proof (`EpsE2.lean`) is conditional on it. -/
theorem IsEpsSol.local {α ε Ce : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    (hρ : IsSmoothKernel ρ) (hε : 0 < ε)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) :
    ∀ M : ℝ, 0 ≤ M → ∃ δ : ℝ, 0 < δ ∧ ∀ h₀ : Fn, EpsDatum α ρ ε h₀ →
      Work.FTS.StrongGlobal.Xn6 α h₀ ≤ M →
      ∃ h : Fam, IsEpsSol α ρ ε δ Φs E h₀ h ∧ EpsReg α ρ ε δ h ∧
        ∀ τ ∈ Set.Icc 0 δ, Work.FTS.StrongGlobal.Xn6 α (slice h τ) ≤ 2 * M + 1 := by
  sorry

/-! **E2 (continuation)**: restart `IsEpsSol.local` every `δ(M)` and concatenate; the glued
solution stays in `EpsReg`, so `hAp` applies to it and keeps every restart datum at `Xn6 ≤ M`.
-/
-- **E2 is PROVED** — but not here: its proof consumes `EpsGlue` (`EpsGlue.lean`), which imports
-- this module for the very definitions below, so the declaration has been moved to
-- `Submission/Work/FTS/StrongEps/EpsE2.lean` (module `Submission.Work.FTS.StrongEps.EpsE2`),
-- where it carries the same fully qualified name `Work.FTS.StrongEps.IsEpsSol.exists_of_aprioriH`
-- and is `sorry`-free.  Import that module to use E2.  (Importing both would be a name clash.)

/-! *Note (added after the v2 ruling; the hypothesis `0 ≤ M` was missing).*  For `M < 0` the
statement above is **not provable**: `EpsAprioriBddH` then says that every regular `ε`-solution on
`[0,T']` (`0 < T' ≤ T`) has `Xn6 ≤ M < 0`, while `Xn6 = HkNorm ≥ 0`, so `hAp` is equivalent to
"there is no regular `ε`-solution on `[0,T']`" — contradicted by the conclusion, which *asserts*
one exists with `Xn6 ≤ M`.  So `0 ≤ M` is part of the honest statement (in E4 the value is
`M = K e^{KT} ≥ 0`).

**The continuation half is `Submission/Work/FTS/StrongEps/EpsGlue.lean`**
(`Work.FTS.StrongEps.EpsGlue`), which proves exactly this theorem with the conclusion of
`IsEpsSol.local` (item **E2a**) in place of `hρ`/`hε`/`hEll`; instantiating it with the proved E2a
is all that separates this statement from a proof. -/

/-! ## E3 — the `ε`-energy inequality

**E3 is `Submission/Work/FTS/StrongEps/EpsE3.lean`** (`Work.FTS.StrongEps.EpsSol_IP6_energy_deriv_le`,
`sorry`-free), with the ε-level pairing estimate `Work.FTS.StrongEps.EpsSol_IP6_pair_le` as its
analytic core.  It is stated for the energy

  `e(τ) = IP6 1 … 1 α (slice (Jfam ρ ε g) τ) (slice (Jfam ρ ε g) τ)`

of the **mollified** family — the pairing and the profile for which the frozen level-six clause work
(`H6Lin`, `H6Pair`, `L6Ctx`) is stated; `Sq6 = HkSq α 6` and `IP6 1 … 1 · ·` are equivalent on the
`HQo α 6`-class (`IP6_lo_coeffs` one way, `IP6_cs_coeffs` the other).  The theorem's inputs are
exactly (i) the external level-six row `H6Pair`, (ii) the level-six context `L6Ctx` for the
mollified family at every fake time, (iii) the regularity data of the scheme's right-hand side
`smoothness/HkMem α 7 (epsW)/HkMem α 6 (epsRHS)` together with the one commutator-control clause
`ε‖epsW‖₇‖h‖₆ ≤ K7(1+e)`, and (iv) the **ε-level energy identity** `hid` (the `IP6`-analogue of
`StrongPersist.H6EnergyDeriv`, i.e. a statement about `IsEpsSol` and the slot derivatives of the
slices along the flow, not a bound).  The earlier statement below — in `HkSq`-terms, for the
*unmollified* slice, with the a-priori bounds `hCC`/`hbd`/`hmem` and the elliptic hypothesis `hEll`
as inputs — is recovered from the proved form by two further steps, both now spelled out here
because they are *not* part of E3's analytic content:

* the **transfer of the profile**: `HkSq α 6 (slice g τ) ≤ C (1 + IP6 … (J_ε (slice g τ)) (J_ε (slice g τ)))`,
  which is the approximation-of-the-identity `HkSq α 6 (f − J_ε f) ≤ (C₀ε)² HkSq α 7 f`
  (`HkSq_Jeps_sub_le`) together with `(a+b)² ≤ 2a² + 2b²` and `IP6_lo_coeffs`; its hypothesis is the
  same `ε·‖slice g τ‖₇²`-control as `h7`;
* the identification of the *mollified* energy identity with the scheme's (this is where a smooth
  kernel is used: the frozen clauses need `SmoothOpen` of the paired profile, and
  `Jeps_contDiffOn` provides it for `J_ε` of an `L²`-profile).

Both are stated in `NOTES.md` §"the `E3` chain", with the exact clauses they consume. -/

/-! ## E4 — the bootstrap -/

/-- **E4 — the bootstrap: the uniform `ε`-bounds `EpsUniform` hold for data in the small class.**

For `α` small, `ρ` an admissible mollifier, `g₀` in the datum class and `Xn₄(g₀) ≤ α²`,
`Xn₆(g₀) ≤ K₀ α²`, the scheme has, for every `T`, solutions on `[0,T]` for all small `ε` whose
mollified slices are of `ℋ⁴`-size `≤ C₀α²` and whose slices are of `ℋ⁶`-size `≤ K e^{KT}` — i.e.
exactly the hypothesis `EpsUniform` of `global_strong2`.

*The mathematics.*  Fix `T`.  Take `ε` small.  By `E2` the scheme has a solution as soon as the
a-priori bound `EpsAprioriBdd` holds; by `E3` the level-six energy obeys `e′ ≤ Λ(1+e)` and the
level-four energy obeys the `S4` algebra (the same argument as `apriori_strong`, with the extra
commutator term `Cε‖g‖_{ℋ⁵}‖g‖_{ℋ⁴}`, whose contribution is `≤ Cε(1+e)` and can be absorbed for
`ε` small); a barrier/Grönwall argument on the ball
`{|g|_{ℋ⁴} ≤ C₀α², |g|_{ℋ⁶} ≤ K e^{KT}}` closes the a-priori bound for `τ ≤ T`, and the
continuation argument of `E2` then returns the solution on the whole `[0,T]`. -/
theorem EpsUniform_of_data {α C₀ K Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    (hρ : IsSmoothKernel ρ) (hα : 0 < α) (hα1 : α ≤ 1) (hC₀ : 0 < C₀) (hK : 0 ≤ K)
    (hvan : ∀ z, 0 ≤ z → g₀ z 0 = 0 ∧ g₀ z (π / 2) = 0)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hml : MuLamOK α C₀ Φs E)
    (hd : ∀ ε : ℝ, 0 < ε → EpsDatum α ρ ε g₀)
    (h4 : Work.FTS.Nonlin.Xn α g₀ ≤ α ^ 2)
    (h6 : Work.FTS.StrongGlobal.Xn6 α g₀ ≤ K * α ^ 2) :
    EpsUniformMem α ρ Φs E g₀ C₀ K := by
  sorry

end Work.FTS.StrongEps
