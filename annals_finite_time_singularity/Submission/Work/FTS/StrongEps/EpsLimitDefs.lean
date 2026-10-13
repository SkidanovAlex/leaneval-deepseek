/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsLimitDefs.lean` — the **vocabulary of E5**
#
# Split out of `EpsLimit.lean` so that the E5 chapters (which all mention `EllLimOK`,
# `MuLamOK`, `EpsLimPkg` or `rhsFun`) can be imported by `EpsLimit.lean` itself, where the
# theorem `exists_limH` is proved.  `EpsLimit.lean` re-exports everything here.
#
# `Submission/Work/FTS/StrongEps/EpsLimit.lean` — **E5**: the `ε`-limit of the scheme

`StrongEps/Basic.lean` defines the log-coordinate mollifier `Jeps`, the family `Jfam`, the
`ε`-scheme `IsEpsSol` and its uniform bound `EpsUniform` (verbatim from the lead's statement file
`FTS_HARD_STMTS.lean.txt`).  This module contains the *limit* chapter of the design
(`FTS_HARD_DESIGN.md` (B), **E5**):

* `rhsFun` — the right-hand side of the *limiting* equation, i.e. the scheme's right-hand side
  with the mollifier removed: `dynLin α g τ + dynRHS α (PsiCan Φs E g) g τ`;
* **`EpsLimPkg α C₀ K T Φs E g₀ g`** — everything the limit is known to satisfy *on `[0,T]`*:
  the datum, the positivised elliptic law, the equation, the joint `C¹`-regularity in `(z,θ,τ)`,
  `C⁴` in space, continuity in `τ`, the `ℋ⁴`-membership and the `ℋ⁴`/`ℋ⁶`-bounds, the vanishing on the
  angular boundaries and the uniform `ℋ³`-bound on `∂_τg` (the `dbd` clause of `RegPkgMin`);
* **`EpsUniform.exists_lim`** (E5) — there is a constant `Cd` (the uniform `ℋ³`-bound on the
  fake-time derivative, obtained in the proof from the level-three estimate `S6` for the mollified
  right-hand side followed by lower semicontinuity) such that for every `T > 0` the `ε`-solutions
  have a limit satisfying `EpsLimPkg`, and the limit is *unique* in that class (this is what makes
  the gluing of `Assembly.lean` possible).

**Status.**  `EpsUniform.exists_lim` is the one remaining analytic input of the whole
`ε`-route: it is the Cauchy/limit step of the design (`E5`, 3–4K lines) together with the
level-three estimate `S6`.  Everything else of the `StrongEps` area is proved; the glue
`E6` = `global_strong2` is `Submission/Work/FTS/StrongEps/Assembly.lean`.

**Read `NOTES_session10.md` first** (it supersedes `NOTES_session9.md` §2/§8 as the working
document).  Its content, in headline form:

* `exists_limH`'s **statement obstruction is now machine-checked** and repaired:
  `EpsLimNecessary.ExistsLimH.datum_vanish` proves `ExistsLimH α C₀ K Φs E g₀ → g₀ z 0 = 0 ∧
  g₀ z (π/2) = 0` for `z ≥ 0` (and `datum_vanish_of_regPkgMin` gives the same from the *target's*
  conclusion).  The repair — one added conjunct of `EpsUniformMem`, the datum's boundary vanishing
  — is **applied** on disk (see `NOTES_session10.md` §1/§2); the `init`/`vanish` clauses of
  `EpsLimPkg` are then free, via the boundary clamp `EpsE5Facts.clampFam`.
* The clauses of `EpsLimPkg` that need no further input are proved and live in
  `EpsE5Facts.lean` (`EpsLimBd6`, `EpsLimBd4`, `EpsLimMem4`, and the whole `clampFam` API) and
  `EpsLimCont.lean` (`cont`), with `EpsLimVolterraP` (`eqT`), `EpsGdotThirdHP` (`dbd` for a single
  `ε`-solution) and `EpsLimDbd_of_Icc` (`dbd` at a limit) on the shelf.
* What remains is a *list of chapters*, not an interface question: `NOTES_session10.md` §3 lists
  them as G1 (regularity of the `ε`-solutions' slices), G2 (per-`z` level-four bound),
  G4 (the pointwise identification — the crux; its mollifier half is `L12_Jeps_sub_le`), G5
  (`H6Adm`/`Ell6Ctx` at the limit slice, feeding `EpsLimDbd_of_Icc`), G6 (uniqueness) and
  G7 (the `hbdd` sup bound, reduced by `EpsRHSP_slotSup` to a sup + `ℋ⁴` bound on `epsWP`);
  §4 is the clause-by-clause assembly recipe.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongEps.LimApproxSE
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongGlobal.dynRHS_congr
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.VocabO2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice dynLin dynRHS gdot IsDynEqOn IsDynGSolWith)

set_option autoImplicit false

/-! ## The right-hand side of the limiting equation -/

/-- The right-hand side of the limiting equation at the fake time `τ`: the scheme's right-hand
side with the mollifier removed,
`dynLin α g τ + dynRHS α (PsiCan Φs E g) g τ`. -/
def rhsFun (α : ℝ) (Φs : Fn) (E : Fn → Fn) (g : Fam) (τ : ℝ) : Fn :=
  fun z θ => dynLin α g τ z θ + dynRHS α (Work.FTS.Nonlin.PsiCan Φs E g) g τ z θ

/-- `rhsFun` depends on the family only through its slice. -/
theorem rhsFun_congr {α : ℝ} {Φs : Fn} {E : Fn → Fn} {g g' : Fam} {τ : ℝ}
    (h : slice g τ = slice g' τ) : rhsFun α Φs E g τ = rhsFun α Φs E g' τ := by
  funext z θ
  simp only [rhsFun, congrFun (congrFun (Work.FTS.StrongGlobal.dynLin_congr h) z) θ,
    congrFun (congrFun (Work.FTS.StrongGlobal.dynRHS_congr h) z) θ]

/-! ## The limit package on `[0,T]` -/

/-- **The limit package on `[0,T]`** — the conclusion of E5, and the input of the assembly
(`E6`).  Every clause is the restriction to `[0,T]` of the corresponding clause of
`Work.FTS.StrongGlobal.RegPkgMin` or of `IsDynGSolWith`, except that the `ℋ⁶`-bound of the slices is
carried along (it is what makes the extraction work and what identifies the limit). -/
structure EpsLimPkg (α C₀ K Cd T : ℝ) (Φs : Fn) (E : Fn → Fn) (g₀ : Fn) (g : Fam) : Prop where
  /-- the datum is attained at `τ = 0`. -/
  init : ∀ z θ, g z θ 0 = g₀ z θ
  /-- the positivised elliptic law at every `τ ∈ [0,T]`. -/
  law : ∀ τ, 0 ≤ τ → τ ≤ T →
    Work.FTS.StrongGlobal.IsBslSolPos α (Work.Construction.Ftau α g τ)
      (slice (Work.FTS.Nonlin.PsiCan Φs E g) τ)
  /-- the limiting equation at every `τ ∈ [0,T]`, within `[0,T]`. -/
  eqT : ∀ τ, 0 ≤ τ → τ ≤ T → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
    HasDerivWithinAt (fun s => g z θ s) (rhsFun α Φs E g τ z θ) (Set.Icc 0 T) τ
  /-- joint `C¹`-regularity on the interior of the quadrant, for every `τ ∈ (0,T)`.

  **Domain note (E5 assembly, session 18).**  The clause was originally stated for *all*
  `τ > 0` (`Set.Ioi 0` in the last slot).  That is not producible from the extraction: the
  limit curve `F` is an arbitrary `Classical.choose` of an existence statement, hence its values
  for `τ > T` are junk, and the extension of `F` past `T` would need the *spatial* `C¹` of the
  horizon value `rhsFun α Φs E g T` (i.e. elliptic regularity at the limit slice).  The
  horizon-restricted domain is exactly what the only consumer (`Assembly.lean`) uses: there the
  `c1`-clause is read at a point `p` with `0 < p.2.2 < Tn (pidx p.2.2)`, i.e. strictly inside the
  horizon of the covering piece.  Nothing is lost: `RegPkgMin.c1` (unbounded in `τ`) is obtained
  in `Assembly.global_strong2_of_lim` by glueing the per-piece clauses. -/
  c1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
    (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioo 0 T)
  /-- `C⁴` in space at every `τ ∈ [0,T]`. -/
  c4 : ∀ τ, 0 ≤ τ → τ ≤ T →
    ContDiffOn ℝ 4 (Function.uncurry (slice g τ)) Work.FTS.EllipticEst.Q0
  /-- continuity in the fake time up to `τ = 0`, on the open quadrant.

  **Domain note (E5 assembly, session 18).**  As for `c1`, the clause is restricted to the horizon
  `Icc 0 T`: the limit curve `F` is the arbitrary `Classical.choose` of an existence statement, so
  its values for `τ > T` are junk and nothing constrains them (the reviewer of
  `E5G/EpsLimPkg_of_horizon` produced an explicit counterexample).  Every producer
  (`E5Clauses.E5_cont`, via `EpsLimCont`) already concludes the `Icc 0 T`-form, and the only
  consumer (`Assembly.global_strong2_of_lim`) reads the clause at a point `τ ∈ Icc 0 (Tn (pidx τ))`
  and then extends the within-set by `ContinuousWithinAt.mono_of_mem_nhdsWithin`; the glued family's
  global continuity (needed for `RegPkgMin.cont`, which is on `Ici 0`) comes from that stitching. -/
  cont : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
    ContinuousOn (fun τ => g z θ τ) (Set.Icc 0 T)
  /-- `ℋ⁴`-membership at every `τ ∈ [0,T]`. -/
  mem4 : ∀ τ, 0 ≤ τ → τ ≤ T → Work.Spaces.HkMem α 4 (slice g τ)
  /-- the uniform `ℋ⁴`-bound. -/
  bd4 : ∀ τ, 0 ≤ τ → τ ≤ T → Work.FTS.Nonlin.Xn α (slice g τ) ≤ C₀ * α ^ 2
  /-- a uniform `ℋ⁶`-bound *carried through from the `ε`-approximants* (for the construction it is
  `K e^{KT}`, the exponential shape of `EpsUniform`).  It is never *re-derived* on the limit slice
  (no `Xn6`/`IP6` energy estimate is applied to a limit); it is the bound of the approximating
  sequence, transferred to the limit by lower semicontinuity.  It is what makes the *uniqueness*
  clause of `EpsUniformMem.exists_lim` work (the `ℋ⁵`-term of the difference estimate is controlled
  by it), and `Assembly.lean` does not read it at all. -/
  bd6 : ∃ B, ∀ τ, 0 ≤ τ → τ ≤ T → Work.FTS.StrongGlobal.Xn6 α (slice g τ) ≤ B
  /-- vanishing on the two angular boundaries, for `z ≥ 0`. -/
  vanish : ∀ τ, 0 ≤ τ → τ ≤ T → ∀ z, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0
  /-- the uniform `ℋ³`-bound on the fake-time derivative, for `0 < τ < T`, with the constant
  `Cd` *shared* by all the pieces (this is what makes the glued family of `Assembly.lean` satisfy
  the `dbd`-clause of `RegPkgMin`).  The bound is stated for `τ < T` and not for `τ ≤ T`: at
  `τ = T` the within-`[0,T]` derivative of `eqT` does not determine the honest derivative
  `gdot g τ = deriv (fun s => g z θ s) τ` (which sees `s > T` as well), so the endpoint instance
  is *not* derivable from the other clauses.  Nothing is lost: `Assembly.lean` reads the clause
  only at fake times `τ < Tn (pidx τ)` (`lt_Tn_pidx`), i.e. strictly inside the covering piece. -/
  dbd : ∀ τ, 0 < τ → τ < T →
    Work.Spaces.HkMem α 3 (gdot g τ) ∧ Work.Spaces.HkNorm α 3 (gdot g τ) ≤ Cd
  /-- **The G2 approximation clause** (`FinalV2.LimApprox`, in the horizon-restricted form of
  `LimApproxSE.LimApproxOn`): on every sub-horizon `[0,T']` the family `g` is the limit of
  class-`C` families with matching `ℋ⁴`-bounds, a uniform `ℋ⁶`-bound, a uniform `ℋ⁴`-Lipschitz
  modulus in `τ`, `C⁴`-jet convergence on `Qd` and convergence of the modulation.  It is glued
  across the covering pieces of `Assembly.lean` exactly like `dbd` — but with *one* piece covering
  the whole of `[0,T]` (see `Assembly.LimApproxOn_glued`). -/
  limApprox : ∀ T', 0 < T' → T' ≤ T → LimApproxOn α C₀ T' Φs E g

theorem EpsLimPkg.init' {α C₀ K Cd T : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn} {g : Fam}
    (h : EpsLimPkg α C₀ K Cd T Φs E g₀ g) : ∀ z θ, g z θ 0 = g₀ z θ := h.init

theorem EpsLimPkg.eqT' {α C₀ K Cd T : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn} {g : Fam}
    (h : EpsLimPkg α C₀ K Cd T Φs E g₀ g) :
    ∀ τ, 0 ≤ τ → τ ≤ T → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      HasDerivWithinAt (fun s => g z θ s) (rhsFun α Φs E g τ z θ) (Set.Icc 0 T) τ := h.eqT

/-- The package restricts to shorter intervals: the `C¹`-, `cont`- and `vanish`-clauses are
interval-independent, and the remaining ones restrict by `HasDerivWithinAt.mono` and monotonicity
of the bound. -/
theorem EpsLimPkg.mono {α C₀ K Cd T T' : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn} {g : Fam}
    (hT : T' ≤ T) (h : EpsLimPkg α C₀ K Cd T Φs E g₀ g) (hT0 : 0 ≤ T') :
    EpsLimPkg α C₀ K Cd T' Φs E g₀ g :=
  { init := h.init
    law := fun τ h1 h2 => h.law τ h1 (le_trans h2 hT)
    eqT := fun τ h1 h2 z θ hz =>
      (h.eqT τ h1 (le_trans h2 hT) z θ hz).mono (Set.Icc_subset_Icc le_rfl hT)
    c1 := h.c1.mono (by
      intro q hq
      simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hq ⊢
      exact ⟨hq.1, hq.2.1, hq.2.2.1, lt_of_lt_of_le hq.2.2.2 hT⟩)
    c4 := fun τ h1 h2 => h.c4 τ h1 (le_trans h2 hT)
    cont := fun z θ hz => (h.cont z θ hz).mono (Set.Icc_subset_Icc le_rfl hT)
    mem4 := fun τ h1 h2 => h.mem4 τ h1 (le_trans h2 hT)
    bd4 := fun τ h1 h2 => h.bd4 τ h1 (le_trans h2 hT)
    bd6 := by
      obtain ⟨B, hB⟩ := h.bd6
      exact ⟨B, fun τ h1 h2 => hB τ h1 (le_trans h2 hT)⟩
    vanish := fun τ h1 h2 => h.vanish τ h1 (le_trans h2 hT)
    dbd := fun τ h1 h2 => h.dbd τ h1 (lt_of_lt_of_le h2 hT)
    limApprox := fun T' h1 h2 => h.limApprox T' h1 (le_trans h2 hT) }

/-! ## E5 and the level-three estimate of the limiting right-hand side -/

/-- **E5 (ruling v2), the conclusion**: for every horizon `T` a constant `Cd` (chosen *after* `T`)
and a limit package on `[0,T]`, unique against packages with *any* constant. -/
def ExistsLimH (α C₀ K : ℝ) (Φs : Fn) (E : Fn → Fn) (g₀ : Fn) : Prop :=
  ∀ T : ℝ, 0 < T → ∃ Cd : ℝ, 0 < Cd ∧ ∃ g : Fam, EpsLimPkg α C₀ K Cd T Φs E g₀ g ∧
    ∀ (Cd' : ℝ) (g' : Fam), EpsLimPkg α C₀ K Cd' T Φs E g₀ g' →
      ∀ z θ τ, 0 ≤ τ → τ ≤ T → g' z θ τ = g z θ τ

/-- **`E` passes to limits of bounded class-C sequences** (ruling v2).  Off the class C a linear
`E` is unconstrained (Hamel extension), so `EpsLimPkg.law`/`eqT` at a limit slice — which is not
in class C — need this.  Producer: EllSol (construction A6, "E extends to limits by boundedness"). -/
def EllLimOK (α : ℝ) (E : Fn → Fn) : Prop :=
  ∀ (fn : ℕ → Fn) (f : Fn) (B : ℝ),
    (∀ n, Work.FTS.ClassC.ClassC α (fn n)) →
    (∀ n, Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ B) →
    ContDiffOn ℝ 4 (Function.uncurry f) Work.Construction.Qd →
    (∀ j i : ℕ, j + i ≤ 4 → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Tendsto (fun n => Work.Spaces.mixed j i (fn n) z θ) atTop
        (𝓝 (Work.Spaces.mixed j i f z θ))) →
    Work.FTS.StrongGlobal.IsBslSolPos α f (E f) ∧
    ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Tendsto (fun n => Work.Spaces.mixed j i (E (fn n)) z θ) atTop
        (𝓝 (Work.Spaces.mixed j i (E f) z θ))

/-- **The modulation bounds on class-C profiles of small `ℋ⁴`-size** (the `hμ`/`hlam` inputs of
`EpsLimDbd_aux`, at the mollified slices).  Producer: CoercivityFix. -/
def MuLamOK (α C₀ : ℝ) (Φs : Fn) (E : Fn → Fn) : Prop :=
  ∀ f : Fn, Work.FTS.ClassC.ClassC α f → Work.FTS.Nonlin.Xn α f ≤ C₀ * α ^ 2 →
    |Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E (fun z θ _ => f z θ))
        (fun z θ _ => f z θ) 0| ≤ 1 / 2 ∧
    |Work.FTS.Galerkin.lamDyn α (Work.FTS.Nonlin.PsiCan Φs E (fun z θ _ => f z θ))
        (fun z θ _ => f z θ) 0| ≤ 1

end Work.FTS.StrongEps
