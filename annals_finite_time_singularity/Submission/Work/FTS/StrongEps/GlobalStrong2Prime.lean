/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/GlobalStrong2Prime.lean` — the (4′) producer of `FinalV2.Inputs'`

This is the `StrongEps` producer of the FinalV2 conjunct **(4′)**: `global_strong2` *plus* the
enriched output clause `LimApprox` (`FinalV2/Defs.lean`, G2 of the redesign).  Its type is copied
verbatim from `FinalV2/Producers.global_strong2'` (same opens, same `Sol`/`DynOK'`).

The proof is a two-liner because everything is already assembled:

* `global_strong2` (E6, `Assembly.lean`) now returns, besides `Sol`, the datum, `RegPkgMin` and the
  uniform `ℋ⁴`-bound, also the **G2 approximation clause** `LimApproxSE` — glued inside
  `global_strong2_of_lim` from the `limApprox` field that every `EpsLimPkg` now carries (the
  one-piece argument: for each `T` the piece `g N` with `T ≤ Tn N` covers the whole of `[0,T]`, and
  the uniqueness clause of `ExistsLimH` identifies the glued family with it there);
* `limApproxSE_iff` identifies my local duplicate `LimApproxSE` with the frozen
  `FinalV2.LimApprox` (they have the same body; the duplicate exists only to avoid the import cycle
  `EpsLimit → FinalV2.Defs → Final.Defs → EpsODE → EpsLimit`).

(2026-10-11, C1–C5 ruling: the producer now goes through `exists_limG` →
`global_strong2_of_limG`, see the theorem's docstring.)  The remaining hole was `StrongEps.exists_limH` (E5), which must now also produce the `limApprox`
field — i.e. the class-`C`, `ℋ⁴`-Lipschitz, jet- and modulation-convergence data of the
approximating sequence.  See `NOTES_session9.md` §3 for the statement-level items that E5's proof
needs in addition to its present hypotheses.
-/
import Mathlib.Algebra.Module.Pi
import Mathlib.Basic.NNReal.Defs
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.StrongEps.Assembly
import Submission.Work.FTS.StrongEps.exists_limG

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice IsDynGSolWith)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Physical (PhysClock)
open Work.FTS.Final
open Work.FTS.FinalClock
open Work.FTS.Regularity (pExp)
open Work.FTS.RegPkgGal (extG)

set_option autoImplicit false

/-- **The local duplicate is the frozen clause**: `LimApproxSE` (`LimApproxSE.lean`) and
`FinalV2.LimApprox` have the same body, so the two `Prop`s are equal (the `∀ T > 0` quantifier is
outermost in both; the inner form is `LimApproxOn`). -/
theorem limApproxSE_iff (α C₀ : ℝ) (Φs : Fn) (E : Fn → Fn) (g : Fam) :
    LimApproxSE α C₀ Φs E g ↔ Work.FTS.FinalV2.LimApprox α C₀ Φs E g :=
  Iff.rfl

/-- The StrongEps copy `EllLimOK3` (`EpsLimitDefsG.lean`) IS the frozen FinalV2 clause. -/
theorem ellLimOK3_iff (α : ℝ) (E : Fn → Fn) :
    EllLimOK3 α E ↔ Work.FTS.FinalV2.EllLimOK3 α E := Iff.rfl

/-- **The `StrongEps` producer of conjunct (4′)** — the type is *verbatim* that of
`Work.FTS.FinalV2.Producers.global_strong2'`, which is now defined as this theorem.

curric-46 lead install 2026-10-11 (`cbc/fts_strongeps_c1c5_ruling.md` §5/§7 item 5, review fixes
F2/F5): hypothesis `EllLimOK` → `Work.FTS.FinalV2.EllLimOK3` (C1), α₂ chosen after `C₀, Ce, Cs`
(F5), and the body is E6 (`global_strong2_of_limG`, proved) from the new E5 leaf `exists_limG`
(one global family, no uniqueness). -/
theorem global_strong2'_proved {C₀ Ce Cs : ℝ} : ∃ α₂ : ℝ, 0 < α₂ ∧ ∀ αG ∈ Set.Ioc 0 α₂,
    ∀ {K : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g₀ : Fn},
    Work.FTS.StrongEps.IsSmoothKernel ρ →
    (∀ u : Fn, Work.FTS.ClassC.ClassC αG u →
      Work.FTS.VocabO.EllPkgGo αG Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK αG 6 Ce u (E u)) →
    Work.FTS.FinalV2.EllLimOK3 αG E → StarPkgo2 αG Cs Φs →
    Work.FTS.StrongEps.MuLamOK αG C₀ Φs E →
    Work.FTS.StrongEps.EpsUniformMem αG ρ Φs E g₀ C₀ K →
      ∃ g : Fam, Work.FTS.FinalV2.Sol αG Φs E g ∧ (∀ z θ, g z θ 0 = g₀ z θ) ∧
      Work.FTS.FinalV2.DynOK' αG C₀ Φs E g := by
  obtain ⟨α₂, hα₂, h⟩ := exists_limG (C₀ := C₀) (Ce := Ce) (Cs := Cs)
  refine ⟨α₂, hα₂, ?_⟩
  intro αG hαG K ρ Φs E g₀ hρ hEll hEL3 hstar hml hU
  obtain ⟨g, hSol, hinit, hreg, hXn, hApprox⟩ :=
    global_strong2_of_limG (h αG hαG hρ hEll ((ellLimOK3_iff αG E).mpr hEL3) hstar hml hU)
  exact ⟨g, hSol, hinit, ⟨⟨hreg, hXn⟩, (limApproxSE_iff αG C₀ Φs (⇑E) g).mp hApprox⟩⟩

end Work.FTS.StrongEps
