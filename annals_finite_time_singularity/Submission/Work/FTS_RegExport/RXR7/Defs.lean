/-
# `Work.FTS_RegExport.RXR7.Defs` — the vocabulary of the RX-R7 node

The objects of the R7 block at the sanitised right-Taylor family, under short names, so that the
three delegated lemmas of this node can be stated compactly and readably.

* `GR α g = gS α (tauExt g)` — the sanitised right-Taylor family (the `g`-argument of `R7Block`);
* `ΦR α Φs E g = psiR α Φs E (tauExt g)` — the stream function fed to R7;
* `μR α Φs E g = maxMu (pExp α) (PsiCan Φs E g) g` — the clock of the coefficients;
* `Vz7R`, `Vθ7R`, `cs7R` — the three transport coefficients `Vz7`/`Vθ7`/`cs7` at `(μR, GR, ΦR)`;
* `Prof α g` — the full profile `profFull α (extG (GR α g))`;
* `K7 α Φs E g` — the closed-form right-hand side
  `Vz7ᵣ·D_z(Prof) + Vθ7ᵣ·∂_θ(Prof) + cs7ᵣ·Prof`;
* `R7Slab S` — the slab `(0,∞) × (0,π/2) × [0,S]` of `R7Block.hFjoint`.

Everything is a transparent `abbrev`, so these names are *definitionally equal* to the literal
expressions appearing in `Work.FTS.RegExportIface.R7Block` and in the frozen producer
`Work.FTS.RegExportIface.r7Block`.  (They coincide with the `RXT.GR`, `RXT.ΦR`, `RXT.μR`,
`RXT.VR`, `RXT.cR` of `Work.FTS.RegExportIface.RXT.Leaves`.)
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.RegExportIface.Defs
import Submission.Work.FTS.RegExportIface.RXT.Leaves

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport.RXR7

set_option autoImplicit false

variable {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
  {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}

/-- The sanitised right-Taylor family `gS α (tauExt g)`. -/
abbrev GR (α : ℝ) (g : Work.FTS.Galerkin.Fam) : Work.FTS.Galerkin.Fam :=
  Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)

/-- The stream function `psiR α Φs E (tauExt g)` fed to R7. -/
abbrev ΦR (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam) :
    Work.FTS.Galerkin.Fam :=
  Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)

/-- The clock `maxMu (pExp α) (PsiCan Φs E g) g` of the coefficients. -/
abbrev μR (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam) :
    ℝ → ℝ :=
  Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α) (Work.FTS.Nonlin.PsiCan Φs E g) g

/-- `Vz7` at the sanitised family (`= RXT.VR`). -/
abbrev Vz7R (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam) :
    ℝ → ℝ → ℝ → ℝ :=
  Work.FTS.RegExportIface.Vz7 (Work.FTS.Regularity.pExp α) (μR α Φs E g) (GR α g)
    (ΦR α Φs E g)

/-- `Vθ7` at the sanitised family. -/
abbrev Vθ7R (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam) :
    ℝ → ℝ → ℝ → ℝ :=
  Work.FTS.RegExportIface.Vθ7 (Work.FTS.Regularity.pExp α) (ΦR α Φs E g)

/-- `cs7` at the sanitised family (`= RXT.cR`). -/
abbrev cs7R (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam) :
    ℝ → ℝ → ℝ → ℝ :=
  Work.FTS.RegExportIface.cs7 (Work.FTS.Regularity.pExp α) (μR α Φs E g) (GR α g)
    (ΦR α Φs E g)

/-- The full profile of the R7 block: `profFull α (extG (GR α g))`. -/
abbrev Prof (α : ℝ) (g : Work.FTS.Galerkin.Fam) : ℝ → ℝ → ℝ → ℝ :=
  fun z θ τ => Work.FTS.Regularity.profFull α (Work.FTS.RegPkgGal.extG (GR α g)) z θ τ

/-- The closed-form right-hand side `Vz7ᵣ·D_z(Prof) + Vθ7ᵣ·∂_θ(Prof) + cs7ᵣ·Prof` of the
transport form of the profile equation (negated in `R7Block.hEq`). -/
abbrev K7 (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam) :
    ℝ → ℝ → ℝ → ℝ :=
  fun z θ τ =>
    Vz7R α Φs E g z θ τ * Work.Spaces.Dz (fun z θ => Prof α g z θ τ) z θ
      + Vθ7R α Φs E g z θ τ * Work.Spaces.pth (fun z θ => Prof α g z θ τ) z θ
      + cs7R α Φs E g z θ τ * Prof α g z θ τ

/-- The slab `(0,∞) × (0,π/2) × [0,S]` of `R7Block.hFjoint`/`hVjoint`/`hcscont`. -/
abbrev R7Slab (S : ℝ) : Set (ℝ × ℝ × ℝ) :=
  Set.prod (Set.Ioi (0 : ℝ))
    (Set.prod (Set.Ioo (0 : ℝ) (Real.pi / 2)) (Set.Icc (0 : ℝ) S))

end Work.FTS_RegExport.RXR7
