/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.MainH` — the retargeted deliverable (route (b) input, conclusion unchanged)

The lead's ruling of 2026-10-11 installs the new hypothesis of `FinalV2.Producers.core1_1a3`:

```
hb : ∃ α₁ > 0, ∀ α, 0 < α → α ≤ α₁ → ∀ g, ClassC α g → ∃ Ψ, EllClassOk 8 α g Ψ
```

(the wire passes `ClassC.ellClassOk_exists_of_classC`), and keeps the conclusion.  This module
proves exactly that conclusion:

```
core1_1a3 : ExistsEllSolC ∨ route (b) ⟹ ∃Ce>0 ∃α₀>0 ∀α≤α₀ ∃E linear,
              (∀ g ∈ ClassC, EllPkgGo ∧ EllPkgK 6) ∧ FinalV2.EllLimOK3
```

## The chain

| step | where |
|---|---|
| route (b) ⇒ a linear selector with `EllClassOk 8` + the two packages | `RulingELF.existsEllSolC8_of_threshold` (proved) |
| the level-`8` class ⇒ the honest fields `HasPkgH` | `RulingELF.ProducerH` = `L1 ∧ L2 ∧ L3` (in flight: `pkgCos_of_ellClassOk`, `pkgMemSqH_of_ellClassOk`, `pkgBoxH_of_ellClassOk`) |
| `HasPkgH` ⇒ obligation 1 | `FatouH.localBoundH_of_hasPkgH`, `FatouH.fatouDataH_of_hasPkgH`, `BoxDataH_of_hasPkgH` (in flight), `ClosedCompact3H_of_bounds_fatou` |
| obligation 2 (jet uniqueness) | `UniqG.smallUniq3G_fts` (proved; package-free) |
| closure ⇒ `EllLimOK3` | `GlueG.exists_ellLimOK3_of_closedG` (proved) |

The box data is now *unconditional* (`BoxDataH/boxDataH_of_hasPkgH` + `SmallAssemblyH.smallBoxDataH`),
so the theorem below has exactly **one** remaining input, `RulingELF.ProducerH` (the producers
`L1`/`L2`/`L3`); `core1_1a3_proved (hb : RouteB)` will be the unconditional form as soon as
`ProducerH` lands (`SmallAssemblyH.smallCompact3H` is already unconditional).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS_EllLimOK.RulingELF
import Submission.Work.FTS_EllLimOK.FatouH
import Submission.Work.FTS_EllLimOK.SmallAssemblyH
import Submission.Work.FTS_EllLimOK.FinalCore
import Submission.Work.FTS_EllLimOK.UniqG.smallUniq3G_fts
import Submission.Work.FTS_EllLimOK.GlueG.exists_ellLimOK3_of_closedG

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_EllLimOK

open Work.FTS.Galerkin (Fn)
open Work.FTS.Regularity (pExp)

set_option autoImplicit false

/-- **Route (b) input.** -/
abbrev RouteB : Prop :=
  ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ α : ℝ, 0 < α → α ≤ α₁ → ∀ g : Fn,
    Work.FTS.ClassC.ClassC α g → ∃ Ψ : Fn, Work.FTS.EllExist.EllClassOk 8 α g Ψ

/-- **The deliverable `core1_1a3` from route (b), modulo the two in-flight inputs.**  The
conclusion is verbatim the conclusion of the lead's `FinalV2.Producers.core1_1a3`; the hypothesis is
the route-(b) input `hb`. -/
theorem core1_1a3_of_routeB (hprod : RulingELF.ProducerH) (hb : RouteB) :
    ∃ Ce : ℝ, 0 < Ce ∧ ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α →
      pExp α ≤ α₀ → ∃ E : Fn →ₗ[ℝ] Fn,
      (∀ g, Work.FTS.ClassC.ClassC (pExp α) g →
        Work.FTS.VocabO.EllPkgGo (pExp α) Ce g (E g) ∧
          Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce g (E g)) ∧
      Work.FTS.FinalV2.EllLimOK3 (pExp α) E := by
  obtain ⟨Ce, hCe, α₀, hα₀, hPkg8⟩ := RulingELF.existsEllSolC8_of_threshold hb
  obtain ⟨αg, hαg, hprod⟩ := hprod
  obtain ⟨αu, hαu, huniq⟩ := Work.FTS_EllLimOK.UniqG.smallUniq3G_fts
  set Θ : ℝ := min (min (min α₀ αg) αu) (1 / 3) with hΘ
  have hΘpos : 0 < Θ :=
    lt_min (lt_min (lt_min hα₀ hαg) hαu) (by norm_num)
  refine ⟨Ce, hCe, Θ, hΘpos, fun α hα hle => ?_⟩
  have h1 : pExp α ≤ α₀ :=
    le_trans hle (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have h2 : pExp α ≤ αg :=
    le_trans hle (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have h3 : pExp α ≤ 1 := by
    have h3' : pExp α ≤ 1 / 3 := le_trans hle (min_le_right _ _)
    rw [Work.FTS.Regularity.pExp_eq] at h3' ⊢
    linarith
  have h4 : pExp α ≤ αu := le_trans hle (le_trans (min_le_left _ _) (min_le_right _ _))
  have hp : 0 < pExp α := Work.FTS.Regularity.pExp_pos hα
  obtain ⟨E, hE8⟩ := hPkg8 (pExp α) hp h1
  obtain ⟨Ce', hCe'pos, hPkgH⟩ := hprod (pExp α) hp h2 Ce E hE8
  -- obligation 1
  have hbd : LocalBoundH (pExp α) (max Ce Ce') :=
    localBoundH_of_hasPkgH (α := pExp α) hp h3
  have hfat : FatouDataH (pExp α) (max Ce Ce') :=
    fatouDataH_of_hasPkgH (α := pExp α) hp
  have hboxd : BoxDataH (pExp α) (max Ce Ce') :=
    (Work.FTS_EllLimOK.BoxDataH.boxDataH_of_hasPkgH (α := pExp α) hp h3)
  have hcomp : ClosedCompact3H (pExp α) (max Ce Ce') :=
    ClosedCompact3H_of_bounds_fatou hbd hfat hboxd
  have hPk : Work.FTS_EllLimOK.HasPkgH (pExp α) (max Ce Ce') E := hPkgH
  -- obligation 1 + obligation 2 ⇒ closure
  have huniq' : ClosedUniq3G (pExp α) := huniq (pExp α) hp h4
  have hcl : ClosedE3G (pExp α) E := ClosedE3H_of_compact3_uniq3 hPk hcomp huniq'
  have hsol : ∀ g, Work.FTS.ClassC.ClassC (pExp α) g →
      Work.FTS.StrongGlobal.IsBslSolPos (pExp α) g (E g) :=
    fun g hg => Work.FTS.StrongGlobal.IsBslSol.toPos (HasPkgH.toHasPkg hPk g hg).1.sol
  have hsm : ∀ g, Work.FTS.ClassC.ClassC (pExp α) g →
      ContDiffOn ℝ 3 (Function.uncurry (E g)) Work.Construction.Qd :=
    fun g hg => contDiffOn_of_smoothOpen (HasPkgH.toHasPkg hPk g hg).1.smooth 3
  -- closure ⇒ `EllLimOK3`
  obtain ⟨E', hE'C, hok⟩ :=
    Work.FTS_EllLimOK.GlueG.exists_ellLimOK3_of_closedG E hsol hsm hcl
  refine ⟨E', fun g hg => ?_, (Lead_EllLimOK3_iff _ E').mp hok⟩
  rw [hE'C g hg]
  exact ⟨(hE8 g hg).2.1, (hE8 g hg).2.2⟩

/-- **The original deliverable of this area** (`StrongEps.EllLimOK`, order-`2` closure) from
route (b), same caveat. -/
theorem EllLimOK_of_routeB (hprod : RulingELF.ProducerH) (hb : RouteB) :
    ∃ Ce : ℝ, 0 < Ce ∧ ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α →
      pExp α ≤ α₀ → ∃ E : Fn →ₗ[ℝ] Fn,
      (∀ g, Work.FTS.ClassC.ClassC (pExp α) g →
        Work.FTS.VocabO.EllPkgGo (pExp α) Ce g (E g) ∧
          Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce g (E g)) ∧
      Work.FTS.StrongEps.EllLimOK (pExp α) E := by
  obtain ⟨Ce, hCe, α₀, hα₀, h⟩ := core1_1a3_of_routeB hprod hb
  refine ⟨Ce, hCe, α₀, hα₀, fun α hα hle => ?_⟩
  obtain ⟨E, hEk, hlim⟩ := h α hα hle
  exact ⟨E, hEk, Work.FTS.FinalV2.EllLimOK3.toEllLimOK hlim⟩

end Work.FTS_EllLimOK
