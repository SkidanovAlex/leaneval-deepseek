/-
Copyright (c) 2025 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area JacFinal (the final assembly: `Work.DescentGeom.Input` from the areas)
-/
import Submission.Work.JacFinal.Basic
import Submission.Work.GCBasics.hom_ext_of_resPt
import Submission.Work.SymQuot.Product.permIso_hom_proj
import Submission.Work.SymQuot.Prod.isReduced_pi_prod
import Submission.Work.Universal.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area `JacFinal` — the invariance of the quotient map under `S_n`

`SymQuotData.desc` is the quotient property of `C^n ⟶ Sym^n C`: an `S_n`-invariant morphism out
of `C^n` factors uniquely through the quotient map.  The *converse* property of the quotient map —
that it is itself invariant under the permutation action, i.e.
`(permIso ρ).hom ≫ quotMap = quotMap` — is **not** among the fields of `SpecLin.SymGeom` and
`Universal.SymQuotData`, but it *is* a consequence of them: the two composites agree at the
canonical `κ(z)`-point of every point `z` of `C^n` (`SymGeom.divOf_powMap` computes both divisors
as `Σ_m [x_m]`, which is permuted by `ρ`), and a morphism out of the reduced scheme `C^n` into the
separated scheme `Sym^n C` is determined by its values at those points
(`GCBasics.hom_ext_of_resPt`).  This is the internal step `hB` of `Work.Charts.powMap_perm`,
respelled here with `Inputs.prodC`, `Inputs.projC` and `Inputs.quotMapC` so that §1.4(b)
(`Submission/Work/JacFinal/GalSym.lean`) can use it without importing area `CH`.

There is no assumption in this file: `Inputs.permQuot` is a theorem.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonObj MonoidalCategory CategoryTheory
open CartesianMonoidalCategory

universe u

namespace Work.JacFinal

noncomputable section

variable {k : Type u} [Field k] {C : CurveBasics.Curve k} {P0 : 𝟙_ (Sch k) ⟶ C.toOver}

namespace Inputs

/-- The base-changed curve `C_{k'} = bc k' C`, in the spelling used by the areas. -/
abbrev C' (d : Inputs C P0) : Sch d.k' := (C.baseChange d.k').toOver

/-- The `n`-fold product `C_{k'}^n`, in the spelling used by this area (it is the
`SymQuotData.prod` of area `UP`; the two differ only by unfolding a definition, so the `Pi`
machinery applies without further `dsimp`). -/
abbrev prodC (d : Inputs C P0) (n : ℕ) : Sch d.k' := ∏ᶜ (fun _ : Fin n => d.C')

/-- The `m`-th projection of the `n`-fold product. -/
abbrev projC (d : Inputs C P0) (n : ℕ) (m : Fin n) : prodC d n ⟶ d.C' :=
  Limits.Pi.π (fun _ : Fin n => d.C') m

/-- The permutation of the `n` factors. -/
def permIsoC (d : Inputs C P0) {n : ℕ} (ρ : Equiv.Perm (Fin n)) : prodC d n ≅ prodC d n :=
  SymQuot.permIso d.C' ρ

/-- The permutation acts on the projections. -/
theorem permIsoC_hom_proj (d : Inputs C P0) {n : ℕ} (ρ : Equiv.Perm (Fin n)) (i : Fin n) :
    (permIsoC d ρ).hom ≫ d.projC n i = d.projC n (ρ.symm i) :=
  SymQuot.Product.permIso_hom_proj d.C' ρ i

/-- The quotient map `C_{k'}^n ⟶ Sym^n C_{k'}` of area `UP` (the interface `SymQuotData`), in
the spelling of this area. -/
def quotMapC (d : Inputs C P0) (n : ℕ) : prodC d n ⟶ d.chart.Sym n :=
  (d.chart.symGeom n).powMap (fun m => d.projC n m)

/-- **The invariance of the quotient map under the permutation action of `S_n`** on the `n`-fold
product.  See the module docstring: it is a consequence of the interfaces `SpecLin.SymGeom` and
`Universal.SymQuotData` (via the reducedness of `C^n` and the separatedness of `Sym^n C`), not an
additional assumption. -/
def PermQuot (d : Inputs C P0) : Prop :=
  ∀ (n : ℕ) (ρ : Equiv.Perm (Fin n)), (d.permIsoC ρ).hom ≫ d.quotMapC n = d.quotMapC n

/-- **(G5) is a theorem.**  The quotient map `C^n ⟶ Sym^n C` is invariant under the permutation
action of `S_n`, for an arbitrary instance of the interface `SpecLin.SymGeom`.  This is the
internal step `hB` of `Work.Charts.powMap_perm` (which is stated for area `CH`'s own `quotMap`),
respelled in the vocabulary of this area. -/
theorem permQuot (d : Inputs C P0) : d.PermQuot := by
  intro n ρ
  haveI : IsReduced (d.prodC n).left :=
    Work.SymQuot.Prod.isReduced_pi_prod d.C' n
  haveI : IsSeparated (d.chart.Sym n).hom := by
    haveI := d.chart.isProper_Sym n
    infer_instance
  apply Work.GCBasics.hom_ext_of_resPt
  intro z
  apply (d.chart.symGeom n).divOf_injective
  simp only [quotMapC, projC, ← Category.assoc]
  rw [← (d.chart.symGeom n).powMap_comp, ← (d.chart.symGeom n).powMap_comp,
    (d.chart.symGeom n).divOf_powMap, (d.chart.symGeom n).divOf_powMap]
  rw [Finset.sum_congr rfl (fun m _ => by rw [Category.assoc, d.permIsoC_hom_proj ρ m])]
  exact Equiv.sum_comp ρ.symm (fun m =>
    SpecLin.ptDiv (Work.GCBasics.resPt (d.prodC n) z ≫ d.projC n m))

end Inputs

end

end Work.JacFinal
