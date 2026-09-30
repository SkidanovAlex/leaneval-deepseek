/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area JacClose

# C1: **the naming data of the base-change comparison of symmetric powers exists**

This file proves `Work.JacClose.nonempty_symBCNaming`: for a curve `C/K`, a field extension
`L/K` and a `RochData R'` on the base change `C_L`, there are

* a place `Q'` of `C_L` (`Work.CurveBasics.exists_place`),
* an affine open `U'` of `C_L` (the affine basis of the topology of a scheme), and
* a basis `h'` of the Riemann–Roch space of the canonical divisor `R'.W`, indexed by
  `Fin R'.g` (which is what `Work.BcDiv.symBC` consumes), lying in that space and spanning it.

The only mathematical input is that `dim L(R'.W) = R'.g`, which is `RochData.ell_canonical`
at the (trivial) field extension `L/L`; the triviality is `Work.JacClose.pullK_self`.
-/
import Mathlib
import Submission.Work.JacClose.Basic
import Submission.Work.Charts.Basic
import Submission.Work.CurveBasics.Place

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

namespace Work.JacClose

open Work.CurveBasics
open Work.GCBasics

noncomputable section

variable {K : Type u} [Field K]

/-- `pullK` is the identity at the (trivial) field extension `K/K`. -/
theorem pullK_self {C : Curve K} [Work.SpecLin.DivBase C] (D : Dv C K) :
    Work.Charts.pullK C D = D := by
  show Work.SpecLin.DivBase.bc (IsScalarTower.toAlgHom K K K) D = D
  rw [show IsScalarTower.toAlgHom K K K = AlgHom.id K K from rfl,
    Work.SpecLin.DivBase.bc_id]

/-- The Riemann–Roch space of the canonical divisor of a `RochData` is `g`-dimensional:
`ℓ(W) = g` (RR5 at `D = 0`), with the base change `pullK` of `RochData.ell_canonical`
removed by `Work.JacClose.pullK_self`. -/
theorem finrank_L_canonical {C : Curve K} [Work.SpecLin.DivBase C]
    (R : Work.Charts.RochData C) :
    Module.finrank K ((C.baseChange K).L R.W) = R.g := by
  have h := R.ell_canonical (F := K)
  rw [pullK_self R.W] at h
  simpa [Work.GCBasics.ell] using h

/-- **C1: the naming data of `Work.BcDiv.symBC` exists.**

The place and the affine open are produced by non-emptiness of a curve and by the affine basis
of the topology of a scheme; the basis of `L(R'.W)` by `Module.finBasis` together with
`dim L(R'.W) = R'.g` (`Work.JacClose.finrank_L_canonical`). -/
theorem nonempty_symBCNaming {K : Type u} [Field K]
    (C : Work.CurveBasics.Curve K) {L : Type u} [Field L] [Algebra K L]
    (R' : Work.Charts.RochData (C.baseChange L)) :
    Nonempty (Work.JacClose.SymBCNaming C R') := by
  obtain ⟨Q'⟩ := exists_place (C.baseChange L)
  obtain ⟨x⟩ : Nonempty (C.baseChange L).left := inferInstance
  obtain ⟨_, ⟨U', hU', rfl⟩, -, -⟩ :=
    (C.baseChange L).left.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
  obtain ⟨h', h_mem', h_span'⟩ :
      ∃ h' : Fin R'.g → ((C.baseChange L).baseChange L).functionField,
        (∀ j, (0 : ((C.baseChange L).baseChange L).Div) ≤
            ((C.baseChange L).baseChange L).div (h' j) + R'.W)
        ∧ ((C.baseChange L).baseChange L).L R'.W = Submodule.span L (Set.range h') := by
    -- `dim L(R'.W) = R'.g`
    have hfin : Module.finrank L (((C.baseChange L).baseChange L).L R'.W) = R'.g :=
      finrank_L_canonical (C := C.baseChange L) R'
    haveI : FiniteDimensional L (((C.baseChange L).baseChange L).L R'.W) :=
      Work.CurveBasics.Linear.finiteDimensional_L _ R'.W
    -- a basis of `L(R'.W)`, reindexed by `Fin R'.g`
    let b : Module.Basis (Fin R'.g) L (((C.baseChange L).baseChange L).L R'.W) :=
      (Module.finBasis L _).reindex (finCongr hfin)
    refine ⟨fun j => ((b j : ((C.baseChange L).baseChange L).L R'.W) :
        ((C.baseChange L).baseChange L).functionField), ?_, ?_⟩
    · -- the basis elements lie in `L(R'.W)`
      intro j
      have hj : ((b j : ((C.baseChange L).baseChange L).L R'.W) :
          ((C.baseChange L).baseChange L).functionField) ∈
          ((C.baseChange L).baseChange L).L R'.W := (b j).2
      rcases (Curve.mem_L_iff ((C.baseChange L).baseChange L)).mp hj with h0 | heff
      · exact absurd (Subtype.ext h0) (Module.Basis.ne_zero b j)
      · simpa only [Curve.Div.IsEffective, Finsupp.le_def, Finsupp.zero_apply] using heff
    · -- and they span it
      have h1 : Submodule.span L (Set.range (fun j => ((b j :
            ((C.baseChange L).baseChange L).L R'.W) :
            ((C.baseChange L).baseChange L).functionField))) =
          ((C.baseChange L).baseChange L).L R'.W := by
        rw [show Set.range (fun j => ((b j : ((C.baseChange L).baseChange L).L R'.W) :
              ((C.baseChange L).baseChange L).functionField)) =
            Submodule.subtype (((C.baseChange L).baseChange L).L R'.W) '' Set.range b from
          Set.range_comp _ _]
        rw [Submodule.span_image, Module.Basis.span_eq, Submodule.map_subtype_top]
      exact h1.symm
  exact ⟨SymBCNaming.mk Q' U' hU' h' h_mem' h_span'⟩

end

end Work.JacClose
