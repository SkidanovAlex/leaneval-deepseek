import Mathlib
import Submission.Work.Kunneth.HomProd
import Submission.Work.Kunneth.CrossGen

/-!
# The homology of a chain complex as `Zₙ ⧸ Bₙ`, and the class of a cycle

`Submission/Work/Cohomology/uctDefs.lean` and `uctDual_evaluation.lean` provide the concrete
description `Hₙ ≅ Zₙ ⧸ Bₙ` of the homology together with the computation rule "the class of a cycle
is the class of the same element" — but without removing the generic `AddCommGroup.toIntModule`
instance, which is *incompatible* with the convention of the Künneth chapter (a statement about
`tpX`-elements cannot even be elaborated in the other convention).

This file redoes, in the chapter's convention, the small part of that API needed by the
cross-product form of the Künneth theorem:

* `Work.Kunneth.cycKer`, `Work.Kunneth.homBnd` — the concrete `Zₙ` and `Bₙ ⊆ Zₙ`;
* `Work.Kunneth.cycIso` — `K.cycles n ≅ Zₙ` (underlying elements unchanged);
* `Work.Kunneth.homQuotIso` — `Hₙ ≅ Zₙ ⧸ Bₙ`, with the computation rule
  `Work.Kunneth.homQuotIso_apply` (the class of a cycle is the class of the same element).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

universe u

variable (K : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)

/-- The concrete `n`-cycles of a chain complex: the kernel of the differential `dₙ`. -/
def cycKer (n : ℕ) : Submodule ℤ ↥(K.X n) := LinearMap.ker (K.d n (n - 1)).hom

/-- The concrete `n`-boundaries *inside the cycles*: the image of `d_{n+1}` in `Zₙ`. -/
def homBnd (n : ℕ) : Submodule ℤ ↥(cycKer K n) :=
  LinearMap.range (((K.d (n + 1) n).hom).codRestrict (cycKer K n) (fun x => by
    show (K.d n (n - 1)).hom ((K.d (n + 1) n).hom x) = 0
    have h := congrArg ModuleCat.Hom.hom (HomologicalComplex.d_comp_d K (n + 1) n (n - 1))
    simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
    exact LinearMap.congr_fun h x))

/-- The boundaries inside the cycles are the range of the concrete map `Zₙ₊₁ → Zₙ`. -/
theorem cycBnd_eq_range (n : ℕ) :
    homBnd K n = LinearMap.range (ShortComplex.moduleCatToCycles (K.sc' (n + 1) n (n - 1))) := rfl

/-- The boundaries inside the cycles, as the preimage of the boundaries. -/
theorem cycBnd_eq_comap (n : ℕ) :
    homBnd K n = (LinearMap.range (K.d (n + 1) n).hom).comap (cycKer K n).subtype := by
  rw [homBnd, LinearMap.range_codRestrict]

/-- Membership in `homBnd`: the element of `Zₙ` is the differential of something. -/
theorem mem_homBnd_iff (n : ℕ) (x : ↥(cycKer K n)) :
    x ∈ homBnd K n ↔ ∃ w : ↥(K.X (n + 1)), (K.d (n + 1) n).hom w = (x : ↥(K.X n)) := by
  rw [show homBnd K n = (LinearMap.range (K.d (n + 1) n).hom).comap (cycKer K n).subtype
      from cycBnd_eq_comap K n, Submodule.mem_comap, LinearMap.mem_range]
  exact Iff.rfl

/-- **The cycles as the concrete kernel of the differential.** -/
noncomputable def cycIso (n : ℕ) : K.cycles n ≅ ModuleCat.of ℤ ↥(cycKer K n) :=
  (K.cyclesIsoSc' (n + 1) n (n - 1) (down_prev n) (down_next n)) ≪≫
    ShortComplex.moduleCatCyclesIso (K.sc' (n + 1) n (n - 1))

theorem cycIso_hom_i (n : ℕ) :
    (cycIso K n).hom ≫
        (ShortComplex.moduleCatLeftHomologyData (K.sc' (n + 1) n (n - 1))).i
      = K.iCycles n := by
  rw [cycIso, Iso.trans_hom, Category.assoc, ShortComplex.moduleCatCyclesIso_hom_i,
    HomologicalComplex.cyclesIsoSc'_hom_iCycles]

/-- `cycIso` does not change the underlying element. -/
theorem cycIso_hom_val (n : ℕ) (c : ↥(K.cycles n)) :
    ((cycIso K n).hom c : ↥(K.X n)) = (K.iCycles n).hom c := by
  have h := congrArg (fun (m : K.cycles n ⟶ K.X n) => ModuleCat.Hom.hom m c) (cycIso_hom_i K n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

/-- **The homology as the concrete quotient `Zₙ ⧸ Bₙ`.** -/
noncomputable def homQuotIso (n : ℕ) :
    K.homology n ≅ ModuleCat.of ℤ (↥(cycKer K n) ⧸ homBnd K n) :=
  (K.homologyIsoSc' (n + 1) n (n - 1) (down_prev n) (down_next n)) ≪≫
    ShortComplex.moduleCatHomologyIso (K.sc' (n + 1) n (n - 1))

/-- The projection onto the left homology data of the degree-`n` short complex is the quotient
map `Zₙ → Zₙ ⧸ Bₙ`. -/
theorem LHD_pi_eq (n : ℕ) :
    (ShortComplex.moduleCatLeftHomologyData (K.sc' (n + 1) n (n - 1))).π
      = ModuleCat.ofHom (homBnd K n).mkQ := by
  rw [ModuleCat.hom_ext_iff, ShortComplex.moduleCatLeftHomologyData_π_hom]
  rfl

theorem homQuotIso_comp (n : ℕ) :
    (K.homologyπ n) ≫ (homQuotIso K n).hom
      = (cycIso K n).hom ≫ ModuleCat.ofHom (homBnd K n).mkQ := by
  simp only [homQuotIso, Iso.trans_hom, Category.assoc, cycIso,
    HomologicalComplex.π_homologyIsoSc'_hom_assoc, ShortComplex.π_moduleCatCyclesIso_hom]
  rw [LHD_pi_eq K n]

/-- **The computation rule for `homQuotIso`**: the class of a cycle is the class of the same
element of `Zₙ ⧸ Bₙ`. -/
theorem homQuotIso_apply (n : ℕ) (c : ↥(K.cycles n)) :
    (homQuotIso K n).hom.hom ((K.homologyπ n).hom c) = (homBnd K n).mkQ ((cycIso K n).hom c) := by
  have h := congrArg (fun (m : K.cycles n ⟶ ModuleCat.of ℤ (↥(cycKer K n) ⧸ homBnd K n)) =>
    ModuleCat.Hom.hom m c) (homQuotIso_comp K n)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] using h

end

end Work.Kunneth
