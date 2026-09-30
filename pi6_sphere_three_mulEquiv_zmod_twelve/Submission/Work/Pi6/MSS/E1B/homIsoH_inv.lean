import Mathlib
import Submission.Work.Pi6.MSS.E1B.Dual
import Submission.Work.StemsB.FieldDualUCT
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The inverse of `homIsoH` on the class of a cycle

`Work.Pi6.MSS.E1B.homIsoH` is the canonical isomorphism `H_n(E) ≅ Z_n(E)/B_n(E)` for a chain
complex of vector spaces, built as the composite of `homologyIsoSc'` (homology computed through the
short complex `E_{n+1} → E_n → E_{n-1}`) and `ShortComplex.moduleCatHomologyIso` (the explicit
description of the homology of a short complex of modules as cycles modulo boundaries).

This file records the behaviour of the *inverse* map: the class of a cycle `z` in `Z_n(E)/B_n(E)`
is sent back to the homology class of `z`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Work.Pi6.MSS.E1B

noncomputable section

variable {𝕜 : Type} [Field 𝕜] {E : ChainComplex (ModuleCat 𝕜) ℕ}

/-! ## Elementwise forms of the Mathlib identifications

Mathlib provides these identifications between the abstract homology of a complex and the explicit
cycles of the associated short complex only as equations of morphisms (or in the case of the
`ShortComplex` lemmas, with the domain written through the generic
`moduleCatLeftHomologyData`).  We record the elementwise forms that the proof below needs, in the
exact `ConcreteCategory.hom` shape in which they appear in the goal. -/

private lemma iCycles_cyclesIsoSc'_inv_apply (K : ChainComplex (ModuleCat 𝕜) ℕ) (i j k : ℕ)
    (hi : (ComplexShape.down ℕ).prev j = i) (hk : (ComplexShape.down ℕ).next j = k)
    (y : (K.sc' i j k).cycles) :
    (ConcreteCategory.hom (K.iCycles j)) ((ConcreteCategory.hom (K.cyclesIsoSc' i j k hi hk).inv) y)
      = (ConcreteCategory.hom (K.sc' i j k).iCycles) y := by
  have h := congrArg (fun (f : (K.sc' i j k).cycles ⟶ K.X j) => f.hom y)
    (HomologicalComplex.cyclesIsoSc'_inv_iCycles K i j k hi hk)
  exact h

private lemma homologyIsoSc'_inv_apply (K : ChainComplex (ModuleCat 𝕜) ℕ) (i j k : ℕ)
    (hi : (ComplexShape.down ℕ).prev j = i) (hk : (ComplexShape.down ℕ).next j = k)
    (y : (K.sc' i j k).cycles) :
    (ConcreteCategory.hom (K.homologyIsoSc' i j k hi hk).inv)
        ((ConcreteCategory.hom (K.sc' i j k).homologyπ) y)
      = (ConcreteCategory.hom (K.homologyπ j))
          ((ConcreteCategory.hom (K.cyclesIsoSc' i j k hi hk).inv) y) := by
  have h := congrArg (fun (f : (K.sc' i j k).cycles ⟶ K.homology j) => f.hom y)
    (HomologicalComplex.π_homologyIsoSc'_inv K i j k hi hk)
  exact h

private lemma moduleCatLeftHomologyData_π_hom' (S : ShortComplex (ModuleCat 𝕜)) :
    ConcreteCategory.hom S.moduleCatLeftHomologyData.π = S.moduleCatToCycles.range.mkQ :=
  CategoryTheory.ShortComplex.moduleCatLeftHomologyData_π_hom S

private lemma moduleCatLeftHomologyData_i_hom' (S : ShortComplex (ModuleCat 𝕜)) :
    ConcreteCategory.hom S.moduleCatLeftHomologyData.i = (ModuleCat.Hom.hom S.g).ker.subtype :=
  CategoryTheory.ShortComplex.moduleCatLeftHomologyData_i_hom S

/-- The class of a cycle, read in `Z_n ⧸ B_n`, is sent by the inverse of `homIsoH` to the homology
class of that cycle. -/
theorem homIsoH_inv {𝕜 : Type} [Field 𝕜] {E : ChainComplex (ModuleCat 𝕜) ℕ} (n : ℕ)
    (z : ↥(E.X n)) (hz : (ModuleCat.Hom.hom (E.d n (n-1))) z = 0) :
    (Work.Pi6.MSS.E1B.homIsoH 𝕜 E n).inv ((Work.StemsB.fdH 𝕜 E n).mkQ (⟨z, hz⟩ : ↥(Work.StemsB.fdZ 𝕜 E n)))
      = HomologicalComplex.homologyπ E n
          (HomologicalComplex.cyclesMk E z ((ComplexShape.down ℕ).next n) rfl
            (by rw [Work.Cohomology.down_next]; exact hz)) := by
  have hz' : (ModuleCat.Hom.hom (E.d n ((ComplexShape.down ℕ).next n))) z = 0 := by
    rw [Work.Cohomology.down_next]; exact hz
  set x : ↥(Work.StemsB.fdZ 𝕜 E n) := ⟨z, hz⟩ with hx
  set y : ↥(E.cycles n) := HomologicalComplex.cyclesMk E z ((ComplexShape.down ℕ).next n) rfl hz'
    with hy
  change (E.homologyIsoSc' (n+1) n (n-1) (Work.Cohomology.down_prev n)
        (Work.Cohomology.down_next n)).inv
      ((CategoryTheory.ShortComplex.moduleCatHomologyIso (E.sc' (n+1) n (n-1))).inv
        ((Work.StemsB.fdH 𝕜 E n).mkQ x))
    = HomologicalComplex.homologyπ E n y
  -- the explicit description of the homology of the short complex `E_{n+1} → E_n → E_{n-1}`
  have h2 : (CategoryTheory.ShortComplex.moduleCatHomologyIso (E.sc' (n+1) n (n-1))).inv
        ((Work.StemsB.fdH 𝕜 E n).mkQ x)
      = (E.sc' (n+1) n (n-1)).homologyπ
          ((CategoryTheory.ShortComplex.moduleCatCyclesIso (E.sc' (n+1) n (n-1))).inv x) := by
    have h := CategoryTheory.ShortComplex.moduleCatCyclesIso_inv_π_apply
      (E.sc' (n+1) n (n-1)) x
    rw [moduleCatLeftHomologyData_π_hom'] at h
    exact h.symm
  rw [h2]
  -- comparison with the homology in degree `n`
  have hA : ∀ (w : (E.sc' (n+1) n (n-1)).cycles),
      (E.homologyIsoSc' (n+1) n (n-1) (Work.Cohomology.down_prev n)
          (Work.Cohomology.down_next n)).inv
        ((E.sc' (n+1) n (n-1)).homologyπ w)
      = HomologicalComplex.homologyπ E n
          ((E.cyclesIsoSc' (n+1) n (n-1) (Work.Cohomology.down_prev n)
            (Work.Cohomology.down_next n)).inv w) := by
    intro w
    exact homologyIsoSc'_inv_apply E (n+1) n (n-1) (Work.Cohomology.down_prev n)
      (Work.Cohomology.down_next n) w
  rw [hA]
  -- the two cycles agree
  have h5 : (E.cyclesIsoSc' (n+1) n (n-1) (Work.Cohomology.down_prev n)
        (Work.Cohomology.down_next n)).inv
        ((CategoryTheory.ShortComplex.moduleCatCyclesIso (E.sc' (n+1) n (n-1))).inv x)
      = y := by
    apply (ModuleCat.mono_iff_injective (E.iCycles n)).mp inferInstance
    rw [iCycles_cyclesIsoSc'_inv_apply]
    have hCi : (E.sc' (n+1) n (n-1)).iCycles
        ((CategoryTheory.ShortComplex.moduleCatCyclesIso (E.sc' (n+1) n (n-1))).inv x) = z := by
      have h := CategoryTheory.ShortComplex.moduleCatCyclesIso_inv_iCycles_apply
        (E.sc' (n+1) n (n-1)) x
      rw [moduleCatLeftHomologyData_i_hom'] at h
      rw [h, hx]
      rfl
    rw [hCi, hy]
    exact (HomologicalComplex.i_cyclesMk E z ((ComplexShape.down ℕ).next n) rfl hz').symm
  rw [h5]

end

end Work.Pi6.MSS.E1B
