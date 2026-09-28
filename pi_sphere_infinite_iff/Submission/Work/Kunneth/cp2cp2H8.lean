import Mathlib
import Submission.Work.Kunneth.kunneth_homology
import Submission.Work.Kunneth.kunneth_h4_cp2cp2
import Submission.Work.Kunneth.cpn_kunneth_hypotheses
import Submission.Work.Kunneth.homology_dual_tpC_ezaw
import Submission.Work.Kunneth.cp2cp2Pairing
import Submission.Work.Kunneth.cp2cp2ModelCpp
import Submission.Work.Kunneth.ctensAux
import Submission.Work.Projective.cpn_homology

/-!
# `H₈(ℂP² × ℂP²; ℤ) ≅ ℤ`, and its fundamental class generates it

The GEN interface `Work.Projective.CP2CP2Model X` carries the fundamental class `c`, and the
consumers `Work.Gen.cp2cp2NumbersOf` / `Work.Gen.Generators8Of` ask in addition for
`Submodule.span ℤ {c} = ⊤` (the generation of `H₈(ℂP² × ℂP²;ℤ) ≅ ℤ` by `c`).

This module supplies the isomorphism `H₈(ℂP² × ℂP²;ℤ) ≅ ℤ` **using the homology Künneth theorem of
this chapter** (`Work.Kunneth.kunneth_homology`) applied to the two factors `ℂP²`; the generation
statements for the classes actually used by the applications (`Work.Kunneth.cpFund = [ℂP²] × [ℂP²]`
and its transport `Work.Kunneth.cppC` to the space `ℂP² × ℂP²`) are in `cp2cp2H8Span.lean`.

## The computation

`kunneth_homology` computes

`H₈(ℂP² ⊗ ℂP²; ℤ) ≅ ⨁_{p+q=8} H_p(ℂP²) ⊗ H_q(ℂP²)`

(the Eilenberg–Zilber identification `ezawHomotopyEquiv` being the first step), and `H_q(ℂP²;ℤ)` is
`ℤ` in the even degrees `q ≤ 4` and `0` otherwise (`Work.Projective.cpn_homology`).  So of the nine
summands of the direct sum only the bidegree `(4,4)` survives, whence `H₈ ≅ ℤ`.  The two Künneth
hypotheses for `Y = ℂP²` are `Work.Kunneth.cpn_kunneth_hypotheses`.

## Main results

* `Work.Kunneth.cp2cp2HomIso : H₈(ℂP² ⊗ ℂP²) ≅ ℤ`
* `Work.Kunneth.cp2cp2HomIso_Z : H₈(ℂP² × ℂP²) ≅ ℤ`
* `Work.Kunneth.cpEHomologyIso`, `Work.Kunneth.cp2cp2HomIso_cpp : H₈(ℂP² × ℂP²) ≅ ℤ` for the space

The generation statements for the fundamental classes are in `cp2cp2H8Span.lean` (a
default-convention module: the scalar multiplication there is the one the consumers use).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct BigOperators Simplicial

namespace Work.Kunneth

noncomputable section

open Work.Cohomology

attribute [-instance] AddCommGroup.toIntModule

/-! ## The degreewise homology of `ℂP²` -/

/-- `Work.Projective.cpn_homology` for `ℂP²`, in the notation of the Künneth chapter: the `q`-th
homology of `ℂP²` is the model `ℤ`-module `cp2Model q` (`ℤ` for even `q ≤ 4`, `0` otherwise). -/
theorem cp2Homology_model (q : ℕ) :
    Nonempty (((sChain cpX).homology q) ≅ cp2Model q) :=
  Work.Projective.cpn_homology 2 q

/-- The degreewise homology of `ℂP²` is projective over `ℤ` (it is free, being the model module
`cp2Model q`).  This is the second Künneth hypothesis of `Work.Kunneth.kunneth_homology`. -/
theorem cp2Homology_projective (q : ℕ) :
    Module.Projective ℤ ↥((sChain cpX).homology q) := by
  haveI : Module.Free ℤ ↥((sChain cpX).homology q) := (cpn_kunneth_hypotheses 2 q).2.1
  exact Module.Projective.of_free

/-- **The Künneth fibre of `ℂP² × ℂP²` in bidegree `(p,q)` is a copy of `ℤ` or the zero module**,
according to whether both `p` and `q` are even and `≤ 4` — the homology analogue of
`Work.Kunneth.cohomSummand_cp2cp2_model`. -/
theorem homSummand_cp2cp2_model (p q : ℕ) :
    Nonempty (((sChain cpX).homology p ⊗ (sChain cpX).homology q) ≅
      ModuleCat.of ℤ (Fin (if Even p ∧ p ≤ 4 ∧ Even q ∧ q ≤ 4 then 1 else 0) → ℤ)) := by
  by_cases hp : Even p ∧ p ≤ 4
  · by_cases hq : Even q ∧ q ≤ 4
    · obtain ⟨e⟩ := tensor_cp2Model_even hp hq
      obtain ⟨ep⟩ := cp2Homology_model p
      obtain ⟨eq⟩ := cp2Homology_model q
      refine ⟨(((TensorProduct.congr (Iso.toLinearEquiv ep) (Iso.toLinearEquiv eq)).toModuleIso).trans
        e).trans ?_⟩
      rw [if_pos ⟨hp.1, hp.2, hq.1, hq.2⟩]
      exact (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso.symm
    · obtain ⟨ep⟩ := cp2Homology_model p
      obtain ⟨eq⟩ := cp2Homology_model q
      have hzq : IsZero (((sChain cpX).homology q)) :=
        isZero_of_iso (isZero_cp2Model hq) eq.symm
      have h1 : IsZero (((sChain cpX).homology p ⊗
          (sChain cpX).homology q : ModuleCat ℤ)) := isZero_tensor_of_isZero_right hzq
      have h2 : IsZero (ModuleCat.of ℤ
          (Fin (if Even p ∧ p ≤ 4 ∧ Even q ∧ q ≤ 4 then 1 else 0) → ℤ)) := by
        rw [if_neg (fun hh => hq ⟨hh.2.2.1, hh.2.2.2⟩)]
        exact ModuleCat.isZero_of_subsingleton _
      exact nonempty_iso_of_isZero h1 h2
  · obtain ⟨ep⟩ := cp2Homology_model p
    obtain ⟨eq⟩ := cp2Homology_model q
    have hzp : IsZero (((sChain cpX).homology p)) :=
      isZero_of_iso (isZero_cp2Model hp) ep.symm
    have h1 : IsZero (((sChain cpX).homology p ⊗
        (sChain cpX).homology q : ModuleCat ℤ)) := isZero_tensor_of_isZero_left hzp
    have h2 : IsZero (ModuleCat.of ℤ
        (Fin (if Even p ∧ p ≤ 4 ∧ Even q ∧ q ≤ 4 then 1 else 0) → ℤ)) := by
      rw [if_neg (fun hh => hp ⟨hh.1, hh.2.1⟩)]
      exact ModuleCat.isZero_of_subsingleton _
    exact nonempty_iso_of_isZero h1 h2

/-- The bidegree pattern of the surviving summands of the homological Künneth target of
`ℂP² × ℂP²` in total degree `8`: `1` in the bidegree `(4,4)` and `0` elsewhere. -/
def cp2cp2K (pq : tpIdx 8) : ℕ :=
  if Even pq.1.1 ∧ pq.1.1 ≤ 4 ∧ Even pq.1.2 ∧ pq.1.2 ≤ 4 then 1 else 0

/-- Only the bidegree `(4,4)` survives in total degree `8`: the number of nonzero summands of the
homological Künneth target of `ℂP² × ℂP²` in degree `8` is `1`. -/
theorem cp2cp2_hom_card_sum : ∑ pq : tpIdx 8, cp2cp2K pq = 1 := by
  have h : (∑ pq : tpIdx 8, cp2cp2K pq)
      = ∑ i : Fin 9, cp2cp2K ((tpIdxEquivFin 8).symm i) :=
    Fintype.sum_equiv (tpIdxEquivFin 8) cp2cp2K
      (fun i : Fin 9 => cp2cp2K ((tpIdxEquivFin 8).symm i)) (fun pq => by simp)
  rw [h]
  decide

/-- **The homological Künneth target of `ℂP² × ℂP²` in degree `8` is `ℤ`.** -/
theorem tpX_homSum_iso_int :
    Nonempty ((tpC (homSum (sChain cpX)) (homSum (sChain cpX))).X 8 ≅
      ModuleCat.of ℤ ℤ) := by
  obtain ⟨e1⟩ := piFinIso (tpIdx 8) cp2cp2K
  refine ⟨(LinearEquiv.toModuleIso (DirectSum.linearEquivFunOnFintype ℤ (tpIdx 8)
      (fun pq : tpIdx 8 => ↥((sChain cpX).homology pq.1.1 ⊗
        (sChain cpX).homology pq.1.2))))
    ≪≫ (LinearEquiv.toModuleIso (LinearEquiv.piCongrRight (fun pq : tpIdx 8 =>
        (homSummand_cp2cp2_model pq.1.1 pq.1.2).some.toLinearEquiv)))
    ≪≫ (LinearEquiv.toModuleIso e1)
    ≪≫ (LinearEquiv.toModuleIso (LinearEquiv.piCongrLeft ℤ (fun _ : Fin 1 => ℤ)
        (finCongr cp2cp2_hom_card_sum)))
    ≪≫ (LinearEquiv.toModuleIso (LinearEquiv.funUnique (Fin 1) ℤ ℤ))⟩

/-- **`H₈(ℂP² ⊗ ℂP²; ℤ) ≅ ℤ`**, by the homology Künneth theorem for the two factors `ℂP²` and the
degreewise vanishing of `H_q(ℂP²)` for odd `q` and `q > 4`. -/
theorem cp2cp2HomIso :
    Nonempty ((tpC (sChain cpX) (sChain cpX)).homology 8 ≅ ModuleCat.of ℤ ℤ) := by
  obtain ⟨eK⟩ := kunneth_homology (sChain cpX) (sChain cpX)
    (fun q => (cpn_kunneth_hypotheses 2 q).1) (fun q => cp2Homology_projective q) 8
  obtain ⟨eT⟩ := tpX_homSum_iso_int
  exact ⟨eK ≪≫ eT⟩

/-- **`H₈(ℂP² × ℂP²; ℤ) ≅ ℤ`**: the Künneth computation, preceded by the Eilenberg–Zilber
identification `Work.Kunneth.ezawHomotopyEquiv` of `ℂP² ⊗ ℂP²` with the tensor product of the
factors. -/
theorem cp2cp2HomIso_Z :
    Nonempty (((sChain cpZ).homology 8) ≅ ModuleCat.of ℤ ℤ) := by
  obtain ⟨e⟩ := cp2cp2HomIso
  exact ⟨(ezawHomotopyEquiv cpX cpX).toHomologyIso 8 ≪≫ e⟩

/-! ## The space `ℂP² × ℂP²` -/

/-- **The Eilenberg–Zilber identification of the space `ℂP² × ℂP²` with the simplicial product
`ℂP² ⊗ ℂP²`, on homology.**  (`Work.Kunneth.cpE` is the isomorphism of simplicial sets; its chain
map is an isomorphism of chain complexes, by `chainComplexMap_comp` and `chainComplexMap_id`.) -/
noncomputable def cpEHomologyIso :
    ((sChain cppSSet).homology 8) ≅ ((sChain cpZ).homology 8) where
  hom := HomologicalComplex.homologyMap (SSet.chainComplexMap cpE.hom zz) 8
  inv := HomologicalComplex.homologyMap (SSet.chainComplexMap cpE.inv zz) 8
  hom_inv_id := by
    rw [← HomologicalComplex.homologyMap_comp, ← chainComplexMap_comp, Iso.hom_inv_id cpE,
      chainComplexMap_id, HomologicalComplex.homologyMap_id]
  inv_hom_id := by
    rw [← HomologicalComplex.homologyMap_comp, ← chainComplexMap_comp, Iso.inv_hom_id cpE,
      chainComplexMap_id, HomologicalComplex.homologyMap_id]

/-- **`H₈(ℂP² × ℂP²; ℤ) ≅ ℤ`** for the space `ℂP² × ℂP²`. -/
theorem cp2cp2HomIso_cpp :
    Nonempty (((sChain cppSSet).homology 8) ≅ ModuleCat.of ℤ ℤ) := by
  obtain ⟨e⟩ := cp2cp2HomIso_Z
  exact ⟨cpEHomologyIso ≪≫ e⟩

end

end Work.Kunneth
