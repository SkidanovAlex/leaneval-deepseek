import Mathlib
import Submission.Work.Kunneth.kunneth_cohomology_cpn
import Submission.Work.Kunneth.piFinIso
import Submission.Work.Projective.CP2Concrete
import Submission.Work.Projective.cpn_cohomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `H⁴(ℂP² × ℂP²; ℤ) ≅ ℤ³`

The Künneth theorem for `ℂP²` (`Work.Kunneth.kunneth_cohomology_cpn`) computes

`H⁴(ℂP² ⊗ ℂP²; ℤ) ≅ ⨁_{p+q=4} Hᵖ(ℂP²) ⊗ H^q(ℂP²)`,

and `H^q(ℂP²; ℤ)` is `ℤ` in the even degrees `q ≤ 4` and `0` otherwise
(`Work.Projective.cpn_cohomology`).  Hence the Künneth target is a product of three copies of `ℤ`
(the bidegrees `(0,4)`, `(2,2)`, `(4,0)`) and two zero factors, which
`Work.Kunneth.piFinIso` collapses to `Fin 3 → ℤ`.

This is the rank statement of item 4 of the Künneth subproject: `H⁴(ℂP² × ℂP²; ℤ) ≅ ℤ³`; the
*spanning* of `H⁴` by `a²`, `ab`, `b²` (`a = π₁^*h`, `b = π₂^*h`) is `Work.Kunneth.cp2cp2Span`, and
the identification of the cross product with the Künneth isomorphism is documented in
`Submission/Work/Kunneth/README.md`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct BigOperators

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- The `q`-th cohomology of `ℂP²` is `ℤ` for even `q ≤ 4` and `0` otherwise: the model
`ModuleCat` object `Fin (if Even q ∧ q ≤ 4 then 1 else 0) → ℤ`. -/
abbrev cp2Model (q : ℕ) : ModuleCat ℤ :=
  ModuleCat.of ℤ (Fin (if Even q ∧ q ≤ 4 then 1 else 0) → ℤ)

/-- `Work.Projective.cpn_cohomology` for `ℂP²`, in the notation of the Künneth chapter. -/
theorem cp2Coh_model (q : ℕ) :
    Nonempty (((Work.Cohomology.cochainC ℤ Work.Projective.cp2SSet).homology q) ≅ cp2Model q) :=
  Work.Projective.cpn_cohomology 2 q

/-- The model is a zero object in the odd degrees (and in the degrees `> 4`). -/
theorem isZero_cp2Model {q : ℕ} (h : ¬(Even q ∧ q ≤ 4)) : IsZero (cp2Model q) := by
  rw [cp2Model, if_neg h]
  exact ModuleCat.isZero_of_subsingleton _

/-- In an even degree `≤ 4` the model is `ℤ`. -/
theorem cp2Model_iso_int {q : ℕ} (h : Even q ∧ q ≤ 4) :
    Nonempty (cp2Model q ≅ ModuleCat.of ℤ ℤ) := by
  refine ⟨?_⟩
  rw [cp2Model, if_pos h]
  exact (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso

/-- `ℤ ⊗ ℤ ≅ ℤ`. -/
theorem tensor_int_int : Nonempty (ModuleCat.of ℤ ℤ ⊗ ModuleCat.of ℤ ℤ ≅ ModuleCat.of ℤ ℤ) :=
  ⟨(TensorProduct.lid ℤ ℤ).toModuleIso⟩

/-- The tensor product of the two (rank one) `ℤ`-modules of the case `(p,q)` even is `ℤ`. -/
theorem tensor_cp2Model_even {p q : ℕ} (hp : Even p ∧ p ≤ 4) (hq : Even q ∧ q ≤ 4) :
    Nonempty (cp2Model p ⊗ cp2Model q ≅ ModuleCat.of ℤ ℤ) := by
  obtain ⟨ep⟩ := cp2Model_iso_int hp
  obtain ⟨eq⟩ := cp2Model_iso_int hq
  exact ⟨(TensorProduct.congr (Iso.toLinearEquiv ep) (Iso.toLinearEquiv eq)).toModuleIso ≪≫
    (TensorProduct.lid ℤ ℤ).toModuleIso⟩

/-- Transport of `IsZero` along an isomorphism (in the direction needed below). -/
theorem isZero_of_iso {M N : ModuleCat ℤ} (h : IsZero M) (e : M ≅ N) : IsZero N :=
  CategoryTheory.Limits.IsZero.of_iso h e.symm

/-- The tensor product of two subsingleton `ℤ`-modules is a subsingleton. -/
theorem subsingleton_tensor_of_subsingleton_left {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (h : Subsingleton M) : Subsingleton (M ⊗[ℤ] N) := by
  have hz : ∀ x : M ⊗[ℤ] N, x = 0 := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | tmul m n => rw [Subsingleton.elim m 0, TensorProduct.zero_tmul]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact ⟨fun x y => by rw [hz x, hz y]⟩

/-- A tensor product with a zero factor is zero. -/
theorem isZero_tensor_of_isZero_left {M N : ModuleCat ℤ} (h : IsZero M) :
    IsZero (M ⊗ N : ModuleCat ℤ) := by
  have hsub : Subsingleton ↥M := ModuleCat.isZero_iff_subsingleton.mp h
  have hsub2 : Subsingleton ↥(M ⊗ N : ModuleCat ℤ) := subsingleton_tensor_of_subsingleton_left hsub
  exact ModuleCat.isZero_iff_subsingleton.mpr hsub2

/-- A tensor product with a zero factor is zero (right version). -/
theorem isZero_tensor_of_isZero_right {M N : ModuleCat ℤ} (h : IsZero N) :
    IsZero (M ⊗ N : ModuleCat ℤ) := by
  rw [ModuleCat.isZero_iff_subsingleton] at h ⊢
  have hz : ∀ x : ↥(M ⊗ N : ModuleCat ℤ), x = 0 := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | tmul m n => rw [Subsingleton.elim n 0, TensorProduct.tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact ⟨fun x y => by rw [hz x, hz y]⟩

/-- Two zero `ℤ`-modules are isomorphic. -/
theorem nonempty_iso_of_isZero {M N : ModuleCat ℤ} (hM : IsZero M) (hN : IsZero N) :
    Nonempty (M ≅ N) :=
  ⟨hM.isoZero ≪≫ hN.isoZero.symm⟩

/-- **The fibre of the Künneth target of `ℂP² × ℂP²` in bidegree `(p,q)` with `p + q = 4` is a
copy of `ℤ` or the zero module**, according to whether `p` (equivalently `q`) is even. -/
theorem cohomSummand_cp2cp2_model (p q : ℕ) (h : p + q = 4) :
    Nonempty ((Work.Cohomology.cochainC ℤ Work.Projective.cp2SSet).homology p ⊗
        (Work.Cohomology.cochainC ℤ Work.Projective.cp2SSet).homology q ≅
      ModuleCat.of ℤ (Fin (if Even p ∧ p ≤ 4 ∧ Even q ∧ q ≤ 4 then 1 else 0) → ℤ)) := by
  by_cases hp : Even p ∧ p ≤ 4
  · by_cases hq : Even q ∧ q ≤ 4
    · -- both even: `ℤ ⊗ ℤ ≅ ℤ`
      obtain ⟨e⟩ := tensor_cp2Model_even hp hq
      obtain ⟨ep⟩ := cp2Coh_model p
      obtain ⟨eq⟩ := cp2Coh_model q
      refine ⟨(((TensorProduct.congr (Iso.toLinearEquiv ep) (Iso.toLinearEquiv eq)).toModuleIso).trans
        e).trans ?_⟩
      rw [if_pos ⟨hp.1, hp.2, hq.1, hq.2⟩]
      exact (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso.symm
    · -- first even, second odd: the second factor is zero
      obtain ⟨ep⟩ := cp2Coh_model p
      obtain ⟨eq⟩ := cp2Coh_model q
      have hzq : IsZero (((Work.Cohomology.cochainC ℤ
          Work.Projective.cp2SSet).homology q)) := isZero_of_iso (isZero_cp2Model hq) eq.symm
      have h1 : IsZero (((Work.Cohomology.cochainC ℤ Work.Projective.cp2SSet).homology p ⊗
          (Work.Cohomology.cochainC ℤ Work.Projective.cp2SSet).homology q : ModuleCat ℤ)) :=
        isZero_tensor_of_isZero_right hzq
      have h2 : IsZero (ModuleCat.of ℤ (Fin (if Even p ∧ p ≤ 4 ∧ Even q ∧ q ≤ 4 then 1 else 0) → ℤ)) := by
        rw [if_neg (fun hh => hq ⟨hh.2.2.1, hh.2.2.2⟩)]
        exact ModuleCat.isZero_of_subsingleton _
      exact nonempty_iso_of_isZero h1 h2
  · -- first odd: the first factor is zero
    obtain ⟨ep⟩ := cp2Coh_model p
    obtain ⟨eq⟩ := cp2Coh_model q
    have hzp : IsZero (((Work.Cohomology.cochainC ℤ
        Work.Projective.cp2SSet).homology p)) := isZero_of_iso (isZero_cp2Model hp) ep.symm
    have h1 : IsZero (((Work.Cohomology.cochainC ℤ Work.Projective.cp2SSet).homology p ⊗
        (Work.Cohomology.cochainC ℤ Work.Projective.cp2SSet).homology q : ModuleCat ℤ)) :=
      isZero_tensor_of_isZero_left hzp
    have h2 : IsZero (ModuleCat.of ℤ (Fin (if Even p ∧ p ≤ 4 ∧ Even q ∧ q ≤ 4 then 1 else 0) → ℤ)) := by
      rw [if_neg (fun hh => hp ⟨hh.1, hh.2.1⟩)]
      exact ModuleCat.isZero_of_subsingleton _
    exact nonempty_iso_of_isZero h1 h2

/-- The number of nonzero summands of the Künneth target of `ℂP² × ℂP²` in degree `4`. -/
theorem cp2cp2_card_sum :
    ∑ pq : tpIdx 4, (if Even pq.1.1 ∧ pq.1.1 ≤ 4 ∧ Even pq.1.2 ∧ pq.1.2 ≤ 4 then 1 else 0) = 3 := by
  decide

/-- **The Künneth target of `ℂP² × ℂP²` in degree `4` is `ℤ³`.** -/
theorem kunnethTarget_cp2cp2_four :
    Nonempty (kunnethTarget Work.Projective.cp2SSet Work.Projective.cp2SSet 4 ≅
      ModuleCat.of ℤ (Fin 3 → ℤ)) := by
  obtain ⟨e⟩ := piFinIso (tpIdx 4)
    (fun pq => if Even pq.1.1 ∧ pq.1.1 ≤ 4 ∧ Even pq.1.2 ∧ pq.1.2 ≤ 4 then 1 else 0)
  refine ⟨(LinearEquiv.piCongrRight (fun pq : tpIdx 4 => ?_)).toModuleIso ≪≫ e.toModuleIso ≪≫ ?_⟩
  · exact (cohomSummand_cp2cp2_model pq.1.1 pq.1.2 pq.2).some.toLinearEquiv
  · exact (LinearEquiv.piCongrLeft ℤ (fun _ : Fin 3 => ℤ)
      (finCongr cp2cp2_card_sum)).symm.toModuleIso

/-- **`H⁴(ℂP² × ℂP²; ℤ) ≅ ℤ³`**: the rank statement of the Künneth computation for the product of
two projective planes, the surface `ℂP² × ℂP²` whose middle cohomology is the source of the
intersection form used in the dimension-`8` Hirzebruch computation. -/
theorem kunneth_h4_cp2cp2 :
    Nonempty (CategoryTheory.Iso
      ((Work.Cohomology.cochainC ℤ (Work.Kunneth.sProd Work.Projective.cp2SSet
        Work.Projective.cp2SSet)).homology 4)
      (ModuleCat.of ℤ (Fin 3 → ℤ))) := by
  obtain ⟨eK⟩ := kunneth_cohomology_cpn Work.Projective.cp2SSet 2 4
  obtain ⟨eT⟩ := kunnethTarget_cp2cp2_four
  exact ⟨eK ≪≫ eT⟩

end

end Work.Kunneth
