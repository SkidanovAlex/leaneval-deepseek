import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.Lemma13
import Submission.Work.BG.H0Conj
import Submission.Work.BG.CharBridge
import Submission.Work.BG.sconjLam
import Submission.Work.BG.Lambda
import Submission.Work.BG.conjByH_basic
import Submission.Work.BG.indexTwoMackey
import Submission.Work.BG.lemma17_iii_aux
import Submission.OddOrder.GroupTheory.RepresentationTheory.InducedTransport

/-!
# Area BG: Bender–Glauberman §2, the Brauer–Suzuki Gram matrix (`GramProp`)

This file proves `Work.BG.GramProp` (design pass 10, input **I-2** of the lead's
`NOTES_BG_s02_leaves.md`): for irreducible `μ, ν, μ', ν' ∈ Irr(H₀)` with `LamEquiv C μ ν` and
`LamEquiv C μ' ν'`,

`⟨(μ - ν)^G, (μ' - ν')^G⟩_G = cH μ μ' - cH μ ν' - cH ν μ' + cH ν ν'`,

where `cH C α β = [β = α] + [β = α^s]` and `(·)^G = ind C (·) = Ind_{H₀}^G`.

The route (design 10, §2.2 "I-2") is

1. `(μ - ν)^H = Ind_{H₀}^H (μ - ν)` vanishes off `T = H₀ ∖ U`:
   * off `H₀`, because `H₀ ⊴ H` (induction from a normal subgroup is supported on it);
   * on `U`, because `μ - ν = (1 - λ_β) μ` and `λ_β` is trivial on `U = ker(H₀ → H₀/U)`;
     every conjugate of an element of `U` stays in `U` (Hypothesis 1.2 forces `H ≤ N_G(U)`).
2. Induction in stages `ind C θ = Ind_H^G (Ind_{H₀}^H θ)` (`induce_induce_subgroupOf`),
   and `lemma13_isometry` (Brauer–Suzuki TI isometry of Hypothesis 1.2) turns the `G`-inner
   product into the `H`-inner product of the two `T`-supported class functions.
3. Index-two Mackey (`indexTwoMackey`) computes
   `⟨Ind_{H₀}^H δ, Ind_{H₀}^H δ'⟩_H = ⟨δ, δ'⟩_{H₀} + ⟨δ, (δ')^s⟩_{H₀}`.
4. Bilinearity of `inner` and orthonormality of irreducible characters
   (`irreducibleCharacter_inner_eq_ite`) reduce the four terms to the `cH`'s.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

section Aux

variable {G : Type} [Group G] [Finite G]

/-! ## The conjugation action `sconj` is an involution and additive -/

/-- `sconj C` is an involution: `(ν^s)^s = ν`, because `conjByH` is multiplicative and
`s² = 1` (`Sec2Ctx.s_sq`). -/
theorem sconj_involutive (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ) :
    sconj C (sconj C ν) = ν := by
  show conjByH C.P C.s (conjByH C.P C.s ν) = ν
  have h1 : conjByH C.P C.s (conjByH C.P C.s ν) = conjByH C.P (C.s * C.s) ν :=
    (conjByH_mul C.P C.s C.s ν).symm
  rw [h1]
  have hs : C.s * C.s = 1 := by rw [← sq, C.s_sq]
  rw [hs, conjByH_one]

/-- `sconj C` is additive. -/
theorem sconj_sub (C : Sec2Ctx G) (a b : ClassFunction ↥C.P.H0 ℂ) :
    sconj C (a - b) = sconj C a - sconj C b := by
  unfold sconj conjByH
  rw [ClassFunction.compHom_sub]

/-! ## `cH` in terms of the inner product

`cH C α β = [β = α] + [β = α^s]`; for irreducible `α, β` the two summands are the inner
products `⟨α, β⟩` and `⟨α, β^s⟩` by orthonormality of `Irr(H₀)`, and
`α = β^s ↔ β = α^s` because `sconj` is an involution. -/

/-- `cH C α β = ⟨α, β⟩ + ⟨α, β^s⟩` for irreducible `α, β`. -/
theorem cH_eq_inner_add (C : Sec2Ctx G) [Fintype ↥C.P.H0]
    [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    {α β : ClassFunction ↥C.P.H0 ℂ} (hα : IsIrreducibleCharacter α)
    (hβ : IsIrreducibleCharacter β) :
    cH C α β = ClassFunction.inner α β + ClassFunction.inner α (sconj C β) := by
  classical
  have hβ' : IsIrreducibleCharacter (sconj C β) := by
    show IsIrreducibleCharacter (conjByH C.P C.s β)
    exact IsIrreducibleCharacter.conjByH C.P C.s hβ
  rw [irreducibleCharacter_inner_eq_ite (⟨α, hα⟩ : IrreducibleCharacter ↥C.P.H0) ⟨β, hβ⟩,
      irreducibleCharacter_inner_eq_ite (⟨α, hα⟩ : IrreducibleCharacter ↥C.P.H0)
        ⟨sconj C β, hβ'⟩]
  rw [cH]
  have e1 : (⟨α, hα⟩ : IrreducibleCharacter ↥C.P.H0) = ⟨β, hβ⟩ ↔ β = α := by
    rw [Subtype.ext_iff]; exact eq_comm
  have e2 : (⟨α, hα⟩ : IrreducibleCharacter ↥C.P.H0) = ⟨sconj C β, hβ'⟩ ↔
      β = sconj C α := by
    rw [Subtype.ext_iff]
    constructor
    · intro h
      have h' : α = sconj C β := h
      have h2 : sconj C α = β := by rw [h', sconj_involutive]
      exact h2.symm
    · intro h
      have h' : sconj C β = α := by rw [h, sconj_involutive]
      exact h'.symm
  congr 1
  · exact (if_congr e1 rfl rfl).symm
  · exact (if_congr e2 rfl rfl).symm

/-! ## The `H`-stage of the induction: `dcf`

`dcf C θ = Ind_{H₀}^H θ`, where `θ` is transported along `↥(H₀.subgroupOf H) ≃* ↥H₀`. -/

/-- `Invertible` for the cardinality of a subgroup of a finite group. -/
noncomputable def invertible_natCard_subgroup [Fintype G]
    (S : Subgroup G) : Invertible (Nat.card ↥S : ℂ) :=
  invertibleOfNonzero (by
    rw [Nat.cast_ne_zero]
    exact Nat.card_ne_zero.mpr ⟨⟨⟨1, S.one_mem⟩⟩, inferInstance⟩)

/-- `Ind_{H₀}^{H}` of a class function of `H₀`, as a class function of `↥C.P.H`. -/
noncomputable def dcf [Fintype G] (C : Sec2Ctx G) [Fintype ↥C.P.H]
    [Invertible (Nat.card ↥(C.P.H0.subgroupOf C.P.H) : ℂ)]
    (θ : ClassFunction ↥C.P.H0 ℂ) : ClassFunction ↥C.P.H ℂ :=
  ClassFunction.induce (C.P.H0.subgroupOf C.P.H)
    (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe C.P.H0_le_H).toMonoidHom θ)

/-- Induction in stages: `ind C θ = Ind_H^G (dcf C θ)`. -/
theorem ind_eq_induce_dcf [Fintype G] (C : Sec2Ctx G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] [Fintype ↥C.P.H]
    [Invertible (Nat.card ↥(C.P.H0.subgroupOf C.P.H) : ℂ)]
    [Invertible (Nat.card ↥C.P.H : ℂ)]
    (θ : ClassFunction ↥C.P.H0 ℂ) :
    ind C θ = ClassFunction.induce C.P.H (dcf C θ) := by
  rw [dcf]
  exact (induce_induce_subgroupOf C.P.H0_le_H θ).symm

/-! ## `dcf C (μ - ν)` is supported on `T = H₀ ∖ U` -/

/-- For `ν = λ_β μ` (`LamEquiv C μ ν`) the class function `(μ - ν)^H` vanishes off
`T = H₀ ∖ U`:
* on `U` because `λ_β` is trivial there (`Lambda.apply_eq_one_of_mem_U`) and `U` is normal
  in `H` (`U_conj_mem`), so all Mackey summands see an element of `U`;
* on `H ∖ H₀` because `Ind_{H₀}^H` from the normal subgroup `H₀ ⊴ H` is supported on `H₀`. -/
theorem dcf_eq_zero_of_not_mem_T [Fintype G] (C : Sec2Ctx G)
    [Fintype ↥C.P.H] [Invertible (Nat.card ↥(C.P.H0.subgroupOf C.P.H) : ℂ)]
    {μ ν : ClassFunction ↥C.P.H0 ℂ} (h : LamEquiv C μ ν) :
    ∀ x : ↥C.P.H, (x : G) ∉ Tset C.P.H0 C.P.U → dcf C (μ - ν) x = 0 := by
  classical
  obtain ⟨β, hβ⟩ := h
  have hθu : ∀ u : ↥C.P.H0, u ∈ C.P.U.subgroupOf C.P.H0 → (μ - ν) u = 0 := by
    intro u hu
    have hlam : lamCF C β u = 1 := Lambda.apply_eq_one_of_mem_U ⟨β, rfl⟩ hu
    change μ u - ν u = 0
    rw [hβ, ClassFunction.mul_apply, hlam, one_mul, sub_self]
  intro x hx
  rw [dcf]
  by_cases hxH0 : (x : G) ∈ C.P.H0
  · have hxU : (x : G) ∈ C.P.U := by
      by_contra hmem
      exact hx ⟨hxH0, hmem⟩
    rw [ClassFunction.induce_apply]
    have hsum : (∑ y : ↥C.P.H,
        ClassFunction.induceTerm (C.P.H0.subgroupOf C.P.H)
          (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe C.P.H0_le_H).toMonoidHom (μ - ν))
          y x) = 0 := by
      refine Finset.sum_eq_zero fun y _ => ?_
      by_cases hy : y⁻¹ * x * y ∈ C.P.H0.subgroupOf C.P.H
      · rw [ClassFunction.induceTerm_of_mem _ hy, ClassFunction.compHom_apply]
        apply hθu
        rw [Subgroup.mem_subgroupOf]
        show ((Subgroup.subgroupOfEquivOfLe C.P.H0_le_H) ⟨y⁻¹ * x * y, hy⟩ : G) ∈ C.P.U
        rw [Subgroup.subgroupOfEquivOfLe_apply_coe]
        have hconj : (((y⁻¹ * x * y : ↥C.P.H)) : G) = (y : G)⁻¹ * (x : G) * (y : G) := by simp
        rw [hconj]
        simpa using U_conj_mem C.P y⁻¹ hxU
      · rw [ClassFunction.induceTerm_of_not_mem _ hy]
    rw [hsum, mul_zero]
  · have hxN : x ∉ C.P.H0.subgroupOf C.P.H := by
      intro hh; exact hxH0 (Subgroup.mem_subgroupOf.mp hh)
    exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hxN

/-! ## The `H`-inner product of the `H`-induced class functions -/

/-- Index-two Mackey + Frobenius reciprocity: for `δ, δ'` class functions of `H₀`,
`⟨δ^H, (δ')^H⟩_H = ⟨δ, δ'⟩_{H₀} + ⟨δ, (δ')^s⟩_{H₀}`. -/
theorem inner_dcf_eq [Fintype G] (C : Sec2Ctx G) [Fintype ↥C.P.H0]
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] [Fintype ↥C.P.H]
    [Fintype ↥(C.P.H0.subgroupOf C.P.H)]
    [Invertible (Nat.card ↥(C.P.H0.subgroupOf C.P.H) : ℂ)]
    [Invertible (Nat.card ↥C.P.H : ℂ)]
    (δ δ' : ClassFunction ↥C.P.H0 ℂ) :
    ClassFunction.inner (dcf C δ) (dcf C δ')
      = ClassFunction.inner δ δ' + ClassFunction.inner δ (sconj C δ') := by
  classical
  have hind : (C.P.H0.subgroupOf C.P.H).index = 2 := C.P.H0_relIndex
  have hs : (C.s : ↥C.P.H) ∉ C.P.H0.subgroupOf C.P.H := by
    rw [Subgroup.mem_subgroupOf]; exact C.s_not_mem_H0
  have htrans := conjByH_transport C.P C.s δ'
  unfold H0inEquiv at htrans
  have h1 : ClassFunction.inner (dcf C δ) (dcf C δ')
      = ClassFunction.inner
          (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe C.P.H0_le_H).toMonoidHom δ)
          (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe C.P.H0_le_H).toMonoidHom δ')
        + ClassFunction.inner
            (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe C.P.H0_le_H).toMonoidHom δ)
            (ClassFunction.conjBy (C.s : ↥C.P.H)
              (ClassFunction.compHom
                (Subgroup.subgroupOfEquivOfLe C.P.H0_le_H).toMonoidHom δ')) := by
    rw [dcf, dcf, ClassFunction.inner_induce_eq_inner_restrict,
      indexTwoMackey (C.P.H0.subgroupOf C.P.H) hind C.s hs, ClassFunction.inner_add_right]
  rw [h1, ClassFunction.inner_compHom_mulEquiv (Subgroup.subgroupOfEquivOfLe C.P.H0_le_H) δ δ']
  congr 1
  rw [← htrans, ClassFunction.inner_compHom_mulEquiv]
  rfl

end Aux

/-- **BG §2, input I-2 (`GramProp`)**: for `ν = λ_β μ`, `ν' = λ_{β'} μ'` the induced
difference `(μ - ν)^G` and `(μ' - ν')^G` have inner product given by the Brauer–Suzuki Gram
matrix `cH C α β = [β = α] + [β = α^s]`. -/
theorem s02_gram {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.BG.GramProp C := by
  intro μ ν μ' ν' hμ hν hμ' hν' heq heq'
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  haveI : Fintype ↥C.P.H := Fintype.ofFinite _
  haveI : Fintype ↥(C.P.H0.subgroupOf C.P.H) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥C.P.H : ℂ) := invertible_natCard_subgroup _
  haveI : Invertible (Nat.card ↥(C.P.H0.subgroupOf C.P.H) : ℂ) := invertible_natCard_subgroup _
  -- Step 1: `lemma13_isometry` on the `H`-stage (`T`-supported) class functions.
  have hstep1 : ClassFunction.inner (ind C (μ - ν)) (ind C (μ' - ν')) =
      ClassFunction.inner (dcf C (μ - ν)) (dcf C (μ' - ν')) := by
    rw [ind_eq_induce_dcf C (μ - ν), ind_eq_induce_dcf C (μ' - ν')]
    exact lemma13_isometry C.P (dcf_eq_zero_of_not_mem_T C heq)
      (dcf_eq_zero_of_not_mem_T C heq')
  -- Step 2: index-two Mackey in `H`, bilinearity, orthonormality.
  have hstep2 : ClassFunction.inner (dcf C (μ - ν)) (dcf C (μ' - ν')) =
      cH C μ μ' - cH C μ ν' - cH C ν μ' + cH C ν ν' := by
    rw [inner_dcf_eq C (μ - ν) (μ' - ν'), sconj_sub]
    rw [cH_eq_inner_add C hμ hμ', cH_eq_inner_add C hμ hν',
      cH_eq_inner_add C hν hμ', cH_eq_inner_add C hν hν']
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right]
    ring
  exact hstep1.trans hstep2

end Work.BG
