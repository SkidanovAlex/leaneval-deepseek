import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.Lemma13
import Submission.Work.BG.H0Conj
import Submission.Work.BG.CharBridge
import Submission.Work.BG.indexTwoMackey
import Submission.Work.BG.s02_bsValueT_aux

/-!
# Area BG: `BSValueTProp` (I-3′ of design10)

**Bender–Glauberman 1981, Lemma 1.3 (value form) on `T`.**  For `μ, ν ∈ Irr(H₀)` with
`ν = λ_β μ` (`LamEquiv C μ ν`) and `g ∈ H₀ ∖ U = T`,

  `(μ - ν)^G(g) = (μ - ν)(g) + (μ - ν)(s g s⁻¹)`,

where `(μ - ν)^G = ind C (μ - ν)` is induction `H₀ → G` and `s g s⁻¹ = conjMulEquiv C.P C.s g`.

The proof is the one prescribed by `NOTES_BG_s02_leaves.md`:

* `δ := Ind_{H₀}^{H}(μ - ν)` (with `μ - ν` transported along `H0inEquiv`);
* `δ` is supported on `T = H₀ ∖ U` (`bsValueT_support`): off `H₀` it vanishes because `H₀ ⊴ H`,
  and on `U` because `μ - ν` vanishes on `U` (`lamEquiv_apply_eq_of_mem_U`) and `s` normalizes
  `U` (`s_conj_mem_U`);
* induction in stages (`induce_induce_subgroupOf`) writes `ind C (μ - ν)` as `Ind_H^G δ`, and
  Lemma 1.3 (`lemma13_value`) evaluates the latter on `T` by `δ`;
* the index-two Mackey formula (`indexTwoMackey`) gives `δ(g) = (μ - ν)(g) + (μ - ν)(s g s⁻¹)`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory
open Subgroup

/-- **Support of `Ind_{H₀}^{H}(μ - ν)`.**  If `ν = λ_β μ` then the induced class function
`δ = Ind_{H₀}^{H}(μ - ν)` (of `μ - ν` transported along `H0inEquiv`) vanishes outside
`T = H₀ ∖ U`.

This is the hypothesis `δ ∈ supportedOnT C.P` required by Lemma 1.3, and the only place
`LamEquiv` enters the proof of `BSValueTProp`. -/
theorem bsValueT_support {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    [Fintype ↥C.P.H] (μ ν : ClassFunction ↥C.P.H0 ℂ) (hLam : LamEquiv C μ ν) :
    ∀ x : ↥C.P.H, (x : G) ∉ Tset C.P.H0 C.P.U →
      ClassFunction.induce (H0in C.P)
        (ClassFunction.compHom (H0inEquiv C.P).toMonoidHom (μ - ν)) x = 0 := by
  intro x hx
  classical
  set χ : ClassFunction ↥(H0in C.P) ℂ :=
    ClassFunction.compHom (H0inEquiv C.P).toMonoidHom (μ - ν) with hχ
  have hsuppU : ∀ u : ↥C.P.H0, u ∈ C.P.U.subgroupOf C.P.H0 → (μ - ν) u = 0 :=
    lamEquiv_apply_eq_of_mem_U C hLam
  by_cases hxH0 : (x : G) ∈ C.P.H0
  · have hxU : (x : G) ∈ C.P.U := by
      by_contra hxu; exact hx ⟨hxH0, hxu⟩
    have hindex : (H0in C.P).index = 2 := C.P.H0_relIndex
    have hsnot : (C.s : ↥C.P.H) ∉ H0in C.P := C.s_not_mem_H0
    have hmackey := indexTwoMackey (H := ↥C.P.H) (H0in C.P) hindex
      (C.s : ↥C.P.H) hsnot χ
    have hval := congrArg
      (fun f : ClassFunction ↥(H0in C.P) ℂ => f (⟨x, hxH0⟩ : ↥(H0in C.P))) hmackey
    rw [ClassFunction.restrict_apply, ClassFunction.add_apply] at hval
    have h1 : χ (⟨x, hxH0⟩ : ↥(H0in C.P)) = 0 := by
      rw [hχ, ClassFunction.compHom_apply]
      exact hsuppU _ (by
        rw [Subgroup.mem_subgroupOf]
        show ((H0inEquiv C.P) (⟨x, hxH0⟩ : ↥(H0in C.P)) : G) ∈ C.P.U
        rw [show ((H0inEquiv C.P) (⟨x, hxH0⟩ : ↥(H0in C.P)) : G) = (x : G) from rfl]
        exact hxU)
    have h2 : ClassFunction.conjBy (G := ↥C.P.H) (H := H0in C.P) (C.s : ↥C.P.H) χ
        (⟨x, hxH0⟩ : ↥(H0in C.P)) = 0 := by
      rw [show ClassFunction.conjBy (G := ↥C.P.H) (H := H0in C.P) (C.s : ↥C.P.H) χ
            (⟨x, hxH0⟩ : ↥(H0in C.P))
          = χ (ClassFunction.conjByMulEquiv (G := ↥C.P.H) (H := H0in C.P)
              (C.s : ↥C.P.H) (⟨x, hxH0⟩ : ↥(H0in C.P))) from rfl,
        hχ, ClassFunction.compHom_apply]
      exact hsuppU _ (by
        rw [Subgroup.mem_subgroupOf]
        show ((H0inEquiv C.P)
          (ClassFunction.conjByMulEquiv (G := ↥C.P.H) (H := H0in C.P)
            (C.s : ↥C.P.H) (⟨x, hxH0⟩ : ↥(H0in C.P))) : G) ∈ C.P.U
        rw [show ((H0inEquiv C.P)
            (ClassFunction.conjByMulEquiv (G := ↥C.P.H) (H := H0in C.P)
              (C.s : ↥C.P.H) (⟨x, hxH0⟩ : ↥(H0in C.P))) : G)
            = (C.s : G) * (x : G) * (C.s : G)⁻¹ from by
          rw [show ((H0inEquiv C.P)
              (ClassFunction.conjByMulEquiv (G := ↥C.P.H) (H := H0in C.P)
                (C.s : ↥C.P.H) (⟨x, hxH0⟩ : ↥(H0in C.P))) : G)
              = ((ClassFunction.conjByMulEquiv (G := ↥C.P.H) (H := H0in C.P)
                (C.s : ↥C.P.H) (⟨x, hxH0⟩ : ↥(H0in C.P)) : ↥C.P.H) : G) from rfl,
            ClassFunction.conjByMulEquiv_apply]
          simp]
        exact s_conj_mem_U C hxU)
    rw [hval, h1, h2, add_zero]
  · exact ClassFunction.induce_apply_eq_zero_of_not_mem_normal (H0in C.P) χ hxH0

/-- **Index-two value form of the Mackey formula for `Ind_{H₀}^{H}(μ - ν)`.**  For every
`g ∈ H₀`, the induced class function `Ind_{H₀}^{H}(μ - ν)` takes at `g` the value
`(μ - ν)(g) + (μ - ν)(s g s⁻¹)`. -/
theorem bsValueT_value {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    [Fintype ↥C.P.H] (μ ν : ClassFunction ↥C.P.H0 ℂ) (g : ↥C.P.H0) :
    ClassFunction.induce (H0in C.P)
      (ClassFunction.compHom (H0inEquiv C.P).toMonoidHom (μ - ν))
      (⟨(g : G), C.P.H0_le_H g.2⟩ : ↥C.P.H)
    = (μ - ν) g + (μ - ν) (conjMulEquiv C.P C.s g) := by
  classical
  set χ : ClassFunction ↥(H0in C.P) ℂ :=
    ClassFunction.compHom (H0inEquiv C.P).toMonoidHom (μ - ν) with hχ
  have hindex : (H0in C.P).index = 2 := C.P.H0_relIndex
  have hsnot : (C.s : ↥C.P.H) ∉ H0in C.P := C.s_not_mem_H0
  have hmackey := indexTwoMackey (H := ↥C.P.H) (H0in C.P) hindex
    (C.s : ↥C.P.H) hsnot χ
  set g' : ↥(H0in C.P) := ⟨(⟨(g : G), C.P.H0_le_H g.2⟩ : ↥C.P.H), g.2⟩ with hg'
  have hval := congrArg (fun f : ClassFunction ↥(H0in C.P) ℂ => f g') hmackey
  rw [ClassFunction.restrict_apply, ClassFunction.add_apply] at hval
  have hg'coe : (g' : ↥C.P.H) = ⟨(g : G), C.P.H0_le_H g.2⟩ := rfl
  have h1 : χ g' = (μ - ν) g := by
    rw [hχ, ClassFunction.compHom_apply]
    congr 1
  have h2 : ClassFunction.conjBy (G := ↥C.P.H) (H := H0in C.P) (C.s : ↥C.P.H) χ g'
      = (μ - ν) (conjMulEquiv C.P C.s g) := by
    rw [show ClassFunction.conjBy (G := ↥C.P.H) (H := H0in C.P) (C.s : ↥C.P.H) χ g'
        = χ (ClassFunction.conjByMulEquiv (G := ↥C.P.H) (H := H0in C.P)
            (C.s : ↥C.P.H) g') from rfl, hχ, ClassFunction.compHom_apply]
    congr 1
  rw [hg'coe] at hval
  rw [hval, h1, h2]

/-- **I-3′ (design10):** the value of `(μ - ν)* = ind C (μ - ν)` on `T = H₀ ∖ U`.  This is
`BSValueTProp`, the `T`-analogue of `BSValueProp` and the input (v) of Theorem 2.3. -/
theorem s02_bsValueT {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.BG.BSValueTProp C := by
  intro μ ν hμ hν hLam g hgU
  classical
  haveI : Fintype ↥C.P.H := Fintype.ofFinite _
  set χ : ClassFunction ↥(H0in C.P) ℂ :=
    ClassFunction.compHom (H0inEquiv C.P).toMonoidHom (μ - ν) with hχ
  set δ : ClassFunction ↥C.P.H ℂ := ClassFunction.induce (H0in C.P) χ with hδ
  -- Induction in stages: `ind C (μ - ν) = Ind_H^G δ`.
  have hA : ClassFunction.induce C.P.H0 (μ - ν) = ClassFunction.induce C.P.H δ := by
    rw [hδ, hχ]
    exact (induce_induce_subgroupOf (M := G) (K := C.P.H0) (H := C.P.H)
      C.P.H0_le_H (μ - ν)).symm
  -- `δ` is supported on `T`.
  have hsupp : ∀ x : ↥C.P.H, (x : G) ∉ Tset C.P.H0 C.P.U → δ x = 0 := by
    intro x hx
    rw [hδ, hχ]
    exact bsValueT_support C μ ν hLam x hx
  -- Lemma 1.3 evaluates `Ind_H^G δ` on `T`.
  let a : ↥C.P.H := ⟨(g : G), C.P.H0_le_H g.2⟩
  have ha : (a : G) ∈ Tset C.P.H0 C.P.U := ⟨g.2, hgU⟩
  have hC : ClassFunction.induce C.P.H δ (a : G) = δ a := lemma13_value C.P hsupp ha
  -- Index-two Mackey at `g ∈ H₀`.
  have hval : ClassFunction.induce (H0in C.P) χ a
      = (μ - ν) g + (μ - ν) (conjMulEquiv C.P C.s g) := by
    rw [hχ]
    exact bsValueT_value C μ ν g
  have hmain : ind C (μ - ν) (g : G) = ClassFunction.induce C.P.H δ (a : G) := by
    rw [show ind C (μ - ν) = ClassFunction.induce C.P.H δ from hA]
  have h3 : δ a = (μ - ν) g + (μ - ν) (conjMulEquiv C.P C.s g) := by
    rw [hδ]
    exact hval
  exact hmain.trans (hC.trans h3)

end Work.BG
