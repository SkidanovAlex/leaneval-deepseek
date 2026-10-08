import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.s02_gram
import Submission.Work.BG.indexTwoInduceIrreducible
import Submission.Work.BG.conjByH_basic
import Submission.Work.BG.H0Conj

namespace Work.BG

open OddOrder.RepresentationTheory

/-- `dcf C μ = Ind_{H₀}^{H} μ` is an irreducible character of `H` when `μ ∈ Irr(H₀)` is not
fixed by `s` (BG Remark 1.4; the index-two case of Clifford theory).  Route: transport `μ` along
`H0inEquiv C.P` to a class function on `↥(H₀.subgroupOf H)`, transport the non-invariance
`sconj C μ ≠ μ` to `conjBy s μ ≠ μ` with `Work.BG.conjByH_transport` plus injectivity of
`ClassFunction.compHom` for a group isomorphism, then apply
`Work.BG.indexTwoInduceIrreducible` with `(C.P.H0.subgroupOf C.P.H).index = 2`
(`Hyp12.H0_relIndex`) and `C.s ∉ C.P.H0.subgroupOf C.P.H` (`Sec2Ctx.s_not_mem_H0`). -/
theorem s02_dcf_mem_irr {G : Type} [Group G] [Finite G] [Fintype G] (C : Work.BG.Sec2Ctx G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] [Fintype ↥C.P.H]
    [Invertible (Nat.card ↥(C.P.H0.subgroupOf C.P.H) : ℂ)] [Invertible (Nat.card ↥C.P.H : ℂ)]
    {μ : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ}
    (hμ : OddOrder.RepresentationTheory.IsIrreducibleCharacter μ)
    (h : Work.BG.sconj C μ ≠ μ) :
    OddOrder.RepresentationTheory.IsIrreducibleCharacter (Work.BG.dcf C μ) := by
  -- `H₀.subgroupOf H` is the index-two normal subgroup `H₀ ≤ H`, and `s ∈ H ∖ H₀`.
  have hind : (C.P.H0.subgroupOf C.P.H).index = 2 := C.P.H0_relIndex
  have hs : (C.s : ↥C.P.H) ∉ C.P.H0.subgroupOf C.P.H := by
    rw [Subgroup.mem_subgroupOf]; exact C.s_not_mem_H0
  -- Transport `μ` to `CF(↥(H₀.subgroupOf H))` along `H0inEquiv C.P`.
  let μ' : ClassFunction ↥(C.P.H0.subgroupOf C.P.H) ℂ :=
    ClassFunction.compHom (H0inEquiv C.P).toMonoidHom μ
  have hμ' : IsIrreducibleCharacter μ' :=
    IsIrreducibleCharacter.compHom_of_surjective (H0inEquiv C.P).surjective hμ
  -- Transport the non-invariance: if `s` fixed `μ'`, then pulling back along the
  -- (surjective) `H0inEquiv` and using `conjByH_transport` would make `s` fix `μ`.
  have hconj : ClassFunction.conjBy (H := C.P.H0.subgroupOf C.P.H) (C.s : ↥C.P.H) μ' ≠ μ' := by
    intro hfix
    apply h
    have htr := conjByH_transport C.P C.s μ
    have h2 : ClassFunction.compHom (H0inEquiv C.P).toMonoidHom (sconj C μ) =
        ClassFunction.compHom (H0inEquiv C.P).toMonoidHom μ := by
      change ClassFunction.compHom (H0inEquiv C.P).toMonoidHom (conjByH C.P C.s μ) =
        ClassFunction.compHom (H0inEquiv C.P).toMonoidHom μ
      rw [htr]
      exact hfix
    exact ClassFunction.compHom_injective_of_surjective (H0inEquiv C.P).surjective h2
  -- Index-two Clifford theory: an `s`-non-invariant irreducible induces irreducibly.
  exact indexTwoInduceIrreducible (C.P.H0.subgroupOf C.P.H) hind (C.s : ↥C.P.H) hs
    ⟨μ', hμ'⟩ hconj

end Work.BG
