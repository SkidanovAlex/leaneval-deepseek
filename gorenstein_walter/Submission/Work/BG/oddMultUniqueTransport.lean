import Mathlib
import Submission.Work.BG.Glauberman
import Submission.Work.BG.CharBridge

namespace Work.BG

open OddOrder.RepresentationTheory

/-! ## BG-L6b: transport of `OddMultUnique` along `C.subgroupOf U₁ ≃* C`

`Work.BG.OddMultUniqueTransportProp` says that if the odd-multiplicity correspondence for
`α ∈ Irr U` and `α₁ ∈ Irr U₁` matches the corresponding multiplicities of `C` and
`C.subgroupOf U₁` (the hypothesis `htrans`, supplied by `parityTransfer`), and if `α₁` has a
*unique* odd-multiplicity constituent on `C.subgroupOf U₁`, then `α` has a unique
odd-multiplicity constituent on `C`.

The proof is pure transport along the group isomorphism
`e = Subgroup.subgroupOfEquivOfLe hC : C.subgroupOf U₁ ≃* C`:
pre- and post-composition with `e` is a bijection `Irr C ≃ Irr (C.subgroupOf U₁)`
(`IsIrreducibleCharacter.compHom_of_surjective` for both `e` and `e.symm`), it is injective on
class functions (`ClassFunction.compHom_injective_of_surjective`), and `htrans` identifies the
two odd-multiplicity predicates on corresponding irreducibles.  The unique witness `γ₀` on
`C.subgroupOf U₁` is therefore pulled back to the unique witness on `C`. -/

theorem oddMultUniqueTransport : Work.BG.OddMultUniqueTransportProp := by
  intro U _ _ U₁ C hC α α₁ htrans huniq
  classical
  let e : ↥(C.subgroupOf U₁) ≃* ↥C := Subgroup.subgroupOfEquivOfLe hC
  obtain ⟨γ₀, hγ₀, hγuniq⟩ := huniq
  -- the witness on `C`, obtained by pulling `γ₀` back along `e`
  let β₀ : IrreducibleCharacter C :=
    ⟨ClassFunction.compHom e.symm.toMonoidHom (γ₀ : ClassFunction ↥(C.subgroupOf U₁) ℂ),
      IsIrreducibleCharacter.compHom_of_surjective e.symm.surjective γ₀.isIrreducible⟩
  have hβ₀val : (β₀ : ClassFunction C ℂ) =
      ClassFunction.compHom e.symm.toMonoidHom (γ₀ : ClassFunction ↥(C.subgroupOf U₁) ℂ) := rfl
  -- `e` is a section-inverse pair, so pushing `β₀` forward recovers `γ₀`
  have hcomp₀ : ClassFunction.compHom e.toMonoidHom (β₀ : ClassFunction C ℂ) =
      (γ₀ : ClassFunction ↥(C.subgroupOf U₁) ℂ) := by
    ext x
    simp [ClassFunction.compHom_apply, hβ₀val]
  refine ⟨β₀, ?_, ?_⟩
  · -- existence: the parity transfer identifies `β₀` with `γ₀`
    show IsOddMult C (α : ClassFunction U ℂ) (β₀ : ClassFunction C ℂ)
    rw [htrans β₀, hcomp₀]
    exact hγ₀
  · -- uniqueness: any odd-multiplicity `β` transports to an odd-multiplicity `γ`, hence to `γ₀`
    intro β hβ
    let γ : IrreducibleCharacter ↥(C.subgroupOf U₁) :=
      ⟨ClassFunction.compHom e.toMonoidHom (β : ClassFunction C ℂ),
        IsIrreducibleCharacter.compHom_of_surjective e.surjective β.isIrreducible⟩
    have hγval : (γ : ClassFunction ↥(C.subgroupOf U₁) ℂ) =
        ClassFunction.compHom e.toMonoidHom (β : ClassFunction C ℂ) := rfl
    have hγ : IsOddMult (C.subgroupOf U₁) α₁ (γ : ClassFunction ↥(C.subgroupOf U₁) ℂ) :=
      (htrans β).1 hβ
    have heqγ : γ = γ₀ := hγuniq γ hγ
    have hkey : ClassFunction.compHom e.toMonoidHom (β : ClassFunction C ℂ) =
        ClassFunction.compHom e.toMonoidHom (β₀ : ClassFunction C ℂ) := by
      rw [← hγval, heqγ, hcomp₀]
    exact Subtype.ext (ClassFunction.compHom_injective_of_surjective e.surjective hkey)

end Work.BG
