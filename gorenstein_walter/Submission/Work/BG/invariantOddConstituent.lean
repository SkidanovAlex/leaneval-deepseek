import Mathlib
import Submission.Work.BG.Glauberman
import Submission.Work.BG.CharBridge

/-!
# Area BG: BG-L5 — the odd constituent is invariant

Bender–Glauberman 1981, Lemma 1.9, step (3) of the induction (see `NOTES_BG.md` §4.2):

if `S` acts on `U` through `φ : S →* MulAut U`, `U₁ = C_U(φ s₀)` is the fixed-point subgroup of
a fixed `s₀ ∈ S`, `S` acts on `U₁` through `φ₁` (the restriction of `φ`, hypothesis `hφ₁`),
`α ∈ Irr(U)` is `φ`-invariant, and `α₁ ∈ Irr(U₁)` is the unique irreducible of `U₁` whose
multiplicity in `α|_{U₁}` is odd, then `α₁` is `φ₁`-invariant.

The proof is the standard one: for `s ∈ S` the automorphism `e = φ₁ s` of `U₁` permutes `Irr(U₁)`
by `θ ↦ θ ∘ e`; the multiplicity of `θ ∘ e` in `α|_{U₁}` equals that of `θ` (the inner product is
invariant under pullback along the isomorphism `e`, and `α|_{U₁}` is `e`-invariant because `α` is
`φ`-invariant and `e` agrees with `φ s` on `U₁`); hence `θ = α₁` is a fixed point, i.e.
`α₁ ∘ e = α₁`.
-/

set_option linter.style.haveILetI false

namespace Work.BG

open OddOrder.RepresentationTheory

/-- Pull an irreducible character back along a group isomorphism.  (This is the same
construction as `Work.BG.irrCompMulEquiv` of `glauberman_general.lean`; the local copy keeps the
present file independent of that development.) -/
noncomputable def irrPullback {H₁ H₂ : Type*} [Group H₁] [Group H₂] (e : H₁ ≃* H₂) :
    IrreducibleCharacter H₂ → IrreducibleCharacter H₁ :=
  fun χ => ⟨ClassFunction.compHom e.toMonoidHom (χ : ClassFunction H₂ ℂ),
    IsIrreducibleCharacter.compHom_of_surjective e.surjective χ.isIrreducible⟩

@[simp] theorem irrPullback_coe {H₁ H₂ : Type*} [Group H₁] [Group H₂] (e : H₁ ≃* H₂)
    (χ : IrreducibleCharacter H₂) :
    ((irrPullback e χ : IrreducibleCharacter H₁) : ClassFunction H₁ ℂ) =
      ClassFunction.compHom e.toMonoidHom (χ : ClassFunction H₂ ℂ) := rfl

/-- `IsOddMult K α θ` unfolded, with the `Fintype`/`Invertible` instances taken from the ambient
context rather than from the definition.  (`Work.BG.oddMultBridge` is the same statement; this
form fixes the ambient type of `K` instead of quantifying over the full `OddMultBridgeProp`.) -/
theorem isOddMult_iff_inner {V : Type} [Group V] [Finite V] [Fintype V] (K : Subgroup V)
    [Fintype K] [Invertible (Nat.card K : ℂ)] (α : ClassFunction V ℂ) (θ : ClassFunction K ℂ) :
    IsOddMult K α θ ↔
      ∃ k : ℤ, ClassFunction.inner (ClassFunction.restrict K α) θ = (2 * k + 1 : ℂ) :=
  oddMultBridge K α θ

theorem invariantOddConstituent : Work.BG.InvariantOddConstituentProp := by
  intro S U _ _ _ φ s₀ φ₁ hφ₁ α α₁ hα hodd s u
  classical
  haveI hUF : Fintype U := Fintype.ofFinite U
  haveI hF : Fintype ↥(fixedSubgroup (φ s₀)) := Fintype.ofFinite _
  haveI hI : Invertible (Nat.card ↥(fixedSubgroup (φ s₀)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- (1) `α|_{U₁}` is invariant under `φ₁ s`
  have hres : ClassFunction.compHom (φ₁ s).toMonoidHom
        (ClassFunction.restrict (fixedSubgroup (φ s₀)) (α : ClassFunction U ℂ)) =
      ClassFunction.restrict (fixedSubgroup (φ s₀)) (α : ClassFunction U ℂ) := by
    ext x
    show (α : ClassFunction U ℂ) (((φ₁ s) x : ↥(fixedSubgroup (φ s₀))) : U) =
      (α : ClassFunction U ℂ) ((x : ↥(fixedSubgroup (φ s₀))) : U)
    rw [hφ₁ s x]
    exact hα s (x : U)
  -- (2) the multiplicity of `α₁ ∘ (φ₁ s)` in `α|_{U₁}` equals that of `α₁`
  have hcomp : ClassFunction.inner
        (ClassFunction.restrict (fixedSubgroup (φ s₀)) (α : ClassFunction U ℂ))
        ((irrPullback (φ₁ s) α₁ : IrreducibleCharacter ↥(fixedSubgroup (φ s₀))) :
          ClassFunction ↥(fixedSubgroup (φ s₀)) ℂ) =
      ClassFunction.inner
        (ClassFunction.restrict (fixedSubgroup (φ s₀)) (α : ClassFunction U ℂ))
        (α₁ : ClassFunction ↥(fixedSubgroup (φ s₀)) ℂ) := by
    rw [irrPullback_coe]
    have h := inner_compHom_of_mulEquiv
      (e := (φ₁ s : ↥(fixedSubgroup (φ s₀)) ≃* ↥(fixedSubgroup (φ s₀))))
      (ClassFunction.restrict (fixedSubgroup (φ s₀)) (α : ClassFunction U ℂ))
      (α₁ : ClassFunction ↥(fixedSubgroup (φ s₀)) ℂ)
    rw [hres] at h
    exact h
  -- (3) `α₁ ∘ (φ₁ s)` also has odd multiplicity, hence equals `α₁` by uniqueness
  obtain ⟨k, hk⟩ := (isOddMult_iff_inner (K := fixedSubgroup (φ s₀)) (α : ClassFunction U ℂ)
      (α₁ : ClassFunction ↥(fixedSubgroup (φ s₀)) ℂ)).1 ((hodd α₁).2 rfl)
  have hodd' : IsOddMult (fixedSubgroup (φ s₀)) (α : ClassFunction U ℂ)
      ((irrPullback (φ₁ s) α₁ : IrreducibleCharacter ↥(fixedSubgroup (φ s₀))) :
        ClassFunction ↥(fixedSubgroup (φ s₀)) ℂ) :=
    (isOddMult_iff_inner (K := fixedSubgroup (φ s₀)) (α : ClassFunction U ℂ)
      ((irrPullback (φ₁ s) α₁ : IrreducibleCharacter ↥(fixedSubgroup (φ s₀))) :
        ClassFunction ↥(fixedSubgroup (φ s₀)) ℂ)).2
      ⟨k, by rw [hcomp]; exact hk⟩
  have heq : irrPullback (φ₁ s) α₁ = α₁ := (hodd (irrPullback (φ₁ s) α₁)).1 hodd'
  have hcf : ClassFunction.compHom (φ₁ s).toMonoidHom
        (α₁ : ClassFunction ↥(fixedSubgroup (φ s₀)) ℂ) =
      (α₁ : ClassFunction ↥(fixedSubgroup (φ s₀)) ℂ) := by
    have h := congrArg (fun χ : IrreducibleCharacter ↥(fixedSubgroup (φ s₀)) =>
      (χ : ClassFunction ↥(fixedSubgroup (φ s₀)) ℂ)) heq
    simpa only [irrPullback_coe] using h
  -- (4) evaluate at `u`
  have h2 : ClassFunction.compHom (φ₁ s).toMonoidHom
        (α₁ : ClassFunction ↥(fixedSubgroup (φ s₀)) ℂ) u =
      (α₁ : ClassFunction ↥(fixedSubgroup (φ s₀)) ℂ) u := by rw [hcf]
  exact h2

end Work.BG
