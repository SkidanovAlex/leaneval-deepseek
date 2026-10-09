import Mathlib
import Submission.Work.SSGRoute.ExtChain.ext_push_engine
import Submission.Work.SSGRoute.ExtChain.FreeCover
import Submission.Work.SSGRoute.PT.e1a_shift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The formal half of `(PUSH)`: injectivity of the coefficient change on a syzygy lattice

Extracted from `Submission/Work/SSGRoute/ExtChain/himgIdelesInput_fin_leaf.lean` so that the module
`Submission/Work/SSGRoute/ExtChain/exists_khLift_of_extToIdeles_eq_zero.lean` (which is a *child* of
that file) can use it without importing its own consumer; the leaf file imports this module.

The lead's `(PUSH)` (`_lead_design/flags_0030/NOTE.md` §2, re-affirmed in `flags_0530/NOTE.md` §1)
asks for the *injectivity* of the coefficient change

    Ext¹_{D_q}(res R, (K^h)ˣ) → Ext¹_{D_q}(res R, K_qˣ),      R = ker (freeCover N),  N = E^∨(1),

where `K^h = Ω^{D_A ⊓ Gal(Ω/K)}` is the henselisation of `K` at `q` and the quotient
`Q = K_qˣ/(K^h)ˣ` is uniquely `p`-divisible.  The *arithmetic* half of this is
`E1aClean.unitsQuotient_pow_bijective` (proved); the *formal* half is the lemma below, which is
purely `Ext`-bookkeeping and holds in the abstract setting: it is the syzygy-shifted form of the
engine `ExtChain.postcomp_mk₀_bijective_of_ptorsion_uniqueDivisible`.

The point of the shift is that `R` is a *lattice*, not `p`-torsion: the engine does not apply to
`Ext¹(res R, ·)` directly.  But `0 → res R → res F → res N → 0` has `res F` projective, so the
syzygy shift `Ext¹(res R, ·) ≅ Ext²(res N, ·)` is a natural isomorphism (`PT.e1aShiftEquiv`), and
the pushed coefficient change is the engine's bijection on `Ext²(res N, ·)`.  Hence the change on
`Ext¹(res R, ·)` is injective as well.
-/

open CategoryTheory SSGRoute.PTExt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000

namespace Work.SSGRoute.ExtChain

/-- **`(PUSH)`, formal half.**  Let `SN : 0 → SN.X₁ → SN.X₂ → SN.X₃ → 0` be a short exact sequence
of representations of a finite group `G` with projective middle term, whose cokernel `SN.X₃` is
annihilated by `p`; let `S : 0 → S.X₁ → S.X₂ → S.X₃ → 0` be a short exact sequence whose cokernel is
uniquely `p`-divisible.  Then the induced coefficient change

    Ext¹_G(SN.X₁, S.X₁) → Ext¹_G(SN.X₁, S.X₂)

is injective.

This is the exact shape needed at `SN = (freeCoverSES N).map (Rep.resFunctor (decompK q).subtype)`
and `S` the coefficient sequence `(K^h)ˣ → K_qˣ → Q`. -/
theorem ext1_coeffPush_injective_of_ptorsion_uniqueDivisible
    {G : Type} [Group G] [Fintype G] (p : ℕ)
    (SN : ShortComplex (Rep.{0} Coeff G)) (hSN : SN.ShortExact) [Projective SN.X₂]
    (hN : ∀ x : SN.X₃.V, p • x = 0)
    (S : ShortComplex (Rep.{0} Coeff G)) (hS : S.ShortExact)
    (hQ : Function.Bijective (fun q : S.X₃.V => p • q)) :
    Function.Injective (fun ζ : CategoryTheory.Abelian.Ext.{0} SN.X₁ S.X₁ 1 =>
      ζ.comp (CategoryTheory.Abelian.Ext.mk₀ S.f) (add_zero 1)) := by
  have hbij := postcomp_mk₀_bijective_of_ptorsion_uniqueDivisible p SN.X₃ hN hS 1 hQ
  have hnat : ∀ (x : CategoryTheory.Abelian.Ext.{0} SN.X₁ S.X₁ 1),
      PT.e1aShiftEquiv SN hSN S.X₂ 1 (le_refl 1)
        (x.comp (CategoryTheory.Abelian.Ext.mk₀ S.f) (add_zero 1))
      = (PT.e1aShiftEquiv SN hSN S.X₁ 1 (le_refl 1) x).comp
          (CategoryTheory.Abelian.Ext.mk₀ S.f) (add_zero 2) := by
    intro x
    rw [PT.e1aShiftEquiv_apply, PT.e1aShiftEquiv_apply]
    exact (CategoryTheory.Abelian.Ext.comp_assoc hSN.extClass x
      (CategoryTheory.Abelian.Ext.mk₀ S.f) (by omega) (add_zero 1) (by omega)).symm
  intro ζ η hζη
  have hζη' : ζ.comp (CategoryTheory.Abelian.Ext.mk₀ S.f) (add_zero 1)
      = η.comp (CategoryTheory.Abelian.Ext.mk₀ S.f) (add_zero 1) := hζη
  have hshift : PT.e1aShiftEquiv SN hSN S.X₁ 1 (le_refl 1) ζ
      = PT.e1aShiftEquiv SN hSN S.X₁ 1 (le_refl 1) η := by
    refine hbij.1 ?_
    calc ((CategoryTheory.Abelian.Ext.mk₀ S.f).postcomp SN.X₃ (add_zero 2))
          (PT.e1aShiftEquiv SN hSN S.X₁ 1 (le_refl 1) ζ)
        = (PT.e1aShiftEquiv SN hSN S.X₁ 1 (le_refl 1) ζ).comp
            (CategoryTheory.Abelian.Ext.mk₀ S.f) (add_zero 2) := rfl
      _ = PT.e1aShiftEquiv SN hSN S.X₂ 1 (le_refl 1)
            (ζ.comp (CategoryTheory.Abelian.Ext.mk₀ S.f) (add_zero 1)) := (hnat ζ).symm
      _ = PT.e1aShiftEquiv SN hSN S.X₂ 1 (le_refl 1)
            (η.comp (CategoryTheory.Abelian.Ext.mk₀ S.f) (add_zero 1)) :=
            congrArg _ hζη'
      _ = (PT.e1aShiftEquiv SN hSN S.X₁ 1 (le_refl 1) η).comp
            (CategoryTheory.Abelian.Ext.mk₀ S.f) (add_zero 2) := hnat η
      _ = ((CategoryTheory.Abelian.Ext.mk₀ S.f).postcomp SN.X₃ (add_zero 2))
          (PT.e1aShiftEquiv SN hSN S.X₁ 1 (le_refl 1) η) := rfl
  exact (PT.e1aShiftEquiv SN hSN S.X₁ 1 (le_refl 1)).injective hshift

end Work.SSGRoute.ExtChain
