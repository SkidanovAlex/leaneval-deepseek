import Mathlib
import Submission.Work.SSGRoute.GrunwaldEscapeCore.OrthImports
import Submission.Work.SSGRoute.GrunwaldEscapeCore.Vocab
import Submission.Work.SSGRoute.InertiaDefs
import Submission.Work.SSGRoute.ZDataMup.LocalUnramified.kummerCharZMod_eq_zero_iff_apply_sqrt
import Submission.Work.SSGRoute.ZDataTwo.mem_fixingSubgroup_adjoin_simple
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Kummer character / inertia dictionary lemmas for the N2v2 orthogonality

Two small, purely Kummer-theoretic lemmas used by the orthogonality computation of
`Work.SSGRoute.N2v2.orthogonality_hsplit_proved`:

* `kummerCharZMod_eq_zero_of_isInertia_of_unramified` — if the Kummer field `↥K(c^{1/p})` of `c` is
  contained in a level `F` that is unramified at the place `A`, then the Kummer character of `c`
  kills the inertia subgroup `I_A` of `A`;
* `not_isRamifiedIn_of_kummerChar_eq_zero_on_inertia` — conversely, if the Kummer character of `c`
  kills the inertia subgroup, then `↥K(c^{1/p})/↥K` is unramified at `A`.
-/

namespace Work.SSGRoute.N2v2

open _root_.SSGRoute

/-- **Unramified at the level implies the Kummer character kills the inertia.** -/
theorem kummerCharZMod_eq_zero_of_isInertia_of_unramified (p : ℕ) [Fact p.Prime] (k Ω : Type)
    [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (c : (↥K)ˣ)
    (F : IntermediateField ↥K Ω) [FiniteDimensional ↥K F] [IsGalois ↥K F]
    (hF : NK.LocalAnabelian.kummerField (p := p) (K' := Ω) c ≤ F)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace ↥K A)
    (hunr : ¬ SSGRoute.IsRamifiedIn ↥K F A)
    (σ : Ω ≃ₐ[↥K] Ω) (hσ : SSGRoute.IsInertia ↥K A σ) :
    Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c σ = 0 := by
  -- `hunr` unfolds to the statement that every inertia element fixes `F` pointwise.
  have hmem : σ ∈ F.fixingSubgroup := by
    by_contra hcon
    exact hunr ⟨σ, hσ, hcon⟩
  -- a chosen `p`-th root of `c` lies in the Kummer field, hence in `F`
  have hroot : ((Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) p c : Ω)) ∈ F :=
    hF (NK.LocalAnabelian.mem_kummerField_of_pow_eq (K' := Ω)
      (Work.SSGRoute.kummerSqrtZMod_pow (Ω := Ω) p c))
  have hfix : (σ : Ω → Ω) (Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) p c : Ω) =
      (Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) p c : Ω) :=
    (IntermediateField.mem_fixingSubgroup_iff F σ).mp hmem _ hroot
  rw [Work.SSGRoute.kummerCharZMod_apply]
  exact Work.SSGRoute.kummerIdx_eq_zero_of_apply_eq p hζ c _
    (Work.SSGRoute.kummerSqrtUnitZMod_pow (Ω := Ω) p c) σ hfix

/-- **The Kummer character killing the inertia forces the Kummer extension to be unramified.** -/
theorem not_isRamifiedIn_of_kummerChar_eq_zero_on_inertia (p : ℕ) [Fact p.Prime] (k Ω : Type)
    [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (c : (↥K)ˣ)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace ↥K A)
    (h : ∀ σ : Ω ≃ₐ[↥K] Ω, SSGRoute.IsInertia ↥K A σ →
      Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c σ = 0) :
    ¬ SSGRoute.IsRamifiedIn ↥K (NK.LocalAnabelian.kummerField (p := p) (K' := Ω) c) A := by
  rintro ⟨σ, hσ, hσnot⟩
  -- the Kummer character vanishes exactly when `σ` fixes the chosen `p`-th root of `c`
  have hfix : σ (Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) p c : Ω) =
      (Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) p c : Ω) :=
    (Work.SSGRoute.ZDataMup.LocalUnramified.kummerCharZMod_eq_zero_iff_apply_sqrt p hζ c σ).mp
      (h σ hσ)
  -- the Kummer field is the adjunction of that root over `↥K`
  have hgen : NK.LocalAnabelian.kummerField (p := p) (K' := Ω) c =
      IntermediateField.adjoin (↥K) ({(Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) p c : Ω)} : Set Ω) :=
    NK.UchidaKummer.Kummer.kummerField_eq_adjoin_simple p Fact.out hζ c
      (Work.SSGRoute.kummerSqrtZMod_pow (Ω := Ω) p c)
  have hmem : σ ∈ (IntermediateField.adjoin (↥K)
      ({(Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) p c : Ω)} : Set Ω)).fixingSubgroup :=
    Work.SSGRoute.ZDataTwo.mem_fixingSubgroup_adjoin_simple
      (Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) p c : Ω) σ hfix
  exact hσnot (hgen.symm ▸ hmem)

end Work.SSGRoute.N2v2
