import Mathlib
import Submission.Work.Hering.AppVII.brauer_lift_aux
import Submission.Work.Hering.AppVII.iota_injective
import Submission.Work.Hering.AppVII.exists_charLift
import Submission.Work.CharCore.Main
import Submission.Work.NormalComplement.AppVII.TildeEAux
import Submission.Work.NormalComplement.AppVII.TildeEScalar
import Submission.Work.NormalComplement.AppVII.TildeEIdentities

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement.AppVII

/-- The five `ℤ[ζ_|A|][A]` identities satisfied by the integral lifts `tildeE χ = |A| • e_χ` of the
central primitive idempotents `e_χ = (χ(1)/|A|) ∑_g χ(g⁻¹) g ∈ ℂ[A]` of a finite group `A`:
centrality, the `|A|`-idempotent relation, orthogonality of distinct irreducible characters,
`∑_χ tildeE χ = |A|`, and `tildeE χ · z = tildeE χ` whenever `χ z = χ 1`.

Each identity is proved in `ℂ[A]` (where the corresponding statement about `e_χ` is standard
character theory), then transferred along the injective ring homomorphism
`iota : ℤ[ζ_|A|] → ℂ` (`iota_injective`).  Conjuncts 1–4 are the (currently `sorry`-ed) statements
`tildeE_central`, `tildeE_mul_self`, `tildeE_mul_eq_zero`, `sum_tildeE` of
`Submission/Work/Hering/AppVII/brauer_lift_aux.lean`: redo them here from scratch, do NOT cite
those sorried theorems (the axiom check would reveal `sorryAx`). -/
theorem TildeEProps {A : Type*} [Group A] [Fintype A] :
    (∀ (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A)
      (x : MonoidAlgebra (Work.Hering.AppVII.CycloRing (Nat.card A)) A),
        x * Work.Hering.AppVII.tildeE χ hχ = Work.Hering.AppVII.tildeE χ hχ * x) ∧
    (∀ (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A),
        Work.Hering.AppVII.tildeE χ hχ * Work.Hering.AppVII.tildeE χ hχ =
          (Nat.card A : Work.Hering.AppVII.CycloRing (Nat.card A)) •
            Work.Hering.AppVII.tildeE χ hχ) ∧
    (∀ (χ χ' : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A) (hχ' : χ' ∈ Work.CharCore.Irr A), χ ≠ χ' →
        Work.Hering.AppVII.tildeE χ hχ * Work.Hering.AppVII.tildeE χ' hχ' = 0) ∧
    (Finset.sum (Work.CharCore.Irr A).attach (fun x => Work.Hering.AppVII.tildeE x.1 x.2) =
        (Nat.card A : Work.Hering.AppVII.CycloRing (Nat.card A)) •
          (1 : MonoidAlgebra (Work.Hering.AppVII.CycloRing (Nat.card A)) A)) ∧
    (∀ (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A) (z : A), χ z = χ 1 →
        Work.Hering.AppVII.tildeE χ hχ *
          MonoidAlgebra.single z (1 : Work.Hering.AppVII.CycloRing (Nat.card A)) =
        Work.Hering.AppVII.tildeE χ hχ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- centrality of `tildeE χ`
    intro χ hχ x
    exact LiftTildeECentral χ hχ x
  · -- the `|A|`-idempotent relation
    intro χ hχ
    refine iotaAlg_injective ?_
    rw [map_mul]
    rw [iotaAlg_tildeE χ hχ]
    rw [iotaAlg_smul]
    rw [iotaAlgHom_apply, map_natCast, iotaAlg_tildeE χ hχ]
    exact Eℂ_mul_self hχ
  · -- orthogonality of distinct characters
    intro χ χ' hχ hχ' hne
    refine iotaAlg_injective ?_
    rw [map_mul, map_zero]
    rw [iotaAlg_tildeE χ hχ, iotaAlg_tildeE χ' hχ']
    exact Eℂ_mul_eq_zero hχ hχ' hne
  · -- the sum of the `tildeE χ` is `|A|`
    refine iotaAlg_injective ?_
    rw [map_sum]
    have h₁ : (∑ x ∈ (Work.CharCore.Irr A).attach,
          iotaAlg (Work.Hering.AppVII.tildeE x.1 x.2)) =
        ∑ x ∈ (Work.CharCore.Irr A).attach, Work.Hering.AppVII.Eℂ x.1 :=
      Finset.sum_congr rfl fun x _ => iotaAlg_tildeE x.1 x.2
    rw [h₁, Finset.sum_attach, sum_Eℂ, iotaAlg_smul, iotaAlgHom_apply, map_natCast, map_one]
  · -- `tildeE χ · z = tildeE χ` when `z` lies in the kernel of `χ`
    intro χ hχ z hz
    refine iotaAlg_injective ?_
    rw [map_mul]
    rw [iotaAlg_single]
    rw [iotaAlgHom_apply, map_one]
    rw [iotaAlg_tildeE χ hχ]
    exact Eℂ_mul_single hχ hz

end Work.NormalComplement.AppVII
