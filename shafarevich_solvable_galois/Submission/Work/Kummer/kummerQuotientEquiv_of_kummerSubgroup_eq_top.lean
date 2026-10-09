import Mathlib
import Submission.Work.Kummer.Pairing
import Submission.Work.Kummer.kummerPairing_bijective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

namespace Work.Kummer

/-- **The Kummer quotient when the Kummer subgroup is everything.**  If `L/K` is a finite Galois
extension, `ζ ∈ K` is a primitive `n`-th root of unity, and every unit of `K` is an `n`-th power
in `L` (`kummerSubgroup n K L = ⊤`), then the Kummer pairing identifies
`Kˣ / (Kˣ)^n` with the group of homomorphisms `Gal(L/K) →* μ_n`.

Indeed the inclusion `Kˣ ∩ (Lˣ)^n ≤ Kˣ` is then an isomorphism, so
`(Kˣ ∩ (Lˣ)^n)/(Kˣ)^n ≃ Kˣ/(Kˣ)^n`, and the Kummer pairing `kummerPairing hζ`
is bijective (`Work.Kummer.kummerPairing_bijective`). -/
theorem kummerQuotientEquiv_of_kummerSubgroup_eq_top {K : Type u} {L : Type v} [Field K]
    [Field L] [Algebra K L] {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    [FiniteDimensional K L] [IsGalois K L] (htop : kummerSubgroup n K L = ⊤) :
    Nonempty ((Kˣ ⧸ nthPowerSubgroup n Kˣ) ≃* (Gal(L/K) →* rootsOfUnity n K)) := by
  have hbij := kummerPairing_bijective (K := K) (L := L) hζ
  -- The inclusion `Kˣ ∩ (Lˣ)^n → Kˣ` is a bijection, since the Kummer subgroup is all of `Kˣ`.
  let e : kummerSubgroup n K L ≃* Kˣ :=
    MulEquiv.ofBijective (Subgroup.subtype (kummerSubgroup n K L)) (by
      constructor
      · exact Subgroup.subtype_injective _
      · intro x
        exact ⟨⟨x, by rw [htop]; trivial⟩, rfl⟩)
  -- It carries `(Kˣ)^n ∩ (Kˣ ∩ (Lˣ)^n) = (Kˣ)^n` onto `(Kˣ)^n`.
  have he : ((nthPowerSubgroup n Kˣ).subgroupOf (kummerSubgroup n K L)).map e =
      nthPowerSubgroup n Kˣ :=
    Subgroup.map_subgroupOf_eq_of_le (nthPowerSubgroup_le_kummerSubgroup n)
  exact ⟨(QuotientGroup.congr _ _ e he).symm.trans
    (MulEquiv.ofBijective (kummerPairing hζ) hbij)⟩

end Work.Kummer
