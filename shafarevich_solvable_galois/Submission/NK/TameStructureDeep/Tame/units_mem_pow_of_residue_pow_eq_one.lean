import Mathlib
import Submission.Commons.RingTheory.Henselian.units_mem_pow_of_residue_mem_pow
import Submission.NK.TameStructureDeep.Tame.exists_pow_eq_of_pow_card_div_eq_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.TameStructureDeep.Tame

/-- **Lifting `ℓ`-th powers of units out of the residue field.**

Let `R` be a Henselian local ring with finite residue field `k`, let `ℓ` be a prime
which is a unit of `R` and which divides `#k - 1`.  If the residue of a unit `u : Rˣ`
is killed by the power `(#k - 1) / ℓ`, then `u` is an `ℓ`-th power in `Rˣ`.

Indeed `kˣ` is cyclic of order `#k - 1`, so `residue u`, being killed by
`(#k - 1)/ℓ`, lies in the image of the `ℓ`-th power map of `kˣ`; and since `ℓ`
is a unit of `R`, an `ℓ`-th root of a unit lifts through a Henselian local ring. -/
theorem units_mem_pow_of_residue_pow_eq_one {R : Type*} [CommRing R]
    [HenselianLocalRing R] [Finite (IsLocalRing.ResidueField R)] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hunit : IsUnit (ℓ : R)) (hdiv : ℓ ∣ Nat.card (IsLocalRing.ResidueField R) - 1)
    (u : Rˣ)
    (h : (IsLocalRing.residue R (u : R)) ^
      ((Nat.card (IsLocalRing.ResidueField R) - 1) / ℓ) = 1) :
    u ∈ (powMonoidHom ℓ).range := by
  classical
  letI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  letI : Fintype (IsLocalRing.ResidueField R) := Fintype.ofFinite _
  -- The residue of `u` is killed by the power `(#k - 1) / ℓ` inside `kˣ`.
  have hres : (Units.map (IsLocalRing.residue R).toMonoidHom u) ^
      ((Nat.card (IsLocalRing.ResidueField R) - 1) / ℓ) = 1 := by
    apply Units.ext
    simpa using h
  -- Order of `kˣ`.
  have hcard : Fintype.card ((IsLocalRing.ResidueField R)ˣ) =
      Nat.card (IsLocalRing.ResidueField R) - 1 := by
    rw [Fintype.card_units, Nat.card_eq_fintype_card]
  have hdiv' : ℓ ∣ Fintype.card ((IsLocalRing.ResidueField R)ˣ) := by
    rw [hcard]; exact hdiv
  have hres' : (Units.map (IsLocalRing.residue R).toMonoidHom u) ^
      (Fintype.card ((IsLocalRing.ResidueField R)ˣ) / ℓ) = 1 := by
    rw [hcard]; exact hres
  -- `kˣ` is cyclic, so the residue of `u` is an `ℓ`-th power there.
  obtain ⟨y, hy⟩ :=
    exists_pow_eq_of_pow_card_div_eq_one (G := (IsLocalRing.ResidueField R)ˣ) hdiv' hres'
  -- Lift the `ℓ`-th root through the Henselian local ring.
  exact Commons.RingTheory.Henselian.units_mem_pow_of_residue_mem_pow ℓ hunit u
    (MonoidHom.mem_range.mpr ⟨y, by rw [powMonoidHom_apply]; exact hy⟩)

end NK.TameStructureDeep.Tame
