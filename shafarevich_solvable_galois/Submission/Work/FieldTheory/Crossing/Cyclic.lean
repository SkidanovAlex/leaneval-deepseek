/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cyclic extensions of prescribed degree over `ℚ`

For every `n ≥ 1` there is a cyclic extension of `ℚ` of degree `n`.  The construction is the
classical one: pick a prime `p ≡ 1 (mod n)` (Dirichlet), so that `(ZMod p)ˣ` is cyclic of order
`p - 1`; the kernel of the natural surjection `(ZMod p)ˣ → Multiplicative (ZMod n)` provides,
via the Galois correspondence inside `ℚ⟮ζ_p⟯`, a subfield whose Galois group is
`Multiplicative (ZMod n)`.

## Main declarations

* `exists_cyclic_subfield_of_prime` : the construction given a prime `p` with `n ∣ p - 1`
* `exists_cyclic_field_of_card` : for every `n ≠ 0` a cyclic degree-`n` extension of `ℚ`

-/
import Mathlib
import Submission.Work.FieldTheory.Crossing.Disjoint
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.FieldTheory.Crossing

open scoped Classical
open Polynomial

noncomputable section

set_option linter.style.haveILetI false

/-- Given a prime `p` with `n ∣ p - 1`, there is a subfield `M ≤ ℚ⟮ζ_p⟯` of `AlgebraicClosure ℚ`
which is finite Galois over `ℚ` with `Gal(M/ℚ) ≃* Multiplicative (ZMod n)`.

The subgroup is the kernel of the surjection `Gal(ℚ⟮ζ_p⟯/ℚ) ≃* (ZMod p)ˣ → Multiplicative
(ZMod n)` and `M` is its fixed field; the Galois group of a fixed field of a normal subgroup `K`
is `Gal/K`. -/
theorem exists_cyclic_subfield_of_prime (p n : ℕ) [NeZero p] [NeZero n] (hp : Nat.Prime p)
    (hdiv : n ∣ p - 1) :
    ∃ M : IntermediateField ℚ (AlgebraicClosure ℚ), M ≤ CycloField p ∧ FiniteDimensional ℚ M ∧
      IsGalois ℚ M ∧ Nonempty (Multiplicative (ZMod n) ≃* (M ≃ₐ[ℚ] M)) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI hFDC : FiniteDimensional ℚ ↥(CycloField p) := finiteDimensional_cycloField p
  haveI hGalC : IsGalois ℚ ↥(CycloField p) := isGalois_cycloField p
  -- the two isomorphisms identifying `Gal(ℚ⟮ζ_p⟯/ℚ)` with `Multiplicative (ZMod (p - 1))`
  let E : Gal(↥(CycloField p)/ℚ) ≃* (ZMod p)ˣ := cycloFieldGalEquiv p
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  have hcyc : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime hp
  let cyc : (ZMod p)ˣ ≃* Multiplicative (ZMod (p - 1)) :=
    (hcard ▸ zmodCyclicMulEquiv hcyc).symm
  -- the reduction `ZMod (p - 1) → ZMod n`
  let χ : Multiplicative (ZMod (p - 1)) →* Multiplicative (ZMod n) :=
    AddMonoidHom.toMultiplicative (ZMod.castHom hdiv (ZMod n)).toAddMonoidHom
  let g : Gal(↥(CycloField p)/ℚ) →* Multiplicative (ZMod n) := χ.comp (E.trans cyc).toMonoidHom
  have hχ : Function.Surjective χ := by
    intro y
    obtain ⟨a, ha⟩ := ZMod.castHom_surjective hdiv (Multiplicative.toAdd y)
    refine ⟨Multiplicative.ofAdd a, ?_⟩
    show Multiplicative.ofAdd ((ZMod.castHom hdiv (ZMod n)) a) = y
    rw [ha, ofAdd_toAdd]
  have hg : Function.Surjective g := hχ.comp (E.trans cyc).surjective
  let K : Subgroup Gal(↥(CycloField p)/ℚ) := g.ker
  have hK : K.Normal := g.normal_ker
  let M : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.lift (IntermediateField.fixedField K)
  have hle : M ≤ CycloField p := IntermediateField.lift_le _
  have hlift : ↥(IntermediateField.fixedField K) ≃ₐ[ℚ] ↥M :=
    IntermediateField.liftAlgEquiv (IntermediateField.fixedField K)
  haveI hFDfix : FiniteDimensional ℚ ↥(IntermediateField.fixedField K) :=
    IntermediateField.finiteDimensional_left _
  haveI hGalfix : IsGalois ℚ ↥(IntermediateField.fixedField K) :=
    @IsGalois.of_fixedField_normal_subgroup ℚ ↥(CycloField p) _ _ _ hGalC K hK
  refine ⟨M, hle, hlift.toLinearEquiv.finiteDimensional, IsGalois.of_algEquiv hlift, ⟨?_⟩⟩
  exact (QuotientGroup.quotientKerEquivOfSurjective g hg).symm.trans
    ((@IsGalois.normalAutEquivQuotient ℚ ↥(CycloField p) _ _ _ hFDC hGalC K hK).trans
      (AlgEquiv.autCongr hlift))

/-- **Cyclic extensions of prescribed degree.**  For every `n ≥ 1` there is a finite Galois
extension of `ℚ` (inside `AlgebraicClosure ℚ`) with Galois group `Multiplicative (ZMod n)`. -/
theorem exists_cyclic_field_of_card (n : ℕ) (hn : n ≠ 0) :
    ∃ M : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ M ∧ IsGalois ℚ M ∧
      Nonempty (Multiplicative (ZMod n) ≃* (M ≃ₐ[ℚ] M)) := by
  haveI : NeZero n := ⟨hn⟩
  obtain ⟨p, hp, -, hmod⟩ := Nat.exists_prime_gt_modEq_one 0 hn
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hdiv : n ∣ p - 1 := (Nat.modEq_iff_dvd' (le_of_lt hp.one_lt)).mp hmod.symm
  obtain ⟨M, -, hfd, hG, hiso⟩ := exists_cyclic_subfield_of_prime p n hp hdiv
  exact ⟨M, hfd, hG, hiso⟩

end

end Work.FieldTheory.Crossing
