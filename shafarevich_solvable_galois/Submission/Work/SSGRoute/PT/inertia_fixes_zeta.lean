import Mathlib
import Submission.Work.SSGRoute.InertiaDefs
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.NK.TameStructureDeep.Tame.InertiaFieldAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

open scoped Pointwise

/-- **The inertia group at a finite place of residue characteristic `≠ p` fixes the `p`-th roots of
unity.**

Let `k` be a number field, `Ω` an algebraic closure of `k`, `A` a finite place of `Ω` over `k` at
which the rational prime `p` is a *unit* (the hypothesis `¬ A.valuation (p) < 1`, i.e. `A` does not
lie over `p`).  Then every element of the inertia subgroup `I_A` fixes every primitive `p`-th root
of unity `ζ ∈ Ω`.

The proof is the standard reduction-modulo-`𝔪` argument.  The root of unity `ζ` is integral over
`ℤ`, hence lies in the valuation ring `A`; since `(p : ↥A)` is a unit, the residue map is injective
on `p`-th roots of unity (`NK.TameStructureDeep.Tame.eq_of_residue_eq_of_pow_eq_one`).  An element
`ι ∈ I_A` acts trivially on the residue field, so `ι ζ` and `ζ` — two `p`-th roots of unity in `A`
— have equal residues, whence they are equal. -/
theorem inertia_fixes_zeta
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (h : ¬ A.valuation ((p : ℚ) : Ω) < 1)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) :
    ∀ ι ∈ Work.SSGRoute.inertiaSub k Ω A, ι • ζ = ζ := by
  intro ι hι
  have hp0 : p ≠ 0 := (Fact.out (p := p.Prime)).ne_zero
  have hI : SSGRoute.IsInertia k A ι := (Work.SSGRoute.mem_inertiaSub k Ω A ι).mp hι
  -- `ζ` is integral over `ℤ`, hence lies in the valuation ring `A`
  have hmem : ζ ∈ A :=
    NK.TameStructureDeep.Tame.mem_valuationSubring_of_isPrimitiveRoot A hζ hp0
  -- the hypothesis on `p` says exactly that `(p : ↥A)` is a unit
  have hunit : IsUnit ((p : ℕ) : ↥A) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hbad
    exact h (by
      have := (ValuationSubring.valuation_lt_one_iff A ((p : ℕ) : ↥A)).mp hbad
      simpa using this)
  let ζA : ↥A := ⟨ζ, hmem⟩
  have hpow : ζA ^ p = 1 := by
    apply Subtype.ext
    change (A.subtype (ζA ^ p)) = (A.subtype 1)
    rw [map_pow, map_one]
    exact hζ.pow_eq_one
  let g : ↥(A.decompositionSubgroup k) := ⟨ι, hI.1⟩
  have hy_pow : (g • ζA) ^ p = 1 := by
    have hh := map_pow (MulSemiringAction.toRingHom ↥(A.decompositionSubgroup k) ↥A g) ζA p
    rw [hpow, map_one] at hh
    rw [MulSemiringAction.toRingHom_apply] at hh
    exact hh.symm
  -- `ι ∈ I_A` acts trivially on the residue field, so `ζA` and `g • ζA` have equal residues
  have hres : IsLocalRing.residue ↥A ζA = IsLocalRing.residue ↥A (g • ζA) := by
    have hmem_m : (g • ζA) - ζA ∈ IsLocalRing.maximalIdeal ↥A := by
      rw [ValuationSubring.valuation_lt_one_iff]
      rw [AddSubgroupClass.coe_sub, NK.Ramification.coe_smul]
      simp only [g, ζA]
      exact hI.2 ζ hmem
    have hzero : IsLocalRing.residue ↥A ((g • ζA) - ζA) = 0 :=
      (IsLocalRing.residue_eq_zero_iff ((g • ζA) - ζA)).mpr hmem_m
    rw [map_sub, sub_eq_zero] at hzero
    exact hzero.symm
  -- reduction is injective on `p`-th roots of unity since `(p : ↥A)` is a unit
  have heq : ζA = g • ζA :=
    NK.TameStructureDeep.Tame.eq_of_residue_eq_of_pow_eq_one hunit hpow hy_pow hres
  have hmain : ι ζ = ζ := by
    have h2 : ((g • ζA : ↥A) : Ω) = (ζA : Ω) := by rw [← heq]
    rw [NK.Ramification.coe_smul] at h2
    simpa only [g, ζA] using h2
  exact hmain

end Work.SSGRoute.PT
