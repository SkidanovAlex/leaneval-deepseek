import Mathlib
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_mul_le
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.LocalForm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Kummer level is unchanged by multiplying the class by a square

`Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel β = ↥K(β^{1/p})` is the Kummer level of a global unit
`β`.  Multiplying `β` by a `p`-th power does not change the field (`(β x^p)^{1/p} = x · β^{1/p}`),
so in particular for `p = 2`

  `hLevel (b * (x * x)) = hLevel b`.

This is the level bookkeeping of step 1 of the p. 16 computation
(`ZDataTwo/TwoRec/NOTE_diagonal_p16_plan.md`): the pinned value `V` is computed at the Kummer level
of the representative `b`, and one may replace `b` by `b x²` (`z = b x²`, the normalised
representative) without changing the level — hence without changing the pinned value.
-/

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute
open Work.SSGRoute.ZDataMup.LTRecFamHonest

set_option linter.unusedSectionVars false

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]

/-- **The Kummer level of a `p`-th power is trivial.** -/
theorem hLevel_self_pow (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (x : (↥K)ˣ) :
    hLevel (Ω := Ω) (K := K) (p := p) (x ^ p) = ⊥ :=
  NK.LocalAnabelian.Kummer.kummerField_eq_bot_of_mem_powSubgroup (K' := Ω) (k := ↥K) p
    Fact.out hζ ⟨x, rfl⟩

/-- **The Kummer level is unchanged on multiplying by a `p`-th power.** -/
theorem hLevel_mul_pow_eq (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (b x : (↥K)ˣ) :
    hLevel (Ω := Ω) (K := K) (p := p) (b * x ^ p) =
      hLevel (Ω := Ω) (K := K) (p := p) b := by
  refine le_antisymm ?_ ?_
  · refine le_trans (hLevel_mul_le (Ω := Ω) (K := K) (p := p) b (x ^ p)) ?_
    rw [hLevel_self_pow (K := K) (Ω := Ω) ζ hζ x, sup_bot_eq]
  · have h := hLevel_div_le (Ω := Ω) (K := K) (p := p) (b * x ^ p) (x ^ p)
    have hid : (b * x ^ p) * (x ^ p)⁻¹ = b := by group
    rw [hid, hLevel_self_pow (K := K) (Ω := Ω) ζ hζ x, sup_bot_eq] at h
    exact h

/-- **The Kummer level is unchanged on multiplying the class by a square** (`p = 2`). -/
theorem hLevel_mul_sq_eq (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2) (b x : (↥K)ˣ) :
    hLevel (Ω := Ω) (K := K) (p := 2) (b * (x * x)) =
      hLevel (Ω := Ω) (K := K) (p := 2) b := by
  have := hLevel_mul_pow_eq (K := K) (Ω := Ω) (p := 2) ζ hζ b x
  rwa [pow_two] at this

end Work.SSGRoute.ZConstruction
