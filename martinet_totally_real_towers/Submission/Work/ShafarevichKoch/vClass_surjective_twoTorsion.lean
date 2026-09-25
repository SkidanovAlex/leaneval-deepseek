import Mathlib
import Submission.Work.ShafarevichKoch.Defs
import Submission.Work.ShafarevichKoch.SquareRoot

/-!
# `Work.ShafarevichKoch.vClass_surjective_twoTorsion`

**The Kummer two-descent `vClass : V_∅ → Cl(F)[2]` is surjective.**

Koch's group `V_∅ = VTwo F = {x ∈ Fˣ : (x) = I²}` (`Defs.lean`) maps to the class group by
sending `x` to the ideal class of the square root of `(x)` (the Kummer two-descent).  This file
proves that the map hits every `2`-torsion class, so that the exact sequence

`0 → 𝓞_Fˣ/(𝓞_Fˣ)² → V_∅/Fˣ² → Cl(F)[2] → 0`

of Koch, *Galois theory of `p`-extensions*, Ch. 11 (with `p = 2`), is exact at `Cl(F)[2]`.

## Proof

`ClassGroup.induction` writes `c = [I]` for an invertible fractional ideal `I`.  From `c ^ 2 = 1`
we get `[I * I] = [I] * [I] = c ^ 2 = 1`, so `I * I` is principal
(`ClassGroup.mk_eq_one_iff` + `FractionalIdeal.isPrincipal_iff`): `I * I = (x)` for some
`x : F`; since `I * I ≠ 0` we have `x ≠ 0` and may regard it as a unit `x' : Fˣ`.  Then
`x' ∈ V_∅` by construction, and its square root `I` is *the* square root of `(x')` by
`squareRoot_unique`, so `vClass F x' = [I] = c`.
-/

open scoped Classical
open scoped NumberField

namespace Work.ShafarevichKoch

/-- **The Kummer two-descent is surjective onto the `2`-torsion of the class group.** -/
theorem vClass_surjective_twoTorsion (F : Type*) [Field F] [NumberField F]
    (c : ClassGroup (NumberField.RingOfIntegers F)) (hc : c ^ 2 = 1) :
    ∃ x : Work.ShafarevichKoch.VTwo F, Work.ShafarevichKoch.vClass F x = c := by
  classical
  -- Every class is the class of an invertible fractional ideal.
  obtain ⟨J, hJ⟩ : ∃ J : IdealUnit F, ClassGroup.mk F J = c :=
    ClassGroup.induction (K := F) (P := fun c => ∃ J : IdealUnit F, ClassGroup.mk F J = c)
      (fun I => ⟨I, rfl⟩) c
  -- `J * J` therefore represents `c ^ 2 = 1`, i.e. it is principal.
  have hmk : ClassGroup.mk F (J * J) = 1 := by
    rw [map_mul, hJ, ← pow_two, hc]
  have hprin : ((J * J : IdealUnit F) : Submodule (𝓞 F) F).IsPrincipal :=
    (ClassGroup.mk_eq_one_iff).mp hmk
  -- Extract a generator `x` of `J * J`.
  obtain ⟨x, hx⟩ := (FractionalIdeal.isPrincipal_iff _).mp hprin
  have hx0 : x ≠ 0 := by
    intro h0
    have hzero : (↑(J * J) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0 := by
      rw [hx, h0, FractionalIdeal.spanSingleton_zero]
    exact Units.ne_zero (J * J) hzero
  let x' : Fˣ := Units.mk0 x hx0
  -- `(x') = J * J`.
  have hxJ : FracIdealOf F x' = J * J := by
    refine Units.ext ?_
    rw [Units.val_mul, FracIdealOf, coe_toPrincipalIdeal, Units.val_mk0]
    exact hx.symm
  -- Hence `x' ∈ V_∅`, with `J` an explicit square root of `(x')`.
  have hmem : x' ∈ VTwo F := ⟨J, by rw [hxJ]⟩
  refine ⟨⟨x', hmem⟩, ?_⟩
  -- The square root chosen in the definition of `vClass` is `J`, by uniqueness.
  have hchoose : Classical.choose (show IsSquareFracIdeal F (FracIdealOf F x') from hmem) = J := by
    refine squareRoot_unique F ?_
    rw [show Classical.choose (show IsSquareFracIdeal F (FracIdealOf F x') from hmem)
          * Classical.choose (show IsSquareFracIdeal F (FracIdealOf F x') from hmem)
        = FracIdealOf F x' from vClass_spec F ⟨x', hmem⟩]
    rw [hxJ]
  rw [vClass]
  rw [hchoose]
  exact hJ

end Work.ShafarevichKoch
