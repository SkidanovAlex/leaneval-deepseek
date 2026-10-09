import Mathlib
import Submission.Work.SSGRoute.H9.swPairingValueFrob
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.H9

open Work.SSGRoute.ZDataMup.OddForm

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

/-- **Antisymmetry of the odd-`p` local pairing.**  For `p ≠ 2` the bilinear form `oPairForm` at a
finite place satisfies `⟨x, y⟩ + ⟨y, x⟩ = 0` for all `x`, `y`.

This is bilinearity together with the alternation `⟨z, z⟩ = 0`
(`Work.SSGRoute.ZDataMup.swz_oPairForm_self_eq_zero`) applied to `z = x + y`: expanding
`⟨x + y, x + y⟩ = 0` kills the two diagonal terms and leaves `⟨x, y⟩ + ⟨y, x⟩`. -/
theorem swOoPairForm_add_swap {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {k Ω : Type} [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    {A : ValuationSubring Ω} (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (hA : SSGRoute.IsFinPlace k A)
    (x y : Work.SSGRoute.ZDataMup.LTRecFamHonest.hV (K := K) (p := p) (k := k) (Ω := Ω) A) :
    oPairForm (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x y
      + oPairForm (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA y x = 0 := by
  have hx := Work.SSGRoute.ZDataMup.swz_oPairForm_self_eq_zero (K := K) (p := p) (k := k) (Ω := Ω)
    (A := A) hp ζ hζ hA x
  have hy := Work.SSGRoute.ZDataMup.swz_oPairForm_self_eq_zero (K := K) (p := p) (k := k) (Ω := Ω)
    (A := A) hp ζ hζ hA y
  have hxy := Work.SSGRoute.ZDataMup.swz_oPairForm_self_eq_zero (K := K) (p := p) (k := k) (Ω := Ω)
    (A := A) hp ζ hζ hA (x + y)
  simp only [map_add, LinearMap.add_apply, hx, hy, zero_add, add_zero] at hxy
  rw [add_comm] at hxy
  exact hxy

theorem swOoPairAt_add_swap {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {k Ω : Type} [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (A : ValuationSubring Ω)
    (hA : _root_.SSGRoute.IsFinPlace k A) (a b : (Ω ≃ₐ[k] Ω) → ZMod p) :
    Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA a b
      + Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA b a
      = 0 := by
  rw [show Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA a b
        = oPairForm (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA
          (Work.SSGRoute.toClass p k Ω K (ZMod p)
            (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a)
          (Work.SSGRoute.toClass p k Ω K (ZMod p)
            (SSGRoute.decomp k A ⊓ K.fixingSubgroup) b) from rfl,
      show Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA b a
        = oPairForm (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA
          (Work.SSGRoute.toClass p k Ω K (ZMod p)
            (SSGRoute.decomp k A ⊓ K.fixingSubgroup) b)
          (Work.SSGRoute.toClass p k Ω K (ZMod p)
            (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a) from rfl]
  exact swOoPairForm_add_swap (K := K) (p := p) (k := k) (Ω := Ω) (A := A) hp ζ hζ hA _ _

end Work.SSGRoute.H9
