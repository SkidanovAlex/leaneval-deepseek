import Mathlib
import Submission.Work.CFT.ClassFormation.Defs

/-!
# Subadditivity of the `p`-rank along a short exact sequence

For an abelian group `A` the `p`-rank `Work.CFT.ClassFormation.rankP p A` is
`dim_{𝔽_p} (𝔽_p ⊗_ℤ A)`, i.e. `dim_{𝔽_p} A/pA`.

The main result of this file is

`Work.CFTLib.rankP_le_add_of_shortExact_of_finite`:

if `0 → X --f--> Y --g--> Z → 0` is a short exact sequence of abelian groups and
`𝔽_p ⊗_ℤ X` is finite dimensional over `𝔽_p`, then
`rankP p Y ≤ rankP p X + rankP p Z`.

The proof is the elementary one.  Tensoring with `𝔽_p` over `ℤ` is right exact, so
`𝔽_p ⊗ X → 𝔽_p ⊗ Y → 𝔽_p ⊗ Z → 0` is exact.  Writing `F`, `G` for the two induced
`𝔽_p`-linear maps, `G` is surjective and `F.range = G.ker`, so if `𝔽_p ⊗ Y` is
finite dimensional the rank–nullity theorem gives

  `finrank (𝔽_p ⊗ Y) = finrank G.ker + finrank (𝔽_p ⊗ Z)`

and `G.ker = F.range` is a quotient of `𝔽_p ⊗ X` (hence has dimension at most
`finrank (𝔽_p ⊗ X)`).  If `𝔽_p ⊗ Y` is infinite dimensional its `finrank` is `0`
and the inequality is trivial.

The abstract rank–nullity statement is proved once, as
`Work.CFTLib.finrank_le_add_of_range_eq_ker`, and then applied to the base change
`f.baseChange 𝔽_p`, `g.baseChange 𝔽_p` of the given maps.
-/

open scoped TensorProduct

namespace Work.CFTLib

/-- Rank–nullity inequality for a pair of `R`-linear maps with `f.range = g.ker`:
if `g` is surjective and `A` is finite dimensional then
`finrank B ≤ finrank A + finrank C`. -/
theorem finrank_le_add_of_range_eq_ker {R : Type*} [DivisionRing R]
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hg : Function.Surjective g)
    (hex : f.range = g.ker) (hA : Module.Finite R A) :
    Module.finrank R B ≤ Module.finrank R A + Module.finrank R C := by
  have hfinA : Module.Finite R A := hA
  by_cases hB : FiniteDimensional R B
  · -- finite dimensional case: rank–nullity
    have hkey := Submodule.finrank_quotient_add_finrank (R := R) (M := B) f.range
    rw [hex] at hkey
    have e : (B ⧸ g.ker) ≃ₗ[R] C := g.quotKerEquivOfSurjective hg
    rw [LinearEquiv.finrank_eq e] at hkey
    -- `hkey : finrank C + finrank g.ker = finrank B`
    have hker : Module.finrank R g.ker ≤ Module.finrank R A := by
      rw [← hex]
      calc Module.finrank R f.range
          = Module.finrank R (A ⧸ f.ker) := (LinearEquiv.finrank_eq f.quotKerEquivRange).symm
        _ ≤ Module.finrank R A := Submodule.finrank_quotient_le f.ker
    omega
  · -- infinite dimensional case: `finrank` vanishes
    rw [Module.finrank_of_infinite_dimensional hB]
    exact Nat.zero_le _

set_option linter.unusedVariables false in
/-- **Subadditivity of `rankP` along a short exact sequence.**
If `0 → X → Y → Z → 0` is a short exact sequence of abelian groups and
`𝔽_p ⊗_ℤ X` is finite dimensional over `𝔽_p`, then
`rankP p Y ≤ rankP p X + rankP p Z`. -/
theorem rankP_le_add_of_shortExact_of_finite {p : ℕ} [Fact p.Prime] {X Y Z : Type}
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] (f : X →+ Y) (g : Y →+ Z)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : LinearMap.range f.toIntLinearMap = LinearMap.ker g.toIntLinearMap)
    (hX : Module.Finite (ZMod p) (TensorProduct ℤ (ZMod p) X)) :
    Work.CFT.ClassFormation.rankP p Y
      ≤ Work.CFT.ClassFormation.rankP p X + Work.CFT.ClassFormation.rankP p Z := by
  -- the short exact sequence, as a pair of `ℤ`-linear maps
  have hfg : Function.Exact ⇑(f.toIntLinearMap) ⇑(g.toIntLinearMap) :=
    LinearMap.exact_iff.mpr hex.symm
  have hg' : Function.Surjective ⇑(g.toIntLinearMap) := hg
  -- base change to `𝔽_p` is right exact
  have hsurj : Function.Surjective ⇑(g.toIntLinearMap.baseChange (ZMod p)) :=
    LinearMap.baseChange_surjective (ZMod p) hg'
  have hker : (g.toIntLinearMap.baseChange (ZMod p)).ker
      = (f.toIntLinearMap.baseChange (ZMod p)).range := by
    exact LinearMap.exact_iff.mp (lTensor_exact (ZMod p) hfg hg')
  have hmain := finrank_le_add_of_range_eq_ker (R := ZMod p)
    (f.toIntLinearMap.baseChange (ZMod p)) (g.toIntLinearMap.baseChange (ZMod p))
    hsurj hker.symm hX
  simpa only [Work.CFT.ClassFormation.rankP] using hmain

end Work.CFTLib
