import Mathlib
import Submission.Work.MotT.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped NumberField

namespace Work.MotT

/-- **T13 (optional).** A number field has a normalized valuation: take any height-one prime `𝔭` of
the ring of integers `𝓞 𝕜` (`IsDedekindDomain` for a number field), the valuation
`𝔭.valuation 𝕜 : Valuation 𝕜 ℤᵐ⁰` and a uniformizer `π` of the local ring at `𝔭`
(`IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer`), so that `v π = ofAdd (-1)`.
Together with `Work.MotT.not_gen_three_of_val` this gives `theorem_1_2_1 (a)` on the T-route.
Declare it in namespace `Work.MotT` so that its full name is
`Work.MotT.exists_val_of_numberField`. -/
theorem exists_val_of_numberField (𝕜 : Type) [Field 𝕜] [NumberField 𝕜] :
    ∃ v : Valuation 𝕜 (WithZero (Multiplicative ℤ)), ∃ π : 𝕜, v π = Work.MotT.vOne := by
  -- `𝓞 𝕜` is a Dedekind domain which is not a field, so it has a maximal ideal, i.e. a
  -- height-one prime `𝔭`.
  have hnf : ¬ IsField (𝓞 𝕜) := NumberField.RingOfIntegers.not_isField 𝕜
  obtain ⟨M, -, hM⟩ := Ring.exists_maximal_of_not_isField hnf
  let 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 𝕜) :=
    (IsDedekindDomain.HeightOneSpectrum.equivMaximalSpectrum hnf).symm ⟨M, hM⟩
  -- The `𝔭`-adic valuation of `𝕜` and a uniformizer `π`.
  obtain ⟨π, hπ⟩ := 𝔭.valuation_exists_uniformizer 𝕜
  exact ⟨𝔭.valuation 𝕜, π, hπ⟩

end Work.MotT
