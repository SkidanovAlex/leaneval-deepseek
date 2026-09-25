import Mathlib
import Submission.Work.CFTLib.RelShafDefs
import Submission.Work.Tower.Unramified.Discriminant

namespace Work.CFTLib

open NumberField

theorem isUnramified_of_le {F K K' : Type} [Field F] [NumberField F] [Field K] [NumberField K]
    [Field K'] [NumberField K'] [Algebra F K] [Algebra F K'] [Algebra K K']
    [IsScalarTower F K K'] [FiniteDimensional F K] [FiniteDimensional F K']
    (h : CFTLib.IsUnramified F K') : CFTLib.IsUnramified F K := by
  haveI : Module.Finite K K' := Module.Finite.of_restrictScalars_finite F K K'
  haveI : Algebra.IsAlgebraic K K' := Algebra.IsAlgebraic.of_finite K K'
  have hinf : IsUnramifiedAtInfinitePlaces F K := by
    haveI := h.2
    exact IsUnramifiedAtInfinitePlaces.bot F K K'
  refine ⟨?_, hinf⟩
  rw [← Work.Tower.isUnramifiedExtensionForallPrimes_iff_differentIdeal_eq_top]
  intro 𝔓 h𝔓
  haveI := h𝔓
  obtain ⟨𝔔⟩ := (inferInstance : Nonempty (𝔓.primesOver (𝓞 K')))
  have hK' : Work.Tower.IsUnramifiedExtensionForallPrimes F K' :=
    Work.Tower.isUnramifiedExtensionForallPrimes_iff_differentIdeal_eq_top.mpr h.1
  have h1 : 𝔔.1.ramificationIdx (𝓞 F) = 1 := hK' 𝔔.1 𝔔.2.1
  have ht := Ideal.ramificationIdx_tower (R := 𝓞 F) (S := 𝓞 K) (T := 𝓞 K') 𝔓 𝔔.1
  rw [ht] at h1
  exact Nat.dvd_one.mp ⟨_, h1.symm⟩

end Work.CFTLib
