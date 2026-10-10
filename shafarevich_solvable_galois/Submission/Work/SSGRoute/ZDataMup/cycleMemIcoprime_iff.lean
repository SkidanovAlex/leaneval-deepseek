import Mathlib.Tactic.Have
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Submission.Work.SSGRoute.ZDataMup.CycleAux
import Submission.Work.SSGRoute.ZDataMup.LT_CyclePort
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup

open NK.CFTLib.ArtinReciprocityIdeal
open NK.GlobalCFT

namespace Cycle

variable {K : Type} [Field K] [NumberField K]

/-- **An idèle of the congruence subgroup of a cycle is a local unit at every prime of the
cycle**: `x ≡ 1` modulo the (positive) level of `c` at `𝔭` forces `v_𝔭(x) = 1`, hence the
fractional ideal of `x` has zero `𝔭`-adic exponent. -/
theorem count_idealOf_eq_zero_of_mem_congrSubgroup (c : Cycle K) {x : Idele K}
    (hx : x ∈ c.congrSubgroup) (𝔭 : HeightOneSpectrum (𝓞 K)) (h𝔭 : 𝔭 ∈ c.supp) :
    FractionalIdeal.count K 𝔭 (Idele.idealOf x) = 0 := by
  classical
  rw [Idele.count_idealOf, Idele.exp_def]
  have hlt : Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (((x (Place.ofFinite 𝔭)) : 𝔭.adicCompletion K) - 1) < 1 :=
    lt_of_le_of_lt (hx.1 𝔭 h𝔭) (level_lt_one c 𝔭)
  have hval : Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      ((x (Place.ofFinite 𝔭)) : 𝔭.adicCompletion K) = 1 := by
    have h := Valuation.map_add_eq_of_lt_left
      (v := Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)))
      (x := (1 : 𝔭.adicCompletion K))
      (y := ((x (Place.ofFinite 𝔭)) : 𝔭.adicCompletion K) - 1) (by simpa using hlt)
    rw [map_one, show (1 : 𝔭.adicCompletion K) +
      (((x (Place.ofFinite 𝔭)) : 𝔭.adicCompletion K) - 1) =
        ((x (Place.ofFinite 𝔭)) : 𝔭.adicCompletion K) from by ring] at h
    exact h
  rw [hval]
  simp

end Cycle

theorem cycleMemIcoprime_iff
    {K : Type} [Field K] [NumberField K]
    (c : Work.SSGRoute.ZDataMup.Cycle K)
    (A : NK.CFTLib.ArtinReciprocityIdeal.Frac K) :
    A ∈ Work.SSGRoute.ZDataMup.Cycle.Icoprime c ↔ ∃ x : NK.GlobalCFT.Idele K,
      x ∈ c.congrSubgroup ∧
        NK.GlobalCFT.IdeleClassGroup.idealOfUnitHom K x = A := by
  constructor
  · intro hA
    exact Cycle.exists_idealOf_eq_of_mem_Icoprime c hA
  · rintro ⟨x, hx, hxA⟩
    show Cycle.FracCoprime c A
    intro 𝔭 h𝔭
    have hcoe : Idele.idealOf x = (A : FractionalIdeal (𝓞 K)⁰ K) := by
      have h := congrArg (fun u : (FractionalIdeal (𝓞 K)⁰ K)ˣ =>
        (u : FractionalIdeal (𝓞 K)⁰ K)) hxA
      simp only [IdeleClassGroup.idealOfUnitHom_apply, Units.val_mk0] at h
      exact h
    rw [← hcoe]
    exact Cycle.count_idealOf_eq_zero_of_mem_congrSubgroup c hx 𝔭 h𝔭

end Work.SSGRoute.ZDataMup
