import Mathlib
import Submission.Work.SSGRoute.ZDataMup.CycleDefs
import Submission.Work.SSGRoute.ZDataMup.CycleCongr
import Submission.Work.SSGRoute.ZDataMup.CycleAuxField
import Submission.Work.SSGRoute.ZDataMup.CycleIdele
import Submission.Work.SSGRoute.ZDataMup.cyclotomicKernelLeCycle
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors

noncomputable section

namespace Work.SSGRoute.ZDataMup

namespace Cycle

variable {K : Type} [Field K] [NumberField K]

/-- **The cycle `c` with its levels enlarged by those of the natural modulus `m`.**

This is the reduction device of `cycleKernelLe_of_cycle`: enlarging the levels only *shrinks* the
principal ray, the norm ray is unchanged (it reads only the support of `cL`), and the coprimality
condition `FracCoprime` is unchanged (it reads only the support of `c`).  The enlarged cycle can be
made admissible, which is what the idèle–ideal dictionary needs. -/
def enlarge (c : Cycle K) (m : ℕ) : Cycle K where
  supp := c.supp
  lev := fun 𝔭 => max (c.lev 𝔭) (cycleLevel (K := K) m 𝔭)

@[simp] theorem mem_supp_enlarge (c : Cycle K) (m : ℕ) (𝔭 : HeightOneSpectrum (𝓞 K)) :
    𝔭 ∈ (c.enlarge m).supp ↔ 𝔭 ∈ c.supp := Iff.rfl

theorem lev_enlarge (c : Cycle K) (m : ℕ) (𝔭 : HeightOneSpectrum (𝓞 K)) :
    (c.enlarge m).lev 𝔭 = max (c.lev 𝔭) (cycleLevel (K := K) m 𝔭) := rfl

theorem le_lev_enlarge (c : Cycle K) (m : ℕ) (𝔭 : HeightOneSpectrum (𝓞 K)) :
    c.lev 𝔭 ≤ (c.enlarge m).lev 𝔭 := le_max_left _ _

theorem cycleLevel_le_lev_enlarge (c : Cycle K) (m : ℕ) (𝔭 : HeightOneSpectrum (𝓞 K)) :
    cycleLevel (K := K) m 𝔭 ≤ (c.enlarge m).lev 𝔭 := le_max_right _ _

@[simp] theorem FracCoprime_enlarge_iff (c : Cycle K) (m : ℕ)
    (A : NK.CFTLib.ArtinReciprocityIdeal.Frac K) :
    (c.enlarge m).FracCoprime A ↔ c.FracCoprime A := Iff.rfl

@[simp] theorem IsBaseChange_enlarge_iff {L : Type} [Field L] [NumberField L] [Algebra K L]
    (c : Cycle K) (m : ℕ) (cL : Cycle L) :
    IsBaseChange K L (c.enlarge m) cL ↔ IsBaseChange K L c cL := Iff.rfl

/-- The principal ray shrinks when the levels are enlarged. -/
theorem principalRay_enlarge_le (c : Cycle K) (m : ℕ) :
    (c.enlarge m).principalRay ≤ c.principalRay := by
  rw [principalRay, Subgroup.closure_le]
  rintro A ⟨a, ha, rfl⟩
  refine Subgroup.subset_closure ⟨a, ⟨fun 𝔭 h𝔭 => ?_, ha.2⟩, rfl⟩
  refine le_trans (ha.1 𝔭 h𝔭) ?_
  rw [WithZero.exp_le_exp]
  exact neg_le_neg (by
    exact_mod_cast le_max_left (c.lev 𝔭) (cycleLevel (K := K) m 𝔭))

/-- The norm ray reads only the base-changed cycle, so it is unchanged by the level enlargement. -/
@[simp] theorem normRay_enlarge {L : Type} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] (c : Cycle K) (m : ℕ) (cL : Cycle L) :
    Cycle.normRay K L (c.enlarge m) cL = Cycle.normRay K L c cL := rfl

end Cycle

/-- ## The target

The statement below is the assigned lemma.  Its proof is the transfer argument of Lang,
*Algebraic Number Theory*, X §2, Theorem 2 at a cycle (ideal modulus): the per-prime auxiliary
field construction (from `Cycle.AuxFieldHyp`, i.e. Artin's lemma) together with the cyclotomic
cell `Cycle.cyclotomicCellKernelLe`, the two norm descents (`Cycle.principalRay_map_relNormUnit_le`,
`Cycle.normRay_map_relNormUnit_le`) and the compatibility of the Artin symbol with relative norms
(`Cycle.artinSym_restrict_relNorm_of_normal`) and with `K`-isomorphisms
(`Cycle.artinSym_algEquiv`, `Cycle.normRay_le_of_algEquiv`). -/
theorem cycleKernelLe_of_cycle
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (c : Work.SSGRoute.ZDataMup.Cycle K) (cL : Work.SSGRoute.ZDataMup.Cycle L)
    (hbc : Work.SSGRoute.ZDataMup.Cycle.IsBaseChange K L c cL)
    (hram : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p → p ∈ c.supp)
    (hlev : ∀ 𝔭 ∈ c.supp, 1 ≤ c.lev 𝔭)
    (haux : Work.SSGRoute.ZDataMup.Cycle.AuxFieldHyp (K := K) L c) :
    ∀ A : NK.CFTLib.ArtinReciprocityIdeal.Frac K,
      Work.SSGRoute.ZDataMup.Cycle.FracCoprime c A →
      NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := L) hcomm A = 1 →
      A ∈ c.principalRay ⊔ c.normRay K L cL := by
  sorry

end Work.SSGRoute.ZDataMup
