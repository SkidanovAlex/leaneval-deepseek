/-
**The strongly embedded subgroups of `PSU(3, 2^n)` are the normalizers of Sylow
`2`-subgroups.**

This is the `PSU(3,2^n)`-level companion of `Submission.PSU3.suStronglyEmbedded_eq_sylow_normalizer`.
The Borel subgroup `psu3B n` is the image of `suBS n` under the surjection `SU(3,2^n) → PSU(3,2^n)`
(whose kernel is a central odd-order subgroup contained in `suBS n`), so maximality of `suBS n`
(`suB_isCoatom`) transfers to `psu3B n` by
`Commons.GroupTheory.Subgroup.isCoatom_map_of_ker_le`.  Together with `psu3B_eq_normalizer` and
the conjugacy-invariance of `IsCoatom` this gives the coatom hypothesis for every Sylow
`2`-subgroup, and the general theorem `exists_sylow_normalizer_eq_of_isStronglyEmbedded` applies.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.ModelStructure
import Submission.Work.Models.Port.SylowNormalizer
import Submission.Work.Models.Port.SylowPointCounts
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.isCoatom_map_of_ker_le
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.isCoatom_map_mulAut_conj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

open Matrix LeanEval.GroupTheory.Defs
open scoped Pointwise

namespace Submission.PSU3

/-- The Borel subgroup of `PSU(3,2^n)` is a maximal subgroup. -/
theorem psu3B_isCoatom (n : ℕ) (hn : 1 ≤ n) : IsCoatom (psu3B n) :=
  Commons.GroupTheory.Subgroup.isCoatom_map_of_ker_le (psu3Hom_surjective n)
    (suB_isCoatom n) (psu3Hom_ker_le_borel n)

/-- The unipotent radical of `PSU(3,2^n)` chosen as a Sylow `2`-subgroup. -/
noncomputable def psu3Sylow (n : ℕ) (hn : 2 ≤ n) : Sylow 2 (PSU3Model n) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (isPGroup_psu3U n (by omega)).toSylow (not_dvd_index_psu3U n hn)

/-- Every normalizer of a Sylow `2`-subgroup of `PSU(3,2^n)` is a conjugate of the Borel subgroup,
hence a maximal subgroup. -/
theorem psu3Sylow_normalizer_isCoatom (n : ℕ) (hn : 2 ≤ n) (T : Sylow 2 (PSU3Model n)) :
    IsCoatom (Subgroup.normalizer (((T : Subgroup (PSU3Model n)) : Set (PSU3Model n)))) := by
  have hn1 : 1 ≤ n := by omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : MulAction.IsPretransitive (PSU3Model n) (Sylow 2 (PSU3Model n)) :=
    Sylow.isPretransitive_of_finite
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := PSU3Model n) (psu3Sylow n hn) T
  have hcoe : (T : Subgroup (PSU3Model n)) = (psu3U n).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.smul_def]
    rfl
  rw [hcoe, Submission.normalizer_map_mulAut_conj, psu3B_eq_normalizer n hn]
  exact Commons.GroupTheory.Subgroup.isCoatom_map_mulAut_conj (psu3B_isCoatom n hn1) g

/-- **A strongly embedded subgroup of `PSU(3,2^n)` is the normalizer of a Sylow
`2`-subgroup.** -/
theorem psu3StronglyEmbedded_eq_sylow_normalizer (n : ℕ) (hn : 2 ≤ n)
    (M : Subgroup (PSU3Model n)) (hM : IsStronglyEmbedded M) :
    ∃ T : Sylow 2 (PSU3Model n),
      M = Subgroup.normalizer (((T : Subgroup (PSU3Model n)) : Set (PSU3Model n))) :=
  Submission.exists_sylow_normalizer_eq_of_isStronglyEmbedded M hM.1 hM.2.1 hM.2.2
    (fun T => psu3Sylow_normalizer_isCoatom n hn T)

end Submission.PSU3
