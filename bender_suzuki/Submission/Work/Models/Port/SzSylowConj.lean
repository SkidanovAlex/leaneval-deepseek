/-
**The strongly embedded subgroups of `Sz(2^(2n+1))` are the normalizers of Sylow
`2`-subgroups.**

The Borel subgroup of `Sz(2^(2n+1))` is a maximal subgroup (the Bruhat decomposition together
with `N_G(U) = B`, `szBorel_isCoatom`), and it is the normalizer of the Suzuki `2`-group
(`szBorelS_eq_normalizer`).  As every Sylow `2`-subgroup is a conjugate of the Suzuki `2`-group,
its normalizer is a conjugate of `B`, hence maximal.  The general theorem
`Submission.exists_sylow_normalizer_eq_of_isStronglyEmbedded` then shows that every strongly
embedded subgroup of `Sz(2^(2n+1))` is the normalizer of a Sylow `2`-subgroup.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.ModelStructure
import Submission.Work.Models.Port.SylowNormalizer
import Submission.Work.Models.Port.Sz.BNPair
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

namespace Submission.Sz

/-- The Borel subgroup of `Sz(2^(2n+1))` is a maximal subgroup. -/
theorem szBorelS_isCoatom (n : ℕ) : IsCoatom (szBorelS n) := by
  rw [isCoatom_iff_ge_of_le]
  refine ⟨?_, ?_⟩
  · intro htop
    have hmem : szWgM n ∈ szBorelS n := by rw [htop]; exact Subgroup.mem_top _
    exact szWg_notMem_szBorel n (Subgroup.mem_subgroupOf.mp hmem)
  · intro K hK hle
    have hHS : K.map (SzModel n).subtype ≤ SzModel n := by
      rintro x ⟨y, hy, rfl⟩; exact y.2
    have hBle : szBorel n ≤ K.map (SzModel n).subtype := by
      intro x hx
      exact ⟨⟨x, szBorel_le_szModel n hx⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
    rcases lt_or_eq_of_le hBle with hlt | heq
    · exfalso
      have htop := szBorel_isCoatom n _ hlt hHS
      refine hK ?_
      rw [Subgroup.eq_top_iff']
      intro x
      have hx' : (x : GL (Fin 4) (SzField n)) ∈ K.map (SzModel n).subtype := by
        rw [htop]; exact x.2
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx'
      have hyx' : y = x := Subtype.ext hyx
      rwa [hyx'] at hy
    · intro x hx
      have hx' : (x : GL (Fin 4) (SzField n)) ∈ szBorel n := by
        rw [heq]
        exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr hx'

/-- Every normalizer of a Sylow `2`-subgroup of `Sz(2^(2n+1))` is a conjugate of the Borel
subgroup, hence a maximal subgroup. -/
theorem szSylow_normalizer_isCoatom (n : ℕ) (hn : 1 ≤ n) (T : Sylow 2 (SzModel n)) :
    IsCoatom (Subgroup.normalizer (((T : Subgroup (SzModel n)) : Set (SzModel n)))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : MulAction.IsPretransitive (SzModel n) (Sylow 2 (SzModel n)) :=
    Sylow.isPretransitive_of_finite
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := SzModel n) (szSylow n) T
  have hcoe : (T : Subgroup (SzModel n)) = (szTwoGroupS n).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.smul_def, szSylow]
    rfl
  rw [hcoe, Submission.normalizer_map_mulAut_conj, szBorelS_eq_normalizer n hn]
  exact Commons.GroupTheory.Subgroup.isCoatom_map_mulAut_conj (szBorelS_isCoatom n) g

/-- **A strongly embedded subgroup of `Sz(2^(2n+1))` is the normalizer of a Sylow
`2`-subgroup.** -/
theorem szStronglyEmbedded_eq_sylow_normalizer (n : ℕ) (hn : 1 ≤ n) (M : Subgroup (SzModel n))
    (hM : IsStronglyEmbedded M) :
    ∃ T : Sylow 2 (SzModel n),
      M = Subgroup.normalizer (((T : Subgroup (SzModel n)) : Set (SzModel n))) :=
  Submission.exists_sylow_normalizer_eq_of_isStronglyEmbedded M hM.1 hM.2.1 hM.2.2
    (fun T => szSylow_normalizer_isCoatom n hn T)

end Submission.Sz
