/-
**Trivial-intersection (`TI`) Sylow `2`-subgroups of the Bender families.**

A group has *TI* Sylow `2`-subgroups when distinct Sylow `2`-subgroups intersect trivially.
This is the 2-local signature of a group with a split `(B,N)`-pair of rank one in
characteristic two; it is a consequence of Bender's analysis of a strongly embedded subgroup
(if `M = N_G(S)` for a Sylow `2`-subgroup `S ≤ M`, then `S ⊓ S^g ≤ M ⊓ M^g` has odd order for
`g ∉ M`, whence `S ⊓ S^g = 1`).

The cases `PSL(2,2^n)`, `Sz(2^(2n+1))` and `SU(3,2^n)` are treated here or in
`Submission/Sz/SuzukiCondition.lean` (`szTwoGroupS_inf_map_conj_eq_bot`) and
`Submission/PSU3/SuzukiCondition.lean` (`suUS_inf_map_conj_eq_bot`) through the double coset
covering `G = B ⊔ B w B`.  The present file records the *projective* case
(`PSU(3,2^n)`) and the `PSL(2,2^n)` case, and isolates the abstract argument, which is a direct
consequence of the Bender action: a nontrivial `2`-subgroup has a *unique* fixed point, so
`S ⊓ S^g` (a `2`-subgroup fixing both the fixed point of `S` and that of `S^g`) must be trivial
whenever those two points differ, i.e. as soon as `g` does not normalise `S`.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.BenderAction
import Submission.Work.Models.Port.ModelStructure
import Submission.Work.Models.Port.PSL2Torus
import Submission.Work.Models.Port.PSL2SylowConj
import Submission.Work.Models.Port.PSU3.Simple
import Submission.Work.Models.Port.Commons.GroupTheory.Bender.existsUnique_fixedPoint_isPGroup_two
import Submission.Work.Models.Port.Commons.GroupTheory.Bender.inf_map_conj_eq_bot_of_isPGroup_two
import Submission.Work.Models.Port.Commons.GroupTheory.SL2.isCoatom_stabilizer_projectiveSpecialLinearGroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open Matrix LeanEval.GroupTheory.Defs
open scoped commutatorElement Pointwise

namespace Submission

namespace PSU3

/-- **The Sylow `2`-subgroups of `PSU(3,2^n)` are `TI`**: `Ū ⊓ Ū^g = 1` for every `g` outside
the Borel subgroup `B̄ = N_G(Ū)`. -/
theorem psu3U_inf_map_conj_eq_bot (n : ℕ) (hn : 2 ≤ n) {g : PSU3Model n}
    (hg : g ∉ psu3B n) :
    psu3U n ⊓ (psu3U n).map (MulAut.conj g).toMonoidHom = ⊥ := by
  obtain ⟨hne, heven, hodd⟩ := psu3B_stronglyEmbedded n hn
  obtain ⟨-, -, hevenG, hinv⟩ :=
    Commons.GroupTheory.Bender.isBenderAction_coset (psu3B n) hne heven hodd
  refine Commons.GroupTheory.Bender.inf_map_conj_eq_bot_of_isPGroup_two hevenG hinv (isPGroup_psu3U n (by omega))
    (α := ((1 : PSU3Model n) : PSU3Model n ⧸ psu3B n)) ?_ ?_
  · intro s hs
    have hst : s ∈ MulAction.stabilizer (PSU3Model n)
        (((1 : PSU3Model n)) : PSU3Model n ⧸ psu3B n) := by
      rw [MulAction.stabilizer_quotient]
      exact psu3U_le_psu3B n hs
    exact hst
  · intro hfix
    refine hg ?_
    rw [← MulAction.stabilizer_quotient (G := PSU3Model n) (psu3B n)]
    exact hfix

end PSU3

namespace PSL2

open Commons.GroupTheory.SL2

/-- The unipotent subgroup of `PSL(2,2^n)` is a `2`-group. -/
theorem isPGroup_unipotent_range (n : ℕ) (hn : 1 ≤ n) :
    IsPGroup 2 ↥((unipotentPSLHom (GaloisField 2 n)).range) := by
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hchar : CharP (GaloisField 2 n) 2 := inferInstance
  have hinj := Commons.GroupTheory.SL2.unipotentPSLHom_injective (K := GaloisField 2 n) hchar
  refine IsPGroup.of_card (p := 2) (n := n) ?_
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
    ← Nat.card_congr Multiplicative.ofAdd, GaloisField.card 2 n (by omega)]

/-- **The Sylow `2`-subgroups of `PSL(2,2^n)` are `TI`**: `U ⊓ U^g = 1` for every `g` outside
the point stabiliser `B = N_G(U)`. -/
theorem unipotent_inf_map_conj_eq_bot (n : ℕ) (hn : 2 ≤ n) {g : PSL2Model n}
    (hg : g ∉ MulAction.stabilizer (PSL2Model n) (pt0 (GaloisField 2 n))) :
    (unipotentPSLHom (GaloisField 2 n)).range ⊓
        ((unipotentPSLHom (GaloisField 2 n)).range).map (MulAut.conj g).toMonoidHom = ⊥ := by
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hchar : CharP (GaloisField 2 n) 2 := inferInstance
  have hcard : 2 ≤ Nat.card (GaloisField 2 n) := by
    rw [GaloisField.card 2 n (by omega)]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨hne, heven, hodd⟩ :=
    Commons.GroupTheory.SL2.stronglyEmbedded_stabilizer_projectiveSpecialLinearGroup
      (K := GaloisField 2 n) hchar hcard (pt0 (GaloisField 2 n))
  obtain ⟨-, -, hevenG, hinv⟩ :=
    Commons.GroupTheory.Bender.isBenderAction_coset
      (MulAction.stabilizer (PSL2Model n) (pt0 (GaloisField 2 n))) hne heven hodd
  refine Commons.GroupTheory.Bender.inf_map_conj_eq_bot_of_isPGroup_two hevenG hinv (isPGroup_unipotent_range n (by omega))
    (α := ((1 : PSL2Model n) :
      PSL2Model n ⧸ MulAction.stabilizer (PSL2Model n) (pt0 (GaloisField 2 n)))) ?_ ?_
  · intro s hs
    have hst : s ∈ MulAction.stabilizer (PSL2Model n)
        (((1 : PSL2Model n)) :
          PSL2Model n ⧸ MulAction.stabilizer (PSL2Model n) (pt0 (GaloisField 2 n))) := by
      rw [MulAction.stabilizer_quotient]
      exact unipotent_range_le_stabilizer_pt0 hs
    exact hst
  · intro hfix
    refine hg ?_
    rw [← MulAction.stabilizer_quotient (G := PSL2Model n)
      (MulAction.stabilizer (PSL2Model n) (pt0 (GaloisField 2 n)))]
    exact hfix

end PSL2

end Submission
