import Submission.NK.NUV2.LC.finite_support_loc_odd_of_twist
import Submission.NK.HassePrinciple.H2_map_injective_of_coprime_index

/-!
# Route B: the restriction `H²(U, Z/p) → H²(V, Z/p)` is injective for prime-to-`p` index

The design's lemma `(L3')` (`Submission/Work/NUV2/LC/RouteB/decompContainment_B.lean`) is the
statement that non-triviality of the local cohomology survives passing to an *open* subgroup; its
recorded proof route is the transfer: `res` is injective whenever the index is prime to `p`, because
`cor ∘ res = [U : V]` and `H²(U, Z/p)` is `p`-torsion.

This file proves the resulting statement at the level of the **profinite colimit**:

  `Function.Injective (NK.LocalDecomposition.H2Profinite.res p h)`  for  `h : V ≤ U`  with
  `Nat.Coprime (Subgroup.index (V.subgroupOf U)) p`.

The proof is level-wise, using the finite-group transfer argument of
`NK.HassePrinciple.H2_map_injective_of_coprime_index` (restriction to a subgroup of index prime to
`p` is injective on `H²(·, Z/p)`) together with the divisibility
`index (range (levelInclHom h M)) ∣ index (V.subgroupOf U)`
(`NK.NUV2.LC.OddTwist.index_range_levelInclHom_dvd`) and the level square
`NK.NUV2.LC.OddTwist.levelMap_triv_levelInclHom_apply`: an element of the colimit is represented
at a level, its restriction at that level is killed by inflation to a larger level, and injectivity
at that larger level finishes.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

namespace NK.NUV2.LC.RouteB

variable {K K' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The restriction on `H²(·, Z/p)` is injective for a subgroup of finite index prime to `p`.** -/
theorem H2Profinite_res_injective_of_coprime_index (p : ℕ) (hp : p.Prime)
    {U V : Subgroup Gal(K'/K)} (hVU : V ≤ U)
    (hcop : Nat.Coprime (Subgroup.index (V.subgroupOf U)) p) :
    Function.Injective (NK.LocalDecomposition.H2Profinite.res p hVU) := by
  intro x y hxy
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨L, a, rfl⟩ := NK.BrauerHasse.H2Profinite.ofLevel_surjective x
  obtain ⟨L', b, rfl⟩ := NK.BrauerHasse.H2Profinite.ofLevel_surjective y
  rw [NK.LocalDecomposition.H2Profinite.res_ofLevel,
    NK.LocalDecomposition.H2Profinite.res_ofLevel] at hxy
  obtain ⟨M, h₁, h₂, heq⟩ := (NK.BrauerHasse.ofLevel_eq_iff _ _).mp hxy
  rw [NK.NUV2.LC.OddTwist.levelMap_triv_levelInclHom_apply p hVU h₁ a,
    NK.NUV2.LC.OddTwist.levelMap_triv_levelInclHom_apply p hVU h₂ b] at heq
  have hinj := NK.HassePrinciple.H2_map_injective_of_coprime_index (p := p)
    (NK.BrauerHasse.levelInclHom hVU M) (NK.HassePrinciple.levelInclHom_injective hVU M)
    (Nat.Coprime.coprime_dvd_left
      (NK.NUV2.LC.OddTwist.index_range_levelInclHom_dvd p hVU M) hcop)
  have h : NK.BrauerHasse.levelMap p (U := U) h₁ a =
      NK.BrauerHasse.levelMap p (U := U) h₂ b := hinj heq
  exact (NK.BrauerHasse.ofLevel_eq_iff a b).mpr ⟨M, h₁, h₂, h⟩

/-- **Design's `(L3')`, in the form the final part of `decompContainment_B` consumes it**:
non-triviality of `H²(·, Z/p)` survives restriction to a subgroup of index prime to `p`. -/
theorem nontrivial_of_nontrivial_of_coprime_index (p : ℕ) (hp : p.Prime)
    {D D' : Subgroup Gal(K'/K)} (h : D' ≤ D)
    (hcop : Nat.Coprime (Subgroup.index (D'.subgroupOf D)) p) :
    Nontrivial (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p D) →
      Nontrivial (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p D') := by
  intro hnt
  obtain ⟨x, hx⟩ := exists_ne (0 : NK.BrauerHasse.H2Profinite (K := K) (K' := K') p D)
  refine ⟨NK.LocalDecomposition.H2Profinite.res p h x, 0, fun h0 => hx ?_⟩
  have heq : NK.LocalDecomposition.H2Profinite.res p h x =
      NK.LocalDecomposition.H2Profinite.res p h 0 := by
    rw [h0, NK.NUV2.LC.OddTwist.H2Profinite_res_zero]
  exact H2Profinite_res_injective_of_coprime_index p hp h hcop heq

end NK.NUV2.LC.RouteB
