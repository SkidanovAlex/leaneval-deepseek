import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.normalizer_eq_of_coatom

/-!
# `N_G(U) = Ĥ` in Case (1b)

Bender 1981, §3 (p. 223): in the subcase `V = O₂(Ĥ)` of Case (1) of Theorem 2.10 one has
`N_G(U) = Ĥ`, where `U = O(H) = O(Ĥ)`.  The companion file `Submission.Work.CORE2A.
thm26a_CS_eq_O2` proves the same statement in the subcase `Ĥ = H` (deriving `U = O(Ĥ)` from
the first paragraph of Theorem 2.6, which there needs `Lemma21Prop`).

Here Theorem 2.6 is available in the *bundled* form `I.h26 : Work.GW2.Thm26Prop`, whose first
conjunct is `oddCoreIn B.Hhat = B.U` in *every* configuration.  That makes the argument
uniform and short:

* `U = O(Ĥ)` is normal in `Ĥ`, so `Ĥ ≤ N_G(U)`;
* `U ≠ ⊥` (it contains the Hall subgroup `D.K ≠ ⊥` of `F(U)` from `D : Case1bData B`);
* `Ĥ` is a coatom, so maximality of `Ĥ` and simplicity of `G` force `N_G(U) = Ĥ`
  (`Work.CORE2A.normalizer_eq_of_coatom`).
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.CORE3

theorem JthreeNormalizerU (I : Work.CORE3.Case1Inputs) (hSetup : Work.GW2.Case1bSetupProp)
    (hCount : Work.GW2.Case1bCountProp) (h89 : Work.GW2.Case1bEightNineProp)
    {G : Type} [Group G] [Finite G] (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (h1 : Work.GW2.Case1 B) (h4 : Work.GW2.IsFourGroup (Work.GW2.pCoreIn 2 B.Hhat))
    (D : Work.GW2.Case1bData B) :
    Subgroup.normalizer (B.U : Set G) = B.Hhat := by
  haveI : IsSimpleGroup G := hBc.simple
  -- Bender 1981, Theorem 2.6 (first conjunct, unconditional): `U = O(Ĥ)`.
  have hU : Work.GW2.oddCoreIn B.Hhat = B.U := (I.h26 G I.T.ft hBc B).1
  have hUmap : (Work.GW2.oddCore ↥B.Hhat).map B.Hhat.subtype = B.U := by
    rw [← hU]; rfl
  have hsub : B.U ≤ B.Hhat := by
    rw [← hUmap]
    exact Subgroup.map_subtype_le _
  -- `U = O(Ĥ)` is normal in `Ĥ`, hence `Ĥ ≤ N_G(U)`.
  have hnorm : (B.U.subgroupOf B.Hhat).Normal := by
    have h : (B.U.subgroupOf B.Hhat) = Work.GW2.oddCore ↥B.Hhat := by
      rw [← hUmap]
      unfold Subgroup.subgroupOf
      exact Subgroup.comap_map_eq_self_of_injective B.Hhat.subtype_injective _
    rw [h]
    exact Work.GW2.oddCore_normal ↥B.Hhat
  have hle : B.Hhat ≤ Subgroup.normalizer (B.U : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hsub).mp hnorm
  -- `U ≠ ⊥`: it contains the nontrivial Hall subgroup `D.K ≤ F(U)`.
  have hKU : D.K ≤ B.U :=
    (Work.CORE2A.isHallIn_le D.hall).trans (Subgroup.map_subtype_le _)
  have hne : B.U ≠ ⊥ := fun h => D.ne (le_bot_iff.mp (h ▸ hKU))
  -- `Ĥ` is a coatom and `U ≠ 1`, so `N_G(U) = Ĥ`.
  exact Work.CORE2A.normalizer_eq_of_coatom B.Hhat_coatom hsub hne hle

end Work.CORE3
