import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.EightIdxDefs
import Submission.Work.CORE4.Case2EightQfacts
import Submission.Work.CORE4.Case2EightCase3U9plus
import Submission.Work.CORE4Qsub.A_le_pCoreInU

namespace Work.CORE4ULeP

/-- `N_G(B.U) ≤ N_G(Qsub p B)`: `Q = Ω₁(Z₂(O_p(U)))` is characteristic in `U`, so every
element normalizing `U` normalizes `Q`.  (This is the general form of
`Work.CORE4.u9_Qsub_normal_in_U`, which has `B.U` in place of `N_G(B.U)`.)

PLAN.  Work with `Subgroup.mem_normalizer_iff_map_conj_eq` (i.e. `conjSub g _`, see
`Work.GW2.conjSub`).  Given `hg : Work.GW2.conjSub g B.U = B.U`:
* `Work.GW2.conjSub g (Work.GW2.pCoreIn p B.U) = Work.GW2.pCoreIn p B.U`: conjugation by `g`
  induces an automorphism of `↥(B.U)` (from `hg`), and `Work.GW2.pCore p ↥(B.U)` is characteristic
  in `↥(B.U)` (`Work.CORE4Qsub.pCore_characteristic`, `CORE4Qsub/A_le_pCoreInU.lean`; the general
  tool is `Work.CORE4Qsub.le_normalizer_map_subtype_of_characteristic`, also in that file, which
  gives directly `Subgroup.normalizer ↑B.U ≤ Subgroup.normalizer ↑(pCoreIn p B.U)` — use whichever
  is convenient, e.g. via `Subgroup.mem_normalizer_iff_map_conj_eq`);
* `Work.CORE4.conjSub_z2` (`CORE4/Case2EightQfacts.lean`, sorry-free) then gives
  `conjSub g (z2 (pCoreIn p B.U)) = z2 (conjSub g (pCoreIn p B.U)) = z2 (pCoreIn p B.U)`;
* `Work.CORE4.conjSub_omega1` (same file) gives
  `conjSub g (omega1 p W) = omega1 p (conjSub g W)`, so `conjSub g (Qsub p B) = Qsub p B` since
  `Qsub p B = omega1 p (z2 (pCoreIn p B.U))` by `rfl`.
Alternatively use the pre-proved bricks `Work.CORE4.u9_le_normalizer_z2`,
`Work.CORE4.u9_le_normalizer_omega1`, `Work.CORE4.u9_le_normalizer_map_subtype_of_normal`
(`CORE4/Case2EightCase3U9plus.lean`, sorry-free) which are stated with a `≤ normalizer` hypothesis.
Only Mathlib group theory is needed beyond the imports; do NOT use `CORE4/QsubNormal.lean`
(it has a name clash / does not build for everyone). -/
theorem normalizer_le_normalizer_Qsub {G : Type} [Group G] [Finite G] (p : ℕ)
    (B : Work.GW2.BenderSetup G) :
    Subgroup.normalizer ((B.U : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Work.CORE4.Qsub p B : Subgroup G) : Set G) := by
  -- `O_p(U)` is characteristic in `U`, so `N_G(U) ≤ N_G(O_p(U))`
  have h1 : Subgroup.normalizer ((B.U : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Work.GW2.pCoreIn p B.U : Subgroup G) : Set G) :=
    Work.CORE4Qsub.le_normalizer_map_subtype_of_characteristic
      (K := B.U) (H := Work.GW2.pCore p ↥B.U)
      (Work.CORE4Qsub.pCore_characteristic (G := ↥B.U) p) (le_refl _)
  -- `Z₂` is conjugation invariant, so `N_G(O_p(U)) ≤ N_G(Z₂(O_p(U)))`
  have h2 : Subgroup.normalizer ((Work.GW2.pCoreIn p B.U : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Work.CORE4.z2 (Work.GW2.pCoreIn p B.U) : Subgroup G) : Set G) :=
    Work.CORE4.u9_le_normalizer_z2 (P := Work.GW2.pCoreIn p B.U) (le_refl _)
  -- `Ω₁` is conjugation invariant, so `N_G(Z₂(O_p(U))) ≤ N_G(Ω₁(Z₂(O_p(U)))) = N_G(Q)`
  have h3 : Subgroup.normalizer ((Work.CORE4.z2 (Work.GW2.pCoreIn p B.U) : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Work.CORE4.omega1 p (Work.CORE4.z2 (Work.GW2.pCoreIn p B.U))
        : Subgroup G) : Set G) :=
    Work.CORE4.u9_le_normalizer_omega1 p (K := Work.CORE4.z2 (Work.GW2.pCoreIn p B.U)) (le_refl _)
  exact (h1.trans h2).trans h3

end Work.CORE4ULeP
