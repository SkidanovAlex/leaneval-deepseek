import Mathlib
import Submission.Work.ELTop.RigInput
import Submission.Work.ELTop.landsN_iff_landsAt
import Submission.Work.ELTop.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Final

theorem exists_alphaPair_pairSides {c : ℂ} (d : Work.EL.RootParabolic c)
    (hJ : Work.Top.JordanForm) :
    ∃ P : Work.EL.CoPair d.hN, P.a = Work.EL.alpha1 ∧ P.b = Work.EL.alpha2 ∧
      P.y = d.z₁ ∧ Work.EL.PairSides d.hN P := by
  have h1 : Work.EL.LandsN d.hN Work.EL.alpha1 d.z₁ :=
    (Work.ELTop.landsN_iff_landsAt d.hN d.bottcher Work.EL.alpha1 d.z₁).mpr d.rays.1
  have h2 : Work.EL.LandsN d.hN Work.EL.alpha2 d.z₁ :=
    (Work.ELTop.landsN_iff_landsAt d.hN d.bottcher Work.EL.alpha2 d.z₁).mpr d.rays.2
  refine ⟨{ toRawPair := ⟨Work.EL.alpha1, Work.EL.alpha2, d.z₁⟩,
            lands_a := h1, lands_b := h2 }, rfl, rfl, rfl, ?_⟩
  have hnd : Work.EL.arcLen Work.EL.alpha1 Work.EL.alpha2 ≠ 0 := by
    apply Work.ELTop.arcLen_ne_zero_of_lt
    · norm_num [Work.EL.alpha1, Work.EL.alpha2]
    · norm_num [Work.EL.alpha1, Work.EL.alpha2]
  exact Work.ELTop.pairSides d.hN hJ _ hnd

end Work.Final
