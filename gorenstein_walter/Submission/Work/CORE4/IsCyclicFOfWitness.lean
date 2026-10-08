import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Case2Seven
import Submission.Work.CORE4.SixThree
import Submission.Work.CORE4.isCyclic_of_le_sup_of_inf_eq_bot

namespace Work.CORE4

/-- **Bender 1981, §4 (6), cyclicity half, in "witness" form.**  If `g ∉ M` conjugates `F` into
`F(U) ⊓ M = K₁ F` (§4 (3), `SixThree`) and `F ⊓ F^g = 1`, then `F` is cyclic.

Indeed `F ≅ F^g ≤ K₁ F ⊆ K F`, while `K F ≤ M = N_G(F)` (`Case2Pre.N_F`) makes `F` normal in
`K F`; so `F^g` embeds into the quotient `(K F)/F` of the cyclic group `K` and is therefore
cyclic (`isCyclic_of_le_sup_of_inf_eq_bot`).  Bender's own phrasing (p. 225): "as we can choose
`g ∈ N_G(K₁F)`, `F` is isomorphic to a subgroup of `K₁`, hence `F` is cyclic". -/
theorem IsCyclicFOfWitness (I : Work.GW2.C4Inputs) {G : Type} [Group G] [Finite G]
    (hbc : Work.GW2.BenderCtx G)
    {B : Work.GW2.BenderSetup G} (D : Work.GW2.Case2Data B) (hpre : Work.GW2.Case2Pre B D)
    {g : G} (hgM : g ∉ D.M) (hwit : Work.GW2.conjSub g D.F ≤ Work.GW2.fittingIn B.U ⊓ D.M)
    (hti : D.F ⊓ Work.GW2.conjSub g D.F = ⊥) : IsCyclic D.F := by
  -- §4 (3): `F(U) ⊓ M = (F(U) ⊓ K) ⊔ F`, so the witness gives `F^g ≤ K ⊔ F`.
  have hle : Work.GW2.conjSub g D.F ≤ D.K ⊔ D.F := by
    refine hwit.trans ?_
    rw [Work.CORE4.SixThree I G hbc B D hpre]
    exact sup_le (le_trans inf_le_right le_sup_left) le_sup_right
  -- `K F ≤ M = N_G(F)`, so `K` normalises `F`.
  have hnorm : D.K ≤ Subgroup.normalizer (D.F : Set G) := by
    rw [Work.GW2.Case2Pre.N_F B D hpre]
    exact Work.GW2.Case2Data.K_le_M B D
  -- hence `F^g`, lying in `K F` and meeting `F` trivially, embeds into the cyclic quotient
  -- `(K F)/F` of the cyclic group `K`.
  have hcyc : IsCyclic ↥(Work.GW2.conjSub g D.F) :=
    isCyclic_of_le_sup_of_inf_eq_bot _ _ _ hle hnorm (by rw [inf_comm]; exact hti)
      (Work.GW2.Case2Pre.K_cyclic B D hpre)
  -- `F ≅ F^g` by conjugation.
  have e : ↥D.F ≃* ↥(Work.GW2.conjSub g D.F) :=
    Subgroup.equivMapOfInjective D.F (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  exact (MulEquiv.isCyclic e).mpr hcyc

end Work.CORE4
