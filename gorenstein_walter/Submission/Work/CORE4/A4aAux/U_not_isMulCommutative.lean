import Mathlib
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.API
import Submission.Work.CORE4.A7Split

namespace Work.CORE4.A4aAux

/-- **`U` is not abelian** in the `A₇` case of §4.

Bender p. 226 (used in `A4a`): if `U = O(H)` were abelian, then `U`, together with `S`, would lie
in `M`.

Route.
* `F ≤ U` (`Case2Data.F_le_U`) and `U` abelian give `U ≤ C_G(F)`, which is contained in
  `N_G(F) = M` (`Case2Pre.N_F`).
* `A7Facts2` gives `S ≤ E(M) ≤ M` (`layerIn_le`).
* `A7Split` gives `H = U ⊔ S`; both summands lie in `M`, so `H ≤ M`, contradicting
  `Case2Pre.not_H_le`. -/
theorem U_not_isMulCommutative (Ip : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G] (B : Work.GW2.BenderSetup G) (C : Work.GW2.Case2Ctx6 B),
      Work.GW2.BenderCtx G → Work.GW2.A7Facts2 B C.D → ¬ IsMulCommutative ↥B.U := by
  intro G _ _ B C hbc h2 hU
  -- `U` is abelian and `F ≤ U`, so `U ≤ C_G(F)`.
  have hUcentF : B.U ≤ Subgroup.centralizer (C.D.F : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact (congrArg Subtype.val
      (mul_comm' (⟨u, hu⟩ : ↥B.U) ⟨f, Work.GW2.Case2Data.F_le_U B C.D hf⟩)).symm
  -- `C_G(F) ≤ N_G(F) = M`.
  have hUleM : B.U ≤ C.D.M := by
    have h1 : Subgroup.centralizer (C.D.F : Set G) ≤ Subgroup.normalizer (C.D.F : Set G) :=
      Subgroup.centralizer_le_normalizer _
    rw [Work.GW2.Case2Pre.N_F B C.D C.pre] at h1
    exact le_trans hUcentF h1
  -- `S ≤ E(M) ≤ M` (`A7Facts2`).
  have hSleM : (B.S : Subgroup G) ≤ C.D.M :=
    le_trans h2.2.2.1 (Work.CORE4.layerIn_le C.D.M)
  -- `H = U ⊔ S ≤ M`, contradicting `¬ H ≤ M`.
  have hHleM : B.H ≤ C.D.M := by
    rw [Work.CORE4.A7Split Ip hbc h2]
    exact sup_le hUleM hSleM
  exact Work.GW2.Case2Pre.not_H_le B C.D C.pre hHleM

end Work.CORE4.A4aAux
