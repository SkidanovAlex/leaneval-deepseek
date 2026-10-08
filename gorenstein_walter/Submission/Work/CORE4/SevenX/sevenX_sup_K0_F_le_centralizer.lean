import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Case2EightObjExists
import Submission.Work.CORE4.ElementaryAbelianRankTwo

namespace Work.CORE4.SevenX

/-- `K₀ F = K₀ ⊔ F` is abelian: `K₀ ≤ K` is cyclic (`Work.GW2.Case2Pre.K_cyclic`), `F` is
cyclic (hypothesis `hFcyc`, which the caller supplies from `Case2Ctx6.F_cyclic`), and `F` commutes
with `K ⊇ K₀` elementwise (`Work.CORE4.F_commute_K_c4`, available from `Case2Pre` alone).  Hence
`K₀ ⊔ F ≤ C_G(K₀ ⊔ F)`.

Route: `Subgroup.centralizer_sup` turns the goal into `K₀ ⊔ F ≤ C_G(K₀) ⊓ C_G(F)`; split by
`sup_le` and `le_inf`.  `K₀ ≤ C_G(K₀)` and `F ≤ C_G(F)` are the two abelianities (`IsCyclic` of
`K₀ ≤ K` and `hFcyc`), `K₀ ≤ C_G(F)` and `F ≤ C_G(K₀)` are the elementwise commutation. -/
theorem sevenX_sup_K0_F_le_centralizer (I : Work.GW2.C4Inputs) {G : Type} [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) (D : Work.GW2.Case2Data B)
    (hpre : Work.GW2.Case2Pre B D) (hFcyc : IsCyclic D.F) :
    D.K0 ⊔ D.F ≤ Subgroup.centralizer ((D.K0 ⊔ D.F : Subgroup G) : Set G) := by
  -- `K₀ ≤ K` is cyclic, hence abelian
  haveI hKcyc : IsCyclic ↥D.K := Work.GW2.Case2Pre.K_cyclic B D hpre
  haveI hK0cyc : IsCyclic ↥D.K0 := Subgroup.isCyclic_of_le (inf_le_right : D.K0 ≤ D.K)
  have hK0comm : IsMulCommutative ↥D.K0 := IsCyclic.isMulCommutative
  -- `F` is cyclic, hence abelian
  haveI hFcycI : IsCyclic ↥D.F := hFcyc
  have hFcomm : IsMulCommutative ↥D.F := IsCyclic.isMulCommutative
  -- `F` commutes with `K ⊇ K₀` elementwise, hence centralizes `K₀`
  have hFK0 : D.F ≤ Subgroup.centralizer ((D.K0 : Subgroup G) : Set G) := by
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hkK : k ∈ D.K := (inf_le_right : D.K0 ≤ D.K) hk
    exact (Work.CORE4.F_commute_K_c4 I B D hpre f hf k hkK).symm
  have hcomm : IsMulCommutative ↥(D.K0 ⊔ D.F) :=
    Work.CORE4.isMulCommutative_sup_of_le_centralizer hFK0 hK0comm hFcomm
  exact Subgroup.le_centralizer_iff_isMulCommutative.mpr hcomm

end Work.CORE4.SevenX
