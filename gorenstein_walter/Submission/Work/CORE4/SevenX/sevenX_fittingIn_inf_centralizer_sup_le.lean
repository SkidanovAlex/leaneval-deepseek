import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Case2SevenAux

namespace Work.CORE4.SevenX

/-- `C_{F(U)}(K₀F) ≤ K₀F`: an element of `F(U)` centralizing `K₀F ⊇ F` lies in `N_G(F)`, so it
lies in `N_G(F) ⊓ F(U) = F(U) ⊓ M` (Bender §4 (5)/(3), `Case2Data.K1F_eq_normalizer`), which is
`K₀F` by `F(U) ⊓ M = K₀ ⊔ F` (hypothesis `hS`, from `SixThree`). -/
theorem sevenX_fittingIn_inf_centralizer_sup_le {G : Type} [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) (D : Work.GW2.Case2Data B)
    (hpre : Work.GW2.Case2Pre B D)
    (hS : Work.GW2.fittingIn B.U ⊓ D.M = D.K0 ⊔ D.F) :
    Work.GW2.fittingIn B.U ⊓ Subgroup.centralizer ((D.K0 ⊔ D.F : Subgroup G) : Set G) ≤ D.K0 ⊔ D.F := by
  intro x hx
  obtain ⟨hxU, hxC⟩ := Subgroup.mem_inf.mp hx
  -- `x` centralizes `F ≤ K₀ ⊔ F`, hence lies in `N_G(F)`
  have hxF : x ∈ Subgroup.normalizer (D.F : Set G) :=
    Subgroup.centralizer_le_normalizer (D.F : Set G)
      (Subgroup.mem_centralizer_iff.mpr (fun f hf =>
        (Subgroup.mem_centralizer_iff.mp hxC) f ((le_sup_right : D.F ≤ D.K0 ⊔ D.F) hf)))
  -- `N_G(F) ⊓ F(U) = F(U) ⊓ M`, so `x ∈ M`
  have hxNM : x ∈ Subgroup.normalizer (D.F : Set G) ⊓ Work.GW2.fittingIn B.U := ⟨hxF, hxU⟩
  rw [Work.CORE4.Case2Data.K1F_eq_normalizer B D hpre] at hxNM
  have hxM : x ∈ D.M := hxNM.2
  rw [← hS]
  exact Subgroup.mem_inf.mpr ⟨hxU, hxM⟩

end Work.CORE4.SevenX
