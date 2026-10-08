import Mathlib
import Submission.Work.CORE2B.HallPerPrime_aux
import Submission.Work.CORE2B.API

namespace Work.CORE2B

-- GW design pass 18, item A′, leaf H6 (copied from `Core18CommTMemPCoreTwoHhat.lean`):
-- `y ∈ Ĥ` implies `[y,t] = y t y⁻¹ t⁻¹ ∈ O₂(Ĥ)`.
-- Sketch: Theorem 2.6 (`h26`) gives `S ⊓ C_G(U) = O₂(Ĥ)`; `t ∈ S₀ ≤ S` and `t` centralizes `U`
-- (`t_commutes_U`), so `t ∈ O₂(Ĥ)`; `O₂(Ĥ) = pCoreIn 2 Ĥ` is normalized by `Ĥ`, so
-- `y t y⁻¹ ∈ O₂(Ĥ)`, and `t⁻¹ ∈ O₂(Ĥ)`.
theorem C18CommTMemPCoreTwoHhat_proved (h26 : Work.GW2.Thm26Prop) (G : Type) [Group G] [Finite G]
    (hFT : Work.GW2.FeitThompsonProp) (hCtx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (y : G) (hy : y ∈ B.Hhat) :
    y * B.t * y⁻¹ * B.t⁻¹ ∈ Work.GW2.pCoreIn 2 B.Hhat := by
  -- Theorem 2.6: `S ⊓ C_G(U) = O₂(Ĥ)`.
  obtain ⟨-, hSU, -⟩ := h26 G hFT hCtx B
  -- First show `t ∈ O₂(Ĥ) = S ⊓ C_G(U)`: `t ∈ S₀ ≤ S` and `t` centralizes `U`.
  have htP : B.t ∈ Work.GW2.pCoreIn 2 B.Hhat := by
    have ht_cent : B.t ∈ Subgroup.centralizer (B.U : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact (t_commutes_U B u hu).symm
    rw [← hSU]
    exact ⟨(BenderSetup_basics B).1, ht_cent⟩
  -- `Ĥ` normalizes `O₂(Ĥ) = pCoreIn 2 Ĥ`, hence `y t y⁻¹ ∈ O₂(Ĥ)`.
  have hnorm : y ∈ Subgroup.normalizer ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) :=
    le_normalizer_pCoreIn_local 2 B.Hhat hy
  have hconj : y * B.t * y⁻¹ ∈ Work.GW2.pCoreIn 2 B.Hhat :=
    (Subgroup.mem_normalizer_iff.mp hnorm B.t).mp htP
  exact Subgroup.mul_mem _ hconj (Subgroup.inv_mem _ htP)

end Work.CORE2B
