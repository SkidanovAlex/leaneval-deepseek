import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.GramVDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-- **The χ/θ cross Gram entry of the physical family `FamV`.**

`⟨Q(e^{ikx}χ_Λ), e^{itx}θ_Λ⟩ = ℓ³ χ̂(ℓ(k−t))` for a non-zero θ-label `t`, and
`0` for `t = 0` (then the θ-mode is the condensate, which is orthogonal to every
χ-mode).  In both cases this is `ℓ³·⟪f k, GRow t⟫`: for `t ≠ 0`, `GRow t = g t`
and `⟪f k, g t⟫ = ⟪g t, f k⟫ = χ̂(ℓ(k−t))` by `HonestModes.hcross`; for `t = 0`,
`GRow 0 = δ_0` and `⟪f k, δ_0⟫ = f k 0 = 0` by `HonestModes.hf0` — consistently
with `⟨Q(e^{ikx}χ_Λ), θ_Λ⟩ = 0` (`corpusBox_gram_values` row 1). -/
theorem realIP_FamV_inl_inr (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (HM : HonestModes v μ)
    (k t : Lab HM.N) :
    Work.BoseK15.corpusBox.realIP (FamV v μ HM (Sum.inl k)) (FamV v μ HM (Sum.inr t))
      = (ellH v μ) ^ 3 * Work.BoseB4.gram (HM.f k) (GRow v μ HM t) := by
  obtain ⟨h1, -, h3, -, -, -⟩ := corpusBox_gram_values (ellH v μ) (ellH_pos v μ) HM.N
  by_cases ht : t = 0
  · -- `t = 0`: the θ-mode is the condensate, orthogonal to `Q(e^{ikx}χ_Λ)`.
    subst ht
    have hG : GRow v μ HM (0 : Lab HM.N) = fun l : Fin HM.m => if l = 0 then (1:ℝ) else 0 := by
      funext l; simp [GRow]
    have hgr : Work.BoseB4.gram (HM.f k) (GRow v μ HM 0) = 0 := by
      rw [hG, Work.BoseB4.gram]
      rw [Finset.sum_eq_single (0 : Fin HM.m)]
      · simp [HonestModes.hf0]
      · intro b _ hb; simp [hb]
      · intro h; exact absurd (Finset.mem_univ (0 : Fin HM.m)) h
    rw [FamV_inr_zero, hgr, mul_zero]
    exact h1 k
  · -- `t ≠ 0`: the cross overlap `ℓ³χ̂(ℓ(k−t))`, read off `hcross`.
    have hGt : GRow v μ HM t = HM.g t := by
      funext l; simp [GRow, ht]
    rw [hGt, Work.BoseB4.gram_comm, HM.hcross t k]
    rw [Work.BoseB4.realIP_comm]
    exact h3 t k ht

end Work.BoseBoxFock
