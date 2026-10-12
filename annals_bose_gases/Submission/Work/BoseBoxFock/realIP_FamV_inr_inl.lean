import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.GramVDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-- **The θ/χ mixed Gram entry of the physical family, in the coordinate rows.**

`realIP (FamV (inr s)) (FamV (inl k)) = ℓ³ · gram (GRow s) (f k)` with `ℓ = ellH v μ`.

The physical θ-mode at the label `s` is `thetaExp ℓ (kmomLab ℓ N s)` and the physical
χ-mode at `k` is `qVec ℓ (kmomLab ℓ N k)`, so for `s ≠ 0` the entry is the corpus box
Gram value `ℓ³·χ̂(ℓ(k−s))` (`corpusBox_gram_values`), which is exactly
`ℓ³·gram (g s) (f k)` by `HonestModes.hcross`; on the coordinate side `GRow s = g s` for
`s ≠ 0`.  For `s = 0` the θ-mode is the condensate `θ_Λ`, which is orthogonal to every
χ-mode (`Q(·) ⊥ θ`), while the coordinate row `GRow 0 = δ_0` pairs with `f k` to
`f k 0 = 0`. -/
theorem realIP_FamV_inr_inl (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (HM : HonestModes v μ)
    (s k : Lab HM.N) :
    Work.BoseK15.corpusBox.realIP (FamV v μ HM (Sum.inr s)) (FamV v μ HM (Sum.inl k))
      = (ellH v μ) ^ 3 * Work.BoseB4.gram (GRow v μ HM s) (HM.f k) := by
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  by_cases hs : s = 0
  · -- the θ-mode is the condensate: `⟨θ, Q(e^{ikx}χ_Λ)⟩ = 0`
    subst hs
    have hL : Work.BoseK15.corpusBox.realIP (FamV v μ HM (Sum.inr (0 : Lab HM.N)))
        (FamV v μ HM (Sum.inl k)) = 0 := by
      rw [FamV_inr_zero]
      show Work.BoseK15.corpusBox.realIP (Work.BoseK15.corpusBox.thetaFun (ellH v μ))
        (Work.BoseK15.corpusBox.qVec (ellH v μ) (kmomLab (ellH v μ) HM.N k)) = 0
      rw [Work.BoseB4.realIP_comm]
      exact Work.BoseB4.realIP_qVec_thetaFun Work.BoseK15.corpusBox hℓ
        (kmomLab (ellH v μ) HM.N k)
    rw [hL]
    -- the coordinate row `GRow 0 = δ_0` pairs with `f k` to `f k 0 = 0`
    simp [Work.BoseB4.gram, GRow, HM.hf0 k]
  · -- `s ≠ 0`: the corpus box Gram value against the coordinate row `g s`
    have hGR : GRow v μ HM s = HM.g s := by
      funext l
      simp only [GRow]
      rw [if_neg hs]
    have hL : Work.BoseK15.corpusBox.realIP (FamV v μ HM (Sum.inr s))
        (FamV v μ HM (Sum.inl k))
        = Work.BoseK15.corpusBox.realIP
            (Work.BoseK15.corpusBox.thetaExp (ellH v μ) (kmomLab (ellH v μ) HM.N s))
            (Work.BoseK15.corpusBox.qVec (ellH v μ) (kmomLab (ellH v μ) HM.N k)) := rfl
    rw [hL, (corpusBox_gram_values (ellH v μ) hℓ HM.N).2.2.1 s k hs, ← HM.hcross s k, hGR]

end Work.BoseBoxFock
