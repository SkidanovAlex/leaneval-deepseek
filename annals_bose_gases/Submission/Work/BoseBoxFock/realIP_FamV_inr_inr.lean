import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.GramVDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.realIP_FamV_inr_inr` — the θ-row of the physical Gram

The `inr`-row of the physical Gram matrix of the honest mode family `FamV`: the
`realIP` pairing of the two θ-modes `e^{isx}θ_Λ`, `e^{itx}θ_Λ` is `ℓ³` times the
coordinate pairing `Work.BoseB4.gram (GRow s) (GRow t)` of the honest rows `GRow`.

The distinction from the χ-row (`realIP_FamV_inl_inl`) is the label `0`, where
`FamV (inr 0) = θ_Λ` is the *condensate* while `GRow ... 0 = δ_0` is its memory
row (`ℓ^{-3/2}θ ↦ (1,0,…,0)`), so that the whole model basis — χ-modes, θ-modes
and condensate — is described by one uniform row `CoordRow`.  The four cases are

* `s = t = 0`:  `⟨θ_Λ, θ_Λ⟩ = ℓ³` and `⟪δ_0, δ_0⟫ = 1` (row 6 of
  `corpusBox_gram_values`);
* `s = 0, t ≠ 0` and `s ≠ 0, t = 0`: `θ_Λ ⟂ e^{itx}θ_Λ` (`⟨θ, e^{itx}θ⟩ = 0`,
  the `realIP`-symmetric form of row 5) and `⟪δ_0, g t⟫ = g t 0 = 0` by
  `HonestModes.hg0`;
* `s, t ≠ 0`: `⟨e^{isx}θ, e^{itx}θ⟩ = ℓ³δ_{st}` (row 4) and
  `⟪g s, g t⟫ = δ_{st}` by `HonestModes.hg`.
-/

noncomputable section

namespace Work.BoseBoxFock

set_option autoImplicit false

/-- `GRow` at the label `0` is the memory row `δ_0` of the condensate. -/
private lemma GRow_zero_eq (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (HM : HonestModes v μ) :
    GRow v μ HM (0 : Lab HM.N) = fun l : Fin HM.m => if l = 0 then (1 : ℝ) else 0 := by
  funext l; simp [GRow]

/-- `GRow` at a non-zero label is the honest θ-row `g`. -/
private lemma GRow_eq_of_ne (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (HM : HonestModes v μ)
    {s : Lab HM.N} (hs : s ≠ 0) : GRow v μ HM s = HM.g s := by
  funext l; simp [GRow, hs]

theorem realIP_FamV_inr_inr (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (HM : HonestModes v μ)
    (s t : Lab HM.N) :
    Work.BoseK15.corpusBox.realIP (FamV v μ HM (Sum.inr s)) (FamV v μ HM (Sum.inr t))
      = (ellH v μ) ^ 3 * Work.BoseB4.gram (GRow v μ HM s) (GRow v μ HM t) := by
  obtain ⟨-, -, -, h4, h5, h6⟩ := corpusBox_gram_values (ellH v μ) (ellH_pos v μ) HM.N
  -- `FamV` on the right summand is the θ-mode at the label's momentum
  have hFam : ∀ s : Lab HM.N, FamV v μ HM (Sum.inr s)
      = Work.BoseK15.corpusBox.thetaExp (ellH v μ) (kmomLab (ellH v μ) HM.N s) := fun _ => rfl
  have hG0 := GRow_zero_eq v μ HM
  have hGne : ∀ a : Lab HM.N, a ≠ 0 → GRow v μ HM a = HM.g a :=
    fun a ha => GRow_eq_of_ne v μ HM ha
  rcases eq_or_ne s 0 with hs | hs
  · subst hs
    rcases eq_or_ne t 0 with ht | ht
    · -- `s = t = 0`: the condensate against itself
      subst ht
      have hgr : Work.BoseB4.gram (GRow v μ HM 0) (GRow v μ HM 0) = 1 := by
        rw [hG0, Work.BoseB4.gram, Finset.sum_eq_single (0 : Fin HM.m)]
        · simp
        · intro b _ hb; simp [hb]
        · intro h; exact absurd (Finset.mem_univ (0 : Fin HM.m)) h
      rw [FamV_inr_zero, h6, hgr, mul_one]
    · -- `s = 0`, `t ≠ 0`: the condensate is orthogonal to `e^{itx}θ_Λ`
      have hgr : Work.BoseB4.gram (GRow v μ HM 0) (GRow v μ HM t) = 0 := by
        rw [hG0, hGne t ht, Work.BoseB4.gram, Finset.sum_eq_single (0 : Fin HM.m)]
        · simpa using HM.hg0 t ht
        · intro b _ hb; simp [hb]
        · intro h; exact absurd (Finset.mem_univ (0 : Fin HM.m)) h
      rw [FamV_inr_zero, hgr, mul_zero, Work.BoseB4.realIP_comm]
      exact h5 t ht
  · rcases eq_or_ne t 0 with ht | ht
    · -- `s ≠ 0`, `t = 0`: symmetric case
      subst ht
      have hgr : Work.BoseB4.gram (GRow v μ HM s) (GRow v μ HM 0) = 0 := by
        rw [hGne s hs, hG0, Work.BoseB4.gram, Finset.sum_eq_single (0 : Fin HM.m)]
        · simpa using HM.hg0 s hs
        · intro b _ hb; simp [hb]
        · intro h; exact absurd (Finset.mem_univ (0 : Fin HM.m)) h
      rw [FamV_inr_zero, hgr, mul_zero]
      exact h5 s hs
    · -- `s, t ≠ 0`: the θ-modes are orthonormal (`ℓ³δ_{st}`)
      rw [hFam s, hFam t, hGne s hs, hGne t ht, HM.hg s t hs ht, h4 s t hs ht]
      by_cases hst : s = t
      · rw [if_pos hst, if_pos hst, mul_one]
      · rw [if_neg hst, if_neg hst, mul_zero]

end Work.BoseBoxFock
