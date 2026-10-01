import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.RectRepDefs
import Submission.Work.LinnikAreas.l31free.lemma3_1_free_gen
import Submission.Work.ZeroFreeTables.HB94.L52supply
import Submission.Work.ZeroFreeTables.OffAxis.HBLemma9_1_engine_H_cplx

namespace Work.ZeroFreeTables.OffAxis

/-- **HB Lemma 3.1 at the exponent `φ = 1/3`, in the wide form.**
Feeding the `sorry`-free Burgess input `LBound13` (HB Lemma 2.5 with `φ = 1/3`) to the
`φ`-free Lemma 3.1 `Work.LinnikAreas.l31free.lemma3_1_free_gen` at slack `ε₁` produces
`L₀` and `δ` and the log-derivative bound with constant `(1/3)/2 + ε₁ = 1/6 + ε₁` on the
strip `1 + 1/(L log L) ≤ Re s ≤ 1 + log L / L`, `|Im s| ≤ 10 L`, the near-zero sum being the
one of `InvNearSum`. -/
theorem RectRepInput (ε₁ : ℝ) (hε₁ : 0 < ε₁) :
    ∃ L₀ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N),
      χ ≠ 1 → χ.IsPrimitive → 3 ≤ N → ∀ {L : ℝ}, L₀ ≤ L → Real.log (N : ℝ) ≤ L →
      Work.ZeroFreeTables.OffAxis.WideLogDerivHyp χ δ L (1/6 + ε₁) := by
  obtain ⟨L₀, δ, hδ0, hδ1, hmain⟩ :=
    Work.LinnikAreas.l31free.lemma3_1_free_gen (φ := (1 : ℝ) / 3) (by norm_num)
      (ε := ε₁) hε₁ Work.ZeroFreeTables.HB94.LBound13_clean
  refine ⟨L₀, δ, hδ0, hδ1, ?_⟩
  intro N _inst χ hχ hχprim hN L hL0 hLlog s hs1 hs2 hs3
  have h := hmain hN χ hχ hχprim hL0 hLlog s hs1 hs2 hs3
  have hconst : (((1 : ℝ) / 3) / 2 + ε₁) * L = (1 / 6 + ε₁) * L := by ring
  rw [hconst] at h
  simpa only [WideLogDerivHyp, InvNearSum, pdiv] using h

end Work.ZeroFreeTables.OffAxis
