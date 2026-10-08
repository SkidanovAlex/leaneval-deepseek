import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.sconjLam
import Submission.Work.BG.s02_assemblyCore

namespace Work.BG

/-- **`Λ`-equivalence is preserved by `s`-conjugation.**  If `ν = λ_β · μ` then
`ν^s = (λ_β · μ)^s = λ_{β⁻¹} · μ^s` by Bender–Glauberman Lemma 2.1(b)
(`Work.BG.sconjLam`), so `μ^s` and `ν^s` lie in the same `Λ`-orbit. -/
theorem s02c_LamEquiv_sconj {G : Type} [Group G] [Finite G] (C : Work.BG.Sec2Ctx G)
    {μ ν : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ}
    (h : Work.BG.LamEquiv C μ ν) :
    Work.BG.LamEquiv C (Work.BG.sconj C μ) (Work.BG.sconj C ν) := by
  obtain ⟨β, hβ⟩ := h
  refine ⟨β⁻¹, ?_⟩
  rw [hβ, sconjLam C β μ]

end Work.BG
