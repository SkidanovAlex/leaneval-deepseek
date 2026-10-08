import Mathlib
import Submission.Work.ZJB.Step1.Defs

namespace Work.ZJB2.Step1

/-- Conjugating `X` by `c * n`, where `c` centralizes `X` (pointwise), is the same as
conjugating by `n`: `pconj X (c * n) = pconj X n`.  This is the only group-theoretic input
of `stepNProp`: it strips off the centralizing factor supplied by condition `(C_p)`. -/
private lemma pconj_mul_of_centralizes {G : Type*} [Group G] {X : Subgroup G} {c : G}
    (hc : c ∈ Subgroup.centralizer (X : Set G)) (n : G) :
    Work.ZJB.pconj X (c * n) = Work.ZJB.pconj X n := by
  have hn : c ∈ Subgroup.normalizer (X : Set G) := Subgroup.centralizer_le_normalizer _ hc
  ext x
  rw [Work.ZJB.mem_pconj, Work.ZJB.mem_pconj]
  rw [show (c * n) * x * (c * n)⁻¹ = c * (n * x * n⁻¹) * c⁻¹ by group]
  exact (Subgroup.mem_normalizer_iff.mp hn (n * x * n⁻¹)).symm

/-- **I.7a.** With `W = Z(S) ⊆ T` and `Z(S)^g = Z(S)^a ⊆ T`, condition `(C_p)` inside
`N(H)` factors `g = c * n` with `c` centralizing `Z(S)` and
`n ∈ N(H) ∩ N(Z(J(T)))`; since `c` centralizes `Z(S)`, `Z(S)^n = Z(S)^g = Z(S)^a`. -/
theorem stepNProp {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    Work.ZJB.StepNProp p G := by
  intro S H T g a hCp hT hg hST hga hTa hSne
  unfold Work.ZJB.CpIn at hCp
  have hWne : (↑(Work.ZJB.ZS (S : Subgroup G)) : Set G).Nonempty :=
    ⟨1, (Work.ZJB.ZS _).one_mem⟩
  have hle : Work.ZJB.pconj (Work.ZJB.ZS (S : Subgroup G)) g ≤ T := by rw [hga]; exact hTa
  have hcond : ∀ w ∈ (↑(Work.ZJB.ZS (S : Subgroup G)) : Set G), g⁻¹ * w * g ∈ T := by
    intro w hw
    apply hle
    rw [Work.ZJB.mem_pconj]
    rw [show g * (g⁻¹ * w * g) * g⁻¹ = w by group]
    exact hw
  obtain ⟨c, n, _hcH, hcC, hnH, hnN, hgn⟩ :=
    hCp T hT (↑(Work.ZJB.ZS (S : Subgroup G))) hWne hST g hg hcond
  refine ⟨n, ?_, ?_⟩
  · rw [Subgroup.mem_inf]; exact ⟨hnH, hnN⟩
  · rw [hgn] at hga
    rw [pconj_mul_of_centralizes hcC n] at hga
    exact hga

end Work.ZJB2.Step1
