import Mathlib
import Submission.Work.ThomBordism.sigmaGaussTelescope

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Topology BigOperators

namespace Work.ThomBordism

open Work.ThomBordism.OrthFrame

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- **Scaling the first vector of the chart tangent frame scales the pair sign.**
`flipTan E i x s` is the chart tangent frame with its first vector multiplied by `s`; since only the
column `Sum.inl 0` of the pair matrix is affected, its determinant sign is multiplied by `s`
(for `s = ±1`). -/
theorem pairSign_flipTan (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (i : Work.ThomBordism.PontryaginThom.CoverIdx V k) (x : V.pt) (s : ℝ)
    (hs : s = 1 ∨ s = -1)
    (G : Fin k → Work.Tubular.Euc (8 + k)) :
    pairSign (flipTan E i x s) G = s * pairSign (tanFrame E i x) G := by
  have hmat : pairMat (flipTan E i x s) G
      = pairMat (tanFrame E i x) G
        * Matrix.diagonal (fun c : Fin 8 ⊕ Fin k => if c = Sum.inl 0 then s else 1) := by
    ext r c
    rw [Matrix.mul_diagonal]
    cases c with
    | inl a =>
      rw [pairMat_inl, pairMat_inl]
      rw [show flipTan E i x s a
          = (if (a : ℕ) = 0 then s • tanFrame E i x a else tanFrame E i x a) from rfl]
      have hif : (if (Sum.inl a : Fin 8 ⊕ Fin k) = Sum.inl 0 then s else 1)
          = (if (a : ℕ) = 0 then s else 1) := by
        by_cases h : (a : ℕ) = 0
        · rw [if_pos h, if_pos (by rw [Sum.inl.injEq]; exact Fin.ext h)]
        · rw [if_neg h, if_neg (by rw [Sum.inl.injEq]; exact fun hh => h (by simpa using congrArg Fin.val hh))]
      rw [hif]
      by_cases h : (a : ℕ) = 0
      · rw [if_pos h, if_pos h, map_smul, Pi.smul_apply, smul_eq_mul]
        ring
      · rw [if_neg h, if_neg h, mul_one]
    | inr b =>
      rw [pairMat_inr, pairMat_inr]
      rw [if_neg (by intro h; exact Sum.inr_ne_inl h), mul_one]
  have hprod : (∏ c : Fin 8 ⊕ Fin k, (if c = Sum.inl 0 then s else 1)) = s := by
    rw [Finset.prod_eq_single (Sum.inl 0)]
    · rw [if_pos rfl]
    · intro c _ hc; rw [if_neg hc]
    · intro h; exact absurd (Finset.mem_univ (Sum.inl 0)) h
  rw [pairSign, pairSign, hmat, Matrix.det_mul, Matrix.det_diagonal, hprod]
  rcases hs with h | h
  · rw [h, mul_one, one_mul]
  · rw [h, mul_neg_one, Real.sign_neg, neg_one_mul]

/-- **The pair sign of the chart tangent frame and the σ-corrected Gauss frame is the chart frame
sign.**  This is the telescoping `Work.ThomBordism.sigmaTelescope_gauss` (`pairSign` of the
`frameSign`-corrected tangent frame with `gframe` is `1`) solved for the uncorrected tangent
frame. -/
theorem pairSign_tanFrame_gframe (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (hk : 1 ≤ k)
    (i : Work.ThomBordism.PontryaginThom.CoverIdx V k) (x : V.pt)
    (hx : x ∈ ND.D.baseSet i) :
    OrthFrame.pairSign (tanFrame E i x) (Gauss.gframe E ND i x)
      = FrameSigns.frameSign V i.1 x := by
  have h := Work.ThomBordism.sigmaTelescope_gauss E ND hk i x hx
  rw [pairSign_flipTan E i x (FrameSigns.frameSign V i.1 x)
    (FrameSigns.frameSign_eq_one_or_neg_one V i.1 x) (Gauss.gframe E ND i x)] at h
  rcases FrameSigns.frameSign_eq_one_or_neg_one V i.1 x with h1 | h1
  · rw [h1, one_mul] at h
    rw [h1]
    exact h
  · rw [h1, neg_one_mul] at h
    rw [h1]
    linarith

end

end Work.ThomBordism
