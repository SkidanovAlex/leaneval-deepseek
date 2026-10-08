import Mathlib
import Submission.Work.L2F.Props.oddsub.CommonEigenvectorAux

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Props.oddsub

/-- If `Q ◁ L ≤ SL(2,F)` and `u` is a common eigenvector for `Q`, then for every `l ∈ L` the
vector `l *ᵥ u` is again a common eigenvector for `Q`.

Indeed, for `y ∈ Q` normality gives `l⁻¹ * y * l ∈ Q`, say `(l⁻¹ * y * l) *ᵥ u = c • u`; applying
`l` gives `y *ᵥ (l *ᵥ u) = c • (l *ᵥ u)`.  Non-vanishing is clear because `l` is invertible. -/
theorem isCommonEigenvector_mulVec (F : Type*) [Field F]
    (L Q : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
    (hQL : Q ≤ L) (hQnorm : (Q.subgroupOf L).Normal)
    (l : Matrix.SpecialLinearGroup (Fin 2) F) (hl : l ∈ L)
    (u : Fin 2 → F) (hu : Work.L2F.Props.oddsub.IsCommonEigenvector Q u) :
    Work.L2F.Props.oddsub.IsCommonEigenvector Q
      (Matrix.mulVec ((l : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) u) := by
  set Lm : Matrix (Fin 2) (Fin 2) F :=
    ((l : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hLm
  set Lminv : Matrix (Fin 2) (Fin 2) F :=
    ((l⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hLminv
  have hLmulLinv : Lm * Lminv = 1 := by
    rw [hLm, hLminv, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hLminvLmul : Lminv * Lm = 1 := by
    rw [hLm, hLminv, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  refine ⟨?_, ?_⟩
  · -- `l *ᵥ u ≠ 0` because `l` is an invertible matrix
    intro h0
    apply hu.1
    have hunit : IsUnit Lm := ⟨⟨Lm, Lminv, hLmulLinv, hLminvLmul⟩, rfl⟩
    exact Matrix.mulVec_injective_of_isUnit hunit (by rw [h0, Matrix.mulVec_zero])
  · -- every `y ∈ Q` acts on `l *ᵥ u` by a scalar
    intro y hy
    have hyL : y ∈ L := hQL hy
    have hconjQ : l⁻¹ * y * l ∈ Q := by
      have h := hQnorm.conj_mem' (⟨y, hyL⟩ : L) (Subgroup.mem_subgroupOf.mpr hy) (⟨l, hl⟩ : L)
      rw [Subgroup.mem_subgroupOf] at h
      simpa using h
    obtain ⟨c, hc⟩ := hu.2 (l⁻¹ * y * l) hconjQ
    set Y : Matrix (Fin 2) (Fin 2) F :=
      ((y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hY
    have hA : ((l⁻¹ * y * l : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        = Lminv * Y * Lm := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        ← hLminv, ← hY, ← hLm]
    rw [hA] at hc
    have hYeq : Y * Lm = Lm * (Lminv * Y * Lm) := by
      conv_rhs => rw [← mul_assoc, ← mul_assoc]
      rw [hLmulLinv, one_mul]
    refine ⟨c, ?_⟩
    calc Y *ᵥ (Lm *ᵥ u) = (Y * Lm) *ᵥ u := by rw [Matrix.mulVec_mulVec]
      _ = (Lm * (Lminv * Y * Lm)) *ᵥ u := by rw [hYeq]
      _ = Lm *ᵥ ((Lminv * Y * Lm) *ᵥ u) := by rw [Matrix.mulVec_mulVec]
      _ = Lm *ᵥ (c • u) := by rw [hc]
      _ = c • (Lm *ᵥ u) := by rw [Matrix.mulVec_smul]

end Work.L2F.Props.oddsub
