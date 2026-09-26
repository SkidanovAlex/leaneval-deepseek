/-
# The cocycles for `rowDiffOdd` and for the carries

`rowDiffOdd γ i = MpElem i * ofSL γ - ∑ j, σ(γ)_{ij} • MpElem j` is a *cocycle*: for
`γ δ : SL(2,ℤ)`,

  `rowDiffOdd (γ * δ) i = ∑ j, σ(γ)_{ij} • rowDiffOdd δ j + rowDiffOdd γ i * ofSL δ`.

Since the carries of `rowDiffOdd γ i` decompose it along `(T-I)²`, `S(T-I)²` and `(1+z)`, the
cocycle for the carries follows from the directness of `𝓘_odd` modulo `(1+z)R`
(`Work.Asymptotics.idealI_direct_augIdealOdd`): the difference

  `carryOdd₁ (γ*δ) i - ∑ j, σ(γ)_{ij} • carryOdd₁ δ j - carryOdd₁ γ i * ofSL δ`

has `(T-I)²`- and `S(T-I)²`-components lying in `(1+z)R`, so it lies in `(1+z)R` itself.

These two identities are exactly what the well-definedness of CKMRV's extension formula needs.
-/
import Mathlib
import Submission.Work.Asymptotics.PropagateCarriesOdd
import Submission.Work.Asymptotics.idealI_direct_augIdealOdd
import Submission.Work.Asymptotics.mem_idealIOdd_exists

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm

namespace Work.Asymptotics

open Work.Kernels

/-! ## `(1+z)R` is a two-sided ideal -/

lemma mul_mem_augIdealOdd (a : R) {x : R} (hx : x ∈ augIdealOdd) : a * x ∈ augIdealOdd := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨r, s, rfl⟩ := hy
    refine Submodule.subset_span ⟨a * r, s, ?_⟩
    simp only [mul_assoc]
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy

/-! ## The cocycle for `rowDiffOdd` -/

lemma sigmaHom_mul_apply (γ δ : SL(2,ℤ)) (i j : Fin 6) :
    (sigmaHom (γ * δ)) i j = ∑ k : Fin 6, (sigmaHom γ) i k * (sigmaHom δ) k j := by
  have h : sigmaHom (γ * δ) = sigmaHom γ * sigmaHom δ := map_mul _ _ _
  rw [h]
  exact Matrix.mul_apply

/-- The reduction identity, in the form in which it is used below. -/
lemma MpElem_mul_ofSL (γ : SL(2,ℤ)) (k : Fin 6) :
    MpElem k * ofSL γ = (∑ j : Fin 6, (sigmaHom γ) k j • MpElem j) + rowDiffOdd γ k := by
  rw [rowDiffOdd]
  abel

/-- **The cocycle identity for the error vector `rowDiffOdd`.** -/
theorem rowDiffOdd_mul (γ δ : SL(2,ℤ)) (i : Fin 6) :
    rowDiffOdd (γ * δ) i
      = (∑ j : Fin 6, (sigmaHom γ) i j • rowDiffOdd δ j) + rowDiffOdd γ i * ofSL δ := by
  have hsum : (∑ j : Fin 6, (sigmaHom (γ * δ)) i j • MpElem j)
      = ∑ j : Fin 6, (∑ k : Fin 6, (sigmaHom γ) i k * (sigmaHom δ) k j) • MpElem j := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [sigmaHom_mul_apply]
  rw [rowDiffOdd, ofSL_mul, hsum]
  rw [show MpElem i * (ofSL γ * ofSL δ)
      = ((∑ k : Fin 6, (sigmaHom γ) i k • MpElem k) * ofSL δ)
        + rowDiffOdd γ i * ofSL δ from by
    rw [← mul_assoc, MpElem_mul_ofSL γ i, add_mul]]
  rw [Finset.sum_mul]
  simp only [smul_mul_assoc, MpElem_mul_ofSL, smul_add, Finset.sum_add_distrib]
  have hcomp : (∑ k : Fin 6, (sigmaHom γ) i k • (∑ j : Fin 6, (sigmaHom δ) k j • MpElem j))
      = ∑ j : Fin 6, (∑ k : Fin 6, (sigmaHom γ) i k * (sigmaHom δ) k j) • MpElem j := by
    simp only [Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl (fun k _ => smul_smul _ _ _)
  rw [hcomp]
  abel

/-! ## The cocycle for the carries -/

/-- The two `(T-I)²`- and `S(T-I)²`-carries of `rowDiffOdd x i` recombine to `rowDiffOdd x i` up to
the collapsed term `(1+z)·carry₃`. -/
lemma carryOdd_pair (x : SL(2,ℤ)) (i : Fin 6) :
    (R_T - 1) ^ 2 * carryOdd₁ x i + R_S * (R_T - 1) ^ 2 * carryOdd₂ x i
      = rowDiffOdd x i - (Rneg + 1) * carryOdd₃ x i := by
  have h := carryOdd_spec x i
  rw [h]
  abel

/-- **The cocycle identity for the carries.**  The `(T-I)²`-carries of `rowDiffOdd` satisfy the
same cocycle as `rowDiffOdd` itself, modulo the collapse ideal `(1+z)R`. -/
theorem carryOdd_cocycle₁ (γ δ : SL(2,ℤ)) (i : Fin 6) :
    carryOdd₁ (γ * δ) i - (∑ j : Fin 6, (sigmaHom γ) i j • carryOdd₁ δ j)
      - carryOdd₁ γ i * ofSL δ ∈ augIdealOdd := by
  have hmem : (R_T - 1) ^ 2 * (carryOdd₁ (γ * δ) i
        - (∑ j : Fin 6, (sigmaHom γ) i j • carryOdd₁ δ j) - carryOdd₁ γ i * ofSL δ)
      + R_S * (R_T - 1) ^ 2 * (carryOdd₂ (γ * δ) i
        - (∑ j : Fin 6, (sigmaHom γ) i j • carryOdd₂ δ j) - carryOdd₂ γ i * ofSL δ)
      ∈ augIdealOdd := by
    have hexp : (R_T - 1) ^ 2 * (carryOdd₁ (γ * δ) i
          - (∑ j : Fin 6, (sigmaHom γ) i j • carryOdd₁ δ j) - carryOdd₁ γ i * ofSL δ)
        + R_S * (R_T - 1) ^ 2 * (carryOdd₂ (γ * δ) i
          - (∑ j : Fin 6, (sigmaHom γ) i j • carryOdd₂ δ j) - carryOdd₂ γ i * ofSL δ)
        = ((R_T - 1) ^ 2 * carryOdd₁ (γ * δ) i
            + R_S * (R_T - 1) ^ 2 * carryOdd₂ (γ * δ) i)
          - (∑ j : Fin 6, (sigmaHom γ) i j •
              ((R_T - 1) ^ 2 * carryOdd₁ δ j + R_S * (R_T - 1) ^ 2 * carryOdd₂ δ j))
          - ((R_T - 1) ^ 2 * carryOdd₁ γ i
              + R_S * (R_T - 1) ^ 2 * carryOdd₂ γ i) * ofSL δ := by
      simp only [mul_sub, sub_mul, Finset.mul_sum, Finset.sum_sub_distrib, smul_add,
        Finset.sum_add_distrib, mul_smul_comm, smul_sub]
      noncomm_ring
    rw [hexp, carryOdd_pair (γ * δ) i, carryOdd_pair γ i, rowDiffOdd_mul γ δ i]
    simp only [carryOdd_pair]
    have hX : (∑ j : Fin 6, (sigmaHom γ) i j • rowDiffOdd δ j) + rowDiffOdd γ i * ofSL δ
          - (Rneg + 1) * carryOdd₃ (γ * δ) i
          - (∑ j : Fin 6, (sigmaHom γ) i j • (rowDiffOdd δ j - (Rneg + 1) * carryOdd₃ δ j))
          - (rowDiffOdd γ i - (Rneg + 1) * carryOdd₃ γ i) * ofSL δ
        = -((Rneg + 1) * carryOdd₃ (γ * δ) i)
          + (∑ j : Fin 6, (sigmaHom γ) i j • ((Rneg + 1) * carryOdd₃ δ j))
          + ((Rneg + 1) * carryOdd₃ γ i) * ofSL δ := by
      simp only [smul_sub, Finset.sum_sub_distrib, sub_mul, add_mul, neg_smul, one_smul,
        neg_neg]
      noncomm_ring
    rw [hX]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · exact Submodule.neg_mem _ (Submodule.subset_span
        ⟨1, carryOdd₃ (γ * δ) i, by rw [one_mul]⟩)
    · refine Submodule.sum_mem _ fun j _ => ?_
      exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨1, carryOdd₃ δ j, by rw [one_mul]⟩)
    · exact augIdealOdd_mul_mem (Submodule.subset_span
        ⟨1, carryOdd₃ γ i, by rw [one_mul]⟩) (ofSL δ)
  exact (idealI_direct_augIdealOdd hmem).1

/-- **The cocycle identity for the second family of carries.** -/
theorem carryOdd_cocycle₂ (γ δ : SL(2,ℤ)) (i : Fin 6) :
    carryOdd₂ (γ * δ) i - (∑ j : Fin 6, (sigmaHom γ) i j • carryOdd₂ δ j)
      - carryOdd₂ γ i * ofSL δ ∈ augIdealOdd := by
  have hmem : (R_T - 1) ^ 2 * (carryOdd₁ (γ * δ) i
        - (∑ j : Fin 6, (sigmaHom γ) i j • carryOdd₁ δ j) - carryOdd₁ γ i * ofSL δ)
      + R_S * (R_T - 1) ^ 2 * (carryOdd₂ (γ * δ) i
        - (∑ j : Fin 6, (sigmaHom γ) i j • carryOdd₂ δ j) - carryOdd₂ γ i * ofSL δ)
      ∈ augIdealOdd := by
    have hexp : (R_T - 1) ^ 2 * (carryOdd₁ (γ * δ) i
          - (∑ j : Fin 6, (sigmaHom γ) i j • carryOdd₁ δ j) - carryOdd₁ γ i * ofSL δ)
        + R_S * (R_T - 1) ^ 2 * (carryOdd₂ (γ * δ) i
          - (∑ j : Fin 6, (sigmaHom γ) i j • carryOdd₂ δ j) - carryOdd₂ γ i * ofSL δ)
        = ((R_T - 1) ^ 2 * carryOdd₁ (γ * δ) i
            + R_S * (R_T - 1) ^ 2 * carryOdd₂ (γ * δ) i)
          - (∑ j : Fin 6, (sigmaHom γ) i j •
              ((R_T - 1) ^ 2 * carryOdd₁ δ j + R_S * (R_T - 1) ^ 2 * carryOdd₂ δ j))
          - ((R_T - 1) ^ 2 * carryOdd₁ γ i
              + R_S * (R_T - 1) ^ 2 * carryOdd₂ γ i) * ofSL δ := by
      simp only [mul_sub, sub_mul, Finset.mul_sum, Finset.sum_sub_distrib, smul_add,
        Finset.sum_add_distrib, mul_smul_comm, smul_sub]
      noncomm_ring
    rw [hexp, carryOdd_pair (γ * δ) i, carryOdd_pair γ i, rowDiffOdd_mul γ δ i]
    simp only [carryOdd_pair]
    have hX : (∑ j : Fin 6, (sigmaHom γ) i j • rowDiffOdd δ j) + rowDiffOdd γ i * ofSL δ
          - (Rneg + 1) * carryOdd₃ (γ * δ) i
          - (∑ j : Fin 6, (sigmaHom γ) i j • (rowDiffOdd δ j - (Rneg + 1) * carryOdd₃ δ j))
          - (rowDiffOdd γ i - (Rneg + 1) * carryOdd₃ γ i) * ofSL δ
        = -((Rneg + 1) * carryOdd₃ (γ * δ) i)
          + (∑ j : Fin 6, (sigmaHom γ) i j • ((Rneg + 1) * carryOdd₃ δ j))
          + ((Rneg + 1) * carryOdd₃ γ i) * ofSL δ := by
      simp only [smul_sub, Finset.sum_sub_distrib, sub_mul, add_mul, neg_smul, one_smul,
        neg_neg]
      noncomm_ring
    rw [hX]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · exact Submodule.neg_mem _ (Submodule.subset_span
        ⟨1, carryOdd₃ (γ * δ) i, by rw [one_mul]⟩)
    · refine Submodule.sum_mem _ fun j _ => ?_
      exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨1, carryOdd₃ δ j, by rw [one_mul]⟩)
    · exact augIdealOdd_mul_mem (Submodule.subset_span
        ⟨1, carryOdd₃ γ i, by rw [one_mul]⟩) (ofSL δ)
  exact (idealI_direct_augIdealOdd hmem).2

end Work.Asymptotics
