import Mathlib.RingTheory.AdjoinRoot

namespace Commons.FieldTheory.AdjoinRoot

open Polynomial

noncomputable section

private def f_neg2_0_2_1_1_neg1 : Polynomial ℚ :=
  Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X - 1

private def g_neg2_0_2_1_1_neg1 : Polynomial ℚ :=
  Polynomial.X ^ 3 - 2 * Polynomial.X ^ 2 + 2

private def qβ_neg2_0_2_1_1_neg1 : Polynomial ℚ :=
  Polynomial.X ^ 2 - Polynomial.X - 1

private def qγ_neg2_0_2_1_1_neg1 : Polynomial ℚ :=
  -(Polynomial.X ^ 2) - Polynomial.X

private abbrev A_neg2_0_2_1_1_neg1 := AdjoinRoot f_neg2_0_2_1_1_neg1
private abbrev B_neg2_0_2_1_1_neg1 := AdjoinRoot g_neg2_0_2_1_1_neg1

private def β_neg2_0_2_1_1_neg1 : B_neg2_0_2_1_1_neg1 :=
  aeval (AdjoinRoot.root g_neg2_0_2_1_1_neg1) qβ_neg2_0_2_1_1_neg1

private def γ_neg2_0_2_1_1_neg1 : A_neg2_0_2_1_1_neg1 :=
  aeval (AdjoinRoot.root f_neg2_0_2_1_1_neg1) qγ_neg2_0_2_1_1_neg1

private lemma hdiv_neg2_0_2_1_1_neg1 :
    g_neg2_0_2_1_1_neg1 ∣ f_neg2_0_2_1_1_neg1.comp qβ_neg2_0_2_1_1_neg1 := by
  use ((Polynomial.X : Polynomial ℚ) ^ 3 - Polynomial.X ^ 2 - Polynomial.X - 1)
  simp [f_neg2_0_2_1_1_neg1, g_neg2_0_2_1_1_neg1, qβ_neg2_0_2_1_1_neg1,
    Polynomial.comp]
  ring

private lemma hdiv_neg2_0_2_1_1_neg1' :
    f_neg2_0_2_1_1_neg1 ∣ g_neg2_0_2_1_1_neg1.comp qγ_neg2_0_2_1_1_neg1 := by
  use (-(Polynomial.X : Polynomial ℚ) ^ 3 - 2 * Polynomial.X ^ 2 - 2 * Polynomial.X - 2)
  simp [f_neg2_0_2_1_1_neg1, g_neg2_0_2_1_1_neg1, qγ_neg2_0_2_1_1_neg1,
    Polynomial.comp]
  ring

private lemma hdiv_inv_neg2_0_2_1_1_neg1 :
    g_neg2_0_2_1_1_neg1 ∣ (qγ_neg2_0_2_1_1_neg1.comp qβ_neg2_0_2_1_1_neg1) - Polynomial.X := by
  use (-(Polynomial.X : Polynomial ℚ))
  simp [g_neg2_0_2_1_1_neg1, qβ_neg2_0_2_1_1_neg1, qγ_neg2_0_2_1_1_neg1,
    Polynomial.comp]
  ring

private lemma hdiv_inv_neg2_0_2_1_1_neg1' :
    f_neg2_0_2_1_1_neg1 ∣ (qβ_neg2_0_2_1_1_neg1.comp qγ_neg2_0_2_1_1_neg1) - Polynomial.X := by
  use (Polynomial.X + 1 : Polynomial ℚ)
  simp [f_neg2_0_2_1_1_neg1, qβ_neg2_0_2_1_1_neg1, qγ_neg2_0_2_1_1_neg1,
    Polynomial.comp]
  ring

private lemma hβ_aeval_neg2_0_2_1_1_neg1 :
    aeval β_neg2_0_2_1_1_neg1 f_neg2_0_2_1_1_neg1 = 0 := by
  rw [β_neg2_0_2_1_1_neg1, ← Polynomial.aeval_comp]
  rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]
  exact hdiv_neg2_0_2_1_1_neg1

private lemma hγ_aeval_neg2_0_2_1_1_neg1 :
    aeval γ_neg2_0_2_1_1_neg1 g_neg2_0_2_1_1_neg1 = 0 := by
  rw [γ_neg2_0_2_1_1_neg1, ← Polynomial.aeval_comp]
  rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]
  exact hdiv_neg2_0_2_1_1_neg1'

private def φ_neg2_0_2_1_1_neg1 : A_neg2_0_2_1_1_neg1 →ₐ[ℚ] B_neg2_0_2_1_1_neg1 :=
  AdjoinRoot.liftAlgHom f_neg2_0_2_1_1_neg1 (Algebra.ofId ℚ B_neg2_0_2_1_1_neg1)
    β_neg2_0_2_1_1_neg1 (by
      simpa [aeval_def] using hβ_aeval_neg2_0_2_1_1_neg1)

private def ψ_neg2_0_2_1_1_neg1 : B_neg2_0_2_1_1_neg1 →ₐ[ℚ] A_neg2_0_2_1_1_neg1 :=
  AdjoinRoot.liftAlgHom g_neg2_0_2_1_1_neg1 (Algebra.ofId ℚ A_neg2_0_2_1_1_neg1)
    γ_neg2_0_2_1_1_neg1 (by
      simpa [aeval_def] using hγ_aeval_neg2_0_2_1_1_neg1)

private lemma hφψ_neg2_0_2_1_1_neg1 :
    φ_neg2_0_2_1_1_neg1.comp ψ_neg2_0_2_1_1_neg1 = AlgHom.id ℚ B_neg2_0_2_1_1_neg1 := by
  apply AdjoinRoot.algHom_ext
  simp [φ_neg2_0_2_1_1_neg1, ψ_neg2_0_2_1_1_neg1,
    β_neg2_0_2_1_1_neg1, γ_neg2_0_2_1_1_neg1]
  change aeval (AdjoinRoot.mk g_neg2_0_2_1_1_neg1 qβ_neg2_0_2_1_1_neg1)
    qγ_neg2_0_2_1_1_neg1 = AdjoinRoot.root g_neg2_0_2_1_1_neg1
  rw [← AdjoinRoot.aeval_eq qβ_neg2_0_2_1_1_neg1]
  rw [← Polynomial.aeval_comp]
  rw [AdjoinRoot.aeval_eq]
  rw [← AdjoinRoot.mk_X]
  rw [AdjoinRoot.mk_eq_mk]
  exact hdiv_inv_neg2_0_2_1_1_neg1

private lemma hψφ_neg2_0_2_1_1_neg1 :
    ψ_neg2_0_2_1_1_neg1.comp φ_neg2_0_2_1_1_neg1 = AlgHom.id ℚ A_neg2_0_2_1_1_neg1 := by
  apply AdjoinRoot.algHom_ext
  simp [φ_neg2_0_2_1_1_neg1, ψ_neg2_0_2_1_1_neg1,
    β_neg2_0_2_1_1_neg1, γ_neg2_0_2_1_1_neg1]
  change aeval (AdjoinRoot.mk f_neg2_0_2_1_1_neg1 qγ_neg2_0_2_1_1_neg1)
    qβ_neg2_0_2_1_1_neg1 = AdjoinRoot.root f_neg2_0_2_1_1_neg1
  rw [← AdjoinRoot.aeval_eq qγ_neg2_0_2_1_1_neg1]
  rw [← Polynomial.aeval_comp]
  rw [AdjoinRoot.aeval_eq]
  rw [← AdjoinRoot.mk_X]
  rw [AdjoinRoot.mk_eq_mk]
  exact hdiv_inv_neg2_0_2_1_1_neg1'

theorem algEquiv_cubic_neg2_0_2_1_1_neg1 :
    Nonempty (AdjoinRoot (Polynomial.X ^ 3 + Polynomial.C (1 : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (1 : ℚ) * Polynomial.X + Polynomial.C (-1 : ℚ) : Polynomial ℚ) ≃ₐ[ℚ]
      AdjoinRoot (Polynomial.X ^ 3 + Polynomial.C (-2 : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (0 : ℚ) * Polynomial.X + Polynomial.C (2 : ℚ) : Polynomial ℚ)) := by
  rw [show (Polynomial.X ^ 3 + Polynomial.C (1 : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (1 : ℚ) * Polynomial.X + Polynomial.C (-1 : ℚ) : Polynomial ℚ) =
      f_neg2_0_2_1_1_neg1 by
    rw [f_neg2_0_2_1_1_neg1, Polynomial.C_neg]
    norm_num
    ring]
  rw [show (Polynomial.X ^ 3 + Polynomial.C (-2 : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (0 : ℚ) * Polynomial.X + Polynomial.C (2 : ℚ) : Polynomial ℚ) =
      g_neg2_0_2_1_1_neg1 by
    rw [g_neg2_0_2_1_1_neg1, Polynomial.C_neg]
    rw [show Polynomial.C (2 : ℚ) = (2 : Polynomial ℚ) by rfl]
    simp
    ring]
  exact ⟨AlgEquiv.ofAlgHom φ_neg2_0_2_1_1_neg1 ψ_neg2_0_2_1_1_neg1
    hφψ_neg2_0_2_1_1_neg1 hψφ_neg2_0_2_1_1_neg1⟩

end

end Commons.FieldTheory.AdjoinRoot