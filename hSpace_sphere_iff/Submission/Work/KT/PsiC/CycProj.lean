import Mathlib
import Submission.Work.KT.PsiC.Setup
import Submission.Work.KT.PsiC.ReindexAux
import Submission.Work.KT.Psi.OrbitBasic
import Submission.Work.KT.Psi.OrbitFacts
import Submission.Work.KT.Psi.k3Aux

/-!
# `Work.KT.PsiC.CycProj` — the spectral projectors of a permutation of order three
-/

namespace Work.KT.PsiC

open Matrix
open Work.KT.Psi

noncomputable section

variable {A : Type} [Ring A] [Algebra ℂ A]
variable {M : Type} [Ring M] [Algebra ℂ M]

/-- `algebraMap`-scalars and `ℂ`-scalars on matrices agree. -/
theorem smulA_eq_smulC {ι : Type} (c : ℂ) (X : Matrix ι ι A) :
    algebraMap ℂ A c • X = c • X := by
  ext i j
  simp only [Matrix.smul_apply, Algebra.smul_def, smul_eq_mul]

/-- Powers of a permutation matrix. -/
theorem permMatrix_pow {ι : Type} [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι) (n : ℕ) :
    (σ.permMatrix A) ^ n = (σ ^ n).permMatrix A := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Matrix.permMatrix_one]
  | succ n ih =>
      rw [pow_succ, pow_succ, Matrix.permMatrix_mul, ← ih, ← pow_succ, ← pow_succ']

theorem permMatrix_cube {ι : Type} [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι)
    (hσ : σ * σ * σ = 1) : (σ.permMatrix A) ^ 3 = 1 := by
  rw [permMatrix_pow, show σ ^ 3 = σ * σ * σ from by rw [pow_succ, pow_two], hσ,
    Matrix.permMatrix_one]

theorem permMatrix_sq {ι : Type} [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι)
    (hσ : σ * σ = 1) : (σ.permMatrix A) ^ 2 = 1 := by
  rw [permMatrix_pow, show σ ^ 2 = σ * σ from pow_two σ, hσ, Matrix.permMatrix_one]

/-- The explicit three-term form of `orbitSpec` for `k = 3`. -/
theorem orbitSpec_three (lam : ℂ) (g : M) :
    orbitSpec lam g 3 = ((3 : ℂ)⁻¹) • (1 + lam⁻¹ • g + (lam⁻¹) ^ 2 • g ^ 2) := by
  rw [orbitSpec, geoSum, qg]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [pow_zero, pow_one]
  rw [smul_pow, add_assoc, Nat.cast_ofNat]

/-- `cycProj` is `orbitSpec`. -/
theorem cycProj_eq_orbitSpec {ι : Type} [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι)
    (lam : ℂ) :
    cycProj (A := A) σ lam = orbitSpec lam (σ.permMatrix A) 3 := by
  rw [cycProj, orbitSpec_three]
  rw [smulA_eq_smulC, smulA_eq_smulC, smulA_eq_smulC]
  simp only [one_div, pow_two, Nat.cast_ofNat]

/-- `halfProj` is `orbitSpec`. -/
theorem halfProj_eq_orbitSpec {ι : Type} [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι) (ε : ℂ)
    (hε : ε ^ 2 = 1) :
    halfProj (A := A) ε σ = orbitSpec ε (σ.permMatrix A) 2 := by
  have h0 : ε ≠ 0 := by intro h; rw [h] at hε; norm_num at hε
  have hε' : ε * ε = 1 := by rw [← pow_two]; exact hε
  have h2 : ε⁻¹ = ε := by
    calc ε⁻¹ = 1 * ε⁻¹ := (one_mul _).symm
      _ = (ε * ε) * ε⁻¹ := by rw [hε']
      _ = ε * (ε * ε⁻¹) := mul_assoc _ _ _
      _ = ε * 1 := by rw [mul_inv_cancel₀ h0]
      _ = ε := mul_one _
  rw [halfProj, orbitSpec, geoSum, qg]
  rw [Finset.sum_range_succ, Finset.sum_range_one, h2]
  simp only [pow_zero, pow_one]
  rw [smulA_eq_smulC, smulA_eq_smulC, one_div, Nat.cast_ofNat]

/-- Distinct eigenparts of a cyclic action are orthogonal. -/
theorem orbitSpec_mul_eq_zero {lam mu : ℂ} {g : M} {k : ℕ} (hk : 0 < k) (hlam : lam ^ k = 1)
    (hmu : mu ^ k = 1) (hq : qg lam g ^ k = 1) (hq' : qg mu g ^ k = 1) (hne : lam ≠ mu) :
    orbitSpec lam g k * orbitSpec mu g k = 0 := by
  have h1 : orbitSpec lam g k * g = algebraMap ℂ M lam * orbitSpec lam g k :=
    orbitSpec_mul_g hk hlam hq
  have h2 : g * orbitSpec mu g k = algebraMap ℂ M mu * orbitSpec mu g k :=
    g_mul_orbitSpec hk hmu hq'
  have key : algebraMap ℂ M lam * (orbitSpec lam g k * orbitSpec mu g k) =
      algebraMap ℂ M mu * (orbitSpec lam g k * orbitSpec mu g k) := by
    calc algebraMap ℂ M lam * (orbitSpec lam g k * orbitSpec mu g k)
        = (algebraMap ℂ M lam * orbitSpec lam g k) * orbitSpec mu g k :=
            (mul_assoc _ _ _).symm
      _ = (orbitSpec lam g k * g) * orbitSpec mu g k := by rw [← h1]
      _ = orbitSpec lam g k * (g * orbitSpec mu g k) := mul_assoc _ _ _
      _ = orbitSpec lam g k * (algebraMap ℂ M mu * orbitSpec mu g k) := by rw [h2]
      _ = (orbitSpec lam g k * algebraMap ℂ M mu) * orbitSpec mu g k :=
            (mul_assoc _ _ _).symm
      _ = (algebraMap ℂ M mu * orbitSpec lam g k) * orbitSpec mu g k := by
            rw [← Algebra.commutes]
      _ = algebraMap ℂ M mu * (orbitSpec lam g k * orbitSpec mu g k) := mul_assoc _ _ _
  have hsub : algebraMap ℂ M (lam - mu) * (orbitSpec lam g k * orbitSpec mu g k) = 0 := by
    rw [map_sub, sub_mul, key, sub_self]
  have hunit : IsUnit (algebraMap ℂ M (lam - mu)) :=
    (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hne)).map (algebraMap ℂ M)
  obtain ⟨u, hu⟩ := hunit
  have h3 : (↑u : M) * (orbitSpec lam g k * orbitSpec mu g k) = 0 := by
    rw [hu]; exact hsub
  have h4 : orbitSpec lam g k * orbitSpec mu g k =
      (↑u⁻¹ : M) * ((↑u : M) * (orbitSpec lam g k * orbitSpec mu g k)) := by
    rw [← mul_assoc, Units.inv_mul, one_mul]
  rw [h4, h3, mul_zero]

/-- `cycProj σ λ` is idempotent for `σ³ = 1`, `λ³ = 1`. -/
theorem cycProj_idem {ι : Type} [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι) (lam : ℂ)
    (hσ : σ * σ * σ = 1) (hlam : lam ^ 3 = 1) :
    cycProj (A := A) σ lam * cycProj (A := A) σ lam = cycProj (A := A) σ lam := by
  rw [cycProj_eq_orbitSpec]
  exact orbitSpec_idem (k := 3) (by norm_num) (qg_pow_eq_one (M := Matrix ι ι A) (permMatrix_cube (A := A) σ hσ) hlam)

/-- Distinct spectral projectors of a permutation of order three are orthogonal. -/
theorem cycProj_orth {ι : Type} [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι) (lam mu : ℂ)
    (hσ : σ * σ * σ = 1) (hlam : lam ^ 3 = 1) (hmu : mu ^ 3 = 1) (hne : lam ≠ mu) :
    cycProj (A := A) σ lam * cycProj (A := A) σ mu = 0 := by
  rw [cycProj_eq_orbitSpec (A := A) σ lam]
  rw [show cycProj (A := A) σ mu = orbitSpec mu (σ.permMatrix A) 3 from
    cycProj_eq_orbitSpec (A := A) σ mu]
  exact orbitSpec_mul_eq_zero (k := 3) (by norm_num) hlam hmu
    (qg_pow_eq_one (M := Matrix ι ι A) (permMatrix_cube (A := A) σ hσ) hlam)
    (qg_pow_eq_one (M := Matrix ι ι A) (permMatrix_cube (A := A) σ hσ) hmu) hne

/-- `halfProj ε σ` is idempotent for `σ² = 1`, `ε² = 1`. -/
theorem halfProj_idem {ι : Type} [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι) (ε : ℂ)
    (hσ : σ * σ = 1) (hε : ε ^ 2 = 1) :
    halfProj (A := A) ε σ * halfProj (A := A) ε σ = halfProj (A := A) ε σ := by
  rw [halfProj_eq_orbitSpec (A := A) σ ε hε]
  exact orbitSpec_idem (k := 2) (by norm_num)
    (qg_pow_eq_one (M := Matrix ι ι A) (permMatrix_sq (A := A) σ hσ) hε)

/-- The two eigenparts of an involution are orthogonal. -/
theorem halfProj_orth {ι : Type} [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι) (ε : ℂ)
    (hσ : σ * σ = 1) (hε : ε ^ 2 = 1) :
    halfProj (A := A) ε σ * halfProj (A := A) (-ε) σ = 0 := by
  have hne : ε ≠ -ε := by
    intro h
    have h' : ε + ε = 0 := by
      nth_rewrite 2 [h]
      rw [add_neg_cancel]
    have h'2 : (2 : ℂ) * ε = 0 := by rw [two_mul]; exact h'
    have h2 : ε = 0 := by
      rcases mul_eq_zero.mp h'2 with h3 | h3
      · exact absurd h3 (by norm_num)
      · exact h3
    rw [h2] at hε
    norm_num at hε
  have hne2 : (-ε) ^ 2 = 1 := by rw [neg_sq, hε]
  rw [halfProj_eq_orbitSpec (A := A) σ ε hε]
  rw [show halfProj (A := A) (-ε) σ = orbitSpec (-ε) (σ.permMatrix A) 2 from
    halfProj_eq_orbitSpec (A := A) σ (-ε) hne2]
  exact orbitSpec_mul_eq_zero (k := 2) (by norm_num) hε hne2
    (qg_pow_eq_one (M := Matrix ι ι A) (permMatrix_sq (A := A) σ hσ) hε) (qg_pow_eq_one (M := Matrix ι ι A) (permMatrix_sq (A := A) σ hσ) hne2) hne

end

end Work.KT.PsiC
