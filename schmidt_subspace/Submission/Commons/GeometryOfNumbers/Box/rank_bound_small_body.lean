import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace Commons.GeometryOfNumbers.Box

open Finset Matrix

lemma det_abs_le_sum {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) :
    |M.det| ≤ ∑ σ : Equiv.Perm n, ∏ i, |M (σ i) i| := by
  rw [Matrix.det_apply']
  refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun σ _ => ?_)
  rw [abs_mul, Finset.abs_prod]
  have h1 : |((Equiv.Perm.sign σ : ℤ) : ℝ)| = 1 := by
    rw [← Int.cast_abs, Equiv.Perm.sign_abs, Int.cast_one]
  rw [h1, one_mul]

lemma eventually_rpow_mul_lt {S : ℝ} (hS : S < 0) {δ N : ℝ} (hN : 0 < N) (hδ : 0 < δ) :
    ∃ Q₀ : ℝ, 1 ≤ Q₀ ∧ ∀ Q : ℝ, Q₀ ≤ Q → N * Q ^ S < δ := by
  set t := -S with ht
  have htpos : 0 < t := by rw [ht]; linarith
  have htne : t ≠ 0 := ne_of_gt htpos
  set x := N / δ with hx
  have hxpos : 0 < x := by rw [hx]; positivity
  refine ⟨1 + x ^ (1/t), ?_, ?_⟩
  · have : 0 < x ^ (1/t) := Real.rpow_pos_of_pos hxpos _
    linarith
  · intro Q hQ
    have hQ0pos : 0 < 1 + x ^ (1/t) := by
      have : 0 < x ^ (1/t) := Real.rpow_pos_of_pos hxpos _
      linarith
    have hxnn : 0 ≤ x ^ (1/t) := Real.rpow_nonneg (le_of_lt hxpos) _
    have hxt : (x ^ (1/t)) ^ t = x := by
      rw [← Real.rpow_mul (le_of_lt hxpos) (1/t) t, one_div, inv_mul_cancel₀ htne,
        Real.rpow_one]
    have hbaselt : x^(1/t) < 1 + x^(1/t) := by linarith
    have hlt : x < (1 + x^(1/t)) ^ t := by
      calc x = (x^(1/t))^t := hxt.symm
        _ < (1 + x^(1/t))^t := Real.rpow_lt_rpow hxnn hbaselt htpos
    have hQ0tpos : 0 < (1 + x^(1/t)) ^ t := Real.rpow_pos_of_pos hQ0pos _
    have hS_eq : -t = S := by rw [ht]; ring
    have step1 : N < δ * (1 + x^(1/t)) ^ t := by
      have h' := (div_lt_iff₀ hδ).mp hlt
      rw [hx] at h'
      rw [mul_comm] at h'
      exact h'
    have hQ0S : (1 + x ^ (1/t)) ^ S = ((1 + x^(1/t))^t)⁻¹ := by
      rw [← hS_eq, Real.rpow_neg (le_of_lt hQ0pos)]
    have hQpos : 0 < Q := lt_of_lt_of_le hQ0pos hQ
    have hmono : Q ^ S ≤ (1 + x^(1/t)) ^ S :=
      Real.rpow_le_rpow_of_nonpos hQ0pos hQ (le_of_lt hS)
    have hbdd : N * (1 + x^(1/t)) ^ S < δ := by
      rw [hQ0S]
      calc N * ((1 + x^(1/t))^t)⁻¹
            < (δ * (1+x^(1/t))^t) * ((1+x^(1/t))^t)⁻¹ :=
              mul_lt_mul_of_pos_right step1 (inv_pos.mpr hQ0tpos)
        _ = δ := by rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hQ0tpos), mul_one]
    calc N * Q ^ S ≤ N * (1 + x^(1/t)) ^ S :=
          mul_le_mul_of_nonneg_left hmono (le_of_lt hN)
      _ < δ := hbdd

theorem rank_bound_small_body {σ : Type*} [Fintype σ] [Nonempty σ]
    (A : (σ → ℝ) →ₗ[ℝ] (σ → ℝ)) (hA : Function.Injective A)
    (c : σ → ℝ) (hc : ∑ i, c i < 0) :
    ∃ Q₀ : ℝ, 1 ≤ Q₀ ∧ ∀ Q : ℝ, Q₀ ≤ Q →
      ¬ ∃ y : σ → (σ → ℤ),
        LinearIndependent ℚ (fun i => (fun j => (y i j : ℚ))) ∧
        ∀ i k, |(A (fun j => (y i j : ℝ))) k| ≤ Q ^ (c k) := by
  classical
  obtain ⟨M, hM⟩ : ∃ M : Matrix σ σ ℝ, M.mulVec = ⇑A :=
    ⟨LinearMap.toMatrix' A, by funext v; exact LinearMap.toMatrix'_mulVec A v⟩
  have hdetM : M.det ≠ 0 := by
    have hMinj : Function.Injective M.mulVec := by rw [hM]; exact hA
    have hunit : IsUnit M := Matrix.mulVec_injective_iff_isUnit.mp hMinj
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det M).mp hunit)
  have hA_apply : ∀ (w : σ → ℝ) (k : σ), (A w) k = ∑ j, M k j * w j := by
    intro w k
    have h1 : A w = M.mulVec w := by rw [hM]
    rw [h1]
    simp only [Matrix.mulVec, dotProduct]
  -- threshold
  set S : ℝ := ∑ i, c i with hSdef
  have hSneg : S < 0 := by rw [hSdef]; exact hc
  set N : ℝ := (Fintype.card (Equiv.Perm σ) : ℝ) with hNdef
  have hNpos : 0 < N := by
    rw [hNdef]
    have : 0 < Fintype.card (Equiv.Perm σ) := Fintype.card_pos_iff.mpr ⟨1⟩
    exact_mod_cast this
  obtain ⟨Q₀, hQ₀1, hQ₀⟩ :=
    eventually_rpow_mul_lt (δ := |M.det|) hSneg hNpos (abs_pos.mpr hdetM)
  refine ⟨Q₀, hQ₀1, fun Q hQ => ?_⟩
  rintro ⟨y, hyind, hybound⟩
  have hQpos : 0 < Q := lt_of_lt_of_le one_pos (le_trans hQ₀1 hQ)
  set Y : Matrix σ σ ℤ := Matrix.of (fun i j => y i j) with hYdef
  set YQ : Matrix σ σ ℚ := (Int.castRingHom ℚ).mapMatrix Y with hYQdef
  set YR : Matrix σ σ ℝ := (Int.castRingHom ℝ).mapMatrix Y with hYRdef
  set B : Matrix σ σ ℝ := Matrix.of (fun i k => (A (fun j => (y i j : ℝ))) k) with hBdef
  have hyre : ∀ i j, YR i j = (y i j : ℝ) := by
    intro i j; simp [YR, Y, Matrix.map]
  have hYQdet : YQ.det ≠ 0 := by
    have hli : LinearIndependent ℚ YQ.row := by
      have h : YQ.row = fun i => fun j => (y i j : ℚ) := by
        funext i j; simp [YQ, Y, Matrix.map]
      rw [h]; exact hyind
    have hunit := Matrix.linearIndependent_rows_iff_isUnit.mp hli
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det YQ).mp hunit)
  have hYQdet' : YQ.det = (Y.det : ℚ) := by
    have hh := (RingHom.map_det (Int.castRingHom ℚ) Y).symm
    simpa [YQ] using hh
  have hYdet : Y.det ≠ 0 := by
    intro hz
    exact hYQdet (by rw [hYQdet', hz, Int.cast_zero])
  have hYRdet : YR.det = (Y.det : ℝ) := by
    have hh := (RingHom.map_det (Int.castRingHom ℝ) Y).symm
    simpa [YR] using hh
  have hYR_ge : 1 ≤ |YR.det| := by
    rw [hYRdet, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hYdet
  have hB_eq : B = YR * Mᵀ := by
    ext i k
    have hBik : B i k = (A (fun j => (y i j : ℝ))) k := rfl
    rw [hBik, hA_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Matrix.transpose_apply, hyre]
    ring
  have hdetB : B.det = YR.det * M.det := by
    rw [hB_eq, Matrix.det_mul, Matrix.det_transpose]
  have hlower : |M.det| ≤ |B.det| := by
    rw [hdetB, abs_mul]
    calc |M.det| = 1 * |M.det| := (one_mul _).symm
      _ ≤ |YR.det| * |M.det| := mul_le_mul_of_nonneg_right hYR_ge (abs_nonneg _)
  have hprod : ∏ i, Q ^ (c i) = Q ^ S := by
    have hh := (Real.rpow_sum_of_pos hQpos c Finset.univ).symm
    simpa [hSdef] using hh
  have hhigh : |B.det| ≤ N * Q ^ S := by
    calc |B.det| ≤ ∑ σ : Equiv.Perm σ, ∏ i, |B (σ i) i| := det_abs_le_sum B
      _ ≤ ∑ σ : Equiv.Perm σ, ∏ i, Q ^ (c i) := by
            refine Finset.sum_le_sum (fun s _ => ?_)
            refine Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => ?_)
            exact hybound (s i) i
      _ = N * Q ^ S := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hNdef, hprod]
  have hlt : |B.det| < |M.det| := lt_of_le_of_lt hhigh (hQ₀ Q hQ)
  exact not_lt_of_ge hlower hlt

end Commons.GeometryOfNumbers.Box