import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Basic.cramer
import Submission.Work.TMC16Core.Basic.toNat_interval_facts
import Submission.Work.TMC16Core.Basic.div_lt_exp_sub

namespace Work.TMC16Core.Basic

open Work.TMC16Core

/-! ## Symmetry of the Dirichlet Green's function

`greenEntry` is an entry of the inverse of `dirMat`, which is symmetric since it is the
tridiagonal matrix `triD`.  Hence `G` is symmetric in its two site arguments. -/

lemma dirMat_transpose_local (α lam : ℝ) (θ : ℝ) (E : ℂ) (n : ℕ) :
    Matrix.transpose (dirMat α lam θ E n) = dirMat α lam θ E n := by
  rw [dirMat_eq_triD, triD_transpose]

lemma G_symm_local {α lam : ℝ} {θ : ℝ} {E : ℂ} {x₁ x₂ x y : ℤ} :
    G α lam θ E x₁ x₂ x y = G α lam θ E x₁ x₂ y x := by
  have hsym : Matrix.transpose (dirMat α lam (θ + (x₁ : ℝ) * α) E ((x₂ - x₁ + 1).toNat))
      = dirMat α lam (θ + (x₁ : ℝ) * α) E ((x₂ - x₁ + 1).toNat) :=
    dirMat_transpose_local _ _ _ _ _
  have hinv : (dirMat α lam (θ + (x₁ : ℝ) * α) E ((x₂ - x₁ + 1).toNat))⁻¹
      = Matrix.transpose ((dirMat α lam (θ + (x₁ : ℝ) * α) E ((x₂ - x₁ + 1).toNat))⁻¹) := by
    rw [Matrix.transpose_nonsing_inv, hsym]
  simp only [G, greenEntry]
  by_cases h1 : (x - x₁).toNat < (x₂ - x₁ + 1).toNat ∧ (y - x₁).toNat < (x₂ - x₁ + 1).toNat
  · have h2 : (y - x₁).toNat < (x₂ - x₁ + 1).toNat ∧ (x - x₁).toNat < (x₂ - x₁ + 1).toNat :=
      ⟨h1.2, h1.1⟩
    rw [dif_pos h1, dif_pos h2]
    have h := congrArg (fun M : Matrix (Fin ((x₂ - x₁ + 1).toNat)) (Fin ((x₂ - x₁ + 1).toNat)) ℂ =>
        M ⟨(y - x₁).toNat, h2.1⟩ ⟨(x - x₁).toNat, h1.1⟩) hinv
    simpa [Matrix.transpose_apply] using h.symm
  · have h2 : ¬((y - x₁).toNat < (x₂ - x₁ + 1).toNat ∧ (x - x₁).toNat < (x₂ - x₁ + 1).toNat) :=
      fun h => h1 ⟨h.2, h.1⟩
    rw [dif_neg h1, dif_neg h2]

/-- **Cramer's rule for the Dirichlet Green's function, in the form consumed by the
regularity family.**  Let `[x₁, x₁+k-1]` be an interval of `k ≥ 40` sites with `y` inside
it, at distance at least `k/40` from both endpoints.  If the Dirichlet determinant at the
left endpoint is exponentially large, `‖pd α lam (θ+x₁α) E (k+1)‖ > e^{c k}`, and the
continuants of all lengths `n ∈ [k/40, k]` are bounded by `e^{n(L+ε₁)}`, then the two
boundary entries of the Green's function decay at rate `c`:
`‖G(y,x₁)‖ < e^{(L+ε₁)·(x₂-y) - c k}` and `‖G(y,x₂)‖ < e^{(L+ε₁)·(y-x₁) - c k}`. -/
theorem green_bound_reg {α lam : ℝ} {E : ℂ} {θ : ℝ} {L ε₁ c : ℝ} {k : ℕ} {x₁ y : ℤ}
    (hε₁ : 0 < ε₁) (hk40 : 40 ≤ k)
    (hbd : ∀ n : ℕ, k / 40 ≤ n → n ≤ k → ∀ ζ : ℝ,
        ‖Work.TMC16Core.pd α lam ζ E (n + 1)‖ ≤ Real.exp ((n : ℝ) * (L + ε₁)))
    (hbig : Real.exp (c * (k : ℝ)) <
        ‖Work.TMC16Core.pd α lam (θ + (x₁ : ℝ) * α) E (k + 1)‖)
    (hd1 : (k : ℤ) ≤ 40 * (y - x₁))
    (hd2 : (k : ℤ) ≤ 40 * ((x₁ + (k : ℤ) - 1) - y)) :
    ‖Work.TMC16Core.G α lam θ E x₁ (x₁ + (k : ℤ) - 1) y x₁‖ <
        Real.exp ((L + ε₁) * (((x₁ + (k : ℤ) - 1) - y : ℤ) : ℝ) - c * (k : ℝ)) ∧
      ‖Work.TMC16Core.G α lam θ E x₁ (x₁ + (k : ℤ) - 1) y (x₁ + (k : ℤ) - 1)‖ <
        Real.exp ((L + ε₁) * ((y - x₁ : ℤ) : ℝ) - c * (k : ℝ)) := by
  have _hε₁ := hε₁
  set x₂ : ℤ := x₁ + (k : ℤ) - 1 with hx₂
  have hxy : x₁ ≤ y := by omega
  have hyx : y ≤ x₂ := by omega
  obtain ⟨hK, -, hJk, hPk, hsum, hJcast, hPcast, -⟩ :=
    toNat_interval_facts (k := k) (x₁ := x₁) (x₂ := x₂) (y := y) hx₂ hxy hyx
  set J : ℕ := (y - x₁).toNat with hJdef
  set P : ℕ := (x₂ - y).toNat with hPdef
  have hJz : (J : ℤ) = y - x₁ := by rw [hJdef]; exact_mod_cast hJcast
  have hPz : (P : ℤ) = x₂ - y := by rw [hPdef]; exact_mod_cast hPcast
  have hJle : J ≤ k := by rw [hJdef]; exact hJk
  have hPle : P ≤ k := by rw [hPdef]; exact hPk
  have hk40J : k / 40 ≤ J := by
    rw [hJdef]
    exact Nat.div_le_of_le_mul (by omega)
  have hk40P : k / 40 ≤ P := by
    rw [hPdef]
    exact Nat.div_le_of_le_mul (by omega)
  obtain ⟨hc1, hc2⟩ := cramer α lam θ E x₁ x₂ y hxy hyx
  have hnumA : ‖pd α lam (θ + ((y : ℝ) + 1) * α) E ((x₂ - y).toNat + 1)‖
      ≤ Real.exp ((P : ℝ) * (L + ε₁)) := by
    have h := hbd P (by rw [hPdef]; exact hk40P) (by rw [hPdef]; exact hPle)
      (θ + ((y : ℝ) + 1) * α)
    rwa [hPdef] at h
  have hnumB : ‖pd α lam (θ + (x₁ : ℝ) * α) E ((y - x₁).toNat + 1)‖
      ≤ Real.exp ((J : ℝ) * (L + ε₁)) := by
    have h := hbd J (by rw [hJdef]; exact hk40J) (by rw [hJdef]; exact hJle)
      (θ + (x₁ : ℝ) * α)
    rwa [hJdef] at h
  have hden : Real.exp (c * (k : ℝ)) <
      ‖pd α lam (θ + (x₁ : ℝ) * α) E ((x₂ - x₁ + 1).toNat + 1)‖ := by
    rw [hK]; exact hbig
  have hGs : G α lam θ E x₁ x₂ y x₁ = G α lam θ E x₁ x₂ x₁ y :=
    G_symm_local (x := y) (y := x₁)
  refine ⟨?_, ?_⟩
  · rw [hGs, hc1, norm_div]
    have h := div_lt_exp_sub (X := (P : ℝ) * (L + ε₁)) (Y := c * (k : ℝ)) hden
      (norm_nonneg _) hnumA
    have hexp : (P : ℝ) * (L + ε₁) - c * (k : ℝ)
        = (L + ε₁) * ((x₂ - y : ℤ) : ℝ) - c * (k : ℝ) := by
      rw [hPdef, hPcast]; ring
    rwa [hexp] at h
  · rw [hc2, norm_div]
    have h := div_lt_exp_sub (X := (J : ℝ) * (L + ε₁)) (Y := c * (k : ℝ)) hden
      (norm_nonneg _) hnumB
    have hexp : (J : ℝ) * (L + ε₁) - c * (k : ℝ)
        = (L + ε₁) * ((y - x₁ : ℤ) : ℝ) - c * (k : ℝ) := by
      rw [hJdef, hJcast]; ring
    rwa [hexp] at h

end Work.TMC16Core.Basic
