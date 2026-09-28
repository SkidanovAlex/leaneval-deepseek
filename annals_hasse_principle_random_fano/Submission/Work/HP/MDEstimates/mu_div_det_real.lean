import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.MDEstimates.mu_sum_aux
import Submission.Work.HP.MDEstimates.dmin_facts

/-!
# `μ(x,y)^R / det Γ_{x,y}` for the exceptional pairs

Browning--Le Boudec--Sawin, *The Hasse principle for random Fano hypersurfaces* (Annals 2023), §4.
This is the `R`-th-power form of the bound `mu_div_det_bound` needed when the weight in the
second-moment estimate is raised to a power.

For `d = n = 4` (quartic threefolds, so `‖ν(x)‖` is a cubic power of `‖x‖` up to constants), write

`𝔡₂ = dmin 2 {x,y},  𝔡₃ = dmin 3 {x,y},  Nx = ‖x‖,  Ny = ‖y‖,  G = detL (Gam 4 4 x y)`.

The hypothesis `¬(𝔡₂³ ≤ 𝔡₃ Nx Ny)` selects the branch of the maximum in
`μ(x,y) = 3n² max(𝔡₂/𝔡₃, Nx·Ny/𝔡₂²)` on which the first term dominates, so that
`μ(x,y) = 3n² 𝔡₂/𝔡₃ = 48 𝔡₂/𝔡₃`.  With the lower bound `Cdet · 𝔡₂ · Nx³ Ny³ ≤ G` on the
covolume one obtains

`μ(x,y)^R / G ≤ 48^R (Nx Ny)^{R-4} / (𝔡₃^R · Cdet)`.

The proof is short because it only uses `𝔡₂ ≤ Nx·Ny` and `Nx·Ny > 0`: writing the right-hand side
as `48^R 𝔡₂^R / (𝔡₃^R G)` the claim is equivalent to `Cdet · 𝔡₂^R · (Nx Ny)^{4-R} ≤ G`, and

`Cdet · 𝔡₂^R (Nx Ny)^{4-R}
   = (Cdet · 𝔡₂ · (Nx Ny)³) · (𝔡₂/(Nx Ny))^{R-1} ≤ Cdet · 𝔡₂ · (Nx Ny)³ ≤ G`

since `0 ≤ 𝔡₂/(Nx Ny) ≤ 1` and `R ≥ 1`.
-/

set_option autoImplicit false
noncomputable section

open Work.HP

namespace Work.HP.MDEstimates

/-- Branch computation for `μ`: if `𝔡₂³ > 𝔡₃·A` with `𝔡₂, 𝔡₃ > 0`, then the first argument of the
maximum defining `muXY 4 x y` dominates. -/
private lemma muXY_four_eq (x y : Fin 5 → ℤ)
    (hneg : ¬ (dmin 2 ({x, y} : Set (Fin 5 → ℤ)) * dmin 2 ({x, y} : Set (Fin 5 → ℤ)) ^ 2
        ≤ dmin 3 ({x, y} : Set (Fin 5 → ℤ)) * (eNorm x * eNorm y)))
    (hd2 : 0 < dmin 2 ({x, y} : Set (Fin 5 → ℤ)))
    (hd3 : 0 < dmin 3 ({x, y} : Set (Fin 5 → ℤ))) :
    muXY 4 x y = 3 * (4 : ℝ) ^ 2 *
      (dmin 2 ({x, y} : Set (Fin 5 → ℤ)) / dmin 3 ({x, y} : Set (Fin 5 → ℤ))) := by
  rw [muXY]
  simp only [Nat.cast_ofNat]
  rw [show max (dmin 2 ({x, y} : Set (Fin 5 → ℤ)) / dmin 3 ({x, y} : Set (Fin 5 → ℤ)))
      (eNorm x * eNorm y / dmin 2 ({x, y} : Set (Fin 5 → ℤ)) ^ 2)
      = dmin 2 ({x, y} : Set (Fin 5 → ℤ)) / dmin 3 ({x, y} : Set (Fin 5 → ℤ)) from
    max_eq_left (by
      rw [div_le_div_iff₀ (pow_pos hd2 2) hd3]
      have h' := lt_of_not_ge hneg
      nlinarith [h'])]

/-- **Real-arithmetic core.**  For positive `K, Cdet, d3, A, G`, `0 ≤ d2 ≤ A`, `R ≥ 1` and
`Cdet · d2 · A³ ≤ G` one has `(K·(d2/d3))^R / G ≤ K^R · A^{R-4} / (d3^R · Cdet)`.

The content is the elementary inequality `Cdet · d2^R · A^{4-R} ≤ G`, which follows from
`d2^R ≤ d2 · A^{R-1}` (here `R ≥ 1` and `d2 ≤ A`) together with the hypothesis. -/
private lemma mu_div_det_rpow_core (K Cdet d2 d3 A G : ℝ) (R : ℕ)
    (hK : 0 < K) (hCdet : 0 < Cdet) (hd2 : 0 ≤ d2) (hd2A : d2 ≤ A) (hd3 : 0 < d3)
    (hA : 0 < A) (hG : 0 < G) (hdet : Cdet * d2 * A ^ 3 ≤ G) (hR : 1 ≤ R) :
    (K * (d2 / d3)) ^ R / G ≤ K ^ R * A ^ ((R : ℝ) - 4) / d3 ^ R / Cdet := by
  have hkey : Cdet * d2 ^ R * A ^ 4 ≤ G * A ^ R := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : R ≠ 0)
    -- `d2^(k+1) ≤ d2 · A^k`
    have h1 : d2 ^ (k + 1) ≤ d2 * A ^ k := by
      rw [pow_succ]
      have := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hd2 hd2A k) hd2
      nlinarith [this]
    calc Cdet * d2 ^ (k + 1) * A ^ 4
        ≤ Cdet * (d2 * A ^ k) * A ^ 4 := by
          have hC4 : 0 ≤ Cdet * A ^ 4 := mul_nonneg (le_of_lt hCdet) (pow_nonneg (le_of_lt hA) 4)
          nlinarith [mul_le_mul_of_nonneg_right h1 hC4]
      _ = Cdet * d2 * A ^ 3 * A ^ (k + 1) := by ring
      _ ≤ G * A ^ (k + 1) :=
          mul_le_mul_of_nonneg_right hdet (pow_nonneg (le_of_lt hA) (k + 1))
  rw [Real.rpow_sub hA (R:ℝ) 4, Real.rpow_natCast, mul_pow, div_pow, Real.rpow_ofNat]
  field_simp
  ring_nf at hkey ⊢
  linarith

/-- **`μ(x,y)^R / det Γ_{x,y}` on the branch where the first term of the maximum dominates.**

Given `𝔡₂³ > 𝔡₃ ‖x‖‖y‖` and the covolume lower bound
`Cdet · 𝔡₂ · ‖x‖³‖y‖³ ≤ detL (Gam 4 4 x y)` (the `d = n = 4` case of the archimedean
`detGam_lower`), the `R`-th power of `μ(x,y) = 48 𝔡₂/𝔡₃` satisfies

`μ(x,y)^R / det Γ_{x,y} ≤ 48^R (‖x‖‖y‖)^{R-4} / (𝔡₃^R · Cdet)`.

This is the quartic-threefold (`d = n = 4`) form used in the second-moment estimate, where the
weight `1/‖ν(x)‖` of `det Γ^{-1}` has been raised to the power `R`. -/
theorem mu_div_det_real (Cdet : ℝ) (hCdet : 0 < Cdet) :
    ∀ (R : ℕ), 1 ≤ R → ∀ (x y : Fin 5 → ℤ),
      IsPrim x → IsPrim y → LinearIndependent ℤ ![x, y] →
      ¬ (dmin 2 ({x, y} : Set (Fin 5 → ℤ)) * dmin 2 ({x, y} : Set (Fin 5 → ℤ)) ^ 2
          ≤ dmin 3 ({x, y} : Set (Fin 5 → ℤ)) * (eNorm x * eNorm y)) →
      Cdet * dmin 2 ({x, y} : Set (Fin 5 → ℤ)) * eNorm x ^ 3 * eNorm y ^ 3 ≤ detL (Gam 4 4 x y) →
      (muXY 4 x y) ^ R / detL (Gam 4 4 x y)
        ≤ (3 * (4 : ℝ) ^ 2) ^ R * (eNorm x * eNorm y) ^ ((R : ℝ) - 4)
            / (dmin 3 ({x, y} : Set (Fin 5 → ℤ))) ^ R / Cdet := by
  intro R hR x y hx hy hind hneg hdet
  -- the basic size facts about `𝔡₂`, `𝔡₃` and the two norms
  have hdf := dmin_facts 4 (by norm_num)
  have hd2one : 1 ≤ dmin 2 ({x, y} : Set (Fin 5 → ℤ)) := hdf.1 x y hind
  have hd2ub : dmin 2 ({x, y} : Set (Fin 5 → ℤ)) ≤ eNorm x * eNorm y := hdf.2.1 x y hind
  have hd3one : 1 ≤ dmin 3 ({x, y} : Set (Fin 5 → ℤ)) := hdf.2.2.1 x y hind
  have hd2pos : 0 < dmin 2 ({x, y} : Set (Fin 5 → ℤ)) := lt_of_lt_of_le zero_lt_one hd2one
  have hd3pos : 0 < dmin 3 ({x, y} : Set (Fin 5 → ℤ)) := lt_of_lt_of_le zero_lt_one hd3one
  have hNx : 0 < eNorm x := eNorm_pos_of_ne_zero (isPrim_ne_zero hx)
  have hNy : 0 < eNorm y := eNorm_pos_of_ne_zero (isPrim_ne_zero hy)
  have hApos : 0 < eNorm x * eNorm y := mul_pos hNx hNy
  -- the covolume hypothesis, with `‖x‖³‖y‖³` collected as `(‖x‖‖y‖)³`
  have hdet' : Cdet * dmin 2 ({x, y} : Set (Fin 5 → ℤ)) * (eNorm x * eNorm y) ^ 3
      ≤ detL (Gam 4 4 x y) := by
    convert hdet using 1
    ring
  have hG : 0 < detL (Gam 4 4 x y) :=
    lt_of_lt_of_le (mul_pos (mul_pos (mul_pos hCdet hd2pos) (pow_pos hNx 3)) (pow_pos hNy 3)) hdet
  have hcore := mu_div_det_rpow_core (3 * (4 : ℝ) ^ 2) Cdet
      (dmin 2 ({x, y} : Set (Fin 5 → ℤ))) (dmin 3 ({x, y} : Set (Fin 5 → ℤ)))
      (eNorm x * eNorm y) (detL (Gam 4 4 x y)) R (by norm_num) hCdet (le_of_lt hd2pos)
      hd2ub hd3pos hApos hG hdet' hR
  rw [muXY_four_eq x y hneg hd2pos hd3pos]
  exact hcore

end Work.HP.MDEstimates
