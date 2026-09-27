import Mathlib
import Submission.Work.EKLC6Core.Basic

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## Auxiliary computations

Everything here is elementary.  The one non-obvious step is `det_one_add_of_cube_eq_zero`:
if `A³ = 0` then `A` is nilpotent, so (via the characteristic polynomial) `charpoly A = X³`,
and evaluating `Matrix.eval_charpoly` at `t = -1` gives `-1 = det (-(1 + A)) = -det (1 + A)`.
-/

/-- **The determinant of `1 + A` is `1` when `A³ = 0`** (for `3 × 3` real matrices).

Indeed `A` is nilpotent, so its characteristic polynomial is `X³`; evaluating the
characteristic polynomial at `-1` gives `det (Matrix.scalar _ (-1) - A) = -1`, i.e.
`-det (1 + A) = -1`. -/
private lemma det_one_add_of_cube_eq_zero (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A ^ 3 = 0) :
    (1 + A).det = 1 := by
  have hnil : IsNilpotent (Matrix.toLin' A) := by
    refine ⟨3, ?_⟩
    rw [← Matrix.toLin'_pow, hA]
    exact map_zero _
  have hcp : A.charpoly = Polynomial.X ^ 3 := by
    have h1 : (Matrix.toLin' A).charpoly
        = Polynomial.X ^ (Module.finrank ℝ (Fin 3 → ℝ)) :=
      IsNilpotent.charpoly_eq_X_pow_finrank hnil
    rw [← Matrix.charpoly_toLin', h1]
    congr 1
    simp
  have he := Matrix.eval_charpoly A (-1)
  rw [hcp] at he
  simp only [Polynomial.eval_pow, Polynomial.eval_X] at he
  have hscalar : Matrix.scalar (Fin 3) (-1 : ℝ) - A = -(1 + A) := by
    rw [map_neg, map_one]
    abel
  rw [hscalar, Matrix.det_neg, Fintype.card_fin] at he
  norm_num at he
  linarith

/-- **`(a • N + b • N²)³ = 0` when `N³ = 0`.**

Writing `P := a • 1 + b • N` we have `a • N + b • N² = P * N` and `Commute P N`, so
`(P * N)³ = P³ * N³ = 0`. -/
private lemma cube_smul_add_smul_sq_eq_zero (N : Matrix (Fin 3) (Fin 3) ℝ) (hN : N ^ 3 = 0)
    (a b : ℝ) : (a • N + b • (N * N)) ^ 3 = 0 := by
  have hPN : Commute (a • (1 : Matrix (Fin 3) (Fin 3) ℝ) + b • N) N := by
    show (a • (1 : Matrix (Fin 3) (Fin 3) ℝ) + b • N) * N
        = N * (a • (1 : Matrix (Fin 3) (Fin 3) ℝ) + b • N)
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one]
  have hA : (a • N + b • (N * N)) = (a • (1 : Matrix (Fin 3) (Fin 3) ℝ) + b • N) * N := by
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul]
  rw [hA, Commute.mul_pow hPN 3, hN, mul_zero]

/-- **Entrywise bound for the unipotent interpolation.**

If every entry of `N` is `< c` in absolute value (`0 < c ≤ 1`) then every entry of
`a • N + b • N²` with `|a| ≤ 1`, `|b| ≤ 1/2` is `< 4 c` in absolute value: the entries of `N²`
are `< 3 c² ≤ 3 c` in absolute value, whence the bound `c + (3/2) c ≤ (5/2) c < 4 c`. -/
private lemma unipotent_path_entry_bound {N : Matrix (Fin 3) (Fin 3) ℝ} {c : ℝ} (hc : 0 < c)
    (hc1 : c ≤ 1) (hN : ∀ i j, |N i j| < c) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (i j : Fin 3) :
    |(s • N + ((s ^ 2 - s) / 2) • (N * N)) i j| < 4 * c := by
  have hNN : |(N * N) i j| < 3 * c ^ 2 := by
    have hk : ∀ k : Fin 3, |N i k * N k j| < c ^ 2 := fun k => by
      rw [abs_mul]
      calc |N i k| * |N k j| < c * c :=
            mul_lt_mul'' (hN i k) (hN k j) (abs_nonneg _) (abs_nonneg _)
        _ = c ^ 2 := by ring
    calc |(N * N) i j| ≤ ∑ k : Fin 3, |N i k * N k j| := by
          rw [Matrix.mul_apply]
          exact Finset.abs_sum_le_sum_abs _ _
      _ < ∑ _k : Fin 3, c ^ 2 :=
          Finset.sum_lt_sum (fun k _ => le_of_lt (hk k)) ⟨0, Finset.mem_univ _, hk 0⟩
      _ = 3 * c ^ 2 := by rw [Fin.sum_univ_three]; ring
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
  have hs1 : |s| ≤ 1 := by rw [abs_of_nonneg hs.1]; exact hs.2
  have hs2 : |(s ^ 2 - s) / 2| ≤ 1 / 2 := by
    have h1 : s ^ 2 - s ≤ 1 / 2 := by nlinarith [hs.1, hs.2]
    have h2 : -(1 / 2) ≤ s ^ 2 - s := by nlinarith [hs.1, hs.2]
    have h3 : |s ^ 2 - s| ≤ 1 / 2 := abs_le.mpr ⟨h2, h1⟩
    calc |(s ^ 2 - s) / 2| = |s ^ 2 - s| / 2 := by rw [abs_div]; norm_num
      _ ≤ (1 / 2) / 2 := by linarith
      _ ≤ 1 / 2 := by norm_num
  have hb1 : |s * N i j| < c := by
    rw [abs_mul]
    calc |s| * |N i j| ≤ 1 * |N i j| := mul_le_mul_of_nonneg_right hs1 (abs_nonneg _)
      _ = |N i j| := one_mul _
      _ < c := hN i j
  have hb2 : |((s ^ 2 - s) / 2) * (N * N) i j| < 3 * c ^ 2 / 2 := by
    rw [abs_mul]
    calc |(s ^ 2 - s) / 2| * |(N * N) i j| ≤ (1 / 2) * |(N * N) i j| :=
          mul_le_mul_of_nonneg_right hs2 (abs_nonneg _)
      _ < (1 / 2) * (3 * c ^ 2) := by linarith
      _ = 3 * c ^ 2 / 2 := by ring
  have htri := abs_add_le (s * N i j) (((s ^ 2 - s) / 2) * (N * N) i j)
  nlinarith [htri, hb1, hb2, hc, hc1, sq_nonneg c, mul_nonneg hc.le (sub_nonneg.mpr hc1)]

/-- **A path in `V (4c)` from `1` to a unipotent `q ∈ V c`.**

For the "crossing" argument in the thin-boundary/margin step of Pisa 7.31 one needs, for
`q ∈ V c ∩ U` (with `U` a contracted unipotent subgroup, so that every `q ∈ U` is unipotent,
i.e. `(q - 1)³ = 0` for `q ∈ SL₃(ℝ)`), a continuous path from `1` to `q` that stays inside a
slightly larger entrywise ball `V (4c)`.

Explicit witness: with `N := (q : Matrix (Fin 3) (Fin 3) ℝ) - 1` and `L := N - N²/2`
(so that `L³ = 0` and `exp L = q`), take `γ s := 1 + s • L + (s²/2) • (L * L)` — a finite
polynomial in `s`, so continuity is immediate; `γ 0 = 1`, `γ 1 = q` by the nilpotency relations,
and `det (γ s) = 1` (e.g. `γ s * γ t = γ (s+t)` gives `(γ (1/k))^k = γ 1 = q`, hence
`det (γ (1/k)) = 1` for odd `k`, and continuity of `det` plus density of the rationals gives it
for all real `s`). -/
theorem path_unipotent_in_V {q : Work.EKLContract.SL3} {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hV : q ∈ Work.EKLContract.V c)
    (hnil : ((q : Matrix (Fin 3) (Fin 3) ℝ) - 1) ^ 3 = 0) :
    ∃ γ : ℝ → Work.EKLContract.SL3, Continuous γ ∧ γ 0 = 1 ∧ γ 1 = q ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1, γ s ∈ Work.EKLContract.V (4 * c) := by
  -- `N = q - 1` is nilpotent (`N³ = 0`) and its entries are `< c` in absolute value.
  set N : Matrix (Fin 3) (Fin 3) ℝ := (q : Matrix (Fin 3) (Fin 3) ℝ) - 1 with hN
  have hN3 : N ^ 3 = 0 := by rw [hN]; exact hnil
  have hNen : ∀ i j, |N i j| < c := by
    intro i j
    have h := hV i j
    rw [hN, Matrix.sub_apply]
    exact h
  -- the polynomial family interpolating between `1` and `q` (`= exp (s L)` for `L = log q`)
  let F : ℝ → Matrix (Fin 3) (Fin 3) ℝ := fun s => 1 + (s • N + ((s ^ 2 - s) / 2) • (N * N))
  have hF0 : F 0 = 1 := by simp [F]
  have hF1 : F 1 = (q : Matrix (Fin 3) (Fin 3) ℝ) := by
    simp only [F, one_pow, sub_self, zero_div, zero_smul, add_zero, one_smul]
    rw [hN]
    abel
  -- `det (F s) = 1` because `F s - 1 = s • N + ((s²-s)/2) • N²` has vanishing cube
  have hdet : ∀ s : ℝ, (F s).det = 1 :=
    fun s => det_one_add_of_cube_eq_zero _ (cube_smul_add_smul_sq_eq_zero N hN3 s ((s ^ 2 - s) / 2))
  have hcont : Continuous F := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    show Continuous fun s : ℝ => F s i j
    simp only [F, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    fun_prop
  refine ⟨fun s => ⟨F s, hdet s⟩, ?_, ?_, ?_, ?_⟩
  · exact hcont.subtype_mk _
  · ext i j
    show F 0 i j = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j
    rw [hF0]
  · ext i j
    show F 1 i j = (q : Matrix (Fin 3) (Fin 3) ℝ) i j
    rw [hF1]
  · intro s hs i j
    show |F s i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < 4 * c
    rw [show F s i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j
        = (s • N + ((s ^ 2 - s) / 2) • (N * N)) i j by
      simp only [F, Matrix.add_apply]; ring]
    exact unipotent_path_entry_bound hc hc1 hNen hs i j

end Work.EKLC6Core
