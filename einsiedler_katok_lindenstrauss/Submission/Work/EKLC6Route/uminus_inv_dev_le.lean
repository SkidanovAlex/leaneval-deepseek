import Mathlib
import Submission.Work.EKLC6Route.Defs
import Submission.Work.EKLC6Core.contraction_rate_uminus

/-!
# `EKLC6Route.uminus_inv_dev_le`

The defect seminorm `dev g = max_{i,j} |gᵢⱼ - δᵢⱼ|` of an element `u` of the contracted
horospherical subgroup `Uminus t = G⁻(t) ⊆ SL₃(ℝ)` controls the defect of the inverse:

`dev u⁻¹ ≤ dev u + 3 · (dev u)²`.

## Mathematics

`Work.EKLC6Core.uminus_entry_facts` says that for `u ∈ Uminus t` the diagonal entries are `1`
and the `(i,j)`-entry vanishes whenever `t j ≤ t i` (`i ≠ j`).  Hence `N := u - 1` satisfies

`N i j ≠ 0 → t i < t j`,  `(*)`

i.e. a non-zero entry of `N` strictly increases the level `t`.  Writing `u = 1 + N`, the identity

`(1 + N) * (1 - N + N²) = 1 + N³`

(in the non-commutative ring of matrices) together with `N³ = 0` shows `u⁻¹ = 1 - N + N²`.
The nilpotency `N³ = 0` is exactly `(*)`: a non-zero product `N i j * N j k * N k l` would
produce four indices with `t i < t j < t k < t l`, which is impossible in `Fin 3`
(`no_four_strict_levels`); see `cube_eq_zero_of_strict_levels`.

Finally `u⁻¹ - 1 = -N + N²` so entrywise
`|(u⁻¹)ᵢⱼ - δᵢⱼ| ≤ |Nᵢⱼ| + |(N²)ᵢⱼ| ≤ dev u + 3 (dev u)²`
(the entries of `N²` are sums of three products of entries of `N`).
-/

namespace Work.EKLC6Route

open Matrix

/-- There is no strictly increasing chain of four `t`-levels inside `Fin 3`. -/
lemma no_four_strict_levels {t : Fin 3 → ℝ} :
    ¬ ∃ i j k l : Fin 3, t i < t j ∧ t j < t k ∧ t k < t l := by
  rintro ⟨i, j, k, l, h1, h2, h3⟩
  have hinj : Function.Injective ![i, j, k, l] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all <;> linarith
  have hcard := Fintype.card_le_of_injective _ hinj
  simp at hcard

/-- A product of three factors of a matrix whose non-zero entries strictly increase the level
`t` vanishes: it would exhibit four strictly increasing `t`-levels. -/
lemma prod_three_eq_zero_of_strict_levels {t : Fin 3 → ℝ} {N : Matrix (Fin 3) (Fin 3) ℝ}
    (hN : ∀ i j, N i j ≠ 0 → t i < t j) (i j k l : Fin 3) : N i j * N j k * N k l = 0 := by
  by_contra h
  have h' : N i j * N j k * N k l ≠ 0 := h
  rw [mul_ne_zero_iff] at h'
  obtain ⟨hijk, hkl⟩ := h'
  rw [mul_ne_zero_iff] at hijk
  obtain ⟨hij, hjk⟩ := hijk
  exact no_four_strict_levels (t := t) ⟨i, j, k, l, hN i j hij, hN j k hjk, hN k l hkl⟩

/-- `N³ = 0` for a matrix whose non-zero entries strictly increase the level `t`
(already true on `Fin 3`). -/
lemma cube_eq_zero_of_strict_levels {t : Fin 3 → ℝ} {N : Matrix (Fin 3) (Fin 3) ℝ}
    (hN : ∀ i j, N i j ≠ 0 → t i < t j) : N * N * N = 0 := by
  ext i l
  rw [Matrix.mul_apply]
  have hstep : ∀ j : Fin 3, (N * N) i j * N j l = 0 := by
    intro j
    rw [Matrix.mul_apply]
    rw [Finset.sum_mul]
    exact Finset.sum_eq_zero (fun k _ => prod_three_eq_zero_of_strict_levels hN i k j l)
  rw [Finset.sum_eq_zero (fun j _ => hstep j), Matrix.zero_apply]

theorem uminus_inv_dev_le {t : Fin 3 → ℝ} {u : Work.EKLContract.SL3}
    (hu : u ∈ Work.EKLC6Core.Uminus t) :
    Work.EKLC6Route.dev u⁻¹ ≤ Work.EKLC6Route.dev u + 3 * Work.EKLC6Route.dev u ^ 2 := by
  -- diagonal entries are `1` and `(i,j)`-entries with `t j ≤ t i` vanish, for `u ∈ Uminus t`
  obtain ⟨hdiag, hzero⟩ := Work.EKLC6Core.uminus_entry_facts t hu
  set M : Matrix (Fin 3) (Fin 3) ℝ := (u : Matrix (Fin 3) (Fin 3) ℝ) with hM
  set N : Matrix (Fin 3) (Fin 3) ℝ := M - 1 with hN
  -- non-zero entries of `N = u - 1` strictly increase the level `t`
  have hNt : ∀ i j, N i j ≠ 0 → t i < t j := by
    intro i j hij
    by_contra hle
    rw [not_lt] at hle
    have hz : N i j = 0 := by
      rw [hN, Matrix.sub_apply]
      by_cases h : i = j
      · subst h; rw [hdiag i, Matrix.one_apply_eq]; ring
      · rw [hzero i j h hle, Matrix.one_apply_ne h]; ring
    exact hij hz
  have hcube : N * N * N = 0 := cube_eq_zero_of_strict_levels hNt
  have hMu : M = 1 + N := by
    rw [hN, hM]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply]
    ring
  -- `(1 + N) * (1 - N + N²) = 1`
  have hprod : M * (1 - N + N * N) = 1 := by
    rw [hMu]
    have h1 : (1 + N) * (1 - N + N * N) = 1 + N * N * N := by noncomm_ring
    rw [h1, hcube, add_zero]
  -- the matrix `1 - N + N²` has determinant `1`, so it is an element `w` of `SL₃(ℝ)`
  have hdet : (1 - N + N * N : Matrix (Fin 3) (Fin 3) ℝ).det = 1 := by
    have h1 : M.det * (1 - N + N * N).det = 1 := by
      rw [← Matrix.det_mul, hprod, Matrix.det_one]
    rw [hM, Matrix.SpecialLinearGroup.det_coe, one_mul] at h1
    exact h1
  set w : Work.EKLContract.SL3 := ⟨1 - N + N * N, hdet⟩ with hw
  have hwco : (w : Matrix (Fin 3) (Fin 3) ℝ) = 1 - N + N * N := by rw [hw]
  have huw : u * w = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, hwco, ← hM]
    exact hprod
  have hwinv : u⁻¹ = w := inv_eq_of_mul_eq_one_right huw
  rw [hwinv]
  -- entrywise bounds against `dev u`
  have hle : ∀ i j : Fin 3, |N i j| ≤ dev u := by
    intro i j
    have hNij : |N i j| = |(u : Matrix (Fin 3) (Fin 3) ℝ) i j -
        (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := by
      rw [hN, Matrix.sub_apply, hM]
    rw [hNij]
    exact Finset.le_sup' (s := (Finset.univ : Finset (Fin 3 × Fin 3)))
      (fun p : Fin 3 × Fin 3 => |(u : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2 -
        (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|) (Finset.mem_univ (i, j))
  have hd0 : 0 ≤ dev u := le_trans (abs_nonneg (N 0 0)) (hle 0 0)
  have hentry : ∀ i j : Fin 3,
      |(w : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤
        dev u + 3 * dev u ^ 2 := by
    intro i j
    -- `|(N²)ᵢⱼ| ≤ 3 (dev u)²`
    have hNN : |(N * N) i j| ≤ 3 * dev u * dev u := by
      rw [Matrix.mul_apply]
      calc |∑ k, N i k * N k j| ≤ ∑ k, |N i k * N k j| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k, |N i k| * |N k j| := by simp [abs_mul]
        _ ≤ ∑ _k : Fin 3, dev u * dev u := by
              apply Finset.sum_le_sum
              intro k _
              exact mul_le_mul (hle i k) (hle k j) (abs_nonneg _) hd0
        _ = 3 * dev u * dev u := by rw [Fin.sum_univ_three]; ring
    rw [hwco, Matrix.add_apply, Matrix.sub_apply]
    have harith : (1 : Matrix (Fin 3) (Fin 3) ℝ) i j - N i j + (N * N) i j -
        (1 : Matrix (Fin 3) (Fin 3) ℝ) i j = -(N i j) + (N * N) i j := by ring
    rw [harith]
    calc |-(N i j) + (N * N) i j| ≤ |-(N i j)| + |(N * N) i j| := abs_add_le _ _
      _ = |N i j| + |(N * N) i j| := by rw [abs_neg]
      _ ≤ dev u + 3 * dev u * dev u := add_le_add (hle i j) hNN
      _ = dev u + 3 * dev u ^ 2 := by ring
  refine Finset.sup'_le _ _ ?_
  intro p _
  exact hentry p.1 p.2

end Work.EKLC6Route
