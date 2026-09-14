import Mathlib
import Submission.Commons.GeometryOfNumbers.Box.rank_bound_small_body_complex

/-
# A "box gap" determinant lemma, weaker exponent hypothesis

This is the variant of `det_eq_zero_of_box_gap` in which the exponent hypothesis
is only one-sided (`γ i ≤ 1`) rather than two-sided (`|γ i| ≤ 1`).  Only the
upper bound is ever used, so the proof is the same, with the single line
`γ (σ lastidx) ≤ 1` now read off directly.

The proof uses the Leibniz formula: for each permutation the product of the
absolute values of the corresponding `N` entries is bounded by
`Qe^{∑γ - γ r} · Q^{γ r} = Qe^{∑γ} · (Q/Qe)^{γ r} ≤ Qe^{-ε/2}`; summing over the
`N!` permutations contradicts the strict lower bound `|det L| > N! Qe^{-ε/2}`
coming from integrality of the determinant of the integer matrix.
-/

namespace Commons.NumberTheory.DiophantineApproximation

open Finset Matrix
open scoped BigOperators

/-- A "box gap" determinant lemma, with the weaker exponent hypothesis `γ i ≤ 1`
(the existing `det_eq_zero_of_box_gap` assumes `|γ i| ≤ 1`, but only `γ i ≤ 1` is needed).
Given an invertible complex matrix `L`, exponents `γ i ≤ 1` with `∑ γ i ≤ -ε`, two scales
`1 ≤ Qe ≤ Q` with `Q ≤ Qe ^ (1 + ε/2)`, and `N` integer vectors (the `N-1` vectors `g` at the
smaller scale and `y` at the larger one), the matrix formed by these columns cannot have
nonzero determinant provided `N! < |det L| · Qe^{ε/2}`. -/
theorem det_eq_zero_of_box_gap_le {N : ℕ} (hN : 2 ≤ N)
    (L : Matrix (Fin N) (Fin N) ℂ) (hL : L.det ≠ 0)
    (γ : Fin N → ℝ) (hγ1 : ∀ i, γ i ≤ 1)
    (ε : ℝ) (hε : 0 < ε) (hsum : ∑ i, γ i ≤ -ε)
    (Qe Q : ℝ) (hQe1 : 1 ≤ Qe) (hQeQ : Qe ≤ Q) (hgap : Q ≤ Qe ^ (1 + ε / 2))
    (hbig : (Nat.factorial N : ℝ) < ‖L.det‖ * Qe ^ (ε / 2))
    (g : Fin (N - 1) → Fin N → ℤ) (y : Fin N → ℤ)
    (hg : ∀ j i, ‖∑ r, L i r * (g j r : ℂ)‖ ≤ Qe ^ (γ i))
    (hy : ∀ i, ‖∑ r, L i r * (y r : ℂ)‖ ≤ Q ^ (γ i))
    (hdet : (Matrix.of (fun i j : Fin N =>
      if h : (j : ℕ) < N - 1 then (g ⟨j, h⟩ i : ℤ) else y i)).det ≠ 0) : False := by
  classical
  have hLpos : 0 < ‖L.det‖ := norm_pos_iff.mpr hL
  have hε2 : 0 < ε / 2 := by positivity
  -- The integer matrix whose columns are `g 0, …, g (N-2), y`.
  set Mz : Matrix (Fin N) (Fin N) ℤ := Matrix.of (fun i j : Fin N =>
      if h : (j : ℕ) < N - 1 then g ⟨j, h⟩ i else y i) with hMz
  have hMzdet : Mz.det ≠ 0 := by simpa only [hMz] using hdet
  -- Its complexification.
  set G : Matrix (Fin N) (Fin N) ℂ := (Int.castRingHom ℂ).mapMatrix Mz with hG
  have hG_apply : ∀ i j, G i j = (Mz i j : ℂ) := by
    intro i j; rw [hG, RingHom.mapMatrix_apply, Matrix.map_apply]; rfl
  have hGdet : G.det = (Mz.det : ℂ) := by
    rw [hG]; exact (RingHom.map_det (Int.castRingHom ℂ) Mz).symm
  have hGge : 1 ≤ ‖G.det‖ := by
    rw [hGdet, Complex.norm_intCast, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hMzdet
  set U : Matrix (Fin N) (Fin N) ℂ := L * G with hU
  have hUdet : U.det = L.det * G.det := by rw [hU, Matrix.det_mul]
  -- Lower bound: `|det L| ≤ |det U|` because `det G` is a nonzero integer.
  have hlower : ‖L.det‖ ≤ ‖U.det‖ := by
    rw [hUdet, norm_mul]
    calc ‖L.det‖ = ‖L.det‖ * 1 := (mul_one _).symm
      _ ≤ ‖L.det‖ * ‖G.det‖ := mul_le_mul_of_nonneg_left hGge (norm_nonneg _)
  -- Positivity / scale facts.
  have hQepos : 0 < Qe := lt_of_lt_of_le one_pos hQe1
  have hQpos : 0 < Q := lt_of_lt_of_le hQepos hQeQ
  set t : ℝ := Q / Qe with ht
  have ht_nonneg : 0 ≤ t := by rw [ht]; positivity
  have ht_ge1 : 1 ≤ t := by
    rw [ht, le_div_iff₀ hQepos]; linarith
  have htQ : Qe * t = Q := by rw [ht]; exact mul_div_cancel₀ _ hQepos.ne'
  have ht_le : t ≤ Qe ^ (ε / 2) := by
    rw [ht, div_le_iff₀ hQepos]
    have h1 : Qe ^ (1 + ε / 2) = Qe * Qe ^ (ε / 2) := by
      rw [Real.rpow_add hQepos, Real.rpow_one]
    rw [h1] at hgap
    linarith
  -- Entrywise description of `U`.
  have hU_apply : ∀ i j, U i j = ∑ r, L i r * (Mz r j : ℂ) := by
    intro i j
    rw [hU, Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [hG_apply]
  -- The last index; it is the column occupied by `y`.
  let lastidx : Fin N := ⟨N - 1, by omega⟩
  have hbound_small : ∀ i (j : Fin N), (j : ℕ) < N - 1 → ‖U i j‖ ≤ Qe ^ (γ i) := by
    intro i j hj
    have hsum_eq : U i j = ∑ r, L i r * (g ⟨j, hj⟩ r : ℂ) := by
      rw [hU_apply]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      congr 1
      simp only [hMz, Matrix.of_apply, dif_pos hj]
    rw [hsum_eq]
    exact hg ⟨j, hj⟩ i
  have hbound_big : ∀ i (j : Fin N), ¬ ((j : ℕ) < N - 1) → ‖U i j‖ ≤ Q ^ (γ i) := by
    intro i j hj
    have hsum_eq : U i j = ∑ r, L i r * (y r : ℂ) := by
      rw [hU_apply]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      congr 1
      simp only [hMz, Matrix.of_apply, dif_neg hj]
    rw [hsum_eq]
    exact hy i
  -- Uniform bound for the Leibniz terms.
  have hterm : ∀ σ : Equiv.Perm (Fin N), ∏ i, ‖U (σ i) i‖ ≤ Qe ^ (-ε) * t := by
    intro σ
    rw [← Finset.prod_erase_mul Finset.univ (fun i => ‖U (σ i) i‖) (Finset.mem_univ lastidx)]
    have hpe : ∏ i ∈ Finset.univ.erase lastidx, ‖U (σ i) i‖ ≤
        ∏ i ∈ Finset.univ.erase lastidx, Qe ^ (γ (σ i)) := by
      refine Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i hi => ?_)
      have hne : i ≠ lastidx := (Finset.mem_erase.mp hi).1
      have hlt : (i : ℕ) < N - 1 := by
        have h1 : (i : ℕ) ≠ N - 1 := fun h => hne (Fin.ext h)
        have h2 := i.isLt
        omega
      exact hbound_small (σ i) i hlt
    have hpc : ‖U (σ lastidx) lastidx‖ ≤ Q ^ (γ (σ lastidx)) :=
      hbound_big (σ lastidx) lastidx (by simp [lastidx])
    have hprod_eq : ∏ i ∈ Finset.univ.erase lastidx, Qe ^ (γ (σ i))
        = Qe ^ (∑ i ∈ Finset.univ.erase lastidx, γ (σ i)) :=
      (Real.rpow_sum_of_pos hQepos (fun i => γ (σ i)) _).symm
    have hsum_decomp : (∑ i ∈ Finset.univ.erase lastidx, γ (σ i))
        = (∑ i, γ i) - γ (σ lastidx) := by
      have h1 : (∑ i ∈ Finset.univ.erase lastidx, γ (σ i)) + γ (σ lastidx) = ∑ i, γ i := by
        rw [Finset.sum_erase_add _ _ (Finset.mem_univ lastidx)]
        exact Equiv.sum_comp σ γ
      linarith
    have hbnd : (∏ i ∈ Finset.univ.erase lastidx, Qe ^ (γ (σ i))) * Q ^ (γ (σ lastidx))
        ≤ Qe ^ (-ε) * t := by
      rw [hprod_eq, hsum_decomp]
      have hstep : Qe ^ ((∑ i, γ i) - γ (σ lastidx)) * Q ^ (γ (σ lastidx))
          = Qe ^ (∑ i, γ i) * t ^ (γ (σ lastidx)) := by
        rw [← htQ, Real.mul_rpow (le_of_lt hQepos) ht_nonneg, ← mul_assoc,
            ← Real.rpow_add hQepos,
            show ((∑ i, γ i) - γ (σ lastidx)) + γ (σ lastidx) = ∑ i, γ i by ring]
      rw [hstep]
      refine mul_le_mul ?_ ?_ (Real.rpow_nonneg ht_nonneg _)
        (Real.rpow_nonneg (le_of_lt hQepos) _)
      · exact Real.rpow_le_rpow_of_exponent_le hQe1 hsum
      · -- here only the one-sided bound is needed
        have hg1 : γ (σ lastidx) ≤ 1 := hγ1 _
        have hh := Real.rpow_le_rpow_of_exponent_le ht_ge1 hg1
        rwa [Real.rpow_one] at hh
    calc (∏ i ∈ Finset.univ.erase lastidx, ‖U (σ i) i‖) * ‖U (σ lastidx) lastidx‖
        ≤ (∏ i ∈ Finset.univ.erase lastidx, Qe ^ (γ (σ i))) * Q ^ (γ (σ lastidx)) :=
          mul_le_mul hpe hpc (norm_nonneg _)
            (Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (le_of_lt hQepos) _))
      _ ≤ Qe ^ (-ε) * t := hbnd
  -- The Hadamard/Leibniz bound.
  have hhigh1 : ∑ σ : Equiv.Perm (Fin N), ∏ i, ‖U (σ i) i‖
      ≤ (Nat.factorial N : ℝ) * (Qe ^ (-ε) * t) := by
    calc ∑ σ : Equiv.Perm (Fin N), ∏ i, ‖U (σ i) i‖
        ≤ ∑ _σ : Equiv.Perm (Fin N), (Qe ^ (-ε) * t) :=
          Finset.sum_le_sum (fun σ _ => hterm σ)
      _ = (Fintype.card (Equiv.Perm (Fin N)) : ℝ) * (Qe ^ (-ε) * t) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (Nat.factorial N : ℝ) * (Qe ^ (-ε) * t) := by
          rw [Fintype.card_perm, Fintype.card_fin]
  have hhigh : ‖U.det‖ ≤ (Nat.factorial N : ℝ) * Qe ^ (-(ε / 2)) := by
    refine (Commons.GeometryOfNumbers.Box.det_norm_le_sum U).trans (hhigh1.trans ?_)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0:ℝ) ≤ (Nat.factorial N : ℝ))
    calc Qe ^ (-ε) * t ≤ Qe ^ (-ε) * Qe ^ (ε / 2) :=
          mul_le_mul_of_nonneg_left ht_le (Real.rpow_nonneg (le_of_lt hQepos) _)
      _ = Qe ^ (-(ε / 2)) := by
          rw [← Real.rpow_add hQepos, show -ε + ε / 2 = -(ε / 2) by ring]
  -- Combine with `hbig` and contradict.
  have hbig' : (Nat.factorial N : ℝ) * Qe ^ (-(ε / 2)) < ‖L.det‖ := by
    have hpos : 0 < Qe ^ (-(ε / 2)) := Real.rpow_pos_of_pos hQepos _
    have h2 : (‖L.det‖ * Qe ^ (ε / 2)) * Qe ^ (-(ε / 2)) = ‖L.det‖ := by
      rw [mul_assoc, ← Real.rpow_add hQepos,
          show ε / 2 + -(ε / 2) = 0 by ring, Real.rpow_zero, mul_one]
    have := mul_lt_mul_of_pos_right hbig hpos
    rwa [h2] at this
  exact absurd (lt_of_lt_of_le (lt_of_le_of_lt hhigh hbig') hlower) (lt_irrefl _)

end Commons.NumberTheory.DiophantineApproximation
