import Mathlib

/-!
# Solving `J v = R` for `J` close to an invertible operator, with a quantitative bound

This is the linear, quantitative "perturbed inverse" step used in the Volterra /
implicit-function long-time existence arguments: if `A : E ≃L[ℝ] E` is an
invertible continuous linear operator with `‖A.symm‖ ≤ B`, and `J` is a
continuous linear operator with `‖J - A‖ ≤ κ` where `B * κ ≤ 1 / 2`, then the
equation `J v = R` is solvable for every `R` close to a point `R₀ = A v₀` of the
range, with the explicit bound

  `‖v - v₀‖ ≤ 2 * B * (κ * ‖v₀‖ + δ)` whenever `‖R - R₀‖ ≤ δ`.

The solution is produced by a Neumann series: writing `C = A.symm`,
`K = C ∘ J` and `T = 1 - K = C ∘ (A - J)`, we have `‖T‖ ≤ ‖C‖ ‖A - J‖ ≤ B κ ≤ 1/2 < 1`,
so `K = 1 - T` is invertible with (two-sided) inverse `S = ∑' n, T ^ n` satisfying
`‖S‖ ≤ 2`.  The solution is `v = S (C R)`.
-/

namespace Work.VolterraLong.C1

theorem solve_near_equiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {A : E ≃L[ℝ] E} {J : E →L[ℝ] E} {B κ δ : ℝ} (hB : 0 < B)
    (hAinv : ‖((A.symm) : E →L[ℝ] E)‖ ≤ B) (hκ : ‖J - (A : E →L[ℝ] E)‖ ≤ κ)
    (hκB : B * κ ≤ 1 / 2) {R R₀ v₀ : E} (hv₀ : (A : E →L[ℝ] E) v₀ = R₀) (hδ : ‖R - R₀‖ ≤ δ) :
    ∃ v : E, J v = R ∧ ‖v - v₀‖ ≤ 2 * B * (κ * ‖v₀‖ + δ) := by
  -- `C` is the inverse of `A`, `K = C ∘ J`, `T = 1 - K = C ∘ (A - J)`, `S = ∑ Tⁿ`.
  set C : E →L[ℝ] E := (A.symm : E →L[ℝ] E) with hC
  set K : E →L[ℝ] E := C.comp J with hK
  set T : E →L[ℝ] E := 1 - K with hT
  set S : E →L[ℝ] E := ∑' n : ℕ, T ^ n with hS
  -- `T = C ∘ (A - J)`
  have hTeq : T = C.comp ((A : E →L[ℝ] E) - J) := by
    rw [hT, hK, hC]
    ext x
    simp
  have hCnorm : ‖C‖ ≤ B := by rw [hC]; exact hAinv
  -- `‖T‖ ≤ B * κ ≤ 1/2`
  have hTnorm : ‖T‖ ≤ 1 / 2 := by
    rw [hTeq]
    calc ‖C.comp ((A : E →L[ℝ] E) - J)‖ ≤ ‖C‖ * ‖(A : E →L[ℝ] E) - J‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖C‖ * ‖J - (A : E →L[ℝ] E)‖ := by rw [norm_sub_rev]
      _ ≤ B * κ := mul_le_mul hCnorm hκ (norm_nonneg _) (le_of_lt hB)
      _ ≤ 1 / 2 := hκB
  have hT1 : ‖T‖ < 1 := by linarith
  -- the Neumann series `S` is a two-sided inverse of `K = 1 - T`
  have hST : S * (1 - T) = 1 := by
    rw [hS]
    exact geom_series_mul_neg T hT1
  have hK_eq : K = 1 - T := by rw [hT, sub_sub_cancel]
  have hSK : S * K = 1 := by rw [hK_eq]; exact hST
  have hKS : K * S = 1 := by
    rw [hK_eq, hS]
    exact mul_neg_geom_series T hT1
  -- norm bound on the Neumann series
  have hSnorm : ‖S‖ ≤ 2 := by
    have h1 := tsum_geometric_le_of_norm_lt_one T hT1
    rw [← hS] at h1
    have h2 : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have h3 : (1 - ‖T‖)⁻¹ ≤ 2 := inv_le_of_inv_le₀ (by norm_num) (by linarith)
    linarith
  -- pointwise descriptions
  have hK_apply : ∀ x : E, K x = C (J x) := fun x => by rw [hK]; rfl
  have hA_apply : ∀ y : E, (A : E →L[ℝ] E) (C y) = y := fun y => by
    rw [hC]; exact ContinuousLinearEquiv.apply_symm_apply A y
  have hA_K : ∀ x : E, (A : E →L[ℝ] E) (K x) = J x := fun x => by
    rw [hK_apply x, hA_apply (J x)]
  -- the candidate solution `v = S (C R)` satisfies `K v = C R`
  have hKv : K (S (C R)) = C R := by
    have h1 : (K * S) (C R) = C R := by rw [hKS]; rfl
    rwa [mul_apply_eq_comp] at h1
  -- and `S (K v₀) = v₀`
  have hv0' : v₀ = S (K v₀) := by
    have h1 : (S * K) v₀ = v₀ := by rw [hSK]; rfl
    rw [mul_apply_eq_comp] at h1
    exact h1.symm
  refine ⟨S (C R), ?_, ?_⟩
  · rw [← hA_K (S (C R)), hKv, hA_apply R]
  · -- difference of the two arguments of `S`
    have hdiff : S (C R) - v₀ = S (C (R - J v₀)) := by
      have h1 : C R - K v₀ = C (R - J v₀) := by
        rw [hK_apply v₀, ← map_sub]
      conv_lhs => rw [hv0']
      rw [← map_sub, h1]
    have hR : R - J v₀ = (R - R₀) + ((A : E →L[ℝ] E) - J) v₀ := by
      rw [← hv₀, sub_apply]
      abel
    have h1 : ‖C (R - R₀)‖ ≤ B * δ := by
      calc ‖C (R - R₀)‖ ≤ ‖C‖ * ‖R - R₀‖ := ContinuousLinearMap.le_opNorm C _
        _ ≤ B * δ := mul_le_mul hCnorm hδ (norm_nonneg _) (le_of_lt hB)
    have h2 : ‖C (((A : E →L[ℝ] E) - J) v₀)‖ ≤ B * κ * ‖v₀‖ := by
      calc ‖C (((A : E →L[ℝ] E) - J) v₀)‖ ≤ ‖C‖ * ‖((A : E →L[ℝ] E) - J) v₀‖ :=
            ContinuousLinearMap.le_opNorm C _
        _ ≤ ‖C‖ * (‖(A : E →L[ℝ] E) - J‖ * ‖v₀‖) := by
              refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
              exact ContinuousLinearMap.le_opNorm ((A : E →L[ℝ] E) - J) v₀
        _ ≤ B * (κ * ‖v₀‖) := by
              refine mul_le_mul hCnorm ?_ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
                (le_of_lt hB)
              exact mul_le_mul_of_nonneg_right (by rw [norm_sub_rev]; exact hκ) (norm_nonneg _)
        _ = B * κ * ‖v₀‖ := by ring
    calc ‖S (C R) - v₀‖ = ‖S (C (R - J v₀))‖ := by rw [hdiff]
      _ = ‖S (C ((R - R₀) + ((A : E →L[ℝ] E) - J) v₀))‖ := by rw [hR]
      _ ≤ ‖S‖ * ‖C ((R - R₀) + ((A : E →L[ℝ] E) - J) v₀)‖ :=
            ContinuousLinearMap.le_opNorm S _
      _ ≤ ‖S‖ * (‖C (R - R₀)‖ + ‖C (((A : E →L[ℝ] E) - J) v₀)‖) := by
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            rw [map_add]
            exact norm_add_le _ _
      _ ≤ 2 * (B * δ + B * κ * ‖v₀‖) := by
            refine mul_le_mul hSnorm (add_le_add h1 h2) ?_ (by norm_num)
            exact add_nonneg (norm_nonneg _) (norm_nonneg _)
      _ = 2 * B * (κ * ‖v₀‖ + δ) := by ring

end Work.VolterraLong.C1
