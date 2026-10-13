import Mathlib

namespace Work.WilG4c

/-- The continuous linear map `(Fin N → ℝ) →L[ℝ] F` determined by prescribed values on the
standard basis vectors `Pi.single j 1`.  Since `Fin N → ℝ` is finite dimensional, the
operator norm of such a map is controlled by its values on the basis, so this construction
turns coordinatewise data into a genuine continuous linear map. -/
noncomputable def coordCLM {N : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (s : Fin N → F) : (Fin N → ℝ) →L[ℝ] F :=
  ∑ j, (ContinuousLinearMap.proj j).smulRight (s j)

lemma coordCLM_apply {N : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (s : Fin N → F) (x : Fin N → ℝ) : coordCLM s x = ∑ j, x j • s j := by
  simp only [coordCLM, sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply]

lemma coordCLM_apply_basis {N : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (s : Fin N → F) (i : Fin N) : coordCLM s (Pi.single i 1) = s i := by
  rw [coordCLM_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-- Every element of `Fin N → ℝ` is the sum of its coordinates against the standard basis. -/
lemma sum_smul_single {N : ℕ} (x : Fin N → ℝ) :
    (∑ j, x j • Pi.single j 1) = x := by
  funext k
  simp [Pi.single_apply]

/-- Norm bound: a continuous linear map out of `Fin N → ℝ` is controlled by its values on
the standard basis vectors. -/
lemma norm_le_sum_norm_apply_single {N : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : (Fin N → ℝ) →L[ℝ] F) : ‖T‖ ≤ ∑ j : Fin N, ‖T (Pi.single j 1)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact Finset.sum_nonneg (fun j _ => norm_nonneg _)
  · intro x
    calc ‖T x‖ = ‖T (∑ j, x j • Pi.single j 1)‖ := by rw [sum_smul_single]
      _ = ‖∑ j, x j • T (Pi.single j 1)‖ := by rw [map_sum]; simp [map_smul]
      _ ≤ ∑ j, ‖x j • T (Pi.single j 1)‖ := norm_sum_le _ _
      _ = ∑ j, ‖x j‖ * ‖T (Pi.single j 1)‖ := by simp [norm_smul]
      _ ≤ ∑ j, ‖x‖ * ‖T (Pi.single j 1)‖ :=
          Finset.sum_le_sum (fun j _ =>
            mul_le_mul_of_nonneg_right (norm_le_pi_norm x j) (norm_nonneg _))
      _ = ‖x‖ * ∑ j, ‖T (Pi.single j 1)‖ := by rw [Finset.mul_sum]
      _ = (∑ j, ‖T (Pi.single j 1)‖) * ‖x‖ := by rw [mul_comm]

theorem ExistsClmTendstoFderivOfCoord {N : ℕ} (hN : 1 ≤ N) {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : (Fin N → ℝ) → F} {u : Fin N → ℝ}
    (h : ∀ j : Fin N, ∃ s : F,
      Filter.Tendsto (fun x => fderiv ℝ g x (Pi.single j 1)) (nhdsWithin u {u}ᶜ) (nhds s)) :
    ∃ L : (Fin N → ℝ) →L[ℝ] F,
      Filter.Tendsto (fun x => fderiv ℝ g x) (nhdsWithin u {u}ᶜ) (nhds L) ∧
        ∀ j : Fin N, Filter.Tendsto (fun x => fderiv ℝ g x (Pi.single j 1))
          (nhdsWithin u {u}ᶜ) (nhds (L (Pi.single j 1))) := by
  classical
  choose s hs using h
  refine ⟨coordCLM s, ?_, ?_⟩
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have hcoord : ∀ j : Fin N, Filter.Tendsto
        (fun x => ‖(fderiv ℝ g x - coordCLM s) (Pi.single j 1)‖)
        (nhdsWithin u {u}ᶜ) (nhds 0) := by
      intro j
      have h1 : Filter.Tendsto (fun x => fderiv ℝ g x (Pi.single j 1) - s j)
          (nhdsWithin u {u}ᶜ) (nhds 0) := by
        simpa using (hs j).sub_const (s j)
      have h2 : Filter.Tendsto (fun x => ‖fderiv ℝ g x (Pi.single j 1) - s j‖)
          (nhdsWithin u {u}ᶜ) (nhds 0) := by
        simpa using h1.norm
      simpa [sub_apply, coordCLM_apply_basis s j] using h2
    have hsum : Filter.Tendsto
        (fun x => ∑ j, ‖(fderiv ℝ g x - coordCLM s) (Pi.single j 1)‖)
        (nhdsWithin u {u}ᶜ) (nhds 0) := by
      simpa using tendsto_finsetSum Finset.univ (fun j _ => hcoord j)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun x => norm_nonneg _) (fun x => norm_le_sum_norm_apply_single _)
  · intro j
    rw [coordCLM_apply_basis s j]
    exact hs j

end Work.WilG4c
