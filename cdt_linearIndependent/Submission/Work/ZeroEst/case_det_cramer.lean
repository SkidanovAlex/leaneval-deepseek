import Mathlib

namespace Work.ZeroEst

/-- **Cramer's rule (matrix form).**  For a square matrix `N` over a commutative ring and any
vector `f`, the `j`-th coordinate of `det N • f` is the `j`-th row of `N.adjugate` applied to
`N *ᵥ f`.  This is the identity `N.adjugate * N = det N • 1` applied to `f`. -/
theorem cramer_aux {R : Type*} [CommRing R] {m : ℕ} (N : Matrix (Fin m) (Fin m) R)
    (f : Fin m → R) (j : Fin m) :
    N.det * f j = ∑ k, N.adjugate j k * (∑ j', N k j' * f j') := by
  rw [eq_comm]
  calc ∑ k, N.adjugate j k * (∑ j', N k j' * f j')
      = ∑ k, ∑ j', N.adjugate j k * (N k j' * f j') := by
          simp only [Finset.mul_sum]
      _ = ∑ j', ∑ k, N.adjugate j k * (N k j' * f j') := by
          rw [Finset.sum_comm]
      _ = ∑ j', (∑ k, N.adjugate j k * N k j') * f j' := by
          congr 1 with j'
          rw [Finset.sum_mul]
          congr 1 with k
          ring
      _ = ∑ j', (N.adjugate * N) j j' * f j' := by
          simp only [Matrix.mul_apply]
      _ = ∑ j', (N.det • (1 : Matrix (Fin m) (Fin m) R)) j j' * f j' := by
          rw [Matrix.adjugate_mul]
      _ = N.det * f j := by
          rw [Finset.sum_eq_single j]
          · simp [Matrix.smul_apply]
          · intro b _ hb
            simp [Matrix.smul_apply, Matrix.one_apply_ne (Ne.symm hb)]
          · intro h
            exact absurd (Finset.mem_univ j) h

/-- Cramer's rule, transported from `Polynomial ℚ` to `PowerSeries ℚ` along the coefficient
embedding: `det M · f j = ∑_k (M.adjugate) j k · (∑_j' M k j' · f j')`. -/
theorem case_det_cramer {m : ℕ} (M : Matrix (Fin m) (Fin m) (Polynomial ℚ))
    (f : Fin m → PowerSeries ℚ) (j : Fin m) :
    (M.det : PowerSeries ℚ) * f j
      = ∑ k : Fin m, (M.adjugate j k : PowerSeries ℚ)
          * (∑ j' : Fin m, (M k j' : PowerSeries ℚ) * f j') := by
  have hmain := cramer_aux (M.map (fun p => (p : PowerSeries ℚ))) f j
  have hdet : (M.map (fun p => (p : PowerSeries ℚ))).det = (M.det : PowerSeries ℚ) :=
    (RingHom.map_det (algebraMap (Polynomial ℚ) (PowerSeries ℚ)) M).symm
  have hadj : ∀ k : Fin m,
      (M.map (fun p => (p : PowerSeries ℚ))).adjugate j k = (M.adjugate j k : PowerSeries ℚ) := by
    intro k
    exact (congr_fun (congr_fun
      (RingHom.map_adjugate (algebraMap (Polynomial ℚ) (PowerSeries ℚ)) M) j) k).symm
  rw [← hdet, hmain]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [hadj k]
  rfl

end Work.ZeroEst
