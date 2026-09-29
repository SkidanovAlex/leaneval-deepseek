import Mathlib
import Submission.Work.ResMath.resamplingAux
import Submission.Work.ResMath.resamplingAssembly
import Submission.Work.ResMath.resamplingAssembly2

/-!
# Assembly: `P_t F_t S` computed
-/

namespace Work.ResMath

open HvdH

lemma summable_gauss_FsZ_1 (s α : ℕ) (hs : 0 < s) (hα : 0 < α) (u : Fin s → ℂ) :
    Summable (fun m : ℤ => Gz s α m * FsZ s u m) := by
  refine (summable_gauss_FsZ s 1 α hs one_pos hα u 0).congr fun m => ?_
  have h1 : (Real.exp (-Real.pi * (α : ℝ) ^ 2 * (((1 : ℕ) : ℝ)) ^ 2 * (0 - (m : ℝ) / (s : ℝ)) ^ 2) : ℂ)
      = Gz s α m := by
    have harg : -Real.pi * (α : ℝ) ^ 2 * (((1 : ℕ) : ℝ)) ^ 2 * (0 - (m : ℝ) / (s : ℝ)) ^ 2
        = -Real.pi * (α : ℝ) ^ 2 * (m : ℝ) ^ 2 / (s : ℝ) ^ 2 := by
      rw [Nat.cast_one, one_pow, mul_one, zero_sub, neg_sq, div_pow]
      ring
    rw [harg, Gz]
  have h2 : FsZ s u (((1 : ℕ) : ℤ) * m) = FsZ s u m := by rw [Nat.cast_one, one_mul]
  rw [h1, h2]

lemma summable_resS_term (s t α : ℕ) (hs : 0 < s) (hα : 0 < α) (u : Fin s → ℂ) (l : Fin t) (c : ℂ) :
    Summable (fun m : ℤ =>
      Gz s α m * Phz t (m : ℂ) (l : ℕ) * FsZ s u m * c) := by
  refine Summable.of_norm_bounded
    (g := fun m : ℤ => ‖Gz s α m * FsZ s u m‖ * ‖c‖)
    (((summable_gauss_FsZ_1 s α hs hα u).norm).mul_right ‖c‖) ?_
  intro m
  have h1 : ‖Phz t (m : ℂ) (l : ℕ)‖ = 1 := by
    simp only [Phz]
    rw [Complex.norm_exp]
    have hlt : ((l : ℂ) / (t : ℂ)) = Complex.ofReal (((l : ℕ) : ℝ) / (t : ℝ)) := by
      rw [Complex.ofReal_div]
      push_cast
      ring
    have hre : (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * ((l : ℂ) / (t : ℂ))).re = 0 := by
      rw [hlt]
      rw [show 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * Complex.ofReal (((l : ℕ) : ℝ) / (t : ℝ))
          = Complex.ofReal (2 * Real.pi * (m : ℝ) * (((l : ℕ) : ℝ) / (t : ℝ))) * Complex.I from by
        push_cast; ring,
        Complex.mul_I_re, Complex.ofReal_im, neg_zero]
    rw [hre, Real.exp_zero]
  simp only [norm_mul, h1, mul_one]
  exact le_refl _

/-- The sum over `l` of the Poisson-expanded rows, with the permutation phase. -/
lemma resS_expand_sum (s t α : ℕ) (hs : 0 < s) (ht : 0 < t) (hα : 0 < α) (u : Fin s → ℂ) (k : Fin t) :
    (1 / (t : ℂ)) * (∑ l : Fin t,
        (∑' m : ℤ, (Real.exp (-Real.pi * (α : ℝ) ^ 2 * (m : ℝ) ^ 2 / (s : ℝ) ^ 2) : ℂ) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * ((l : ℂ) / (t : ℂ))) * FsZ s u m) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((s : ℂ) * (k : ℂ)) * ((l : ℂ) / (t : ℂ))))
      = ∑' m : ℤ, (if (t : ℤ) ∣ (m + (s : ℤ) * (k : ℤ)) then
          (Real.exp (-Real.pi * (α : ℝ) ^ 2 * (m : ℝ) ^ 2 / (s : ℝ) ^ 2) : ℂ) * FsZ s u m else 0) := by
  change (1 / (t : ℂ)) * (∑ l : Fin t,
        (∑' m : ℤ, Gz s α m * Phz t (m : ℂ) (l : ℕ) * FsZ s u m) *
        Phz t ((s : ℂ) * (k : ℂ)) (l : ℕ))
      = ∑' m : ℤ, (if (t : ℤ) ∣ (m + (s : ℤ) * (k : ℤ)) then Gz s α m * FsZ s u m else 0)
  have htne : ((t : ℂ)) ≠ 0 := by simp [ht.ne']
  have h1 : (∑ l : Fin t, (∑' m : ℤ, Gz s α m * Phz t (m : ℂ) (l : ℕ) * FsZ s u m) *
        Phz t ((s : ℂ) * (k : ℂ)) (l : ℕ))
      = ∑' m : ℤ, ∑ l : Fin t, (Gz s α m * Phz t (m : ℂ) (l : ℕ) * FsZ s u m) *
          Phz t ((s : ℂ) * (k : ℂ)) (l : ℕ) := by
    have ha : (∑ l : Fin t, (∑' m : ℤ, Gz s α m * Phz t (m : ℂ) (l : ℕ) * FsZ s u m) *
          Phz t ((s : ℂ) * (k : ℂ)) (l : ℕ))
        = ∑ l : Fin t, ∑' m : ℤ, (Gz s α m * Phz t (m : ℂ) (l : ℕ) * FsZ s u m) *
            Phz t ((s : ℂ) * (k : ℂ)) (l : ℕ) :=
      Finset.sum_congr rfl fun (l : Fin t) _ => (tsum_mul_right).symm
    rw [ha]
    exact (Summable.tsum_finsetSum (s := Finset.univ)
      (f := fun (l : Fin t) (m : ℤ) => (Gz s α m * Phz t (m : ℂ) (l : ℕ) * FsZ s u m) *
          Phz t ((s : ℂ) * (k : ℂ)) (l : ℕ))
      (fun (l : Fin t) _ => summable_resS_term s t α hs hα u l (Phz t ((s : ℂ) * (k : ℂ)) (l : ℕ)))).symm
  rw [h1, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  have hA : (∑ l : Fin t, (Gz s α m * Phz t (m : ℂ) (l : ℕ) * FsZ s u m) *
        Phz t ((s : ℂ) * (k : ℂ)) (l : ℕ))
      = (Gz s α m * FsZ s u m) * ∑ l : Fin t, Phz t (((m + (s : ℤ) * (k : ℤ)) : ℤ) : ℂ) (l : ℕ) := by
    have hAa : (∑ l : Fin t, (Gz s α m * Phz t (m : ℂ) (l : ℕ) * FsZ s u m) *
          Phz t ((s : ℂ) * (k : ℂ)) (l : ℕ))
        = ∑ l : Fin t, (Gz s α m * FsZ s u m) *
            (Phz t (m : ℂ) (l : ℕ) * Phz t ((s : ℂ) * (k : ℂ)) (l : ℕ)) :=
      Finset.sum_congr rfl fun l _ => by ring
    have hAb : (∑ l : Fin t, (Gz s α m * FsZ s u m) *
            (Phz t (m : ℂ) (l : ℕ) * Phz t ((s : ℂ) * (k : ℂ)) (l : ℕ)))
        = (Gz s α m * FsZ s u m) *
            ∑ l : Fin t, (Phz t (m : ℂ) (l : ℕ) * Phz t ((s : ℂ) * (k : ℂ)) (l : ℕ)) :=
      (Finset.mul_sum _ _ _).symm
    have hAc : (∑ l : Fin t, (Phz t (m : ℂ) (l : ℕ) * Phz t ((s : ℂ) * (k : ℂ)) (l : ℕ)))
        = ∑ l : Fin t, Phz t (((m + (s : ℤ) * (k : ℤ)) : ℤ) : ℂ) (l : ℕ) := by
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [Phz]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hAa, hAb, hAc]
  rw [hA, rootUnitySum_phz t ht (m + (s : ℤ) * (k : ℤ))]
  exact inv_mul_ite (t : ℂ) htne _ _

/-- The coset sum as a Gaussian sum. -/
lemma coset_to_gauss (s t α : ℕ) (hs : 0 < s) (ht : 0 < t) (hα : 0 < α) (u : Fin s → ℂ) (k : Fin t) :
    (∑' m : ℤ, (if (t : ℤ) ∣ (m + (s : ℤ) * (k : ℤ)) then
        (Real.exp (-Real.pi * (α : ℝ) ^ 2 * (m : ℝ) ^ 2 / (s : ℝ) ^ 2) : ℂ) * FsZ s u m else 0))
      = ∑' j : ℤ, (Real.exp (-Real.pi * (α : ℝ) ^ 2 * (t : ℝ) ^ 2 *
          ((k : ℝ) / (t : ℝ) - (j : ℝ) / (s : ℝ)) ^ 2) : ℂ) * FsZ s u (t * j) := by
  change (∑' m : ℤ, (if (t : ℤ) ∣ (m + (s : ℤ) * (k : ℤ)) then Gz s α m * FsZ s u m else 0))
      = ∑' j : ℤ, Gzk s t α (k : ℕ) j * FsZ s u (t * j)
  rw [show (∑' m : ℤ, (if (t : ℤ) ∣ (m + (s : ℤ) * (k : ℤ)) then Gz s α m * FsZ s u m else 0))
      = ∑' m : ℤ, (if (t : ℤ) ∣ (m - (-((s : ℤ) * (k : ℤ)))) then Gz s α m * FsZ s u m else 0) from by
        refine tsum_congr fun m => ?_
        rw [show m + (s : ℤ) * (k : ℤ) = m - (-((s : ℤ) * (k : ℤ))) from by ring]]
  rw [← tsum_int_coset t ht (-((s : ℤ) * (k : ℤ))) _ (summable_gauss_FsZ_1 s α hs hα u)]
  refine tsum_congr fun j => ?_
  have hFs : FsZ s u (-((s : ℤ) * (k : ℤ)) + (t : ℤ) * j) = FsZ s u (t * j) := by
    rw [show -((s : ℤ) * (k : ℤ)) + (t : ℤ) * j = t * j + (s : ℤ) * (-(k : ℤ)) from by ring]
    rw [FsZ_period s hs u (t * j) (-(k : ℤ))]
  have hrr : Gz s α (-((s : ℤ) * (k : ℤ)) + (t : ℤ) * j) = Gzk s t α (k : ℕ) j := by
    rw [Gz, Gzk]
    congr 1
    congr 1
    push_cast
    field_simp
    ring
  rw [hrr, hFs]


/-- The right-hand side `P_t F_t S` acting on `u`, computed. -/
theorem permT_dft_resS_mulVec (s t α : ℕ) (hs : 0 < s) (ht : 0 < t) (hα : 0 < α)
    (u : Fin s → ℂ) (k : Fin t) :
    ((HvdH.permT s t * HvdH.dftMat t * HvdH.resSmat s t α).mulVec u) k =
      ∑' n : ℤ, (Real.exp (-Real.pi * (α : ℝ) ^ 2 * (t : ℝ) ^ 2 *
        ((k : ℝ) / (t : ℝ) - (n : ℝ) / (s : ℝ)) ^ 2) : ℂ) * FsZ s u (t * n) := by
  have hstep1 : ((HvdH.permT s t * HvdH.dftMat t * HvdH.resSmat s t α).mulVec u) k
      = FtZ t ((HvdH.resSmat s t α).mulVec u) (-((s : ℤ) * (k : ℤ))) := by
    rw [← Matrix.mulVec_mulVec u (HvdH.permT s t * HvdH.dftMat t) (HvdH.resSmat s t α)]
    rw [← Matrix.mulVec_mulVec ((HvdH.resSmat s t α).mulVec u) (HvdH.permT s t) (HvdH.dftMat t)]
    rw [permT_mulVec s t ht]
    exact dftMat_mulVec_permTrow s t ht ((HvdH.resSmat s t α).mulVec u) k
  rw [hstep1, FtZ]
  rw [show (∑ l : Fin t, ((HvdH.resSmat s t α).mulVec u) l *
        Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
          (((-(((s : ℤ) * (k : ℤ))) : ℤ) : ℂ) * ((l : ℕ) : ℂ)) / (t : ℂ)))
      = ∑ l : Fin t, ((HvdH.resSmat s t α).mulVec u) l *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((s : ℂ) * (k : ℂ)) * ((l : ℂ) / (t : ℂ))) from by
      refine Finset.sum_congr rfl fun l _ => ?_
      congr 1
      push_cast
      ring]
  rw [show (∑ l : Fin t, ((HvdH.resSmat s t α).mulVec u) l *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((s : ℂ) * (k : ℂ)) * ((l : ℂ) / (t : ℂ))))
      = ∑ l : Fin t,
          (∑' m : ℤ, (Real.exp (-Real.pi * (α : ℝ) ^ 2 * (m : ℝ) ^ 2 / (s : ℝ) ^ 2) : ℂ) *
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * ((l : ℂ) / (t : ℂ))) * FsZ s u m) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((s : ℂ) * (k : ℂ)) * ((l : ℂ) / (t : ℂ))) from by
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [resS_mulVec_expand s t α hs ht hα u l]]
  rw [resS_expand_sum s t α hs ht hα u k]
  rw [coset_to_gauss s t α hs ht hα u k]

end Work.ResMath
