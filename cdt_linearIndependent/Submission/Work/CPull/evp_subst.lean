import Mathlib
import Submission.Work.CPull.defs
import Submission.Work.CPull.evp_aux
import Submission.Work.CPull.evpPow
import Submission.Work.CPull.coeffSubstTsum

/-!
# Area CPull — evaluation commutes with substitution of power series

`evp f z = ∑' n, (coeff n f : ℂ) * z ^ n` (see `Submission.Work.CPull.defs`).

The theorem `Work.CPull.evp_subst` states that if `b` has zero constant coefficient, the
coefficient series of `b` is absolutely summable at `z`, and the coefficient series of `f` is
absolutely summable at `S = ∑' j, ‖coeff j b‖ * ‖z‖^j` (the ℓ¹ mass of `b` at `z`, which
dominates `‖evp b z‖`), then the substituted series `f.subst b` (`= f ∘ b`) is absolutely
summable at `z` and

`evp (f.subst b) z = evp f (evp b z)`.

The proof is the classical rearrangement of the double series
`∑_n ∑_d (coeff d f) * (coeff n (b^d)) * z^n`:
`Work.CPull.coeffSubstTsum` computes the coefficients of `f.subst b` as such a series over `d`,
`Work.CPull.evpPow` identifies `∑'_n coeff n (b^d) z^n` with `(evp b z)^d` and controls the
ℓ¹ masses `∑'_n ‖coeff n (b^d) z^n‖ ≤ S^d`, and Tonelli (`summable_prod_of_nonneg`) plus
`Summable.tsum_comm` then swap the two summations.
-/

namespace Work.CPull

open PowerSeries

theorem evp_subst (f b : PowerSeries ℚ) (z : ℂ) (hb0 : PowerSeries.constantCoeff b = 0)
    (hb : Summable fun j : ℕ => ‖((PowerSeries.coeff j b : ℚ) : ℂ)‖ * ‖z‖ ^ j)
    (hf : Summable fun n : ℕ => ‖((PowerSeries.coeff n f : ℚ) : ℂ)‖ *
      (∑' j : ℕ, ‖((PowerSeries.coeff j b : ℚ) : ℂ)‖ * ‖z‖ ^ j) ^ n) :
    Summable (fun n : ℕ => ((PowerSeries.coeff n (f.subst b) : ℚ) : ℂ) * z ^ n) ∧
      evp (f.subst b) z = evp f (evp b z) := by
  set A : ℕ → ℂ := fun d => ((PowerSeries.coeff d f : ℚ) : ℂ) with hA
  set C : ℕ → ℂ := fun j => ((PowerSeries.coeff j b : ℚ) : ℂ) with hC
  set V : ℕ → ℕ → ℂ := fun d n => ((PowerSeries.coeff n (b ^ d) : ℚ) : ℂ) * z ^ n with hV
  set S : ℝ := ∑' j : ℕ, ‖C j‖ * ‖z‖ ^ j with hS
  have hnormC : ∀ j : ℕ, ‖C j * z ^ j‖ = ‖C j‖ * ‖z‖ ^ j := fun j => by rw [norm_mul, norm_pow]
  have hb' : Summable fun j : ℕ => ‖C j * z ^ j‖ := hb.congr (fun j => (hnormC j).symm)
  have hS' : (∑' j : ℕ, ‖C j * z ^ j‖) = S := by
    rw [hS]; exact tsum_congr hnormC
  have hf' : Summable fun d : ℕ => ‖A d‖ * S ^ d := by
    simpa only [hA] using hf
  have hpow := evpPow b z hb'
  have hVnorm : ∀ d : ℕ, Summable fun n : ℕ => ‖V d n‖ :=
    fun d => by simpa only [hV] using (hpow d).1
  have hVbnd : ∀ d : ℕ, (∑' n : ℕ, ‖V d n‖) ≤ S ^ d := by
    intro d
    have h := (hpow d).2.1
    rw [hS'] at h
    simpa only [hV] using h
  have hVval : ∀ d : ℕ, (∑' n : ℕ, V d n) = (evp b z) ^ d :=
    fun d => by simpa only [hV] using (hpow d).2.2
  -- Tonelli: the double family of norms is summable
  have hinner : ∀ d : ℕ, Summable fun n : ℕ => ‖A d * V d n‖ := fun d => by
    simpa only [norm_mul] using (hVnorm d).mul_left ‖A d‖
  have houter : Summable fun d : ℕ => ∑' n : ℕ, ‖A d * V d n‖ := by
    refine Summable.of_nonneg_of_le (fun d => tsum_nonneg fun n => norm_nonneg _) (fun d => ?_) hf'
    have h1 : (∑' n : ℕ, ‖A d * V d n‖) = ‖A d‖ * ∑' n : ℕ, ‖V d n‖ := by
      rw [tsum_congr (fun n => norm_mul (A d) (V d n)), Summable.tsum_mul_left ‖A d‖ (hVnorm d)]
    rw [h1]
    exact mul_le_mul_of_nonneg_left (hVbnd d) (norm_nonneg _)
  have hprod : Summable fun p : ℕ × ℕ => ‖A p.1 * V p.1 p.2‖ :=
    (summable_prod_of_nonneg (f := fun p : ℕ × ℕ => ‖A p.1 * V p.1 p.2‖)
      (fun p => norm_nonneg _)).mpr ⟨hinner, houter⟩
  have hcol : ∀ n : ℕ, Summable fun d : ℕ => ‖A d * V d n‖ := by
    have hswap : Summable fun p : ℕ × ℕ => ‖A p.2 * V p.2 p.1‖ := by
      simpa only [Prod.swap] using hprod.prod_symm
    exact ((summable_prod_of_nonneg (f := fun p : ℕ × ℕ => ‖A p.2 * V p.2 p.1‖)
      (fun p => norm_nonneg _)).mp hswap).1
  have hcolsum : Summable fun n : ℕ => ∑' d : ℕ, ‖A d * V d n‖ := by
    have hswap : Summable fun p : ℕ × ℕ => ‖A p.2 * V p.2 p.1‖ := by
      simpa only [Prod.swap] using hprod.prod_symm
    exact ((summable_prod_of_nonneg (f := fun p : ℕ × ℕ => ‖A p.2 * V p.2 p.1‖)
      (fun p => norm_nonneg _)).mp hswap).2
  -- the coefficients of `f.subst b`
  have hpoint : ∀ n : ℕ,
      ((PowerSeries.coeff n (f.subst b) : ℚ) : ℂ) * z ^ n = ∑' d : ℕ, A d * V d n := by
    intro n
    rw [coeffSubstTsum f b hb0 n, ← tsum_mul_right]
    exact tsum_congr fun d => by rw [hV]; ring
  have hV0norm : Summable fun n : ℕ => ‖∑' d : ℕ, A d * V d n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hcolsum
    exact norm_tsum_le_tsum_norm (hcol n)
  have hV0 : Summable fun n : ℕ => ((PowerSeries.coeff n (f.subst b) : ℚ) : ℂ) * z ^ n := by
    have hfun : (fun n : ℕ => ((PowerSeries.coeff n (f.subst b) : ℚ) : ℂ) * z ^ n)
        = fun n : ℕ => ∑' d : ℕ, A d * V d n := funext hpoint
    rw [hfun]
    exact hV0norm.of_norm
  refine ⟨hV0, ?_⟩
  have hG : Summable fun p : ℕ × ℕ => A p.1 * V p.1 p.2 := Summable.of_norm hprod
  have hfin : evp (f.subst b) z = ∑' n : ℕ, ∑' d : ℕ, A d * V d n := by
    rw [evp]
    exact tsum_congr hpoint
  rw [hfin, Summable.tsum_comm (f := fun d n => A d * V d n) hG]
  have hstep : (∑' d : ℕ, ∑' n : ℕ, A d * V d n) = ∑' d : ℕ, A d * (evp b z) ^ d :=
    tsum_congr fun d => by
      rw [Summable.tsum_mul_left _ (hVnorm d |>.of_norm), hVval d]
  rw [hstep, evp]
  exact tsum_congr fun d => by rw [hA]


end Work.CPull
