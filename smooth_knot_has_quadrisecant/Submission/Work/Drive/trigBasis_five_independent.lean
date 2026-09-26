import Mathlib
import Submission.Work.Drive.knotPerturbDefs
import Submission.Work.Drive.tangencyBadSet

namespace Work.Drive

noncomputable section

open LeanEval.KnotTheory.Quadrisecant

/-! ## Auxiliary facts about the trigonometric basis

The basis functions with index `0 … 4` are `1, cos t, sin t, cos 2t, sin 2t`.  We record their
values (they hold by `rfl`, but `simp` does not unfold the pattern match by itself). -/

private lemma trigBasis_zero (t : ℝ) : trigBasis 0 t = 1 := rfl

private lemma trigBasis_one (t : ℝ) : trigBasis 1 t = Real.cos t := rfl

private lemma trigBasis_two (t : ℝ) : trigBasis 2 t = Real.sin t := rfl

private lemma trigBasis_three (t : ℝ) : trigBasis 3 t = Real.cos (2 * t) := rfl

private lemma trigBasis_four (t : ℝ) : trigBasis 4 t = Real.sin (2 * t) := rfl

/-! ## Distinct parameters give distinct points on the unit circle -/

/-- If two real parameters are separated in the circular metric `csep`, the corresponding points
`exp (t * I)` of the unit circle are distinct.  Indeed `exp` equality forces `s - t ∈ 2πℤ`, while
`0 < csep s t` forces `0 < |s - t| < 2π`. -/
private lemma exp_I_ne_of_csep_pos {s t : ℝ} (h : 0 < csep s t) :
    Complex.exp ((s : ℂ) * Complex.I) ≠ Complex.exp ((t : ℂ) * Complex.I) := by
  intro he
  rw [Complex.exp_eq_exp_iff_exists_int] at he
  obtain ⟨n, hn⟩ := he
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  have h2 : (s : ℂ) = (t : ℂ) + (n : ℂ) * (2 * (Real.pi : ℂ)) := by
    have h3 : (s : ℂ) * Complex.I = ((t : ℂ) + (n : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I := by
      rw [hn]; ring
    exact mul_right_cancel₀ Complex.I_ne_zero h3
  have h2r : s = t + (n : ℝ) * (2 * Real.pi) := by
    have h4 : ((s : ℂ)) = ((t + (n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) := by
      push_cast
      exact h2
    exact Complex.ofReal_inj.mp h4
  have hmin : 0 < min |s - t| (2 * Real.pi - |s - t|) := by simpa [csep] using h
  have hgt : 0 < |s - t| := (lt_min_iff.mp hmin).1
  have hlt : |s - t| < 2 * Real.pi := by
    have := (lt_min_iff.mp hmin).2; linarith
  have hsdt : s - t = (n : ℝ) * (2 * Real.pi) := by linarith
  have h1 : |(n:ℝ) * (2 * Real.pi)| < 2 * Real.pi := by rw [← hsdt]; exact hlt
  rw [abs_mul, abs_of_pos hpi] at h1
  have h2' : |(n:ℝ)| < 1 := by nlinarith [hpi]
  have hn0 : n = 0 := by
    have := abs_lt.mp h2'
    have h3 : n < 1 := by exact_mod_cast this.2
    have h4 : (-1 : ℤ) < n := by exact_mod_cast this.1
    omega
  have hz : |s - t| = 0 := by rw [hsdt, hn0]; simp
  linarith

/-! ## From real trigonometric equations to complex moment equations -/

/-- Real equations for the frequency `k` give the complex equation `∑ αᵢ zᵢ^k = 0`, where
`zᵢ = exp (wᵢ * I)`. -/
private lemma sum_exp_pow_zero (w : Fin 5 → ℝ) (α : Fin 5 → ℝ) (k : ℕ)
    (hc : ∑ i, α i * Real.cos (k * w i) = 0)
    (hs : ∑ i, α i * Real.sin (k * w i) = 0) :
    ∑ i, (α i : ℂ) * (Complex.exp ((w i : ℂ) * Complex.I)) ^ k = 0 := by
  have hterm : ∀ i : Fin 5, (α i : ℂ) * (Complex.exp ((w i : ℂ) * Complex.I)) ^ k
      = ((α i * Real.cos (k * w i) : ℝ) : ℂ)
        + ((α i * Real.sin (k * w i) : ℝ) : ℂ) * Complex.I := by
    intro i
    have e1 : Complex.exp ((w i : ℂ) * Complex.I) ^ k
        = Complex.exp ((k : ℂ) * ((w i : ℂ) * Complex.I)) :=
      (Complex.exp_nat_mul ((w i : ℂ) * Complex.I) k).symm
    have e2 : (k : ℂ) * ((w i : ℂ) * Complex.I) = ((k * w i : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [e1, e2, Complex.exp_ofReal_mul_I]
    push_cast
    ring
  calc ∑ i, (α i : ℂ) * (Complex.exp ((w i : ℂ) * Complex.I)) ^ k
      = ∑ i, (((α i * Real.cos (k * w i) : ℝ) : ℂ)
          + ((α i * Real.sin (k * w i) : ℝ) : ℂ) * Complex.I) :=
        Finset.sum_congr rfl fun i _ => hterm i
    _ = ((∑ i, α i * Real.cos (k * w i) : ℝ) : ℂ)
        + ((∑ i, α i * Real.sin (k * w i) : ℝ) : ℂ) * Complex.I := by
        rw [Finset.sum_add_distrib, ← Complex.ofReal_sum, ← Finset.sum_mul, ← Complex.ofReal_sum]
    _ = 0 := by rw [hc, hs]; simp

/-- The same real equations give the complex equation for the inverse powers
`∑ αᵢ (zᵢ⁻¹)^k = 0`. -/
private lemma sum_exp_neg_pow_zero (w : Fin 5 → ℝ) (α : Fin 5 → ℝ) (k : ℕ)
    (hc : ∑ i, α i * Real.cos (k * w i) = 0)
    (hs : ∑ i, α i * Real.sin (k * w i) = 0) :
    ∑ i, (α i : ℂ) * ((Complex.exp ((w i : ℂ) * Complex.I))⁻¹) ^ k = 0 := by
  have hterm : ∀ i : Fin 5, (α i : ℂ) * ((Complex.exp ((w i : ℂ) * Complex.I))⁻¹) ^ k
      = ((α i * Real.cos (k * w i) : ℝ) : ℂ)
        - ((α i * Real.sin (k * w i) : ℝ) : ℂ) * Complex.I := by
    intro i
    have e1 : (Complex.exp ((w i : ℂ) * Complex.I))⁻¹ ^ k
        = Complex.exp ((k : ℂ) * (-((w i : ℂ) * Complex.I))) := by
      rw [← Complex.exp_neg, ← Complex.exp_nat_mul]
    have e2 : (k : ℂ) * (-((w i : ℂ) * Complex.I)) = ((-(k * w i) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [e1, e2, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  calc ∑ i, (α i : ℂ) * ((Complex.exp ((w i : ℂ) * Complex.I))⁻¹) ^ k
      = ∑ i, (((α i * Real.cos (k * w i) : ℝ) : ℂ)
          - ((α i * Real.sin (k * w i) : ℝ) : ℂ) * Complex.I) :=
        Finset.sum_congr rfl fun i _ => hterm i
    _ = ((∑ i, α i * Real.cos (k * w i) : ℝ) : ℂ)
        - ((∑ i, α i * Real.sin (k * w i) : ℝ) : ℂ) * Complex.I := by
        rw [Finset.sum_sub_distrib, ← Complex.ofReal_sum, ← Finset.sum_mul, ← Complex.ofReal_sum]
    _ = 0 := by rw [hc, hs]; simp

open LeanEval.KnotTheory.Quadrisecant in
/-- Five value functionals of the trigonometric basis (frequencies `0 … 4`, `trigBasis : Fin 9 → ℝ → ℝ`
from `Submission.Work.Drive.knotPerturbDefs`) at five parameters separated in the circular metric
`csep` are linearly independent: a relation `∑ i, α i * trigBasis j (w i) = 0` for all `j : Fin 9`
forces `α = 0`.

Route.  With `z i := Complex.exp ((w i : ℂ) * Complex.I)` (nonzero, pairwise distinct because
`0 < csep (w i) (w j)` and `w i ∈ [0, 2π]` rule out differences in `2πℤ` — use
`Complex.exp_eq_exp_iff_exists_int`), the five equations of frequency `0,1,2` give
`∑ i, α i * (z i)^k = 0` for `k = 0, 1, 2`, and their conjugates give `k = -1, -2`.  Put
`β i := α i * ((z i)⁻¹)^2`; then `∑ i, β i * (z i)^m = 0` for `m = 0, 1, 2, 3, 4`.  That says
`(Matrix.vandermonde z).transpose *ᵥ β = 0`; `Matrix.det_vandermonde` gives the determinant
`∏ i, ∏ j > i, (z j - z i) ≠ 0`, so `β = 0` (`Matrix.mulVec_injective_of_isUnit`,
`Matrix.isUnit_iff_isUnit_det`), hence `α = 0`.

Alternative (reviewer's) route: test the relation against `∏ j ≠ i, (2 - 2 * Real.cos (t - w j))`. -/
theorem trigBasis_five_independent (w : Fin 5 → ℝ)
    (hw : ∀ i : Fin 5, w i ∈ Set.Icc (0 : ℝ) (2 * Real.pi))
    (hsep : ∀ i j : Fin 5, i ≠ j → 0 < csep (w i) (w j))
    (α : Fin 5 → ℝ)
    (h : ∀ j : Fin 9, ∑ i : Fin 5, α i * trigBasis j (w i) = 0) : α = 0 := by
  classical
  set z : Fin 5 → ℂ := fun i => Complex.exp ((w i : ℂ) * Complex.I) with hzdef
  have hz : ∀ i : Fin 5, z i = Complex.exp ((w i : ℂ) * Complex.I) := fun i => by rw [hzdef]
  have hz_ne : ∀ i : Fin 5, z i ≠ 0 := fun i => Complex.exp_ne_zero _
  have hzinj : Function.Injective z := by
    intro i j hij
    by_contra hne
    exact exp_I_ne_of_csep_pos (hsep i j hne) (by rw [hz i, hz j] at hij; exact hij)
  -- the real equations of frequency `0`, `1`, `2`
  have hc0 : ∑ i : Fin 5, α i * Real.cos (((0 : ℕ) : ℝ) * w i) = 0 := by
    simpa [trigBasis_zero] using h 0
  have hs0 : ∑ i : Fin 5, α i * Real.sin (((0 : ℕ) : ℝ) * w i) = 0 := by simp
  have hc1 : ∑ i : Fin 5, α i * Real.cos (((1 : ℕ) : ℝ) * w i) = 0 := by
    simpa [trigBasis_one] using h 1
  have hs1 : ∑ i : Fin 5, α i * Real.sin (((1 : ℕ) : ℝ) * w i) = 0 := by
    simpa [trigBasis_two] using h 2
  have hc2 : ∑ i : Fin 5, α i * Real.cos (((2 : ℕ) : ℝ) * w i) = 0 := by
    simpa [trigBasis_three] using h 3
  have hs2 : ∑ i : Fin 5, α i * Real.sin (((2 : ℕ) : ℝ) * w i) = 0 := by
    simpa [trigBasis_four] using h 4
  -- the complex equations for powers `0`, `1`, `2`, `-1`, `-2`
  have E0 : ∑ i : Fin 5, (α i : ℂ) = 0 := by
    have hh := sum_exp_pow_zero w α 0 hc0 hs0
    simpa [hz] using hh
  have E1 : ∑ i : Fin 5, (α i : ℂ) * (z i) = 0 := by
    have hh := sum_exp_pow_zero w α 1 hc1 hs1
    simpa [hz] using hh
  have E2 : ∑ i : Fin 5, (α i : ℂ) * (z i) ^ 2 = 0 := by
    have hh := sum_exp_pow_zero w α 2 hc2 hs2
    simpa [hz] using hh
  have Em1 : ∑ i : Fin 5, (α i : ℂ) * ((z i)⁻¹) = 0 := by
    have hh := sum_exp_neg_pow_zero w α 1 hc1 hs1
    simpa [hz] using hh
  have Em2 : ∑ i : Fin 5, (α i : ℂ) * ((z i)⁻¹) ^ 2 = 0 := by
    have hh := sum_exp_neg_pow_zero w α 2 hc2 hs2
    simpa [hz] using hh
  -- shift the measure by `(z i)⁻²` so that the powers `-2 … 2` become `0 … 4`
  set β : Fin 5 → ℂ := fun i => (α i : ℂ) * ((z i)⁻¹) ^ 2 with hβdef
  have hβ_apply : ∀ i : Fin 5, β i = (α i : ℂ) * ((z i)⁻¹) ^ 2 := fun i => by rw [hβdef]
  have hmom : ∀ m : Fin 5, ∑ i : Fin 5, β i * (z i) ^ (m : ℕ) = 0 := by
    have hmom_nat : ∀ m : ℕ, m ≤ 4 → ∑ i : Fin 5, β i * (z i) ^ m = 0 := by
      intro m hm
      interval_cases m
      · have hstep : ∑ i : Fin 5, β i * (z i) ^ (0 : ℕ)
            = ∑ i : Fin 5, (α i : ℂ) * ((z i)⁻¹) ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hβ_apply i]; field_simp [hz_ne i]
        rw [hstep]; exact Em2
      · have hstep : ∑ i : Fin 5, β i * (z i) ^ (1 : ℕ)
            = ∑ i : Fin 5, (α i : ℂ) * ((z i)⁻¹) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hβ_apply i]; field_simp [hz_ne i]
        rw [hstep]; exact Em1
      · have hstep : ∑ i : Fin 5, β i * (z i) ^ (2 : ℕ)
            = ∑ i : Fin 5, (α i : ℂ) * 1 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hβ_apply i]; field_simp [hz_ne i]
        rw [hstep]; simpa using E0
      · have hstep : ∑ i : Fin 5, β i * (z i) ^ (3 : ℕ)
            = ∑ i : Fin 5, (α i : ℂ) * (z i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hβ_apply i]; field_simp [hz_ne i]
        rw [hstep]; exact E1
      · have hstep : ∑ i : Fin 5, β i * (z i) ^ (4 : ℕ)
            = ∑ i : Fin 5, (α i : ℂ) * (z i) ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hβ_apply i]; field_simp [hz_ne i]
        rw [hstep]; exact E2
    intro m
    exact hmom_nat (m : ℕ) (by have := m.isLt; omega)
  -- Vandermonde: the five moments vanish, so `β = 0`
  have hmat : Matrix.mulVec (Matrix.transpose (Matrix.vandermonde z)) β = 0 := by
    funext m
    simpa [Matrix.mulVec, dotProduct, Matrix.vandermonde, mul_comm] using hmom m
  have hβzero : β = 0 := by
    have hdet0 : (Matrix.vandermonde z).det ≠ 0 := by
      rw [Matrix.det_vandermonde]
      refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
      rw [sub_ne_zero]
      intro hji
      exact absurd (hzinj hji).symm (ne_of_lt (Finset.mem_Ioi.mp hj))
    have hdet : (Matrix.transpose (Matrix.vandermonde z)).det ≠ 0 := by
      rw [Matrix.det_transpose]; exact hdet0
    have hunit : IsUnit (Matrix.transpose (Matrix.vandermonde z)) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
    exact (Matrix.mulVec_injective_of_isUnit hunit) (by rw [hmat, Matrix.mulVec_zero])
  funext i
  have hi : β i = 0 := congrFun hβzero i
  have h1 : (α i : ℂ) * ((z i)⁻¹) ^ 2 = 0 := by rw [← hβ_apply i]; exact hi
  have key : (α i : ℂ) * ((z i)⁻¹) ^ 2 * (z i) ^ 2 = (α i : ℂ) := by
    rw [inv_pow, mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 (hz_ne i)), mul_one]
  rw [h1, zero_mul] at key
  exact Complex.ofReal_eq_zero.mp key.symm

end

end Work.Drive
