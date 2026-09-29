import Mathlib
import Submission.Work.Resample.defs

/-!
# The one-dimensional entrywise resampling identity (paper Lemma 4.8 / Theorem 4.1, per dimension)

`Work.Resample.resample1DEntry` is the entrywise form of the 1-D identity
`dftMat s = 2^{2α²} • (resB s t α * dftMat t * resA s t α)` supplied by `ResMath1DProp`,
written with the unbundled entry functions `rA`, `rB`, `dE` of `Submission.Work.Resample.defs`.

It is the per-dimension ingredient of the tensor factorisation `resampleIdentity`
(and, through `tensorChain`, of `ResampleProp`).
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-! ### Elementary facts about `unb` -/

/-- Outside the top-left `n × n` block, `unb` vanishes. -/
theorem r1E_unbZeroLeft {s t : ℕ} (M : Matrix (Fin s) (Fin t) ℂ) {j : ℕ} (hj : ¬ j < s)
    (k : ℕ) : unb s t M j k = 0 := by
  rw [unb]; exact dite_eq_right (fun h => hj h.1)

/-- Outside the top-left `n × m` block, `unb` vanishes (second coordinate). -/
theorem r1E_unbZeroRight {s t : ℕ} (M : Matrix (Fin s) (Fin t) ℂ) (j : ℕ) {k : ℕ} (hk : ¬ k < t) :
    unb s t M j k = 0 := by
  rw [unb]; exact dite_eq_right (fun h => hk h.2)

/-- `unb` of a square matrix, evaluated at a genuine index pair, is the matrix entry. -/
theorem r1E_unbSelf {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (j k : Fin n) :
    unb n n M j k = M j k := by
  rw [unb_apply M j.isLt k.isLt]

/-- `unb` at an in-range row and a `Fin t` column. -/
theorem r1E_unbRow {s t : ℕ} (B : Matrix (Fin s) (Fin t) ℂ) {j : ℕ} (hj : j < s) (l : Fin t) :
    unb s t B j l = B ⟨j, hj⟩ l := by
  rw [unb_apply B hj l.isLt]

/-- `unb` at a `Fin t` row and an in-range column. -/
theorem r1E_unbCol {s t : ℕ} (A : Matrix (Fin t) (Fin s) ℂ) (l2 : Fin t) {k : ℕ} (hk : k < s) :
    unb t s A l2 k = A l2 ⟨k, hk⟩ := by
  rw [unb_apply A l2.isLt hk]

/-- `unb` is compatible with scalar multiplication. -/
theorem r1E_unbSmul {n : ℕ} (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) (j k : ℕ) :
    unb n n (c • A) j k = c * unb n n A j k := by
  by_cases h : j < n ∧ k < n
  · rw [unb, dite_eq_left h, unb, dite_eq_left h, Matrix.smul_apply, smul_eq_mul]
  · rw [unb, dite_eq_right h, unb, dite_eq_right h, mul_zero]

/-! ### The sum over the middle index is the matrix-product entry -/

/-- The unbundled triple product `∑_l B_{jl} (∑_{l₂} F_{l l₂} A_{l₂ k})` is `unb` of the matrix
product `B * F * A`. -/
theorem r1E_unbSum {s t : ℕ} (B : Matrix (Fin s) (Fin t) ℂ) (F : Matrix (Fin t) (Fin t) ℂ)
    (A : Matrix (Fin t) (Fin s) ℂ) (j k : ℕ) :
    (∑ l : Fin t, unb s t B j l * (∑ l2 : Fin t, unb t t F l l2 * unb t s A l2 k))
      = unb s s (B * F * A) j k := by
  by_cases hj : j < s
  · by_cases hk : k < s
    · rw [unb_apply (B * F * A) hj hk, Matrix.mul_assoc, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro l _
      rw [Matrix.mul_apply]
      congr 1
      · exact r1E_unbRow B hj l
      · apply Finset.sum_congr rfl
        intro l2 _
        rw [r1E_unbSelf F l l2, r1E_unbCol A l2 hk]
    · rw [r1E_unbZeroRight (B * F * A) j hk]
      apply Finset.sum_eq_zero
      intro l _
      have hz : (∑ l2 : Fin t, unb t t F l l2 * unb t s A l2 k) = 0 := by
        apply Finset.sum_eq_zero
        intro l2 _
        rw [r1E_unbZeroRight A l2 hk, mul_zero]
      rw [hz, mul_zero]
  · rw [r1E_unbZeroLeft (B * F * A) hj]
    apply Finset.sum_eq_zero
    intro l _
    rw [r1E_unbZeroLeft B hj l, zero_mul]

/-! ### Turning the 1-D identity into the entrywise form -/

/-- If `dftMat s = c • M` with `c = 2^{2α²}`, then the `(j,k)` entry of `M` is the `(j,k)` entry
of the DFT matrix scaled by `1/c`. -/
theorem r1E_entry (s α : ℕ) (M : Matrix (Fin s) (Fin s) ℂ)
    (hid : dftMat s = (2 : ℂ) ^ (2 * α ^ 2) • M) (j k : ℕ) :
    unb s s M j k = (1 / (2 : ℂ) ^ (2 * α ^ 2)) * dE s j k := by
  set c : ℂ := (2 : ℂ) ^ (2 * α ^ 2) with hc
  have hc0 : c ≠ 0 := by rw [hc]; exact pow_ne_zero _ (by norm_num)
  have hM' : M = c⁻¹ • dftMat s := by
    rw [hid, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [hM', hc, r1E_unbSmul, show dE s = unb s s (dftMat s) from rfl, one_div]

/-! ### The target lemma -/

theorem resample1DEntry (p α : ℕ) (ss ts : List ℕ) (h : HvdH.ResParams p α ss ts)
    (hM : HvdH.ResMath1DProp) (i : ℕ) (hi : i < HvdH.D) :
    (fun j k : ℕ => ∑ l : Fin (ts.getD i 0),
        Work.Resample.rB (ss.getD i 0) (ts.getD i 0) α j l *
          (∑ l2 : Fin (ts.getD i 0), Work.Resample.dE (ts.getD i 0) l l2 *
            Work.Resample.rA (ss.getD i 0) (ts.getD i 0) α l2 k))
      = fun j k : ℕ => (1 / (2 : ℂ) ^ (2 * α ^ 2)) * Work.Resample.dE (ss.getD i 0) j k := by
  obtain ⟨hs2, hst, _htp, hcop, hgr⟩ := h.2.2.2.2.2 i hi
  have hα : 2 ≤ α := h.2.2.2.1
  have hα2p : α ^ 2 < p := h.2.2.2.2.1
  have hid : dftMat (ss.getD i 0) = (2 : ℂ) ^ (2 * α ^ 2) •
      (resB (ss.getD i 0) (ts.getD i 0) α * dftMat (ts.getD i 0) *
        resA (ss.getD i 0) (ts.getD i 0) α) :=
    (hM (ss.getD i 0) (ts.getD i 0) α p hs2 hst hcop hα hα2p hgr).1
  funext j k
  simp only [rB, dE, rA]
  rw [r1E_unbSum (resB (ss.getD i 0) (ts.getD i 0) α) (dftMat (ts.getD i 0))
    (resA (ss.getD i 0) (ts.getD i 0) α) j k]
  exact r1E_entry (ss.getD i 0) α _ hid j k

end Work.Resample
