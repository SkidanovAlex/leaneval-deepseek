/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Basis reduction for the perturbed `∂̄`-equation (the "componentwise" trick)

`Work.NN.Final.dbarCn_eq_of_basis`: if `Φ = Jstd + A` is **almost complex at `z`**
(`Φ z (Φ z v) = -v`), `A z` is small on the coordinate vectors (`‖A z e_j‖ ≤ ε` with
`n·ε < 1/2`), `f z` is `Φ z`-antilinear, and the *form* `∂̄_Φ u` agrees with `f` on the
coordinate vectors `e_j` only, then `∂̄_Φ u = f` on **all** vectors.

This is the structural lemma that turns a fixed-point equation stated *componentwise*
(`a_j = f(e_j) - (i/2)·du(A e_j)`, which makes the defect `∂̄_Φ u - f` vanish **exactly**)
into the form-level equation.  See `NOTES_l2Solvability_obstruction.md` §43.

Proof.  Put `δ := ∂̄_Φ u - f z` and `J := Φ z`.  Both summands are `J`-antilinear, so `δ` is
`J`-antilinear, and `δ(e_j) = 0` gives `δ(J e_j) = 0` as well.  Since `J e_j = i e_j + A e_j`,
this is `δ(i e_j) = -δ(A e_j)`, and expanding `A e_j = Σ_k (A e_j)_k • e_k` (with the real and
imaginary parts separated, and using `δ(e_k) = 0`) gives the linear system
`V_j = -Σ_k Im((A z e_j)_k)·V_k` for `V_k := δ(i e_k)`.  Taking the sup norm,
`‖V‖ ≤ n·ε·‖V‖`, so `‖V‖ = 0` because `n·ε < 1/2`.  Hence `δ` vanishes on `{e_j, i e_j}`, a real
basis of `ℂⁿ`, and `Work.NN.Core.form_ext_basis` gives `δ = 0`.
-/
import Mathlib
import Submission.Work.NN.Core.CnPert

noncomputable section

open scoped NNReal ENNReal
open Finset

namespace Work.NN.Final

open Work.NN.Core

/-- The decomposition of `Pi.single k c` into real multiples of `e_k` and `i·e_k`. -/
private lemma single_eq_real_combination {n : ℕ} (k : Fin n) (c : ℂ) :
    Pi.single k c = (c.re) • (Pi.single k (1 : ℂ) : Cn n)
      + (c.im) • (Complex.I • (Pi.single k (1 : ℂ) : Cn n)) := by
  funext m
  by_cases hm : m = k
  · subst hm
    simp [Complex.re_add_im]
  · simp [Pi.single_eq_of_ne hm]

/-- **Basis reduction for the perturbed `∂̄`-equation.** -/
theorem dbarCn_eq_of_basis {n : ℕ} {A : Cn n → Cn n →L[ℝ] Cn n}
    {u : Cn n → ℂ} {f : Cn n → Cn n →L[ℝ] ℂ}
    {z : Cn n} {ε : ℝ} (hε : (n : ℝ) * ε < 1 / 2)
    (hJ : ∀ v, (JstdCn n + A) z ((JstdCn n + A) z v) = -v)
    (hAz : ∀ j : Fin n, ‖A z (Pi.single j (1 : ℂ))‖ ≤ ε)
    (hf : ∀ v, f z ((JstdCn n + A) z v) = -Complex.I * f z v)
    (h : ∀ j : Fin n, dbarCn (JstdCn n + A) u z (Pi.single j (1 : ℂ))
        = f z (Pi.single j (1 : ℂ))) :
    ∀ V, dbarCn (JstdCn n + A) u z V = f z V := by
  set w : Cn n →L[ℝ] ℂ := dbarCn (JstdCn n + A) u z - f z with hwdef
  -- `w` is `(Jstd+A) z`-antilinear
  have hwanti : ∀ v : Cn n, w ((JstdCn n + A) z v) = -Complex.I * w v := by
    intro v
    have h1 : dbarCn (JstdCn n + A) u z ((JstdCn n + A) z v)
        = -Complex.I * dbarCn (JstdCn n + A) u z v :=
      dbarCn_antilinear (J := JstdCn n + A) (u := u) (z := z) hJ v
    have h2 : f z ((JstdCn n + A) z v) = -Complex.I * f z v := hf v
    simp only [hwdef, sub_apply]
    rw [h1, h2]
    ring
  -- `w` vanishes on the coordinate vectors
  have hwe : ∀ j : Fin n, w (Pi.single j (1 : ℂ)) = 0 := by
    intro j
    simp only [hwdef, sub_apply]
    rw [h j, sub_self]
  -- the splitting `(Jstd+A) z e_j = A z e_j + i e_j`
  have hsplit : ∀ j : Fin n, (JstdCn n + A) z (Pi.single j (1 : ℂ))
      = A z (Pi.single j (1 : ℂ)) + Complex.I • (Pi.single j (1 : ℂ) : Cn n) := by
    intro j
    simp only [Pi.add_apply, add_apply, JstdCn_apply, add_comm]
  have hwB : ∀ j : Fin n, w (Complex.I • (Pi.single j (1 : ℂ) : Cn n))
      = -w (A z (Pi.single j (1 : ℂ))) := by
    intro j
    have h0 : w ((JstdCn n + A) z (Pi.single j (1 : ℂ))) = 0 := by
      rw [hwanti, hwe j]
      ring
    rw [hsplit j, map_add] at h0
    linear_combination h0
  -- the linear system satisfied by `V j := w (i e_j)`
  have hsys : ∀ j : Fin n, w (Complex.I • (Pi.single j (1 : ℂ) : Cn n))
      = -∑ k : Fin n, (((A z (Pi.single j (1 : ℂ))) k).im : ℂ)
          * w (Complex.I • (Pi.single k (1 : ℂ) : Cn n)) := by
    intro j
    have h2 : w (A z (Pi.single j (1 : ℂ)))
        = ∑ k : Fin n, (((A z (Pi.single j (1 : ℂ))) k).im : ℂ)
            * w (Complex.I • (Pi.single k (1 : ℂ) : Cn n)) := by
      conv_lhs => rw [show A z (Pi.single j (1 : ℂ))
        = ∑ k : Fin n, Pi.single k ((A z (Pi.single j (1 : ℂ))) k) from
          (Finset.univ_sum_single (fun k : Fin n => (A z (Pi.single j (1 : ℂ))) k)).symm]
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [single_eq_real_combination, map_add, map_smul, map_smul, hwe k]
      simp [Complex.real_smul]
    rw [hwB j, h2]
  set V : Fin n → ℂ := fun j => w (Complex.I • (Pi.single j (1 : ℂ) : Cn n)) with hVdef
  have hsysV : ∀ j : Fin n, V j = -∑ k : Fin n,
      (((A z (Pi.single j (1 : ℂ))) k).im : ℂ) * V k := by
    intro j
    have h := hsys j
    simpa only [hVdef] using h
  -- the sup-norm bound `‖V‖ ≤ n·ε·‖V‖`
  have hεnn : 0 ≤ (n : ℝ) * ε := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have j : Fin n := ⟨0, hn⟩
      nlinarith [norm_nonneg (A z (Pi.single j (1 : ℂ))), hAz j]
  have hbound : ‖V‖ ≤ ((n : ℝ) * ε) * ‖V‖ := by
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg hεnn (norm_nonneg V))]
    intro j
    have h1 : ‖V j‖ ≤ ∑ k : Fin n,
        ‖(((A z (Pi.single j (1 : ℂ))) k).im : ℂ) * V k‖ := by
      rw [hsysV j, norm_neg]
      exact norm_sum_le _ _
    have h2 : ∀ k : Fin n,
        ‖(((A z (Pi.single j (1 : ℂ))) k).im : ℂ) * V k‖ ≤ ε * ‖V‖ := by
      intro k
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hk : |((A z (Pi.single j (1 : ℂ))) k).im|
          ≤ ‖A z (Pi.single j (1 : ℂ))‖ :=
        le_trans (Complex.abs_im_le_norm _) (norm_le_pi_norm _ k)
      have hk' : |((A z (Pi.single j (1 : ℂ))) k).im| ≤ ε := le_trans hk (hAz j)
      have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) hk'
      calc |((A z (Pi.single j (1 : ℂ))) k).im| * ‖V k‖
          ≤ ε * ‖V k‖ := mul_le_mul_of_nonneg_right hk' (norm_nonneg _)
        _ ≤ ε * ‖V‖ := mul_le_mul_of_nonneg_left (norm_le_pi_norm V k) hε0
    calc ‖V j‖ ≤ ∑ k : Fin n,
          ‖(((A z (Pi.single j (1 : ℂ))) k).im : ℂ) * V k‖ := h1
      _ ≤ ∑ _k : Fin n, ε * ‖V‖ := Finset.sum_le_sum fun k _ => h2 k
      _ = (n : ℝ) * (ε * ‖V‖) := by simp [Finset.sum_const, nsmul_eq_mul]
      _ = ((n : ℝ) * ε) * ‖V‖ := by ring
  have hVzero : V = 0 := by
    have : ‖V‖ = 0 := by nlinarith [hbound, norm_nonneg V]
    exact norm_eq_zero.mp this
  -- `w` vanishes on `{e_j, i e_j}`, a real basis
  have hwI : ∀ j : Fin n, w (Complex.I • (Pi.single j (1 : ℂ) : Cn n)) = 0 := by
    intro j
    have h := congrFun hVzero j
    simpa only [hVdef, Pi.zero_apply] using h
  have hbasis : ∀ j : Fin n, w (Pi.single j (Complex.I : ℂ)) = 0 := by
    intro j
    rw [← Work.NN.Core.smul_single_I j]
    exact hwI j
  have hw0 : w = 0 :=
    Work.NN.Core.form_ext_basis (f := w) (g := 0)
      (fun j => by rw [hwe j]; rfl) (fun j => by rw [hbasis j]; rfl)
  intro V
  have hV := congrArg (fun (L : Cn n →L[ℝ] ℂ) => L V) hw0
  simp only [zero_apply] at hV
  simp only [hwdef, sub_apply] at hV
  exact sub_eq_zero.mp hV

end Work.NN.Final
