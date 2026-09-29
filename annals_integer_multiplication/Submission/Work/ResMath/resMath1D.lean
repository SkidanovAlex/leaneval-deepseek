import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.ResMath.resA_norm_le
import Submission.Work.ResMath.resE_norm_le
import Submission.Work.ResMath.resNeumann
import Submission.Work.ResMath.diagDp_entry_le_one
import Submission.Work.ResMath.resB_norm_le
import Submission.Work.ResMath.resamplingIdentity
import Submission.Work.ResMath.permS_transpose_mul
import Submission.Work.ResMath.diagD_mul_inv

/-! Area `ResMath` (paper §4.1–4.3(i), `REFS/nlogn.txt` lines 1188–1603): one-dimensional Gaussian
resampling.  We prove `HvdH.ResMath1DProp`, the eight conjuncts of Theorem 4.2, Lemmas 4.5 and 4.6 and
Proposition 4.7(i):

* `resamplingIdentity` : Theorem 4.2 `T·P_s·F_s = P_t·F_t·S`;
* `conj1` below : Proposition 4.7(i) `F_s = 2^{2α²}·B·F_t·A`, obtained from Theorem 4.2 by solving the
  (overdetermined) system `T x = y` with the left inverse `D·N⁻¹·C` of `T`, using
  `permS_transpose_mul` (`P_sᵀ = P_s⁻¹`), `diagD_mul_inv` (`D` invertible) and `resNeumann`
  (`N = 1 + E` invertible, `N⁻¹ = Jmat`, `‖J/2‖ ≤ 7/8`);
* `resA_norm_le`, `resE_norm_le`, `resNeumann`, `diagDp_entry_le_one`, `resB_norm_le` : the norm
  bounds, delegating Lemmas 4.5, 4.6 and the M4/M5/M6 steps.
-/

namespace Work.ResMath

open HvdH

/-- `2^(2α²-2) * (2*2) = 2^(2α²)` for `α ≥ 2` (the exponents are natural numbers). -/
lemma two_pow_sub (α : ℕ) (hα : 2 ≤ α) :
    (2 : ℂ) ^ (2 * α ^ 2 - 2) * (2 * 2) = (2 : ℂ) ^ (2 * α ^ 2) := by
  have hk : 2 * α ^ 2 - 2 + 2 = 2 * α ^ 2 := Nat.sub_add_cancel (by nlinarith [hα])
  calc (2 : ℂ) ^ (2 * α ^ 2 - 2) * (2 * 2) = (2 : ℂ) ^ (2 * α ^ 2 - 2) * (2 : ℂ) ^ 2 := by
        norm_num
    _ = (2 : ℂ) ^ ((2 * α ^ 2 - 2) + 2) := by rw [pow_add]
    _ = (2 : ℂ) ^ (2 * α ^ 2) := by rw [hk]

/-- Proposition 4.7(i): passing from `F_s` to `F_t` through the normalised resampling maps
`A = S/2`, `B = P_sᵀ D' J' C P_t`. -/
theorem conj1 (s t α p : ℕ) (hs : 2 ≤ s) (hst : s < t) (hc : Nat.Coprime s t) (hα : 2 ≤ α)
    (hαp : α ^ 2 < p) (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1) :
    dftMat s = (2 : ℂ) ^ (2 * α ^ 2) • (resB s t α * dftMat t * resA s t α) := by
  have hE := (resE_norm_le s t α p hs hst hα hαp hθ).1
  obtain ⟨hNJ, hJN⟩ := (resNeumann s t α hs hE).1
  obtain ⟨Dinv, hD1, hD2⟩ := diagD_mul_inv s t α
  have hPP' : (permS s t).transpose * permS s t = 1 := (permS_transpose_mul s t hc).1
  have hM0r : resTmat s t α * (permS s t * dftMat s) =
      permT s t * (dftMat t * resSmat s t α) := by
    simpa only [Matrix.mul_assoc] using resamplingIdentity s t α hs hst hc hα
  have hDW : diagD s t α * (Dinv * (permS s t * dftMat s)) = permS s t * dftMat s := by
    rw [← Matrix.mul_assoc, hD1, Matrix.one_mul]
  have hA : rowSel s t * (resTmat s t α * (diagD s t α * (Dinv * (permS s t * dftMat s)))) =
      rowSel s t * (permT s t * (dftMat t * resSmat s t α)) := by
    rw [hDW, hM0r]
  have hC : Nmat s t α * (Dinv * (permS s t * dftMat s)) =
      rowSel s t * (permT s t * (dftMat t * resSmat s t α)) := by
    simpa only [Nmat, Matrix.mul_assoc] using hA
  have hJ := congrArg (fun X => Jmat s t α * X) hC
  have hDinvPF : Dinv * (permS s t * dftMat s) =
      Jmat s t α * (rowSel s t * (permT s t * (dftMat t * resSmat s t α))) := by
    calc Dinv * (permS s t * dftMat s)
        = (Jmat s t α * Nmat s t α) * (Dinv * (permS s t * dftMat s)) := by
            rw [hJN, Matrix.one_mul]
      _ = Jmat s t α * (Nmat s t α * (Dinv * (permS s t * dftMat s))) := by
            rw [Matrix.mul_assoc]
      _ = Jmat s t α * (rowSel s t * (permT s t * (dftMat t * resSmat s t α))) := hJ
  have hPF : permS s t * dftMat s = diagD s t α *
      (Jmat s t α * (rowSel s t * (permT s t * (dftMat t * resSmat s t α)))) := by
    calc permS s t * dftMat s
        = (diagD s t α * Dinv) * (permS s t * dftMat s) := by rw [hD1, Matrix.one_mul]
      _ = diagD s t α * (Dinv * (permS s t * dftMat s)) := by rw [Matrix.mul_assoc]
      _ = diagD s t α * (Jmat s t α *
            (rowSel s t * (permT s t * (dftMat t * resSmat s t α)))) := by rw [hDinvPF]
  have hF : dftMat s = (permS s t).transpose *
      (diagD s t α * (Jmat s t α * (rowSel s t * (permT s t * (dftMat t * resSmat s t α))))) := by
    calc dftMat s = ((permS s t).transpose * permS s t) * dftMat s := by rw [hPP', Matrix.one_mul]
      _ = (permS s t).transpose * (permS s t * dftMat s) := by rw [Matrix.mul_assoc]
      _ = (permS s t).transpose *
            (diagD s t α * (Jmat s t α *
              (rowSel s t * (permT s t * (dftMat t * resSmat s t α))))) := by rw [hPF]
  have hD' : diagD s t α = (2 : ℂ) ^ (2 * α ^ 2 - 2) • diagD' s t α := by
    rw [diagD', smul_smul,
      show (2 : ℂ) ^ (2 * α ^ 2 - 2) * (1 / (2 : ℂ) ^ (2 * α ^ 2 - 2)) = 1 by
        rw [one_div, mul_inv_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0))],
      one_smul]
  have hJ' : (2 : ℂ) • ((1 / 2 : ℂ) • Jmat s t α) = Jmat s t α := by
    rw [smul_smul, show (2 : ℂ) * (1 / 2) = 1 by norm_num, one_smul]
  have hS' : (2 : ℂ) • resA s t α = resSmat s t α := by
    rw [resA, smul_smul, show (2 : ℂ) * (1 / 2) = 1 by norm_num, one_smul]
  rw [hF, hD', ← hJ', ← hS', resB, resA]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  rw [show 2 * (1 / 2) * (2 * (1 / 2)) * (2 : ℂ) ^ (2 * α ^ 2 - 2)
      = (2 : ℂ) ^ (2 * α ^ 2) * (1 / 2 * (1 / 2)) by
    simp only [show (2 : ℂ) * (1 / 2) = 1 by norm_num, one_mul,
      show (2 : ℂ) ^ (2 * α ^ 2) = (2 : ℂ) ^ (2 * α ^ 2 - 2) * (2 * 2) from
        (two_pow_sub α hα).symm]
    ring]

/-- Paper Thm 4.2, Lem. 4.5 and 4.6, Proposition 4.7(i): one-dimensional Gaussian resampling. -/
theorem resMath1D : HvdH.ResMath1DProp := by
  intro s t α p hs hst hc hα hαp hθ
  have hE := (resE_norm_le s t α p hs hst hα hαp hθ).1
  have hN := resNeumann s t α hs hE
  exact ⟨conj1 s t α p hs hst hc hα hαp hθ,
    resA_norm_le s t α hs hst hα,
    (resE_norm_le s t α p hs hst hα hαp hθ).1,
    (resE_norm_le s t α p hs hst hα hαp hθ).2,
    hN.2.1,
    hN.2.2,
    fun ℓ => diagDp_entry_le_one s t α hα ℓ,
    fun v => resB_norm_le s t α hs hst hc hα (fun ℓ => diagDp_entry_le_one s t α hα ℓ) hN.2.2 v⟩

end Work.ResMath
