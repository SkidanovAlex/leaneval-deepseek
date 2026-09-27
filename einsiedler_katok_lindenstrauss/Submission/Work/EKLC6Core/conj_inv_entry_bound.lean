import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLComp.LeafDefs
import Submission.Work.EKLComp.atom_bad_bound
import Submission.Work.EKLContract.Lemmas.Box1_Uij
import Submission.Work.EKLContract.Lemmas.Uij_range

/-!
# `EKLC6Core.conj_inv_entry_bound` — inverting the conjugation by the diagonal flow on `U_ij`

The diagonal flow `aDiag t` *expands* an element `u = u_ij(s)` of the root group `U_ij` whenever
`t i < t j`: conjugating by `aDiag t ^ k` multiplies the single non-trivial entry `(i,j)` by
`e^{k (t i - t j)}`,

`aDiag t ^ k · u · (aDiag t ^ k)⁻¹ = u_ij (e^{k (t i - t j)} s)`.

The main result of this file inverts that statement quantitatively: if the *conjugate* lies in the
`ρ`-ball of the identity inside `U_ij`,

`aDiag t ^ k · u · (aDiag t ^ k)⁻¹ ∈ Uball U_ij ρ`   (`0 < ρ`),

then the original element `u` is bounded entrywise by the reciprocal expansion factor:

`|u a b| ≤ ρ · (e^{t i - t j} ^ k)⁻¹ + 1`   for all `a b : Fin 3`.

The bound is sharp in the only direction that matters: the diagonal entries of `u` equal `1`, and
the entry `(i,j)` is squeezed to `|s| < ρ · (e^{t i - t j} ^ k)⁻¹`.  No hypothesis on the sign of
`t i - t j` is needed — for `t i > t j` the expansion factor is `< 1` and the conjugate is pushed
*out* of any small ball unless `s` is already small, and the same computation covers it.

The proof is the entrywise conjugation formula (`conjInv_aDiag_pow_apply`, proved here from the
`toMat` API of `EKLContract/Diag.lean` to avoid the fragile `Coe`-handling of
`Matrix.SpecialLinearGroup`), together with `Uij = {u_ij(s)}` (`mem_Uij_iff`) and the explicit
entries of `u_ij(s)` (`uij_apply`).
-/

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## The entrywise conjugation formula for the diagonal flow -/

/-- Conjugation by `aDiag t` inverts conjugation by `aDiag (-t)`. -/
private theorem conjInv_aDiag_inv_eq_neg (t : Fin 3 → ℝ) : (aDiag t)⁻¹ = aDiag (-t) := by
  apply inv_eq_of_mul_eq_one_right
  rw [aDiag_add]
  simp [aDiag_zero]

/-- **The diagonal flow scales the entries**: conjugation by `aDiag s` multiplies the `(i,j)`-entry
by `e^{sᵢ - sⱼ}`.  (The normalising factors `e^{(∑ s)/3}` of `aDiag` cancel.) -/
private theorem conjInv_aDiag_conj_apply (s : Fin 3 → ℝ) (g : SL3) (i j : Fin 3) :
    (↑(aDiag s * g * (aDiag s)⁻¹) : Matrix (Fin 3) (Fin 3) ℝ) i j
      = Real.exp (s i - s j) * (↑g : Matrix (Fin 3) (Fin 3) ℝ) i j := by
  rw [conjInv_aDiag_inv_eq_neg]
  have key : toMat ((aDiag s * g) * aDiag (-s))
      = Matrix.diagonal (fun k => Real.exp (s k - (∑ j, s j) / 3)) * toMat g
        * Matrix.diagonal (fun k => Real.exp ((-s) k - (∑ j, (-s) j) / 3)) := by
    rw [toMat_mul, toMat_mul, toMat_aDiag, toMat_aDiag]
  have hexp : Real.exp (s i - (∑ j, s j) / 3) * Real.exp ((-s) j - (∑ j, (-s) j) / 3)
      = Real.exp (s i - s j) := by
    rw [← Real.exp_add]
    congr 1
    simp only [Pi.neg_apply, Finset.sum_neg_distrib]
    ring
  have happ : (↑(aDiag s * g * aDiag (-s)) : Matrix (Fin 3) (Fin 3) ℝ) i j
      = Real.exp (s i - (∑ j, s j) / 3) * (↑g : Matrix (Fin 3) (Fin 3) ℝ) i j
        * Real.exp ((-s) j - (∑ j, (-s) j) / 3) := by
    rw [← toMat_apply, key, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [happ, ← hexp]
  ring

/-- **Conjugation by a power of the diagonal flow.**
`((aDiag t)ⁿ · g · (aDiag t)⁻ⁿ)ᵢⱼ = e^{n (tᵢ - tⱼ)} · gᵢⱼ`. -/
private theorem conjInv_aDiag_pow_apply {t : Fin 3 → ℝ} (k : ℕ) (g : SL3) (i j : Fin 3) :
    (↑(aDiag t ^ k * g * (aDiag t ^ k)⁻¹) : Matrix (Fin 3) (Fin 3) ℝ) i j
      = Real.exp ((k : ℝ) * (t i - t j)) * (↑g : Matrix (Fin 3) (Fin 3) ℝ) i j := by
  have hpow : aDiag t ^ k = aDiag ((k : ℝ) • t) := by
    induction k with
    | zero => simp [aDiag_zero]
    | succ n ih =>
      rw [pow_succ, ih, aDiag_add]
      congr 1
      ext a
      simp only [Pi.add_apply, Pi.smul_apply]
      push_cast
      ring
  have hexp : ((k : ℝ) • t) i - ((k : ℝ) • t) j = (k : ℝ) * (t i - t j) := by
    simp only [Pi.smul_apply]; ring
  rw [hpow, conjInv_aDiag_conj_apply, hexp]

/-! ## The bound -/

/-- **Inverting the expansion of a root-group element.**  If `u ∈ U_ij` and its conjugate
`aDiag t ^ k · u · (aDiag t ^ k)⁻¹` lies in the `ρ`-ball `Uball U_ij ρ` of the identity (inside
`U_ij`), then every entry of `u` is bounded by `ρ (e^{t i - t j} ^ k)⁻¹ + 1`. -/
theorem conj_inv_entry_bound {i j : Fin 3} (hij : i ≠ j) (t : Fin 3 → ℝ) (k : ℕ) (ρ : ℝ)
    (hρ : 0 < ρ) {u : Work.EKLContract.SL3} (hu : u ∈ Work.EKLContract.Uij hij)
    (h : Work.EKLContract.aDiag t ^ k * u * (Work.EKLContract.aDiag t ^ k)⁻¹ ∈
      Work.EKLComp.Uball (Work.EKLContract.Uij hij) ρ) :
    ∀ a b : Fin 3, |((u : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) a b| ≤
      ρ * (Real.exp (t i - t j) ^ k)⁻¹ + 1 := by
  -- `u` is a transvection `u_ij s`
  obtain ⟨s, hs⟩ := (Work.EKLContract.Lemmas.mem_Uij_iff hij u).1 hu
  have hpos : 0 < Real.exp (t i - t j) ^ k := by positivity
  -- the `(i,j)`-entry of the conjugate is `e^{k (t i - t j)} s`
  have hconj : (↑(aDiag t ^ k * u * (aDiag t ^ k)⁻¹) : Matrix (Fin 3) (Fin 3) ℝ) i j
      = Real.exp ((k : ℝ) * (t i - t j)) * s := by
    rw [conjInv_aDiag_pow_apply, ← hs, Work.EKLContract.Lemmas.uij_apply_self]
  have hone : (1 : Matrix (Fin 3) (Fin 3) ℝ) i j = 0 := Matrix.one_apply_ne hij
  -- membership in the ball bounds that entry by `ρ`
  have hbound : |Real.exp ((k : ℝ) * (t i - t j)) * s| < ρ := by
    have hg := h.2 i j
    rw [hconj, hone, sub_zero] at hg
    exact hg
  have hstep : Real.exp (t i - t j) ^ k * |s| < ρ := by
    rw [Real.exp_nat_mul (t i - t j) k, abs_mul, abs_of_pos hpos] at hbound
    exact hbound
  -- hence `|s| ≤ ρ (e^{t i - t j} ^ k)⁻¹`
  have hfinal : |s| ≤ ρ * (Real.exp (t i - t j) ^ k)⁻¹ := by
    have h2 : |s| < ρ / Real.exp (t i - t j) ^ k :=
      (lt_div_iff₀ hpos).2 (by rw [mul_comm]; exact hstep)
    rw [div_eq_mul_inv] at h2
    exact le_of_lt h2
  have hnn : 0 ≤ ρ * (Real.exp (t i - t j) ^ k)⁻¹ :=
    mul_nonneg hρ.le (inv_nonneg.mpr hpos.le)
  -- and the entries of `u_ij s` are `1`, `s` and `0`
  intro a b
  have hua : (↑u : Matrix (Fin 3) (Fin 3) ℝ) a b
      = (↑(uij hij s) : Matrix (Fin 3) (Fin 3) ℝ) a b := by rw [← hs]
  rw [hua, Work.EKLContract.Lemmas.uij_apply]
  split_ifs with hab hijab
  · simp only [abs_one]; linarith
  · linarith
  · simp only [abs_zero]; linarith

end Work.EKLC6Core
