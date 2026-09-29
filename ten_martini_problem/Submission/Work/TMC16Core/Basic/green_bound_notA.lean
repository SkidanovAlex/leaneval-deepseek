import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Basic.dirMat_mulVec_entry
import Submission.Work.TMC16Core.Basic.toNat_interval_facts
import Submission.Work.TMC16Core.Basic.div_lt_exp_sub

namespace Work.TMC16Core.Basic

open Work.TMC16Core

/-! ## Continuant identities for `pd` -/

/-- `amoPot` phase/site shift: replacing the phase `φ` by `φ + j α` and the site `n` by
`n + j` does not change the potential. -/
lemma amoPot_shiftZ (α lam φ : ℝ) (j : ℤ) (n : ℤ) :
    amoPot α lam (φ + (j : ℝ) * α) n = amoPot α lam φ (n + j) := by
  simp only [amoPot]
  rw [show (2:ℝ) * Real.pi * (φ + (j:ℝ)*α + (n:ℝ)*α)
      = 2 * Real.pi * (φ + ((n + j : ℤ) : ℝ) * α) by push_cast; ring]

/-- Shifting the phase of `amoPot` by `+α` shifts the site index by one. -/
lemma amoPot_plus_one_phase (α lam ψ : ℝ) (k : ℕ) :
    amoPot α lam (ψ + α) ((k:ℕ):ℤ) = amoPot α lam ψ (((k+1:ℕ)):ℤ) := by
  have h := amoPot_shiftZ α lam ψ (1:ℤ) ((k:ℕ):ℤ)
  rw [show ψ + ((1:ℤ):ℝ) * α = ψ + α by norm_num] at h
  rw [show ((k:ℤ) + 1) = (((k+1:ℕ)):ℤ) by omega] at h
  exact h

/-- Shifting the phase of `amoPot` by `+2α` shifts the site index by two (written in
successor form so that it matches the index terms produced by unfolding `pd`). -/
lemma amoPot_plus_two_phase (α lam ψ : ℝ) (k : ℕ) :
    amoPot α lam (ψ + 2 * α) ((k:ℕ):ℤ) = amoPot α lam ψ (((k+1)+1:ℕ):ℤ) := by
  have h1 := amoPot_plus_one_phase α lam (ψ + α) k
  rw [show (ψ + α) + α = ψ + 2 * α by ring] at h1
  rw [h1, amoPot_plus_one_phase]

/-- Site-index form of the phase shift of `amoPot`, matching the index pattern produced by
`pd`'s recursion. -/
lemma amoPot_self_shift_nat (α lam φ : ℝ) (j : ℕ) :
    amoPot α lam (φ + (j:ℝ) * α) ((0:ℕ):ℤ) = amoPot α lam φ ((j:ℕ):ℤ) := by
  have h := amoPot_shiftZ α lam φ (j:ℤ) 0
  rw [show φ + ((j:ℤ):ℝ) * α = φ + (j:ℝ) * α by norm_num] at h
  simpa using h

/-- The defining recursion of the continuant, in a `rw`-friendly general form. -/
lemma pd_unfold (α lam : ℝ) (θ : ℝ) (E : ℂ) (n : ℕ) :
    pd α lam θ E (n + 2) = (E - ((amoPot α lam θ ((n:ℕ):ℤ) : ℝ) : ℂ)) * pd α lam θ E (n + 1)
      - pd α lam θ E n := by
  rw [pd]

lemma pd_zero (α lam : ℝ) (θ : ℝ) (E : ℂ) : pd α lam θ E 0 = 0 := by rw [pd]

lemma pd_one (α lam : ℝ) (θ : ℝ) (E : ℂ) : pd α lam θ E 1 = 1 := by rw [pd]

lemma pd_two (α lam : ℝ) (ψ : ℝ) (E : ℂ) :
    pd α lam ψ E 2 = E - ((amoPot α lam ψ ((0:ℕ):ℤ) : ℝ) : ℂ) := by
  rw [show (2:ℕ) = 0+2 from rfl, pd_unfold]
  simp [pd_zero, pd_one]

/-- The continuant expansion along the first site:
`P_n(θ) = (E - v_0(θ)) P_{n-1}(θ+α) - P_{n-2}(θ+2α)`. -/
lemma pd_shift_first (α lam : ℝ) (E : ℂ) (ψ : ℝ) (n : ℕ) :
    pd α lam ψ E (n + 2) =
      (E - ((amoPot α lam ψ ((0:ℕ):ℤ) : ℝ) : ℂ)) * pd α lam (ψ + α) E (n + 1)
        - pd α lam (ψ + 2 * α) E n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · -- n = 0
      show pd α lam ψ E (0+2) = (E - ((amoPot α lam ψ ((0:ℕ):ℤ) : ℝ) : ℂ)) * pd α lam (ψ + α) E (0+1)
        - pd α lam (ψ + 2 * α) E 0
      rw [pd_unfold]
      have e : (0:ℕ) + 1 = 1 := by omega
      simp only [e, pd_one, pd_zero]
    rcases n with _ | m
    · -- n = 0 + 1
      have h1 : amoPot α lam (ψ + α) ((0:ℕ):ℤ) = amoPot α lam ψ ((1:ℕ):ℤ) :=
        amoPot_plus_one_phase α lam ψ 0
      show pd α lam ψ E (1+2) = (E - ((amoPot α lam ψ ((0:ℕ):ℤ) : ℝ) : ℂ)) * pd α lam (ψ + α) E (1+1)
        - pd α lam (ψ + 2 * α) E 1
      rw [show (1:ℕ)+1 = 0+2 from rfl] at *
      rw [pd, pd]
      simp only [pd, h1]
      ring
    · -- n = m + 1 + 1
      have ih1 : pd α lam ψ E (m+1+1+1) =
          (E - ((amoPot α lam ψ ((0:ℕ):ℤ) : ℝ) : ℂ)) * pd α lam (ψ+α) E (m+1+1)
            - pd α lam (ψ+2*α) E (m+1) := by
        have h := ih (m+1) (by omega)
        rw [show (m+1)+2 = m+1+1+1 by omega, show (m+1)+1 = m+1+1 by omega] at h
        exact h
      have ih0 : pd α lam ψ E (m+1+1) =
          (E - ((amoPot α lam ψ ((0:ℕ):ℤ) : ℝ) : ℂ)) * pd α lam (ψ+α) E (m+1)
            - pd α lam (ψ+2*α) E m := by
        have h := ih m (by omega)
        rw [show m+2 = m+1+1 by omega] at h
        exact h
      have hR1 : pd α lam (ψ+α) E (m+1+1+1) =
          (E - ((amoPot α lam (ψ+α) ((m+1:ℕ):ℤ) : ℝ) : ℂ)) * pd α lam (ψ+α) E (m+1+1)
            - pd α lam (ψ+α) E (m+1) := by
        rw [show m+1+1+1 = (m+1)+2 by omega, pd_unfold]
      have hR2 : pd α lam (ψ+2*α) E (m+1+1) =
          (E - ((amoPot α lam (ψ+2*α) ((m:ℕ):ℤ) : ℝ) : ℂ)) * pd α lam (ψ+2*α) E (m+1)
            - pd α lam (ψ+2*α) E m := by
        rw [show m+1+1 = m+2 by omega, pd_unfold]
      rw [pd_unfold, ih1, ih0, hR1, hR2]
      rw [amoPot_plus_one_phase, amoPot_plus_two_phase]
      ring


/-! ## The two boundary columns of the Dirichlet Green's function -/

noncomputable section

/-- The backward continuants of the potential sequence starting at `φ`: `pdVecB n k` is the
continuant of the suffix `v_{k+1}, …, v_{n-1}` (with the two boundary cases definitional). -/
def pdVecB (α lam : ℝ) (φ : ℝ) (E : ℂ) (n : ℕ) : ℕ → ℂ
  | 0 => pd α lam (φ + α) E n
  | (k+1) => pd α lam (φ + ((k:ℝ) + 2) * α) E (n - (k+1))

/-- The forward continuants: `pdVecF n i = pd φ E (i+1)`, the leading principal minors. -/
def pdVecF (α lam : ℝ) (φ : ℝ) (E : ℂ) (n : ℕ) : Fin n → ℂ :=
  fun i => pd α lam φ E ((i:ℕ) + 1)

lemma pdVecB_phase (α lam : ℝ) (φ : ℝ) (E : ℂ) (n k : ℕ) :
    pdVecB α lam φ E n k = pd α lam (φ + ((k:ℝ) + 1) * α) E (n - k) := by
  cases k with
  | zero => simp [pdVecB]
  | succ k =>
      simp only [pdVecB]
      congr 1
      push_cast
      ring

/-- **The first column of the inverse of the Dirichlet matrix.**  The vector
`r ↦ -pdVecB n r` is mapped by `dirMat` to `pd φ E (n+1)` times the first basis vector: the
interior rows are the continuant recurrence for the suffix continuants, and the boundary
rows are the convention `pd 0 = 0` and the identity `pd_shift_first`. -/
theorem pdVecB_mulVec_entry (α lam : ℝ) (φ : ℝ) (E : ℂ) (n k : ℕ) (hk : k < n) :
    ((dirMat α lam φ E n).mulVec (fun r : Fin n => - pdVecB α lam φ E n (r:ℕ))) ⟨k, hk⟩ =
      if k = 0 then pd α lam φ E (n+1) else 0 := by
  rw [dirMat_mulVec_entry]
  by_cases hk0 : k = 0
  · -- first row
    subst hk0
    rw [if_pos rfl]
    have hlow : (if h : 0 < (0:ℕ) then - pdVecB α lam φ E n ((0:ℕ) - 1) else 0) = 0 := by
      rw [dif_neg (by omega)]
    have hn1 : 1 ≤ n := by omega
    have hps := pd_shift_first α lam E φ (n-1)
    rw [show n-1+2 = n+1 by omega, show n-1+1 = n by omega] at hps
    have hQ1 : pdVecB α lam φ E n ((0:ℕ)+1) = pd α lam (φ + 2*α) E (n-1) := by
      show pd α lam (φ + (((0:ℕ):ℝ) + 2) * α) E (n - ((0:ℕ)+1)) = pd α lam (φ + 2*α) E (n-1)
      rw [show (((0:ℕ):ℝ) + 2) * α = 2*α by norm_num]
    rw [hlow, add_zero]
    by_cases h1n : (0:ℕ) + 1 < n
    · rw [dif_pos h1n, hQ1, hps]
      rw [show pdVecB α lam φ E n 0 = pd α lam (φ + α) E n from rfl]
      ring
    · rw [dif_neg h1n]
      have hn : n = 1 := by omega
      have hp1 : pd α lam (φ + α) E n = 1 := by rw [hn, pd_one]
      have hp2 : pd α lam φ E (n+1) = E - ((amoPot α lam φ ((0:ℕ):ℤ) : ℝ) : ℂ) := by
        rw [hn, show (1:ℕ)+1 = 2 by omega, pd_two]
      rw [show pdVecB α lam φ E n 0 = pd α lam (φ + α) E n from rfl, hp1, hp2]
      ring
  · rw [if_neg hk0]
    have hkpos : 0 < k := by omega
    by_cases hlast : k + 1 = n
    · -- last row
      rw [dif_neg (by omega : ¬ k + 1 < n), dif_pos hkpos]
      have hni : n - k = 1 := by omega
      have hQ : pdVecB α lam φ E n k = 1 := by
        rw [pdVecB_phase, hni, pd_one]
      have hQm : pdVecB α lam φ E n (k - 1)
          = E - ((amoPot α lam φ (k:ℤ) : ℝ) : ℂ) := by
        rw [pdVecB_phase]
        have e1 : ((k - 1 : ℕ):ℝ) + 1 = (k:ℝ) := by
          rw [Nat.cast_sub (by omega : (1:ℕ) ≤ k)]
          ring
        have e2 : n - (k - 1) = 2 := by omega
        rw [e1, e2, pd_two, amoPot_self_shift_nat]
      rw [hQ, hQm]
      ring
    · -- interior
      have hlt : k + 1 < n := by omega
      rw [dif_pos hlt, dif_pos hkpos]
      have hQi : pdVecB α lam φ E n k
          = pd α lam (φ + ((k:ℝ)+1)*α) E (n - k) := pdVecB_phase ..
      have hQip : pdVecB α lam φ E n (k+1)
          = pd α lam (φ + ((k:ℝ)+2)*α) E (n - (k+1)) := rfl
      have hQim : pdVecB α lam φ E n (k-1)
          = pd α lam (φ + (k:ℝ)*α) E (n - k + 1) := by
        rw [pdVecB_phase]
        have e1 : ((k - 1 : ℕ):ℝ) + 1 = (k:ℝ) := by
          rw [Nat.cast_sub (by omega : (1:ℕ) ≤ k)]
          ring
        have e2 : n - (k - 1) = n - k + 1 := by omega
        rw [e1, e2]
      have e3 : n - (k+1) = n - k - 1 := by omega
      have hps := pd_shift_first α lam E (φ + (k:ℝ) * α) (n - k - 1)
      rw [show (n - k - 1) + 2 = n - k + 1 by omega,
          show (n - k - 1) + 1 = n - k by omega,
          show φ + (k:ℝ)*α + α = φ + ((k:ℝ)+1)*α by ring,
          show φ + (k:ℝ)*α + 2*α = φ + ((k:ℝ)+2)*α by ring,
          amoPot_self_shift_nat] at hps
      rw [hQi, hQip, e3, hQim, hps]
      ring

/-- **The last column of the inverse of the Dirichlet matrix**: the forward continuant
vector solves `dirMat *ᵥ x = -pd φ E (n+1) · e_{last}`. -/
theorem pdVecF_mulVec_entry (α lam : ℝ) (φ : ℝ) (E : ℂ) (n : ℕ) (hn : 0 < n) (i : Fin n) :
    ((dirMat α lam φ E n).mulVec (pdVecF α lam φ E n)) i =
      if (i:ℕ) = n - 1 then - pd α lam φ E (n+1) else 0 := by
  have hrec : ∀ k : ℕ,
      (((amoPot α lam φ (k : ℤ) : ℝ) : ℂ) - E) * pd α lam φ E (k + 1) + pd α lam φ E k
        = - pd α lam φ E (k + 2) := by
    intro k
    rw [pd_unfold]
    ring
  have hlow : (if h : 0 < (i : ℕ) then pd α lam φ E ((i : ℕ) - 1 + 1) else 0)
      = pd α lam φ E (i : ℕ) := by
    by_cases h : 0 < (i : ℕ)
    · rw [dif_pos h]
      congr 1
      omega
    · rw [dif_neg h]
      have h0 : (i : ℕ) = 0 := by omega
      rw [h0]
      simp [pd_zero]
  rw [dirMat_mulVec_entry]
  simp only [pdVecF]
  by_cases hi : (i : ℕ) = n - 1
  · have hup : ¬ ((i : ℕ) + 1 < n) := by omega
    rw [if_pos hi, dif_neg hup, hlow, hi]
    simp only [add_zero]
    have h2 := hrec (n - 1)
    rw [show n - 1 + 2 = n + 1 by omega] at h2
    exact h2
  · have hup : (i : ℕ) + 1 < n := by omega
    rw [if_neg hi, dif_pos hup, hlow]
    have h2 := hrec (i : ℕ)
    rw [show ((i : ℕ) + 1) + 1 = (i : ℕ) + 2 by omega]
    linear_combination h2

/-- `pd φ E (n+1) ≠ 0` whenever the Dirichlet matrix is invertible: the forward continuant
vector is non-zero in its first coordinate and lies in the kernel of `dirMat` when
`pd φ E (n+1) = 0`. -/
lemma pd_ne_zero_of_det_ne_zero {α lam φ : ℝ} {E : ℂ} {n : ℕ} (hn : 0 < n)
    (hdet : (dirMat α lam φ E n).det ≠ 0) : pd α lam φ E (n+1) ≠ 0 := by
  intro h0
  have hzero : (dirMat α lam φ E n).mulVec (pdVecF α lam φ E n) = 0 := by
    funext r
    rw [pdVecF_mulVec_entry α lam φ E n hn, h0]
    split <;> simp
  have h1 : (pdVecF α lam φ E n) ⟨0, hn⟩ = 0 :=
    congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet hzero) ⟨0, hn⟩
  have h2 : (pdVecF α lam φ E n) ⟨0, hn⟩ = 1 := by
    simp only [pdVecF]
    rw [show (0:ℕ) + 1 = 1 by omega, pd_one]
  rw [h2] at h1
  exact one_ne_zero h1

/-- **First column of the inverse of the Dirichlet matrix.** -/
theorem dirMat_inv_firstCol {α lam φ : ℝ} {E : ℂ} {n : ℕ}
    (hdet : (dirMat α lam φ E n).det ≠ 0)
    (j : Fin n) (hj : (j:ℕ) = 0) (i : Fin n) :
    ((dirMat α lam φ E n)⁻¹) i j =
      - (pd α lam (φ + (((i:ℕ):ℝ) + 1) * α) E (n - (i:ℕ))) / (pd α lam φ E (n+1)) := by
  have hn : 0 < n := by have := i.isLt; omega
  have hunit : IsUnit (dirMat α lam φ E n).det := isUnit_iff_ne_zero.mpr hdet
  have hkernel : ∀ v : Fin n → ℂ, (dirMat α lam φ E n).mulVec v = 0 → v = 0 :=
    fun v hv => Matrix.eq_zero_of_mulVec_eq_zero hdet hv
  have hpd : pd α lam φ E (n+1) ≠ 0 := pd_ne_zero_of_det_ne_zero hn hdet
  have hw : (dirMat α lam φ E n).mulVec (fun r : Fin n => - pdVecB α lam φ E n (r:ℕ))
      = pd α lam φ E (n+1) • (Pi.single j 1) := by
    funext r
    rw [pdVecB_mulVec_entry α lam φ E n (r:ℕ) r.isLt]
    by_cases hr : (r:ℕ) = 0
    · have hrj : r = j := Fin.ext (by rw [hr, hj])
      rw [if_pos hr, hrj, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    · have hrj : r ≠ j := fun hh => hr (by rw [hh, hj])
      rw [if_neg hr, Pi.smul_apply, Pi.single_eq_of_ne hrj, smul_zero]
  have hmul_s : (dirMat α lam φ E n).mulVec
      (fun r : Fin n => - (pdVecB α lam φ E n (r:ℕ) / pd α lam φ E (n+1))) = Pi.single j 1 := by
    have hs_eq : (fun r : Fin n => - (pdVecB α lam φ E n (r:ℕ) / pd α lam φ E (n+1)))
        = ((pd α lam φ E (n+1))⁻¹) • (fun r : Fin n => - pdVecB α lam φ E n (r:ℕ)) := by
      funext r
      simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
      ring
    rw [hs_eq, Matrix.mulVec_smul, hw, smul_smul, inv_mul_cancel₀ hpd, one_smul]
  have hkey : (dirMat α lam φ E n)⁻¹.mulVec (Pi.single j 1)
      = (fun r : Fin n => - (pdVecB α lam φ E n (r:ℕ) / pd α lam φ E (n+1))) := by
    have h2 : (dirMat α lam φ E n).mulVec
        ((dirMat α lam φ E n)⁻¹.mulVec (Pi.single j 1)) = Pi.single j 1 := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
    have h3 : (dirMat α lam φ E n).mulVec
        ((dirMat α lam φ E n)⁻¹.mulVec (Pi.single j 1)
          - (fun r : Fin n => - (pdVecB α lam φ E n (r:ℕ) / pd α lam φ E (n+1)))) = 0 := by
      rw [Matrix.mulVec_sub, h2, hmul_s, sub_self]
    exact sub_eq_zero.mp (hkernel _ h3)
  have hcoord : ((dirMat α lam φ E n)⁻¹) i j
      = ((dirMat α lam φ E n)⁻¹.mulVec (Pi.single j 1)) i := by
    rw [Matrix.mulVec_single_one, Matrix.col_apply]
  rw [hcoord, hkey]
  simp only [pdVecB_phase, neg_div]

/-- **Last column of the inverse of the Dirichlet matrix.** -/
theorem dirMat_inv_lastCol' {α lam φ : ℝ} {E : ℂ} {n : ℕ}
    (hdet : (dirMat α lam φ E n).det ≠ 0)
    (j : Fin n) (hj : (j:ℕ) = n - 1) (i : Fin n) :
    ((dirMat α lam φ E n)⁻¹) i j =
      - (pd α lam φ E ((i:ℕ)+1) / pd α lam φ E (n+1)) := by
  have hn : 0 < n := by omega
  have hunit : IsUnit (dirMat α lam φ E n).det := isUnit_iff_ne_zero.mpr hdet
  have hkernel : ∀ v : Fin n → ℂ, (dirMat α lam φ E n).mulVec v = 0 → v = 0 :=
    fun v hv => Matrix.eq_zero_of_mulVec_eq_zero hdet hv
  have hpd : pd α lam φ E (n+1) ≠ 0 := pd_ne_zero_of_det_ne_zero hn hdet
  have hw : (dirMat α lam φ E n).mulVec (pdVecF α lam φ E n)
      = (-(pd α lam φ E (n+1))) • (Pi.single j 1) := by
    funext r
    rw [pdVecF_mulVec_entry α lam φ E n hn r]
    by_cases hr : (r:ℕ) = n - 1
    · have hrj : r = j := Fin.ext (by rw [hr, hj])
      rw [if_pos hr, hrj, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    · have hrj : r ≠ j := fun hh => hr (by rw [hh, hj])
      rw [if_neg hr, Pi.smul_apply, Pi.single_eq_of_ne hrj, smul_zero]
  have hmul_s : (dirMat α lam φ E n).mulVec
      (fun r : Fin n => - (pd α lam φ E ((r:ℕ)+1) / pd α lam φ E (n+1))) = Pi.single j 1 := by
    have hs_eq : (fun r : Fin n => - (pd α lam φ E ((r:ℕ)+1) / pd α lam φ E (n+1)))
        = ((-(pd α lam φ E (n+1)))⁻¹) • (pdVecF α lam φ E n) := by
      funext r
      simp only [pdVecF, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
      ring
    rw [hs_eq, Matrix.mulVec_smul, hw, smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr hpd), one_smul]
  have hkey : (dirMat α lam φ E n)⁻¹.mulVec (Pi.single j 1)
      = (fun r : Fin n => - (pd α lam φ E ((r:ℕ)+1) / pd α lam φ E (n+1))) := by
    have h2 : (dirMat α lam φ E n).mulVec
        ((dirMat α lam φ E n)⁻¹.mulVec (Pi.single j 1)) = Pi.single j 1 := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
    have h3 : (dirMat α lam φ E n).mulVec
        ((dirMat α lam φ E n)⁻¹.mulVec (Pi.single j 1)
          - (fun r : Fin n => - (pd α lam φ E ((r:ℕ)+1) / pd α lam φ E (n+1)))) = 0 := by
      rw [Matrix.mulVec_sub, h2, hmul_s, sub_self]
    exact sub_eq_zero.mp (hkernel _ h3)
  have hcoord : ((dirMat α lam φ E n)⁻¹) i j
      = ((dirMat α lam φ E n)⁻¹.mulVec (Pi.single j 1)) i := by
    rw [Matrix.mulVec_single_one, Matrix.col_apply]
  rw [hcoord, hkey]


/-- The Dirichlet Green's function is the corresponding entry of the inverse of the
Dirichlet matrix, for indices strictly inside the interval. -/
lemma G_eq_inv_entry {α lam θ : ℝ} {E : ℂ} {x₁ x₂ y z : ℤ}
    (hy : (y - x₁).toNat < (x₂ - x₁ + 1).toNat)
    (hz : (z - x₁).toNat < (x₂ - x₁ + 1).toNat) :
    G α lam θ E x₁ x₂ y z
      = (dirMat α lam (θ + (x₁:ℝ)*α) E ((x₂-x₁+1).toNat))⁻¹
          ⟨(y-x₁).toNat, hy⟩ ⟨(z-x₁).toNat, hz⟩ := by
  rw [G, greenEntry, dif_pos ⟨hy, hz⟩]

/-- The `inverse` of a singular square matrix is zero, entrywise. -/
lemma matrix_inv_apply_eq_zero_of_det_eq_zero {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (h : M.det = 0) (i j : Fin n) : M⁻¹ i j = 0 := by
  rw [Matrix.inv_def, h]
  simp

theorem green_bound_notA {α lam : ℝ} {E : ℂ} {θ r L ε₁ : ℝ} {k : ℕ} {x₁ x₂ y : ℤ}
    (hbd : ∀ n : ℕ, n ≤ k → ∀ ζ : ℝ, ‖Work.TMC16Core.pd α lam ζ E (n + 1)‖ ≤
        Real.exp ((n : ℝ) * (L + ε₁)))
    (hx : x₂ = x₁ + (k : ℤ) - 1) (h1 : x₁ ≤ y) (h2 : y ≤ x₂)
    (hnot : Real.exp (((k : ℝ) + 1) * r) <
        ‖Work.TMC16Core.pd α lam (θ + (x₁ : ℝ) * α) E (k + 1)‖) :
    ‖Work.TMC16Core.G α lam θ E x₁ x₂ y x₁‖ <
        Real.exp ((L + ε₁) * ((x₂ - y : ℤ) : ℝ) - ((k : ℝ) + 1) * r) ∧
      ‖Work.TMC16Core.G α lam θ E x₁ x₂ y x₂‖ <
        Real.exp ((L + ε₁) * ((y - x₁ : ℤ) : ℝ) - ((k : ℝ) + 1) * r) := by
  obtain ⟨htn, htn1, hy_le, hxy_le, hlen, hy_cast, hxy_cast, hx1x1⟩ :=
    toNat_interval_facts hx h1 h2
  have hkpos : 0 < k := by omega
  have hyx1_lt : (y - x₁).toNat < (x₂ - x₁ + 1).toNat := by
    have hyz : ((y - x₁).toNat : ℤ) = y - x₁ := Int.toNat_of_nonneg (by omega)
    have hxz : ((x₂ - x₁).toNat : ℤ) = x₂ - x₁ := Int.toNat_of_nonneg (by omega)
    have hle : (y - x₁).toNat ≤ (x₂ - x₁).toNat := by
      have h2' : ((y - x₁).toNat : ℤ) ≤ ((x₂ - x₁).toNat : ℤ) := by rw [hyz, hxz]; omega
      omega
    have hle2 : (y - x₁).toNat ≤ k - 1 := by rw [← htn1]; exact hle
    rw [htn]
    omega
  have hx2x1_lt : (x₂ - x₁).toNat < (x₂ - x₁ + 1).toNat := by
    rw [htn, htn1]; omega
  have hx1x1_lt : (x₁ - x₁).toNat < (x₂ - x₁ + 1).toNat := by
    rw [hx1x1, htn]; omega
  have hG1 := G_eq_inv_entry (α := α) (lam := lam) (θ := θ) (E := E) (x₁ := x₁) (x₂ := x₂)
    (y := y) (z := x₁) hyx1_lt hx1x1_lt
  have hG2 := G_eq_inv_entry (α := α) (lam := lam) (θ := θ) (E := E) (x₁ := x₁) (x₂ := x₂)
    (y := y) (z := x₂) hyx1_lt hx2x1_lt
  have hden1 : (x₂-x₁+1).toNat + 1 = k + 1 := by rw [htn]
  constructor
  · rw [hG1]
    by_cases hdet : (dirMat α lam (θ + (x₁:ℝ)*α) E ((x₂-x₁+1).toNat)).det = 0
    · rw [matrix_inv_apply_eq_zero_of_det_eq_zero hdet]
      simp only [norm_zero]
      exact Real.exp_pos _
    · have hcol := dirMat_inv_firstCol (α := α) (lam := lam) (φ := θ + (x₁:ℝ)*α) (E := E)
        hdet ⟨(x₁-x₁).toNat, hx1x1_lt⟩ hx1x1 ⟨(y-x₁).toNat, hyx1_lt⟩
      rw [hcol]
      have hph : θ + (x₁:ℝ)*α + (((y-x₁).toNat : ℝ) + 1) * α = θ + ((y:ℝ) + 1) * α := by
        rw [hy_cast]; push_cast; ring
      have hlen1 : (x₂-x₁+1).toNat - (y-x₁).toNat = (x₂-y).toNat + 1 := by
        rw [htn]; exact hlen
      rw [hph, hlen1, hden1, norm_div, norm_neg]
      have hnum : ‖pd α lam (θ + ((y:ℝ) + 1) * α) E ((x₂-y).toNat + 1)‖
          ≤ Real.exp (((x₂-y : ℤ) : ℝ) * (L + ε₁)) := by
        have h := hbd (x₂-y).toNat hxy_le (θ + ((y:ℝ) + 1) * α)
        rwa [hxy_cast] at h
      have hthis : ‖pd α lam (θ + ((y:ℝ) + 1) * α) E ((x₂-y).toNat + 1)‖
            / ‖pd α lam (θ + (x₁:ℝ)*α) E (k + 1)‖
          < Real.exp (((x₂-y : ℤ) : ℝ) * (L + ε₁) - ((k:ℝ) + 1) * r) :=
        div_lt_exp_sub hnot (norm_nonneg _) hnum
      rwa [show ((x₂ - y : ℤ) : ℝ) * (L + ε₁) - ((k:ℝ) + 1) * r
          = (L + ε₁) * ((x₂ - y : ℤ) : ℝ) - ((k:ℝ) + 1) * r by ring] at hthis
  · rw [hG2]
    by_cases hdet : (dirMat α lam (θ + (x₁:ℝ)*α) E ((x₂-x₁+1).toNat)).det = 0
    · rw [matrix_inv_apply_eq_zero_of_det_eq_zero hdet]
      simp only [norm_zero]
      exact Real.exp_pos _
    · have hj2 : ((⟨(x₂-x₁).toNat, hx2x1_lt⟩ : Fin (x₂-x₁+1).toNat) : ℕ) = (x₂-x₁+1).toNat - 1 := by
        show (x₂ - x₁).toNat = (x₂ - x₁ + 1).toNat - 1
        rw [htn, htn1]
      have hcol := dirMat_inv_lastCol' (α := α) (lam := lam) (φ := θ + (x₁:ℝ)*α) (E := E)
        hdet ⟨(x₂-x₁).toNat, hx2x1_lt⟩ hj2 ⟨(y-x₁).toNat, hyx1_lt⟩
      rw [hcol, hden1, norm_neg, norm_div]
      have hnum : ‖pd α lam (θ + (x₁:ℝ)*α) E ((y-x₁).toNat + 1)‖
          ≤ Real.exp (((y-x₁ : ℤ) : ℝ) * (L + ε₁)) := by
        have h := hbd (y-x₁).toNat hy_le (θ + (x₁:ℝ)*α)
        rwa [hy_cast] at h
      have hthis : ‖pd α lam (θ + (x₁:ℝ)*α) E ((y-x₁).toNat + 1)‖
            / ‖pd α lam (θ + (x₁:ℝ)*α) E (k + 1)‖
          < Real.exp (((y-x₁ : ℤ) : ℝ) * (L + ε₁) - ((k:ℝ) + 1) * r) :=
        div_lt_exp_sub hnot (norm_nonneg _) hnum
      rwa [show ((y - x₁ : ℤ) : ℝ) * (L + ε₁) - ((k:ℝ) + 1) * r
          = (L + ε₁) * ((y - x₁ : ℤ) : ℝ) - ((k:ℝ) + 1) * r by ring] at hthis

end

end Work.TMC16Core.Basic
