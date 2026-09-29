import Mathlib
import Submission.Work.TMContract.Components
import Submission.Work.TMPuig.Defs
import Submission.Work.TMPuig.FourierAux
import Submission.Work.TMPuig.dual_recurrence
import Submission.Work.TMPuig.dual_cF_vanishing
import Submission.Work.TMPuig.dual_cF_tendsto_zero

open MeasureTheory Filter intervalIntegral Set Matrix
open scoped Real

noncomputable section

namespace Work.TMPuig


/-! ## 1. The elementary sequence lemma

Two bi-infinite sequences satisfying the same symmetric three-term recurrence whose
initial data are proportional are proportional. -/

/-- Forward uniqueness: a sequence satisfying `s (n+1) + s (n-1) = R n * s n` and vanishing at
`0` and `1` vanishes on `ℕ`. -/
theorem seq_fwd_zero {R : ℤ → ℂ} {s : ℤ → ℂ}
    (hs : ∀ n : ℤ, s (n + 1) + s (n - 1) = R n * s n) (h0 : s 0 = 0) (h1 : s 1 = 0) :
    ∀ m : ℕ, s (m : ℤ) = 0 := by
  have hstep : ∀ n : ℤ, s (n + 1) = R n * s n - s (n - 1) := by
    intro n
    have h := hs n
    rw [← h]
    ring
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | _ | k
    · simpa using h0
    · simpa using h1
    · have hk1 : s ((k : ℤ) + 1) = 0 := by
        have h := ih (k + 1) (by omega)
        simpa using h
      have hk0 : s ((k : ℤ)) = 0 := by
        have h := ih k (by omega)
        simpa using h
      have hstep' : s ((k : ℤ) + 1 + 1) = R ((k : ℤ) + 1) * s ((k : ℤ) + 1) - s (k : ℤ) := by
        have h := hstep ((k : ℤ) + 1)
        simpa using h
      rw [show (((k + 1 + 1 : ℕ)) : ℤ) = (k : ℤ) + 1 + 1 by push_cast; ring,
        hstep', hk1, hk0]
      ring

/-- A sequence satisfying `s (n+1) + s (n-1) = R n * s n` and vanishing at `0` and `1` vanishes
identically. -/
theorem seq_zero_of_data_zero {R : ℤ → ℂ} {s : ℤ → ℂ}
    (hs : ∀ n : ℤ, s (n + 1) + s (n - 1) = R n * s n) (h0 : s 0 = 0) (h1 : s 1 = 0) :
    ∀ n : ℤ, s n = 0 := by
  have hm1 : s (-1) = 0 := by
    have h := hs 0
    rw [zero_add, h0, mul_zero, h1, zero_add] at h
    exact h
  have hneg : ∀ m : ℕ, s (-(m : ℤ)) = 0 := by
    have ht : ∀ n : ℤ, (fun m : ℤ => s (-m)) (n + 1) + (fun m : ℤ => s (-m)) (n - 1)
        = (fun n : ℤ => R (-n)) n * (fun m : ℤ => s (-m)) n := by
      intro n
      have h := hs (-n)
      have e1 : -((n : ℤ) + 1) = -n - 1 := by ring
      have e2 : -((n : ℤ) - 1) = -n + 1 := by ring
      show s (-(n + 1)) + s (-(n - 1)) = R (-n) * s (-n)
      rw [e1, e2, add_comm]
      exact h
    refine seq_fwd_zero (R := fun n : ℤ => R (-n)) (s := fun m : ℤ => s (-m)) ht ?_ ?_
    · simpa using h0
    · simpa using hm1
  intro n
  by_cases hn : 0 ≤ n
  · have hn' : n = ((n.toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg hn).symm
    rw [hn']
    exact seq_fwd_zero hs h0 h1 n.toNat
  · have hn' : n = -((( -n).toNat : ℕ) : ℤ) := by
      have h1' : (((-n).toNat : ℕ) : ℤ) = -n := Int.toNat_of_nonneg (by omega)
      omega
    rw [hn']
    exact hneg ((-n).toNat)

/-- Two sequences satisfying the same three-term recurrence with proportional initial data, the
second of which is not identically zero, are proportional. -/
theorem seq_dependent_of_data {R : ℤ → ℂ} {cc dd : ℤ → ℂ}
    (hc : ∀ n : ℤ, cc (n + 1) + cc (n - 1) = R n * cc n)
    (hd : ∀ n : ℤ, dd (n + 1) + dd (n - 1) = R n * dd n)
    (hw : cc 1 * dd 0 = cc 0 * dd 1) (hne : ∃ k : ℤ, dd k ≠ 0) :
    ∃ γ : ℂ, ∀ n : ℤ, cc n = γ * dd n := by
  have key : ∀ γ : ℂ, cc 0 = γ * dd 0 → cc 1 = γ * dd 1 → ∀ n : ℤ, cc n = γ * dd n := by
    intro γ h0 h1 n
    have he : ∀ n : ℤ, (fun m : ℤ => cc m - γ * dd m) (n + 1)
          + (fun m : ℤ => cc m - γ * dd m) (n - 1)
        = R n * (fun m : ℤ => cc m - γ * dd m) n := by
      intro n
      show cc (n + 1) - γ * dd (n + 1) + (cc (n - 1) - γ * dd (n - 1))
        = R n * (cc n - γ * dd n)
      rw [show cc (n + 1) - γ * dd (n + 1) + (cc (n - 1) - γ * dd (n - 1))
          = (cc (n + 1) + cc (n - 1)) - γ * (dd (n + 1) + dd (n - 1)) by ring, hc n, hd n]
      ring
    have he0 : (fun m : ℤ => cc m - γ * dd m) 0 = 0 := by
      show cc 0 - γ * dd 0 = 0
      rw [h0]; ring
    have he1 : (fun m : ℤ => cc m - γ * dd m) 1 = 0 := by
      show cc 1 - γ * dd 1 = 0
      rw [h1]; ring
    exact sub_eq_zero.mp
      (seq_zero_of_data_zero (R := R) (s := fun m : ℤ => cc m - γ * dd m) he he0 he1 n)
  by_cases h0 : dd 0 = 0
  · have h1 : dd 1 ≠ 0 := by
      by_contra hcon
      obtain ⟨k, hk⟩ := hne
      exact hk (seq_zero_of_data_zero hd h0 (by simpa using hcon) k)
    have hc0 : cc 0 = 0 := by
      have hw' : cc 1 * dd 0 = cc 0 * dd 1 := hw
      rw [h0, mul_zero] at hw'
      exact (mul_eq_zero.mp hw'.symm).resolve_right h1
    have hA : cc 0 = (cc 1 / dd 1) * dd 0 := by rw [hc0, h0, mul_zero]
    have hB : cc 1 = (cc 1 / dd 1) * dd 1 := by
      field_simp
    exact ⟨cc 1 / dd 1, fun n => key (cc 1 / dd 1) hA hB n⟩
  · have hA : cc 0 = (cc 0 / dd 0) * dd 0 := by rw [div_mul_cancel₀ _ h0]
    have hB : cc 1 = (cc 0 / dd 0) * dd 1 := by
      rw [div_mul_eq_mul_div, eq_div_iff h0]
      exact hw
    exact ⟨cc 0 / dd 0, fun n => key (cc 0 / dd 0) hA hB n⟩


/-! ## 2. The matrix part of the resonant argument

Given the resonant conjugacy `B (x + α) * S x = rot c * B x` with `c - l α ∈ ℤ`, the matrix
`T x = rot (-l x) * B x` conjugates the cocycle to the identity:
`T (x + α) * S x = T x`.  Hence `A x = T x⁻¹` provides a two-dimensional space of periodic
solutions of the cocycle, whose first coordinates solve the dual scalar equation. -/

section MatrixPart

/-- The conjugating matrix `T x = rot (-l x) * B x`. -/
def resT (l : ℤ) (B : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Work.TMContract.rot (-(l : ℝ) * x) * B x

/-- `A x = (T x)⁻¹`, expanded as the adjugate of `T x`; the two agree because `det (T x) = 1`. -/
def resA (l : ℤ) (B : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![resT l B x 1 1, -(resT l B x 0 1); -(resT l B x 1 0), resT l B x 0 0]

theorem resT_per {B : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (hper : ∀ x, B (x + 1) = B x)
    (l : ℤ) (x : ℝ) : resT l B (x + 1) = resT l B x := by
  have h1 : -(l : ℝ) * (x + 1) = -(l : ℝ) * x + (-(l : ℝ)) := by ring
  rw [resT, resT, h1, Work.TMPuig.rot_add]
  have h2 : Work.TMContract.rot (-(l : ℝ)) = 1 := by
    have h3 : (-(l : ℝ)) = ((-l : ℤ) : ℝ) := by push_cast; ring
    rw [h3, Work.TMPuig.rot_int]
  rw [h2, mul_one, hper x]

theorem resT_conj {α lam E c : ℝ} {B : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hconj : ∀ x, B (x + α) * Work.TMContract.tmR lam E x = Work.TMContract.rot c * B x)
    {l : ℤ} {m : ℤ} (hl : c - (l : ℝ) * α = (m : ℝ)) (x : ℝ) :
    resT l B (x + α) * Work.TMContract.tmR lam E x = resT l B x := by
  have harg : -(l : ℝ) * (x + α) + c = -(l : ℝ) * x + (m : ℝ) := by
    linear_combination hl
  simp only [resT]
  rw [mul_assoc, hconj x, ← mul_assoc, ← Work.TMPuig.rot_add, harg, Work.TMPuig.rot_add,
    Work.TMPuig.rot_int, mul_one]

theorem resT_det {B : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (hdet : ∀ x, (B x).det = 1)
    (l : ℤ) (x : ℝ) : (resT l B x).det = 1 := by
  rw [resT, Matrix.det_mul, Work.TMPuig.det_rot, hdet x, one_mul]

theorem resA_eq_adjugate (l : ℤ) (B : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ) :
    resA l B x = (resT l B x).adjugate := by
  rw [resA, Matrix.adjugate_fin_two]

theorem resA_det {B : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (hdet : ∀ x, (B x).det = 1)
    (l : ℤ) (x : ℝ) : (resA l B x).det = 1 := by
  rw [resA_eq_adjugate, Matrix.det_adjugate, resT_det hdet l x]
  norm_num

theorem resA_eq_inv {B : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (hdet : ∀ x, (B x).det = 1)
    (l : ℤ) (x : ℝ) : resA l B x = (resT l B x)⁻¹ := by
  rw [resA_eq_adjugate, Matrix.inv_def, resT_det hdet l x, Ring.inverse_one, one_smul]

theorem resA_per {B : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (hper : ∀ x, B (x + 1) = B x)
    (l : ℤ) (x : ℝ) : resA l B (x + 1) = resA l B x := by
  rw [resA, resA, resT_per hper l x]

theorem resT_cont {B : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hBc : ∀ i j, Continuous (fun x => B x i j)) (l : ℤ) (i j : Fin 2) :
    Continuous (fun x => resT l B x i j) := by
  simp only [resT, Matrix.mul_apply, Fin.sum_univ_two]
  apply Continuous.add <;> apply Continuous.mul
  · fin_cases i <;> simp only [Work.TMContract.rot] <;> fun_prop
  · exact hBc 0 j
  · fin_cases i <;> simp only [Work.TMContract.rot] <;> fun_prop
  · exact hBc 1 j

theorem resA_cont {B : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hBc : ∀ i j, Continuous (fun x => B x i j)) (l : ℤ) (i j : Fin 2) :
    Continuous (fun x => resA l B x i j) := by
  have hT := resT_cont hBc l
  fin_cases i <;> fin_cases j <;>
    simp only [resA, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val'] <;>
    first
      | exact hT 0 0
      | exact (hT 0 1).neg
      | exact (hT 1 0).neg
      | exact hT 1 1

theorem resA_conj {α lam E c : ℝ} {B : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hdet : ∀ x, (B x).det = 1)
    (hconj : ∀ x, B (x + α) * Work.TMContract.tmR lam E x = Work.TMContract.rot c * B x)
    {l : ℤ} {m : ℤ} (hl : c - (l : ℝ) * α = (m : ℝ)) (x : ℝ) :
    resA l B (x + α) = Work.TMContract.tmR lam E x * resA l B x := by
  have hinv : ∀ x, IsUnit (resT l B x).det := fun x => by
    rw [resT_det hdet l x]
    exact isUnit_one
  have hconj' : ∀ x, resT l B (x + α) * Work.TMContract.tmR lam E x = 1 * resT l B x := by
    intro x
    rw [resT_conj hconj hl x, one_mul]
  have h := Work.TMPuig.tmR_conj_step (B := resT l B) (R := 1) hinv hconj' x
  rw [resA_eq_inv hdet l (x + α), resA_eq_inv hdet l x, h, mul_one]

theorem resA_vec {α lam E c : ℝ} {B : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hdet : ∀ x, (B x).det = 1)
    (hconj : ∀ x, B (x + α) * Work.TMContract.tmR lam E x = Work.TMContract.rot c * B x)
    {l : ℤ} {m : ℤ} (hl : c - (l : ℝ) * α = (m : ℝ)) (v : Fin 2 → ℝ) (x : ℝ) :
    resA l B (x + α) *ᵥ v = Work.TMContract.tmR lam E x *ᵥ (resA l B x *ᵥ v) := by
  rw [resA_conj hdet hconj hl x, Matrix.mulVec_mulVec]

theorem resA_vec_per {B : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (hper : ∀ x, B (x + 1) = B x)
    (l : ℤ) (v : Fin 2 → ℝ) (x : ℝ) :
    resA l B (x + 1) *ᵥ v = resA l B x *ᵥ v := by
  rw [resA_per hper l x]

theorem resA_vec_cont {B : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hBc : ∀ i j, Continuous (fun x => B x i j)) (l : ℤ) (v : Fin 2 → ℝ) (j : Fin 2) :
    Continuous (fun x => (resA l B x *ᵥ v) j) := by
  have hc : Continuous (fun x => resA l B x j 0 * v 0 + resA l B x j 1 * v 1) :=
    ((resA_cont hBc l j 0).mul continuous_const).add
      ((resA_cont hBc l j 1).mul continuous_const)
  convert hc using 1
  funext x
  simp [Matrix.mulVec, Fin.sum_univ_two]

theorem tmR_mulVec_zero (a : ℝ) (w : Fin 2 → ℝ) :
    ((!![a, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ w) 0 = a * w 0 - w 1 := by
  conv_lhs => rw [show w = ![w 0, w 1] from by funext i; fin_cases i <;> rfl]
  simp [Matrix.mulVec, Fin.sum_univ_two]
  ring

theorem tmR_mulVec_one (a : ℝ) (w : Fin 2 → ℝ) :
    ((!![a, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ w) 1 = w 0 := by
  conv_lhs => rw [show w = ![w 0, w 1] from by funext i; fin_cases i <;> rfl]
  simp [Matrix.mulVec, Fin.sum_univ_two]

theorem resA_scalar {α lam E c : ℝ} {B : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hdet : ∀ x, (B x).det = 1)
    (hconj : ∀ x, B (x + α) * Work.TMContract.tmR lam E x = Work.TMContract.rot c * B x)
    {l : ℤ} {m : ℤ} (hl : c - (l : ℝ) * α = (m : ℝ)) (v : Fin 2 → ℝ) (x : ℝ) :
    (resA l B (x + α) *ᵥ v) 0 + (resA l B (x - α) *ᵥ v) 0
      = (E - 2 * lam * Real.cos (2 * Real.pi * x)) * (resA l B x *ᵥ v) 0 := by
  have h0 : ∀ y : ℝ, (resA l B (y + α) *ᵥ v) 0
      = (E - 2 * lam * Real.cos (2 * Real.pi * y)) * (resA l B y *ᵥ v) 0
        - (resA l B y *ᵥ v) 1 := by
    intro y
    rw [resA_vec hdet hconj hl v y]
    exact tmR_mulVec_zero (E - 2 * lam * Real.cos (2 * Real.pi * y)) (resA l B y *ᵥ v)
  have h1 : ∀ y : ℝ, (resA l B (y + α) *ᵥ v) 1 = (resA l B y *ᵥ v) 0 := by
    intro y
    rw [resA_vec hdet hconj hl v y]
    exact tmR_mulVec_one (E - 2 * lam * Real.cos (2 * Real.pi * y)) (resA l B y *ᵥ v)
  have heq : (x - α) + α = x := by ring
  rw [h0 x, ← h1 (x - α), heq]
  ring

end MatrixPart

/-! ## 3. The scalar theorem (assembly of the three Fourier lemmas) -/

/-- The characters have norm one. -/
theorem norm_chr (n : ℤ) (x : ℝ) : ‖chr n x‖ = 1 := by
  rw [chr, show 2 * Real.pi * Complex.I * ((n : ℝ) : ℂ) * (x : ℂ)
      = (((2 * Real.pi * (n : ℝ) * x : ℝ)) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- Coefficients are bounded by the `L¹` norm. -/
theorem cF_norm_le (f : ℝ → ℂ) (n : ℤ) :
    ‖cF f n‖ ≤ ∫ x in (0 : ℝ)..1, ‖f x‖ := by
  rw [cF]
  refine le_trans (intervalIntegral.norm_integral_le_integral_norm zero_le_one) (le_of_eq ?_)
  apply intervalIntegral.integral_congr
  intro x _
  simp only []
  rw [norm_mul, norm_chr, one_mul]

/-- A null sequence times a bounded sequence is null. -/
theorem tendsto_mul_of_bounded {a b : ℕ → ℂ} (ha : Filter.Tendsto a Filter.atTop (nhds 0))
    (C : ℝ) (hb : ∀ k, ‖b k‖ ≤ C) :
    Filter.Tendsto (fun k => a k * b k) Filter.atTop (nhds 0) := by
  have h2 : Filter.Tendsto (fun k => ‖a k‖ * C) Filter.atTop (nhds 0) := by
    simpa using ha.norm.mul_const C
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) h2
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hb k) (norm_nonneg _)

/-- **Two continuous `1`-periodic solutions of the dual almost Mathieu equation are
proportional.** -/
theorem dual_solutions_dependent {α lam E : ℝ} (hlam : lam ≠ 0) {u v : ℝ → ℂ}
    (hu : Continuous u) (hv : Continuous v)
    (hup : ∀ x, u (x + 1) = u x) (hvp : ∀ x, v (x + 1) = v x)
    (huq : ∀ x, u (x + α) + u (x - α) =
      ((E - 2 * lam * Real.cos (2 * Real.pi * x) : ℝ) : ℂ) * u x)
    (hvq : ∀ x, v (x + α) + v (x - α) =
      ((E - 2 * lam * Real.cos (2 * Real.pi * x) : ℝ) : ℂ) * v x)
    (hvne : v ≠ 0) : ∃ γ : ℂ, ∀ x, u x = γ * v x := by
  have hlamC : (lam : ℂ) ≠ 0 := by
    simpa using hlam
  have hc : ∀ n : ℤ, cF u (n + 1) + cF u (n - 1)
      = (((E : ℂ) - ((2 * Real.cos (2 * Real.pi * (n : ℝ) * α) : ℝ) : ℂ)) / (lam : ℂ)) * cF u n := by
    intro n
    have h := dual_recurrence hu hup huq n
    rw [div_mul_eq_mul_div, eq_div_iff hlamC]
    rw [mul_comm] at h
    exact h
  have hd : ∀ n : ℤ, cF v (n + 1) + cF v (n - 1)
      = (((E : ℂ) - ((2 * Real.cos (2 * Real.pi * (n : ℝ) * α) : ℝ) : ℂ)) / (lam : ℂ)) * cF v n := by
    intro n
    have h := dual_recurrence hv hvp hvq n
    rw [div_mul_eq_mul_div, eq_div_iff hlamC]
    rw [mul_comm] at h
    exact h
  have hWstep : ∀ k : ℤ,
      cF u (k + 1 + 1) * cF v (k + 1) - cF u (k + 1) * cF v (k + 1 + 1)
        = cF u (k + 1) * cF v k - cF u k * cF v (k + 1) := by
    intro k
    have h1 := hc (k + 1)
    have h2 := hd (k + 1)
    simp only [add_sub_cancel_right] at h1 h2
    linear_combination cF v (k + 1) * h1 - cF u (k + 1) * h2
  have hWconst : ∀ k : ℕ,
      cF u ((k : ℤ) + 1) * cF v (k : ℤ) - cF u (k : ℤ) * cF v ((k : ℤ) + 1)
        = cF u 1 * cF v 0 - cF u 0 * cF v 1 := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [show (((k + 1 : ℕ)) : ℤ) = (k : ℤ) + 1 by push_cast; ring]
      rw [hWstep (k : ℤ), ih]
  have hu_lim : Filter.Tendsto (fun k : ℕ => cF u (k : ℤ)) Filter.atTop (nhds 0) :=
    dual_cF_tendsto_zero hu hup
  have hv_lim : Filter.Tendsto (fun k : ℕ => cF v (k : ℤ)) Filter.atTop (nhds 0) :=
    dual_cF_tendsto_zero hv hvp
  have hu_lim' : Filter.Tendsto (fun k : ℕ => cF u ((k : ℤ) + 1)) Filter.atTop (nhds 0) := by
    have heq : (fun k : ℕ => cF u ((k : ℤ) + 1))
        = (fun k : ℕ => cF u (k : ℤ)) ∘ (fun a : ℕ => a + 1) := by
      funext k
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    rw [heq]
    exact hu_lim.comp (tendsto_add_atTop_nat 1)
  have hv_lim' : Filter.Tendsto (fun k : ℕ => cF v ((k : ℤ) + 1)) Filter.atTop (nhds 0) := by
    have heq : (fun k : ℕ => cF v ((k : ℤ) + 1))
        = (fun k : ℕ => cF v (k : ℤ)) ∘ (fun a : ℕ => a + 1) := by
      funext k
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    rw [heq]
    exact hv_lim.comp (tendsto_add_atTop_nat 1)
  have hbdd_v : ∀ k : ℕ, ‖cF v (k : ℤ)‖ ≤ ∫ x in (0 : ℝ)..1, ‖v x‖ := fun k => cF_norm_le v _
  have hbdd_v' : ∀ k : ℕ, ‖cF v ((k : ℤ) + 1)‖ ≤ ∫ x in (0 : ℝ)..1, ‖v x‖ :=
    fun k => cF_norm_le v _
  have hWlim : Filter.Tendsto
      (fun k : ℕ => cF u ((k : ℤ) + 1) * cF v (k : ℤ) - cF u (k : ℤ) * cF v ((k : ℤ) + 1))
      Filter.atTop (nhds 0) := by
    have h1 := tendsto_mul_of_bounded hu_lim' (∫ x in (0 : ℝ)..1, ‖v x‖) hbdd_v
    have h2 := tendsto_mul_of_bounded hu_lim (∫ x in (0 : ℝ)..1, ‖v x‖) hbdd_v'
    simpa using h1.sub h2
  have hW0 : cF u 1 * cF v 0 - cF u 0 * cF v 1 = 0 := by
    have h1 : (fun k : ℕ => cF u ((k : ℤ) + 1) * cF v (k : ℤ)
        - cF u (k : ℤ) * cF v ((k : ℤ) + 1))
        = fun _ => cF u 1 * cF v 0 - cF u 0 * cF v 1 := funext hWconst
    rw [h1] at hWlim
    exact (tendsto_nhds_unique hWlim tendsto_const_nhds).symm
  have hw : cF u 1 * cF v 0 = cF u 0 * cF v 1 := sub_eq_zero.mp hW0
  obtain ⟨k, hk⟩ : ∃ k : ℤ, cF v k ≠ 0 := by
    by_contra h
    push_neg at h
    exact hvne (funext (dual_cF_vanishing hv hvp h))
  obtain ⟨γ, hγ⟩ := seq_dependent_of_data hc hd hw ⟨k, hk⟩
  refine ⟨γ, fun x => ?_⟩
  have hvan : ∀ x, (fun y => u y - γ * v y) x = 0 := by
    refine dual_cF_vanishing (hu.sub (continuous_const.mul hv)) (fun x => ?_) (fun n => ?_)
    · show u (x + 1) - γ * v (x + 1) = u x - γ * v x
      rw [hup, hvp]
    · have hcoef : cF (fun y => u y - γ * v y) n = cF u n - γ * cF v n := by
        have h := cF_sub (f := u) (g := fun y => γ * v y) hu (continuous_const.mul hv) n
        rw [h, cF_const_mul]
      rw [hcoef, hγ n, sub_self]
  have := hvan x
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.zero_apply] at this
  exact sub_eq_zero.mp this


theorem resonant_false {α lam E c : ℝ} (hα : Irrational α) (hlam : lam ≠ 0)
    {B : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hB : ∀ i j, AnalyticOnNhd ℝ (fun x => B x i j) univ)
    (hper : ∀ x, B (x + 1) = B x) (hdet : ∀ x, (B x).det = 1)
    (hconj : ∀ x, B (x + α) * Work.TMContract.tmR lam E x = Work.TMContract.rot c * B x)
    (l : ℤ) (hl : ∃ m : ℤ, c - (l : ℝ) * α = (m : ℝ)) : False := by
  obtain ⟨m, hm⟩ := hl
  have hBc : ∀ i j, Continuous (fun x => B x i j) := fun i j =>
    continuousOn_univ.mp (hB i j).continuousOn
  set u₁ : ℝ → ℂ := fun x => (((resA l B x) *ᵥ ![1, 0]) 0 : ℂ) with hu₁
  set u₂ : ℝ → ℂ := fun x => (((resA l B x) *ᵥ ![0, 1]) 0 : ℂ) with hu₂
  have hu₁c : Continuous u₁ := by
    rw [hu₁]
    exact Complex.continuous_ofReal.comp (resA_vec_cont hBc l ![1, 0] 0)
  have hu₂c : Continuous u₂ := by
    rw [hu₂]
    exact Complex.continuous_ofReal.comp (resA_vec_cont hBc l ![0, 1] 0)
  have hu₁p : ∀ x, u₁ (x + 1) = u₁ x := by
    intro x
    rw [hu₁]
    simp only
    rw [resA_vec_per hper l ![1, 0] x]
  have hu₂p : ∀ x, u₂ (x + 1) = u₂ x := by
    intro x
    rw [hu₂]
    simp only
    rw [resA_vec_per hper l ![0, 1] x]
  have hu₁q : ∀ x, u₁ (x + α) + u₁ (x - α)
      = ((E - 2 * lam * Real.cos (2 * Real.pi * x) : ℝ) : ℂ) * u₁ x := by
    intro x
    rw [hu₁]
    simp only
    rw [← Complex.ofReal_add, resA_scalar hdet hconj hm ![1, 0] x, ← Complex.ofReal_mul]
  have hu₂q : ∀ x, u₂ (x + α) + u₂ (x - α)
      = ((E - 2 * lam * Real.cos (2 * Real.pi * x) : ℝ) : ℂ) * u₂ x := by
    intro x
    rw [hu₂]
    simp only
    rw [← Complex.ofReal_add, resA_scalar hdet hconj hm ![0, 1] x, ← Complex.ofReal_mul]
  have hu₂ne : u₂ ≠ 0 := by
    intro hzero
    have h0 : ∀ x, (resA l B x *ᵥ ![0, 1]) 0 = 0 := by
      intro x
      have h := congrFun hzero x
      rw [hu₂] at h
      simp only [Pi.zero_apply] at h
      exact_mod_cast h
    have h1 : ∀ x, (resA l B x *ᵥ ![0, 1]) 1 = 0 := by
      intro x
      have hv := resA_vec hdet hconj hm ![0, 1] (x - α)
      rw [show (x - α) + α = x by ring] at hv
      have hone : (Work.TMContract.tmR lam E (x - α) *ᵥ (resA l B (x - α) *ᵥ ![0, 1])) 1
          = (resA l B (x - α) *ᵥ ![0, 1]) 0 := tmR_mulVec_one _ _
      rw [hv, hone, h0 (x - α)]
    have hw2 : ∀ x, resA l B x *ᵥ ![0, 1] = 0 := by
      intro x
      funext i
      fin_cases i
      · simpa using h0 x
      · simpa using h1 x
    have hz : resA l B 0 *ᵥ ![0, 1] = 0 := hw2 0
    have hdetu : IsUnit (resT l B 0).det := by
      rw [resT_det hdet l 0]
      exact isUnit_one
    have hres : (resT l B 0) *ᵥ (resA l B 0 *ᵥ ![0, 1]) = 0 := by
      rw [hz, Matrix.mulVec_zero]
    rw [Matrix.mulVec_mulVec, resA_eq_inv hdet l 0, Matrix.mul_nonsing_inv _ hdetu,
      Matrix.one_mulVec] at hres
    have hv : (![0, 1] : Fin 2 → ℝ) 1 = (0 : Fin 2 → ℝ) 1 := congrFun hres 1
    norm_num at hv
  obtain ⟨γ, hγ⟩ := dual_solutions_dependent hlam hu₁c hu₂c hu₁p hu₂p hu₁q hu₂q hu₂ne
  have hcomp0 : ∀ x, (((resA l B x *ᵥ ![1, 0]) 0 : ℝ) : ℂ)
      = γ * (((resA l B x *ᵥ ![0, 1]) 0 : ℝ) : ℂ) := by
    intro x
    have h := hγ x
    rw [hu₁, hu₂] at h
    simpa using h
  have hcomp1 : ∀ x, (((resA l B x *ᵥ ![1, 0]) 1 : ℝ) : ℂ)
      = γ * (((resA l B x *ᵥ ![0, 1]) 1 : ℝ) : ℂ) := by
    intro x
    have hs₁ : (resA l B x *ᵥ ![1, 0]) 1 = (resA l B (x - α) *ᵥ ![1, 0]) 0 := by
      have hv := resA_vec hdet hconj hm ![1, 0] (x - α)
      rw [show (x - α) + α = x by ring] at hv
      rw [hv]
      exact tmR_mulVec_one _ _
    have hs₂ : (resA l B x *ᵥ ![0, 1]) 1 = (resA l B (x - α) *ᵥ ![0, 1]) 0 := by
      have hv := resA_vec hdet hconj hm ![0, 1] (x - α)
      rw [show (x - α) + α = x by ring] at hv
      rw [hv]
      exact tmR_mulVec_one _ _
    have h := hcomp0 (x - α)
    rw [← hs₁, ← hs₂] at h
    exact h
  have hdet0 : (resA l B 0).det = 0 := by
    have h00 : ((resA l B 0) 0 0 : ℂ) = γ * ((resA l B 0) 0 1 : ℂ) := by
      have h := hcomp0 0
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h
    have h10 : ((resA l B 0) 1 0 : ℂ) = γ * ((resA l B 0) 1 1 : ℂ) := by
      have h := hcomp1 0
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h
    have hc : (((resA l B 0).det : ℝ) : ℂ) = 0 := by
      rw [Matrix.det_fin_two]
      push_cast
      rw [h00, h10]
      ring
    exact Complex.ofReal_injective (by simpa using hc)
  have hone := resA_det hdet l 0
  rw [hdet0] at hone
  norm_num at hone
