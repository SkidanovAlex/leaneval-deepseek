/-
Auxiliary development for `Work.TMComp.IDSBox.shift` (module `Submission.Work.TMComp.IDSBox.shiftAux`).

The requested statement `Work.TMComp.IDSBox.shift` is FALSE as written: its third conjunct
requires `∑ k, shiftVec φ i n k * conj (shiftVec φ j' n k) = 0` whenever `R ≤ |i - j'|`,
but `hsupp` only forces the support of `φ` into `{m : |m| ≤ R - 1}` (a window of width
`2R - 1`, not `R`).  Two shifts `i`, `j'` of such a window overlap as soon as
`|i - j'| ≤ 2R - 2`, which is compatible with `R ≤ |i - j'|` as soon as `R ≥ 2`
(for `R = 2`, `i = 0`, `j' = 2`, `φ` supported on `{±1}` the sum is `≠ 0`).

The correct hypothesis is `2 * R - 1 ≤ |i - j'|`; the proof of the orthogonality is
then a pointwise vanishing argument (`shiftVec_orth'` below).

This file records the two conjuncts that are true as stated (the residual bound and the
unit norm) in the shape needed by the correct statement.
-/
import Mathlib
import Submission.Work.TMComp.IDSDefs

noncomputable section

open scoped BigOperators
open Work.TMContract

namespace Work.TMComp.IDSBox

/-! ## I. Support bookkeeping -/

/-- The support of a sequence dominated by `hsupp` lives in `1 - R ≤ m ≤ R - 1`. -/
theorem abs_lt_of_ne_zero {R : ℕ} {φ : ℤ → ℂ}
    (hsupp : ∀ m : ℤ, R ≤ m.natAbs → φ m = 0) {m : ℤ} (hm : φ m ≠ 0) :
    |m| < (R : ℤ) := by
  have h : ¬ (R ≤ m.natAbs) := fun h => hm (hsupp m h)
  have : m.natAbs < R := not_le.mp h
  rw [Int.abs_eq_natAbs]
  exact_mod_cast this

/-- `R ≤ m.natAbs` is the same as `(R : ℤ) ≤ |m|`. -/
theorem natAbs_ge_iff {R : ℕ} {m : ℤ} : R ≤ m.natAbs ↔ (R : ℤ) ≤ |m| := by
  rw [Int.abs_eq_natAbs]
  exact Int.ofNat_le.symm

/-- Orthogonality of distinct shifts of a sequence supported in `|m| ≤ R - 1`, with the
correct spacing `2R - 1`. -/
theorem shiftVec_orth' {R : ℕ} (φ : ℤ → ℂ)
    (hsupp : ∀ m : ℤ, R ≤ m.natAbs → φ m = 0)
    (i j' : ℤ) (n : ℕ) (hd : 2 * (R : ℤ) - 1 ≤ |i - j'|) :
    (∑ k : Fin n, shiftVec φ i n k * (starRingEnd ℂ) (shiftVec φ j' n k)) = 0 := by
  refine Finset.sum_eq_zero fun k _ => ?_
  simp only [shiftVec]
  by_cases h1 : φ ((k : ℤ) - i) = 0
  · simp [h1]
  · by_cases h2 : φ ((k : ℤ) - j') = 0
    · simp [h2]
    · exfalso
      have hb1 : |(k : ℤ) - i| ≤ (R : ℤ) - 1 := by
        have := abs_lt_of_ne_zero hsupp h1
        omega
      have hb2 : |(k : ℤ) - j'| ≤ (R : ℤ) - 1 := by
        have := abs_lt_of_ne_zero hsupp h2
        omega
      have hkey : |i - j'| ≤ 2 * (R : ℤ) - 2 := by
        have h : i - j' = ((k : ℤ) - j') - ((k : ℤ) - i) := by ring
        rw [h, sub_eq_add_neg]
        calc |((k : ℤ) - j') + -((k : ℤ) - i)| ≤ |(k : ℤ) - j'| + |-((k : ℤ) - i)| := abs_add_le _ _
          _ = |(k : ℤ) - j'| + |(k : ℤ) - i| := by rw [abs_neg]
          _ ≤ (R : ℤ) - 1 + ((R : ℤ) - 1) := add_le_add hb2 hb1
          _ = 2 * (R : ℤ) - 2 := by ring
      omega

/-! ## II. The residual of the shifted vector -/

/-- The residual of `φ` for the phase-`0` AMO at energy `E`. -/
def resSeq (α lam E : ℝ) (φ : ℤ → ℂ) : ℤ → ℂ :=
  fun m => amoAct α lam 0 φ m - (E : ℂ) * φ m

/-- The residual at `m` only sees `φ` at `m - 1`, `m`, `m + 1`; a sequence supported in
`|m| ≤ R - 1` therefore has residual supported in `|m| ≤ R + 1`. -/
theorem resSeq_eq_zero_of_gt {R : ℕ} {φ : ℤ → ℂ}
    (hsupp : ∀ m : ℤ, R ≤ m.natAbs → φ m = 0) (α lam E : ℝ) {m : ℤ}
    (hm : (R : ℤ) + 1 < |m|) : resSeq α lam E φ m = 0 := by
  have hmR : (R : ℤ) ≤ |m| := by omega
  have h0 : φ m = 0 := hsupp m (natAbs_ge_iff.mpr hmR)
  have h1 : φ (m + 1) = 0 := by
    apply hsupp
    refine natAbs_ge_iff.mpr ?_
    have h : |m| ≤ |m + 1| + 1 := by
      calc |m| = |(m + 1) + (-1 : ℤ)| := by ring_nf
        _ ≤ |m + 1| + |(-1 : ℤ)| := abs_add_le _ _
        _ = |m + 1| + 1 := by rw [abs_neg, abs_one]
    omega
  have h2 : φ (m - 1) = 0 := by
    apply hsupp
    refine natAbs_ge_iff.mpr ?_
    have h : |m| ≤ |m - 1| + 1 := by
      calc |m| = |(m - 1) + (1 : ℤ)| := by ring_nf
        _ ≤ |m - 1| + |(1 : ℤ)| := abs_add_le _ _
        _ = |m - 1| + 1 := by rw [abs_one]
    omega
  simp [resSeq, amoAct, h0, h1, h2]

/-- The window sum of the residual norm-squares is at most the full `ℓ²` mass of the
residual. -/
theorem sum_window_res_le {R : ℕ} {φ : ℤ → ℂ}
    (hsupp : ∀ m : ℤ, R ≤ m.natAbs → φ m = 0) (α lam E ε : ℝ) (j : ℤ) (n : ℕ)
    (hres : (∑' m : ℤ, ‖resSeq α lam E φ m‖ ^ 2) ≤ ε ^ 2) :
    (∑ k : Fin n, ‖resSeq α lam E φ ((k : ℤ) - j)‖ ^ 2) ≤ ε ^ 2 := by
  have hs : ∀ m ∉ Finset.Icc (-((R : ℤ) + 1)) ((R : ℤ) + 1), resSeq α lam E φ m = 0 := by
    intro m hm
    apply resSeq_eq_zero_of_gt hsupp
    have hm' : ¬ (-((R : ℤ) + 1) ≤ m ∧ m ≤ (R : ℤ) + 1) := by
      simpa [Finset.mem_Icc] using hm
    have h : ¬ (|m| ≤ (R : ℤ) + 1) := fun h => hm' (abs_le.mp h)
    omega
  have hsumm : Summable fun m : ℤ => ‖resSeq α lam E φ m‖ ^ 2 := by
    apply summable_of_ne_finset_zero (s := Finset.Icc (-((R : ℤ) + 1)) ((R : ℤ) + 1))
    intro m hm
    rw [hs m hm]
    simp
  have hinj : Set.InjOn (fun k : Fin n => (k : ℤ) - j) ↑(Finset.univ : Finset (Fin n)) := by
    intro a _ b _ hab
    have h1 : (a : ℤ) = (b : ℤ) := by
      have := congrArg (fun t : ℤ => t + j) hab
      simpa using this
    exact Fin.ext (by exact_mod_cast h1)
  calc (∑ k : Fin n, ‖resSeq α lam E φ ((k : ℤ) - j)‖ ^ 2)
      = ∑ m ∈ Finset.univ.image (fun k : Fin n => (k : ℤ) - j), ‖resSeq α lam E φ m‖ ^ 2 := by
        rw [Finset.sum_image (f := fun m : ℤ => ‖resSeq α lam E φ m‖ ^ 2)
          (g := fun k : Fin n => (k : ℤ) - j) hinj]
    _ ≤ ∑' m : ℤ, ‖resSeq α lam E φ m‖ ^ 2 :=
        Summable.sum_le_tsum _ (fun i _ => by positivity) hsumm
    _ ≤ ε ^ 2 := hres

/-! ## III. The squared triangle inequality in `ℓ²(Fin n)` -/

/-- The sharp squared triangle inequality for nonnegative real vectors. -/
theorem l2_add_real {n : ℕ} (x y : Fin n → ℝ) (hx : ∀ k, 0 ≤ x k) (hy : ∀ k, 0 ≤ y k) :
    (∑ k : Fin n, (x k + y k) ^ 2)
      ≤ (Real.sqrt (∑ k : Fin n, x k ^ 2) + Real.sqrt (∑ k : Fin n, y k ^ 2)) ^ 2 := by
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  have hA : 0 ≤ ∑ k : Fin n, x k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hB : 0 ≤ ∑ k : Fin n, y k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hS : 0 ≤ ∑ k : Fin n, x k * y k :=
    Finset.sum_nonneg fun k _ => mul_nonneg (hx k) (hy k)
  have hpq : (∑ k : Fin n, x k * y k)
      ≤ Real.sqrt (∑ k : Fin n, x k ^ 2) * Real.sqrt (∑ k : Fin n, y k ^ 2) := by
    rw [← Real.sqrt_mul' (∑ k : Fin n, x k ^ 2) hB]
    exact Real.le_sqrt_of_sq_le hCS
  have hp : Real.sqrt (∑ k : Fin n, x k ^ 2) ^ 2 = ∑ k : Fin n, x k ^ 2 := Real.sq_sqrt hA
  have hq : Real.sqrt (∑ k : Fin n, y k ^ 2) ^ 2 = ∑ k : Fin n, y k ^ 2 := Real.sq_sqrt hB
  calc (∑ k : Fin n, (x k + y k) ^ 2)
      = (∑ k : Fin n, x k ^ 2) + 2 * (∑ k : Fin n, x k * y k) + (∑ k : Fin n, y k ^ 2) := by
        rw [Finset.sum_congr rfl (fun k _ => by ring : ∀ k ∈ (Finset.univ : Finset (Fin n)),
          (x k + y k) ^ 2 = x k ^ 2 + y k ^ 2 + 2 * (x k * y k))]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
    _ ≤ (Real.sqrt (∑ k : Fin n, x k ^ 2) + Real.sqrt (∑ k : Fin n, y k ^ 2)) ^ 2 := by
        nlinarith [hpq, hp, hq]

/-! ## IV. Conjunct 1 (the residual bound) -/

/-- **Conjunct 1** of the target, conditional on the operator identity (`jbox_apply`) and
the potential perturbation estimate (`pot_shift_close`), together with the normalisation
of the shift. -/
theorem shift_res_of {R : ℕ} (φ : ℤ → ℂ) (α lam θ E δ ε : ℝ) (j : ℤ) (n : ℕ)
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hbox : ∀ k : Fin n,
      (Matrix.mulVec (Jbox α lam θ n) (shiftVec φ j n)) k - (E : ℂ) * shiftVec φ j n k
        = resSeq α lam E φ ((k : ℤ) - j)
          + (((amoPot α lam θ (k : ℤ) - amoPot α lam 0 ((k : ℤ) - j)) : ℝ) : ℂ)
              * φ ((k : ℤ) - j))
    (hpot : ∀ k : Fin n,
      |amoPot α lam θ (k : ℤ) - amoPot α lam 0 ((k : ℤ) - j)| ≤ 4 * Real.pi * |lam| * δ)
    (hwin : (∑ k : Fin n, ‖resSeq α lam E φ ((k : ℤ) - j)‖ ^ 2) ≤ ε ^ 2)
    (hnorm : (∑ k : Fin n, ‖shiftVec φ j n k‖ ^ 2) = 1) :
    (∑ k : Fin n,
        ‖(Matrix.mulVec (Jbox α lam θ n) (shiftVec φ j n)) k - (E : ℂ) * shiftVec φ j n k‖ ^ 2)
      ≤ (ε + 4 * Real.pi * |lam| * δ) ^ 2 := by
  set c : ℝ := 4 * Real.pi * |lam| * δ with hcdef
  have hc : 0 ≤ c := by rw [hcdef]; positivity
  have hterm : ∀ k : Fin n,
      ‖(Matrix.mulVec (Jbox α lam θ n) (shiftVec φ j n)) k - (E : ℂ) * shiftVec φ j n k‖
        ≤ ‖resSeq α lam E φ ((k : ℤ) - j)‖ + c * ‖shiftVec φ j n k‖ := by
    intro k
    rw [hbox k]
    refine (norm_add_le _ _).trans ?_
    have hΔ : ‖(((amoPot α lam θ (k : ℤ) - amoPot α lam 0 ((k : ℤ) - j)) : ℝ) : ℂ)
        * φ ((k : ℤ) - j)‖ ≤ c * ‖shiftVec φ j n k‖ := by
      rw [norm_mul, shiftVec, Complex.norm_real, Real.norm_eq_abs]
      have h := hpot k
      rw [hcdef] at h
      rw [hcdef]
      exact mul_le_mul_of_nonneg_right h (norm_nonneg _)
    linarith
  have hsqc : (∑ k : Fin n, (c * ‖shiftVec φ j n k‖) ^ 2) = c ^ 2 := by
    rw [Finset.sum_congr rfl (fun k _ => by ring : ∀ k ∈ (Finset.univ : Finset (Fin n)),
      (c * ‖shiftVec φ j n k‖) ^ 2 = c ^ 2 * ‖shiftVec φ j n k‖ ^ 2)]
    rw [← Finset.mul_sum, hnorm, mul_one]
  have hsqrtc : Real.sqrt (∑ k : Fin n, (c * ‖shiftVec φ j n k‖) ^ 2) = c := by
    rw [hsqc, Real.sqrt_sq hc]
  calc (∑ k : Fin n,
        ‖(Matrix.mulVec (Jbox α lam θ n) (shiftVec φ j n)) k - (E : ℂ) * shiftVec φ j n k‖ ^ 2)
      ≤ ∑ k : Fin n, (‖resSeq α lam E φ ((k : ℤ) - j)‖ + c * ‖shiftVec φ j n k‖) ^ 2 :=
        Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hterm k) 2
    _ ≤ (Real.sqrt (∑ k : Fin n, ‖resSeq α lam E φ ((k : ℤ) - j)‖ ^ 2)
          + Real.sqrt (∑ k : Fin n, (c * ‖shiftVec φ j n k‖) ^ 2)) ^ 2 :=
        l2_add_real _ _ (fun k => norm_nonneg _) (fun k => by positivity)
    _ = (Real.sqrt (∑ k : Fin n, ‖resSeq α lam E φ ((k : ℤ) - j)‖ ^ 2) + c) ^ 2 := by
        rw [hsqrtc]
    _ ≤ (ε + c) ^ 2 := by
        have h1 : Real.sqrt (∑ k : Fin n, ‖resSeq α lam E φ ((k : ℤ) - j)‖ ^ 2) ≤ ε :=
          Real.sqrt_le_iff.mpr ⟨hε, hwin⟩
        have h2 : 0 ≤ Real.sqrt (∑ k : Fin n, ‖resSeq α lam E φ ((k : ℤ) - j)‖ ^ 2) :=
          Real.sqrt_nonneg _
        nlinarith [h1, hc, hε, h2]

end Work.TMComp.IDSBox
