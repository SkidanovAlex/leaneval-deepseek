import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.Instances

/-!
# The horospherical zone of a `t0`-contracted subgroup `U ≤ SL₃(ℝ)`

`Work.EKLContract.IsHoro U` demands, among other things, a diagonal element `aDiag t0` that
*contracts* `U`: the `n`-th conjugate `aDiag t0 ^ n * u * (aDiag t0 ^ n)⁻¹` of every `u ∈ U`
tends to the identity.  The present file proves that under this single hypothesis the whole
group `U` is trapped in the unipotent radical of the Borel subgroup belonging to the linear
functional `t0`: writing `t0 i ≥ t0 j` for `i ≠ j`, the `(i,j)`-entry of `u` must vanish, and
the diagonal entries of `u` are all `1`.

The mechanism is one explicit computation: `aDiag t` is scalar times the diagonal matrix with
entries `e^{t k}`, so conjugating by its `n`-th power multiplies the `(i,j)`-entry of `u` by
`e^{n(t i - t j)}`; convergence to `1` then forces that entry to vanish as soon as the factor
does not decay to zero, while the diagonal is untouched.

This is the "horospherical" direction of the EKL argument (Lemma 4.4/§2.2 of
Einsiedler–Katok–Lindenstrauss): a contracted subgroup is unipotent with respect to the
ordering of the weights of `t0`.
-/

namespace Work.EKLRelCross

open Work.EKLContract Filter Matrix

/-- The underlying matrix of `(aDiag t)⁻¹` is diagonal, with entries the inverses of the
entries of `aDiag t`. -/
lemma toMat_aDiag_inv (t : Fin 3 → ℝ) :
    toMat (aDiag t)⁻¹ = Matrix.diagonal (fun i => (Real.exp (t i - (∑ j, t j) / 3))⁻¹) := by
  have hinv : (aDiag t)⁻¹ = aDiag (-t) := inv_eq_of_mul_eq_one_left (aDiag_neg_mul t)
  rw [hinv, toMat_aDiag, Work.EKLContract.Lemmas.aDiag_neg_diag]

/-- **Entry formula for the `aDiag t`-conjugation.**  The `(i,j)`-entry of
`aDiag t ^ n * u * (aDiag t ^ n)⁻¹` is `e^{n(t i - t j)}` times the `(i,j)`-entry of `u`
(the normalising scalar `e^{-(∑t)/3}` cancels between the two diagonal factors). -/
lemma conj_entry (t : Fin 3 → ℝ) (u : SL3) (n : ℕ) (i j : Fin 3) :
    toMat (aDiag t ^ n * u * (aDiag t ^ n)⁻¹) i j
      = Real.exp ((n : ℝ) * (t i - t j)) * toMat u i j := by
  have hpow : (aDiag t) ^ n = aDiag (fun k : Fin 3 => (n : ℝ) * t k) :=
    Work.EKLContract.Lemmas.horoUij_aDiag_pow t n
  rw [hpow, toMat_mul, toMat_mul, toMat_aDiag, toMat_aDiag_inv]
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [Work.EKLContract.Lemmas.exp_aDiag_scalar (fun k : Fin 3 => (n : ℝ) * t k) i j (toMat u i j)]
  congr 1
  ring_nf

/-- Convergence of the conjugated sequence to `1` in `SL₃(ℝ)` gives convergence of every
matrix entry to the corresponding entry of the identity: the entries are continuous functions
of the group element. -/
lemma tendsto_conj_entry {t : Fin 3 → ℝ} {u : SL3}
    (h : Tendsto (fun n : ℕ => aDiag t ^ n * u * (aDiag t ^ n)⁻¹) atTop (nhds 1))
    (i j : Fin 3) :
    Tendsto (fun n : ℕ => (toMat (aDiag t ^ n * u * (aDiag t ^ n)⁻¹)) i j)
      atTop (nhds ((1 : Matrix (Fin 3) (Fin 3) ℝ) i j)) := by
  have hcont : Continuous fun A : SL3 => toMat A i j :=
    (continuous_apply j).comp (Matrix.SpecialLinearGroup.continuous_apply _ continuous_id i)
  have hcomp := (hcont.continuousAt.tendsto).comp h
  simpa [Function.comp_def, toMat_one] using hcomp

theorem horoZone {U : Subgroup Work.EKLContract.SL3} {t0 : Fin 3 → ℝ}
    (hcontr : ∀ u ∈ U, Filter.Tendsto
      (fun n : ℕ => Work.EKLContract.aDiag t0 ^ n * u * (Work.EKLContract.aDiag t0 ^ n)⁻¹)
      Filter.atTop (nhds 1)) :
    ∀ u ∈ U,
      (∀ i j : Fin 3, i ≠ j → t0 i ≥ t0 j →
        (u : Matrix (Fin 3) (Fin 3) ℝ) i j = 0) ∧
      (∀ i : Fin 3, (u : Matrix (Fin 3) (Fin 3) ℝ) i i = 1) := by
  intro u hu
  have h := hcontr u hu
  constructor
  · intro i j hij hge
    have hentry := tendsto_conj_entry h i j
    rw [Matrix.one_apply_ne hij] at hentry
    have hentry' : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * (t0 i - t0 j)) * toMat u i j)
        atTop (nhds 0) := by
      simpa only [conj_entry] using hentry
    rcases lt_or_eq_of_le hge with hlt | heq
    · -- `t0 i > t0 j`: the `(i,j)`-entry is expanded, so it has to be `0` from the start.
      have hδ : 0 < t0 i - t0 j := by linarith
      have hexp : Tendsto (fun n : ℕ => Real.exp (-((n : ℝ) * (t0 i - t0 j)))) atTop (nhds 0) := by
        have hp : Tendsto (fun n : ℕ => (Real.exp (-(t0 i - t0 j))) ^ n) atTop (nhds 0) :=
          tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_nonneg _)
            (Real.exp_lt_one_iff.mpr (by linarith))
        have hfun : (fun n : ℕ => Real.exp (-((n : ℝ) * (t0 i - t0 j))))
            = fun n : ℕ => (Real.exp (-(t0 i - t0 j))) ^ n := by
          funext n
          rw [← Real.exp_nat_mul]
          congr 1
          ring
        rw [hfun]; exact hp
      have hprod : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * (t0 i - t0 j)) * toMat u i j
          * Real.exp (-((n : ℝ) * (t0 i - t0 j)))) atTop (nhds 0) := by
        simpa using hentry'.mul hexp
      have hfun2 : (fun n : ℕ => Real.exp ((n : ℝ) * (t0 i - t0 j)) * toMat u i j
          * Real.exp (-((n : ℝ) * (t0 i - t0 j)))) = fun _ : ℕ => toMat u i j := by
        funext n
        rw [mul_assoc, mul_comm (toMat u i j), ← mul_assoc, ← Real.exp_add]
        simp
      rw [hfun2] at hprod
      exact tendsto_nhds_unique tendsto_const_nhds hprod
    · -- `t0 i = t0 j`: the `(i,j)`-entry is not conjugated at all.
      have hentry'' : Tendsto (fun _ : ℕ => toMat u i j) atTop (nhds 0) := by
        have hfun : (fun n : ℕ => Real.exp ((n : ℝ) * (t0 i - t0 j)) * toMat u i j)
            = fun _ : ℕ => toMat u i j := by
          funext n
          rw [heq, sub_self, mul_zero, Real.exp_zero, one_mul]
        rw [hfun] at hentry'
        exact hentry'
      exact tendsto_nhds_unique tendsto_const_nhds hentry''
  · -- The diagonal entries are fixed by the conjugation, hence converge to `1`.
    intro i
    have hentry := tendsto_conj_entry h i i
    rw [Matrix.one_apply_eq i] at hentry
    have hentry' : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * (t0 i - t0 i)) * toMat u i i)
        atTop (nhds 1) := by
      simpa only [conj_entry] using hentry
    have hfun : (fun n : ℕ => Real.exp ((n : ℝ) * (t0 i - t0 i)) * toMat u i i)
        = fun _ : ℕ => toMat u i i := by
      funext n
      rw [sub_self, mul_zero, Real.exp_zero, one_mul]
    rw [hfun] at hentry'
    exact tendsto_nhds_unique tendsto_const_nhds hentry'

end Work.EKLRelCross
