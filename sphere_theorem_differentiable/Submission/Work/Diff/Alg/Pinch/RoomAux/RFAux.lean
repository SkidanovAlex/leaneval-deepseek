import Mathlib
import Submission.Work.Diff.Alg.Pinch.Linv
import Submission.Work.Diff.Alg.Pinch.BQ_iso
import Submission.Work.Diff.Alg.Pinch.inPIC2_metric_basic
import Submission.Work.Diff.Alg.Pinch.inPIC2_comp_bound
import Submission.Work.Diff.Alg.Pinch.ric_Q
import Submission.Work.Diff.Alg.Pinch.scalAlg_Q
import Submission.Work.Diff.Alg.Pinch.ric_knProd_id2
import Submission.Work.Diff.Alg.Pinch.scalAlg_knProd
import Submission.Work.Diff.Alg.Pinch.Q_isAlgCurv
import Submission.Work.Diff.Alg.Pinch.ricForm_Q
import Submission.Work.Diff.Alg.Pinch.scalAlg_linv
import Submission.Work.Diff.Alg.Pinch.ric_ell_form
import Submission.Work.Diff.Alg.Pinch.knProd_id2_contraction
import Submission.Work.Diff.Alg.Pinch.psd_pairing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary lemmas for `Work.Diff.Alg.Pinch.ricForm_X_strict_at_tight`

Vocabulary:
* `ricForm T v = ∑ᵢ∑ⱼ ric T i j * vᵢ * vⱼ`, the Ricci quadratic form of a `4`-index array;
* `ricMat T`, the matrix of that form;
* `Nz R v p q = ∑ᵢ∑ⱼ R i p j q * vᵢ * vⱼ`, the "curvature matrix in the direction `v`".

The point of `Nz` is that Hamilton's reaction term factorises through it
(`ricForm_Q`: `ricForm (Q R) v = 2 ∑_{pq} ric R p q * Nz R v p q`), while `InPIC2` makes
`Nz R v` positive semidefinite (`Nz_psd`).  Positive semidefiniteness is handled with
`Matrix.PosSemidef` (in particular the Schur product theorem and
`PosSemidef.dotProduct_mulVec_zero_iff`), which is why every quadratic form below is also
written as a `Matrix.dotProduct`/`Matrix.mulVec` expression.
-/

namespace Work.Diff.Alg.Pinch.RFAux

open Finset Submission.Diff.Alg Matrix

variable {n : ℕ}

/-- The Ricci quadratic form `∑ᵢ∑ⱼ ric T i j * vᵢ * vⱼ` of a `4`-index array. -/
noncomputable def ricForm (T : Curv4 n) (v : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, ric T i j * v i * v j

/-- The matrix of the Ricci quadratic form. -/
noncomputable def ricMat (T : Curv4 n) : Matrix (Fin n) (Fin n) ℝ := fun i j => ric T i j

/-- The curvature matrix in the direction `v`: `Nz R v p q = ∑ᵢ∑ⱼ R i p j q * vᵢ * vⱼ`. -/
noncomputable def Nz (R : Curv4 n) (v : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun p q => ∑ i, ∑ j, R i p j q * v i * v j

/-! ## Elementary sum manipulations -/

/-- Swapping the two blocks of summation indices. -/
lemma sum4_swap_block (g : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ p, ∑ q, ∑ i, ∑ j, g p q i j) = ∑ i, ∑ j, ∑ p, ∑ q, g p q i j := by
  calc (∑ p, ∑ q, ∑ i, ∑ j, g p q i j)
      = ∑ p, ∑ i, ∑ q, ∑ j, g p q i j := by
        apply Finset.sum_congr rfl; intro p _; rw [Finset.sum_comm]
    _ = ∑ i, ∑ p, ∑ q, ∑ j, g p q i j := by rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, ∑ p, ∑ q, g p q i j := by
        apply Finset.sum_congr rfl; intro i _
        calc (∑ p, ∑ q, ∑ j, g p q i j) = ∑ p, ∑ j, ∑ q, g p q i j := by
              apply Finset.sum_congr rfl; intro p _; rw [Finset.sum_comm]
          _ = ∑ j, ∑ p, ∑ q, g p q i j := by rw [Finset.sum_comm]

/-- A constant factor can be moved out of a double sum. -/
lemma sum2_mul_const {f : Fin n → Fin n → ℝ} {c : ℝ} :
    (∑ i, ∑ j, f i j * c) = (∑ i, ∑ j, f i j) * c := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_mul]

/-! ## The curvature matrix in a direction -/

/-- `∑ p, Nz R v p p = ricForm R v` for an algebraic curvature tensor. -/
theorem tr_Nz_eq {R : Curv4 n} (hR : IsAlgCurv R) (v : Fin n → ℝ) :
    (∑ p, Nz R v p p) = ricForm R v := by
  have h1 : (∑ p, Nz R v p p) = ∑ i, ∑ j, (∑ p, R i p j p) * v i * v j := by
    simp only [Nz]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    rw [Finset.sum_mul, Finset.sum_mul]
  rw [h1, ricForm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [sum_self_eq_ric hR i j]

/-- `R4 R v z v z = ∑_{p q} Nz R v p q * z p * z q`. -/
theorem R4_eq_Nz_quad (R : Curv4 n) (v z : Fin n → ℝ) :
    R4 R v z v z = ∑ p, ∑ q, Nz R v p q * z p * z q := by
  have h1 : R4 R v z v z = ∑ i, ∑ k, (∑ p, ∑ q, R i p k q * z p * z q) * v i * v k := by
    simp only [R4]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _
    ring
  rw [h1]
  have h2 : (∑ p, ∑ q, (∑ i, ∑ j, R i p j q * v i * v j) * z p * z q)
      = ∑ i, ∑ k, (∑ p, ∑ q, R i p k q * z p * z q) * v i * v k := by
    have e1 : (∑ p, ∑ q, (∑ i, ∑ j, R i p j q * v i * v j) * z p * z q)
        = ∑ p, ∑ q, ∑ i, ∑ j, R i p j q * v i * v j * z p * z q := by
      apply Finset.sum_congr rfl; intro p _
      apply Finset.sum_congr rfl; intro q _
      simp only [Finset.sum_mul]
    rw [e1, sum4_swap_block (fun p q i j => R i p j q * v i * v j * z p * z q)]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _
    ring
  simp only [Nz]
  exact h2.symm

/-- `Nz R v` is symmetric for an algebraic curvature tensor. -/
theorem Nz_symm {R : Curv4 n} (hR : IsAlgCurv R) (v : Fin n → ℝ) (p q : Fin n) :
    Nz R v p q = Nz R v q p := by
  simp only [Nz]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  rw [(hR.2.1 j p i q).symm]
  ring

/-- `InPIC2` makes the curvature matrix `Nz R v` positive semidefinite. -/
theorem Nz_psd {R : Curv4 n} (hR : IsAlgCurv R) (hP : InPIC2 R) (v : Fin n → ℝ) :
    ∀ z : Fin n → ℝ, 0 ≤ ∑ p, ∑ q, Nz R v p q * z p * z q := by
  intro z
  rw [← R4_eq_Nz_quad R v z]
  exact inPIC2_R4_nonneg R hP v z

/-! ## Matrix form of the Ricci quadratic form -/

/-- `∑ᵢ∑ⱼ M i j * vᵢ * vⱼ = v ⬝ᵥ (M *ᵥ v)`. -/
lemma sum2_eq_dotProduct_mulVec (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    (∑ i, ∑ j, M i j * v i * v j) = v ⬝ᵥ (M *ᵥ v) := by
  simp only [dotProduct, mulVec]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  ring

lemma ricForm_eq_dotProduct (T : Curv4 n) (v : Fin n → ℝ) :
    ricForm T v = v ⬝ᵥ (ricMat T *ᵥ v) :=
  sum2_eq_dotProduct_mulVec (ricMat T) v

lemma ricMat_isHermitian {R : Curv4 n} (hR : IsAlgCurv R) : (ricMat R).IsHermitian := by
  refine Matrix.IsHermitian.ext ?_
  intro i j
  simp only [ricMat, star_trivial]
  exact ric_symm hR j i

/-- `InPIC2 R` makes the Ricci quadratic form positive semidefinite. -/
theorem ricMat_posSemidef {R : Curv4 n} (hR : IsAlgCurv R) (hP : InPIC2 R) :
    (ricMat R).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (ricMat_isHermitian hR) ?_
  intro x
  rw [star_trivial, ← sum2_eq_dotProduct_mulVec]
  exact (inPIC2_metric_basic n).2.1 R hP x

/-- `Nz R v` as a positive semidefinite matrix. -/
theorem NzMat_posSemidef {R : Curv4 n} (hR : IsAlgCurv R) (hP : InPIC2 R) (v : Fin n → ℝ) :
    (Nz R v).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · refine Matrix.IsHermitian.ext ?_
    intro i j
    simp only [star_trivial]
    exact Nz_symm hR v j i
  · intro z
    rw [star_trivial, ← sum2_eq_dotProduct_mulVec]
    exact Nz_psd hR hP v z

/-! ## Positive semidefinite pairings (Schur product theorem) -/

/-- The Frobenius pairing of two positive semidefinite matrices is nonnegative. -/
theorem psd_pairing_mat {A N : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    (hN : N.PosSemidef) : 0 ≤ ∑ i, ∑ j, A i j * N i j := by
  have h := (hA.hadamard hN).dotProduct_mulVec_nonneg (fun _ => 1)
  rw [star_trivial] at h
  simpa [dotProduct, mulVec, Matrix.hadamard, mul_comm, Finset.mul_sum, mul_assoc] using h

end Work.Diff.Alg.Pinch.RFAux

namespace Work.Diff.Alg.Pinch.RFAux

open Finset Submission.Diff.Alg Matrix

variable {n : ℕ}

/-! ## The final scalar inequality

The scalars below are those appearing in the Böhm–Wilking one-step estimate.  Everything is a
rational function of `n`, `b` and the two invariants `s = scalAlg S`, `ρ = |Ric₀|²`, times one
factor of `q = |v|²`. -/

/-- `1 + (n-2)b`. -/
noncomputable def bwA0 (n : ℕ) (b : ℝ) : ℝ := 1 + ((n : ℝ) - 2) * b
/-- `1 + (n-2)b²`. -/
noncomputable def bwq0 (n : ℕ) (b : ℝ) : ℝ := 1 + ((n : ℝ) - 2) * b ^ 2
/-- `1 + 2(n-1)b + n(n-2)b²`. -/
noncomputable def bwR (n : ℕ) (b : ℝ) : ℝ :=
  1 + 2 * ((n : ℝ) - 1) * b + (n : ℝ) * ((n : ℝ) - 2) * b ^ 2
/-- `Λ = p·scal/n`. -/
noncomputable def bwΛ (n : ℕ) (b s : ℝ) : ℝ := ccP n b * s / (n : ℝ)
/-- `μ = Λ - scal/n`. -/
noncomputable def bwμ (n : ℕ) (b s : ℝ) : ℝ := bwΛ n b s - s / (n : ℝ)
/-- `κ = (1+2(n-1)a)·scal/n`. -/
noncomputable def bwκ (n : ℕ) (b s : ℝ) : ℝ := (1 + 2 * ((n : ℝ) - 1) * ccA n b) * s / (n : ℝ)
/-- `β = b/(1+(n-2)b)`. -/
noncomputable def bwβ (n : ℕ) (b : ℝ) : ℝ := b / bwA0 n b
/-- `γ₀ = (a/n)/(1+2(n-1)a)`. -/
noncomputable def bwγ0 (n : ℕ) (b : ℝ) : ℝ := (ccA n b / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * ccA n b)

noncomputable def bwS1 (n : ℕ) (b s q : ℝ) : ℝ :=
  bwΛ n b s * q * (bwA0 n b * bwμ n b s + bwκ n b s)

noncomputable def bwS2 (n : ℕ) (b s ρ q : ℝ) : ℝ :=
  bwμ n b s * q * bwκ n b s * (n : ℝ)
    - 2 * bwμ n b s * (bwA0 n b * bwμ n b s * q + bwκ n b s * q) + q * bwA0 n b * ρ

noncomputable def bwS3 (n : ℕ) (b s q : ℝ) : ℝ :=
  2 * q * bwκ n b s * (n : ℝ) - 2 * (bwA0 n b * bwμ n b s * q + bwκ n b s * q)

noncomputable def bwsQY (n : ℕ) (b s ρ : ℝ) : ℝ :=
  2 * ((bwA0 n b) ^ 2 * ρ + (bwκ n b s) ^ 2 * (n : ℝ))

/-- The coefficient of `ρ·q` in the final estimate (in factored form). -/
noncomputable def bwCρ (n : ℕ) (b : ℝ) : ℝ :=
  b ^ 2 * (4 * ((n : ℝ)) ^ 4 * b ^ 5 + 4 * ((n : ℝ)) ^ 3 * b ^ 3 * (2 - 3 * b) * (1 + 2 * b)
      + 4 * ((n : ℝ)) ^ 2 * b * (1 + 2 * b - 8 * b ^ 2 - 4 * b ^ 3 + 12 * b ^ 4)
      + 4 * (n : ℝ) * (1 - 2 * b) * (1 - 2 * b ^ 2) ^ 2)
    / ((n : ℝ) * bwR n b * (bwq0 n b) ^ 2)

/-- The coefficient `bwCρ` of the final estimate is positive. -/
theorem bwCρ_pos (n : ℕ) (hn : 2 ≤ n) {b : ℝ} (hb : 0 < b) (hb' : b ≤ 1 / 2) :
    0 < bwCρ n b := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have hnm1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hnm2 : (0 : ℝ) ≤ ((n : ℝ) - 2) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hA0 : (0 : ℝ) < 1 + ((n : ℝ) - 2) * b := by nlinarith
  have hq0 : (0 : ℝ) < 1 + ((n : ℝ) - 2) * b ^ 2 := by nlinarith [sq_nonneg b]
  have hR : (0 : ℝ) < 1 + 2 * ((n : ℝ) - 1) * b + (n : ℝ) * ((n : ℝ) - 2) * b ^ 2 := by
    have h2 : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 2) * b ^ 2 :=
      mul_nonneg (mul_nonneg hn0.le hnm2) (sq_nonneg b)
    have h1 : (0 : ℝ) ≤ 2 * ((n : ℝ) - 1) * b :=
      mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hb.le
    nlinarith [h1, h2]
  have hg : (1 : ℝ) / 4 ≤ 1 + 2 * b - 8 * b ^ 2 - 4 * b ^ 3 + 12 * b ^ 4 := by
    have h1 : (0 : ℝ) ≤ 1 / 2 - b := by linarith
    have hcos : (0 : ℝ) ≤ 2 - b - 6 * b ^ 2 := by
      have h := mul_nonneg h1 (by linarith : (0 : ℝ) ≤ 4 + 6 * b)
      nlinarith [h]
    have h3 : (0 : ℝ) ≤ 3 / 2 + 3 * b + 2 * b * (2 - b - 6 * b ^ 2) := by
      have := mul_nonneg hb.le hcos
      linarith
    have h := mul_nonneg h1 h3
    nlinarith [h]
  have hT1 : (0 : ℝ) < 4 * ((n : ℝ)) ^ 4 * b ^ 5 := by positivity
  have hT2 : (0 : ℝ) ≤ 4 * ((n : ℝ)) ^ 3 * b ^ 3 * (2 - 3 * b) * (1 + 2 * b) := by
    have h2 : (0 : ℝ) ≤ 2 - 3 * b := by linarith
    have h3 : (0 : ℝ) ≤ 1 + 2 * b := by linarith
    positivity
  have hT3 : (0 : ℝ) < 4 * ((n : ℝ)) ^ 2 * b * (1 + 2 * b - 8 * b ^ 2 - 4 * b ^ 3 + 12 * b ^ 4) := by
    have h4 : (0 : ℝ) < 4 * ((n : ℝ)) ^ 2 * b := by positivity
    nlinarith [hg, h4]
  have hT4 : (0 : ℝ) ≤ 4 * (n : ℝ) * (1 - 2 * b) * (1 - 2 * b ^ 2) ^ 2 := by
    have h5 : (0 : ℝ) ≤ 1 - 2 * b := by linarith
    positivity
  have hsum : 0 < 4 * ((n : ℝ)) ^ 4 * b ^ 5 + 4 * ((n : ℝ)) ^ 3 * b ^ 3 * (2 - 3 * b) * (1 + 2 * b)
      + 4 * ((n : ℝ)) ^ 2 * b * (1 + 2 * b - 8 * b ^ 2 - 4 * b ^ 3 + 12 * b ^ 4)
      + 4 * (n : ℝ) * (1 - 2 * b) * (1 - 2 * b ^ 2) ^ 2 := by
    linarith [hT1, hT2, hT3, hT4]
  have hb2 : (0 : ℝ) < b ^ 2 := by positivity
  rw [bwCρ]
  refine div_pos (mul_pos hb2 hsum) ?_
  have hR' : 0 < bwR n b := by rw [bwR]; exact hR
  have hq0' : 0 < (bwq0 n b) ^ 2 := by rw [bwq0]; nlinarith [hq0]
  exact mul_pos (mul_pos hn0 hR') hq0'

/-- The Böhm–Wilking one-step estimate, as a scalar inequality. -/
theorem bw_final_algebra (n : ℕ) (hn : 2 ≤ n) {b s ρ q : ℝ} (hb : 0 < b) (hb' : b ≤ 1 / 2)
    (hρ : 0 < ρ) (hq : 0 < q) :
    0 < (1 - bwβ n b * ((n : ℝ) - 2))
          * (2 * (bwS1 n b s q + b * bwS2 n b s ρ q
              + (ccA n b * s / (n : ℝ)) * bwS3 n b s q))
        + (bwβ n b * ((n : ℝ) - 2) - ccP n b) * (bwsQY n b s ρ / (n : ℝ)) * q
        - bwγ0 n b * bwsQY n b s ρ * (2 * (n : ℝ) - 2) * q * (1 - ccP n b) := by
  have key : (1 - bwβ n b * ((n : ℝ) - 2))
          * (2 * (bwS1 n b s q + b * bwS2 n b s ρ q
              + (ccA n b * s / (n : ℝ)) * bwS3 n b s q))
        + (bwβ n b * ((n : ℝ) - 2) - ccP n b) * (bwsQY n b s ρ / (n : ℝ)) * q
        - bwγ0 n b * bwsQY n b s ρ * (2 * (n : ℝ) - 2) * q * (1 - ccP n b)
      = bwCρ n b * ρ * q := by
    have hn0 : ((n : ℝ)) ≠ 0 := by
      have : (0 : ℕ) < n := by omega
      exact_mod_cast (Nat.pos_iff_ne_zero.mp this)
    have hnm1 : (0 : ℝ) ≤ ((n : ℝ) - 1) := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hnm2 : (0 : ℝ) ≤ ((n : ℝ) - 2) := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hA0 : 1 + ((n : ℝ) - 2) * b ≠ 0 := by
      have : (0 : ℝ) < 1 + ((n : ℝ) - 2) * b := by nlinarith
      linarith
    have hq0 : 1 + ((n : ℝ) - 2) * b ^ 2 ≠ 0 := by
      have hb2 : (0 : ℝ) ≤ b ^ 2 := sq_nonneg b
      have h : (0 : ℝ) < 1 + ((n : ℝ) - 2) * b ^ 2 := by nlinarith
      linarith
    have hR0 : 1 + 2 * ((n : ℝ) - 1) * b + (n : ℝ) * ((n : ℝ) - 2) * b ^ 2 ≠ 0 := by
      have h2 : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 2) * b ^ 2 :=
        mul_nonneg (mul_nonneg (le_of_lt (by
          have : (0 : ℕ) < n := by omega
          exact_mod_cast this)) hnm2) (sq_nonneg b)
      have h1 : (0 : ℝ) ≤ 2 * ((n : ℝ) - 1) * b :=
        mul_nonneg (mul_nonneg (by norm_num) hnm1) hb.le
      have h : (0 : ℝ) < 1 + 2 * ((n : ℝ) - 1) * b + (n : ℝ) * ((n : ℝ) - 2) * b ^ 2 := by
        nlinarith [h1, h2]
      linarith
    have hden : 1 + 2 * ((n : ℝ) - 1) * ccA n b
        = (1 + 2 * ((n : ℝ) - 1) * b + (n : ℝ) * ((n : ℝ) - 2) * b ^ 2)
            / (1 + ((n : ℝ) - 2) * b ^ 2) := by
      rw [ccA]
      field_simp
      ring
    simp only [bwβ, bwγ0, bwS1, bwS2, bwS3, bwsQY, bwCρ, bwΛ, bwμ, bwA0, bwκ, bwR, bwq0]
    rw [hden]
    simp only [ccA, ccP]
    field_simp
    set_option maxHeartbeats 4000000 in
    ring_nf
  rw [key]
  exact mul_pos (mul_pos (bwCρ_pos n hn hb hb') hρ) hq

end Work.Diff.Alg.Pinch.RFAux

namespace Work.Diff.Alg.Pinch.RFAux

open Finset Submission.Diff.Alg Matrix

variable {n : ℕ}

/-! ## Tightness of the Ricci pinching upgrades to an eigenvector -/

private lemma sum_id2_mul (v : Fin n → ℝ) : (∑ i, ∑ j, id2 n i j * v i * v j) = ∑ i, v i * v i := by
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_eq_single i]
  · simp [id2]
  · intro j _ hj
    simp only [id2, if_neg (fun h : i = j => hj h.symm), zero_mul, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

lemma sum2_const_mul {f : Fin n → Fin n → ℝ} {c : ℝ} :
    (∑ i, ∑ j, c * f i j) = c * (∑ i, ∑ j, f i j) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]

/-- The quadratic form of `M - Λ • 1`. -/
lemma sum_sub_smul_one (M : Matrix (Fin n) (Fin n) ℝ) (Λ : ℝ) (v : Fin n → ℝ) :
    (∑ i, ∑ j, (M - Λ • 1) i j * v i * v j)
      = (∑ i, ∑ j, M i j * v i * v j) - Λ * (∑ i, v i * v i) := by
  have hpt : ∀ i j, (M - Λ • 1) i j * v i * v j
      = M i j * v i * v j - Λ * (id2 n i j * v i * v j) := by
    intro i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, id2]
    ring
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hpt i j))]
  simp only [Finset.sum_sub_distrib]
  congr 1
  rw [sum2_const_mul, sum_id2_mul]

/-- `Ric - Λ · id` is positive semidefinite under the pinching `RicPinch p S` with
`Λ = p * scalAlg S / n`. -/
theorem ric_sub_posSemidef {S : Curv4 n} (hS : IsAlgCurv S) {p : ℝ} (hric : RicPinch p S) :
    (ricMat S - (p * scalAlg S / (n : ℝ)) • 1).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · refine Matrix.IsHermitian.ext ?_
    intro i j
    simp only [star_trivial, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      ricMat]
    rw [ric_symm hS i j]
    by_cases h : i = j
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hh : j = i => h hh.symm)]
  · intro x
    rw [star_trivial, ← sum2_eq_dotProduct_mulVec, sum_sub_smul_one]
    simp only [ricMat]
    linarith [hric x]

/-- **Tightness at `v` makes `v` an eigenvector of `Ric` with eigenvalue `p·scal/n`.** -/
theorem ric_sub_eigen_of_tight {S : Curv4 n} (hS : IsAlgCurv S) {p : ℝ} (hric : RicPinch p S)
    {v : Fin n → ℝ}
    (htight : (p * scalAlg S / (n : ℝ)) * (∑ i, v i * v i)
      = ∑ i, ∑ j, ric S i j * v i * v j) :
    ∀ i, (∑ j, ric S i j * v j) = (p * scalAlg S / (n : ℝ)) * v i := by
  set Λ := p * scalAlg S / (n : ℝ) with hΛdef
  have hA := ric_sub_posSemidef (n := n) hS hric
  have hzero : v ⬝ᵥ ((ricMat S - Λ • 1) *ᵥ v) = 0 := by
    rw [← sum2_eq_dotProduct_mulVec, sum_sub_smul_one, hΛdef]
    rw [htight]
    simp only [ricMat]
    ring
  have hmv := hA.dotProduct_mulVec_zero_iff.mp hzero
  intro i
  have hi : ((ricMat S - Λ • 1) *ᵥ v) i = 0 := by rw [hmv]; rfl
  simp only [mulVec, dotProduct, ricMat, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, id2] at hi
  have hsplit : (∑ j, (ric S i j - Λ * (if i = j then (1 : ℝ) else 0)) * v j)
      = (∑ j, ric S i j * v j) - Λ * v i := by
    rw [show (∑ j, (ric S i j - Λ * (if i = j then (1 : ℝ) else 0)) * v j)
        = (∑ j, ric S i j * v j) - ∑ j, Λ * (if i = j then (1 : ℝ) else 0) * v j from by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro j _; ring]
    congr 1
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [if_neg (fun h : i = j => hj h.symm)]
      ring
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [hsplit] at hi
  rw [hΛdef] at hi
  linarith

/-- The traceless Ricci tensor in the tight direction: `Ric₀ v = (Λ - scal/n) v`. -/
lemma ric0_eigen_of_tight {S : Curv4 n} (hS : IsAlgCurv S) {p : ℝ} (hric : RicPinch p S)
    {v : Fin n → ℝ}
    (htight : (p * scalAlg S / (n : ℝ)) * (∑ i, v i * v i)
      = ∑ i, ∑ j, ric S i j * v i * v j) (i : Fin n) :
    (∑ j, ric0 S i j * v j)
      = ((p * scalAlg S / (n : ℝ)) - scalAlg S / (n : ℝ)) * v i := by
  have h1 := ric_sub_eigen_of_tight hS hric htight i
  have hsplit : (∑ j, ric0 S i j * v j)
      = (∑ j, ric S i j * v j) - (scalAlg S / (n : ℝ)) * v i := by
    have hpt : ∀ j, ric0 S i j * v j
        = ric S i j * v j - scalAlg S / (n : ℝ) * (id2 n i j * v j) := by
      intro j; rw [ric0]; ring
    rw [Finset.sum_congr rfl (fun j _ => hpt j)]
    rw [Finset.sum_sub_distrib]
    congr 1
    rw [show (∑ j, scalAlg S / (n : ℝ) * (id2 n i j * v j))
        = scalAlg S / (n : ℝ) * (∑ j, id2 n i j * v j) from
      (Finset.mul_sum Finset.univ (fun j => id2 n i j * v j) (scalAlg S / (n : ℝ))).symm]
    rw [ellinv_sum_id2_mul]
  rw [hsplit, h1]; ring

/-- Double contraction of `id ∧ id` against `v ⊗ v`. -/
lemma knProd_id2_id2_contraction (n : ℕ) (v : Fin n → ℝ) (p q : Fin n) :
    (∑ i, ∑ j, knProd (id2 n) (id2 n) i p j q * v i * v j)
      = 2 * (∑ i, v i * v i) * (if p = q then (1 : ℝ) else 0) - 2 * v p * v q := by
  have hpt : ∀ i j, knProd (id2 n) (id2 n) i p j q * v i * v j
      = 2 * (id2 n i j * id2 n p q * v i * v j) - 2 * (id2 n i q * id2 n p j * v i * v j) := by
    intro i j; simp only [knProd, id2]; ring
  have hsplit : (∑ i, ∑ j, knProd (id2 n) (id2 n) i p j q * v i * v j)
      = 2 * (∑ i, ∑ j, id2 n i j * id2 n p q * v i * v j)
        - 2 * (∑ i, ∑ j, id2 n i q * id2 n p j * v i * v j) := by
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hpt i j))]
    simp only [Finset.sum_sub_distrib]
    congr 1
    · rw [show (∑ i, ∑ j, 2 * (id2 n i j * id2 n p q * v i * v j))
          = 2 * (∑ i, ∑ j, id2 n i j * id2 n p q * v i * v j) from by
        rw [sum2_const_mul]]
    · rw [show (∑ i, ∑ j, 2 * (id2 n i q * id2 n p j * v i * v j))
          = 2 * (∑ i, ∑ j, id2 n i q * id2 n p j * v i * v j) from by
        rw [sum2_const_mul]]
  have h1a : ∀ i j, id2 n i j * id2 n p q * v i * v j = id2 n p q * (id2 n i j * v i * v j) := by
    intro i j; ring
  have h1 : (∑ i, ∑ j, id2 n i j * id2 n p q * v i * v j)
      = id2 n p q * (∑ i, ∑ j, id2 n i j * v i * v j) := by
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => h1a i j))]
    exact sum2_const_mul
  have hfac : ∀ i, (∑ j, id2 n i q * id2 n p j * v i * v j)
      = (id2 n i q * v i) * (∑ j, id2 n p j * v j) := by
    intro i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; ring
  have h2 : (∑ i, ∑ j, id2 n i q * id2 n p j * v i * v j)
      = (∑ i, id2 n i q * v i) * (∑ j, id2 n p j * v j) := by
    rw [Finset.sum_congr rfl (fun i _ => hfac i)]
    exact (Finset.sum_mul Finset.univ (fun i => id2 n i q * v i) _).symm
  have h3 : (∑ i, id2 n i q * v i) = v q := by
    rw [show (∑ i, id2 n i q * v i) = ∑ i, v i * id2 n i q from by
      apply Finset.sum_congr rfl; intro i _; ring]
    exact ellinv_sum_mul_id2 v q
  have h4 : (∑ j, id2 n p j * v j) = v p := ellinv_sum_id2_mul v p
  rw [hsplit, h1, h2, h3, h4, sum_id2_mul]
  simp only [id2]
  ring

end Work.Diff.Alg.Pinch.RFAux

namespace Work.Diff.Alg.Pinch.RFAux

open Finset Submission.Diff.Alg Matrix

variable {n : ℕ}

/-! ## The quadratic form of a `2`-tensor -/

/-- The quadratic form of a `2`-tensor. -/
noncomputable def qform (M : Fin n → Fin n → ℝ) (v : Fin n → ℝ) : ℝ := ∑ i, ∑ j, M i j * v i * v j

lemma ricForm_eq_qform (T : Curv4 n) (v : Fin n → ℝ) : ricForm T v = qform (ric T) v := rfl

lemma qform_add (A B : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    qform (A + B) v = qform A v + qform B v := by
  simp only [qform, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma qform_sub (A B : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    qform (A - B) v = qform A v - qform B v := by
  simp only [qform, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma qform_smul (c : ℝ) (A : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    qform (c • A) v = c * qform A v := by
  show (∑ i, ∑ j, (c • A) i j * v i * v j) = c * (∑ i, ∑ j, A i j * v i * v j)
  rw [show (∑ i, ∑ j, (c • A) i j * v i * v j) = ∑ i, ∑ j, c * (A i j * v i * v j) from by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    simp only [Pi.smul_apply, smul_eq_mul]; ring]
  exact sum2_const_mul

lemma qform_id2 (v : Fin n → ℝ) : qform (id2 n) v = ∑ i, v i * v i := sum_id2_mul v

lemma qform_ric0 (Y : Curv4 n) (v : Fin n → ℝ) :
    qform (ric0 Y) v = ricForm Y v - (scalAlg Y / (n : ℝ)) * (∑ i, v i * v i) := by
  have hdecomp : ric0 Y = ric Y - (scalAlg Y / (n : ℝ)) • (id2 n : Fin n → Fin n → ℝ) := rfl
  rw [hdecomp, qform_sub, qform_smul, qform_id2, ricForm_eq_qform]

/-- The Ricci quadratic form of `A ∧ id`. -/
lemma ricForm_knProd_id2 (A : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    ricForm (knProd A (id2 n)) v
      = (∑ k, A k k) * (∑ i, v i * v i) + ((n : ℝ) - 2) * qform A v := by
  have hsplit : (∑ i, ∑ j, ric (knProd A (id2 n)) i j * v i * v j)
      = (∑ k, A k k) * (∑ i, ∑ j, id2 n i j * v i * v j)
        + ((n : ℝ) - 2) * (∑ i, ∑ j, A i j * v i * v j) := by
    have hpt : ∀ i j, ric (knProd A (id2 n)) i j * v i * v j
        = (∑ k, A k k) * (id2 n i j * v i * v j) + ((n : ℝ) - 2) * (A i j * v i * v j) := by
      intro i j; rw [ric_knProd_id2]; simp only [id2]; ring
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hpt i j))]
    simp only [Finset.sum_add_distrib]
    congr 1
    · exact sum2_const_mul
    · rw [show (∑ i, ∑ j, ((n : ℝ) - 2) * (A i j * v i * v j))
          = ((n : ℝ) - 2) * (∑ i, ∑ j, A i j * v i * v j) from sum2_const_mul]
  rw [ricForm, hsplit, sum_id2_mul, qform]

/-- The Ricci quadratic form of `id ∧ id`. -/
lemma ricForm_knProd_id2_id2 (v : Fin n → ℝ) :
    ricForm (knProd (id2 n) (id2 n)) v = (2 * (n : ℝ) - 2) * (∑ i, v i * v i) := by
  have hsplit : (∑ i, ∑ j, ric (knProd (id2 n) (id2 n)) i j * v i * v j)
      = (2 * (n : ℝ) - 2) * (∑ i, ∑ j, id2 n i j * v i * v j) := by
    have hpt : ∀ i j, ric (knProd (id2 n) (id2 n)) i j * v i * v j
        = (2 * (n : ℝ) - 2) * (id2 n i j * v i * v j) := by
      intro i j; rw [ellinv_ric_knProd_id2_id2]; ring
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hpt i j))]
    exact sum2_const_mul
  rw [ricForm, hsplit, sum_id2_mul]

/-! ## Linearity of the Ricci quadratic form -/

lemma ricForm_add (A B : Curv4 n) (v : Fin n → ℝ) :
    ricForm (A + B) v = ricForm A v + ricForm B v := by
  show (∑ i, ∑ j, ric (A + B) i j * v i * v j)
      = (∑ i, ∑ j, ric A i j * v i * v j) + (∑ i, ∑ j, ric B i j * v i * v j)
  have hpt : ∀ i j, ric (A + B) i j * v i * v j = ric A i j * v i * v j + ric B i j * v i * v j := by
    intro i j; rw [ric_add_linv]; ring
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hpt i j))]
  simp only [Finset.sum_add_distrib]

lemma ricForm_smul (c : ℝ) (A : Curv4 n) (v : Fin n → ℝ) :
    ricForm (c • A) v = c * ricForm A v := by
  show (∑ i, ∑ j, ric (c • A) i j * v i * v j) = c * (∑ i, ∑ j, ric A i j * v i * v j)
  rw [show (∑ i, ∑ j, ric (c • A) i j * v i * v j)
      = ∑ i, ∑ j, c * (ric A i j * v i * v j) from by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [ric_smul_linv]; ring]
  exact sum2_const_mul

lemma ricForm_sub (A B : Curv4 n) (v : Fin n → ℝ) :
    ricForm (A - B) v = ricForm A v - ricForm B v := by
  show (∑ i, ∑ j, ric (A - B) i j * v i * v j)
      = (∑ i, ∑ j, ric A i j * v i * v j) - (∑ i, ∑ j, ric B i j * v i * v j)
  have hpt : ∀ i j, ric (A - B) i j * v i * v j = ric A i j * v i * v j - ric B i j * v i * v j := by
    intro i j; rw [ric_sub]; ring
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hpt i j))]
  simp only [Finset.sum_sub_distrib]

/-- The Ricci quadratic form of `linv a b Y`. -/
lemma qform_ric_linv (n : ℕ) (a b : ℝ) {Y : Curv4 n} (v : Fin n → ℝ) :
    ricForm (linv a b Y) v
      = ricForm Y v - (b / (1 + ((n : ℝ) - 2) * b)) * (((n : ℝ) - 2)
            * (ricForm Y v - (scalAlg Y / (n : ℝ)) * (∑ i, v i * v i)))
        - ((a / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * a) * scalAlg Y)
            * (2 * (n : ℝ) - 2) * (∑ i, v i * v i) := by
  have hlinv : linv a b Y
      = Y - (b / (1 + ((n : ℝ) - 2) * b)) • knProd (ric0 Y) (id2 n)
        - (((a / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * a) * scalAlg Y))
            • knProd (id2 n) (id2 n) := rfl
  rw [hlinv, ricForm_sub, ricForm_sub, ricForm_smul, ricForm_smul]
  rw [ricForm_knProd_id2, ricForm_knProd_id2_id2, qform_ric0]
  have htr : (∑ k, ric0 Y k k) = 0 := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have hn' : ((n : ℝ)) ≠ 0 := by
        exact_mod_cast (Nat.pos_iff_ne_zero.mp hn)
      have hdiag : (∑ i : Fin n, ric Y i i) = scalAlg Y := by
        simp only [scalAlg, ric]; rw [Finset.sum_comm]
      have hid : (∑ i : Fin n, id2 n i i) = (n : ℝ) := by
        simp [id2, Finset.sum_const, nsmul_eq_mul]
      have hsum : (∑ k, ric0 Y k k)
          = (∑ k, ric Y k k) - (scalAlg Y / (n : ℝ)) * (∑ k, id2 n k k) := by
        simp only [ric0, Finset.sum_sub_distrib]
        rw [Finset.mul_sum]
      rw [hsum, hdiag, hid]
      field_simp
      ring
  rw [htr]
  ring

end Work.Diff.Alg.Pinch.RFAux

namespace Work.Diff.Alg.Pinch.RFAux

open Finset Submission.Diff.Alg Matrix

variable {n : ℕ}

/-! ## Contraction of `ℓ_{a,b}(S)` against `v ⊗ v` -/

/-- The double contraction of `ℓ_{a,b}(S)` against `v ⊗ v`, in terms of `Nz S v`, of the
`Ric₀`-contraction and of the identity contribution.  Uses that `v` is an eigenvector of `Ric₀`
with eigenvalue `μ`. -/
lemma Nz_ell_decomp (n : ℕ) {a b μ : ℝ} {S : Curv4 n} (hS : IsAlgCurv S) {v : Fin n → ℝ}
    (heig : ∀ i, (∑ j, ric0 S i j * v j) = μ * v i) (p q : Fin n) :
    (∑ i, ∑ j, (ell a b S) i p j q * v i * v j)
      = Nz S v p q + b * (μ * (∑ i, v i * v i) * (if p = q then (1 : ℝ) else 0)
            - 2 * μ * v p * v q + (∑ i, v i * v i) * ric0 S p q)
        + (a / (n : ℝ) * scalAlg S)
            * (2 * (∑ i, v i * v i) * (if p = q then (1 : ℝ) else 0) - 2 * v p * v q) := by
  have hAvv : (∑ i, ∑ j, ric0 S i j * v i * v j) = μ * (∑ i, v i * v i) := by
    rw [show (∑ i, ∑ j, ric0 S i j * v i * v j) = ∑ i, (∑ j, ric0 S i j * v j) * v i from by
      apply Finset.sum_congr rfl; intro i _
      rw [show (∑ j, ric0 S i j * v i * v j) = (∑ j, ric0 S i j * v j) * v i from by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro j _; ring]]
    rw [Finset.sum_congr rfl (fun i _ => by rw [heig i])]
    rw [show (∑ i, μ * v i * v i) = μ * (∑ i, v i * v i) from by
      rw [show (∑ i, μ * v i * v i) = ∑ i, μ * (v i * v i) from by
        apply Finset.sum_congr rfl; intro i _; ring]
      rw [Finset.mul_sum]]
  have hc1 := knProd_id2_contraction n (A := ric0 S) (fun i j => ric0_symm hS i j) v p q
  have hc2 := knProd_id2_id2_contraction n v p q
  simp only [ell]
  rw [show (∑ i, ∑ j, (S + b • knProd (ric0 S) (id2 n)
        + (a / (n : ℝ) * scalAlg S) • knProd (id2 n) (id2 n)) i p j q * v i * v j)
      = (∑ i, ∑ j, S i p j q * v i * v j)
        + b * (∑ i, ∑ j, knProd (ric0 S) (id2 n) i p j q * v i * v j)
        + (a / (n : ℝ) * scalAlg S)
            * (∑ i, ∑ j, knProd (id2 n) (id2 n) i p j q * v i * v j) from by
    have hpt : ∀ i j, (S + b • knProd (ric0 S) (id2 n)
          + (a / (n : ℝ) * scalAlg S) • knProd (id2 n) (id2 n)) i p j q * v i * v j
        = S i p j q * v i * v j + b * (knProd (ric0 S) (id2 n) i p j q * v i * v j)
          + (a / (n : ℝ) * scalAlg S)
              * (knProd (id2 n) (id2 n) i p j q * v i * v j) := by
      intro i j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hpt i j))]
    simp only [Finset.sum_add_distrib]
    rw [show (∑ i, ∑ j, b * (knProd (ric0 S) (id2 n) i p j q * v i * v j))
        = b * (∑ i, ∑ j, knProd (ric0 S) (id2 n) i p j q * v i * v j) from sum2_const_mul]
    rw [show (∑ i, ∑ j, (a / (n : ℝ) * scalAlg S)
          * (knProd (id2 n) (id2 n) i p j q * v i * v j))
        = (a / (n : ℝ) * scalAlg S)
            * (∑ i, ∑ j, knProd (id2 n) (id2 n) i p j q * v i * v j) from sum2_const_mul]]
  rw [hc1, hc2, hAvv, heig p, heig q]
  simp only [Nz]
  ring_nf

end Work.Diff.Alg.Pinch.RFAux

namespace Work.Diff.Alg.Pinch.RFAux

open Finset Submission.Diff.Alg Matrix

variable {n : ℕ}

/-- `Ric₀ v = μ v`, in the notation of the `bw` quantities. -/
lemma ric0_eigen_bw {S : Curv4 n} (hS : IsAlgCurv S) {b : ℝ} (hric : RicPinch (ccP n b) S)
    {v : Fin n → ℝ}
    (htight : (ccP n b * scalAlg S / (n : ℝ)) * (∑ i, v i * v i)
      = ∑ i, ∑ j, ric S i j * v i * v j) (i : Fin n) :
    (∑ j, ric0 S i j * v j) = bwμ n b (scalAlg S) * v i := by
  rw [ric0_eigen_of_tight hS hric htight i]
  simp only [bwμ, bwΛ]

/-- The Ricci tensor of `ℓ_{a,b}(S)`, split off the traceless part. -/
lemma zeta_eq (n : ℕ) (hn0 : ((n : ℝ)) ≠ 0) (a b : ℝ) {S : Curv4 n} (hS : IsAlgCurv S)
    (p q : Fin n) :
    ric (ell a b S) p q
      = (1 + ((n : ℝ) - 2) * b) * ric0 S p q
        + ((1 + 2 * ((n : ℝ) - 1) * a) * scalAlg S / (n : ℝ))
            * (if p = q then (1 : ℝ) else 0) := by
  rw [ric_ell_form n hn0 a b hS p q]
  simp only [ric0, id2]
  field_simp
  ring

/-- `Σ_p Nz S v p p = Λ · |v|²`. -/
lemma tr_Nz_bw {S : Curv4 n} (hS : IsAlgCurv S) {b : ℝ} {v : Fin n → ℝ}
    (htight : (ccP n b * scalAlg S / (n : ℝ)) * (∑ i, v i * v i)
      = ∑ i, ∑ j, ric S i j * v i * v j) :
    (∑ p, Nz S v p p) = bwΛ n b (scalAlg S) * (∑ i, v i * v i) := by
  rw [tr_Nz_eq hS v]
  show (∑ i, ∑ j, ric S i j * v i * v j) = bwΛ n b (scalAlg S) * (∑ i, v i * v i)
  rw [← htight]
  simp only [bwΛ]

/-- The pairing bound: `Σ_{pq} Ric₀(S)_{pq} Nz_{pq} ≥ μ · tr Nz`. -/
lemma ric0_Nz_lower {S : Curv4 n} (hS : IsAlgCurv S) (hP : InPIC2 S) {b : ℝ}
    (hric : RicPinch (ccP n b) S) {v : Fin n → ℝ} :
    bwμ n b (scalAlg S) * (∑ p, Nz S v p p)
      ≤ ∑ p, ∑ q, ric0 S p q * Nz S v p q := by
  have hpsdA : (ricMat S - (ccP n b * scalAlg S / (n : ℝ)) • 1).PosSemidef :=
    ric_sub_posSemidef hS hric
  have hpsdN : (Nz S v).PosSemidef := NzMat_posSemidef hS hP v
  have hpair : 0 ≤ ∑ p, ∑ q, (ricMat S - (ccP n b * scalAlg S / (n : ℝ)) • 1) p q * Nz S v p q :=
    psd_pairing_mat hpsdA hpsdN
  have hsplit : (∑ p, ∑ q, (ricMat S - (ccP n b * scalAlg S / (n : ℝ)) • 1) p q * Nz S v p q)
      = (∑ p, ∑ q, ric S p q * Nz S v p q)
        - (ccP n b * scalAlg S / (n : ℝ)) * (∑ p, Nz S v p p) := by
    have hpt : ∀ p q, (ricMat S - (ccP n b * scalAlg S / (n : ℝ)) • 1) p q * Nz S v p q
        = ric S p q * Nz S v p q
          - (ccP n b * scalAlg S / (n : ℝ)) * ((if p = q then (1 : ℝ) else 0) * Nz S v p q) := by
      intro p q
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, ricMat, id2]
      ring
    rw [Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => hpt p q))]
    simp only [Finset.sum_sub_distrib]
    congr 1
    · rw [show (∑ p, ∑ q, (ccP n b * scalAlg S / (n : ℝ))
            * ((if p = q then (1 : ℝ) else 0) * Nz S v p q))
          = (ccP n b * scalAlg S / (n : ℝ))
              * (∑ p, ∑ q, (if p = q then (1 : ℝ) else 0) * Nz S v p q) from sum2_const_mul]
      congr 1
      apply Finset.sum_congr rfl; intro p _
      rw [Finset.sum_eq_single p]
      · simp
      · intro q _ hq; rw [if_neg (fun h : p = q => hq h.symm)]; ring
      · intro h; exact absurd (Finset.mem_univ p) h
  have hric0split : (∑ p, ∑ q, ric0 S p q * Nz S v p q)
      = (∑ p, ∑ q, ric S p q * Nz S v p q)
        - (scalAlg S / (n : ℝ)) * (∑ p, Nz S v p p) := by
    have hpt : ∀ p q, ric0 S p q * Nz S v p q
        = ric S p q * Nz S v p q
          - (scalAlg S / (n : ℝ)) * ((if p = q then (1 : ℝ) else 0) * Nz S v p q) := by
      intro p q
      simp only [ric0, id2]
      ring
    rw [Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => hpt p q))]
    simp only [Finset.sum_sub_distrib]
    congr 1
    · rw [show (∑ p, ∑ q, (scalAlg S / (n : ℝ)) * ((if p = q then (1 : ℝ) else 0) * Nz S v p q))
          = (scalAlg S / (n : ℝ)) * (∑ p, ∑ q, (if p = q then (1 : ℝ) else 0) * Nz S v p q) from
        sum2_const_mul]
      congr 1
      apply Finset.sum_congr rfl; intro p _
      rw [Finset.sum_eq_single p]
      · simp
      · intro q _ hq; rw [if_neg (fun h : p = q => hq h.symm)]; ring
      · intro h; exact absurd (Finset.mem_univ p) h
  rw [hric0split]
  have h1 : (ccP n b * scalAlg S / (n : ℝ)) * (∑ p, Nz S v p p) ≤ ∑ p, ∑ q, ric S p q * Nz S v p q := by
    linarith [hpair, hsplit]
  have hμ : bwμ n b (scalAlg S) = ccP n b * scalAlg S / (n : ℝ) - scalAlg S / (n : ℝ) := rfl
  rw [hμ]
  linarith [h1]

end Work.Diff.Alg.Pinch.RFAux

namespace Work.Diff.Alg.Pinch.RFAux

open Finset Submission.Diff.Alg Matrix

variable {n : ℕ}

/-- The two `N'`-correction coefficients appearing in `Nz_ell_decomp`. -/
noncomputable def bwA2 (n : ℕ) (b s : ℝ) (v : Fin n → ℝ) (S : Curv4 n) (p q : Fin n) : ℝ :=
  bwμ n b s * (∑ i, v i * v i) * (if p = q then (1 : ℝ) else 0)
    - 2 * bwμ n b s * v p * v q + (∑ i, v i * v i) * ric0 S p q

noncomputable def bwA3 (n : ℕ) (v : Fin n → ℝ) (p q : Fin n) : ℝ :=
  2 * (∑ i, v i * v i) * (if p = q then (1 : ℝ) else 0) - 2 * v p * v q

/-- `Σ_p ζ_pp = κ · n`. -/
lemma sum_zeta_diag (n : ℕ) (hn0 : ((n : ℝ)) ≠ 0) {b : ℝ} {S : Curv4 n} (hS : IsAlgCurv S) :
    (∑ p, ric (ell (ccA n b) b S) p p) = bwκ n b (scalAlg S) * (n : ℝ) := by
  have hpt : ∀ p, ric (ell (ccA n b) b S) p p
      = bwA0 n b * ric0 S p p + bwκ n b (scalAlg S) := by
    intro p
    rw [zeta_eq n hn0 (ccA n b) b hS p p]
    simp only [bwA0, bwκ]
    simp
  rw [Finset.sum_congr rfl (fun p _ => hpt p)]
  rw [Finset.sum_add_distrib]
  have htr : (∑ p, ric0 S p p) = 0 := ellinv_sum_ric0_diag hS
  rw [show (∑ p, bwA0 n b * ric0 S p p) = bwA0 n b * (∑ p, ric0 S p p) from
    (Finset.mul_sum Finset.univ (fun p => ric0 S p p) (bwA0 n b)).symm]
  rw [htr, mul_zero, zero_add]
  rw [show (∑ _p : Fin n, bwκ n b (scalAlg S)) = (n : ℝ) * bwκ n b (scalAlg S) from by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]]
  ring

/-- `Σ_{pq} ζ_pq v_p v_q = A₀ μ |v|² + κ |v|²`. -/
lemma sum_zeta_vv (n : ℕ) (hn0 : ((n : ℝ)) ≠ 0) {b : ℝ} {S : Curv4 n} (hS : IsAlgCurv S)
    {v : Fin n → ℝ} (hμ : (∑ i, ∑ j, ric0 S i j * v i * v j) = bwμ n b (scalAlg S)
      * (∑ i, v i * v i)) :
    (∑ p, ∑ q, ric (ell (ccA n b) b S) p q * v p * v q)
      = bwA0 n b * bwμ n b (scalAlg S) * (∑ i, v i * v i)
        + bwκ n b (scalAlg S) * (∑ i, v i * v i) := by
  have hpt : ∀ p q, ric (ell (ccA n b) b S) p q * v p * v q
      = bwA0 n b * (ric0 S p q * v p * v q)
        + bwκ n b (scalAlg S) * ((if p = q then (1 : ℝ) else 0) * v p * v q) := by
    intro p q
    rw [zeta_eq n hn0 (ccA n b) b hS p q]
    simp only [bwA0, bwκ]
    ring
  rw [Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => hpt p q))]
  simp only [Finset.sum_add_distrib]
  rw [show (∑ p, ∑ q, bwA0 n b * (ric0 S p q * v p * v q))
      = bwA0 n b * (∑ p, ∑ q, ric0 S p q * v p * v q) from sum2_const_mul]
  rw [show (∑ p, ∑ q, bwκ n b (scalAlg S) * ((if p = q then (1 : ℝ) else 0) * v p * v q))
      = bwκ n b (scalAlg S) * (∑ p, ∑ q, (if p = q then (1 : ℝ) else 0) * v p * v q) from
    sum2_const_mul]
  rw [hμ]
  have hdelta : (∑ p, ∑ q, (if p = q then (1 : ℝ) else 0) * v p * v q) = ∑ p, v p * v p := by
    apply Finset.sum_congr rfl; intro p _
    rw [Finset.sum_eq_single p]
    · simp
    · intro q _ hq; rw [if_neg (fun h : p = q => hq h.symm)]; ring
    · intro h; exact absurd (Finset.mem_univ p) h
  rw [hdelta]
  ring

/-- `Σ_{pq} ζ_pq Ric₀(S)_pq = A₀ |Ric₀|²`. -/
lemma sum_zeta_ric0 (n : ℕ) (hn0 : ((n : ℝ)) ≠ 0) {b : ℝ} {S : Curv4 n} (hS : IsAlgCurv S) :
    (∑ p, ∑ q, ric (ell (ccA n b) b S) p q * ric0 S p q)
      = bwA0 n b * (∑ p, ∑ q, ric0 S p q * ric0 S p q) := by
  have hpt : ∀ p q, ric (ell (ccA n b) b S) p q * ric0 S p q
      = bwA0 n b * (ric0 S p q * ric0 S p q)
        + bwκ n b (scalAlg S) * ((if p = q then (1 : ℝ) else 0) * ric0 S p q) := by
    intro p q
    rw [zeta_eq n hn0 (ccA n b) b hS p q]
    simp only [bwA0, bwκ]
    ring
  rw [Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => hpt p q))]
  simp only [Finset.sum_add_distrib]
  rw [show (∑ p, ∑ q, bwA0 n b * (ric0 S p q * ric0 S p q))
      = bwA0 n b * (∑ p, ∑ q, ric0 S p q * ric0 S p q) from sum2_const_mul]
  rw [show (∑ p, ∑ q, bwκ n b (scalAlg S) * ((if p = q then (1 : ℝ) else 0) * ric0 S p q))
      = bwκ n b (scalAlg S) * (∑ p, ∑ q, (if p = q then (1 : ℝ) else 0) * ric0 S p q) from
    sum2_const_mul]
  have htr : (∑ p, ∑ q, (if p = q then (1 : ℝ) else 0) * ric0 S p q) = 0 := by
    rw [show (∑ p, ∑ q, (if p = q then (1 : ℝ) else 0) * ric0 S p q)
        = ∑ p, ric0 S p p from by
      apply Finset.sum_congr rfl; intro p _
      rw [Finset.sum_eq_single p]
      · simp
      · intro q _ hq; rw [if_neg (fun h : p = q => hq h.symm)]; ring
      · intro h; exact absurd (Finset.mem_univ p) h]
    exact ellinv_sum_ric0_diag hS
  rw [htr, mul_zero, add_zero]

/-- `scalAlg (Q (ℓ S)) = 2 (A₀² |Ric₀|² + κ² n)`. -/
lemma scalAlg_Q_ell (n : ℕ) (hn0 : ((n : ℝ)) ≠ 0) {b : ℝ} {S : Curv4 n} (hS : IsAlgCurv S) :
    scalAlg (Q (ell (ccA n b) b S)) = bwsQY n b (scalAlg S) (∑ p, ∑ q, ric0 S p q ^ 2) := by
  rw [scalAlg_Q n (ell_isAlgCurv n (ccA n b) b hS)]
  have hpt : ∀ p q, ric (ell (ccA n b) b S) p q * ric (ell (ccA n b) b S) p q
      = bwA0 n b ^ 2 * (ric0 S p q * ric0 S p q)
        + 2 * bwA0 n b * bwκ n b (scalAlg S) * ((if p = q then (1 : ℝ) else 0) * ric0 S p q)
        + bwκ n b (scalAlg S) ^ 2 * ((if p = q then (1 : ℝ) else 0) ^ 2) := by
    intro p q
    rw [zeta_eq n hn0 (ccA n b) b hS p q]
    simp only [bwA0, bwκ]
    by_cases h : p = q
    · simp [h]; ring
    · simp [h]; ring
  rw [Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => hpt p q))]
  simp only [Finset.sum_add_distrib]
  have h1 : (∑ p, ∑ q, bwA0 n b ^ 2 * (ric0 S p q * ric0 S p q))
      = bwA0 n b ^ 2 * (∑ p, ∑ q, ric0 S p q * ric0 S p q) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro p _
    rw [Finset.mul_sum]
  have h2 : (∑ p, ∑ q, 2 * bwA0 n b * bwκ n b (scalAlg S) * ((if p = q then (1 : ℝ) else 0) * ric0 S p q))
      = 2 * bwA0 n b * bwκ n b (scalAlg S)
          * (∑ p, ∑ q, (if p = q then (1 : ℝ) else 0) * ric0 S p q) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro p _
    rw [Finset.mul_sum]
  have h3 : (∑ p : Fin n, ∑ q : Fin n, bwκ n b (scalAlg S) ^ 2 * ((if p = q then (1 : ℝ) else 0) ^ 2))
      = bwκ n b (scalAlg S) ^ 2 * (∑ p : Fin n, ∑ q : Fin n, (if p = q then (1 : ℝ) else 0) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro p _
    rw [Finset.mul_sum]
  rw [h1, h2, h3]
  have htr : (∑ p, ∑ q, (if p = q then (1 : ℝ) else 0) * ric0 S p q) = 0 := by
    rw [show (∑ p, ∑ q, (if p = q then (1 : ℝ) else 0) * ric0 S p q) = ∑ p, ric0 S p p from by
      apply Finset.sum_congr rfl; intro p _
      rw [Finset.sum_eq_single p]
      · simp
      · intro q _ hq; rw [if_neg (fun h : p = q => hq h.symm)]; ring
      · intro h; exact absurd (Finset.mem_univ p) h]
    exact ellinv_sum_ric0_diag hS
  have hsq : (∑ p : Fin n, ∑ q : Fin n, (if p = q then (1 : ℝ) else 0) ^ 2) = (n : ℝ) := by
    have hinner : ∀ p : Fin n, (∑ q : Fin n, (if p = q then (1 : ℝ) else 0) ^ 2) = 1 := by
      intro p
      rw [Finset.sum_eq_single p]
      · simp
      · intro q _ hq; rw [if_neg (fun h : p = q => hq h.symm)]; norm_num
      · intro h; exact absurd (Finset.mem_univ p) h
    rw [Finset.sum_congr rfl (fun p _ => hinner p)]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [htr, hsq]
  simp only [bwsQY]
  ring

end Work.Diff.Alg.Pinch.RFAux

namespace Work.Diff.Alg.Pinch.RFAux

open Finset Submission.Diff.Alg Matrix

variable {n : ℕ}

/-- Explicit-argument form of "a constant may be moved out of a double sum". -/
lemma sum2_const_mul_ex (m : ℕ) (f : Fin m → Fin m → ℝ) (c : ℝ) :
    (∑ i, ∑ j, c * f i j) = c * (∑ i, ∑ j, f i j) := by
  rw [show (∑ i : Fin m, ∑ j : Fin m, c * f i j)
      = ∑ i : Fin m, c * (∑ j : Fin m, f i j) from by
    apply Finset.sum_congr rfl; intro i _
    exact (Finset.mul_sum Finset.univ (fun j => f i j) c).symm]
  exact (Finset.mul_sum Finset.univ (fun i => ∑ j : Fin m, f i j) c).symm

/-- The `A₂`-sum: `Σ_{pq} ζ_pq (A₂)_pq = bwS2`. -/
lemma sum_zeta_A2 (n : ℕ) (hn0 : ((n : ℝ)) ≠ 0) {b : ℝ} {S : Curv4 n} (hS : IsAlgCurv S)
    {v : Fin n → ℝ}
    (hμ : (∑ i, ∑ j, ric0 S i j * v i * v j) = bwμ n b (scalAlg S) * (∑ i, v i * v i)) :
    (∑ p, ∑ q, ric (ell (ccA n b) b S) p q * bwA2 n b (scalAlg S) v S p q)
      = bwS2 n b (scalAlg S) (∑ p, ∑ q, ric0 S p q ^ 2) (∑ i, v i * v i) := by
  have hexp : (∑ p, ∑ q, ric (ell (ccA n b) b S) p q * bwA2 n b (scalAlg S) v S p q)
      = bwμ n b (scalAlg S) * (∑ i, v i * v i) * (∑ p, ric (ell (ccA n b) b S) p p)
        - 2 * bwμ n b (scalAlg S)
            * (∑ p, ∑ q, ric (ell (ccA n b) b S) p q * v p * v q)
        + (∑ i, v i * v i) * (∑ p, ∑ q, ric (ell (ccA n b) b S) p q * ric0 S p q) := by
    have hpt : ∀ p q, ric (ell (ccA n b) b S) p q * bwA2 n b (scalAlg S) v S p q
        = bwμ n b (scalAlg S) * (∑ i, v i * v i)
            * ((if p = q then (1 : ℝ) else 0) * ric (ell (ccA n b) b S) p q)
          - 2 * bwμ n b (scalAlg S) * (ric (ell (ccA n b) b S) p q * v p * v q)
          + (∑ i, v i * v i) * (ric (ell (ccA n b) b S) p q * ric0 S p q) := by
      intro p q
      simp only [bwA2]
      ring
    rw [Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => hpt p q))]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [sum2_const_mul_ex n
      (fun p q => (if p = q then (1 : ℝ) else 0) * ric (ell (ccA n b) b S) p q)
      (bwμ n b (scalAlg S) * (∑ i, v i * v i))]
    rw [sum2_const_mul_ex n
      (fun p q => ric (ell (ccA n b) b S) p q * v p * v q) (2 * bwμ n b (scalAlg S))]
    rw [sum2_const_mul_ex n
      (fun p q => ric (ell (ccA n b) b S) p q * ric0 S p q) (∑ i, v i * v i)]
    congr 1
    rw [show (∑ p, ∑ q, (if p = q then (1 : ℝ) else 0) * ric (ell (ccA n b) b S) p q)
        = ∑ p, ric (ell (ccA n b) b S) p p from by
      apply Finset.sum_congr rfl; intro p _
      rw [Finset.sum_eq_single p]
      · simp
      · intro q _ hq; rw [if_neg (fun h : p = q => hq h.symm)]; ring
      · intro h; exact absurd (Finset.mem_univ p) h]
  rw [hexp, sum_zeta_diag n hn0 hS, sum_zeta_vv n hn0 hS hμ, sum_zeta_ric0 n hn0 hS]
  simp only [bwS2]
  ring

/-- The `A₃`-sum: `Σ_{pq} ζ_pq (A₃)_pq = bwS3`. -/
lemma sum_zeta_A3 (n : ℕ) (hn0 : ((n : ℝ)) ≠ 0) {b : ℝ} {S : Curv4 n} (hS : IsAlgCurv S)
    {v : Fin n → ℝ}
    (hμ : (∑ i, ∑ j, ric0 S i j * v i * v j) = bwμ n b (scalAlg S) * (∑ i, v i * v i)) :
    (∑ p, ∑ q, ric (ell (ccA n b) b S) p q * bwA3 n v p q)
      = bwS3 n b (scalAlg S) (∑ i, v i * v i) := by
  have hexp : (∑ p, ∑ q, ric (ell (ccA n b) b S) p q * bwA3 n v p q)
      = 2 * (∑ i, v i * v i) * (∑ p, ric (ell (ccA n b) b S) p p)
        - 2 * (∑ p, ∑ q, ric (ell (ccA n b) b S) p q * v p * v q) := by
    have hpt : ∀ p q, ric (ell (ccA n b) b S) p q * bwA3 n v p q
        = 2 * (∑ i, v i * v i) * ((if p = q then (1 : ℝ) else 0) * ric (ell (ccA n b) b S) p q)
          - 2 * (ric (ell (ccA n b) b S) p q * v p * v q) := by
      intro p q
      simp only [bwA3]
      ring
    rw [Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => hpt p q))]
    simp only [Finset.sum_sub_distrib]
    rw [sum2_const_mul_ex n
      (fun p q => (if p = q then (1 : ℝ) else 0) * ric (ell (ccA n b) b S) p q)
      (2 * (∑ i, v i * v i))]
    rw [sum2_const_mul_ex n (fun p q => ric (ell (ccA n b) b S) p q * v p * v q) 2]
    congr 1
    rw [show (∑ p, ∑ q, (if p = q then (1 : ℝ) else 0) * ric (ell (ccA n b) b S) p q)
        = ∑ p, ric (ell (ccA n b) b S) p p from by
      apply Finset.sum_congr rfl; intro p _
      rw [Finset.sum_eq_single p]
      · simp
      · intro q _ hq; rw [if_neg (fun h : p = q => hq h.symm)]; ring
      · intro h; exact absurd (Finset.mem_univ p) h]
  rw [hexp, sum_zeta_diag n hn0 hS, sum_zeta_vv n hn0 hS hμ]
  simp only [bwS3]
  ring

/-- The `Nz`-part of the estimate: `bwS1 ≤ Σ_{pq} ζ_pq Nz_pq`. -/
lemma sum_zeta_Nz_lower (n : ℕ) (hn : 2 ≤ n) {b : ℝ} (hb : 0 < b)
    (hn0 : ((n : ℝ)) ≠ 0) {S : Curv4 n} (hS : IsAlgCurv S) (hP : InPIC2 S)
    (hric : RicPinch (ccP n b) S) {v : Fin n → ℝ}
    (htight : (ccP n b * scalAlg S / (n : ℝ)) * (∑ i, v i * v i)
      = ∑ i, ∑ j, ric S i j * v i * v j) :
    bwS1 n b (scalAlg S) (∑ i, v i * v i)
      ≤ ∑ p, ∑ q, ric (ell (ccA n b) b S) p q * Nz S v p q := by
  have hsplit : (∑ p, ∑ q, ric (ell (ccA n b) b S) p q * Nz S v p q)
      = bwA0 n b * (∑ p, ∑ q, ric0 S p q * Nz S v p q)
        + bwκ n b (scalAlg S) * (∑ p, Nz S v p p) := by
    have hpt : ∀ p q, ric (ell (ccA n b) b S) p q * Nz S v p q
        = bwA0 n b * (ric0 S p q * Nz S v p q)
          + bwκ n b (scalAlg S) * ((if p = q then (1 : ℝ) else 0) * Nz S v p q) := by
      intro p q
      rw [zeta_eq n hn0 (ccA n b) b hS p q]
      simp only [bwA0, bwκ]
      ring
    rw [Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => hpt p q))]
    simp only [Finset.sum_add_distrib]
    rw [sum2_const_mul_ex n (fun p q => ric0 S p q * Nz S v p q) (bwA0 n b)]
    rw [sum2_const_mul_ex n (fun p q => (if p = q then (1 : ℝ) else 0) * Nz S v p q)
      (bwκ n b (scalAlg S))]
    congr 1
    rw [show (∑ p, ∑ q, (if p = q then (1 : ℝ) else 0) * Nz S v p q) = ∑ p, Nz S v p p from by
      apply Finset.sum_congr rfl; intro p _
      rw [Finset.sum_eq_single p]
      · simp
      · intro q _ hq; rw [if_neg (fun h : p = q => hq h.symm)]; ring
      · intro h; exact absurd (Finset.mem_univ p) h]
  rw [hsplit, tr_Nz_bw hS htight]
  have h1 := ric0_Nz_lower hS hP hric (v := v)
  rw [tr_Nz_bw hS htight] at h1
  have hgoal : bwS1 n b (scalAlg S) (∑ i, v i * v i)
      = bwA0 n b * (bwΛ n b (scalAlg S) * (∑ i, v i * v i) * bwμ n b (scalAlg S))
        + bwκ n b (scalAlg S) * (bwΛ n b (scalAlg S) * (∑ i, v i * v i)) := by
    simp only [bwS1]
    ring
  rw [hgoal]
  have hA0 : 0 ≤ bwA0 n b := by
    have hnm2 : (0 : ℝ) ≤ ((n : ℝ) - 2) := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    simp only [bwA0]
    nlinarith [hb]
  nlinarith [h1, hA0]

/-- The lower bound for `ricForm (Q (ℓ S)) v`. -/
lemma QY_lower (n : ℕ) (hn : 2 ≤ n) {b : ℝ} (hb : 0 < b) (hb' : b ≤ 1 / 2) {S : Curv4 n}
    (hS : IsAlgCurv S) (hP : InPIC2 S) (hric : RicPinch (ccP n b) S) {v : Fin n → ℝ}
    (htight : (ccP n b * scalAlg S / (n : ℝ)) * (∑ i, v i * v i)
      = ∑ i, ∑ j, ric S i j * v i * v j) :
    2 * (bwS1 n b (scalAlg S) (∑ i, v i * v i)
          + b * bwS2 n b (scalAlg S) (∑ p, ∑ q, ric0 S p q ^ 2) (∑ i, v i * v i)
          + (ccA n b * scalAlg S / (n : ℝ)) * bwS3 n b (scalAlg S) (∑ i, v i * v i))
      ≤ ricForm (Q (ell (ccA n b) b S)) v := by
  have hn0 : ((n : ℝ)) ≠ 0 := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast (Nat.pos_iff_ne_zero.mp this)
  have hA0nn : 0 ≤ bwA0 n b := by
    have hnm2 : (0 : ℝ) ≤ ((n : ℝ) - 2) := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    simp only [bwA0]
    nlinarith
  have hμ := fun i => ric0_eigen_bw hS hric htight i
  have hμsum : (∑ i, ∑ j, ric0 S i j * v i * v j) = bwμ n b (scalAlg S) * (∑ i, v i * v i) := by
    rw [show (∑ i, ∑ j, ric0 S i j * v i * v j) = ∑ i, (∑ j, ric0 S i j * v j) * v i from by
      apply Finset.sum_congr rfl; intro i _
      rw [show (∑ j, ric0 S i j * v i * v j) = (∑ j, ric0 S i j * v j) * v i from by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro j _; ring]]
    rw [Finset.sum_congr rfl (fun i _ => by rw [hμ i])]
    rw [show (∑ i, bwμ n b (scalAlg S) * v i * v i)
        = bwμ n b (scalAlg S) * (∑ i, v i * v i) from by
      rw [show (∑ i, bwμ n b (scalAlg S) * v i * v i)
          = ∑ i, bwμ n b (scalAlg S) * (v i * v i) from by
        apply Finset.sum_congr rfl; intro i _; ring]
      rw [Finset.mul_sum]]
  have hQY : ricForm (Q (ell (ccA n b) b S)) v
      = 2 * ∑ p, ∑ q, ric (ell (ccA n b) b S) p q
          * (∑ i, ∑ j, (ell (ccA n b) b S) i p j q * v i * v j) := by
    rw [ricForm]
    exact ricForm_Q n (ell_isAlgCurv n (ccA n b) b hS) v
  have hN' : ∀ p q, (∑ i, ∑ j, (ell (ccA n b) b S) i p j q * v i * v j)
      = Nz S v p q + b * bwA2 n b (scalAlg S) v S p q
        + (ccA n b / (n : ℝ) * scalAlg S) * bwA3 n v p q := by
    intro p q
    exact Nz_ell_decomp n hS hμ p q
  have hsplit : (∑ p, ∑ q, ric (ell (ccA n b) b S) p q
        * (∑ i, ∑ j, (ell (ccA n b) b S) i p j q * v i * v j))
      = (∑ p, ∑ q, ric (ell (ccA n b) b S) p q * Nz S v p q)
        + b * (∑ p, ∑ q, ric (ell (ccA n b) b S) p q * bwA2 n b (scalAlg S) v S p q)
        + (ccA n b / (n : ℝ) * scalAlg S)
            * (∑ p, ∑ q, ric (ell (ccA n b) b S) p q * bwA3 n v p q) := by
    have hpt : ∀ p q, ric (ell (ccA n b) b S) p q
          * (∑ i, ∑ j, (ell (ccA n b) b S) i p j q * v i * v j)
        = ric (ell (ccA n b) b S) p q * Nz S v p q
          + b * (ric (ell (ccA n b) b S) p q * bwA2 n b (scalAlg S) v S p q)
          + (ccA n b / (n : ℝ) * scalAlg S)
              * (ric (ell (ccA n b) b S) p q * bwA3 n v p q) := by
      intro p q; rw [hN' p q]; ring
    rw [Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => hpt p q))]
    simp only [Finset.sum_add_distrib]
    rw [sum2_const_mul_ex n
      (fun p q => ric (ell (ccA n b) b S) p q * bwA2 n b (scalAlg S) v S p q) b]
    rw [sum2_const_mul_ex n
      (fun p q => ric (ell (ccA n b) b S) p q * bwA3 n v p q) (ccA n b / (n : ℝ) * scalAlg S)]
  rw [hQY, hsplit, sum_zeta_A2 n hn0 hS hμsum, sum_zeta_A3 n hn0 hS hμsum]
  have h1 := sum_zeta_Nz_lower n hn hb hn0 hS hP hric htight
  have hcoef : (ccA n b / (n : ℝ) * scalAlg S) = ccA n b * scalAlg S / (n : ℝ) := by ring
  rw [hcoef]
  linarith [h1]

end Work.Diff.Alg.Pinch.RFAux

namespace Work.Diff.Alg.Pinch.RFAux

open Finset Submission.Diff.Alg Matrix

variable {n : ℕ}

/-- A nonzero vector has positive squared length. -/
lemma q_pos_of_ne_zero {v : Fin n → ℝ} (hv : v ≠ 0) : 0 < ∑ i, v i * v i := by
  rcases lt_or_ge 0 (∑ i, v i * v i) with h | h
  · exact h
  · exfalso
    apply hv
    funext i
    have h0 : (∑ j, v j * v j) = 0 :=
      le_antisymm h (Finset.sum_nonneg (fun j _ => mul_self_nonneg _))
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (v j))).mp h0
    exact mul_self_eq_zero.mp (hall i (Finset.mem_univ i))

/-- **Böhm–Wilking one-step strictness of the Ricci form at a tight direction.**

If `S` is a nonzero algebraic curvature tensor with `InPIC2 S` and `Ric ≥ (ccP n b)·scal/n`, and
`v ≠ 0` is a *tight* direction (`ric S v v = (ccP n b · scal S / n) |v|²`), then the transformed
tensor `X = ℓ^{-1}(Q(ℓ S))` satisfies `ric X v v > (ccP n b · scal X / n) |v|²`. -/
theorem ric_X_strict_aux (n : ℕ) (hn2 : 2 ≤ n) {b : ℝ} (hb : 0 < b) (hb' : b ≤ 1 / 2)
    {S : Submission.Diff.Alg.Curv4 n} (hS : Submission.Diff.Alg.IsAlgCurv S) (hS0 : S ≠ 0)
    (hP : Submission.Diff.Alg.InPIC2 S)
    (hric : Work.Diff.Alg.Pinch.RicPinch (Work.Diff.Alg.Pinch.ccP n b) S)
    {v : Fin n → ℝ} (hv : v ≠ 0)
    (htight : (Work.Diff.Alg.Pinch.ccP n b * Submission.Diff.Alg.scalAlg S / (n : ℝ))
      * (∑ i, v i * v i) = ∑ i, ∑ j, Work.Diff.Alg.Pinch.ric S i j * v i * v j) :
    0 < ricForm (linv (ccA n b) b (Q (ell (ccA n b) b S))) v
      - (ccP n b * scalAlg (linv (ccA n b) b (Q (ell (ccA n b) b S))) / (n : ℝ))
          * (∑ i, v i * v i) := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn2
  have hn0 : ((n : ℝ)) ≠ 0 := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast (Nat.pos_iff_ne_zero.mp this)
  have hnm2 : (0 : ℝ) ≤ ((n : ℝ) - 2) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    linarith
  have hq : 0 < ∑ i, v i * v i := q_pos_of_ne_zero hv
  have hspos : 0 < scalAlg S := by
    have h1 : 0 ≤ scalAlg S := (inPIC2_metric_basic n).2.2 S hP
    have h2 : scalAlg S ≠ 0 := fun h => hS0 ((inPIC2_comp_bound n).2 S hP h)
    exact lt_of_le_of_ne h1 (Ne.symm h2)
  have hA0pos : 0 < 1 + ((n : ℝ) - 2) * b := by nlinarith
  have hβ0 : 1 + ((n : ℝ) - 2) * b ≠ 0 := ne_of_gt hA0pos
  have haden : 1 + 2 * ((n : ℝ) - 1) * ccA n b ≠ 0 := ccA_denom_ne hn1 hb hb'
  have hY : IsAlgCurv (ell (ccA n b) b S) := ell_isAlgCurv n (ccA n b) b hS
  have hQYalg : IsAlgCurv (Q (ell (ccA n b) b S)) := Q_isAlgCurv n hY
  have hμeig := fun i => ric0_eigen_bw hS hric htight i
  -- ρ > 0
  have hρ : 0 < ∑ p, ∑ q, ric0 S p q ^ 2 := by
    have hμne : bwμ n b (scalAlg S) ≠ 0 := by
      rw [show bwμ n b (scalAlg S) = (ccP n b - 1) * scalAlg S / (n : ℝ) from by
        simp only [bwμ, bwΛ]; ring]
      apply div_ne_zero
      · apply mul_ne_zero
        · rw [sub_ne_zero]
          intro h
          have h1 : ccP n b < 1 := ccP_lt_one hn1 hb hb'
          linarith
        · exact ne_of_gt hspos
      · exact hn0
    have hcs : ∀ p : Fin n, (∑ j, ric0 S p j * v j) ^ 2
        ≤ (∑ j, ric0 S p j ^ 2) * (∑ j, v j * v j) := by
      intro p
      have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ric0 S p j) v
      simpa only [pow_two] using h
    have h1 : bwμ n b (scalAlg S) ^ 2 * (∑ i, v i * v i)
        ≤ (∑ p, ∑ q, ric0 S p q ^ 2) * (∑ i, v i * v i) := by
      calc bwμ n b (scalAlg S) ^ 2 * (∑ i, v i * v i)
          = ∑ p, (∑ j, ric0 S p j * v j) ^ 2 := by
            rw [show (∑ p, (∑ j, ric0 S p j * v j) ^ 2)
                = ∑ p, (bwμ n b (scalAlg S) * v p) ^ 2 from by
              apply Finset.sum_congr rfl; intro p _; rw [hμeig p]]
            rw [show (∑ p, (bwμ n b (scalAlg S) * v p) ^ 2)
                = bwμ n b (scalAlg S) ^ 2 * (∑ i, v i * v i) from by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl; intro p _; ring]
        _ ≤ ∑ p, (∑ j, ric0 S p j ^ 2) * (∑ j, v j * v j) :=
            Finset.sum_le_sum (fun p _ => hcs p)
        _ = (∑ p, ∑ j, ric0 S p j ^ 2) * (∑ j, v j * v j) := by
            rw [Finset.sum_mul]
    nlinarith [h1, hq, sq_pos_of_ne_zero hμne]
  -- the two estimates
  have hQY := QY_lower n hn2 hb hb' hS hP hric htight
  have hscQY := scalAlg_Q_ell n hn0 (b := b) hS
  -- the two `linv` evaluations
  rw [qform_ric_linv n (ccA n b) b (Y := Q (ell (ccA n b) b S)) v,
    scalAlg_linv n (a := ccA n b) (b := b) hβ0 haden hQYalg]
  -- normalise to the `bw` notation
  have hE : ricForm (Q (ell (ccA n b) b S)) v
        - b / (1 + ((n : ℝ) - 2) * b)
            * (((n : ℝ) - 2) * (ricForm (Q (ell (ccA n b) b S)) v
              - scalAlg (Q (ell (ccA n b) b S)) / (n : ℝ) * (∑ i, v i * v i)))
        - ((ccA n b / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * ccA n b)
            * scalAlg (Q (ell (ccA n b) b S))) * (2 * (n : ℝ) - 2) * (∑ i, v i * v i)
        - (ccP n b * (scalAlg (Q (ell (ccA n b) b S))
            - ((ccA n b / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * ccA n b)
                * scalAlg (Q (ell (ccA n b) b S))) * (2 * (n : ℝ) - 2) * (n : ℝ))
            / (n : ℝ)) * (∑ i, v i * v i)
      = (1 - b / (1 + ((n : ℝ) - 2) * b) * ((n : ℝ) - 2))
          * ricForm (Q (ell (ccA n b) b S)) v
        + (b / (1 + ((n : ℝ) - 2) * b) * ((n : ℝ) - 2) - ccP n b)
            * (scalAlg (Q (ell (ccA n b) b S)) / (n : ℝ)) * (∑ i, v i * v i)
        - ((ccA n b / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * ccA n b))
            * scalAlg (Q (ell (ccA n b) b S)) * (2 * (n : ℝ) - 2) * (∑ i, v i * v i)
            * (1 - ccP n b) := by
    field_simp
    ring
  rw [hE]
  rw [hscQY]
  rw [show (1 - b / (1 + ((n : ℝ) - 2) * b) * ((n : ℝ) - 2)) = 1 / (1 + ((n : ℝ) - 2) * b) from by
    field_simp
    ring]
  rw [show b / (1 + ((n : ℝ) - 2) * b) = bwβ n b from rfl]
  rw [show (ccA n b / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * ccA n b) = bwγ0 n b from rfl]
  have hβnn : 0 ≤ (1 : ℝ) / (1 + ((n : ℝ) - 2) * b) := by positivity
  have hbw := bw_final_algebra n hn2 (s := scalAlg S) (ρ := ∑ p, ∑ q, ric0 S p q ^ 2)
    (q := ∑ i, v i * v i) hb hb' hρ hq
  have hmono : (1 : ℝ) / (1 + ((n : ℝ) - 2) * b)
        * (2 * (bwS1 n b (scalAlg S) (∑ i, v i * v i)
            + b * bwS2 n b (scalAlg S) (∑ p, ∑ q, ric0 S p q ^ 2) (∑ i, v i * v i)
            + (ccA n b * scalAlg S / (n : ℝ)) * bwS3 n b (scalAlg S) (∑ i, v i * v i)))
      ≤ (1 : ℝ) / (1 + ((n : ℝ) - 2) * b) * ricForm (Q (ell (ccA n b) b S)) v :=
    mul_le_mul_of_nonneg_left hQY hβnn
  have hβc : 1 - bwβ n b * ((n : ℝ) - 2) = 1 / (1 + ((n : ℝ) - 2) * b) := by
    rw [show bwβ n b = b / (1 + ((n : ℝ) - 2) * b) from rfl]
    field_simp
    ring
  rw [hβc] at hbw
  linarith [hbw, hmono]

end Work.Diff.Alg.Pinch.RFAux
