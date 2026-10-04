import Mathlib
import Submission.Work.Diff.Alg.Pinch.Base
import Submission.Work.Diff.Alg.q2p_defs
import Submission.Work.Diff.Alg.Pinch.Qop
import Submission.Work.Diff.Alg.Pinch.Qop2
import Submission.Work.Diff.Alg.Pinch.Qop3
import Submission.Work.Diff.Alg.Pinch.Phi_Q1
import Submission.Work.Diff.Alg.Pinch.Phi_Q2
import Submission.Work.Diff.Alg.Pinch.Phi_wedge
import Submission.Work.Diff.Alg.Pinch.secondVariation
import Submission.Work.Diff.Alg.Pinch.Q_isAlgCurv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Tangential invariance of the cone of nonnegative complex sectional curvature

The main result of this file is `inPIC2_Q_pointwise`: if `R` has nonnegative complex sectional
curvature (`InPIC2 R`) and `X = ζ ∧ η` is a degenerate direction (`EFun R x y z w = 0`), then the
Hamilton reaction term at that direction is nonnegative, `0 ≤ EFun (Q R) x y z w`.  Equivalently,
`Q R` lies in the tangent cone of the `PIC2`-cone at `R`.

Proof chain (`X = wedgeF ζ η`, `X̄ = bar X`):

* the dictionary `Phi_wedge` identifies `EFun` with a quarter of the Hermitian form `Phi R · (bar ·)`
  of `R` at `X`;
* the second variation `secondVariation` gives `0 ≤ (Phi R (adF X v) (bar (adF X v))).re` for the
  *shear* directions, hence (reducing a general `v` to its skew part, which is where `Rop R` lives)
  for every `v`;
* this makes `Tmat R X = ad_X^* R̃ ad_X` positive semidefinite and gives the trace hypothesis of
  `trace_mul_posSemidef`, whence `0 ≤ (Tmat R X * Rm R).trace.re`;
* the operator identity `Phi_Q2` expresses `Phi (Q2 R) X X̄` as that trace, while `Phi_Q1` writes
  `Phi (Q1 R) X X̄` as a sum of squares;
* `Q R = Q1 R + Q2 R` and the dictionary convert back to `EFun (Q R) x y z w`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg Matrix
open scoped ComplexOrder

variable {n : ℕ}

/-! ## Trace of a product of a positive semidefinite and a "nonnegative on its range" matrix -/

theorem trace_diag_mul {N : Type*} [Fintype N] [DecidableEq N] (d : N → ℂ) (M : Matrix N N ℂ) :
    (Matrix.diagonal d * M).trace = ∑ i, d i * M i i := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]

theorem trace_four {N : Type*} [Fintype N] (P Q R S : Matrix N N ℂ) :
    (P * (Q * (R * S))).trace = (Q * (R * (S * P))).trace := by
  rw [Matrix.trace_mul_comm P (Q * (R * S))]
  simp only [Matrix.mul_assoc]

/-- If `T` is positive semidefinite and the Hermitian matrix `A` is nonnegative on the range of
`T`, then `tr (T * A)` has nonnegative real part. -/
theorem trace_mul_nonneg {N : Type*} [Fintype N] [DecidableEq N]
    {T A : Matrix N N ℂ} (hT : T.PosSemidef) (hA : A.IsHermitian)
    (h : ∀ v : N → ℂ, 0 ≤ ((star (T *ᵥ v)) ⬝ᵥ (A *ᵥ (T *ᵥ v))).re) :
    0 ≤ ((T * A).trace).re := by
  classical
  have hstarU : star ((hT.1.eigenvectorUnitary : Matrix N N ℂ))
      * (hT.1.eigenvectorUnitary : Matrix N N ℂ) = 1 := Unitary.coe_star_mul_self _
  have hUstar : (hT.1.eigenvectorUnitary : Matrix N N ℂ)
      * star ((hT.1.eigenvectorUnitary : Matrix N N ℂ)) = 1 := Unitary.coe_mul_star_self _
  have hspec : star ((hT.1.eigenvectorUnitary : Matrix N N ℂ)) * T
      * (hT.1.eigenvectorUnitary : Matrix N N ℂ)
      = Matrix.diagonal (RCLike.ofReal ∘ hT.1.eigenvalues) := by
    have h1 := Matrix.IsHermitian.conjStarAlgAut_star_eigenvectorUnitary hT.1
    rw [Unitary.conjStarAlgAut_star_apply] at h1
    exact h1
  have hTeq : (hT.1.eigenvectorUnitary : Matrix N N ℂ)
      * Matrix.diagonal (RCLike.ofReal ∘ hT.1.eigenvalues)
      * star ((hT.1.eigenvectorUnitary : Matrix N N ℂ)) = T := by
    have key : (hT.1.eigenvectorUnitary : Matrix N N ℂ)
        * (star ((hT.1.eigenvectorUnitary : Matrix N N ℂ)) * T
          * (hT.1.eigenvectorUnitary : Matrix N N ℂ))
        * star ((hT.1.eigenvectorUnitary : Matrix N N ℂ)) = T := by
      calc (hT.1.eigenvectorUnitary : Matrix N N ℂ)
          * (star ((hT.1.eigenvectorUnitary : Matrix N N ℂ)) * T
            * (hT.1.eigenvectorUnitary : Matrix N N ℂ))
          * star ((hT.1.eigenvectorUnitary : Matrix N N ℂ))
          = ((hT.1.eigenvectorUnitary : Matrix N N ℂ)
              * star ((hT.1.eigenvectorUnitary : Matrix N N ℂ))) * T
            * ((hT.1.eigenvectorUnitary : Matrix N N ℂ)
              * star ((hT.1.eigenvectorUnitary : Matrix N N ℂ))) := by
            simp only [Matrix.mul_assoc]
        _ = 1 * T * 1 := by rw [hUstar]
        _ = T := by rw [one_mul, mul_one]
    conv_lhs => rw [← hspec]
    exact key
  conv_rhs => rw [← hTeq]
  have htr : ((hT.1.eigenvectorUnitary : Matrix N N ℂ)
        * Matrix.diagonal (RCLike.ofReal ∘ hT.1.eigenvalues)
        * star ((hT.1.eigenvectorUnitary : Matrix N N ℂ)) * A).trace
      = ∑ i, (hT.1.eigenvalues i : ℂ) *
          ((star (hT.1.eigenvectorBasis i).ofLp) ⬝ᵥ (A *ᵥ (hT.1.eigenvectorBasis i).ofLp)) := by
    simp only [Matrix.mul_assoc]
    rw [trace_four, trace_diag_mul]
    congr 1
  rw [htr, Complex.re_sum]
  apply Finset.sum_nonneg; intro i _
  rw [Complex.mul_re]
  have hval_im : ((star (hT.1.eigenvectorBasis i).ofLp)
      ⬝ᵥ (A *ᵥ (hT.1.eigenvectorBasis i).ofLp)).im = 0 := by
    have h2 := Matrix.IsHermitian.im_star_dotProduct_mulVec_self hA (hT.1.eigenvectorBasis i).ofLp
    simpa using h2
  rw [Complex.ofReal_im, hval_im, mul_zero, sub_zero]
  by_cases hlam : hT.1.eigenvalues i = 0
  · rw [hlam]; simp
  · have hpos : 0 < hT.1.eigenvalues i := lt_of_le_of_ne (hT.eigenvalues_nonneg i) (Ne.symm hlam)
    refine mul_nonneg (le_of_lt hpos) ?_
    have heig := Matrix.IsHermitian.mulVec_eigenvectorBasis hT.1 i
    have hu : (hT.1.eigenvectorBasis i).ofLp
        = T *ᵥ (((hT.1.eigenvalues i)⁻¹ : ℝ) • (hT.1.eigenvectorBasis i).ofLp) := by
      rw [Matrix.mulVec_smul, heig, smul_smul]
      rw [inv_mul_cancel₀ (ne_of_gt hpos), one_smul]
    have hh := h (((hT.1.eigenvalues i)⁻¹ : ℝ) • (hT.1.eigenvectorBasis i).ofLp)
    rw [← hu] at hh
    exact hh


/-! ## The Hermitian form of `Rop R` versus `Phi` -/

theorem quad_eq_Phi (R : Curv4 n) (hR : IsAlgCurv R) (w : Fin n × Fin n → ℂ) :
    (star w) ⬝ᵥ (Rm R *ᵥ w) = Phi R w (bar w) := by
  rw [Phi_self_real R hR w, ← Phi_self_star R hR w]
  rfl

theorem Phi_adF_nonneg (R : Curv4 n) (hR : IsAlgCurv R) (hPIC : InPIC2 R) {ζ η : Fin n → ℂ}
    (h0 : Phi R (wedgeF ζ η) (bar (wedgeF ζ η)) = 0) (V : Fin n × Fin n → ℂ) :
    0 ≤ (Phi R (adF (wedgeF ζ η) V) (bar (adF (wedgeF ζ η) V))).re :=
  good_any R hR hPIC h0 V

/-! ## `Tmat R X` is positive semidefinite -/

theorem Tmat_mulVec_form (R : Curv4 n) (X : Fin n × Fin n → ℂ) (v : Fin n × Fin n → ℂ) :
    Tmat R X *ᵥ v = (adMat X)ᴴ *ᵥ (Rop R (adF X v)) := by
  have h1 : Tmat R X = (adMat X)ᴴ * (Rm R * adMat X) := by rw [Tmat, Matrix.mul_assoc]
  rw [h1, ← Matrix.mulVec_mulVec v ((adMat X)ᴴ) (Rm R * adMat X),
    ← Matrix.mulVec_mulVec v (Rm R) (adMat X), adF_mulVec]
  rfl

theorem Tmat_posSemidef (R : Curv4 n) (hR : IsAlgCurv R) (hPIC : InPIC2 R) {ζ η : Fin n → ℂ}
    (h0 : Phi R (wedgeF ζ η) (bar (wedgeF ζ η)) = 0) :
    (Tmat R (wedgeF ζ η)).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (Tmat_isHermitian R hR _) (fun v => ?_)
  have h1 : (star v) ⬝ᵥ (Tmat R (wedgeF ζ η) *ᵥ v)
      = Phi R (adF (wedgeF ζ η) v) (bar (adF (wedgeF ζ η) v)) := by
    rw [Tmat_mulVec_form, dotProduct_conjTranspose_mulVec, adF_mulVec]
    rw [show (star (adF (wedgeF ζ η) v)) ⬝ᵥ (Rop R (adF (wedgeF ζ η) v))
        = (star (adF (wedgeF ζ η) v)) ⬝ᵥ (Rm R *ᵥ (adF (wedgeF ζ η) v)) from rfl]
    rw [quad_eq_Phi R hR]
  rw [h1]
  exact (Phi_self_nonneg_iff R hR _).mpr (Phi_adF_nonneg R hR hPIC h0 v)

/-! ## The trace hypothesis -/

theorem trace_hyp (R : Curv4 n) (hR : IsAlgCurv R) (hPIC : InPIC2 R) {ζ η : Fin n → ℂ}
    (h0 : Phi R (wedgeF ζ η) (bar (wedgeF ζ η)) = 0) (v : Fin n × Fin n → ℂ) :
    0 ≤ ((star (Tmat R (wedgeF ζ η) *ᵥ v)) ⬝ᵥ
        (Rm R *ᵥ (Tmat R (wedgeF ζ η) *ᵥ v))).re := by
  have hXskew : swapF (wedgeF ζ η) = - wedgeF ζ η := swapF_wedgeF ζ η
  -- the degenerate direction for the conjugate bivector
  have h0bar : Phi R (wedgeF (star ζ) (star η))
      (bar (wedgeF (star ζ) (star η))) = 0 := by
    rw [← bar_wedgeF ζ η, bar_bar]
    exact (Phi_comm R hR _ _).trans h0
  have h1 : Tmat R (wedgeF ζ η) *ᵥ v
      = - adF (wedgeF (star ζ) (star η)) (Rop R (adF (wedgeF ζ η) v)) := by
    rw [Tmat_mulVec_form, adMat_conjTranspose_of_skew hXskew, Matrix.neg_mulVec, adF_mulVec,
      bar_wedgeF]
  rw [h1, star_neg, Matrix.mulVec_neg, neg_dotProduct_neg, quad_eq_Phi R hR]
  exact (Phi_self_nonneg_iff R hR _).mp (RCLike.nonneg_iff.mpr
    ⟨Phi_adF_nonneg R hR hPIC h0bar (Rop R (adF (wedgeF ζ η) v)), Phi_self_im R hR _⟩)

/-! ## The main theorem -/

theorem inPIC2_Q_pointwise (n : ℕ) : ∀ R : Submission.Diff.Alg.Curv4 n,
    Submission.Diff.Alg.IsAlgCurv R → Submission.Diff.Alg.InPIC2 R →
      ∀ x y z w : Fin n → ℝ, Work.Diff.Alg.Q2P.EFun R x y z w = 0 →
        0 ≤ Work.Diff.Alg.Q2P.EFun (Submission.Diff.Alg.Q R) x y z w := by
  intro R hR hPIC x y z w h0
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Fin n → ℂ, ∀ i, ζ i = (x i : ℂ) + (y i : ℂ) * Complex.I :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨η, hη⟩ : ∃ η : Fin n → ℂ, ∀ i, η i = (z i : ℂ) + (w i : ℂ) * Complex.I :=
    ⟨_, fun _ => rfl⟩
  have hcreζ : Q2P.cRe ζ = x := by funext i; simp [Q2P.cRe, hζ i]
  have hcimζ : Q2P.cIm ζ = y := by funext i; simp [Q2P.cIm, hζ i]
  have hcreη : Q2P.cRe η = z := by funext i; simp [Q2P.cRe, hη i]
  have hcimη : Q2P.cIm η = w := by funext i; simp [Q2P.cIm, hη i]
  -- the degenerate direction in `Phi` language
  have h0Phi : Phi R (wedgeF ζ η) (bar (wedgeF ζ η)) = 0 := by
    have h := Phi_wedge n R hR ζ η
    rw [hcreζ, hcimζ, hcreη, hcimη, h0] at h
    simpa using h
  -- `Phi (Q R)` splits into the two pieces
  have hsplit : (Phi (Q R) (wedgeF ζ η) (bar (wedgeF ζ η))).re
      = (Phi (Q1 R) (wedgeF ζ η) (bar (wedgeF ζ η))).re
        + (Phi (Q2 R) (wedgeF ζ η) (bar (wedgeF ζ η))).re := by
    rw [Q_eq_Q1_add_Q2, Phi_add]
    exact Complex.add_re _ _
  have hterm1 : 0 ≤ (Phi (Q1 R) (wedgeF ζ η) (bar (wedgeF ζ η))).re := by
    rw [Phi_Q1 n R hR]
    have h2 : (∑ p : Fin n × Fin n, Rop R (wedgeF ζ η) p * Rop R (bar (wedgeF ζ η)) p)
        = ((∑ p : Fin n × Fin n, Complex.normSq (Rop R (wedgeF ζ η) p) : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl; intro p _
      rw [Rop_bar]
      show Rop R (wedgeF ζ η) p * star (Rop R (wedgeF ζ η) p)
        = ((Complex.normSq (Rop R (wedgeF ζ η) p) : ℝ) : ℂ)
      rw [Complex.star_def]
      exact Complex.mul_conj _
    rw [h2, Complex.ofReal_re]
    exact Finset.sum_nonneg fun p _ => Complex.normSq_nonneg _
  have hterm2 : 0 ≤ (Phi (Q2 R) (wedgeF ζ η) (bar (wedgeF ζ η))).re := by
    rw [Phi_Q2 n R hR]
    exact trace_mul_nonneg (Tmat_posSemidef R hR hPIC h0Phi) (Rm_isHermitian R hR)
      (trace_hyp R hR hPIC h0Phi)
  have hmain : 0 ≤ (Phi (Q R) (wedgeF ζ η) (bar (wedgeF ζ η))).re := by
    rw [hsplit]; linarith
  -- convert back to `EFun`
  rw [Phi_wedge n (Q R) (Q_isAlgCurv n hR) ζ η, hcreζ, hcimζ, hcreη, hcimη] at hmain
  have h4 : (4 * (Q2P.EFun (Q R) x y z w : ℂ)).re = 4 * Q2P.EFun (Q R) x y z w := by
    simp
  rw [h4] at hmain
  linarith
