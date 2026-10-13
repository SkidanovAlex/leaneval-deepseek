/-
  annals_wilkies_conjecture, AREA E3, the frame step of `E3_identity` (GV Cor. 4.7).

  This file builds the *tangential frame* of the effectively smooth set `{h = 0}` at a point `z`,
  in the complexified setting in which the multiplicity bound `Work.WilE3.MultiplicityBound` lives.

  The frozen operator `detOp c h ι l` is the determinant with rows `h_a, Q` and columns
  `∂_{ι b}, ∂_l`.  The main content of this file is the *operator identity*

      `eaEvalC c (detOp c h ι l Q) z = Δ(z) · (V_l Q)(z)`,

  where `Δ = jacDet c h ι` and `V_l` is the directional derivative along the *tangential* frame
  vector `VcoefC c h ι l z : Fin k → ℂ`, i.e. the vector with `ι^c`-coordinates `e_l` which is
  tangent to `{h = 0}` at `z`.  Together with `VcoefC_tangent` (`V_l` kills the `h_a`) this is the
  whole algebraic input of the frame step: `detOp c h ι l` acts, modulo the never vanishing factor
  `Δ`, as the directional derivative along a vector field tangent to `{h = 0}`, and the `k - j`
  vectors `V_l` (`l ∉ range ι`) frame the tangent space.

  The proof of the operator identity avoids the explicit cofactor computation: the determinant of
  the `(j+1) × (j+1)` matrix is unchanged when the last column `C_l` is replaced by
  `C_l - Σ_b β_b C_b` (adding multiples of the other columns, `Matrix.det_updateCol_sum`), and each
  of the intermediate determinants vanishes because its last column equals one of the `ι`-columns.
  In the resulting matrix the first `j` entries of the last column are `V_l h_a = 0`, so expanding
  along that column gives `Δ · (V_l Q)` directly.
-/
import Mathlib
import Submission.Work.WilE3.Defs
import Submission.Work.WilE3.API.eaEvalC_ring
import Submission.Work.WilE3.API.eaEval_jacDet
import Submission.Work.WilE3.API.eaEvalC_fderiv_analytic
import Submission.Work.WilE3.API.detOp_linear_derivation

namespace Work.WilE3.Frame

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical Topology Matrix
open WilkiesDesign.E
open Work.WilE3 (jacDet)

variable {k r j : ℕ}

/-! ## §1. The `ι`-Jacobian at a complex point and the frame vector -/

/-- `M z = (∂_{ι b} h_a)(z)`, the `ι`-Jacobian matrix of `h` at the complex point `z`. -/
def jacMatC (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k) (z : Fin k → ℂ) :
    Matrix (Fin j) (Fin j) ℂ :=
  Matrix.of fun a b => eaEvalC c (eaD c (ι b) (h a)) z

/-- `Δ(z)`: the `ι`-Jacobian determinant `jacDet c h ι` evaluated at `z`. -/
def jacValC (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k)
    (z : Fin k → ℂ) : ℂ :=
  eaEvalC c (jacDet c h ι) z

/-- The `l`-column `(∂_l h_a)(z)` of the Jacobian. -/
def dlColC (c : EAChain k r) (h : Fin j → EAPoly k r) (l : Fin k) (z : Fin k → ℂ) : Fin j → ℂ :=
  fun a => eaEvalC c (eaD c l (h a)) z

theorem jacValC_eq_det (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k)
    (z : Fin k → ℂ) : jacValC c h ι z = (jacMatC c h ι z).det := by
  have h1 : jacValC c h ι z = MvPolynomial.eval₂Hom (algebraMap ℝ ℂ)
      (Work.WilE3.API.eaPsi c z) (jacDet c h ι) :=
    Work.WilE3.API.eaEvalC_eq c (jacDet c h ι) z
  rw [h1, Work.WilE3.jacDet, RingHom.map_det]
  congr 1

/-- Cramer's coefficients: `β_b = (M⁻¹ ∂_l h)_b`, written through the adjugate so that no matrix
inverse is needed. -/
def betaC (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k) (l : Fin k)
    (z : Fin k → ℂ) : Fin j → ℂ :=
  fun b => (jacValC c h ι z)⁻¹ * ((jacMatC c h ι z).adjugate *ᵥ dlColC c h l z) b

/-- **The tangential frame vector**: the vector with `ι^c`-coordinates `e_l` which is tangent to
`{h = 0}` at `z`. -/
def VcoefC (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k) (l : Fin k)
    (z : Fin k → ℂ) : Fin k → ℂ :=
  fun i => (if i = l then (1 : ℂ) else 0) -
    ∑ b : Fin j, if ι b = i then betaC c h ι l z b else 0

/-- The frame vector contracted with any vector `w`. -/
theorem sum_VcoefC_mul (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k)
    (l : Fin k) (z : Fin k → ℂ) (w : Fin k → ℂ) :
    ∑ i, VcoefC c h ι l z i * w i = w l - ∑ b, betaC c h ι l z b * w (ι b) := by
  have h1 : ∀ i : Fin k,
      VcoefC c h ι l z i * w i =
        (if i = l then (1 : ℂ) else 0) * w i -
          (∑ b : Fin j, if ι b = i then betaC c h ι l z b else 0) * w i := by
    intro i
    rw [show VcoefC c h ι l z i = (if i = l then (1 : ℂ) else 0) -
        ∑ b : Fin j, if ι b = i then betaC c h ι l z b else 0 from rfl]
    ring
  have h2 : ∀ i : Fin k, (∑ b : Fin j, if ι b = i then betaC c h ι l z b else 0) * w i
      = ∑ b : Fin j, (if ι b = i then betaC c h ι l z b else 0) * w i :=
    fun i => Finset.sum_mul _ _ _
  rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_sub_distrib,
    Finset.sum_congr rfl (fun i _ => h2 i), Finset.sum_comm]
  congr 1
  · rw [Finset.sum_eq_single l]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ l) h
  · refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_eq_single (ι b)]
    · simp
    · intro i _ hi; rw [if_neg (fun h => hi h.symm), zero_mul]
    · intro h; exact absurd (Finset.mem_univ (ι b)) h

/-- The `b`-sum of the Cramer coefficients against the Jacobian: `Σ_b β_b M_{ab} = ∂_l h_a`. -/
theorem sum_betaC_mul_jacMat (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k)
    (l : Fin k) (z : Fin k → ℂ) (hz : jacValC c h ι z ≠ 0) (a : Fin j) :
    ∑ b : Fin j, betaC c h ι l z b * eaEvalC c (eaD c (ι b) (h a)) z = dlColC c h l z a := by
  have h1 : ∀ b : Fin j,
      betaC c h ι l z b * eaEvalC c (eaD c (ι b) (h a)) z
        = (jacValC c h ι z)⁻¹ * (jacMatC c h ι z a b *
            ((jacMatC c h ι z).adjugate *ᵥ dlColC c h l z) b) := by
    intro b
    rw [betaC]
    simp only [jacMatC, Matrix.of_apply]
    ring
  rw [Finset.sum_congr rfl (fun b _ => h1 b), ← Finset.mul_sum]
  congr 1
  have h2 : ∑ b : Fin j, jacMatC c h ι z a b *
        ((jacMatC c h ι z).adjugate *ᵥ dlColC c h l z) b
      = ((jacMatC c h ι z) *ᵥ ((jacMatC c h ι z).adjugate *ᵥ dlColC c h l z)) a := by
    simp only [Matrix.mulVec, dotProduct]
  rw [h2, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
    Matrix.one_mulVec]
  rw [Pi.smul_apply, smul_eq_mul, ← jacValC_eq_det, ← mul_assoc, inv_mul_cancel₀ hz, one_mul]

/-- **Tangency**: the frame vector kills every `h_a` at every point where `Δ ≠ 0`. -/
theorem VcoefC_tangent (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k)
    (l : Fin k) (z : Fin k → ℂ) (hz : jacValC c h ι z ≠ 0) (a : Fin j) :
    ∑ i, VcoefC c h ι l z i * eaEvalC c (eaD c i (h a)) z = 0 := by
  rw [sum_VcoefC_mul, sum_betaC_mul_jacMat c h ι l z hz a]
  exact sub_self _

/-! ## §2. The operator identity `detOp c h ι l = Δ · V_l` -/

/-- **The frame identity.**  On the evaluated functions, `detOp c h ι l` is `Δ` times the
directional derivative along the tangential frame vector `V_l`. -/
theorem eaEvalC_detOp_eq (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k)
    (l : Fin k) (z : Fin k → ℂ) (hz : jacValC c h ι z ≠ 0) (Q : EAPoly k r) :
    eaEvalC c (detOp c h ι l Q) z =
      jacValC c h ι z * ∑ i, VcoefC c h ι l z i * eaEvalC c (eaD c i Q) z := by
  classical
  -- The evaluated `(j+1) × (j+1)` matrix whose determinant is `detOp c h ι l Q`.
  set N : Matrix (Fin (j+1)) (Fin (j+1)) ℂ := Matrix.of fun (a b : Fin (j+1)) =>
    eaEvalC c (eaD c (Fin.lastCases l ι b) (Fin.lastCases Q h a)) z with hN
  have hdet : eaEvalC c (detOp c h ι l Q) z = N.det := by
    have h1 : detOp c h ι l Q = (Matrix.of fun (a b : Fin (j+1)) =>
        eaD c (Fin.lastCases l ι b) (Fin.lastCases Q h a)).det := rfl
    rw [h1, Work.WilE3.API.eaEvalC_eq, RingHom.map_det]
    congr 1
  have hN_last : ∀ a : Fin (j+1), N a (Fin.last j) =
      eaEvalC c (eaD c l (Fin.lastCases Q h a)) z := by
    intro a; rw [hN]; simp
  have hN_cast : ∀ (b : Fin j) (a : Fin (j+1)), N a (Fin.castSucc b) =
      eaEvalC c (eaD c (ι b) (Fin.lastCases Q h a)) z := by
    intro b a; rw [hN]; simp
  -- The "V-column".
  set Vc : Fin (j+1) → ℂ := fun a =>
    ∑ i, VcoefC c h ι l z i * eaEvalC c (eaD c i (Fin.lastCases Q h a)) z with hVc
  -- `Vc` is the linear combination `∂_l - Σ_b β_b ∂_{ι b}` of the columns of `N`.
  have hVc_eq : ∀ a, Vc a = ∑ i : Fin (j+1),
      (Fin.lastCases (motive := fun _ => ℂ) (1 : ℂ)
        (fun b : Fin j => -(betaC c h ι l z b))) i • N a i := by
    intro a
    have h2 : (∑ i : Fin k, VcoefC c h ι l z i * eaEvalC c (eaD c i (Fin.lastCases Q h a)) z)
        = eaEvalC c (eaD c l (Fin.lastCases Q h a)) z -
          ∑ b : Fin j, betaC c h ι l z b *
            eaEvalC c (eaD c (ι b) (Fin.lastCases Q h a)) z :=
      sum_VcoefC_mul c h ι l z _
    have h5 : (∑ b : Fin j, (-betaC c h ι l z b) • N a (Fin.castSucc b))
        = -(∑ b : Fin j, betaC c h ι l z b *
            eaEvalC c (eaD c (ι b) (Fin.lastCases Q h a)) z) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun b _ => by
        rw [hN_cast b a]; simp only [smul_eq_mul]; ring
    rw [hVc, Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_last, Fin.lastCases_castSucc, one_smul]
    rw [h2, h5, hN_last a]
    ring
  -- The determinant is unchanged by this column operation.
  have hstep : N.det = (N.updateCol (Fin.last j) Vc).det := by
    have hW : Vc = fun a => ∑ i : Fin (j+1),
        (Fin.lastCases (motive := fun _ => ℂ) (1 : ℂ)
          (fun b : Fin j => -(betaC c h ι l z b))) i • N a i := funext hVc_eq
    have h1 : N.updateCol (Fin.last j) Vc = N.updateCol (Fin.last j)
        (fun a => ∑ i : Fin (j+1),
          (Fin.lastCases (motive := fun _ => ℂ) (1 : ℂ)
            (fun b : Fin j => -(betaC c h ι l z b))) i • N a i) :=
      congrArg (fun v : Fin (j+1) → ℂ => N.updateCol (Fin.last j) v) hW
    rw [h1, Matrix.det_updateCol_sum]
    simp
  -- In the updated matrix only the last entry of the last column is nonzero.
  have hzero : ∀ b : Fin j, Vc (Fin.castSucc b) = 0 := by
    intro b
    have h1 : Vc (Fin.castSucc b) = ∑ i, VcoefC c h ι l z i * eaEvalC c (eaD c i (h b)) z := by
      rw [hVc]
      exact Finset.sum_congr rfl fun i _ => by
        rw [Fin.lastCases_castSucc (motive := fun _ => EAPoly k r) (last := Q) (cast := h) b]
    rw [h1]
    exact VcoefC_tangent c h ι l z hz b
  -- Expand along the last column.
  have hfinal : (N.updateCol (Fin.last j) Vc).det = jacValC c h ι z * Vc (Fin.last j) := by
    set M : Matrix (Fin (j+1)) (Fin (j+1)) ℂ := N.updateCol (Fin.last j) Vc with hM
    have hMcol : ∀ i : Fin (j+1), M i (Fin.last j) = Vc i := by
      intro i; rw [hM]; simp
    have hMtop : ∀ (a b : Fin j), M (Fin.castSucc a) (Fin.castSucc b) =
        jacMatC c h ι z a b := by
      intro a b
      have hne : Fin.castSucc b ≠ Fin.last j := Fin.castSucc_ne_last b
      have h1 : M (Fin.castSucc a) (Fin.castSucc b) = N (Fin.castSucc a) (Fin.castSucc b) := by
        rw [hM, Matrix.updateCol_apply, if_neg hne]
      rw [h1, hN_cast b (Fin.castSucc a), Fin.lastCases_castSucc]
      rfl
    have htrans : M.det = Mᵀ.det := (Matrix.det_transpose M).symm
    rw [htrans, Matrix.det_succ_row Mᵀ (Fin.last j), Fin.sum_univ_castSucc]
    have hzero2 : ∀ b : Fin j, (-1 : ℂ) ^ ((Fin.last j : ℕ) + ((Fin.castSucc b : Fin (j+1)) : ℕ)) *
        Mᵀ (Fin.last j) (Fin.castSucc b) *
        ((Mᵀ).submatrix (Fin.last j).succAbove (Fin.castSucc b).succAbove).det = 0 := by
      intro b
      rw [Matrix.transpose_apply, hMcol, hzero b]
      ring
    rw [Finset.sum_congr rfl (fun b _ => hzero2 b), Finset.sum_const_zero, zero_add]
    have hsign : (-1 : ℂ) ^ ((Fin.last j : ℕ) + ((Fin.last j : Fin (j+1)) : ℕ)) = 1 :=
      Even.neg_one_pow (by rw [Fin.val_last]; exact ⟨j, by ring⟩)
    rw [hsign, one_mul, Matrix.transpose_apply, hMcol]
    have hminor : (Mᵀ).submatrix (Fin.last j).succAbove (Fin.last j).succAbove =
        (jacMatC c h ι z)ᵀ := by
      ext a b
      rw [Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.transpose_apply,
        Fin.succAbove_last, hMtop b a]
    rw [hminor, Matrix.det_transpose, jacValC_eq_det]
    ring
  rw [hdet, hstep, hfinal]
  congr 1
  rw [hVc]
  simp only [Fin.lastCases_last]

end

end Work.WilE3.Frame
