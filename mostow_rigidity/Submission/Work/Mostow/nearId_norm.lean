import Mathlib
import Submission.Work.Mostow.zassDefs
import Submission.Work.Mostow.StabLift
import Submission.Work.Mostow.hdistBasic
import Submission.Work.Mostow.abs_tpart_sub_le
import Submission.Work.Mostow.cosh_sub_one_quad
import Submission.Work.Mostow.entry_le_of_hlift_bound

namespace Work.Mostow

-- File: Submission/Work/Mostow/nearId_norm.lean (module Submission.Work.Mostow.nearId_norm).
-- Useful imports: import Submission.Work.Mostow.StabLift (Work.Mostow.LambdaMat, LambdaMat_mul)
--                  import Submission.Mostow.HLDefs       (Submission.Mostow.NearIdAt)
-- `open scoped Matrix.Norms.Operator` selects the (submultiplicative) operator norm on matrices.
-- Mathematical content: `NearIdAt g 0 η` (g moves the hyperbolic unit ball around 0 by < η) forces
-- the lift `LambdaMat g` to be close to the identity, with a linear constant.
-- Suggested route: for ‖u‖ ≤ 1/4 (so hdist 0 u ≤ ‖u‖ ≤ 1) put x = hlift u, y = LambdaMat g *ᵥ x
-- = hlift (g • u).  Then mform y y = mform x x = -1 and mform x y = -cosh (hdist u (g•u)), so
-- mform (y-x) (y-x) = 2 (cosh (hdist u (g•u)) - 1); and ‖y - x‖² = mform (y-x) (y-x) + 2 * (time
-- component of y - x)², where the time component is tpart (g•u) - tpart u, bounded by
-- η * sinh 1 using hdist 0 (g•u) ≤ hdist 0 u + η and |cosh a - cosh b| ≤ |a-b| * sinh (max a b).
-- Hence ‖(LambdaMat g - 1) *ᵥ hlift u‖ ≤ C' η for ‖u‖ ≤ 1/4.  Finally re-write the standard
-- basis vectors: hlift (0) = (0,1) and hlift (t e_i) - hlift (-t e_i) = (2t e_i, 0), so each
-- column of LambdaMat g - 1 has entries of size ≤ C'η, giving the operator-norm bound.
open scoped Matrix.Norms.Operator
open scoped _root_.Matrix
open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

variable {n : ℕ}

/-- The hyperbolic distance from the base point `0` is `arsinh ‖u‖`. -/
lemma hdist_zero_eq_arsinh (u : E n) : hdist (0 : E n) u = Real.arsinh ‖u‖ := by
  rw [Submission.Mostow.hdist]
  have h0 : tpart (0 : E n) * tpart u - inner ℝ (0 : E n) u = tpart u := by
    simp [Submission.Mostow.tpart]
  rw [h0]
  rw [show tpart u = Real.cosh (Real.arsinh ‖u‖) from (Real.cosh_arsinh ‖u‖).symm]
  exact Real.arcosh_cosh (Real.arsinh_nonneg_iff.mpr (norm_nonneg u))

/-- In particular `hdist 0 u ≤ ‖u‖`. -/
lemma hdist_zero_le_norm (u : E n) : hdist (0 : E n) u ≤ ‖u‖ := by
  rw [hdist_zero_eq_arsinh]
  rw [← Real.sinh_le_sinh, Real.sinh_arsinh]
  exact Real.self_le_sinh_iff.mpr (norm_nonneg u)

/-- **Pointwise estimate.** If `g` moves the unit ball around `0` by less than `η`, then the lift
`LambdaMat g` moves each `hlift u`, `‖u‖ ≤ 1/4`, by at most `C η` in the Euclidean norm of
`Fin n ⊕ Fin 1 → ℝ`, with `C = √(cosh 1 ^ 2 + 2 * sinh 1 ^ 2)`. -/
lemma nearId_pointwise (hA : POActionProp n) (hI : HypIsometryProp n)
    (g : PO n 1) {η : ℝ} (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hnear : NearIdAt g (0 : E n) η)
    {u : E n} (hu : ‖u‖ ≤ 1 / 4) :
    Real.sqrt (∑ i, ((LambdaMat g - 1) *ᵥ hlift u) i ^ 2)
      ≤ Real.sqrt (Real.cosh 1 ^ 2 + 2 * Real.sinh 1 ^ 2) * η := by
  have hη1 : η ≤ 1 := by linarith
  have hdist0u : hdist (0 : E n) u ≤ 1 := by
    have := hdist_zero_le_norm u; linarith
  have hdu : hdist u (g • u) < η := hnear u hdist0u
  have hdist0gu : hdist (0 : E n) (g • u) ≤ 1 := by
    have h1 := hI.2.2.2.1 (0 : E n) u (g • u)
    have h2 := hdist_zero_le_norm u
    linarith
  have hcc : Hyper.cc u (g • u) = Real.cosh (hdist u (g • u)) := by
    rw [← Real.cosh_arcosh (one_le_cc u (g • u)), ← Hyper.hdist_eq_cc]
  have hcc_le : 2 * (Hyper.cc u (g • u) - 1) ≤ Real.cosh 1 ^ 2 * η ^ 2 := by
    have hmono : Real.cosh (hdist u (g • u)) ≤ Real.cosh η := by
      rw [Real.cosh_le_cosh, abs_of_nonneg (hI.1 u (g • u)), abs_of_nonneg (le_of_lt hη)]
      exact le_of_lt hdu
    have hq := cosh_sub_one_quad η (le_of_lt hη) hη1
    rw [hcc]
    linarith
  have htime : |(hlift (g • u) - hlift u) (Sum.inr 0)| ≤ Real.sinh 1 * η := by
    rw [Pi.sub_apply, hlift_inr, hlift_inr]
    have h1 := abs_tpart_sub_le n hI (u := g • u) (v := u) hdist0gu hdist0u
    rw [hI.2.1 (g • u) u] at h1
    have h2 : Real.sinh 1 * hdist u (g • u) ≤ Real.sinh 1 * η :=
      mul_le_mul_of_nonneg_left (le_of_lt hdu)
        (le_of_lt (Real.sinh_pos_iff.mpr one_pos))
    linarith
  have htime_sq : ((hlift (g • u) - hlift u) (Sum.inr 0)) ^ 2 ≤ (Real.sinh 1 * η) ^ 2 := by
    rw [sq_le_sq,
      abs_of_nonneg (mul_nonneg (le_of_lt (Real.sinh_pos_iff.mpr one_pos)) (le_of_lt hη))]
    exact htime
  have hsqsum : (∑ i, (hlift (g • u) - hlift u) i ^ 2)
      = mform (hlift (g • u) - hlift u) (hlift (g • u) - hlift u)
        + 2 * ((hlift (g • u) - hlift u) (Sum.inr 0)) ^ 2 := by
    rw [mform_self_apply, Fintype.sum_sum_type, Fin.sum_univ_one]
    ring
  have hmform : mform (hlift (g • u) - hlift u) (hlift (g • u) - hlift u)
      = 2 * (Hyper.cc u (g • u) - 1) := by
    rw [mform_sub_left, mform_sub_right, mform_sub_right, mform_hlift_self, mform_hlift_hlift,
      mform_hlift_hlift, mform_hlift_self, Hyper.cc, real_inner_comm (g • u) u]
    ring
  have hcol : (LambdaMat g - 1) *ᵥ hlift u = hlift (g • u) - hlift u := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hlift_LambdaMat hA]
  calc Real.sqrt (∑ i, ((LambdaMat g - 1) *ᵥ hlift u) i ^ 2)
      = Real.sqrt (∑ i, (hlift (g • u) - hlift u) i ^ 2) := by rw [hcol]
    _ = Real.sqrt (2 * (Hyper.cc u (g • u) - 1)
          + 2 * ((hlift (g • u) - hlift u) (Sum.inr 0)) ^ 2) := by rw [hsqsum, hmform]
    _ ≤ Real.sqrt (Real.cosh 1 ^ 2 * η ^ 2 + 2 * (Real.sinh 1 * η) ^ 2) := by
        apply Real.sqrt_le_sqrt
        linarith
    _ = Real.sqrt (Real.cosh 1 ^ 2 + 2 * Real.sinh 1 ^ 2) * η := by
        rw [show Real.cosh 1 ^ 2 * η ^ 2 + 2 * (Real.sinh 1 * η) ^ 2
              = (Real.cosh 1 ^ 2 + 2 * Real.sinh 1 ^ 2) * η ^ 2 by ring]
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (le_of_lt hη)]

theorem nearId_norm (n : ℕ) (hA : POActionProp n) (hI : HypIsometryProp n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : PO n 1) (η : ℝ), 0 < η → η ≤ 1 / 8 →
      NearIdAt g (0 : E n) η → ‖Work.Mostow.LambdaMat g - 1‖ ≤ C * η := by
  have hK1pos : (0 : ℝ) < Real.sqrt (Real.cosh 1 ^ 2 + 2 * Real.sinh 1 ^ 2) :=
    Real.sqrt_pos.mpr (by positivity)
  refine ⟨4 * ((n : ℝ) + 1) * Real.sqrt (Real.cosh 1 ^ 2 + 2 * Real.sinh 1 ^ 2), ?_, ?_⟩
  · exact mul_pos (mul_pos (by norm_num) (by positivity)) hK1pos
  · intro g η hη hη8 hnear
    set K1 := Real.sqrt (Real.cosh 1 ^ 2 + 2 * Real.sinh 1 ^ 2) with hK1
    set A := LambdaMat g - 1 with hAdef
    have hpt : ∀ u : E n, ‖u‖ ≤ 1 / 4 → Real.sqrt (∑ i, (A *ᵥ hlift u) i ^ 2) ≤ K1 * η := by
      intro u hu
      have h := nearId_pointwise hA hI g hη hη8 hnear hu
      rw [hAdef, hK1]
      exact h
    have hentry : ∀ i j : Fin n ⊕ Fin 1, |A i j| ≤ 4 * (K1 * η) :=
      entry_le_of_hlift_bound n A (K1 * η) (by positivity) hpt
    have hrowle : ∀ i : Fin n ⊕ Fin 1, (∑ j, |A i j|) ≤ 4 * ((n : ℝ) + 1) * (K1 * η) := by
      intro i
      have h1 : (∑ j, |A i j|) ≤ ∑ _j : Fin n ⊕ Fin 1, 4 * (K1 * η) :=
        Finset.sum_le_sum (fun j _ => hentry i j)
      have h2 : (∑ _j : Fin n ⊕ Fin 1, 4 * (K1 * η)) = ((n : ℝ) + 1) * (4 * (K1 * η)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin,
          Fintype.card_fin]
        simp only [nsmul_eq_mul]
        push_cast
        ring
      have h3 : ((n : ℝ) + 1) * (4 * (K1 * η)) = 4 * ((n : ℝ) + 1) * (K1 * η) := by ring
      linarith
    have hop : ∀ x : Fin n ⊕ Fin 1 → ℝ,
        ‖(Matrix.mulVecLin A) x‖ ≤ (4 * ((n : ℝ) + 1) * (K1 * η)) * ‖x‖ := by
      intro x
      rw [pi_norm_le_iff_of_nonneg (by positivity)]
      intro i
      have h1 : ((Matrix.mulVecLin A) x) i = ∑ j, A i j * x j := by
        simp [Matrix.mulVecLin, Matrix.mulVec, dotProduct]
      calc ‖((Matrix.mulVecLin A) x) i‖ = |∑ j, A i j * x j| := by rw [h1, Real.norm_eq_abs]
        _ ≤ ∑ j, |A i j * x j| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j, |A i j| * |x j| := by simp only [abs_mul]
        _ ≤ ∑ j, |A i j| * ‖x‖ :=
            Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left
              (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm x j) (abs_nonneg _))
        _ = (∑ j, |A i j|) * ‖x‖ := by rw [Finset.sum_mul]
        _ ≤ (4 * ((n : ℝ) + 1) * (K1 * η)) * ‖x‖ :=
            mul_le_mul_of_nonneg_right (hrowle i) (norm_nonneg x)
    have hfin : ‖A‖ ≤ 4 * ((n : ℝ) + 1) * (K1 * η) := by
      rw [Matrix.linfty_opNorm_eq_opNorm]
      refine ContinuousLinearMap.opNorm_le_bound _ ?_ ?_
      · positivity
      · exact hop
    rw [hAdef] at hfin
    rw [hK1] at hfin
    calc ‖Work.Mostow.LambdaMat g - 1‖ ≤ 4 * ((n : ℝ) + 1)
            * (Real.sqrt (Real.cosh 1 ^ 2 + 2 * Real.sinh 1 ^ 2) * η) := hfin
      _ = (4 * ((n : ℝ) + 1) * Real.sqrt (Real.cosh 1 ^ 2 + 2 * Real.sinh 1 ^ 2)) * η := by
          ring

end Work.Mostow
