import Mathlib
import Submission.Work.Mostow.ematSpec
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.StabLift
import Submission.Work.Mostow.margulisPair
import Submission.Work.Mostow.margulisCuspDefs
import Submission.Work.Mostow.Margulis.ComplexifyOrth

/-!
# The shape of the sheet-preserving lift of a chart-linear isometry

An isometry `g` of `ℍⁿ` that fixes the base point is linear in the chart (`g • u = R u`).  This
file computes the sheet-preserving lift `LambdaMat g` of such a `g`:

* `LambdaMat g` fixes the time vector `etime n`;
* it maps `wvec u` to `wvec (R u)`;
* hence it acts on `ℝ^{Fin n ⊕ Fin 1} = E n ⊕ ℝ` as `fromBlocks (Rmat R) 0 0 1`, where
  `Rmat R i j = (R e_j) i` is the matrix of `R` in the standard basis.
-/

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Matrix

namespace Work.Mostow

noncomputable section

variable {n : ℕ}

/-- The matrix of `R` in the standard basis `e_j = EuclideanSpace.single j 1` of `E n`. -/
noncomputable def Rmat (n : ℕ) (R : E n ≃ₗᵢ[ℝ] E n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => (R (EuclideanSpace.single j 1)) i

/-! ## Elementary decompositions -/

lemma hlift_eq_wvec_add (u : E n) :
    hlift u = wvec u + tpart u • Hyper.etime n := by
  funext z
  rcases z with i | j
  · simp [hlift, wvec, Hyper.etime]
  · fin_cases j
    simp [hlift, wvec, Hyper.etime]

/-- `tpart` is invariant under a chart-linear isometry fixing the base point. -/
lemma tpart_linIso (R : E n ≃ₗᵢ[ℝ] E n) (u : E n) : tpart (R u) = tpart u := by
  rw [tpart, tpart, R.norm_map]

lemma spat_wvec (w : E n) : Hyper.spat (wvec w) = w := by
  simp [Hyper.spat, wvec]

/-- Decomposition of an arbitrary vector of `ℝ^{Fin n ⊕ Fin 1}` as `wvec (spat x) + t • etime`. -/
lemma eq_wvec_spat_add (x : Fin n ⊕ Fin 1 → ℝ) :
    x = wvec (Hyper.spat x) + x (Sum.inr 0) • Hyper.etime n := by
  funext z
  rcases z with i | j
  · simp [wvec, Hyper.spat, Hyper.etime]
  · fin_cases j
    simp [wvec, Hyper.spat, Hyper.etime]

lemma spat_single (j : Fin n) :
    Hyper.spat (Pi.single (Sum.inl j) (1:ℝ) : Fin n ⊕ Fin 1 → ℝ)
      = EuclideanSpace.single j (1:ℝ) := by
  apply WithLp.ofLp_injective
  funext i
  simp only [Hyper.spat, WithLp.ofLp_toLp, EuclideanSpace.single, PiLp.single]
  simp [Pi.single_apply]

lemma spat_etime : Hyper.spat (Hyper.etime n) = (0 : E n) := by
  rw [← Hyper.hlift_zero, Hyper.spat_hlift]

lemma etime_apply_inl (i : Fin n) : Hyper.etime n (Sum.inl i) = 0 := by
  rw [Hyper.etime, Pi.single_eq_of_ne Sum.inl_ne_inr]

lemma etime_apply_inr : Hyper.etime n (Sum.inr 0) = 1 := by
  simp [Hyper.etime]

lemma inner_single (i : Fin n) (v : E n) :
    inner ℝ (EuclideanSpace.single i (1:ℝ)) v = v i := by
  rw [Hyper.inner_eq_sum]
  simp

lemma sum_single (x : E n) : x = ∑ j : Fin n, x j • EuclideanSpace.single j (1:ℝ) := by
  apply WithLp.ofLp_injective
  rw [WithLp.ofLp_sum]
  funext i
  rw [Finset.sum_apply]
  simp only [WithLp.ofLp_smul, EuclideanSpace.single, PiLp.single, Pi.smul_apply,
    smul_eq_mul, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [ite_eq_right (fun h : i = j => hj h.symm), mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- `Rmat R` acts on a vector as `R` does. -/
lemma Rmat_apply (R : E n ≃ₗᵢ[ℝ] E n) (x : E n) (i : Fin n) :
    ∑ j : Fin n, Rmat n R i j * x j = (R x) i := by
  have hRx : R x = ∑ j : Fin n, x j • R (EuclideanSpace.single j (1:ℝ)) := by
    conv_lhs => rw [sum_single x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => map_smul R (x j) _
  rw [hRx, WithLp.ofLp_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, Rmat, Matrix.of_apply]
  ring

/-! ## The block action of `LambdaMat` -/

/-- `LambdaMat g` acts as the identity on the time coordinate and as `R` on the spatial part. -/
theorem LamMulVec (hA : Submission.Mostow.POActionProp n) (g : PO n 1)
    (R : E n ≃ₗᵢ[ℝ] E n) (hR : ∀ u : E n, g • u = R u) (x : Fin n ⊕ Fin 1 → ℝ) :
    LambdaMat g *ᵥ x = wvec (R (Hyper.spat x)) + x (Sum.inr 0) • Hyper.etime n := by
  have hfix : LambdaMat g *ᵥ Hyper.etime n = Hyper.etime n := by
    have h := hlift_LambdaMat hA g (0 : E n)
    rw [hR 0, R.map_zero, Hyper.hlift_zero] at h
    exact h.symm
  have hw : ∀ u : E n, LambdaMat g *ᵥ wvec u = wvec (R u) := by
    intro u
    have hub := hlift_LambdaMat hA g u
    rw [hR u] at hub
    rw [hlift_eq_wvec_add u, Matrix.mulVec_add, Matrix.mulVec_smul, hfix] at hub
    rw [hlift_eq_wvec_add (R u), tpart_linIso] at hub
    exact (add_right_cancel hub).symm
  conv_lhs => rw [eq_wvec_spat_add x]
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, hw, hfix]

lemma Lam_inl_inl (hA : Submission.Mostow.POActionProp n) (g : PO n 1)
    (R : E n ≃ₗᵢ[ℝ] E n) (hR : ∀ u : E n, g • u = R u) (i j : Fin n) :
    (LambdaMat g) (Sum.inl i) (Sum.inl j) = Rmat n R i j := by
  have key := congrFun (LamMulVec hA g R hR (Pi.single (Sum.inl j) (1:ℝ))) (Sum.inl i)
  conv_lhs at key => rw [Matrix.mulVec_single_one, Matrix.col_apply]
  simp only [Pi.add_apply, Pi.smul_apply, wvec, Sum.elim_inl, Sum.elim_inr,
    etime_apply_inl, Pi.single_apply, Sum.inr_ne_inl, ite_false, zero_smul,
    Pi.zero_apply, add_zero] at key
  rw [spat_single] at key
  exact key

lemma Lam_inl_inr (hA : Submission.Mostow.POActionProp n) (g : PO n 1)
    (R : E n ≃ₗᵢ[ℝ] E n) (hR : ∀ u : E n, g • u = R u) (i : Fin n) :
    (LambdaMat g) (Sum.inl i) (Sum.inr 0) = 0 := by
  have key := congrFun (LamMulVec hA g R hR (Hyper.etime n)) (Sum.inl i)
  conv_lhs at key => rw [show Hyper.etime n = Pi.single (Sum.inr 0) (1:ℝ) from rfl,
    Matrix.mulVec_single_one, Matrix.col_apply]
  simp only [Pi.add_apply, Pi.smul_apply, wvec, Sum.elim_inl, Sum.elim_inr,
    etime_apply_inl, etime_apply_inr] at key
  rw [spat_etime, R.map_zero] at key
  simpa using key

lemma Lam_inr_inl (hA : Submission.Mostow.POActionProp n) (g : PO n 1)
    (R : E n ≃ₗᵢ[ℝ] E n) (hR : ∀ u : E n, g • u = R u) (j : Fin n) :
    (LambdaMat g) (Sum.inr 0) (Sum.inl j) = 0 := by
  have key := congrFun (LamMulVec hA g R hR (Pi.single (Sum.inl j) (1:ℝ))) (Sum.inr 0)
  conv_lhs at key => rw [Matrix.mulVec_single_one, Matrix.col_apply]
  simp only [Pi.add_apply, Pi.smul_apply, wvec, Sum.elim_inl, Sum.elim_inr,
    etime_apply_inr, Pi.single_apply, Sum.inr_ne_inl, ite_false, zero_smul,
    Pi.zero_apply, add_zero] at key
  exact key

lemma Lam_inr_inr (hA : Submission.Mostow.POActionProp n) (g : PO n 1)
    (R : E n ≃ₗᵢ[ℝ] E n) (hR : ∀ u : E n, g • u = R u) :
    (LambdaMat g) (Sum.inr 0) (Sum.inr 0) = 1 := by
  have key := congrFun (LamMulVec hA g R hR (Hyper.etime n)) (Sum.inr 0)
  conv_lhs at key => rw [show Hyper.etime n = Pi.single (Sum.inr 0) (1:ℝ) from rfl,
    Matrix.mulVec_single_one, Matrix.col_apply]
  simp only [Pi.add_apply, Pi.smul_apply, wvec, Sum.elim_inl, Sum.elim_inr,
    etime_apply_inr] at key
  simpa using key

/-- The lift acts as `diag (mat R, 1)` in the splitting `ℝ^{Fin n ⊕ Fin 1} = E n ⊕ ℝ`. -/
theorem Lam_eq_fromBlocks (hA : Submission.Mostow.POActionProp n) (g : PO n 1)
    (R : E n ≃ₗᵢ[ℝ] E n) (hR : ∀ u : E n, g • u = R u) :
    LambdaMat g = Matrix.fromBlocks (Rmat n R) 0 0 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · rw [Matrix.fromBlocks_apply₁₁]; exact Lam_inl_inl hA g R hR i j
  · fin_cases j
    rw [Matrix.fromBlocks_apply₁₂]; exact Lam_inl_inr hA g R hR i
  · fin_cases i
    rw [Matrix.fromBlocks_apply₂₁]; exact Lam_inr_inl hA g R hR j
  · rw [show i = (0 : Fin 1) from Subsingleton.elim i 0,
      show j = (0 : Fin 1) from Subsingleton.elim j 0,
      Matrix.fromBlocks_apply₂₂, Lam_inr_inr hA g R hR]
    simp [Matrix.one_apply]

/-- The complexified lift is `diag (mat ℂ R, 1)`. -/
theorem Lam_map_eq_fromBlocks (hA : Submission.Mostow.POActionProp n) (g : PO n 1)
    (R : E n ≃ₗᵢ[ℝ] E n) (hR : ∀ u : E n, g • u = R u) :
    (LambdaMat g).map (algebraMap ℝ ℂ)
      = Matrix.fromBlocks ((Rmat n R).map (algebraMap ℝ ℂ)) 0 0 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · rw [Matrix.map_apply, Matrix.fromBlocks_apply₁₁, Matrix.map_apply,
      Lam_inl_inl hA g R hR i j]
  · rw [show j = (0 : Fin 1) from Subsingleton.elim j 0,
      Matrix.map_apply, Matrix.fromBlocks_apply₁₂, Lam_inl_inr hA g R hR i]
    simp
  · rw [show i = (0 : Fin 1) from Subsingleton.elim i 0,
      Matrix.map_apply, Matrix.fromBlocks_apply₂₁, Lam_inr_inl hA g R hR j]
    simp
  · rw [show i = (0 : Fin 1) from Subsingleton.elim i 0,
      show j = (0 : Fin 1) from Subsingleton.elim j 0,
      Matrix.map_apply, Matrix.fromBlocks_apply₂₂, Lam_inr_inr hA g R hR]
    simp [Matrix.one_apply]

end

end Work.Mostow
