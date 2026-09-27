import Mathlib
import Submission.Work.Mostow.fermiTwoDefs
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.ematSpec
import Submission.Work.Mostow.minkLineDecomp

/-!
# Any unit-speed geodesic line of `ℍ²` is the image of the standard one

Given a unit-speed geodesic line `line : ℝ → E 2` of the hyperbolic plane whose hyperboloid
lift is the `cosh`/`sinh` combination of `hlift (line 0)` and `hlift (line 1)` (hypothesis
`hform`), there is an isometry `g : PO 2 1` with `g • lineStd s = line s` for every `s`.

The proof builds the `O(2,1)`-matrix `M` whose first two columns are
`U = hlift (line 0)` and `W = (sinh 1)⁻¹ • (hlift (line 1) - cosh 1 • hlift (line 0))` (the
Minkowski-orthonormal frame of the geodesic) and whose third column is the Lorentzian cross
product `U × W`; then `M *ᵥ hlift (lineStd s) = hlift (line s)` by `hform`, and the class of
`M` in `PO 2 1` is the required isometry.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity
open Matrix
open scoped Matrix

noncomputable section

/-! ## The standard basis and the Lorentzian cross product of `ℝ^{Fin 2 ⊕ Fin 1}` -/

/-- The standard basis vector `eᵢ` of `ℝ^{Fin 2 ⊕ Fin 1}`. -/
def sb (i : Fin 2 ⊕ Fin 1) : Fin 2 ⊕ Fin 1 → ℝ := Pi.single i 1

/-- The Lorentzian cross product: the vector `x × y` with `⟨x × y, z⟩ = det (x, y, z)`, where
`⟨·,·⟩` is the Minkowski form `mink` and the determinant is taken in the basis
`(e_{inl 0}, e_{inl 1}, e_{inr 0})`. -/
def xp (x y : Fin 2 ⊕ Fin 1 → ℝ) : Fin 2 ⊕ Fin 1 → ℝ :=
  fun k => match k with
    | Sum.inl i =>
        if i = 0 then x (Sum.inl 1) * y (Sum.inr 0) - x (Sum.inr 0) * y (Sum.inl 1)
        else x (Sum.inr 0) * y (Sum.inl 0) - x (Sum.inl 0) * y (Sum.inr 0)
    | Sum.inr _ => x (Sum.inl 1) * y (Sum.inl 0) - x (Sum.inl 0) * y (Sum.inl 1)

lemma xp_mink_left (x y : Fin 2 ⊕ Fin 1 → ℝ) : mink (xp x y) x = 0 := by
  simp only [mink, xp, Fin.sum_univ_two, ↓reduceIte,
    show ¬ ((1 : Fin 2) = 0) from by decide]
  ring

lemma xp_mink_right (x y : Fin 2 ⊕ Fin 1 → ℝ) : mink (xp x y) y = 0 := by
  simp only [mink, xp, Fin.sum_univ_two, ↓reduceIte,
    show ¬ ((1 : Fin 2) = 0) from by decide]
  ring

lemma xp_mink_self (x y : Fin 2 ⊕ Fin 1 → ℝ) :
    mink (xp x y) (xp x y) = -(mink x x * mink y y - mink x y * mink y x) := by
  simp only [mink, xp, Fin.sum_univ_two, ↓reduceIte,
    show ¬ ((1 : Fin 2) = 0) from by decide]
  ring

/-! ## The matrix with prescribed columns -/

/-- The matrix whose columns are `U`, `W` (in positions `inl 0`), `Z` (in position `inl 1`) and
`U` (in position `inr 0`). -/
def matOfCols (U W Z : Fin 2 ⊕ Fin 1 → ℝ) : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ :=
  fun i j => if j = (Sum.inr 0 : Fin 2 ⊕ Fin 1) then U i
             else if j = (Sum.inl 0 : Fin 2 ⊕ Fin 1) then W i else Z i

lemma matOfCols_col_inr (U W Z : Fin 2 ⊕ Fin 1 → ℝ) :
    matOfCols U W Z *ᵥ sb (Sum.inr 0) = U := by
  funext i
  rw [show matOfCols U W Z *ᵥ sb (Sum.inr 0) = (matOfCols U W Z).col (Sum.inr 0) from
    Matrix.mulVec_single_one _ _, Matrix.col_apply]
  simp [matOfCols]

lemma matOfCols_col_inl0 (U W Z : Fin 2 ⊕ Fin 1 → ℝ) :
    matOfCols U W Z *ᵥ sb (Sum.inl 0) = W := by
  funext i
  rw [show matOfCols U W Z *ᵥ sb (Sum.inl 0) = (matOfCols U W Z).col (Sum.inl 0) from
    Matrix.mulVec_single_one _ _, Matrix.col_apply]
  simp [matOfCols]

lemma matOfCols_col_inl1 (U W Z : Fin 2 ⊕ Fin 1 → ℝ) :
    matOfCols U W Z *ᵥ sb (Sum.inl 1) = Z := by
  funext i
  rw [show matOfCols U W Z *ᵥ sb (Sum.inl 1) = (matOfCols U W Z).col (Sum.inl 1) from
    Matrix.mulVec_single_one _ _, Matrix.col_apply]
  simp [matOfCols]

/-! ## `J`-orthogonality from the pairing of the columns -/

lemma dotProduct_sb (i : Fin 2 ⊕ Fin 1) (v : Fin 2 ⊕ Fin 1 → ℝ) :
    dotProduct (sb i) v = v i := by
  rw [dotProduct, Finset.sum_eq_single i]
  · rw [sb, Pi.single_eq_same, one_mul]
  · intro b _ hb; rw [sb, Pi.single_eq_of_ne hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

lemma mform_sb (i j : Fin 2 ⊕ Fin 1) : mform (sb i) (sb j) = pmOneMat i j := by
  rw [show mform (sb i) (sb j) = dotProduct (sb i) (pmOneMat *ᵥ sb j) from rfl, dotProduct_sb]
  have h2 : pmOneMat *ᵥ (sb j) = pmOneMat.col j := by
    simp only [sb]; exact Matrix.mulVec_single_one pmOneMat j
  rw [h2, Matrix.col_apply]

lemma mat_eq_of_dotProduct_sb {v w : Fin 2 ⊕ Fin 1 → ℝ}
    (h : ∀ i, dotProduct (sb i) v = dotProduct (sb i) w) : v = w := by
  funext i; rw [← dotProduct_sb i v, ← dotProduct_sb i w, h i]

lemma mat_eq_of_mulVec_sb {A B : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ}
    (h : ∀ j, A *ᵥ sb j = B *ᵥ sb j) : A = B := by
  ext i j
  have h1 := congrFun (h j) i
  rw [show A *ᵥ sb j = A.col j from Matrix.mulVec_single_one A j,
      show B *ᵥ sb j = B.col j from Matrix.mulVec_single_one B j] at h1
  rwa [Matrix.col_apply, Matrix.col_apply] at h1

/-- A matrix sending a Minkowski-orthonormal basis to a Minkowski-orthonormal basis is
`J`-orthogonal. -/
lemma jorth_of_mform_cols {M : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ}
    (h : ∀ i j, mform (M *ᵥ sb i) (M *ᵥ sb j) = mform (sb i) (sb j)) :
    Mᵀ * pmOneMat * M = pmOneMat := by
  apply mat_eq_of_mulVec_sb
  intro j
  apply mat_eq_of_dotProduct_sb
  intro i
  calc dotProduct (sb i) ((Mᵀ * pmOneMat * M) *ᵥ sb j)
      = dotProduct (sb i) (Mᵀ *ᵥ (pmOneMat *ᵥ (M *ᵥ sb j))) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    _ = dotProduct (M *ᵥ sb i) (pmOneMat *ᵥ (M *ᵥ sb j)) := by
        rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    _ = mform (M *ᵥ sb i) (M *ᵥ sb j) := rfl
    _ = mform (sb i) (sb j) := h i j
    _ = dotProduct (sb i) (pmOneMat *ᵥ sb j) := rfl

/-- The transpose condition follows from the column condition. -/
lemma jorth_row_of_col {M : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ}
    (hcol : Mᵀ * pmOneMat * M = pmOneMat) :
    M * pmOneMat * Mᵀ = pmOneMat := by
  have hLM : (pmOneMat * Mᵀ * pmOneMat) * M = 1 := by
    rw [show (pmOneMat * Mᵀ * pmOneMat) * M
        = pmOneMat * (Mᵀ * pmOneMat * M) from by simp only [Matrix.mul_assoc],
      hcol, pmOneMat_mul_pmOneMat]
  have hML : M * (pmOneMat * Mᵀ * pmOneMat) = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ
      (by simp : Fintype.card (Fin 2 ⊕ Fin 1) = Fintype.card (Fin 2 ⊕ Fin 1))).mp hLM
  have hJ : M * pmOneMat * Mᵀ * pmOneMat = 1 := by
    rw [show M * pmOneMat * Mᵀ * pmOneMat = M * (pmOneMat * Mᵀ * pmOneMat) from by
        simp only [Matrix.mul_assoc]]
    exact hML
  calc M * pmOneMat * Mᵀ = (M * pmOneMat * Mᵀ) * (pmOneMat * pmOneMat) := by
        rw [pmOneMat_mul_pmOneMat, Matrix.mul_one]
    _ = (M * pmOneMat * Mᵀ * pmOneMat) * pmOneMat := by simp only [Matrix.mul_assoc]
    _ = 1 * pmOneMat := by rw [hJ]
    _ = pmOneMat := Matrix.one_mul _

/-- The columns of `matOfCols U W Z` pair like the standard basis when `U, W, Z` is a
Minkowski-orthonormal frame. -/
lemma matOfCols_cols_on (U W Z : Fin 2 ⊕ Fin 1 → ℝ)
    (hUU : mink U U = -1) (hUW : mink U W = 0) (hWW : mink W W = 1)
    (hZU : mink Z U = 0) (hZW : mink Z W = 0) (hZZ : mink Z Z = 1) :
    ∀ i j, mform ((matOfCols U W Z) *ᵥ sb i) ((matOfCols U W Z) *ᵥ sb j)
      = mform (sb i) (sb j) := by
  have hWU : mink W U = 0 := by rw [minkSeg_comm]; exact hUW
  have hUZ : mink U Z = 0 := by rw [minkSeg_comm]; exact hZU
  have hWZ : mink W Z = 0 := by rw [minkSeg_comm]; exact hZW
  intro i j
  simp only [← mink_eq_mform]
  rcases i with i | i <;> rcases j with j | j
  · fin_cases i <;> fin_cases j
    · show mink (matOfCols U W Z *ᵥ sb (Sum.inl (0 : Fin 2)))
          (matOfCols U W Z *ᵥ sb (Sum.inl (0 : Fin 2)))
        = mink (sb (Sum.inl (0 : Fin 2))) (sb (Sum.inl (0 : Fin 2)))
      rw [matOfCols_col_inl0, hWW]; simp [mink, sb]
    · show mink (matOfCols U W Z *ᵥ sb (Sum.inl (0 : Fin 2)))
          (matOfCols U W Z *ᵥ sb (Sum.inl (1 : Fin 2)))
        = mink (sb (Sum.inl (0 : Fin 2))) (sb (Sum.inl (1 : Fin 2)))
      rw [matOfCols_col_inl0, matOfCols_col_inl1, hWZ]; simp [mink, sb]
    · show mink (matOfCols U W Z *ᵥ sb (Sum.inl (1 : Fin 2)))
          (matOfCols U W Z *ᵥ sb (Sum.inl (0 : Fin 2)))
        = mink (sb (Sum.inl (1 : Fin 2))) (sb (Sum.inl (0 : Fin 2)))
      rw [matOfCols_col_inl0, matOfCols_col_inl1, hZW]; simp [mink, sb]
    · show mink (matOfCols U W Z *ᵥ sb (Sum.inl (1 : Fin 2)))
          (matOfCols U W Z *ᵥ sb (Sum.inl (1 : Fin 2)))
        = mink (sb (Sum.inl (1 : Fin 2))) (sb (Sum.inl (1 : Fin 2)))
      rw [matOfCols_col_inl1, hZZ]; simp [mink, sb]
  · fin_cases i <;> fin_cases j
    · show mink (matOfCols U W Z *ᵥ sb (Sum.inl (0 : Fin 2)))
          (matOfCols U W Z *ᵥ sb (Sum.inr (0 : Fin 1)))
        = mink (sb (Sum.inl (0 : Fin 2))) (sb (Sum.inr (0 : Fin 1)))
      rw [matOfCols_col_inl0, matOfCols_col_inr, hWU]; simp [mink, sb]
    · show mink (matOfCols U W Z *ᵥ sb (Sum.inl (1 : Fin 2)))
          (matOfCols U W Z *ᵥ sb (Sum.inr (0 : Fin 1)))
        = mink (sb (Sum.inl (1 : Fin 2))) (sb (Sum.inr (0 : Fin 1)))
      rw [matOfCols_col_inl1, matOfCols_col_inr, hZU]; simp [mink, sb]
  · fin_cases i <;> fin_cases j
    · show mink (matOfCols U W Z *ᵥ sb (Sum.inr (0 : Fin 1)))
          (matOfCols U W Z *ᵥ sb (Sum.inl (0 : Fin 2)))
        = mink (sb (Sum.inr (0 : Fin 1))) (sb (Sum.inl (0 : Fin 2)))
      rw [matOfCols_col_inr, matOfCols_col_inl0, hUW]; simp [mink, sb]
    · show mink (matOfCols U W Z *ᵥ sb (Sum.inr (0 : Fin 1)))
          (matOfCols U W Z *ᵥ sb (Sum.inl (1 : Fin 2)))
        = mink (sb (Sum.inr (0 : Fin 1))) (sb (Sum.inl (1 : Fin 2)))
      rw [matOfCols_col_inr, matOfCols_col_inl1, hUZ]; simp [mink, sb]
  · fin_cases i <;> fin_cases j
    · show mink (matOfCols U W Z *ᵥ sb (Sum.inr (0 : Fin 1)))
          (matOfCols U W Z *ᵥ sb (Sum.inr (0 : Fin 1)))
        = mink (sb (Sum.inr (0 : Fin 1))) (sb (Sum.inr (0 : Fin 1)))
      rw [matOfCols_col_inr, hUU]; simp [mink, sb]

/-! ## Minkowski pairings of the hyperboloid lifts -/

lemma mink_hlift_self' {n : ℕ} (u : E n) : mink (hlift u) (hlift u) = -1 := by
  rw [mink_eq_mform]; exact mform_hlift_self u

lemma mink_hlift_neg_cosh' {n : ℕ} (u v : E n) :
    mink (hlift u) (hlift v) = -Real.cosh (hdist u v) := by
  rw [mink_eq_mform, mform_hlift_hlift]
  linarith [cosh_hdist u v]

/-! ## The lift of the standard line -/

lemma tpart_lineStd (s : ℝ) : tpart (FermiTwo.lineStd s) = Real.cosh s := by
  rw [tpart, FermiTwo.lineStd]
  rw [norm_smul, FermiTwo.axis, EuclideanSpace.single, PiLp.norm_single]
  simp only [norm_one, mul_one, Real.norm_eq_abs, sq_abs]
  rw [show (1 : ℝ) + Real.sinh s ^ 2 = Real.cosh s ^ 2 from by rw [Real.cosh_sq]; ring]
  exact Real.sqrt_sq (le_of_lt (Real.cosh_pos s))

lemma sb_inl_apply (i : Fin 2) : sb (Sum.inl (0 : Fin 2)) (Sum.inl i) = FermiTwo.axis i := by
  by_cases hi : i = 0
  · subst hi; simp [sb, FermiTwo.axis, EuclideanSpace.single]
  · simp [sb, FermiTwo.axis, EuclideanSpace.single, hi]

lemma hlift_lineStd (s : ℝ) :
    hlift (FermiTwo.lineStd s) = Real.cosh s • sb (Sum.inr 0) + Real.sinh s • sb (Sum.inl 0) := by
  have ht := tpart_lineStd s
  funext z
  rcases z with i | j
  · change (Real.sinh s • FermiTwo.axis) i
      = (Real.cosh s • sb (Sum.inr 0) + Real.sinh s • sb (Sum.inl 0)) (Sum.inl i)
    rw [PiLp.smul_apply]
    rw [show FermiTwo.axis i = sb (Sum.inl (0 : Fin 2)) (Sum.inl i) from (sb_inl_apply i).symm]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hz : sb (Sum.inr (0 : Fin 1)) (Sum.inl i) = 0 := by simp [sb]
    rw [hz]; ring
  · obtain rfl : j = 0 := Subsingleton.elim j 0
    show tpart (FermiTwo.lineStd s)
      = (Real.cosh s • sb (Sum.inr 0) + Real.sinh s • sb (Sum.inl 0)) (Sum.inr 0)
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, ht]
    simp [sb]

/-! ## The main theorem -/

theorem existsIsomOfGeodFormula (hA : Submission.Mostow.POActionProp 2)
    (hI : Submission.Mostow.HypIsometryProp 2) (line : ℝ → Submission.Mostow.E 2)
    (hline : ∀ s t : ℝ, Submission.Mostow.hdist (line s) (line t) = |s - t|)
    (hform : ∀ s : ℝ, Submission.Mostow.hlift (line s) =
      Real.cosh s • Submission.Mostow.hlift (line 0) +
        Real.sinh s • ((Real.sinh 1)⁻¹ •
          (Submission.Mostow.hlift (line 1) - Real.cosh 1 • Submission.Mostow.hlift (line 0)))) :
    ∃ g : LeanEval.Geometry.MostowRigidity.PO 2 1,
      ∀ s : ℝ, g • Work.Mostow.FermiTwo.lineStd s = line s := by
  set U : Fin 2 ⊕ Fin 1 → ℝ := hlift (line 0) with hU
  set V : Fin 2 ⊕ Fin 1 → ℝ := hlift (line 1) with hV
  set W : Fin 2 ⊕ Fin 1 → ℝ :=
    (Real.sinh 1)⁻¹ • (hlift (line 1) - Real.cosh 1 • hlift (line 0)) with hW
  set Z : Fin 2 ⊕ Fin 1 → ℝ := xp U W with hZ
  have hUU : mink U U = -1 := by rw [hU]; exact mink_hlift_self' (line 0)
  have hVV : mink V V = -1 := by rw [hV]; exact mink_hlift_self' (line 1)
  have hUV : mink U V = -Real.cosh 1 := by
    rw [hU, hV, mink_hlift_neg_cosh', hline 0 1]
    norm_num
  have hUW : mink U W = 0 := by
    rw [hW, minkSmul_right, minkSub_right, minkSmul_right, hUV, hUU]; ring
  have hWW : mink W W = 1 := by
    rw [hW, minkSeg_smul]
    have hkey : mink (V - Real.cosh 1 • U) (V - Real.cosh 1 • U) = Real.sinh 1 ^ 2 := by
      rw [minkFrame_sub_right, minkFrame_sub_left, minkFrame_sub_left,
        minkFrame_smul_left, minkFrame_smul_right, minkSeg_smul, hVV, hUV, minkSeg_comm, hUV, hUU]
      have h := Real.cosh_sq_sub_sinh_sq 1
      nlinarith [h]
    have hs : Real.sinh 1 ≠ 0 := (Real.sinh_pos_iff.mpr one_pos).ne'
    rw [hkey, ← sq, inv_pow]
    exact inv_mul_cancel₀ (pow_ne_zero 2 hs)
  have hZU : mink Z U = 0 := by rw [hZ]; exact xp_mink_left U W
  have hZW : mink Z W = 0 := by rw [hZ]; exact xp_mink_right U W
  have hZZ : mink Z Z = 1 := by
    rw [hZ, xp_mink_self, hUU, hWW, minkSeg_comm W U, hUW]; ring
  have hcols := matOfCols_cols_on U W Z hUU hUW hWW hZU hZW hZZ
  have hcol : (matOfCols U W Z)ᵀ * pmOneMat * (matOfCols U W Z) = pmOneMat :=
    jorth_of_mform_cols hcols
  have hrow : (matOfCols U W Z) * pmOneMat * (matOfCols U W Z)ᵀ = pmOneMat :=
    jorth_row_of_col hcol
  set A : O1 2 := O1.ofMatrix (matOfCols U W Z) ⟨hcol, hrow⟩ with hAdef
  have hmatA : mat A = matOfCols U W Z := by rw [hAdef]; exact mat_O1_ofMatrix _ _
  have htsign : tsign A = 1 := by
    rw [tsign_eq_one_iff, hmatA]
    rw [show matOfCols U W Z (Sum.inr 0) (Sum.inr 0) = U (Sum.inr 0) from by simp [matOfCols],
      hU, hlift_inr]
    exact tpart_pos (line 0)
  refine ⟨(A : PO 2 1), fun s => ?_⟩
  apply hlift_injective
  rw [hA.2.1 A (FermiTwo.lineStd s), Hyper.hlift_actO, hmatA, htsign, one_smul]
  rw [hlift_lineStd s, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    matOfCols_col_inr, matOfCols_col_inl0]
  exact (hform s).symm

end

end Work.Mostow
