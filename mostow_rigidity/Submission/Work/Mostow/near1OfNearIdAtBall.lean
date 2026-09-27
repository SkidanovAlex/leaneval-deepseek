import Mathlib
import Submission.Work.Mostow.mlDefs
import Submission.Work.Mostow.chartClose

/-!
# The bridge from `NearIdAt` on the unit ball to `Near1` of the lift

The analytic input is available as `Work.Mostow.chartClose` (proved, sorry-free): for `‖w‖ ≤ K` and
`hdist w w' ≤ 1`, every coordinate of `v - w` and the difference `tpart v - tpart w` are bounded by
`C (K) * hdist w w'`.  Use it with `K = Real.sinh 1` and with `K = 0`.

Probe points: `u₀ := 0` and `u_k := Real.sinh 1 • EuclideanSpace.single k 1` for `k : Fin n`.
Both satisfy `hdist 0 u_k ≤ 1`, hence by `NearIdAt` we get `hdist u_k (g • u_k) < η` and
`hdist 0 (g • 0) < η`.

With `A := mat (ToO g) = LambdaMat g`, `s_k := Pi.single (Sum.inl k) 1` and `t := hlift 0`, the
relation `A *ᵥ hlift u = hlift (g • u)` gives, in coordinates,
`Real.sinh 1 * (A l (inl k) - 1 l) = (hlift (g • u_k) - hlift u_k) l - cosh 1 * (hlift (g • 0) - hlift 0) l`,
and the two displacements are `< η`.  The last column is `hlift (g • 0)`, giving the remaining
entries.
-/
open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Matrix

namespace Work.Mostow

noncomputable section

variable {n : ℕ}

/-! ## The probe points `sinh 1 • e_k` -/

/-- The probe point `Real.sinh 1 • e_k` has norm `Real.sinh 1`. -/
lemma norm_sinh_single (n : ℕ) (k : Fin n) :
    ‖(Real.sinh 1 • EuclideanSpace.single k 1 : E n)‖ = Real.sinh 1 := by
  simp [EuclideanSpace.single_apply, norm_smul, Real.norm_eq_abs, abs_one, one_mul]

/-- The probe point `Real.sinh 1 • e_k` lies at hyperbolic distance exactly `1` from the base point. -/
lemma hdist_sinh_single (n : ℕ) (k : Fin n) :
    hdist (0 : E n) (Real.sinh 1 • EuclideanSpace.single k 1) = 1 := by
  rw [hdist]
  have h1 : tpart (0 : E n) = 1 := by simp [tpart]
  rw [h1, inner_zero_left, one_mul, sub_zero]
  have ht : tpart (Real.sinh 1 • EuclideanSpace.single k 1 : E n) = Real.cosh 1 := by
    simp [tpart, EuclideanSpace.single_apply, norm_smul, Real.norm_eq_abs, abs_one, one_mul]
    rw [← Real.cosh_sq']
    exact Real.sqrt_sq (le_of_lt (Real.cosh_pos 1))
  rw [ht, Real.arcosh_cosh (by norm_num : (0 : ℝ) ≤ 1)]

/-- The hyperboloid lift of the probe point `Real.sinh 1 • e_k`, decomposed in the basis
`{s_k, hlift 0}`. -/
lemma hlift_sinh_single (n : ℕ) (k : Fin n) :
    hlift (Real.sinh 1 • EuclideanSpace.single k 1 : E n)
      = Real.sinh 1 • (Pi.single (Sum.inl k) 1 : Fin n ⊕ Fin 1 → ℝ)
        + Real.cosh 1 • hlift (0 : E n) := by
  rw [hlift_zero]
  ext a
  rcases a with i | j
  · simp [hlift, Pi.single_apply]
  · fin_cases j
    simp [hlift, tpart, EuclideanSpace.single_apply, norm_smul, Real.norm_eq_abs, abs_one, one_mul]
    rw [← Real.cosh_sq']
    exact Real.sqrt_sq (le_of_lt (Real.cosh_pos 1))

/-- `Pi.single (Sum.inl k) 1` evaluated at `l` is the Kronecker delta `dE n l (Sum.inl k)`. -/
lemma single_inl_eq_dE (n : ℕ) (k : Fin n) (l : Fin n ⊕ Fin 1) :
    (Pi.single (Sum.inl k) (1 : ℝ) : Fin n ⊕ Fin 1 → ℝ) l = dE n l (Sum.inl k) := by
  rw [Pi.single_apply, dE_apply]

/-- The key coordinate identity: the `k`-th column defect of `LambdaMat g` is the value of the two
displacements of the probe points. -/
lemma LambdaMat_col_entry (hA : POActionProp n) (g : PO n 1) (k : Fin n)
    (l : Fin n ⊕ Fin 1) :
    Real.sinh 1 * (LambdaMat g l (Sum.inl k) - dE n l (Sum.inl k))
      = (hlift (g • (Real.sinh 1 • EuclideanSpace.single k 1 : E n)) l
          - hlift (Real.sinh 1 • EuclideanSpace.single k 1 : E n) l)
        - Real.cosh 1 * (hlift (g • (0 : E n)) l - hlift (0 : E n) l) := by
  have huk := hlift_sinh_single n k
  have hgk : hlift (g • (Real.sinh 1 • EuclideanSpace.single k 1 : E n))
      = Real.sinh 1 • (LambdaMat g *ᵥ (Pi.single (Sum.inl k) 1 : Fin n ⊕ Fin 1 → ℝ))
        + Real.cosh 1 • hlift (g • (0 : E n)) := by
    rw [hlift_LambdaMat hA g (Real.sinh 1 • EuclideanSpace.single k 1 : E n), huk,
      Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      ← hlift_LambdaMat hA g (0 : E n)]
  have h1 := congrFun hgk l
  have h2 := congrFun huk l
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
  rw [Matrix.mulVec_single_one, Matrix.col_apply] at h1
  rw [single_inl_eq_dE] at h2
  rw [h1, h2]
  ring

/-- The last column of `LambdaMat g` is `hlift (g • 0)`. -/
lemma LambdaMat_last_col (hA : POActionProp n) (g : PO n 1) (l : Fin n ⊕ Fin 1) :
    LambdaMat g l (Sum.inr 0) = hlift (g • (0 : E n)) l := by
  have h := congrFun (hlift_LambdaMat hA g (0 : E n)) l
  rw [hlift_zero, Matrix.mulVec_single_one, Matrix.col_apply] at h
  exact h.symm

theorem near1OfNearIdAtBall (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (η : ℝ), 0 < η → η ≤ 1 → ∀ g : LeanEval.Geometry.MostowRigidity.PO n 1,
      Submission.Mostow.NearIdAt g (0 : Submission.Mostow.E n) η →
      Work.Mostow.Near1 (Work.Mostow.ToO g) (C * η) := by
  obtain ⟨Csh, hCshpos, hCsh⟩ := chartClose n hI (Real.sinh 1)
  obtain ⟨C0, hC0pos, hC0⟩ := chartClose n hI 0
  have hsinh1 : 0 < Real.sinh 1 := Real.sinh_pos_iff.mpr one_pos
  have hcosh1 : 0 < Real.cosh 1 := Real.cosh_pos 1
  set CA : ℝ := (1 / Real.sinh 1) * (Csh + Real.cosh 1 * C0) with hCAdef
  have hCApos : 0 < CA := by
    rw [hCAdef]
    exact mul_pos (by positivity) (by nlinarith [hCshpos, hC0pos, hcosh1])
  refine ⟨max CA (Real.cosh 1), lt_of_lt_of_le hCApos (le_max_left _ _), ?_⟩
  intro η hη hη1 g hnear
  have hCAη : CA * η ≤ max CA (Real.cosh 1) * η :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (le_of_lt hη)
  have hCη : Real.cosh 1 * η ≤ max CA (Real.cosh 1) * η :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) (le_of_lt hη)
  have h0η : hdist (0 : E n) (g • (0 : E n)) < η := hnear 0 (by rw [hdist_self]; norm_num)
  have h0η1 : hdist (0 : E n) (g • (0 : E n)) ≤ 1 := le_of_lt (lt_of_lt_of_le h0η hη1)
  have h0nonneg : 0 ≤ hdist (0 : E n) (g • (0 : E n)) := hdist_nonneg _ _
  have hch0 := hC0 (0 : E n) (g • (0 : E n)) (by simp) h0η1
  -- the `k`-th column bounds
  have colbound : ∀ (k : Fin n) (l : Fin n ⊕ Fin 1),
      |LambdaMat g l (Sum.inl k) - dE n l (Sum.inl k)| ≤ CA * η := by
    intro k l
    have huk_η : hdist (Real.sinh 1 • EuclideanSpace.single k 1 : E n)
        (g • (Real.sinh 1 • EuclideanSpace.single k 1 : E n)) < η :=
      hnear _ (le_of_eq (hdist_sinh_single n k))
    have huk1 : hdist (Real.sinh 1 • EuclideanSpace.single k 1 : E n)
        (g • (Real.sinh 1 • EuclideanSpace.single k 1 : E n)) ≤ 1 :=
      le_of_lt (lt_of_lt_of_le huk_η hη1)
    have hch := hCsh _ _ (le_of_eq (norm_sinh_single n k)) huk1
    have b1 : |(hlift (g • (Real.sinh 1 • EuclideanSpace.single k 1 : E n)) l
        - hlift (Real.sinh 1 • EuclideanSpace.single k 1 : E n) l)| ≤ Csh * η := by
      rcases l with i | j
      · rw [hlift_inl, hlift_inl]
        calc |(g • (Real.sinh 1 • EuclideanSpace.single k 1 : E n) : E n) i
              - (Real.sinh 1 • EuclideanSpace.single k 1 : E n) i|
            ≤ Csh * hdist (Real.sinh 1 • EuclideanSpace.single k 1 : E n)
                (g • (Real.sinh 1 • EuclideanSpace.single k 1 : E n)) := hch.1 i
          _ ≤ Csh * η := mul_le_mul_of_nonneg_left (le_of_lt huk_η) (le_of_lt hCshpos)
      · obtain rfl : j = 0 := Subsingleton.elim j 0
        rw [hlift_inr, hlift_inr]
        calc |tpart (g • (Real.sinh 1 • EuclideanSpace.single k 1 : E n))
              - tpart (Real.sinh 1 • EuclideanSpace.single k 1 : E n)|
            ≤ Csh * hdist (Real.sinh 1 • EuclideanSpace.single k 1 : E n)
                (g • (Real.sinh 1 • EuclideanSpace.single k 1 : E n)) := hch.2
          _ ≤ Csh * η := mul_le_mul_of_nonneg_left (le_of_lt huk_η) (le_of_lt hCshpos)
    have b2 : |(hlift (g • (0 : E n)) l - hlift (0 : E n) l)| ≤ C0 * η := by
      rcases l with i | j
      · rw [hlift_inl, hlift_inl]
        calc |(g • (0 : E n) : E n) i - (0 : E n) i|
            ≤ C0 * hdist (0 : E n) (g • (0 : E n)) := hch0.1 i
          _ ≤ C0 * η := mul_le_mul_of_nonneg_left (le_of_lt h0η) (le_of_lt hC0pos)
      · obtain rfl : j = 0 := Subsingleton.elim j 0
        rw [hlift_inr, hlift_inr]
        calc |tpart (g • (0 : E n)) - tpart (0 : E n)|
            ≤ C0 * hdist (0 : E n) (g • (0 : E n)) := hch0.2
          _ ≤ C0 * η := mul_le_mul_of_nonneg_left (le_of_lt h0η) (le_of_lt hC0pos)
    have hbd : |(hlift (g • (Real.sinh 1 • EuclideanSpace.single k 1 : E n)) l
          - hlift (Real.sinh 1 • EuclideanSpace.single k 1 : E n) l)
          - Real.cosh 1 * (hlift (g • (0 : E n)) l - hlift (0 : E n) l)|
        ≤ (Csh + Real.cosh 1 * C0) * η := by
      have h3 : |(hlift (g • (Real.sinh 1 • EuclideanSpace.single k 1 : E n)) l
            - hlift (Real.sinh 1 • EuclideanSpace.single k 1 : E n) l)
            - Real.cosh 1 * (hlift (g • (0 : E n)) l - hlift (0 : E n) l)|
          ≤ |hlift (g • (Real.sinh 1 • EuclideanSpace.single k 1 : E n)) l
              - hlift (Real.sinh 1 • EuclideanSpace.single k 1 : E n) l|
            + Real.cosh 1 * |hlift (g • (0 : E n)) l - hlift (0 : E n) l| := by
        have h := abs_add_le
          ((hlift (g • (Real.sinh 1 • EuclideanSpace.single k 1 : E n)) l
              - hlift (Real.sinh 1 • EuclideanSpace.single k 1 : E n) l))
          (-(Real.cosh 1 * (hlift (g • (0 : E n)) l - hlift (0 : E n) l)))
        rw [abs_neg, abs_mul, abs_of_pos hcosh1] at h
        rw [sub_eq_add_neg]
        exact h
      nlinarith [b1, b2, hcosh1]
    have hfinal : |Real.sinh 1 * (LambdaMat g l (Sum.inl k) - dE n l (Sum.inl k))|
        ≤ (Csh + Real.cosh 1 * C0) * η := by
      rw [LambdaMat_col_entry hA g k l]
      exact hbd
    calc |LambdaMat g l (Sum.inl k) - dE n l (Sum.inl k)|
        = (1 / Real.sinh 1)
            * |Real.sinh 1 * (LambdaMat g l (Sum.inl k) - dE n l (Sum.inl k))| := by
          rw [abs_mul, abs_of_pos hsinh1, one_div, inv_mul_cancel_left₀ (ne_of_gt hsinh1)]
      _ ≤ (1 / Real.sinh 1) * ((Csh + Real.cosh 1 * C0) * η) :=
          mul_le_mul_of_nonneg_left hfinal (by positivity)
      _ = CA * η := by rw [hCAdef]; ring
  -- the last column bounds
  have lastcol : ∀ l : Fin n ⊕ Fin 1,
      |LambdaMat g l (Sum.inr 0) - dE n l (Sum.inr 0)| ≤ Real.cosh 1 * η := by
    intro l
    rw [LambdaMat_last_col hA g l]
    rcases l with i | j
    · rw [hlift_inl, show dE n (Sum.inl i) (Sum.inr 0) = 0 from dE_ne (by simp), sub_zero]
      calc |(g • (0 : E n) : E n) i| ≤ ‖g • (0 : E n)‖ := by
            simpa using PiLp.norm_apply_le (g • (0 : E n)) i
        _ = Real.sinh (hdist (0 : E n) (g • (0 : E n))) := (sinh_hdist_zero _).symm
        _ ≤ Real.sinh η := Real.sinh_le_sinh.mpr (le_of_lt h0η)
        _ ≤ Real.cosh 1 * η := by
            have h := absSinhSubSinhLe 1 η 0 (le_of_lt hη) le_rfl hη1 zero_le_one
            rw [Real.sinh_zero, sub_zero, sub_zero, abs_of_nonneg (le_of_lt hη),
              abs_of_nonneg (Real.sinh_nonneg_iff.mpr (le_of_lt hη))] at h
            exact h
    · obtain rfl : j = 0 := Subsingleton.elim j 0
      rw [hlift_inr, dE_self]
      rw [show tpart (g • (0 : E n)) = Real.cosh (hdist (0 : E n) (g • (0 : E n))) from
        (cosh_hdist_zero _).symm]
      have hb := coshSubOneLeSq (hdist (0 : E n) (g • (0 : E n))) h0nonneg h0η1
      have hsq : (hdist (0 : E n) (g • (0 : E n))) ^ 2 ≤ η := by
        nlinarith [h0nonneg, le_of_lt h0η, hη1, hη]
      have habs : |Real.cosh (hdist (0 : E n) (g • (0 : E n))) - 1|
          = Real.cosh (hdist (0 : E n) (g • (0 : E n))) - 1 :=
        abs_of_nonneg (by linarith [Real.one_le_cosh (hdist (0 : E n) (g • (0 : E n)))])
      rw [habs]
      exact le_trans hb (mul_le_mul_of_nonneg_left hsq (le_of_lt hcosh1))
  intro i j
  rw [mat_ToO]
  rcases j with k | k
  · exact le_trans (colbound k i) hCAη
  · obtain rfl : k = 0 := Subsingleton.elim k 0
    exact le_trans (lastcol i) hCη

end

end Work.Mostow
