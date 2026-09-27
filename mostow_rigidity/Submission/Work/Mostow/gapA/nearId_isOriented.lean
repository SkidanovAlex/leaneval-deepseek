import Mathlib
import Submission.Work.Mostow.gapA.defs
import Submission.Work.Mostow.pairStabDefs

/-!
# `nearId_isOriented`: a near-identity isometry of `ℍ³` preserves orientation

`Work.Mostow.IsOriented g` says that the determinant of a lift of `g ∈ PO(3,1)` to
`O(3,1)` is positive.  We prove that if `g` moves every point of the unit ball around `z`
by less than `η ≤ 1`, then `g` is orientation preserving.

The mathematical input is the following.  Write `M = emat f` for the lift of `f` that
preserves the upper sheet of the hyperboloid, and suppose `det M = -1`.  Then (a) `-1` is an
eigenvalue of `M`, (b) some eigenvector `n` of `M` for the eigenvalue `-1` is space-like, and
(c) after rescaling, `⟨n,n⟩ = 1`, so that `P = n^⊥` is a totally geodesic plane of `ℍ³`,
preserved by `f`, and `f` acts on `ℍ³ = P × ℝ` as `(x, t) ↦ (f_0 x, -t)` for an isometry `f_0`
of the plane `P`.  Moving from `z` one unit away from `P` (in the normal direction) therefore
displaces by at least `2`, contradicting `NearIdAt f z η` with `η ≤ 1`.
-/

set_option maxHeartbeats 4000000

namespace Work.Mostow.gapA

open LeanEval.Geometry.MostowRigidity Submission.Mostow
open Matrix
open scoped Matrix

noncomputable section

/-! ## Bilinearity of `mform` -/

/-- The Minkowski square of a two-term linear combination. -/
lemma mform_lincomb2 {n : ℕ} (A B : Fin n ⊕ Fin 1 → ℝ) (a b : ℝ) :
    mform (a • A + b • B) (a • A + b • B) =
      a ^ 2 * mform A A + 2 * (a * b) * mform A B + b ^ 2 * mform B B := by
  have hBA : mform B A = mform A B := mform_comm B A
  rw [mform_add_left, mform_add_right, mform_add_right, mform_smul, mform_smul, mform_smul,
    mform_smul, hBA]
  ring

/-- `mform` of two two-term linear combinations. -/
lemma mform_pair2 {n : ℕ} (A B C D : Fin n ⊕ Fin 1 → ℝ) (a b c d : ℝ) :
    mform (a • A + b • B) (c • C + d • D) =
      a * c * mform A C + a * d * mform A D + b * c * mform B C + b * d * mform B D := by
  rw [mform_add_left, mform_add_right, mform_add_right, mform_smul, mform_smul, mform_smul,
    mform_smul]
  ring

/-- `mform` of two hyperboloid lifts is the negative `cosh` kernel. -/
lemma mform_hlift_pair {n : ℕ} (u v : E n) :
    mform (hlift u) (hlift v) = inner ℝ u v - tpart u * tpart v := by
  rw [mform_eq]; simp

/-- `1 ≤ -mform (hlift u) (hlift v)`: reverse Cauchy–Schwarz on the hyperboloid. -/
lemma one_le_neg_mform_hlift {n : ℕ} (u v : E n) : 1 ≤ -mform (hlift u) (hlift v) := by
  rw [mform_hlift_pair]
  have h := one_le_cosh_hdist u v
  linarith

/-- The hyperbolic distance in terms of the Minkowski form of the lifts. -/
lemma hdist_eq_neg_mform {n : ℕ} (u v : E n) :
    hdist u v = Real.arcosh (-mform (hlift u) (hlift v)) := by
  rw [Hyper.hdist_eq_cc, Hyper.cc, mform_hlift_pair]
  ring_nf

/-! ## Determinants of `J` and of `J`-orthogonal matrices -/

/-- `det J = -1` for `J = diag(1,1,1,-1)`. -/
lemma det_pmOneMat3 : (pmOneMat (p := Fin 3) (q := Fin 1) (α := ℝ)).det = -1 := by
  rw [pmOneMat, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, Matrix.det_neg, Matrix.det_one]
  norm_num

/-- A `J`-orthogonal matrix has determinant `±1`. -/
lemma det_eq_pm_one {M : Matrix (Fin 3 ⊕ Fin 1) (Fin 3 ⊕ Fin 1) ℝ}
    (hM : Mᵀ * pmOneMat * M = pmOneMat) : M.det = 1 ∨ M.det = -1 := by
  have h := congrArg Matrix.det hM
  simp only [Matrix.det_mul, Matrix.det_transpose] at h
  rw [det_pmOneMat3] at h
  have h2 : M.det ^ 2 = 1 := by
    rw [sq]; linarith
  exact sq_eq_one_iff.mp h2

/-- If a `J`-orthogonal matrix has determinant `-1`, then `-1` is an eigenvalue. -/
lemma negOneEigen {M : Matrix (Fin 3 ⊕ Fin 1) (Fin 3 ⊕ Fin 1) ℝ}
    (hM : Mᵀ * pmOneMat * M = pmOneMat) (hdet : M.det = -1) :
    ∃ v : Fin 3 ⊕ Fin 1 → ℝ, v ≠ 0 ∧ M *ᵥ v = -v := by
  set J : Matrix (Fin 3 ⊕ Fin 1) (Fin 3 ⊕ Fin 1) ℝ := pmOneMat with hJdef
  have hJJ : J * J = 1 := by
    rw [hJdef]
    exact pmOneMat_mul_pmOneMat (Fin 3) (Fin 1) ℝ
  have hJdet : J.det = -1 := by rw [hJdef]; exact det_pmOneMat3
  -- `J Mᵀ J` is a left inverse of `M`
  have hstep : J * Mᵀ * J * M = 1 := by
    calc J * Mᵀ * J * M = J * (Mᵀ * J * M) := by simp only [mul_assoc]
      _ = J * J := by rw [hM]
      _ = 1 := hJJ
  -- `(J Mᵀ J + 1) * M = 1 + M`
  have hmul : (J * Mᵀ * J + 1) * M = 1 + M := by
    rw [Matrix.add_mul, hstep, one_mul]
  -- `J Mᵀ J + 1 = J (Mᵀ + 1) J`
  have hfac : J * Mᵀ * J + 1 = J * (Mᵀ + 1) * J := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hJJ]
  -- `det (J Mᵀ J + 1) = det (1 + M)`
  have hdet1 : (J * Mᵀ * J + 1).det = (1 + M).det := by
    rw [hfac, Matrix.det_mul, Matrix.det_mul, hJdet,
      show (Mᵀ + 1).det = (1 + M).det from by
        rw [show Mᵀ + 1 = (1 + M)ᵀ by
          rw [Matrix.transpose_add, Matrix.transpose_one, add_comm], Matrix.det_transpose]]
    ring
  have hkey : (J * Mᵀ * J + 1).det * M.det = (1 + M).det := by
    rw [← Matrix.det_mul, hmul]
  rw [hdet1, hdet] at hkey
  have hzero : (1 + M).det = 0 := by linarith
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hzero
  refine ⟨v, hv, ?_⟩
  have h := hv0
  rw [Matrix.add_mulVec, Matrix.one_mulVec] at h
  have h2 : M *ᵥ v + v = 0 := by rw [add_comm]; exact h
  exact eq_neg_of_add_eq_zero_left h2

/-- A nonzero eigenvector of `emat f` for the eigenvalue `-1` is space-like. -/
lemma eigVecSpacelike (f : PO 3 1) (v : Fin 3 ⊕ Fin 1 → ℝ) (hv : v ≠ 0)
    (heig : emat f *ᵥ v = -v) : 0 < mform v v := by
  rcases lt_trichotomy (mform v v) 0 with hneg | hzero | hpos
  · -- time-like: `f` would map a future point to a past point
    exfalso
    set c : ℝ := Real.sqrt (-(mform v v)) with hcdef
    have hcpos : 0 < c := Real.sqrt_pos.mpr (by linarith)
    have hcsq : c * c = -(mform v v) := Real.mul_self_sqrt (by linarith)
    have hcne : c ≠ 0 := ne_of_gt hcpos
    set X : Fin 3 ⊕ Fin 1 → ℝ := c⁻¹ • v with hXdef
    have hXX : mform X X = -1 := by
      rw [hXdef, mform_smul]
      have hmv : mform v v = -(c * c) := by linarith [hcsq]
      rw [hmv]
      field_simp
    have heigX : emat f *ᵥ X = -X := by
      calc emat f *ᵥ X = emat f *ᵥ (c⁻¹ • v) := by rw [hXdef]
        _ = c⁻¹ • (emat f *ᵥ v) := Matrix.mulVec_smul _ _ _
        _ = c⁻¹ • (-v) := by rw [heig]
        _ = -(c⁻¹ • v) := smul_neg _ _
        _ = -X := by rw [hXdef]
    have hXt : htime X ≠ 0 := by
      intro h0
      have h := hXX
      rw [mform_eq, h0, mul_zero, sub_zero, real_inner_self_eq_norm_sq] at h
      nlinarith [sq_nonneg ‖hspat X‖]
    have key : ∀ Y : Fin 3 ⊕ Fin 1 → ℝ, mform Y Y = -1 → 0 < htime Y →
        emat f *ᵥ Y = -Y → False := by
      intro Y hYY hYt hY
      have hlift : hlift (hspat Y) = Y := Hyper.hlift_spat_of_mink Y hYY hYt
      have h1 : htime (emat f *ᵥ Y) = tpart (f • hspat Y) := by
        rw [← hlift, emat_hlift]
        rfl
      have h2 : htime (emat f *ᵥ Y) = -htime Y := by rw [hY, htime_neg]
      have := tpart_pos (f • hspat Y)
      linarith
    rcases lt_or_gt_of_ne hXt with hlt | hgt
    · refine key (-X) ?_ ?_ ?_
      · rw [mform_neg_left, mform_neg_right, hXX, neg_neg]
      · rw [htime_neg]; linarith
      · rw [Matrix.mulVec_neg, heigX, neg_neg]
    · exact key X hXX hgt heigX
  · -- null: `v` would be a null eigenvector with negative eigenvalue
    exfalso
    have hw : htime v ≠ 0 := by
      intro h0
      have h := hzero
      rw [mform_eq, h0, mul_zero, sub_zero, real_inner_self_eq_norm_sq] at h
      have hsp : hspat v = 0 := by
        have : ‖hspat v‖ = 0 := by nlinarith [sq_nonneg ‖hspat v‖]
        exact norm_eq_zero.mp this
      apply hv
      funext i
      rcases i with k | k
      · simpa [hspat] using congrArg (fun w : E 3 => w k) hsp
      · fin_cases k
        simpa [htime] using h0
    set ξ : E 3 := (htime v)⁻¹ • hspat v with hξdef
    have hnorm : ‖hspat v‖ = |htime v| := by
      have h := hzero
      rw [mform_eq, real_inner_self_eq_norm_sq] at h
      have h2 : ‖hspat v‖ ^ 2 = (htime v) ^ 2 := by linarith
      calc ‖hspat v‖ = Real.sqrt (‖hspat v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ = Real.sqrt ((htime v) ^ 2) := by rw [h2]
        _ = |htime v| := Real.sqrt_sq_eq_abs _
    have hξnorm : ‖ξ‖ = 1 := by
      have hmain : ‖((htime v)⁻¹ : ℝ)‖ * ‖hspat v‖ = 1 := by
        rw [norm_inv, hnorm, Real.norm_eq_abs]
        exact inv_mul_cancel₀ (abs_ne_zero.mpr hw)
      rw [hξdef, norm_smul]
      exact hmain
    have hξmem : ξ ∈ Sph 3 := (mem_Sph_iff ξ).mpr hξnorm
    have hv_eq : htime v • theta ξ = v := by
      funext i
      rcases i with k | k
      · show htime v * ξ k = v (Sum.inl k)
        have hξk : ξ k = (htime v)⁻¹ * v (Sum.inl k) := by
          rw [hξdef]
          simp [hspat]
        rw [hξk]
        field_simp
      · fin_cases k
        show htime v * 1 = v (Sum.inr 0)
        rw [mul_one]
        rfl
    have hθeig : emat f *ᵥ theta ξ = (-1 : ℝ) • theta ξ := by
      have h1' : htime v • (emat f *ᵥ theta ξ) = -(htime v • theta ξ) := by
        rw [← Matrix.mulVec_smul (emat f) (htime v) (theta ξ), hv_eq, heig]
      have h4 := congrArg (fun w : Fin 3 ⊕ Fin 1 → ℝ => (htime v)⁻¹ • w) h1'
      rw [smul_smul, inv_mul_cancel₀ hw, one_smul] at h4
      rw [smul_neg, smul_smul, inv_mul_cancel₀ hw, one_smul, ← neg_one_smul ℝ (theta ξ)] at h4
      exact h4
    obtain ⟨-, hposlam, -⟩ := lev_emat_eigen f hξmem hθeig
    norm_num at hposlam
  · exact hpos

/-! ## The displacement bound -/

/-- If `n` is a space-like unit vector with `emat f *ᵥ n = -n`, then some point of the closed
unit ball around `z` is moved by `f` at least `2`. -/
theorem displacementBound (f : PO 3 1) (n : Fin 3 ⊕ Fin 1 → ℝ)
    (hn : mform n n = 1) (heig : emat f *ᵥ n = -n) (z : E 3) :
    ∃ y : E 3, hdist z y ≤ 1 ∧ 2 ≤ hdist y (f • y) := by
  have hOrth : IsJOrth (emat f) := emat_isJOrth f
  have hmf : ∀ x y : Fin 3 ⊕ Fin 1 → ℝ, mform (emat f *ᵥ x) (emat f *ᵥ y) = mform x y :=
    fun x y => mform_mulVec_mulVec hOrth x y
  have key : ∀ n : Fin 3 ⊕ Fin 1 → ℝ, mform n n = 1 → emat f *ᵥ n = -n →
      0 ≤ mform (hlift z) n →
      ∃ y : E 3, hdist z y ≤ 1 ∧ 2 ≤ hdist y (f • y) := by
    intro n hn heig hρ
    set Z : Fin 3 ⊕ Fin 1 → ℝ := hlift z with hZdef
    have hZZ : mform Z Z = -1 := by rw [hZdef]; exact Hyper.mink_hlift_self z
    set ρ : ℝ := mform Z n with hρdef
    have hρnn : 0 ≤ ρ := by rw [hρdef]; exact hρ
    set c : ℝ := Real.sqrt (1 + ρ ^ 2) with hcdef
    have hct : (0 : ℝ) ≤ 1 + ρ ^ 2 := by positivity
    have hcpos : 0 < c := Real.sqrt_pos.mpr (by linarith [sq_nonneg ρ])
    have hcsq : c ^ 2 = 1 + ρ ^ 2 := Real.sq_sqrt hct
    have hcne : c ≠ 0 := ne_of_gt hcpos
    set Q : Fin 3 ⊕ Fin 1 → ℝ := c⁻¹ • (Z - ρ • n) with hQdef
    have hZQn : Z = c • Q + ρ • n := by
      rw [hQdef, smul_smul, mul_inv_cancel₀ hcne, one_smul]
      abel
    have hsub : Z - ρ • n = (1 : ℝ) • Z + (-ρ) • n := by
      rw [one_smul, neg_smul, sub_eq_add_neg]
    have hWsq : mform (Z - ρ • n) (Z - ρ • n) = -(1 + ρ ^ 2) := by
      rw [hsub, mform_lincomb2, hZZ, ← hρdef, hn]
      ring
    have hQQ : mform Q Q = -1 := by
      rw [hQdef, mform_smul, hWsq, ← hcsq]
      have h : c⁻¹ * c⁻¹ * -(c ^ 2) = -1 := by
        field_simp
      exact h
    have hQn : mform Q n = 0 := by
      rw [hQdef, mform_smul_left, mform_sub_left, mform_smul_left, ← hρdef, hn]
      ring
    -- time coordinates
    set q : ℝ := htime Q with hqdef
    set w : ℝ := htime n with hwdef
    have hqwn : q * w = inner ℝ (hspat Q) (hspat n) := by
      have h := hQn
      rw [mform_eq, ← hqdef, ← hwdef] at h
      linarith
    have hQnrm : ‖hspat Q‖ ^ 2 = q ^ 2 - 1 := by
      have h := hQQ
      rw [mform_eq, real_inner_self_eq_norm_sq, ← hqdef] at h
      linarith
    have hnnrm : ‖hspat n‖ ^ 2 = w ^ 2 + 1 := by
      have h := hn
      rw [mform_eq, real_inner_self_eq_norm_sq, ← hwdef] at h
      linarith
    have hsqrtn : ‖hspat n‖ = Real.sqrt (1 + w ^ 2) := by
      rw [← Real.sqrt_sq (norm_nonneg (hspat n)), hnnrm,
        show w ^ 2 + 1 = 1 + w ^ 2 from by ring]
    have hQtime : q = c⁻¹ * (tpart z - ρ * w) := by
      rw [hqdef, hQdef, htime_smul, htime_sub, htime_smul, hZdef, htime_hlift', hwdef]
    have hρw : ρ = inner ℝ z (hspat n) - tpart z * w := by
      rw [hρdef, hZdef, mform_eq, htime_hlift', hspat_hlift', ← hwdef]
    have hinner_le : inner ℝ z (hspat n) ≤ ‖z‖ * Real.sqrt (1 + w ^ 2) := by
      have h := real_inner_le_norm z (hspat n)
      rwa [hsqrtn] at h
    have hinner_ge : -(‖z‖ * Real.sqrt (1 + w ^ 2)) ≤ inner ℝ z (hspat n) := by
      have h := abs_real_inner_le_norm z (hspat n)
      rw [hsqrtn] at h
      have h2 := neg_abs_le (inner ℝ z (hspat n))
      linarith
    have hbrk : ‖z‖ * |w| < Real.sqrt (1 + ‖z‖ ^ 2) * Real.sqrt (1 + w ^ 2) := by
      rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 1 + ‖z‖ ^ 2),
        ← Real.sqrt_sq (mul_nonneg (norm_nonneg z) (abs_nonneg w))]
      apply Real.sqrt_lt_sqrt (by positivity)
      rw [mul_pow, sq_abs]
      nlinarith [sq_nonneg ‖z‖, sq_nonneg w]
    have hpos : 0 < tpart z * (1 + w ^ 2) - inner ℝ z (hspat n) * w := by
      have hspos : 0 < Real.sqrt (1 + w ^ 2) := Real.sqrt_pos.mpr (by positivity)
      have h4 : 0 < Real.sqrt (1 + ‖z‖ ^ 2) * (1 + w ^ 2)
          - ‖z‖ * Real.sqrt (1 + w ^ 2) * |w| := by
        have hsq : Real.sqrt (1 + w ^ 2) * Real.sqrt (1 + w ^ 2) = 1 + w ^ 2 :=
          Real.mul_self_sqrt (by positivity)
        have h5 : 0 < Real.sqrt (1 + w ^ 2) *
            (Real.sqrt (1 + ‖z‖ ^ 2) * Real.sqrt (1 + w ^ 2) - ‖z‖ * |w|) :=
          mul_pos hspos (sub_pos.mpr hbrk)
        calc 0 < Real.sqrt (1 + w ^ 2) *
              (Real.sqrt (1 + ‖z‖ ^ 2) * Real.sqrt (1 + w ^ 2) - ‖z‖ * |w|) := h5
          _ = Real.sqrt (1 + ‖z‖ ^ 2) * (Real.sqrt (1 + w ^ 2) * Real.sqrt (1 + w ^ 2))
              - Real.sqrt (1 + w ^ 2) * ‖z‖ * |w| := by ring
          _ = Real.sqrt (1 + ‖z‖ ^ 2) * (1 + w ^ 2)
              - ‖z‖ * Real.sqrt (1 + w ^ 2) * |w| := by rw [hsq]; ring
      have h6 : inner ℝ z (hspat n) * w ≤ ‖z‖ * Real.sqrt (1 + w ^ 2) * |w| := by
        rcases le_total 0 w with hw0 | hw0
        · have h7 : inner ℝ z (hspat n) * w ≤ (‖z‖ * Real.sqrt (1 + w ^ 2)) * w :=
            mul_le_mul_of_nonneg_right hinner_le hw0
          have h8 : (‖z‖ * Real.sqrt (1 + w ^ 2)) * w ≤ ‖z‖ * Real.sqrt (1 + w ^ 2) * |w| := by
            rw [abs_of_nonneg hw0]
          linarith
        · have h7 : inner ℝ z (hspat n) * w ≤ (-(‖z‖ * Real.sqrt (1 + w ^ 2))) * w :=
            mul_le_mul_of_nonpos_right hinner_ge hw0
          have h8 : (-(‖z‖ * Real.sqrt (1 + w ^ 2))) * w
              = ‖z‖ * Real.sqrt (1 + w ^ 2) * |w| := by
            rw [abs_of_nonpos hw0]; ring
          linarith
      rw [tpart]
      linarith
    have hqpos : 0 < q := by
      rw [hQtime]
      apply mul_pos (inv_pos.mpr hcpos)
      rw [hρw]
      nlinarith [hpos]
    have hwlt : |w| < q := by
      have h1 : (q * w) ^ 2 ≤ (q ^ 2 - 1) * (w ^ 2 + 1) := by
        have h2 : |inner ℝ (hspat Q) (hspat n)| ≤ ‖hspat Q‖ * ‖hspat n‖ :=
          abs_real_inner_le_norm _ _
        have h3 : (inner ℝ (hspat Q) (hspat n)) ^ 2 ≤ (‖hspat Q‖ * ‖hspat n‖) ^ 2 := by
          rw [sq_le_sq, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
          exact h2
        rw [mul_pow, hQnrm, hnnrm] at h3
        rwa [← hqwn] at h3
      have hq2 : 1 ≤ q ^ 2 := by nlinarith [hQnrm, sq_nonneg ‖hspat Q‖]
      have h4 : w ^ 2 ≤ q ^ 2 - 1 := by nlinarith [h1]
      have h5 : w ^ 2 < q ^ 2 := by linarith
      have h6 := sq_lt_sq.mp h5
      rwa [abs_of_pos hqpos] at h6
    -- the coefficients
    set A : ℝ := c * Real.cosh 1 + ρ * Real.sinh 1 with hAdef
    set B : ℝ := ρ * Real.cosh 1 + c * Real.sinh 1 with hBdef
    have hsinh1pos : 0 < Real.sinh 1 := Real.sinh_pos_iff.mpr (by norm_num)
    have hcosh1pos : 0 < Real.cosh 1 := Real.cosh_pos 1
    have hcs1 : Real.sinh 1 < Real.cosh 1 := by
      rw [Real.cosh_eq, Real.sinh_eq]
      have h1 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
      have h2 : (0 : ℝ) < Real.exp (-1) := Real.exp_pos (-1)
      linarith
    have hcρ : ρ < c := by nlinarith [hcsq, hcpos, hρnn, sq_nonneg ρ]
    have hApos : 0 < A := by
      rw [hAdef]
      have h1 : 0 < c * Real.cosh 1 := mul_pos hcpos hcosh1pos
      have h2 : 0 ≤ ρ * Real.sinh 1 := mul_nonneg hρnn (le_of_lt hsinh1pos)
      linarith
    have hBpos : 0 < B := by
      rw [hBdef]
      have h1 : 0 < c * Real.sinh 1 := mul_pos hcpos hsinh1pos
      have h2 : 0 ≤ ρ * Real.cosh 1 := mul_nonneg hρnn (le_of_lt hcosh1pos)
      linarith
    have hAB : B < A := by
      have h1 : A - B = (c - ρ) * (Real.cosh 1 - Real.sinh 1) := by rw [hAdef, hBdef]; ring
      have h2 : 0 < (c - ρ) * (Real.cosh 1 - Real.sinh 1) :=
        mul_pos (by linarith) (by linarith)
      linarith
    set Y : Fin 3 ⊕ Fin 1 → ℝ := A • Q + B • n with hYdef
    have hYY : mform Y Y = -1 := by
      rw [hYdef, mform_lincomb2, hQQ, hQn, hn]
      have hAB2 : A ^ 2 - B ^ 2 = 1 := by
        have h2 : (c - ρ) * (c + ρ) = 1 := by nlinarith [hcsq]
        have h3 : (Real.cosh 1 - Real.sinh 1) * (Real.cosh 1 + Real.sinh 1) = 1 := by
          nlinarith [Real.cosh_sq_sub_sinh_sq 1]
        have h4 : A - B = (c - ρ) * (Real.cosh 1 - Real.sinh 1) := by rw [hAdef, hBdef]; ring
        have h5 : A + B = (c + ρ) * (Real.cosh 1 + Real.sinh 1) := by rw [hAdef, hBdef]; ring
        calc A ^ 2 - B ^ 2 = (A - B) * (A + B) := by ring
          _ = ((c - ρ) * (c + ρ)) * ((Real.cosh 1 - Real.sinh 1) * (Real.cosh 1 + Real.sinh 1)) := by
                rw [h4, h5]; ring
          _ = 1 := by rw [h2, h3, mul_one]
      nlinarith [hAB2]
    have hYt' : 0 < htime (A • Q + B • n) := by
      have h1 : htime (A • Q + B • n) = A * htime Q + B * htime n := rfl
      rw [h1, ← hqdef, ← hwdef]
      rcases le_total 0 w with hw0 | hw0
      · nlinarith [hApos, hqpos, hBpos, hw0]
      · have hlt : -w < q := by
          rw [abs_of_nonpos hw0] at hwlt; exact hwlt
        have h2 : B * (-w) < B * q := mul_lt_mul_of_pos_left hlt hBpos
        have h3 : 0 < (A - B) * q := mul_pos (by linarith) hqpos
        nlinarith [h2, h3, hw0]
    have hYt : 0 < htime Y := hYt'
    have hYlift : hlift (hspat Y) = Y := Hyper.hlift_spat_of_mink Y hYY hYt
    have hZY : mform Z Y = -Real.cosh 1 := by
      rw [hZQn, hYdef, mform_pair2, hQQ, hQn, hn]
      rw [show mform n Q = 0 from by rw [mform_comm]; exact hQn]
      have hcA : c * A - ρ * B = Real.cosh 1 := by
        rw [hAdef, hBdef]
        nlinarith [hcsq, Real.cosh_sq_sub_sinh_sq 1]
      nlinarith [hcA]
    have hMY : emat f *ᵥ Y = A • (emat f *ᵥ Q) + (-B) • n := by
      have h1 : emat f *ᵥ (A • Q) = A • (emat f *ᵥ Q) := Matrix.mulVec_smul (emat f) A Q
      have h2 : emat f *ᵥ (B • n) = (-B) • n := by
        rw [Matrix.mulVec_smul (emat f) B n, heig, smul_neg, ← neg_smul]
      rw [hYdef, Matrix.mulVec_add, h1, h2]
    have hnMQ : mform n (emat f *ᵥ Q) = 0 := by
      have h := hmf Q n
      rw [heig, mform_neg_right, hQn] at h
      have h1 : mform (emat f *ᵥ Q) n = 0 := by linarith
      rwa [mform_comm] at h1
    have hQlift : hlift (hspat Q) = Q := Hyper.hlift_spat_of_mink Q hQQ hqpos
    have hQMQ : mform Q (emat f *ᵥ Q) ≤ -1 := by
      have h := one_le_neg_mform_hlift (hspat Q) (f • hspat Q)
      rw [hQlift] at h
      rw [← emat_hlift f (hspat Q), hQlift] at h
      linarith
    have hcosh : Real.cosh 2 ≤ -mform (hlift (hspat Y)) (hlift (f • hspat Y)) := by
      have hYM : mform Y (emat f *ᵥ Y) ≤ -(A ^ 2 + B ^ 2) := by
        have hbil : mform Y (emat f *ᵥ Y) = A ^ 2 * mform Q (emat f *ᵥ Q) - B ^ 2 := by
          rw [hMY, hYdef, mform_pair2, hQn, hnMQ, hn]
          ring
        rw [hbil]
        have h1 : A ^ 2 * mform Q (emat f *ᵥ Q) ≤ A ^ 2 * (-1) :=
          mul_le_mul_of_nonneg_left hQMQ (sq_nonneg A)
        nlinarith [h1, sq_nonneg B]
      have hAB2 : Real.cosh 2 ≤ A ^ 2 + B ^ 2 := by
        rw [hAdef, hBdef]
        have hc2 : Real.cosh 2 = Real.cosh 1 * Real.cosh 1 + Real.sinh 1 * Real.sinh 1 := by
          rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.cosh_add]
        have hs2 : Real.sinh 2 = Real.sinh 1 * Real.cosh 1 + Real.cosh 1 * Real.sinh 1 := by
          rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.sinh_add]
        have hid : (c * Real.cosh 1 + ρ * Real.sinh 1) ^ 2
              + (ρ * Real.cosh 1 + c * Real.sinh 1) ^ 2
            = (1 + 2 * ρ ^ 2) * Real.cosh 2 + 2 * c * ρ * Real.sinh 2 := by
          rw [hc2, hs2]
          nlinarith [hcsq]
        rw [hid]
        have h1 : Real.cosh 2 ≤ (1 + 2 * ρ ^ 2) * Real.cosh 2 := by
          nlinarith [Real.cosh_pos 2, sq_nonneg ρ]
        have h2 : 0 ≤ 2 * c * ρ * Real.sinh 2 := by
          have hs : 0 < Real.sinh 2 := Real.sinh_pos_iff.mpr (by norm_num)
          positivity
        linarith
      rw [hYlift, ← emat_hlift f (hspat Y), hYlift]
      linarith [hYM, hAB2]
    refine ⟨hspat Y, ?_, ?_⟩
    · rw [hdist_eq_neg_mform]
      have h1 : -mform (hlift z) (hlift (hspat Y)) = Real.cosh 1 := by
        rw [← hZdef, hYlift]
        linarith [hZY]
      rw [h1, Real.arcosh_cosh (by norm_num : (0 : ℝ) ≤ 1)]
    · rw [hdist_eq_neg_mform, ← Real.arcosh_cosh (by norm_num : (0 : ℝ) ≤ 2)]
      exact (Real.arcosh_le_arcosh (Real.cosh_pos 2)
        (by linarith [hcosh, Real.cosh_pos 2])).mpr hcosh
  by_cases hρ : 0 ≤ mform (hlift z) n
  · exact key n hn heig hρ
  · refine key (-n) ?_ ?_ ?_
    · rw [mform_neg_left, mform_neg_right, hn, neg_neg]
    · rw [Matrix.mulVec_neg, heig, neg_neg]
    · rw [mform_neg_right]
      linarith [not_le.mp hρ]


/-- A lift of `f ∈ PO(3,1)` and the "effective matrix" `emat f` have the same determinant. -/
lemma det_emat (f : PO 3 1) :
    (emat f).det = (Submission.Mostow.mat (Submission.Mostow.rep f)).det := by
  have h4 : tsign (Submission.Mostow.rep f) ^ 4 = 1 := by
    have h := tsign_sq (Submission.Mostow.rep f)
    calc tsign (Submission.Mostow.rep f) ^ 4
        = (tsign (Submission.Mostow.rep f) * tsign (Submission.Mostow.rep f))
          * (tsign (Submission.Mostow.rep f) * tsign (Submission.Mostow.rep f)) := by ring
      _ = 1 := by rw [h]; norm_num
  have hcard : Fintype.card (Fin 3 ⊕ Fin 1) = 4 := by simp [Fintype.card_sum]
  rw [emat, Matrix.det_smul, hcard, h4, one_mul]

/-- **Orientation of a near-identity isometry.**  If `f ∈ PO(3,1)` moves every point of the
closed unit ball around `z` by less than `η ≤ 1`, then `f` preserves the orientation of `ℍ³`. -/
theorem nearId_isOriented (hA : Submission.Mostow.POActionProp 3)
    (hI : Submission.Mostow.HypIsometryProp 3)
    (f : LeanEval.Geometry.MostowRigidity.PO 3 1) (z : Submission.Mostow.E 3) (η : ℝ)
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hnear : Submission.Mostow.NearIdAt f z η) :
    Work.Mostow.IsOriented f := by
  by_contra hcon
  have hJorth : (emat f)ᵀ * (pmOneMat (p := Fin 3) (q := Fin 1) (α := ℝ)) * emat f
      = (pmOneMat (p := Fin 3) (q := Fin 1) (α := ℝ)) := emat_isJOrth f
  have hdetM : (emat f).det = (mat (rep f)).det := det_emat f
  have hdet : (emat f).det = -1 := by
    rcases det_eq_pm_one hJorth with h | h
    · rw [hdetM] at h
      have hpos : (0 : ℝ) < (Submission.Mostow.mat (Submission.Mostow.rep f)).det := by
        rw [h]; norm_num
      exact absurd hpos hcon
    · exact h
  obtain ⟨v, hv, heig⟩ := negOneEigen hJorth hdet
  have hvpos : 0 < mform v v := eigVecSpacelike f v hv heig
  set c : ℝ := Real.sqrt (mform v v) with hcdef
  have hcpos : 0 < c := Real.sqrt_pos.mpr hvpos
  have hcsq : c ^ 2 = mform v v := Real.sq_sqrt (le_of_lt hvpos)
  have hn1 : mform (c⁻¹ • v) (c⁻¹ • v) = 1 := by
    rw [mform_smul, ← hcsq]
    have hcne : c ≠ 0 := ne_of_gt hcpos
    field_simp
  have heig1 : emat f *ᵥ (c⁻¹ • v) = -(c⁻¹ • v) := by
    rw [Matrix.mulVec_smul (emat f) c⁻¹ v, heig, smul_neg]
  obtain ⟨y, hy1, hy2⟩ := displacementBound f (c⁻¹ • v) hn1 heig1 z
  have hy3 : Submission.Mostow.hdist y (f • y) < η := hnear y hy1
  linarith

end

end Work.Mostow.gapA
