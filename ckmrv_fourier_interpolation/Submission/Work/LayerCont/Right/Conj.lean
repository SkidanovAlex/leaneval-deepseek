/-
# The reflection `τ ↦ -τ̄` and the mirror of the `SL(2,ℤ)`-action

The whole left-hand construction at `Re τ = 1` (in `Submission/Work/LayerCont/`) mirrors to the
right-hand construction at `Re τ = -1` through the anti-holomorphic isometry

  `negRefl τ = -conj τ`

of `ℍ`, which is the action of `UpperHalfPlane.J = !!![-1,0;0,1]` in Mathlib's `GL(2,ℝ)`-action
(`UpperHalfPlane.coe_J_smul`).  Under `negRefl`:

* the centre `1 + i s₀` goes to `-1 + i s₀` (`onePlusI` ↔ `negOnePlusI`);
* the pole `T⁻¹τ = τ - 1` goes to the pole `T τ = τ + 1` (`tauSubOne` ↔ `tauAddOne`);
* the removable coincidence `S T⁻¹ τ = -1/(τ-1)` goes to `S T τ = -1/(τ+1)`
  (`tauCoinc` ↔ `tauCoincRight`);
* the imaginary axis is fixed (`negRefl (imagAxis t ht) = imagAxis t ht`), and `negRefl` is an
  isometry (`negRefl_isometry`), so hyperbolic balls transport;
* the `SL(2,ℤ)`-action is transported to itself: `negRefl (γ • z) = mirrorElem γ • negRefl z`
  with the explicit involution `mirrorElem γ = J γ J` of `SL(2,ℤ)` (entries
  `!![γ 0 0, -γ 0 1; -γ 1 0, γ 1 1]`, the `J`-conjugate of `γ`), which exchanges `S` and
  `S⁻¹`(up to sign) and `T` with `T⁻¹`.

These are exactly the facts needed to transport the *geometry* of
`Work.LayerCont.ECS.exists_contour_left_data` (the left rectangles `[-ξ,0] × …`, the cleanliness
of the retained axis and the web classification at `1 + i s₀`) to the corresponding right data at
`-1 + i s₀` (`Submission/Work/LayerCont/Right/Geometry.lean`).
-/
import Mathlib
import Submission.Work.LayerCont.Right.Defs

open UpperHalfPlane MeasureTheory

set_option maxHeartbeats 1000000

noncomputable section

namespace Work.LayerCont.Right

open UpperHalfPlane

/-! ## The reflection -/

/-- The reflection `τ ↦ -τ̄` of the upper half plane, i.e. the action of the matrix
`!![-1,0;0,1]` in Mathlib's `GL(2,ℝ)`-action.  It is the anti-holomorphic isometry through which
the left construction at `Re τ = 1` mirrors to the right construction at `Re τ = -1`. -/
abbrev negRefl (τ : UpperHalfPlane) : UpperHalfPlane := UpperHalfPlane.J • τ

lemma negRefl_coe (τ : UpperHalfPlane) :
    ((negRefl τ : UpperHalfPlane) : ℂ) = -((starRingEnd ℂ) (τ : ℂ)) :=
  UpperHalfPlane.coe_J_smul τ

lemma negRefl_re (τ : UpperHalfPlane) : (negRefl τ).re = -τ.re := by
  have h := congrArg Complex.re (negRefl_coe τ)
  simpa using h

lemma negRefl_im (τ : UpperHalfPlane) : (negRefl τ).im = τ.im := by
  have h := congrArg Complex.im (negRefl_coe τ)
  simpa using h

lemma negRefl_involutive (τ : UpperHalfPlane) : negRefl (negRefl τ) = τ := by
  apply UpperHalfPlane.ext
  rw [negRefl_coe, negRefl_coe]
  simp

@[simp] lemma negRefl_imagAxis (t : ℝ) (ht : 0 < t) :
    negRefl (Work.Kernels.imagAxis t ht) = Work.Kernels.imagAxis t ht := by
  apply UpperHalfPlane.ext
  rw [negRefl_coe, Work.Kernels.imagAxis]
  simp

/-- `negRefl (u + i v) = -u + i v` for `v > 0` (the mirror of
`Work.Asymptotics.ofReImT`'s parametrisation). -/
lemma negRefl_ofReImT (u v : ℝ) (hv : 0 < v) :
    negRefl (Work.Asymptotics.ofReImT u v) = Work.Asymptotics.ofReImT (-u) v := by
  apply UpperHalfPlane.ext
  rw [negRefl_coe, Work.Asymptotics.ofReImT_coe u v hv, Work.Asymptotics.ofReImT_coe (-u) v hv]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  ring

@[simp] lemma negRefl_onePlusI (s₀ : ℝ) (hs₀ : 0 < s₀) :
    negRefl (Work.Asymptotics.onePlusI s₀ hs₀) = negOnePlusI s₀ hs₀ := by
  apply UpperHalfPlane.ext
  rw [negRefl_coe, Work.Asymptotics.onePlusI_coe, negOnePlusI_coe]
  simp [Complex.ext_iff]

@[simp] lemma negRefl_negOnePlusI (s₀ : ℝ) (hs₀ : 0 < s₀) :
    negRefl (negOnePlusI s₀ hs₀) = Work.Asymptotics.onePlusI s₀ hs₀ := by
  rw [← negRefl_onePlusI s₀ hs₀, negRefl_involutive]

/-! ## `negRefl` is an isometry -/

/-- **The reflection is an isometry of the hyperbolic metric.** -/
theorem negRefl_isometry (z w : UpperHalfPlane) : dist (negRefl z) (negRefl w) = dist z w := by
  have hz : (negRefl z).re = -z.re := negRefl_re z
  have hw : (negRefl w).re = -w.re := negRefl_re w
  have hzi : (negRefl z).im = z.im := negRefl_im z
  have hwi : (negRefl w).im = w.im := negRefl_im w
  have h1 := UpperHalfPlane.cosh_dist' (negRefl z) (negRefl w)
  have h2 := UpperHalfPlane.cosh_dist' z w
  rw [hz, hw, hzi, hwi] at h1
  have hcosh : Real.cosh (dist (negRefl z) (negRefl w)) = Real.cosh (dist z w) := by
    rw [h1, h2]; ring_nf
  exact Real.cosh_injOn (Set.mem_Ici.mpr dist_nonneg) (Set.mem_Ici.mpr dist_nonneg) hcosh

/-- The distance to the two mirror centres: `dist (negRefl z) (-1+is₀) = dist z (1+is₀)`. -/
lemma dist_negRefl_negOnePlusI (z : UpperHalfPlane) (s₀ : ℝ) (hs₀ : 0 < s₀) :
    dist (negRefl z) (negOnePlusI s₀ hs₀) = dist z (Work.Asymptotics.onePlusI s₀ hs₀) := by
  rw [← negRefl_onePlusI s₀ hs₀, negRefl_isometry]

/-- The distance from `-1 + i s₀` to a reflected point. -/
lemma dist_negOnePlusI_negRefl (z : UpperHalfPlane) (s₀ : ℝ) (hs₀ : 0 < s₀) :
    dist (negOnePlusI s₀ hs₀) (negRefl z) = dist (Work.Asymptotics.onePlusI s₀ hs₀) z := by
  rw [← negRefl_onePlusI s₀ hs₀, dist_comm, negRefl_isometry, dist_comm]

/-! ## The transport of the `SL(2,ℤ)`-action -/

/-- The `J`-conjugate `J γ J` of `γ ∈ SL(2,ℤ)`, i.e. the matrix
`!![γ 0 0, -γ 0 1; -γ 1 0, γ 1 1]` (again of determinant `1`). -/
def mirrorElem (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨!![γ 0 0, -(γ 0 1); -(γ 1 0), γ 1 1], by
    rw [Matrix.det_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.empty_val']
    have h := γ.2
    rw [Matrix.det_fin_two] at h
    linarith⟩

@[simp] lemma mirrorElem_zero_zero (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    (mirrorElem γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = γ 0 0 := by
  rw [mirrorElem, Matrix.SpecialLinearGroup.coe_mk]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val']

@[simp] lemma mirrorElem_zero_one (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    (mirrorElem γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = -(γ 0 1) := by
  rw [mirrorElem, Matrix.SpecialLinearGroup.coe_mk]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val']

@[simp] lemma mirrorElem_one_zero (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    (mirrorElem γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = -(γ 1 0) := by
  rw [mirrorElem, Matrix.SpecialLinearGroup.coe_mk]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val']

@[simp] lemma mirrorElem_one_one (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    (mirrorElem γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = γ 1 1 := by
  rw [mirrorElem, Matrix.SpecialLinearGroup.coe_mk]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val']

/-- At the level of the `GL(2,ℝ)`-action, `mirrorElem γ` is the `J`-conjugate of `γ`:
`mirrorElem γ * J = J * γ`. -/
lemma mirrorElem_mul_J (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ((mirrorElem γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : GL (Fin 2) ℝ)
        * UpperHalfPlane.J
      = UpperHalfPlane.J * (γ : GL (Fin 2) ℝ) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
  · simp only [Matrix.mul_apply, Finset.univ_unique, Fin.default_eq_zero, Fin.sum_univ_two,
      UpperHalfPlane.val_J, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.head_cons, Matrix.of_apply]
    simp

/-- **The reflection intertwines the `SL(2,ℤ)`-action with itself**, through `mirrorElem`. -/
theorem negRefl_smul (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane) :
    negRefl (γ • z) = mirrorElem γ • negRefl z := by
  have hL : negRefl (γ • z) = (UpperHalfPlane.J * (γ : GL (Fin 2) ℝ)) • z := by
    rw [negRefl, show γ • z = (γ : GL (Fin 2) ℝ) • z from ModularGroup.sl_moeb γ z,
      ← mul_smul]
  have hR : mirrorElem γ • negRefl z
      = (((mirrorElem γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : GL (Fin 2) ℝ)
          * UpperHalfPlane.J) • z := by
    rw [negRefl, show mirrorElem γ • (UpperHalfPlane.J • z)
        = ((mirrorElem γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : GL (Fin 2) ℝ)
            • (UpperHalfPlane.J • z) from ModularGroup.sl_moeb _ _, ← mul_smul]
  rw [hL, hR, mirrorElem_mul_J]

/-! ## The two special orbit points -/

/-- `negRefl` transports the pole `τ - 1` to the pole `τ + 1`. -/
lemma negRefl_tauSubOne_negRefl (τ : UpperHalfPlane) :
    negRefl (Work.Asymptotics.tauSubOne (negRefl τ)) = tauAddOne τ := by
  apply UpperHalfPlane.ext
  rw [negRefl_coe, Work.Asymptotics.tauSubOne_coe, negRefl_coe, tauAddOne_coe]
  simp only [map_sub, map_one, map_neg, neg_sub, Complex.conj_conj, neg_neg]
  ring

/-- `negRefl` transports the removable coincidence `ST⁻¹τ = -1/(τ-1)` to `STτ = -1/(τ+1)`. -/
lemma negRefl_tauCoinc_negRefl (τ : UpperHalfPlane) :
    negRefl (Work.Asymptotics.tauCoinc (negRefl τ)) = tauCoincRight τ := by
  apply UpperHalfPlane.ext
  rw [negRefl_coe, Work.Asymptotics.tauCoinc_coe, negRefl_coe, tauCoincRight_coe,
    map_div₀, map_neg, map_one, map_sub, map_neg, Complex.conj_conj]
  rw [map_one, show (-(↑τ) - 1 : ℂ) = -((↑τ) + 1) by ring, div_neg, neg_div, neg_neg]

end Work.LayerCont.Right
