/-
# `Work.KT.HopfK.hk_diskW_class_move`

The class of the disk-side `W`-matrix of the Hopf construction is unchanged when the data
`(χ, P, Q)` are deformed to `(χ', P ∘ shiftSnd 1, Q ∘ shiftFst 1)`.

The proof is homotopy invariance of `K₀` in the closed algebra `Kpair (Eu m × Eu m)`
(`Work.KT.homotopy_inv`): for `s ∈ [0,1]` interpolate the angle linearly,
`χ_s = (1-s)·χ + s·χ'` (still equal to `chiB m ∘ hopfKMap m μ` on the boundary of the ball),
and deform the matrices along the self-maps
`shiftSnd m e₀ s : (x,y) ↦ ((1-s)x + s·e₀, y)`, `shiftFst m e₀ s : (x,y) ↦ (x, (1-s)y + s·e₀)`.
The collar hypotheses are inherited by the deformed matrices (the collars `{‖y‖ ≥ 1-δ}` and
`{‖x‖ ≥ 1-δ}` only involve the coordinate that is left untouched), so by
`Work.KT.HopfK.hk_diskW_mem_Kpair` every value of the path is a `Kpair`-valued matrix.
-/
import Mathlib
import Submission.Work.KT.HopfK.Disk
import Submission.Work.KT.hk_relprod
import Submission.Work.KT.HopfK.hk_diskW_mem_Kpair
import Submission.Work.KT.homotopy_inv

namespace Work.KT.HopfK

open _root_.Matrix

noncomputable section

set_option maxHeartbeats 800000

/-! ## The joint self-maps of the ball -/

/-- The pair `((1-s)x + s·e₀, y)` lies in the closed unit ball whenever `(x,y)` and `e₀` do. -/
lemma hkDM_shiftSnd_pair_mem (m : ℕ) (e₀ : Sph (Eu m))
    (p : Ball (Eu m × Eu m) × unitInterval) :
    (((1 - (p.2 : ℝ)) • (p.1 : Eu m × Eu m).1 + (p.2 : ℝ) • (e₀ : Eu m),
      (p.1 : Eu m × Eu m).2) : Eu m × Eu m) ∈ Metric.closedBall (0 : Eu m × Eu m) 1 := by
  have h1 : ‖(e₀ : Eu m)‖ = 1 := by
    have h := Metric.mem_sphere.mp e₀.2
    rwa [dist_eq_norm, sub_zero] at h
  have hx : ‖(p.1 : Eu m × Eu m).1‖ ≤ 1 :=
    le_trans (le_max_left _ _) (mem_closedBall_zero_iff.mp p.1.2)
  have hy : ‖(p.1 : Eu m × Eu m).2‖ ≤ 1 :=
    le_trans (le_max_right _ _) (mem_closedBall_zero_iff.mp p.1.2)
  have hs0 : (0 : ℝ) ≤ (p.2 : ℝ) := p.2.2.1
  have hs1 : (p.2 : ℝ) ≤ 1 := p.2.2.2
  have key : ‖(1 - (p.2 : ℝ)) • (p.1 : Eu m × Eu m).1 + (p.2 : ℝ) • (e₀ : Eu m)‖ ≤ 1 := by
    calc ‖(1 - (p.2 : ℝ)) • (p.1 : Eu m × Eu m).1 + (p.2 : ℝ) • (e₀ : Eu m)‖
        ≤ ‖(1 - (p.2 : ℝ)) • (p.1 : Eu m × Eu m).1‖ + ‖(p.2 : ℝ) • (e₀ : Eu m)‖ :=
          norm_add_le _ _
      _ = (1 - (p.2 : ℝ)) * ‖(p.1 : Eu m × Eu m).1‖ + (p.2 : ℝ) * 1 := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg hs0,
            h1, mul_one]
      _ ≤ (1 - (p.2 : ℝ)) * 1 + (p.2 : ℝ) * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left hx (by linarith)) le_rfl
      _ = 1 := by ring
  refine mem_closedBall_zero_iff.mpr ?_
  rw [Prod.norm_def]
  exact max_le key (by simpa using hy)

/-- The pair `(x, (1-s)y + s·e₀)` lies in the closed unit ball. -/
lemma hkDM_shiftFst_pair_mem (m : ℕ) (e₀ : Sph (Eu m))
    (p : Ball (Eu m × Eu m) × unitInterval) :
    (((p.1 : Eu m × Eu m).1,
      (1 - (p.2 : ℝ)) • (p.1 : Eu m × Eu m).2 + (p.2 : ℝ) • (e₀ : Eu m)) : Eu m × Eu m)
      ∈ Metric.closedBall (0 : Eu m × Eu m) 1 := by
  have h1 : ‖(e₀ : Eu m)‖ = 1 := by
    have h := Metric.mem_sphere.mp e₀.2
    rwa [dist_eq_norm, sub_zero] at h
  have hx : ‖(p.1 : Eu m × Eu m).1‖ ≤ 1 :=
    le_trans (le_max_left _ _) (mem_closedBall_zero_iff.mp p.1.2)
  have hy : ‖(p.1 : Eu m × Eu m).2‖ ≤ 1 :=
    le_trans (le_max_right _ _) (mem_closedBall_zero_iff.mp p.1.2)
  have hs0 : (0 : ℝ) ≤ (p.2 : ℝ) := p.2.2.1
  have hs1 : (p.2 : ℝ) ≤ 1 := p.2.2.2
  have key : ‖(1 - (p.2 : ℝ)) • (p.1 : Eu m × Eu m).2 + (p.2 : ℝ) • (e₀ : Eu m)‖ ≤ 1 := by
    calc ‖(1 - (p.2 : ℝ)) • (p.1 : Eu m × Eu m).2 + (p.2 : ℝ) • (e₀ : Eu m)‖
        ≤ ‖(1 - (p.2 : ℝ)) • (p.1 : Eu m × Eu m).2‖ + ‖(p.2 : ℝ) • (e₀ : Eu m)‖ :=
          norm_add_le _ _
      _ = (1 - (p.2 : ℝ)) * ‖(p.1 : Eu m × Eu m).2‖ + (p.2 : ℝ) * 1 := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg hs0,
            h1, mul_one]
      _ ≤ (1 - (p.2 : ℝ)) * 1 + (p.2 : ℝ) * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left hy (by linarith)) le_rfl
      _ = 1 := by ring
  refine mem_closedBall_zero_iff.mpr ?_
  rw [Prod.norm_def]
  exact max_le (by simpa using hx) key

/-- The joint map `((x,y),s) ↦ ((1-s)x + s·e₀, y)`. -/
def hkDM_shiftSndJ (m : ℕ) (e₀ : Sph (Eu m)) :
    C(Ball (Eu m × Eu m) × unitInterval, Ball (Eu m × Eu m)) where
  toFun p := ⟨((1 - (p.2 : ℝ)) • (p.1 : Eu m × Eu m).1 + (p.2 : ℝ) • (e₀ : Eu m),
    (p.1 : Eu m × Eu m).2), hkDM_shiftSnd_pair_mem m e₀ p⟩
  continuous_toFun := Continuous.subtype_mk (by fun_prop) (hkDM_shiftSnd_pair_mem m e₀)

/-- The joint map `((x,y),s) ↦ (x, (1-s)y + s·e₀)`. -/
def hkDM_shiftFstJ (m : ℕ) (e₀ : Sph (Eu m)) :
    C(Ball (Eu m × Eu m) × unitInterval, Ball (Eu m × Eu m)) where
  toFun p := ⟨((p.1 : Eu m × Eu m).1,
    (1 - (p.2 : ℝ)) • (p.1 : Eu m × Eu m).2 + (p.2 : ℝ) • (e₀ : Eu m)),
    hkDM_shiftFst_pair_mem m e₀ p⟩
  continuous_toFun := Continuous.subtype_mk (by fun_prop) (hkDM_shiftFst_pair_mem m e₀)

@[simp] lemma hkDM_shiftSndJ_coe (m : ℕ) (e₀ : Sph (Eu m))
    (p : Ball (Eu m × Eu m) × unitInterval) :
    ((hkDM_shiftSndJ m e₀ p : Ball (Eu m × Eu m)) : Eu m × Eu m)
      = ((1 - (p.2 : ℝ)) • (p.1 : Eu m × Eu m).1 + (p.2 : ℝ) • (e₀ : Eu m),
        (p.1 : Eu m × Eu m).2) := rfl

@[simp] lemma hkDM_shiftFstJ_coe (m : ℕ) (e₀ : Sph (Eu m))
    (p : Ball (Eu m × Eu m) × unitInterval) :
    ((hkDM_shiftFstJ m e₀ p : Ball (Eu m × Eu m)) : Eu m × Eu m)
      = ((p.1 : Eu m × Eu m).1,
        (1 - (p.2 : ℝ)) • (p.1 : Eu m × Eu m).2 + (p.2 : ℝ) • (e₀ : Eu m)) := rfl

lemma hkDM_shiftSndJ_comp_slice (m : ℕ) (e₀ : Sph (Eu m)) (s : unitInterval) :
    (hkDM_shiftSndJ m e₀).comp ⟨fun z : Ball (Eu m × Eu m) => (z, s), by fun_prop⟩
      = shiftSnd m e₀ s := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  simp only [ContinuousMap.comp_apply, hkDM_shiftSndJ_coe, shiftSnd, ContinuousMap.coe_mk]

lemma hkDM_shiftFstJ_comp_slice (m : ℕ) (e₀ : Sph (Eu m)) (s : unitInterval) :
    (hkDM_shiftFstJ m e₀).comp ⟨fun z : Ball (Eu m × Eu m) => (z, s), by fun_prop⟩
      = shiftFst m e₀ s := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  simp only [ContinuousMap.comp_apply, hkDM_shiftFstJ_coe, shiftFst, ContinuousMap.coe_mk]

@[simp] lemma hkDM_shiftSnd_zero (m : ℕ) (e₀ : Sph (Eu m)) :
    shiftSnd m e₀ (0 : unitInterval) = ContinuousMap.id (Ball (Eu m × Eu m)) := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  simp only [shiftSnd, ContinuousMap.coe_mk, ContinuousMap.id_apply]
  rw [show ((0 : unitInterval) : ℝ) = 0 from rfl]
  simp

@[simp] lemma hkDM_shiftFst_zero (m : ℕ) (e₀ : Sph (Eu m)) :
    shiftFst m e₀ (0 : unitInterval) = ContinuousMap.id (Ball (Eu m × Eu m)) := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  simp only [shiftFst, ContinuousMap.coe_mk, ContinuousMap.id_apply]
  rw [show ((0 : unitInterval) : ℝ) = 0 from rfl]
  simp

/-! ## The interpolated angle -/

/-- The angle at parameter `s`: the linear interpolation of `χ` and `χ'`. -/
def hkDM_angPath (m : ℕ) (χ χ' : C(Ball (Eu m × Eu m), ℝ)) (s : unitInterval) :
    C(Ball (Eu m × Eu m), ℝ) :=
  ⟨fun z => (1 - (s : ℝ)) * χ z + (s : ℝ) * χ' z, by fun_prop⟩

/-- The joint angle `(z,s) ↦ (1-s)·χ z + s·χ' z`. -/
def hkDM_angJ (m : ℕ) (χ χ' : C(Ball (Eu m × Eu m), ℝ)) :
    C(Ball (Eu m × Eu m) × unitInterval, ℝ) :=
  ⟨fun p => (1 - (p.2 : ℝ)) * χ p.1 + (p.2 : ℝ) * χ' p.1, by fun_prop⟩

@[simp] lemma hkDM_angPath_apply (m : ℕ) (χ χ' : C(Ball (Eu m × Eu m), ℝ))
    (s : unitInterval) (z : Ball (Eu m × Eu m)) :
    hkDM_angPath m χ χ' s z = (1 - (s : ℝ)) * χ z + (s : ℝ) * χ' z := rfl

@[simp] lemma hkDM_angJ_apply (m : ℕ) (χ χ' : C(Ball (Eu m × Eu m), ℝ))
    (p : Ball (Eu m × Eu m) × unitInterval) :
    hkDM_angJ m χ χ' p = (1 - (p.2 : ℝ)) * χ p.1 + (p.2 : ℝ) * χ' p.1 := rfl

@[simp] lemma hkDM_angPath_zero (m : ℕ) (χ χ' : C(Ball (Eu m × Eu m), ℝ)) :
    hkDM_angPath m χ χ' 0 = χ := by
  apply ContinuousMap.ext
  intro z
  simp

@[simp] lemma hkDM_angPath_one (m : ℕ) (χ χ' : C(Ball (Eu m × Eu m), ℝ)) :
    hkDM_angPath m χ χ' 1 = χ' := by
  apply ContinuousMap.ext
  intro z
  simp

/-- `cos (π/2 · χ_s)` over the ball, jointly in `(z,s)`. -/
def hkDM_cosJ (m : ℕ) (χ χ' : C(Ball (Eu m × Eu m), ℝ)) :
    C(Ball (Eu m × Eu m) × unitInterval, ℂ) :=
  ⟨fun p => (Real.cos (Real.pi / 2 * hkDM_angJ m χ χ' p) : ℂ),
    Complex.continuous_ofReal.comp
      (Real.continuous_cos.comp (continuous_const.mul (hkDM_angJ m χ χ').continuous))⟩

/-- `sin (π/2 · χ_s)` over the ball, jointly in `(z,s)`. -/
def hkDM_sinJ (m : ℕ) (χ χ' : C(Ball (Eu m × Eu m), ℝ)) :
    C(Ball (Eu m × Eu m) × unitInterval, ℂ) :=
  ⟨fun p => (Real.sin (Real.pi / 2 * hkDM_angJ m χ χ' p) : ℂ),
    Complex.continuous_ofReal.comp
      (Real.continuous_sin.comp (continuous_const.mul (hkDM_angJ m χ χ').continuous))⟩

@[simp] lemma hkDM_cosJ_apply (m : ℕ) (χ χ' : C(Ball (Eu m × Eu m), ℝ))
    (p : Ball (Eu m × Eu m) × unitInterval) :
    hkDM_cosJ m χ χ' p = (Real.cos (Real.pi / 2 * hkDM_angJ m χ χ' p) : ℂ) := rfl

@[simp] lemma hkDM_sinJ_apply (m : ℕ) (χ χ' : C(Ball (Eu m × Eu m), ℝ))
    (p : Ball (Eu m × Eu m) × unitInterval) :
    hkDM_sinJ m χ χ' p = (Real.sin (Real.pi / 2 * hkDM_angJ m χ χ' p) : ℂ) := rfl

/-! ## The path of `W`-matrices over `C(Ball (Eu m × Eu m) × [0,1], ℂ)` -/

/-- The `W`-matrix at all parameters, over `C(D × [0,1], ℂ)`. -/
def hkDM_Wpath (m n r : ℕ) (e₀ : Sph (Eu m)) (χ χ' : C(Ball (Eu m × Eu m), ℝ))
    (P Q : Matrix (Fin n) (Fin n) (C(Ball (Eu m × Eu m), ℂ))) :
    Matrix (Fin ((n * n + n * n) + (n * n + n * n)))
      (Fin ((n * n + n * n) + (n * n + n * n)))
      (C(Ball (Eu m × Eu m) × unitInterval, ℂ)) :=
  diskW (P.map (pullAlg (hkDM_shiftSndJ m e₀)).toRingHom)
    (Q.map (pullAlg (hkDM_shiftFstJ m e₀)).toRingHom)
    (matConst (C(Ball (Eu m × Eu m) × unitInterval, ℂ)) (diagIdemMat r n))
    (hkDM_cosJ m χ χ') (hkDM_sinJ m χ χ')

/-- The slice at parameter `s` of the path of `W`-matrices, over `C(D, ℂ)`. -/
def hkDM_Wslice (m n r : ℕ) (e₀ : Sph (Eu m)) (χ χ' : C(Ball (Eu m × Eu m), ℝ))
    (P Q : Matrix (Fin n) (Fin n) (C(Ball (Eu m × Eu m), ℂ))) (s : unitInterval) :
    Matrix (Fin ((n * n + n * n) + (n * n + n * n)))
      (Fin ((n * n + n * n) + (n * n + n * n))) (C(Ball (Eu m × Eu m), ℂ)) :=
  (hkDM_Wpath m n r e₀ χ χ' P Q).map (sliceAt s)

/-! ## Idempotency transport -/

lemma hkDM_map_idem (m : ℕ) {n : ℕ}
    (R : C(Ball (Eu m × Eu m), ℂ) →ₐ[ℂ] C(Ball (Eu m × Eu m), ℂ))
    (P : Matrix (Fin n) (Fin n) (C(Ball (Eu m × Eu m), ℂ))) (hP : P * P = P) :
    (P.map R.toRingHom) * (P.map R.toRingHom) = P.map R.toRingHom := by
  rw [← Matrix.map_mul (f := R.toRingHom), hP]

/-! ## Slicing the `W`-matrix -/

/-- **The slice of the path is the `W`-matrix of the sliced data.** -/
lemma hkDM_Wslice_eq (m n r : ℕ) (e₀ : Sph (Eu m)) (χ χ' : C(Ball (Eu m × Eu m), ℝ))
    (P Q : Matrix (Fin n) (Fin n) (C(Ball (Eu m × Eu m), ℂ))) (s : unitInterval) :
    hkDM_Wslice m n r e₀ χ χ' P Q s
      = hopfDiskW m n r (hkDM_angPath m χ χ' s)
          (P.map (pullAlg (shiftSnd m e₀ s)).toRingHom)
          (Q.map (pullAlg (shiftFst m e₀ s)).toRingHom) := by
  apply Matrix.ext
  intro i j
  apply ContinuousMap.ext
  intro z
  -- left-hand side: slice the path at `s` and then evaluate at `z`
  have hL : hkDM_Wslice m n r e₀ χ χ' P Q s i j z
      = (diskW (P.map (pullAlg (hkDM_shiftSndJ m e₀)).toRingHom)
          (Q.map (pullAlg (hkDM_shiftFstJ m e₀)).toRingHom)
          (matConst (C(Ball (Eu m × Eu m) × unitInterval, ℂ)) (diagIdemMat r n))
          (hkDM_cosJ m χ χ') (hkDM_sinJ m χ χ')).map (evalC (z, s)) i j := by
    show ((hkDM_Wpath m n r e₀ χ χ' P Q).map (sliceAt s)) i j z
      = (diskW (P.map (pullAlg (hkDM_shiftSndJ m e₀)).toRingHom)
          (Q.map (pullAlg (hkDM_shiftFstJ m e₀)).toRingHom)
          (matConst (C(Ball (Eu m × Eu m) × unitInterval, ℂ)) (diagIdemMat r n))
          (hkDM_cosJ m χ χ') (hkDM_sinJ m χ χ')).map (evalC (z, s)) i j
    simp only [Matrix.map_apply]
    rfl
  -- right-hand side: evaluate the `W`-matrix of the sliced data at `z`
  have hR : hopfDiskW m n r (hkDM_angPath m χ χ' s)
        (P.map (pullAlg (shiftSnd m e₀ s)).toRingHom)
        (Q.map (pullAlg (shiftFst m e₀ s)).toRingHom) i j z
      = (diskW (P.map (pullAlg (shiftSnd m e₀ s)).toRingHom)
          (Q.map (pullAlg (shiftFst m e₀ s)).toRingHom)
          (matConst (C(Ball (Eu m × Eu m), ℂ)) (diagIdemMat r n))
          (diskCos (hkDM_angPath m χ χ' s)) (diskSin (hkDM_angPath m χ χ' s))).map
            (evalC z) i j := by
    rw [show hopfDiskW m n r (hkDM_angPath m χ χ' s)
          (P.map (pullAlg (shiftSnd m e₀ s)).toRingHom)
          (Q.map (pullAlg (shiftFst m e₀ s)).toRingHom)
        = diskW (P.map (pullAlg (shiftSnd m e₀ s)).toRingHom)
            (Q.map (pullAlg (shiftFst m e₀ s)).toRingHom)
            (matConst (C(Ball (Eu m × Eu m), ℂ)) (diagIdemMat r n))
            (diskCos (hkDM_angPath m χ χ' s)) (diskSin (hkDM_angPath m χ χ' s)) from rfl]
    simp only [Matrix.map_apply]
    rfl
  rw [hL, hR]
  rw [diskW_map_evalC (T := Ball (Eu m × Eu m) × unitInterval) (z, s)
    (P.map (pullAlg (hkDM_shiftSndJ m e₀)).toRingHom)
    (Q.map (pullAlg (hkDM_shiftFstJ m e₀)).toRingHom)
    (matConst (C(Ball (Eu m × Eu m) × unitInterval, ℂ)) (diagIdemMat r n))
    (hkDM_cosJ m χ χ') (hkDM_sinJ m χ χ')]
  rw [diskW_map_evalC z (P.map (pullAlg (shiftSnd m e₀ s)).toRingHom)
    (Q.map (pullAlg (shiftFst m e₀ s)).toRingHom)
    (matConst (C(Ball (Eu m × Eu m), ℂ)) (diagIdemMat r n))
    (diskCos (hkDM_angPath m χ χ' s)) (diskSin (hkDM_angPath m χ χ' s))]
  have hP' : (P.map (pullAlg (hkDM_shiftSndJ m e₀)).toRingHom).map (evalC (z, s))
      = (P.map (pullAlg (shiftSnd m e₀ s)).toRingHom).map (evalC z) := by
    apply Matrix.ext
    intro k l
    rw [Matrix.map_apply, Matrix.map_apply]
    change (P k l) (hkDM_shiftSndJ m e₀ (z, s)) = (P k l) (shiftSnd m e₀ s z)
    congr 1
  have hQ' : (Q.map (pullAlg (hkDM_shiftFstJ m e₀)).toRingHom).map (evalC (z, s))
      = (Q.map (pullAlg (shiftFst m e₀ s)).toRingHom).map (evalC z) := by
    apply Matrix.ext
    intro k l
    rw [Matrix.map_apply, Matrix.map_apply]
    change (Q k l) (hkDM_shiftFstJ m e₀ (z, s)) = (Q k l) (shiftFst m e₀ s z)
    congr 1
  have hE' : (matConst (C(Ball (Eu m × Eu m) × unitInterval, ℂ)) (diagIdemMat r n)).map
        (evalC (z, s))
      = (matConst (C(Ball (Eu m × Eu m), ℂ)) (diagIdemMat r n)).map (evalC z) := by
    apply Matrix.ext
    intro k l
    rw [Matrix.map_apply, Matrix.map_apply]
    show (evalC (z, s))
        ((algebraMap ℂ C(Ball (Eu m × Eu m) × unitInterval, ℂ)) (diagIdemMat r n k l))
      = (evalC z) ((algebraMap ℂ C(Ball (Eu m × Eu m), ℂ)) (diagIdemMat r n k l))
    rw [AlgHom.commutes (evalC (z, s)), AlgHom.commutes (evalC z)]
  have hc' : (evalC (z, s)) (hkDM_cosJ m χ χ')
      = (evalC z) (diskCos (hkDM_angPath m χ χ' s)) := rfl
  have hs' : (evalC (z, s)) (hkDM_sinJ m χ χ')
      = (evalC z) (diskSin (hkDM_angPath m χ χ' s)) := rfl
  rw [hP', hQ', hE', hc', hs']

/-- **Idempotency of the slice.** -/
lemma hkDM_Wslice_mul_self (m n r : ℕ) (e₀ : Sph (Eu m)) (χ χ' : C(Ball (Eu m × Eu m), ℝ))
    (P Q : Matrix (Fin n) (Fin n) (C(Ball (Eu m × Eu m), ℂ)))
    (hP : P * P = P) (hQ : Q * Q = Q) (s : unitInterval) :
    hkDM_Wslice m n r e₀ χ χ' P Q s * hkDM_Wslice m n r e₀ χ χ' P Q s
      = hkDM_Wslice m n r e₀ χ χ' P Q s := by
  have hE : matConst (C(Ball (Eu m × Eu m), ℂ)) (diagIdemMat r n)
        * matConst (C(Ball (Eu m × Eu m), ℂ)) (diagIdemMat r n)
      = matConst (C(Ball (Eu m × Eu m), ℂ)) (diagIdemMat r n) := by
    rw [← matConst_mul]
    exact congrArg (matConst (C(Ball (Eu m × Eu m), ℂ))) (diagIdemMat_isIdem r n)
  rw [hkDM_Wslice_eq m n r e₀ χ χ' P Q s]
  unfold hopfDiskW
  exact diskW_idem (P.map (pullAlg (shiftSnd m e₀ s)).toRingHom)
    (Q.map (pullAlg (shiftFst m e₀ s)).toRingHom)
    (matConst (C(Ball (Eu m × Eu m), ℂ)) (diagIdemMat r n))
    (hkDM_map_idem m (pullAlg (shiftSnd m e₀ s)) P hP)
    (hkDM_map_idem m (pullAlg (shiftFst m e₀ s)) Q hQ) hE
    (diskCos_sq_add_diskSin_sq (hkDM_angPath m χ χ' s))

/-- **Continuity in the parameter.** -/
lemma hkDM_Wslice_continuous (m n r : ℕ) (e₀ : Sph (Eu m)) (χ χ' : C(Ball (Eu m × Eu m), ℝ))
    (P Q : Matrix (Fin n) (Fin n) (C(Ball (Eu m × Eu m), ℂ)))
    (i j : Fin ((n * n + n * n) + (n * n + n * n))) :
    Continuous (fun s : unitInterval => hkDM_Wslice m n r e₀ χ χ' P Q s i j) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  show Continuous (fun p : unitInterval × Ball (Eu m × Eu m) =>
    hkDM_Wslice m n r e₀ χ χ' P Q p.1 i j p.2)
  simp only [hkDM_Wslice, Matrix.map_apply, sliceAt, pullAlg]
  exact ((hkDM_Wpath m n r e₀ χ χ' P Q) i j).continuous.comp
    (continuous_snd.prodMk continuous_fst)

/-! ## Inheritance of the hypotheses -/

lemma hkDM_collar_snd (m : ℕ) (e₀ : Sph (Eu m)) {n r : ℕ} (δ : ℝ) (s : unitInterval)
    (P : Matrix (Fin n) (Fin n) (C(Ball (Eu m × Eu m), ℂ)))
    (hPc : ∀ z : Ball (Eu m × Eu m), 1 - δ ≤ ‖(z : Eu m × Eu m).2‖ →
      P.map (evalC z) = diagIdemMat r n) :
    ∀ z : Ball (Eu m × Eu m), 1 - δ ≤ ‖(z : Eu m × Eu m).2‖ →
      (P.map (pullAlg (shiftSnd m e₀ s)).toRingHom).map (evalC z) = diagIdemMat r n := by
  intro z hz
  rw [Matrix.map_map]
  have hcomp : (⇑(evalC z)) ∘ ⇑(pullAlg (shiftSnd m e₀ s)).toRingHom
      = ⇑(evalC (shiftSnd m e₀ s z)) := by
    funext f
    change (f.comp (shiftSnd m e₀ s)) z = f (shiftSnd m e₀ s z)
    rfl
  rw [hcomp]
  exact hPc (shiftSnd m e₀ s z) (by simpa [shiftSnd] using hz)

lemma hkDM_collar_fst (m : ℕ) (e₀ : Sph (Eu m)) {n r : ℕ} (δ : ℝ) (s : unitInterval)
    (Q : Matrix (Fin n) (Fin n) (C(Ball (Eu m × Eu m), ℂ)))
    (hQc : ∀ z : Ball (Eu m × Eu m), 1 - δ ≤ ‖(z : Eu m × Eu m).1‖ →
      Q.map (evalC z) = diagIdemMat r n) :
    ∀ z : Ball (Eu m × Eu m), 1 - δ ≤ ‖(z : Eu m × Eu m).1‖ →
      (Q.map (pullAlg (shiftFst m e₀ s)).toRingHom).map (evalC z) = diagIdemMat r n := by
  intro z hz
  rw [Matrix.map_map]
  have hcomp : (⇑(evalC z)) ∘ ⇑(pullAlg (shiftFst m e₀ s)).toRingHom
      = ⇑(evalC (shiftFst m e₀ s z)) := by
    funext f
    change (f.comp (shiftFst m e₀ s)) z = f (shiftFst m e₀ s z)
    rfl
  rw [hcomp]
  exact hQc (shiftFst m e₀ s z) (by simpa [shiftFst] using hz)

lemma hkDM_angPath_bdry (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m)))
    {χ χ' : C(Ball (Eu m × Eu m), ℝ)}
    (hχ : ∀ (z : Ball (Eu m × Eu m)) (hz : z ∈ bdry (Eu m × Eu m)),
      χ z = chiB m (hopfKMap m μ ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩))
    (hχ' : ∀ (z : Ball (Eu m × Eu m)) (hz : z ∈ bdry (Eu m × Eu m)),
      χ' z = chiB m (hopfKMap m μ ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩))
    (s : unitInterval) :
    ∀ (z : Ball (Eu m × Eu m)) (hz : z ∈ bdry (Eu m × Eu m)),
      hkDM_angPath m χ χ' s z =
        chiB m (hopfKMap m μ ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩) := by
  intro z hz
  rw [hkDM_angPath_apply, hχ z hz, hχ' z hz]
  ring

/-! ## The `Kpair`-valued path -/

/-- All entries of the sliced `W`-matrix are `Kpair`-valued. -/
lemma hkDM_Wslice_mem (m n r : ℕ) (δ : ℝ)
    (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m))) (e₀ : Sph (Eu m))
    (χ χ' : C(Ball (Eu m × Eu m), ℝ))
    (P Q : Matrix (Fin n) (Fin n) (C(Ball (Eu m × Eu m), ℂ)))
    (hP : P * P = P) (hQ : Q * Q = Q)
    (hPc : ∀ z : Ball (Eu m × Eu m), 1 - δ ≤ ‖(z : Eu m × Eu m).2‖ →
      P.map (evalC z) = diagIdemMat r n)
    (hQc : ∀ z : Ball (Eu m × Eu m), 1 - δ ≤ ‖(z : Eu m × Eu m).1‖ →
      Q.map (evalC z) = diagIdemMat r n)
    (hχ : ∀ (z : Ball (Eu m × Eu m)) (hz : z ∈ bdry (Eu m × Eu m)),
      χ z = chiB m (hopfKMap m μ ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩))
    (hχ' : ∀ (z : Ball (Eu m × Eu m)) (hz : z ∈ bdry (Eu m × Eu m)),
      χ' z = chiB m (hopfKMap m μ ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩))
    (hδ : 1 - Real.sqrt 3 / 2 ≤ δ) (s : unitInterval)
    (i j : Fin ((n * n + n * n) + (n * n + n * n))) :
    hkDM_Wslice m n r e₀ χ χ' P Q s i j ∈ Kpair (Eu m × Eu m) := by
  have hmem := hk_diskW_mem_Kpair m μ n r δ (hkDM_angPath m χ χ' s)
    (hkDM_angPath_bdry m μ hχ hχ' s)
    (P.map (pullAlg (shiftSnd m e₀ s)).toRingHom)
    (Q.map (pullAlg (shiftFst m e₀ s)).toRingHom)
    (hkDM_map_idem m _ P hP) (hkDM_map_idem m _ Q hQ)
    (hkDM_collar_snd m e₀ δ s P hPc) (hkDM_collar_fst m e₀ δ s Q hQc) hδ i j
  rwa [← hkDM_Wslice_eq m n r e₀ χ χ' P Q s] at hmem

/-- The `Kpair`-valued `W`-matrix at parameter `s`. -/
def hkDM_Zmat (m n r : ℕ) (δ : ℝ)
    (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m))) (e₀ : Sph (Eu m))
    (χ χ' : C(Ball (Eu m × Eu m), ℝ))
    (P Q : Matrix (Fin n) (Fin n) (C(Ball (Eu m × Eu m), ℂ)))
    (hP : P * P = P) (hQ : Q * Q = Q)
    (hPc : ∀ z : Ball (Eu m × Eu m), 1 - δ ≤ ‖(z : Eu m × Eu m).2‖ →
      P.map (evalC z) = diagIdemMat r n)
    (hQc : ∀ z : Ball (Eu m × Eu m), 1 - δ ≤ ‖(z : Eu m × Eu m).1‖ →
      Q.map (evalC z) = diagIdemMat r n)
    (hχ : ∀ (z : Ball (Eu m × Eu m)) (hz : z ∈ bdry (Eu m × Eu m)),
      χ z = chiB m (hopfKMap m μ ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩))
    (hχ' : ∀ (z : Ball (Eu m × Eu m)) (hz : z ∈ bdry (Eu m × Eu m)),
      χ' z = chiB m (hopfKMap m μ ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩))
    (hδ : 1 - Real.sqrt 3 / 2 ≤ δ) (s : unitInterval) :
    Matrix (Fin ((n * n + n * n) + (n * n + n * n)))
      (Fin ((n * n + n * n) + (n * n + n * n))) (Kpair (Eu m × Eu m)) :=
  fun i j => ⟨hkDM_Wslice m n r e₀ χ χ' P Q s i j,
    hkDM_Wslice_mem m n r δ μ e₀ χ χ' P Q hP hQ hPc hQc hχ hχ' hδ s i j⟩

lemma hkDM_Zmat_val (m n r : ℕ) (δ : ℝ)
    (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m))) (e₀ : Sph (Eu m))
    (χ χ' : C(Ball (Eu m × Eu m), ℝ))
    (P Q : Matrix (Fin n) (Fin n) (C(Ball (Eu m × Eu m), ℂ)))
    (hP : P * P = P) (hQ : Q * Q = Q)
    (hPc : ∀ z : Ball (Eu m × Eu m), 1 - δ ≤ ‖(z : Eu m × Eu m).2‖ →
      P.map (evalC z) = diagIdemMat r n)
    (hQc : ∀ z : Ball (Eu m × Eu m), 1 - δ ≤ ‖(z : Eu m × Eu m).1‖ →
      Q.map (evalC z) = diagIdemMat r n)
    (hχ : ∀ (z : Ball (Eu m × Eu m)) (hz : z ∈ bdry (Eu m × Eu m)),
      χ z = chiB m (hopfKMap m μ ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩))
    (hχ' : ∀ (z : Ball (Eu m × Eu m)) (hz : z ∈ bdry (Eu m × Eu m)),
      χ' z = chiB m (hopfKMap m μ ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩))
    (hδ : 1 - Real.sqrt 3 / 2 ≤ δ) (s : unitInterval) :
    (hkDM_Zmat m n r δ μ e₀ χ χ' P Q hP hQ hPc hQc hχ hχ' hδ s).map
        (Kpair (Eu m × Eu m)).val.toRingHom
      = hkDM_Wslice m n r e₀ χ χ' P Q s := by
  apply Matrix.ext
  intro i j
  rw [Matrix.map_apply]
  rfl

lemma hkDM_Zmat_mul_self (m n r : ℕ) (δ : ℝ)
    (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m))) (e₀ : Sph (Eu m))
    (χ χ' : C(Ball (Eu m × Eu m), ℝ))
    (P Q : Matrix (Fin n) (Fin n) (C(Ball (Eu m × Eu m), ℂ)))
    (hP : P * P = P) (hQ : Q * Q = Q)
    (hPc : ∀ z : Ball (Eu m × Eu m), 1 - δ ≤ ‖(z : Eu m × Eu m).2‖ →
      P.map (evalC z) = diagIdemMat r n)
    (hQc : ∀ z : Ball (Eu m × Eu m), 1 - δ ≤ ‖(z : Eu m × Eu m).1‖ →
      Q.map (evalC z) = diagIdemMat r n)
    (hχ : ∀ (z : Ball (Eu m × Eu m)) (hz : z ∈ bdry (Eu m × Eu m)),
      χ z = chiB m (hopfKMap m μ ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩))
    (hχ' : ∀ (z : Ball (Eu m × Eu m)) (hz : z ∈ bdry (Eu m × Eu m)),
      χ' z = chiB m (hopfKMap m μ ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩))
    (hδ : 1 - Real.sqrt 3 / 2 ≤ δ) (s : unitInterval) :
    hkDM_Zmat m n r δ μ e₀ χ χ' P Q hP hQ hPc hQc hχ hχ' hδ s
        * hkDM_Zmat m n r δ μ e₀ χ χ' P Q hP hQ hPc hQc hχ hχ' hδ s
      = hkDM_Zmat m n r δ μ e₀ χ χ' P Q hP hQ hPc hQc hχ hχ' hδ s := by
  have h1 : (hkDM_Zmat m n r δ μ e₀ χ χ' P Q hP hQ hPc hQc hχ hχ' hδ s
        * hkDM_Zmat m n r δ μ e₀ χ χ' P Q hP hQ hPc hQc hχ hχ' hδ s).map
          (Kpair (Eu m × Eu m)).val.toRingHom
      = hkDM_Wslice m n r e₀ χ χ' P Q s := by
    rw [Matrix.map_mul (f := (Kpair (Eu m × Eu m)).val.toRingHom)]
    rw [hkDM_Zmat_val m n r δ μ e₀ χ χ' P Q hP hQ hPc hQc hχ hχ' hδ s]
    exact hkDM_Wslice_mul_self m n r e₀ χ χ' P Q hP hQ s
  have h2 := hkDM_Zmat_val m n r δ μ e₀ χ χ' P Q hP hQ hPc hQc hχ hχ' hδ s
  apply Matrix.ext
  intro i j
  apply Subtype.ext
  have h := congrFun (congrFun (h1.trans h2.symm) i) j
  rw [Matrix.map_apply, Matrix.map_apply] at h
  exact h

lemma hkDM_Zmat_continuous (m n r : ℕ) (δ : ℝ)
    (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m))) (e₀ : Sph (Eu m))
    (χ χ' : C(Ball (Eu m × Eu m), ℝ))
    (P Q : Matrix (Fin n) (Fin n) (C(Ball (Eu m × Eu m), ℂ)))
    (hP : P * P = P) (hQ : Q * Q = Q)
    (hPc : ∀ z : Ball (Eu m × Eu m), 1 - δ ≤ ‖(z : Eu m × Eu m).2‖ →
      P.map (evalC z) = diagIdemMat r n)
    (hQc : ∀ z : Ball (Eu m × Eu m), 1 - δ ≤ ‖(z : Eu m × Eu m).1‖ →
      Q.map (evalC z) = diagIdemMat r n)
    (hχ : ∀ (z : Ball (Eu m × Eu m)) (hz : z ∈ bdry (Eu m × Eu m)),
      χ z = chiB m (hopfKMap m μ ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩))
    (hχ' : ∀ (z : Ball (Eu m × Eu m)) (hz : z ∈ bdry (Eu m × Eu m)),
      χ' z = chiB m (hopfKMap m μ ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩))
    (hδ : 1 - Real.sqrt 3 / 2 ≤ δ) :
    Continuous (hkDM_Zmat m n r δ μ e₀ χ χ' P Q hP hQ hPc hQc hχ hχ' hδ) := by
  apply continuous_matrix
  intro i j
  show Continuous (fun s : unitInterval =>
    (⟨hkDM_Wslice m n r e₀ χ χ' P Q s i j,
      hkDM_Wslice_mem m n r δ μ e₀ χ χ' P Q hP hQ hPc hQc hχ hχ' hδ s i j⟩ :
      Kpair (Eu m × Eu m)))
  exact Continuous.subtype_mk
    (hkDM_Wslice_continuous m n r e₀ χ χ' P Q i j)
    (fun s => hkDM_Wslice_mem m n r δ μ e₀ χ χ' P Q hP hQ hPc hQc hχ hχ' hδ s i j)

/-! ## The endpoints of the path -/

lemma hkDM_pullAlg_id (m : ℕ) {n : ℕ}
    (P : Matrix (Fin n) (Fin n) (C(Ball (Eu m × Eu m), ℂ))) :
    P.map (pullAlg (ContinuousMap.id (Ball (Eu m × Eu m)))).toRingHom = P := by
  apply Matrix.ext
  intro i j
  rw [Matrix.map_apply]
  change (P i j).comp (ContinuousMap.id (Ball (Eu m × Eu m))) = P i j
  rw [ContinuousMap.comp_id]

lemma hkDM_Zmat_zero (m n r : ℕ) (δ : ℝ)
    (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m))) (e₀ : Sph (Eu m))
    (χ χ' : C(Ball (Eu m × Eu m), ℝ))
    (P Q : Matrix (Fin n) (Fin n) (C(Ball (Eu m × Eu m), ℂ)))
    (hP : P * P = P) (hQ : Q * Q = Q)
    (hPc : ∀ z : Ball (Eu m × Eu m), 1 - δ ≤ ‖(z : Eu m × Eu m).2‖ →
      P.map (evalC z) = diagIdemMat r n)
    (hQc : ∀ z : Ball (Eu m × Eu m), 1 - δ ≤ ‖(z : Eu m × Eu m).1‖ →
      Q.map (evalC z) = diagIdemMat r n)
    (hχ : ∀ (z : Ball (Eu m × Eu m)) (hz : z ∈ bdry (Eu m × Eu m)),
      χ z = chiB m (hopfKMap m μ ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩))
    (hχ' : ∀ (z : Ball (Eu m × Eu m)) (hz : z ∈ bdry (Eu m × Eu m)),
      χ' z = chiB m (hopfKMap m μ ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩))
    (hδ : 1 - Real.sqrt 3 / 2 ≤ δ)
    (H : ∀ i j : Fin ((n * n + n * n) + (n * n + n * n)),
      hopfDiskW m n r χ P Q i j ∈ Kpair (Eu m × Eu m)) :
    (⟨(n * n + n * n) + (n * n + n * n),
        hkDM_Zmat m n r δ μ e₀ χ χ' P Q hP hQ hPc hQc hχ hχ' hδ 0⟩ :
      Mat (Kpair (Eu m × Eu m)))
      = hopfDiskZ m n r χ P Q H := by
  refine Sigma.ext rfl ?_
  refine heq_of_eq ?_
  apply Matrix.ext
  intro i j
  apply Subtype.ext
  show hkDM_Wslice m n r e₀ χ χ' P Q 0 i j = hopfDiskW m n r χ P Q i j
  rw [hkDM_Wslice_eq m n r e₀ χ χ' P Q 0]
  simp only [hkDM_angPath_zero, hkDM_shiftSnd_zero, hkDM_shiftFst_zero, hkDM_pullAlg_id]

lemma hkDM_Zmat_one (m n r : ℕ) (δ : ℝ)
    (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m))) (e₀ : Sph (Eu m))
    (χ χ' : C(Ball (Eu m × Eu m), ℝ))
    (P Q : Matrix (Fin n) (Fin n) (C(Ball (Eu m × Eu m), ℂ)))
    (hP : P * P = P) (hQ : Q * Q = Q)
    (hPc : ∀ z : Ball (Eu m × Eu m), 1 - δ ≤ ‖(z : Eu m × Eu m).2‖ →
      P.map (evalC z) = diagIdemMat r n)
    (hQc : ∀ z : Ball (Eu m × Eu m), 1 - δ ≤ ‖(z : Eu m × Eu m).1‖ →
      Q.map (evalC z) = diagIdemMat r n)
    (hχ : ∀ (z : Ball (Eu m × Eu m)) (hz : z ∈ bdry (Eu m × Eu m)),
      χ z = chiB m (hopfKMap m μ ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩))
    (hχ' : ∀ (z : Ball (Eu m × Eu m)) (hz : z ∈ bdry (Eu m × Eu m)),
      χ' z = chiB m (hopfKMap m μ ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩))
    (hδ : 1 - Real.sqrt 3 / 2 ≤ δ)
    (Hd : ∀ i j : Fin ((n * n + n * n) + (n * n + n * n)),
      hopfDiskW m n r χ' (P.map (pullAlg (shiftSnd m e₀ 1)).toRingHom)
        (Q.map (pullAlg (shiftFst m e₀ 1)).toRingHom) i j ∈ Kpair (Eu m × Eu m)) :
    (⟨(n * n + n * n) + (n * n + n * n),
        hkDM_Zmat m n r δ μ e₀ χ χ' P Q hP hQ hPc hQc hχ hχ' hδ 1⟩ :
      Mat (Kpair (Eu m × Eu m)))
      = hopfDiskZ m n r χ' (P.map (pullAlg (shiftSnd m e₀ 1)).toRingHom)
          (Q.map (pullAlg (shiftFst m e₀ 1)).toRingHom) Hd := by
  refine Sigma.ext rfl ?_
  refine heq_of_eq ?_
  apply Matrix.ext
  intro i j
  apply Subtype.ext
  show hkDM_Wslice m n r e₀ χ χ' P Q 1 i j
    = hopfDiskW m n r χ' (P.map (pullAlg (shiftSnd m e₀ 1)).toRingHom)
        (Q.map (pullAlg (shiftFst m e₀ 1)).toRingHom) i j
  rw [hkDM_Wslice_eq m n r e₀ χ χ' P Q 1]
  simp only [hkDM_angPath_one]

/-! ## Closedness of `Kpair` -/

lemma hkDM_isClosed_Kpair (m : ℕ) :
    IsClosed ((Kpair (Eu m × Eu m) : Subalgebra ℂ C(Ball (Eu m × Eu m), ℂ)) :
      Set C(Ball (Eu m × Eu m), ℂ)) := by
  have hset : ((Kpair (Eu m × Eu m) : Subalgebra ℂ C(Ball (Eu m × Eu m), ℂ)) :
        Set C(Ball (Eu m × Eu m), ℂ)) =
      ⋂ (y : Ball (Eu m × Eu m)) (_ : y ∈ bdry (Eu m × Eu m))
        (y' : Ball (Eu m × Eu m)) (_ : y' ∈ bdry (Eu m × Eu m)),
        {g : C(Ball (Eu m × Eu m), ℂ) | g y = g y'} := by
    ext g
    simp [Kpair, constOn, Set.mem_iInter]
  rw [hset]
  refine isClosed_iInter fun y => isClosed_iInter fun hy => isClosed_iInter fun y' =>
    isClosed_iInter fun hy' => isClosed_eq ?_ ?_
  · fun_prop
  · fun_prop

/-! ## The main theorem -/

theorem hk_diskW_class_move (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m)))
    (n r : ℕ) (δ : ℝ) (hδ : 1 - Real.sqrt 3 / 2 ≤ δ) (e₀ : Sph (Eu m))
    (P Q : Matrix (Fin n) (Fin n) (C(Ball (Eu m × Eu m), ℂ)))
    (hP : P * P = P) (hQ : Q * Q = Q)
    (hPc : ∀ z : Ball (Eu m × Eu m), 1 - δ ≤ ‖(z : Eu m × Eu m).2‖ →
      P.map (evalC z) = diagIdemMat r n)
    (hQc : ∀ z : Ball (Eu m × Eu m), 1 - δ ≤ ‖(z : Eu m × Eu m).1‖ →
      Q.map (evalC z) = diagIdemMat r n)
    (χ χ' : C(Ball (Eu m × Eu m), ℝ))
    (hχ : ∀ (z : Ball (Eu m × Eu m)) (hz : z ∈ bdry (Eu m × Eu m)),
      χ z = chiB m (hopfKMap m μ ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩))
    (hχ' : ∀ (z : Ball (Eu m × Eu m)) (hz : z ∈ bdry (Eu m × Eu m)),
      χ' z = chiB m (hopfKMap m μ ⟨(z : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hz⟩))
    (H : ∀ i j : Fin ((n * n + n * n) + (n * n + n * n)),
      hopfDiskW m n r χ P Q i j ∈ Kpair (Eu m × Eu m))
    (Hd : ∀ i j : Fin ((n * n + n * n) + (n * n + n * n)),
      hopfDiskW m n r χ' (P.map (pullAlg (shiftSnd m e₀ 1)).toRingHom)
        (Q.map (pullAlg (shiftFst m e₀ 1)).toRingHom) i j ∈ Kpair (Eu m × Eu m)) :
    cls (hopfDiskZ m n r χ P Q H)
      = cls (hopfDiskZ m n r χ' (P.map (pullAlg (shiftSnd m e₀ 1)).toRingHom)
          (Q.map (pullAlg (shiftFst m e₀ 1)).toRingHom) Hd) := by
  have hhom := homotopy_inv (C(Ball (Eu m × Eu m), ℂ)) (Kpair (Eu m × Eu m))
    (hkDM_isClosed_Kpair m) _
    (hkDM_Zmat m n r δ μ e₀ χ χ' P Q hP hQ hPc hQc hχ hχ' hδ)
    (hkDM_Zmat_continuous m n r δ μ e₀ χ χ' P Q hP hQ hPc hQc hχ hχ' hδ)
    (fun s => hkDM_Zmat_mul_self m n r δ μ e₀ χ χ' P Q hP hQ hPc hQc hχ hχ' hδ s)
  have e0 := hkDM_Zmat_zero m n r δ μ e₀ χ χ' P Q hP hQ hPc hQc hχ hχ' hδ H
  have e1 := hkDM_Zmat_one m n r δ μ e₀ χ χ' P Q hP hQ hPc hQc hχ hχ' hδ Hd
  rw [← e0, ← e1]
  exact hhom

end

end Work.KT.HopfK
