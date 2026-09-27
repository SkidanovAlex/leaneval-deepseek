/-
# The disk side of the relative product: the `W`-construction over the cell algebra

Definitions for the disk side of the relative product computation (`Work.KT.hk_relprod`),
abstracted so that they can be used over the cell algebra alone.

For a commutative ring `R`, idempotents `P Q E` of size `n` and `c s : R` with `c * c + s * s = 1`:

* `diskQ1 P Q E = P ⊗ Q ⊕ E ⊗ E` and `diskQ2 P Q E = P ⊗ E ⊕ E ⊗ Q` (size `n*n + n*n`),
* `diskC P Q E c s = U Q₂ U⁻¹` with `U = rotMat c s`,
* `diskW P Q E c s = W (Q₁ ⊕ (1 - C)) W` with `W = Wblk C`,

and `diskW_class` computes the `K₀`-class: `[diskW] = [Q₁] - [Q₂] + [diagMat]`.

For the Hopf construction `f = hopfKMap m μ` we then define the *specific* angle

`diskAng m z = clamp (1/2 + √(1 - ‖z.1‖²) - √(1 - ‖z.2‖²))`,

a function of `(‖x‖, ‖y‖)` only (so it lies in `prodAlg`), which on the boundary
`bdry (Eu m × Eu m)` agrees with `chiB m ∘ f`.  `hopfDiskW` is the `W`-matrix over the cell
algebra `C(Ball (Eu m × Eu m), ℂ)` built from `P`, `Q`, the angle `χ` and the constant
`diag(1_r, 0)`.
-/
import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic
import Submission.Work.KT.HopfK.Basic
import Submission.Work.KT.hk_relprod

namespace Work.KT

open _root_.Matrix

noncomputable section

/-! ## The general `W`-construction over a commutative ring -/

section General

variable {R : Type} [CommRing R]

/-- `Q₁ = P ⊗ Q ⊕ E ⊗ E`, as a block matrix of size `n*n + n*n`. -/
def diskQ1 {n : ℕ} (P Q E : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (n * n + n * n)) (Fin (n * n + n * n)) R :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (kronMat P Q) 0 0 (kronMat E E))

/-- `Q₂ = P ⊗ E ⊕ E ⊗ Q`, as a block matrix of size `n*n + n*n`. -/
def diskQ2 {n : ℕ} (P Q E : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (n * n + n * n)) (Fin (n * n + n * n)) R :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (kronMat P E) 0 0 (kronMat E Q))

/-- `C = U Q₂ U⁻¹`, the rotated `Q₂`. -/
def diskC {n : ℕ} (P Q E : Matrix (Fin n) (Fin n) R) (c s : R) :
    Matrix (Fin (n * n + n * n)) (Fin (n * n + n * n)) R :=
  rotMat (n * n) c s * diskQ2 P Q E * rotMatInv (n * n) c s

/-- The `W`-construction matrix `W (Q₁ ⊕ (1 - C)) W` over a commutative ring. -/
def diskW {n : ℕ} (P Q E : Matrix (Fin n) (Fin n) R) (c s : R) :
    Matrix (Fin ((n * n + n * n) + (n * n + n * n)))
      (Fin ((n * n + n * n) + (n * n + n * n))) R :=
  Wblk (n * n + n * n) (diskC P Q E c s) *
    Dblk (n * n + n * n) (diskQ1 P Q E) (diskC P Q E c s) *
    Wblk (n * n + n * n) (diskC P Q E c s)

/-- `Q₁` is idempotent (over a commutative ring). -/
lemma diskQ1_idem {n : ℕ} (P Q E : Matrix (Fin n) (Fin n) R)
    (hP : P * P = P) (hQ : Q * Q = Q) (hE : E * E = E) :
    Mat.IsIdem (⟨n * n + n * n, diskQ1 P Q E⟩ : Mat R) :=
  Mat.sum_idem
    (Mat.kron_idem (fun x y => mul_comm x y) (p := (⟨n, P⟩ : Mat R))
      (q := (⟨n, Q⟩ : Mat R)) hP hQ)
    (Mat.kron_idem (fun x y => mul_comm x y) (p := (⟨n, E⟩ : Mat R))
      (q := (⟨n, E⟩ : Mat R)) hE hE)

/-- `Q₂` is idempotent (over a commutative ring). -/
lemma diskQ2_idem {n : ℕ} (P Q E : Matrix (Fin n) (Fin n) R)
    (hP : P * P = P) (hQ : Q * Q = Q) (hE : E * E = E) :
    Mat.IsIdem (⟨n * n + n * n, diskQ2 P Q E⟩ : Mat R) :=
  Mat.sum_idem
    (Mat.kron_idem (fun x y => mul_comm x y) (p := (⟨n, P⟩ : Mat R))
      (q := (⟨n, E⟩ : Mat R)) hP hE)
    (Mat.kron_idem (fun x y => mul_comm x y) (p := (⟨n, E⟩ : Mat R))
      (q := (⟨n, Q⟩ : Mat R)) hE hQ)

/-- `C = U Q₂ U⁻¹` is idempotent when `c * c + s * s = 1` and `Q₂` is. -/
lemma diskC_idem {n : ℕ} (P Q E : Matrix (Fin n) (Fin n) R)
    (hP : P * P = P) (hQ : Q * Q = Q) (hE : E * E = E) {c s : R}
    (hcs : c * c + s * s = 1) :
    diskC P Q E c s * diskC P Q E c s = diskC P Q E c s := by
  have h2 : diskQ2 P Q E * diskQ2 P Q E = diskQ2 P Q E := diskQ2_idem P Q E hP hQ hE
  have h1 : rotMatInv (n * n) c s * rotMat (n * n) c s = 1 :=
    rotMatInv_mul_rotMat (m := n * n) c s hcs
  simp only [diskC]
  rw [show (rotMat (n * n) c s * diskQ2 P Q E * rotMatInv (n * n) c s)
        * (rotMat (n * n) c s * diskQ2 P Q E * rotMatInv (n * n) c s)
      = rotMat (n * n) c s * (diskQ2 P Q E * (rotMatInv (n * n) c s * rotMat (n * n) c s)
          * diskQ2 P Q E) * rotMatInv (n * n) c s from by noncomm_ring]
  rw [h1, Matrix.mul_one, h2]

/-- `diskW` is idempotent. -/
lemma diskW_idem {n : ℕ} (P Q E : Matrix (Fin n) (Fin n) R)
    (hP : P * P = P) (hQ : Q * Q = Q) (hE : E * E = E) {c s : R}
    (hcs : c * c + s * s = 1) :
    diskW P Q E c s * diskW P Q E c s = diskW P Q E c s := by
  have hC := diskC_idem P Q E hP hQ hE hcs
  have hW : Wblk (n * n + n * n) (diskC P Q E c s)
      * Wblk (n * n + n * n) (diskC P Q E c s) = 1 := Wblk_mul_self hC
  have hD : Dblk (n * n + n * n) (diskQ1 P Q E) (diskC P Q E c s)
      * Dblk (n * n + n * n) (diskQ1 P Q E) (diskC P Q E c s)
      = Dblk (n * n + n * n) (diskQ1 P Q E) (diskC P Q E c s) :=
    Mat.sum_idem (p := (⟨n * n + n * n, diskQ1 P Q E⟩ : Mat R))
      (q := (⟨n * n + n * n, 1 - diskC P Q E c s⟩ : Mat R))
      (diskQ1_idem P Q E hP hQ hE)
      (Mat.isIdem_one_sub (p := (⟨n * n + n * n, diskC P Q E c s⟩ : Mat R)) hC)
  simp only [diskW]
  rw [show (Wblk (n * n + n * n) (diskC P Q E c s)
      * Dblk (n * n + n * n) (diskQ1 P Q E) (diskC P Q E c s)
      * Wblk (n * n + n * n) (diskC P Q E c s))
      * (Wblk (n * n + n * n) (diskC P Q E c s)
      * Dblk (n * n + n * n) (diskQ1 P Q E) (diskC P Q E c s)
      * Wblk (n * n + n * n) (diskC P Q E c s))
      = Wblk (n * n + n * n) (diskC P Q E c s)
        * (Dblk (n * n + n * n) (diskQ1 P Q E) (diskC P Q E c s)
          * (Wblk (n * n + n * n) (diskC P Q E c s)
            * Wblk (n * n + n * n) (diskC P Q E c s))
          * Dblk (n * n + n * n) (diskQ1 P Q E) (diskC P Q E c s))
        * Wblk (n * n + n * n) (diskC P Q E c s) from by noncomm_ring,
    hW, Matrix.mul_one, hD]

/-- **The class identity of the `W`-construction.**  The class of `diskW P Q E c s` is
`[Q₁] - [Q₂] + [diag(1_{n*n}, 0)]`. -/
theorem diskW_class {n : ℕ} (P Q E : Matrix (Fin n) (Fin n) R)
    (hP : P * P = P) (hQ : Q * Q = Q) (hE : E * E = E) {c s : R}
    (hcs : c * c + s * s = 1) :
    cls (⟨(n * n + n * n) + (n * n + n * n), diskW P Q E c s⟩ : Mat R) =
      cls (⟨n * n + n * n, diskQ1 P Q E⟩ : Mat R)
        - cls (⟨n * n + n * n, diskQ2 P Q E⟩ : Mat R)
        + cls (diagMat R (n * n + n * n) ((n * n + n * n) + (n * n + n * n))) := by
  have hC := diskC_idem P Q E hP hQ hE hcs
  have hQ1 := diskQ1_idem P Q E hP hQ hE
  have hQ2 := diskQ2_idem P Q E hP hQ hE
  have hCY : cls (⟨n * n + n * n, diskC P Q E c s⟩ : Mat R)
      = cls (⟨n * n + n * n, diskQ2 P Q E⟩ : Mat R) := by
    refine homInv_cls_eq_of_conj (p := diskC P Q E c s) (q := diskQ2 P Q E) hC hQ2
      ⟨rotMat (n * n) c s, rotMatInv (n * n) c s,
        rotMat_mul_rotMatInv (m := n * n) c s hcs,
        rotMatInv_mul_rotMat (m := n * n) c s hcs⟩ ?_
    show rotMat (n * n) c s * diskQ2 P Q E
      = rotMat (n * n) c s * diskQ2 P Q E * rotMatInv (n * n) c s * rotMat (n * n) c s
    rw [Matrix.mul_assoc, Matrix.mul_assoc, rotMatInv_mul_rotMat (m := n * n) c s hcs,
      Matrix.mul_one]
  exact hkW_class (R := R) (fun x y => mul_comm x y) (diskQ1 P Q E) (diskQ2 P Q E)
    (diskC P Q E c s) hQ1 hC hCY

end General

/-! ## The angle, and the `W`-matrix over the cell algebra -/

/-- The angle on the ball: `clamp (1/2 + √(1 - ‖x‖²) - √(1 - ‖y‖²))`. -/
def diskAng (m : ℕ) : C(Ball (Eu m × Eu m), ℝ) :=
  ⟨fun z => min 1 (max 0 ((1 : ℝ) / 2 + Real.sqrt (1 - ‖(z : Eu m × Eu m).1‖ ^ 2)
      - Real.sqrt (1 - ‖(z : Eu m × Eu m).2‖ ^ 2))), by fun_prop⟩

@[simp] lemma diskAng_apply (m : ℕ) (z : Ball (Eu m × Eu m)) :
    diskAng m z = min 1 (max 0 ((1 : ℝ) / 2 + Real.sqrt (1 - ‖(z : Eu m × Eu m).1‖ ^ 2)
      - Real.sqrt (1 - ‖(z : Eu m × Eu m).2‖ ^ 2))) := rfl

/-- `cos (π/2 · χ)` as a complex-valued function on the ball. -/
def diskCos {m : ℕ} (χ : C(Ball (Eu m × Eu m), ℝ)) : C(Ball (Eu m × Eu m), ℂ) :=
  ⟨fun z => (Real.cos (Real.pi / 2 * χ z) : ℂ),
    Complex.continuous_ofReal.comp
      (Real.continuous_cos.comp (continuous_const.mul χ.continuous))⟩

/-- `sin (π/2 · χ)`. -/
def diskSin {m : ℕ} (χ : C(Ball (Eu m × Eu m), ℝ)) : C(Ball (Eu m × Eu m), ℂ) :=
  ⟨fun z => (Real.sin (Real.pi / 2 * χ z) : ℂ),
    Complex.continuous_ofReal.comp
      (Real.continuous_sin.comp (continuous_const.mul χ.continuous))⟩

lemma diskCos_sq_add_diskSin_sq {m : ℕ} (χ : C(Ball (Eu m × Eu m), ℝ)) :
    diskCos χ * diskCos χ + diskSin χ * diskSin χ = 1 := by
  ext z
  have h := Real.cos_sq_add_sin_sq (Real.pi / 2 * χ z)
  rw [pow_two, pow_two] at h
  show (Real.cos (Real.pi / 2 * χ z) : ℂ) * (Real.cos (Real.pi / 2 * χ z) : ℂ)
      + (Real.sin (Real.pi / 2 * χ z) : ℂ) * (Real.sin (Real.pi / 2 * χ z) : ℂ) = 1
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add, h, Complex.ofReal_one]

/-- The `W`-matrix over the cell algebra, with angle `χ` and trivial idempotent `diag(1_r,0)`. -/
def hopfDiskW (m n r : ℕ) (χ : C(Ball (Eu m × Eu m), ℝ))
    (P Q : Matrix (Fin n) (Fin n) (C(Ball (Eu m × Eu m), ℂ))) :
    Matrix (Fin ((n * n + n * n) + (n * n + n * n)))
      (Fin ((n * n + n * n) + (n * n + n * n))) (C(Ball (Eu m × Eu m), ℂ)) :=
  diskW P Q (matConst (C(Ball (Eu m × Eu m), ℂ)) (diagIdemMat r n))
    (diskCos χ) (diskSin χ)

/-- The point `(e₀, y)` of the ball `Ball (Eu m × Eu m)`. -/
def ptSnd (m : ℕ) (e₀ : Sph (Eu m)) (y : Ball (Eu m)) : Ball (Eu m × Eu m) :=
  ⟨((e₀ : Eu m), (y : Eu m)), by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Prod.norm_def]
    have h1 : ‖(e₀ : Eu m)‖ = 1 := by
      have h := Metric.mem_sphere.mp e₀.2
      rwa [dist_eq_norm, sub_zero] at h
    rw [h1, max_eq_left (mem_closedBall_zero_iff.mp y.2)]⟩

/-- The point `(x, e₀)` of the ball `Ball (Eu m × Eu m)`. -/
def ptFst (m : ℕ) (e₀ : Sph (Eu m)) (x : Ball (Eu m)) : Ball (Eu m × Eu m) :=
  ⟨((x : Eu m), (e₀ : Eu m)), by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Prod.norm_def]
    have h1 : ‖(e₀ : Eu m)‖ = 1 := by
      have h := Metric.mem_sphere.mp e₀.2
      rwa [dist_eq_norm, sub_zero] at h
    rw [h1, max_eq_right (mem_closedBall_zero_iff.mp x.2)]⟩

/-- The self-map `(x, y) ↦ ((1-s)x + s·e₀, y)` of the ball. -/
def shiftSnd (m : ℕ) (e₀ : Sph (Eu m)) (s : unitInterval) :
    C(Ball (Eu m × Eu m), Ball (Eu m × Eu m)) where
  toFun z := ⟨(((1 - (s : ℝ)) • (z : Eu m × Eu m).1 + (s : ℝ) • (e₀ : Eu m)),
      (z : Eu m × Eu m).2), by
    have h1 : ‖(e₀ : Eu m)‖ = 1 := by
      have h := Metric.mem_sphere.mp e₀.2
      rwa [dist_eq_norm, sub_zero] at h
    have hx : ‖(z : Eu m × Eu m).1‖ ≤ 1 :=
      le_trans (le_max_left _ _) (mem_closedBall_zero_iff.mp z.2)
    have hy : ‖(z : Eu m × Eu m).2‖ ≤ 1 :=
      le_trans (le_max_right _ _) (mem_closedBall_zero_iff.mp z.2)
    have hs0 : (0 : ℝ) ≤ (s : ℝ) := s.2.1
    have hs1 : (s : ℝ) ≤ 1 := s.2.2
    have key : ‖(1 - (s : ℝ)) • (z : Eu m × Eu m).1 + (s : ℝ) • (e₀ : Eu m)‖ ≤ 1 := by
      calc ‖(1 - (s : ℝ)) • (z : Eu m × Eu m).1 + (s : ℝ) • (e₀ : Eu m)‖
          ≤ ‖(1 - (s : ℝ)) • (z : Eu m × Eu m).1‖ + ‖(s : ℝ) • (e₀ : Eu m)‖ := norm_add_le _ _
        _ = (1 - (s : ℝ)) * ‖(z : Eu m × Eu m).1‖ + (s : ℝ) * 1 := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg hs0,
              h1, mul_one]
        _ ≤ (1 - (s : ℝ)) * 1 + (s : ℝ) * 1 :=
            add_le_add (mul_le_mul_of_nonneg_left hx (by linarith)) le_rfl
        _ = 1 := by ring
    refine mem_closedBall_zero_iff.mpr ?_
    rw [Prod.norm_def]
    exact max_le key (by simpa using hy)⟩
  continuous_toFun := by fun_prop

/-- The self-map `(x, y) ↦ (x, (1-s)y + s·e₀)` of the ball. -/
def shiftFst (m : ℕ) (e₀ : Sph (Eu m)) (s : unitInterval) :
    C(Ball (Eu m × Eu m), Ball (Eu m × Eu m)) where
  toFun z := ⟨((z : Eu m × Eu m).1,
      ((1 - (s : ℝ)) • (z : Eu m × Eu m).2 + (s : ℝ) • (e₀ : Eu m))), by
    have h1 : ‖(e₀ : Eu m)‖ = 1 := by
      have h := Metric.mem_sphere.mp e₀.2
      rwa [dist_eq_norm, sub_zero] at h
    have hx : ‖(z : Eu m × Eu m).1‖ ≤ 1 :=
      le_trans (le_max_left _ _) (mem_closedBall_zero_iff.mp z.2)
    have hy : ‖(z : Eu m × Eu m).2‖ ≤ 1 :=
      le_trans (le_max_right _ _) (mem_closedBall_zero_iff.mp z.2)
    have hs0 : (0 : ℝ) ≤ (s : ℝ) := s.2.1
    have hs1 : (s : ℝ) ≤ 1 := s.2.2
    have key : ‖(1 - (s : ℝ)) • (z : Eu m × Eu m).2 + (s : ℝ) • (e₀ : Eu m)‖ ≤ 1 := by
      calc ‖(1 - (s : ℝ)) • (z : Eu m × Eu m).2 + (s : ℝ) • (e₀ : Eu m)‖
          ≤ ‖(1 - (s : ℝ)) • (z : Eu m × Eu m).2‖ + ‖(s : ℝ) • (e₀ : Eu m)‖ := norm_add_le _ _
        _ = (1 - (s : ℝ)) * ‖(z : Eu m × Eu m).2‖ + (s : ℝ) * 1 := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg hs0,
              h1, mul_one]
        _ ≤ (1 - (s : ℝ)) * 1 + (s : ℝ) * 1 :=
            add_le_add (mul_le_mul_of_nonneg_left hy (by linarith)) le_rfl
        _ = 1 := by ring
    refine mem_closedBall_zero_iff.mpr ?_
    rw [Prod.norm_def]
    exact max_le (by simpa using hx) key⟩
  continuous_toFun := by fun_prop

/-- `y ↦ ptSnd m e₀ y` is continuous. -/
lemma continuous_ptSnd (m : ℕ) (e₀ : Sph (Eu m)) : Continuous (ptSnd m e₀) :=
  Continuous.subtype_mk (continuous_const.prodMk continuous_subtype_val)
    (fun y => (ptSnd m e₀ y).2)

/-- `x ↦ ptFst m e₀ x` is continuous. -/
lemma continuous_ptFst (m : ℕ) (e₀ : Sph (Eu m)) : Continuous (ptFst m e₀) :=
  Continuous.subtype_mk (continuous_subtype_val.prodMk continuous_const)
    (fun x => (ptFst m e₀ x).2)

/-- The `Kpair`-valued `W`-matrix, from a proof that the entries of `hopfDiskW` lie in
`Kpair (Eu m × Eu m)`. -/
def hopfDiskZ (m n r : ℕ) (χ : C(Ball (Eu m × Eu m), ℝ))
    (P Q : Matrix (Fin n) (Fin n) (C(Ball (Eu m × Eu m), ℂ)))
    (H : ∀ i j : Fin ((n * n + n * n) + (n * n + n * n)),
      hopfDiskW m n r χ P Q i j ∈ Kpair (Eu m × Eu m)) :
    Mat (Kpair (Eu m × Eu m)) :=
  ⟨(n * n + n * n) + (n * n + n * n),
    fun i j => ⟨hopfDiskW m n r χ P Q i j, H i j⟩⟩

/-- The slice matrix `y ↦ P (e₀, y)`, as a matrix over `Kpair (Eu m)`. -/
def sliceSnd (m n : ℕ) (e₀ : Sph (Eu m))
    (P : Matrix (Fin n) (Fin n) (C(Ball (Eu m × Eu m), ℂ)))
    (h : ∀ i j : Fin n,
      (⟨fun y => P i j (ptSnd m e₀ y),
        (P i j).continuous.comp (continuous_ptSnd m e₀)⟩ : C(Ball (Eu m), ℂ))
        ∈ Kpair (Eu m)) :
    Matrix (Fin n) (Fin n) (Kpair (Eu m)) :=
  fun i j => ⟨⟨fun y => P i j (ptSnd m e₀ y),
    (P i j).continuous.comp (continuous_ptSnd m e₀)⟩, h i j⟩

/-- The slice matrix `x ↦ Q (x, e₀)`, as a matrix over `Kpair (Eu m)`. -/
def sliceFst (m n : ℕ) (e₀ : Sph (Eu m))
    (Q : Matrix (Fin n) (Fin n) (C(Ball (Eu m × Eu m), ℂ)))
    (h : ∀ i j : Fin n,
      (⟨fun x => Q i j (ptFst m e₀ x),
        (Q i j).continuous.comp (continuous_ptFst m e₀)⟩ : C(Ball (Eu m), ℂ))
        ∈ Kpair (Eu m)) :
    Matrix (Fin n) (Fin n) (Kpair (Eu m)) :=
  fun i j => ⟨⟨fun x => Q i j (ptFst m e₀ x),
    (Q i j).continuous.comp (continuous_ptFst m e₀)⟩, h i j⟩

end

end Work.KT
