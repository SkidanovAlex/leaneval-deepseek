import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Rat.Star
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Submission.NK.GlobalCFTdeep.Herbrand.DescentSetup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFTdeep.Herbrand.Descent

open Matrix TensorProduct
open scoped TensorProduct

/-! ## Auxiliary definitions and lemmas for the descent argument -/

section Aux

variable {d k : ℕ}

/-- Monotonicity of `Matrix.of` under addition. -/
private lemma of_add (Y Z : Fin d → Fin d → ℚ) : Matrix.of (Y + Z) = Matrix.of Y + Matrix.of Z := by
  ext a b; simp [Matrix.of_apply]

/-- Compatibility of `Matrix.of` with scalar multiplication. -/
private lemma of_smul (r : ℚ) (Y : Fin d → Fin d → ℚ) : Matrix.of (r • Y) = r • Matrix.of Y := by
  ext a b; simp [Matrix.of_apply]

/-- Compatibility of `Matrix.of` with addition over `ℝ`. -/
private lemma of_addR (Y Z : Fin d → Fin d → ℝ) : Matrix.of (Y + Z) = Matrix.of Y + Matrix.of Z := by
  ext a b; simp [Matrix.of_apply]

/-- Compatibility of `Matrix.of` with scalar multiplication over `ℝ`. -/
private lemma of_smulR (r : ℝ) (Y : Fin d → Fin d → ℝ) : Matrix.of (r • Y) = r • Matrix.of Y := by
  ext a b; simp [Matrix.of_apply]

/-- The rational linear system `Q i * Y = Y * P i`, as a linear map. -/
private noncomputable def Ho (P Q : Fin k → Matrix (Fin d) (Fin d) ℚ) :
    (Fin d → Fin d → ℚ) →ₗ[ℚ] (Fin k → Fin d → Fin d → ℚ) where
  toFun Y := fun i a b => (Q i * Matrix.of Y - Matrix.of Y * P i) a b
  map_add' Y Z := by
    ext i a b
    simp only [Pi.add_apply]
    rw [of_add, Matrix.mul_add, Matrix.add_mul]
    simp only [Matrix.add_apply, Matrix.sub_apply]
    ring
  map_smul' r Y := by
    ext i a b
    simp only [Pi.smul_apply]
    rw [of_smul, Matrix.mul_smul, Matrix.smul_mul]
    simp only [Matrix.smul_apply, Matrix.sub_apply, RingHom.id_apply]
    ring

/-- Explicit formula for `Ho`. -/
private lemma Ho_apply (P Q : Fin k → Matrix (Fin d) (Fin d) ℚ) (Y : Fin d → Fin d → ℚ) :
    Ho P Q Y = fun i a b => (Q i * Matrix.of Y - Matrix.of Y * P i) a b := rfl

/-- The real linear system obtained from the rational one by base change. -/
private noncomputable def HoR (P Q : Fin k → Matrix (Fin d) (Fin d) ℚ) :
    (Fin d → Fin d → ℝ) →ₗ[ℝ] (Fin k → Fin d → Fin d → ℝ) where
  toFun Y := fun i a b =>
    ((Q i).map (algebraMap ℚ ℝ) * Matrix.of Y - Matrix.of Y * (P i).map (algebraMap ℚ ℝ)) a b
  map_add' Y Z := by
    ext i a b
    simp only [Pi.add_apply]
    rw [of_addR, Matrix.mul_add, Matrix.add_mul]
    simp only [Matrix.add_apply, Matrix.sub_apply]
    ring
  map_smul' r Y := by
    ext i a b
    simp only [Pi.smul_apply]
    rw [of_smulR, Matrix.mul_smul, Matrix.smul_mul]
    simp only [Matrix.smul_apply, Matrix.sub_apply, RingHom.id_apply]
    ring

/-- Explicit formula for `HoR`. -/
private lemma HoR_apply (P Q : Fin k → Matrix (Fin d) (Fin d) ℚ) (Y : Fin d → Fin d → ℝ) :
    HoR P Q Y = fun i a b =>
      ((Q i).map (algebraMap ℚ ℝ) * Matrix.of Y - Matrix.of Y * (P i).map (algebraMap ℚ ℝ)) a b :=
  rfl

/-- The kernel of `Ho` consists of the solutions of the rational system. -/
private lemma Ho_mem_ker (P Q : Fin k → Matrix (Fin d) (Fin d) ℚ) (Y : Fin d → Fin d → ℚ) :
    Y ∈ LinearMap.ker (Ho P Q) ↔ ∀ i, Q i * Matrix.of Y = Matrix.of Y * P i := by
  rw [LinearMap.mem_ker, Ho_apply]
  constructor
  · intro h i
    ext a b
    have h1 : (Q i * Matrix.of Y - Matrix.of Y * P i) a b = 0 := by
      simpa using congrFun (congrFun (congrFun h i) a) b
    exact sub_eq_zero.mp h1
  · intro h
    funext i a b
    rw [h i]
    simp

/-- The identification `ℝ ⊗[ℚ] (Fin d → Fin d → ℚ) ≃ₗ[ℝ] (Fin d → Fin d → ℝ)`
with `eM (r ⊗ Y) = r • Y.map (algebraMap ℚ ℝ)`. -/
private noncomputable def eM (d : ℕ) :
    ℝ ⊗[ℚ] (Fin d → Fin d → ℚ) ≃ₗ[ℝ] (Fin d → Fin d → ℝ) :=
  (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin d => (Fin d → ℚ))).trans
    (LinearEquiv.piCongrRight fun _ : Fin d => TensorProduct.piScalarRight ℚ ℝ ℝ (Fin d))

/-- Action of `eM` on pure tensors. -/
private lemma eM_tmul (r : ℝ) (Y : Fin d → Fin d → ℚ) :
    eM d (r ⊗ₜ[ℚ] Y) = fun a b => r * algebraMap ℚ ℝ (Y a b) := by
  unfold eM
  rw [LinearEquiv.trans_apply]
  ext a b
  rw [LinearEquiv.piCongrRight_apply]
  rw [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
  rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  simp [Algebra.smul_def, mul_comm]

/-- The same identification on `Fin k`-indexed families. -/
private noncomputable def eW (d k : ℕ) :
    ℝ ⊗[ℚ] (Fin k → Fin d → Fin d → ℚ) ≃ₗ[ℝ] (Fin k → Fin d → Fin d → ℝ) :=
  (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin k => (Fin d → Fin d → ℚ))).trans
    (LinearEquiv.piCongrRight fun _ : Fin k => eM d)

/-- Action of `eW` on pure tensors. -/
private lemma eW_tmul (r : ℝ) (Y : Fin k → Fin d → Fin d → ℚ) :
    eW d k (r ⊗ₜ[ℚ] Y) = fun i a b => r * algebraMap ℚ ℝ (Y i a b) := by
  unfold eW
  rw [LinearEquiv.trans_apply]
  ext i a b
  rw [LinearEquiv.piCongrRight_apply]
  rw [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
  simp only [eM_tmul]

/-- The map `Matrix.map` turns `A * Y - Y * B` into the corresponding expression over `ℝ`. -/
private lemma map_mul_sub (f : ℚ →+* ℝ) (A Y B : Matrix (Fin d) (Fin d) ℚ) :
    (A * Y - Y * B).map f = A.map f * Y.map f - Y.map f * B.map f := by
  rw [← RingHom.mapMatrix_apply (f := f)]
  rw [map_sub, map_mul, map_mul]
  simp only [RingHom.mapMatrix_apply]

/-- Scalar-multiplication version of `map_mul_sub`. -/
private lemma smul_map_mul_sub (f : ℚ →+* ℝ) (r : ℝ) (A Y B : Matrix (Fin d) (Fin d) ℚ) :
    r • ((A * Y - Y * B).map f) = A.map f * (r • Y.map f) - (r • Y.map f) * B.map f := by
  rw [map_mul_sub, smul_sub, Matrix.mul_smul, Matrix.smul_mul]

/-- **Base change of the system.**  Under the identifications `eM`, `eW`, the base change of the
rational linear system is the real one. -/
private lemma eW_baseChange (P Q : Fin k → Matrix (Fin d) (Fin d) ℚ)
    (z : ℝ ⊗[ℚ] (Fin d → Fin d → ℚ)) :
    eW d k ((Ho P Q).baseChange ℝ z) = (HoR P Q) (eM d z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r Y =>
      rw [LinearMap.baseChange_tmul, eW_tmul, eM_tmul]
      funext i a b
      rw [HoR_apply, Ho_apply]
      simp only
      have hM : Matrix.of (fun a b => r * algebraMap ℚ ℝ (Y a b))
          = r • (Matrix.of Y).map (algebraMap ℚ ℝ) := by
        ext a b; simp [Matrix.of_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
      have hL : (r • ((Q i * Matrix.of Y - Matrix.of Y * P i).map (algebraMap ℚ ℝ))) a b
          = r * algebraMap ℚ ℝ ((Q i * Matrix.of Y - Matrix.of Y * P i) a b) := by
        simp [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
      rw [← hL, smul_map_mul_sub (algebraMap ℚ ℝ) r (Q i) (Matrix.of Y) (P i), hM]
  | add x y hx hy => simp [map_add, hx, hy]

/-- The canonical map `Y ↦ 1 ⊗ Y`. -/
private noncomputable def mkOne (d : ℕ) :
    (Fin d → Fin d → ℚ) →ₗ[ℚ] (ℝ ⊗[ℚ] (Fin d → Fin d → ℚ)) :=
  TensorProduct.mk ℚ ℝ (Fin d → Fin d → ℚ) 1

/-- Action of `eM` on `mkOne Y`. -/
private lemma eM_mkOne (Y : Fin d → Fin d → ℚ) :
    eM d (mkOne d Y) = fun a b => algebraMap ℚ ℝ (Y a b) := by
  have h := eM_tmul (1 : ℝ) Y
  simpa [mkOne, one_mul] using h

/-- Evaluation at a rational point of the determinant polynomial. -/
private lemma polyAm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Yf : ι → Fin d → Fin d → ℚ) (c : ι → ℚ) :
    (Matrix.of (fun a b => ∑ i, MvPolynomial.C (Yf i a b) * MvPolynomial.X i)).map
        (MvPolynomial.eval c)
      = ∑ i, c i • Matrix.of (Yf i) := by
  ext a b
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [map_sum]
  simp only [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- Evaluation at a real point of the determinant polynomial. -/
private lemma polyBm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Yf : ι → Fin d → Fin d → ℚ) (c : ι → ℝ) :
    (Matrix.of (fun a b => ∑ i, MvPolynomial.C (Yf i a b) * MvPolynomial.X i)).map
        (MvPolynomial.eval₂ (algebraMap ℚ ℝ) c)
      = ∑ i, c i • (Matrix.of (Yf i)).map (algebraMap ℚ ℝ) := by
  ext a b
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [MvPolynomial.eval₂_sum]
  simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end Aux

/-- **Milne, *CFT*, Lemma 3.2 (matrix form).**  Let `P i, Q i` be matrices over `ℚ` (`i : Fin k`),
giving the rational homogeneous linear system `Q i * X = X * P i` in the unknown `X`.  If the
system has an invertible solution over `ℝ`, then it has an invertible solution over `ℚ`.

This is the "descent from `ℝ` to `ℚ`" which turns the comparison of two `G`-stable full lattices
in the same real representation into a comparison of `ℚ[G]`-modules (Milne's Proposition 3.1).

## Proof sketch (all ingredients are in Mathlib)

Let `Ho : Matrix (Fin d) (Fin d) ℚ →ₗ[ℚ] (Fin k → Matrix (Fin d) (Fin d) ℚ)` be
`Y ↦ fun i => Q i * Y - Y * P i` (built from `mulLeftLinearMap`/`mulRightLinearMap`), so that the
rational solutions are `ker Ho`, and let `Y j` (`j : Fin m`) be a finite spanning family of
`ker Ho` (e.g. obtained from a basis).

1. By `NK.GlobalCFTdeep.ker_baseChange_eq` and `Submodule.baseChange_eq_span`, a real solution is
   a real linear combination of the `(1 : ℝ) ⊗ₜ[ℚ] Y j`.
2. The identification `e : ℝ ⊗[ℚ] (Fin d → Fin d → ℚ) ≃ₗ[ℝ] (Fin d → Fin d → ℝ)` obtained from
   `TensorProduct.piRight` followed by `TensorProduct.piScalarRight` satisfies
   `e (1 ⊗ₜ Y) = Y.map (algebraMap ℚ ℝ)` (prove by `ext`/`simp`).  Hence the real solution `X`
   equals `∑ j, λ j • (Y j).map (algebraMap ℚ ℝ)` for suitable `λ : Fin m → ℝ`.
3. Define `Z : Matrix (Fin d) (Fin d) (MvPolynomial (Fin m) ℚ) := ∑ j, MvPolynomial.X j • (Y j).map MvPolynomial.C`
   and `Ppoly := Z.det`.  By `RingHom.map_det` applied to the ring hom `MvPolynomial.eval c`
   one has `MvPolynomial.eval c Ppoly = (∑ j, c j • Y j).det` for every `c : Fin m → ℚ`, and
   likewise `MvPolynomial.eval λ (Ppoly.map (algebraMap ℚ ℝ)) = (∑ j, λ j • (Y j).map (algebraMap ℚ ℝ)).det = X.det ≠ 0`.
4. So `Ppoly.map (algebraMap ℚ ℝ) ≠ 0`, hence `Ppoly ≠ 0`.  If all rational solutions were
   singular, `MvPolynomial.eval c Ppoly = 0` for every `c : Fin m → ℚ`, so `Ppoly = 0` by
   `MvPolynomial.funext` (valid since `ℚ` is infinite), a contradiction.  Hence some rational
   combination `∑ j, c j • Y j` is an invertible rational solution.

(The `k = 0` and `d = 0` cases are degenerate and are handled by the same argument.) -/
theorem exists_det_ne_zero_of_map_solution {d k : ℕ} (P Q : Fin k → Matrix (Fin d) (Fin d) ℚ)
    (X : Matrix (Fin d) (Fin d) ℝ)
    (hX : ∀ i, (Q i).map (algebraMap ℚ ℝ) * X = X * (P i).map (algebraMap ℚ ℝ))
    (hdet : X.det ≠ 0) :
    ∃ Y : Matrix (Fin d) (Fin d) ℚ, (∀ i, Q i * Y = Y * P i) ∧ Y.det ≠ 0 := by
  set XR : Fin d → Fin d → ℝ := fun a b => X a b with hXR
  have hXRof : Matrix.of XR = X := by
    rw [hXR]; ext a b; simp [Matrix.of_apply]
  have hXR0 : HoR P Q XR = 0 := by
    funext i a b
    rw [HoR_apply]
    simp only [hXRof, hX i]
    simp
  set z : ℝ ⊗[ℚ] (Fin d → Fin d → ℚ) := (eM d).symm XR with hz
  have hez : eM d z = XR := by rw [hz]; exact (eM d).apply_symm_apply XR
  have hbase : (Ho P Q).baseChange ℝ z = 0 := by
    have h := eW_baseChange P Q z
    rw [hez, hXR0] at h
    exact (eW d k).injective h
  have hzbc : z ∈ (LinearMap.ker (Ho P Q)).baseChange ℝ := by
    rw [NK.GlobalCFTdeep.ker_baseChange_eq (Ho P Q)]
    exact LinearMap.mem_ker.mpr hbase
  have hzspan : z ∈ Submodule.span ℝ (↑(Submodule.map (mkOne d) (LinearMap.ker (Ho P Q)))) := by
    rw [show (mkOne d : (Fin d → Fin d → ℚ) →ₗ[ℚ] (ℝ ⊗[ℚ] (Fin d → Fin d → ℚ)))
        = TensorProduct.mk ℚ ℝ (Fin d → Fin d → ℚ) 1 from rfl]
    rw [← Submodule.baseChange_eq_span ℝ (LinearMap.ker (Ho P Q))]
    exact hzbc
  obtain ⟨t, ht, c, hc⟩ := (Submodule.mem_span_image_iff_exists_fun ℝ
    (v := ⇑(mkOne d)) (s := ↑(LinearMap.ker (Ho P Q))) (x := z)).mp hzspan
  let Yf : ↑t → Fin d → Fin d → ℚ := fun i => (↑i : Fin d → Fin d → ℚ)
  have hXsum : XR = ∑ i : ↑t, c i • (fun a b => algebraMap ℚ ℝ (Yf i a b)) := by
    rw [← hez, ← hc]
    simp only [map_sum, map_smul, eM_mkOne, Yf]
  set Yℓ : Matrix (Fin d) (Fin d) ℝ :=
    ∑ i : ↑t, c i • (Matrix.of (Yf i)).map (algebraMap ℚ ℝ) with hYℓ
  have hXmat : Yℓ = X := by
    rw [hYℓ, ← hXRof, hXsum]
    ext a b
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  set Z : Matrix (Fin d) (Fin d) (MvPolynomial ↑t ℚ) :=
    Matrix.of (fun a b => ∑ i : ↑t, MvPolynomial.C (Yf i a b) * MvPolynomial.X i) with hZdef
  have hPne : Z.det ≠ 0 := by
    intro h
    have h1 : MvPolynomial.eval₂ (algebraMap ℚ ℝ) c Z.det = X.det := by
      have hd := RingHom.map_det (MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) c) Z
      rw [RingHom.mapMatrix_apply] at hd
      rw [show Z.map ⇑(MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) c)
          = Z.map (MvPolynomial.eval₂ (algebraMap ℚ ℝ) c) from rfl] at hd
      rw [hZdef, polyBm Yf c, ← hYℓ, hXmat, ← hZdef] at hd
      exact hd
    rw [h] at h1
    simp at h1
    exact hdet h1.symm
  have hex : ∃ c' : ↑t → ℚ, (∑ i : ↑t, c' i • Matrix.of (Yf i)).det ≠ 0 := by
    by_contra hcon
    refine hPne (MvPolynomial.funext fun c' => ?_)
    have hd := RingHom.map_det (MvPolynomial.eval c') Z
    rw [RingHom.mapMatrix_apply, hZdef, polyAm Yf c', ← hZdef] at hd
    have h0 : (∑ i : ↑t, c' i • Matrix.of (Yf i)).det = 0 := by
      by_contra hne
      exact hcon ⟨c', hne⟩
    rw [hd, h0]
    simp
  obtain ⟨c', hc'⟩ := hex
  refine ⟨∑ i : ↑t, c' i • Matrix.of (Yf i), ?_, hc'⟩
  intro i
  have hA : ∀ j : ↑t, Q i * Matrix.of (Yf j) = Matrix.of (Yf j) * P i := fun j =>
    (Ho_mem_ker P Q (Yf j)).mp (ht j.2) i
  rw [Matrix.mul_sum, Matrix.sum_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  exact Finset.sum_congr rfl fun j _ => by rw [hA j]

end NK.GlobalCFTdeep.Herbrand.Descent
