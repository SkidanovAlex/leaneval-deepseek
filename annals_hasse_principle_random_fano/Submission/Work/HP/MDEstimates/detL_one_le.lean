import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Lat.detL_basis_gram

/-!
# `1 ≤ detL L` for every integral lattice `L ⊆ ℤ^ι`

For a `ℤ`-basis `b` of `L`, `detL L = √(det G)` where `G` is the Gram matrix of the real
vectors underlying `b` (`Submission.Work.HP.Lat.detL_basis_gram`).  Since `b` is a basis, those
real vectors are linearly independent, so `G = C * Cᵀ` for the coordinate matrix `C` is positive
definite, and `G.det > 0`.  Moreover `G` is the image under `ℤ → ℝ` of the *integer* Gram matrix
`Gz`, so `G.det = (Gz.det : ℝ)` is the cast of a positive integer, hence `G.det ≥ 1`.  Therefore
`detL L = √(G.det) ≥ 1` (with `detL ⊥ = √1 = 1` in the rank-zero case).
-/

set_option autoImplicit false

namespace Work.HP.MDEstimates

open Work

/-- The Gram matrix (over `ℝ`) of any `ℝ`-linearly independent family of vectors is positive
definite. -/
private lemma gram_posDef {κ ι : Type*} [Fintype κ] [Fintype ι] (w : κ → ι → ℝ)
    (hw : LinearIndependent ℝ w) :
    (Matrix.of fun i j : κ => ∑ x, w i x * w j x).PosDef := by
  let C : Matrix κ ι ℝ := Matrix.of w
  have hCw : C = w := rfl
  have hinj : Function.Injective C.vecMul := by
    rw [Matrix.vecMul_injective_iff]
    rw [hCw]
    exact hw
  have h := Matrix.PosDef.mul_conjTranspose_self C hinj
  convert h using 1
  ext i j
  simp [C, Matrix.mul_apply]

theorem detL_one_le {ι : Type*} [Fintype ι] (L : Submodule ℤ (ι → ℤ)) :
    1 ≤ Work.HP.detL L := by
  classical
  obtain ⟨n, b⟩ := Submodule.basisOfPid (Pi.basisFun ℤ ι) L
  rw [Work.HP.Lat.detL_basis_gram L b]
  set w : Fin n → ι → ℝ := fun i x => ((b i : ι → ℤ) x : ℝ) with hw
  have hlin : LinearIndependent ℝ w := by
    have hb : LinearIndependent ℤ (fun i : Fin n => (b i : ι → ℤ)) :=
      b.linearIndependent.map' L.subtype (Submodule.ker_subtype L)
    have := (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℝ)
      (v := fun i : Fin n => (b i : ι → ℤ))).mpr hb
    simpa [w, Pi.algebraMap, Function.comp_def] using this
  have hpd : (Matrix.of fun i j : Fin n => ∑ x, w i x * w j x).PosDef := gram_posDef w hlin
  -- the integer Gram matrix of `b`
  set Gz : Matrix (Fin n) (Fin n) ℤ :=
    Matrix.of fun i j => ∑ x, (b i : ι → ℤ) x * (b j : ι → ℤ) x with hGz
  have hGr_eq : (Matrix.of fun i j : Fin n => ∑ x, w i x * w j x)
      = Gz.map (Int.castRingHom ℝ) := by
    ext i j
    simp [Gz, w, Matrix.map_apply, Int.cast_sum, Int.cast_mul]
  have hdet : (Matrix.of fun i j : Fin n => ∑ x, w i x * w j x).det = (Gz.det : ℝ) := by
    rw [hGr_eq]
    have := RingHom.map_det (Int.castRingHom ℝ) Gz
    simpa using this.symm
  have hpos : 0 < (Matrix.of fun i j : Fin n => ∑ x, w i x * w j x).det := hpd.det_pos
  have hposz : 0 < Gz.det := by
    rw [hdet] at hpos
    exact_mod_cast hpos
  have h1z : (1 : ℤ) ≤ Gz.det := by omega
  have h1r : (1 : ℝ) ≤ (Matrix.of fun i j : Fin n => ∑ x, w i x * w j x).det := by
    rw [hdet]
    exact_mod_cast h1z
  exact Real.one_le_sqrt.mpr h1r

end Work.HP.MDEstimates
