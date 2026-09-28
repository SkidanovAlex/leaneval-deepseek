import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.HPgram

/-!
# Monotonicity of the Gram determinant (covolume) under inclusions

If `L ≤ M` are sublattices of `ℤ^ι` with `ℤ`-bases `b`, `c` indexed by the *same* type `Fin k`,
then the inclusion `L ↪ M` is injective between free `ℤ`-modules of equal rank `k`, so the covolume
of `L` in its real span is the index `[M : L] ≥ 1` times that of `M`:

`(gramMat k L b).det = [M : L]^2 * (gramMat k M c).det ≥ (gramMat k M c).det`.

The transition matrix `Mtx i j` (the `i`-th coordinate of `b j` in the basis `c`) satisfies
`gramMat k L b = Mtxᵀ * gramMat k M c * Mtx`, and `Mtx.det ≠ 0` because the coordinate map
`v ↦ Mtx *ᵥ v` is (the matrix of) the injective composite `ℤ^k ≅ L ↪ M ≅ ℤ^k`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MvPolynomial Finset

namespace Work.HP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Monotonicity of the covolume.** If `L ≤ M` are sublattices of `ℤ^ι` with `ℤ`-bases `b`, `c`
indexed by the *same* type `Fin k`, then the Gram determinant of `c` (the squared covolume of `M`)
is at most that of `b` (the squared covolume of `L`). -/
theorem gramMat_det_le_of_le {k : ℕ} {L M : Submodule ℤ (ι → ℤ)}
    (b : Module.Basis (Fin k) ℤ L) (c : Module.Basis (Fin k) ℤ M) (hLM : L ≤ M) :
    (gramMat k M c).det ≤ (gramMat k L b).det := by
  classical
  -- the inclusion as a map into `M`, and the coordinate-change matrix `Mtx`
  set v : Fin k → M := fun j => ⟨(b j : ι → ℤ), hLM (b j).2⟩ with hv
  set Mtx : Matrix (Fin k) (Fin k) ℤ := c.toMatrix v with hMtx
  set MtxR : Matrix (Fin k) (Fin k) ℝ := (Int.castRingHom ℝ).mapMatrix Mtx with hMtxR
  have hMtx_apply : ∀ i j, Mtx i j = (c.repr (v j)) i := by
    intro i j; rw [hMtx]; exact Module.Basis.toMatrix_apply c v i j
  have hvj : ∀ j, v j = ∑ i, (Mtx i j) • c i := by
    intro j
    have h := Module.Basis.sum_repr c (v j)
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hMtx_apply i j]
  have hspec_val : ∀ j, (∑ i, (Mtx i j) • (c i : ι → ℤ)) = (b j : ι → ℤ) := by
    intro j
    have h := congrArg (fun z : M => (z : ι → ℤ)) (hvj j)
    simpa [hv] using h.symm
  -- the pointwise coordinates of `b j` in the basis `c`, as real numbers
  have hpt : ∀ j x, ((b j : ι → ℤ) x : ℝ) = ∑ i, MtxR i j * ((c i : ι → ℤ) x : ℝ) := by
    intro j x
    have h := congrFun (hspec_val j) x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [← h]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hMtxR, RingHom.mapMatrix_apply]
    rfl
  -- the coordinate map `v ↦ Mtx *ᵥ v` is the composite `ℤ^k ≅ L ↪ M ≅ ℤ^k`, hence injective
  have heq : ∀ w : Fin k → ℤ, Mtx.mulVec w = c.equivFun (∑ j, w j • v j) := by
    intro w
    have h1 : ∀ j, c.equivFun (v j) = fun i => Mtx i j := by
      intro j
      ext i
      rw [Module.Basis.equivFun_apply, hMtx_apply i j]
    rw [map_sum]
    simp only [map_smul, h1]
    ext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hinj : Function.Injective (Mtx.mulVec) := by
    intro w w' h
    rw [heq w, heq w'] at h
    have h2 : (∑ j, w j • v j : M) = ∑ j, w' j • v j := c.equivFun.injective h
    have h3 : (∑ j, w j • b j : L) = ∑ j, w' j • b j := by
      have h2' := congrArg (fun z : M => (z : ι → ℤ)) h2
      simp only [Submodule.coe_sum, Submodule.coe_smul, hv] at h2'
      exact Subtype.ext (by simpa using h2')
    have h4 : (∑ j, (w j - w' j) • b j : L) = 0 := by
      have h5 : (∑ j, (w j - w' j) • b j : L) = (∑ j, w j • b j) - (∑ j, w' j • b j) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => sub_smul _ _ _
      rw [h5, h3, sub_self]
    have h6 := Fintype.linearIndependent_iff.mp b.linearIndependent (fun j => w j - w' j) h4
    funext j
    exact sub_eq_zero.mp (h6 j)
  have hMtx_ne : Mtx.det ≠ 0 := by
    intro h0
    have hinj2 : Function.Injective (Matrix.toLin' Mtx) := by
      intro x y hxy
      exact hinj (by simpa [Matrix.toLin'_apply] using hxy)
    have hker : (Matrix.toLin' Mtx).ker ≠ ⊥ := by
      rw [← LinearMap.det_eq_zero_iff_ker_ne_bot, LinearMap.det_toLin']
      exact h0
    rw [LinearMap.ker_eq_bot.mpr hinj2] at hker
    exact hker rfl
  -- the Gram matrix relation and the determinant identity
  have hcoord : coordMat k L b = MtxR.transpose * coordMat k M c := by
    ext j x
    rw [Matrix.mul_apply]
    exact hpt j x
  have hgram : gramMat k L b = MtxR.transpose * gramMat k M c * MtxR := by
    rw [gramMat_eq_mul_transpose, gramMat_eq_mul_transpose, hcoord]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
  have hRdet : MtxR.det = (((Mtx.det : ℤ)) : ℝ) := by
    rw [hMtxR, ← RingHom.map_det]
    rfl
  have hdet : (gramMat k L b).det = (((Mtx.det : ℤ) : ℝ)) ^ 2 * (gramMat k M c).det := by
    rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hRdet]
    ring
  have hnonneg : 0 ≤ (gramMat k M c).det := gramMat_det_nonneg k M c
  have hsq : (1 : ℝ) ≤ (((Mtx.det : ℤ) : ℝ)) ^ 2 := by
    have hpos : (0 : ℤ) < Mtx.det ^ 2 := sq_pos_of_ne_zero hMtx_ne
    have : (1 : ℤ) ≤ Mtx.det ^ 2 := by omega
    exact_mod_cast this
  calc (gramMat k M c).det ≤ (((Mtx.det : ℤ) : ℝ)) ^ 2 * (gramMat k M c).det := by
        nth_rewrite 1 [← one_mul ((gramMat k M c).det)]
        exact mul_le_mul_of_nonneg_right hsq hnonneg
    _ = (gramMat k L b).det := hdet.symm

/-- The same comparison for bases indexed by possibly different `Fin`s, given the equality of the
indices (which is what the definition of `detL` produces for two lattices of equal rank). -/
theorem gramMat_det_le_of_le' {k k' : ℕ} (h : k = k') {L M : Submodule ℤ (ι → ℤ)}
    (b : Module.Basis (Fin k) ℤ L) (c : Module.Basis (Fin k') ℤ M) (hLM : L ≤ M) :
    (gramMat k' M c).det ≤ (gramMat k L b).det := by
  subst h
  exact gramMat_det_le_of_le b c hLM

end Work.HP
