import Mathlib

open Matrix

namespace Work.L2F.Props.CFP

theorem pow_two_mul_orderOf_eigenvalue (F : Type*) [Field F]
    (X : Matrix.SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F) (hv : v ≠ 0) (c : F)
    (hXv : Matrix.mulVec (X : Matrix (Fin 2) (Fin 2) F) v = c • v) (n : ℕ)
    (hn : (Matrix.SpecialLinearGroup.toPGL X) ^ n = 1) :
    c ^ (2 * n) = 1 := by
  -- `X ^ n` maps to the identity in `PGL`, hence lies in the kernel of `toPGL`,
  -- which Mathlib identifies with the center of `SL(2, F)`.
  have hker : X ^ n ∈ (Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)).ker := by
    rw [MonoidHom.mem_ker, map_pow, hn]
  rw [Matrix.SpecialLinearGroup.toPGL_ker] at hker
  -- So `X ^ n` is a scalar matrix, say `r • 1`, with `r ^ 2 = 1`.
  obtain ⟨r, hr2, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hker
  -- `X ^ m` acts on the eigenvector `v` by multiplication by `c ^ m`.
  have hvec : ∀ m : ℕ, ((X : Matrix (Fin 2) (Fin 2) F) ^ m) *ᵥ v = c ^ m • v := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hXv, Matrix.mulVec_smul, ih, smul_smul,
        ← pow_succ']
  -- A scalar matrix acts on a vector by scalar multiplication.
  have hscal : (Matrix.scalar (Fin 2) r) *ᵥ v = r • v := by
    ext i
    rw [Matrix.scalar_apply, Matrix.mulVec_diagonal]
    rfl
  -- Hence `r • v = c ^ n • v`; comparing a non-zero coordinate gives `r = c ^ n`.
  have h3 : r • v = c ^ n • v := by
    rw [← hscal, hrA, Matrix.SpecialLinearGroup.coe_pow]
    exact hvec n
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have h4 : r = c ^ n := by
    have h5 : r * v i = c ^ n * v i := by
      have hh := congr_fun h3 i
      simpa using hh
    exact mul_right_cancel₀ hi h5
  rw [h4] at hr2
  simp only [Fintype.card_fin] at hr2
  have hmain : (c ^ n) ^ 2 = c ^ (2 * n) := by
    rw [← pow_mul, Nat.mul_comm 2 n]
  rwa [← hmain]

end Work.L2F.Props.CFP
