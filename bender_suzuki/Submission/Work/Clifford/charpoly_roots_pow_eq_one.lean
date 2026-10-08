import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Clifford

/-- If a linear endomorphism `T` of a finite-dimensional complex vector space satisfies
`T ^ n = 1`, then every root `a` of the characteristic polynomial of `T` is an `n`-th root of
unity. Indeed such a root is an eigenvalue of `T` (Mathlib: the roots of the characteristic
polynomial are the eigenvalues), and an eigenvector `v ≠ 0` with `T v = a • v` satisfies
`a ^ n • v = T ^ n v = v`, whence `a ^ n = 1`. -/
theorem charpoly_roots_pow_eq_one {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (T : W →ₗ[ℂ] W) (n : ℕ) (hT : T ^ n = 1) {a : ℂ} (ha : a ∈ T.charpoly.roots) :
    a ^ n = 1 := by
  have hne : T.charpoly ≠ 0 := T.charpoly_monic.ne_zero
  have hroot : T.charpoly.IsRoot a := (Polynomial.mem_roots hne).mp ha
  have hev : Module.End.HasEigenvalue T a :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly T a).mpr hroot
  rw [Module.End.hasEigenvalue_iff] at hev
  obtain ⟨v, hvmem, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hev
  have hvv : T v = a • v := (Module.End.mem_eigenspace_iff).mp hvmem
  have hp : ∀ m : ℕ, (T ^ m) v = a ^ m • v := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, hvv, smul_smul, pow_succ]
  have hv1 : a ^ n • v = v := by
    have h := hp n
    rw [hT] at h
    simpa using h.symm
  have hzero : (a ^ n - 1) • v = 0 := by
    rw [sub_smul, one_smul, hv1, sub_self]
  have : a ^ n - 1 = 0 := (smul_eq_zero.mp hzero).resolve_right hv0
  exact sub_eq_zero.mp this

end Work.Clifford
