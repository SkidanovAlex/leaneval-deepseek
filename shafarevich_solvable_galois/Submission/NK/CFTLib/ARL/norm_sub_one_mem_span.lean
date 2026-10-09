import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.CFTLib.ARL

/-- If two square matrices over a commutative ring are entrywise congruent modulo an ideal `I`,
then their determinants are congruent modulo `I`. -/
lemma det_sub_det_mem_of_sub_mem {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (I : Ideal R) {M N : Matrix ι ι R} (h : ∀ i j, M i j - N i j ∈ I) :
    M.det - N.det ∈ I := by
  rw [← Ideal.Quotient.eq]
  rw [RingHom.map_det, RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply,
    Ideal.Quotient.eq]
  exact h i j

/-- If `x ≡ 1` modulo `n` in a finite free `ℤ`-algebra `S`, then the norm of `x` is `≡ 1`
modulo `n`. -/
theorem norm_sub_one_mem_span {S : Type*} [CommRing S] [Module.Free ℤ S] [Module.Finite ℤ S]
    (n : ℕ) (x : S) (hx : x - 1 ∈ Ideal.span {(n : S)}) :
    Algebra.norm ℤ x - 1 ∈ Ideal.span {(n : ℤ)} := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hx
  have hx' : x = 1 + n • a := by
    have h : x - 1 = n • a := by rw [← ha, nsmul_eq_mul, mul_comm]
    rw [eq_add_of_sub_eq h, add_comm]
  let b := Module.finBasis ℤ S
  have hM : Algebra.leftMulMatrix b x = 1 + n • Algebra.leftMulMatrix b a := by
    rw [hx', map_add, map_one, map_nsmul]
  have hentry : ∀ i j, (Algebra.leftMulMatrix b x) i j -
      (1 : Matrix (Fin (Module.finrank ℤ S)) (Fin (Module.finrank ℤ S)) ℤ) i j
      ∈ Ideal.span {(n : ℤ)} := by
    intro i j
    have h : (Algebra.leftMulMatrix b x) i j -
        (1 : Matrix (Fin (Module.finrank ℤ S)) (Fin (Module.finrank ℤ S)) ℤ) i j
        = (n : ℤ) * (Algebra.leftMulMatrix b a) i j := by
      rw [hM, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [h]
    exact Ideal.mem_span_singleton.mpr ⟨_, rfl⟩
  have hdet := det_sub_det_mem_of_sub_mem (Ideal.span {(n : ℤ)}) hentry
  rw [Algebra.norm_eq_matrix_det b x]
  simpa using hdet

end NK.CFTLib.ARL
