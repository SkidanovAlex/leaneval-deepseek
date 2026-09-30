import Submission.Work.ThomBordism.PontryaginThom.Hurewicz

/-!
# The Hurewicz image of the Pontryagin–Thom class, rationally

Item 2 of the chapter in the form in which the vanishing is usually quoted: when the tangent
Pontryagin numbers of `V` vanish, the Hurewicz image of `α_V` is **zero in rational homology**,
`h ⊗ 1 = 0` in `H_{k+8}(T;ℤ) ⊗[ℤ] ℚ`.

`ThomTarget.detects_torsion` (the coefficient-free form of `H^{k+8}(T;ℚ) = ℚ{p₁²U, p₂U}`, since the
workspace has no coefficient-change functor in homology) gives a positive multiple `N • h = 0`;
`tmul_one_eq_zero_of_nsmul_eq_zero` extracts the rational consequence, the elementary computation
`h ⊗ 1 = h ⊗ (N · N⁻¹) = (N • h) ⊗ N⁻¹ = 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open TensorProduct

namespace Work.ThomBordism.PontryaginThom

noncomputable section

open Work.Cohomology

/-- **An element with a positive multiple equal to zero dies in rational homology**: for `N • h = 0`
with `N > 0`, `h ⊗ 1 = h ⊗ (N · (1/N)) = (N • h) ⊗ (1/N) = 0`. -/
theorem tmul_one_eq_zero_of_nsmul_eq_zero {M : Type*} [AddCommGroup M] (h : M)
    {N : ℕ} (hN : 0 < N) (hh : (N : ℤ) • h = 0) : h ⊗ₜ[ℤ] (1 : ℚ) = 0 := by
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hq : (1 : ℚ) = (N : ℤ) • ((1 : ℚ) / (N : ℚ)) := by
    rw [← Int.cast_smul_eq_zsmul ℚ (N : ℤ) ((1 : ℚ) / (N : ℚ)), smul_eq_mul, Int.cast_natCast]
    rw [eq_comm, mul_comm, div_mul_cancel₀ 1 hNq]
  rw [hq, tmul_smul, smul_tmul', hh]
  simp

/-- **The Hurewicz image of the Pontryagin–Thom class is zero rationally** when the tangent
Pontryagin numbers of `V` vanish. -/
theorem PTRep.hurewiczClass_rat_eq_zero {V : Man8} {k : ℕ} {D : ThomTarget k}
    (r : PTRep V k D) (h1 : V.p1Sq = 0) (h2 : V.p2Num = 0) :
    hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀ r.α ⊗ₜ[ℤ] (1 : ℚ) = 0 := by
  obtain ⟨N, hN, hh⟩ := r.hurewiczClass_torsion h1 h2
  rw [show (HomologicalComplex.homology (chainC ℤ (ssetOf D.T)) (k + 8)).isModule
      = AddCommGroup.toIntModule ↥((chainC ℤ (ssetOf D.T)).homology (k + 8))
      from Subsingleton.elim _ _]
  exact tmul_one_eq_zero_of_nsmul_eq_zero
    (hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀ r.α) hN hh

/-- The same for a family with vanishing total Pontryagin numbers. -/
theorem PTFamilyRep.hurewiczClass_rat_eq_zero {ι : Type} [Fintype ι] {F : ι → Man8}
    {k : ℕ} {D : ThomTarget k} (r : PTFamilyRep ι F k D)
    (h1 : ∑ i, (F i).p1Sq = 0) (h2 : ∑ i, (F i).p2Num = 0) :
    hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀ r.α ⊗ₜ[ℤ] (1 : ℚ) = 0 := by
  obtain ⟨N, hN, hh⟩ := r.hurewiczClass_torsion h1 h2
  rw [show (HomologicalComplex.homology (chainC ℤ (ssetOf D.T)) (k + 8)).isModule
      = AddCommGroup.toIntModule ↥((chainC ℤ (ssetOf D.T)).homology (k + 8))
      from Subsingleton.elim _ _]
  exact tmul_one_eq_zero_of_nsmul_eq_zero
    (hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀ r.α) hN hh

end

end Work.ThomBordism.PontryaginThom
