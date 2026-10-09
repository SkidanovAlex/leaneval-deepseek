import Mathlib
import Submission.Work.SSGRoute.ZDataMup.ssg_cyclic_quotient_separates
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.SSGRoute.ZDataMup

/-- **A non-trivial element of a finite abelian Galois group is separated by a cyclic intermediate
field.**  If `L/K` is finite Galois with commutative Galois group and `σ ≠ 1` in `Gal(L/K)`, there
is an intermediate field `M` with `Gal(M/K)` cyclic such that `σ` does not fix `M` pointwise
(`σ ∉ M.fixingSubgroup`).

Route: the finite-abelian-group fact that a non-trivial element is separated by a cyclic quotient
(`Work.SSGRoute.ZDataMup.ssg_cyclic_quotient_separates`) applied to `σ` gives a finite cyclic `C`
and `φ : Gal(L/K) →* C` with `φ σ ≠ 1`; take `M = IntermediateField.fixedField φ.ker`.  Then
`σ ∉ φ.ker = M.fixingSubgroup` (`IntermediateField.fixingSubgroup_fixedField`), and
`Gal(M/K) ≅ Gal(L/K) ⧸ φ.ker ≅ φ.range ≤ C` is cyclic (`IsGalois.normalAutEquivQuotient`,
`QuotientGroup.quotientKerEquivRange`, `Subgroup.isCyclic`). -/
theorem exists_isCyclic_fixingSubgroup_notMem
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1) :
    ∃ M : IntermediateField K L, IsCyclic (↥M ≃ₐ[K] ↥M) ∧ σ ∉ M.fixingSubgroup := by
  classical
  -- `Gal(L/K)` is commutative, so we may use the finite-abelian-group separation lemma on it.
  letI : CommGroup (L ≃ₐ[K] L) :=
    { (inferInstance : Group (L ≃ₐ[K] L)) with mul_comm := hcomm }
  obtain ⟨C, hComm, hFin, hCyc, φ, hφ⟩ :=
    ssg_cyclic_quotient_separates (G := L ≃ₐ[K] L) σ hσ
  letI : CommGroup C := hComm
  letI : Fintype C := hFin
  letI : IsCyclic C := hCyc
  -- The intermediate field fixed by the kernel of `φ`.
  refine ⟨IntermediateField.fixedField φ.ker, ?_, ?_⟩
  · -- `Gal(fixedField φ.ker / K) ≅ Gal(L/K) ⧸ φ.ker ≅ φ.range ≤ C` is cyclic.
    have h1 : IsCyclic (Gal(L/K) ⧸ φ.ker) :=
      (MulEquiv.isCyclic (QuotientGroup.quotientKerEquivRange φ)).mpr (Subgroup.isCyclic φ.range)
    have h2 : IsCyclic (Gal(↥(IntermediateField.fixedField φ.ker)/K)) :=
      (MulEquiv.isCyclic (IsGalois.normalAutEquivQuotient φ.ker)).mp h1
    exact h2
  · -- `σ` does not lie in the fixing subgroup of its fixed field.
    rw [IntermediateField.fixingSubgroup_fixedField]
    exact fun h => hφ (MonoidHom.mem_ker.mp h)

end Work.SSGRoute.ZDataMup
