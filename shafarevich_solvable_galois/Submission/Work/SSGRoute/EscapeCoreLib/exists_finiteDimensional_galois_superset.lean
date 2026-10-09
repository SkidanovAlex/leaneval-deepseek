import Mathlib
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A finite Galois extension containing finitely many finite subextensions

`Work.SSGRoute.EscapeCoreLib.exists_finiteDimensional_galois_superset`: for finitely many
intermediate fields `K, M, N` of `Ω / k` that are finite over `k` (and `k` perfect of
characteristic `0`), there is a single finite Galois intermediate field `L` containing all of them.

This is the first piece of the Čebotarev step of the Grünwald-with-escape node: the Galois-theoretic
lemma `EscapeCoreLib.exists_algEquiv_restrict_eq_of_fixing` needs all the fields to live inside one
finite Galois extension, and the escape construction needs `L` to contain `K`, the class field `M`
and `N = L₁ ⊔ L₂`.

## Construction

Take finite generating sets `sK`, `sM`, `sN` of `K`, `M`, `N` over `k` (they exist because the
extensions are finite, `Algebra.FiniteType.out` + `Subalgebra.fg_def`), let `S` be the union of
their images in `Ω`, let `F = adjoin k S` (finite over `k` by `IntermediateField.finiteDimensional_adjoin`,
the generators being algebraic, hence integral, over `k`) and let `L` be the normal closure of `F`
in `Ω` over `k`.  Then `L` is finite over `k` and Galois over `k` (Mathlib instances
`normalClosure.is_finiteDimensional`, `IsGalois.normalClosure`), and each of `K`, `M`, `N` is
contained in `L` because the preimage of `F` under the corresponding comparison map is a
`k`-subalgebra containing the generating set, hence everything.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Work.SSGRoute.EscapeCoreLib

/-- **A finite Galois intermediate field containing `K`, `M` and `N`.** -/
theorem exists_finiteDimensional_galois_superset
    {k Ω : Type} [Field k] [PerfectField k] [CharZero k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    (K M N : IntermediateField k Ω) [FiniteDimensional k K] [FiniteDimensional k M]
    [FiniteDimensional k N] :
    ∃ L : IntermediateField k Ω, FiniteDimensional k L ∧ IsGalois k L ∧
      K ≤ L ∧ M ≤ L ∧ N ≤ L := by
  classical
  obtain ⟨sK, hsKfin, hsK⟩ : ∃ s : Set ↥K, s.Finite ∧ Algebra.adjoin k s = ⊤ :=
    Subalgebra.fg_def.mp (Algebra.FiniteType.out (R := k) (A := ↥K))
  obtain ⟨sM, hsMfin, hsM⟩ : ∃ s : Set ↥M, s.Finite ∧ Algebra.adjoin k s = ⊤ :=
    Subalgebra.fg_def.mp (Algebra.FiniteType.out (R := k) (A := ↥M))
  obtain ⟨sN, hsNfin, hsN⟩ : ∃ s : Set ↥N, s.Finite ∧ Algebra.adjoin k s = ⊤ :=
    Subalgebra.fg_def.mp (Algebra.FiniteType.out (R := k) (A := ↥N))
  let S : Set Ω := ((↑) '' sK) ∪ ((↑) '' sM) ∪ ((↑) '' sN)
  have hSfin : S.Finite := (hsKfin.image _ |>.union (hsMfin.image _)).union (hsNfin.image _)
  have hSint : ∀ x ∈ S, IsIntegral k x := by
    intro x _
    exact isAlgebraic_iff_isIntegral.mp (Algebra.IsAlgebraic.isAlgebraic x)
  let F : IntermediateField k Ω := IntermediateField.adjoin k S
  let L : IntermediateField k Ω := IntermediateField.normalClosure k ↥F Ω
  have hFL : F ≤ L := IntermediateField.le_normalClosure F
  haveI : Finite S := hSfin.to_subtype
  have hFd : FiniteDimensional k ↥F := IntermediateField.finiteDimensional_adjoin hSint
  haveI : FiniteDimensional k ↥F := hFd
  haveI : FiniteDimensional k ↥L := inferInstance
  haveI : IsGalois k ↥L := inferInstance
  have hKF : K ≤ F := by
    intro x hx
    have h : Algebra.adjoin k sK ≤
        (IntermediateField.comap (IsScalarTower.toAlgHom k ↥K Ω) F).toSubalgebra := by
      refine Algebra.adjoin_le_iff.mpr ?_
      intro y hy
      exact IntermediateField.subset_adjoin k S (Or.inl (Or.inl ⟨y, hy, rfl⟩))
    have hx0 : (⟨x, hx⟩ : ↥K) ∈ Algebra.adjoin k sK := by rw [hsK]; trivial
    exact h hx0
  have hMF : M ≤ F := by
    intro x hx
    have h : Algebra.adjoin k sM ≤
        (IntermediateField.comap (IsScalarTower.toAlgHom k ↥M Ω) F).toSubalgebra := by
      refine Algebra.adjoin_le_iff.mpr ?_
      intro y hy
      exact IntermediateField.subset_adjoin k S (Or.inl (Or.inr ⟨y, hy, rfl⟩))
    have hx0 : (⟨x, hx⟩ : ↥M) ∈ Algebra.adjoin k sM := by rw [hsM]; trivial
    exact h hx0
  have hNF : N ≤ F := by
    intro x hx
    have h : Algebra.adjoin k sN ≤
        (IntermediateField.comap (IsScalarTower.toAlgHom k ↥N Ω) F).toSubalgebra := by
      refine Algebra.adjoin_le_iff.mpr ?_
      intro y hy
      exact IntermediateField.subset_adjoin k S (Or.inr ⟨y, hy, rfl⟩)
    have hx0 : (⟨x, hx⟩ : ↥N) ∈ Algebra.adjoin k sN := by rw [hsN]; trivial
    exact h hx0
  exact ⟨L, inferInstance, inferInstance, le_trans hKF hFL, le_trans hMF hFL, le_trans hNF hFL⟩

end Work.SSGRoute.EscapeCoreLib
