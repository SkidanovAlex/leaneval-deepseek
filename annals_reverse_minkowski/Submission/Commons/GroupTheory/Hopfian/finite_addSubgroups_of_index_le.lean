import Mathlib.Algebra.Order.Star.Basic
import Mathlib.GroupTheory.IndexNSmul

/-!
# Finitely many subgroups of bounded finite index

For an additive commutative group `M` which is free and finitely generated as a
`ℤ`-module, only finitely many additive subgroups have finite index at most `m`.

Strategy: any such subgroup `H` contains the image `R` of multiplication by
`m!` (since the index `q = H.index` satisfies `q ∣ m!` and `q • x ∈ H` for
every `x`).  The quotient `M ⧸ R` is finite (it has `m! ^ finrank ℤ M`
elements), and additive subgroups of `M` containing `R` correspond, via the
correspondence theorem, to additive subgroups of the finite quotient `M ⧸ R`.
-/

namespace Commons.GroupTheory.Hopfian

private lemma factorial_smul_mem_of_index_le {M : Type*} [AddCommGroup M]
    (H : AddSubgroup M) (hH : H.FiniteIndex) {m : ℕ} (hm : H.index ≤ m) (x : M) :
    m.factorial • x ∈ H := by
  have hpos : 0 < H.index := Nat.pos_of_ne_zero hH.index_ne_zero
  have hdvd : H.index ∣ m.factorial := Nat.dvd_factorial hpos hm
  rcases hdvd with ⟨c, hc⟩
  have hmem : H.index • x ∈ H := AddSubgroup.nsmul_index_mem H x
  have hmem' : c • (H.index • x) ∈ H := AddSubgroup.nsmul_mem H hmem c
  rw [hc]
  simpa [mul_nsmul] using hmem'

private lemma finite_addSubgroups_of_finite {G : Type*} [AddGroup G] [Finite G] :
    Finite (AddSubgroup G) := by
  classical
  refine Finite.of_injective (fun H : AddSubgroup G => (H : Set G)) ?_
  intro H K h
  exact SetLike.ext' h

private lemma finite_addSubgroups_containing {M : Type*} [AddCommGroup M]
    (R : AddSubgroup M) (hfin : Finite (M ⧸ R)) :
    Finite {H : AddSubgroup M // R ≤ H} := by
  classical
  have hfs : Finite (AddSubgroup (M ⧸ R)) := finite_addSubgroups_of_finite
  exact (Equiv.finite_iff (QuotientAddGroup.comapMk'OrderIso R).toEquiv.symm).2 hfs

private lemma finite_quotient_of_finiteIndex' {G : Type*} [AddGroup G]
    (H : AddSubgroup G) (hH : H.FiniteIndex) : Finite (G ⧸ H) :=
  (AddSubgroup.finiteIndex_iff_finite_quotient).1 hH

theorem finite_addSubgroups_of_index_le {M : Type*} [AddCommGroup M]
    [Module.Free ℤ M] [Module.Finite ℤ M] (m : ℕ) :
    Finite {H : AddSubgroup M // H.FiniteIndex ∧ H.index ≤ m} := by
  classical
  let R : AddSubgroup M := (nsmulAddMonoidHom (α := M) m.factorial).range
  have hCont : ∀ H : AddSubgroup M, H.FiniteIndex → H.index ≤ m → R ≤ H := by
    intro H hH hm x hx
    rcases hx with ⟨y, hy⟩
    rw [← hy]
    simpa using factorial_smul_mem_of_index_le H hH hm y
  have hRindex : R.index = m.factorial ^ Module.finrank ℤ M := by
    simpa [R] using AddSubgroup.index_range_nsmul M m.factorial
  have hRfi : R.FiniteIndex := by
    rw [AddSubgroup.finiteIndex_iff]
    rw [hRindex]
    exact pow_ne_zero _ (Nat.factorial_ne_zero m)
  have hQ : Finite (M ⧸ R) := finite_quotient_of_finiteIndex' R hRfi
  have hSup : Finite {H : AddSubgroup M // R ≤ H} := finite_addSubgroups_containing R hQ
  refine Finite.of_injective
    (fun H : {H : AddSubgroup M // H.FiniteIndex ∧ H.index ≤ m} =>
      (⟨H.1, hCont H.1 H.2.1 H.2.2⟩ : {H : AddSubgroup M // R ≤ H})) ?_
  intro H K h
  have hfst : H.1 = K.1 := by
    simpa using congrArg Subtype.val h
  exact Subtype.ext hfst

end Commons.GroupTheory.Hopfian