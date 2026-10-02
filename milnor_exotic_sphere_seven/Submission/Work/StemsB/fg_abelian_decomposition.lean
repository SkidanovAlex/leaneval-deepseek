import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

/-!
# Structure theorem for finitely generated abelian groups, in product form

A finitely generated `ℤ`-module (i.e. a finitely generated abelian group) is isomorphic to
`(Fin r → ℤ) × F` for some `r : ℕ` and some finite abelian group `F`.  This is the shape in
which the structure theorem is used in the stable-stems computations: the free part is recorded
by its rank `r` and all the torsion is collected into a single finite group `F`.

The content is Mathlib's `AddCommGroup.equiv_free_prod_directSum_zmod`, rewritten from
`(Fin r →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)` into the product form above (the finitely supported
functions on `Fin r` are all functions, and a finite direct sum of finite groups is finite).
-/

namespace Work.StemsB

theorem fg_abelian_decomposition (A : Type) [AddCommGroup A] [Module.Finite ℤ A] :
    ∃ (r : ℕ) (F : Type) (_ : AddCommGroup F) (_ : Finite F),
      Nonempty (A ≃+ ((Fin r → ℤ) × F)) := by
  classical
  have hG : AddGroup.FG A := (Module.Finite.iff_addGroup_fg).mp ‹Module.Finite ℤ A›
  obtain ⟨n, ι, fι, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod A
  haveI := fι
  haveI : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  haveI : Fintype (DirectSum ι fun i => ZMod (p i ^ e i)) :=
    Fintype.ofEquiv (∀ i, ZMod (p i ^ e i)) DFinsupp.equivFunOnFintype.symm
  refine ⟨n, DirectSum ι fun i => ZMod (p i ^ e i), inferInstance, inferInstance, ?_⟩
  exact ⟨f.trans (AddEquiv.prodCongr Finsupp.addEquivFunOnFinite (AddEquiv.refl _))⟩

end Work.StemsB
