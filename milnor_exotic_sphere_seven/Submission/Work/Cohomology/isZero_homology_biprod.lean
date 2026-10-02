import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Cohomology

open CategoryTheory Limits HomologicalComplex

/-- Homology is additive, hence carries binary biproducts to binary biproducts;
in particular the homology of a biproduct of two complexes is zero as soon as
both factors have vanishing homology in the given degree. -/
theorem isZero_homology_biprod {C D : ChainComplex (ModuleCat ℤ) ℕ} (n : ℕ)
    (hC : CategoryTheory.Limits.IsZero (C.homology n)) (hD : CategoryTheory.Limits.IsZero (D.homology n)) :
    CategoryTheory.Limits.IsZero ((C ⊞ D).homology n) := by
  let F := HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n
  have h : CategoryTheory.Limits.IsZero (F.obj (C ⊞ D)) := by
    rw [CategoryTheory.Limits.IsZero.iff_id_eq_zero]
    have hfst : F.map (biprod.fst : C ⊞ D ⟶ C) = 0 := hC.eq_of_tgt _ 0
    have hsnd : F.map (biprod.snd : C ⊞ D ⟶ D) = 0 := hD.eq_of_tgt _ 0
    calc 𝟙 (F.obj (C ⊞ D)) = F.map (𝟙 (C ⊞ D)) := (F.map_id _).symm
      _ = F.map (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) := by rw [biprod.total]
      _ = F.map (biprod.fst ≫ biprod.inl) + F.map (biprod.snd ≫ biprod.inr) := F.map_add
      _ = F.map biprod.fst ≫ F.map biprod.inl + F.map biprod.snd ≫ F.map biprod.inr := by
            rw [F.map_comp, F.map_comp]
      _ = 0 := by rw [hfst, hsnd, zero_comp, zero_comp, add_zero]
  simpa [F] using h

end Work.Cohomology
