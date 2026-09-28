import Mathlib
import Submission.Work.Cohomology.cup1Faces

/-!
# Casting cochains along an equality of degrees

Evaluation of a cochain transported along an equality of degrees (`genEval_cast`), and the
identifications of the face maps of the transported simplex with `Delmap` and with `frontIncl` /
`backIncl` / `Amap`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable {R : Type} [CommRing R] {X : SSet}

/-- **Evaluating a transported cochain**: transporting a cochain along `h : p = q` and evaluating at
`σ` is the same as evaluating the original cochain at the transported simplex. -/
lemma genEval_cast {p q : ℕ} (h : p = q) (f : Cochain R X p) (σ : X _⦋q⦌) :
    genEval R X (h ▸ f) σ = genEval R X f (X.map (shmap p q h).op σ) := by
  show (h ▸ f) ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1)
      = f ((X.ιChainComplex (R := ModuleCat.of R R) (X.map (shmap p q h).op σ)).hom 1)
  have hmor : (eqToHom (congrArg SimplexCategory.mk h.symm).symm : ⦋p⦌ ⟶ ⦋q⦌)
      = shmap p q h := by
    simp only [shmap]
  rw [cast_linearMap_apply, generator_transport h.symm σ, hmor]

/-- The face maps of a transported simplex are `Delmap`. -/
lemma delta_comp_shmap (n m : ℕ) (hh : n+m-1+1 = n+m) (i : Fin ((n+m-1+1)+1))
    (h : 1 ≤ n+m) :
    SimplexCategory.δ i ≫ shmap (n+m-1+1) (n+m) hh = Delmap n m i.val h := by
  refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
  apply Fin.ext
  rw [CategoryTheory.comp_apply]
  simp only [SimplexCategory.coe_δ, shmap_val, Delmap_val_if, succAbove_val_if']
  try (split_ifs <;> omega)

lemma frontIncl_comp_shmap (n m : ℕ) :
    frontIncl m (m+n) (by omega) ≫ shmap (m+n) (n+m) (Nat.add_comm m n)
      = frontIncl m (n+m) (by omega) := by
  refine ConcreteCategory.hom_ext _ _ (fun j => ?_)
  apply Fin.ext
  rw [CategoryTheory.comp_apply]
  simp only [shmap_val, hom_frontIncl_val]

lemma backIncl_comp_shmap (n m : ℕ) :
    backIncl m n ≫ shmap (m+n) (n+m) (Nat.add_comm m n) = Amap n m m (by omega) := by
  refine ConcreteCategory.hom_ext _ _ (fun j => ?_)
  apply Fin.ext
  rw [CategoryTheory.comp_apply]
  simp only [shmap_val, hom_backIncl_val, Amap_val]

lemma Amap_zero_eq_frontIncl (n m : ℕ) :
    Amap n m 0 (by omega) = frontIncl n (n+m) (by omega) := by
  refine ConcreteCategory.hom_ext _ _ (fun j => ?_)
  apply Fin.ext
  simp only [Amap_val, hom_frontIncl_val]
  omega

/-- A sum over `Finset.range` as a sum over `Fin`. -/
lemma sum_range_eq_fin (K : ℕ) (f : ℕ → R) :
    (∑ i ∈ Finset.range K, f i) = ∑ i : Fin K, f i.val := by
  rw [← Fin.sum_univ_eq_sum_range f K]

end

end Work.Cohomology
