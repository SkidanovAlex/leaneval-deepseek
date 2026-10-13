import Mathlib
import Submission.Work.DSF1.Sheaf.AcycDefs
import Submission.Work.DSF1.Cech.DeltaSuccK
import Submission.Work.DSMX0bU.CechHomotopyDefs
import Submission.Work.DSMX0bU.DeltaSuccCechK

/-!
# Exactness of the Čech complex of a family containing a cover of `V`

Let `X` be a scheme, `U : ι → X.Opens` a family of opens, `i₀ : ι`, `V : X.Opens` with
`V ≤ U i₀`, and `P : X.Opensᵒᵖ ⥤ AddCommGrpCat` a presheaf of abelian groups.  This
file shows that the Čech complex of the family `i ↦ V ⊓ U i` with coefficients in `P` has
trivial cohomology in positive degrees (`Work.DSF1.Sheaf.CechTrivAll`).

The point is that this complex is *contractible*: since `V ⊓ U i ≤ V = V ⊓ U i₀`, every
finite intersection of members of the family is contained in `V = V ⊓ U i₀`, so inserting
the index `i₀` at position `0` gives a contracting homotopy `cechK` of the (cosimplicial)
Čech object, on the nose (see `CechHomotopyDefs` for its construction and its component
formulas).  No sheaf condition, no separatedness and no finiteness of `ι` are used; only the
lattice identity `V ⊓ U i₀ = V` (from `hV`) is needed.
-/

namespace Work.DSMX0bU

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

universe u

variable {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u}


/-- The differential of the Čech complex is the alternating sum of the cofaces. -/
lemma cech_d_eq_sum_delta (U : ι → X.Opens) (V : X.Opens)
    (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) :
    ((cechComplexFunctor (fun i => V ⊓ U i)).obj P).d n (n+1) =
      ∑ i : Fin (n+2), (-1 : ℤ) ^ (i : ℕ) • cechDelta U V P n i :=
  (CochainComplex.of_d (fun m => (Cosi U V P).obj (SimplexCategory.mk m))
    (AlgebraicTopology.AlternatingCofaceMapComplex.objD (Cosi U V P)) n).trans rfl

/-- The homotopy identity showing that the Čech complex of `i ↦ V ⊓ U i` is contractible
in positive degrees. -/
lemma cech_homotopy (U : ι → X.Opens) (i₀ : ι) (V : X.Opens) (hV : V ≤ U i₀)
    (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) :
    cechK U i₀ V hV P n ≫ ((cechComplexFunctor (fun i => V ⊓ U i)).obj P).d n (n+1) +
      ((cechComplexFunctor (fun i => V ⊓ U i)).obj P).d (n+1) (n+2) ≫
        cechK U i₀ V hV P (n+1) =
      𝟙 (((cechComplexFunctor (fun i => V ⊓ U i)).obj P).X (n+1)) := by
  rw [cech_d_eq_sum_delta U V P n, cech_d_eq_sum_delta U V P (n+1)]
  rw [Preadditive.comp_sum, Preadditive.sum_comp]
  simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  rw [Fin.sum_univ_succ (n := n+2)]
  rw [Fin.val_zero, pow_zero, one_zsmul, delta0_comp_cechK U i₀ V hV P (n+1)]
  have hh : (∑ x : Fin (n+2), (-1 : ℤ) ^ (x : ℕ) •
        (cechK U i₀ V hV P n ≫ cechDelta U V P n x)) +
      (∑ i : Fin (n+2), (-1 : ℤ) ^ ((i.succ : Fin (n+3)) : ℕ) •
        (cechDelta U V P (n+1) i.succ ≫ cechK U i₀ V hV P (n+1))) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    rw [DeltaSuccCechK U i₀ V hV P n i,
      show (-1 : ℤ) ^ ((i.succ : Fin (n+3)) : ℕ) = -((-1 : ℤ) ^ (i : ℕ)) from by
        simp [Fin.val_succ, pow_succ]]
    rw [neg_zsmul, add_neg_cancel]
  rw [show (∑ x : Fin (n+2), (-1 : ℤ) ^ (x : ℕ) •
          (cechK U i₀ V hV P n ≫ cechDelta U V P n x)) +
        (𝟙 (((cechComplexFunctor (fun i => V ⊓ U i)).obj P).X (n+1)) +
          ∑ i : Fin (n+2), (-1 : ℤ) ^ ((i.succ : Fin (n+3)) : ℕ) •
            (cechDelta U V P (n+1) i.succ ≫ cechK U i₀ V hV P (n+1)))
      = ((∑ x : Fin (n+2), (-1 : ℤ) ^ (x : ℕ) •
            (cechK U i₀ V hV P n ≫ cechDelta U V P n x)) +
          (∑ i : Fin (n+2), (-1 : ℤ) ^ ((i.succ : Fin (n+3)) : ℕ) •
            (cechDelta U V P (n+1) i.succ ≫ cechK U i₀ V hV P (n+1)))) +
          𝟙 (((cechComplexFunctor (fun i => V ⊓ U i)).obj P).X (n+1)) from by abel,
    hh, zero_add]

/-- In a cochain complex of abelian groups, a family of maps `k n : X (n+1) ⟶ X n` with
`k n ≫ d n (n+1) + d (n+1) (n+2) ≫ k (n+1) = 𝟙` trivialises all positive-degree cocycles. -/
lemma cechTrivAll_of_contractible {K : CochainComplex AddCommGrpCat.{u} ℕ}
    (k : ∀ n : ℕ, K.X (n+1) ⟶ K.X n)
    (h : ∀ n : ℕ, k n ≫ K.d n (n+1) + K.d (n+1) (n+2) ≫ k (n+1) = 𝟙 (K.X (n+1))) :
    Work.DSF1.Sheaf.CechTrivAll K := by
  intro p x hx
  refine ⟨(k p) x, ?_⟩
  have h1 := congrArg (fun f : K.X (p+1) ⟶ K.X (p+1) => f x) (h p)
  simp only [AddCommGrpCat.hom_add_apply, AddCommGrpCat.comp_apply, AddCommGrpCat.id_apply,
    hx, map_zero, add_zero] at h1
  exact h1

theorem cechTrivAll_of_le_mem {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u} [Finite ι]
    (U : ι → X.Opens) (i₀ : ι) (V : X.Opens) (hV : V ≤ U i₀)
    (P : CategoryTheory.Functor (Opposite (X.Opens)) (AddCommGrpCat.{u})) :
    Work.DSF1.Sheaf.CechTrivAll
      ((CategoryTheory.cechComplexFunctor (fun i => V ⊓ U i)).obj P) := by
  exact cechTrivAll_of_contractible (cechK U i₀ V hV P) (cech_homotopy U i₀ V hV P)

end Work.DSMX0bU
