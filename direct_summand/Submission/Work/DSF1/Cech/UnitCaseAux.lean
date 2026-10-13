import Mathlib
import Submission.Work.DSF1.Cech.CechSetup
import Submission.Work.DSF1.Cech.CechComponents
import Submission.Work.DSF1.Cech.UnitCaseSetup
import Submission.Work.DSF1.Cech.CoaugCycle
import Submission.Work.DSF1.Cech.DeltaSuccK
import Submission.Work.DSF1.Cech.KTopSq

/-!
# The augmented Čech complex in the "unit case"

Assuming `IsIsoDeletion U Q i₀` (one of the Čech cofaces is inverted by `Q`), the Čech
complex of `Q` for the family `U` is exact in positive degrees and its `H⁰` is `Q(⊤)`,
with `coaug : Q(⊤) ⟶ Č⁰` a split monomorphism.

This file proves the two chain-homotopy identities

* `kTop ≫ coaug + d 0 1 ≫ k 0 = 𝟙` (degree `0`), and
* `k n ≫ d n (n+1) + d (n+1) (n+2) ≫ k (n+1) = 𝟙` (degree `n+1`),

from the "extra codegeneracy" identities `δ₀ ≫ k = 𝟙`, `δ_{i+1} ≫ k = k ≫ δ_i` and the
boundary identity `δ₁ ≫ k₀ = kTop ≫ coaug`.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

universe u

namespace Work.DSF1.Cech

variable {X : Scheme.{u}} {S : Type u} [CommRing S] {ι : Type u}
variable (U : ι → X.Opens) (Q : X.Opensᵒᵖ ⥤ ModuleCat S) {i₀ : ι}

/-- The coface maps of the Čech cosimplicial object, re-typed as morphisms of the Čech
complex.  This ascription is what makes the bookkeeping of (co)faces and of `k` line up. -/
noncomputable def deltaX (n : ℕ) (i : Fin (n+2)) :
    ((cechComplexFunctor U).obj Q).X n ⟶ ((cechComplexFunctor U).obj Q).X (n+1) :=
  (Cosimplicial U Q).δ i

/-- The differential of the Čech complex is the alternating sum of its cofaces. -/
lemma d_eq_sum_deltaX (n : ℕ) :
    ((cechComplexFunctor U).obj Q).d n (n+1) =
      ∑ i : Fin (n+2), (-1 : ℤ) ^ (i : ℕ) • deltaX U Q n i :=
  (CochainComplex.of_d (fun m => (Cosimplicial U Q).obj (SimplexCategory.mk m))
    (AlgebraicTopology.AlternatingCofaceMapComplex.objD (Cosimplicial U Q)) n).trans rfl

/-- `δ₀ ≫ k = 𝟙`, the first extra-codegeneracy identity, in `X`-types. -/
lemma delta0_comp_k_dX (h : IsIsoDeletion U Q i₀) (n : ℕ) :
    deltaX U Q n 0 ≫ k U Q h n = 𝟙 _ :=
  delta0_comp_k U Q h n

/-- `δ_{i+1} ≫ k = k ≫ δ_i`, the second extra-codegeneracy identity, in `X`-types. -/
lemma DeltaSuccK_dX (h : IsIsoDeletion U Q i₀) (n : ℕ) (i : Fin (n+2)) :
    deltaX U Q (n+1) i.succ ≫ k U Q h (n+1) = k U Q h n ≫ deltaX U Q n i :=
  DeltaSuccK U Q h n i

/-- `δ₁ ≫ k₀ = kTop ≫ coaug`, the boundary case of the second identity. -/
lemma KTopSq_dX (h : IsIsoDeletion U Q i₀) :
    deltaX U Q 0 1 ≫ k U Q h 0 = kTop U Q h ≫ coaug U Q :=
  KTopSq U Q h

/-- **Chain homotopy identity in degree `n + 1`.** -/
lemma homotopy_succ (h : IsIsoDeletion U Q i₀) (n : ℕ) :
    k U Q h n ≫ ((cechComplexFunctor U).obj Q).d n (n+1) +
      ((cechComplexFunctor U).obj Q).d (n+1) (n+2) ≫ k U Q h (n+1) =
        𝟙 (((cechComplexFunctor U).obj Q).X (n+1)) := by
  rw [d_eq_sum_deltaX U Q n, d_eq_sum_deltaX U Q (n+1)]
  rw [Preadditive.comp_sum, Preadditive.sum_comp]
  simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  rw [Fin.sum_univ_succ (n := n+2)]
  rw [Fin.val_zero, pow_zero, one_zsmul, delta0_comp_k_dX U Q h (n+1)]
  have hh : (∑ x : Fin (n+2), (-1 : ℤ) ^ (x:ℕ) • (k U Q h n ≫ deltaX U Q n x)) +
      (∑ i : Fin (n+2), (-1 : ℤ) ^ ((i.succ : Fin (n+3)) : ℕ) •
          (deltaX U Q (n+1) i.succ ≫ k U Q h (n+1))) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    rw [DeltaSuccK_dX U Q h n i,
      show (-1 : ℤ) ^ ((i.succ : Fin (n+3)) : ℕ) = -((-1 : ℤ) ^ (i : ℕ)) from by
        simp [Fin.val_succ, pow_succ]]
    rw [neg_zsmul, add_neg_cancel]
  rw [show (∑ x : Fin (n+2), (-1 : ℤ) ^ (x:ℕ) • (k U Q h n ≫ deltaX U Q n x)) +
        (𝟙 (((cechComplexFunctor U).obj Q).X (n+1)) +
          ∑ i : Fin (n+2), (-1 : ℤ) ^ ((i.succ : Fin (n+3)) : ℕ) •
            (deltaX U Q (n+1) i.succ ≫ k U Q h (n+1)))
      = ((∑ x : Fin (n+2), (-1 : ℤ) ^ (x:ℕ) • (k U Q h n ≫ deltaX U Q n x)) +
          (∑ i : Fin (n+2), (-1 : ℤ) ^ ((i.succ : Fin (n+3)) : ℕ) •
            (deltaX U Q (n+1) i.succ ≫ k U Q h (n+1)))) +
          𝟙 (((cechComplexFunctor U).obj Q).X (n+1)) from by abel,
    hh, zero_add]

/-- **Chain homotopy identity in degree `0`.** -/
lemma homotopy_zero (h : IsIsoDeletion U Q i₀) :
    kTop U Q h ≫ coaug U Q +
      ((cechComplexFunctor U).obj Q).d 0 1 ≫ k U Q h 0 =
        𝟙 (((cechComplexFunctor U).obj Q).X 0) := by
  rw [d_eq_sum_deltaX U Q 0]
  rw [Fin.sum_univ_two]
  rw [Fin.val_zero, pow_zero, one_zsmul]
  rw [show ((-1 : ℤ) ^ (((1 : Fin 2) : ℕ))) = -1 from by norm_num]
  rw [neg_one_zsmul]
  rw [Preadditive.add_comp, Preadditive.neg_comp]
  rw [delta0_comp_k_dX U Q h 0, KTopSq_dX U Q h]
  abel

end Work.DSF1.Cech
