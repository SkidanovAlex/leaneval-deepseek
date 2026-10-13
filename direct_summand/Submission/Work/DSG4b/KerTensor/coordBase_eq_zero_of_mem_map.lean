import Mathlib
import Submission.Work.DSM2b.FlatSetup
import Submission.Work.DSM2bA.syzygy_mod_pow

namespace Work.DSG4b.KerTensor

universe u

open Work.DSM2b

/-- Reducing `coordBase g` modulo an ideal `J` of the target: the class of the base change is the
base change to the quotient, coordinatewise. -/
lemma coordBase_quot {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B)
    {k m : ℕ} (g : (Fin k → R) →ₗ[R] (Fin m → R)) (y : Fin k → B) :
    coordBase (R := R) (B := B ⧸ J) g (fun j => Ideal.Quotient.mk J (y j))
      = fun i => Ideal.Quotient.mk J (coordBase (R := R) (B := B) g y i) := by
  have h := map_coordBase (R := R) (B := B) (C := B ⧸ J) (Ideal.Quotient.mkₐ R J) g y
  have hzeq : (fun j => Ideal.Quotient.mk J (y j))
      = (fun j => (Ideal.Quotient.mkₐ R J) (y j)) := by
    funext j
    rw [Ideal.Quotient.mkₐ_eq_mk]
  rw [hzeq, ← h]
  ext i
  rw [Ideal.Quotient.mkₐ_eq_mk]

/-- The hypothesis "every coordinate of `coordBase g y` lies in `I ^ n B`" says exactly that the
base change of `coordBase g` to `S = R ⧸ I ^ n` and `M = B ⧸ (I ^ n).map (algebraMap R B)` kills
the class of `y`.

The declaration should live in `namespace Work.DSG4b.KerTensor` (file
`Submission/Work/DSG4b/KerTensor/coordBase_eq_zero_of_mem_map.lean`). -/
lemma coordBase_eq_zero_of_mem_map {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (I : Ideal R) {k m : ℕ} (g : (Fin k → R) →ₗ[R] (Fin m → R)) (n : ℕ) {y : Fin k → B}
    (hy : ∀ i, Work.DSM2b.coordBase (R := R) (B := B) g y i ∈ (I ^ n).map (algebraMap R B)) :
    Work.DSM2b.coordBase (R := R ⧸ I ^ n) (B := B ⧸ (I ^ n).map (algebraMap R B))
      (Work.DSM2b.coordBase (R := R) (B := R ⧸ I ^ n) g)
      (fun j => Ideal.Quotient.mk ((I ^ n).map (algebraMap R B)) (y j)) = 0 := by
  have hzR : coordBase (R := R) (B := B ⧸ (I ^ n).map (algebraMap R B)) g
      (fun j => Ideal.Quotient.mk ((I ^ n).map (algebraMap R B)) (y j)) = 0 := by
    rw [coordBase_quot]
    ext i
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hy i)
  rw [Work.DSM2bA.coordBase_coordBase_tower (R := R) (B := R ⧸ I ^ n)
    (C := B ⧸ (I ^ n).map (algebraMap R B)) g
    (fun j => Ideal.Quotient.mk ((I ^ n).map (algebraMap R B)) (y j))]
  exact hzR

end Work.DSG4b.KerTensor
