import Mathlib
import Submission.Work.ORLyndon.CLDirect.cldDefs
import Submission.Work.ORLyndon.CLDirect.clPhi_one
import Submission.Work.ORLyndon.CLDirect.clPhi_mul
import Submission.Work.ORLyndon.CLDirect.clPhi_conj_pow

/-!
# Equivariance of `φ` under conjugation

`Work.ORLyndon.CLDirect.clPhi_conj`: for `n` in the normal closure of `u ^ l`, the map `φ = clPhi D l`
satisfies `φ (f n f⁻¹) = f̄ · φ n`.  This is the crossing equivariance used by the Fox-kernel lemma
`Work.ORLyndon.CLDirect.foxKernel_vanish` (unit C5), with `φ := clPhi D l`.
-/

set_option autoImplicit false

namespace Work.ORLyndon.CLDirect

open MonoidAlgebra

universe u v

variable {X : Type u} [DecidableEq X] {K : Type v} [Field K]

/-- **Equivariance of `φ` under conjugation.** -/
theorem clPhi_conj {u : FreeGroup X} (D : CLData u) (l : ℕ) (f : FreeGroup X) {n : FreeGroup X}
    (hn : n ∈ Subgroup.normalClosure ({u ^ l} : Set (FreeGroup X))) :
    clPhi (K := K) D l (f * n * f⁻¹) =
      MonoidAlgebra.of K _ (presentRho (u ^ l) f) * clPhi (K := K) D l n := by
  classical
  -- `φ` is odd on `⟪u ^ l⟫`.
  have hodd : ∀ {a : FreeGroup X}, a ∈ Subgroup.normalClosure ({u ^ l} : Set (FreeGroup X)) →
      clPhi (K := K) D l a⁻¹ = - clPhi (K := K) D l a := by
    intro a ha
    have h := clPhi_mul (K := K) D l ha
      ((Subgroup.normalClosure ({u ^ l} : Set (FreeGroup X))).inv_mem ha)
    rw [mul_inv_cancel, clPhi_one] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  -- The subgroup of elements on which `φ` is equivariant under conjugation.
  let H : Subgroup (FreeGroup X) :=
    { carrier := {t | t ∈ Subgroup.normalClosure ({u ^ l} : Set (FreeGroup X)) ∧
        ∀ f : FreeGroup X, clPhi (K := K) D l (f * t * f⁻¹) =
          MonoidAlgebra.of K _ (presentRho (u ^ l) f) * clPhi (K := K) D l t}
      one_mem' := by
        refine ⟨Subgroup.one_mem _, fun f => ?_⟩
        rw [mul_one, mul_inv_cancel, clPhi_one, mul_zero]
      mul_mem' := by
        rintro t t' ⟨ht, hft⟩ ⟨ht', hft'⟩
        refine ⟨Subgroup.mul_mem _ ht ht', fun f => ?_⟩
        have h1 : f * t * f⁻¹ ∈ Subgroup.normalClosure ({u ^ l} : Set (FreeGroup X)) :=
          (Subgroup.normalClosure_normal (s := ({u ^ l} : Set (FreeGroup X)))).conj_mem t ht f
        have h2 : f * t' * f⁻¹ ∈ Subgroup.normalClosure ({u ^ l} : Set (FreeGroup X)) :=
          (Subgroup.normalClosure_normal (s := ({u ^ l} : Set (FreeGroup X)))).conj_mem t' ht' f
        calc clPhi (K := K) D l (f * (t * t') * f⁻¹)
            = clPhi (K := K) D l ((f * t * f⁻¹) * (f * t' * f⁻¹)) := by
              rw [show f * (t * t') * f⁻¹ = (f * t * f⁻¹) * (f * t' * f⁻¹) from by group]
          _ = clPhi (K := K) D l (f * t * f⁻¹) + clPhi (K := K) D l (f * t' * f⁻¹) :=
              clPhi_mul (K := K) D l h1 h2
          _ = MonoidAlgebra.of K _ (presentRho (u ^ l) f) * clPhi (K := K) D l t +
                MonoidAlgebra.of K _ (presentRho (u ^ l) f) * clPhi (K := K) D l t' := by
              rw [hft f, hft' f]
          _ = MonoidAlgebra.of K _ (presentRho (u ^ l) f) *
                (clPhi (K := K) D l t + clPhi (K := K) D l t') := by rw [mul_add]
          _ = MonoidAlgebra.of K _ (presentRho (u ^ l) f) * clPhi (K := K) D l (t * t') := by
              rw [clPhi_mul (K := K) D l ht ht']
      inv_mem' := by
        rintro t ⟨ht, hft⟩
        refine ⟨Subgroup.inv_mem _ ht, fun f => ?_⟩
        have h1 : f * t * f⁻¹ ∈ Subgroup.normalClosure ({u ^ l} : Set (FreeGroup X)) :=
          (Subgroup.normalClosure_normal (s := ({u ^ l} : Set (FreeGroup X)))).conj_mem t ht f
        calc clPhi (K := K) D l (f * t⁻¹ * f⁻¹)
            = clPhi (K := K) D l ((f * t * f⁻¹)⁻¹) := by
              rw [show f * t⁻¹ * f⁻¹ = (f * t * f⁻¹)⁻¹ from by group]
          _ = - clPhi (K := K) D l (f * t * f⁻¹) := hodd h1
          _ = - (MonoidAlgebra.of K _ (presentRho (u ^ l) f) * clPhi (K := K) D l t) := by
              rw [hft f]
          _ = MonoidAlgebra.of K _ (presentRho (u ^ l) f) * (- clPhi (K := K) D l t) := by
              rw [mul_neg]
          _ = MonoidAlgebra.of K _ (presentRho (u ^ l) f) * clPhi (K := K) D l t⁻¹ := by
              rw [hodd ht] }
  -- `H` contains the relator `u ^ l`.
  have hgen : u ^ l ∈ H := by
    refine ⟨Subgroup.subset_normalClosure (Set.mem_singleton _), fun f => ?_⟩
    have h1 : clPhi (K := K) D l (u ^ l) =
        Work.ORLyndon.normElem K l (presentRho (u ^ l) u) := by
      have h := clPhi_conj_pow (K := K) D l (1 : FreeGroup X)
      rw [one_mul, inv_one, mul_one] at h
      rw [show (MonoidAlgebra.of K (OneRelatorGroup (u ^ l))) (presentRho (u ^ l) 1) = 1
        from map_one _] at h
      simpa using h
    rw [clPhi_conj_pow (K := K) D l f, h1]
  -- `H` is normal, hence contains `⟪u ^ l⟫`.
  have hHnormal : H.Normal :=
    { conj_mem := by
        intro t ht c
        obtain ⟨htN, hft⟩ := ht
        refine ⟨(Subgroup.normalClosure_normal (s := ({u ^ l} : Set (FreeGroup X)))).conj_mem t htN c,
          fun f => ?_⟩
        rw [show f * (c * t * c⁻¹) * f⁻¹ = (f * c) * t * (f * c)⁻¹ from by group, hft (f * c),
          hft c]
        simp only [map_mul, mul_assoc] }
  have hle : Subgroup.normalClosure ({u ^ l} : Set (FreeGroup X)) ≤ H :=
    Subgroup.normalClosure_le_normal (fun t ht => by
      rw [Set.mem_singleton_iff] at ht
      rw [ht]
      exact hgen)
  exact (hle hn).2 f

end Work.ORLyndon.CLDirect
