import Mathlib
import Submission.Work.MotC5N3.ASRulingMainV2Gen
import Submission.Work.MotAS.ASRul.sAS2_ruling_mem
import Submission.Work.MotAS.ASrulV_mem
import Submission.Work.MotAS.ASrulW_mem
import Submission.Work.MotAS.ASRul.kleinMAS_fibre

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.Nodes.ASGen` — Naturality of the AS ruling system under ring homomorphisms (piece 1/6 of the split `ASCertDefsGen`)

This module is one piece of the split of `Submission/Work/MotAS/Nodes/ASCertDefsGen.lean`
(51 KB, `maxHeartbeats 100000000`), which never compiled within the build budget.  The pieces
below 25 KB each with `maxHeartbeats 4000000`; the aggregator `ASCertDefsGen` still exports the
whole `Work.MotAS.Nodes.ASGen` namespace, so no consumer has to change.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotAS.Nodes.ASGen

/-! ## §1  Naturality of the AS ruling system under a ring homomorphism -/

/-- The AS ruling matrix is a polynomial expression in its arguments, hence commutes with any ring
homomorphism. -/
theorem AmatAS2_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (a b g : R) (c : Fin 5 → R) :
    Matrix.map (Work.MotAS.AmatAS2 a b g c) φ
      = Work.MotAS.AmatAS2 (φ a) (φ b) (φ g) (fun j => φ (c j)) := by
  ext i l
  fin_cases i <;> fin_cases l <;>
  · simp only [Matrix.map_apply, Work.MotAS.AmatAS2, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, Matrix.empty_eq, Matrix.of_apply, Matrix.cons_val', Fin.isValue,
      Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one, map_add, map_mul, map_sub, map_neg,
      map_ofNat, map_zero]

/-- A ring homomorphism commutes with the matrix-vector product. -/
theorem mulVec_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (M : Matrix (Fin 5) (Fin 5) R) (y : Fin 5 → R) :
    Matrix.mulVec (Matrix.map M φ) (fun j => φ (y j)) = fun i => φ (Matrix.mulVec M y i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_five, Matrix.map_apply, map_add, map_mul]

/-- **Base change of the ruling system**: if `AmatAS2 a b g c *ᵥ y = 0` then the base change along
`φ` satisfies the same equation. -/
theorem AmatAS2_mulVec_map_zero {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (a b g : R) (c y : Fin 5 → R)
    (h : Matrix.mulVec (Work.MotAS.AmatAS2 a b g c) y = 0) :
    Matrix.mulVec (Work.MotAS.AmatAS2 (φ a) (φ b) (φ g) (fun j => φ (c j)))
      (fun j => φ (y j)) = 0 := by
  have hmap : Matrix.map (Work.MotAS.AmatAS2 a b g c) φ
      = Work.MotAS.AmatAS2 (φ a) (φ b) (φ g) (fun j => φ (c j)) :=
    AmatAS2_map φ a b g c
  rw [← hmap, mulVec_map, h]
  funext i
  simp

/-- **Base change of the ruling system, membership form**: if the image under `φ` of the ruling
system `AmatAS2 a b g c *ᵥ y` vanishes, then so does the base changed system. -/
theorem AmatAS2_map_mulVec_zero {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (a b g : R) (c y : Fin 5 → R)
    (h : (fun i => φ (Matrix.mulVec (Work.MotAS.AmatAS2 a b g c) y i)) = 0) :
    Matrix.mulVec (Work.MotAS.AmatAS2 (φ a) (φ b) (φ g) (fun j => φ (c j)))
      (fun j => φ (y j)) = 0 := by
  have hmap : Matrix.map (Work.MotAS.AmatAS2 a b g c) φ
      = Work.MotAS.AmatAS2 (φ a) (φ b) (φ g) (fun j => φ (c j)) :=
    AmatAS2_map φ a b g c
  rw [← hmap, mulVec_map]
  exact h

/-- The fraction field of a domain of characteristic `p` has characteristic `p`. -/
theorem charP_fractionRing {R : Type*} [CommRing R] [IsDomain R] (p : ℕ) [CharP R p] :
    CharP (FractionRing R) p where
  cast_eq_zero_iff x := by
    have h : ((x : ℕ) : FractionRing R) = algebraMap R (FractionRing R) ((x : ℕ) : R) :=
      (map_natCast (algebraMap R (FractionRing R)) x).symm
    rw [h, ← map_zero (algebraMap R (FractionRing R)),
      (IsFractionRing.injective R (FractionRing R)).eq_iff]
    exact CharP.cast_eq_zero_iff R p x

/-- **The fibre of the AS ruling matrix is one-dimensional** (directional form). -/
theorem kleinMAS_fibre' {K : Type} [Field K] [CharP K 5] (a b g : K) (y c : Fin 5 → K)
    (hy : Work.MotAS.kleinPAS a b g y ≠ 0) (hc : c ≠ 0)
    (hker : Matrix.mulVec (Work.MotAS.ASRul.kleinMAS a b g y) c = 0) :
    ∃ μ : K, μ ≠ 0 ∧ ∀ i, Work.MotAS.kleinPAS a b g y i = μ * c i :=
  (Work.MotAS.ASRul.kleinMAS_fibre K a b g y c hy hc).mp hker

end Work.MotAS.Nodes.ASGen
