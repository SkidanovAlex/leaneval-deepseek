/-
The isotropic points of the Hermitian plane (the Hermitian curve) and the action of
`SU(3, 2^n)` on them.

`PG n = ℙ (F n) (Fin 3 → F n)` is the projective plane; a point is *isotropic* when one
(equivalently every) representing vector satisfies `IsIsoVec`.  We set up the action of
`SU(3,2^n)` on the type `suIsoPt n` of isotropic points and establish transitivity, the
point stabiliser `[e_0]` (= the Borel subgroup `B`) and the fact that the unipotent radical
`U` is transitive on the isotropic points other than `[e_0]`.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.PSU3.Stabilizer
import Mathlib.LinearAlgebra.Projectivization.Action

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.unnecessarySeqFocus false

open Matrix LeanEval.GroupTheory.Defs
open scoped LinearAlgebra.Projectivization

namespace Submission.PSU3

/-- The Frobenius conjugate of a vector over `GF(2^(2n))`. -/
noncomputable def hermV (n : ℕ) (v : Fin 3 → F n) : Fin 3 → F n := fun i => v i ^ (2 ^ n)

lemma isIsoVec_iff (n : ℕ) (v : Fin 3 → F n) :
    IsIsoVec n v ↔ (hermV n v) ⬝ᵥ (J3 *ᵥ v) = 0 := by
  have h : (hermV n v) ⬝ᵥ (J3 *ᵥ v) =
      v 0 ^ (2 ^ n) * v 2 + v 1 ^ (2 ^ n + 1) + v 2 ^ (2 ^ n) * v 0 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    simp only [hermV, J3, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.of_apply]
    rw [pow_succ]; ring
  rw [h, IsIsoVec]

lemma hermV_mulVec (n : ℕ) (M : Matrix (Fin 3) (Fin 3) (F n)) (v : Fin 3 → F n) :
    hermV n (M *ᵥ v) = hermV n v ᵥ* herm M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  ext j
  simp only [hermV, herm, Matrix.vecMul, dotProduct, Matrix.mulVec, Matrix.of_apply,
    Fin.sum_univ_three]
  rw [show (M j 0 * v 0 + M j 1 * v 1 + M j 2 * v 2) =
      (M j 0 * v 0 + M j 1 * v 1) + M j 2 * v 2 by ring,
    add_pow_char_pow, add_pow_char_pow, mul_pow, mul_pow, mul_pow]
  ring

/-- A form-preserving matrix preserves isotropy. -/
lemma isIsoVec_mulVec_iff (n : ℕ) (M : Matrix (Fin 3) (Fin 3) (F n))
    (hM : herm M * J3 * M = J3) (v : Fin 3 → F n) :
    IsIsoVec n (M *ᵥ v) ↔ IsIsoVec n v := by
  rw [isIsoVec_iff, isIsoVec_iff, hermV_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]

/-! ## Isotropic projective points -/

/-- The projective plane over `F n`. -/
abbrev PG (n : ℕ) : Type := Projectivization (F n) (Fin 3 → F n)

lemma suE0_ne_zero (n : ℕ) : suE0 n ≠ 0 := by
  intro h
  have hh := congrFun h 0
  simp [suE0] at hh

lemma suE0_iso (n : ℕ) : IsIsoVec n (suE0 n) := by
  rw [IsIsoVec]; simp [suE0]

lemma vInf_iso (n : ℕ) : IsIsoVec n (![0, 0, 1] : Fin 3 → F n) := by
  rw [IsIsoVec]; simp

lemma vInf_ne_zero (n : ℕ) : (![0, 0, 1] : Fin 3 → F n) ≠ 0 := by
  intro h
  have hh := congrFun h 2
  simp at hh

/-- The point `[e_0]`. -/
noncomputable def pE0 (n : ℕ) : PG n :=
  Projectivization.mk (F n) (suE0 n) (suE0_ne_zero n)

/-- The point at infinity `[(0,0,1)]`. -/
noncomputable def pInf (n : ℕ) : PG n :=
  Projectivization.mk (F n) (![0, 0, 1] : Fin 3 → F n) (vInf_ne_zero n)

/-- A projective point is isotropic if some (equivalently every) representative is. -/
def IsIsoPt (n : ℕ) (p : PG n) : Prop := IsIsoVec n p.rep

lemma isIsoPt_mk_iff {n : ℕ} {v w : Fin 3 → F n} (hv : v ≠ 0) (hw : w ≠ 0)
    (h : Projectivization.mk (F n) v hv = Projectivization.mk (F n) w hw) :
    IsIsoVec n v ↔ IsIsoVec n w := by
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' (F n) v w hv hw).mp h
  have ha' : a ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at ha
    exact hv ha.symm
  have hthis := isIsoVec_smul_iff n w ha'
  rw [ha] at hthis
  exact hthis

lemma isIsoPt_mk {n : ℕ} (v : Fin 3 → F n) (hv : v ≠ 0) :
    IsIsoPt n (Projectivization.mk (F n) v hv) ↔ IsIsoVec n v :=
  isIsoPt_mk_iff (Projectivization.rep_nonzero _) hv
    (Projectivization.mk_rep (Projectivization.mk (F n) v hv))

lemma isIsoPt_pE0 (n : ℕ) : IsIsoPt n (pE0 n) :=
  (isIsoPt_mk (suE0 n) (suE0_ne_zero n)).mpr (suE0_iso n)

lemma isIsoPt_pInf (n : ℕ) : IsIsoPt n (pInf n) :=
  (isIsoPt_mk (![0, 0, 1] : Fin 3 → F n) (vInf_ne_zero n)).mpr (vInf_iso n)

/-- `mk` with the same vector and different nonzero proofs. -/
lemma mk_proof_irrel {n : ℕ} {v : Fin 3 → F n} (h1 h2 : v ≠ 0) :
    Projectivization.mk (F n) v h1 = Projectivization.mk (F n) v h2 :=
  (Projectivization.mk_eq_mk_iff' (F n) v v h1 h2).mpr ⟨1, by rw [one_smul]⟩

/-- The action of `SU(3,2^n)` on a point, in terms of a representative. -/
lemma smul_eq_mk (n : ℕ) (g : ↥(SU3 n)) (p : PG n) :
    ∃ (h : ((g : GL (Fin 3) (F n)) • p.rep) ≠ 0),
      g • p = Projectivization.mk (F n) ((g : GL (Fin 3) (F n)) • p.rep) h := by
  refine ⟨?_, ?_⟩
  · intro h
    apply Projectivization.rep_nonzero p
    have h2 := congrArg (fun x => ((g : GL (Fin 3) (F n)))⁻¹ • x) h
    simpa using h2
  · conv_lhs => rw [show g • p = (g : GL (Fin 3) (F n)) • p from rfl,
      ← Projectivization.mk_rep p]
    rw [Projectivization.smul_mk]

/-- Isotropy is preserved by the action of `SU(3, 2^n)`. -/
lemma isIsoPt_smul {n : ℕ} (g : ↥(SU3 n)) {p : PG n} (hp : IsIsoPt n p) :
    IsIsoPt n (g • p) := by
  have hgform : herm ((g : GL (Fin 3) (F n)) : Matrix (Fin 3) (Fin 3) (F n)) * J3 *
      ((g : GL (Fin 3) (F n)) : Matrix (Fin 3) (Fin 3) (F n)) = J3 := g.2.1
  have hne : ((g : GL (Fin 3) (F n)) : GL (Fin 3) (F n)) • p.rep ≠ 0 := by
    intro h
    apply Projectivization.rep_nonzero p
    have h2 := congrArg (fun x => ((g : GL (Fin 3) (F n)))⁻¹ • x) h
    simpa using h2
  obtain ⟨hsm, hmk⟩ := smul_eq_mk n g p
  have e1 : IsIsoVec n (Projectivization.rep (g • p)) ↔
      IsIsoVec n ((g : GL (Fin 3) (F n)) • p.rep) :=
    isIsoPt_mk_iff (Projectivization.rep_nonzero (g • p)) hne
      ((Projectivization.mk_rep (g • p)).trans hmk)
  have e2 : IsIsoVec n ((g : GL (Fin 3) (F n)) • p.rep) ↔ IsIsoVec n p.rep :=
    isIsoVec_mulVec_iff n ((g : GL (Fin 3) (F n)) : Matrix (Fin 3) (Fin 3) (F n)) hgform p.rep
  show IsIsoVec n (Projectivization.rep (g • p))
  exact (e1.trans e2).mpr hp

/-- The type of isotropic projective points. -/
abbrev suIsoPt (n : ℕ) : Type := {p : PG n // IsIsoPt n p}

noncomputable instance (n : ℕ) : MulAction ↥(SU3 n) (suIsoPt n) where
  smul g p := ⟨g • p.1, isIsoPt_smul g p.2⟩
  one_smul p := Subtype.ext (one_smul _ p.1)
  mul_smul g h p := Subtype.ext (mul_smul g h p.1)

lemma suIsoPt_smul_def (n : ℕ) (g : ↥(SU3 n)) (p : suIsoPt n) :
    (g • p).1 = g • p.1 := rfl

/-- The isotropic point `[e_0]`. -/
noncomputable def pE0' (n : ℕ) : suIsoPt n := ⟨pE0 n, isIsoPt_pE0 n⟩

/-- The isotropic point at infinity. -/
noncomputable def pInf' (n : ℕ) : suIsoPt n := ⟨pInf n, isIsoPt_pInf n⟩

lemma pE0'_val (n : ℕ) : (pE0' n).1 = pE0 n := rfl
lemma pInf'_val (n : ℕ) : (pInf' n).1 = pInf n := rfl

/-- The action on `pE0`, in terms of `suE0`. -/
lemma smul_pE0 (n : ℕ) (g : ↥(SU3 n)) :
    ∃ (h : (g : GL (Fin 3) (F n)) • suE0 n ≠ 0),
      g • pE0 n = Projectivization.mk (F n) ((g : GL (Fin 3) (F n)) • suE0 n) h := by
  refine ⟨?_, ?_⟩
  · intro hh
    have h2 : ((g : GL (Fin 3) (F n)))⁻¹ • ((g : GL (Fin 3) (F n)) • suE0 n) = suE0 n := by
      rw [← mul_smul, inv_mul_cancel, one_smul]
    rw [hh, smul_zero] at h2
    exact suE0_ne_zero n h2.symm
  · conv_lhs => rw [show g • pE0 n = (g : GL (Fin 3) (F n)) • pE0 n from rfl]
    rw [pE0, Projectivization.smul_mk]

/-! ## Transitivity of `SU(3,2^n)` on the isotropic points -/

theorem suIsoPt_isPretransitive (n : ℕ) :
    MulAction.IsPretransitive ↥(SU3 n) (suIsoPt n) := by
  refine ⟨fun p q => ?_⟩
  obtain ⟨A, hA, hAv⟩ := su3_exists_mulVec_suE0_eq n p.1.rep p.2 p.1.rep_nonzero
  obtain ⟨B, hB, hBv⟩ := su3_exists_mulVec_suE0_eq n q.1.rep q.2 q.1.rep_nonzero
  have hAinv : ((A⁻¹ : GL (Fin 3) (F n)) : Matrix (Fin 3) (Fin 3) (F n)) *ᵥ p.1.rep = suE0 n := by
    rw [← hAv, Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
  have hBA : (((B : GL (Fin 3) (F n))) * (A : GL (Fin 3) (F n))⁻¹ : GL (Fin 3) (F n)) *ᵥ p.1.rep
      = q.1.rep := by
    rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hAinv, hBv]
  set g : ↥(SU3 n) := (⟨B, hB⟩ : ↥(SU3 n)) * (⟨A, hA⟩ : ↥(SU3 n))⁻¹ with hg
  refine ⟨g, ?_⟩
  apply Subtype.ext
  rw [suIsoPt_smul_def]
  obtain ⟨hsm, hmk⟩ := smul_eq_mk n g p.1
  rw [hmk, ← Projectivization.mk_rep q.1]
  refine (Projectivization.mk_eq_mk_iff' (F n) _ _ hsm
    (Projectivization.rep_nonzero q.1)).mpr ⟨1, ?_⟩
  rw [one_smul]
  show q.1.rep = ((g : GL (Fin 3) (F n)) : Matrix (Fin 3) (Fin 3) (F n)) *ᵥ p.1.rep
  rw [hg]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact hBA.symm

/-! ## The stabiliser of `[e_0]` is the Borel subgroup -/

theorem stabilizer_pE0 (n : ℕ) :
    MulAction.stabilizer ↥(SU3 n) (pE0' n) = (suB n).subgroupOf (SU3 n) := by
  ext g
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have h1 : g • pE0 n = pE0 n := congrArg Subtype.val h
    obtain ⟨hsm, hmk⟩ := smul_pE0 n g
    rw [hmk, pE0] at h1
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' (F n)
      ((g : GL (Fin 3) (F n)) • suE0 n) (suE0 n)
      hsm (suE0_ne_zero n)).mp h1
    have ha' : a ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at ha
      exact hsm ha.symm
    exact (mem_suB_iff_smul n (g : GL (Fin 3) (F n)) g.2).mpr ⟨a, ha', ha.symm⟩
  · intro hg
    apply Subtype.ext
    show g • pE0 n = pE0 n
    obtain ⟨x, hx, hxeq⟩ := (mem_suB_iff_smul n (g : GL (Fin 3) (F n)) g.2).mp hg
    obtain ⟨hsm, hmk⟩ := smul_pE0 n g
    rw [hmk, pE0]
    exact (Projectivization.mk_eq_mk_iff' (F n)
      ((g : GL (Fin 3) (F n)) • suE0 n) (suE0 n)
      hsm (suE0_ne_zero n)).mpr ⟨x, hxeq.symm⟩

end Submission.PSU3
