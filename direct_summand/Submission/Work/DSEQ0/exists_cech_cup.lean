import Mathlib
import Submission.Work.DSMap.Map
import Submission.Work.DSEQ0.CupBasic
import Submission.Work.DSEQ0Cup.aw_indices
import Submission.Work.DSEQ0Cup.sum_split_three
import Submission.Work.DSEQ0Cup.unit_cup
import Submission.Work.DSEQ0Cup.assoc_cup_proof

open CategoryTheory AlgebraicGeometry Limits
open Work.DSEQ0.Cup
open scoped Simplicial

namespace Work.DSEQ0

universe a

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Leibniz

variable (A : Type a) [CommRing A] (X : AlgebraicGeometry.Scheme.{a})
  (f : X ⟶ AlgebraicGeometry.Spec (.of A)) {ι : Type a} (U : ι → X.Opens)

/-- the `φ`-component of `x ∈ Čᵐ` inside `Γ(X, sec z)` -/
abbrev tm (m N : ℕ) (z : Fin (N+1) → ι) (φ : Fin (m+1) → Fin (N+1))
    (x : ↥((DSMap.cech A X f U).X m)) : ↥(frame A X f U N z) :=
  (res A X f U z φ).hom ((proj A X f U m (fun i => z (φ i))).hom x)

lemma proj_d_tm (n : ℕ) (z : Fin (n+2) → ι) (x : ↥((DSMap.cech A X f U).X n)) :
    (proj A X f U (n+1) z).hom (((DSMap.cech A X f U).d n (n+1)).hom x)
      = ∑ k : Fin (n+2), (-1 : ℤ) ^ (k:ℕ) • tm A X f U n (n+1) z (deltaMap n k) x := by
  rw [proj_d A X f U n z x]

lemma proj_cup_tm (p q : ℕ) (a : ↥((DSMap.cech A X f U).X p)) (b : ↥((DSMap.cech A X f U).X q))
    (z : Fin (p+q+1) → ι) :
    (proj A X f U (p+q) z).hom ((cup A X f U p q) a b)
      = tm A X f U p (p+q) z (frontIdx p q) a * tm A X f U q (p+q) z (backIdx p q) b := by
  rw [proj_cup_apply A X f U p q a b z, cupComp]

lemma res_comp_apply {m n N : ℕ} (z : Fin (N+1) → ι) (φ : Fin (m+1) → Fin (N+1))
    (ψ : Fin (n+1) → Fin (m+1)) (y : ↥(frame A X f U n (fun i => z (φ (ψ i))))) :
    (res A X f U z φ).hom ((res A X f U (fun i => z (φ i)) ψ).hom y)
      = (res A X f U z (fun k => φ (ψ k))).hom y := by
  have h := congrArg (fun γ => γ.hom y) (res_comp A X f U z φ ψ)
  exact h

lemma tm_res {m n N : ℕ} (z : Fin (N+1) → ι) (φ : Fin (m+1) → Fin (N+1))
    (ψ : Fin (n+1) → Fin (m+1)) (x : ↥((DSMap.cech A X f U).X n)) :
    (res A X f U z φ).hom (tm A X f U n m (fun i => z (φ i)) ψ x)
      = tm A X f U n N z (fun k => φ (ψ k)) x := by
  rw [res_comp_apply]

lemma lhs_eq (p q : ℕ) (a : ↥((DSMap.cech A X f U).X p)) (b : ↥((DSMap.cech A X f U).X q))
    (z : Fin (p+q+2) → ι) :
    (proj A X f U (p+q+1) z).hom
        (((DSMap.cech A X f U).d (p+q) (p+q+1)).hom ((cup A X f U p q) a b))
      = ∑ k : Fin (p+q+2), (-1 : ℤ) ^ (k:ℕ) •
          (tm A X f U p (p+q+1) z (fun i => deltaMap (p+q) k (frontIdx p q i)) a *
           tm A X f U q (p+q+1) z (fun j => deltaMap (p+q) k (backIdx p q j)) b) := by
  rw [proj_d_tm A X f U (p+q) z ((cup A X f U p q) a b)]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [tm]
  rw [proj_cup_tm A X f U p q a b, res_mul, tm_res, tm_res]

lemma tm_d (m N : ℕ) (z : Fin (N+1) → ι) (φ : Fin (m+2) → Fin (N+1))
    (x : ↥((DSMap.cech A X f U).X m)) :
    tm A X f U (m+1) N z φ (((DSMap.cech A X f U).d m (m+1)).hom x)
      = ∑ k : Fin (m+2), (-1 : ℤ) ^ (k:ℕ) •
          tm A X f U m N z (fun i => φ (deltaMap m k i)) x := by
  simp only [tm]
  rw [proj_d A X f U m (fun i => z (φ i)) x]
  simp only [map_sum, map_zsmul, res_comp_apply]

lemma rhs1_eq (p q : ℕ) (a : ↥((DSMap.cech A X f U).X p)) (b : ↥((DSMap.cech A X f U).X q))
    (z : Fin (p+q+2) → ι) :
    (proj A X f U (p+q+1) z).hom
        ((HomologicalComplex.XIsoOfEq (DSMap.cech A X f U) (by omega : (p+1)+q = (p+q)+1)).hom
          ((cup A X f U (p+1) q) (((DSMap.cech A X f U).d p (p+1)).hom a) b))
      = (∑ m : Fin (p+2), (-1 : ℤ) ^ (m:ℕ) •
            tm A X f U p (p+q+1) z
              (fun i => castIdx p q (frontIdx (p+1) q (deltaMap p m i))) a)
        * tm A X f U q (p+q+1) z (fun j => castIdx p q (backIdx (p+1) q j)) b := by
  rw [proj_XIsoOfEq A X f U (by omega : (p+1)+q = (p+q)+1) z
    ((cup A X f U (p+1) q) (((DSMap.cech A X f U).d p (p+1)).hom a) b)]
  rw [proj_cup_tm A X f U (p+1) q (((DSMap.cech A X f U).d p (p+1)).hom a) b]
  rw [res_mul]
  rw [tm_res, tm_res]
  rw [tm_d]

lemma tm_congr {m N : ℕ} {z : Fin (N+1) → ι} {φ ψ : Fin (m+1) → Fin (N+1)} (h : φ = ψ)
    (x : ↥((DSMap.cech A X f U).X m)) :
    tm A X f U m N z φ x = tm A X f U m N z ψ x := by
  subst h
  rfl

lemma rhs2_eq (p q : ℕ) (a : ↥((DSMap.cech A X f U).X p)) (b : ↥((DSMap.cech A X f U).X q))
    (z : Fin (p+q+2) → ι) :
    (proj A X f U (p+q+1) z).hom
        ((cup A X f U p (q+1)) a (((DSMap.cech A X f U).d q (q+1)).hom b))
      = tm A X f U p (p+q+1) z (frontIdx p (q+1)) a
        * (∑ j : Fin (q+2), (-1 : ℤ) ^ (j:ℕ) •
            tm A X f U q (p+q+1) z (fun j' => backIdx p (q+1) (deltaMap q j j')) b) := by
  show (proj A X f U (p+(q+1)) z).hom
        ((cup A X f U p (q+1)) a (((DSMap.cech A X f U).d q (q+1)).hom b)) =
      tm A X f U p (p+(q+1)) z (frontIdx p (q+1)) a
        * (∑ j : Fin (q+2), (-1 : ℤ) ^ (j:ℕ) •
            tm A X f U q (p+(q+1)) z (fun j' => backIdx p (q+1) (deltaMap q j j')) b)
  rw [proj_cup_tm A X f U p (q+1) a (((DSMap.cech A X f U).d q (q+1)).hom b) z]
  rw [tm_d A X f U q (p+(q+1)) z (backIdx p (q+1)) b]

lemma tm_F1 (p q : ℕ) (i : Fin (p+1)) (z : Fin (p+q+2) → ι)
    (a : ↥((DSMap.cech A X f U).X p)) :
    tm A X f U p (p+q+1) z
        (fun i' => deltaMap (p+q) (⟨i.val, by omega⟩ : Fin (p+q+2)) (frontIdx p q i')) a
      = tm A X f U p (p+q+1) z
          (fun i' => castIdx p q (frontIdx (p+1) q (deltaMap p ⟨i.val, by omega⟩ i'))) a :=
  tm_congr A X f U (funext fun i' =>
    (Work.DSEQ0Cup.aw_indices p q).1 (⟨i.val, by omega⟩ : Fin (p+q+2))
      (Nat.le_of_lt_succ i.isLt) i') a

lemma tm_F2 (p q : ℕ) (i : Fin (p+1)) (z : Fin (p+q+2) → ι)
    (b : ↥((DSMap.cech A X f U).X q)) :
    tm A X f U q (p+q+1) z
        (fun j => deltaMap (p+q) (⟨i.val, by omega⟩ : Fin (p+q+2)) (backIdx p q j)) b
      = tm A X f U q (p+q+1) z (fun j => castIdx p q (backIdx (p+1) q j)) b :=
  tm_congr A X f U (funext fun j =>
    (Work.DSEQ0Cup.aw_indices p q).2.1 (⟨i.val, by omega⟩ : Fin (p+q+2))
      (Nat.le_of_lt_succ i.isLt) j) b

lemma tm_F3 (p q : ℕ) (j : Fin (q+1)) (z : Fin (p+q+2) → ι)
    (a : ↥((DSMap.cech A X f U).X p)) :
    tm A X f U p (p+q+1) z
        (fun i => deltaMap (p+q) ⟨p+1+j.val, by omega⟩ (frontIdx p q i)) a
      = tm A X f U p (p+q+1) z (frontIdx p (q+1)) a :=
  tm_congr A X f U (funext fun i => (Work.DSEQ0Cup.aw_indices p q).2.2.1 j i) a

lemma tm_F4 (p q : ℕ) (j : Fin (q+1)) (z : Fin (p+q+2) → ι)
    (b : ↥((DSMap.cech A X f U).X q)) :
    tm A X f U q (p+q+1) z
        (fun j' => deltaMap (p+q) ⟨p+1+j.val, by omega⟩ (backIdx p q j')) b
      = tm A X f U q (p+q+1) z
          (fun j' => backIdx p (q+1) (deltaMap q (Fin.succ j) j')) b :=
  tm_congr A X f U (funext fun j' => (Work.DSEQ0Cup.aw_indices p q).2.2.2.1 j j') b

lemma tm_F5 (p q : ℕ) (z : Fin (p+q+2) → ι) (a : ↥((DSMap.cech A X f U).X p)) :
    tm A X f U p (p+q+1) z
        (fun i => castIdx p q (frontIdx (p+1) q (deltaMap p (Fin.last (p+1)) i))) a
      = tm A X f U p (p+q+1) z (frontIdx p (q+1)) a :=
  tm_congr A X f U (funext fun i => (Work.DSEQ0Cup.aw_indices p q).2.2.2.2.1 i) a

lemma tm_F6 (p q : ℕ) (z : Fin (p+q+2) → ι) (b : ↥((DSMap.cech A X f U).X q)) :
    tm A X f U q (p+q+1) z (fun j => castIdx p q (backIdx (p+1) q j)) b
      = tm A X f U q (p+q+1) z (fun j => backIdx p (q+1) (deltaMap q 0 j)) b :=
  tm_congr A X f U (funext fun j => (Work.DSEQ0Cup.aw_indices p q).2.2.2.2.2 j) b

lemma key (p q : ℕ) (a : ↥((DSMap.cech A X f U).X p)) (b : ↥((DSMap.cech A X f U).X q))
    (z : Fin (p+q+2) → ι) :
    (proj A X f U (p+q+1) z).hom
        (((DSMap.cech A X f U).d (p+q) (p+q+1)).hom ((cup A X f U p q) a b))
      = (proj A X f U (p+q+1) z).hom
          ((HomologicalComplex.XIsoOfEq (DSMap.cech A X f U) (by omega : (p+1)+q = (p+q)+1)).hom
            ((cup A X f U (p+1) q) (((DSMap.cech A X f U).d p (p+1)).hom a) b))
        + (-1 : A) ^ p • (proj A X f U (p+q+1) z).hom
            ((cup A X f U p (q+1)) a (((DSMap.cech A X f U).d q (q+1)).hom b)) := by
  rw [lhs_eq A X f U p q a b z, rhs1_eq A X f U p q a b z, rhs2_eq A X f U p q a b z]
  simp only [← Int.cast_smul_eq_zsmul A, Int.cast_pow, Int.cast_neg, Int.cast_one]
  have hL : (∑ k : Fin (p+q+2), (-1 : A) ^ (k:ℕ) •
        (tm A X f U p (p+q+1) z (fun i => deltaMap (p+q) k (frontIdx p q i)) a *
          tm A X f U q (p+q+1) z (fun j => deltaMap (p+q) k (backIdx p q j)) b))
      = (∑ i : Fin (p+1), (-1 : A) ^ (i:ℕ) •
            tm A X f U p (p+q+1) z
              (fun i' => castIdx p q (frontIdx (p+1) q (deltaMap p ⟨i.val, by omega⟩ i'))) a) *
          tm A X f U q (p+q+1) z (fun j => castIdx p q (backIdx (p+1) q j)) b
        + tm A X f U p (p+q+1) z (frontIdx p (q+1)) a *
            (∑ j' : Fin (q+1), (-1 : A) ^ (p+1+(j':ℕ)) •
              tm A X f U q (p+q+1) z
                (fun j'' => backIdx p (q+1) (deltaMap q (Fin.succ j') j'')) b) := by
    rw [Work.DSEQ0Cup.sum_split_three]
    congr 1
    · trans ∑ i : Fin (p+1), (-1 : A) ^ (i:ℕ) •
          (tm A X f U p (p+q+1) z
              (fun i' => castIdx p q (frontIdx (p+1) q (deltaMap p ⟨i.val, by omega⟩ i'))) a *
            tm A X f U q (p+q+1) z (fun j => castIdx p q (backIdx (p+1) q j)) b)
      · refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        congr 1
        · exact tm_F1 A X f U p q i z a
        · exact tm_F2 A X f U p q i z b
      · rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => (smul_mul_assoc _ _ _).symm
    · trans ∑ j : Fin (q+1), (-1 : A) ^ (p+1+(j:ℕ)) •
          (tm A X f U p (p+q+1) z (frontIdx p (q+1)) a *
            tm A X f U q (p+q+1) z
              (fun j'' => backIdx p (q+1) (deltaMap q (Fin.succ j) j'')) b)
      · refine Finset.sum_congr rfl fun j _ => ?_
        congr 1
        congr 1
        · exact tm_F3 A X f U p q j z a
        · exact tm_F4 A X f U p q j z b
      · rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => (mul_smul_comm _ _ _).symm
  have hR : (∑ m : Fin (p+2), (-1 : A) ^ (m:ℕ) •
        tm A X f U p (p+q+1) z (fun i => castIdx p q (frontIdx (p+1) q (deltaMap p m i))) a) *
      tm A X f U q (p+q+1) z (fun j => castIdx p q (backIdx (p+1) q j)) b
    + (-1 : A) ^ p • (tm A X f U p (p+q+1) z (frontIdx p (q+1)) a *
        ∑ j : Fin (q+2), (-1 : A) ^ (j:ℕ) •
          tm A X f U q (p+q+1) z (fun j' => backIdx p (q+1) (deltaMap q j j')) b)
      = (∑ i : Fin (p+1), (-1 : A) ^ (i:ℕ) •
            tm A X f U p (p+q+1) z
              (fun i' => castIdx p q (frontIdx (p+1) q (deltaMap p ⟨i.val, by omega⟩ i'))) a) *
          tm A X f U q (p+q+1) z (fun j => castIdx p q (backIdx (p+1) q j)) b
        + tm A X f U p (p+q+1) z (frontIdx p (q+1)) a *
            (∑ j' : Fin (q+1), (-1 : A) ^ (p+1+(j':ℕ)) •
              tm A X f U q (p+q+1) z
                (fun j'' => backIdx p (q+1) (deltaMap q (Fin.succ j') j'')) b) := by
    rw [Fin.sum_univ_castSucc (fun m : Fin (p+2) => (-1 : A) ^ (m:ℕ) •
      tm A X f U p (p+q+1) z
        (fun i => castIdx p q (frontIdx (p+1) q (deltaMap p m i))) a)]
    rw [Fin.sum_univ_succ (fun j : Fin (q+2) => (-1 : A) ^ (j:ℕ) •
      tm A X f U q (p+q+1) z (fun j' => backIdx p (q+1) (deltaMap q j j')) b)]
    rw [tm_F5 A X f U p q z a, tm_F6 A X f U p q z b]
    simp only [Fin.castAdd, Fin.castLE, Fin.castSucc, Fin.val_last, Fin.val_zero, Fin.val_succ,
      Fin.le_refl, dif_pos, pow_zero, one_smul]
    have hS' : (-1 : A) ^ p •
          (tm A X f U p (p+q+1) z (frontIdx p (q+1)) a *
            (∑ i : Fin (q+1), (-1 : A) ^ ((i:ℕ) + 1) •
              tm A X f U q (p+q+1) z (fun j' => backIdx p (q+1) (deltaMap q i.succ j')) b))
        = tm A X f U p (p+q+1) z (frontIdx p (q+1)) a *
            (∑ j' : Fin (q+1), (-1 : A) ^ (p + 1 + (j':ℕ)) •
              tm A X f U q (p+q+1) z (fun j'' => backIdx p (q+1) (deltaMap q j'.succ j'')) b) := by
      rw [(mul_smul_comm _ _ _).symm]
      congr 1
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [smul_smul]
      have hpow := pow_add (-1 : A) p ((j':ℕ) + 1)
      rw [← hpow]
      congr 1
      simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    rw [add_mul, smul_mul_assoc, mul_add, smul_add, hS']
    rw [show (-1 : A) ^ (p+1) = -(-1 : A)^p by ring, neg_smul]
    abel

  rw [hL, hR]

end Leibniz

end

theorem exists_cech_cup (A : Type a) [CommRing A] (X : AlgebraicGeometry.Scheme.{a})
    (f : X ⟶ AlgebraicGeometry.Spec (.of A)) {ι : Type a} [Finite ι] (U : ι → X.Opens) :
    ∃ cup : ∀ p q : ℕ, (DSMap.cech A X f U).X p →ₗ[A] (DSMap.cech A X f U).X q →ₗ[A]
        (DSMap.cech A X f U).X (p + q),
      (∀ (p q : ℕ) (a : ↥((DSMap.cech A X f U).X p)) (b : ↥((DSMap.cech A X f U).X q)),
        ((DSMap.cech A X f U).d (p + q) (p + q + 1)).hom ((cup p q) a b)
          = ((DSMap.cech A X f U).XIsoOfEq (by omega : (p + 1) + q = (p + q) + 1)).hom
              ((cup (p + 1) q) (((DSMap.cech A X f U).d p (p + 1)).hom a) b)
            + (-1 : A) ^ p • (cup p (q + 1)) a (((DSMap.cech A X f U).d q (q + 1)).hom b)) ∧
      (∀ (q : ℕ) (b : ↥((DSMap.cech A X f U).X q)),
        ((DSMap.cech A X f U).XIsoOfEq (Nat.zero_add q)).hom
          ((cup 0 q) ((DSMap.coaug0 A X f U).hom 1) b) = b) ∧
      (∀ (p q r : ℕ) (a : ↥((DSMap.cech A X f U).X p)) (b : ↥((DSMap.cech A X f U).X q))
        (c : ↥((DSMap.cech A X f U).X r)),
        ((DSMap.cech A X f U).XIsoOfEq (by omega : (p + q) + r = p + (q + r))).hom
            ((cup (p + q) r) ((cup p q) a b) c)
          = (cup p (q + r)) a ((cup q r) b c)) := by
  refine ⟨fun p q => Work.DSEQ0.Cup.cup A X f U p q, ?_, ?_, ?_⟩
  · intro p q a b
    apply Work.DSEQ0.Cup.proj_ext A X f U
    intro z
    rw [map_add, map_smul]
    exact Leibniz.key A X f U p q a b z
  · intro q b
    exact Work.DSEQ0Cup.unit_cup A X f U q b
  · intro p q r a b c
    exact Work.DSEQ0Cup.assoc_cup_proof A X f U p q r a b c

end Work.DSEQ0
