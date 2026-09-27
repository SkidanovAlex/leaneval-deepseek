import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic
import Submission.Work.KT.mvN_additive
import Submission.Work.KT.mvN_comm
import Submission.Work.KT.mvN_assoc
import Submission.Work.KT.K0Prod.mulCls_add
import Submission.Work.KT.K0Prod.mulCls_mvN
import Submission.Work.KT.Rank.rank_sum
import Submission.Work.KT.Rank.rank_eq_of_mvN
import Submission.Work.KT.Rank.mvN_one_rank_v2
import Submission.Work.KT.K0map.map_comp
import Submission.Work.KT.K0map.map_id

/-!
# Node `k0_basic`: `K₀` of a commutative ring is a commutative ring, functorially, and `K₀(ℂ) ≅ ℤ`

* Conjunct 1: the product `[p]·[q] := [p ⊗ q]` of `K₀` (Kronecker product of matrices), obtained by
  a double descent of `mulCls` from `FreeAbelianGroup (Mat A)` along the relations `K0Rel`; it is
  commutative, associative, and `[1₁]` is a unit.
* Conjunct 2: naturality of that product (`Work.KT.k0_mul_natural`).
* Conjuncts 3, 4: `K₀` is a functor (`Work.KT.K0map.map_comp`, `Work.KT.K0map.map_id`).
* Conjunct 5: `K₀(ℂ) ≅ ℤ` by the rank of an idempotent (`Work.KT.k0RankEquiv`).
-/

namespace Work.KT

open Matrix
open Classical

noncomputable section

/-! ## Elementary facts about `Mat.one`, `Mat.sum` and `cls` -/

lemma Mat.one_idem (R : Type) [Ring R] (n : ℕ) : (Mat.one R n).IsIdem := by
  unfold Mat.one Mat.IsIdem
  rw [Matrix.mul_one]

/-- `1_m ⊕ 1_n = 1_{m+n}`. -/
lemma Mat.one_sum (R : Type) [Ring R] (m n : ℕ) :
    Mat.sum (Mat.one R m) (Mat.one R n) = Mat.one R (m + n) := by
  unfold Mat.sum Mat.one
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.fromBlocks_one,
    Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · have h' : finSumFinEquiv.symm i ≠ finSumFinEquiv.symm j :=
      fun hh => h (finSumFinEquiv.symm.injective hh)
    simp [h, h']

/-- The class of the `0 × 0` identity matrix vanishes (it is `0 ⊕ 0`). -/
lemma cls_one_zero (R : Type) [Ring R] : cls (Mat.one R 0) = (0 : K0 R) := by
  have h1 : cls (Mat.sum (Mat.one R 0) (Mat.one R 0))
      = cls (Mat.one R 0) + cls (Mat.one R 0) :=
    cls_sum (Mat.one_idem R 0) (Mat.one_idem R 0)
  rw [Mat.one_sum, Nat.add_zero] at h1
  have h2 : cls (Mat.one R 0) + 0 = cls (Mat.one R 0) + cls (Mat.one R 0) := by
    rw [add_zero]
    exact h1
  exact (add_left_cancel h2).symm

/-- `cls (1_r) = r • cls (1₁)`. -/
lemma cls_one_nsmul (R : Type) [Ring R] (r : ℕ) :
    cls (Mat.one R r) = r • cls (Mat.one R 1) := by
  induction r with
  | zero => rw [zero_nsmul, cls_one_zero]
  | succ r ih =>
    rw [← Mat.one_sum R r 1, cls_sum (Mat.one_idem R r) (Mat.one_idem R 1), ih, succ_nsmul]

/-! ## Conjunct 2: naturality of the product on `K₀` -/

/-- Conjunct 2 of `k0_basic` (proved in `Submission/Work/KT/k0_mul_natural_PROOF.txt`). -/
theorem k0_mul_natural (A B : Type) [Ring A] [Ring B] (φ : A →+* B) (μA : K0 A →+ K0 A →+ K0 A)
    (μB : K0 B →+ K0 B →+ K0 B) (hcA : ∀ x y : A, x * y = y * x) (hA : IsK0Mul μA)
    (hB : IsK0Mul μB) :
    ∀ a b, K0.map φ (μA a b) = μB (K0.map φ a) (K0.map φ b) := by
  have hmap : ∀ p : Mat A, K0.map φ (cls p) = mapCls φ p := by
    intro p
    simp only [K0.map, cls, QuotientAddGroup.lift_mk, FreeAbelianGroup.lift_apply_of]
  have hkron : ∀ p q : Mat A, (p.kron q).map φ = (p.map φ).kron (q.map φ) := by
    intro p q
    simp only [Mat.kron, Mat.map, kronMat, Sigma.mk.injEq, heq_eq_eq, true_and]
    ext i j
    simp only [Matrix.map_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.kroneckerMap_apply, map_mul]
    rfl
  have hidem : ∀ p : Mat A, p.IsIdem → (p.map φ).IsIdem := by
    intro p hp
    unfold Mat.IsIdem Mat.map at *
    simp only
    rw [← Matrix.map_mul, hp]
  have hkidem : ∀ p q : Mat A, p.IsIdem → q.IsIdem → (p.kron q).IsIdem := by
    intro p q hp hq
    let _ : CommRing A := { ‹Ring A› with mul_comm := hcA }
    unfold Mat.IsIdem Mat.kron kronMat at *
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
    rw [← Matrix.mul_kronecker_mul, hp, hq]
  -- generators
  have gen : ∀ p q : Mat A, K0.map φ (μA (cls p) (cls q)) =
      μB (K0.map φ (cls p)) (K0.map φ (cls q)) := by
    intro p q
    rw [hA, hmap, hmap]
    by_cases hp : p.IsIdem
    · by_cases hq : q.IsIdem
      · simp only [mulCls, mapCls, if_pos (And.intro hp hq), if_pos hp, if_pos hq]
        rw [hmap, mapCls, if_pos (hkidem p q hp hq), hB, mulCls,
          if_pos (And.intro (hidem p hp) (hidem q hq)), hkron]
      · simp [mulCls, mapCls, hp, hq]
    · simp [mulCls, mapCls, hp]
  intro a b
  induction a using QuotientAddGroup.induction_on with
  | H x =>
  induction b using QuotientAddGroup.induction_on with
  | H y =>
  induction x using FreeAbelianGroup.induction_on with
  | zero => simp
  | of p =>
    induction y using FreeAbelianGroup.induction_on with
    | zero => simp
    | of q => exact gen p q
    | neg q ih => simpa using ih
    | add q r ih1 ih2 => simp only [QuotientAddGroup.mk_add, map_add] at ih1 ih2 ⊢; rw [ih1, ih2]
  | neg p ih => simp only [QuotientAddGroup.mk_neg, map_neg, AddMonoidHom.neg_apply] at ih ⊢; rw [ih]
  | add p r ih1 ih2 =>
    simp only [QuotientAddGroup.mk_add, map_add, AddMonoidHom.add_apply] at ih1 ih2 ⊢; rw [ih1, ih2]

/-! ## The product of `K₀` (conjunct 1) -/

/-- Descent criterion for `K0Rel`: an additive map out of `FreeAbelianGroup (Mat A)` vanishes on the
three families of relations, hence factors through `K₀ A`. -/
lemma K0Rel_le_ker_of {A : Type} [Ring A] {M : Type} [AddCommGroup M]
    (f : FreeAbelianGroup (Mat A) →+ M)
    (h1 : ∀ p q : Mat A, p.IsIdem → q.IsIdem →
      f (FreeAbelianGroup.of (p.sum q)) = f (FreeAbelianGroup.of p) + f (FreeAbelianGroup.of q))
    (h2 : ∀ p q : Mat A, p.IsIdem → q.IsIdem → p.MvN q →
      f (FreeAbelianGroup.of p) = f (FreeAbelianGroup.of q))
    (h3 : ∀ p : Mat A, ¬ p.IsIdem → f (FreeAbelianGroup.of p) = 0) :
    K0Rel A ≤ f.ker := by
  unfold K0Rel
  rw [AddSubgroup.closure_le]
  rintro x ((⟨p, q, hp, hq, rfl⟩ | ⟨p, q, hp, hq, hm, rfl⟩) | ⟨p, hp, rfl⟩)
  · rw [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, map_sub, h1 p q hp hq]
    abel
  · rw [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, sub_eq_zero]
    exact h2 p q hp hq hm
  · rw [SetLike.mem_coe, AddMonoidHom.mem_ker]
    exact h3 p hp

/-- `[p]·[q] = [p ⊗ q]` on idempotents. -/
lemma mulCls_of_idem {A : Type} [Ring A] {p q : Mat A} (hp : p.IsIdem) (hq : q.IsIdem) :
    mulCls p q = cls (p.kron q) := by
  rw [mulCls, if_pos ⟨hp, hq⟩]

/-- `mulCls` vanishes when its first argument is not idempotent. -/
lemma mulCls_of_not_idem_left {A : Type} [Ring A] {p q : Mat A} (hp : ¬ p.IsIdem) :
    mulCls p q = (0 : K0 A) := by
  rw [mulCls, if_neg (fun h => hp h.1)]

/-- `mulCls` vanishes when its second argument is not idempotent. -/
lemma mulCls_of_not_idem_right {A : Type} [Ring A] {p q : Mat A} (hq : ¬ q.IsIdem) :
    mulCls p q = (0 : K0 A) := by
  rw [mulCls, if_neg (fun h => hq h.2)]

/-- `q ↦ mulCls p q` descends to `K₀`. -/
def k0MulInner (A : Type) [Ring A] (hcomm : ∀ x y : A, x * y = y * x) (p : Mat A) :
    K0 A →+ K0 A :=
  QuotientAddGroup.lift (K0Rel A) (FreeAbelianGroup.lift (mulCls p))
    (K0Rel_le_ker_of (FreeAbelianGroup.lift (mulCls p))
      (fun q r hq hr => by
        rw [FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of,
          FreeAbelianGroup.lift_apply_of, (K0Prod.mulCls_add A hcomm).1 p q r hq hr])
      (fun q r hq hr hm => by
        rw [FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of,
          (K0Prod.mulCls_mvN A hcomm).2 p q r hq hr hm])
      (fun q hq => by
        rw [FreeAbelianGroup.lift_apply_of, mulCls_of_not_idem_right hq]))

lemma k0MulInner_cls (A : Type) [Ring A] (hcomm : ∀ x y : A, x * y = y * x) (p q : Mat A) :
    k0MulInner A hcomm p (cls q) = mulCls p q := by
  unfold k0MulInner cls
  rw [QuotientAddGroup.lift_mk, FreeAbelianGroup.lift_apply_of]

/-- A homomorphism out of `K₀` agrees with another one as soon as it does on the `cls p`. -/
lemma k0_ext_cls {A : Type} [Ring A] {F G : K0 A →+ K0 A}
    (h : ∀ p : Mat A, F (cls p) = G (cls p)) : F = G := by
  refine AddMonoidHom.ext fun z => ?_
  induction z using QuotientAddGroup.induction_on with
  | H x =>
  induction x using FreeAbelianGroup.induction_on with
  | zero => simp
  | of p => exact h p
  | neg p ih => simp only [QuotientAddGroup.mk_neg, map_neg, AddMonoidHom.neg_apply] at ih ⊢; rw [ih]
  | add p q ih1 ih2 =>
    simp only [QuotientAddGroup.mk_add, map_add, AddMonoidHom.add_apply] at ih1 ih2 ⊢; rw [ih1, ih2]

lemma k0MulInner_add (A : Type) [Ring A] (hcomm : ∀ x y : A, x * y = y * x) (p q : Mat A)
    (hp : p.IsIdem) (hq : q.IsIdem) :
    k0MulInner A hcomm (p.sum q) = k0MulInner A hcomm p + k0MulInner A hcomm q := by
  refine k0_ext_cls fun r => ?_
  rw [k0MulInner_cls, AddMonoidHom.add_apply, k0MulInner_cls, k0MulInner_cls,
    (K0Prod.mulCls_add A hcomm).2 p q r hp hq]

lemma k0MulInner_mvN (A : Type) [Ring A] (hcomm : ∀ x y : A, x * y = y * x) (p q : Mat A)
    (hp : p.IsIdem) (hq : q.IsIdem) (h : p.MvN q) :
    k0MulInner A hcomm p = k0MulInner A hcomm q := by
  refine k0_ext_cls fun r => ?_
  rw [k0MulInner_cls, k0MulInner_cls, (K0Prod.mulCls_mvN A hcomm).1 p q r hp hq h]

lemma k0MulInner_junk (A : Type) [Ring A] (hcomm : ∀ x y : A, x * y = y * x) (p : Mat A)
    (hp : ¬ p.IsIdem) : k0MulInner A hcomm p = 0 := by
  refine k0_ext_cls fun r => ?_
  rw [k0MulInner_cls, AddMonoidHom.zero_apply, mulCls_of_not_idem_left hp]

/-- The additive map `Mat A → (K₀ A →+ K₀ A)`, `p ↦ (q ↦ [p]·[q])`. -/
abbrev k0MulAux (A : Type) [Ring A] (hcomm : ∀ x y : A, x * y = y * x) :
    FreeAbelianGroup (Mat A) →+ (K0 A →+ K0 A) :=
  FreeAbelianGroup.lift (k0MulInner A hcomm)

lemma k0MulAux_of (A : Type) [Ring A] (hcomm : ∀ x y : A, x * y = y * x) (p : Mat A) :
    k0MulAux A hcomm (FreeAbelianGroup.of p) = k0MulInner A hcomm p :=
  FreeAbelianGroup.lift_apply_of _ p

lemma k0MulAux_add (A : Type) [Ring A] (hcomm : ∀ x y : A, x * y = y * x) (p q : Mat A)
    (hp : p.IsIdem) (hq : q.IsIdem) :
    k0MulAux A hcomm (FreeAbelianGroup.of (p.sum q))
      = k0MulAux A hcomm (FreeAbelianGroup.of p) + k0MulAux A hcomm (FreeAbelianGroup.of q) := by
  rw [k0MulAux_of, k0MulAux_of, k0MulAux_of]
  exact k0MulInner_add A hcomm p q hp hq

lemma k0MulAux_mvN (A : Type) [Ring A] (hcomm : ∀ x y : A, x * y = y * x) (p q : Mat A)
    (hp : p.IsIdem) (hq : q.IsIdem) (h : p.MvN q) :
    k0MulAux A hcomm (FreeAbelianGroup.of p) = k0MulAux A hcomm (FreeAbelianGroup.of q) := by
  rw [k0MulAux_of, k0MulAux_of]
  exact k0MulInner_mvN A hcomm p q hp hq h

lemma k0MulAux_junk (A : Type) [Ring A] (hcomm : ∀ x y : A, x * y = y * x) (p : Mat A)
    (hp : ¬ p.IsIdem) : k0MulAux A hcomm (FreeAbelianGroup.of p) = 0 := by
  rw [k0MulAux_of]
  exact k0MulInner_junk A hcomm p hp

/-- The ring product of `K₀ A`. -/
def k0Mul (A : Type) [Ring A] (hcomm : ∀ x y : A, x * y = y * x) : K0 A →+ K0 A →+ K0 A :=
  QuotientAddGroup.lift (K0Rel A) (k0MulAux A hcomm)
    (K0Rel_le_ker_of (k0MulAux A hcomm)
      (fun p q hp hq => k0MulAux_add A hcomm p q hp hq)
      (fun p q hp hq hm => k0MulAux_mvN A hcomm p q hp hq hm)
      (fun p hp => k0MulAux_junk A hcomm p hp))

/-- The homomorphism `x ↦ [p]·x`. -/
lemma k0Mul_cls_hom (A : Type) [Ring A] (hcomm : ∀ x y : A, x * y = y * x) (p : Mat A) :
    k0Mul A hcomm (cls p) = k0MulInner A hcomm p := by
  unfold k0Mul cls
  rw [QuotientAddGroup.lift_mk, k0MulAux_of]

lemma k0Mul_cls (A : Type) [Ring A] (hcomm : ∀ x y : A, x * y = y * x) (p q : Mat A) :
    k0Mul A hcomm (cls p) (cls q) = mulCls p q := by
  rw [k0Mul_cls_hom, k0MulInner_cls]

lemma k0Mul_isK0Mul (A : Type) [Ring A] (hcomm : ∀ x y : A, x * y = y * x) :
    IsK0Mul (k0Mul A hcomm) := fun p q => k0Mul_cls A hcomm p q

lemma k0Mul_cls_kron (A : Type) [Ring A] (hcomm : ∀ x y : A, x * y = y * x) {p q : Mat A}
    (hp : p.IsIdem) (hq : q.IsIdem) :
    k0Mul A hcomm (cls p) (cls q) = cls (p.kron q) := by
  rw [k0Mul_cls, mulCls_of_idem hp hq]

lemma k0Mul_cls_junk_left (A : Type) [Ring A] (hcomm : ∀ x y : A, x * y = y * x) {p : Mat A}
    (hp : ¬ p.IsIdem) (q : Mat A) : k0Mul A hcomm (cls p) (cls q) = 0 := by
  rw [k0Mul_cls, mulCls_of_not_idem_left hp]

lemma k0Mul_cls_junk_right (A : Type) [Ring A] (hcomm : ∀ x y : A, x * y = y * x) {q : Mat A}
    (hq : ¬ q.IsIdem) (p : Mat A) : k0Mul A hcomm (cls p) (cls q) = 0 := by
  rw [k0Mul_cls, mulCls_of_not_idem_right hq]

lemma k0Mul_comm_gen (A : Type) [Ring A] (hcomm : ∀ x y : A, x * y = y * x) (p q : Mat A) :
    k0Mul A hcomm (cls p) (cls q) = k0Mul A hcomm (cls q) (cls p) := by
  by_cases hp : p.IsIdem
  · by_cases hq : q.IsIdem
    · rw [k0Mul_cls_kron A hcomm hp hq, k0Mul_cls_kron A hcomm hq hp]
      exact cls_eq_of_mvN (Mat.kron_idem hcomm hp hq) (Mat.kron_idem hcomm hq hp)
        (mvN_kron_comm hcomm p q)
    · rw [k0Mul_cls_junk_right A hcomm hq p, k0Mul_cls_junk_left A hcomm hq p]
  · rw [k0Mul_cls_junk_left A hcomm hp q, k0Mul_cls_junk_right A hcomm hp q]

lemma k0Mul_comm (A : Type) [Ring A] (hcomm : ∀ x y : A, x * y = y * x) :
    ∀ a b : K0 A, k0Mul A hcomm a b = k0Mul A hcomm b a := by
  intro a b
  induction a using QuotientAddGroup.induction_on with
  | H x =>
  induction b using QuotientAddGroup.induction_on with
  | H y =>
  induction x using FreeAbelianGroup.induction_on with
  | zero => simp
  | of p =>
    induction y using FreeAbelianGroup.induction_on with
    | zero => simp
    | of q => exact k0Mul_comm_gen A hcomm p q
    | neg q ih =>
      simp only [QuotientAddGroup.mk_neg, map_neg, AddMonoidHom.neg_apply] at ih ⊢; rw [ih]
    | add q r ih1 ih2 =>
      simp only [QuotientAddGroup.mk_add, map_add, AddMonoidHom.add_apply] at ih1 ih2 ⊢
      rw [ih1, ih2]
  | neg p ih => simp only [QuotientAddGroup.mk_neg, map_neg, AddMonoidHom.neg_apply] at ih ⊢; rw [ih]
  | add p r ih1 ih2 =>
    simp only [QuotientAddGroup.mk_add, map_add, AddMonoidHom.add_apply] at ih1 ih2 ⊢
    rw [ih1, ih2]

lemma k0Mul_assoc_gen (A : Type) [Ring A] (hcomm : ∀ x y : A, x * y = y * x) (p q r : Mat A) :
    k0Mul A hcomm (k0Mul A hcomm (cls p) (cls q)) (cls r)
      = k0Mul A hcomm (cls p) (k0Mul A hcomm (cls q) (cls r)) := by
  by_cases hp : p.IsIdem
  · by_cases hq : q.IsIdem
    · by_cases hr : r.IsIdem
      · rw [k0Mul_cls_kron A hcomm hp hq,
          k0Mul_cls_kron A hcomm (Mat.kron_idem hcomm hp hq) hr,
          k0Mul_cls_kron A hcomm hq hr,
          k0Mul_cls_kron A hcomm hp (Mat.kron_idem hcomm hq hr)]
        exact cls_eq_of_mvN (Mat.kron_idem hcomm (Mat.kron_idem hcomm hp hq) hr)
          (Mat.kron_idem hcomm hp (Mat.kron_idem hcomm hq hr)) (mvNassoc_kron_assoc p q r)
      · rw [k0Mul_cls_kron A hcomm hp hq, k0Mul_cls_junk_right A hcomm hr (p.kron q),
          k0Mul_cls_junk_right A hcomm hr q]
        simp
    · rw [k0Mul_cls_junk_right A hcomm hq p, map_zero, k0Mul_cls_junk_left A hcomm hq r]
      simp
  · rw [k0Mul_cls_junk_left A hcomm hp q, map_zero, k0Mul_cls_hom A hcomm p,
      k0MulInner_junk A hcomm p hp]
    simp

lemma k0Mul_assoc (A : Type) [Ring A] (hcomm : ∀ x y : A, x * y = y * x) :
    ∀ a b c : K0 A, k0Mul A hcomm (k0Mul A hcomm a b) c
      = k0Mul A hcomm a (k0Mul A hcomm b c) := by
  have g3 := k0Mul_assoc_gen A hcomm
  have g2 : ∀ (p q : Mat A) (c : K0 A),
      k0Mul A hcomm (k0Mul A hcomm (cls p) (cls q)) c
        = k0Mul A hcomm (cls p) (k0Mul A hcomm (cls q) c) := by
    intro p q c
    induction c using QuotientAddGroup.induction_on with
    | H x =>
    induction x using FreeAbelianGroup.induction_on with
    | zero => simp
    | of r => exact g3 p q r
    | neg r ih =>
      simp only [QuotientAddGroup.mk_neg, map_neg, AddMonoidHom.neg_apply] at ih ⊢; rw [ih]
    | add r s ih1 ih2 =>
      simp only [QuotientAddGroup.mk_add, map_add, AddMonoidHom.add_apply] at ih1 ih2 ⊢
      rw [ih1, ih2]
  have g1 : ∀ (p : Mat A) (b c : K0 A),
      k0Mul A hcomm (k0Mul A hcomm (cls p) b) c
        = k0Mul A hcomm (cls p) (k0Mul A hcomm b c) := by
    intro p b c
    induction b using QuotientAddGroup.induction_on with
    | H y =>
    induction y using FreeAbelianGroup.induction_on with
    | zero => simp
    | of q => exact g2 p q c
    | neg q ih =>
      simp only [QuotientAddGroup.mk_neg, map_neg, AddMonoidHom.neg_apply] at ih ⊢; rw [ih]
    | add q r ih1 ih2 =>
      simp only [QuotientAddGroup.mk_add, map_add, AddMonoidHom.add_apply] at ih1 ih2 ⊢
      rw [ih1, ih2]
  intro a b c
  induction a using QuotientAddGroup.induction_on with
  | H x =>
  induction x using FreeAbelianGroup.induction_on with
  | zero => simp
  | of p => exact g1 p b c
  | neg p ih => simp only [QuotientAddGroup.mk_neg, map_neg, AddMonoidHom.neg_apply] at ih ⊢; rw [ih]
  | add p r ih1 ih2 =>
    simp only [QuotientAddGroup.mk_add, map_add, AddMonoidHom.add_apply] at ih1 ih2 ⊢
    rw [ih1, ih2]

lemma k0Mul_one (A : Type) [Ring A] (hcomm : ∀ x y : A, x * y = y * x) :
    ∀ a : K0 A, k0Mul A hcomm (cls (Mat.one A 1)) a = a := by
  have h : k0Mul A hcomm (cls (Mat.one A 1)) = AddMonoidHom.id (K0 A) := by
    refine k0_ext_cls fun p => ?_
    rw [k0Mul_cls, AddMonoidHom.id_apply]
    by_cases hp : p.IsIdem
    · rw [mulCls_of_idem (Mat.one_idem A 1) hp]
      exact cls_eq_of_mvN (Mat.kron_idem hcomm (Mat.one_idem A 1) hp) hp
        (mvNassoc_kron_unit p)
    · rw [mulCls_of_not_idem_right hp, cls_of_not_idem hp]
  intro a
  rw [h, AddMonoidHom.id_apply]

/-! ## `K₀(ℂ) ≅ ℤ` (conjunct 5) -/

/-- The rank of a matrix, on the generators of `K₀(ℂ)`; zero on non-idempotents. -/
def k0RankGen (p : Mat ℂ) : ℤ := if p.IsIdem then (p.2.rank : ℤ) else 0

lemma k0RankGen_idem {p : Mat ℂ} (hp : p.IsIdem) : k0RankGen p = (p.2.rank : ℤ) :=
  if_pos hp

lemma k0RankGen_sum {p q : Mat ℂ} (hp : p.IsIdem) (hq : q.IsIdem) :
    k0RankGen (p.sum q) = k0RankGen p + k0RankGen q := by
  obtain ⟨n, P⟩ := p
  obtain ⟨m, Q⟩ := q
  have hsum : (Mat.sum (⟨n, P⟩ : Mat ℂ) (⟨m, Q⟩ : Mat ℂ)).IsIdem :=
    Mat.sum_idem (p := (⟨n, P⟩ : Mat ℂ)) (q := (⟨m, Q⟩ : Mat ℂ)) hp hq
  rw [k0RankGen_idem hsum, k0RankGen_idem hp, k0RankGen_idem hq,
    Rank.rank_sum n m P Q]
  push_cast
  ring

lemma k0RankGen_mvN {p q : Mat ℂ} (hp : p.IsIdem) (hq : q.IsIdem) (h : p.MvN q) :
    k0RankGen p = k0RankGen q := by
  obtain ⟨n, P⟩ := p
  obtain ⟨m, Q⟩ := q
  rw [k0RankGen_idem hp, k0RankGen_idem hq, Rank.rank_eq_of_mvN P Q hp hq h]

lemma k0RankGen_junk {p : Mat ℂ} (hp : ¬ p.IsIdem) : k0RankGen p = 0 := by
  simp [k0RankGen, hp]

/-- The rank, as an additive map `K₀(ℂ) → ℤ`. -/
def k0Rank : K0 ℂ →+ ℤ :=
  QuotientAddGroup.lift (K0Rel ℂ) (FreeAbelianGroup.lift k0RankGen)
    (K0Rel_le_ker_of (FreeAbelianGroup.lift k0RankGen)
      (fun p q hp hq => by
        rw [FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of,
          FreeAbelianGroup.lift_apply_of, k0RankGen_sum hp hq])
      (fun p q hp hq hm => by
        rw [FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of,
          k0RankGen_mvN hp hq hm])
      (fun p hp => by
        rw [FreeAbelianGroup.lift_apply_of, k0RankGen_junk hp]))

lemma k0Rank_cls (p : Mat ℂ) : k0Rank (cls p) = k0RankGen p := by
  unfold k0Rank cls
  rw [QuotientAddGroup.lift_mk, FreeAbelianGroup.lift_apply_of]

lemma k0Rank_one (n : ℕ) : k0Rank (cls (Mat.one ℂ n)) = n := by
  rw [k0Rank_cls, k0RankGen_idem (Mat.one_idem ℂ n)]
  show (((1 : Matrix (Fin n) (Fin n) ℂ).rank : ℕ) : ℤ) = (n : ℤ)
  rw [Matrix.rank_one, Fintype.card_fin]

/-- The inverse of the rank: `z ↦ z · [1₁]`. -/
def k0RankInv : ℤ →+ K0 ℂ where
  toFun z := z • cls (Mat.one ℂ 1)
  map_zero' := zero_zsmul _
  map_add' := fun a b => add_zsmul _ a b

lemma k0RankInv_rank (z : K0 ℂ) : k0RankInv (k0Rank z) = z := by
  induction z using QuotientAddGroup.induction_on with
  | H x =>
  induction x using FreeAbelianGroup.induction_on with
  | zero => simp
  | of p =>
    change k0RankInv (k0Rank (cls p)) = cls p
    by_cases hp : p.IsIdem
    · obtain ⟨n, P⟩ := p
      have hcl : cls (⟨n, P⟩ : Mat ℂ) = ((P.rank : ℕ) : ℤ) • cls (Mat.one ℂ 1) := by
        rw [cls_eq_of_mvN hp (Mat.one_idem ℂ P.rank) (Rank.mvN_one_rank_v2 n P hp),
          cls_one_nsmul, natCast_zsmul]
      rw [k0Rank_cls, k0RankGen_idem hp]
      show ((P.rank : ℕ) : ℤ) • cls (Mat.one ℂ 1) = cls (⟨n, P⟩ : Mat ℂ)
      rw [hcl]
    · rw [k0Rank_cls, k0RankGen_junk hp, cls_of_not_idem hp]
      simp
  | neg p ih => simp only [QuotientAddGroup.mk_neg, map_neg, AddMonoidHom.neg_apply] at ih ⊢; rw [ih]
  | add p q ih1 ih2 =>
    simp only [QuotientAddGroup.mk_add, map_add, AddMonoidHom.add_apply] at ih1 ih2 ⊢
    rw [ih1, ih2]

lemma k0RankInv_rank_inv (z : ℤ) : k0Rank (k0RankInv z) = z := by
  change k0Rank (z • cls (Mat.one ℂ 1)) = z
  rw [map_zsmul, k0Rank_one 1]
  simp

/-- `K₀(ℂ) ≅ ℤ` by the rank, sending `[1₁]` to `1`. -/
def k0RankEquiv : K0 ℂ ≃+ ℤ where
  toFun := k0Rank
  invFun := k0RankInv
  left_inv := k0RankInv_rank
  right_inv := k0RankInv_rank_inv
  map_add' := k0Rank.map_add

lemma k0RankEquiv_one : k0RankEquiv (cls (Mat.one ℂ 1)) = 1 := k0Rank_one 1
/-! ## The theorem -/

/-- `K₀` of a commutative ring is a commutative ring with unit `[1₁]`, its product is natural,
`K₀` is a functor, and `K₀(ℂ) ≅ ℤ` by the rank. -/
theorem k0_basic :
    (∀ (A : Type) [Ring A], (∀ x y : A, x * y = y * x) →
      ∃ μ : K0 A →+ K0 A →+ K0 A, IsK0Mul μ ∧ (∀ a b, μ a b = μ b a) ∧
        (∀ a b c, μ (μ a b) c = μ a (μ b c)) ∧ ∀ a, μ (cls (Mat.one A 1)) a = a) ∧
    (∀ (A B : Type) [Ring A] [Ring B], (∀ x y : A, x * y = y * x) →
      ∀ (φ : A →+* B) (μA : K0 A →+ K0 A →+ K0 A)
      (μB : K0 B →+ K0 B →+ K0 B), IsK0Mul μA → IsK0Mul μB →
        ∀ a b, K0.map φ (μA a b) = μB (K0.map φ a) (K0.map φ b)) ∧
    (∀ (A B C : Type) [Ring A] [Ring B] [Ring C] (φ : A →+* B) (ψ : B →+* C),
      K0.map (ψ.comp φ) = (K0.map ψ).comp (K0.map φ)) ∧
    (∀ (A : Type) [Ring A], K0.map (RingHom.id A) = AddMonoidHom.id (K0 A)) ∧
    ∃ e : K0 ℂ ≃+ ℤ, e (cls (Mat.one ℂ 1)) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro A _ hcomm
    exact ⟨k0Mul A hcomm, k0Mul_isK0Mul A hcomm, k0Mul_comm A hcomm, k0Mul_assoc A hcomm,
      k0Mul_one A hcomm⟩
  · intro A B _ _ hcomm φ μA μB hA hB a b
    exact k0_mul_natural A B φ μA μB hcomm hA hB a b
  · intro A B C _ _ _ φ ψ
    exact K0map.map_comp A B C φ ψ
  · intro A _
    exact K0map.map_id A
  · exact ⟨k0RankEquiv, k0RankEquiv_one⟩

end

end Work.KT
