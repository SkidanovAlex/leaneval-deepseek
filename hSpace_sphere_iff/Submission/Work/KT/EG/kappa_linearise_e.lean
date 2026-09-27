import Mathlib
import Submission.Work.KT.EG.kappa_linearise_defs
import Submission.Work.KT.EG.kappa_linearise_b
import Submission.Work.KT.EG.kappa_linearise_c
import Submission.Work.KT.EG.kappa_linearise_d
import Submission.Work.KT.Fund.kappa_add
import Submission.Work.KT.Fund.kappa_one
import Submission.Work.KT.k0_basic

/-!
# `Work.KT.EG.kappa_linearise_e` — the homotopy through units and the linearisation theorem
-/

namespace Work.KT.EG

open Matrix

noncomputable section

variable (X : Type) [TopologicalSpace X]

/-! ## 1. Slicing matrices over the cylinder -/

/-- Restriction of functions on the cylinder to a slice, as a ring homomorphism. -/
def sliceHom (X : Type) [TopologicalSpace X]
    (e : C(X × Sph ℂ, (X × unitInterval) × Sph ℂ)) :
    C((X × unitInterval) × Sph ℂ, ℂ) →+* C(X × Sph ℂ, ℂ) where
  toFun f := f.comp e
  map_one' := by ext p; rfl
  map_mul' f g := by ext p; rfl
  map_zero' := by ext p; rfl
  map_add' f g := by ext p; rfl

/-- The `e`-slice of a matrix over the cylinder. -/
abbrev sliceMat {ι κ : Type} (e : C(X × Sph ℂ, (X × unitInterval) × Sph ℂ))
    (M : Matrix ι κ C((X × unitInterval) × Sph ℂ, ℂ)) : Matrix ι κ C(X × Sph ℂ, ℂ) :=
  M.map ⇑(sliceHom X e)

@[simp] lemma sliceMat_apply {ι κ : Type} (e : C(X × Sph ℂ, (X × unitInterval) × Sph ℂ))
    (M : Matrix ι κ C((X × unitInterval) × Sph ℂ, ℂ)) (i : ι) (j : κ) (p : X × Sph ℂ) :
    sliceMat X e M i j p = M i j (e p) := rfl

section Slice

variable {ι κ : Type} (e : C(X × Sph ℂ, (X × unitInterval) × Sph ℂ))

lemma sliceMat_add (M N : Matrix ι κ C((X × unitInterval) × Sph ℂ, ℂ)) :
    sliceMat X e (M + N) = sliceMat X e M + sliceMat X e N := by
  funext i j
  show (sliceHom X e) (M i j + N i j) = (sliceHom X e) (M i j) + (sliceHom X e) (N i j)
  rw [map_add]

lemma sliceMat_neg (M : Matrix ι κ C((X × unitInterval) × Sph ℂ, ℂ)) :
    sliceMat X e (-M) = -sliceMat X e M := by
  funext i j
  show (sliceHom X e) (-(M i j)) = -((sliceHom X e) (M i j))
  rw [map_neg]

lemma sliceMat_zero : sliceMat X e (0 : Matrix ι κ C((X × unitInterval) × Sph ℂ, ℂ)) = 0 := by
  funext i j
  show (sliceHom X e) (0 : C((X × unitInterval) × Sph ℂ, ℂ)) = 0
  rw [map_zero]

lemma sliceMat_one [Fintype ι] [DecidableEq ι] :
    sliceMat X e (1 : Matrix ι ι C((X × unitInterval) × Sph ℂ, ℂ)) = 1 := by
  change (RingHom.mapMatrix (sliceHom X e)) (1 : Matrix ι ι C((X × unitInterval) × Sph ℂ, ℂ))
    = 1
  exact map_one _

lemma sliceMat_mul [Fintype ι] [DecidableEq ι]
    (M N : Matrix ι ι C((X × unitInterval) × Sph ℂ, ℂ)) :
    sliceMat X e (M * N) = sliceMat X e M * sliceMat X e N := by
  change (RingHom.mapMatrix (sliceHom X e)) (M * N)
    = (RingHom.mapMatrix (sliceHom X e)) M * (RingHom.mapMatrix (sliceHom X e)) N
  exact map_mul _ _ _

lemma sliceMat_pow [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι C((X × unitInterval) × Sph ℂ, ℂ)) (k : ℕ) :
    sliceMat X e (M ^ k) = (sliceMat X e M) ^ k := by
  change (RingHom.mapMatrix (sliceHom X e)) (M ^ k)
    = ((RingHom.mapMatrix (sliceHom X e)) M) ^ k
  exact map_pow _ _ _

lemma sliceMat_sum [Fintype ι] [DecidableEq ι] {ι' : Type} (s : Finset ι')
    (f : ι' → Matrix ι ι C((X × unitInterval) × Sph ℂ, ℂ)) :
    sliceMat X e (∑ i ∈ s, f i) = ∑ i ∈ s, sliceMat X e (f i) := by
  change (RingHom.mapMatrix (sliceHom X e)) (∑ i ∈ s, f i)
    = ∑ i ∈ s, (RingHom.mapMatrix (sliceHom X e)) (f i)
  exact map_sum _ _ _

lemma sliceMat_smul (a : C((X × unitInterval) × Sph ℂ, ℂ))
    (M : Matrix ι κ C((X × unitInterval) × Sph ℂ, ℂ)) :
    sliceMat X e (a • M) = (sliceHom X e) a • sliceMat X e M := by
  funext i j
  show (sliceHom X e) (a * M i j) = (sliceHom X e) a * (sliceHom X e) (M i j)
  rw [map_mul]

lemma sliceMat_fromBlocks {n l o p : Type} (A : Matrix n l C((X × unitInterval) × Sph ℂ, ℂ))
    (B : Matrix n p C((X × unitInterval) × Sph ℂ, ℂ))
    (C : Matrix o l C((X × unitInterval) × Sph ℂ, ℂ))
    (D : Matrix o p C((X × unitInterval) × Sph ℂ, ℂ)) :
    sliceMat X e (Matrix.fromBlocks A B C D)
      = Matrix.fromBlocks (sliceMat X e A) (sliceMat X e B)
          (sliceMat X e C) (sliceMat X e D) := by
  show (Matrix.fromBlocks A B C D).map ⇑(sliceHom X e) = _
  rw [Matrix.fromBlocks_map]

end Slice

@[simp] lemma sliceHom_incl0_tCyl :
    sliceHom X (Work.KT.Fund.incl0 X) (tCyl_kld X) = 0 := by
  ext p
  rfl

@[simp] lemma sliceHom_incl1_tCyl :
    sliceHom X (Work.KT.Fund.incl1 X) (tCyl_kld X) = 1 := by
  ext p
  rfl

@[simp] lemma sliceHom_incl0_zCyl :
    sliceHom X (Work.KT.Fund.incl0 X) (zCyl_kld X) = (Work.KT.zUnit X : C(X × Sph ℂ, ℂ)) := by
  ext p
  rfl

@[simp] lemma sliceHom_incl1_zCyl :
    sliceHom X (Work.KT.Fund.incl1 X) (zCyl_kld X) = (Work.KT.zUnit X : C(X × Sph ℂ, ℂ)) := by
  ext p
  rfl

lemma sliceMat_pullCyl (e : C(X × Sph ℂ, (X × unitInterval) × Sph ℂ))
    (he : ∀ p, projCylS X (e p) = p) {ι κ : Type}
    (M : Matrix ι κ C(X × Sph ℂ, ℂ)) : sliceMat X e (pullCyl X M) = M := by
  funext i j
  refine ContinuousMap.ext (fun p => ?_)
  show (M i j) (projCylS X (e p)) = (M i j) p
  rw [he p]

lemma sliceMat_AmatCyl (e : C(X × Sph ℂ, (X × unitInterval) × Sph ℂ))
    (he : ∀ p, projCylS X (e p) = p) {m : ℕ} (N : ℕ)
    (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ))) :
    sliceMat X e (AmatCyl X N q) = Amat X N q :=
  sliceMat_pullCyl X e he (Amat X N q)

lemma zero_smul_mat {ι κ : Type} (M : Matrix ι κ C(X × Sph ℂ, ℂ)) :
    (0 : C(X × Sph ℂ, ℂ)) • M = 0 := by
  funext i j
  show (0 : C(X × Sph ℂ, ℂ)) * M i j = 0
  rw [zero_mul]

lemma one_smul_mat {ι κ : Type} (M : Matrix ι κ C(X × Sph ℂ, ℂ)) :
    (1 : C(X × Sph ℂ, ℂ)) • M = M := by
  funext i j
  show (1 : C(X × Sph ℂ, ℂ)) * M i j = M i j
  rw [one_mul]

lemma sliceMat_shCyl (e : C(X × Sph ℂ, (X × unitInterval) × Sph ℂ)) (N m : ℕ) :
    sliceMat X e (shCyl X N m : Matrix (BIdx N m) (BIdx N m)
        C((X × unitInterval) × Sph ℂ, ℂ)) = shC X N m := by
  funext i j
  show (sliceHom X e) ((if BIdx.st i < N then
        (if j = BIdx.nx i then (1 : C((X × unitInterval) × Sph ℂ, ℂ)) else 0) else 0))
      = (if BIdx.st i < N then (if j = BIdx.nx i then (1 : C(X × Sph ℂ, ℂ)) else 0) else 0)
  by_cases h : BIdx.st i < N
  · rw [if_pos h, if_pos h]
    by_cases h2 : j = BIdx.nx i
    · rw [if_pos h2, if_pos h2, map_one]
    · rw [if_neg h2, if_neg h2, map_zero]
  · rw [if_neg h, if_neg h, map_zero]

lemma sliceMat_RmatCyl_incl0 (N m : ℕ) :
    sliceMat X (Work.KT.Fund.incl0 X) (RmatCyl X N : Matrix (BIdx N m) (BIdx N m)
      C((X × unitInterval) × Sph ℂ, ℂ)) = 1 := by
  have hp : (sliceHom X (Work.KT.Fund.incl0 X)) (tCyl_kld X * zCyl_kld X) = 0 := by
    rw [map_mul, sliceHom_incl0_tCyl, sliceHom_incl0_zCyl, zero_mul]
  have hzero : ∀ k ∈ Finset.range (N + 1), k ≠ 0 →
      sliceMat X (Work.KT.Fund.incl0 X)
        ((tCyl_kld X * zCyl_kld X) ^ k • (shCyl X N m) ^ k) = 0 := by
    intro k _ hk
    simp only [sliceMat_smul, sliceMat_pow, sliceMat_shCyl, map_pow, hp, zero_pow hk,
      zero_smul_mat]
  have hmem : (0 : ℕ) ∉ Finset.range (N + 1) → sliceMat X (Work.KT.Fund.incl0 X)
      ((tCyl_kld X * zCyl_kld X) ^ 0 • (shCyl X N m) ^ 0) = 0 := by
    intro hh
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos N)) hh
  rw [RmatCyl, sliceMat_sum, Finset.sum_eq_single (0 : ℕ) hzero hmem]
  simp only [sliceMat_smul, sliceMat_pow, sliceMat_shCyl, map_pow, hp, pow_zero, one_smul_mat,
    sliceMat_one]

lemma sliceMat_RmatCyl_incl1 (N m : ℕ) :
    sliceMat X (Work.KT.Fund.incl1 X) (RmatCyl X N : Matrix (BIdx N m) (BIdx N m)
      C((X × unitInterval) × Sph ℂ, ℂ)) = Rmat X N := by
  have hp : (sliceHom X (Work.KT.Fund.incl1 X)) (tCyl_kld X * zCyl_kld X) = zc X := by
    rw [map_mul, sliceHom_incl1_tCyl, sliceHom_incl1_zCyl, one_mul]
  rw [RmatCyl, Rmat, sliceMat_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [sliceMat_smul, sliceMat_pow, sliceMat_shCyl, map_pow, hp]

/-! ## 2. The units over the cylinder -/

/-- The inverse of `LmatCyl`. -/
def uRowInvCyl {m : ℕ} (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ))) :
    Matrix (BIdx N m) (BIdx N m) C((X × unitInterval) × Sph ℂ, ℂ) :=
  (Matrix.fromBlocks (1 : Matrix (Fin N × Fin m) (Fin N × Fin m)
      C((X × unitInterval) × Sph ℂ, ℂ)) 0
    (tCyl_kld X • RowMCyl X N q) (1 : Matrix (Fin m) (Fin m) C((X × unitInterval) × Sph ℂ, ℂ)) :
      Matrix (BIdx N m) (BIdx N m) C((X × unitInterval) × Sph ℂ, ℂ))

lemma LmatCyl_mul_uRowInvCyl {m : ℕ} (N : ℕ)
    (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ))) :
    LmatCyl X N q * uRowInvCyl X N q = 1 := by
  show (Matrix.fromBlocks (1 : Matrix (Fin N × Fin m) (Fin N × Fin m)
        C((X × unitInterval) × Sph ℂ, ℂ)) 0
      (-(tCyl_kld X • RowMCyl X N q))
      (1 : Matrix (Fin m) (Fin m) C((X × unitInterval) × Sph ℂ, ℂ)))
    * (Matrix.fromBlocks (1 : Matrix (Fin N × Fin m) (Fin N × Fin m)
        C((X × unitInterval) × Sph ℂ, ℂ)) 0
      (tCyl_kld X • RowMCyl X N q)
      (1 : Matrix (Fin m) (Fin m) C((X × unitInterval) × Sph ℂ, ℂ))) = 1
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,
    Matrix.neg_mul, neg_add_cancel, neg_zero, Matrix.fromBlocks_one]

lemma uRowInvCyl_mul_LmatCyl {m : ℕ} (N : ℕ)
    (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ))) :
    uRowInvCyl X N q * LmatCyl X N q = 1 := by
  show (Matrix.fromBlocks (1 : Matrix (Fin N × Fin m) (Fin N × Fin m)
        C((X × unitInterval) × Sph ℂ, ℂ)) 0
      (tCyl_kld X • RowMCyl X N q)
      (1 : Matrix (Fin m) (Fin m) C((X × unitInterval) × Sph ℂ, ℂ)))
    * (Matrix.fromBlocks (1 : Matrix (Fin N × Fin m) (Fin N × Fin m)
        C((X × unitInterval) × Sph ℂ, ℂ)) 0
      (-(tCyl_kld X • RowMCyl X N q))
      (1 : Matrix (Fin m) (Fin m) C((X × unitInterval) × Sph ℂ, ℂ))) = 1
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,
    Matrix.mul_neg, add_neg_cancel, neg_zero, Matrix.fromBlocks_one]

lemma sliceMat_LmatCyl_incl0 {m : ℕ} (N : ℕ)
    (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ))) :
    sliceMat X (Work.KT.Fund.incl0 X) (LmatCyl X N q) = 1 := by
  show sliceMat X (Work.KT.Fund.incl0 X)
    (Matrix.fromBlocks (1 : Matrix (Fin N × Fin m) (Fin N × Fin m)
        C((X × unitInterval) × Sph ℂ, ℂ)) 0
      (-(tCyl_kld X • RowMCyl X N q))
      (1 : Matrix (Fin m) (Fin m) C((X × unitInterval) × Sph ℂ, ℂ))) = 1
  simp only [sliceMat_fromBlocks, sliceMat_one, sliceMat_zero, sliceMat_neg, sliceMat_smul,
    sliceHom_incl0_tCyl, zero_smul_mat, neg_zero, Matrix.fromBlocks_one,
    sliceMat_pullCyl X (Work.KT.Fund.incl0 X) (fun p => rfl)]

lemma sliceMat_LmatCyl_incl1 {m : ℕ} (N : ℕ)
    (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ))) :
    sliceMat X (Work.KT.Fund.incl1 X) (LmatCyl X N q) = Lmat X N q := by
  show sliceMat X (Work.KT.Fund.incl1 X)
    (Matrix.fromBlocks (1 : Matrix (Fin N × Fin m) (Fin N × Fin m)
        C((X × unitInterval) × Sph ℂ, ℂ)) 0
      (-(tCyl_kld X • RowMCyl X N q))
      (1 : Matrix (Fin m) (Fin m) C((X × unitInterval) × Sph ℂ, ℂ))) = Lmat X N q
  simp only [sliceMat_fromBlocks, sliceMat_one, sliceMat_zero, sliceMat_neg, sliceMat_smul,
    sliceHom_incl1_tCyl, one_smul_mat,
    sliceMat_pullCyl X (Work.KT.Fund.incl1 X) (fun p => rfl)]

/-- The interpolated row-elimination unit. -/
def uLcyl {m : ℕ} (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ))) :
    (Matrix (BIdx N m) (BIdx N m) C((X × unitInterval) × Sph ℂ, ℂ))ˣ :=
  Units.mk (LmatCyl X N q) (uRowInvCyl X N q)
    (LmatCyl_mul_uRowInvCyl X N q) (uRowInvCyl_mul_LmatCyl X N q)

@[simp] lemma uLcyl_val {m : ℕ} (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ))) :
    ((uLcyl X N q : (Matrix (BIdx N m) (BIdx N m)
        C((X × unitInterval) × Sph ℂ, ℂ))ˣ) :
      Matrix (BIdx N m) (BIdx N m) C((X × unitInterval) × Sph ℂ, ℂ)) = LmatCyl X N q := rfl

/-- The interpolated column-operation unit. -/
def uRcyl (N m : ℕ) :
    (Matrix (BIdx N m) (BIdx N m) C((X × unitInterval) × Sph ℂ, ℂ))ˣ :=
  Units.mk (RmatCyl X N) (1 - (tCyl_kld X * zCyl_kld X) • shCyl X N m)
    (by
      show RmatCyl X N * (1 - (tCyl_kld X * zCyl_kld X) • shCyl X N m) = 1
      exact (one_sub_smul_mul_sum (shCyl X N m) (tCyl_kld X * zCyl_kld X) N
        (shMat_pow_succ_eq_zero _ N m)).2)
    (by
      show (1 - (tCyl_kld X * zCyl_kld X) • shCyl X N m) * RmatCyl X N = 1
      exact (one_sub_smul_mul_sum (shCyl X N m) (tCyl_kld X * zCyl_kld X) N
        (shMat_pow_succ_eq_zero _ N m)).1)

@[simp] lemma uRcyl_val (N m : ℕ) :
    ((uRcyl X N m : (Matrix (BIdx N m) (BIdx N m)
        C((X × unitInterval) × Sph ℂ, ℂ))ˣ) :
      Matrix (BIdx N m) (BIdx N m) C((X × unitInterval) × Sph ℂ, ℂ)) = RmatCyl X N := rfl

/-- The pull-back of functions on `X × S¹` to the cylinder. -/
def cylPullHom : C(X × Sph ℂ, ℂ) →+* C((X × unitInterval) × Sph ℂ, ℂ) where
  toFun f := f.comp (projCylS X)
  map_one' := by ext p; rfl
  map_mul' f g := by ext p; rfl
  map_zero' := by ext p; rfl
  map_add' f g := by ext p; rfl

/-- The companion unit over the cylinder, obtained by pulling back the circle-level one. -/
def uAcyl {m : ℕ} (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ)))
    (u : (Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ))ˣ)
    (hu : (u : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ)) = q.map (polyMapA X)) :
    (Matrix (BIdx N m) (BIdx N m) C((X × unitInterval) × Sph ℂ, ℂ))ˣ :=
  Units.map (RingHom.mapMatrix (cylPullHom X)).toMonoidHom (uAmat X N q u hu)

theorem uAcyl_val {m : ℕ} (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ)))
    (u : (Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ))ˣ)
    (hu : (u : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ)) = q.map (polyMapA X))
    (hN : ∀ i j, (q i j).natDegree ≤ N) :
    ((uAcyl X N q u hu : (Matrix (BIdx N m) (BIdx N m)
        C((X × unitInterval) × Sph ℂ, ℂ))ˣ) :
      Matrix (BIdx N m) (BIdx N m) C((X × unitInterval) × Sph ℂ, ℂ)) = AmatCyl X N q := by
  rw [uAcyl, Units.coe_map]
  change (↑(uAmat X N q u hu) : Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ)).map
      ⇑(cylPullHom X) = AmatCyl X N q
  rw [uAmat_val X N q u hu hN]
  rfl

/-- The unit over the cylinder whose slices are `A` and `B`. -/
def Hcyl {m : ℕ} (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ)))
    (u : (Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ))ˣ)
    (hu : (u : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ)) = q.map (polyMapA X)) :
    (Matrix (BIdx N m) (BIdx N m) C((X × unitInterval) × Sph ℂ, ℂ))ˣ :=
  uLcyl X N q * uAcyl X N q u hu * uRcyl X N m

@[simp] lemma Hcyl_val {m : ℕ} (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ)))
    (u : (Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ))ˣ)
    (hu : (u : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ)) = q.map (polyMapA X))
    (hN : ∀ i j, (q i j).natDegree ≤ N) :
    ((Hcyl X N q u hu : (Matrix (BIdx N m) (BIdx N m)
        C((X × unitInterval) × Sph ℂ, ℂ))ˣ) :
      Matrix (BIdx N m) (BIdx N m) C((X × unitInterval) × Sph ℂ, ℂ))
      = LmatCyl X N q * AmatCyl X N q * RmatCyl X N := by
  rw [Hcyl, Units.val_mul, Units.val_mul, uLcyl_val, uAcyl_val X N q u hu hN, uRcyl_val]

lemma sliceMat_Hcyl_incl0 {m : ℕ} (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ)))
    (u : (Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ))ˣ)
    (hu : (u : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ)) = q.map (polyMapA X))
    (hN : ∀ i j, (q i j).natDegree ≤ N) :
    sliceMat X (Work.KT.Fund.incl0 X)
      ((Hcyl X N q u hu : (Matrix (BIdx N m) (BIdx N m)
        C((X × unitInterval) × Sph ℂ, ℂ))ˣ) :
      Matrix (BIdx N m) (BIdx N m) C((X × unitInterval) × Sph ℂ, ℂ)) = Amat X N q := by
  rw [Hcyl_val X N q u hu hN, sliceMat_mul, sliceMat_mul, sliceMat_LmatCyl_incl0,
    sliceMat_AmatCyl X (Work.KT.Fund.incl0 X) (fun p => rfl) N q,
    sliceMat_RmatCyl_incl0, Matrix.one_mul, Matrix.mul_one]

lemma sliceMat_Hcyl_incl1 {m : ℕ} (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ)))
    (u : (Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ))ˣ)
    (hu : (u : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ)) = q.map (polyMapA X))
    (hN : ∀ i j, (q i j).natDegree ≤ N) :
    sliceMat X (Work.KT.Fund.incl1 X)
      ((Hcyl X N q u hu : (Matrix (BIdx N m) (BIdx N m)
        C((X × unitInterval) × Sph ℂ, ℂ))ˣ) :
      Matrix (BIdx N m) (BIdx N m) C((X × unitInterval) × Sph ℂ, ℂ)) = Bmat X N q := by
  rw [Hcyl_val X N q u hu hN, sliceMat_mul, sliceMat_mul, sliceMat_LmatCyl_incl1,
    sliceMat_AmatCyl X (Work.KT.Fund.incl1 X) (fun p => rfl) N q,
    sliceMat_RmatCyl_incl1]
  rw [mul_assoc, Lmat_mul_Amat_Rmat X m N q hN]

/-! ## 3. Reindexing the circle-level data -/

lemma cls_one_add' (R : Type) [Ring R] (n k : ℕ) :
    cls (Mat.one R (n + k)) = cls (Mat.one R n) + cls (Mat.one R k) := by
  rw [← Work.KT.Mat.one_sum R n k,
    Work.KT.cls_sum (Work.KT.Mat.one_idem R n) (Work.KT.Mat.one_idem R k)]

lemma reindex_one' {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (R : Type) [Zero R] [One R] :
    (Matrix.reindex e e (1 : Matrix ι ι R) : Matrix κ κ R) = 1 := by
  funext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · have h' : e.symm i ≠ e.symm j := fun hh => h (e.symm.injective hh)
    simp [h, h']

lemma reindex_refl' {ι : Type} (R : Type) (M : Matrix ι ι R) :
    Matrix.reindex (Equiv.refl ι) (Equiv.refl ι) M = M := by
  funext i j; rfl

lemma reindex_add {ι κ : Type} (e : ι ≃ κ)
    (M N : Matrix ι ι C(X × Sph ℂ, ℂ)) :
    Matrix.reindex e e (M + N) = Matrix.reindex e e M + Matrix.reindex e e N := by
  funext i j
  show (M (e.symm i) (e.symm j) + N (e.symm i) (e.symm j))
      = (M (e.symm i) (e.symm j) + N (e.symm i) (e.symm j))
  rfl

lemma reindex_smul {ι κ : Type} (e : ι ≃ κ) (a : C(X × Sph ℂ, ℂ))
    (M : Matrix ι ι C(X × Sph ℂ, ℂ)) :
    Matrix.reindex e e (a • M) = a • Matrix.reindex e e M := by
  funext i j
  show a * M (e.symm i) (e.symm j) = a * M (e.symm i) (e.symm j)
  rfl

lemma pullIdx_idMat {N m : ℕ} :
    pullIdx (ContinuousMap.fst : C(X × Sph ℂ, X)) (idMat C(X, ℂ) N m)
      = idMat C(X × Sph ℂ, ℂ) N m := by
  funext i j
  ext p
  rw [pullIdx_apply, idMat_apply_eq, idMat_apply_eq]
  by_cases h : BIdx.st i < N
  · rw [if_pos h, if_pos h]
    by_cases h2 : j = i
    · rw [if_pos h2, if_pos h2]; rfl
    · rw [if_neg h2, if_neg h2]; rfl
  · rw [if_neg h, if_neg h]; rfl

lemma pullIdx_shMat {N m : ℕ} :
    pullIdx (ContinuousMap.fst : C(X × Sph ℂ, X)) (shMat C(X, ℂ) N m)
      = shMat C(X × Sph ℂ, ℂ) N m := by
  funext i j
  ext p
  rw [pullIdx_apply, shMat_apply_eq, shMat_apply_eq]
  by_cases h : BIdx.st i < N
  · rw [if_pos h, if_pos h]
    by_cases h2 : j = BIdx.nx i
    · rw [if_pos h2, if_pos h2]; rfl
    · rw [if_neg h2, if_neg h2]; rfl
  · rw [if_neg h, if_neg h]; rfl

lemma smul_neg_mat {ι κ : Type} (a : C(X × Sph ℂ, ℂ))
    (M : Matrix ι κ C(X × Sph ℂ, ℂ)) : a • (-M) = -(a • M) := by
  funext i j
  show a * (-(M i j)) = -(a * M i j)
  exact mul_neg a (M i j)

lemma pullIdx_neg {ι : Type} (M : Matrix ι ι C(X, ℂ)) :
    pullIdx (ContinuousMap.fst : C(X × Sph ℂ, X)) (-M)
      = -pullIdx (ContinuousMap.fst : C(X × Sph ℂ, X)) M := by
  funext i j
  ext p
  simp only [pullIdx_apply, Matrix.neg_apply, ContinuousMap.neg_apply]

lemma pullIdx_add {ι : Type} (M N : Matrix ι ι C(X, ℂ)) :
    pullIdx (ContinuousMap.fst : C(X × Sph ℂ, X)) (M + N)
      = pullIdx (ContinuousMap.fst : C(X × Sph ℂ, X)) M
        + pullIdx (ContinuousMap.fst : C(X × Sph ℂ, X)) N := by
  funext i j
  ext p
  simp only [pullIdx_apply, Matrix.add_apply, ContinuousMap.add_apply]

lemma Amat_decomp {m : ℕ} (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ))) :
    Amat X N q = zc X • pullIdx (ContinuousMap.fst : C(X × Sph ℂ, X)) (aMat X N)
      + pullIdx (ContinuousMap.fst : C(X × Sph ℂ, X)) (bMat X N q) := by
  rw [show Amat X N q = idMat C(X × Sph ℂ, ℂ) N m - zc X • shC X N m + coeffC X N q
      from rfl]
  rw [show (idMat C(X × Sph ℂ, ℂ) N m)
        = pullIdx (ContinuousMap.fst : C(X × Sph ℂ, X)) (idMat C(X, ℂ) N m)
      from (pullIdx_idMat X (N := N) (m := m)).symm,
    show (shC X N m) = pullIdx (ContinuousMap.fst : C(X × Sph ℂ, X)) (shMat C(X, ℂ) N m)
      from (pullIdx_shMat X (N := N) (m := m)).symm,
    show (coeffC X N q)
        = pullIdx (ContinuousMap.fst : C(X × Sph ℂ, X)) (coeffMatBig X N q) from rfl,
    show aMat X N = -shMat C(X, ℂ) N m from rfl,
    show bMat X N q = idMat C(X, ℂ) N m + coeffMatBig X N q from rfl]
  rw [pullIdx_neg, pullIdx_add]
  rw [smul_neg_mat]
  abel

lemma reindex_pullIdx {N m : ℕ} (e : BIdx N m ≃ Fin (N * m + m))
    {M : Matrix (BIdx N m) (BIdx N m) C(X, ℂ)} :
    Matrix.reindex e e (pullIdx (ContinuousMap.fst : C(X × Sph ℂ, X)) M)
      = Work.KT.Fund.pullMat X (Matrix.reindex e e M) := by
  show Matrix.reindex e e (M.map (fun f => f.comp (ContinuousMap.fst : C(X × Sph ℂ, X))))
      = (Matrix.reindex e e M).map (fun f => f.comp (ContinuousMap.fst : C(X × Sph ℂ, X)))
  rw [Work.KT.Fund.reindex_map']

lemma slice_Hcyl_incl0_fin {N m : ℕ} (e : BIdx N m ≃ Fin (N * m + m))
    (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ)))
    (u : (Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ))ˣ)
    (hu : (u : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ)) = q.map (polyMapA X))
    (hN : ∀ i j, (q i j).natDegree ≤ N) :
    (Matrix.reindex e e (Hcyl X N q u hu : Matrix (BIdx N m) (BIdx N m)
        C((X × unitInterval) × Sph ℂ, ℂ))).map (fun f => f.comp (Work.KT.Fund.incl0 X))
      = Matrix.reindex e e (Amat X N q) := by
  rw [Work.KT.Fund.reindex_map',
    show ((Hcyl X N q u hu : Matrix (BIdx N m) (BIdx N m)
        C((X × unitInterval) × Sph ℂ, ℂ)).map (fun f => f.comp (Work.KT.Fund.incl0 X)))
        = Amat X N q from sliceMat_Hcyl_incl0 X N q u hu hN]

lemma slice_Hcyl_incl1_fin {N m : ℕ} (e : BIdx N m ≃ Fin (N * m + m))
    (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ)))
    (u : (Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ))ˣ)
    (hu : (u : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ)) = q.map (polyMapA X))
    (hN : ∀ i j, (q i j).natDegree ≤ N) :
    (Matrix.reindex e e (Hcyl X N q u hu : Matrix (BIdx N m) (BIdx N m)
        C((X × unitInterval) × Sph ℂ, ℂ))).map (fun f => f.comp (Work.KT.Fund.incl1 X))
      = Matrix.reindex e e (Bmat X N q) := by
  rw [Work.KT.Fund.reindex_map',
    show ((Hcyl X N q u hu : Matrix (BIdx N m) (BIdx N m)
        C((X × unitInterval) × Sph ℂ, ℂ)).map (fun f => f.comp (Work.KT.Fund.incl1 X)))
        = Bmat X N q from sliceMat_Hcyl_incl1 X N q u hu hN]

/-! ## 4. The linearisation theorem -/

theorem kappa_linearise_aux (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (m : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ)))
    (u : (Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ))ˣ)
    (hu : (u : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ)) = q.map (polyMapA X)) :
    ∃ (m' : ℕ) (a b : Matrix (Fin m') (Fin m') C(X, ℂ))
      (D : (Matrix (Fin m') (Fin m') C(X × Sph ℂ, ℂ))ˣ),
      (D : Matrix (Fin m') (Fin m') C(X × Sph ℂ, ℂ))
        = (Work.KT.zUnit X : C(X × Sph ℂ, ℂ)) • Work.KT.Fund.pullMat X a
          + Work.KT.Fund.pullMat X b ∧
      redKa X m u = redKa X m' D := by
  classical
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ i j, (q i j).natDegree ≤ N :=
    ⟨(Finset.univ : Finset (Fin m × Fin m)).sup (fun p => (q p.1 p.2).natDegree),
      fun i j => Finset.le_sup (f := fun p : Fin m × Fin m => (q p.1 p.2).natDegree)
        (Finset.mem_univ (i, j))⟩
  set e : BIdx N m ≃ Fin (N * m + m) := bIdxEquiv N m with he
  set ψc : Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ) ≃ₐ[ℂ]
      Matrix (Fin (N * m + m)) (Fin (N * m + m)) C(X × Sph ℂ, ℂ) :=
    Matrix.reindexAlgEquiv ℂ C(X × Sph ℂ, ℂ) e with hψc
  set ψk : Matrix (BIdx N m) (BIdx N m) C((X × unitInterval) × Sph ℂ, ℂ) ≃ₐ[ℂ]
      Matrix (Fin (N * m + m)) (Fin (N * m + m)) C((X × unitInterval) × Sph ℂ, ℂ) :=
    Matrix.reindexAlgEquiv ℂ C((X × unitInterval) × Sph ℂ, ℂ) e with hψk
  have hcoeM : ∀ M : Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ),
      ψc M = Matrix.reindex e e M :=
    fun M => congrFun (Matrix.coe_reindexAlgEquiv ℂ C(X × Sph ℂ, ℂ) e) M
  have hcoe : ∀ M : Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ),
      ψc.toRingEquiv.toMonoidHom M = Matrix.reindex e e M :=
    fun M => congrFun (Matrix.coe_reindexAlgEquiv ℂ C(X × Sph ℂ, ℂ) e) M
  have hcoek : ∀ M : Matrix (BIdx N m) (BIdx N m) C((X × unitInterval) × Sph ℂ, ℂ),
      ψk.toRingEquiv.toMonoidHom M = Matrix.reindex e e M :=
    fun M => congrFun (Matrix.coe_reindexAlgEquiv ℂ C((X × unitInterval) × Sph ℂ, ℂ) e) M
  set uA' : (Matrix (Fin (N * m + m)) (Fin (N * m + m)) C(X × Sph ℂ, ℂ))ˣ :=
    Units.map ψc.toRingEquiv.toMonoidHom (uAmat X N q u hu) with huA'
  set uB' : (Matrix (Fin (N * m + m)) (Fin (N * m + m)) C(X × Sph ℂ, ℂ))ˣ :=
    Units.map ψc.toRingEquiv.toMonoidHom (uBmat X N q u hu) with huB'
  set H' : (Matrix (Fin (N * m + m)) (Fin (N * m + m))
      C((X × unitInterval) × Sph ℂ, ℂ))ˣ :=
    Units.map ψk.toRingEquiv.toMonoidHom (Hcyl X N q u hu) with hH'
  have hAeq : ((uA' : (Matrix (Fin (N * m + m)) (Fin (N * m + m)) C(X × Sph ℂ, ℂ))ˣ) :
      Matrix (Fin (N * m + m)) (Fin (N * m + m)) C(X × Sph ℂ, ℂ))
      = Matrix.reindex e e (Amat X N q) := by
    rw [huA', Units.coe_map, uAmat_val X N q u hu hN, hcoe]
  have hBeq : ((uB' : (Matrix (Fin (N * m + m)) (Fin (N * m + m)) C(X × Sph ℂ, ℂ))ˣ) :
      Matrix (Fin (N * m + m)) (Fin (N * m + m)) C(X × Sph ℂ, ℂ))
      = Matrix.reindex e e (Bmat X N q) := by
    rw [huB', Units.coe_map, uBmat_val X N q u hu, hcoe]
  have hHval : ((H' : (Matrix (Fin (N * m + m)) (Fin (N * m + m))
        C((X × unitInterval) × Sph ℂ, ℂ))ˣ) :
      Matrix (Fin (N * m + m)) (Fin (N * m + m)) C((X × unitInterval) × Sph ℂ, ℂ))
      = Matrix.reindex e e (Hcyl X N q u hu : Matrix (BIdx N m) (BIdx N m)
        C((X × unitInterval) × Sph ℂ, ℂ)) := by
    rw [hH', Units.coe_map, hcoek]
  refine ⟨N * m + m, Matrix.reindex e e (aMat X N), Matrix.reindex e e (bMat X N q),
    uA', ?_, ?_⟩
  · rw [hAeq, ← hcoeM (Amat X N q), Amat_decomp X N q, hcoeM, reindex_add, reindex_smul,
      reindex_pullIdx X e, reindex_pullIdx X e]
  · have hBblocks : ((uB' : (Matrix (Fin (N * m + m)) (Fin (N * m + m))
          C(X × Sph ℂ, ℂ))ˣ) :
        Matrix (Fin (N * m + m)) (Fin (N * m + m)) C(X × Sph ℂ, ℂ))
        = Matrix.reindex finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks (1 : Matrix (Fin (N * m)) (Fin (N * m)) C(X × Sph ℂ, ℂ)) 0 0
              ((u : (Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ))ˣ) :
                Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ))) := by
      rw [hBeq]
      rw [show Matrix.reindex e e (Bmat X N q)
          = Matrix.reindex e e (Matrix.fromBlocks (1 : Matrix (Fin N × Fin m)
                (Fin N × Fin m) C(X × Sph ℂ, ℂ)) 0 0 (q.map (polyMapA X)))
          from rfl]
      rw [show Matrix.reindex e e (Matrix.fromBlocks (1 : Matrix (Fin N × Fin m)
              (Fin N × Fin m) C(X × Sph ℂ, ℂ)) 0 0 (q.map (polyMapA X)))
          = Matrix.reindex finSumFinEquiv finSumFinEquiv
              (Matrix.reindex (Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin m)))
                (Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin m)))
                (Matrix.fromBlocks (1 : Matrix (Fin N × Fin m) (Fin N × Fin m)
                  C(X × Sph ℂ, ℂ)) 0 0 (q.map (polyMapA X)))) from rfl]
      rw [Work.KT.Fund.fromBlocks_reindex_sumCongr]
      rw [reindex_one', reindex_refl']
      rw [← hu]
    have hhom := Work.KT.Fund.kappa_homotopic X (N * m + m) uA' uB' H'
      (by rw [hHval, slice_Hcyl_incl0_fin X e q u hu hN, hAeq])
      (by rw [hHval, slice_Hcyl_incl1_fin X e q u hu hN, hBeq])
    have hadd := Work.KT.Fund.kappa_add X (N * m) m uB'
      (1 : (Matrix (Fin (N * m)) (Fin (N * m)) C(X × Sph ℂ, ℂ))ˣ) u hBblocks
    have hone := Work.KT.Fund.kappa_one X (N * m)
    have hcls : cls (Mat.one C(X × S2, ℂ) (N * m + m))
        = cls (Mat.one C(X × S2, ℂ) (N * m)) + cls (Mat.one C(X × S2, ℂ) m) :=
      cls_one_add' _ (N * m) m
    show Work.KT.Fund.kappa X m u - cls (Mat.one C(X × S2, ℂ) m)
        = Work.KT.Fund.kappa X (N * m + m) uA' - cls (Mat.one C(X × S2, ℂ) (N * m + m))
    rw [hhom, hadd, hone, hcls]
    abel

end

end Work.KT.EG
