import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Psi.Basic
import Submission.Work.KT.Psi.sq2Part_idem
import Submission.Work.KT.Psi.psi2sum_Setup

/-!
# `Work.KT.Psi.sq2Part_MvN`

`cls (sq2Part ε p)` depends only on the Murray–von Neumann class of the idempotent `p`.

For `ε² = 1` this is proved by exhibiting explicit Murray–von Neumann witnesses
`u = P_ε(q) · (a ⊗ a)`, `v = b ⊗ b` for `p = ba`, `q = ab`: they satisfy `v * u = sq2PartP ε p`
and `u * v = sq2PartP ε q`, because `a ⊗ a` and `b ⊗ b` intertwine the two swap permutation
matrices (this is where commutativity of `A` is used).

For `ε² ≠ 1` both sides vanish: `X * X - X = ((ε²-1)/4) • (p ⊗ p)`, so `X` fails to be
idempotent unless `p ⊗ p = 0`, and `p ⊗ p = 0` (with `p` idempotent, over a commutative ring)
forces `p = 0`, hence `q = ab = 0` and both `sq2Part`s are literally zero.
-/

namespace Work.KT.Psi

open Matrix

noncomputable section

variable {A : Type} [Ring A]

namespace Sq2PartMvN

/-! ## Rectangular permutation and Kronecker lemmas -/

/-- Left multiplication by the permutation matrix of `σ` reindexes the rows by `σ`
(rectangular version). -/
lemma rect_permMatrix_mul {ι κ : Type} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) (X : Matrix ι κ A) : σ.permMatrix A * X = X.submatrix σ id := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id_eq]
  rw [Finset.sum_eq_single (σ i)]
  · rw [Work.KT.permMatrix_apply' σ i (σ i), if_pos rfl, one_mul]
  · intro b _ hb
    rw [Work.KT.permMatrix_apply' σ i b, if_neg (fun h => hb h.symm), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Right multiplication by the permutation matrix of `σ` reindexes the columns by `σ⁻¹`
(rectangular version). -/
lemma rect_mul_permMatrix {ι κ : Type} [Fintype κ] [DecidableEq κ]
    (σ : Equiv.Perm κ) (X : Matrix ι κ A) : X * σ.permMatrix A = X.submatrix id σ.symm := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id_eq]
  rw [Finset.sum_eq_single (σ.symm j)]
  · rw [Work.KT.permMatrix_apply' σ (σ.symm j) j, Equiv.apply_symm_apply, if_pos rfl, mul_one]
  · intro b _ hb
    have h : ¬ (σ b = j) := fun hh => hb ((Equiv.eq_symm_apply σ).mpr hh)
    rw [Work.KT.permMatrix_apply' σ b j, if_neg h, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The permutation matrix of an involution is its own inverse. -/
lemma permMatrix_invol {ι : Type} [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι)
    (hσ : ∀ x, σ (σ x) = x) : σ.permMatrix A * σ.permMatrix A = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ i)]
  · rw [Work.KT.permMatrix_apply' σ i (σ i), if_pos rfl, Work.KT.permMatrix_apply' σ (σ i) j,
      hσ i]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h]
      simp [Matrix.one_apply_ne h]
  · intro b _ hb
    rw [Work.KT.permMatrix_apply' σ i b, if_neg (fun h => hb h.symm), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `a ⊗ a` intertwines the two swap permutation matrices (rectangular `a`); this is where
commutativity of the entries of `a` is used. -/
lemma kroneckerMap_rect_prodComm (hA : ∀ x y : A, x * y = y * x) {m k : ℕ}
    (a : Matrix (Fin m) (Fin k) A) :
    Matrix.kroneckerMap (· * ·) a a * Equiv.Perm.permMatrix A (Equiv.prodComm (Fin k) (Fin k)) =
      Equiv.Perm.permMatrix A (Equiv.prodComm (Fin m) (Fin m)) *
        Matrix.kroneckerMap (· * ·) a a := by
  rw [rect_mul_permMatrix (Equiv.prodComm (Fin k) (Fin k)) (Matrix.kroneckerMap (· * ·) a a),
    rect_permMatrix_mul (Equiv.prodComm (Fin m) (Fin m)) (Matrix.kroneckerMap (· * ·) a a),
    Equiv.prodComm_symm]
  ext i j
  rcases i with ⟨i1, i2⟩
  rcases j with ⟨j1, j2⟩
  simp only [Matrix.submatrix_apply, Matrix.kroneckerMap_apply, id_eq, Equiv.prodComm_apply,
    Prod.swap_prod_mk]
  exact hA _ _

/-- Kronecker multiplicativity for rectangular matrices over a commutative ring. -/
lemma mul_kronecker_rect (hA : ∀ x y : A, x * y = y * x)
    {l m n l' m' n' : Type} [Fintype m] [Fintype m']
    (X : Matrix l m A) (Y : Matrix l' m' A) (Z : Matrix m n A) (W : Matrix m' n' A) :
    Matrix.kroneckerMap (· * ·) X Y * Matrix.kroneckerMap (· * ·) Z W =
      Matrix.kroneckerMap (· * ·) (X * Z) (Y * W) := by
  letI : CommRing A := { ‹Ring A› with mul_comm := hA }
  exact (Matrix.mul_kronecker_mul X Z Y W).symm

/-- `reindex` pushes through rectangular matrix multiplication. -/
lemma reindex_mul_rect {m m' n n' p p' : Type} [Fintype n] [Fintype n']
    (e : m ≃ m') (f : n ≃ n') (g : p ≃ p') (X : Matrix m n A) (Y : Matrix n p A) :
    Matrix.reindex e f X * Matrix.reindex f g Y = Matrix.reindex e g (X * Y) := by
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply]
  exact Matrix.submatrix_mul_equiv X Y e.symm f.symm g.symm

/-- An `A`-scalar `algebraMap ℂ A c` acts on matrices exactly as the complex scalar `c`. -/
lemma algMap_smul_eq_smul_C [Algebra ℂ A] {ι : Type} (c : ℂ) (M : Matrix ι ι A) :
    algebraMap ℂ A c • M = c • M := by
  ext i j
  simp only [Matrix.smul_apply, Algebra.smul_def, smul_eq_mul]

/-! ## The two generic projector identities -/

/-- The `ε`-projector on the row index set moves `a ⊗ a` to the column side. -/
lemma proj_mul_kron [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x) {m k : ℕ}
    (a : Matrix (Fin m) (Fin k) A) (ε : ℂ) :
    ((1 / 2 : ℂ) • (1 + ε • Equiv.Perm.permMatrix A (Equiv.prodComm (Fin m) (Fin m)))) *
        Matrix.kroneckerMap (· * ·) a a =
      Matrix.kroneckerMap (· * ·) a a *
        ((1 / 2 : ℂ) • (1 + ε • Equiv.Perm.permMatrix A (Equiv.prodComm (Fin k) (Fin k)))) := by
  have h : (1 + ε • Equiv.Perm.permMatrix A (Equiv.prodComm (Fin m) (Fin m))) *
      Matrix.kroneckerMap (· * ·) a a =
      Matrix.kroneckerMap (· * ·) a a *
        (1 + ε • Equiv.Perm.permMatrix A (Equiv.prodComm (Fin k) (Fin k))) := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, kroneckerMap_rect_prodComm hA a]
  rw [Matrix.smul_mul, Matrix.mul_smul, h]

/-- The `ε`-projector commutes with `M ⊗ M` for square `M`. -/
lemma kronMap_proj_comm [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) A) (ε : ℂ) :
    Matrix.kroneckerMap (· * ·) M M *
        ((1 / 2 : ℂ) • (1 + ε • Equiv.Perm.permMatrix A (Equiv.prodComm (Fin n) (Fin n)))) =
      ((1 / 2 : ℂ) • (1 + ε • Equiv.Perm.permMatrix A (Equiv.prodComm (Fin n) (Fin n)))) *
        Matrix.kroneckerMap (· * ·) M M := by
  have hMT : Matrix.kroneckerMap (· * ·) M M *
      Equiv.Perm.permMatrix A (Equiv.prodComm (Fin n) (Fin n)) =
      Equiv.Perm.permMatrix A (Equiv.prodComm (Fin n) (Fin n)) *
        Matrix.kroneckerMap (· * ·) M M := kroneckerMap_rect_prodComm hA M
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, Matrix.mul_smul,
    Matrix.smul_mul, hMT]

/-! ## `K₀`-class lemmas -/

/-- Murray–von Neumann equivalence gives an equality in `K₀` for matrices over an arbitrary
finite index type. -/
theorem clsI_eq_of_MvN {ι κ : Type} [Fintype ι] [Fintype κ]
    {X : Matrix ι ι A} {Y : Matrix κ κ A} (hX : X * X = X) (hY : Y * Y = Y)
    {u : Matrix κ ι A} {v : Matrix ι κ A} (hvu : v * u = X) (huv : u * v = Y) :
    clsI X = clsI Y := by
  rw [clsI_eq X (Fintype.equivFin ι), clsI_eq Y (Fintype.equivFin κ)]
  have hX' : Mat.IsIdem (Mat.ofIdx X (Fintype.card ι) (Fintype.equivFin ι)) := by
    show Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) X *
        Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) X =
      Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) X
    rw [reindex_mul_rect (Fintype.equivFin ι) (Fintype.equivFin ι) (Fintype.equivFin ι) X X, hX]
  have hY' : Mat.IsIdem (Mat.ofIdx Y (Fintype.card κ) (Fintype.equivFin κ)) := by
    show Matrix.reindex (Fintype.equivFin κ) (Fintype.equivFin κ) Y *
        Matrix.reindex (Fintype.equivFin κ) (Fintype.equivFin κ) Y =
      Matrix.reindex (Fintype.equivFin κ) (Fintype.equivFin κ) Y
    rw [reindex_mul_rect (Fintype.equivFin κ) (Fintype.equivFin κ) (Fintype.equivFin κ) Y Y, hY]
  refine cls_eq_of_MvN hX' hY' ⟨?_, ?_, ?_, ?_⟩
  · exact Matrix.reindex (Fintype.equivFin κ) (Fintype.equivFin ι) u
  · exact Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin κ) v
  · change Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin κ) v *
        Matrix.reindex (Fintype.equivFin κ) (Fintype.equivFin ι) u =
      Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) X
    rw [reindex_mul_rect (Fintype.equivFin ι) (Fintype.equivFin κ) (Fintype.equivFin ι) v u, hvu]
  · change Matrix.reindex (Fintype.equivFin κ) (Fintype.equivFin ι) u *
        Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin κ) v =
      Matrix.reindex (Fintype.equivFin κ) (Fintype.equivFin κ) Y
    rw [reindex_mul_rect (Fintype.equivFin κ) (Fintype.equivFin ι) (Fintype.equivFin κ) u v, huv]

/-- The class of a non-idempotent matrix (over an arbitrary finite index type) vanishes. -/
lemma clsI_zero_of_not_idem {ι : Type} [Fintype ι] {M : Matrix ι ι A} (h : M * M ≠ M) :
    clsI M = 0 := by
  rw [clsI_eq M (Fintype.equivFin ι)]
  refine cls_zero_of_not_idem (fun hc => h ?_)
  have hc' : Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) (M * M) =
      Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) M := by
    rw [← reindex_mul_rect (Fintype.equivFin ι) (Fintype.equivFin ι) (Fintype.equivFin ι) M M]
    exact hc
  exact (Matrix.reindexRingEquiv A (Fintype.equivFin ι)).injective hc'

/-- The class of the empty matrix is zero. -/
lemma cls_fin_zero : cls (⟨0, (0 : Matrix (Fin 0) (Fin 0) A)⟩ : Mat A) = 0 := by
  have hidem : Mat.IsIdem (⟨0, (0 : Matrix (Fin 0) (Fin 0) A)⟩ : Mat A) := by
    show (0 : Matrix (Fin 0) (Fin 0) A) * 0 = 0
    rw [mul_zero]
  have hsum : Mat.sum (⟨0, (0 : Matrix (Fin 0) (Fin 0) A)⟩ : Mat A)
      (⟨0, (0 : Matrix (Fin 0) (Fin 0) A)⟩ : Mat A) =
      ⟨0, (0 : Matrix (Fin 0) (Fin 0) A)⟩ := by
    refine Sigma.ext rfl ?_
    apply heq_of_eq
    ext i j
    exact Fin.elim0 i
  have h := cls_sum hidem hidem
  rw [hsum] at h
  have hc : cls (⟨0, (0 : Matrix (Fin 0) (Fin 0) A)⟩ : Mat A) + (0 : K0 A) =
      cls (⟨0, (0 : Matrix (Fin 0) (Fin 0) A)⟩ : Mat A) +
        cls (⟨0, (0 : Matrix (Fin 0) (Fin 0) A)⟩ : Mat A) := by
    rw [add_zero]; exact h
  exact (add_left_cancel hc).symm

/-- The zero matrix of any size has `K₀`-class `0`. -/
lemma cls_zero_mat (n : ℕ) : cls (⟨n, (0 : Matrix (Fin n) (Fin n) A)⟩ : Mat A) = 0 := by
  have hidemn : Mat.IsIdem (⟨n, (0 : Matrix (Fin n) (Fin n) A)⟩ : Mat A) := by
    show (0 : Matrix (Fin n) (Fin n) A) * 0 = 0
    rw [mul_zero]
  have hidem0 : Mat.IsIdem (⟨0, (0 : Matrix (Fin 0) (Fin 0) A)⟩ : Mat A) := by
    show (0 : Matrix (Fin 0) (Fin 0) A) * 0 = 0
    rw [mul_zero]
  have hmvN : Mat.MvN (⟨n, (0 : Matrix (Fin n) (Fin n) A)⟩ : Mat A)
      (⟨0, (0 : Matrix (Fin 0) (Fin 0) A)⟩ : Mat A) := by
    refine ⟨0, 0, ?_, ?_⟩
    · ext i j; simp
    · ext i j; exact Fin.elim0 i
  rw [cls_eq_of_MvN hidemn hidem0 hmvN, cls_fin_zero]

/-- The class of the zero matrix over an arbitrary finite index type is zero. -/
lemma clsI_zero {ι : Type} [Fintype ι] : clsI (0 : Matrix ι ι A) = 0 := by
  rw [clsI_eq (0 : Matrix ι ι A) (Fintype.equivFin ι)]
  have h : Mat.ofIdx (0 : Matrix ι ι A) (Fintype.card ι) (Fintype.equivFin ι) =
      (⟨Fintype.card ι, (0 : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) A)⟩ :
        Mat A) := by
    simp only [Mat.ofIdx]
    rw [show Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) (0 : Matrix ι ι A) = 0
      from by simp]
  rw [h, cls_zero_mat]

/-- `sq2PartP` in complex-scalar form. -/
lemma sq2PartP_eq_smul [Algebra ℂ A] (ε : ℂ) (p : Mat A) :
    sq2PartP ε p = Matrix.kroneckerMap (· * ·) p.2 p.2 *
      ((1 / 2 : ℂ) • (1 + ε •
        Equiv.Perm.permMatrix A (Equiv.prodComm (Fin p.1) (Fin p.1)))) := by
  unfold sq2PartP
  rw [algMap_smul_eq_smul_C, algMap_smul_eq_smul_C]

/-- `cls (sq2Part ε p) = clsI (sq2PartP ε p)`. -/
lemma cls_sq2PartP_clsI [Algebra ℂ A] (ε : ℂ) (p : Mat A) :
    cls (sq2Part ε p) = clsI (sq2PartP ε p) := by
  rw [clsI_eq (sq2PartP ε p) finProdFinEquiv]
  exact congrArg cls (sq2Part_eq ε p)

/-- `p ⊗ p = 0` forces `p = 0` for an idempotent `p` over a commutative ring. -/
lemma kroneckerMap_self_eq_zero {p : Mat A} (hp : p.IsIdem)
    (h : Matrix.kroneckerMap (· * ·) p.2 p.2 = 0) : p.2 = 0 := by
  ext i j
  have hidem : (p.2 * p.2) i j = p.2 i j := by rw [hp]
  rw [← hidem, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  have hk : Matrix.kroneckerMap (· * ·) p.2 p.2 (i, k) (k, j) = 0 := by rw [h]; rfl
  rw [Matrix.kroneckerMap_apply] at hk
  exact hk

/-- Multiplication by a non-zero complex scalar is injective on matrices. -/
lemma smul_eq_zero_of_ne [Algebra ℂ A] {c : ℂ} (hc : c ≠ 0) {ι : Type}
    {M : Matrix ι ι A} (h : algebraMap ℂ A c • M = 0) : M = 0 := by
  ext i j
  have h1 : algebraMap ℂ A c * M i j = 0 := by
    have := congrFun (congrFun h i) j
    simpa using this
  have h2 : algebraMap ℂ A c⁻¹ * (algebraMap ℂ A c * M i j) = 0 := by rw [h1, mul_zero]
  rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul] at h2
  simpa using h2

/-- The basic computation `M * (P + c • 1) - M * P = c • M`. -/
lemma mul_add_smul_one_sub [Algebra ℂ A] {ι : Type} [Fintype ι] [DecidableEq ι]
    (M P : Matrix ι ι A) (c : ℂ) :
    M * (P + c • (1 : Matrix ι ι A)) - M * P = c • M := by
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
  abel

/-- The `ε`-projector is idempotent up to the scalar `(ε²-1)/4`. -/
lemma proj_sq_eps [Algebra ℂ A] {ι : Type} [Fintype ι] [DecidableEq ι]
    (ε : ℂ) (T : Matrix ι ι A) (hT : T * T = 1) :
    ((1 / 2 : ℂ) • (1 + ε • T)) * ((1 / 2 : ℂ) • (1 + ε • T)) =
      (1 / 2 : ℂ) • (1 + ε • T) + ((ε * ε - 1) / 4) • (1 : Matrix ι ι A) := by
  have hsq : (1 + ε • T) * (1 + ε • T) =
      (1 + ε * ε) • (1 : Matrix ι ι A) + (2 * ε) • T := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, hT]
    rw [add_smul, one_smul, show (2 * ε : ℂ) = ε + ε by ring, add_smul]
    abel
  calc ((1 / 2 : ℂ) • (1 + ε • T)) * ((1 / 2 : ℂ) • (1 + ε • T))
      = ((1 / 2 : ℂ) * (1 / 2)) • ((1 + ε • T) * (1 + ε • T)) := by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    _ = ((1 / 2 : ℂ) * (1 / 2)) • ((1 + ε * ε) • (1 : Matrix ι ι A) + (2 * ε) • T) := by
        rw [hsq]
    _ = (((1 / 2 : ℂ) * (1 / 2)) * (1 + ε * ε)) • (1 : Matrix ι ι A) +
          (((1 / 2 : ℂ) * (1 / 2)) * (2 * ε)) • T := by
        rw [smul_add, smul_smul, smul_smul]
    _ = (1 / 2 + (ε * ε - 1) / 4) • (1 : Matrix ι ι A) + (ε / 2) • T := by
        rw [show (1 / 2 : ℂ) * (1 / 2) * (1 + ε * ε) = 1 / 2 + (ε * ε - 1) / 4 by ring,
          show (1 / 2 : ℂ) * (1 / 2) * (2 * ε) = ε / 2 by ring]
    _ = (1 / 2 : ℂ) • (1 + ε • T) + ((ε * ε - 1) / 4) • (1 : Matrix ι ι A) := by
        rw [add_smul, smul_add, smul_smul, show (1 / 2 : ℂ) * ε = ε / 2 by ring]
        abel

/-- `sq2PartP ε p` is idempotent when `ε² = 1`. -/
theorem sq2PartP_idem (hA : ∀ x y : A, x * y = y * x) [Algebra ℂ A]
    (ε : ℂ) (hε : ε * ε = 1) {p : Mat A} (hp : p.IsIdem) :
    sq2PartP ε p * sq2PartP ε p = sq2PartP ε p := by
  have h1 : (sq2Part ε p).IsIdem := sq2Part_idem hA ε hε hp
  have hr : Matrix.reindex finProdFinEquiv finProdFinEquiv (sq2PartP ε p) =
      (sq2Part ε p).2 := sq2Part_reindex ε p
  have key : Matrix.reindex finProdFinEquiv finProdFinEquiv
        (sq2PartP ε p * sq2PartP ε p) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (sq2PartP ε p) := by
    rw [← reindex_mul_rect finProdFinEquiv finProdFinEquiv finProdFinEquiv
      (sq2PartP ε p) (sq2PartP ε p), hr]
    exact h1
  exact (Matrix.reindexRingEquiv A finProdFinEquiv).injective key

/-- `X * X - X` for `X = sq2PartP ε p` with `p` idempotent. -/
lemma sq2PartP_self_sub (hA : ∀ x y : A, x * y = y * x) [Algebra ℂ A] (ε : ℂ) {p : Mat A}
    (hp : p.IsIdem) :
    sq2PartP ε p * sq2PartP ε p - sq2PartP ε p =
      algebraMap ℂ A ((ε * ε - 1) / 4) • Matrix.kroneckerMap (· * ·) p.2 p.2 := by
  set M : Matrix (Fin p.1 × Fin p.1) (Fin p.1 × Fin p.1) A :=
    Matrix.kroneckerMap (· * ·) p.2 p.2 with hM
  set P : Matrix (Fin p.1 × Fin p.1) (Fin p.1 × Fin p.1) A :=
    (1 / 2 : ℂ) • (1 + ε • Equiv.Perm.permMatrix A (Equiv.prodComm (Fin p.1) (Fin p.1)))
    with hP
  have hMT : M * Equiv.Perm.permMatrix A (Equiv.prodComm (Fin p.1) (Fin p.1)) =
      Equiv.Perm.permMatrix A (Equiv.prodComm (Fin p.1) (Fin p.1)) * M := by
    rw [hM]
    exact kroneckerMap_rect_prodComm hA p.2
  have hMP : M * P = P * M := by
    rw [hP, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul,
      Matrix.mul_smul, hMT]
  have hMM : M * M = M := by
    rw [hM, mul_kronecker_rect hA p.2 p.2 p.2 p.2, hp]
  have hTT : Equiv.Perm.permMatrix A (Equiv.prodComm (Fin p.1) (Fin p.1)) *
      Equiv.Perm.permMatrix A (Equiv.prodComm (Fin p.1) (Fin p.1)) = 1 :=
    permMatrix_invol _ (fun x => by simp [Equiv.prodComm_apply])
  have hPP : P * P = P + ((ε * ε - 1) / 4) •
      (1 : Matrix (Fin p.1 × Fin p.1) (Fin p.1 × Fin p.1) A) := by
    rw [hP]
    exact proj_sq_eps ε _ hTT
  have hX : sq2PartP ε p = M * P := by
    rw [sq2PartP_eq_smul, hM, hP]
  calc sq2PartP ε p * sq2PartP ε p - sq2PartP ε p
      = M * P * (M * P) - M * P := by rw [hX]
    _ = M * (P * M) * P - M * P := by
        rw [← Matrix.mul_assoc (M * P) M P, Matrix.mul_assoc M P M]
    _ = M * (M * P) * P - M * P := by rw [hMP]
    _ = (M * M) * (P * P) - M * P := by
        rw [← Matrix.mul_assoc M M P, ← Matrix.mul_assoc (M * M) P P]
    _ = M * (P * P) - M * P := by rw [hMM]
    _ = M * (P + ((ε * ε - 1) / 4) •
          (1 : Matrix (Fin p.1 × Fin p.1) (Fin p.1 × Fin p.1) A)) - M * P := by rw [hPP]
    _ = ((ε * ε - 1) / 4) • M := by
        exact mul_add_smul_one_sub M P _
    _ = algebraMap ℂ A ((ε * ε - 1) / 4) • Matrix.kroneckerMap (· * ·) p.2 p.2 := by
        rw [← algMap_smul_eq_smul_C, hM]

end Sq2PartMvN

export Sq2PartMvN (sq2PartP_idem cls_sq2PartP_clsI)

open Sq2PartMvN

/-! ## The main statement -/

/-- `cls (sq2Part ε p)` only depends on the `MvN` class of `p`. -/
theorem sq2Part_MvN [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    (ε : ℂ) {p q : Mat A} (hp : p.IsIdem) (hq : q.IsIdem) (h : p.MvN q) :
    cls (sq2Part ε p) = cls (sq2Part ε q) := by
  obtain ⟨a, b, hba, hab⟩ := h
  rw [cls_sq2PartP_clsI ε p, cls_sq2PartP_clsI ε q]
  by_cases hε : ε * ε = 1
  · -- explicit `MvN` witnesses
    set A2 : Matrix (Fin q.1 × Fin q.1) (Fin p.1 × Fin p.1) A :=
      Matrix.kroneckerMap (· * ·) a a with hA2
    set B2 : Matrix (Fin p.1 × Fin p.1) (Fin q.1 × Fin q.1) A :=
      Matrix.kroneckerMap (· * ·) b b with hB2
    set Tp : Matrix (Fin p.1 × Fin p.1) (Fin p.1 × Fin p.1) A :=
      Equiv.Perm.permMatrix A (Equiv.prodComm (Fin p.1) (Fin p.1)) with hTp
    set Tq : Matrix (Fin q.1 × Fin q.1) (Fin q.1 × Fin q.1) A :=
      Equiv.Perm.permMatrix A (Equiv.prodComm (Fin q.1) (Fin q.1)) with hTq
    set Pp : Matrix (Fin p.1 × Fin p.1) (Fin p.1 × Fin p.1) A :=
      (1 / 2 : ℂ) • (1 + ε • Tp) with hPp
    set Pq : Matrix (Fin q.1 × Fin q.1) (Fin q.1 × Fin q.1) A :=
      (1 / 2 : ℂ) • (1 + ε • Tq) with hPq
    have hpq : Matrix.kroneckerMap (· * ·) p.2 p.2 = B2 * A2 := by
      rw [hA2, hB2, mul_kronecker_rect hA b b a a, hba]
    have hqp : Matrix.kroneckerMap (· * ·) q.2 q.2 = A2 * B2 := by
      rw [hA2, hB2, mul_kronecker_rect hA a a b b, hab]
    have hMPp : Matrix.kroneckerMap (· * ·) p.2 p.2 * Pp =
        Pp * Matrix.kroneckerMap (· * ·) p.2 p.2 := by
      rw [hPp]
      exact kronMap_proj_comm hA p.2 ε
    have hMPq : Matrix.kroneckerMap (· * ·) q.2 q.2 * Pq =
        Pq * Matrix.kroneckerMap (· * ·) q.2 q.2 := by
      rw [hPq]
      exact kronMap_proj_comm hA q.2 ε
    have hPB : B2 * Pq = Pp * B2 := by
      rw [hPq, hPp, hB2]
      exact (proj_mul_kron hA b ε).symm
    have hMPpk : (B2 * A2) * Pp = Pp * (B2 * A2) := by
      rw [← hpq]
      exact hMPp
    have hMPqk : (A2 * B2) * Pq = Pq * (A2 * B2) := by
      rw [← hqp]
      exact hMPq
    have hX : sq2PartP ε p = Pp * (B2 * A2) := by
      rw [sq2PartP_eq_smul, ← hTp, ← hPp, hpq]
      exact hMPpk
    have hY : sq2PartP ε q = Pq * (A2 * B2) := by
      rw [sq2PartP_eq_smul, ← hTq, ← hPq, hqp]
      exact hMPqk
    refine clsI_eq_of_MvN (Sq2PartMvN.sq2PartP_idem hA ε hε hp)
      (Sq2PartMvN.sq2PartP_idem hA ε hε hq)
      (u := Pq * A2) (v := B2) ?_ ?_
    · rw [hX, ← Matrix.mul_assoc, hPB, Matrix.mul_assoc]
    · rw [hY, Matrix.mul_assoc]
  · -- both classes vanish
    have hc : ((ε * ε - 1) / 4) ≠ 0 := by
      intro h0
      apply hε
      have h4 : (ε * ε - 1) / 4 * 4 = 0 := by rw [h0, zero_mul]
      rw [div_mul_cancel₀ _ (by norm_num : (4 : ℂ) ≠ 0)] at h4
      linear_combination h4
    rcases eq_or_ne (Matrix.kroneckerMap (· * ·) p.2 p.2) 0 with hM0 | hMne
    · have hp0 : p.2 = 0 := kroneckerMap_self_eq_zero hp hM0
      have hq0 : q.2 = 0 := by
        have h2 : q.2 * q.2 = 0 := by
          rw [← hab]
          calc (a * b) * (a * b) = a * (b * (a * b)) := by rw [Matrix.mul_assoc a b (a * b)]
            _ = a * ((b * a) * b) := by rw [← Matrix.mul_assoc b a b]
            _ = a * (p.2 * b) := by rw [hba]
            _ = 0 := by rw [hp0, Matrix.zero_mul, Matrix.mul_zero]
        rw [← hq, h2]
      have hX : sq2PartP ε p = 0 := by
        rw [sq2PartP_eq_smul, hp0]
        simp
      have hY : sq2PartP ε q = 0 := by
        rw [sq2PartP_eq_smul, hq0]
        simp
      rw [hX, hY]
      exact (clsI_zero (A := A) (ι := Fin p.1 × Fin p.1)).trans
        (clsI_zero (A := A) (ι := Fin q.1 × Fin q.1)).symm
    · have hMqne : Matrix.kroneckerMap (· * ·) q.2 q.2 ≠ 0 := by
        intro hq0
        apply hMne
        have hq2 : q.2 = 0 := kroneckerMap_self_eq_zero hq hq0
        have h2 : p.2 * p.2 = 0 := by
          rw [← hba]
          calc (b * a) * (b * a) = b * (a * (b * a)) := by rw [Matrix.mul_assoc b a (b * a)]
            _ = b * ((a * b) * a) := by rw [← Matrix.mul_assoc a b a]
            _ = b * (q.2 * a) := by rw [hab]
            _ = 0 := by rw [hq2, Matrix.zero_mul, Matrix.mul_zero]
        have hp2 : p.2 = 0 := by rw [← hp, h2]
        rw [hp2]
        simp
      have hXnot : sq2PartP ε p * sq2PartP ε p ≠ sq2PartP ε p := by
        intro hXidem
        refine hMne ?_
        have h0 : algebraMap ℂ A ((ε * ε - 1) / 4) •
            Matrix.kroneckerMap (· * ·) p.2 p.2 = 0 := by
          rw [← sq2PartP_self_sub hA ε hp, hXidem, sub_self]
        exact smul_eq_zero_of_ne hc h0
      have hYnot : sq2PartP ε q * sq2PartP ε q ≠ sq2PartP ε q := by
        intro hYidem
        refine hMqne ?_
        have h0 : algebraMap ℂ A ((ε * ε - 1) / 4) •
            Matrix.kroneckerMap (· * ·) q.2 q.2 = 0 := by
          rw [← sq2PartP_self_sub hA ε hq, hYidem, sub_self]
        exact smul_eq_zero_of_ne hc h0
      rw [clsI_zero_of_not_idem hXnot, clsI_zero_of_not_idem hYnot]

end

end Work.KT.Psi
