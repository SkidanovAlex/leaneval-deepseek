import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Psi.Basic
import Submission.Work.KT.Psi.cubeAux
import Submission.Work.KT.Psi.k3Aux
import Submission.Work.KT.Psi.cubeMvNAux
import Submission.Work.KT.Psi.kron3_mul
import Submission.Work.KT.Psi.cls_split
import Submission.Work.KT.Psi.OrbitBasic

namespace Work.KT.Psi

open Matrix

noncomputable section

/-- Rotating a product of three commuting elements: `(p * q) * r = (q * r) * p`. -/
lemma cubeMvN_mul_rotate {A : Type} [Ring A] (hA : ∀ x y : A, x * y = y * x) (p q r : A) :
    (p * q) * r = (q * r) * p := by
  rw [mul_assoc, hA p (q * r)]

/-! ## Rectangular equivariance of the tensor cube under the cyclic permutation

`kron3r a = a ⊗ a ⊗ a` for a (possibly rectangular) matrix `a : Matrix (Fin m) (Fin k) A`.
Cyclically permuting the three tensor factors on the row side and on the column side is the same
operation, so the permutation matrix of `cycPermP m` (rows) commutes with `kron3r a` up to moving
to the permutation matrix of `cycPermP k` (columns). -/

theorem cubeMvN_kron3r_permMatrix_comm {A : Type} [Ring A] (hA : ∀ x y : A, x * y = y * x)
    {m k : ℕ} (a : Matrix (Fin m) (Fin k) A) :
    Equiv.Perm.permMatrix A (cycPermP m) * kron3r a =
      kron3r a * Equiv.Perm.permMatrix A (cycPermP k) := by
  have key : ∀ (x : (Fin m × Fin m) × Fin m) (y : (Fin k × Fin k) × Fin k),
      (Equiv.Perm.permMatrix A (cycPermP m) * kron3r a) x y =
        (kron3r a * Equiv.Perm.permMatrix A (cycPermP k)) x y := by
    intro x y
    have e1 : (cycPermP m x).1.1 = x.2 := rfl
    have e2 : (cycPermP m x).1.2 = x.1.1 := rfl
    have e3 : (cycPermP m x).2 = x.1.2 := rfl
    have f1 : ((cycPermP k).symm y).1.1 = y.1.2 := rfl
    have f2 : ((cycPermP k).symm y).1.2 = y.2 := rfl
    have f3 : ((cycPermP k).symm y).2 = y.1.1 := rfl
    have hL : (Equiv.Perm.permMatrix A (cycPermP m) * kron3r a) x y =
        (a x.2 y.1.1 * a x.1.1 y.1.2) * a x.1.2 y.2 := by
      rw [Matrix.mul_apply, Finset.sum_eq_single (cycPermP m x)]
      · rw [Work.KT.permMatrix_apply', if_pos rfl, one_mul, kron3r_apply, e1, e2, e3]
      · intro b _ hb
        rw [Work.KT.permMatrix_apply', if_neg (fun h => hb h.symm), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hR : (kron3r a * Equiv.Perm.permMatrix A (cycPermP k)) x y =
        (a x.1.1 y.1.2 * a x.1.2 y.2) * a x.2 y.1.1 := by
      rw [Matrix.mul_apply, Finset.sum_eq_single ((cycPermP k).symm y)]
      · rw [Work.KT.permMatrix_apply', if_pos (Equiv.apply_symm_apply (cycPermP k) y), mul_one,
          kron3r_apply, f1, f2, f3]
      · intro b _ hb
        rw [Work.KT.permMatrix_apply',
          if_neg (fun h => hb (by rw [← h]; exact (Equiv.symm_apply_apply (cycPermP k) b).symm)),
          mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hL, hR]
    exact cubeMvN_mul_rotate hA _ _ _
  ext x y
  exact key x y

/-- The order-three spectral projector `cubeW` intertwines the tensor cube. -/
theorem cubeMvN_cubeW_kron3r_comm {A : Type} [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    (lam : ℂ) {m k : ℕ} (a : Matrix (Fin m) (Fin k) A) :
    kron3r a * cubeW (A := A) k lam = cubeW (A := A) m lam * kron3r a := by
  have hc : Equiv.Perm.permMatrix A (cycPermP m) * kron3r a =
      kron3r a * Equiv.Perm.permMatrix A (cycPermP k) := cubeMvN_kron3r_permMatrix_comm hA a
  have hcc : (Equiv.Perm.permMatrix A (cycPermP m) * Equiv.Perm.permMatrix A (cycPermP m)) *
        kron3r a =
      kron3r a * (Equiv.Perm.permMatrix A (cycPermP k) *
        Equiv.Perm.permMatrix A (cycPermP k)) := by
    rw [Matrix.mul_assoc, hc, ← Matrix.mul_assoc, hc, Matrix.mul_assoc]
  rw [cubeW, cubeW]
  simp only [algebraMap_smul_eq_smul_C, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul,
    Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
  simp only [hc, hcc]

/-! ## `cubeW` is the spectral projector of the cyclic action -/

/-- `cubeW` written with complex scalars. -/
theorem cubeMvN_cubeW_eq_smul {A : Type} [Ring A] [Algebra ℂ A] (n : ℕ) (lam : ℂ) :
    cubeW (A := A) n lam =
      (1 / 3 : ℂ) • (1 + lam⁻¹ • Equiv.Perm.permMatrix A (cycPermP n) +
        (lam⁻¹) ^ 2 • (Equiv.Perm.permMatrix A (cycPermP n) *
          Equiv.Perm.permMatrix A (cycPermP n))) := by
  rw [cubeW]
  simp only [algebraMap_smul_eq_smul_C]

/-- The orbit projector of the cyclic permutation at `k = 3`, written out. -/
theorem cubeMvN_orbitSpec3_eq {A : Type} [Ring A] [Algebra ℂ A] (n : ℕ) (lam : ℂ) :
    orbitSpec lam (Equiv.Perm.permMatrix A (cycPermP n)) 3 =
      (1 / 3 : ℂ) • (1 + lam⁻¹ • Equiv.Perm.permMatrix A (cycPermP n) +
        (lam⁻¹) ^ 2 • (Equiv.Perm.permMatrix A (cycPermP n) *
          Equiv.Perm.permMatrix A (cycPermP n))) := by
  rw [orbitSpec, geoSum, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [qg_pow]
  simp only [pow_zero, one_smul, pow_one]
  rw [pow_two (Equiv.Perm.permMatrix A (cycPermP n))]
  have h3 : (((3 : ℕ) : ℂ))⁻¹ = (1 / 3 : ℂ) := by norm_num
  simp only [h3]

/-- `cubeW` is the spectral projector `orbitSpec λ (cyclic permutation) 3`. -/
theorem cubeMvN_cubeW_eq_orbitSpec {A : Type} [Ring A] [Algebra ℂ A] (n : ℕ) (lam : ℂ) :
    cubeW (A := A) n lam = orbitSpec lam (Equiv.Perm.permMatrix A (cycPermP n)) 3 :=
  (cubeMvN_cubeW_eq_smul n lam).trans (cubeMvN_orbitSpec3_eq n lam).symm

/-- `cubeW` is idempotent when `λ ^ 3 = 1`. -/
theorem cubeMvN_cubeW_mul_self {A : Type} [Ring A] [Algebra ℂ A] (n : ℕ) (lam : ℂ)
    (hlam : lam ^ 3 = 1) :
    cubeW (A := A) n lam * cubeW (A := A) n lam = cubeW (A := A) n lam := by
  have hg : (Equiv.Perm.permMatrix A (cycPermP n)) ^ 3 = 1 := by
    rw [pow_three']
    exact permMatrix_cycPermP_cube
  rw [cubeMvN_cubeW_eq_orbitSpec n lam]
  exact orbitSpec_idem (k := 3) (by norm_num) (qg_pow_eq_one hg hlam)

/-! ## Idempotency of `cubePartP` -/

theorem cubeMvN_cubePartP_idem {A : Type} [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    (lam : ℂ) (hlam : lam ^ 3 = 1) {p : Mat A} (hp : p.IsIdem) :
    cubePartP (A := A) lam p * cubePartP (A := A) lam p = cubePartP (A := A) lam p := by
  have hp2 : p.2 * p.2 = p.2 := hp
  have hK : kron3r p.2 * kron3r p.2 = kron3r p.2 := by
    rw [kron3_mul hA p.2 p.2, hp2]
  have hKW : kron3r p.2 * cubeW (A := A) p.1 lam = cubeW (A := A) p.1 lam * kron3r p.2 :=
    cubeMvN_cubeW_kron3r_comm hA lam p.2
  have hWW : cubeW (A := A) p.1 lam * cubeW (A := A) p.1 lam = cubeW (A := A) p.1 lam :=
    cubeMvN_cubeW_mul_self p.1 lam hlam
  rw [cubePartP_eq_kron3r]
  calc (kron3r p.2 * cubeW (A := A) p.1 lam) * (kron3r p.2 * cubeW (A := A) p.1 lam)
      = kron3r p.2 * (cubeW (A := A) p.1 lam * kron3r p.2) * cubeW (A := A) p.1 lam := by
        noncomm_ring
    _ = kron3r p.2 * (kron3r p.2 * cubeW (A := A) p.1 lam) * cubeW (A := A) p.1 lam := by
        rw [← hKW]
    _ = (kron3r p.2 * kron3r p.2) * (cubeW (A := A) p.1 lam * cubeW (A := A) p.1 lam) := by
        noncomm_ring
    _ = kron3r p.2 * cubeW (A := A) p.1 lam := by rw [hK, hWW]

/-! ## Classes of Murray–von Neumann equivalent matrices over different index types -/

/-- Reindexing a rectangular product: `reindex` pushes through matrix multiplication, with the
rows/columns transported separately. -/
lemma cubeMvN_reindex_mul_rect {A : Type} [AddCommMonoid A] [Mul A]
    {m m' n n' p p' : Type} [Fintype n] [Fintype n']
    (e : m ≃ m') (f : n ≃ n') (g : p ≃ p') (X : Matrix m n A) (Y : Matrix n p A) :
    Matrix.reindex e f X * Matrix.reindex f g Y = Matrix.reindex e g (X * Y) := by
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply]
  exact Matrix.submatrix_mul_equiv X Y e.symm f.symm g.symm

/-- `clsE` is invariant under Murray–von Neumann equivalence across index types. -/
theorem cubeMvN_clsE_eq_of_MvN {R : Type} [Ring R] {ι κ : Type} [Fintype ι] [Fintype κ]
    {X : Matrix ι ι R} {Y : Matrix κ κ R} (hX : X * X = X) (hY : Y * Y = Y)
    {u : Matrix κ ι R} {v : Matrix ι κ R} (hvu : v * u = X) (huv : u * v = Y)
    (n : ℕ) (e : ι ≃ Fin n) (m : ℕ) (f : κ ≃ Fin m) :
    Work.KT.clsE X n e = Work.KT.clsE Y m f := by
  have hidemX : Work.KT.Mat.IsIdem (⟨n, Matrix.reindex e e X⟩ : Mat R) := by
    show Matrix.reindex e e X * Matrix.reindex e e X = Matrix.reindex e e X
    rw [cubeMvN_reindex_mul_rect e e e X X, hX]
  have hidemY : Work.KT.Mat.IsIdem (⟨m, Matrix.reindex f f Y⟩ : Mat R) := by
    show Matrix.reindex f f Y * Matrix.reindex f f Y = Matrix.reindex f f Y
    rw [cubeMvN_reindex_mul_rect f f f Y Y, hY]
  have hMvN : Mat.MvN (⟨n, Matrix.reindex e e X⟩ : Mat R) ⟨m, Matrix.reindex f f Y⟩ :=
    ⟨Matrix.reindex f e u, Matrix.reindex e f v,
      (by rw [cubeMvN_reindex_mul_rect e f e v u, hvu] :
        Matrix.reindex e f v * Matrix.reindex f e u = Matrix.reindex e e X),
      (by rw [cubeMvN_reindex_mul_rect f e f u v, huv] :
        Matrix.reindex f e u * Matrix.reindex e f v = Matrix.reindex f f Y)⟩
  have h := Work.KT.cls_eq_of_MvN hidemX hidemY hMvN
  simpa only [Work.KT.clsE, Work.KT.Mat.ofIdx] using h

/-! ## The main theorem -/

theorem cubePart_MvN {A : Type} [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    (lam : ℂ) (hlam : lam ^ 3 = 1) {p q : Mat A} (hp : p.IsIdem) (hq : q.IsIdem)
    (h : p.MvN q) : cls (cubePart lam p) = cls (cubePart lam q) := by
  obtain ⟨a, b, hba, hab⟩ := h
  have hp2 : p.2 * p.2 = p.2 := hp
  have hq2 : q.2 * q.2 = q.2 := hq
  set X := cubePartP (A := A) lam p with hXdef
  set Y := cubePartP (A := A) lam q with hYdef
  have hXfac : X = kron3r p.2 * cubeW (A := A) p.1 lam := cubePartP_eq_kron3r lam p
  have hYfac : Y = kron3r q.2 * cubeW (A := A) q.1 lam := cubePartP_eq_kron3r lam q
  have hXX : X * X = X := by rw [hXfac]; exact cubeMvN_cubePartP_idem hA lam hlam hp
  have hYY : Y * Y = Y := by rw [hYfac]; exact cubeMvN_cubePartP_idem hA lam hlam hq
  have hKKp : kron3r p.2 * kron3r p.2 = kron3r p.2 := by
    rw [kron3_mul hA p.2 p.2, hp2]
  have hKKq : kron3r q.2 * kron3r q.2 = kron3r q.2 := by
    rw [kron3_mul hA q.2 q.2, hq2]
  have hBA : kron3r b * kron3r a = kron3r p.2 := by rw [kron3_mul hA b a, hba]
  have hAB : kron3r a * kron3r b = kron3r q.2 := by rw [kron3_mul hA a b, hab]
  have hqa : q.2 * a = a * p.2 := by rw [← hab, Matrix.mul_assoc, hba]
  have hpb : p.2 * b = b * q.2 := by rw [← hba, Matrix.mul_assoc, hab]
  have hKqA : kron3r q.2 * kron3r a = kron3r a * kron3r p.2 := by
    rw [kron3_mul hA q.2 a, kron3_mul hA a p.2, hqa]
  have hKpB : kron3r p.2 * kron3r b = kron3r b * kron3r q.2 := by
    rw [kron3_mul hA p.2 b, kron3_mul hA b q.2, hpb]
  have hSqA : cubeW (A := A) q.1 lam * kron3r a = kron3r a * cubeW (A := A) p.1 lam :=
    (cubeMvN_cubeW_kron3r_comm hA lam a).symm
  have hSpB : cubeW (A := A) p.1 lam * kron3r b = kron3r b * cubeW (A := A) q.1 lam :=
    (cubeMvN_cubeW_kron3r_comm hA lam b).symm
  have hKpX : kron3r p.2 * X = X := by rw [hXfac, ← Matrix.mul_assoc, hKKp]
  have hKqY : kron3r q.2 * Y = Y := by rw [hYfac, ← Matrix.mul_assoc, hKKq]
  have hYA : Y * kron3r a = kron3r a * X := by
    rw [hYfac, hXfac]
    rw [Matrix.mul_assoc, hSqA, ← Matrix.mul_assoc, hKqA, Matrix.mul_assoc]
  have hXB : X * kron3r b = kron3r b * Y := by
    rw [hXfac, hYfac]
    rw [Matrix.mul_assoc, hSpB, ← Matrix.mul_assoc, hKpB, Matrix.mul_assoc]
  have hvu : (kron3r b * Y) * (kron3r a * X) = X := by
    rw [Matrix.mul_assoc (kron3r b) Y (kron3r a * X)]
    rw [← Matrix.mul_assoc Y (kron3r a) X]
    rw [hYA]
    rw [Matrix.mul_assoc (kron3r a) X X]
    rw [hXX]
    rw [← Matrix.mul_assoc (kron3r b) (kron3r a) X]
    rw [hBA]
    exact hKpX
  have huv : (kron3r a * X) * (kron3r b * Y) = Y := by
    rw [Matrix.mul_assoc (kron3r a) X (kron3r b * Y)]
    rw [← Matrix.mul_assoc X (kron3r b) Y]
    rw [hXB]
    rw [Matrix.mul_assoc (kron3r b) Y Y]
    rw [hYY]
    rw [← Matrix.mul_assoc (kron3r a) (kron3r b) Y]
    rw [hAB]
    exact hKqY
  have hmain : Work.KT.clsE X (p.1 * p.1 * p.1) (cycIdx p.1).symm =
      Work.KT.clsE Y (q.1 * q.1 * q.1) (cycIdx q.1).symm :=
    cubeMvN_clsE_eq_of_MvN hXX hYY hvu huv (p.1 * p.1 * p.1) (cycIdx p.1).symm
      (q.1 * q.1 * q.1) (cycIdx q.1).symm
  exact (cls_cubePartP lam p).symm.trans (hmain.trans (cls_cubePartP lam q))

end

end Work.KT.Psi
