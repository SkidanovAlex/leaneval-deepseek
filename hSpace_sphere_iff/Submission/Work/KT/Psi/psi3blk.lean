import Mathlib
import Submission.Work.KT.Psi.psi3sum_Setup

/-!
# `Work.KT.Psi.psi3blk` — the block calculus for `ψ³`-additivity

Concrete matrix identities for the word decomposition of the triple tensor power of `p ⊕ q`:

* `permMatrix` conjugation;
* the triple Kronecker product `kron3m` (multiplicativity, behaviour under `cyc3`);
* the coordinate/word projectors `coord`, `eBlk` (idempotent, orthogonal, summing to `1`);
* the cyclic permutation matrix `uPerm` acting on the word projectors;
* the `p ⊕ q` block matrices `sumBlk`, `sumBlkP`, `sumBlkQ` and the resulting block splittings.
-/

namespace Work.KT.Psi

open Matrix

noncomputable section

variable {A : Type} [Ring A]

/-! ## Conjugation by a permutation matrix -/

theorem psi_pm_apply {S : Type} [Fintype S] [DecidableEq S] (σ : Equiv.Perm S) (i j : S) :
    Equiv.Perm.permMatrix A σ i j = if σ i = j then 1 else 0 := by
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]; simp

theorem mul_permMatrix {S : Type} [Fintype S] [DecidableEq S] (σ : Equiv.Perm S)
    (M : Matrix S S A) : M * Equiv.Perm.permMatrix A σ = M.submatrix id σ.symm := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id_eq, psi_pm_apply]
  rw [Finset.sum_eq_single (σ.symm j)]
  · rw [if_pos (Equiv.apply_symm_apply σ j), mul_one]
  · intro b _ hb; rw [if_neg (fun h => hb ((Equiv.eq_symm_apply σ).mpr h)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem permMatrix_mul' {S : Type} [Fintype S] [DecidableEq S] (σ : Equiv.Perm S)
    (M : Matrix S S A) : Equiv.Perm.permMatrix A σ * M = M.submatrix σ id := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id_eq, psi_pm_apply]
  rw [Finset.sum_eq_single (σ i)]
  · rw [if_pos rfl, one_mul]
  · intro b _ hb; rw [if_neg (fun h => hb h.symm), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem permMatrix_conj {S : Type} [Fintype S] [DecidableEq S] (σ : Equiv.Perm S)
    (M : Matrix S S A) :
    Equiv.Perm.permMatrix A σ * M * Equiv.Perm.permMatrix A σ.symm =
      Matrix.reindex σ.symm σ.symm M := by
  rw [permMatrix_mul', mul_permMatrix, Matrix.reindex_apply, Matrix.submatrix_submatrix]
  simp

theorem permMatrix_conj' {S : Type} [Fintype S] [DecidableEq S] (σ : Equiv.Perm S)
    (M : Matrix S S A) :
    Equiv.Perm.permMatrix A σ.symm * M * Equiv.Perm.permMatrix A σ =
      Matrix.reindex σ σ M := by
  rw [permMatrix_mul' σ.symm M, mul_permMatrix σ, Matrix.reindex_apply,
    Matrix.submatrix_submatrix]
  simp

/-! ## The triple Kronecker product -/

variable {S : Type} [Fintype S] [DecidableEq S]

theorem kron3m_mul' (hA : ∀ x y : A, x * y = y * x) (X X' Y Y' Z Z' : Matrix S S A) :
    kron3m X Y Z * kron3m X' Y' Z' = kron3m (X * X') (Y * Y') (Z * Z') := by
  letI : CommRing A := { ‹Ring A› with mul_comm := hA }
  show Matrix.kroneckerMap (· * ·) (Matrix.kroneckerMap (· * ·) X Y) Z *
      Matrix.kroneckerMap (· * ·) (Matrix.kroneckerMap (· * ·) X' Y') Z' = _
  rw [← Matrix.mul_kronecker_mul (Matrix.kroneckerMap (· * ·) X Y)
        (Matrix.kroneckerMap (· * ·) X' Y') Z Z',
      ← Matrix.mul_kronecker_mul X X' Y Y']
  rfl

theorem reindex_cyc3_kron3m (hA : ∀ x y : A, x * y = y * x) (X Y Z : Matrix S S A) :
    Matrix.reindex (cyc3 S) (cyc3 S) (kron3m X Y Z) = kron3m Z X Y := by
  letI : CommRing A := { ‹Ring A› with mul_comm := hA }
  ext u v
  rcases u with ⟨⟨u1, u2⟩, u3⟩
  rcases v with ⟨⟨v1, v2⟩, v3⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, kron3m_apply, Equiv.symm_symm,
    cyc3_symm_apply]
  ring

theorem reindex_symm_cyc3_kron3m (hA : ∀ x y : A, x * y = y * x) (X Y Z : Matrix S S A) :
    Matrix.reindex (cyc3 S).symm (cyc3 S).symm (kron3m X Y Z) = kron3m Y Z X := by
  letI : CommRing A := { ‹Ring A› with mul_comm := hA }
  ext u v
  rcases u with ⟨⟨u1, u2⟩, u3⟩
  rcases v with ⟨⟨v1, v2⟩, v3⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, kron3m_apply, Equiv.symm_symm,
    cyc3_apply]
  ring

theorem kron3m_sum₁ {ι : Type} [Fintype ι] (f : ι → Matrix S S A) (Y Z : Matrix S S A) :
    (∑ a, kron3m (f a) Y Z) = kron3m (∑ a, f a) Y Z := by
  ext u v
  rcases u with ⟨⟨u1, u2⟩, u3⟩; rcases v with ⟨⟨v1, v2⟩, v3⟩
  simp only [Matrix.sum_apply, kron3m_apply]
  rw [Finset.sum_mul, Finset.sum_mul]

theorem kron3m_sum₂ {ι : Type} [Fintype ι] (X : Matrix S S A) (g : ι → Matrix S S A)
    (Z : Matrix S S A) : (∑ a, kron3m X (g a) Z) = kron3m X (∑ a, g a) Z := by
  ext u v
  rcases u with ⟨⟨u1, u2⟩, u3⟩; rcases v with ⟨⟨v1, v2⟩, v3⟩
  simp only [Matrix.sum_apply, kron3m_apply]
  rw [Finset.mul_sum, Finset.sum_mul]

theorem kron3m_sum₃ {ι : Type} [Fintype ι] (X Y : Matrix S S A) (h : ι → Matrix S S A) :
    (∑ a, kron3m X Y (h a)) = kron3m X Y (∑ a, h a) := by
  ext u v
  rcases u with ⟨⟨u1, u2⟩, u3⟩; rcases v with ⟨⟨v1, v2⟩, v3⟩
  simp only [Matrix.sum_apply, kron3m_apply]
  rw [Finset.mul_sum]

theorem kron3m_zero₁ (Y Z : Matrix S S A) : kron3m 0 Y Z = 0 := by
  ext u v; simp [kron3m_apply]
theorem kron3m_zero₂ (X Z : Matrix S S A) : kron3m X 0 Z = 0 := by
  ext u v; simp [kron3m_apply]
theorem kron3m_zero₃ (X Y : Matrix S S A) : kron3m X Y 0 = 0 := by
  ext u v; simp [kron3m_apply]

theorem kron3m_one : kron3m (1 : Matrix S S A) 1 1 = 1 := by
  simp only [kron3m]
  rw [Matrix.one_kronecker_one, Matrix.one_kronecker_one]

theorem kron3g_mul_self (hA : ∀ x y : A, x * y = y * x) (X : Matrix S S A) :
    kron3g X * kron3g X = kron3g (X * X) := by
  show kron3m X X X * kron3m X X X = kron3m (X * X) (X * X) (X * X)
  rw [kron3m_mul' hA]

theorem kron3g_idem (hA : ∀ x y : A, x * y = y * x) {X : Matrix S S A} (hX : X * X = X) :
    kron3g X * kron3g X = kron3g X := by
  rw [kron3g_mul_self hA, hX]

/-! ## The coordinate projectors and the word projectors -/

theorem coord_mul_self {m n : ℕ} (i : Fin 2) :
    coord (A := A) (m := m) (n := n) i * coord i = coord i := by
  fin_cases i <;> ext a b <;> simp [coord, Matrix.fromBlocks_multiply]

theorem coord_orth {m n : ℕ} {i j : Fin 2} (h : i ≠ j) :
    coord (A := A) (m := m) (n := n) i * coord j = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [coord, Matrix.fromBlocks_multiply]

theorem coord_sum {m n : ℕ} :
    coord (A := A) (m := m) (n := n) 0 + coord 1 = 1 := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [coord, Matrix.one_apply, Sum.inl.injEq, Sum.inr.injEq]

theorem coord_zero_ne_one : (0 : Fin 2) ≠ 1 := by decide

theorem eBlk_mul {m n : ℕ} (hA : ∀ x y : A, x * y = y * x)
    (w w' : (Fin 2 × Fin 2) × Fin 2) :
    eBlk (A := A) (m := m) (n := n) w * eBlk w' =
      kron3m (coord w.1.1 * coord w'.1.1) (coord w.1.2 * coord w'.1.2)
        (coord w.2 * coord w'.2) := by
  rw [eBlk, eBlk, kron3m_mul' hA]

theorem eBlk_idem {m n : ℕ} (hA : ∀ x y : A, x * y = y * x)
    (w : (Fin 2 × Fin 2) × Fin 2) :
    eBlk (A := A) (m := m) (n := n) w * eBlk w = eBlk w := by
  rw [eBlk_mul hA]
  simp only [coord_mul_self, eBlk]

theorem eBlk_orth {m n : ℕ} (hA : ∀ x y : A, x * y = y * x)
    {w w' : (Fin 2 × Fin 2) × Fin 2} (h : w ≠ w') :
    eBlk (A := A) (m := m) (n := n) w * eBlk w' = 0 := by
  rw [eBlk_mul hA]
  by_cases h1 : w.1.1 = w'.1.1
  · by_cases h2 : w.1.2 = w'.1.2
    · have h3 : w.2 ≠ w'.2 := fun h3 => h (by ext <;> simp_all)
      rw [h1, h2, coord_mul_self, coord_mul_self, coord_orth h3, kron3m_zero₃]
    · rw [h1, coord_mul_self, coord_orth h2, kron3m_zero₂]
  · rw [coord_orth h1, kron3m_zero₁]

theorem eBlk_sum {m n : ℕ} (hA : ∀ x y : A, x * y = y * x) :
    (∑ w : (Fin 2 × Fin 2) × Fin 2, eBlk (A := A) (m := m) (n := n) w) = 1 := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [eBlk]
  simp only [kron3m_sum₃, kron3m_sum₂, kron3m_sum₁, Fin.sum_univ_two, coord_sum, kron3m_one]

/-! ## The cyclic permutation matrix -/

theorem cyc3_sq_eq_symm (S : Type) : cyc3 S * cyc3 S = (cyc3 S).symm := by
  refine Equiv.ext ?_
  intro x
  rcases x with ⟨⟨a, b⟩, c⟩
  rfl

theorem uPerm_cube (S : Type) [Fintype S] [DecidableEq S] :
    uPerm A S * uPerm A S * uPerm A S = 1 := by
  have hc : cyc3 S * (cyc3 S * cyc3 S) = 1 := by rw [← mul_assoc]; exact cyc3_cube S
  have h : Equiv.Perm.permMatrix A (cyc3 S * (cyc3 S * cyc3 S)) =
      (Equiv.Perm.permMatrix A (cyc3 S) * Equiv.Perm.permMatrix A (cyc3 S)) *
        Equiv.Perm.permMatrix A (cyc3 S) := by
    rw [Matrix.permMatrix_mul, Matrix.permMatrix_mul]
  rw [hc, Matrix.permMatrix_one] at h
  show Equiv.Perm.permMatrix A (cyc3 S) * Equiv.Perm.permMatrix A (cyc3 S) *
      Equiv.Perm.permMatrix A (cyc3 S) = 1
  exact h.symm

theorem uPerm_sq (S : Type) [Fintype S] [DecidableEq S] :
    uPerm A S * uPerm A S = Equiv.Perm.permMatrix A (cyc3 S).symm := by
  show Equiv.Perm.permMatrix A (cyc3 S) * Equiv.Perm.permMatrix A (cyc3 S) = _
  rw [← Matrix.permMatrix_mul, cyc3_sq_eq_symm]

theorem uPerm_eBlk_conj {m n : ℕ} (hA : ∀ x y : A, x * y = y * x)
    (w : (Fin 2 × Fin 2) × Fin 2) :
    uPerm A (Fin m ⊕ Fin n) * eBlk w * (uPerm A (Fin m ⊕ Fin n) * uPerm A (Fin m ⊕ Fin n))
      = eBlk (rotW w) := by
  have h1 : uPerm A (Fin m ⊕ Fin n) = Equiv.Perm.permMatrix A (cyc3 (Fin m ⊕ Fin n)) := rfl
  have h2 : uPerm A (Fin m ⊕ Fin n) * uPerm A (Fin m ⊕ Fin n) =
      Equiv.Perm.permMatrix A (cyc3 (Fin m ⊕ Fin n)).symm := uPerm_sq _
  rw [h2, h1, permMatrix_conj, eBlk, reindex_symm_cyc3_kron3m hA, eBlk]
  rfl

theorem uPerm_sq_eBlk_conj {m n : ℕ} (hA : ∀ x y : A, x * y = y * x)
    (w : (Fin 2 × Fin 2) × Fin 2) :
    (uPerm A (Fin m ⊕ Fin n) * uPerm A (Fin m ⊕ Fin n)) * eBlk w * uPerm A (Fin m ⊕ Fin n)
      = eBlk (rotW (rotW w)) := by
  have h1 : uPerm A (Fin m ⊕ Fin n) = Equiv.Perm.permMatrix A (cyc3 (Fin m ⊕ Fin n)) := rfl
  have h2 : uPerm A (Fin m ⊕ Fin n) * uPerm A (Fin m ⊕ Fin n) =
      Equiv.Perm.permMatrix A (cyc3 (Fin m ⊕ Fin n)).symm := uPerm_sq _
  rw [h2, h1, permMatrix_conj', eBlk, reindex_cyc3_kron3m hA, eBlk]
  rfl

theorem orb3_eBlk {m n : ℕ} (hA : ∀ x y : A, x * y = y * x)
    (w : (Fin 2 × Fin 2) × Fin 2) :
    orb3 (Fin m ⊕ Fin n) (eBlk (A := A) (m := m) (n := n) w) =
      eBlk w + eBlk (rotW w) + eBlk (rotW (rotW w)) := by
  rw [orb3, uPerm_eBlk_conj hA, uPerm_sq_eBlk_conj hA]

/-! ## The `p ⊕ q` blocks -/

variable {p q : Mat A}

theorem sumBlk_mul_self (hp : p.IsIdem) (hq : q.IsIdem) :
    sumBlk p q * sumBlk p q = sumBlk p q := by
  have hp' : p.2 * p.2 = p.2 := hp
  have hq' : q.2 * q.2 = q.2 := hq
  rw [sumBlk, Matrix.fromBlocks_multiply, hp', hq']
  simp

theorem sumBlk_mul_coord_zero :
    sumBlk p q * coord (m := p.1) (n := q.1) 0 = sumBlkP p q := by
  rw [sumBlk, sumBlkP, coord, if_pos rfl, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero]

theorem sumBlk_mul_coord_one :
    sumBlk p q * coord (m := p.1) (n := q.1) 1 = sumBlkQ p q := by
  rw [sumBlk, sumBlkQ, coord, if_neg (by decide), Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

theorem coord_zero_mul_sumBlk :
    coord (m := p.1) (n := q.1) 0 * sumBlk p q = sumBlkP p q := by
  rw [sumBlk, sumBlkP, coord, if_pos rfl, Matrix.fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero]

theorem coord_one_mul_sumBlk :
    coord (m := p.1) (n := q.1) 1 * sumBlk p q = sumBlkQ p q := by
  rw [sumBlk, sumBlkQ, coord, if_neg (by decide), Matrix.fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

theorem sumBlk_mul_coord (hA : ∀ x y : A, x * y = y * x) (i : Fin 2) :
    sumBlk p q * coord (m := p.1) (n := q.1) i =
      coord (m := p.1) (n := q.1) i * sumBlk p q := by
  fin_cases i
  · show sumBlk p q * coord (m := p.1) (n := q.1) 0 =
      coord (m := p.1) (n := q.1) 0 * sumBlk p q
    rw [sumBlk_mul_coord_zero, coord_zero_mul_sumBlk]
  · show sumBlk p q * coord (m := p.1) (n := q.1) 1 =
      coord (m := p.1) (n := q.1) 1 * sumBlk p q
    rw [sumBlk_mul_coord_one, coord_one_mul_sumBlk]

/-- `kron3g (sumBlk p q) * eBlk w` in block form. -/
theorem kron3g_sumBlk_mul_eBlk (hA : ∀ x y : A, x * y = y * x)
    (w : (Fin 2 × Fin 2) × Fin 2) :
    kron3g (sumBlk p q) * eBlk (A := A) (m := p.1) (n := q.1) w =
      kron3m (sumBlk p q * coord w.1.1) (sumBlk p q * coord w.1.2)
        (sumBlk p q * coord w.2) := by
  rw [kron3g, eBlk, kron3m_mul' hA]

theorem kron3g_sumBlk_comm_eBlk (hA : ∀ x y : A, x * y = y * x)
    (w : (Fin 2 × Fin 2) × Fin 2) :
    kron3g (sumBlk p q) * eBlk (A := A) (m := p.1) (n := q.1) w =
      eBlk w * kron3g (sumBlk p q) := by
  rw [kron3g_sumBlk_mul_eBlk hA, eBlk, kron3g, kron3m_mul' hA,
    ← sumBlk_mul_coord hA w.1.1, ← sumBlk_mul_coord hA w.1.2, ← sumBlk_mul_coord hA w.2]

theorem kron3g_sumBlk_mul_eBlk_w000 (hA : ∀ x y : A, x * y = y * x) :
    kron3g (sumBlk p q) * eBlk (A := A) (m := p.1) (n := q.1) w000 = kron3g (sumBlkP p q) := by
  rw [kron3g_sumBlk_mul_eBlk hA]
  simp only [w000]
  rw [sumBlk_mul_coord_zero, kron3g]

theorem kron3g_sumBlk_mul_eBlk_w111 (hA : ∀ x y : A, x * y = y * x) :
    kron3g (sumBlk p q) * eBlk (A := A) (m := p.1) (n := q.1) w111 = kron3g (sumBlkQ p q) := by
  rw [kron3g_sumBlk_mul_eBlk hA]
  simp only [w111]
  rw [sumBlk_mul_coord_one, kron3g]

theorem kron3g_sumBlk_idem (hA : ∀ x y : A, x * y = y * x) (hp : p.IsIdem) (hq : q.IsIdem) :
    kron3g (sumBlk p q) * kron3g (sumBlk p q) = kron3g (sumBlk p q) :=
  kron3g_idem hA (sumBlk_mul_self hp hq)

theorem kron3g_sumBlk_comm_uPerm (hA : ∀ x y : A, x * y = y * x) :
    kron3g (sumBlk p q) * uPerm A (Fin p.1 ⊕ Fin q.1) =
      uPerm A (Fin p.1 ⊕ Fin q.1) * kron3g (sumBlk p q) := by
  letI : CommRing A := { ‹Ring A› with mul_comm := hA }
  show kron3g (sumBlk p q) * Equiv.Perm.permMatrix A (cyc3 (Fin p.1 ⊕ Fin q.1)) =
      Equiv.Perm.permMatrix A (cyc3 (Fin p.1 ⊕ Fin q.1)) * kron3g (sumBlk p q)
  rw [mul_permMatrix, permMatrix_mul']
  ext i j
  simp only [Matrix.submatrix_apply, id_eq, kron3g_apply, cyc3_apply, cyc3_symm_apply]
  ring

end

end Work.KT.Psi
