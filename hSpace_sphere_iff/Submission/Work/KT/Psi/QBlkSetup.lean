import Mathlib
import Submission.Work.KT.Psi.psi3sum_Setup

/-!
# `Work.KT.Psi.QBlkSetup` — the `q`-word inside the triple tensor power of `p ⊕ q`

The index type of `kron3g (sumBlkQ p q)` is `SQ (Fin p.1 ⊕ Fin q.1)`, the triple tensor power of
the block index set of `p ⊕ q`.  Since `sumBlkQ p q` is the block matrix with `q.2` in the
`q`-block and `0` elsewhere, the matrix `kron3g (sumBlkQ p q)` is supported on the single "word"
all of whose entries lie in the `q`-block (the word `(1,1,1)`), and the cyclic permutation
`cyc3` preserves that word.  This file isolates that word:

* `jQ n m : SQ (Fin m) → SQ (Fin n ⊕ Fin m)` — the inclusion of the word;
* `isQ x` — the predicate "`x` lies in that word";
* `blkE n m : SQ (Fin m) ≃ {x // isQ x}` — the canonical equivalence.

It also records the two entry computations on which the class computation rests, both of which
are *entrywise* and therefore need no commutativity of the coefficient ring:

* `kron3g_sumBlkQ_*` — the entries of the triple tensor cube of `sumBlkQ p q`;
* `Cp_apply`, `Cp_jQ`, `Cp_eq_zero_of_isQ_not_isQ` — the entries of the cyclic spectral
  projector `Cp` on the `q`-word.
-/

namespace Work.KT.Psi

open Matrix

noncomputable section

/-! ## The `q`-word -/

/-- The inclusion of the `q`-word into the triple tensor-power index of `p ⊕ q`. -/
def jQ {n m : ℕ} (x : SQ (Fin m)) : SQ (Fin n ⊕ Fin m) :=
  ((Sum.inr x.1.1, Sum.inr x.1.2), Sum.inr x.2)

@[simp] theorem jQ_apply {n m : ℕ} (x : SQ (Fin m)) :
    jQ (n := n) x = ((Sum.inr x.1.1, Sum.inr x.1.2), Sum.inr x.2) := rfl

/-- The `q`-word of `SQ (Fin n ⊕ Fin m)`: the triples all of whose entries lie in the right
summand. -/
def isQ {n m : ℕ} (x : SQ (Fin n ⊕ Fin m)) : Prop := ∃ y : SQ (Fin m), jQ (n := n) y = x

theorem isQ_jQ {n m : ℕ} (x : SQ (Fin m)) : isQ (jQ (n := n) x) := ⟨x, rfl⟩

theorem jQ_injective {n m : ℕ} : Function.Injective (jQ (n := n) (m := m)) := by
  intro a b h
  simp only [jQ, Prod.mk.injEq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact Prod.ext (Prod.ext (Sum.inr_injective h1) (Sum.inr_injective h2)) (Sum.inr_injective h3)

theorem jQ_inj_eq {n m : ℕ} (x y : SQ (Fin m)) : jQ (n := n) x = jQ (n := n) y ↔ x = y :=
  ⟨fun h => jQ_injective h, fun h => by rw [h]⟩

theorem isQ_iff {n m : ℕ} (x : SQ (Fin n ⊕ Fin m)) :
    isQ x ↔ ∃ a b c : Fin m, x = ((Sum.inr a, Sum.inr b), Sum.inr c) := by
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨y.1.1, y.1.2, y.2, rfl⟩
  · rintro ⟨a, b, c, rfl⟩; exact ⟨((a, b), c), rfl⟩

/-- The canonical equivalence `SQ (Fin m) ≃ {x // isQ x}`. -/
def blkE (n m : ℕ) : SQ (Fin m) ≃ {x : SQ (Fin n ⊕ Fin m) // isQ x} where
  toFun x := ⟨jQ x, isQ_jQ x⟩
  invFun x := x.2.choose
  left_inv x := jQ_injective (Classical.choose_spec (isQ_jQ x))
  right_inv x := Subtype.ext x.2.choose_spec

@[simp] theorem blkE_apply (n m : ℕ) (x : SQ (Fin m)) : (blkE n m x).1 = jQ x := rfl

/-! ## `cyc3` preserves the `q`-word -/

theorem cyc3_eq_cycPermP (m : ℕ) : cyc3 (Fin m) = Work.KT.cycPermP m := by
  apply Equiv.ext; intro x; rfl

theorem jQ_cyc3 {n m : ℕ} (x : SQ (Fin m)) :
    cyc3 (Fin n ⊕ Fin m) (jQ (n := n) x) = jQ (n := n) (cyc3 (Fin m) x) := rfl

theorem jQ_cyc3_symm {n m : ℕ} (x : SQ (Fin m)) :
    (cyc3 (Fin n ⊕ Fin m)).symm (jQ (n := n) x) = jQ (n := n) ((cyc3 (Fin m)).symm x) := rfl

theorem jQ_cyc3_mul {n m : ℕ} (x : SQ (Fin m)) :
    (cyc3 (Fin n ⊕ Fin m) * cyc3 (Fin n ⊕ Fin m)) (jQ (n := n) x) =
      jQ (n := n) ((cyc3 (Fin m) * cyc3 (Fin m)) x) := rfl

theorem jQ_cyc3_symm_mul {n m : ℕ} (x : SQ (Fin m)) :
    ((cyc3 (Fin n ⊕ Fin m) * cyc3 (Fin n ⊕ Fin m))) (jQ (n := n) x) =
      jQ (n := n) ((cyc3 (Fin m) * cyc3 (Fin m)) x) := jQ_cyc3_mul x

theorem isQ_cyc3 {n m : ℕ} (x : SQ (Fin n ⊕ Fin m)) :
    isQ (cyc3 (Fin n ⊕ Fin m) x) ↔ isQ x := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(cyc3 (Fin m)).symm y, ?_⟩
    have h := congrArg (cyc3 (Fin n ⊕ Fin m)).symm hy
    rwa [jQ_cyc3_symm] at h
  · rintro ⟨y, rfl⟩
    exact ⟨cyc3 (Fin m) y, jQ_cyc3 y⟩

theorem isQ_cyc3_symm {n m : ℕ} (x : SQ (Fin n ⊕ Fin m)) :
    isQ ((cyc3 (Fin n ⊕ Fin m)).symm x) ↔ isQ x := by
  rw [← isQ_cyc3 ((cyc3 (Fin n ⊕ Fin m)).symm x), Equiv.apply_symm_apply]

theorem isQ_cyc3_mul {n m : ℕ} (x : SQ (Fin n ⊕ Fin m)) :
    isQ ((cyc3 (Fin n ⊕ Fin m) * cyc3 (Fin n ⊕ Fin m)) x) ↔ isQ x := by
  rw [Equiv.Perm.mul_apply, isQ_cyc3, isQ_cyc3]

/-! ## Entries of `kron3g (sumBlkQ p q)` -/

theorem sumBlkQ_apply_inl {A : Type} [Ring A] (p q : Mat A) (a : Fin p.1)
    (b : Fin p.1 ⊕ Fin q.1) : sumBlkQ p q (Sum.inl a) b = 0 := by
  rcases b with b | b <;> simp [sumBlkQ, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂]

theorem sumBlkQ_apply_inl_col {A : Type} [Ring A] (p q : Mat A) (b : Fin p.1 ⊕ Fin q.1)
    (a : Fin p.1) : sumBlkQ p q b (Sum.inl a) = 0 := by
  rcases b with b | b <;> simp [sumBlkQ, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁]

theorem sumBlkQ_apply_inr_inl {A : Type} [Ring A] (p q : Mat A) (a : Fin q.1) (b : Fin p.1) :
    sumBlkQ p q (Sum.inr a) (Sum.inl b) = 0 := by
  simp [sumBlkQ, Matrix.fromBlocks_apply₂₁]

theorem sumBlkQ_apply_inr_inr {A : Type} [Ring A] (p q : Mat A) (a b : Fin q.1) :
    sumBlkQ p q (Sum.inr a) (Sum.inr b) = q.2 a b := by
  simp [sumBlkQ, Matrix.fromBlocks_apply₂₂]

theorem kron3g_sumBlkQ_jQ {A : Type} [Ring A] (p q : Mat A) (x y : SQ (Fin q.1)) :
    kron3g (sumBlkQ p q) (jQ (n := p.1) x) (jQ (n := p.1) y) = kron3g q.2 x y := by
  simp only [kron3g_apply, jQ, sumBlkQ_apply_inr_inr]

theorem kron3g_sumBlkQ_eq_zero_of_not_isQ_left {A : Type} [Ring A] (p q : Mat A)
    (x y : SQ (Fin p.1 ⊕ Fin q.1)) (hx : ¬ isQ x) : kron3g (sumBlkQ p q) x y = 0 := by
  rw [kron3g_apply]
  rcases h₁ : x.1.1 with a | a
  · simp [sumBlkQ_apply_inl]
  rcases h₂ : x.1.2 with b | b
  · simp [sumBlkQ_apply_inl]
  rcases h₃ : x.2 with c | c
  · simp [sumBlkQ_apply_inl]
  · exact absurd (by rw [isQ_iff]; exact ⟨a, b, c, Prod.ext (Prod.ext h₁ h₂) h₃⟩) hx

theorem kron3g_sumBlkQ_eq_zero_of_not_isQ_right {A : Type} [Ring A] (p q : Mat A)
    (x y : SQ (Fin p.1 ⊕ Fin q.1)) (hy : ¬ isQ y) : kron3g (sumBlkQ p q) x y = 0 := by
  rw [kron3g_apply]
  rcases h₁ : y.1.1 with a | a
  · simp [sumBlkQ_apply_inl_col]
  rcases h₂ : y.1.2 with b | b
  · simp [sumBlkQ_apply_inl_col]
  rcases h₃ : y.2 with c | c
  · simp [sumBlkQ_apply_inl_col]
  · exact absurd (by rw [isQ_iff]; exact ⟨a, b, c, Prod.ext (Prod.ext h₁ h₂) h₃⟩) hy

/-! ## Entries of the cyclic spectral projector -/

/-- The entry formula for the cyclic spectral projector: this reduces `Cp` to the three
conditions under which its entries can be nonzero. -/
theorem Cp_apply {A : Type} [Ring A] [Algebra ℂ A] {S : Type} [Fintype S] [DecidableEq S]
    (lam : ℂ) (x y : SQ S) :
    Cp (A := A) S lam x y = algebraMap ℂ A (1 / 3) *
      ((if x = y then 1 else 0) + algebraMap ℂ A lam⁻¹ * (if cyc3 S x = y then 1 else 0)
        + algebraMap ℂ A ((lam⁻¹) ^ 2) *
          (if (cyc3 S * cyc3 S) x = y then 1 else 0)) := by
  simp only [Cp, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    ← Matrix.permMatrix_mul, Work.KT.permMatrix_apply']

/-- On the `q`-word, `Cp` of `p ⊕ q` restricts to `Cp` of `q`. -/
theorem Cp_jQ {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ} (lam : ℂ) (x y : SQ (Fin m)) :
    Cp (A := A) (Fin n ⊕ Fin m) lam (jQ (n := n) x) (jQ (n := n) y) =
      Cp (A := A) (Fin m) lam x y := by
  rw [Cp_apply, Cp_apply]
  have h1 : (jQ (n := n) x = jQ (n := n) y) ↔ (x = y) := jQ_inj_eq x y
  have h2 : (cyc3 (Fin n ⊕ Fin m) (jQ (n := n) x) = jQ (n := n) y) ↔ (cyc3 (Fin m) x = y) := by
    rw [jQ_cyc3]; exact jQ_inj_eq _ _
  have h3 : ((cyc3 (Fin n ⊕ Fin m) * cyc3 (Fin n ⊕ Fin m)) (jQ (n := n) x) = jQ (n := n) y) ↔
      ((cyc3 (Fin m) * cyc3 (Fin m)) x = y) := by
    rw [jQ_cyc3_mul]; exact jQ_inj_eq _ _
  simp only [h1, h2, h3]

/-- `Cp` has no entries from the `q`-word to its complement. -/
theorem Cp_eq_zero_of_isQ_not_isQ {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ} (lam : ℂ)
    (x y : SQ (Fin n ⊕ Fin m)) (hx : isQ x) (hy : ¬ isQ y) :
    Cp (A := A) (Fin n ⊕ Fin m) lam x y = 0 := by
  have h1 : x ≠ y := fun h => hy (h ▸ hx)
  have h2 : cyc3 (Fin n ⊕ Fin m) x ≠ y := fun h => hy (by
    have hh : isQ (cyc3 (Fin n ⊕ Fin m) x) := (isQ_cyc3 x).mpr hx
    rwa [h] at hh)
  have h3 : (cyc3 (Fin n ⊕ Fin m) * cyc3 (Fin n ⊕ Fin m)) x ≠ y := fun h => hy (by
    have hh : isQ ((cyc3 (Fin n ⊕ Fin m) * cyc3 (Fin n ⊕ Fin m)) x) := (isQ_cyc3_mul x).mpr hx
    rwa [h] at hh)
  rw [Cp_apply, if_neg h1, if_neg h2, if_neg h3]
  simp

end

end Work.KT.Psi
