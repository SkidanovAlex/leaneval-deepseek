import Mathlib
import Submission.Work.KT.Psi.psi3sum_Setup
import Submission.Work.KT.Psi.PWordSetup
import Submission.Work.KT.Psi.clsM_submatrix

/-!
# `Work.KT.Psi.clsM_sumBlkP_cubePart`

The `K₀`-class, over the triple tensor-power index `SQ (Fin p.1 ⊕ Fin q.1)`, of the triple tensor
cube of the `p`-block `sumBlkP p q` cut down by the spectral projector `Cp` of the cyclic
permutation of the three tensor factors, is the class of `cubePart λ p`.

Everything is *entrywise*, so no commutativity of the coefficient ring is used.  The matrix
`kron3g (sumBlkP p q)` is supported on the `p`-word `pWord p.1 q.1` of the triple index type and
agrees there with `kron3g p.2` (transported along `emb p.1 q.1`), while `Cp (Fin p.1 ⊕ Fin q.1) λ`
has no entries from the `p`-word to its complement (and restricts to `Cp (Fin p.1) λ` on the word).
Hence the product `M` is the block matrix with `cubePartP λ p` in the `p`-word and `0` elsewhere.

Finally, `clsM` of a matrix supported on a block is the class of its block
(`pw_clsM_submatrix_of_support`): for an idempotent matrix this is a Murray–von Neumann
equivalence (`Work.KT.Psi.clsM_submatrix`), and a matrix supported on a block is idempotent if and
only if its block is, so the non-idempotent case has both classes equal to `0`.
-/

namespace Work.KT.Psi

open Matrix

noncomputable section

variable {A : Type} [Ring A] [Algebra ℂ A]

/-! ## The `p`-word, concretely -/

theorem pw_pWord_iff {m n : ℕ} (x : SQ (Fin m ⊕ Fin n)) :
    pWord m n x ↔ ∃ a b c : Fin m, x = ((Sum.inl a, Sum.inl b), Sum.inl c) := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.1.1, y.1.2, y.2, rfl⟩
  · rintro ⟨a, b, c, rfl⟩
    exact ⟨((a, b), c), rfl⟩

/-! ## Entries of `sumBlkP p q` -/

theorem pw_sumBlkP_apply_inl_inl (p q : Mat A) (a b : Fin p.1) :
    sumBlkP p q (Sum.inl a) (Sum.inl b) = p.2 a b := by
  simp [sumBlkP]

theorem pw_sumBlkP_apply_inr_col (p q : Mat A) (a : Fin p.1 ⊕ Fin q.1) (b : Fin q.1) :
    sumBlkP p q a (Sum.inr b) = 0 := by
  rcases a with a | a <;> simp [sumBlkP]

theorem pw_sumBlkP_apply_inr_row (p q : Mat A) (a : Fin q.1) (b : Fin p.1 ⊕ Fin q.1) :
    sumBlkP p q (Sum.inr a) b = 0 := by
  rcases b with b | b <;> simp [sumBlkP]

/-! ## Entries of `kron3g (sumBlkP p q)` -/

theorem pw_kron3g_emb_app (p q : Mat A) (x y : SQ (Fin p.1)) :
    kron3g (sumBlkP p q) (emb p.1 q.1 x) (emb p.1 q.1 y) = kron3g p.2 x y := by
  simp only [kron3g_apply, emb_apply, pw_sumBlkP_apply_inl_inl]

theorem pw_kron3g_eq_zero_of_not_pWord_left (p q : Mat A)
    (x y : SQ (Fin p.1 ⊕ Fin q.1)) (hx : ¬ pWord p.1 q.1 x) :
    kron3g (sumBlkP p q) x y = 0 := by
  rw [kron3g_apply]
  rcases h₁ : x.1.1 with a | a
  · rcases h₂ : x.1.2 with b | b
    · rcases h₃ : x.2 with c | c
      · exact absurd ((pw_pWord_iff x).mpr ⟨a, b, c, Prod.ext (Prod.ext h₁ h₂) h₃⟩) hx
      · simp [pw_sumBlkP_apply_inr_row]
    · simp [pw_sumBlkP_apply_inr_row]
  · simp [pw_sumBlkP_apply_inr_row]

theorem pw_kron3g_eq_zero_of_not_pWord_right (p q : Mat A)
    (x y : SQ (Fin p.1 ⊕ Fin q.1)) (hy : ¬ pWord p.1 q.1 y) :
    kron3g (sumBlkP p q) x y = 0 := by
  rw [kron3g_apply]
  rcases k₁ : y.1.1 with d | d
  · rcases k₂ : y.1.2 with e | e
    · rcases k₃ : y.2 with f | f
      · exact absurd ((pw_pWord_iff y).mpr ⟨d, e, f, Prod.ext (Prod.ext k₁ k₂) k₃⟩) hy
      · simp [pw_sumBlkP_apply_inr_col]
    · simp [pw_sumBlkP_apply_inr_col]
  · simp [pw_sumBlkP_apply_inr_col]

theorem pw_kron3g_eq_zero (p q : Mat A) (x y : SQ (Fin p.1 ⊕ Fin q.1))
    (h : ¬ (pWord p.1 q.1 x ∧ pWord p.1 q.1 y)) :
    kron3g (sumBlkP p q) x y = 0 := by
  by_cases hx : pWord p.1 q.1 x
  · exact pw_kron3g_eq_zero_of_not_pWord_right p q x y (fun hy => h ⟨hx, hy⟩)
  · exact pw_kron3g_eq_zero_of_not_pWord_left p q x y hx

/-! ## Entries of the cyclic spectral projector `Cp` -/

/-- The entry formula for `Cp`: its `(x,y)`-entry can be non-zero only when `y` is `x`, `c x` or
`c (c x)` for the cyclic permutation `c`. -/
theorem pw_Cp_entry {S : Type} [Fintype S] [DecidableEq S] (lam : ℂ) (x y : SQ S) :
    Cp (A := A) S lam x y = algebraMap ℂ A (1 / 3) *
      ((if x = y then 1 else 0) + algebraMap ℂ A lam⁻¹ * (if cyc3 S x = y then 1 else 0)
        + algebraMap ℂ A ((lam⁻¹) ^ 2) *
          (if (cyc3 S * cyc3 S) x = y then 1 else 0)) := by
  simp only [Cp, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    ← Matrix.permMatrix_mul, Work.KT.permMatrix_apply']

theorem pw_Cp_emb (m n : ℕ) (lam : ℂ) (x y : SQ (Fin m)) :
    Cp (A := A) (Fin m ⊕ Fin n) lam (emb m n x) (emb m n y) = Cp (A := A) (Fin m) lam x y := by
  simp only [pw_Cp_entry]
  have h1 : (emb m n x = emb m n y) ↔ (x = y) := emb_inj_eq m n x y
  have h2 : (cyc3 (Fin m ⊕ Fin n) (emb m n x) = emb m n y) ↔ (cyc3 (Fin m) x = y) := by
    rw [cyc3_emb]
    exact emb_inj_eq m n _ _
  have h3 : ((cyc3 (Fin m ⊕ Fin n) * cyc3 (Fin m ⊕ Fin n)) (emb m n x) = emb m n y) ↔
      ((cyc3 (Fin m) * cyc3 (Fin m)) x = y) := by
    rw [cyc3_cyc3_emb]
    exact emb_inj_eq m n _ _
  simp only [h1, h2, h3]

theorem pw_Cp_eq_zero_of_pWord_not (m n : ℕ) (lam : ℂ) (x y : SQ (Fin m ⊕ Fin n))
    (hx : pWord m n x) (hy : ¬ pWord m n y) :
    Cp (A := A) (Fin m ⊕ Fin n) lam x y = 0 := by
  have h1 : x ≠ y := fun h => hy (h ▸ hx)
  have h2 : cyc3 (Fin m ⊕ Fin n) x ≠ y := fun h => hy (by
    obtain ⟨z, rfl⟩ := hx
    exact ⟨cyc3 (Fin m) z, (cyc3_emb m n z).symm.trans h⟩)
  have h3 : (cyc3 (Fin m ⊕ Fin n) * cyc3 (Fin m ⊕ Fin n)) x ≠ y := fun h => hy (by
    obtain ⟨z, rfl⟩ := hx
    exact ⟨(cyc3 (Fin m) * cyc3 (Fin m)) z, (cyc3_cyc3_emb m n z).symm.trans h⟩)
  rw [pw_Cp_entry, if_neg h1, if_neg h2, if_neg h3]
  simp

/-! ## Collapsing a sum to the range of an injection -/

theorem pw_sum_eq_sum_of_range {N : Type} [AddCommMonoid N] {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (g : κ → ι) (hinj : Function.Injective g) (f : ι → N)
    (h : ∀ z : ι, (∀ c : κ, g c ≠ z) → f z = 0) :
    (∑ z, f z) = ∑ c : κ, f (g c) := by
  have h1 : (∑ z ∈ (Finset.univ.image g), f z) = ∑ z, f z := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro z _ hz
    exact h z (fun c hc => hz (Finset.mem_image.mpr ⟨c, Finset.mem_univ c, hc⟩))
  rw [← h1, Finset.sum_image (s := Finset.univ) (g := g) (f := f)
    (fun a _ b _ hab => hinj hab)]

/-! ## Products of matrices supported on a block -/

theorem pw_mul_apply_eq_zero_of_support {ι : Type} [Fintype ι] (qr : ι → Prop)
    (X Y : Matrix ι ι A)
    (hX : ∀ a b : ι, ¬ (qr a ∧ qr b) → X a b = 0)
    (hY : ∀ a b : ι, ¬ (qr a ∧ qr b) → Y a b = 0) :
    ∀ a b : ι, ¬ (qr a ∧ qr b) → (X * Y) a b = 0 := by
  intro a b h
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro w _
  by_cases hw : qr w
  · by_cases hb : qr b
    · rw [hX a w (fun hh => h ⟨hh.1, hb⟩), zero_mul]
    · rw [hY w b (fun hh => hb hh.2), mul_zero]
  · rw [hX a w (fun hh => hw hh.2), zero_mul]

/-- The compression of a product of matrices supported on a block. -/
theorem pw_submatrix_mul_self {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {g : κ → ι} (hinj : Function.Injective g) (M : Matrix ι ι A)
    (hsupp : ∀ i j : ι, ¬ (∃ a b : κ, g a = i ∧ g b = j) → M i j = 0) :
    (M * M).submatrix g g = M.submatrix g g * M.submatrix g g := by
  ext p q
  rw [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.submatrix_apply]
  rw [pw_sum_eq_sum_of_range g hinj (fun w => M (g p) w * M w (g q))
    (fun z hz => by rw [hsupp (g p) z (fun ⟨a, b, ha, hb⟩ => hz b hb), zero_mul])]

/-! ## The class of a matrix supported on a block -/

/-- The class of a non-idempotent square matrix over a finite index type is zero. -/
theorem pw_clsM_eq_zero_of_not_idem {R : Type} [Ring R] {ι : Type} [Fintype ι]
    {M : Matrix ι ι R} (hM : ¬ M * M = M) : clsM ι M = 0 := by
  rw [clsM_eq_cls]
  refine cls_zero_of_not_idem (fun hc => hM ?_)
  change Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) M *
      Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) M =
    Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) M at hc
  have hc' : (Matrix.reindexRingEquiv R (Fintype.equivFin ι)) (M * M) =
      (Matrix.reindexRingEquiv R (Fintype.equivFin ι)) M := by
    rw [map_mul]
    exact hc
  exact (Matrix.reindexRingEquiv R (Fintype.equivFin ι)).injective hc'

section Block

variable {ι : Type} [Fintype ι] {pr : ι → Prop} [DecidablePred pr]

/-- If `M` vanishes off the block determined by `pr`, then `clsM` of `M` is the class of its
compression to the block.  No idempotency hypothesis is needed: `M` is idempotent exactly when its
compression is. -/
theorem pw_clsM_submatrix_of_support (M : Matrix ι ι A)
    (hdiag : ∀ i j : ι, ¬ (pr i ∧ pr j) → M i j = 0) :
    clsM ι M = clsM {i // pr i} (M.submatrix (fun i : {i // pr i} => (i : ι))
      (fun i : {i // pr i} => (i : ι))) := by
  classical
  have hsupp : ∀ i j : ι, ¬ (∃ a b : {i // pr i}, (a : ι) = i ∧ (b : ι) = j) → M i j = 0 :=
    fun i j h => hdiag i j (fun hij => h ⟨⟨i, hij.1⟩, ⟨j, hij.2⟩, rfl, rfl⟩)
  have hsub : (M.submatrix (fun i : {i // pr i} => (i : ι))
        (fun i : {i // pr i} => (i : ι))) *
        (M.submatrix (fun i : {i // pr i} => (i : ι)) (fun i : {i // pr i} => (i : ι))) =
        ((M * M).submatrix (fun i : {i // pr i} => (i : ι))
          (fun i : {i // pr i} => (i : ι))) :=
    (pw_submatrix_mul_self (g := fun i : {i // pr i} => (i : ι))
      (fun a b h => Subtype.ext h) M hsupp).symm
  by_cases hM : M * M = M
  · exact clsM_submatrix M hM hdiag
  · have hC : ¬ ((M.submatrix (fun i : {i // pr i} => (i : ι))
          (fun i : {i // pr i} => (i : ι))) *
          (M.submatrix (fun i : {i // pr i} => (i : ι)) (fun i : {i // pr i} => (i : ι))) =
          M.submatrix (fun i : {i // pr i} => (i : ι)) (fun i : {i // pr i} => (i : ι))) := by
      intro hc
      refine hM (Matrix.ext ?_)
      intro i j
      by_cases hij : pr i ∧ pr j
      · have h1 : ((M * M).submatrix (fun i : {i // pr i} => (i : ι))
            (fun i : {i // pr i} => (i : ι))) ⟨i, hij.1⟩ ⟨j, hij.2⟩ = (M * M) i j := rfl
        have h2 : (M.submatrix (fun i : {i // pr i} => (i : ι))
            (fun i : {i // pr i} => (i : ι))) ⟨i, hij.1⟩ ⟨j, hij.2⟩ = M i j := rfl
        rw [← h1, ← h2, hsub.symm.trans hc]
      · rw [hdiag i j hij]
        exact pw_mul_apply_eq_zero_of_support pr M M hdiag hdiag i j hij
    rw [pw_clsM_eq_zero_of_not_idem hM, pw_clsM_eq_zero_of_not_idem hC]

end Block

theorem pw_clsM_reindex {R : Type} [Ring R] {ι κ : Type} [Fintype ι] [Fintype κ]
    (g : ι ≃ κ) (M : Matrix ι ι R) :
    clsM κ (Matrix.reindex g g M) = clsM ι M := clsI_reindex g M

/-! ## The entries of the product -/

theorem pw_kron3g_mul_Cp_emb (p q : Mat A) (lam : ℂ) (x y : SQ (Fin p.1)) :
    (kron3g (sumBlkP p q) * Cp (A := A) (Fin p.1 ⊕ Fin q.1) lam)
        (emb p.1 q.1 x) (emb p.1 q.1 y) = cubePartP lam p x y := by
  have hsum := pw_sum_eq_sum_of_range (emb p.1 q.1) (emb_injective p.1 q.1)
    (fun w => kron3g (sumBlkP p q) (emb p.1 q.1 x) w *
      Cp (A := A) (Fin p.1 ⊕ Fin q.1) lam w (emb p.1 q.1 y))
    (fun w hw => by
      rw [pw_kron3g_eq_zero p q (emb p.1 q.1 x) w (fun h => by
        obtain ⟨c, hc⟩ := h.2
        exact hw c hc), zero_mul])
  rw [Matrix.mul_apply, hsum]
  trans ∑ z : SQ (Fin p.1), kron3g p.2 x z * Cp (A := A) (Fin p.1) lam z y
  · exact Finset.sum_congr rfl (fun z _ => by rw [pw_kron3g_emb_app, pw_Cp_emb])
  · rw [← Matrix.mul_apply]
    rfl

theorem pw_kron3g_mul_Cp_eq_zero (p q : Mat A) (lam : ℂ)
    (x y : SQ (Fin p.1 ⊕ Fin q.1)) (h : ¬ (pWord p.1 q.1 x ∧ pWord p.1 q.1 y)) :
    (kron3g (sumBlkP p q) * Cp (A := A) (Fin p.1 ⊕ Fin q.1) lam) x y = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro w _
  by_cases hw : pWord p.1 q.1 w
  · by_cases hx : pWord p.1 q.1 x
    · rw [pw_Cp_eq_zero_of_pWord_not p.1 q.1 lam w y hw (fun hy => h ⟨hx, hy⟩), mul_zero]
    · rw [pw_kron3g_eq_zero p q x w (fun hh => hx hh.1), zero_mul]
  · rw [pw_kron3g_eq_zero p q x w (fun hh => hw hh.2), zero_mul]

/-! ## The class computation -/

theorem clsM_sumBlkP_cubePart {A : Type} [Ring A] [Algebra ℂ A] (p q : Work.KT.Mat A) (lam : ℂ) :
    Work.KT.Psi.clsM (Work.KT.Psi.SQ (Fin p.1 ⊕ Fin q.1))
      (Work.KT.Psi.kron3g (Work.KT.Psi.sumBlkP p q) * Work.KT.Psi.Cp (Fin p.1 ⊕ Fin q.1) lam)
      = Work.KT.cls (Work.KT.cubePart lam p) := by
  classical
  set M := kron3g (sumBlkP p q) * Cp (A := A) (Fin p.1 ⊕ Fin q.1) lam with hM
  have hstep : clsM (SQ (Fin p.1 ⊕ Fin q.1)) M
      = clsM {i : SQ (Fin p.1 ⊕ Fin q.1) // pWord p.1 q.1 i}
          (M.submatrix (fun i : {i : SQ (Fin p.1 ⊕ Fin q.1) // pWord p.1 q.1 i} =>
              (i : SQ (Fin p.1 ⊕ Fin q.1)))
            (fun i : {i : SQ (Fin p.1 ⊕ Fin q.1) // pWord p.1 q.1 i} =>
              (i : SQ (Fin p.1 ⊕ Fin q.1)))) :=
    pw_clsM_submatrix_of_support (pr := pWord p.1 q.1) M
      (fun i j h => pw_kron3g_mul_Cp_eq_zero p q lam i j h)
  have hminor : Matrix.reindex (embEquiv p.1 q.1).symm (embEquiv p.1 q.1).symm
      (M.submatrix (fun i : {i : SQ (Fin p.1 ⊕ Fin q.1) // pWord p.1 q.1 i} =>
          (i : SQ (Fin p.1 ⊕ Fin q.1)))
        (fun i : {i : SQ (Fin p.1 ⊕ Fin q.1) // pWord p.1 q.1 i} =>
          (i : SQ (Fin p.1 ⊕ Fin q.1))))
      = cubePartP lam p := by
    ext x y
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.submatrix_apply]
    simp only [Equiv.symm_symm]
    show M (emb p.1 q.1 x) (emb p.1 q.1 y) = cubePartP lam p x y
    exact pw_kron3g_mul_Cp_emb p q lam x y
  have hstep2 : clsM {i : SQ (Fin p.1 ⊕ Fin q.1) // pWord p.1 q.1 i}
      (M.submatrix (fun i : {i : SQ (Fin p.1 ⊕ Fin q.1) // pWord p.1 q.1 i} =>
          (i : SQ (Fin p.1 ⊕ Fin q.1)))
        (fun i : {i : SQ (Fin p.1 ⊕ Fin q.1) // pWord p.1 q.1 i} =>
          (i : SQ (Fin p.1 ⊕ Fin q.1))))
      = clsM (SQ (Fin p.1)) (cubePartP lam p) := by
    rw [← pw_clsM_reindex (embEquiv p.1 q.1).symm
      (M.submatrix (fun i : {i : SQ (Fin p.1 ⊕ Fin q.1) // pWord p.1 q.1 i} =>
          (i : SQ (Fin p.1 ⊕ Fin q.1)))
        (fun i : {i : SQ (Fin p.1 ⊕ Fin q.1) // pWord p.1 q.1 i} =>
          (i : SQ (Fin p.1 ⊕ Fin q.1)))), hminor]
  rw [hstep, hstep2, clsM_I3_cubePartP lam p]

end

end Work.KT.Psi
