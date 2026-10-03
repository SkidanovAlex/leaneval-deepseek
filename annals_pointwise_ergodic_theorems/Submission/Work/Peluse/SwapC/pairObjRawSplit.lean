import Mathlib
import Submission.Work.Peluse.SwapC.concatGlue

/-!
# `Work.Peluse.SwapC.pairObjRawSplit`

The raw slot `qH i[M]` of the concatenation step has a *degenerate* index dependence: the increment
tuple `incr s M qH q₁ q₂ H H'` at coordinate `0` only sees the *first* component of `H 0` and of
`H' 0` (`pdir qH 0 m = qH·(m₁+1)` does not involve `m₂`), and at the coordinates `≥ 1` it only sees
the *tail* of `H` and of `H'`.

Consequently the summed object `pairObj` — the doubled `Rest`-product over two independent
indices — is invariant under any change of the *second* component of the `0`-th entry of each of its
four tuples.  Summing over that degenerate coordinate therefore produces exactly a factor `M⁴`, and
the sum over the four tuples `H₀, H₀', H₁, H₁' : Fin (s+1) → Fin M × Fin M` collapses onto the
*reduced* index set on which the `0`-th second component is the distinguished value
`⟨0, hM⟩ : Fin M` (`pairObjRawSplit`).

The proof has three layers.

* the pointwise degeneracy of the increment (`incr_cons_fst`, `incr_cons_snd`) and hence of
  `pairObj` in each of its four variables (`pairObj_cons_1` … `pairObj_cons_4`);
* the splitting lemma `sumFinSuccSplit`: for a function invariant under the second component of the
  `0`-th entry, the sum over `Fin (s+1) → Fin M × Fin M` is `M` times the sum over the reduced
  index set `Fin M × (Fin s → Fin M × Fin M)`;
* the reordering `sumFourProdSwap`, which separates the first components from the tails of two
  independent pairs of indices.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.SwapC

lemma incr_cons_fst (s M : ℕ) (hM : 0 < M) (qH : ℤ) (q₁ q₂ : Fin s → ℤ) (a b : Fin M)
    (k : Fin s → Fin M × Fin M) (H : Fin (s+1) → Fin M × Fin M) :
    incr s M qH q₁ q₂ (Fin.cons (a,b) k) H = incr s M qH q₁ q₂ (Fin.cons (a,⟨0,hM⟩) k) H := by
  funext j
  refine Fin.cases ?_ ?_ j
  · simp only [incr, Fin.cons_zero, pdir_zero_right]
  · intro i
    simp only [incr, Fin.cons_succ]

lemma incr_cons_snd (s M : ℕ) (hM : 0 < M) (qH : ℤ) (q₁ q₂ : Fin s → ℤ) (a b : Fin M)
    (k : Fin s → Fin M × Fin M) (H : Fin (s+1) → Fin M × Fin M) :
    incr s M qH q₁ q₂ H (Fin.cons (a,b) k) = incr s M qH q₁ q₂ H (Fin.cons (a,⟨0,hM⟩) k) := by
  funext j
  refine Fin.cases ?_ ?_ j
  · simp only [incr, Fin.cons_zero, pdir_zero_right]
  · intro i
    simp only [incr, Fin.cons_succ]

lemma pairObj_cons_1 {I : Type} (s M : ℕ) (hM : 0 < M) (qH : I → ℤ) (q₁ q₂ : I → Fin s → ℤ)
    (f : ℤ → ℂ) (i₀ i₁ : I) (a₀ : Fin M) (b₀ : Fin M) (k₀ : Fin s → Fin M × Fin M)
    (H₀' H₁ H₁' : Fin (s+1) → Fin M × Fin M) :
    pairObj s M qH q₁ q₂ f i₀ i₁ (Fin.cons (a₀,b₀) k₀) H₀' H₁ H₁'
      = pairObj s M qH q₁ q₂ f i₀ i₁ (Fin.cons (a₀,⟨0,hM⟩) k₀) H₀' H₁ H₁' := by
  simp only [pairObj]
  rw [incr_cons_fst]

lemma pairObj_cons_2 {I : Type} (s M : ℕ) (hM : 0 < M) (qH : I → ℤ) (q₁ q₂ : I → Fin s → ℤ)
    (f : ℤ → ℂ) (i₀ i₁ : I) (a₀' : Fin M) (b₀' : Fin M) (k₀' : Fin s → Fin M × Fin M)
    (H₀ H₁ H₁' : Fin (s+1) → Fin M × Fin M) :
    pairObj s M qH q₁ q₂ f i₀ i₁ H₀ (Fin.cons (a₀',b₀') k₀') H₁ H₁'
      = pairObj s M qH q₁ q₂ f i₀ i₁ H₀ (Fin.cons (a₀',⟨0,hM⟩) k₀') H₁ H₁' := by
  simp only [pairObj]
  rw [incr_cons_snd]

lemma pairObj_cons_3 {I : Type} (s M : ℕ) (hM : 0 < M) (qH : I → ℤ) (q₁ q₂ : I → Fin s → ℤ)
    (f : ℤ → ℂ) (i₀ i₁ : I) (a₁ : Fin M) (b₁ : Fin M) (k₁ : Fin s → Fin M × Fin M)
    (H₀ H₀' H₁' : Fin (s+1) → Fin M × Fin M) :
    pairObj s M qH q₁ q₂ f i₀ i₁ H₀ H₀' (Fin.cons (a₁,b₁) k₁) H₁'
      = pairObj s M qH q₁ q₂ f i₀ i₁ H₀ H₀' (Fin.cons (a₁,⟨0,hM⟩) k₁) H₁' := by
  simp only [pairObj]
  rw [incr_cons_fst]

lemma pairObj_cons_4 {I : Type} (s M : ℕ) (hM : 0 < M) (qH : I → ℤ) (q₁ q₂ : I → Fin s → ℤ)
    (f : ℤ → ℂ) (i₀ i₁ : I) (a₁' : Fin M) (b₁' : Fin M) (k₁' : Fin s → Fin M × Fin M)
    (H₀ H₀' H₁ : Fin (s+1) → Fin M × Fin M) :
    pairObj s M qH q₁ q₂ f i₀ i₁ H₀ H₀' H₁ (Fin.cons (a₁',b₁') k₁')
      = pairObj s M qH q₁ q₂ f i₀ i₁ H₀ H₀' H₁ (Fin.cons (a₁',⟨0,hM⟩) k₁') := by
  simp only [pairObj]
  rw [incr_cons_snd]

def finSuccConsEquiv (s M : ℕ) :
    (Fin M × Fin M) × (Fin s → Fin M × Fin M) ≃ (Fin (s+1) → Fin M × Fin M) where
  toFun p := Fin.cons p.1 p.2
  invFun H := (H 0, Fin.tail H)
  left_inv p := by obtain ⟨x, k⟩ := p; rfl
  right_inv H := Fin.cons_self_tail H

lemma sumProdFstSnd {α β : Type} [Fintype α] [Fintype β] {γ : Type} [AddCommMonoid γ]
    (F : α × β → γ) : (∑ x : α × β, F x) = ∑ a, ∑ b, F (a,b) :=
  Fintype.sum_prod_type F

lemma sumProdFstSnd' {α β : Type} [Fintype α] [Fintype β] {γ : Type} [AddCommMonoid γ]
    (F : α × β → γ) : (∑ a, ∑ b, F (a,b)) = ∑ x : α × β, F x :=
  (Fintype.sum_prod_type F).symm

lemma sumFinSuccSplit (s M : ℕ) (hM : 0 < M)
    (G : (Fin (s+1) → Fin M × Fin M) → ℂ)
    (hG : ∀ (a b : Fin M) (k : Fin s → Fin M × Fin M),
        G (Fin.cons (a,b) k) = G (Fin.cons (a,⟨0,hM⟩) k)) :
    (∑ H : Fin (s+1) → Fin M × Fin M, G H)
      = (M : ℂ) * ∑ p : Fin M × (Fin s → Fin M × Fin M),
          G (Fin.cons (p.1,⟨0,hM⟩) p.2) := by
  have key : ∀ a : Fin M, (∑ b : Fin M, ∑ k : Fin s → Fin M × Fin M, G (Fin.cons (a,b) k))
      = (M : ℂ) * ∑ k : Fin s → Fin M × Fin M, G (Fin.cons (a,⟨0,hM⟩) k) := by
    intro a
    calc ∑ b : Fin M, ∑ k : Fin s → Fin M × Fin M, G (Fin.cons (a,b) k)
        = ∑ b : Fin M, ∑ k : Fin s → Fin M × Fin M, G (Fin.cons (a,⟨0,hM⟩) k) :=
          Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun k _ => hG a b k))
      _ = (M : ℂ) * ∑ k : Fin s → Fin M × Fin M, G (Fin.cons (a,⟨0,hM⟩) k) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h1 : (∑ H : Fin (s+1) → Fin M × Fin M, G H)
      = ∑ p : (Fin M × Fin M) × (Fin s → Fin M × Fin M), G (Fin.cons p.1 p.2) :=
    Fintype.sum_equiv (finSuccConsEquiv s M).symm G
      (fun p : (Fin M × Fin M) × (Fin s → Fin M × Fin M) => G (Fin.cons p.1 p.2))
      (fun H => by congr 1; exact (Fin.cons_self_tail H).symm)
  rw [h1]
  rw [sumProdFstSnd (F := fun p : (Fin M × Fin M) × (Fin s → Fin M × Fin M) =>
      G (Fin.cons p.1 p.2))]
  rw [sumProdFstSnd (F := fun x : Fin M × Fin M =>
      ∑ k : Fin s → Fin M × Fin M, G (Fin.cons x k))]
  rw [Finset.sum_congr rfl (fun a _ => key a), ← Finset.mul_sum]
  congr 1
  exact (sumProdFstSnd (F := fun p : Fin M × (Fin s → Fin M × Fin M) =>
      G (Fin.cons (p.1,⟨0,hM⟩) p.2))).symm

def pairSwapMiddle (A K : Type) : (A × K) × (A × K) ≃ (A × A) × (K × K) where
  toFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  invFun q := ((q.1.1, q.2.1), (q.1.2, q.2.2))
  left_inv p := by obtain ⟨⟨a,b⟩,⟨c,d⟩⟩ := p; rfl
  right_inv q := by obtain ⟨⟨a,b⟩,⟨c,d⟩⟩ := q; rfl

@[simp] lemma pairSwapMiddle_symm_apply {A K : Type} (a c : A) (b d : K) :
    (pairSwapMiddle A K).symm ((a,c),(b,d)) = ((a,b),(c,d)) := rfl

lemma sumFstSndEq {α β : Type} [Fintype α] [Fintype β] {γ : Type} [AddCommMonoid γ]
    (F : α → β → γ) : (∑ x : α × β, F x.1 x.2) = ∑ a, ∑ b, F a b :=
  Fintype.sum_prod_type (f := fun x : α × β => F x.1 x.2)

lemma sumFstSndEq' {α β : Type} [Fintype α] [Fintype β] {γ : Type} [AddCommMonoid γ]
    (F : α → β → γ) : (∑ a, ∑ b, F a b) = ∑ x : α × β, F x.1 x.2 :=
  (sumFstSndEq F).symm

lemma sumEquivSymm {α β : Type} [Fintype α] [Fintype β] {γ : Type} [AddCommMonoid γ]
    (e : α ≃ β) (F : β → γ) : (∑ b : β, F b) = ∑ a : α, F (e a) :=
  (Fintype.sum_equiv e (fun a => F (e a)) F (fun _ => rfl)).symm

lemma sumFourProdSwap {A K : Type} [Fintype A] [Fintype K] {γ : Type} [AddCommMonoid γ]
    (Q : (A × K) → (A × K) → (A × K) → (A × K) → γ) :
    (∑ p₀ : A × K, ∑ p₀' : A × K, ∑ p₁ : A × K, ∑ p₁' : A × K, Q p₀ p₀' p₁ p₁')
  = ∑ a₀ : A, ∑ a₀' : A, ∑ a₁ : A, ∑ a₁' : A, ∑ k₀ : K, ∑ k₀' : K, ∑ k₁ : K, ∑ k₁' : K,
      Q (a₀,k₀) (a₀',k₀') (a₁,k₁) (a₁',k₁') := by
  rw [sumFstSndEq' (F := fun (p₀ : A × K) (p₀' : A × K) =>
        ∑ p₁ : A × K, ∑ p₁' : A × K, Q p₀ p₀' p₁ p₁')]
  rw [Finset.sum_congr rfl (fun (x : (A × K) × (A × K)) _ => sumFstSndEq'
        (F := fun (p₁ : A × K) (p₁' : A × K) => Q x.1 x.2 p₁ p₁'))]
  rw [sumEquivSymm (pairSwapMiddle A K).symm
      (F := fun (r : (A × K) × (A × K)) =>
        ∑ y : (A × K) × (A × K), Q r.1 r.2 y.1 y.2)]
  rw [Finset.sum_congr rfl (fun (r₀ : (A × A) × (K × K)) _ => sumEquivSymm
      (pairSwapMiddle A K).symm
      (F := fun (r₁ : (A × K) × (A × K)) =>
        Q ((pairSwapMiddle A K).symm r₀).1 ((pairSwapMiddle A K).symm r₀).2 r₁.1 r₁.2))]
  rw [sumFstSndEq (F := fun (a : A × A) (b : K × K) =>
        ∑ r₁ : (A × A) × (K × K),
          Q ((pairSwapMiddle A K).symm (a,b)).1 ((pairSwapMiddle A K).symm (a,b)).2
            ((pairSwapMiddle A K).symm r₁).1 ((pairSwapMiddle A K).symm r₁).2)]
  rw [Finset.sum_congr rfl (fun (x : A × A) _ => Finset.sum_congr rfl (fun (y : K × K) _ =>
      sumFstSndEq (F := fun (a : A × A) (b : K × K) =>
        Q ((pairSwapMiddle A K).symm (x,y)).1 ((pairSwapMiddle A K).symm (x,y)).2
          ((pairSwapMiddle A K).symm (a,b)).1 ((pairSwapMiddle A K).symm (a,b)).2)))]
  rw [Finset.sum_congr rfl (fun (x : A × A) _ => Finset.sum_comm)]
  simp only [Fintype.sum_prod_type]
  simp only [pairSwapMiddle_symm_apply]

theorem pairObjRawSplit {I : Type} [Fintype I] (s M : ℕ) (hM : 0 < M) (qH : I → ℤ)
    (q₁ q₂ : I → Fin s → ℤ) (f : ℤ → ℂ) :
    (∑ i₀ : I, ∑ i₁ : I, ∑ H₀ : Fin (s + 1) → Fin M × Fin M,
        ∑ H₀' : Fin (s + 1) → Fin M × Fin M, ∑ H₁ : Fin (s + 1) → Fin M × Fin M,
          ∑ H₁' : Fin (s + 1) → Fin M × Fin M,
            Work.Peluse.SwapC.pairObj s M qH q₁ q₂ f i₀ i₁ H₀ H₀' H₁ H₁')
      = (M : ℂ) ^ 4 * ∑ i₀ : I, ∑ i₁ : I, ∑ a₀ : Fin M, ∑ a₀' : Fin M, ∑ a₁ : Fin M,
          ∑ a₁' : Fin M, ∑ k₀ : Fin s → Fin M × Fin M, ∑ k₀' : Fin s → Fin M × Fin M,
            ∑ k₁ : Fin s → Fin M × Fin M, ∑ k₁' : Fin s → Fin M × Fin M,
              Work.Peluse.SwapC.pairObj s M qH q₁ q₂ f i₀ i₁ (Fin.cons (a₀, ⟨0, hM⟩) k₀)
                (Fin.cons (a₀', ⟨0, hM⟩) k₀') (Fin.cons (a₁, ⟨0, hM⟩) k₁)
                (Fin.cons (a₁', ⟨0, hM⟩) k₁') := by
  classical
  have inner : ∀ i₀ i₁ : I,
      (∑ H₀ : Fin (s+1) → Fin M × Fin M, ∑ H₀' : Fin (s+1) → Fin M × Fin M,
        ∑ H₁ : Fin (s+1) → Fin M × Fin M, ∑ H₁' : Fin (s+1) → Fin M × Fin M,
          pairObj s M qH q₁ q₂ f i₀ i₁ H₀ H₀' H₁ H₁')
      = (M : ℂ)^4 * ∑ a₀ : Fin M, ∑ a₀' : Fin M, ∑ a₁ : Fin M, ∑ a₁' : Fin M,
          ∑ k₀ : Fin s → Fin M × Fin M, ∑ k₀' : Fin s → Fin M × Fin M,
            ∑ k₁ : Fin s → Fin M × Fin M, ∑ k₁' : Fin s → Fin M × Fin M,
              pairObj s M qH q₁ q₂ f i₀ i₁ (Fin.cons (a₀,⟨0,hM⟩) k₀)
                (Fin.cons (a₀',⟨0,hM⟩) k₀') (Fin.cons (a₁,⟨0,hM⟩) k₁)
                (Fin.cons (a₁',⟨0,hM⟩) k₁') := by
    intro i₀ i₁
    have hG1 : ∀ (a b : Fin M) (k : Fin s → Fin M × Fin M),
        (∑ H₀' : Fin (s+1) → Fin M × Fin M, ∑ H₁ : Fin (s+1) → Fin M × Fin M,
          ∑ H₁' : Fin (s+1) → Fin M × Fin M,
            pairObj s M qH q₁ q₂ f i₀ i₁ (Fin.cons (a,b) k) H₀' H₁ H₁')
        = ∑ H₀' : Fin (s+1) → Fin M × Fin M, ∑ H₁ : Fin (s+1) → Fin M × Fin M,
          ∑ H₁' : Fin (s+1) → Fin M × Fin M,
            pairObj s M qH q₁ q₂ f i₀ i₁ (Fin.cons (a,⟨0,hM⟩) k) H₀' H₁ H₁' := by
      intro a b k
      exact Finset.sum_congr rfl (fun H₀' _ => Finset.sum_congr rfl (fun H₁ _ =>
        Finset.sum_congr rfl (fun H₁' _ =>
          pairObj_cons_1 s M hM qH q₁ q₂ f i₀ i₁ a b k H₀' H₁ H₁')))
    rw [sumFinSuccSplit s M hM
        (G := fun H₀ : Fin (s+1) → Fin M × Fin M =>
          ∑ H₀' : Fin (s+1) → Fin M × Fin M, ∑ H₁ : Fin (s+1) → Fin M × Fin M,
            ∑ H₁' : Fin (s+1) → Fin M × Fin M, pairObj s M qH q₁ q₂ f i₀ i₁ H₀ H₀' H₁ H₁')
        (hG := hG1)]
    rw [Finset.sum_congr rfl (fun (p₀ : Fin M × (Fin s → Fin M × Fin M)) _ => by
      have hG2 : ∀ (a b : Fin M) (k : Fin s → Fin M × Fin M),
          (∑ H₁ : Fin (s+1) → Fin M × Fin M, ∑ H₁' : Fin (s+1) → Fin M × Fin M,
            pairObj s M qH q₁ q₂ f i₀ i₁ (Fin.cons (p₀.1,⟨0,hM⟩) p₀.2)
              (Fin.cons (a,b) k) H₁ H₁')
          = ∑ H₁ : Fin (s+1) → Fin M × Fin M, ∑ H₁' : Fin (s+1) → Fin M × Fin M,
            pairObj s M qH q₁ q₂ f i₀ i₁ (Fin.cons (p₀.1,⟨0,hM⟩) p₀.2)
              (Fin.cons (a,⟨0,hM⟩) k) H₁ H₁' := by
        intro a b k
        exact Finset.sum_congr rfl (fun H₁ _ => Finset.sum_congr rfl (fun H₁' _ =>
          pairObj_cons_2 s M hM qH q₁ q₂ f i₀ i₁ a b k
            (Fin.cons (p₀.1,⟨0,hM⟩) p₀.2) H₁ H₁'))
      exact sumFinSuccSplit s M hM
        (G := fun H₀' : Fin (s+1) → Fin M × Fin M =>
          ∑ H₁ : Fin (s+1) → Fin M × Fin M, ∑ H₁' : Fin (s+1) → Fin M × Fin M,
            pairObj s M qH q₁ q₂ f i₀ i₁ (Fin.cons (p₀.1,⟨0,hM⟩) p₀.2) H₀' H₁ H₁')
        (hG := hG2))]
    simp only [← Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun (p₀ : Fin M × (Fin s → Fin M × Fin M)) _ => Finset.sum_congr rfl (fun (p₀' : Fin M × (Fin s → Fin M × Fin M)) _ => by
      have hG3 : ∀ (a b : Fin M) (k : Fin s → Fin M × Fin M),
          (∑ H₁' : Fin (s+1) → Fin M × Fin M,
            pairObj s M qH q₁ q₂ f i₀ i₁ (Fin.cons (p₀.1,⟨0,hM⟩) p₀.2)
              (Fin.cons (p₀'.1,⟨0,hM⟩) p₀'.2) (Fin.cons (a,b) k) H₁')
          = ∑ H₁' : Fin (s+1) → Fin M × Fin M,
            pairObj s M qH q₁ q₂ f i₀ i₁ (Fin.cons (p₀.1,⟨0,hM⟩) p₀.2)
              (Fin.cons (p₀'.1,⟨0,hM⟩) p₀'.2) (Fin.cons (a,⟨0,hM⟩) k) H₁' := by
        intro a b k
        exact Finset.sum_congr rfl (fun H₁' _ =>
          pairObj_cons_3 s M hM qH q₁ q₂ f i₀ i₁ a b k
            (Fin.cons (p₀.1,⟨0,hM⟩) p₀.2) (Fin.cons (p₀'.1,⟨0,hM⟩) p₀'.2) H₁')
      exact sumFinSuccSplit s M hM
        (G := fun H₁ : Fin (s+1) → Fin M × Fin M =>
          ∑ H₁' : Fin (s+1) → Fin M × Fin M,
            pairObj s M qH q₁ q₂ f i₀ i₁ (Fin.cons (p₀.1,⟨0,hM⟩) p₀.2)
              (Fin.cons (p₀'.1,⟨0,hM⟩) p₀'.2) H₁ H₁')
        (hG := hG3)))]
    simp only [← Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun (p₀ : Fin M × (Fin s → Fin M × Fin M)) _ => Finset.sum_congr rfl (fun (p₀' : Fin M × (Fin s → Fin M × Fin M)) _ =>
      Finset.sum_congr rfl (fun (p₁ : Fin M × (Fin s → Fin M × Fin M)) _ => by
      have hG4 : ∀ (a b : Fin M) (k : Fin s → Fin M × Fin M),
          pairObj s M qH q₁ q₂ f i₀ i₁ (Fin.cons (p₀.1,⟨0,hM⟩) p₀.2)
              (Fin.cons (p₀'.1,⟨0,hM⟩) p₀'.2) (Fin.cons (p₁.1,⟨0,hM⟩) p₁.2) (Fin.cons (a,b) k)
          = pairObj s M qH q₁ q₂ f i₀ i₁ (Fin.cons (p₀.1,⟨0,hM⟩) p₀.2)
              (Fin.cons (p₀'.1,⟨0,hM⟩) p₀'.2) (Fin.cons (p₁.1,⟨0,hM⟩) p₁.2) (Fin.cons (a,⟨0,hM⟩) k) := by
        intro a b k
        exact pairObj_cons_4 s M hM qH q₁ q₂ f i₀ i₁ a b k
          (Fin.cons (p₀.1,⟨0,hM⟩) p₀.2) (Fin.cons (p₀'.1,⟨0,hM⟩) p₀'.2)
          (Fin.cons (p₁.1,⟨0,hM⟩) p₁.2)
      exact sumFinSuccSplit s M hM
        (G := fun H₁' : Fin (s+1) → Fin M × Fin M =>
            pairObj s M qH q₁ q₂ f i₀ i₁ (Fin.cons (p₀.1,⟨0,hM⟩) p₀.2)
              (Fin.cons (p₀'.1,⟨0,hM⟩) p₀'.2) (Fin.cons (p₁.1,⟨0,hM⟩) p₁.2) H₁')
        (hG := hG4))))]
    simp only [← Finset.mul_sum]
    ring_nf
    rw [sumFourProdSwap (Q := fun (p₀ : Fin M × (Fin s → Fin M × Fin M))
        (p₀' : Fin M × (Fin s → Fin M × Fin M)) (p₁ : Fin M × (Fin s → Fin M × Fin M))
        (p₁' : Fin M × (Fin s → Fin M × Fin M)) =>
          pairObj s M qH q₁ q₂ f i₀ i₁ (Fin.cons (p₀.1,⟨0,hM⟩) p₀.2)
            (Fin.cons (p₀'.1,⟨0,hM⟩) p₀'.2) (Fin.cons (p₁.1,⟨0,hM⟩) p₁.2)
            (Fin.cons (p₁'.1,⟨0,hM⟩) p₁'.2))]
  calc (∑ i₀ : I, ∑ i₁ : I, ∑ H₀ : Fin (s + 1) → Fin M × Fin M,
        ∑ H₀' : Fin (s + 1) → Fin M × Fin M, ∑ H₁ : Fin (s + 1) → Fin M × Fin M,
          ∑ H₁' : Fin (s + 1) → Fin M × Fin M,
            Work.Peluse.SwapC.pairObj s M qH q₁ q₂ f i₀ i₁ H₀ H₀' H₁ H₁')
      = ∑ i₀ : I, ∑ i₁ : I, (M : ℂ)^4 *
          ∑ a₀ : Fin M, ∑ a₀' : Fin M, ∑ a₁ : Fin M, ∑ a₁' : Fin M,
            ∑ k₀ : Fin s → Fin M × Fin M, ∑ k₀' : Fin s → Fin M × Fin M,
              ∑ k₁ : Fin s → Fin M × Fin M, ∑ k₁' : Fin s → Fin M × Fin M,
                pairObj s M qH q₁ q₂ f i₀ i₁ (Fin.cons (a₀,⟨0,hM⟩) k₀)
                  (Fin.cons (a₀',⟨0,hM⟩) k₀') (Fin.cons (a₁,⟨0,hM⟩) k₁)
                  (Fin.cons (a₁',⟨0,hM⟩) k₁') :=
        Finset.sum_congr rfl (fun i₀ _ => Finset.sum_congr rfl (fun i₁ _ => inner i₀ i₁))
    _ = (M : ℂ)^4 * ∑ i₀ : I, ∑ i₁ : I, ∑ a₀ : Fin M, ∑ a₀' : Fin M, ∑ a₁ : Fin M,
          ∑ a₁' : Fin M, ∑ k₀ : Fin s → Fin M × Fin M, ∑ k₀' : Fin s → Fin M × Fin M,
            ∑ k₁ : Fin s → Fin M × Fin M, ∑ k₁' : Fin s → Fin M × Fin M,
              Work.Peluse.SwapC.pairObj s M qH q₁ q₂ f i₀ i₁ (Fin.cons (a₀, ⟨0, hM⟩) k₀)
                (Fin.cons (a₀', ⟨0, hM⟩) k₀') (Fin.cons (a₁, ⟨0, hM⟩) k₁)
                (Fin.cons (a₁', ⟨0, hM⟩) k₁') := by
        simp only [← Finset.mul_sum]

end Work.Peluse.SwapC
