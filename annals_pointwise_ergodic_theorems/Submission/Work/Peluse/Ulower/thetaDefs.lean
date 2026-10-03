import Mathlib
import Submission.Work.Peluse.Ulower.iterDefs

/-!
# The counting lemma for Peluse's `□_s(H)`: the finite combinatorics

This module fixes the vocabulary of the counting lemma `Work.Peluse.Ulower.thetaSet_card_ge`,
i.e. of Peluse's Lemma 7.4's `□_s(H)`: the number of triples `(k⁽¹⁾,k⁽²⁾,k⁽³⁾) ∈ ([1,D]^σ)³`
such that for every `ω : Fin σ → Bool` the pair `(k⁽¹⁾, ω·k⁽²⁾ + (1-ω)·k⁽³⁾)` lies in `H`.

The mathematical content is the following.  If `H ⊆ [1,D]^σ × [1,D]^σ` has density `γ`
(i.e. `|H| ≥ γ·D^{2σ}`), then

  `|ThetaSet σ D H| ≥ γ^{2^σ} D^{3σ}`.

The proof is a "Loomis–Whitney type" counting argument:

* for a *single* `k⁽¹⁾` the `2^σ` conditions say that the whole `2^σ`-point box spanned by
  `k⁽²⁾` and `k⁽³⁾` lies in the fibre `K = {c | (k⁽¹⁾,c) ∈ H}`; writing `N(K)` for the number of
  such pairs, one has the *pair-counting bound* `N(K) ≥ |K|^{2^σ} / D^{σ(2^σ-2)}`, proved by
  induction on `σ` using Cauchy–Schwarz twice at each step;
* summing the pair-counting bound over `k⁽¹⁾` and applying the power mean inequality to the fibre
  sizes gives `|ThetaSet| ≥ |H|^{2^σ}/D^{σ(2^{σ+1}-3)}`, which is `γ^{2^σ}D^{3σ}`.

The definitions here are the interface of that argument.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

open Finset

/-- The box `[1,D]^σ ⊆ ℤ^σ` of admissible shifts, as a finset of functions `Fin σ → ℤ`. -/
def thetaBox (σ D : ℕ) : Finset (Fin σ → ℤ) :=
  Fintype.piFinset (fun _ : Fin σ => Finset.Icc (1 : ℤ) (D : ℤ))

lemma mem_thetaBox {σ D : ℕ} {f : Fin σ → ℤ} :
    f ∈ thetaBox σ D ↔ ∀ i, f i ∈ Finset.Icc (1 : ℤ) (D : ℤ) :=
  Fintype.mem_piFinset

lemma thetaBox_card (σ D : ℕ) : (thetaBox σ D).card = D ^ σ := by
  rw [thetaBox, Fintype.card_piFinset]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [Int.card_Icc]
  norm_num

/-- The `ω`-th corner of the box spanned by `s` and `t`: coordinatewise selection of `s` where
`ω` is true and of `t` where `ω` is false. -/
def thetaSel {σ : ℕ} (ω : Fin σ → Bool) (s t : Fin σ → ℤ) : Fin σ → ℤ :=
  fun i => if ω i then s i else t i

lemma thetaSel_mem_thetaBox {σ D : ℕ} {s t : Fin σ → ℤ} (hs : s ∈ thetaBox σ D)
    (ht : t ∈ thetaBox σ D) (ω : Fin σ → Bool) : thetaSel ω s t ∈ thetaBox σ D := by
  rw [mem_thetaBox] at hs ht ⊢
  intro i
  by_cases h : ω i
  · simpa [thetaSel, h] using hs i
  · simpa [thetaSel, h] using ht i

lemma thetaSel_cons {σ : ℕ} (ε : Bool) (ω : Fin σ → Bool) (a b : ℤ) (u v : Fin σ → ℤ) :
    thetaSel (Fin.cons ε ω) (Fin.cons a u) (Fin.cons b v)
      = Fin.cons (if ε then a else b) (thetaSel ω u v) := by
  funext i
  cases i using Fin.cases with
  | zero => simp [thetaSel]
  | succ i => rfl

lemma thetaSel_eq_cons {σ : ℕ} (ω : Fin (σ+1) → Bool) (s t : Fin (σ+1) → ℤ) :
    thetaSel ω s t = Fin.cons (if ω 0 then s 0 else t 0)
      (thetaSel (Fin.tail ω) (Fin.tail s) (Fin.tail t)) := by
  funext i
  cases i using Fin.cases with
  | zero => simp [thetaSel]
  | succ i => rfl

/-- The number of ordered pairs `(s,t)` in `[1,D]^σ × [1,D]^σ` whose `2^σ` "corners"
`thetaSel ω s t` all lie in `K`. -/
def thetaPairCount (σ D : ℕ) (K : Finset (Fin σ → ℤ)) : ℕ :=
  ((thetaBox σ D).product (thetaBox σ D) |>.filter
    (fun p => ∀ ω : Fin σ → Bool, thetaSel ω p.1 p.2 ∈ K)).card

lemma thetaPairCount_eq_sum (σ D : ℕ) (K : Finset (Fin σ → ℤ)) :
    thetaPairCount σ D K =
      ∑ s ∈ thetaBox σ D, ∑ t ∈ thetaBox σ D,
        if (∀ ω : Fin σ → Bool, thetaSel ω s t ∈ K) then 1 else 0 := by
  rw [thetaPairCount, Finset.card_filter,
    show (thetaBox σ D).product (thetaBox σ D) = thetaBox σ D ×ˢ thetaBox σ D from rfl,
    Finset.sum_product]

/-- The fibre of `H` over its first component. -/
def thetaFibre {σ : ℕ} (D : ℕ) (H : Finset ((Fin σ → ℤ) × (Fin σ → ℤ))) (k1 : Fin σ → ℤ) :
    Finset (Fin σ → ℤ) :=
  (thetaBox σ D).filter (fun k2 => (k1, k2) ∈ H)

lemma mem_thetaFibre {σ D : ℕ} {H : Finset ((Fin σ → ℤ) × (Fin σ → ℤ))} {k1 k2 : Fin σ → ℤ} :
    k2 ∈ thetaFibre D H k1 ↔ k2 ∈ thetaBox σ D ∧ (k1, k2) ∈ H :=
  Finset.mem_filter

lemma thetaFibre_subset {σ D : ℕ} (H : Finset ((Fin σ → ℤ) × (Fin σ → ℤ))) (k1 : Fin σ → ℤ) :
    thetaFibre D H k1 ⊆ thetaBox σ D :=
  Finset.filter_subset _ _

/-- The fibre of `K ⊆ [1,D]^(σ+1)` over the value of its `0`-th coordinate. -/
def thetaFibreOne {σ : ℕ} (D : ℕ) (K : Finset (Fin (σ+1) → ℤ)) (a : ℤ) :
    Finset (Fin σ → ℤ) :=
  (thetaBox σ D).filter (fun u => Fin.cons a u ∈ K)

lemma mem_thetaFibreOne {σ D : ℕ} {K : Finset (Fin (σ+1) → ℤ)} {a : ℤ} {u : Fin σ → ℤ} :
    u ∈ thetaFibreOne D K a ↔ u ∈ thetaBox σ D ∧ Fin.cons a u ∈ K :=
  Finset.mem_filter

lemma thetaFibreOne_subset {σ D : ℕ} (K : Finset (Fin (σ+1) → ℤ)) (a : ℤ) :
    thetaFibreOne D K a ⊆ thetaBox σ D :=
  Finset.filter_subset _ _

lemma tail_mem_thetaBox {σ D : ℕ} {s : Fin (σ+1) → ℤ} (hs : s ∈ thetaBox (σ+1) D) :
    Fin.tail s ∈ thetaBox σ D := by
  rw [mem_thetaBox] at hs ⊢
  intro i
  simpa [Fin.tail] using hs i.succ

lemma cons_mem_thetaBox {σ D : ℕ} {a : ℤ} {u : Fin σ → ℤ}
    (ha : a ∈ Finset.Icc (1:ℤ) (D:ℤ)) (hu : u ∈ thetaBox σ D) :
    Fin.cons a u ∈ thetaBox (σ+1) D := by
  rw [mem_thetaBox] at hu ⊢
  intro i
  cases i using Fin.cases with
  | zero => simpa using ha
  | succ j => simpa using hu j

/-- Splitting a sum over `[1,D]^(σ+1)` into the value of the `0`-th coordinate and the `tail`. -/
lemma thetaSum_box_succ {σ D : ℕ} {M : Type*} [AddCommMonoid M] (F : (Fin (σ+1) → ℤ) → M) :
    ∑ s ∈ thetaBox (σ+1) D, F s =
      ∑ a ∈ Finset.Icc (1:ℤ) (D:ℤ), ∑ u ∈ thetaBox σ D, F (Fin.cons a u) := by
  have h1 : (∑ a ∈ Finset.Icc (1:ℤ) (D:ℤ), ∑ u ∈ thetaBox σ D, F (Fin.cons a u))
      = ∑ p ∈ (Finset.Icc (1:ℤ) (D:ℤ)) ×ˢ thetaBox σ D, F (Fin.cons p.1 p.2) := by
    rw [Finset.sum_product]
  rw [h1]
  refine Finset.sum_bij' (fun s _ => (s 0, Fin.tail s)) (fun p _ => Fin.cons p.1 p.2)
    (fun s hs => ?_) (fun p hp => ?_) (fun s hs => ?_) (fun p hp => ?_) (fun s hs => ?_)
  · exact Finset.mem_product.mpr ⟨(mem_thetaBox.mp hs 0), tail_mem_thetaBox hs⟩
  · exact cons_mem_thetaBox (Finset.mem_product.mp hp).1 (Finset.mem_product.mp hp).2
  · exact Fin.cons_self_tail s
  · simp [Fin.tail_cons]
  · simp [Fin.cons_self_tail]

end

end Work.Peluse.Ulower
