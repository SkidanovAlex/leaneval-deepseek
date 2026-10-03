import Mathlib
import Submission.Work.A3.Defs

/-!
# The energy of a polynomial sequence over an arbitrary finite set

`Work.A3.polyEnergy Q s N` counts the pairs of `s`-tuples of integers in `[1,N]^s` with equal
`Q`-sums; it is the `2s`-th moment of the exponential sum `∑_{n ≤ N} e(θ Q(n))`
(`Work.A3.moment_identity`), and the object of the arithmetic core `Work.A3.PolyEnergyBound` of
Area A3 (`Submission/Work/A3/Defs.lean`).

This module (sorry-free, and hence safe to import) holds the formalisable *foundations* of the
sharp mean value estimate `E_s(N) ≪ N^{2s - deg Q}`:

* the energy over a **general** finite set `A ⊆ ℤ` (`polyEnergyOn`), which is what allows the
  interval shifts coming from the normalisation of `Q` to be stated;
* the trivial upper bound `E_s(A) ≤ |A|^{2s}` and monotonicity of `A ↦ E_s(A)` and of `N ↦ E_s(N)`
  (the latter is how a proof reduces to large `N`);
* the `WLOG` invariances of the target: adding a constant to `Q` (`polyEnergy_const_add`),
  changing its sign (`polyEnergy_neg`) and shifting the argument of `Q`
  (`polyEnergyOn_comp_add` / `polyEnergy_comp_add`), the last of which *shifts the summation set*
  rather than leaving it fixed.  Together they normalise `Q` to have positive leading coefficient
  and `Q'' > 0` on the range, but — since the energy is **not** invariant under translating the
  argument of `Q` (e.g. `Q = X²+X`, `s = 2`: `E₂({1,…,5}) = 53` but `E₂({2,…,6}) = 45`) — this
  reduction is legitimate only for a proof that establishes the estimate for every interval
  `[a+1, a+N]`, which is how the circle method works anyway.  See §2 of
  `NOTES_A3_polyEnergy_bound.md`.

See `NOTES_A3_polyEnergy_bound.md` (workspace root) for the analysis of what the full proof of
`PolyEnergyBound` requires.
-/

set_option autoImplicit false

namespace Work.A3

open Polynomial Finset
open scoped BigOperators

/-- The `s`-fold **energy of `Q` over an arbitrary finite set `A ⊆ ℤ`**: the number of pairs of
`s`-tuples of elements of `A` whose `Q`-sums agree.  `polyEnergy Q s N` is the special case
`A = {1, …, N}` (`polyEnergy_eq_polyEnergyOn`).  Working with a general `A` is what allows the
interval shifts coming from the `WLOG` normalisation of `Q` to be stated. -/
def polyEnergyOn (Q : ℤ[X]) (s : ℕ) (A : Finset ℤ) : ℕ :=
  (((Fintype.piFinset (fun _ : Fin s => A)).product
   (Fintype.piFinset (fun _ : Fin s => A))).filter
   (fun p => (∑ i, Q.eval (p.1 i)) = (∑ i, Q.eval (p.2 i)))).card

lemma polyEnergy_eq_polyEnergyOn (Q : ℤ[X]) (s N : ℕ) :
    polyEnergy Q s N = polyEnergyOn Q s (Finset.Icc (1 : ℤ) (N : ℤ)) := rfl

/-- Membership in a product of finsets, phrased with `Finset.product` so that it rewrites the
goal (the Mathlib lemma is stated with the `×ˢ` notation). -/
lemma mem_product_iff {α β : Type*} {s : Finset α} {t : Finset β} {p : α × β} :
    p ∈ s.product t ↔ p.1 ∈ s ∧ p.2 ∈ t := Finset.mem_product

/-- The tuples of an `s`-fold product are `|A|^s` in number. -/
lemma card_piFinset_int (A : Finset ℤ) (s : ℕ) :
    (Fintype.piFinset (fun _ : Fin s => A)).card = A.card ^ s := by
  rw [Fintype.card_piFinset]
  simp [Finset.prod_const]

lemma card_prod_piFinset_int (A : Finset ℤ) (s : ℕ) :
    ((Fintype.piFinset (fun _ : Fin s => A)).product
      (Fintype.piFinset (fun _ : Fin s => A))).card = A.card ^ (2 * s) := by
  have h : ((Fintype.piFinset (fun _ : Fin s => A)).product
      (Fintype.piFinset (fun _ : Fin s => A))).card
      = (Fintype.piFinset (fun _ : Fin s => A)).card
        * (Fintype.piFinset (fun _ : Fin s => A)).card :=
    Finset.card_product _ _
  rw [h, card_piFinset_int, ← pow_add, ← Nat.two_mul]

/-- **Trivial upper bound**: the energy never exceeds the total number of pairs of tuples. -/
lemma polyEnergyOn_le_card_pow (Q : ℤ[X]) (s : ℕ) (A : Finset ℤ) :
    polyEnergyOn Q s A ≤ A.card ^ (2 * s) := by
  refine le_trans (Finset.card_filter_le _ _) ?_
  rw [card_prod_piFinset_int]

lemma polyEnergy_le_pow (Q : ℤ[X]) (s N : ℕ) : polyEnergy Q s N ≤ N ^ (2 * s) := by
  have h := polyEnergyOn_le_card_pow Q s (Finset.Icc (1 : ℤ) (N : ℤ))
  rw [Int.card_Icc] at h
  have h' : ((N : ℤ) + 1 - 1).toNat = N := by simp
  rw [h'] at h
  exact h

/-- The energy is monotone in the underlying set. -/
lemma polyEnergyOn_mono (Q : ℤ[X]) (s : ℕ) {A B : Finset ℤ} (hAB : A ⊆ B) :
    polyEnergyOn Q s A ≤ polyEnergyOn Q s B := by
  unfold polyEnergyOn
  refine Finset.card_le_card ?_
  refine Finset.filter_subset_filter _ ?_
  exact Finset.product_subset_product
    (Fintype.piFinset_subset _ _ (fun _ => hAB))
    (Fintype.piFinset_subset _ _ (fun _ => hAB))

/-- **Monotonicity in `N`**; this is how a proof reduces to the range `N ≥ N₀` on which the
circle-method estimates are non-trivial (small `N` is absorbed into the constant). -/
lemma polyEnergy_mono (Q : ℤ[X]) (s : ℕ) {N M : ℕ} (hNM : N ≤ M) :
    polyEnergy Q s N ≤ polyEnergy Q s M := by
  rw [polyEnergy_eq_polyEnergyOn, polyEnergy_eq_polyEnergyOn]
  refine polyEnergyOn_mono Q s (Finset.Icc_subset_Icc (le_refl (1 : ℤ)) ?_)
  exact_mod_cast hNM

/-- Adding a constant to `Q` shifts both sides of the defining equation by `s·c`. -/
lemma polyEnergy_const_add (Q : ℤ[X]) (s N : ℕ) (c : ℤ) :
    polyEnergy (Q + Polynomial.C c) s N = polyEnergy Q s N := by
  rw [polyEnergy_eq_polyEnergyOn, polyEnergy_eq_polyEnergyOn]
  unfold polyEnergyOn
  congr 1
  ext p
  simp only [Finset.mem_filter]
  constructor
  · intro h
    obtain ⟨hm, he⟩ := h
    refine ⟨hm, ?_⟩
    simp only [Polynomial.eval_add, Polynomial.eval_C] at he
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at he
    exact add_right_cancel he
  · intro h
    obtain ⟨hm, he⟩ := h
    refine ⟨hm, ?_⟩
    simp only [Polynomial.eval_add, Polynomial.eval_C]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, he]

/-- Changing the sign of `Q` does not change the energy.  Together with `polyEnergy_const_add`
this is the `WLOG` reduction of the leading coefficient of `Q` to be positive. -/
lemma polyEnergy_neg (Q : ℤ[X]) (s N : ℕ) :
    polyEnergy (-Q) s N = polyEnergy Q s N := by
  rw [polyEnergy_eq_polyEnergyOn, polyEnergy_eq_polyEnergyOn]
  unfold polyEnergyOn
  congr 1
  ext p
  simp only [Finset.mem_filter]
  constructor
  · intro h
    obtain ⟨hm, he⟩ := h
    refine ⟨hm, ?_⟩
    simp only [Polynomial.eval_neg] at he
    rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib] at he
    exact neg_inj.mp he
  · intro h
    obtain ⟨hm, he⟩ := h
    refine ⟨hm, ?_⟩
    simp only [Polynomial.eval_neg]
    rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib, he]

lemma eval_comp_X_add_C (Q : ℤ[X]) (c x : ℤ) :
    (Q.comp (Polynomial.X + Polynomial.C c)).eval x = Q.eval (x + c) := by
  rw [Polynomial.eval_comp]
  congr 1
  simp

/-- **Shifting the argument of `Q` shifts the summation set.**  This is the interface of the
`WLOG Q'' > 0` reduction: replacing `Q` by `Q(· + c)` is the same as computing the energy of `Q`
over the shifted interval `A + c`, so a proof of the sharp estimate for *all* intervals (which
the circle method gives) may assume `Q'' > 0` on the range. -/
lemma polyEnergyOn_comp_add (Q : ℤ[X]) (s : ℕ) (A : Finset ℤ) (c : ℤ) :
    polyEnergyOn (Q.comp (Polynomial.X + Polynomial.C c)) s A
      = polyEnergyOn Q s (A.image (fun x => x + c)) := by
  unfold polyEnergyOn
  refine Finset.card_bij
    (fun p _ => (((fun i => p.1 i + c)), ((fun i => p.2 i + c)))) ?h1 ?h2 ?h3
  case h1 =>
    intro p hp
    rw [Finset.mem_filter, mem_product_iff] at hp
    obtain ⟨hp, he⟩ := hp
    obtain ⟨hp1, hp2⟩ := hp
    rw [Fintype.mem_piFinset] at hp1 hp2
    rw [Finset.mem_filter, mem_product_iff]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Fintype.mem_piFinset]; intro i
      exact Finset.mem_image.mpr ⟨p.1 i, hp1 i, rfl⟩
    · rw [Fintype.mem_piFinset]; intro i
      exact Finset.mem_image.mpr ⟨p.2 i, hp2 i, rfl⟩
    · simpa only [eval_comp_X_add_C] using he
  case h2 =>
    intro p1 _ p2 _ hpq
    have h1 : (fun i => p1.1 i + c) = (fun i => p2.1 i + c) := congrArg Prod.fst hpq
    have h2 : (fun i => p1.2 i + c) = (fun i => p2.2 i + c) := congrArg Prod.snd hpq
    have e1 : p1.1 = p2.1 := by
      funext i; have := congrFun h1 i; omega
    have e2 : p1.2 = p2.2 := by
      funext i; have := congrFun h2 i; omega
    exact Prod.ext e1 e2
  case h3 =>
    intro q hq
    rw [Finset.mem_filter, mem_product_iff] at hq
    obtain ⟨hq, he⟩ := hq
    obtain ⟨hq1, hq2⟩ := hq
    rw [Fintype.mem_piFinset] at hq1 hq2
    refine ⟨((fun i => q.1 i - c), (fun i => q.2 i - c)), ?_, ?_⟩
    · rw [Finset.mem_filter, mem_product_iff]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [Fintype.mem_piFinset]; intro i
        obtain ⟨a, ha, _⟩ := Finset.mem_image.mp (hq1 i)
        have hsub : q.1 i - c = a := by omega
        show q.1 i - c ∈ A
        rw [hsub]; exact ha
      · rw [Fintype.mem_piFinset]; intro i
        obtain ⟨a, ha, _⟩ := Finset.mem_image.mp (hq2 i)
        have hsub : q.2 i - c = a := by omega
        show q.2 i - c ∈ A
        rw [hsub]; exact ha
      · simp only [eval_comp_X_add_C, sub_add_cancel]
        exact he
    · ext i <;> simp

lemma polyEnergy_comp_add (Q : ℤ[X]) (s N : ℕ) (c : ℤ) :
    polyEnergy (Q.comp (Polynomial.X + Polynomial.C c)) s N
      = polyEnergyOn Q s ((Finset.Icc (1 : ℤ) (N : ℤ)).image (fun x => x + c)) :=
  polyEnergyOn_comp_add Q s _ c

end Work.A3
