import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators
open Finset Polynomial

namespace Commons.Combinatorics.Fin

/-! If two finite lists of natural numbers (of equal length `n`) have equal power sums
`p_0, ..., p_n`, then they are permutations of one another.  The proof proceeds in stages:

1. Newton's identities (`MvPolynomial.mul_esymm_eq_sum`) show that equal power sums force
   equal elementary symmetric sums.
2. Vieta's formula (`Multiset.prod_X_sub_X_eq_sum_esymm`) shows that equal elementary symmetric
   sums force the two monic polynomials `∏ (X - z)` to agree.
3. A root-removal induction shows that equal monic split products force the multisets of roots
   to agree.
4. Equal value multisets give a permutation of the indices. -/

private lemma esymm_multiset_eq_of_powerSums_eq {n : ℕ} (f g : Fin n → ℤ)
    (hp : ∀ j ≤ n, (∑ i : Fin n, f i ^ j) = (∑ i : Fin n, g i ^ j)) :
    ∀ k ≤ n, ((Finset.univ : Finset (Fin n)).val.map f).esymm k =
        ((Finset.univ : Finset (Fin n)).val.map g).esymm k := by
  classical
  have hp' : ∀ j ≤ n, MvPolynomial.aeval f (MvPolynomial.psum (Fin n) ℤ j) =
        MvPolynomial.aeval g (MvPolynomial.psum (Fin n) ℤ j) := by
    intro j hj
    simp [MvPolynomial.psum, hp j hj]
  have hE : ∀ m ≤ n, MvPolynomial.aeval f (MvPolynomial.esymm (Fin n) ℤ m) =
        MvPolynomial.aeval g (MvPolynomial.esymm (Fin n) ℤ m) := by
    intro m
    refine Nat.strong_induction_on m ?_
    intro m ih hm
    by_cases hm0 : m = 0
    · subst m
      simp [MvPolynomial.esymm]
    · have hn := MvPolynomial.mul_esymm_eq_sum (Fin n) ℤ m
      have hfx := congrArg (MvPolynomial.aeval f) hn
      have hgx := congrArg (MvPolynomial.aeval g) hn
      have hRf : (∑ a ∈ (antidiagonal m).filter (fun a : ℕ × ℕ => a.1 < m),
            (-1 : ℤ) ^ a.1 * MvPolynomial.aeval f (MvPolynomial.esymm (Fin n) ℤ a.1) *
              MvPolynomial.aeval f (MvPolynomial.psum (Fin n) ℤ a.2)) =
            (∑ a ∈ (antidiagonal m).filter (fun a : ℕ × ℕ => a.1 < m),
            (-1 : ℤ) ^ a.1 * MvPolynomial.aeval g (MvPolynomial.esymm (Fin n) ℤ a.1) *
              MvPolynomial.aeval g (MvPolynomial.psum (Fin n) ℤ a.2)) := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          have ha1 : a.1 < m := (Finset.mem_filter.mp ha).2
          have hsum : a.1 + a.2 = m := by
            simpa using (mem_antidiagonal.mp (Finset.mem_filter.mp ha).1)
          have ha1n : a.1 ≤ n := by omega
          have ha2n : a.2 ≤ n := by omega
          have h1 : MvPolynomial.aeval f (MvPolynomial.esymm (Fin n) ℤ a.1) =
              MvPolynomial.aeval g (MvPolynomial.esymm (Fin n) ℤ a.1) := ih a.1 ha1 ha1n
          have h2 : MvPolynomial.aeval f (MvPolynomial.psum (Fin n) ℤ a.2) =
              MvPolynomial.aeval g (MvPolynomial.psum (Fin n) ℤ a.2) := hp' a.2 ha2n
          simp [h1, h2]
      have hmpos : 0 < m := by omega
      have hmz : (m : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hmpos)
      have hcm : (m : ℤ) * MvPolynomial.aeval f (MvPolynomial.esymm (Fin n) ℤ m) =
          (m : ℤ) * MvPolynomial.aeval g (MvPolynomial.esymm (Fin n) ℤ m) := by
        have hf1 : (m : ℤ) * MvPolynomial.aeval f (MvPolynomial.esymm (Fin n) ℤ m) =
            (-1 : ℤ) ^ (m + 1) * (∑ a ∈ (antidiagonal m).filter (fun a : ℕ × ℕ => a.1 < m),
              (-1 : ℤ) ^ a.1 * MvPolynomial.aeval f (MvPolynomial.esymm (Fin n) ℤ a.1) *
                MvPolynomial.aeval f (MvPolynomial.psum (Fin n) ℤ a.2)) := by
          simpa using hfx
        have hg1 : (m : ℤ) * MvPolynomial.aeval g (MvPolynomial.esymm (Fin n) ℤ m) =
            (-1 : ℤ) ^ (m + 1) * (∑ a ∈ (antidiagonal m).filter (fun a : ℕ × ℕ => a.1 < m),
              (-1 : ℤ) ^ a.1 * MvPolynomial.aeval g (MvPolynomial.esymm (Fin n) ℤ a.1) *
                MvPolynomial.aeval g (MvPolynomial.psum (Fin n) ℤ a.2)) := by
          simpa using hgx
        rw [hf1, hg1, hRf]
      exact mul_left_cancel₀ hmz hcm
  intro k hk
  have hf := MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin n) ℤ k f
  have hg := MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin n) ℤ k g
  rw [← hf, ← hg]
  exact hE k hk

private lemma aeval_prod_map_X_sub_C (a : ℤ) (s : Multiset ℤ) :
    (Polynomial.aeval a) ((s.map fun z => Polynomial.X - Polynomial.C z).prod) =
      (s.map fun z => a - z).prod := by
  induction s using Multiset.induction with
  | empty => simp
  | cons z s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons]
      rw [map_mul]
      rw [ih]
      simp

private lemma multiset_eq_of_prod_eq_core :
    ∀ s : Multiset ℤ, ∀ t : Multiset ℤ, s.card = t.card →
     (s.map (fun z : ℤ => Polynomial.X - Polynomial.C z)).prod =
       (t.map (fun z : ℤ => Polynomial.X - Polynomial.C z)).prod → s = t := by
  classical
  intro s
  refine Multiset.induction_on s ?base ?step
  · intro t hcard hp
    have ht0 : t.card = 0 := by simpa using hcard.symm
    exact (Multiset.card_eq_zero.mp ht0).symm
  · intro a s' ih t hcard hp
    have hrootL : (Polynomial.aeval a) (((a ::ₘ s').map fun z => Polynomial.X - Polynomial.C z).prod) = 0 := by
      rw [Multiset.map_cons, Multiset.prod_cons, map_mul]
      simp
    have hrootR : (Polynomial.aeval a) ((t.map fun z => Polynomial.X - Polynomial.C z).prod) = 0 := by
      rw [← hp]
      exact hrootL
    have hz : (t.map (fun z => a - z)).prod = 0 := by
      rw [← aeval_prod_map_X_sub_C a t]
      exact hrootR
    have hzin : (0 : ℤ) ∈ t.map (fun z : ℤ => a - z) := Multiset.prod_eq_zero_iff.mp hz
    obtain ⟨z, hzmem, hz0⟩ := Multiset.mem_map.mp hzin
    have hza : z = a := by omega
    have hat : a ∈ t := by
      rw [hza] at hzmem
      exact hzmem
    have hsplit_s : ((a ::ₘ s').map fun z => Polynomial.X - Polynomial.C z).prod =
        (Polynomial.X - Polynomial.C a) * ((s'.map fun z => Polynomial.X - Polynomial.C z).prod) := by
      simp [Multiset.prod_cons, Multiset.map_cons]
    have htcons : a ::ₘ t.erase a = t := Multiset.cons_erase hat
    have hsplit_t : (t.map fun z => Polynomial.X - Polynomial.C z).prod =
        (Polynomial.X - Polynomial.C a) * (((t.erase a).map fun z => Polynomial.X - Polynomial.C z).prod) := by
      rw [← htcons]
      simp [Multiset.prod_cons, Multiset.map_cons]
    have hp' : (s'.map fun z => Polynomial.X - Polynomial.C z).prod =
        ((t.erase a).map fun z => Polynomial.X - Polynomial.C z).prod := by
      apply mul_left_cancel₀ (Polynomial.X_sub_C_ne_zero a)
      rw [hsplit_s.symm, hp, hsplit_t]
    have hcard' : s'.card = (t.erase a).card := by
      have h1 : s'.card + 1 = (t.erase a).card + 1 := by
        calc
          s'.card + 1 = (a ::ₘ s').card := (Multiset.card_cons a s').symm
          _ = t.card := hcard
          _ = (a ::ₘ (t.erase a)).card := by rw [htcons]
          _ = (t.erase a).card + 1 := Multiset.card_cons a (t.erase a)
      omega
    have hEq : s' = t.erase a := ih (t.erase a) hcard' hp'
    rw [← htcons]
    exact congrArg (fun m : Multiset ℤ => a ::ₘ m) hEq

private lemma card_filter_univ_val {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    ((Finset.univ : Finset (Fin n)).val.filter p).card =
      ((Finset.univ : Finset (Fin n)).filter p).card := by rfl

private lemma count_map_univ_val {n : ℕ} (c : ℤ) (f : Fin n → ℤ) :
    Multiset.count c ((Finset.univ : Finset (Fin n)).val.map f) =
      ((Finset.univ : Finset (Fin n)).filter (fun i => f i = c)).card := by
  rw [Multiset.count_map]
  rw [card_filter_univ_val]
  congr 1
  ext i
  simp [eq_comm]

private lemma card_fiber {n : ℕ} (c : ℤ) (f : Fin n → ℤ) :
    Fintype.card {i : Fin n // f i = c} =
      ((Finset.univ : Finset (Fin n)).filter (fun i => f i = c)).card := by
  rw [Fintype.card_subtype]

private lemma exists_perm_of_multiset_map_eq {n : ℕ} (f g : Fin n → ℤ)
    (h : ((Finset.univ : Finset (Fin n)).val.map f) = ((Finset.univ : Finset (Fin n)).val.map g)) :
    ∃ σ : Equiv.Perm (Fin n), g ∘ σ = f := by
  classical
  have hcount (c : ℤ) : Fintype.card {i : Fin n // f i = c} = Fintype.card {i : Fin n // g i = c} := by
    have hc := congrArg (fun s : Multiset ℤ => Multiset.count c s) h
    rwa [count_map_univ_val, count_map_univ_val, ← card_fiber, ← card_fiber] at hc
  let e : ∀ c : ℤ, {i : Fin n // f i = c} ≃ {i : Fin n // g i = c} := fun c => Fintype.equivOfCardEq (hcount c)
  refine ⟨Equiv.ofFiberEquiv e, ?_⟩
  funext i
  exact Equiv.ofFiberEquiv_map e i

/-- Equal power sums up to the length of the tuples force the tuples to be permutations of
one another. -/
theorem exists_perm_of_powerSums_eq (n : ℕ) (x y : Fin n → ℕ)
    (h : ∀ j ≤ n, (∑ i, (x i) ^ j) = (∑ i, (y i) ^ j)) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, y i = x (σ i) := by
  classical
  let xf : Fin n → ℤ := fun i => (x i : ℤ)
  let yf : Fin n → ℤ := fun i => (y i : ℤ)
  let sx : Multiset ℤ := (Finset.univ : Finset (Fin n)).val.map xf
  let sy : Multiset ℤ := (Finset.univ : Finset (Fin n)).val.map yf
  have hZ : ∀ j ≤ n, (∑ i : Fin n, xf i ^ j) = (∑ i : Fin n, yf i ^ j) := by
    intro j hj
    dsimp [xf, yf]
    exact_mod_cast h j hj
  have hE := esymm_multiset_eq_of_powerSums_eq xf yf hZ
  have hcard_sx : sx.card = n := by simp [sx]
  have hcard_sy : sy.card = n := by simp [sy]
  have hP1 : (sx.map fun z => Polynomial.X - Polynomial.C z).prod =
        ∑ j ∈ range (n + 1),
          ((-1 : Polynomial ℤ) ^ j) * (Polynomial.C (sx.esymm j) * Polynomial.X ^ (n - j)) := by
    simpa [hcard_sx] using Multiset.prod_X_sub_X_eq_sum_esymm sx
  have hP2 : (sy.map fun z => Polynomial.X - Polynomial.C z).prod =
        ∑ j ∈ range (n + 1),
          ((-1 : Polynomial ℤ) ^ j) * (Polynomial.C (sy.esymm j) * Polynomial.X ^ (n - j)) := by
    simpa [hcard_sy] using Multiset.prod_X_sub_X_eq_sum_esymm sy
  have hP : (sx.map fun z => Polynomial.X - Polynomial.C z).prod =
        (sy.map fun z => Polynomial.X - Polynomial.C z).prod := by
    rw [hP1, hP2]
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt : j < n + 1 := Finset.mem_range.mp hj
    have hj' : j ≤ n := by omega
    rw [hE j hj']
  have hsx_eq : sx = sy := multiset_eq_of_prod_eq_core sx sy (by simp [sx, sy]) hP
  obtain ⟨σ, hσ⟩ := exists_perm_of_multiset_map_eq yf xf hsx_eq.symm
  refine ⟨σ, ?_⟩
  intro i
  have hσi := congrFun hσ i
  dsimp [yf, xf] at hσi
  exact_mod_cast hσi.symm

end Commons.Combinatorics.Fin