import Mathlib
import Submission.Commons.NumberTheory.Padics.hensel_lift_coprime_factorization

open Polynomial
open scoped BigOperators

set_option autoImplicit false

namespace Commons.NumberTheory.Padics

section Family

variable {p : ℕ} [Fact p.Prime]

/-- A monic polynomial over `ℤ_[p]` whose reduction modulo `p` is the constant
`1` must itself be the constant polynomial `1`. -/
private lemma monic_eq_one_of_map_eq_one (g : (PadicInt p)[X]) (hg : g.Monic)
    (h : g.map (PadicInt.toZMod : PadicInt p →+* ZMod p) = 1) : g = 1 := by
  have hnd : g.natDegree = 0 := by
    have hm := hg.natDegree_map (PadicInt.toZMod : PadicInt p →+* ZMod p)
    rw [h, natDegree_one] at hm
    exact hm.symm
  rw [eq_C_of_natDegree_eq_zero hnd]
  have hc : g.coeff 0 = 1 := by
    simpa [hnd] using hg.coeff_natDegree
  rw [hc]
  simp

/-- The statement of `hensel_lift_family`, generalised so that the finite set of
factors has arbitrary cardinality `n` and the polynomial being factored is
arbitrary; proved by induction on `n`. -/
private theorem hensel_lift_family_aux {ι : Type*} [DecidableEq ι] (q : ι → (ZMod p)[X]) :
    ∀ (n : ℕ) (s : Finset ι), s.card = n →
    ∀ (f : (PadicInt p)[X]), f.Monic →
      (∀ i ∈ s, (q i).Monic) →
      (f.map (PadicInt.toZMod : PadicInt p →+* ZMod p) = ∏ i ∈ s, q i) →
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (q i) (q j)) →
      ∃ F : ι → (PadicInt p)[X],
        (∀ i ∈ s, (F i).Monic) ∧
        (∀ i ∈ s, (F i).natDegree = (q i).natDegree) ∧
        f = ∏ i ∈ s, F i ∧
        (∀ i ∈ s, (F i).map (PadicInt.toZMod : PadicInt p →+* ZMod p) = q i) := by
  intro n
  induction n with
  | zero =>
      intro s hs f hf hmon hfac hcop
      have hEmpty : s = ∅ := Finset.card_eq_zero.mp hs
      subst s
      have hf1 : f = 1 := monic_eq_one_of_map_eq_one f hf (by simp [hfac])
      refine ⟨fun _ : ι => 1, ?_, ?_, ?_, ?_⟩
      · intro i hi
        simp at hi
      · intro i hi
        simp at hi
      · simpa [hf1]
      · intro i hi
        simp at hi
  | succ n ih =>
      intro s hs f hf hmon hfac hcop
      have hnonempty : s.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨a, ha⟩ := hnonempty
      let t : Finset ι := s.erase a
      have ht_card : t.card = n := by
        dsimp [t]
        have hc := Finset.card_erase_of_mem ha
        omega
      have han : a ∉ t := by
        dsimp [t]
        exact Finset.notMem_erase a s
      have hins : insert a t = s := by
        dsimp [t]
        exact Finset.insert_erase ha
      let b : (ZMod p)[X] := ∏ i ∈ t, q i
      have hbmon : b.Monic := by
        dsimp [b]
        exact monic_prod_of_monic t q (by
          intro i hi
          exact hmon i (Finset.mem_erase.mp hi).2)
      have hcopab : IsCoprime (q a) b := by
        dsimp [b]
        apply IsCoprime.prod_right
        intro i hi
        exact hcop a ha i (Finset.mem_erase.mp hi).2 (Finset.mem_erase.mp hi).1.symm
      have hfac_decomp :
          f.map (PadicInt.toZMod : PadicInt p →+* ZMod p) = (q a) * b := by
        rw [hfac]
        dsimp [b, t]
        exact (Finset.mul_prod_erase s q ha).symm
      obtain ⟨A, B, hAmon, hBmon, hAdeg, hBdeg, hAB, hAred, hBred⟩ :=
        hensel_lift_coprime_factorization (p := p) (f := f) hf (a := q a)
          (hmon a ha) (b := b) hbmon hfac_decomp hcopab
      have hmon_t : ∀ i ∈ t, (q i).Monic := by
        intro i hi
        exact hmon i (Finset.mem_erase.mp hi).2
      have hcop_t : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → IsCoprime (q i) (q j) := by
        intro i hi j hj hij
        exact hcop i (Finset.mem_erase.mp hi).2 j (Finset.mem_erase.mp hj).2 hij
      obtain ⟨G, hGmon, hGdeg, hGprod, hGred⟩ := ih t ht_card B hBmon hmon_t hBred hcop_t
      let F : ι → (PadicInt p)[X] := fun i => if i = a then A else G i
      have hFa : F a = A := by
        simp [F]
      have hF_eq_G {i : ι} (hi : i ∈ t) : F i = G i := by
        have hia : i ≠ a := (Finset.mem_erase.mp hi).1
        simp [F, hia]
      have hFmon : ∀ i ∈ s, (F i).Monic := by
        intro i hi
        by_cases hia : i = a
        · subst i
          rw [hFa]
          exact hAmon
        · have hit : i ∈ t := Finset.mem_erase.mpr ⟨hia, hi⟩
          rw [hF_eq_G hit]
          exact hGmon i hit
      have hFdeg : ∀ i ∈ s, (F i).natDegree = (q i).natDegree := by
        intro i hi
        by_cases hia : i = a
        · subst i
          rw [hFa]
          exact hAdeg
        · have hit : i ∈ t := Finset.mem_erase.mpr ⟨hia, hi⟩
          rw [hF_eq_G hit]
          exact hGdeg i hit
      have hFred : ∀ i ∈ s, (F i).map (PadicInt.toZMod : PadicInt p →+* ZMod p) = q i := by
        intro i hi
        by_cases hia : i = a
        · subst i
          rw [hFa]
          exact hAred
        · have hit : i ∈ t := Finset.mem_erase.mpr ⟨hia, hi⟩
          rw [hF_eq_G hit]
          exact hGred i hit
      have hFprod : ∏ i ∈ s, F i = f := by
        calc
          ∏ i ∈ s, F i = ∏ i ∈ insert a t, F i := by rw [← hins]
          _ = F a * ∏ i ∈ t, F i := Finset.prod_insert han
          _ = A * ∏ i ∈ t, F i := by rw [hFa]
          _ = A * ∏ i ∈ t, G i := by
            congr 1
            apply Finset.prod_congr rfl
            intro i hi
            exact hF_eq_G hi
          _ = A * B := by rw [hGprod]
          _ = f := hAB.symm
      refine ⟨F, hFmon, hFdeg, hFprod.symm, hFred⟩

end Family

/-- Hensel lifting over an arbitrary finite family of pairwise coprime monic
factors.

If the monic polynomial `f : ℤ_[p][X]` reduces modulo `p` to the product
`∏ i ∈ s, q i` of monic pairwise-coprime polynomials over `𝔽_p = ZMod p`,
then each factor lifts: there are monic polynomials `F i : ℤ_[p][X]`
(`i ∈ s`) with the same degree as `q i`, whose reductions modulo `p` are
exactly `q i`, and with `f = ∏ i ∈ s, F i`.

Proved by iterating `Commons.NumberTheory.Padics.hensel_lift_coprime_factorization`
(the binary Hensel lift) over the finite set `s`; at each step one factor is
peeled off (its coprimality with the product of the remaining factors follows
from the pairwise coprimality via `IsCoprime.prod_right`), and the rest is
handled by induction. -/
theorem hensel_lift_family {p : ℕ} [Fact p.Prime] {ι : Type*} [DecidableEq ι]
    (f : (PadicInt p)[X]) (hf : f.Monic) (q : ι → (ZMod p)[X]) (s : Finset ι)
    (hqmon : ∀ i ∈ s, (q i).Monic)
    (hfac : f.map (PadicInt.toZMod : PadicInt p →+* ZMod p) = ∏ i ∈ s, q i)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (q i) (q j)) :
    ∃ F : ι → (PadicInt p)[X],
      (∀ i ∈ s, (F i).Monic) ∧ (∀ i ∈ s, (F i).natDegree = (q i).natDegree) ∧
        f = ∏ i ∈ s, F i ∧
        (∀ i ∈ s, (F i).map (PadicInt.toZMod : PadicInt p →+* ZMod p) = q i) := by
  classical
  exact hensel_lift_family_aux (p := p) (q := q) s.card s rfl f hf hqmon hfac hcop

end Commons.NumberTheory.Padics
