import Mathlib.Algebra.MvPolynomial.Eval

namespace Commons.Algebra.MvPolynomial

noncomputable section

open Finsupp

/-- The `R`-submodule spanned by monomials whose block-degrees are bounded by `e`. -/
private def blockSpan {R : Type*} [CommSemiring R] (m N' : ℕ) (e : Fin m → ℕ) :
    Submodule R (MvPolynomial (Fin m × Fin N') R) :=
  Submodule.span R {q | ∃ v : Fin m × Fin N' →₀ ℕ,
    (∀ h : Fin m, ∑ j : Fin N', v (h, j) ≤ e h) ∧ q = MvPolynomial.monomial v 1}

/-- The `R`-submodule of polynomials all of whose monomials have block-degree bounded by `e`. -/
private def bddSpan {R : Type*} [CommSemiring R] (m N' : ℕ) (e : Fin m → ℕ) :
    Submodule R (MvPolynomial (Fin m × Fin N') R) where
  carrier := {q | ∀ v ∈ q.support, ∀ h : Fin m, ∑ j : Fin N', v (h, j) ≤ e h}
  zero_mem' := by intro v hv; simp at hv
  add_mem' := by
    intro x y hx hy v hv h
    have hv' : v ∈ x.support ∪ y.support := MvPolynomial.support_add (p := x) (q := y) hv
    rw [Finset.mem_union] at hv'
    rcases hv' with hv' | hv'
    · exact hx v hv' h
    · exact hy v hv' h
  smul_mem' := by
    intro a x hx v hv h
    exact hx v (MvPolynomial.support_smul (a := a) hv) h

private lemma blockSpan_le_bddSpan {R : Type*} [CommSemiring R] {m N' : ℕ} (e : Fin m → ℕ) :
    blockSpan (R:=R) m N' e ≤ bddSpan (R:=R) m N' e := by
  simp only [blockSpan]
  apply Submodule.span_le.mpr
  rintro q ⟨v, hv, rfl⟩
  intro w hw h'
  have hsub := MvPolynomial.support_monomial_subset (s := v) (a := (1:R)) hw
  rw [Finset.mem_singleton] at hsub
  rw [hsub]
  exact hv h'

private lemma blockSpan_mono {R : Type*} [CommSemiring R] {m N' : ℕ} {e e' : Fin m → ℕ}
    (h : ∀ i, e i ≤ e' i) : blockSpan (R:=R) m N' e ≤ blockSpan (R:=R) m N' e' := by
  simp only [blockSpan]
  apply Submodule.span_le.mpr
  rintro q ⟨v, hv, rfl⟩
  exact Submodule.subset_span ⟨v, fun i => le_trans (hv i) (h i), rfl⟩

private lemma blockSpan_mul_le {R : Type*} [CommSemiring R] {m N' : ℕ} (e e' : Fin m → ℕ) :
    blockSpan (R:=R) m N' e * blockSpan (R:=R) m N' e' ≤ blockSpan (R:=R) m N' (e + e') := by
  simp only [blockSpan]
  rw [Submodule.span_mul_span]
  apply Submodule.span_le.mpr
  rintro q ⟨x, ⟨v, hv, rfl⟩, y, ⟨v', hv', rfl⟩, rfl⟩
  simp only []
  rw [MvPolynomial.monomial_mul]
  simp only [mul_one]
  refine Submodule.subset_span ⟨v + v', fun h => ?_, rfl⟩
  have hsum : (∑ j : Fin N', (v + v') (h, j))
      = (∑ j : Fin N', v (h, j)) + ∑ j : Fin N', v' (h, j) := by
    simp [Finsupp.add_apply, Finset.sum_add_distrib]
  rw [hsum, Pi.add_apply]
  exact add_le_add (hv h) (hv' h)

private lemma blockSpan_mul_mem {R : Type*} [CommSemiring R] {m N' : ℕ} {e e' : Fin m → ℕ}
    {p q : MvPolynomial (Fin m × Fin N') R}
    (hp : p ∈ blockSpan (R:=R) m N' e) (hq : q ∈ blockSpan (R:=R) m N' e') :
    p * q ∈ blockSpan (R:=R) m N' (e + e') :=
  blockSpan_mul_le e e' (Submodule.mul_mem_mul hp hq)

private lemma blockSpan_pow_mem {R : Type*} [CommSemiring R] {m N' : ℕ} {e : Fin m → ℕ}
    {p : MvPolynomial (Fin m × Fin N') R} (hp : p ∈ blockSpan (R:=R) m N' e) (n : ℕ) :
    p ^ n ∈ blockSpan (R:=R) m N' (n • e) := by
  induction n with
  | zero =>
      have h1 : (1 : MvPolynomial (Fin m × Fin N') R)
          = MvPolynomial.monomial (0 : Fin m × Fin N' →₀ ℕ) 1 := by
        rw [MvPolynomial.monomial_zero', MvPolynomial.C_1]
      rw [pow_zero, h1]
      refine Submodule.subset_span ⟨0, fun h => ?_, rfl⟩
      simp
  | succ n ih =>
      rw [pow_succ, succ_nsmul]
      exact blockSpan_mul_le (n • e) e (Submodule.mul_mem_mul ih hp)

/-- Summing `v` over the indices whose first coordinate equals `h`. -/
private lemma sum_fiber_eq {m N : ℕ} (v : Fin m × Fin N →₀ ℕ) (h : Fin m) :
    (∑ x ∈ v.support, (if x.1 = h then v x else 0)) = ∑ j : Fin N, v (h, j) := by
  classical
  have h1 : (∑ x ∈ v.support, (if x.1 = h then v x else 0))
      = ∑ x : Fin m × Fin N, (if x.1 = h then v x else 0) := by
    apply Finset.sum_subset (Finset.subset_univ v.support)
    intro x _ hx
    rw [Finsupp.notMem_support_iff] at hx
    simp [hx]
  rw [h1, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single h]
  · apply Finset.sum_congr rfl
    intro j _
    simp
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro j _
    simp [hb]
  · intro hh; exact absurd (Finset.mem_univ h) hh

/-- The value of `Finsupp.mapDomain Prod.fst` at `h` is the sum over the `j`-fiber. -/
private lemma mapDomain_prodFst_apply {m N' : ℕ} (v : Fin m × Fin N' →₀ ℕ) (h : Fin m) :
    Finsupp.mapDomain Prod.fst v h = ∑ j : Fin N', v (h, j) := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  simp only [Finsupp.single_apply, Finsupp.sum]
  exact sum_fiber_eq v h

private lemma blockSpan_prod_mem {R : Type*} [CommSemiring R] {m N' : ℕ} {ι : Type*}
    [DecidableEq ι]
    (t : Finset ι) (g : ι → MvPolynomial (Fin m × Fin N') R) (e : ι → Fin m → ℕ)
    (hg : ∀ x ∈ t, g x ∈ blockSpan (R:=R) m N' (e x)) :
    (∏ x ∈ t, g x) ∈ blockSpan (R:=R) m N' (fun h => ∑ x ∈ t, e x h) := by
  classical
  induction t using Finset.induction with
  | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty]
      have h1 : (1 : MvPolynomial (Fin m × Fin N') R)
          = MvPolynomial.monomial (0 : Fin m × Fin N' →₀ ℕ) 1 := by
        rw [MvPolynomial.monomial_zero', MvPolynomial.C_1]
      rw [h1]
      refine Submodule.subset_span ⟨0, fun h => ?_, rfl⟩
      simp
  | insert a t ha ih =>
      rw [Finset.prod_insert ha]
      have hga : g a ∈ blockSpan (R:=R) m N' (e a) := hg a (Finset.mem_insert_self a t)
      have hgt : (∏ x ∈ t, g x) ∈ blockSpan (R:=R) m N' (fun h => ∑ x ∈ t, e x h) :=
        ih (fun x hx => hg x (Finset.mem_insert_of_mem hx))
      have hmem := blockSpan_mul_le (e a) (fun h => ∑ x ∈ t, e x h)
        (Submodule.mul_mem_mul hga hgt)
      have heq : (e a + fun h => ∑ x ∈ t, e x h) = (fun h => ∑ x ∈ insert a t, e x h) := by
        ext h
        simp only [Pi.add_apply, Finset.sum_insert ha]
      rwa [heq] at hmem

/-- The block weight of a variable index `x`: `1` at block `x.1`, `0` elsewhere. -/
private def wdeg {m N : ℕ} (x : Fin m × Fin N) : Fin m → ℕ :=
  fun h => if x.1 = h then 1 else 0

private lemma f_mem_blockSpan {R : Type*} [CommSemiring R] {m N N' : ℕ}
    (A : Fin m × Fin N → Fin m × Fin N' → R)
    (hA : ∀ (h : Fin m) (j : Fin N) (h' : Fin m) (j' : Fin N'),
      A (h, j) (h', j') ≠ 0 → h' = h)
    (x : Fin m × Fin N) :
    (∑ y : Fin m × Fin N', MvPolynomial.C (A x y) * MvPolynomial.X y)
      ∈ blockSpan (R:=R) m N' (wdeg (N:=N) x) := by
  classical
  apply Submodule.sum_mem
  intro y _
  rw [MvPolynomial.C_mul_X_eq_monomial]
  by_cases hAy : A x y = 0
  · rw [hAy, MvPolynomial.monomial_zero]
    exact Submodule.zero_mem _
  · have hy : y.1 = x.1 := by
      have h' := hA x.1 x.2 y.1 y.2
      exact h' hAy
    have hgen : MvPolynomial.monomial (Finsupp.single y 1) 1
        ∈ blockSpan (R:=R) m N' (wdeg (N:=N) x) := by
      have hgen0 : MvPolynomial.monomial (Finsupp.single y 1) 1
          ∈ blockSpan (R:=R) m N' (wdeg (N:=N') y) := by
        refine Submodule.subset_span ⟨Finsupp.single y 1, fun h => ?_, rfl⟩
        rw [← mapDomain_prodFst_apply (Finsupp.single y 1) h,
          Finsupp.mapDomain_single, Finsupp.single_apply, wdeg]
      have hw : (wdeg (N:=N') y) = (wdeg (N:=N) x) := by
        ext h; simp only [wdeg]; rw [hy]
      rwa [hw] at hgen0
    have hsmul : A x y • MvPolynomial.monomial (Finsupp.single y 1) 1
        = MvPolynomial.monomial (Finsupp.single y 1) (A x y) := by
      rw [MvPolynomial.smul_eq_C_mul, ← MvPolynomial.monomial_zero', MvPolynomial.monomial_mul]
      simp
    rw [← hsmul]
    exact Submodule.smul_mem _ _ hgen

theorem blockDiag_aeval_degree_le {R : Type*} [CommSemiring R] {m N N' : ℕ}
    (P : MvPolynomial (Fin m × Fin N) R) (d : Fin m → ℕ)
    (hP : ∀ u ∈ P.support, ∀ h : Fin m, ∑ j : Fin N, u (h, j) ≤ d h)
    (A : Fin m × Fin N → Fin m × Fin N' → R)
    (hA : ∀ (h : Fin m) (j : Fin N) (h' : Fin m) (j' : Fin N'), A (h, j) (h', j') ≠ 0 → h' = h)
    (u' : Fin m × Fin N' →₀ ℕ)
    (hu' : u' ∈ (MvPolynomial.aeval (fun x : Fin m × Fin N =>
      ∑ y : Fin m × Fin N', MvPolynomial.C (A x y) * MvPolynomial.X y) P).support)
    (h : Fin m) :
    ∑ j : Fin N', u' (h, j) ≤ d h := by
  classical
  set f : Fin m × Fin N → MvPolynomial (Fin m × Fin N') R :=
    fun x => ∑ y : Fin m × Fin N', MvPolynomial.C (A x y) * MvPolynomial.X y with hf
  have hmem : MvPolynomial.aeval f P ∈ blockSpan (R:=R) m N' d := by
    rw [MvPolynomial.as_sum P, MvPolynomial.aeval_sum]
    apply Submodule.sum_mem
    intro u hu
    rw [MvPolynomial.aeval_monomial]
    rw [Finsupp.prod]
    have hprod : (∏ x ∈ u.support, (f x) ^ (u x))
        ∈ blockSpan (R:=R) m N' (fun h => ∑ x ∈ u.support, u x * wdeg (N:=N) x h) := by
      apply blockSpan_prod_mem
      intro x _
      have hxmem : f x ∈ blockSpan (R:=R) m N' (wdeg (N:=N) x) := f_mem_blockSpan A hA x
      have hpw := blockSpan_pow_mem hxmem (u x)
      have heq : (u x • wdeg (N:=N) x) = (fun h => u x * wdeg (N:=N) x h) := by
        ext h; simp [Pi.smul_apply]
      rwa [heq] at hpw
    have hmono : blockSpan (R:=R) m N' (fun h => ∑ x ∈ u.support, u x * wdeg (N:=N) x h)
        ≤ blockSpan (R:=R) m N' d := by
      apply blockSpan_mono
      intro h
      have hsum : (∑ x ∈ u.support, u x * wdeg (N:=N) x h)
          = ∑ x ∈ u.support, (if x.1 = h then u x else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x.1 = h
        · simp [wdeg, hx]
        · simp [wdeg, hx]
      rw [hsum, sum_fiber_eq u h]
      exact hP u hu h
    have hterm : algebraMap R (MvPolynomial (Fin m × Fin N') R) (P.coeff u)
        * (∏ x ∈ u.support, (f x) ^ (u x)) ∈ blockSpan (R:=R) m N' d := by
      rw [← Algebra.smul_def]
      exact hmono (Submodule.smul_mem _ _ hprod)
    exact hterm
  have hbdd : MvPolynomial.aeval f P ∈ bddSpan (R:=R) m N' d :=
    blockSpan_le_bddSpan d hmem
  exact hbdd u' hu' h

end

end Commons.Algebra.MvPolynomial