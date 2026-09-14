import Mathlib
import Submission.Commons.Algebra.MvPolynomial.pderivIter_properties
import Submission.Commons.Algebra.MvPolynomial.pderivIter_add
import Submission.Commons.Algebra.MvPolynomial.coeff_pderivIter
import Submission.Commons.Algebra.Polynomial.exists_derivative_eval_ne_zero

set_option maxHeartbeats 1600000

namespace Commons.Algebra.MvPolynomial

open scoped BigOperators

/-! ## Auxiliary facts about `optionEquivRight` -/

section OptionAux
variable {S₁ : Type*} {R : Type*} [CommRing R]

/-- The image of a monomial under `optionEquivRight`: the variable `none` becomes the polynomial
variable and the variables `some i` become the multivariable variables. -/
lemma optionEquivRight_monomial (s : Option S₁ →₀ ℕ) (c : R) :
    MvPolynomial.optionEquivRight R S₁ (MvPolynomial.monomial s c) =
      MvPolynomial.monomial s.some (Polynomial.C c * Polynomial.X ^ (s none)) := by
  rw [MvPolynomial.optionEquivRight_apply, MvPolynomial.aeval_monomial]
  rw [Finsupp.prod_option_index
    (b := fun o k => (o.elim (MvPolynomial.C Polynomial.X) MvPolynomial.X) ^ k)]
  · rw [MvPolynomial.monomial_eq]
    simp only [Option.elim, map_pow, MvPolynomial.C_mul]
    rw [show (algebraMap R (MvPolynomial S₁ (Polynomial R))) c =
        MvPolynomial.C (Polynomial.C c) from rfl]
    ring
  · intro o; simp
  · intro o m1 m2; simp [pow_add]

/-- `Finsupp.optionElim` is the "insert a value at `none`" operation. -/
lemma optionElim_def (m : S₁ →₀ ℕ) (i : ℕ) :
    m.optionElim i = (m.embDomain Function.Embedding.some).update none i := by
  simp [Finsupp.optionElim, Finsupp.optionEquiv]

/-- The coefficient formula for `optionEquivRight`. -/
lemma optionEquivRight_coeff_coeff (m : S₁ →₀ ℕ) (g : MvPolynomial (Option S₁) R) (i : ℕ) :
    (MvPolynomial.coeff m (MvPolynomial.optionEquivRight R S₁ g)).coeff i =
      MvPolynomial.coeff (m.optionElim i) g := by
  classical
  induction g using MvPolynomial.induction_on' with
  | add p q hp hq =>
      simp only [map_add, MvPolynomial.coeff_add, Polynomial.coeff_add, hp, hq]
  | monomial s c =>
      have key : (s = m.optionElim i) ↔ (s.some = m ∧ s none = i) := by
        rw [optionElim_def, Finsupp.eq_option_embedding_update_none_iff]; exact and_comm
      rw [optionEquivRight_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
      by_cases h1 : s.some = m
      · rw [if_pos h1, Polynomial.coeff_C_mul_X_pow]
        by_cases h2 : i = s none
        · rw [if_pos h2, if_pos (key.mpr ⟨h1, h2.symm⟩)]
        · rw [if_neg h2, if_neg (fun h => h2 (key.mp h).2.symm)]
      · rw [if_neg h1, if_neg (fun h => h1 (key.mp h).1)]
        simp

/-- `optionEquivRight` does not increase the degree in the variable `some j`. -/
lemma degreeOf_optionEquivRight_le (j : S₁) (g : MvPolynomial (Option S₁) R) :
    (MvPolynomial.optionEquivRight R S₁ g).degreeOf j ≤ g.degreeOf (some j) := by
  rw [MvPolynomial.degreeOf_le_iff]
  intro m hm
  rw [MvPolynomial.mem_support_iff] at hm
  obtain ⟨i, hi⟩ :
      ((MvPolynomial.coeff m (MvPolynomial.optionEquivRight R S₁ g)).support).Nonempty := by
    rwa [Polynomial.support_nonempty]
  rw [Polynomial.mem_support_iff, optionEquivRight_coeff_coeff] at hi
  have hmem : m.optionElim i ∈ g.support := by rwa [MvPolynomial.mem_support_iff]
  rw [MvPolynomial.degreeOf_eq_sup]
  calc m j = (m.optionElim i) (some j) := (Finsupp.optionElim_apply_some i m j).symm
    _ ≤ g.support.sup (fun n => n (some j)) := Finset.le_sup (f := fun n => n (some j)) hmem

end OptionAux

/-! ## The decomposition isomorphism

We split off the variable `X 0`, writing a polynomial in `n+1` variables as a polynomial in
`n` variables whose coefficients are univariate polynomials in `X 0`. -/

section Decomp
variable {R : Type*} [CommRing R]

/-- Decompose `R[X₀, …, Xₙ]` as `(R[X₀])[X₁, …, Xₙ]`. -/
noncomputable def decompΦ (n : ℕ) :
    MvPolynomial (Fin (n+1)) R ≃ₐ[R] MvPolynomial (Fin n) (Polynomial R) :=
  (MvPolynomial.renameEquiv R (_root_.finSuccEquiv n)).trans
    (MvPolynomial.optionEquivRight R (Fin n))

@[simp] lemma decompΦ_X_zero (n : ℕ) :
    decompΦ (R := R) n (MvPolynomial.X 0) = MvPolynomial.C Polynomial.X := by
  simp [decompΦ]

@[simp] lemma decompΦ_X_succ (n : ℕ) (j : Fin n) :
    decompΦ (R := R) n (MvPolynomial.X (Fin.succ j)) = MvPolynomial.X j := by
  simp [decompΦ]

/-- The generator check for the commutation of `decompΦ` with partial derivatives. -/
lemma decompΦ_pderiv_gen (n : ℕ) (j : Fin n) (i : Fin (n+1)) :
    decompΦ (R := R) n (MvPolynomial.pderiv (Fin.succ j) (MvPolynomial.X i)) =
      MvPolynomial.pderiv j (decompΦ (R := R) n (MvPolynomial.X i)) := by
  induction i using Fin.cases with
  | zero => simp
  | succ l =>
      by_cases h : l = j
      · subst h; simp
      · simp [MvPolynomial.pderiv_X_of_ne, h]

/-- `decompΦ` commutes with the partial derivative along a "kept" variable. -/
lemma decompΦ_pderiv_succ (n : ℕ) (j : Fin n) (f : MvPolynomial (Fin (n+1)) R) :
    decompΦ (R := R) n (MvPolynomial.pderiv (Fin.succ j) f) =
      MvPolynomial.pderiv j (decompΦ (R := R) n f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [decompΦ]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
      rw [MvPolynomial.pderiv_mul, map_add, map_mul, map_mul, hp, map_mul,
        MvPolynomial.pderiv_mul]
      have hgen := decompΦ_pderiv_gen (R := R) n j i
      rw [hgen]

end Decomp

/-! ## Iterated derivatives and the multi-index decomposition -/

section Iter
variable {R : Type*} [CommSemiring R] {σ : Type*} [Fintype σ]

/-- A single multi-index derivative is an iterate of one partial derivative. -/
lemma pderivIter_single_eq (i : σ) (k : ℕ) (P : MvPolynomial σ R) :
    pderivIter (Finsupp.single i k) P = (MvPolynomial.pderiv i)^[k] P := by
  induction k with
  | zero =>
      rw [Finsupp.single_zero i]
      exact (pderivIter_properties (R := R) (σ := σ)).1 P
  | succ k ih =>
      have h : Finsupp.single i (k+1) = Finsupp.single i k + Finsupp.single i 1 := by
        rw [Finsupp.single_add]
      rw [h, pderivIter_add, ih]
      rw [show pderivIter (Finsupp.single i 1) ((MvPolynomial.pderiv i)^[k] P) =
          MvPolynomial.pderiv i ((MvPolynomial.pderiv i)^[k] P) from
        (pderivIter_properties (R := R) (σ := σ)).2.1 i _]
      rw [Function.iterate_succ_apply']

/-- `Finsupp.cons 0` commutes with adding a single index on the `Fin.succ` part. -/
lemma cons_zero_add_single {n : ℕ} (m' : Fin n →₀ ℕ) (j : Fin n) (b : ℕ) :
    Finsupp.cons 0 (Finsupp.single j b + m') =
      Finsupp.single (Fin.succ j) b + Finsupp.cons 0 m' := by
  ext x
  induction x using Fin.cases with
  | zero => simp [Finsupp.cons_zero]
  | succ l => simp [Finsupp.cons_succ, Finsupp.single_apply, Fin.succ_inj]

end Iter

section DecompIter
variable {R : Type*} [CommRing R]

/-- `decompΦ` commutes with iterated derivatives along a single "kept" variable. -/
lemma decompΦ_pderivIter_single (n : ℕ) (j : Fin n) (k : ℕ)
    (f : MvPolynomial (Fin (n+1)) R) :
    decompΦ (R := R) n (pderivIter (Finsupp.single (Fin.succ j) k) f) =
      pderivIter (Finsupp.single j k) (decompΦ (R := R) n f) := by
  rw [pderivIter_single_eq, pderivIter_single_eq]
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', decompΦ_pderiv_succ, ih]

/-- `decompΦ` intertwines `∂^{cons 0 m}` (derivatives only in the "kept" variables) with
`∂^m`. -/
lemma decompΦ_pderivIter (n : ℕ) (m : Fin n →₀ ℕ) (f : MvPolynomial (Fin (n+1)) R) :
    decompΦ (R := R) n (pderivIter (Finsupp.cons 0 m) f) =
      pderivIter m (decompΦ (R := R) n f) := by
  induction m using Finsupp.induction generalizing f with
  | zero =>
      have h0a : pderivIter (0 : Fin (n+1) →₀ ℕ) f = f :=
        (pderivIter_properties (R := R) (σ := Fin (n+1))).1 f
      have h0b : pderivIter (0 : Fin n →₀ ℕ) (decompΦ (R := R) n f) =
          decompΦ (R := R) n f :=
        (pderivIter_properties (R := Polynomial R) (σ := Fin n)).1 _
      rw [Finsupp.cons_zero_zero, h0a, h0b]
  | single_add j b m' hb hmem ih =>
      rw [cons_zero_add_single, pderivIter_add, ih, decompΦ_pderivIter_single,
        ← pderivIter_add]

/-- `decompΦ` does not increase the degree in a kept variable. -/
lemma degreeOf_decompΦ_le (n : ℕ) (j : Fin n) (f : MvPolynomial (Fin (n+1)) R) :
    (decompΦ (R := R) n f).degreeOf j ≤ f.degreeOf (Fin.succ j) := by
  rw [show decompΦ (R := R) n f = MvPolynomial.optionEquivRight R (Fin n)
      (MvPolynomial.rename (_root_.finSuccEquiv n) f) from rfl]
  calc (MvPolynomial.optionEquivRight R (Fin n)
          (MvPolynomial.rename (_root_.finSuccEquiv n) f)).degreeOf j
      ≤ (MvPolynomial.rename (_root_.finSuccEquiv n) f).degreeOf (Option.some j) :=
        degreeOf_optionEquivRight_le (S₁ := Fin n) (R := R) j
          (MvPolynomial.rename (_root_.finSuccEquiv n) f)
    _ = f.degreeOf (Fin.succ j) := by
        have h := MvPolynomial.degreeOf_rename_of_injective
          (p := f) (_root_.finSuccEquiv n).injective (i := Fin.succ j)
        rwa [show _root_.finSuccEquiv n (Fin.succ j) = Option.some j from
          _root_.finSuccEquiv_succ j] at h

end DecompIter

section SuccAux
variable {R : Type*} [CommRing R]

/-- `finSuccEquiv` intertwines `∂₀` with the formal derivative. -/
theorem finSuccEquiv_pderiv_zero {n : ℕ} (g : MvPolynomial (Fin (n+1)) R) :
    MvPolynomial.finSuccEquiv R n (MvPolynomial.pderiv 0 g) =
      Polynomial.derivative (MvPolynomial.finSuccEquiv R n g) := by
  induction g using MvPolynomial.induction_on with
  | C a =>
      rw [show MvPolynomial.finSuccEquiv R n (MvPolynomial.C a) =
          Polynomial.C (MvPolynomial.C a) from by
        simp [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C]]
      simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
      rw [MvPolynomial.pderiv_mul, map_add, map_mul, hp, map_mul, map_mul,
        Polynomial.derivative_mul]
      have hgen : MvPolynomial.finSuccEquiv R n
            (MvPolynomial.pderiv 0 (MvPolynomial.X i)) =
          Polynomial.derivative (MvPolynomial.finSuccEquiv R n (MvPolynomial.X i)) := by
        induction i using Fin.cases with
        | zero => simp [MvPolynomial.finSuccEquiv_X_zero]
        | succ l => simp [MvPolynomial.finSuccEquiv_X_succ]
      rw [hgen]

/-- Iterated form of `finSuccEquiv_pderiv_zero`. -/
theorem finSuccEquiv_pderiv_zero_iterate {n : ℕ} (k : ℕ) (g : MvPolynomial (Fin (n+1)) R) :
    MvPolynomial.finSuccEquiv R n ((MvPolynomial.pderiv 0)^[k] g) =
      (Polynomial.derivative^[k]) (MvPolynomial.finSuccEquiv R n g) := by
  induction k generalizing g with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        finSuccEquiv_pderiv_zero, ih]

/-- `Polynomial.map` of `finSuccEquiv` equals evaluation in the `decompΦ`-picture. -/
theorem map_finSuccEquiv_decompΦ (n : ℕ) (z' : Fin n → R)
    (g : MvPolynomial (Fin (n+1)) R) :
    Polynomial.map (MvPolynomial.eval z') (MvPolynomial.finSuccEquiv R n g) =
      MvPolynomial.eval (fun j : Fin n => Polynomial.C (z' j))
        (decompΦ (R := R) n g) := by
  induction g using MvPolynomial.induction_on with
  | C a =>
      rw [show MvPolynomial.finSuccEquiv R n (MvPolynomial.C a) =
          Polynomial.C (MvPolynomial.C a) from by
        simp [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C]]
      simp [decompΦ]
  | add p q hp hq => simp only [Polynomial.map_add, map_add, hp, hq]
  | mul_X p i hp =>
      rw [show MvPolynomial.finSuccEquiv R n (p * MvPolynomial.X i) =
            MvPolynomial.finSuccEquiv R n p * MvPolynomial.finSuccEquiv R n (MvPolynomial.X i)
            from map_mul _ _ _,
          show decompΦ (R := R) n (p * MvPolynomial.X i) =
            decompΦ (R := R) n p * decompΦ (R := R) n (MvPolynomial.X i) from map_mul _ _ _,
          Polynomial.map_mul, map_mul, hp]
      have hgen : Polynomial.map (MvPolynomial.eval z')
            (MvPolynomial.finSuccEquiv R n (MvPolynomial.X i)) =
          MvPolynomial.eval (fun j : Fin n => Polynomial.C (z' j))
            (decompΦ (R := R) n (MvPolynomial.X i)) := by
        induction i using Fin.cases with
        | zero => simp [decompΦ, MvPolynomial.finSuccEquiv_X_zero]
        | succ l => simp [decompΦ, MvPolynomial.finSuccEquiv_X_succ]
      rw [hgen]

end SuccAux

section DegreeIter
variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R]

/-- Iterated partial derivatives do not increase the degree in an untouched variable. -/
lemma degreeOf_pderivIter_le {σ : Type*} [Fintype σ] (j : σ) (m : σ →₀ ℕ)
    (P : MvPolynomial σ R) (hm : m j = 0) :
    (pderivIter m P).degreeOf j ≤ P.degreeOf j := by
  rw [MvPolynomial.degreeOf_le_iff]
  intro n hn
  rw [MvPolynomial.mem_support_iff, coeff_pderivIter] at hn
  have h1 : MvPolynomial.coeff (n + m) P ≠ 0 := by
    intro h
    rw [h, zero_mul] at hn
    exact hn rfl
  have h2 : n + m ∈ P.support := by rwa [MvPolynomial.mem_support_iff]
  have h3 : (n + m) j = n j := by rw [Finsupp.add_apply, hm, add_zero]
  rw [← h3]
  exact MvPolynomial.monomial_le_degreeOf j h2

end DegreeIter

/-! ## The induction -/

theorem main_aux : ∀ (N : ℕ), ∀ (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
    (e : Fin N → ℕ) (f : MvPolynomial (Fin N) R), f ≠ 0 →
    (∀ m ∈ f.support, ∀ j : Fin N, m j ≤ e j) →
    ∀ B : ℕ, 1 ≤ B →
    ∃ (z : Fin N → ℤ) (i : Fin N →₀ ℕ),
      (∀ j : Fin N, |z j| ≤ (B : ℤ)) ∧ (∀ j : Fin N, i j ≤ e j / B) ∧
      MvPolynomial.eval (fun j : Fin N => (z j : R)) (pderivIter i f) ≠ 0 := by
  intro N
  induction N with
  | zero =>
    intro R _ _ _ e f hf hdeg B hB
    refine ⟨fun j => j.elim0, 0, ?_, ?_, ?_⟩
    · intro j; exact j.elim0
    · intro j; exact j.elim0
    · rw [(pderivIter_properties).1]
      intro h
      have hf0 : f = MvPolynomial.C (MvPolynomial.coeff 0 f) := by
        conv_lhs => rw [MvPolynomial.eq_C_of_isEmpty f]
      have hc : MvPolynomial.coeff 0 f = 0 := by
        have h' := h
        rw [hf0] at h'
        simpa using h'
      exact hf (by rw [hf0, hc, map_zero])
  | succ n ih =>
    intro R _ _ _ e f hf hdeg B hB
    set F : MvPolynomial (Fin n) (Polynomial R) := decompΦ (R := R) n f with hFdef
    have hF : F ≠ 0 := by
      rw [hFdef]
      intro h
      exact hf ((decompΦ (R := R) n).injective (by rw [h, map_zero]))
    have hdegF : ∀ m ∈ F.support, ∀ j : Fin n, m j ≤ (fun j => e (Fin.succ j)) j := by
      intro m hm j
      have hm' : m ∈ (decompΦ (R := R) n f).support := by rwa [hFdef] at hm
      calc m j ≤ (decompΦ (R := R) n f).degreeOf j :=
            MvPolynomial.monomial_le_degreeOf j hm'
        _ ≤ f.degreeOf (Fin.succ j) := degreeOf_decompΦ_le n j f
        _ ≤ e (Fin.succ j) :=
            MvPolynomial.degreeOf_le_iff.mpr (fun m' hm' => hdeg m' hm' (Fin.succ j))
    obtain ⟨z', i', hz', hi', hne⟩ :=
      ih (Polynomial R) (fun j => e (Fin.succ j)) F hF hdegF B hB
    set h : Polynomial R := Polynomial.map (MvPolynomial.eval (fun j : Fin n => (z' j : R)))
      (MvPolynomial.finSuccEquiv R n (pderivIter (Finsupp.cons 0 i') f)) with hhdef
    have hh : h ≠ 0 := by
      rw [hhdef, map_finSuccEquiv_decompΦ, decompΦ_pderivIter, ← hFdef]
      exact hne
    have hdeg_h : h.natDegree ≤ e 0 := by
      rw [hhdef]
      calc (Polynomial.map (MvPolynomial.eval (fun j : Fin n => (z' j : R)))
              (MvPolynomial.finSuccEquiv R n (pderivIter (Finsupp.cons 0 i') f))).natDegree
          ≤ (MvPolynomial.finSuccEquiv R n (pderivIter (Finsupp.cons 0 i') f)).natDegree :=
            Polynomial.natDegree_map_le
        _ = (pderivIter (Finsupp.cons 0 i') f).degreeOf 0 :=
            MvPolynomial.natDegree_finSuccEquiv _
        _ ≤ f.degreeOf 0 :=
            degreeOf_pderivIter_le 0 (Finsupp.cons 0 i') f (Finsupp.cons_zero 0 i')
        _ ≤ e 0 :=
            MvPolynomial.degreeOf_le_iff.mpr (fun m hm => hdeg m hm 0)
    obtain ⟨z₀, k, hz₀, hk, hne₂⟩ :=
      Commons.Algebra.Polynomial.exists_derivative_eval_ne_zero h hh (e 0) B hdeg_h hB
    refine ⟨Fin.cons z₀ z', Finsupp.cons k i', ?_, ?_, ?_⟩
    · intro j
      induction j using Fin.cases with
      | zero => simpa using hz₀
      | succ l => simpa using hz' l
    · intro j
      induction j using Fin.cases with
      | zero => simpa using hk
      | succ l => simpa using hi' l
    · have hz_fun : (fun j : Fin (n+1) => (((Fin.cons z₀ z' : Fin (n+1) → ℤ)) j : R)) =
          Fin.cons (z₀ : R) (fun j : Fin n => (z' j : R)) := by
        funext j
        induction j using Fin.cases with
        | zero => simp
        | succ l => simp
      have hi : Finsupp.cons k i' = Finsupp.cons 0 i' + Finsupp.single 0 k := by
        ext x
        induction x using Fin.cases with
        | zero => simp [Finsupp.cons_zero]
        | succ l => simp [Finsupp.cons_succ]
      have key : MvPolynomial.eval
            (fun j : Fin (n+1) => (((Fin.cons z₀ z' : Fin (n+1) → ℤ)) j : R))
            (pderivIter (Finsupp.cons k i') f) =
          (Polynomial.derivative^[k] h).eval (z₀ : R) := by
        rw [hi, pderivIter_add, pderivIter_single_eq, hz_fun]
        rw [MvPolynomial.eval_eq_eval_mv_eval', finSuccEquiv_pderiv_zero_iterate]
        rw [hhdef, ← Polynomial.iterate_derivative_map]
      rw [key]
      exact hne₂

/-! ## The non-vanishing lemma -/

/-- **Non-vanishing lemma** (survey on the subspace theorem, §"Nonvanishing results").

Let `K` be a field of characteristic zero, `f ∈ K[x_0, …, x_{N-1}]` a nonzero polynomial whose
degree in each variable is at most `e j`, and let `B ≥ 1`.  Then there are integers `z j` with
`|z j| ≤ B` and a multi-index `i` with `i j ≤ e j / B` for all `j`, such that the iterated
partial derivative `∂^i f` does not vanish at `z`.

Proof sketch: induction on `N`.  In one variable, if `∂^k f (b) = 0` for all `|b| ≤ B` and all
`k ≤ e / B`, then `f` is divisible by `∏_{|b| ≤ B} (X - b) ^ (e / B + 1)`, whose degree is
`(2B+1) (e/B + 1) > e`. -/
theorem exists_pderivIter_eval_ne_zero {K : Type*} [Field K] [CharZero K] {N : ℕ}
    (e : Fin N → ℕ) (f : MvPolynomial (Fin N) K) (hf : f ≠ 0)
    (hdeg : ∀ m ∈ f.support, ∀ j : Fin N, m j ≤ e j) (B : ℕ) (hB : 1 ≤ B) :
    ∃ (z : Fin N → ℤ) (i : Fin N →₀ ℕ),
      (∀ j : Fin N, |z j| ≤ (B : ℤ)) ∧ (∀ j : Fin N, i j ≤ e j / B) ∧
      MvPolynomial.eval (fun j : Fin N => (z j : K)) (pderivIter i f) ≠ 0 :=
  main_aux N K e f hf hdeg B hB

end Commons.Algebra.MvPolynomial
