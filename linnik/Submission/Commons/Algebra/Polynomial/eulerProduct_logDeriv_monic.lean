import Mathlib
import Submission.Commons.FieldTheory.Polynomial.monic_index_ge_card_le
import Submission.Commons.FieldTheory.Polynomial.squarefree_monic_card
import Submission.Commons.Algebra.Polynomial.sum_natDegree_mul_count_normalizedFactors
import Submission.Commons.NumberTheory.Nat.sum_range_divisors_reindex
import Submission.Commons.Algebra.Polynomial.pow_dvd_iff_le_count_normalizedFactors

set_option maxHeartbeats 1000000

open Classical
open Polynomial Finset
open scoped BigOperators

namespace Commons.Algebra.Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Monic polynomials of degree `n` over `F`. -/
abbrev MonicDegF (F : Type*) [Field F] (n : ℕ) : Type _ := SqfreeMonicCardInternal.MonicDeg F n

/-- Monic irreducible polynomials of degree `d` over `F`. -/
abbrev MonicIrredDeg (F : Type*) [Field F] (d : ℕ) : Type _ :=
  {p : Polynomial F // p.Monic ∧ Irreducible p ∧ p.natDegree = d}

noncomputable instance instFintypeMonicIrredDeg (d : ℕ) : Fintype (MonicIrredDeg F d) :=
  Fintype.ofInjective (fun p : MonicIrredDeg F d => (⟨p.1, p.2.1, p.2.2.2⟩ : MonicDegF F d))
    (fun a b h => by
      have h2 : (a : Polynomial F) = (b : Polynomial F) := by
        have := congrArg (fun x : MonicDegF F d => (x : Polynomial F)) h
        simpa using this
      exact Subtype.ext h2)

noncomputable def monicIrrEquiv (d : ℕ) :
    MonicIrredDeg F d ≃ {p : MonicDegF F d // Irreducible (p : Polynomial F)} where
  toFun p := ⟨⟨p.1, p.2.1, p.2.2.2⟩, p.2.2.1⟩
  invFun p := ⟨p.1.1, p.1.2.1, p.2, p.1.2.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- Sums of `if q a then f a else 0` over a fintype are sums over the subtype of elements
satisfying `q`. -/
lemma sum_ite_subtype {α : Type*} {M : Type*} [Fintype α] [AddCommMonoid M]
    (q : α → Prop) [DecidablePred q] (f : α → M) :
    (∑ a : α, (if q a then f a else 0)) = ∑ a : {a // q a}, f a.1 := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype (p := q) ((Finset.univ : Finset α).filter q)
    (fun x => by simp) (fun a => f a)

/-- A multiset element has nonzero multiplicity exactly when it belongs to the multiset. -/
lemma multiset_count_ne_zero_iff {α : Type*} [DecidableEq α] {s : Multiset α} {a : α} :
    s.count a ≠ 0 ↔ a ∈ s := by
  rw [← Multiset.count_pos, Nat.pos_iff_ne_zero]

/-- Sums over `Fin m → F` may be reindexed as sums over all monic polynomials of degree `m`,
via `c ↦ X^m + ∑ i, C (c i) X^i`. -/
lemma sum_repPoly (m : ℕ) {M : Type*} [AddCommMonoid M] (g : Polynomial F → M) :
    (∑ c : Fin m → F, g (Commons.FieldTheory.Polynomial.repPoly m c)) =
      ∑ p : MonicDegF F m, g p := by
  rw [Fintype.sum_equiv (SqfreeMonicCardInternal.monicDegEquivFin F m).symm
      (fun c : Fin m → F => g (Commons.FieldTheory.Polynomial.repPoly m c))
      (fun p : MonicDegF F m => g p)]
  intro c
  rfl

/-- The same reindexing restricted to irreducible polynomials. -/
lemma sum_repPoly_irred (d : ℕ) {M : Type*} [AddCommMonoid M] (g : Polynomial F → M) :
    (∑ c : Fin d → F,
        (if Irreducible (Commons.FieldTheory.Polynomial.repPoly d c)
          then g (Commons.FieldTheory.Polynomial.repPoly d c) else 0)) =
      ∑ P : MonicIrredDeg F d, g P := by
  rw [sum_repPoly (F := F) d (fun p : Polynomial F => if Irreducible p then g p else 0)]
  rw [sum_ite_subtype (fun p : MonicDegF F d => Irreducible (p : Polynomial F))
      (fun p : MonicDegF F d => g p)]
  exact Fintype.sum_equiv (monicIrrEquiv (F := F) d).symm
    (fun p : {p : MonicDegF F d // Irreducible (p : Polynomial F)} => g p.1)
    (fun P : MonicIrredDeg F d => g P) (fun p => rfl)


/-- Power rule for `Ψ` on powers of monic polynomials. -/
lemma psi_pow (Ψ : Polynomial F → ℂ) (h1 : Ψ 1 = 1)
    (hmul : ∀ A B : Polynomial F, A.Monic → B.Monic → Ψ (A * B) = Ψ A * Ψ B)
    (P : Polynomial F) (hP : P.Monic) (e : ℕ) : Ψ (P ^ e) = Ψ P ^ e := by
  induction e with
  | zero => simpa using h1
  | succ n ih =>
      calc Ψ (P ^ (n + 1)) = Ψ (P ^ n * P) := by rw [pow_succ]
        _ = Ψ (P ^ n) * Ψ P := hmul _ _ (hP.pow n) hP
        _ = Ψ P ^ n * Ψ P := by rw [ih]
        _ = Ψ P ^ (n + 1) := by rw [pow_succ]

/-- The Dirichlet coefficient `c_m = ∑_{deg A = m} Ψ A`. -/
noncomputable def Cm (Ψ : Polynomial F → ℂ) (m : ℕ) : ℂ := ∑ p : MonicDegF F m, Ψ p

/-- The log-derivative coefficient `S_j`. -/
noncomputable def Sm (Ψ : Polynomial F → ℂ) (j : ℕ) : ℂ :=
  ∑ d ∈ j.divisors, (d : ℂ) * ∑ P : MonicIrredDeg F d, Ψ P ^ (j / d)

/-- Step 1: expand the product of the two Dirichlet coefficients. -/
lemma step1 (Ψ : Polynomial F → ℂ) (N : ℕ) :
    (∑ m ∈ Finset.range N, Cm Ψ m * Sm Ψ (N - m)) =
      ∑ m ∈ Finset.range N, ∑ A : MonicDegF F m, ∑ d ∈ (N - m).divisors,
        ∑ P : MonicIrredDeg F d, (d : ℂ) * (Ψ A * Ψ P ^ ((N - m) / d)) := by
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Cm, Sm, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  ring

/-- Multiplication by `P ^ e` for a monic `P` gives a bijection from monic polynomials of
degree `N - e * deg P` onto monic polynomials of degree `N` divisible by `P ^ e`. -/
noncomputable def mulPowEquiv (P : Polynomial F) (hP : P.Monic) (e N : ℕ)
    (he : P.natDegree * e ≤ N) :
    MonicDegF F (N - P.natDegree * e) ≃
      {Q : MonicDegF F N // P ^ e ∣ (Q : Polynomial F)} where
  toFun A := ⟨⟨A.1 * P ^ e, A.2.1.mul (hP.pow e), by
      rw [Monic.natDegree_mul A.2.1 (hP.pow e), A.2.2, Monic.natDegree_pow hP e,
        Nat.mul_comm e P.natDegree, Nat.sub_add_cancel he]⟩, dvd_mul_left _ _⟩
  invFun Q := ⟨Q.1.1 / P ^ e, by
      have hd : P ^ e * ((Q.1 : Polynomial F) / P ^ e) = (Q.1 : Polynomial F) :=
        EuclideanDomain.mul_div_cancel' (hP.pow e).ne_zero Q.2
      have hmon : ((Q.1 : Polynomial F) / P ^ e).Monic :=
        Monic.of_mul_monic_left (hP.pow e) (by rw [hd]; exact Q.1.2.1)
      refine ⟨hmon, ?_⟩
      have hne : (Q.1 : Polynomial F) / P ^ e ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hd
        exact Q.1.2.1.ne_zero hd.symm
      have hnat := Monic.natDegree_mul (hP.pow e) hmon
      rw [hd] at hnat
      rw [Monic.natDegree_pow hP e, Q.1.2.2, Nat.mul_comm e P.natDegree] at hnat
      omega⟩
  left_inv A := by
    refine Subtype.ext ?_
    exact mul_left_cancel₀ (pow_ne_zero e hP.ne_zero)
      (by rw [EuclideanDomain.mul_div_cancel' (pow_ne_zero e hP.ne_zero) (dvd_mul_left _ _),
        mul_comm])
  right_inv Q := by
    refine Subtype.ext ?_
    refine Subtype.ext ?_
    have hd : P ^ e * ((Q.1 : Polynomial F) / P ^ e) = (Q.1 : Polynomial F) :=
      EuclideanDomain.mul_div_cancel' (hP.pow e).ne_zero Q.2
    simpa [mul_comm] using hd

/-- Step 2: multiplicativity replaces `Ψ A * Ψ P^e` by `Ψ (A * P^e)`. -/
lemma step2 (Ψ : Polynomial F → ℂ) (h1 : Ψ 1 = 1)
    (hmul : ∀ A B : Polynomial F, A.Monic → B.Monic → Ψ (A * B) = Ψ A * Ψ B) (N : ℕ) :
    (∑ m ∈ Finset.range N, ∑ A : MonicDegF F m, ∑ d ∈ (N - m).divisors,
        ∑ P : MonicIrredDeg F d, (d : ℂ) * (Ψ A * Ψ P ^ ((N - m) / d))) =
      ∑ m ∈ Finset.range N, ∑ A : MonicDegF F m, ∑ d ∈ (N - m).divisors,
        ∑ P : MonicIrredDeg F d, (d : ℂ) * Ψ (A * P ^ ((N - m) / d)) := by
  refine Finset.sum_congr rfl (fun m _ => ?_)
  refine Finset.sum_congr rfl (fun A _ => ?_)
  refine Finset.sum_congr rfl (fun d _ => ?_)
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [← psi_pow Ψ h1 hmul P P.2.1 ((N - m) / d),
    hmul A (P ^ ((N - m) / d)) A.2.1 (P.2.1.pow _)]

/-- Step 3: reindex the double sum over `(m, d)` by `(d, e)` with `m = N - d*e`. -/
lemma step3 (Ψ : Polynomial F → ℂ) (N : ℕ) :
    (∑ m ∈ Finset.range N, ∑ A : MonicDegF F m, ∑ d ∈ (N - m).divisors,
        ∑ P : MonicIrredDeg F d, (d : ℂ) * Ψ (A * P ^ ((N - m) / d))) =
      ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 (N / d), ∑ A : MonicDegF F (N - d * e),
        ∑ P : MonicIrredDeg F d, (d : ℂ) * Ψ (A * P ^ e) := by
  have hswap : (∑ m ∈ Finset.range N, ∑ A : MonicDegF F m, ∑ d ∈ (N - m).divisors,
        ∑ P : MonicIrredDeg F d, (d : ℂ) * Ψ (A * P ^ ((N - m) / d))) =
      ∑ m ∈ Finset.range N, ∑ d ∈ (N - m).divisors, ∑ A : MonicDegF F m,
        ∑ P : MonicIrredDeg F d, (d : ℂ) * Ψ (A * P ^ ((N - m) / d)) := by
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Finset.sum_comm]
  rw [hswap]
  rw [Commons.NumberTheory.Nat.sum_range_divisors_reindex N
    (fun m d => ∑ A : MonicDegF F m, ∑ P : MonicIrredDeg F d,
      (d : ℂ) * Ψ (A * P ^ ((N - m) / d)))]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  refine Finset.sum_congr rfl (fun e he => ?_)
  refine Finset.sum_congr rfl (fun A _ => ?_)
  refine Finset.sum_congr rfl (fun P _ => ?_)
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  have he1 : e ≤ N / d := (Finset.mem_Icc.mp he).2
  have hde : d * e ≤ N := by
    have h : e * d ≤ N := (Nat.le_div_iff_mul_le (by omega : 0 < d)).mp he1
    simpa [Nat.mul_comm] using h
  rw [Nat.sub_sub_self hde, Nat.mul_div_right e (by omega : 0 < d)]

/-- Step 4: exchange the order of the sums over `e` and `P`. -/
lemma step4 (Ψ : Polynomial F → ℂ) (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 (N / d), ∑ A : MonicDegF F (N - d * e),
        ∑ P : MonicIrredDeg F d, (d : ℂ) * Ψ (A * P ^ e)) =
      ∑ d ∈ Finset.Icc 1 N, ∑ P : MonicIrredDeg F d, ∑ e ∈ Finset.Icc 1 (N / d),
        ∑ A : MonicDegF F (N - d * e), (d : ℂ) * Ψ (A * P ^ e) := by
  have h1 : (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 (N / d),
        ∑ A : MonicDegF F (N - d * e),
        ∑ P : MonicIrredDeg F d, (d : ℂ) * Ψ (A * P ^ e)) =
      ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 (N / d), ∑ P : MonicIrredDeg F d,
        ∑ A : MonicDegF F (N - d * e), (d : ℂ) * Ψ (A * P ^ e) := by
    refine Finset.sum_congr rfl (fun d _ => ?_)
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [Finset.sum_comm]
  rw [h1]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [Finset.sum_comm]

/-- The summand in the final double counting. -/
noncomputable def T (Ψ : Polynomial F → ℂ) (N : ℕ) (d : ℕ) (P : Polynomial F) (e : ℕ)
    (Q : MonicDegF F N) : ℂ := if P ^ e ∣ (Q : Polynomial F) then (d : ℂ) * Ψ Q else 0

/-- Multiplication by `P ^ e` as a sum identity. -/
lemma step5inner (Ψ : Polynomial F → ℂ) (P : Polynomial F) (hP : P.Monic) (N e d : ℕ)
    (hpd : P.natDegree = d) (he : P.natDegree * e ≤ N) :
    (∑ A : MonicDegF F (N - d * e), (d : ℂ) * Ψ (A * P ^ e)) =
      ∑ Q : MonicDegF F N,
        (if P ^ e ∣ (Q : Polynomial F) then (d : ℂ) * Ψ Q else 0) := by
  subst hpd
  rw [sum_ite_subtype (fun Q : MonicDegF F N => P ^ e ∣ (Q : Polynomial F))
      (fun Q : MonicDegF F N => (P.natDegree : ℂ) * Ψ Q)]
  exact Fintype.sum_equiv (mulPowEquiv P hP e N he)
    (fun A : MonicDegF F (N - P.natDegree * e) => (P.natDegree : ℂ) * Ψ (A * P ^ e))
    (fun Q : {Q : MonicDegF F N // P ^ e ∣ (Q : Polynomial F)} =>
      (P.natDegree : ℂ) * Ψ Q.1)
    (fun A => rfl)

/-- Step 5: replace the sum over `B` of `Ψ (B * P^e)` by a sum over monic `Q` divisible by
`P ^ e`. -/
lemma step5 (Ψ : Polynomial F → ℂ) (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, ∑ P : MonicIrredDeg F d, ∑ e ∈ Finset.Icc 1 (N / d),
        ∑ A : MonicDegF F (N - d * e), (d : ℂ) * Ψ (A * P ^ e)) =
      ∑ d ∈ Finset.Icc 1 N, ∑ P : MonicIrredDeg F d, ∑ e ∈ Finset.Icc 1 (N / d),
        ∑ Q : MonicDegF F N, T Ψ N d P e Q := by
  refine Finset.sum_congr rfl (fun d hd => ?_)
  refine Finset.sum_congr rfl (fun P _ => ?_)
  refine Finset.sum_congr rfl (fun e he => ?_)
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  have he1 : e ≤ N / d := (Finset.mem_Icc.mp he).2
  have hde : d * e ≤ N := by
    have h : e * d ≤ N := (Nat.le_div_iff_mul_le (by omega : 0 < d)).mp he1
    simpa [Nat.mul_comm] using h
  have hdn : (P : Polynomial F).natDegree * e ≤ N := by
    rw [P.2.2.2]; exact hde
  exact step5inner Ψ P P.2.1 N e d P.2.2.2 hdn

/-- Step 7: exchange the sum over `(d, P, e)` with the sum over `Q`. -/
lemma step7 (Ψ : Polynomial F → ℂ) (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, ∑ P : MonicIrredDeg F d, ∑ e ∈ Finset.Icc 1 (N / d),
        ∑ Q : MonicDegF F N, T Ψ N d P e Q) =
      ∑ Q : MonicDegF F N, ∑ d ∈ Finset.Icc 1 N, ∑ P : MonicIrredDeg F d,
        ∑ e ∈ Finset.Icc 1 (N / d), T Ψ N d P e Q := by
  let S : Finset (Σ _ : ℕ, Σ _ : MonicIrredDeg F _, ℕ) :=
    (Finset.Icc 1 N).sigma (fun d =>
      (Finset.univ : Finset (MonicIrredDeg F d)).sigma (fun _ => Finset.Icc 1 (N / d)))
  have hL : (∑ d ∈ Finset.Icc 1 N, ∑ P : MonicIrredDeg F d, ∑ e ∈ Finset.Icc 1 (N / d),
        ∑ Q : MonicDegF F N, T Ψ N d P e Q) =
      ∑ x ∈ S, ∑ Q : MonicDegF F N, T Ψ N x.1 x.2.1 x.2.2 Q := by
    have hinner : ∀ d, (∑ P : MonicIrredDeg F d, ∑ e ∈ Finset.Icc 1 (N / d),
          ∑ Q : MonicDegF F N, T Ψ N d P e Q) =
        ∑ y ∈ (Finset.univ : Finset (MonicIrredDeg F d)).sigma
          (fun _ => Finset.Icc 1 (N / d)), ∑ Q : MonicDegF F N, T Ψ N d y.1 y.2 Q := by
      intro d
      exact (Finset.sum_sigma (s := (Finset.univ : Finset (MonicIrredDeg F d)))
        (t := fun _ => Finset.Icc 1 (N / d))
        (f := fun y => ∑ Q : MonicDegF F N, T Ψ N d y.1 y.2 Q)).symm
    exact (Finset.sum_congr rfl (fun d _ => hinner d)).trans
      (Finset.sum_sigma (s := Finset.Icc 1 N)
        (t := fun d => (Finset.univ : Finset (MonicIrredDeg F d)).sigma
          (fun _ => Finset.Icc 1 (N / d)))
        (f := fun x => ∑ Q : MonicDegF F N, T Ψ N x.1 x.2.1 x.2.2 Q)).symm
  have hcomm : (∑ x ∈ S, ∑ Q : MonicDegF F N, T Ψ N x.1 x.2.1 x.2.2 Q) =
      ∑ Q : MonicDegF F N, ∑ x ∈ S, T Ψ N x.1 x.2.1 x.2.2 Q := Finset.sum_comm
  have hR : (∑ Q : MonicDegF F N, ∑ x ∈ S, T Ψ N x.1 x.2.1 x.2.2 Q) =
      ∑ Q : MonicDegF F N, ∑ d ∈ Finset.Icc 1 N, ∑ P : MonicIrredDeg F d,
        ∑ e ∈ Finset.Icc 1 (N / d), T Ψ N d P e Q := by
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    have hinner : ∀ d, (∑ y ∈ (Finset.univ : Finset (MonicIrredDeg F d)).sigma
          (fun _ => Finset.Icc 1 (N / d)), T Ψ N d y.1 y.2 Q) =
        ∑ P : MonicIrredDeg F d, ∑ e ∈ Finset.Icc 1 (N / d), T Ψ N d P e Q := by
      intro d
      exact Finset.sum_sigma (s := (Finset.univ : Finset (MonicIrredDeg F d)))
        (t := fun _ => Finset.Icc 1 (N / d))
        (f := fun y => T Ψ N d y.1 y.2 Q)
    exact (Finset.sum_sigma (s := Finset.Icc 1 N)
        (t := fun d => (Finset.univ : Finset (MonicIrredDeg F d)).sigma
          (fun _ => Finset.Icc 1 (N / d)))
        (f := fun x => T Ψ N x.1 x.2.1 x.2.2 Q)).trans
      (Finset.sum_congr rfl (fun d _ => hinner d))
  rw [hL, hcomm, hR]

/-- Auxiliary counting lemma: for a monic irreducible `P` of degree `d`, the number of
exponents `e ∈ {1,…,N/d}` with `P ^ e ∣ Q`, weighted by `d`, is `d` times the multiplicity
of `P` in `Q`. -/
lemma step8a (N : ℕ) (Q : MonicDegF F N) (d : ℕ) (P : MonicIrredDeg F d) (m : ℕ)
    (hm : m = (UniqueFactorizationMonoid.normalizedFactors (Q : Polynomial F)).count
      (P : Polynomial F)) :
    (∑ e ∈ Finset.Icc 1 (N / d),
        (if (P : Polynomial F) ^ e ∣ (Q : Polynomial F) then (d : ℂ) else 0))
      = (d : ℂ) * (m : ℂ) := by
  subst hm
  have hp0 : 0 < d := by rw [← P.2.2.2]; exact Irreducible.natDegree_pos P.2.2.1
  have hcnt : (UniqueFactorizationMonoid.normalizedFactors (Q : Polynomial F)).count
      (P : Polynomial F) ≤ N / d := by
    have hdvd : (P : Polynomial F) ^ ((UniqueFactorizationMonoid.normalizedFactors
        (Q : Polynomial F)).count (P : Polynomial F)) ∣ (Q : Polynomial F) :=
      (Commons.Algebra.Polynomial.pow_dvd_iff_le_count_normalizedFactors P.2.1 P.2.2.1
        Q.2.1 _).mpr le_rfl
    have hdeg : ((P : Polynomial F) ^ ((UniqueFactorizationMonoid.normalizedFactors
        (Q : Polynomial F)).count (P : Polynomial F))).natDegree ≤ N := by
      have h := Polynomial.natDegree_le_of_dvd hdvd Q.2.1.ne_zero
      rwa [Q.2.2] at h
    rw [Monic.natDegree_pow P.2.1, P.2.2.2] at hdeg
    rwa [Nat.le_div_iff_mul_le hp0]
  have hfilter : (Finset.Icc 1 (N / d)).filter
      (fun e => (P : Polynomial F) ^ e ∣ (Q : Polynomial F)) =
        Finset.Icc 1 ((UniqueFactorizationMonoid.normalizedFactors (Q : Polynomial F)).count
          (P : Polynomial F)) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      exact ⟨h1, (Commons.Algebra.Polynomial.pow_dvd_iff_le_count_normalizedFactors P.2.1
        P.2.2.1 Q.2.1 e).mp h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, le_trans h2 hcnt⟩, (Commons.Algebra.Polynomial.pow_dvd_iff_le_count_normalizedFactors
        P.2.1 P.2.2.1 Q.2.1 e).mpr h2⟩
  have h1 : ∀ e, (if (P : Polynomial F) ^ e ∣ (Q : Polynomial F) then (d : ℂ) else 0)
      = (d : ℂ) * (if (P : Polynomial F) ^ e ∣ (Q : Polynomial F) then (1 : ℂ) else 0) := by
    intro e; split <;> simp
  simp_rw [h1]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_boole, hfilter, Nat.card_Icc]
  simp

/-- Auxiliary: the total coefficient of `1` in the double counting equals `N`. -/
lemma step8aux (N : ℕ) (Q : MonicDegF F N) :
    (∑ d ∈ Finset.Icc 1 N, ∑ P : MonicIrredDeg F d, ∑ e ∈ Finset.Icc 1 (N / d),
        (if (P : Polynomial F) ^ e ∣ (Q : Polynomial F) then (d : ℂ) else 0))
      = (N : ℂ) := by
  let nf := UniqueFactorizationMonoid.normalizedFactors (Q : Polynomial F)
  have hA : (∑ d ∈ Finset.Icc 1 N, ∑ P : MonicIrredDeg F d, ∑ e ∈ Finset.Icc 1 (N / d),
        (if (P : Polynomial F) ^ e ∣ (Q : Polynomial F) then (d : ℂ) else 0))
      = ∑ d ∈ Finset.Icc 1 N, ∑ P : MonicIrredDeg F d,
          (d : ℂ) * ((nf.count (P : Polynomial F) : ℕ) : ℂ) := by
    refine Finset.sum_congr rfl (fun d _ => ?_)
    refine Finset.sum_congr rfl (fun P _ => ?_)
    exact step8a N Q d P _ rfl
  rw [hA]
  have h1 : (∑ d ∈ Finset.Icc 1 N, ∑ P : MonicIrredDeg F d,
          (d : ℂ) * ((nf.count (P : Polynomial F) : ℕ) : ℂ))
      = ∑ d ∈ Finset.Icc 1 N,
          ∑ P ∈ (Finset.univ : Finset (MonicIrredDeg F d)).filter
            (fun P : MonicIrredDeg F d => nf.count (P : Polynomial F) ≠ 0),
            (d : ℂ) * ((nf.count (P : Polynomial F) : ℕ) : ℂ) := by
    refine Finset.sum_congr rfl (fun d _ => ?_)
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro P _ hPnot
    have h0 : nf.count (P : Polynomial F) = 0 := by
      by_contra hc
      exact hPnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
    rw [h0]; simp
  rw [h1]
  have h2 : (∑ d ∈ Finset.Icc 1 N,
          ∑ P ∈ (Finset.univ : Finset (MonicIrredDeg F d)).filter
            (fun P : MonicIrredDeg F d => nf.count (P : Polynomial F) ≠ 0),
            (d : ℂ) * ((nf.count (P : Polynomial F) : ℕ) : ℂ))
      = ∑ d ∈ Finset.Icc 1 N,
          ∑ R ∈ nf.toFinset.filter (fun R : Polynomial F => R.natDegree = d),
            (R.natDegree : ℂ) * ((nf.count R : ℕ) : ℂ) := by
    refine Finset.sum_congr rfl (fun d _ => ?_)
    refine Finset.sum_bij
      (fun (P : MonicIrredDeg F d)
        (_ : P ∈ (Finset.univ : Finset (MonicIrredDeg F d)).filter
          (fun P : MonicIrredDeg F d => nf.count (P : Polynomial F) ≠ 0)) =>
        (P : Polynomial F))
      ?_ ?_ ?_ ?_
    · intro P hP
      rw [Finset.mem_filter] at hP
      refine Finset.mem_filter.mpr ⟨?_, P.2.2.2⟩
      exact Multiset.mem_toFinset.mpr ((multiset_count_ne_zero_iff.mp hP.2))
    · intro P1 _ P2 _ h
      exact Subtype.ext h
    · intro R hR
      rw [Finset.mem_filter] at hR
      refine ⟨(⟨R,
        Commons.FieldTheory.Polynomial.monic_of_mem_normalizedFactors Q.2.1.ne_zero
          (Multiset.mem_toFinset.mp hR.1),
        Commons.FieldTheory.Polynomial.irreducible_of_mem_normalizedFactors Q.2.1.ne_zero
          (Multiset.mem_toFinset.mp hR.1),
        hR.2⟩ : MonicIrredDeg F d), ?_, rfl⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      exact fun hc => Multiset.count_eq_zero.mp hc (Multiset.mem_toFinset.mp hR.1)
    · intro P _
      rw [P.2.2.2]
  rw [h2]
  have hpd : Set.PairwiseDisjoint ((Finset.Icc 1 N : Finset ℕ) : Set ℕ)
      (fun d => nf.toFinset.filter (fun R : Polynomial F => R.natDegree = d)) := by
    intro d1 _ d2 _ hne
    change Disjoint (nf.toFinset.filter (fun R : Polynomial F => R.natDegree = d1))
      (nf.toFinset.filter (fun R : Polynomial F => R.natDegree = d2))
    rw [Finset.disjoint_iff_inter_eq_empty]
    ext R
    simp only [Finset.mem_inter, Finset.mem_filter]
    constructor
    · rintro ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
      exact absurd (h1.symm.trans h2) hne
    · intro h
      simp at h
  have h3 : (∑ d ∈ Finset.Icc 1 N, ∑ R ∈ nf.toFinset.filter (fun R : Polynomial F => R.natDegree = d),
        (R.natDegree : ℂ) * ((nf.count R : ℕ) : ℂ))
      = ∑ R ∈ (Finset.Icc 1 N).biUnion
          (fun d => nf.toFinset.filter (fun R : Polynomial F => R.natDegree = d)),
          (R.natDegree : ℂ) * ((nf.count R : ℕ) : ℂ) :=
    (Finset.sum_biUnion (f := fun R => (R.natDegree : ℂ) * ((nf.count R : ℕ) : ℂ)) hpd).symm
  rw [h3]
  have hU : (Finset.Icc 1 N).biUnion (fun d => nf.toFinset.filter (fun R : Polynomial F => R.natDegree = d))
      = nf.toFinset := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro R hR
      rw [Finset.mem_biUnion] at hR
      obtain ⟨d, _, hRd⟩ := hR
      exact (Finset.mem_filter.mp hRd).1
    · intro R hR
      rw [Multiset.mem_toFinset] at hR
      have hRmon : R.Monic :=
        Commons.FieldTheory.Polynomial.monic_of_mem_normalizedFactors Q.2.1.ne_zero hR
      have hRirr : Irreducible R :=
        Commons.FieldTheory.Polynomial.irreducible_of_mem_normalizedFactors Q.2.1.ne_zero hR
      have hRdvd : R ∣ (Q : Polynomial F) :=
        ((Polynomial.mem_normalizedFactors_iff Q.2.1.ne_zero).mp hR).2.2
      have hdegN : R.natDegree ≤ N := by
        have h := Polynomial.natDegree_le_of_dvd hRdvd Q.2.1.ne_zero
        rwa [Q.2.2] at h
      rw [Finset.mem_biUnion]
      exact ⟨R.natDegree, Finset.mem_Icc.mpr ⟨Irreducible.natDegree_pos hRirr, hdegN⟩,
        Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hR, rfl⟩⟩
  rw [hU]
  have hB4 : (∑ R ∈ nf.toFinset, (R.natDegree : ℂ) * ((nf.count R : ℕ) : ℂ))
      = (N : ℂ) := by
    have hnat := Commons.Algebra.Polynomial.sum_natDegree_mul_count_normalizedFactors
      (Q : Polynomial F) Q.2.1
    have hN : (((Q : Polynomial F).natDegree) : ℂ) = (N : ℂ) := by rw [Q.2.2]
    rw [← hN]
    have hcongr : (∑ R ∈ nf.toFinset, (R.natDegree : ℂ) * ((nf.count R : ℕ) : ℂ))
        = ∑ R ∈ nf.toFinset, ((R.natDegree * nf.count R : ℕ) : ℂ) := by
      refine Finset.sum_congr rfl (fun R _ => ?_)
      push_cast
      ring
    rw [hcongr, ← Nat.cast_sum, hnat]
  exact hB4

/-- Step 8: the total coefficient of `Ψ Q` in the double counting. -/
lemma step8 (Ψ : Polynomial F → ℂ) (N : ℕ) (Q : MonicDegF F N) :
    (∑ d ∈ Finset.Icc 1 N, ∑ P : MonicIrredDeg F d, ∑ e ∈ Finset.Icc 1 (N / d),
        T Ψ N d P e Q) = (N : ℂ) * Ψ Q := by
  have hT : ∀ (d : ℕ) (P : Polynomial F) (e : ℕ),
      T Ψ N d P e Q = (if P ^ e ∣ (Q : Polynomial F) then (d : ℂ) else 0) * Ψ Q := by
    intro d P e; simp only [T]; split <;> simp
  have hA : (∑ d ∈ Finset.Icc 1 N, ∑ P : MonicIrredDeg F d, ∑ e ∈ Finset.Icc 1 (N / d),
        T Ψ N d P e Q)
      = ∑ d ∈ Finset.Icc 1 N, ∑ P : MonicIrredDeg F d, ∑ e ∈ Finset.Icc 1 (N / d),
          (if (P : Polynomial F) ^ e ∣ (Q : Polynomial F) then (d : ℂ) else 0) * Ψ Q := by
    refine Finset.sum_congr rfl (fun d _ => ?_)
    refine Finset.sum_congr rfl (fun P _ => ?_)
    refine Finset.sum_congr rfl (fun e _ => ?_)
    exact hT d (P : Polynomial F) e
  have h1 : (∑ d ∈ Finset.Icc 1 N, ∑ P : MonicIrredDeg F d, ∑ e ∈ Finset.Icc 1 (N / d),
          (if (P : Polynomial F) ^ e ∣ (Q : Polynomial F) then (d : ℂ) else 0) * Ψ Q)
      = ∑ d ∈ Finset.Icc 1 N, ∑ P : MonicIrredDeg F d,
          (∑ e ∈ Finset.Icc 1 (N / d),
            (if (P : Polynomial F) ^ e ∣ (Q : Polynomial F) then (d : ℂ) else 0)) * Ψ Q := by
    refine Finset.sum_congr rfl (fun d _ => ?_)
    refine Finset.sum_congr rfl (fun P _ => ?_)
    rw [← Finset.sum_mul]
  have h2 : (∑ d ∈ Finset.Icc 1 N, ∑ P : MonicIrredDeg F d,
          (∑ e ∈ Finset.Icc 1 (N / d),
            (if (P : Polynomial F) ^ e ∣ (Q : Polynomial F) then (d : ℂ) else 0)) * Ψ Q)
      = ∑ d ∈ Finset.Icc 1 N,
          (∑ P : MonicIrredDeg F d, ∑ e ∈ Finset.Icc 1 (N / d),
            (if (P : Polynomial F) ^ e ∣ (Q : Polynomial F) then (d : ℂ) else 0)) * Ψ Q := by
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [← Finset.sum_mul]
  have h3 : (∑ d ∈ Finset.Icc 1 N,
          (∑ P : MonicIrredDeg F d, ∑ e ∈ Finset.Icc 1 (N / d),
            (if (P : Polynomial F) ^ e ∣ (Q : Polynomial F) then (d : ℂ) else 0)) * Ψ Q)
      = (∑ d ∈ Finset.Icc 1 N, ∑ P : MonicIrredDeg F d, ∑ e ∈ Finset.Icc 1 (N / d),
          (if (P : Polynomial F) ^ e ∣ (Q : Polynomial F) then (d : ℂ) else 0)) * Ψ Q := by
    rw [← Finset.sum_mul]
  rw [hA, h1, h2, h3, step8aux N Q]

open Classical in
/-- **Euler-product log-derivative for monic polynomials.**

Let `F` be a finite field and `Ψ : F[X] → ℂ` be multiplicative on monic polynomials with `Ψ 1 = 1`.
Writing `monicPoly m c := X^m + ∑_{i<m} c i · X^i` for the monic polynomials of degree `m`, set
`c m := ∑_{c : Fin m → F} Ψ (monicPoly m c)` and
`S j := ∑_{d ∈ j.divisors} d · ∑_{c : Fin d → F} (if Irreducible (monicPoly d c) then Ψ (monicPoly d c) ^ (j/d) else 0)`.

Then `∑_{m<N} c m · S (N-m) = N · c N` for every `N ≥ 1`: this is the coefficient form of the
identity `L · (∑_j S_j X^j) = X · L'` for `L := ∑_m c m · X^m`, i.e. the logarithmic derivative of
the Euler product `L = ∏_P (1 - Ψ P · X^{deg P})^{-1}`.

Proof: expand both sides over `(B, P, e)` with `B` monic, `P` monic irreducible, `e ≥ 1`, and
`deg(B · P^e) = N`; the value is `(deg P) · Ψ(B) · Ψ(P)^e = (deg P) · Ψ(B · P^e)`.  The map
`(B,P,e) ↦ (B·P^e, P, e)` is a bijection onto the triples `(A,P,e)` with `A` monic of degree `N` and
`P^e ∣ A`; and `∑_{P^e ∣ A} deg P = deg A` for monic `A` (unique factorisation; use the multiset
`A.normalizedFactors` of monic irreducibles, together with `natDegree_multiset_prod_monic` and
`prod_normalizedFactors_of_monic`).  Hence both sides equal
`∑_{A monic, deg A = N} (deg A) · Ψ A = N · c N`. -/
theorem eulerProduct_logDeriv_monic {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (Ψ : Polynomial F → ℂ) (h1 : Ψ 1 = 1)
    (hmul : ∀ A B : Polynomial F, A.Monic → B.Monic → Ψ (A * B) = Ψ A * Ψ B) :
    ∀ N : ℕ, 1 ≤ N →
      (∑ m ∈ Finset.range N,
          (∑ c : Fin m → F, Ψ (Polynomial.X ^ m + ∑ i : Fin m, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ))) *
          (∑ d ∈ (N - m).divisors, (d : ℂ) *
            ∑ c : Fin d → F, if Irreducible (Polynomial.X ^ d + ∑ i : Fin d, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ))
              then Ψ (Polynomial.X ^ d + ∑ i : Fin d, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)) ^ ((N - m) / d) else 0))
        = (N : ℂ) * (∑ c : Fin N → F, Ψ (Polynomial.X ^ N + ∑ i : Fin N, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ))) := by
  intro N _
  have hL : (∑ m ∈ Finset.range N,
          (∑ c : Fin m → F, Ψ (Polynomial.X ^ m + ∑ i : Fin m, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ))) *
          (∑ d ∈ (N - m).divisors, (d : ℂ) *
            ∑ c : Fin d → F, if Irreducible (Polynomial.X ^ d + ∑ i : Fin d, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ))
              then Ψ (Polynomial.X ^ d + ∑ i : Fin d, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)) ^ ((N - m) / d) else 0))
      = ∑ m ∈ Finset.range N, Cm Ψ m * Sm Ψ (N - m) := by
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Cm, Sm]
    congr 1
    · exact sum_repPoly (F := F) m (fun p => Ψ p)
    · refine Finset.sum_congr rfl (fun d _ => ?_)
      congr 1
      exact sum_repPoly_irred (F := F) d (fun p : Polynomial F => Ψ p ^ ((N - m) / d))
  have hR : (N : ℂ) * (∑ c : Fin N → F, Ψ (Polynomial.X ^ N + ∑ i : Fin N, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)))
      = (N : ℂ) * Cm Ψ N := by
    rw [Cm]
    congr 1
    exact sum_repPoly (F := F) N (fun p => Ψ p)
  rw [hL, hR]
  calc (∑ m ∈ Finset.range N, Cm Ψ m * Sm Ψ (N - m))
      = ∑ m ∈ Finset.range N, ∑ A : MonicDegF F m, ∑ d ∈ (N - m).divisors,
          ∑ P : MonicIrredDeg F d, (d : ℂ) * (Ψ A * Ψ P ^ ((N - m) / d)) := step1 Ψ N
    _ = ∑ m ∈ Finset.range N, ∑ A : MonicDegF F m, ∑ d ∈ (N - m).divisors,
          ∑ P : MonicIrredDeg F d, (d : ℂ) * Ψ (A * P ^ ((N - m) / d)) := step2 Ψ h1 hmul N
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 (N / d), ∑ A : MonicDegF F (N - d * e),
          ∑ P : MonicIrredDeg F d, (d : ℂ) * Ψ (A * P ^ e) := step3 Ψ N
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ P : MonicIrredDeg F d, ∑ e ∈ Finset.Icc 1 (N / d),
          ∑ A : MonicDegF F (N - d * e), (d : ℂ) * Ψ (A * P ^ e) := step4 Ψ N
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ P : MonicIrredDeg F d, ∑ e ∈ Finset.Icc 1 (N / d),
          ∑ Q : MonicDegF F N, T Ψ N d P e Q := step5 Ψ N
    _ = ∑ Q : MonicDegF F N, ∑ d ∈ Finset.Icc 1 N, ∑ P : MonicIrredDeg F d,
          ∑ e ∈ Finset.Icc 1 (N / d), T Ψ N d P e Q := step7 Ψ N
    _ = ∑ Q : MonicDegF F N, (N : ℂ) * Ψ Q :=
          Finset.sum_congr rfl (fun Q _ => step8 Ψ N Q)
    _ = (N : ℂ) * Cm Ψ N := by rw [Cm, Finset.mul_sum]

end Commons.Algebra.Polynomial
