import Mathlib
import Submission.Commons.Algebra.MvPolynomial.pderivIter_properties
import Submission.Commons.Algebra.MvPolynomial.pderiv_aeval_linear
import Submission.Commons.Algebra.MvPolynomial.coeff_pderivIter
import Submission.Commons.Algebra.MvPolynomial.pderivIter_add
import Submission.Commons.Algebra.MvPolynomial.pderiv_bind1

namespace Commons.Algebra.MvPolynomial

open scoped BigOperators
open _root_.MvPolynomial

variable {R : Type*} [CommRing R] {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The linear-form substitution `φ_A : X x ↦ ∑ y, C (A x y) * X y`. -/
noncomputable def phiR (A : σ → σ → R) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  MvPolynomial.aeval (fun x => ∑ y, MvPolynomial.C (A x y) * MvPolynomial.X y)

/-- Chain rule: `∂_y ∘ φ_A = ∑_x C (A x y) * φ_A ∘ ∂_x`. -/
lemma pderiv_phiR (A : σ → σ → R) (y : σ) (P : MvPolynomial σ R) :
    MvPolynomial.pderiv y (phiR A P) =
      ∑ x, MvPolynomial.C (A x y) * phiR A (MvPolynomial.pderiv x P) := by
  classical
  change MvPolynomial.pderiv y
        (MvPolynomial.aeval (fun x => ∑ z, MvPolynomial.C (A x z) * MvPolynomial.X z) P)
      = ∑ x, MvPolynomial.C (A x y)
          * MvPolynomial.aeval (fun x => ∑ z, MvPolynomial.C (A x z) * MvPolynomial.X z)
              (MvPolynomial.pderiv x P)
  have hpd : ∀ i : σ,
      MvPolynomial.pderiv y ((fun x => ∑ z, MvPolynomial.C (A x z) * MvPolynomial.X z) i)
        = MvPolynomial.C (A i y) := by
    intro i
    show MvPolynomial.pderiv y (∑ z, MvPolynomial.C (A i z) * MvPolynomial.X z)
        = MvPolynomial.C (A i y)
    rw [map_sum]
    rw [Finset.sum_eq_single y]
    · rw [MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X, Pi.single_eq_same, mul_one]
    · intro z _ hz
      rw [MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X_of_ne hz, mul_zero]
    · intro hy; exact absurd (Finset.mem_univ y) hy
  rw [MvPolynomial.aeval_eq_bind₁,
    Commons.Algebra.MvPolynomial.pderiv_bind1
      (fun x => ∑ z, MvPolynomial.C (A x z) * MvPolynomial.X z) y P]
  simp only [hpd]

/-- The conjugated derivative: `φ_A (∂_a P) = ∑_y C (B y a) * ∂_y (φ_A P)`. -/
lemma phiR_pderiv (A B : σ → σ → R)
    (hBA : ∀ x x', ∑ y, B y x * A x' y = if x = x' then 1 else 0)
    (a : σ) (P : MvPolynomial σ R) :
    phiR A (MvPolynomial.pderiv a P) =
      ∑ y, MvPolynomial.C (B y a) * MvPolynomial.pderiv y (phiR A P) := by
  classical
  have hchain : ∀ y : σ, MvPolynomial.pderiv y (phiR A P)
      = ∑ x, MvPolynomial.C (A x y) * phiR A (MvPolynomial.pderiv x P) :=
    fun y => pderiv_phiR A y P
  have key : (∑ y, MvPolynomial.C (B y a) * MvPolynomial.pderiv y (phiR A P))
      = ∑ x, MvPolynomial.C (∑ y, B y a * A x y) * phiR A (MvPolynomial.pderiv x P) := by
    calc ∑ y, MvPolynomial.C (B y a) * MvPolynomial.pderiv y (phiR A P)
        = ∑ y, MvPolynomial.C (B y a)
            * ∑ x, MvPolynomial.C (A x y) * phiR A (MvPolynomial.pderiv x P) := by
            refine Finset.sum_congr rfl (fun y _ => ?_); rw [hchain y]
      _ = ∑ y, ∑ x, MvPolynomial.C (B y a)
            * (MvPolynomial.C (A x y) * phiR A (MvPolynomial.pderiv x P)) := by
            refine Finset.sum_congr rfl (fun y _ => ?_); rw [Finset.mul_sum]
      _ = ∑ x, ∑ y, MvPolynomial.C (B y a)
            * (MvPolynomial.C (A x y) * phiR A (MvPolynomial.pderiv x P)) := Finset.sum_comm
      _ = ∑ x, (∑ y, MvPolynomial.C (B y a) * MvPolynomial.C (A x y))
            * phiR A (MvPolynomial.pderiv x P) := by
            refine Finset.sum_congr rfl (fun x _ => ?_)
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl; intro y _; ring
      _ = ∑ x, MvPolynomial.C (∑ y, B y a * A x y)
            * phiR A (MvPolynomial.pderiv x P) := by
            refine Finset.sum_congr rfl (fun x _ => ?_)
            congr 1
            rw [map_sum]
            refine Finset.sum_congr rfl (fun y _ => ?_)
            rw [map_mul]
  rw [key]
  simp only [hBA a]
  rw [Finset.sum_eq_single a]
  · simp
  · intro x _ hx; rw [if_neg (fun h => hx h.symm)]; simp
  · intro ha; exact absurd (Finset.mem_univ a) ha

omit [DecidableEq σ] in
/-- If `J` is a monomial of `∂^m P`, then `J + m` is a monomial of `P`. -/
lemma support_pderivIter_shift_ring {m J : σ →₀ ℕ} {P : MvPolynomial σ R}
    (hJ : J ∈ (pderivIter m P).support) : J + m ∈ P.support := by
  rw [MvPolynomial.mem_support_iff] at hJ ⊢
  intro h0
  exact hJ (by rw [coeff_pderivIter, h0, zero_mul])

/-- `∑ y, A x y * B y x' = δ` obtained from `hBA` by commutativity. -/
lemma sum_A_mul_B_ring (A B : σ → σ → R)
    (hBA : ∀ x x', ∑ y, B y x * A x' y = if x = x' then 1 else 0) (x x' : σ) :
    ∑ y, A x y * B y x' = if x = x' then 1 else 0 := by
  have h : (∑ y, A x y * B y x') = ∑ y, B y x' * A x y := by
    apply Finset.sum_congr rfl; intro y _; ring
  rw [h, hBA x' x]
  by_cases hxx : x = x'
  · rw [if_pos hxx.symm, if_pos hxx]
  · rw [if_neg (fun h => hxx h.symm), if_neg hxx]

/-- The other matrix identity `∑ z, B i z * A z j = δ`, by stable finiteness of
`Matrix σ σ R` (square matrices over a commutative ring). -/
lemma sum_B_mul_A_ring (A B : σ → σ → R)
    (hBA : ∀ x x', ∑ y, B y x * A x' y = if x = x' then 1 else 0) (i j : σ) :
    ∑ z, B i z * A z j = if i = j then 1 else 0 := by
  have hAB := sum_A_mul_B_ring A B hBA
  have hmul : (Matrix.of A : Matrix σ σ R) * Matrix.of B = 1 := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.one_apply]
    exact hAB a b
  have hmul' : (Matrix.of B : Matrix σ σ R) * Matrix.of A = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq σ σ R rfl).mp hmul
  simpa only [Matrix.mul_apply, Matrix.one_apply, Matrix.of_apply] using congrFun (congrFun hmul' i) j

/-- If `B y x ≠ 0` then `w x = w y`. -/
lemma w_eq_of_B_ne_zero_ring (A B : σ → σ → R)
    (hBA : ∀ x x', ∑ y, B y x * A x' y = if x = x' then 1 else 0)
    (w : σ → ℕ) (hA : ∀ x y, A x y ≠ 0 → w y = w x) {y x : σ} (h : B y x ≠ 0) :
    w y = w x := by
  by_contra hne
  have hAB := sum_A_mul_B_ring A B hBA
  have hBA' := sum_B_mul_A_ring A B hBA
  set S : Finset σ := Finset.univ.filter (fun t => w t = w x) with hS
  have hxS : x ∈ S := by rw [hS]; simp
  have hyS : y ∉ S := by
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hne
  have hI : ∀ t ∈ S, ∑ z ∈ S, A t z * B z x = if t = x then 1 else 0 := by
    intro t ht
    have htS : w t = w x := by
      rw [hS] at ht; simpa using ht
    have hrestrict : (∑ z ∈ S, A t z * B z x) = ∑ z, A t z * B z x := by
      refine Finset.sum_subset (Finset.subset_univ S) ?_
      intro z _ hz
      have hzw : w z ≠ w x := fun hwz =>
        hz (by rw [hS]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, hwz⟩)
      by_cases hAz : A t z = 0
      · rw [hAz, zero_mul]
      · exact absurd ((hA t z hAz).trans htS) hzw
    rw [hrestrict, hAB t x]
  have hII : ∀ z ∈ S, ∑ t ∈ S, B y t * A t z = 0 := by
    intro z hz
    have hzS : w z = w x := by
      rw [hS] at hz; simpa using hz
    have hyz : y ≠ z := fun hyz => hyS (by rw [hyz]; exact hz)
    have hrestrict : (∑ t ∈ S, B y t * A t z) = ∑ t, B y t * A t z := by
      refine Finset.sum_subset (Finset.subset_univ S) ?_
      intro t _ ht
      have htw : w t ≠ w x := fun hwt =>
        ht (by rw [hS]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ t, hwt⟩)
      by_cases hAt : A t z = 0
      · rw [hAt, mul_zero]
      · exact absurd ((hA t z hAt).symm.trans hzS) htw
    rw [hrestrict, hBA' y z, if_neg hyz]
  have hcomb : B y x = 0 := by
    have h1 : B y x = ∑ t ∈ S, B y t * (if t = x then 1 else 0) := by
      rw [Finset.sum_eq_single x]
      · simp
      · intro t _ htx; rw [if_neg htx, mul_zero]
      · intro hxnot; exact absurd hxS hxnot
    rw [h1]
    have h2 : (∑ t ∈ S, B y t * (if t = x then 1 else 0))
        = ∑ t ∈ S, B y t * (∑ z ∈ S, A t z * B z x) := by
      apply Finset.sum_congr rfl; intro t ht
      rw [hI t ht]
    rw [h2]
    have h3 : (∑ t ∈ S, B y t * (∑ z ∈ S, A t z * B z x))
        = ∑ z ∈ S, (∑ t ∈ S, B y t * A t z) * B z x := by
      calc ∑ t ∈ S, B y t * (∑ z ∈ S, A t z * B z x)
          = ∑ t ∈ S, ∑ z ∈ S, B y t * (A t z * B z x) := by
              apply Finset.sum_congr rfl; intro t _; rw [Finset.mul_sum]
        _ = ∑ z ∈ S, ∑ t ∈ S, B y t * (A t z * B z x) := Finset.sum_comm
        _ = ∑ z ∈ S, (∑ t ∈ S, B y t * A t z) * B z x := by
              apply Finset.sum_congr rfl; intro z _
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl; intro t _; ring
    rw [h3]
    apply Finset.sum_eq_zero; intro z hz
    rw [hII z hz, zero_mul]
  exact absurd hcomb h

/-- The bound on `ν` occurring in the conclusion. -/
def wboundR (w : σ → ℕ) (e ν : σ →₀ ℕ) : Prop :=
  ∀ y, ν y ≤ ∑ x ∈ Finset.univ.filter (fun x => w x = w y), e x

/-- The bound propagates through one more derivative. -/
lemma wbound_step_ring {w : σ → ℕ} {f : σ →₀ ℕ} {a y : σ} {ν : σ →₀ ℕ}
    (hν : wboundR w f ν) (hay : w a = w y) :
    wboundR w (f + Finsupp.single a 1) (Finsupp.single y 1 + ν) := by
  intro z
  have hνz : ν z ≤ ∑ x ∈ Finset.univ.filter (fun x => w x = w z), f x := hν z
  have h1 : (∑ x ∈ Finset.univ.filter (fun x => w x = w z), (Finsupp.single a 1 : σ →₀ ℕ) x)
      = if w a = w z then 1 else 0 := by
    simp only [Finsupp.single_apply, Finset.sum_ite_eq]
    simp
  have hsum : (∑ x ∈ Finset.univ.filter (fun x => w x = w z), (f + (Finsupp.single a 1 : σ →₀ ℕ)) x)
      = (∑ x ∈ Finset.univ.filter (fun x => w x = w z), f x) + (if w a = w z then 1 else 0) := by
    simp only [Finsupp.add_apply]
    rw [Finset.sum_add_distrib, h1]
  rw [Finsupp.add_apply, Finsupp.single_apply, hsum]
  by_cases hzy : y = z
  · rw [if_pos hzy, if_pos (hay.trans (congrArg w hzy))]
    omega
  · rw [if_neg hzy]
    omega

theorem pderivIter_aeval_linForm_support_ring {R : Type*} [CommRing R] {σ : Type*} [Fintype σ]
    [DecidableEq σ]
    (A B : σ → σ → R) (hBA : ∀ x x', ∑ y, B y x * A x' y = if x = x' then 1 else 0)
    (w : σ → ℕ) (hA : ∀ x y, A x y ≠ 0 → w y = w x)
    (e : σ →₀ ℕ) (Q : MvPolynomial σ R) (J : σ →₀ ℕ)
    (hJ : J ∈ (MvPolynomial.aeval (fun x => ∑ y, MvPolynomial.C (A x y) * MvPolynomial.X y)
        (Commons.Algebra.MvPolynomial.pderivIter e Q)).support) :
    ∃ ν : σ →₀ ℕ,
      (∀ y, ν y ≤ ∑ x ∈ Finset.univ.filter (fun x => w x = w y), e x) ∧
      J + ν ∈ (MvPolynomial.aeval (fun x => ∑ y, MvPolynomial.C (A x y) * MvPolynomial.X y) Q).support := by
  classical
  let Mot : (σ →₀ ℕ) → Prop := fun e => ∀ Q : MvPolynomial σ R, ∀ J : σ →₀ ℕ,
      J ∈ (phiR A (pderivIter e Q)).support →
        ∃ ν : σ →₀ ℕ, wboundR w e ν ∧ J + ν ∈ (phiR A Q).support
  have hsingle : ∀ (f : σ →₀ ℕ) (a : σ), Mot f → Mot (f + Finsupp.single a 1) := by
    intro f a hf Q J hJ
    have hdec : phiR A (pderivIter (f + Finsupp.single a 1) Q)
        = ∑ y, MvPolynomial.C (B y a) * MvPolynomial.pderiv y (phiR A (pderivIter f Q)) := by
      rw [show pderivIter (f + Finsupp.single a 1) Q = MvPolynomial.pderiv a (pderivIter f Q) from
        ((pderivIter_properties (R := R) (σ := σ)).2.2.1 a f Q).symm]
      exact phiR_pderiv A B hBA a (pderivIter f Q)
    rw [hdec] at hJ
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sum] at hJ
    obtain ⟨y, _, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hJ
    rw [MvPolynomial.coeff_C_mul] at hy
    have hBa : B y a ≠ 0 := fun h0 => hy (by rw [h0, zero_mul])
    have hy' : MvPolynomial.coeff J (MvPolynomial.pderiv y (phiR A (pderivIter f Q))) ≠ 0 :=
      fun h0 => hy (by rw [h0, mul_zero])
    have hmem : J ∈ (MvPolynomial.pderiv y (phiR A (pderivIter f Q))).support := by
      rwa [MvPolynomial.mem_support_iff]
    have hmem' : J ∈ (pderivIter (Finsupp.single y 1) (phiR A (pderivIter f Q))).support := by
      rw [(pderivIter_properties (R := R) (σ := σ)).2.1 y (phiR A (pderivIter f Q))]
      exact hmem
    have hshift := support_pderivIter_shift_ring hmem'
    obtain ⟨ν, hν, hνmem⟩ := hf Q (J + Finsupp.single y 1) hshift
    refine ⟨Finsupp.single y 1 + ν, wbound_step_ring hν ?_, ?_⟩
    · exact (w_eq_of_B_ne_zero_ring A B hBA w hA hBa).symm
    · rw [← add_assoc]; exact hνmem
  have hgen : ∀ (n : ℕ) (f : σ →₀ ℕ) (a : σ), Mot f → Mot (f + Finsupp.single a n) := by
    intro n
    induction n with
    | zero => intro f a hf; simpa using hf
    | succ n ih =>
        intro f a hf
        have h1 : f + Finsupp.single a (n + 1) = (f + Finsupp.single a n) + Finsupp.single a 1 := by
          rw [Finsupp.single_add, add_assoc]
        rw [h1]
        exact hsingle (f + Finsupp.single a n) a (ih f a hf)
  have key : Mot e := by
    refine Finsupp.induction₂ (motive := Mot) e ?_ ?_
    · intro Q J hJ
      refine ⟨0, ?_, ?_⟩
      · intro y; simp
      · rw [show pderivIter (0 : σ →₀ ℕ) Q = Q from
            (pderivIter_properties (R := R) (σ := σ)).1 Q] at hJ
        simpa using hJ
    · intro a b f _ hb hf
      exact hgen b f a hf
  exact key Q J hJ

end Commons.Algebra.MvPolynomial
