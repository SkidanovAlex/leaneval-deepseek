import Mathlib
import Submission.Commons.Algebra.MvPolynomial.pderivIter_properties
import Submission.Commons.Algebra.MvPolynomial.pderivIter_add
import Submission.Commons.Algebra.MvPolynomial.coeff_pderivIter

namespace Commons.Algebra.MvPolynomial

open scoped BigOperators

section Kron

variable {K : Type*} [CommRing K] {σ : Type*} [Fintype σ]

/-- The Kronecker substitution `x_j ↦ t ^ (w j)` as an algebra homomorphism. -/
noncomputable abbrev kron (w : σ → ℕ) (g : MvPolynomial σ K) : Polynomial K :=
  MvPolynomial.aeval (fun j => Polynomial.X ^ (w j)) g

omit [Fintype σ] in
lemma kron_add (w : σ → ℕ) (p q : MvPolynomial σ K) :
    kron w (p + q) = kron w p + kron w q := by
  simp only [kron, map_add]

/-- The total `w`-weight `∑ i, w i * s i` of a multi-index. -/
def kronWeight (w : σ → ℕ) (s : σ →₀ ℕ) : ℕ := ∑ i : σ, w i * s i

lemma kronWeight_add (w : σ → ℕ) (m m' : σ →₀ ℕ) :
    kronWeight w (m + m') = kronWeight w m + kronWeight w m' := by
  simp only [kronWeight, Finsupp.add_apply, mul_add, Finset.sum_add_distrib]

lemma kronWeight_single (w : σ → ℕ) (j : σ) :
    kronWeight w (Finsupp.single j 1) = w j := by
  simp only [kronWeight]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb; rw [Finsupp.single_eq_of_ne hb, mul_zero]
  · intro hj; exact absurd (Finset.mem_univ j) hj

lemma kron_monomial (w : σ → ℕ) (s : σ →₀ ℕ) (a : K) :
    kron w (MvPolynomial.monomial s a) = Polynomial.C a * Polynomial.X ^ (kronWeight w s) := by
  unfold kron
  rw [MvPolynomial.aeval_monomial]
  congr 1
  rw [show (s.prod fun i k => (Polynomial.X ^ w i) ^ k)
        = ∏ i ∈ s.support, (Polynomial.X ^ w i) ^ (s i) from rfl]
  rw [show (∏ i ∈ s.support, (Polynomial.X ^ w i) ^ (s i))
        = ∏ i ∈ s.support, (Polynomial.X : Polynomial K) ^ (w i * s i) from
    Finset.prod_congr rfl (fun i _ => by rw [pow_mul])]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [kronWeight]
  exact Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => by
    rw [Finsupp.notMem_support_iff.mp hx, mul_zero])

lemma kron_term (w : σ → ℕ) (s : σ →₀ ℕ) (a : K) (j : σ) :
    ((w j : K) • Polynomial.X ^ (w j - 1)) *
      kron w (MvPolynomial.pderiv j (MvPolynomial.monomial s a))
    = Polynomial.C (a * (s j : K) * (w j : K)) * Polynomial.X ^ (kronWeight w s - 1) := by
  rw [MvPolynomial.pderiv_monomial, kron_monomial, Polynomial.smul_eq_C_mul]
  by_cases hwj : w j = 0
  · rw [hwj]
    simp
  · by_cases hsj : s j = 0
    · rw [hsj]
      simp
    · have hle : Finsupp.single j 1 ≤ s := by
        rw [Finsupp.single_le_iff]; omega
      have hcancel : (s - Finsupp.single j 1) + Finsupp.single j 1 = s :=
        tsub_add_cancel_of_le_finsupp hle
      have h1 : kronWeight w (s - Finsupp.single j 1) + w j = kronWeight w s := by
        rw [← kronWeight_single w j, ← kronWeight_add, hcancel]
      have h1' : kronWeight w (s - Finsupp.single j 1) = kronWeight w s - w j :=
        Nat.eq_sub_of_add_eq h1
      have hwj1 : 1 ≤ w j := Nat.one_le_iff_ne_zero.mpr hwj
      have hsj1 : 1 ≤ s j := Nat.one_le_iff_ne_zero.mpr hsj
      have hle2 : w j ≤ kronWeight w s := by
        rw [kronWeight]
        calc w j = w j * 1 := (mul_one _).symm
          _ ≤ w j * s j := by gcongr
          _ ≤ ∑ i : σ, w i * s i :=
              Finset.single_le_sum (s := Finset.univ) (f := fun i => w i * s i)
                (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
      have h2 : (w j - 1) + (kronWeight w s - w j) = kronWeight w s - 1 := by omega
      have hkey : (Polynomial.C (w j : K) * Polynomial.X ^ (w j - 1)) *
            (Polynomial.C (a * (s j : K)) * Polynomial.X ^ (kronWeight w s - w j))
          = Polynomial.C ((w j : K) * (a * (s j : K))) *
            Polynomial.X ^ ((w j - 1) + (kronWeight w s - w j)) := by
        rw [mul_mul_mul_comm, ← map_mul, ← pow_add]
      rw [h1', hkey, h2,
        show (w j : K) * (a * (s j : K)) = a * (s j : K) * (w j : K) by ring]

lemma derivative_kron_monomial (w : σ → ℕ) (s : σ →₀ ℕ) (a : K) :
    Polynomial.derivative (kron w (MvPolynomial.monomial s a)) =
      ∑ j : σ, ((w j : K) • Polynomial.X ^ (w j - 1)) *
        kron w (MvPolynomial.pderiv j (MvPolynomial.monomial s a)) := by
  rw [Finset.sum_congr rfl (fun j _ => kron_term w s a j)]
  rw [kron_monomial, Polynomial.derivative_C_mul, Polynomial.derivative_X_pow]
  rw [← Finset.sum_mul, ← map_sum Polynomial.C]
  have hcast : (∑ j : σ, a * (s j : K) * (w j : K)) = a * (kronWeight w s : K) := by
    rw [kronWeight, Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Nat.cast_mul]
    ring
  rw [hcast, map_mul, mul_assoc]

/-- The chain rule for the Kronecker substitution (proved by linearity on monomials). -/
lemma derivative_kron (w : σ → ℕ) (h : MvPolynomial σ K) :
    Polynomial.derivative (kron w h) =
      ∑ j : σ, ((w j : K) • Polynomial.X ^ (w j - 1)) * kron w (MvPolynomial.pderiv j h) := by
  induction h using MvPolynomial.induction_on' with
  | monomial s a => exact derivative_kron_monomial w s a
  | add p q hp hq =>
      have hpq : ∀ j, MvPolynomial.pderiv j (p + q)
          = MvPolynomial.pderiv j p + MvPolynomial.pderiv j q := fun j => map_add _ p q
      calc Polynomial.derivative (kron w (p + q))
          = Polynomial.derivative (kron w p) + Polynomial.derivative (kron w q) := by
            rw [kron_add, Polynomial.derivative_add]
        _ = (∑ j : σ, ((w j : K) • Polynomial.X ^ (w j - 1)) * kron w (MvPolynomial.pderiv j p))
              + (∑ j : σ, ((w j : K) • Polynomial.X ^ (w j - 1)) *
                  kron w (MvPolynomial.pderiv j q)) := by
            rw [hp, hq]
        _ = ∑ j : σ, ((w j : K) • Polynomial.X ^ (w j - 1)) *
              kron w (MvPolynomial.pderiv j (p + q)) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro j _
            rw [hpq j, kron_add, mul_add]

end Kron

section Assembly

variable {K : Type*} [CommRing K] {σ : Type*} [Fintype σ]

/-- `Phi w g Q = ∑_μ Q μ * τ(∂^μ g)`, as an additive homomorphism in the coefficient family `Q`. -/
noncomputable def Phi (w : σ → ℕ) (g : MvPolynomial σ K) :
    ((σ →₀ ℕ) →₀ Polynomial K) →+ Polynomial K :=
  Finsupp.liftAddHom fun μ =>
    AddMonoidHom.mulRight (kron w (pderivIter μ g))

lemma Phi_apply (w : σ → ℕ) (g : MvPolynomial σ K) (Q : (σ →₀ ℕ) →₀ Polynomial K) :
    Phi w g Q = Q.sum (fun μ p => p * kron w (pderivIter μ g)) := by
  simp only [Phi, Finsupp.liftAddHom_apply, Finsupp.sum, AddMonoidHom.mulRight_apply]

lemma Phi_single (w : σ → ℕ) (g : MvPolynomial σ K) (μ : σ →₀ ℕ) (p : Polynomial K) :
    Phi w g (Finsupp.single μ p) = p * kron w (pderivIter μ g) := by
  simp only [Phi, Finsupp.liftAddHom_apply_single, AddMonoidHom.mulRight_apply]

/-- The one-step coefficient map, as an additive homomorphism in the polynomial entry. -/
noncomputable def stepF (w : σ → ℕ) (μ : σ →₀ ℕ) :
    Polynomial K →+ ((σ →₀ ℕ) →₀ Polynomial K) :=
  ((Finsupp.singleAddHom μ : Polynomial K →+ ((σ →₀ ℕ) →₀ Polynomial K)).comp
      (Polynomial.derivative.toAddMonoidHom))
    + ∑ j : σ, ((Finsupp.singleAddHom (μ + Finsupp.single j 1) :
        Polynomial K →+ ((σ →₀ ℕ) →₀ Polynomial K)).comp
        (AddMonoidHom.mulRight ((w j : K) • Polynomial.X ^ (w j - 1))))

lemma stepF_apply (w : σ → ℕ) (μ : σ →₀ ℕ) (p : Polynomial K) :
    stepF w μ p = Finsupp.single μ (Polynomial.derivative p) +
      ∑ j : σ, Finsupp.single (μ + Finsupp.single j 1)
        (p * ((w j : K) • Polynomial.X ^ (w j - 1))) := by
  simp only [stepF, AddMonoidHom.add_apply, AddMonoidHom.finsetSum_apply,
    AddMonoidHom.comp_apply, Finsupp.singleAddHom_apply, AddMonoidHom.mulRight_apply]
  rfl

/-- One step of differentiation on coefficients: the derivative of `∑_μ Q μ * τ(∂^μ g)` is again
of the same shape, with coefficient family `stepHom w Q`. -/
noncomputable def stepHom (w : σ → ℕ) :
    ((σ →₀ ℕ) →₀ Polynomial K) →+ ((σ →₀ ℕ) →₀ Polynomial K) :=
  Finsupp.liftAddHom (stepF w)

lemma stepHom_apply (w : σ → ℕ) (Q : (σ →₀ ℕ) →₀ Polynomial K) :
    stepHom w Q = Q.sum (fun μ => stepF w μ) := by
  simp only [stepHom, Finsupp.liftAddHom_apply]

lemma stepHom_single (w : σ → ℕ) (μ : σ →₀ ℕ) (p : Polynomial K) :
    stepHom w (Finsupp.single μ p) =
      Finsupp.single μ (Polynomial.derivative p) +
        ∑ j : σ, Finsupp.single (μ + Finsupp.single j 1)
          (p * ((w j : K) • Polynomial.X ^ (w j - 1))) := by
  rw [stepHom, Finsupp.liftAddHom_apply_single, stepF_apply]

lemma derivative_mul_kron (w : σ → ℕ) (g : MvPolynomial σ K) (μ : σ →₀ ℕ) (p : Polynomial K) :
    Polynomial.derivative (p * kron w (pderivIter μ g)) =
      Polynomial.derivative p * kron w (pderivIter μ g) +
        ∑ j : σ, (p * ((w j : K) • Polynomial.X ^ (w j - 1))) *
          kron w (pderivIter (μ + Finsupp.single j 1) g) := by
  have hpd : ∀ j : σ,
      MvPolynomial.pderiv j (pderivIter μ g) = pderivIter (μ + Finsupp.single j 1) g :=
    fun j => (pderivIter_properties (R := K) (σ := σ)).2.2.1 j μ g
  have hkey : p * (∑ j : σ, ((w j : K) • Polynomial.X ^ (w j - 1)) *
        kron w (MvPolynomial.pderiv j (pderivIter μ g)))
      = ∑ j : σ, (p * ((w j : K) • Polynomial.X ^ (w j - 1))) *
        kron w (pderivIter (μ + Finsupp.single j 1) g) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hpd j]
    ring
  rw [Polynomial.derivative_mul, derivative_kron, hkey]

lemma Phi_step_single (w : σ → ℕ) (g : MvPolynomial σ K) (μ : σ →₀ ℕ) (p : Polynomial K) :
    Polynomial.derivative (Phi w g (Finsupp.single μ p)) =
      Phi w g (stepHom w (Finsupp.single μ p)) := by
  rw [Phi_single, stepHom_single, map_add, map_sum (Phi w g)]
  simp only [Phi_single]
  rw [derivative_mul_kron]

lemma Phi_step (w : σ → ℕ) (g : MvPolynomial σ K) (P : (σ →₀ ℕ) →₀ Polynomial K) :
    Polynomial.derivative (Phi w g P) = Phi w g (stepHom w P) := by
  have h1 : P = ∑ μ ∈ P.support, Finsupp.single μ (P μ) := (Finsupp.sum_single P).symm
  rw [h1, map_sum (Phi w g), map_sum Polynomial.derivative, map_sum (stepHom w),
    map_sum (Phi w g)]
  exact Finset.sum_congr rfl (fun μ _ => Phi_step_single w g μ (P μ))

/-- The coefficient family produced by `k` iterations of `stepHom`. -/
noncomputable def Pseq (w : σ → ℕ) (k : ℕ) : (σ →₀ ℕ) →₀ Polynomial K :=
  (stepHom w)^[k] (Finsupp.single 0 1)

lemma Pseq_zero (w : σ → ℕ) :
    Pseq w 0 = Finsupp.single (0 : σ →₀ ℕ) (1 : Polynomial K) := by
  simp only [Pseq, Function.iterate_zero_apply]

lemma Pseq_succ (w : σ → ℕ) (n : ℕ) :
    Pseq w (n + 1) = stepHom w (Pseq (K := K) w n) := by
  simp only [Pseq, Function.iterate_succ_apply']

lemma derivative_iter_kron (w : σ → ℕ) (k : ℕ) (g : MvPolynomial σ K) :
    (Polynomial.derivative^[k]) (kron w g) = Phi w g (Pseq w k) := by
  induction k with
  | zero =>
      rw [Function.iterate_zero, id_eq, Phi_apply, Pseq_zero]
      rw [Finsupp.sum_single_index]
      · rw [(pderivIter_properties (R := K) (σ := σ)).1 g, one_mul]
      · simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, Phi_step, Pseq_succ]

end Assembly

section Support

variable {K : Type*} [CommRing K] {σ : Type*} [Fintype σ]

/-- Total degree `|μ| = ∑ i, μ i` of a multi-index. -/
def totalDeg (μ : σ →₀ ℕ) : ℕ := μ.sum (fun _ n => n)

omit [Fintype σ] in
lemma totalDeg_add (μ ν : σ →₀ ℕ) : totalDeg (μ + ν) = totalDeg μ + totalDeg ν := by
  simp only [totalDeg]
  rw [Finsupp.sum_add_index']
  · intro a; rfl
  · intro a b₁ b₂; rfl

omit [Fintype σ] in
lemma totalDeg_single (i : σ) (n : ℕ) : totalDeg (Finsupp.single i n) = n := by
  rw [totalDeg, Finsupp.sum_single_index]
  rfl

omit [Fintype σ] in
lemma totalDeg_zero : totalDeg (0 : σ →₀ ℕ) = 0 := by
  simp only [totalDeg, Finsupp.sum_zero_index]

lemma mem_stepHom_support (w : σ → ℕ) (P : (σ →₀ ℕ) →₀ Polynomial K) {ν : σ →₀ ℕ}
    (hν : ν ∈ (stepHom w P).support) :
    ∃ μ ∈ P.support, ν = μ ∨ ∃ j : σ, ν = μ + Finsupp.single j 1 := by
  rw [stepHom_apply] at hν
  obtain ⟨μ, hμ, hνμ⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum hν)
  refine ⟨μ, hμ, ?_⟩
  rw [stepF_apply] at hνμ
  rcases Finset.mem_union.mp (Finsupp.support_add hνμ) with h | h
  · exact Or.inl (Finset.mem_singleton.mp (Finsupp.support_single_subset h))
  · refine Or.inr ?_
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum h)
    exact ⟨j, Finset.mem_singleton.mp (Finsupp.support_single_subset hj)⟩

lemma stepHom_support_totalDeg (w : σ → ℕ) (P : (σ →₀ ℕ) →₀ Polynomial K) (k : ℕ)
    (hP : ∀ μ ∈ P.support, totalDeg μ ≤ k) :
    ∀ ν ∈ (stepHom w P).support, totalDeg ν ≤ k + 1 := by
  intro ν hν
  obtain ⟨μ, hμ, hcase⟩ := mem_stepHom_support w P hν
  have hk := hP μ hμ
  rcases hcase with rfl | ⟨j, rfl⟩
  · omega
  · rw [totalDeg_add, totalDeg_single]; omega

lemma Pseq_support (w : σ → ℕ) (k : ℕ) :
    ∀ μ ∈ (Pseq (K := K) w k).support, totalDeg μ ≤ k := by
  induction k with
  | zero =>
      intro μ hμ
      rw [Pseq_zero, Finsupp.mem_support_iff] at hμ
      have h0 : μ = 0 := by
        by_contra h
        exact hμ (Finsupp.single_eq_of_ne h)
      rw [h0, totalDeg_zero]
  | succ k ih =>
      intro μ hμ
      rw [Pseq_succ] at hμ
      exact stepHom_support_totalDeg w (Pseq w k) k ih μ hμ

end Support

/-
**Iterated derivatives of a Kronecker substitution.**

For `w : σ → ℕ` (with `σ` finite) let `τ g := aeval (fun j => X ^ (w j)) g`, i.e. the substitution
`x_j ↦ t^(w j)`.  Then for every `k` the `k`-th derivative of `τ g` is a `K[t]`-linear combination,
with coefficients `P μ ∈ K[t]` supported on multi-indices `μ` of total degree `|μ| ≤ k`, of the
Kronecker images of the iterated partial derivatives `∂^μ g`:
`(d/dt)^k (τ g) = ∑_μ P μ * τ (∂^μ g)`.

Suggested proof: induction on `k`.  For `k = 0` take `P = Finsupp.single 0 1`.  For the induction
step use the chain rule `(d/dt) (τ h) = ∑_j (w j : K) • (X ^ (w j - 1) * τ (∂_j h))`, proved on
monomials (`MvPolynomial.aeval_monomial`, `MvPolynomial.pderiv_monomial`); the coefficients for
`k+1` are those of `P` differentiated plus, for each `j`, the coefficients of `P` shifted by
`Finsupp.single j 1` and multiplied by `(w j : K) • X ^ (w j - 1)`.  The relation
`∂_j (∂^μ g) = ∂^(μ + single j 1) g` is `pderivIter_properties`.
-/
theorem iterate_derivative_aeval_kronecker {K : Type*} [CommRing K]
    {σ : Type*} [Fintype σ] (w : σ → ℕ) (k : ℕ) :
    ∃ P : (σ →₀ ℕ) →₀ Polynomial K,
      (∀ μ ∈ P.support, μ.sum (fun _ n => n) ≤ k) ∧
      ∀ g : MvPolynomial σ K,
        (Polynomial.derivative^[k]) (MvPolynomial.aeval (fun j => Polynomial.X ^ (w j)) g) =
          P.sum (fun μ p => p * MvPolynomial.aeval (fun j => Polynomial.X ^ (w j))
            (Commons.Algebra.MvPolynomial.pderivIter μ g)) := by
  refine ⟨Pseq w k, ?_, ?_⟩
  · exact Pseq_support w k
  · intro g
    have h := derivative_iter_kron w k g
    rw [Phi_apply] at h
    simpa only [kron] using h

end Commons.Algebra.MvPolynomial
