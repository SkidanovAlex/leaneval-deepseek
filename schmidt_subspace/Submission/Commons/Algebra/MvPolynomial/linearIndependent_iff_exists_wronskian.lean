import Mathlib
import Submission.Commons.Algebra.MvPolynomial.pderivIter_properties
import Submission.Commons.Algebra.MvPolynomial.pderivIter_add
import Submission.Commons.Algebra.MvPolynomial.iterate_derivative_aeval_kronecker
import Submission.Commons.Algebra.Matrix.det_eq_sum_of_rows
import Submission.Commons.Algebra.Polynomial.wronskian_linearIndependent

namespace Commons.Algebra.MvPolynomial

open scoped BigOperators
open _root_.MvPolynomial

/-! ## Linearity of `pderivIter` -/

section Linearity

variable {R : Type*} [CommSemiring R] {σ : Type*} [Fintype σ]

lemma pderivIter_zero_apply (m : σ →₀ ℕ) : pderivIter m (0 : MvPolynomial σ R) = 0 := by
  rw [pderivIter_eq_sum]
  simp

lemma pderivIter_single_add_apply (i : σ) (a : ℕ) (P Q : MvPolynomial σ R) :
    pderivIter (Finsupp.single i a) (P + Q) =
      pderivIter (Finsupp.single i a) P + pderivIter (Finsupp.single i a) Q := by
  induction a with
  | zero =>
    rw [Finsupp.single_zero, pderivIter_properties.1, pderivIter_properties.1,
      pderivIter_properties.1]
  | succ a ih =>
    rw [Finsupp.single_add, pderivIter_single_add 1 i (Finsupp.single i a) (P + Q), ih,
      pderivIter_properties.2.1, map_add, pderivIter_properties.2.2.1,
      pderivIter_properties.2.2.1]

lemma pderivIter_add_apply (m : σ →₀ ℕ) (P Q : MvPolynomial σ R) :
    pderivIter m (P + Q) = pderivIter m P + pderivIter m Q := by
  induction m using Finsupp.induction₂ with
  | zero =>
    rw [pderivIter_properties.1, pderivIter_properties.1, pderivIter_properties.1]
  | add_single a b f _ _ ih =>
    rw [pderivIter_single_add b a f (P + Q), ih,
      pderivIter_single_add_apply a b (pderivIter f P) (pderivIter f Q),
      pderivIter_single_add b a f P, pderivIter_single_add b a f Q]

lemma pderivIter_smul_apply (c : R) (m : σ →₀ ℕ) (P : MvPolynomial σ R) :
    pderivIter m (c • P) = c • pderivIter m P := by
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul,
    pderivIter_properties.2.2.2]

lemma pderivIter_sum_apply {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ R) (m : σ →₀ ℕ) :
    pderivIter m (∑ i ∈ s, f i) = ∑ i ∈ s, pderivIter m (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [pderivIter_zero_apply]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, pderivIter_add_apply, ih]

end Linearity

/-! ## The Kronecker substitution is injective on bounded monomials -/

/-- Base-`B` expansion is injective on digit vectors. -/
lemma digit_sum_injective {B : ℕ} (hB : 2 ≤ B) :
    ∀ {m : ℕ} (α β : Fin m → ℕ), (∀ i, α i < B) → (∀ i, β i < B) →
      (∑ i : Fin m, B ^ (i : ℕ) * α i) = (∑ i : Fin m, B ^ (i : ℕ) * β i) → α = β := by
  intro m
  induction m with
  | zero => intro α β _ _ _; exact Subsingleton.elim _ _
  | succ m ih =>
    intro α β hα hβ h
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at h
    simp only [Fin.val_zero, pow_zero, one_mul] at h
    have hpow : ∀ i : Fin m, B ^ ((i.succ : Fin (m + 1)) : ℕ) = B * B ^ (i : ℕ) := by
      intro i; rw [Fin.val_succ, pow_succ, mul_comm]
    simp only [hpow] at h
    have hfac : ∀ γ : Fin m → ℕ, (∑ i : Fin m, B * B ^ (i : ℕ) * γ i)
        = B * (∑ i : Fin m, B ^ (i : ℕ) * γ i) := by
      intro γ
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hfac, hfac] at h
    have h0 : α 0 = β 0 := by
      have hmod := congrArg (fun n : ℕ => n % B) h
      rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (hα 0), Nat.mod_eq_of_lt (hβ 0)] at hmod
      exact hmod
    have hXY : (∑ i : Fin m, B ^ (i : ℕ) * α i.succ) = (∑ i : Fin m, B ^ (i : ℕ) * β i.succ) := by
      rw [h0] at h
      exact Nat.mul_left_cancel (by omega : 0 < B) (Nat.add_left_cancel h)
    have hsucc := ih (fun i => α i.succ) (fun i => β i.succ) (fun i => hα i.succ)
      (fun i => hβ i.succ) hXY
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact h0
    · exact congrFun hsucc j

/-- The Kronecker weights `B ^ (e j)` separate multi-indices whose coordinates are all `< B`. -/
lemma kronecker_weight_injective {σ : Type*} [Fintype σ] {B : ℕ} (hB : 2 ≤ B)
    {α β : σ →₀ ℕ} (hα : ∀ j, α j < B) (hβ : ∀ j, β j < B)
    (h : ∑ j : σ, B ^ (Fintype.equivFin σ j).val * α j =
         ∑ j : σ, B ^ (Fintype.equivFin σ j).val * β j) : α = β := by
  classical
  have h1 : (∑ j : σ, B ^ (Fintype.equivFin σ j).val * α j)
      = ∑ i : Fin (Fintype.card σ), B ^ (i : ℕ) * α ((Fintype.equivFin σ).symm i) :=
    Fintype.sum_equiv (Fintype.equivFin σ) _ _ (fun x => by simp)
  have h2 : (∑ j : σ, B ^ (Fintype.equivFin σ j).val * β j)
      = ∑ i : Fin (Fintype.card σ), B ^ (i : ℕ) * β ((Fintype.equivFin σ).symm i) :=
    Fintype.sum_equiv (Fintype.equivFin σ) _ _ (fun x => by simp)
  rw [h1, h2] at h
  have hfun := digit_sum_injective hB
    (fun i => α ((Fintype.equivFin σ).symm i)) (fun i => β ((Fintype.equivFin σ).symm i))
    (fun i => hα _) (fun i => hβ _) h
  ext j
  have := congrFun hfun (Fintype.equivFin σ j)
  simpa using this

/-- The Kronecker substitution `x_j ↦ t ^ (B ^ (e j))` of a monomial. -/
lemma aeval_monomial_kronecker {K : Type*} [CommSemiring K] {σ : Type*} [Fintype σ]
    (w : σ → ℕ) (c : K) (α : σ →₀ ℕ) :
    MvPolynomial.aeval (fun j => (Polynomial.X ^ (w j) : Polynomial K))
        (MvPolynomial.monomial α c)
      = Polynomial.C c * Polynomial.X ^ (∑ j : σ, w j * α j) := by
  rw [MvPolynomial.aeval_monomial]
  rw [Polynomial.C_eq_algebraMap]
  congr 1
  rw [Finsupp.prod]
  rw [Finset.prod_subset (Finset.subset_univ α.support) (fun j _ hj => by
    simp [Finsupp.notMem_support_iff.mp hj])]
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_congr rfl fun j _ => by rw [pow_mul]

/-- The Kronecker substitution is injective on polynomials whose monomials have all coordinates
bounded by `D`. -/
lemma kronecker_injective {K : Type*} [Field K] {σ : Type*} [Fintype σ]
    {D : ℕ} (hD : 2 ≤ D) (g : MvPolynomial σ K)
    (hg : ∀ α ∈ g.support, ∀ j : σ, α j < D) :
    (MvPolynomial.aeval (fun j => (Polynomial.X ^ (D ^ (Fintype.equivFin σ j).val) : Polynomial K)) g
      : Polynomial K) = 0 → g = 0 := by
  intro h0
  by_contra hg0
  have hne : g.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    refine hg0 ?_
    rw [← MvPolynomial.support_sum_monomial_coeff g, hemp]
    simp
  obtain ⟨α₀, hα₀⟩ := hne
  have key : ∀ α ∈ g.support,
      (Polynomial.C (g.coeff α) * Polynomial.X
        ^ (∑ j : σ, D ^ (Fintype.equivFin σ j).val * α j)).coeff
        (∑ j : σ, D ^ (Fintype.equivFin σ j).val * α₀ j)
        = if α = α₀ then g.coeff α else 0 := by
    intro α hα
    rw [Polynomial.coeff_C_mul_X_pow]
    by_cases h : α = α₀
    · subst h; simp
    · have hw : (∑ j : σ, D ^ (Fintype.equivFin σ j).val * α j)
          ≠ ∑ j : σ, D ^ (Fintype.equivFin σ j).val * α₀ j := by
        intro hw
        exact h (kronecker_weight_injective hD (hg α hα) (hg α₀ hα₀) hw)
      have hw' : ¬ ((∑ j : σ, D ^ (Fintype.equivFin σ j).val * α₀ j)
          = ∑ j : σ, D ^ (Fintype.equivFin σ j).val * α j) := fun hc => hw hc.symm
      simp [h, hw']
  have hexp : (MvPolynomial.aeval
      (fun j => (Polynomial.X ^ (D ^ (Fintype.equivFin σ j).val) : Polynomial K)) g : Polynomial K)
      = ∑ α ∈ g.support, Polynomial.C (g.coeff α) * Polynomial.X
        ^ (∑ j : σ, D ^ (Fintype.equivFin σ j).val * α j) := by
    conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff g]
    rw [map_sum]
    exact Finset.sum_congr rfl fun α _ => aeval_monomial_kronecker _ _ _
  have hcoeff : (∑ α ∈ g.support, Polynomial.C (g.coeff α) * Polynomial.X
      ^ (∑ j : σ, D ^ (Fintype.equivFin σ j).val * α j)).coeff
        (∑ j : σ, D ^ (Fintype.equivFin σ j).val * α₀ j) = g.coeff α₀ := by
    rw [← Polynomial.lcoeff_apply (R := K), map_sum]
    simp only [Polynomial.lcoeff_apply]
    rw [Finset.sum_congr rfl key, Finset.sum_ite_eq', if_pos hα₀]
  rw [hexp] at h0
  rw [h0, Polynomial.coeff_zero] at hcoeff
  exact (MvPolynomial.mem_support_iff.mp hα₀) hcoeff.symm

/-! ## The generalized Wronskian criterion -/

section Wronskian

variable {K : Type*} [Field K] [CharZero K] {σ : Type*} [Fintype σ] {n : ℕ}

/-- Auxiliary statement of the forward direction of the Wronskian criterion. -/
lemma exists_wronskian_det_ne_zero_of_linearIndependent
    (φ : Fin n → MvPolynomial σ K) (h : LinearIndependent K φ) :
    ∃ μ : Fin n → σ →₀ ℕ,
      (∀ i : Fin n, (μ i).sum (fun _ k => k) ≤ (i : ℕ)) ∧
      (Matrix.det (fun i j => pderivIter (μ i) (φ j)) : MvPolynomial σ K) ≠ 0 := by
  classical
  set S : Finset (σ →₀ ℕ) := Finset.univ.biUnion (fun j : Fin n => (φ j).support) with hS
  set B : ℕ := 2 + S.sup (fun α => α.support.sup (fun i : σ => α i)) with hBdef
  have hB2 : 2 ≤ B := by rw [hBdef]; omega
  have hbound : ∀ α ∈ S, ∀ i : σ, α i < B := by
    intro α hα i
    rw [hBdef]
    have : α i ≤ S.sup (fun α => α.support.sup (fun i : σ => α i)) := by
      by_cases hi : α i = 0
      · omega
      · exact le_trans (Finset.le_sup (f := fun i : σ => α i) (Finsupp.mem_support_iff.mpr hi))
          (Finset.le_sup (f := fun α : σ →₀ ℕ => α.support.sup (fun i : σ => α i)) hα)
    omega
  have hinj : ∀ c : Fin n → K,
      (MvPolynomial.aeval (fun j => (Polynomial.X ^ (B ^ (Fintype.equivFin σ j).val) : Polynomial K))
        (∑ j, c j • φ j) : Polynomial K) = 0 → (∑ j, c j • φ j) = 0 := by
    intro c hc
    refine kronecker_injective hB2 _ ?_ hc
    intro α hαmem i
    have hmem : α ∈ S := by
      by_contra hnot
      refine (MvPolynomial.mem_support_iff.mp hαmem) ?_
      rw [MvPolynomial.coeff_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [MvPolynomial.coeff_smul]
      have : α ∉ (φ j).support := fun hh =>
        hnot (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hh⟩)
      rw [MvPolynomial.notMem_support_iff.mp this, smul_zero]
    exact hbound α hmem i
  have hLI : LinearIndependent K (fun j => (MvPolynomial.aeval
      (fun j => (Polynomial.X ^ (B ^ (Fintype.equivFin σ j).val) : Polynomial K)) (φ j)
        : Polynomial K)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hτc : (MvPolynomial.aeval
        (fun j => (Polynomial.X ^ (B ^ (Fintype.equivFin σ j).val) : Polynomial K))
        (∑ j, c j • φ j) : Polynomial K) = 0 := by
      rw [map_sum]
      calc (∑ j, MvPolynomial.aeval (fun j => (Polynomial.X ^ (B ^ (Fintype.equivFin σ j).val)
              : Polynomial K)) (c j • φ j))
          = ∑ j, c j • (MvPolynomial.aeval
              (fun j => (Polynomial.X ^ (B ^ (Fintype.equivFin σ j).val) : Polynomial K))
              (φ j)) := Finset.sum_congr rfl fun j _ => map_smul _ _ _
        _ = 0 := hc
    have := hinj c hτc
    exact (Fintype.linearIndependent_iff.mp h) c this
  have hdet : (Matrix.of (fun i j : Fin n => (Polynomial.derivative^[(i : ℕ)])
      (MvPolynomial.aeval (fun j => (Polynomial.X ^ (B ^ (Fintype.equivFin σ j).val)
        : Polynomial K)) (φ j)))).det ≠ 0 :=
    Commons.Algebra.Polynomial.wronskian_linearIndependent _ hLI
  choose P hP using fun k : Fin n => iterate_derivative_aeval_kronecker (K := K)
    (fun j => B ^ (Fintype.equivFin σ j).val) (k : ℕ)
  have hArow : ∀ k : Fin n,
      (Matrix.of (fun i j : Fin n => (Polynomial.derivative^[(i : ℕ)])
        (MvPolynomial.aeval (fun j => (Polynomial.X ^ (B ^ (Fintype.equivFin σ j).val)
          : Polynomial K)) (φ j)))) k
      = ∑ μ : {μ : σ →₀ ℕ // μ ∈ (P k).support},
          (P k) (μ : σ →₀ ℕ) •
            (fun j : Fin n => MvPolynomial.aeval
              (fun j => (Polynomial.X ^ (B ^ (Fintype.equivFin σ j).val) : Polynomial K))
              (pderivIter (μ : σ →₀ ℕ) (φ j))) := by
    intro k
    funext j
    simp only [Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [(hP k).2 (φ j), Finsupp.sum]
    rw [Finset.sum_subtype ((P k).support) (fun x => Iff.rfl)
      (fun μ => (P k) μ * MvPolynomial.aeval
        (fun j => (Polynomial.X ^ (B ^ (Fintype.equivFin σ j).val) : Polynomial K))
        (pderivIter μ (φ j)))]
  have hsum := Commons.Algebra.Matrix.det_eq_sum_of_rows
    (ι := fun k : Fin n => {μ : σ →₀ ℕ // μ ∈ (P k).support})
    (Matrix.of (fun i j : Fin n => (Polynomial.derivative^[(i : ℕ)])
      (MvPolynomial.aeval (fun j => (Polynomial.X ^ (B ^ (Fintype.equivFin σ j).val)
        : Polynomial K)) (φ j))))
    (fun k μ j => MvPolynomial.aeval
      (fun j => (Polynomial.X ^ (B ^ (Fintype.equivFin σ j).val) : Polynomial K))
      (pderivIter (μ : σ →₀ ℕ) (φ j)))
    (fun k μ => (P k) (μ : σ →₀ ℕ)) hArow
  rw [hsum] at hdet
  obtain ⟨f, hf⟩ := Finset.exists_ne_zero_of_sum_ne_zero hdet
  have hfdet : (Matrix.of (fun k : Fin n => fun j : Fin n => MvPolynomial.aeval
      (fun j => (Polynomial.X ^ (B ^ (Fintype.equivFin σ j).val) : Polynomial K))
      (pderivIter ((f k : σ →₀ ℕ)) (φ j)))).det ≠ 0 :=
    (mul_ne_zero_iff.mp hf.2).2
  refine ⟨fun k => (f k : σ →₀ ℕ), fun i => (hP i).1 (f i).val (f i).property, ?_⟩
  intro hzero
  apply hfdet
  have hmap : (Matrix.of (fun k : Fin n => fun j : Fin n => MvPolynomial.aeval
      (fun j => (Polynomial.X ^ (B ^ (Fintype.equivFin σ j).val) : Polynomial K))
      (pderivIter ((f k : σ →₀ ℕ)) (φ j))))
      = (Matrix.of (fun k j : Fin n => pderivIter
          ((f k : σ →₀ ℕ)) (φ j))).map
        (MvPolynomial.aeval (fun j => (Polynomial.X ^ (B ^ (Fintype.equivFin σ j).val)
          : Polynomial K))) := by
    ext k j
    simp [Matrix.map_apply]
  rw [hmap]
  let hτ : MvPolynomial σ K →+* Polynomial K := (MvPolynomial.aeval
    (fun j => (Polynomial.X ^ (B ^ (Fintype.equivFin σ j).val) : Polynomial K))).toRingHom
  change (hτ.mapMatrix (Matrix.of (fun k j : Fin n =>
    pderivIter ((f k : σ →₀ ℕ)) (φ j)))).det = 0
  have hzero' : (Matrix.of (fun k j : Fin n =>
      pderivIter ((f k : σ →₀ ℕ)) (φ j))).det = 0 := hzero
  rw [← RingHom.map_det, hzero', map_zero]

end Wronskian

section Backward

variable {K : Type*} [Field K] {σ : Type*} [Fintype σ] {n : ℕ}

/-- The backward direction: a nonvanishing (generalized) Wronskian forces linear independence. -/
lemma linearIndependent_of_exists_wronskian
    (φ : Fin n → MvPolynomial σ K) (μ : Fin n → σ →₀ ℕ)
    (hdet : (Matrix.det (fun i j => pderivIter (μ i) (φ j)) : MvPolynomial σ K) ≠ 0) :
    LinearIndependent K φ := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  by_contra hgi
  have hsum : ∀ k : Fin n, (∑ j, C (g j) * pderivIter (μ k) (φ j)) = 0 := by
    intro k
    have h0 : pderivIter (μ k) (∑ j, g j • φ j) = ∑ j, g j • pderivIter (μ k) (φ j) := by
      rw [pderivIter_sum_apply]
      exact Finset.sum_congr rfl fun j _ => pderivIter_smul_apply (g j) (μ k) (φ j)
    have h1 : (∑ j, g j • pderivIter (μ k) (φ j)) = 0 := by
      rw [← h0, hg, pderivIter_zero_apply]
    rw [← h1]
    exact Finset.sum_congr rfl fun j _ => (MvPolynomial.smul_eq_C_mul _ _).symm
  have hker : Matrix.mulVec (Matrix.of (fun i j => pderivIter (μ i) (φ j)))
      (fun j => C (g j)) = 0 := by
    funext k
    rw [Matrix.mulVec_apply, dotProduct, Pi.zero_apply, ← hsum k]
    exact (Finset.sum_congr rfl fun j _ => mul_comm (C (g j)) (pderivIter (μ k) (φ j))).symm
  have hne : (fun j => C (g j) : Fin n → MvPolynomial σ K) ≠ 0 := by
    intro hzero
    exact hgi (MvPolynomial.C_injective σ K (by simpa using congr_fun hzero i))
  exact hdet ((Matrix.exists_mulVec_eq_zero_iff).mp ⟨_, hne, hker⟩)

end Backward

/-- **Generalized Wronskian criterion for linear independence.**

A family `φ : Fin n → MvPolynomial σ K` over a field `K` of characteristic zero is linearly
independent if and only if some generalized Wronskian
`det (fun i j => ∂^{μ i} (φ j))` is a nonzero polynomial, with the multi-indices satisfying
`|μ i| ≤ i` (total degree; with `i` 0-indexed this is the survey's `|μ_i| ≤ i-1`).

The forward direction uses the Kronecker substitution `x_j ↦ t ^ (d ^ j)` and the classical
univariate Wronskian criterion; the backward direction is immediate since a linear relation
between the `φ j` makes the rows dependent. -/
theorem linearIndependent_iff_exists_wronskian {K : Type*} [Field K] [CharZero K]
    {σ : Type*} [Fintype σ] {n : ℕ} (φ : Fin n → MvPolynomial σ K) :
    LinearIndependent K φ ↔ ∃ μ : Fin n → σ →₀ ℕ,
      (∀ i : Fin n, (μ i).sum (fun _ k => k) ≤ (i : ℕ)) ∧
      (Matrix.det (fun i j => pderivIter (μ i) (φ j)) : MvPolynomial σ K) ≠ 0 :=
  ⟨fun h => exists_wronskian_det_ne_zero_of_linearIndependent φ h,
   fun ⟨μ, _, hdet⟩ => linearIndependent_of_exists_wronskian φ μ hdet⟩

end Commons.Algebra.MvPolynomial
