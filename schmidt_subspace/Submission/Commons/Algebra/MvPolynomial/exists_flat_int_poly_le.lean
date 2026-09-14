import Mathlib.NumberTheory.NumberField.House
import Mathlib.NumberTheory.SiegelsLemma
import Submission.Commons.Algebra.MvPowerSeries.card_finsupp_degree_eq

/-!
# Quantitative Siegel-type lemma: a flat integral polynomial with small coefficients

Statement: there is a constant `C > 0` such that for every family of degrees `d : Fin m → ℕ`
and every set `S` of "flat" exponent vectors with `2 * [K:ℚ] * #S < ∏ h, C(d h + N - 1, N - 1)`,
there is a nonzero integral polynomial `F ∈ ℤ[X (h,i)]`, homogeneous of degree `d h` in the block
`h`, whose `Λ`-expansion vanishes on `S`, and whose coefficients are bounded by
`C * (∏ h, C(d h + N - 1, N - 1)) * (C*M)^(∑ h, d h)` where `M` bounds the `Λ i j`.
-/

open MvPolynomial BigOperators
open Finset
open Module
open scoped Pointwise

attribute [local instance] Matrix.seminormedAddCommGroup

namespace Commons.Algebra.MvPolynomial

noncomputable section

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

/-! ## The house-`ℓ¹` norm on multivariate polynomials -/

variable {K : Type*} [Field K] [NumberField K]

/-- The coefficient `ℓ¹`-norm of a multivariate polynomial over a number field, measured with
the house of the coefficients. -/
@[simp] lemma house_zero : NumberField.house (0 : K) = 0 := by
  simp [NumberField.house]

@[simp] lemma house_one : NumberField.house (1 : K) = 1 := by
  simp [NumberField.house]

def hl1 {σ : Type*} (f : MvPolynomial σ K) : ℝ :=
  ∑ m ∈ f.support, NumberField.house (f.coeff m)

lemma hl1_nonneg {σ : Type*} (f : MvPolynomial σ K) : 0 ≤ hl1 f :=
  Finset.sum_nonneg fun _ _ => NumberField.house_nonneg _

lemma house_coeff_le_hl1 {σ : Type*} [DecidableEq σ] (f : MvPolynomial σ K)
    (m : σ →₀ ℕ) : NumberField.house (f.coeff m) ≤ hl1 f := by
  classical
  rw [hl1]
  by_cases h : m ∈ f.support
  · exact Finset.single_le_sum (fun _ _ => NumberField.house_nonneg _) h
  · rw [MvPolynomial.notMem_support_iff.mp h]
    simp only [NumberField.house, map_zero, norm_zero]
    exact Finset.sum_nonneg fun _ _ => NumberField.house_nonneg _

lemma hl1_zero {σ : Type*} : hl1 (0 : MvPolynomial σ K) = 0 := by
  simp [hl1]

lemma hl1_add_le {σ : Type*} [DecidableEq σ] (f g : MvPolynomial σ K) :
    hl1 (f + g) ≤ hl1 f + hl1 g := by
  classical
  have h1 : (∑ m ∈ (f + g).support, NumberField.house ((f + g).coeff m))
      ≤ ∑ m ∈ f.support ∪ g.support, NumberField.house ((f + g).coeff m) :=
    Finset.sum_le_sum_of_subset_of_nonneg (MvPolynomial.support_add (p := f) (q := g))
      (fun _ _ _ => NumberField.house_nonneg _)
  have h2 : (∑ m ∈ f.support ∪ g.support, NumberField.house ((f + g).coeff m))
      ≤ ∑ m ∈ f.support ∪ g.support,
          (NumberField.house (f.coeff m) + NumberField.house (g.coeff m)) := by
    refine Finset.sum_le_sum fun m _ => ?_
    rw [MvPolynomial.coeff_add]
    exact NumberField.house_add_le _ _
  have h3 : (∑ m ∈ f.support ∪ g.support, NumberField.house (f.coeff m))
      = ∑ m ∈ f.support, NumberField.house (f.coeff m) := by
    refine (Finset.sum_subset (Finset.subset_union_left) ?_).symm
    intro m _ hm
    rw [MvPolynomial.notMem_support_iff.mp hm]
    simp only [NumberField.house, map_zero, norm_zero]
  have h4 : (∑ m ∈ f.support ∪ g.support, NumberField.house (g.coeff m))
      = ∑ m ∈ g.support, NumberField.house (g.coeff m) := by
    refine (Finset.sum_subset (Finset.subset_union_right) ?_).symm
    intro m _ hm
    rw [MvPolynomial.notMem_support_iff.mp hm]
    simp only [NumberField.house, map_zero, norm_zero]
  rw [hl1]
  calc ∑ m ∈ (f + g).support, NumberField.house ((f + g).coeff m)
      ≤ ∑ m ∈ f.support ∪ g.support, NumberField.house ((f + g).coeff m) := h1
    _ ≤ ∑ m ∈ f.support ∪ g.support,
          (NumberField.house (f.coeff m) + NumberField.house (g.coeff m)) := h2
    _ = (∑ m ∈ f.support ∪ g.support, NumberField.house (f.coeff m))
        + (∑ m ∈ f.support ∪ g.support, NumberField.house (g.coeff m)) :=
        Finset.sum_add_distrib
    _ = hl1 f + hl1 g := by rw [h3, h4]; rfl

lemma hl1_monomial {σ : Type*} [DecidableEq σ] (m : σ →₀ ℕ) (a : K) :
    hl1 (MvPolynomial.monomial m a) = NumberField.house a := by
  classical
  rw [hl1]
  by_cases ha : a = 0
  · subst ha
    simp
  · rw [MvPolynomial.support_monomial, if_neg ha, Finset.sum_singleton,
      MvPolynomial.coeff_monomial, if_pos rfl]

lemma hl1_C {σ : Type*} [DecidableEq σ] (a : K) :
    hl1 (MvPolynomial.C a : MvPolynomial σ K) = NumberField.house a := by
  rw [MvPolynomial.C_apply, hl1_monomial]

lemma hl1_X {σ : Type*} [DecidableEq σ] (i : σ) :
    hl1 (MvPolynomial.X i : MvPolynomial σ K) = 1 := by
  rw [MvPolynomial.X, hl1_monomial]
  simp [NumberField.house]

/-- Counting lemma (real version): the pairs `(x.1, x.2)` with `x.1 ∈ A`, `x.2 ∈ B` occurring
in the antidiagonals of `S` are bounded by `#(A ×ˢ B)` weighted by `f, g`. -/
private lemma sum_antidiagonal_le_mul_house {M : Type*} [DecidableEq M] [AddCommMonoid M]
    [HasAntidiagonal M] (A B S : Finset M) (f g : M → ℝ)
    (hf : ∀ a ∈ A, 0 ≤ f a) (hg : ∀ b ∈ B, 0 ≤ g b) :
    ∑ m ∈ S, ∑ x ∈ HasAntidiagonal.antidiagonal m,
        (if x.1 ∈ A ∧ x.2 ∈ B then f x.1 * g x.2 else 0)
      ≤ (∑ a ∈ A, f a) * (∑ b ∈ B, g b) := by
  classical
  set T : M → Finset (M × M) := fun m =>
    (HasAntidiagonal.antidiagonal m).filter (fun x => x.1 ∈ A ∧ x.2 ∈ B) with hT
  have hinner : ∀ m, ∑ x ∈ HasAntidiagonal.antidiagonal m,
        (if x.1 ∈ A ∧ x.2 ∈ B then f x.1 * g x.2 else 0)
      = ∑ x ∈ T m, f x.1 * g x.2 := by
    intro m
    rw [hT]
    simp only [Finset.sum_filter]
  have hpair : (S : Set M).PairwiseDisjoint T := by
    intro m _ m' _ hne
    change Disjoint (T m) (T m')
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [hT] at hx hx'
    simp only [Finset.mem_filter] at hx hx'
    have h1 : x.1 + x.2 = m := HasAntidiagonal.mem_antidiagonal.mp hx.1
    have h2 : x.1 + x.2 = m' := HasAntidiagonal.mem_antidiagonal.mp hx'.1
    exact hne (h1.symm.trans h2)
  have hsubset : S.biUnion T ⊆ A ×ˢ B := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨m, _, hxm⟩ := hx
    rw [hT, Finset.mem_filter] at hxm
    rw [Finset.mem_product]
    exact hxm.2
  have hnonneg : ∀ x ∈ A ×ˢ B, 0 ≤ f x.1 * g x.2 := by
    intro x hx
    rw [Finset.mem_product] at hx
    exact mul_nonneg (hf x.1 hx.1) (hg x.2 hx.2)
  calc ∑ m ∈ S, ∑ x ∈ HasAntidiagonal.antidiagonal m,
        (if x.1 ∈ A ∧ x.2 ∈ B then f x.1 * g x.2 else 0)
      = ∑ m ∈ S, ∑ x ∈ T m, f x.1 * g x.2 := Finset.sum_congr rfl (fun m _ => hinner m)
    _ = ∑ x ∈ S.biUnion T, f x.1 * g x.2 := (Finset.sum_biUnion hpair).symm
    _ ≤ ∑ x ∈ A ×ˢ B, f x.1 * g x.2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun x _ _ => hnonneg x ‹_›)
    _ = (∑ a ∈ A, f a) * (∑ b ∈ B, g b) := by
        rw [Finset.sum_mul_sum]
        exact Finset.sum_product' A B (fun a b => f a * g b)

lemma hl1_mul_le {σ : Type*} [DecidableEq σ] (P Q : MvPolynomial σ K) :
    hl1 (P * Q) ≤ hl1 P * hl1 Q := by
  classical
  have step1 : (∑ m ∈ (P * Q).support, NumberField.house ((P * Q).coeff m))
      ≤ ∑ m ∈ P.support + Q.support, NumberField.house ((P * Q).coeff m) :=
    Finset.sum_le_sum_of_subset_of_nonneg (MvPolynomial.support_mul P Q)
      (fun _ _ _ => NumberField.house_nonneg _)
  have step2 : (∑ m ∈ P.support + Q.support, NumberField.house ((P * Q).coeff m))
      ≤ ∑ m ∈ P.support + Q.support, ∑ x ∈ HasAntidiagonal.antidiagonal m,
          NumberField.house (P.coeff x.1) * NumberField.house (Q.coeff x.2) := by
    refine Finset.sum_le_sum fun m _ => ?_
    rw [MvPolynomial.coeff_mul]
    calc NumberField.house (∑ x ∈ HasAntidiagonal.antidiagonal m,
            P.coeff x.1 * Q.coeff x.2)
        ≤ ∑ x ∈ HasAntidiagonal.antidiagonal m,
            NumberField.house (P.coeff x.1 * Q.coeff x.2) :=
          NumberField.house_sum_le_sum_house _ _
      _ ≤ ∑ x ∈ HasAntidiagonal.antidiagonal m,
            NumberField.house (P.coeff x.1) * NumberField.house (Q.coeff x.2) :=
          Finset.sum_le_sum fun x _ => NumberField.house_mul_le _ _
  have step3 : (∑ m ∈ P.support + Q.support, ∑ x ∈ HasAntidiagonal.antidiagonal m,
          NumberField.house (P.coeff x.1) * NumberField.house (Q.coeff x.2))
      = ∑ m ∈ P.support + Q.support, ∑ x ∈ HasAntidiagonal.antidiagonal m,
          (if x.1 ∈ P.support ∧ x.2 ∈ Q.support then
            NumberField.house (P.coeff x.1) * NumberField.house (Q.coeff x.2) else 0) := by
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun x _ => ?_
    by_cases h : x.1 ∈ P.support ∧ x.2 ∈ Q.support
    · rw [if_pos h]
    · rw [if_neg h]
      rcases not_and_or.mp h with h1 | h2
      · rw [MvPolynomial.notMem_support_iff.mp h1]; simp
      · rw [MvPolynomial.notMem_support_iff.mp h2]; simp
  have step4 : (∑ m ∈ P.support + Q.support, ∑ x ∈ HasAntidiagonal.antidiagonal m,
          (if x.1 ∈ P.support ∧ x.2 ∈ Q.support then
            NumberField.house (P.coeff x.1) * NumberField.house (Q.coeff x.2) else 0))
      ≤ (∑ a ∈ P.support, NumberField.house (P.coeff a))
        * (∑ b ∈ Q.support, NumberField.house (Q.coeff b)) :=
    sum_antidiagonal_le_mul_house P.support Q.support (P.support + Q.support)
      (fun a => NumberField.house (P.coeff a)) (fun b => NumberField.house (Q.coeff b))
      (fun _ _ => NumberField.house_nonneg _) (fun _ _ => NumberField.house_nonneg _)
  rw [hl1]
  exact le_trans step1 (le_trans step2 (le_trans (le_of_eq step3) step4))

lemma hl1_pow_le {σ : Type*} [DecidableEq σ] (P : MvPolynomial σ K) (n : ℕ) :
    hl1 (P ^ n) ≤ hl1 P ^ n := by
  induction n with
  | zero => simp [hl1]
  | succ n ih =>
      rw [pow_succ]
      exact le_trans (hl1_mul_le _ _) (mul_le_mul_of_nonneg_right ih (hl1_nonneg _))

lemma hl1_prod_le {σ ι : Type*} [DecidableEq σ] (s : Finset ι) (f : ι → MvPolynomial σ K) :
    hl1 (∏ i ∈ s, f i) ≤ ∏ i ∈ s, hl1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hl1]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      exact le_trans (hl1_mul_le _ _) (mul_le_mul_of_nonneg_left ih (hl1_nonneg _))

lemma hl1_sum_le {σ ι : Type*} [DecidableEq σ] (s : Finset ι) (f : ι → MvPolynomial σ K) :
    hl1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, hl1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hl1]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact le_trans (hl1_add_le _ _) (add_le_add le_rfl ih)

/-! ## Combinatorial index type for the monomials of a multidegree -/

private noncomputable instance instFintypeFinsuppDegreeEq {σ : Type*} [Finite σ] (n : ℕ) :
    Fintype {f : σ →₀ ℕ // f.degree = n} :=
  haveI : Finite {f : σ →₀ ℕ // f.degree = n} :=
    (Finsupp.finite_of_degree_eq (σ := σ) n).to_subtype
  Fintype.ofFinite _

/-- The index type of exponent vectors of multidegree `d`: the `h`-block has total degree
`d h`. -/
private abbrev BlockIdx (m N : ℕ) (d : Fin m → ℕ) :=
  (h : Fin m) → {v : Fin N →₀ ℕ // v.degree = d h}

/-- The exponent vector in `Fin m × Fin N` variables associated to an element of `BlockIdx`. -/
private noncomputable def expOf {m N : ℕ} (d : Fin m → ℕ) (V : BlockIdx m N d) :
    (Fin m × Fin N) →₀ ℕ :=
  Finsupp.uncurry (Finsupp.equivFunOnFinite.symm (fun h => (V h).val))

private lemma expOf_apply {m N : ℕ} (d : Fin m → ℕ) (V : BlockIdx m N d) (h : Fin m)
    (i : Fin N) : expOf d V (h, i) = (V h).val i := by
  rw [expOf, Finsupp.uncurry_apply]
  simp only [Finsupp.coe_equivFunOnFinite_symm]

private lemma sum_expOf {m N : ℕ} (d : Fin m → ℕ) (V : BlockIdx m N d) (h : Fin m) :
    ∑ i, expOf d V (h, i) = d h := by
  simp only [expOf_apply, ← Finsupp.degree_eq_sum]
  exact (V h).property

private lemma degree_expOf {m N : ℕ} (d : Fin m → ℕ) (V : BlockIdx m N d) :
    (expOf d V).degree = ∑ h, d h := by
  rw [Finsupp.degree_eq_sum, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun h _ => sum_expOf d V h

private lemma expOf_injective {m N : ℕ} (d : Fin m → ℕ) :
    Function.Injective (expOf (N := N) d) := by
  intro V W hVW
  funext h
  apply Subtype.ext
  ext i
  have := congrArg (fun f : (Fin m × Fin N) →₀ ℕ => f (h, i)) hVW
  rwa [expOf_apply, expOf_apply] at this

private lemma card_blockIdx {m N : ℕ} (hN : 1 ≤ N) (d : Fin m → ℕ) :
    Fintype.card (BlockIdx m N d) = ∏ h, (d h + N - 1).choose (N - 1) := by
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro h _
  rw [← Nat.card_eq_fintype_card]
  rw [Commons.Algebra.MvPowerSeries.card_finsupp_degree_eq (Fin N) (d h)]
  simp only [Fintype.card_fin]
  have h1 : N + d h - 1 = d h + N - 1 := by omega
  rw [h1]
  exact Nat.choose_symm_of_eq_add (by omega : d h + N - 1 = d h + (N - 1))

/-! ## The linear forms and the associated monomial substitution -/

/-- The linear form `∑ k, Λ k i * X (h, k)` attached to the variable `(h,i)`. -/
private def linForms {m N : ℕ} (Λ : Matrix (Fin N) (Fin N) K) :
    (Fin m × Fin N) → MvPolynomial (Fin m × Fin N) K :=
  fun x => ∑ k : Fin N, MvPolynomial.C (Λ k x.2) * MvPolynomial.X (x.1, k)

private lemma aeval_linForms_monomial {m N : ℕ} (Λ : Matrix (Fin N) (Fin N) K)
    (u : (Fin m × Fin N) →₀ ℕ) :
    MvPolynomial.aeval (linForms Λ) (MvPolynomial.monomial u 1)
      = ∏ p : Fin m × Fin N, (linForms Λ p) ^ (u p) := by
  rw [MvPolynomial.aeval_monomial, map_one, one_mul]
  rw [Finsupp.prod_of_support_subset u (Finset.subset_univ _)
        (fun i k => (linForms Λ i) ^ k) (fun i _ => by rw [pow_zero])]

private lemma hl1_C_mul_X {m N : ℕ} (a : K) (p : Fin m × Fin N) :
    hl1 (MvPolynomial.C a * MvPolynomial.X p : MvPolynomial (Fin m × Fin N) K)
      = NumberField.house a := by
  rw [MvPolynomial.C_mul_X_eq_monomial, hl1_monomial]

private lemma hl1_linForms_le {m N : ℕ} (Λ : Matrix (Fin N) (Fin N) K) {H : ℝ}
    (hH : ∀ i j, NumberField.house (Λ i j) ≤ H) (p : Fin m × Fin N) :
    hl1 (linForms Λ p) ≤ N * H := by
  rw [linForms]
  calc hl1 (∑ k : Fin N, MvPolynomial.C (Λ k p.2) * MvPolynomial.X (p.1, k))
      ≤ ∑ k : Fin N, hl1 (MvPolynomial.C (Λ k p.2) * MvPolynomial.X (p.1, k)) :=
        hl1_sum_le _ _
    _ ≤ ∑ k : Fin N, H := Finset.sum_le_sum fun k _ => by
        rw [hl1_C_mul_X]; exact hH k p.2
    _ = N * H := by simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

private lemma house_coeff_prod_linForms_le {m N : ℕ} (Λ : Matrix (Fin N) (Fin N) K) {H : ℝ}
    (hH : ∀ i j, NumberField.house (Λ i j) ≤ H) (hH0 : 0 ≤ H)
    (u J : (Fin m × Fin N) →₀ ℕ) :
    NumberField.house (MvPolynomial.coeff J (∏ p : Fin m × Fin N, (linForms Λ p) ^ (u p)))
      ≤ (N * H) ^ u.degree := by
  classical
  have hNH : 0 ≤ (N : ℝ) * H := mul_nonneg (Nat.cast_nonneg N) hH0
  calc NumberField.house (MvPolynomial.coeff J (∏ p : Fin m × Fin N, (linForms Λ p) ^ (u p)))
      ≤ hl1 (∏ p : Fin m × Fin N, (linForms Λ p) ^ (u p)) := house_coeff_le_hl1 _ _
    _ ≤ ∏ p : Fin m × Fin N, hl1 ((linForms Λ p) ^ (u p)) := hl1_prod_le _ _
    _ ≤ ∏ p : Fin m × Fin N, (hl1 (linForms Λ p)) ^ (u p) :=
        Finset.prod_le_prod (fun _ _ => hl1_nonneg _) (fun p _ => hl1_pow_le _ _)
    _ ≤ ∏ p : Fin m × Fin N, (N * H) ^ (u p) := by
        refine Finset.prod_le_prod (fun _ _ => ?_) (fun p _ => ?_)
        · exact pow_nonneg (hl1_nonneg _) _
        · exact pow_le_pow_left₀ (hl1_nonneg _) (hl1_linForms_le Λ hH p) _
    _ = (N * H) ^ u.degree := by
        rw [Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_eq_sum]

/-! ## Integrality of the coefficients of the substituted monomial -/

private lemma isIntegral_coeff_prod_linForms {m N : ℕ} (Λ : Matrix (Fin N) (Fin N) K)
    {c : ℕ} (hint : ∀ i j, IsIntegral ℤ ((c : K) * Λ i j))
    (u J : (Fin m × Fin N) →₀ ℕ) :
    IsIntegral ℤ ((c : K) ^ u.degree *
      MvPolynomial.coeff J (∏ p : Fin m × Fin N, (linForms Λ p) ^ (u p))) := by
  classical
  let b : Fin N → Fin N → NumberField.RingOfIntegers K := fun k i => ⟨(c : K) * Λ k i, hint k i⟩
  let linFormsO : (Fin m × Fin N) → MvPolynomial (Fin m × Fin N) (NumberField.RingOfIntegers K) :=
    fun p => ∑ k : Fin N, MvPolynomial.C (b k p.2) * MvPolynomial.X (p.1, k)
  have hmap_linform : ∀ p, MvPolynomial.map (algebraMap (NumberField.RingOfIntegers K) K) (linFormsO p)
      = MvPolynomial.C (c : K) * linForms Λ p := by
    intro p
    simp only [linFormsO, linForms, map_sum, map_mul, map_C, map_X]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← mul_assoc, ← MvPolynomial.C_mul, ← NumberField.RingOfIntegers.coe_eq_algebraMap]
    simp only [b]
    rfl
  have hmap_prod : MvPolynomial.map (algebraMap (NumberField.RingOfIntegers K) K)
        (∏ p : Fin m × Fin N, (linFormsO p) ^ (u p))
      = ((c : K) ^ u.degree) • (∏ p : Fin m × Fin N, (linForms Λ p) ^ (u p)) := by
    rw [map_prod]
    simp only [map_pow]
    rw [Finset.prod_congr rfl (fun p _ => by rw [hmap_linform p])]
    rw [Finset.prod_congr rfl (fun p _ => mul_pow _ _ _)]
    rw [Finset.prod_mul_distrib]
    rw [Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_eq_sum]
    rw [← map_pow MvPolynomial.C]
    rw [Algebra.smul_def, MvPolynomial.algebraMap_eq]
  have hcoeff := congrArg (MvPolynomial.coeff J) hmap_prod
  rw [MvPolynomial.coeff_map] at hcoeff
  have hsmul : MvPolynomial.coeff J
        (((c : K) ^ u.degree) • (∏ p : Fin m × Fin N, (linForms Λ p) ^ (u p)))
      = (c : K) ^ u.degree *
          MvPolynomial.coeff J (∏ p : Fin m × Fin N, (linForms Λ p) ^ (u p)) := by
    rw [Algebra.smul_def, MvPolynomial.algebraMap_eq, MvPolynomial.coeff_C_mul]
  rw [hsmul] at hcoeff
  rw [← hcoeff]
  exact NumberField.RingOfIntegers.isIntegral_coe _

/-- Coefficient of the `Λ`-expansion of a monomial, as a multiple of the corresponding product
of linear forms. -/
private lemma coeff_aeval_linForms_monomial {m N : ℕ} (Λ : Matrix (Fin N) (Fin N) K)
    (u J : (Fin m × Fin N) →₀ ℕ) (r : K) :
    MvPolynomial.coeff J (MvPolynomial.aeval (linForms Λ) (MvPolynomial.monomial u r))
      = r * MvPolynomial.coeff J (∏ p : Fin m × Fin N, (linForms Λ p) ^ (u p)) := by
  rw [MvPolynomial.aeval_monomial]
  rw [Finsupp.prod_of_support_subset u (Finset.subset_univ _)
        (fun i k => (linForms Λ i) ^ k) (fun i _ => by rw [pow_zero])]
  rw [MvPolynomial.algebraMap_eq, MvPolynomial.coeff_C_mul]

/-- A bound for the coordinates of an algebraic integer in a `ℤ`-basis of `𝓞 K`, in terms of
the house of the element. -/
private theorem exists_coord_bound (K : Type*) [Field K] [NumberField K]
    [DecidableEq (K →+* ℂ)] :
    ∃ cK : ℝ, 0 < cK ∧ ∀ (α : NumberField.RingOfIntegers K) (i : K →+* ℂ),
      ‖((((NumberField.RingOfIntegers.basis K).repr α (NumberField.equivReindex K i)) : ℤ) : ℝ)‖
        ≤ cK * NumberField.house (algebraMap (NumberField.RingOfIntegers K) K α) := by
  classical
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, ∀ (α : NumberField.RingOfIntegers K) (i : K →+* ℂ),
      ‖(((NumberField.integralBasis K).reindex (NumberField.equivReindex K).symm).repr
          (algebraMap (NumberField.RingOfIntegers K) K α) i : ℂ)‖
        ≤ c₀ * NumberField.house (algebraMap (NumberField.RingOfIntegers K) K α) :=
    ⟨_, NumberField.house.basis_repr_norm_le_const_mul_house K⟩
  refine ⟨|c₀| + 1, by positivity, fun α i => ?_⟩
  have hkey : ((NumberField.integralBasis K).reindex (NumberField.equivReindex K).symm).repr
        (algebraMap (NumberField.RingOfIntegers K) K α) i
      = (((NumberField.RingOfIntegers.basis K).repr α (NumberField.equivReindex K i) : ℤ) : ℚ) := by
    rw [Module.Basis.repr_reindex_apply, NumberField.integralBasis_repr_apply]
    rfl
  calc ‖((((NumberField.RingOfIntegers.basis K).repr α (NumberField.equivReindex K i)) : ℤ) : ℝ)‖
      = ‖(((NumberField.integralBasis K).reindex (NumberField.equivReindex K).symm).repr
          (algebraMap (NumberField.RingOfIntegers K) K α) i : ℂ)‖ := by
        rw [hkey]
        push_cast
        simp
    _ ≤ c₀ * NumberField.house (algebraMap (NumberField.RingOfIntegers K) K α) := hc₀ α i
    _ ≤ (|c₀| + 1) * NumberField.house (algebraMap (NumberField.RingOfIntegers K) K α) := by
        apply mul_le_mul_of_nonneg_right _ (NumberField.house_nonneg _)
        exact le_trans (le_abs_self c₀) (le_add_of_nonneg_right zero_le_one)

theorem exists_flat_int_poly_le (K : Type*) [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    [Algebra K ℂ] [IsScalarTower ℚ K ℂ]
    {N : ℕ} (hN : 1 ≤ N) (Λ : Matrix (Fin N) (Fin N) K) (hΛ : Λ.det ≠ 0)
    (c : ℕ) (hc : 0 < c) (hint : ∀ i j, IsIntegral ℤ ((c : K) * Λ i j))
    (M : ℝ) (hM : 1 ≤ M) (hΛM : ∀ i j, ‖algebraMap K ℂ (Λ i j)‖ ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ {m : ℕ} (d : Fin m → ℕ) (hd : ∀ h, 0 < d h)
      (S : Finset ((Fin m × Fin N) →₀ ℕ))
      (hS : 2 * (Module.finrank ℚ K * S.card) < ∏ h, (d h + N - 1).choose (N - 1)),
      ∃ F : MvPolynomial (Fin m × Fin N) ℤ, F ≠ 0 ∧
        (∀ u ∈ F.support, ∀ h, ∑ i, u (h, i) = d h) ∧
        (∀ J ∈ S, MvPolynomial.coeff J
          (MvPolynomial.aeval (fun x : Fin m × Fin N =>
              ∑ k : Fin N, MvPolynomial.C (Λ k x.2) * MvPolynomial.X (x.1, k))
            (F.map (Int.castRingHom K))) = 0) ∧
        (∀ u, ‖((F.coeff u : ℤ) : ℝ)‖ ≤ C *
          (∏ h, (((d h + N - 1).choose (N - 1) : ℕ) : ℝ)) * (C * M) ^ (∑ h, d h)) := by
  classical
  haveI hC0 : CharZero K := algebraRat.charZero K
  have halg : (inferInstance : Algebra ℚ K) = DivisionRing.toRatAlgebra :=
    Rat.algebra_rat_subsingleton.elim _ _
  subst halg
  haveI : NumberField K := { to_charZero := hC0, to_finiteDimensional := ‹FiniteDimensional ℚ K› }
  haveI : DecidableEq (K →+* ℂ) := Classical.decEq _
  obtain ⟨cK, hcKpos, hcK⟩ := exists_coord_bound K
  set H : ℝ := (∑ p : Fin N × Fin N, NumberField.house (Λ p.1 p.2)) + 1 with hHdef
  have hH0 : 0 ≤ H := by
    rw [hHdef]
    have := Finset.sum_nonneg (s := Finset.univ)
      (f := fun p : Fin N × Fin N => NumberField.house (Λ p.1 p.2))
      (fun p _ => NumberField.house_nonneg _)
    linarith
  have hHle : ∀ i j, NumberField.house (Λ i j) ≤ H := by
    intro i j
    have h1 : NumberField.house (Λ i j) ≤ ∑ p : Fin N × Fin N, NumberField.house (Λ p.1 p.2) :=
      Finset.single_le_sum (f := fun p : Fin N × Fin N => NumberField.house (Λ p.1 p.2))
        (fun p _ => NumberField.house_nonneg _) (Finset.mem_univ (i, j))
    rw [hHdef]; linarith
  refine ⟨max 1 (max cK ((c : ℝ) * N * H)), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro m d hd S hS
  have hC1 : (1 : ℝ) ≤ max 1 (max cK ((c : ℝ) * N * H)) := le_max_left _ _
  have hcKle : cK ≤ max 1 (max cK ((c : ℝ) * N * H)) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hcNHle : (c : ℝ) * N * H ≤ max 1 (max cK ((c : ℝ) * N * H)) :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hP1 : (1 : ℝ) ≤ ∏ h, (((d h + N - 1).choose (N - 1) : ℕ) : ℝ) := by
    have key : ∀ h, (1 : ℝ) ≤ (((d h + N - 1).choose (N - 1) : ℕ) : ℝ) := by
      intro h
      have hpos : 0 < (d h + N - 1).choose (N - 1) := Nat.choose_pos (by omega)
      exact_mod_cast (Nat.succ_le_of_lt hpos)
    simpa using Finset.prod_le_prod (s := Finset.univ) (f := fun _ : Fin m => (1 : ℝ))
      (fun _ _ => zero_le_one) (fun h _ => key h)
  have hCM1 : (1 : ℝ) ≤ max 1 (max cK ((c : ℝ) * N * H)) * M := by nlinarith [hC1, hM]
  have hbound1 : (1 : ℝ) ≤ max 1 (max cK ((c : ℝ) * N * H)) *
      (∏ h, (((d h + N - 1).choose (N - 1) : ℕ) : ℝ)) *
      (max 1 (max cK ((c : ℝ) * N * H)) * M) ^ (∑ h, d h) := by
    refine one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC1 hP1)
      (one_le_pow₀ hCM1)
  by_cases hS0 : S.card = 0
  · have hSempty : S = ∅ := Finset.card_eq_zero.mp hS0
    have hNpos : 0 < N := hN
    let V0 : BlockIdx m N d := fun h => ⟨Finsupp.single ⟨0, hNpos⟩ (d h), by rw [Finsupp.degree_single]⟩
    refine ⟨MvPolynomial.monomial (expOf d V0) 1, ?_, ?_, ?_, ?_⟩
    · simpa [MvPolynomial.monomial_eq_zero] using one_ne_zero
    · intro u hu h
      rw [MvPolynomial.support_monomial] at hu
      rw [if_neg one_ne_zero, Finset.mem_singleton] at hu
      rw [hu]
      exact sum_expOf d V0 h
    · intro J hJ
      rw [hSempty] at hJ
      exact absurd hJ (Finset.notMem_empty J)
    · intro u
      have hcoeff : ‖(((MvPolynomial.coeff u (MvPolynomial.monomial (expOf d V0) 1) : ℤ)) : ℝ)‖ ≤ 1 := by
        rw [MvPolynomial.coeff_monomial]
        split_ifs <;> simp
      exact le_trans hcoeff hbound1
  · -- main case
    have hSpos : 0 < S.card := Nat.pos_of_ne_zero hS0
    set Adeg : ℕ := ∑ h, d h with hAdeg
    have hdA : ∀ V : BlockIdx m N d, (expOf d V).degree = Adeg := fun V => by rw [degree_expOf, hAdeg]
    have hInt : ∀ (J : (Fin m × Fin N) →₀ ℕ) (V : BlockIdx m N d),
        IsIntegral ℤ ((c : K) ^ Adeg *
          MvPolynomial.coeff J (∏ p : Fin m × Fin N, (linForms Λ p) ^ ((expOf d V) p))) := by
      intro J V
      rw [← hdA V]
      exact isIntegral_coeff_prod_linForms Λ hint (expOf d V) J
    let αof : ((Fin m × Fin N) →₀ ℕ) → BlockIdx m N d → NumberField.RingOfIntegers K := fun J =>
      NumberField.RingOfIntegers.restrict
        (fun V : BlockIdx m N d => (c : K) ^ Adeg * MvPolynomial.coeff J
          (∏ p : Fin m × Fin N, (linForms Λ p) ^ ((expOf d V) p)))
        (fun V => hInt J V)
    let Mmat : Matrix (↥S × (K →+* ℂ)) (BlockIdx m N d) ℤ := fun Jr V =>
      (NumberField.RingOfIntegers.basis K).repr (αof Jr.1 V) (NumberField.equivReindex K Jr.2)
    have hrows_lt : Fintype.card (↥S × (K →+* ℂ)) < Fintype.card (BlockIdx m N d) := by
      rw [Fintype.card_prod, Fintype.card_coe, NumberField.Embeddings.card K ℂ, card_blockIdx hN d]
      have h := hS
      rw [mul_comm (Module.finrank ℚ K) S.card] at h
      omega
    have hrows_pos : 0 < Fintype.card (↥S × (K →+* ℂ)) := by
      rw [Fintype.card_prod, Fintype.card_coe, NumberField.Embeddings.card K ℂ]
      exact Nat.mul_pos hSpos finrank_pos
    obtain ⟨t, htne, htker, htbound⟩ :=
      Int.Matrix.exists_ne_zero_int_vec_norm_le Mmat hrows_lt hrows_pos
    set F : MvPolynomial (Fin m × Fin N) ℤ :=
      ∑ V : BlockIdx m N d, MvPolynomial.monomial (expOf d V) (t V) with hFdef
    have hαcoe : ∀ (J : (Fin m × Fin N) →₀ ℕ) (V : BlockIdx m N d),
        (algebraMap (NumberField.RingOfIntegers K) K) (αof J V)
          = (c : K) ^ Adeg * MvPolynomial.coeff J
              (∏ p : Fin m × Fin N, (linForms Λ p) ^ ((expOf d V) p)) := by
      intro J V
      rw [← NumberField.RingOfIntegers.coe_eq_algebraMap]
      rfl
    -- matrix norm bound
    have hentry : ∀ (Jr : ↥S × (K →+* ℂ)) (V : BlockIdx m N d),
        ‖Mmat Jr V‖ ≤ cK * ((c : ℝ) * N * H) ^ Adeg := by
      intro Jr V
      have h := hcK (αof Jr.1 V) Jr.2
      refine le_trans h (mul_le_mul_of_nonneg_left ?_ hcKpos.le)
      rw [hαcoe Jr.1 V]
      rw [show (c : K) ^ Adeg = ((c ^ Adeg : ℕ) : K) by rw [Nat.cast_pow]]
      rw [NumberField.house_nat_mul]
      have h2 : NumberField.house (MvPolynomial.coeff Jr.1
            (∏ p : Fin m × Fin N, (linForms Λ p) ^ ((expOf d V) p))) ≤ ((N : ℝ) * H) ^ Adeg := by
        rw [← hdA V]
        exact house_coeff_prod_linForms_le Λ hHle hH0 (expOf d V) Jr.1
      calc ((c ^ Adeg : ℕ) : ℝ) * NumberField.house (MvPolynomial.coeff Jr.1
            (∏ p : Fin m × Fin N, (linForms Λ p) ^ ((expOf d V) p)))
          ≤ ((c ^ Adeg : ℕ) : ℝ) * ((N : ℝ) * H) ^ Adeg :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = ((c : ℝ) * N * H) ^ Adeg := by
            rw [Nat.cast_pow, ← mul_pow]
            congr 1
            ring
    have hMnorm : ‖Mmat‖ ≤ max 1 (cK * ((c : ℝ) * N * H) ^ Adeg) := by
      rw [Matrix.norm_le_iff (show (0 : ℝ) ≤ max 1 (cK * ((c : ℝ) * N * H) ^ Adeg) by positivity)]
      intro Jr V
      exact le_trans (hentry Jr V) (le_max_right _ _)
    have hmb : max 1 ‖Mmat‖ ≤
        max 1 (max cK ((c : ℝ) * N * H)) *
          (max 1 (max cK ((c : ℝ) * N * H)) * M) ^ Adeg := by
      have hX0 : 0 ≤ (c : ℝ) * N * H := by positivity
      have hXle : (c : ℝ) * N * H ≤ max 1 (max cK ((c : ℝ) * N * H)) * M := by
        nlinarith [hcNHle, hM, hC1]
      have h2 : cK * ((c : ℝ) * N * H) ^ Adeg ≤
          max 1 (max cK ((c : ℝ) * N * H)) *
            (max 1 (max cK ((c : ℝ) * N * H)) * M) ^ Adeg :=
        mul_le_mul hcKle (pow_le_pow_left₀ hX0 hXle Adeg) (pow_nonneg hX0 _)
          (le_trans hcKpos.le hcKle)
      have h1 : (1 : ℝ) ≤ max 1 (max cK ((c : ℝ) * N * H)) *
          (max 1 (max cK ((c : ℝ) * N * H)) * M) ^ Adeg :=
        one_le_mul_of_one_le_of_one_le hC1 (one_le_pow₀ hCM1)
      exact le_trans (max_le (le_max_left _ _) hMnorm) (max_le h1 h2)
    have hNpos : 0 < N := hN
    have hne : Nonempty (BlockIdx m N d) :=
      ⟨fun h => ⟨Finsupp.single ⟨0, hNpos⟩ (d h), by rw [Finsupp.degree_single]⟩⟩
    have hcardpos : (1 : ℝ) ≤ (Fintype.card (BlockIdx m N d) : ℝ) := by
      exact_mod_cast (Fintype.card_pos_iff.mpr hne)
    have hbase1 : (1 : ℝ) ≤ (Fintype.card (BlockIdx m N d) : ℝ) * max 1 ‖Mmat‖ :=
      one_le_mul_of_one_le_of_one_le hcardpos (le_max_left _ _)
    have hrows2 : 2 * Fintype.card (↥S × (K →+* ℂ)) < Fintype.card (BlockIdx m N d) := by
      rw [Fintype.card_prod, Fintype.card_coe, NumberField.Embeddings.card K ℂ, card_blockIdx hN d]
      have h := hS
      rw [mul_comm (Module.finrank ℚ K) S.card] at h
      omega
    have hθle : ((Fintype.card (↥S × (K →+* ℂ)) : ℝ) /
          ((Fintype.card (BlockIdx m N d) : ℝ) - (Fintype.card (↥S × (K →+* ℂ)) : ℝ))) ≤ 1 := by
      have hb : (0 : ℝ) < (Fintype.card (BlockIdx m N d) : ℝ) -
          (Fintype.card (↥S × (K →+* ℂ)) : ℝ) := by
        have h : (Fintype.card (↥S × (K →+* ℂ)) : ℝ) < (Fintype.card (BlockIdx m N d) : ℝ) := by
          exact_mod_cast hrows_lt
        linarith
      rw [div_le_one hb]
      have h : (2 : ℝ) * (Fintype.card (↥S × (K →+* ℂ)) : ℝ) < (Fintype.card (BlockIdx m N d) : ℝ) := by
        exact_mod_cast hrows2
      linarith
    have htbound' : ‖t‖ ≤ (Fintype.card (BlockIdx m N d) : ℝ) * max 1 ‖Mmat‖ := by
      have h2 := Real.rpow_le_rpow_of_exponent_le hbase1 hθle
      rw [Real.rpow_one] at h2
      exact le_trans htbound h2
    have htfinal : ‖t‖ ≤ max 1 (max cK ((c : ℝ) * N * H)) *
        (∏ h, (((d h + N - 1).choose (N - 1) : ℕ) : ℝ)) *
        (max 1 (max cK ((c : ℝ) * N * H)) * M) ^ (∑ h, d h) := by
      calc ‖t‖ ≤ (Fintype.card (BlockIdx m N d) : ℝ) * max 1 ‖Mmat‖ := htbound'
        _ = (∏ h, (((d h + N - 1).choose (N - 1) : ℕ) : ℝ)) * max 1 ‖Mmat‖ := by
              rw [card_blockIdx hN d, Nat.cast_prod]
        _ ≤ (∏ h, (((d h + N - 1).choose (N - 1) : ℕ) : ℝ)) *
              (max 1 (max cK ((c : ℝ) * N * H)) *
                (max 1 (max cK ((c : ℝ) * N * H)) * M) ^ Adeg) :=
              mul_le_mul_of_nonneg_left hmb (by positivity)
        _ = max 1 (max cK ((c : ℝ) * N * H)) *
              (∏ h, (((d h + N - 1).choose (N - 1) : ℕ) : ℝ)) *
              (max 1 (max cK ((c : ℝ) * N * H)) * M) ^ Adeg := by ring
        _ = max 1 (max cK ((c : ℝ) * N * H)) *
              (∏ h, (((d h + N - 1).choose (N - 1) : ℕ) : ℝ)) *
              (max 1 (max cK ((c : ℝ) * N * H)) * M) ^ (∑ h, d h) := by rw [hAdeg]
    -- the vanishing condition
    have hzero : ∀ J ∈ S, MvPolynomial.coeff J
        (MvPolynomial.aeval (linForms Λ) (F.map (Int.castRingHom K))) = 0 := by
      intro J hJ
      have hsum0 : ∑ V : BlockIdx m N d, ((t V : ℤ) : K) *
          MvPolynomial.coeff J (∏ p : Fin m × Fin N, (linForms Λ p) ^ ((expOf d V) p)) = 0 := by
        have hrepr0 : (∑ V : BlockIdx m N d, t V • αof J V) = 0 := by
          apply (NumberField.RingOfIntegers.basis K).repr.injective
          rw [map_zero]
          ext l
          rw [Finsupp.zero_apply]
          have h1 : ((NumberField.RingOfIntegers.basis K).repr
                (∑ V : BlockIdx m N d, t V • αof J V)) l
              = ∑ V : BlockIdx m N d,
                  t V * ((NumberField.RingOfIntegers.basis K).repr (αof J V)) l := by
            rw [map_sum]
            simp only [map_zsmul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
              smul_eq_mul]
          rw [h1]
          have h2 := congrFun htker (⟨J, hJ⟩, (NumberField.equivReindex K).symm l)
          simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at h2
          rw [← h2]
          refine Finset.sum_congr rfl fun V _ => ?_
          simp only [Mmat, NumberField.equivReindex, Equiv.apply_symm_apply]
          ring
        have hcoe : (algebraMap (NumberField.RingOfIntegers K) K)
              (∑ V : BlockIdx m N d, t V • αof J V)
            = (c : K) ^ Adeg * ∑ V : BlockIdx m N d, ((t V : ℤ) : K) *
                MvPolynomial.coeff J (∏ p : Fin m × Fin N, (linForms Λ p) ^ ((expOf d V) p)) := by
          have step : ∀ V : BlockIdx m N d, (t V) •
                (algebraMap (NumberField.RingOfIntegers K) K) (αof J V)
              = ((t V : ℤ) : K) * ((c : K) ^ Adeg * MvPolynomial.coeff J
                  (∏ p : Fin m × Fin N, (linForms Λ p) ^ ((expOf d V) p))) := by
            intro V
            rw [hαcoe J V, zsmul_eq_mul]
          calc (algebraMap (NumberField.RingOfIntegers K) K) (∑ V : BlockIdx m N d, t V • αof J V)
              = ∑ V : BlockIdx m N d, (t V) •
                  (algebraMap (NumberField.RingOfIntegers K) K) (αof J V) := by
                rw [map_sum]
                exact Finset.sum_congr rfl fun V _ => by rw [map_zsmul]
            _ = ∑ V : BlockIdx m N d, ((t V : ℤ) : K) * ((c : K) ^ Adeg * MvPolynomial.coeff J
                  (∏ p : Fin m × Fin N, (linForms Λ p) ^ ((expOf d V) p))) :=
                Finset.sum_congr rfl fun V _ => step V
            _ = (c : K) ^ Adeg * ∑ V : BlockIdx m N d, ((t V : ℤ) : K) * MvPolynomial.coeff J
                  (∏ p : Fin m × Fin N, (linForms Λ p) ^ ((expOf d V) p)) := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun V _ => by ring
        have h0 := congrArg (algebraMap (NumberField.RingOfIntegers K) K) hrepr0
        rw [map_zero, hcoe] at h0
        exact (mul_eq_zero.mp h0).resolve_left (pow_ne_zero _ (show (c : K) ≠ 0 by
          exact_mod_cast hc.ne'))
      have hcoeff : MvPolynomial.coeff J
            (MvPolynomial.aeval (linForms Λ) (F.map (Int.castRingHom K)))
          = ∑ V : BlockIdx m N d, ((t V : ℤ) : K) *
              MvPolynomial.coeff J (∏ p : Fin m × Fin N, (linForms Λ p) ^ ((expOf d V) p)) := by
        rw [hFdef, map_sum, map_sum, MvPolynomial.coeff_sum]
        exact Finset.sum_congr rfl fun V _ => by
          rw [MvPolynomial.map_monomial]
          exact coeff_aeval_linForms_monomial Λ (expOf d V) J ((t V : ℤ) : K)
      rw [hcoeff, hsum0]
    refine ⟨F, ?_, ?_, ?_, ?_⟩
    · obtain ⟨V0, hV0⟩ : ∃ V, t V ≠ 0 := by
        by_contra h
        simp only [not_exists, not_not] at h
        exact htne (funext h)
      have hcoeff : MvPolynomial.coeff (expOf d V0) F = t V0 := by
        rw [hFdef, MvPolynomial.coeff_sum]
        rw [Finset.sum_eq_single V0]
        · rw [MvPolynomial.coeff_monomial, if_pos rfl]
        · intro V _ hVne
          rw [MvPolynomial.coeff_monomial, if_neg]
          intro h; exact hVne (expOf_injective d h)
        · intro h; exact absurd (Finset.mem_univ V0) h
      intro hF0
      rw [hF0, MvPolynomial.coeff_zero] at hcoeff
      exact hV0 hcoeff.symm
    · intro u hu h
      rw [MvPolynomial.mem_support_iff] at hu
      have hcoeff_u : MvPolynomial.coeff u F = ∑ V, (if expOf d V = u then t V else 0) := by
        rw [hFdef, MvPolynomial.coeff_sum]
        apply Finset.sum_congr rfl; intro V _
        rw [MvPolynomial.coeff_monomial]
      obtain ⟨V, hV⟩ : ∃ V, expOf d V = u := by
        by_contra hh
        simp only [not_exists] at hh
        apply hu
        rw [hcoeff_u]
        exact Finset.sum_eq_zero fun V _ => by rw [if_neg (hh V)]
      rw [← hV]
      exact sum_expOf d V h
    · intro J hJ
      have h1 := hzero J hJ
      rwa [show (fun x : Fin m × Fin N =>
            ∑ k : Fin N, MvPolynomial.C (Λ k x.2) * MvPolynomial.X (x.1, k)) = linForms Λ from rfl]
    · intro u
      by_cases hu : ∃ V : BlockIdx m N d, expOf d V = u
      · obtain ⟨V0, hV0⟩ := hu
        have hcoeff : MvPolynomial.coeff u F = t V0 := by
          rw [hFdef, MvPolynomial.coeff_sum]
          rw [Finset.sum_eq_single V0]
          · rw [MvPolynomial.coeff_monomial, if_pos hV0]
          · intro V _ hVne
            rw [MvPolynomial.coeff_monomial, if_neg]
            intro h; exact hVne (expOf_injective d (h.trans hV0.symm))
          · intro h; exact absurd (Finset.mem_univ V0) h
        rw [hcoeff]
        refine le_trans ?_ htfinal
        simpa only [Real.norm_eq_abs, Int.norm_eq_abs] using norm_le_pi_norm t V0
      · have hcoeff : MvPolynomial.coeff u F = 0 := by
          rw [hFdef, MvPolynomial.coeff_sum]
          exact Finset.sum_eq_zero fun V _ => by
            rw [MvPolynomial.coeff_monomial, if_neg]
            intro h; exact hu ⟨V, h⟩
        rw [hcoeff]
        simp only [Int.cast_zero, norm_zero]
        exact le_trans zero_le_one hbound1

end

end Commons.Algebra.MvPolynomial
