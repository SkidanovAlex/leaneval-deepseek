import Mathlib

/-!
# Polynomial lemmas for the DSNORM area

Elementary facts about evaluating homogeneous polynomials in elements of an ideal:

* `Work.DSNORM.finsupp_prod_pow_mem_pow`: a product of `s.degree` elements of an ideal (with
  repetitions recorded by `s : ι →₀ ℕ`) lies in the `s.degree`-th power of the ideal.
* `Work.DSNORM.eval_mem_pow_of_isHomogeneous`: the value at `x` of a homogeneous polynomial of
  degree `n` whose values `x i` lie in an ideal `I` lies in `I ^ n`.
* `Work.DSNORM.eval_mem_pow_succ_of_coeff_mem`: if moreover all coefficients lie in `I`, the value
  lies in `I ^ (n + 1)`.
* `Work.DSNORM.exists_isHomogeneous_of_dvd`: in a polynomial ring over a field, a divisor of a
  homogeneous polynomial can be chosen homogeneous.
-/

namespace Work.DSNORM

open MvPolynomial

variable {A : Type*} [CommRing A] {ι : Type*}

/-- A product of `s.degree` elements of `I` (the exponent `s i` records how often `x i` occurs)
lies in `I ^ s.degree`. -/
theorem finsupp_prod_pow_mem_pow (I : Ideal A) (x : ι → A) (hx : ∀ i, x i ∈ I) (s : ι →₀ ℕ) :
    (∏ i ∈ s.support, x i ^ (s i)) ∈ I ^ s.degree := by
  classical
  have h := SetLike.prod_pow_mem_graded (A := fun n : ℕ => I ^ n) (F := s.support)
    (i := fun _ => 1) (n := fun i => s i) (g := x) (fun i _ => by simpa using hx i)
  simpa [Finsupp.degree_apply] using h

/-- The value at `x` of a homogeneous polynomial of degree `n` whose values `x i` lie in `I` lies
in `I ^ n`. -/
theorem eval_mem_pow_of_isHomogeneous (I : Ideal A) (x : ι → A) (hx : ∀ i, x i ∈ I) {n : ℕ}
    {P : MvPolynomial ι A} (hP : P.IsHomogeneous n) : MvPolynomial.eval x P ∈ I ^ n := by
  classical
  rw [MvPolynomial.as_sum P, map_sum]
  refine Submodule.sum_mem _ fun s hs => ?_
  rw [MvPolynomial.eval_monomial]
  have hdeg : s.degree = n := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hs) (hP.coeff_eq_zero h)
  rw [← hdeg]
  exact Ideal.mul_mem_left (I := I ^ s.degree) (P.coeff s) (finsupp_prod_pow_mem_pow I x hx s)

/-- If all coefficients of a homogeneous polynomial of degree `n` lie in `I`, then its value at
`x` (with `x i ∈ I`) lies in `I ^ (n + 1)`. -/
theorem eval_mem_pow_succ_of_coeff_mem (I : Ideal A) (x : ι → A) (hx : ∀ i, x i ∈ I) {n : ℕ}
    {P : MvPolynomial ι A} (hP : P.IsHomogeneous n) (h : ∀ s, P.coeff s ∈ I) :
    MvPolynomial.eval x P ∈ I ^ (n + 1) := by
  classical
  rw [MvPolynomial.as_sum P, map_sum]
  refine Submodule.sum_mem _ fun s hs => ?_
  rw [MvPolynomial.eval_monomial]
  have hdeg : s.degree = n := by
    by_contra h'
    exact (MvPolynomial.mem_support_iff.mp hs) (hP.coeff_eq_zero h')
  rw [← hdeg, pow_succ']
  exact Ideal.mul_mem_mul (h s) (finsupp_prod_pow_mem_pow I x hx s)

/-- In a polynomial ring over a field, a divisor of a homogeneous polynomial of degree `b` can be
chosen homogeneous (of degree `b - a`). -/
theorem exists_isHomogeneous_of_dvd {k : Type*} [Field k] {σ : Type*} {f g : MvPolynomial σ k}
    {a b : ℕ} (hf : f.IsHomogeneous a) (hf0 : f ≠ 0) (hg : g.IsHomogeneous b) (h : f ∣ g) :
    ∃ R : MvPolynomial σ k, R.IsHomogeneous (b - a) ∧ g = f * R := by
  classical
  rcases eq_or_ne g 0 with hg0 | hg0
  · exact ⟨0, MvPolynomial.isHomogeneous_zero σ k _, by rw [hg0, mul_zero]⟩
  · obtain ⟨R₀, rfl⟩ := h
    have hR₀0 : R₀ ≠ 0 := fun h0 => hg0 (by rw [h0, mul_zero])
    have hmem : f * R₀ ∈ MvPolynomial.homogeneousSubmodule σ k b := hg
    have hn : b - a ≤ R₀.totalDegree := by
      have hmul := MvPolynomial.totalDegree_mul_of_isDomain (σ := σ) hf0 hR₀0
      rw [MvPolynomial.IsHomogeneous.totalDegree hf hf0,
        MvPolynomial.IsHomogeneous.totalDegree hg hg0] at hmul
      omega
    have hstep : ∀ i ∈ Finset.range (R₀.totalDegree + 1), i ≠ b - a →
        MvPolynomial.homogeneousComponent i R₀ = 0 := by
      intro i hi hib
      have hai : a + i ≠ b := by omega
      have h1 : MvPolynomial.homogeneousComponent (a + i) (f * R₀) = 0 := by
        rw [MvPolynomial.homogeneousComponent_of_mem hmem, if_neg hai]
      have hterm : ∀ j ∈ Finset.range (R₀.totalDegree + 1),
          MvPolynomial.homogeneousComponent (a + i) (f * MvPolynomial.homogeneousComponent j R₀)
            = if j = i then f * MvPolynomial.homogeneousComponent j R₀ else 0 := by
        intro j _
        rw [MvPolynomial.homogeneousComponent_of_mem]
        · by_cases hji : j = i
          · rw [if_pos (show a + i = a + j by omega), if_pos hji]
          · rw [if_neg (show a + i ≠ a + j by omega), if_neg hji]
        · exact MvPolynomial.homogeneousSubmodule_mul a j
            (Submodule.mul_mem_mul ((MvPolynomial.mem_homogeneousSubmodule a f).mpr hf)
              ((MvPolynomial.mem_homogeneousSubmodule j _).mpr
                (MvPolynomial.homogeneousComponent_isHomogeneous j R₀)))
      have h2 : MvPolynomial.homogeneousComponent (a + i) (f * R₀)
          = f * MvPolynomial.homogeneousComponent i R₀ := by
        conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent R₀]
        rw [Finset.mul_sum, map_sum, Finset.sum_congr rfl hterm, Finset.sum_eq_single i]
        · rw [if_pos rfl]
        · intro j _ hji
          rw [if_neg hji]
        · intro hnot
          exact absurd hi hnot
      rw [h2] at h1
      exact (mul_eq_zero.mp h1).resolve_left hf0
    have hterm2 : ∀ j ∈ Finset.range (R₀.totalDegree + 1),
        f * MvPolynomial.homogeneousComponent j R₀
          = if j = b - a then f * MvPolynomial.homogeneousComponent (b - a) R₀ else 0 := by
      intro j hj
      by_cases hj' : j = b - a
      · rw [if_pos hj', hj']
      · rw [if_neg hj', hstep j hj hj', mul_zero]
    refine ⟨MvPolynomial.homogeneousComponent (b - a) R₀,
      MvPolynomial.homogeneousComponent_isHomogeneous (b - a) R₀, ?_⟩
    conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent R₀]
    rw [Finset.mul_sum, Finset.sum_congr rfl hterm2, Finset.sum_eq_single (b - a)]
    · simp
    · intro j _ hji
      rw [if_neg hji]
    · intro hnot
      exact absurd (Finset.mem_range.mpr (by omega)) hnot

end Work.DSNORM
