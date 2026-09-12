import Mathlib
import Submission.Commons.NumberTheory.NumberField.model_parameters_strict
import Submission.Commons.NumberTheory.NumberField.model_parameters_bounds
import Submission.Commons.NumberTheory.NumberField.coefficient_bound_estimate
import Submission.Commons.NumberTheory.NumberField.one_le_rootDiscr
import Submission.Commons.NumberTheory.NumberField.choose_two_mul_sub_one
import Submission.Commons.NumberTheory.NumberField.exists_uniform_ringOfIntegers_basis_house_le_2000
import Submission.Commons.NumberTheory.NumberField.exists_wellPoised_point_bounded
import Submission.Commons.NumberTheory.NumberField.small_relations_of_wellPoised

/-!
# Small algebraic models of number fields

Assembling the proof of `Commons.NumberTheory.NumberField.small_algebraic_model`, following
J.-M. Couveignes, *Enumerating number fields*, Annals of Math. 192 (2020).

The construction is:

* choose `r = d` with `2(n-1)(r+1) < (2r choose r) ≤ 32 n (r+1)` (Couveignes' §4 parameters);
* take a short `ℤ`-basis `ω` of `𝓞 K` with house `≤ n^2000 · δ^2000` (Minkowski's second theorem
  plus the fact that pairwise products of `⌈n/2⌉` short elements span `𝓞 K`);
* use the interpolation/box argument (`grid_eval_ne_zero`) to find a *well poised* tuple
  `κ : Fin r → 𝓞 K` — i.e. such that the jet evaluation map
  `f ↦ (f(κ), ∂₁f(κ), …, ∂ᵣf(κ))` from `ℚ[x₁,…,xᵣ]_{≤d}` is surjective — with
  `house (κ j) ≤ d·n·(r+1)·n^2000·δ^2000`;
* extract `r` small relations `Eᵢ ∈ ℤ[x₁,…,xᵣ]` of degree `≤ d`, from the lattice of relations
  `ℒ = {E ∈ ℤ[x]_{≤d} : E(κ) = 0}` using Minkowski's second theorem; the well poisedness gives
  that the gradients of the `ℓ - n + 1` smallest relations span, so a codimension count in
  `L = ℒ ⊗ ℚ` (of dimension `ℓ = (d+r choose r) - n`) produces `r` of them with invertible
  Jacobian.
-/

open scoped NumberField BigOperators

namespace Commons.NumberTheory.NumberField

noncomputable section

theorem small_algebraic_model :
    ∃ Q > 0, ∀ n ≥ Q, ∀ (K : Type*) [Field K] [NumberField K],
      Module.finrank ℚ K = n →
      ∃ r d : ℕ, (r : ℝ) ≤ Q * Real.log n ∧ (d : ℝ) ≤ Q * Real.log n ∧
        ((d + r).choose r : ℝ) ≤ Q * (n : ℝ) * Real.log n ∧
        ∃ E : Fin r → MvPolynomial (Fin r) ℤ,
          (∀ i, (E i).totalDegree ≤ d) ∧
          (∀ i j, |(E i).coeff j| ≤ ((n : ℝ) * NumberField.rootDiscr K) ^ (Q * Real.log n)) ∧
          ∃ φ : MvPolynomial (Fin r) ℚ →ₐ[ℚ] K, Function.Surjective φ ∧
            (∀ i, φ ((E i).map (algebraMap ℤ ℚ)) = 0) ∧
            IsUnit (φ (Matrix.det fun i j => MvPolynomial.pderiv j ((E i).map (algebraMap ℤ ℚ)))) := by
  refine ⟨10 ^ 8, by norm_num, ?_⟩
  intro n hn K _ _ hfin
  have hn100 : 100 ≤ n := by
    have : (10 : ℕ) ^ 8 ≤ n := by exact_mod_cast hn
    omega
  obtain ⟨r, hstrict, hbinom, hr6, hrlog⟩ := model_parameters_strict n hn100
  obtain ⟨hrQ, hCQ⟩ := model_parameters_bounds n r hn100 hbinom hrlog
  have hrpos : 1 ≤ r := by omega
  have hdpos : 0 < r := by omega
  -- the interpolation hypothesis
  have hinterp : (n - 1) * (r + 1) < (r + r - 1).choose r := by
    have hid := choose_two_mul_sub_one r hrpos
    have h2 : 2 * ((n - 1) * (r + 1)) < 2 * ((r + r - 1).choose r) := by
      rw [hid]
      simpa [mul_assoc] using hstrict
    exact Nat.lt_of_mul_lt_mul_left h2
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have h10 : ((10 ^ 8 : ℕ) : ℝ) = 10 ^ 8 := by norm_num
  have hrQ' : (r : ℝ) ≤ ((10 ^ 8 : ℕ) : ℝ) * Real.log n := by
    rw [h10]
    have := hrQ
    nlinarith
  have hCQ' : ((r + r).choose r : ℝ) ≤ ((10 ^ 8 : ℕ) : ℝ) * (n : ℝ) * Real.log n := by
    rw [h10]
    have := hCQ
    nlinarith [show (0:ℝ) ≤ (n:ℝ) by positivity]
  refine ⟨r, r, hrQ', hrQ', hCQ', ?_⟩
  -- the model
  obtain ⟨bb, hbb⟩ := exists_uniform_ringOfIntegers_basis_house_le_2000 K
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K)) = n := by
    rw [← Module.finrank_eq_card_chooseBasisIndex ℤ (NumberField.RingOfIntegers K),
      NumberField.RingOfIntegers.rank K, hfin]
  let e : Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K) ≃ Fin n :=
    Fintype.equivFinOfCardEq hcard
  let b : Module.Basis (Fin n) ℤ (NumberField.RingOfIntegers K) := bb.reindex e
  have hR : ∀ i : Fin n,
      NumberField.house (((b i : NumberField.RingOfIntegers K) : K)) ≤
        (n : ℝ) ^ (2000 : ℝ) * NumberField.rootDiscr K ^ (2000 : ℝ) := by
    intro i
    have h1 : b i = bb (e.symm i) := by rw [Module.Basis.reindex_apply]
    rw [h1]
    have h2 := hbb (e.symm i)
    rw [hfin] at h2
    exact h2
  -- the well poised tuple
  obtain ⟨κ, hκhouse, hκwp⟩ :=
    exists_wellPoised_point_bounded K n r r hfin b
      ((n : ℝ) ^ (2000 : ℝ) * NumberField.rootDiscr K ^ (2000 : ℝ)) hR hdpos hinterp
  -- the relations
  obtain ⟨E, hEdeg, hEcoeff, hEzero, hEunit⟩ :=
    small_relations_of_wellPoised K n r r hfin κ
      ((r : ℝ) * n * (r + 1) * ((n : ℝ) ^ (2000 : ℝ) * NumberField.rootDiscr K ^ (2000 : ℝ)))
      (by intro j; simpa using hκhouse j) hκwp hdpos hrpos
  refine ⟨E, hEdeg, ?_, ?_⟩
  · -- coefficient bound
    have hδ : 1 ≤ NumberField.rootDiscr K := one_le_rootDiscr K
    intro i j
    have h1 := coefficient_bound_estimate n r hn100 (NumberField.rootDiscr K) hδ hrlog
    have hpow : (n : ℝ) ^ (2000 : ℝ) * NumberField.rootDiscr K ^ (2000 : ℝ)
        = (n : ℝ) ^ 2000 * NumberField.rootDiscr K ^ 2000 := by
      simp [Real.rpow_natCast]
    rw [← hpow] at h1
    simp only [Nat.cast_add, Nat.cast_one] at h1 hEcoeff
    refine (hEcoeff i j).trans (le_trans h1 ?_)
    apply Real.rpow_le_rpow_of_exponent_le ?_ ?_
    · have h2 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
      nlinarith
    · nlinarith
  · -- the algebra map
    refine ⟨MvPolynomial.aeval (fun j : Fin r => (((κ j : NumberField.RingOfIntegers K) : K))),
      ?_, hEzero, hEunit⟩
    intro x
    obtain ⟨f, _, hfval, _⟩ := hκwp (x, fun _ => 0)
    exact ⟨f, hfval⟩

end

end Commons.NumberTheory.NumberField
