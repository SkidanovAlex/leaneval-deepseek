import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Analysis.Polynomial.Norm
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Submission.Commons.NumberTheory.NumberField.Completion.ringOfIntegers_dense_in_adicIntegers

open scoped NumberField Valued
open IsDedekindDomain.HeightOneSpectrum
open Filter Set Topology

set_option autoImplicit false

namespace Commons.NumberTheory.NumberField.Completion

/-- Density of `K` in the completion, expressed in terms of the norm: every element of the
completion is arbitrarily well approximated by an element of `K`. -/
lemma exists_alg_sub_norm_lt {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : K, ‖algebraMap K (v.adicCompletion K) a - x‖ < ε := by
  have hx : x ∈ closure (Set.range (algebraMap K (v.adicCompletion K))) := by
    rw [(IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 K) K v).closure_eq]
    trivial
  obtain ⟨y, hyb, hyr⟩ := (mem_closure_iff_nhds.mp hx) (Metric.ball x ε)
    (Metric.ball_mem_nhds x hε)
  obtain ⟨a, rfl⟩ := hyr
  refine ⟨a, ?_⟩
  rw [← dist_eq_norm]
  exact hyb

/-- Polynomials over a number field `K` are dense in polynomials over the completion `Q.adicCompletion K`
in the coefficient sup-norm: for every `f` over the completion, every `n ≥ f.natDegree` and every
`ε > 0` there is `g ∈ K[X]` of degree at most `n` with `(f - g).supNorm < ε`, where `g` is viewed
in `(Q.adicCompletion K)[X]` via `Polynomial.map (algebraMap K _)`. -/
theorem exists_polynomial_map_close_adicCompletion {K : Type*} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (f : Polynomial (Q.adicCompletion K)) (n : ℕ) (hdeg : f.natDegree ≤ n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : Polynomial K, g.natDegree ≤ n ∧
      (f - g.map (algebraMap K (Q.adicCompletion K))).supNorm < ε := by
  classical
  choose a ha using fun i : ℕ => exists_alg_sub_norm_lt Q (f.coeff i) hε
  let g : Polynomial K := ∑ i ∈ Finset.range (n+1), Polynomial.monomial i (a i)
  have hgcoeff : ∀ m : ℕ, g.coeff m = if m ≤ n then a m else 0 := by
    intro m
    simp only [g]
    rw [← Polynomial.lcoeff_apply, map_sum]
    simp only [Polynomial.lcoeff_apply, Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_range, Nat.lt_succ_iff]
  have hgdeg : g.natDegree ≤ n := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [hgcoeff m]
    exact if_neg (by omega)
  refine ⟨g, hgdeg, ?_⟩
  have hcoeff : ∀ k : ℕ,
      ‖(f - g.map (algebraMap K (Q.adicCompletion K))).coeff k‖ < ε := by
    intro k
    rw [Polynomial.coeff_sub, Polynomial.coeff_map, hgcoeff k]
    by_cases hk : k ≤ n
    · rw [if_pos hk, norm_sub_rev]
      exact ha k
    · rw [if_neg hk, map_zero, sub_zero]
      have hfk : f.coeff k = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hfk, norm_zero]
      exact hε
  obtain ⟨k, hk⟩ := Polynomial.exists_eq_supNorm (f - g.map (algebraMap K (Q.adicCompletion K)))
  rw [hk]
  exact hcoeff k

end Commons.NumberTheory.NumberField.Completion