import Mathlib
import Submission.Work.FunctionalEquations.FourierSeriesHelpers
import Submission.Work.FunctionalEquations.CoeffsSeminormDecayFamily

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

noncomputable section

/-!
# Polynomial growth of the Schwartz seminorms of a Fourier-transformed family

This file proves `Work.FunctionalEquations.SeminormFourierGrowth`: if a family
`u m` of Schwartz functions on `R^n`, indexed by `m : Set.Ici k₀`, has Schwartz seminorms of
every order growing at most polynomially in `m`, then the same is true of the family of Fourier
transforms `(u m)^`.

The two ingredients are

* `Work.FunctionalEquations.coeffsSeminormDecay_fourierSeminorm` (from
  `CoeffsSeminormDecayFamily`): for every order `(k, l)` the seminorm
  `SchwartzMap.seminorm ℂ k l (f̂)` is bounded by a constant times a *finite* supremum
  `s.sup (schwartzSeminormFamily ℂ E ℂ) f` of Schwartz seminorms of `f`
  (continuity of the Fourier transform together with `Seminorm.bound_of_continuous`);
* the bookkeeping lemma `finset_sup_schwartzSeminorm_le` below: a finite supremum of
  Schwartz seminorms of a polynomially bounded family is again polynomially bounded, since it
  is bounded by the (finite) sum of the individual bounds, and a finite sum of polynomials in
  `m` is bounded by a single constant times a single power of `m`.
-/

/-- A finite supremum of Schwartz seminorms of a polynomially bounded family of Schwartz
functions is again polynomially bounded. -/
lemma finset_sup_schwartzSeminorm_le {n : ℕ} [NeZero n] {k₀ : ℕ}
    (v : Set.Ici k₀ → 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (hv : ∀ i : ℕ × ℕ, ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ m : Set.Ici k₀,
        (SchwartzMap.seminorm ℂ i.1 i.2) (v m) ≤ C * ((m.1 : ℝ) + 1) ^ N)
    (s : Finset (ℕ × ℕ)) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ m : Set.Ici k₀,
      (s.sup (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin n)) ℂ)) (v m)
        ≤ C * ((m.1 : ℝ) + 1) ^ N := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · refine ⟨0, 0, le_rfl, fun m => ?_⟩
    simp
  choose Cf Nf hCf using hv
  refine ⟨∑ i ∈ s, Cf i, s.sup' hs Nf, Finset.sum_nonneg (fun i _ => (hCf i).1), fun m => ?_⟩
  have hbase1 : 1 ≤ (m.1 : ℝ) + 1 := by
    have h0 : (0 : ℝ) ≤ (m.1 : ℝ) := Nat.cast_nonneg _
    linarith
  have hbase0 : (0 : ℝ) ≤ (m.1 : ℝ) + 1 := le_trans zero_le_one hbase1
  refine Seminorm.finset_sup_apply_le
    (mul_nonneg (Finset.sum_nonneg fun i _ => (hCf i).1) (pow_nonneg hbase0 _)) fun i hi => ?_
  have hNle : Nf i ≤ s.sup' hs Nf := Finset.le_sup' Nf hi
  have hCle : Cf i ≤ ∑ j ∈ s, Cf j :=
    Finset.single_le_sum (fun j _ => (hCf j).1) hi
  calc (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin n)) ℂ i) (v m)
      = (SchwartzMap.seminorm ℂ i.1 i.2) (v m) := rfl
    _ ≤ Cf i * ((m.1 : ℝ) + 1) ^ (Nf i) := (hCf i).2 m
    _ ≤ (∑ j ∈ s, Cf j) * ((m.1 : ℝ) + 1) ^ (s.sup' hs Nf) :=
        mul_le_mul hCle (pow_le_pow_right₀ hbase1 hNle) (pow_nonneg hbase0 _)
          (Finset.sum_nonneg fun j _ => (hCf j).1)

/-- **Polynomial growth of the Schwartz seminorms is preserved by the Fourier transform.**
If every Schwartz seminorm of the family `u` grows at most polynomially in the index `m`, then
the same holds for the family of Fourier transforms. -/
theorem SeminormFourierGrowth {n : ℕ} [NeZero n] {k₀ : ℕ}
    (u : Set.Ici k₀ → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ)
    (hu : ∀ k l : ℕ, ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ m : Set.Ici k₀,
        (SchwartzMap.seminorm ℂ k l) (u m) ≤ C * ((m.1 : ℝ) + 1) ^ N) :
    ∀ k l : ℕ, ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ m : Set.Ici k₀,
      (SchwartzMap.seminorm ℂ k l)
          (FourierTransform.fourierCLM ℂ (SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) (u m))
        ≤ C * ((m.1 : ℝ) + 1) ^ N := by
  intro k l
  obtain ⟨s, Cf, hCf, hle⟩ := coeffsSeminormDecay_fourierSeminorm (n := n) k l
  obtain ⟨Cg, N, hCg, hg⟩ :=
    finset_sup_schwartzSeminorm_le (v := u) (fun i => hu i.1 i.2) s
  refine ⟨Cf * Cg, N, mul_nonneg hCf hCg, fun m => ?_⟩
  calc (SchwartzMap.seminorm ℂ k l)
        (FourierTransform.fourierCLM ℂ (SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) (u m))
      ≤ Cf * (s.sup (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin n)) ℂ)) (u m) :=
        hle (u m)
    _ ≤ Cf * (Cg * ((m.1 : ℝ) + 1) ^ N) := mul_le_mul_of_nonneg_left (hg m) hCf
    _ = Cf * Cg * ((m.1 : ℝ) + 1) ^ N := by ring

end

end Work.FunctionalEquations
