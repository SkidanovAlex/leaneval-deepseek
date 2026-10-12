import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.LatticeParsevalDeriv
import Submission.Work.BoseFixR.LatticeParsevalGram
import Submission.Work.BoseFixR.LatticeParsevalNormSq
import Submission.Work.BoseFixR.LatticeParsevalSumSq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.LatticeW1sqParseval` — the lattice Parseval identity on the box

`LatticeW1sqParseval` is the Parseval/Plancherel identity for the characters of the
box lattice `(2π/ℓ)ℤ³` restricted to the truncated cube `Lab N` of mode labels, on the
box `boxL ℓ = {y | ∀ i, |y i| ≤ ℓ/2}` of volume `ℓ³`:

* `∫_{boxL ℓ} ‖Σ_{k≠0} c k e^{i⟪k,x⟫}‖² = ℓ³ Σ_{k≠0} ‖c k‖²`;
* `Σ_i ∫_{boxL ℓ} ‖∂_i (Σ_{k≠0} c k e^{i⟪k,·⟫})(x)‖² = ℓ³ Σ_{k≠0} ‖k‖² ‖c k‖²`.

Both are the same computation: expanding `‖Σ_k A k‖² = (Σ_{k,k'} A k conj(A k')).re`,
interchanging the finite sums with the integral, and evaluating the Gram matrix of the
characters `∫_{boxL ℓ} e^{i⟪k,x⟫} conj(e^{i⟪k',x⟫}) = ℓ³ δ_{k,k'}`
(`Work.BoseFixR.LatticeParsevalGram`).  The second identity additionally differentiates
the finite sum (`Work.BoseFixR.LatticeParsevalDeriv`), and uses
`Σ_i k_i² = ‖k‖²` (`Work.BoseFixR.LatticeParsevalSumSq`).

The generic double-sum identity behind the expansion of `‖·‖²` is
`Work.BoseFixR.LatticeParsevalNormSq`; the core Parseval lemma is
`integral_normSq_labChar_sum` below.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory Filter

namespace Work.BoseFixR

set_option maxHeartbeats 1000000

/-- A lattice character `x ↦ e^{i⟪k,x⟫}` is continuous. -/
lemma continuous_labChar (ℓ : ℝ) (N : ℕ) (k : Work.BoseBoxFock.Lab N) :
    Continuous (labChar ℓ N k) := by
  rw [show labChar ℓ N k = fun x : EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (Complex.I * ((inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k) x : ℝ) : ℂ))
      from rfl]
  fun_prop

/-- **Parseval for the lattice characters.**  For any finite family of complex coefficients
supported on a finite set `K` of mode labels, the `L²` norm squared of `Σ_{k∈K} c_k e^{i⟪k,·⟫}`
on the box is `ℓ³` times the sum of the squared moduli of the coefficients. -/
lemma integral_normSq_labChar_sum {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ)
    (K : Finset (Work.BoseBoxFock.Lab N)) (d : Work.BoseBoxFock.Lab N → ℂ) :
    ∫ x in boxL ℓ, ‖∑ k ∈ K, d k * labChar ℓ N k x‖ ^ 2 = ℓ ^ 3 * ∑ k ∈ K, ‖d k‖ ^ 2 := by
  have hfin : IsFiniteMeasure (volume.restrict (boxL ℓ)) := 
    isFiniteMeasure_restrict.mpr (volume_boxL_ne_top ℓ)
  have h1 : ∀ (j : Work.BoseBoxFock.Lab N) (x : EuclideanSpace ℝ (Fin 3)),
      ‖labChar ℓ N j x‖ = 1 := by
    intro j x
    rw [labChar, Complex.norm_exp_I_mul_ofReal]
  -- a product of two characters is integrable on the (finite measure) box
  have hchar_int : ∀ k k', Integrable
      (fun x => labChar ℓ N k x * star (labChar ℓ N k' x)) (volume.restrict (boxL ℓ)) := by
    intro k k'
    refine Integrable.of_bound ((continuous_labChar ℓ N k).mul
      (continuous_labChar ℓ N k').star).aestronglyMeasurable 1
      (Eventually.of_forall fun x => ?_)
    simp
  have hdouble_int : Integrable (fun x => ∑ k ∈ K, ∑ k' ∈ K,
      (d k * star (d k')) * (labChar ℓ N k x * star (labChar ℓ N k' x)))
      (volume.restrict (boxL ℓ)) :=
    integrable_finsetSum K fun k _ =>
      integrable_finsetSum K fun k' _ => (hchar_int k k').const_mul _
  -- expansion of `‖Σ‖²` as the real part of the double sum
  have hnorm : ∀ x : EuclideanSpace ℝ (Fin 3),
      ‖∑ k ∈ K, d k * labChar ℓ N k x‖ ^ 2
        = (∑ k ∈ K, ∑ k' ∈ K,
            (d k * star (d k')) * (labChar ℓ N k x * star (labChar ℓ N k' x))).re := by
    intro x
    rw [LatticeParsevalNormSq K (fun k => d k * labChar ℓ N k x)]
    congr 1
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
    rw [star_mul]
    ring
  -- the finite sums may be interchanged with the integral
  have hInt : ∫ x in boxL ℓ, (∑ k ∈ K, ∑ k' ∈ K,
      (d k * star (d k')) * (labChar ℓ N k x * star (labChar ℓ N k' x)))
      = ∑ k ∈ K, ∑ k' ∈ K, (d k * star (d k'))
          * (∫ x in boxL ℓ, labChar ℓ N k x * star (labChar ℓ N k' x)) := by
    rw [MeasureTheory.integral_finsetSum]
    · refine Finset.sum_congr rfl fun k hk => ?_
      rw [MeasureTheory.integral_finsetSum]
      · refine Finset.sum_congr rfl fun k' hk' => ?_
        rw [integral_const_mul]
      · intro k' hk'
        exact (hchar_int k k').const_mul _
    · intro k hk
      exact integrable_finsetSum K fun k' hk' => (hchar_int k k').const_mul _
  -- the Gram matrix of the characters is diagonal with entry `ℓ³`
  have hdiag : ∀ k ∈ K,
      (∑ k' ∈ K, (d k * star (d k'))
        * (∫ x in boxL ℓ, labChar ℓ N k x * star (labChar ℓ N k' x)))
      = (d k * star (d k)) * ((ℓ : ℂ) ^ 3) := by
    intro k hk
    have hinner : (∑ k' ∈ K, (d k * star (d k'))
        * (∫ x in boxL ℓ, labChar ℓ N k x * star (labChar ℓ N k' x)))
        = (d k * star (d k))
            * (∫ x in boxL ℓ, labChar ℓ N k x * star (labChar ℓ N k x)) := by
      refine Finset.sum_eq_single k ?_ ?_
      · intro k' hk' hne
        rw [LatticeParsevalGram hℓ N k k',
          if_neg (fun h : k = k' => hne h.symm), mul_zero]
      · intro hknot
        exact absurd hk hknot
    rw [hinner, LatticeParsevalGram hℓ N k k, if_pos rfl]
  calc ∫ x in boxL ℓ, ‖∑ k ∈ K, d k * labChar ℓ N k x‖ ^ 2
      = (∫ x in boxL ℓ, ∑ k ∈ K, ∑ k' ∈ K,
          (d k * star (d k')) * (labChar ℓ N k x * star (labChar ℓ N k' x))).re := by
        rw [show (∫ x in boxL ℓ, ‖∑ k ∈ K, d k * labChar ℓ N k x‖ ^ 2)
            = ∫ x in boxL ℓ, (∑ k ∈ K, ∑ k' ∈ K,
                (d k * star (d k')) * (labChar ℓ N k x * star (labChar ℓ N k' x))).re
            from integral_congr_ae (Eventually.of_forall hnorm)]
        simpa only [Complex.reCLM_apply] using Complex.reCLM.integral_comp_comm hdouble_int
    _ = (∑ k ∈ K, ∑ k' ∈ K, (d k * star (d k'))
          * (∫ x in boxL ℓ, labChar ℓ N k x * star (labChar ℓ N k' x))).re := by
        rw [hInt]
    _ = ℓ ^ 3 * ∑ k ∈ K, ‖d k‖ ^ 2 := by
        rw [Finset.sum_congr rfl hdiag]
        have hterm : ∀ k : Work.BoseBoxFock.Lab N,
            (d k * star (d k)) * ((ℓ : ℂ) ^ 3) = ((‖d k‖ ^ 2 * ℓ ^ 3 : ℝ) : ℂ) := by
          intro k
          simp only [Complex.star_def]
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow,
            ← Complex.ofReal_mul]
        rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Complex.ofReal_sum, Complex.ofReal_re,
          ← Finset.sum_mul]
        ring

theorem LatticeW1sqParseval {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ)
    (c : Work.BoseBoxFock.Lab N → ℂ) :
    (∫ x in boxL ℓ, ‖(∑ k ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0,
        c k * Complex.exp
          (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k) x : ℂ)))‖ ^ 2
      = ℓ ^ 3 * ∑ k ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0,
          ‖c k‖ ^ 2)
    ∧ ((∑ i : Fin 3, ∫ x in boxL ℓ,
          ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) =>
              ∑ k ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0,
                c k * Complex.exp
                  (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k) y : ℂ))) x
            (EuclideanSpace.single i 1)‖ ^ 2)
      = ℓ ^ 3 * ∑ k ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0,
          ‖Work.BoseBoxFock.kmomLab ℓ N k‖ ^ 2 * ‖c k‖ ^ 2) := by
  refine ⟨?_, ?_⟩
  · -- the `L²` form is the core Parseval lemma
    simpa only [labChar_apply] using
      integral_normSq_labChar_sum hℓ N
        ((Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0) c
  · set K : Finset (Work.BoseBoxFock.Lab N) :=
      (Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0 with hK
    -- for each coordinate direction `i` the directional derivative is again a lattice sum,
    -- with coefficients `c k · i · k_i`, so the same Parseval lemma applies
    have hpiece : ∀ i : Fin 3,
        ∫ x in boxL ℓ, ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) =>
            ∑ k ∈ K, c k * labChar ℓ N k y) x (EuclideanSpace.single i 1)‖ ^ 2
          = ℓ ^ 3 * ∑ k ∈ K, ‖c k‖ ^ 2 * ((Work.BoseBoxFock.kmomLab ℓ N k i) ^ 2) := by
      intro i
      have hpt : ∀ x : EuclideanSpace ℝ (Fin 3),
          ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) =>
              ∑ k ∈ K, c k * labChar ℓ N k y) x (EuclideanSpace.single i 1)‖ ^ 2
            = ‖∑ k ∈ K, (c k * (Complex.I * ((Work.BoseBoxFock.kmomLab ℓ N k i : ℝ) : ℂ)))
                * labChar ℓ N k x‖ ^ 2 := by
        intro x
        rw [LatticeParsevalDeriv]
      rw [show (∫ x in boxL ℓ, ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) =>
            ∑ k ∈ K, c k * labChar ℓ N k y) x (EuclideanSpace.single i 1)‖ ^ 2)
          = ∫ x in boxL ℓ, ‖∑ k ∈ K,
              (c k * (Complex.I * ((Work.BoseBoxFock.kmomLab ℓ N k i : ℝ) : ℂ)))
                * labChar ℓ N k x‖ ^ 2 from integral_congr_ae (Eventually.of_forall hpt)]
      rw [integral_normSq_labChar_sum hℓ N K
        (fun k => c k * (Complex.I * ((Work.BoseBoxFock.kmomLab ℓ N k i : ℝ) : ℂ)))]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      have hsq : ∀ a : ℝ, ‖((a : ℝ) : ℂ)‖ ^ 2 = a ^ 2 := by
        intro a
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, pow_two]
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul, mul_pow, hsq]
    have hmain : (∑ i : Fin 3, ∫ x in boxL ℓ, ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) =>
            ∑ k ∈ K, c k * labChar ℓ N k y) x (EuclideanSpace.single i 1)‖ ^ 2)
        = ℓ ^ 3 * ∑ k ∈ K, ‖Work.BoseBoxFock.kmomLab ℓ N k‖ ^ 2 * ‖c k‖ ^ 2 := by
      calc (∑ i : Fin 3, ∫ x in boxL ℓ, ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) =>
              ∑ k ∈ K, c k * labChar ℓ N k y) x (EuclideanSpace.single i 1)‖ ^ 2)
          = ∑ i : Fin 3, ℓ ^ 3 * ∑ k ∈ K,
              ‖c k‖ ^ 2 * ((Work.BoseBoxFock.kmomLab ℓ N k i) ^ 2) :=
            Finset.sum_congr rfl fun i _ => hpiece i
        _ = ℓ ^ 3 * ∑ i : Fin 3, ∑ k ∈ K,
              ‖c k‖ ^ 2 * ((Work.BoseBoxFock.kmomLab ℓ N k i) ^ 2) := by
            rw [Finset.mul_sum]
        _ = ℓ ^ 3 * ∑ k ∈ K, ‖Work.BoseBoxFock.kmomLab ℓ N k‖ ^ 2 * ‖c k‖ ^ 2 := by
            rw [LatticeParsevalSumSq]
    simpa only [labChar_apply] using hmain

end Work.BoseFixR
