import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.PotCubicPins
import Submission.Work.BoseBoxFock.qVec_expansion_finset
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pinQ_kernel_expansion`

The **honest pair kernel** of the FS `Q₂` row, expanded into its four lattice sums.

The `Q₂` row carries, in each of its three blocks, a finite sum over the labels `k : Lab N` of the
*sandwich* `pinQ v μ N k w · conj (pinQ v μ N k y)` (the two slots of the pair row).  Since
`pinQ v μ N k = (√(ℓ³))⁻¹ · qVec ℓ (kmomLab ℓ N k)` with `ℓ = ellH v μ`
(`Work.BoseBoxFock.pinQ`), the pointwise expansion `Work.BoseBoxFock.qVec_expansion_finset` gives

    Σ_k c k · pinQ_k(w)·conj(pinQ_k(y))
      = ℓ⁻³ · ( χ(w)χ(y)·Σ_k c k e^{i⟪κ_k,w−y⟫}
              − χ(w)θ(y)·Σ_k c k χ̂(ℓκ_k)e^{i⟪κ_k,w⟫}
              − θ(w)χ(y)·Σ_k c k χ̂(ℓκ_k)e^{−i⟪κ_k,y⟫}
              + θ(w)θ(y)·Σ_k c k χ̂(ℓκ_k)² )

(`χ = Submission.BoseGases.chiScale ℓ`, `θ = Work.BoseK15.corpusBox.thetaFun ℓ`,
`χ̂ = Work.BoseK15.corpusBox.hatChi`, `κ_k = kmomLab ℓ N k`).

This is the algebraic bridge between the row's kernel form
(`Work.BoseBoxFock.potPairRows_kernelForm`) and the four lattice sums whose limits are analysed in
`FINDING_PotPairRows_exists.md` §SESSION 5 (the `χχ` sum is the truncated lattice Fourier series
with `L²` limit the periodisation; the three `χ̂` sums converge absolutely).

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The four lattice sums -/

/-- The `χχ` lattice sum of the pair kernel: `Σ_k c k · e^{i⟪κ_k,z⟫}` (the truncated lattice
Fourier series whose `L²` limit is the periodisation `ℓ³Σ_m W(·+ℓ•latVec m)`). -/
noncomputable def pinQA (v : E3 → ℝ) (μ : ℝ) (N : ℕ) (c : Lab N → ℝ) (z : E3) : ℂ :=
  ∑ k : Lab N, (c k : ℂ) * Complex.exp
    (Complex.I * ((inner ℝ (kmomLab (ellH v μ) N k) z : ℝ) : ℂ))

/-- The first `χ̂`-lattice sum: `Σ_k c k · χ̂(ℓκ_k) · e^{i⟪κ_k,w⟫}` (absolutely convergent). -/
noncomputable def pinQB (v : E3 → ℝ) (μ : ℝ) (N : ℕ) (c : Lab N → ℝ) (w : E3) : ℂ :=
  ∑ k : Lab N, (c k : ℂ) * (((Work.BoseK15.corpusBox.hatChi
      (ellH v μ • kmomLab (ellH v μ) N k) : ℝ)) : ℂ) * Complex.exp
    (Complex.I * ((inner ℝ (kmomLab (ellH v μ) N k) w : ℝ) : ℂ))

/-- The second `χ̂`-lattice sum: `Σ_k c k · χ̂(ℓκ_k) · e^{−i⟪κ_k,y⟫}` (absolutely convergent). -/
noncomputable def pinQC (v : E3 → ℝ) (μ : ℝ) (N : ℕ) (c : Lab N → ℝ) (y : E3) : ℂ :=
  ∑ k : Lab N, (c k : ℂ) * (((Work.BoseK15.corpusBox.hatChi
      (ellH v μ • kmomLab (ellH v μ) N k) : ℝ)) : ℂ) * Complex.exp
    (-(Complex.I * ((inner ℝ (kmomLab (ellH v μ) N k) y : ℝ) : ℂ)))

/-- The `θθ`-lattice sum: `Σ_k c k · χ̂(ℓκ_k)²` (a constant). -/
noncomputable def pinQD (v : E3 → ℝ) (μ : ℝ) (N : ℕ) (c : Lab N → ℝ) : ℂ :=
  ∑ k : Lab N, (c k : ℂ) * ((((Work.BoseK15.corpusBox.hatChi
      (ellH v μ • kmomLab (ellH v μ) N k) : ℝ)) : ℂ)) ^ 2

/-- **The expanded honest pair kernel**: the four-term form of `Σ_k c k · pinQ_k(w)·conj(pinQ_k(y))`
at the honest box side `ℓ = ellH v μ` (`= pinQ_kernel_expansion`'s right-hand side).  This is the
kernel that replaces `Σ_k c k · pinQ_k(w)·conj(pinQ_k y)` in each block of the `Q₂` row. -/
noncomputable def K1exp (v : E3 → ℝ) (μ : ℝ) (N : ℕ) (c : Lab N → ℝ) (w y : E3) : ℂ :=
  ((ellH v μ) ^ 3)⁻¹ *
    ( (((Submission.BoseGases.chiScale (ellH v μ) w : ℝ)) : ℂ)
        * (((Submission.BoseGases.chiScale (ellH v μ) y : ℝ)) : ℂ) * pinQA v μ N c (w - y)
      - (((Submission.BoseGases.chiScale (ellH v μ) w : ℝ)) : ℂ)
        * Work.BoseK15.corpusBox.thetaFun (ellH v μ) y * pinQB v μ N c w
      - Work.BoseK15.corpusBox.thetaFun (ellH v μ) w
        * (((Submission.BoseGases.chiScale (ellH v μ) y : ℝ)) : ℂ) * pinQC v μ N c y
      + Work.BoseK15.corpusBox.thetaFun (ellH v μ) w
        * Work.BoseK15.corpusBox.thetaFun (ellH v μ) y * pinQD v μ N c)

/-! ## 2. The expansion -/

/-- The `pinQ`-kernel expansion (see the module docstring). -/
theorem pinQ_kernel_expansion {N : ℕ} {v : E3 → ℝ} {μ : ℝ} (c : Lab N → ℝ) (w y : E3) :
    (∑ k : Lab N, (c k : ℂ) * (pinQ v μ N k w * (starRingEnd ℂ) (pinQ v μ N k y)))
      = ((ellH v μ) ^ 3)⁻¹ *
          ( (((Submission.BoseGases.chiScale (ellH v μ) w : ℝ)) : ℂ)
              * (((Submission.BoseGases.chiScale (ellH v μ) y : ℝ)) : ℂ)
              * pinQA v μ N c (w - y)
            - (((Submission.BoseGases.chiScale (ellH v μ) w : ℝ)) : ℂ)
              * Work.BoseK15.corpusBox.thetaFun (ellH v μ) y * pinQB v μ N c w
            - Work.BoseK15.corpusBox.thetaFun (ellH v μ) w
              * (((Submission.BoseGases.chiScale (ellH v μ) y : ℝ)) : ℂ) * pinQC v μ N c y
            + Work.BoseK15.corpusBox.thetaFun (ellH v μ) w
              * Work.BoseK15.corpusBox.thetaFun (ellH v μ) y * pinQD v μ N c) := by
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  have hsne : (((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact inv_ne_zero (ne_of_gt (Real.sqrt_pos_of_pos (pow_pos hℓ 3)))
  -- the scaled kernel is `s²` times the `qVec` kernel
  have hstep : (∑ k : Lab N, (c k : ℂ) * (pinQ v μ N k w * (starRingEnd ℂ) (pinQ v μ N k y)))
      = (((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ) ^ 2 *
          (∑ k : Lab N, (c k : ℂ) * (Work.BoseK15.corpusBox.qVec (ellH v μ)
              (kmomLab (ellH v μ) N k) w
            * (starRingEnd ℂ) (Work.BoseK15.corpusBox.qVec (ellH v μ)
                (kmomLab (ellH v μ) N k) y))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [pinQ]
    have hconj : (starRingEnd ℂ) ((((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ)
        * Work.BoseK15.corpusBox.qVec (ellH v μ) (kmomLab (ellH v μ) N k) y)
        = (((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ)
          * (starRingEnd ℂ) (Work.BoseK15.corpusBox.qVec (ellH v μ)
              (kmomLab (ellH v μ) N k) y) := by
      rw [map_mul, Complex.conj_ofReal]
    rw [hconj]
    ring
  -- `s² = (ℓ³)⁻¹`
  have hsq : ((((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ)) ^ 2 = (((ellH v μ) ^ 3)⁻¹ : ℝ) := by
    have h1 : ((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ) ^ 2 = ((ellH v μ) ^ 3)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt (pow_nonneg hℓ.le 3)]
    rw [← Complex.ofReal_pow, h1]
  rw [hstep, hsq, qVec_expansion_finset Finset.univ (fun k => (c k : ℂ))
    (fun k => kmomLab (ellH v μ) N k) w y]
  simp only [pinQA, pinQB, pinQC, pinQD]

end Work.BoseBoxFock
