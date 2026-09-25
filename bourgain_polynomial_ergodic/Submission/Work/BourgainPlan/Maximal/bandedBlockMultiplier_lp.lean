import Mathlib
import Submission.Commons.Analysis.Fourier.mikhlin_multiplier_lp
import Submission.Work.BourgainPlan.Maximal.l2_defs
import Submission.Work.BourgainPlan.Maximal.bandLocalizedIncrement_mikhlin
import Submission.Work.BourgainPlan.Maximal.signedSum_mikhlin_of_disjointSupport

/-!
# The banded block multiplier on `L^p(ℝ)`

Let `P ∈ ℤ[X]` of degree `d = deg P ≥ 2`, `1 < p < ∞`, and let `ψ : ℝ → ℝ` be `C²` with
`0 ≤ ψ ≤ 1` and `ψ t ≠ 0 ⟹ 1 < t < 2^d`.

The **banded block symbol** is

  `m_K(ξ) = ∑_{i<K} ε_i · ψ(2^{i d} ξ) · (Φ_{2^{i+1}}(ξ) − Φ_{2^i}(ξ))`,

where `Φ_N(β) = ∫₀¹ e(β P(N s)) ds` is the polynomial profile and `‖ε_i‖ ≤ 1`.  The bands
`{ψ(2^{i d}·) ≠ 0} ⊂ (2^{-id}, 2^{(1-i)d})` are pairwise disjoint (up to the zero set of `ψ`), and
each band multiplier satisfies the Mikhlin conditions with a constant `A` **independent of `i`**
(`bandLocalizedIncrement_mikhlin`).  Hence `m_K` itself satisfies the Mikhlin conditions with the
same constant (`signedSum_mikhlin_of_disjointSupport`), and Mikhlin's multiplier theorem
(`mikhlin_multiplier_lp`) gives the `L^p` bound, uniformly in `K` and in the signs `ε`.
-/

namespace Work.BourgainPlan.Maximal

open scoped BigOperators ENNReal

noncomputable section

/-- The band multiplier of index `i` for the polynomial `P` and the cut-off `ψ`. -/
noncomputable def bandIncrement (P : Polynomial ℤ) (ψ : ℝ → ℝ) (i : ℕ) (ξ : ℝ) : ℂ :=
  (ψ ((2 : ℝ) ^ (i * P.natDegree) * ξ) : ℂ) *
    (polyProfile P (2 ^ (i + 1)) ξ - polyProfile P (2 ^ i) ξ)

lemma contDiff_bandIncrement (P : Polynomial ℤ) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 2 ψ) (i : ℕ) :
    ContDiff ℝ 2 (bandIncrement P ψ i) := by
  have h1 : ContDiff ℝ 2 (fun ξ : ℝ => (ψ ((2 : ℝ) ^ (i * P.natDegree) * ξ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (hψ.comp (contDiff_const.mul contDiff_id))
  have h2 : ContDiff ℝ 2 (fun ξ : ℝ => polyProfile P (2 ^ (i + 1)) ξ
      - polyProfile P (2 ^ i) ξ) :=
    ((contDiff_polyProfile P (2 ^ (i + 1))).of_le (WithTop.coe_le_coe.mpr le_top)).sub
      ((contDiff_polyProfile P (2 ^ i)).of_le (WithTop.coe_le_coe.mpr le_top))
  exact h1.mul h2

theorem bandedBlockMultiplier_lp (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (p : ℝ) (hp : 1 < p)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 2 ψ) (hψ0 : ∀ t : ℝ, 0 ≤ ψ t) (hψ1 : ∀ t : ℝ, ψ t ≤ 1)
    (hψs : ∀ t : ℝ, ψ t ≠ 0 → 1 < t ∧ t < (2 : ℝ) ^ P.natDegree) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (K : ℕ) (ε : Fin K → ℂ), (∀ i, ‖ε i‖ ≤ 1) → ∀ (G : SchwartzMap ℝ ℂ),
        MeasureTheory.eLpNorm
          (fun x : ℝ => ∫ ξ : ℝ,
            (((∑ i : Fin K, ε i * ((ψ ((2:ℝ) ^ ((i : ℕ) * P.natDegree) * ξ) : ℂ) *
                (Work.BourgainPlan.Maximal.polyProfile P (2 ^ ((i : ℕ)+1)) ξ
                  - Work.BourgainPlan.Maximal.polyProfile P (2 ^ (i : ℕ)) ξ))))
              * Complex.exp (2 * Real.pi * Complex.I * (x * ξ)))
              • (FourierTransform.fourier (G : ℝ → ℂ) ξ))
          (ENNReal.ofReal p) (MeasureTheory.volume : MeasureTheory.Measure ℝ)
        ≤ ENNReal.ofReal C *
            MeasureTheory.eLpNorm (fun x : ℝ => G x) (ENNReal.ofReal p)
              (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  obtain ⟨A, hApos, hA0, hA1, hA2, hAdisj⟩ :=
    bandLocalizedIncrement_mikhlin P hd ψ hψ hψ0 hψ1 hψs
  obtain ⟨C0, hC0pos, hmik⟩ := Commons.Analysis.Fourier.mikhlin_multiplier_lp p hp
  refine ⟨C0 * A, mul_pos hC0pos hApos, ?_⟩
  intro K ε hε G
  let M : Fin K → ℝ → ℂ := fun i => bandIncrement P ψ (i : ℕ)
  have hcd : ∀ i : Fin K, ContDiff ℝ 2 (M i) := fun i => contDiff_bandIncrement P ψ hψ (i : ℕ)
  have hbdd : ∀ (i : Fin K) (ξ : ℝ), ‖M i ξ‖ ≤ A := fun i ξ => hA0 (i : ℕ) ξ
  have hder1 : ∀ (i : Fin K) (ξ : ℝ), |ξ| * ‖deriv (M i) ξ‖ ≤ A := fun i ξ => hA1 (i : ℕ) ξ
  have hder2 : ∀ (i : Fin K) (ξ : ℝ),
      |ξ| ^ 2 * ‖iteratedDeriv 2 (M i) ξ‖ ≤ A := fun i ξ => hA2 (i : ℕ) ξ
  have hdisj : ∀ i j : Fin K, i ≠ j → ∀ ξ : ℝ, M i ξ = 0 ∨ M j ξ = 0 := by
    intro i j hij ξ
    rcases hAdisj (i : ℕ) (j : ℕ) (fun h => hij (Fin.ext h)) ξ with h | h
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨hmcd, hmb, hm1, hm2⟩ :=
    signedSum_mikhlin_of_disjointSupport M ε A hApos.le hε hcd hbdd hder1 hder2 hdisj
  exact hmik (fun ξ : ℝ => ∑ i : Fin K, ε i * M i ξ) A hApos.le hmcd hmb hm1 hm2 G

end

end Work.BourgainPlan.Maximal
