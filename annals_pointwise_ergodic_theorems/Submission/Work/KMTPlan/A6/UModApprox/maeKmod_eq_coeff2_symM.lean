/-
# The model-side kernel identity: `maeKmod = coeff2 symM`

`Work.KMTPlan.A6.UModApprox.maeKmod_eq_coeff2_symM`: the kernel of the §6 model operator `mdlPart`
— the `t`-integral of the composition of the *cumulative*-height arithmetic kernel
`maeTwKernel = arithKernel · cw m_* ⊗ cw m_*` with the two exact-height kernels of the modulated
§5 bumps — is the coefficient kernel of the model symbol `symM` of area A6.

## The route

* **The model coefficient identity** (`Work.KMTPlan.A6.coeff2_symMWin_eq_integral_kernComp`, proved
  in `KMTAreas/A7/LoMixedWinDefs.lean`): the `(a,b)`-coefficient of `coeff2` of the `t`-integral of
  the product symbol is the `t`-integral of the composed kernel.
* **The per-`t` arithmetic collapse**: for each `t` the *cumulative* arithmetic kernel
  (`arithKernel`, summed over `(ℚ/ℤ)_{≤l}`) and the *exact* one (`arithKernelEx`, summed over
  `(ℚ/ℤ)_l`) give the same composition with the two exact-height bump kernels.  This is
  `Work.KMTAreas.A7.kernCompArithCollapseGen` applied twice, with the one-variable collapse
  `Work.KMTAreas.A7.tsumCwCollapseOfSupport` supplying the diagonal restriction — which uses the
  non-aliasing of each arithmetic-frequency set at the *window* scale `-2u` and the fact that both
  the window `m_*` and the §5 bump are supported in the arc `ℝ_{≤-2u}`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.UModApprox.kernComp_maeTwKernel_collapse

set_option autoImplicit false
set_option maxHeartbeats 20000000


namespace Work.KMTPlan.A6.UModApprox

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.KMTAreas.A7
open Work.Analysis.EndVar

/-- **The model-side kernel identity.** -/
theorem maeKmod_eq_coeff2_symM (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ)
    (hd : 1 ≤ P.natDegree)
    (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ n : ℕ) (hN : 1 ≤ Nat.floor (a n))
    (hnA₁ : Work.Analysis.IonescuWainger.NonAliasing (-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)))
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁))
    (hnA₂ : Work.Analysis.IonescuWainger.NonAliasing (-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)))
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂))
    (hs₁ : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ ξ : ℝ,
      Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t ξ ≠ 0 →
        ξ ∈ Work.Analysis.IonescuWainger.realArc (-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ))))
    (hs₂ : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ ξ : ℝ,
      Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t ξ ≠ 0 →
        ξ ∈ Work.Analysis.IonescuWainger.realArc (-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)))) :
    Work.KMTPlan.A6.maeKmod ρ P a l₁ l₂ k₁ k₂ n
      = Work.KMTPlan.A6.coeff2 (Work.KMTPlan.A6.symM ρ P (Nat.floor (a n)) l₁ l₂ k₁ k₂) := by
  classical
  have hU : Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) = Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) := by rw [Work.KMTPlan.A6.lcL]
  obtain ⟨B₁, hB₁0, hB₁b⟩ := Work.KMTPlan.A6.uniform_tmKer_varphiNt ρ l₁ (Nat.floor (a n)) k₁
  obtain ⟨B₂, hB₂0, hB₂b⟩ := Work.KMTPlan.A6.uniform_tmKer_varphitildeNt ρ P l₂ (Nat.floor (a n)) k₂
  have hKsum : Summable (fun p : ℤ × ℤ =>
      ‖Work.KMTAreas.A7.arithKerMWin ρ P (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)) l₁ l₂ p.1 p.2‖) := by
    rw [hU]
    exact Work.KMTPlan.A6.summable_arithKerM ρ P l₁ l₂ k₁ k₂
  have hm₁ : ∀ j : ℤ, Measurable (fun t : ℝ =>
      Work.KMTPlan.A6.tmKer ρ l₁ (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) j) :=
    fun j => Work.KMTPlan.A6.measurable_tmKer_varphiNt ρ l₁ (Nat.floor (a n)) k₁ j
  have hm₂ : ∀ j : ℤ, Measurable (fun t : ℝ =>
      Work.KMTPlan.A6.tmKer ρ l₂
        (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) j) :=
    fun j => Work.KMTPlan.A6.measurable_tmKer_varphitildeNt ρ P l₂ (Nat.floor (a n)) k₂ j
  have hσm : Measurable (fun q : ℝ × ℝ × ℝ =>
      Work.KMTPlan.A6.symSeq2 (Work.KMTAreas.A7.arithKerMWin ρ P (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)) l₁ l₂) q.2.1 q.2.2
        * Work.KMTPlan.A6.symSeq
            (Work.KMTPlan.A6.tmKer ρ l₁ (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ q.1))
            q.2.1
        * Work.KMTPlan.A6.symSeq
            (Work.KMTPlan.A6.tmKer ρ l₂
              (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ q.1)) q.2.2) :=
    Work.KMTPlan.A6.lpMeasurableSymProduct
      (Kar := Work.KMTAreas.A7.arithKerMWin ρ P
        (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)) l₁ l₂)
      (κ₁ := fun t : ℝ => Work.KMTPlan.A6.tmKer ρ l₁
        (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t))
      (κ₂ := fun t : ℝ => Work.KMTPlan.A6.tmKer ρ l₂
        (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t))
      (Work.KMTPlan.A6.measurable_symSeq2
        (Work.KMTAreas.A7.arithKerMWin ρ P
          (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)) l₁ l₂))
      (Work.KMTPlan.A6.lpMeasurableSymSeqPair hm₁)
      (Work.KMTPlan.A6.lpMeasurableSymSeqPair hm₂)
  have hσb : ∀ t, t ∈ Set.Icc (1/2 : ℝ) 1 → ∀ x y : ℝ,
      ‖Work.KMTPlan.A6.symSeq2 (Work.KMTAreas.A7.arithKerMWin ρ P (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)) l₁ l₂) x y
        * Work.KMTPlan.A6.symSeq
            (Work.KMTPlan.A6.tmKer ρ l₁ (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t)) x
        * Work.KMTPlan.A6.symSeq
            (Work.KMTPlan.A6.tmKer ρ l₂
              (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t)) y‖
        ≤ (∑' p : ℤ × ℤ, ‖Work.KMTAreas.A7.arithKerMWin ρ P (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)) l₁ l₂ p.1 p.2‖)
            * B₁ * B₂ := by
    intro t ht x y
    have hS0 : (0 : ℝ) ≤ ∑' p : ℤ × ℤ,
        ‖Work.KMTAreas.A7.arithKerMWin ρ P (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)) l₁ l₂ p.1 p.2‖ :=
      tsum_nonneg (fun _ => norm_nonneg _)
    rw [norm_mul, norm_mul]
    refine mul_le_mul (mul_le_mul (Work.KMTPlan.A6.norm_symSeq2_le hKsum x y)
      (le_trans (Work.KMTPlan.A6.norm_symSeq_le (hB₁b t ht).1 x) (hB₁b t ht).2) (norm_nonneg _)
      hS0) (le_trans (Work.KMTPlan.A6.norm_symSeq_le (hB₂b t ht).1 y) (hB₂b t ht).2)
      (norm_nonneg _) ?_
    exact mul_nonneg hS0 hB₁0
  have h := Work.KMTPlan.A6.coeff2_symMWin_eq_integral_kernComp (ρ := ρ) (P := P)
    (u := Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)) (N := Nat.floor (a n)) (l₁ := l₁) (l₂ := l₂) (k₁ := k₁) (k₂ := k₂)
    (κ₁ := fun t => Work.KMTPlan.A6.tmKer ρ l₁ (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t))
    (κ₂ := fun t => Work.KMTPlan.A6.tmKer ρ l₂
      (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t))
    (fun t => rfl) (fun t => rfl) hKsum (fun t ht => (hB₁b t ht).1)
    (fun t ht => (hB₂b t ht).1) hσm hσb
  have h2 : Work.KMTPlan.A6.coeff2
        (Work.KMTPlan.A6.symM ρ P (Nat.floor (a n)) l₁ l₂ k₁ k₂)
      = fun p q : ℤ => ∫ t in (1/2 : ℝ)..1,
          Work.KMTAreas.A7.kernComp (Work.KMTAreas.A7.arithKerMWin ρ P (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)) l₁ l₂)
            (Work.KMTPlan.A6.tmKer ρ l₁ (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t))
            (Work.KMTPlan.A6.tmKer ρ l₂
              (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t)) p q := by
    rw [Work.KMTAreas.A7.symM_eq_win]
    unfold Work.KMTAreas.A7.symMWin
    exact h
  have h1 : Work.KMTPlan.A6.maeKmod ρ P a l₁ l₂ k₁ k₂ n
      = fun j₁ j₂ => ∫ t in (1/2 : ℝ)..1,
          Work.KMTAreas.A7.kernComp
            (Work.KMTPlan.A6.maeTwKernel ρ P l₁ l₂ (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)))) (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)))))
            (Work.KMTPlan.A6.maeKer ρ l₁ (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t))
            (Work.KMTPlan.A6.maeKer ρ l₂
              (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t)) j₁ j₂ := rfl
  rw [h1, h2]
  ext j₁ j₂
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [Set.uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 1)] at ht
  have hc := kernComp_maeTwKernel_collapse ρ P (Nat.floor (a n)) l₁ l₂ k₁ k₂ hd ?_ hnA₁ hnA₂
    hs₁ hs₂ ht j₁ j₂
  · exact hc
  · rw [hU]
    exact one_le_uScale ρ hρ _

end

end Work.KMTPlan.A6.UModApprox
