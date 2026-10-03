/-
# Measurability in `t` and uniform boundedness of the slices of the §6 model operator
        `BtwistEx` with the *modified* bumps `φ_{N,t,j}`

The §5/§8 model operator of the low case of area A6 is the `t`-integral over `[1/2,1]` of the
exact-height twisted bilinear multiplier `BtwistEx` evaluated at the two Ionescu--Wainger
projections `Tm ρ l₁ (φ_{N,t,j₁}) f`, `Tm ρ l₂ (φ̃_{N,t,j₂}) g` of the *modified* bumps
`varphiNtj N k₁ j₁ t`, `varphitildeNtj P N k₂ j₂ t` (`j ∈ {-1,0,1}`, with `(k,j) ≠ (0,-1)`).

For the `t`-integral to be a genuine Lebesgue integral one needs, for every `x : ℤ`,

* the measurability in `t` of the slice `t ↦ BtwistEx …(x)` (`Measurable.tsum` applied twice,
  the measurability of the two convolution values in `t` coming from the package
  `tmKerPackage_varphiNtj`/`tmKerPackage_varphitildeNtj` for the kernel of `Tm`, written as the
  convolution `Tm ρ l φ u = convOp (tmKer ρ l φ) u`);
* a bound uniform on `t ∈ [1/2,1]` (then the slice is integrable on the finite interval `[1/2,1]`,
  `MeasureTheory.Integrable.of_bound`).

The uniform bound is assembled from three already-proved inputs:

* `Tm_bdd_of_l2`: the `ℓ² → ℓ^∞` bound for the exact-height multiplier, applied to the two
  modified bumps via the uniform-in-`t` `C²`/`L¹` bounds `varphiNtj_bounds`,
  `varphitildeNtj_bounds`;
* the cardinality bound `norm_arithKernelSet_le` for the arithmetic kernel, together with the
  quadratic decay `cw_etaCut_decay` of the coefficients of the two §6 windows `mStarF u`,
  `mStargF P.natDegree u`;
* the general uniform bound `exists_bound_BtwistSet_uniform`, of which `BtwistEx` is the instance
  with the exact-height frequency sets `Aᵢ = diffFreqs ρ lᵢ`
  (`BtwistEx_eq_BtwistSet`, definitional).
-/
import Mathlib
import Submission.Work.KMTPlan.A6.LowModelVarCaseBAux
import Submission.Work.KMTPlan.A6.Tm_bdd_of_l2
import Submission.Work.KMTAreas.A7.exists_bound_BtwistSet_uniform

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.KMTAreas.A7

/-- **`BtwistEx` is `BtwistSet` at the exact-height frequency sets** `Aᵢ = diffFreqs ρ lᵢ`: the
two definitions have the same body, `arithKernelEx` being `arithKernelSet` on those sets. -/
private lemma BtwistEx_eq_BtwistSet (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (h k : ℤ → ℂ) (x : ℤ) :
    BtwistEx ρ P l₁ l₂ m₁ m₂ h k x
      = BtwistSet ρ P l₁ l₂ (diffFreqs ρ l₁) (diffFreqs ρ l₂) m₁ m₂ h k x := rfl

theorem btwistExNtjSliceBound (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ u N k₁ k₂ : ℕ) (j₁ j₂ : ℤ)
    (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ))
    (hk₁ : k₁ ≠ 0 ∨ 0 ≤ j₁) (hk₂ : k₂ ≠ 0 ∨ 0 ≤ j₂)
    (f g : ℤ → ℂ) (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count) (x : ℤ) :
    Measurable (fun t : ℝ => Work.KMTPlan.A6.BtwistEx ρ P l₁ l₂
        (Work.KMTAreas.A7.mStarF u) (Work.KMTAreas.A7.mStargF P.natDegree u)
        (Work.KMTAreas.A7.Tm ρ l₁ (Work.KMTPlan.A6.varphiNtj N k₁ j₁ t) f)
        (Work.KMTAreas.A7.Tm ρ l₂ (Work.KMTPlan.A6.varphitildeNtj P N k₂ j₂ t) g) x) ∧
      (∃ C : ℝ, ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ‖Work.KMTPlan.A6.BtwistEx ρ P l₁ l₂
        (Work.KMTAreas.A7.mStarF u) (Work.KMTAreas.A7.mStargF P.natDegree u)
        (Work.KMTAreas.A7.Tm ρ l₁ (Work.KMTPlan.A6.varphiNtj N k₁ j₁ t) f)
        (Work.KMTAreas.A7.Tm ρ l₂ (Work.KMTPlan.A6.varphitildeNtj P N k₂ j₂ t) g) x‖ ≤ C) := by
  constructor
  · -- measurability in `t` of the slice
    obtain ⟨a₁, _ha₁sum, _ha₁bd, ha₁meas⟩ := tmKerPackage_varphiNtj ρ l₁ N k₁ j₁ hj₁ hk₁
    obtain ⟨a₂, _ha₂sum, _ha₂bd, ha₂meas⟩ := tmKerPackage_varphitildeNtj ρ l₂ P N k₂ j₂ hj₂ hk₂
    have hH : ∀ y : ℤ, Measurable (fun t : ℝ => Tm ρ l₁ (varphiNtj N k₁ j₁ t) f y) := by
      intro y
      have hfun : (fun t : ℝ => Tm ρ l₁ (varphiNtj N k₁ j₁ t) f y)
          = fun t : ℝ => ∑' i : ℤ, tmKer ρ l₁ (varphiNtj N k₁ j₁ t) i * f (y - i) := by
        funext t
        rw [Tm_eq_convOp]
        rfl
      rw [hfun]
      exact Measurable.tsum (L := SummationFilter.unconditional ℤ)
        (fun i => (ha₁meas i).mul_const _)
    have hK : ∀ y : ℤ, Measurable (fun t : ℝ => Tm ρ l₂ (varphitildeNtj P N k₂ j₂ t) g y) := by
      intro y
      have hfun : (fun t : ℝ => Tm ρ l₂ (varphitildeNtj P N k₂ j₂ t) g y)
          = fun t : ℝ => ∑' i : ℤ, tmKer ρ l₂ (varphitildeNtj P N k₂ j₂ t) i * g (y - i) := by
        funext t
        rw [Tm_eq_convOp]
        rfl
      rw [hfun]
      exact Measurable.tsum (L := SummationFilter.unconditional ℤ)
        (fun i => (ha₂meas i).mul_const _)
    simp only [BtwistEx]
    refine Measurable.tsum (L := SummationFilter.unconditional ℤ) (fun a => ?_)
    refine Measurable.tsum (L := SummationFilter.unconditional ℤ) (fun b => ?_)
    exact (((hH (x - a)).const_mul
      (arithKernelEx ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ a b
        * cw (mStarF u) a * cw (mStargF P.natDegree u) b))).mul (hK (x - b))
  · -- the uniform-in-`t` bound
    obtain ⟨S₁, hS₁nn, hbd₁⟩ := varphiNtj_bounds N k₁ j₁ hk₁
    obtain ⟨S₂, hS₂nn, hbd₂⟩ := varphitildeNtj_bounds P N k₂ j₂ hk₂
    obtain ⟨C₁, _hC₁nn, hC₁⟩ := Tm_bdd_of_l2 ρ l₁ S₁ hS₁nn
    obtain ⟨C₂, _hC₂nn, hC₂⟩ := Tm_bdd_of_l2 ρ l₂ S₂ hS₂nn
    have hbH : ∃ Ch : ℝ, ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ y : ℤ,
        ‖Tm ρ l₁ (varphiNtj N k₁ j₁ t) f y‖ ≤ Ch :=
      ⟨C₁ * Real.sqrt (∑' i : ℤ, ‖f i‖ ^ 2), fun t ht y =>
        hC₁ (varphiNtj N k₁ j₁ t) (hbd₁ t ht).1 (hbd₁ t ht).2.1 (hbd₁ t ht).2.2.1
          (hbd₁ t ht).2.2.2 f hf y⟩
    have hbK : ∃ Ck : ℝ, ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ y : ℤ,
        ‖Tm ρ l₂ (varphitildeNtj P N k₂ j₂ t) g y‖ ≤ Ck :=
      ⟨C₂ * Real.sqrt (∑' i : ℤ, ‖g i‖ ^ 2), fun t ht y =>
        hC₂ (varphitildeNtj P N k₂ j₂ t) (hbd₂ t ht).1 (hbd₂ t ht).2.1 (hbd₂ t ht).2.2.1
          (hbd₂ t ht).2.2.2 g hg y⟩
    have hKbd : ∃ K : ℝ, ∀ a b : ℤ, ‖arithKernelSet P (arithQ ρ (max l₁ l₂))
        (diffFreqs ρ l₁) (diffFreqs ρ l₂) a b‖ ≤ K :=
      ⟨((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ),
        fun a b => norm_arithKernelSet_le P _ _ _ a b⟩
    have hdec₁ : ∃ Cd : ℝ, ∀ j : ℤ, ‖cw (mStarF u) j‖ ≤ Cd / (1 + |(j : ℝ)|) ^ 2 := by
      obtain ⟨C, _hCpos, hC⟩ := cw_etaCut_decay (-(2 * (u : ℤ)))
      exact ⟨C, fun j => hC j⟩
    have hdec₂ : ∃ Cd : ℝ, ∀ j : ℤ,
        ‖cw (mStargF P.natDegree u) j‖ ≤ Cd / (1 + |(j : ℝ)|) ^ 2 := by
      obtain ⟨C, _hCpos, hC⟩ := cw_etaCut_decay (-((P.natDegree : ℤ) * 2 * (u : ℤ)))
      exact ⟨C, fun j => hC j⟩
    obtain ⟨C, hC⟩ := exists_bound_BtwistSet_uniform ρ P l₁ l₂
      (diffFreqs ρ l₁) (diffFreqs ρ l₂) (mStarF u) (mStargF P.natDegree u)
      (fun t => Tm ρ l₁ (varphiNtj N k₁ j₁ t) f)
      (fun t => Tm ρ l₂ (varphitildeNtj P N k₂ j₂ t) g) x
      hKbd hdec₁ hdec₂ hbH hbK
    refine ⟨C, fun t ht => ?_⟩
    rw [BtwistEx_eq_BtwistSet]
    exact hC t ht

end

end Work.KMTPlan.A6
