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
import Submission.Work.KMTPlan.A6.MaeKernels
import Submission.Work.KMTAreas.A7.kernCompArithCollapseGen
import Submission.Work.KMTAreas.A7.tsumCwCollapseOfSupport
import Submission.Work.KMTAreas.A7.LpMixedModelSymbol
import Submission.Work.KMTAreas.A7.lacunaryBump_mult_bound_k1pos
import Submission.Work.KMTPlan.A6.MaeCollapse

set_option autoImplicit false
set_option maxHeartbeats 20000000

namespace Work.KMTPlan.A6.UModApprox

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.KMTAreas.A7
open Work.Analysis.EndVar

/-- `1 ≤ uScale ρ L` (the auxiliary scale is at least one). -/
theorem one_le_uScale (ρ : ℝ) (hρ : 0 < ρ) (L : ℕ) : 1 ≤ Work.KMTAreas.A7.uScale ρ L := by
  have h0 : (0 : ℝ) ≤ 2 * ρ * (L : ℝ) := by positivity
  have h1 : (((1 : ℤ) : ℝ)) ≤ (2 : ℝ) ^ (2 * ρ * (L : ℝ)) := by
    have h := Real.one_le_rpow (x := (2 : ℝ)) (z := 2 * ρ * (L : ℝ)) (by norm_num) h0
    simpa using h
  have h3 : (1 : ℤ) ≤ ⌊(2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋ := Int.le_floor.mpr h1
  unfold Work.KMTAreas.A7.uScale Work.Analysis.EndVar.scaleCount
  simp only [Nat.cast_one, one_mul]
  exact (Int.le_toNat (le_trans (by norm_num : (0 : ℤ) ≤ 1) h3)).mpr h3

/-- **The per-`t` collapse of the twisted composition.** -/
theorem kernComp_maeTwKernel_collapse (ρ : ℝ) (P : Polynomial ℤ) (N l₁ l₂ k₁ k₂ : ℕ)
    (hd : 1 ≤ P.natDegree)
    (hu1 : 1 ≤ Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂))
    (hnA₁ : Work.Analysis.IonescuWainger.NonAliasing (-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)))
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁))
    (hnA₂ : Work.Analysis.IonescuWainger.NonAliasing (-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)))
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂))
    (hs₁ : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ ξ : ℝ,
      Work.KMTAreas.A7.varphiNt N k₁ t ξ ≠ 0 →
        ξ ∈ Work.Analysis.IonescuWainger.realArc (-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ))))
    (hs₂ : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ ξ : ℝ,
      Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t ξ ≠ 0 →
        ξ ∈ Work.Analysis.IonescuWainger.realArc (-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ))))
    {t : ℝ} (ht : t ∈ Set.Icc (1/2 : ℝ) 1) (j₁ j₂ : ℤ) :
    Work.KMTAreas.A7.kernComp
        (Work.KMTPlan.A6.maeTwKernel ρ P l₁ l₂ (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂))) (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂))))
        (Work.KMTPlan.A6.maeKer ρ l₁ (Work.KMTAreas.A7.varphiNt N k₁ t)) (Work.KMTPlan.A6.maeKer ρ l₂ (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t)) j₁ j₂
      = Work.KMTAreas.A7.kernComp (Work.KMTAreas.A7.arithKerMWin ρ P (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)) l₁ l₂)
        (Work.KMTPlan.A6.maeKer ρ l₁ (Work.KMTAreas.A7.varphiNt N k₁ t)) (Work.KMTPlan.A6.maeKer ρ l₂ (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t)) j₁ j₂ := by
  classical
  have hk4 : (2 : ℝ) ^ (-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ))) ≤ 1 / 4 := by
    have h2 : (-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ))) ≤ (-2 : ℤ) := by
      have h1 : (1 : ℤ) ≤ (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ) := by exact_mod_cast hu1
      nlinarith
    have h3 : (2 : ℝ) ^ (-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ))) ≤ (2 : ℝ) ^ (-2 : ℤ) :=
      zpow_le_zpow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) h2
    have h4 : (2 : ℝ) ^ (-2 : ℤ) = 1 / 4 := by norm_num
    rwa [h4] at h3
  have hmk₁ : ∀ x : ℝ, Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)) x ≠ 0 →
      x ∈ Work.Analysis.IonescuWainger.realArc (-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ))) := by
    intro x hx
    exact Work.KMTAreas.A7.etaCut_ne_zero_mem_realArc (-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ))) hx
  have hmk₂ : ∀ x : ℝ, Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)) x ≠ 0 →
      x ∈ Work.Analysis.IonescuWainger.realArc (-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ))) := by
    intro x hx
    have h := Work.KMTAreas.A7.etaCut_ne_zero_mem_realArc
      (-((P.natDegree : ℤ) * 2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)))
      (by simpa only [Work.KMTAreas.A7.mStargF] using hx)
    refine Work.Analysis.IonescuWainger.realArc_mono ?_ h
    have hd' : (1 : ℤ) ≤ (P.natDegree : ℤ) := by exact_mod_cast hd
    have hu0 : (0 : ℤ) ≤ (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ) := Int.natCast_nonneg _
    nlinarith
  have hsm₁ : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂))) j‖ := summable_cw_mStarF (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂))
  have hsm₂ : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂))) j‖ :=
    summable_cw_mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂))
  have hsf : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphiNt N k₁ t) j‖ := summable_cw_varphiNt N k₁ t
  have hsg : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t) j‖ :=
    summable_cw_varphitildeNt P P.natDegree N k₂ t
  have hcol₁ : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
      ∀ α₁ ∈ Work.KMTAreas.A7.diffFreqs ρ l₁,
      (∑' j : ℤ, Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂))) j * fourier (T := 1) (-j) (α - α₁)
          * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphiNt N k₁ t) (j₁ - j))
        = if α = α₁ then Work.KMTAreas.A7.cw (fun x => (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂))) x * (Work.KMTAreas.A7.varphiNt N k₁ t) x) j₁ else 0 := by
    intro α hα α₁ hα₁
    refine Work.KMTAreas.A7.tsumCwCollapseOfSupport (m := (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))) (f := (Work.KMTAreas.A7.varphiNt N k₁ t))
      ?_ ?_ ?_ (k := -(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ))) hk4 ?_ hmk₁ ?_ hα
      (Work.KMTPlan.A6.mae_diffFreqs_subset ρ l₁ hα₁) j₁
    · exact (Work.KMTAreas.A7.contDiff_etaCut (-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)))).of_le (WithTop.coe_le_coe.mpr le_top)
    · exact Work.KMTAreas.A7.hasCompactSupport_etaCut (-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)))
    · exact Work.KMTAreas.A7.lacBump_integrable_varphiNt N k₁ t
    · exact hnA₁
    · exact hs₁ t ht
  have hcol₂ : ∀ β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂,
      ∀ β₁ ∈ Work.KMTAreas.A7.diffFreqs ρ l₂,
      (∑' j : ℤ, Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂))) j * fourier (T := 1) (-j) (β - β₁)
          * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t) (j₂ - j))
        = if β = β₁ then Work.KMTAreas.A7.cw (fun x => (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂))) x * (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t) x) j₂ else 0 := by
    intro β hβ β₁ hβ₁
    refine Work.KMTAreas.A7.tsumCwCollapseOfSupport (m := (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))) (f := (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t))
      ?_ ?_ ?_ (k := -(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ))) hk4 ?_ hmk₂ ?_ hβ
      (Work.KMTPlan.A6.mae_diffFreqs_subset ρ l₂ hβ₁) j₂
    · exact (Work.KMTAreas.A7.contDiff_etaCut (-((P.natDegree : ℤ) * 2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)))).of_le (WithTop.coe_le_coe.mpr le_top)
    · exact Work.KMTAreas.A7.hasCompactSupport_etaCut (-((P.natDegree : ℤ) * 2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)))
    · exact Work.KMTAreas.A7.integrable_varphitildeNt_aux P P.natDegree N k₂ t
    · exact hnA₂
    · exact hs₂ t ht
  have hkerf : ∀ j : ℤ, Work.KMTPlan.A6.maeKer ρ l₁ (Work.KMTAreas.A7.varphiNt N k₁ t) j
      = (∑ α ∈ Work.KMTAreas.A7.diffFreqs ρ l₁, fourier (T := 1) (-j) α)
        * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphiNt N k₁ t) j :=
    fun j => Work.KMTPlan.A6.maeKer_fourier ρ l₁
      (Work.KMTAreas.A7.lacBump_integrable_varphiNt N k₁ t) j
  have hkerg : ∀ j : ℤ, Work.KMTPlan.A6.maeKer ρ l₂ (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t) j
      = (∑ β ∈ Work.KMTAreas.A7.diffFreqs ρ l₂, fourier (T := 1) (-j) β)
        * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t) j :=
    fun j => Work.KMTPlan.A6.maeKer_fourier ρ l₂
      (Work.KMTAreas.A7.integrable_varphitildeNt_aux P P.natDegree N k₂ t) j
  have hL := Work.KMTAreas.A7.kernCompArithCollapseGen
    (A₁ := Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁)
    (B₁ := Work.KMTAreas.A7.diffFreqs ρ l₁)
    (A₂ := Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂)
    (B₂ := Work.KMTAreas.A7.diffFreqs ρ l₂)
    (W := fun α β => Work.KMTAreas.A7.mZ P (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) α β)
    (m₁ := (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))) (m₂ := (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))) (f := (Work.KMTAreas.A7.varphiNt N k₁ t)) (g := (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t)) (a := j₁) (b := j₂)
    (Work.KMTPlan.A6.mae_diffFreqs_subset ρ l₁) (Work.KMTPlan.A6.mae_diffFreqs_subset ρ l₂)
    hsm₁ hsm₂ hsf hsg hcol₁ hcol₂
  have hR := Work.KMTAreas.A7.kernCompArithCollapseGen
    (A₁ := Work.KMTAreas.A7.diffFreqs ρ l₁) (B₁ := Work.KMTAreas.A7.diffFreqs ρ l₁)
    (A₂ := Work.KMTAreas.A7.diffFreqs ρ l₂) (B₂ := Work.KMTAreas.A7.diffFreqs ρ l₂)
    (W := fun α β => Work.KMTAreas.A7.mZ P (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) α β)
    (m₁ := (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))) (m₂ := (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))) (f := (Work.KMTAreas.A7.varphiNt N k₁ t)) (g := (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t)) (a := j₁) (b := j₂)
    (Finset.Subset.refl _) (Finset.Subset.refl _)
    hsm₁ hsm₂ hsf hsg
    (fun α hα α₁ hα₁ => hcol₁ α (Work.KMTPlan.A6.mae_diffFreqs_subset ρ l₁ hα) α₁ hα₁)
    (fun β hβ β₁ hβ₁ => hcol₂ β (Work.KMTPlan.A6.mae_diffFreqs_subset ρ l₂ hβ) β₁ hβ₁)
  have hKc : (Work.KMTPlan.A6.maeTwKernel ρ P l₁ l₂ (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂))) (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂))) : ℤ → ℤ → ℂ) = (fun j₁ j₂ => (∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁, ∑ β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂, Work.KMTAreas.A7.mZ P (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) α β * fourier (T := 1) (-j₁) α * fourier (T := 1) (-j₂) β) * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂))) j₁ * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂))) j₂) := by
    funext a b
    rw [Work.KMTPlan.A6.maeTwKernel, Work.KMTAreas.A7.arithKernel]
  have hKe : (Work.KMTAreas.A7.arithKerMWin ρ P (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)) l₁ l₂ : ℤ → ℤ → ℂ) = (fun j₁ j₂ => (∑ α ∈ Work.KMTAreas.A7.diffFreqs ρ l₁, ∑ β ∈ Work.KMTAreas.A7.diffFreqs ρ l₂, Work.KMTAreas.A7.mZ P (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) α β * fourier (T := 1) (-j₁) α * fourier (T := 1) (-j₂) β) * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂))) j₁ * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂))) j₂) := by
    funext a b
    simp only [Work.KMTAreas.A7.arithKerMWin, Work.KMTPlan.A6.arithKernelEx]
  have hk1 : (Work.KMTPlan.A6.maeKer ρ l₁ (Work.KMTAreas.A7.varphiNt N k₁ t) : ℤ → ℂ) = (fun j => (∑ α₁ ∈ Work.KMTAreas.A7.diffFreqs ρ l₁, fourier (T := 1) (-j) α₁) * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphiNt N k₁ t) j) := funext hkerf
  have hk2 : (Work.KMTPlan.A6.maeKer ρ l₂ (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t) : ℤ → ℂ) = (fun j => (∑ β₁ ∈ Work.KMTAreas.A7.diffFreqs ρ l₂, fourier (T := 1) (-j) β₁) * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t) j) := funext hkerg
  rw [hKc, hKe, hk1, hk2]
  exact hL.trans hR.symm

end

end Work.KMTPlan.A6.UModApprox
