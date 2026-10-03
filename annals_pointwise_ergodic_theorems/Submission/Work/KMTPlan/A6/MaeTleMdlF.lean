/-
# The model-side functional calculus of the large-scale model operator (`mdlPart`)

The model column `mdlPart` of `Submission/Work/KMTPlan/A6/lowLargeScaled.lean` applies the
height-`≤ l` Ionescu--Wainger multiplier `Tle ρ l (φ_{N,t})` to the *narrow* exact-height input
`mdlF ρ u l f = piExact (kmtPj ρ) l (-u) f`.  On the frequency window (the support of the
modulated bump `φ_{N,t}`, which in the main regime is contained in the plateau of
`periodize (etaCut kmtEta (-u))`), this composite is the *exact-height* multiplier
`Tm ρ l (φ_{N,t})` applied to `f`, which is what turns `mdlPart` into a bilinear convolution with
the explicit kernel of `KmodL` (`Submission/Work/KMTPlan/A6/KmodDefs.lean`).

The proof is the composition of two ingredients:

* `Work.KMTPlan.A6.mae_Tle_mdlF_eq_iwConv` (proved, the non-aliasing functional calculus):
  `Tle ρ l (φ) (mdlF ρ u l f) = iwConv (diffFreqs ρ l) (periodize φ · periodize (etaCut kmtEta (-u))) f`;
* `Work.KMTPlan.A6.mae_Phi_eq_one_of_small`: on the arc `ℝ_{≤-u-1}` the cutoff
  `periodize (etaCut kmtEta (-u))` is identically `1` (its plateau is `|θ| ≤ 2^{-u}/2`).
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MaeCollapse
import Submission.Work.KMTPlan.A6.MaeKernels
import Submission.Work.KMTPlan.A6.MaePhiSmall

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.KMTAreas.A7

namespace Work.KMTPlan.A6

/-- Monotonicity of `SupportedInArc` in the scale. -/
lemma mae_supportedInArc_mono {k k' : ℤ} (h : k ≤ k') {Φ : Circle → ℂ}
    (hΦ : SupportedInArc k Φ) : SupportedInArc k' Φ :=
  fun ξ hξ => let ⟨θ, hθ, hθ'⟩ := hΦ ξ hξ; ⟨θ, realArc_mono h hθ, hθ'⟩

/-- **The model-side functional calculus in its final form.**  If the support of the modulated
bump `periodize (varphiNt N k t)` sits inside the plateau `ℝ_{≤-u-1}` of
`periodize (etaCut kmtEta (-u))` and the arithmetic frequencies of height `≤ l` are non-aliasing
at scale `-u`, then

  `Tle ρ l (φ_{N,t}) (mdlF ρ u l f) = Tm ρ l (φ_{N,t}) f`,

i.e. the concrete model input is the exact-height multiplier of the *unprojected* function `f`. -/
theorem mae_Tle_mdlF_eq_Tm (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (u l N k : ℕ) (hu : 1 ≤ u) (t : ℝ)
    {f : ℤ → ℂ} (hf : MemLp f 2 Measure.count)
    (hnA : NonAliasing (-(u : ℤ)) (iwArithFreqs ρ l))
    (hΦ : SupportedInArc (-(u : ℤ) - 1) (periodize (varphiNt N k t))) :
    Tle ρ l (varphiNt N k t) (mdlF ρ u l f) = Tm ρ l (varphiNt N k t) f := by
  show Tle ρ l (varphiNt N k t) (Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) l (-(u : ℤ)) f) = Tm ρ l (varphiNt N k t) f
  have hle : -(u : ℤ) - 1 ≤ -(u : ℤ) := by omega
  have hC1 := mae_Tle_mdlF_eq_iwConv ρ hρ hρ1 u l N k t hf hnA (mae_supportedInArc_mono hle hΦ)
  have hfun : (fun ξ : Circle => periodize (varphiNt N k t) ξ
        * periodize (etaCut Work.KMTContract.kmtEta (-(u : ℤ))) ξ)
      = periodize (varphiNt N k t) := by
    funext ξ
    by_cases hξ : periodize (varphiNt N k t) ξ = 0
    · rw [hξ, zero_mul]
    · obtain ⟨θ, hθ, rfl⟩ := hΦ ξ hξ
      have hk : (2 : ℝ) ^ (-(u : ℤ)) ≤ 1 / 2 := by
        rw [zpow_neg, zpow_natCast]
        have h2u : (2 : ℝ) ≤ (2 : ℝ) ^ u := by
          simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hu
        simpa [one_div] using
          one_div_le_one_div_of_le (show (0 : ℝ) < 2 by norm_num) h2u
      have hθ' : |θ| ≤ (2 : ℝ) ^ (-(u : ℤ)) / 2 := by
        have h2 : |θ| ≤ (2 : ℝ) ^ (-(u : ℤ) - 1) := by
          have hθ'' := hθ
          rw [realArc, Set.mem_Icc] at hθ''
          rw [abs_le]
          exact ⟨by linarith [hθ''.1], by linarith [hθ''.2]⟩
        have he : (2 : ℝ) ^ (-(u : ℤ) - 1) = (2 : ℝ) ^ (-(u : ℤ)) / 2 := by
          rw [zpow_sub₀ (show (2 : ℝ) ≠ 0 by norm_num), zpow_one]
        rwa [he] at h2
      rw [mae_Phi_eq_one_of_small hk hθ', mul_one]
  rw [hC1, hfun]
  rfl

/-- **The model-side pieces as convolutions.**  Combining `mae_Tle_mdlF_eq_Tm` with the definitional
identity `Tm ρ l φ u = convOp (maeKer ρ l φ) u`, the two arguments of `Btwist` in the model column
are the convolutions with the explicit kernels `maeKer ρ lᵢ (φ_{N,t})` — the input shape of
`kernComp` (`maeKmod`). -/
theorem mae_Tle_mdlF_eq_convOp (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (u l N k : ℕ) (hu : 1 ≤ u)
    (t : ℝ) {f : ℤ → ℂ} (hf : MemLp f 2 Measure.count)
    (hnA : NonAliasing (-(u : ℤ)) (iwArithFreqs ρ l))
    (hΦ : SupportedInArc (-(u : ℤ) - 1) (periodize (varphiNt N k t))) :
    Tle ρ l (varphiNt N k t) (mdlF ρ u l f)
      = convOp (maeKer ρ l (varphiNt N k t)) f := by
  rw [mae_Tle_mdlF_eq_Tm ρ hρ hρ1 u l N k hu t hf hnA hΦ]
  rfl

/-- The definitional unfolding used above: `Tm ρ l φ` is the convolution with `maeKer ρ l φ`. -/
theorem mae_Tm_eq_convOp_maeKer (ρ : ℝ) (l : ℕ) (φ : ℝ → ℂ) (u : ℤ → ℂ) :
    Tm ρ l φ u = convOp (maeKer ρ l φ) u := rfl

/-! ## The kernels of the two factors of the model input

The model input of `mdlPart` is the composition
`Tle ρ l (φ_{N,t}) ∘ (mdlF ρ u l)` of the height-`≤ l` multiplier with the narrow exact-height
projection.  Both factors are convolutions with explicit kernels, so their composition is the
convolution with the convolution of the two kernels (`convOp_comp`):

* `Tle ρ l ψ = convOp (maeTleKerA ρ l ψ)` (definitional);
* `mdlF ρ u l f = convOp (exactKer ρ l (-u)) f` (`maeA_mdlF_eq_convOp_exactKer`).

The kernel of the composite is therefore `maeTleKerA ρ l (φ_{N,t}) * exactKer ρ l (-u)`, and the
`Tm`-kernel `maeKer ρ l (φ_{N,t})` is its "ideal" form; the difference is the cross-fibre term
bounded in `NOTES_ModApproxErrCoreExact_ROUTE.md` §12 (`O(2^k/N)`). -/

/-- The kernel of the height-`≤ l` multiplier `Tle ρ l ψ`. -/
noncomputable def maeTleKerA (ρ : ℝ) (l : ℕ) (ψ : ℝ → ℂ) : ℤ → ℂ :=
  Work.Analysis.IWMultiplier.iwKernel
    (Work.Analysis.IonescuWainger.iwSymbolSet (iwArithFreqs ρ l)
      (Work.Analysis.IonescuWainger.periodize ψ))

/-- **`Tle` is the convolution with `maeTleKerA`** (definitional). -/
theorem maeA_Tle_eq_convOp (ρ : ℝ) (l : ℕ) (ψ : ℝ → ℂ) (u : ℤ → ℂ) :
    Tle ρ l ψ u = convOp (maeTleKerA ρ l ψ) u := rfl

/-- **The narrow exact-height projection `mdlF ρ u l` is the convolution with `exactKer ρ l (-u)`.**
`piExact` is defined as the difference `Π_{≤l} - Π_{≤l-1}` and `exactKer` as the difference of the
two `kmtKern`s, so this is the linearity of `convOp` in its kernel together with
`convOp_kmtKern`. -/
theorem maeA_mdlF_eq_convOp_exactKer (ρ : ℝ) (u l : ℕ) {f : ℤ → ℂ}
    (hf : Work.KMTAreas.A5.BoundedZ f) :
    mdlF ρ u l f = convOp (Work.KMTAreas.A7.exactKer ρ l (-(u : ℤ))) f := by
  rcases Nat.eq_zero_or_pos l with hl | hl
  · subst hl
    rw [mdlF, Work.A7.piExact_zero]
    rw [Work.KMTAreas.A7.exactKer, if_pos rfl]
    exact (Work.A7.convOp_kmtKern ρ 0 (-(u : ℤ)) f).symm
  · have hne : l ≠ 0 := Nat.pos_iff_ne_zero.mp hl
    rw [mdlF, Work.A7.piExact_of_ne ρ hne (-(u : ℤ)) f]
    rw [Work.KMTAreas.A7.exactKer, if_neg hne]
    rw [Work.A7.convOp_sub]
    · rw [Work.A7.convOp_kmtKern, Work.A7.convOp_kmtKern]
    · intro x
      exact Work.KMTAreas.A5.summable_kmtKern_mul ρ l (-(u : ℤ)) hf x
    · intro x
      exact Work.KMTAreas.A5.summable_kmtKern_mul ρ (l - 1) (-(u : ℤ)) hf x

end Work.KMTPlan.A6
