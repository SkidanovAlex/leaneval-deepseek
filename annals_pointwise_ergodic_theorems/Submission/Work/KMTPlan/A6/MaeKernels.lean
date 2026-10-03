/-
# The model-side kernels of the exact-height single-scale model approximation (`mdlPart`)

This module collects the explicit convolution kernels attached to the two sides of the §6 model
approximation of area A6, so that the several sub-proofs of
`Work.KMTPlan.A6.ModApproxErrCoreExact` (the fibre decompositions of the concrete and of the
model kernel, the summability/measurability lemmas, the mass bound) can be stated and proved in
modules that import this one.

* `maeKer ρ l φ` — the kernel of the *exact-height* IW multiplier `Tm ρ l φ` (Fourier
  coefficients of `∑_{γ ∈ (ℚ/ℤ)_l} periodize φ (·-γ)`);
* `maeKerL ρ l ψ` — the kernel of the *height-`≤ l`* multiplier `Tle ρ l ψ`;
* `maeTwKernel ρ P l₁ l₂ m₁ m₂` — the kernel of the twisted bilinear multiplier `Btwist`;
* `maeCompKer ρ l u ψ`, `maeCompKerG ρ P l u ψ` — the convolution products realising the
  composition `Tle ρ l ψ ∘ mdlF ρ u l`, resp. `Tle ρ l ψ ∘ mdlG ρ P u l`;
* `maeKmod` — the `t`-integral of `kernComp` of the three kernels above, i.e. the *ideal*
  (exact-height `Tm`-based) model kernel of `mdlPart`;
* `maeKmodX` — the same with the honest composite kernels `maeCompKer` / `maeCompKerG`.

The two differ by the "cross" fibres which exist when the arithmetic frequencies of height `≤ l`
are not separated at the window scale `-u`; no non-aliasing hypothesis is used in this module.
-/
import Mathlib
import Submission.Work.A7.ModelApproxCore_Fpiece_convOp
import Submission.Work.KMTPlan.A6.MdlDecayDefs

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar
open Work.KMTContract
open Work.KMTAreas.A7

noncomputable section

/-! ## The model-side kernel reduction

`mdlPart` is the `t`-integral of the twisted bilinear multiplier `Btwist ρ P l₁ l₂ (mStarF u)
(mStargF d u)` applied to the two modulated exact-height pieces
`Tle ρ lᵢ (φ_{N,t}) (mdlF ρ u lᵢ f)`.  Its *kernel*, as a bilinear operator in `(f, g)`, is the
`t`-integral of the composition of the arithmetic kernel with the two `Tm`-kernels:

  `KmodL n = ∫_{1/2}^1 kernComp (arithKernel ⊗ cw (mStarF u) ⊗ cw (mStargF d u))
                (TmKernel ρ l₁ (φ_{N,t})) (TmKernel ρ l₂ (φ̃_{N,t})) dt`,

where `u = uScale ρ (max (max l₁ l₂) (max k₁ k₂))` (`maeKmod` below).  The reduction
`mdlPart = bilinOp (KmodL …)` on the core uses

* `Btwist` as a bilinear convolution (`Btwist_eq_bilinOp`, definitional);
* the functional calculus `Tle ρ l (φ_{N,t}) (mdlF ρ u l f) = Tm ρ l (φ_{N,t}) f` for `ℓ²` inputs
  (non-aliasing of `(l, -u)`, satisfied in the main regime, plus `periodize (etaCut kmtEta (-u)) = 1`
  on the frequency window `|θ| ≤ 2^{k}/N ≤ 2^{-2u}`);
* `Tm ρ l φ = convOp (TmKernel ρ l φ)` (definitional) and `ModelApproxCore_kernelComp`;
* the interchange of the `t`-integral with the bilinear convolution (`intervalIntegral_bilinOp`).
-/

/-- The kernel of the exact-height Ionescu--Wainger multiplier `Tm ρ l φ`, i.e. the Fourier
coefficients of `iwSymbolSet (diffFreqs ρ l) (periodize φ)`.  (Definitionally the same object as
`Work.KMTPlan.A6.TmKernel` of the A6 cluster, repeated here so that this file does not depend on
the cluster module while it is being re-organised.) -/
noncomputable def maeKer (ρ : ℝ) (l : ℕ) (φ : ℝ → ℂ) : ℤ → ℂ :=
  Work.Analysis.IWMultiplier.iwKernel
    (Work.Analysis.IonescuWainger.iwSymbolSet (diffFreqs ρ l)
      (Work.Analysis.IonescuWainger.periodize φ))

/-- The kernel of the twisted bilinear multiplier of §6 as a bilinear kernel:
`(j₁,j₂) ↦ arithKernel ρ P (arithQ ρ L) l₁ l₂ j₁ j₂ · cw m₁ j₁ · cw m₂ j₂`. -/
noncomputable def maeTwKernel (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ) : ℤ → ℤ → ℂ :=
  fun j₁ j₂ => arithKernel ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ j₁ j₂ * cw m₁ j₁ * cw m₂ j₂

/-- **`Btwist` is the bilinear convolution with `maeTwKernel`.** -/
theorem Btwist_eq_bilinOp_maeTwKernel (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ) (h k : ℤ → ℂ) :
    Btwist ρ P l₁ l₂ m₁ m₂ h k = bilinOp (maeTwKernel ρ P l₁ l₂ m₁ m₂) h k := rfl

/-- **The kernel of the model column `mdlPart`** on the core: the `t`-integral of the composition
of the twisted kernel with the two `Tm`-kernels of the modulated exact-height pieces. -/
noncomputable def maeKmod (ρ : ℝ) (P : ℤ[X]) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ n : ℕ) :
    ℤ → ℤ → ℂ :=
  fun j₁ j₂ =>
    ∫ t in (1/2 : ℝ)..1,
      kernComp (maeTwKernel ρ P l₁ l₂
          (mStarF (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
          (mStargF P.natDegree (uScale ρ (max (max l₁ l₂) (max k₁ k₂)))))
        (maeKer ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t))
        (maeKer ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t)) j₁ j₂


/-! ## The composite kernel of `Tle ρ l ψ ∘ mdlF ρ u l`

The model column `mdlPart` applies the height-`≤ l` multiplier `Tle ρ l (φ_{N,t})` to the narrow
exact-height input `mdlF ρ u l f = piExact (kmtPj ρ) l (-u) f`.  Both factors are convolutions
with explicit kernels (`maeKerL`, `exactKer`), so their composition is the convolution with the
convolution product `maeCompKer` — no symbol algebra and in particular *no* non-aliasing
hypothesis is needed for this step. -/

/-- The kernel of the height-`≤ l` Ionescu--Wainger multiplier `Tle ρ l ψ`. -/
noncomputable def maeKerL (ρ : ℝ) (l : ℕ) (ψ : ℝ → ℂ) : ℤ → ℂ :=
  Work.Analysis.IWMultiplier.iwKernel
    (Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
      (Work.Analysis.IonescuWainger.periodize ψ))

/-- **`Tle` is the convolution with `maeKerL`** (definitional). -/
theorem mae_Tle_apply (ρ : ℝ) (l : ℕ) (ψ : ℝ → ℂ) (v : ℤ → ℂ) :
    Tle ρ l ψ v = convOp (maeKerL ρ l ψ) v := rfl

/-- **The narrow exact-height projection `mdlF ρ u l` is the convolution with `exactKer ρ l (-u)`.** -/
theorem mae_mdlF_eq_convOp_exactKer (ρ : ℝ) (u l : ℕ) {f : ℤ → ℂ}
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

/-- **The narrow exact-height projection `mdlG ρ P u l` is the convolution with
`exactKer ρ l (-(d u))`**, `d = P.natDegree`. -/
theorem mae_mdlG_eq_convOp_exactKer (ρ : ℝ) (P : ℤ[X]) (u l : ℕ) {g : ℤ → ℂ}
    (hg : Work.KMTAreas.A5.BoundedZ g) :
    mdlG ρ P u l g
      = convOp (Work.KMTAreas.A7.exactKer ρ l (-((P.natDegree : ℤ) * (u : ℤ)))) g := by
  rcases Nat.eq_zero_or_pos l with hl | hl
  · subst hl
    rw [mdlG, Work.A7.piExact_zero]
    rw [Work.KMTAreas.A7.exactKer, if_pos rfl]
    exact (Work.A7.convOp_kmtKern ρ 0 (-((P.natDegree : ℤ) * (u : ℤ))) g).symm
  · have hne : l ≠ 0 := Nat.pos_iff_ne_zero.mp hl
    rw [mdlG, Work.A7.piExact_of_ne ρ hne (-((P.natDegree : ℤ) * (u : ℤ))) g]
    rw [Work.KMTAreas.A7.exactKer, if_neg hne]
    rw [Work.A7.convOp_sub]
    · rw [Work.A7.convOp_kmtKern, Work.A7.convOp_kmtKern]
    · intro x
      exact Work.KMTAreas.A5.summable_kmtKern_mul ρ l (-((P.natDegree : ℤ) * (u : ℤ))) hg x
    · intro x
      exact Work.KMTAreas.A5.summable_kmtKern_mul ρ (l - 1) (-((P.natDegree : ℤ) * (u : ℤ))) hg x

/-- The composite kernel of `Tle ρ l ψ ∘ mdlF ρ u l`. -/
noncomputable def maeCompKer (ρ : ℝ) (l u : ℕ) (ψ : ℝ → ℂ) : ℤ → ℂ :=
  fun j => ∑' m : ℤ, maeKerL ρ l ψ m * Work.KMTAreas.A7.exactKer ρ l (-(u : ℤ)) (j - m)

/-- The composite kernel of `Tle ρ l ψ ∘ mdlG ρ P u l`. -/
noncomputable def maeCompKerG (ρ : ℝ) (P : ℤ[X]) (l u : ℕ) (ψ : ℝ → ℂ) : ℤ → ℂ :=
  fun j => ∑' m : ℤ, maeKerL ρ l ψ m
    * Work.KMTAreas.A7.exactKer ρ l (-((P.natDegree : ℤ) * (u : ℤ))) (j - m)


/-- **The `t`-integral of the *honest* composite kernel of the model column.**  This is the
kernel of `mdlPart` obtained without any non-aliasing hypothesis: the model input
`Tle ρ lᵢ (φ_{N,t}) (mdlF ρ u lᵢ f)` is the convolution with `maeCompKer ρ lᵢ u (φ_{N,t})`. -/
noncomputable def maeKmodX (ρ : ℝ) (P : ℤ[X]) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ n : ℕ) :
    ℤ → ℤ → ℂ :=
  fun j₁ j₂ =>
    ∫ t in (1/2 : ℝ)..1,
      kernComp (maeTwKernel ρ P l₁ l₂
          (mStarF (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
          (mStargF P.natDegree (uScale ρ (max (max l₁ l₂) (max k₁ k₂)))))
        (maeCompKer ρ l₁ (uScale ρ (max (max l₁ l₂) (max k₁ k₂)))
          (varphiNt (Nat.floor (a n)) k₁ t))
        (maeCompKerG ρ P l₂ (uScale ρ (max (max l₁ l₂) (max k₁ k₂)))
          (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t)) j₁ j₂

/-! ## The fibre form of the two linear kernels

Both `maeKer` and `maeKerL` are Fourier coefficients of a finite translate-sum of a periodised
bump, so by `Work.KMTPlan.A6.IwKernelArithChar` they factor as the arithmetic character sum of
the corresponding frequency set times the *continuous* Fourier transform `cw` of the bump.  These
two identities are the entry point of every fibre (de Leeuw) argument below. -/

/-- **Fibre form of the exact-height kernel.** -/
theorem maeKer_fourier (ρ : ℝ) (l : ℕ) {φ : ℝ → ℂ} (hφ : MeasureTheory.Integrable φ) (j : ℤ) :
    maeKer ρ l φ j = (∑ α ∈ diffFreqs ρ l, fourier (T := 1) (-j) α) * cw φ j :=
  IwKernelArithChar (diffFreqs ρ l) hφ j

/-- **Fibre form of the height-`≤ l` kernel.** -/
theorem maeKerL_fourier (ρ : ℝ) (l : ℕ) {ψ : ℝ → ℂ} (hψ : MeasureTheory.Integrable ψ) (j : ℤ) :
    maeKerL ρ l ψ j
      = (∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l, fourier (T := 1) (-j) α) * cw ψ j :=
  IwKernelArithChar (Work.Analysis.IonescuWainger.iwArithFreqs ρ l) hψ j

end

end Work.KMTPlan.A6
