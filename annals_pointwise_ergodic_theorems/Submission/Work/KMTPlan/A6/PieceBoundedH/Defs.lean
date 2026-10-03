/-
# The vocabulary of the bounded-height model piece (`Work.KMTPlan.A6.ModelPieceBoundedH`)

This module fixes the objects used by the bounded-height model bound
`Work.KMTPlan.A6.PieceBoundedH.modelPiece`:

* `mdlKernel` — the kernel of the twisted bilinear multiplier `Btwist` of §6 in the form used by
  the slice-kernel bound `Work.Analysis.Variational.SliceKernelL1`
  (`Btwist_bilinOp_apply` below is the definitional identification);
* `sliceF`, `sliceG` — the two *packet families* of the frozen-`t` slice of the model tuple
  (the families `mdlSliceF … 0 t f` and `mdlSliceG … 0 t g` of
  `Submission/Work/KMTPlan/A6/MdlSliceCoreGainBig.lean`);
* `SliceFBound`, `SliceGBound` — the two *bounded-height packet estimates* into which the
  model piece is decomposed (the `(2,2,1)`-instances at bounded arithmetic height of the paper's
  linear lacunary variational estimates `(lin-1)`/`(lin-2)`, with the loss absorbed into a
  constant depending on `ρ, B` — see `NOTES_A6_PieceBoundedH_SESSION.md`);
* `KernelMassBound` — the `ℓ¹(ℤ²)`-mass bound for `mdlKernel` at bounded height.

## Why the height bound matters

`lcL l₁ l₂ k₁ k₂ = max (max l₁ l₂) (max k₁ k₂) ≤ B` bounds all four arithmetic/scale parameters of
the model operator, hence also `uScale ρ (lcL …) ≤ uScale ρ B` and the arithmetic frequency sets
`iwArithFreqs ρ lᵢ`.  Consequently *every* loss that the general (gain-carrying) statement of
Theorem `varp` has to absorb — the sieve mass `sieveMass ρ l₁ = 2^{Θ(l₁)}` of
`Work.A7Hi2.SieveAssembly.eLpNorm_variationalNorm_lpf_le_sieveMass'`, the `(1+l)²`/`lossWeight`
factors of the A7 assembly, and the finite sets of "bad scales" — is a constant depending only on
`ρ, B`, and may be absorbed into `K Λ`.  This is what makes the bounded-height pieces provable
without the smallness restriction on `ρ` (`ρ ≤ 1/(2C₀)`) that the general A6/A7 statements carry.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6.PieceBoundedH

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTAreas.A7

/-- The kernel of the twisted bilinear multiplier `Btwist ρ P l₁ l₂ (m_*) (m_*)` of §6, as a
function of the two summation variables: the arithmetic kernel times the two continuous
Fourier-coefficient sequences `cw (mStarF u)`, `cw (mStargF d u)`, with `u = uScale ρ (lcL …)`. -/
noncomputable def mdlKernel (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ k₁ k₂ : ℕ) : ℤ → ℤ → ℂ :=
  fun i j =>
    Work.KMTAreas.A7.arithKernel ρ P (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) l₁ l₂ i j
      * Work.KMTAreas.A7.cw
          (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂))) i
      * Work.KMTAreas.A7.cw
          (Work.KMTAreas.A7.mStargF P.natDegree
            (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂))) j

/-- `Btwist` is the slice kernel associated to `mdlKernel` (definitional). -/
theorem Btwist_eq_mdlKernel_apply (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ k₁ k₂ : ℕ)
    (h k : ℤ → ℂ) (x : ℤ) :
    Work.KMTAreas.A7.Btwist ρ P l₁ l₂
        (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂)))
        (Work.KMTAreas.A7.mStargF P.natDegree
          (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂))) h k x
      = ∑' i : ℤ, ∑' j : ℤ, mdlKernel ρ P l₁ l₂ k₁ k₂ i j * h (x - i) * k (x - j) := rfl

/-- **The `f`-side packet family of the frozen-`t` slice** of the model tuple: the exact-height
Ionescu--Wainger multiplier `T^{≤l₁}_{φ_{N,t}}` of the modulated bump
`φ_{N,t}(ξ) = φ_N(ξ)e(Ntξ)` applied to the exact-height shell `mdlF ρ (uScale ρ L) l₁ f`,
`N = ⌊a n⌋`, `L = lcL l₁ l₂ k₁ k₂`, clipped at the core condition. -/
noncomputable def sliceF (ρ : ℝ) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ)
    (f : ℤ → ℂ) : ℕ → ℤ → ℂ :=
  fun n =>
    if mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
      Work.KMTAreas.A7.Tle ρ l₁ (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t)
        (mdlF ρ (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂)) l₁ f)
    else 0

/-- **The `g`-side packet family of the frozen-`t` slice** of the model tuple, with the
`d`-fold rescaled modulation `φ̃_{N,t}(ξ) = φ̃_N(ξ)e(P(Nt)ξ)`. -/
noncomputable def sliceG (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ)
    (g : ℤ → ℂ) : ℕ → ℤ → ℂ :=
  fun n =>
    if mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
      Work.KMTAreas.A7.Tle ρ l₂
        (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t)
        (mdlG ρ P (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂)) l₂ g)
    else 0

/-- `sliceF` is the `f`-side packet family `mdlSliceF … 0 t f` (definitional). -/
theorem sliceF_eq_mdlSliceF (ρ : ℝ) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ)
    (f : ℤ → ℂ) :
    sliceF ρ C₀ a l₁ l₂ k₁ k₂ t f
      = fun n => if mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
          Work.KMTAreas.A7.Tle ρ l₁ (Work.KMTPlan.A6.varphiNtj (Nat.floor (a n)) k₁ 0 t)
            (mdlF ρ (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂)) l₁ f)
        else 0 := by
  funext n x
  by_cases h : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
  · simp only [sliceF, if_pos h]
    rw [Work.KMTPlan.A6.varphiNtj_zero]
  · simp only [sliceF, if_pos h, if_neg h]

/-- `sliceG` is the `g`-side packet family `mdlSliceG … 0 t g` (definitional). -/
theorem sliceG_eq_mdlSliceG (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ)
    (t : ℝ) (g : ℤ → ℂ) :
    sliceG ρ P C₀ a l₁ l₂ k₁ k₂ t g
      = fun n => if mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
          Work.KMTAreas.A7.Tle ρ l₂
            (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ 0 t)
            (mdlG ρ P (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂)) l₂ g)
        else 0 := by
  funext n x
  by_cases h : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
  · simp only [sliceG, if_pos h]
    rw [Work.KMTPlan.A6.varphitildeNtj_zero]
  · simp only [sliceG, if_pos h, if_neg h]

/-! ## The three inputs of the bounded-height model piece -/

/-- **The `f`-side bounded-height packet estimate** (the `(2,2,1)`-instance of the paper's linear
lacunary variational estimate `(lin-1)` at bounded arithmetic height): for every `ρ ∈ (0,1]` and
every height bound `B` there is `K : ℝ≥0 → ℝ≥0` such that, uniformly in the `Λ`-lacunary family
`a`, in the multi-index with `lcL l₁ l₂ k₁ k₂ ≤ B`, in `t ∈ [1/2,1]` and in `f`,

  `‖ Vʳ (n ↦ 1_{core n} · T^{≤l₁}_{φ_{N_n,t}}(Π_{l₁,≤-u}f)) ‖_{ℓ²(ℤ)} ≤ K(Λ) ‖f‖_{ℓ²(ℤ)}`,

`N_n = ⌊a n⌋`, `u = uScale ρ (lcL …)`. -/
def SliceFBound (r : NNReal) (C₀ : ℕ) (ρ : ℝ) (B : ℕ) : Prop :=
  ∃ K : NNReal → NNReal,
    ∀ (a : ℕ → ℝ≥0) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ),
      1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      t ∈ Set.Icc (1 / 2 : ℝ) 1 →
      lcL l₁ l₂ k₁ k₂ ≤ B →
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => sliceF ρ C₀ a l₁ l₂ k₁ k₂ t f n x))
        2 MeasureTheory.Measure.count
      ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count

/-- **The `g`-side bounded-height packet estimate** (the `(2,2,1)`-instance of `(lin-2)` at
bounded arithmetic height). -/
def SliceGBound (P : Polynomial ℤ) (r : NNReal) (C₀ : ℕ) (ρ : ℝ) (B : ℕ) : Prop :=
  ∃ K : NNReal → NNReal,
    ∀ (a : ℕ → ℝ≥0) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ),
      1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      t ∈ Set.Icc (1 / 2 : ℝ) 1 →
      lcL l₁ l₂ k₁ k₂ ≤ B →
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => sliceG ρ P C₀ a l₁ l₂ k₁ k₂ t g n x))
        2 MeasureTheory.Measure.count
      ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count

/-- **The `ℓ¹(ℤ²)`-mass of the model kernel is bounded at bounded height.** -/
def KernelMassBound (ρ : ℝ) (P : Polynomial ℤ) (B : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (l₁ l₂ k₁ k₂ : ℕ), lcL l₁ l₂ k₁ k₂ ≤ B →
    (Summable fun p : ℤ × ℤ => ‖mdlKernel ρ P l₁ l₂ k₁ k₂ p.1 p.2‖) ∧
    (∑' p : ℤ × ℤ, ‖mdlKernel ρ P l₁ l₂ k₁ k₂ p.1 p.2‖) ≤ C

end

end Work.KMTPlan.A6.PieceBoundedH
