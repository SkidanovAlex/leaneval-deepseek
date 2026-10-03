/-
# `Work.KMTPlan.A6.MdlSliceCoreGainBig` — the frozen-`t` core of the large-scale model
estimate at `(2,2,1)` (paper `model-est-2`, `all-all-large-2`)

This file is the `ℓ²`-reduction half of the frozen-`t` slice estimate
`Work.KMTPlan.A6.MdlSliceCoreGain P r C₀ j₁ j₂` (Krause–Mirek–Tao, *Pointwise ergodic theorems
for non-conventional bilinear polynomial averages*, Annals 195 (2022), §8, Theorem
`model-est-2`, estimate `all-all-large-2` at `(p₁,p₂,p) = (2,2,1)`).

## CRITICAL PATH (2026-09-28): this file's target is the unique remaining input of area A6

`Submission/Work/KMTPlan/A6/LowModelGainEstimate.lean` (sorry-free) now proves
`Work.KMTPlan.A6.LowModelGain` as

    have hcore : MdlCoreGain P r C₀ 0 0 :=
      mdlCoreGain_zero_zero P r hr1 C₀ (MdlSliceCoreGainBig P hd r hr C₀ hC₀ hA1 hI 0 0 hj0 hj0)
    exact lowModelGain_of_gainOn P r C₀ (gainOn_smallK P r C₀ hcore)
      (gainOn_highLow …) (gainOn_lowHigh …)

i.e. **the whole A6 chain (`LowModelGain` → `LowCase` → `AreaA6`, and hence
`Work.KMTContract.AreaA6` and the final theorem's composition) now rests on this file's
`MdlSliceCoreGainBig`** (used at `j₁ = j₂ = 0`).  The sibling stub
`MdlSliceCoreGainEstimate` is no longer imported by the chain; `MdlSliceCoreGainAll` imports
*this* file.  So closing this file (or its `j₁ = j₂ = 0` instance) closes area A6.

The fleet's decomposition of the remaining `ℓ²`-case is by now (all stubs, all under
`Submission/Work/KMTPlan/A6/` unless stated): `MdlSlicePktLinF`/`MdlSlicePktLinG` (paper
`(lin-1)`/`(lin-2)` for the A6 packet carriers), `MdlBileTwistOpNorm` (the *sampled* arithmetic
bilinear estimate with gain for arbitrary symbols), `MdlSliceFkrPackets` (paper Corollary
`bilinear-fkr` with the increment hypotheses), plus the *duplicates* delegated from this file
(`MdlSliceLinF`, `MdlSliceLinG`, `BileGeneralR`).  The A7 side of the picture is *proved*:
`lacunaryBumpVarEstimate`/`…G`, `fiberVarSampling`/`…G`, `ModelLargeBound`, `BilinearFkr`,
`Btwist_eq_fiberSum`, `residueLp_mul_le`, `Tle_mdlF_eq_Tm`, `sampling_principle_variation*`
(`Work/BourgainPlan/**`).  The one link no piece supplies is the *sampling transfer*
(paper Theorem `Sampling`, display (5.4)): `ℓ^p(ℤ;V^r) ≃ L^p(𝔸_ℤ;V^r)` for the band-limited
(sampled) model families — without it the discrete `ℓ¹(ℤ)`-norm of the *full* `variationalNorm`
cannot be reached from the `ℓ^r(ℤ)`-norm of the `varPart` that `MdlSliceFkrPackets` provides
(there is no `ℓ¹ ≤ ℓ^r` on `ℤ`); see `NOTES_MdlSliceCoreGainBig_STATE.md` §4.

## What is in this file

* `mdlSliceF`, `mdlSliceG` — the two *packet families* of the frozen slice, i.e. the `f`- and
  `g`-side inputs of the twisted bilinear multiplier, clipped at the core condition;
* `mdlSliceJ_eq_Btwist` — the identification of the frozen slice with the twisted bilinear
  multiplier `Btwist` applied to the two packet families (definitional bookkeeping);
* `MdlSliceCoreGainMemLp` — the target restricted to `ℓ²` inputs;
* `MdlSliceCoreGain_of_memLp` (**proved**) — the reduction of the target to that case: if
  `f ∉ ℓ²` or `g ∉ ℓ²` the right-hand side is `⊤` (the constants of the target are positive), so
  only `f, g ∈ ℓ²(ℤ)` matter.

## What remains (the analytic core, no owner as of this file's last update)

The `ℓ²`-case `MdlSliceCoreGainMemLp` is the paper's §8 argument for `(p₁,p₂) = (2,2)`, in the
workspace's discrete vocabulary.  Its three inputs, and their state:

1. **The arithmetic bilinear estimate** (paper Theorem `bile`): the operator norm
   `L² × L² → L^r` of the arithmetic average is `O(2^{-c_r l})` on the exact-height packets.
   At `r = 1` this is *proved* (`MdlSliceLinF`'s sibling `Work.KMTPlan.A6.MdlBileR1OfImprov`,
   from `ImprovKMT`); the general exponent `2 ≤ r < 2d/(d-1)` is delegated as
   `Work.KMTPlan.A6.BileGeneralR` (the interpolation needs the `Q`-uniform `L^q` bound
   `BilinearAverageLqUniformImprov`, which is in flight — note that as of writing,
   `KMTPlan/A6/BilinearAverageLqUniform.lean` and `KMTPlan/A6/bileInterpIw.lean` do **not
   compile** (they carry proof errors, not sorries), so `MdlBileOfR1` is not importable.)
2. **The sampling transfer** (paper Theorem `Sampling`, their (5.4)): the `ℓ^p(ℤ; V^r)` norm of the
   *discrete* (sampled) model tuple is equivalent to the `L^p(𝔸_ℤ; V^r)` norm of the *adelic* model
   tuple, in the large-scale regime — this is what turns the "value at one adelic point" into the
   average over `Ẑ` that `bile` bounds (`q|A(0)|` is *not* controlled by `∫|A|`), and it is the
   piece the A7 side isolates as the variational fibre sampling
   (`Work.KMTAreas.A7.fiberOpVarSamplingCoreTex`, a stub).  The clean sampling machinery in the
   workspace is `Work.BourgainPlan.IonescuWainger.sampling_principle_variation_decimated`
   (**proved**), plus `…/MSW_pairing`, `…/msw_sampling_lp`, `KMTAreas/A7/msw_sampling_pairing_narrow`
   (**proved**).
3. **The linear lacunary variational estimates** (paper `(lin-1)`, `(lin-2)`) for the two packet
   families at the exponent `R`, `2 < R < r`, in the `ℓ²(ℤ; V^R)` form — delegated as
   `Work.KMTPlan.A6.MdlSliceLinF` and `Work.KMTPlan.A6.MdlSliceLinG`.

With (1)–(3) the assembly is the paper's display after `form-2`: the arithmetic operator norm
(1) into `Work.KMTPlan.A6.BilinearFkr` (**proved**, the paper's Corollary `bilinear-fkr`) with the
exponent `R < r`, Cauchy–Schwarz in the real variable against the two `ℓ²`-norms of (3), and the
transfer (2) — followed by the absorption of the polynomial loss into the gain
(`Work.KMTAreas.A7.ofReal_lossWeight_prod_le`, `lossWeight_mul_le_lcWeight`) and the `t`-uniformity
of the statement.  This file proves the outer reduction; (1)–(3) are the delegated pieces.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlCoreGainBook
import Submission.Work.KMTPlan.A6.MdlBileR1OfImprov
import Submission.Work.KMTAreas.A7.lacunaryBumpGlue
-- NOTE (2026-10-02, A6): the import below was `…A6.MdlCoreGainEstimate` (the *target* file),
-- which made this module — and everything above it (`MdlSliceCoreGainMemLp2`,
-- `MdlAdelicDefs`, `MdlAdelicFormPlus`, `MdlSliceCoreGainAll`, …) — unimportable by that target
-- (import cycle), so no producer of `MdlSliceCoreGain` could ever reach it.  The seven
-- bookkeeping lemmas this file uses (`Btwist_zero_left_fun`, `eLpNorm_variationalNorm_zero`,
-- `mdlSliceJ_eq_zero_of_left/right_zero`, `eq_zero_of_eLpNorm_two_eq_zero`,
-- `memLp_two_count_of_ne_top`, `one_le_lossWeight_mdl`) are declared *verbatim* in the
-- cycle-free `MdlCoreGainBook`, which is what the target file itself imports; repointing here
-- is therefore semantics-preserving (see `MdlCoreGainBook.lean`'s docstring).

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTAreas.A7

/-! ## The two packet families of the frozen slice -/

/-- The `f`-side packet family of the frozen-`t` slice: the IW projection of the modified bump
`φ_{N,t,j₁}` against the exact-height shell `mdlF ρ (uScale ρ L) l₁ f`, `N = ⌊a n⌋`,
`L = max (max l₁ l₂) (max k₁ k₂)`, clipped at the core condition. -/
def mdlSliceF (ρ : ℝ) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (j₁ : ℤ) (t : ℝ)
    (f : ℤ → ℂ) : ℕ → ℤ → ℂ :=
  fun n =>
    if mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
      Tle ρ l₁ (varphiNtj (Nat.floor (a n)) k₁ j₁ t)
        (mdlF ρ (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₁ f)
    else 0

/-- The `g`-side packet family of the frozen-`t` slice. -/
def mdlSliceG (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (j₂ : ℤ)
    (t : ℝ) (g : ℤ → ℂ) : ℕ → ℤ → ℂ :=
  fun n =>
    if mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
      Tle ρ l₂ (varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t)
        (mdlG ρ P (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₂ g)
    else 0

/-- **The frozen slice is the twisted bilinear multiplier applied to the two packet families.** -/
theorem mdlSliceJ_eq_Btwist (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) (t : ℝ) (n : ℕ) (x : ℤ) :
    mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x
      = Btwist ρ P l₁ l₂ (mStarF (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
          (mStargF P.natDegree (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
          (mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n)
          (mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) x := by
  rw [mdlSliceJ_apply, mdlSliceF, mdlSliceG]
  by_cases h : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
  · simp only [h, if_true]
  · simp only [h, if_false]
    exact (congrFun (Btwist_zero_left_fun ρ P l₁ l₂ _ _ _) x).symm

/-- The slice family vanishes when the `f`-side packet family does. -/
theorem mdlSliceJ_eq_zero_of_sliceF_eq_zero (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) (t : ℝ)
    (h : mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f = 0) :
    mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t = 0 := by
  funext n x
  rw [mdlSliceJ_eq_Btwist]
  have h0 : mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n = 0 := by
    rw [h]; rfl
  rw [h0]
  exact congrFun (Btwist_zero_left_fun ρ P l₁ l₂ _ _ _) x

/-! ## The clipped symbol families (the form in which the packet estimates are stated)

The pieces of the fleet's decomposition (`MdlSlicePktLinF`/`…G`, `MdlSliceFkrPackets`,
`MdlBileTwistOpNorm`) are stated for an *arbitrary* symbol family `Ψ` applied to `mdlF`/`mdlG`.
The two lemmas below rewrite this file's packet families — which carry the core clip — in that
form, using the proved `Work.KMTAreas.A7.Tle_ite`; they are what an assembly needs to feed the
pieces with `Ψ = mdlSliceSymbF/G`. -/

/-- The clipped `f`-side symbol family `n ↦ 1_{mdlCore n} · φ_{⌊a n⌋,k₁,t,j₁}`. -/
def mdlSliceSymbF (ρ : ℝ) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (j₁ : ℤ) (t : ℝ) :
    ℕ → ℝ → ℂ :=
  fun n ξ => if mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then varphiNtj (Nat.floor (a n)) k₁ j₁ t ξ else 0

/-- The clipped `g`-side symbol family `n ↦ 1_{mdlCore n} · φ̃_{⌊a n⌋,k₂,t,j₂}`. -/
def mdlSliceSymbG (P : ℤ[X]) (ρ : ℝ) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (j₂ : ℤ)
    (t : ℝ) : ℕ → ℝ → ℂ :=
  fun n ξ => if mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
    varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t ξ else 0

/-- **The `f`-side packet family is `Tle` of its clipped symbol family.** -/
lemma mdlSliceF_eq (ρ : ℝ) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (j₁ : ℤ) (t : ℝ)
    (f : ℤ → ℂ) :
    mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f
      = fun n => Tle ρ l₁ (mdlSliceSymbF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t n)
          (mdlF ρ (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₁ f) := by
  funext n x
  have hsym : mdlSliceSymbF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t n
      = fun ξ : ℝ => if mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
          varphiNtj (Nat.floor (a n)) k₁ j₁ t ξ else 0 := rfl
  rw [hsym, Tle_ite ρ l₁ (mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n)]
  by_cases h : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n <;> simp [mdlSliceF, h]

/-- **The `g`-side packet family is `Tle` of its clipped symbol family.** -/
lemma mdlSliceG_eq (P : ℤ[X]) (ρ : ℝ) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (j₂ : ℤ)
    (t : ℝ) (g : ℤ → ℂ) :
    mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g
      = fun n => Tle ρ l₂ (mdlSliceSymbG P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n)
          (mdlG ρ P (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₂ g) := by
  funext n x
  have hsym : mdlSliceSymbG P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n
      = fun ξ : ℝ => if mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
          varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t ξ else 0 := rfl
  rw [hsym, Tle_ite ρ l₂ (mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n)]
  by_cases h : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n <;> simp [mdlSliceG, h]

/-! ## The target restricted to `ℓ²` inputs -/

/-- **`MdlSliceCoreGain`, restricted to `f, g ∈ ℓ²(ℤ)`.**  By
`MdlSliceCoreGain_of_memLp` this is the only non-degenerate case of the target. -/
def MdlSliceCoreGainMemLp (P : ℤ[X]) (r : ℝ≥0) (C₀ : ℕ) (j₁ j₂ : ℤ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : ℝ≥0 → ℝ≥0,
      ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f g : ℤ → ℂ),
        1 < Λ → Lacunary Λ a → (∀ n, 1 ≤ a n) → t ∈ Set.Icc (1 / 2 : ℝ) 1 →
        (k₁ = 0 → j₁ ≠ -1) → (k₂ = 0 → j₂ ≠ -1) →
        MemLp f 2 Measure.count → MemLp g 2 Measure.count →
        eLpNorm (fun x : ℤ => variationalNorm r
            (fun n : ℕ => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x))
          1 Measure.count
          ≤ (K Λ : ℝ≥0∞) * ENNReal.ofReal (lossWeight A ρ l₁ l₂ k₁ k₂
              * (2 : ℝ) ^ (-(c * (max (l₁ : ℝ) (l₂ : ℝ))))) *
            eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count

/-- **The target `MdlSliceCoreGain` follows from its `ℓ²` case.**  If `f ∉ ℓ²(ℤ)` or `g ∉ ℓ²(ℤ)`
the right-hand side of the target's estimate is `⊤` (the multiplicative constants
`K(Λ) · lossWeight · 2^{-c max(l₁,l₂)}` of `MdlSliceCoreGain` are bounded below by a positive
number, see `one_le_lossWeight_mdl`), while if `f, g ∈ ℓ²(ℤ)` the hypothesis applies. -/
theorem MdlSliceCoreGain_of_memLp (P : ℤ[X]) (r : ℝ≥0) (hr : 1 ≤ r) (C₀ : ℕ) (j₁ j₂ : ℤ)
    (h : MdlSliceCoreGainMemLp P r C₀ j₁ j₂) : MdlSliceCoreGain P r C₀ j₁ j₂ := by
  obtain ⟨c, hc, A, hA, ρ₀, hρ₀, h'⟩ := h
  refine ⟨c, hc, A, hA, ρ₀, hρ₀, ?_⟩
  intro ρ hρ hρle
  obtain ⟨K, hK⟩ := h' ρ hρ hρle
  refine ⟨fun Λ => max (K Λ) 1, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ t f g hΛ ha ha1 ht hj₁ hj₂
  set W : ℝ≥0∞ := ENNReal.ofReal (lossWeight A ρ l₁ l₂ k₁ k₂
      * (2 : ℝ) ^ (-(c * (max (l₁ : ℝ) (l₂ : ℝ))))) with hW
  have hW0 : W ≠ 0 := by
    rw [hW, Ne, ENNReal.ofReal_eq_zero, not_le]
    exact mul_pos (lt_of_lt_of_le zero_lt_one (one_le_lossWeight_mdl hA hρ.le l₁ l₂ k₁ k₂))
      (Real.rpow_pos_of_pos (by norm_num) _)
  have hK0 : ((max (K Λ) 1 : ℝ≥0) : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (by positivity)
  -- the two vanishing cases
  by_cases hf0 : eLpNorm f 2 Measure.count = 0
  · rw [eq_zero_of_eLpNorm_two_eq_zero hf0]
    have hfam : (fun x : ℤ => variationalNorm r (fun n : ℕ =>
        mdlSliceJ ρ P C₀ a 0 g l₁ l₂ k₁ k₂ j₁ j₂ t n x))
        = fun _ : ℤ => variationalNorm r (fun _ : ℕ => (0 : ℂ)) := by
      funext x
      have h0 : (fun n : ℕ => mdlSliceJ ρ P C₀ a 0 g l₁ l₂ k₁ k₂ j₁ j₂ t n x)
          = fun _ : ℕ => (0 : ℂ) := by
        funext n
        simp [mdlSliceJ_eq_zero_of_left_zero]
      rw [h0]
    rw [hfam, eLpNorm_variationalNorm_zero hr]
    exact bot_le
  by_cases hg0 : eLpNorm g 2 Measure.count = 0
  · rw [eq_zero_of_eLpNorm_two_eq_zero hg0]
    have hfam : (fun x : ℤ => variationalNorm r (fun n : ℕ =>
        mdlSliceJ ρ P C₀ a f 0 l₁ l₂ k₁ k₂ j₁ j₂ t n x))
        = fun _ : ℤ => variationalNorm r (fun _ : ℕ => (0 : ℂ)) := by
      funext x
      have h0 : (fun n : ℕ => mdlSliceJ ρ P C₀ a f 0 l₁ l₂ k₁ k₂ j₁ j₂ t n x)
          = fun _ : ℕ => (0 : ℂ) := by
        funext n
        simp [mdlSliceJ_eq_zero_of_right_zero]
      rw [h0]
    rw [hfam, eLpNorm_variationalNorm_zero hr]
    exact bot_le
  -- the right-hand side is `⊤` as soon as `f ∉ ℓ²` or `g ∉ ℓ²`
  by_cases hfT : eLpNorm f 2 Measure.count = ⊤
  · have htop : ((max (K Λ) 1 : ℝ≥0) : ℝ≥0∞) * W * eLpNorm f 2 Measure.count
        * eLpNorm g 2 Measure.count = ⊤ := by
      rw [hfT, ENNReal.mul_top (mul_ne_zero hK0 hW0), ENNReal.top_mul hg0]
    rw [htop]
    exact le_top
  by_cases hgT : eLpNorm g 2 Measure.count = ⊤
  · have htop : ((max (K Λ) 1 : ℝ≥0) : ℝ≥0∞) * W * eLpNorm f 2 Measure.count
        * eLpNorm g 2 Measure.count = ⊤ := by
      rw [hgT, ENNReal.mul_top (mul_ne_zero (mul_ne_zero hK0 hW0) hf0)]
    rw [htop]
    exact le_top
  -- the main case
  have hf2 : MemLp f 2 Measure.count := memLp_two_count_of_ne_top hfT
  have hg2 : MemLp g 2 Measure.count := memLp_two_count_of_ne_top hgT
  have hle : (K Λ : ℝ≥0∞) ≤ ((max (K Λ) 1 : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_le_coe]
    exact le_max_left _ _
  refine le_trans (hK a Λ l₁ l₂ k₁ k₂ t f g hΛ ha ha1 ht hj₁ hj₂ hf2 hg2) ?_
  calc (K Λ : ℝ≥0∞) * W * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count
      ≤ (((max (K Λ) 1 : ℝ≥0) : ℝ≥0∞) * W) * eLpNorm f 2 Measure.count
          * eLpNorm g 2 Measure.count := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle bot_le) bot_le) bot_le

end
end Work.KMTPlan.A6
