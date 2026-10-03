/-
# The large-scale model estimate at `(2,2,1)` with the exponential gain (area A6)

Target: `Work.KMTPlan.A6.LowModelGain P r C₀`, i.e. `LowBound P r C₀` for the family

  `mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
     = ∫_{1/2}^1 Btwist_{m_*}(T^{l₁}_{φ_{N,t}} F, T^{l₂}_{φ̃_{N,t}} G)(x) dt`,
  `N = ⌊a n⌋`, `F = piExact (kmtPj ρ) l₁ 0 f`, `G = piExact (kmtPj ρ) l₂ 0 g`,

on the large scales `N > splitCut ρ L` in the main regime `k + 2u ≤ Log N`: Krause--Mirek--Tao,
Theorem `model-est` (§6--§8) at `p₁ = p₂ = 2`, `p = 1`, estimate `all-all-large-2`.

## The decomposition (`Submission/Work/KMTPlan/A6/MdlDefs.lean`)

The target is proved by splitting on `max k₁ k₂` against `max l₁ l₂`
(`L = lcL l₁ l₂ k₁ k₂ = max (max l₁ l₂) (max k₁ k₂)`):

* **Case A** (`max k ≤ max l`, `mdlGain_of_core_smallK` below): here `L = max l₁ l₂`, and the
  *arithmetic* gain `2^{-c·max(l₁,l₂)}` of the paper's Theorem `model-est-2`
  (`MdlCoreGain`, i.e. `all-all-large-2` at `(2,2,1)`) already has the strength of `2^{-cL}`; the
  polynomial loss `⟨L⟩^A 2^{AρL}` of the core is absorbed into the gain for `ρ ≤ c/(4(A+1))`
  (`lossWeight_mul_le_lcWeight`).
* **Case B** (`max k > max l`, possible only with `k₁ = 0 ∨ k₂ = 0`): the target demands the
  *stronger* gain `2^{-c·max k}`, which is **not** part of `model-est-2`; it comes from the
  integration-by-parts identity `integ-ident` of §6, applied to the `t`-integral of the modulated
  tensor `φ_{N,t} ⊗ φ̃_{N,t}`:
  * if `k₁ = 0 < k₂` use identity (ii) (`integIdent_ii_corrected`), which produces the factor
    `2^{-d k₂}` (`MdlBumpIntegIdent`);
  * if `k₂ = 0 < k₁` use identity (i) (`integIdent_i_core`), which produces the factor `2^{-k₁}`
    (`MdlBumpIntegIdentI`).
  Both identities are the *bump-level* forms of the paper's Lemma `integ-ident`; transferring them
  to the model tuple is a *kernel-level* computation — `Tle ρ l φ` is the convolution with the
  kernel `j ↦ arithChar ρ l j · cw φ j` (`IwKernelArithChar`), so the `t`-integral of the slice
  kernel involves only `∫_t cw(φ_{N,t})(j₁) cw(φ̃_{N,t})(j₂) dt`, i.e. the `(j₁,j₂)`-th Fourier
  coefficient of `∫_t (φ_{N,t} ⊗ φ̃_{N,t}) dt` — followed by the `V^r`-bookkeeping
  (`variationalNorm` subadditivity, `variationalNorm_prod_le`, the uniform `V^r` bounds of the
  weights `N^{d-1}/P'(Nt)`, `N^dP''/(P'Nt)²`, `P'(Nt)/N^{d-1}` (`weightVarBound`), and
  `varNorm_integral_le` for the `t`-integral), and applied to the frozen-`t` core estimate
  `MdlSliceCoreGain` (`MdlSliceCoreGainEstimate`).

The *extension* from bounded inputs (where the `tsum`-valued identities are valid, cf. the
`FpieceEqTm` warning about junk values of `tsum`) to all `f, g : ℤ → ℂ` proceeds as in the §5
assembly: for `f, g ∈ ℓ²` one truncates and passes to the limit (`truncZ`), and if `f ∉ ℓ²` or
`g ∉ ℓ²` the right-hand side is `⊤`.

## State of the reduction (2026-09-26)

*Proved in this file:* `lmax_eq_of_max_le`/`lmaxR_eq_of_max_le`/`lcL_eq_of_max_le` (the
bookkeeping of the sub-case `max k ≤ max l`), `lossWeight_mul_le_lcWeight` (the absorption of the
core's polynomial loss into the gain) and **`mdlGain_of_core_smallK`** (Case A: the *integrated*
core `MdlCoreGain P r C₀ 0 0` alone gives the target in the sub-case `max k ≤ max l`).

*Proved elsewhere, available to import* (all sorry-free):

| module | what it gives |
|---|---|
| `KMTPlan/A6/IwKernelArithChar` | `iwKernel (iwSymbolSet A (periodize φ)) j = (∑_{α∈A} e(-jα))·cw φ j`: `Tle ρ l φ` is the convolution with `j ↦ arithChar ρ l (-j)·cw φ j` |
| `KMTPlan/A6/MdlBumpIntegIdent` | the bump-level `integ-ident` **(ii)** (`k₁ = 0 < k₂`): the factor `2^{-d k₂}` |
| `KMTPlan/A6/MdlBumpIntegIdentI` | the bump-level `integ-ident` **(i)** (`k₂ = 0 < k₁`): the factor `2^{-k₁}` |
| `KMTPlan/A6/MdlCoreGainEstimate` | `MdlCoreGain` from `MdlSliceCoreGain` via Minkowski (`varNorm_integral_le`) |
| `KMTPlan/A6/varNorm_integral_le` | `V^r(∫_{1/2}^1 H t · dt) ≤ ∫⁻_{uIoc 1/2 1} V^r(H t)` |
| `KMTPlan/A6/variationalNorm_prod_le` | `V^r(a·b) ≤ 2 V^r(a) V^r(b)` |
| `KMTPlan/A6/weightVarBound` | the uniform `V^r` bounds of `N^{d-1}/P'(Nt)`, `P'(Nt)/N^{d-1}`, `N^dP''(Nt)/P'(Nt)²` along a lacunary sequence (for a threshold `∀ n, C₀ ≤ a n`) |

*Delegated and in progress:* `MdlSliceCoreGainEstimate` (the frozen-`t` core — the arithmetic
input of `model-est-2` at `(2,2,1)`, via `BileTwoOfImprov`/`ArithSymbolHeightSmall`/`FkrInterchange`),
`MdlDecayLowHigh` and `MdlDecayHighLow` (the family-level forms of the two `integ-ident`
identities, which turn Case B into a bound on the *modified*-bump families).

*Recipe for Case B* (`max k > max l`, so `k₁ = 0 < k₂` or `k₂ = 0 < k₁`), once the three
delegated inputs are available: apply the corresponding family identity, bound the (weighted,
frozen or `t`-integrated) modified-bump families by `MdlSliceCoreGain` through
`variationalNorm_prod_le` + the `V^r` bound of the weights + `varNorm_integral_le` and Tonelli
(`∫⁻_t` of the `ℓ¹(ℤ)` norm is `≤ (1/2)·sup_t`, the interval `[1/2,1]` having length `1/2`),
multiply by the decay factor `2^{-d k₂}` (resp. `2^{-k₁}`) and absorb `⟨L⟩^A 2^{AρL}` into
`2^{-cL}` as in `lossWeight_mul_le_lcWeight`; finally pass from bounded to general inputs by
`truncZ`-approximation (the small-`L` regime `lcL ≤ B` needs no identity at all — the core's
weight is then `O(1)` — which is also what makes the weight `V^r` bound applicable, since on the
core `⌊a n⌋ > splitCut ρ L ≥ 2^{2^{uScale ρ L}}` is large as soon as `L` is).
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlSliceCoreGainBig
import Submission.Work.KMTPlan.A6.MdlPartHighLowGainV2
import Submission.Port.Aesm
-- `MdlCoreGainBook` carries *verbatim* copies of every declaration of `MdlCoreGainEstimate`
-- except its final target; it is import-cycle-free (it does not import the `A6Clean/adelic*`
-- subtree), so the bookkeeping lemma `MdlCoreGain_of_sliceMeasInt` used below is taken from
-- there.  (Importing the target file itself would pull in the whole gated-adelic consumer
-- subtree, which is unnecessary here and was the source of a duplicate-declaration clash.)

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar Work.KMTContract Work.KMTAreas.A7

/-! ## The sub-case `max k ≤ max l`: `lmax` and `lcL` depend only on the height scales -/

/-- `lmax` depends only on the two height scales when `max k ≤ max l`. -/
lemma lmax_eq_of_max_le {l₁ l₂ k₁ k₂ : ℕ} (hk : max k₁ k₂ ≤ max l₁ l₂) :
    lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) = ((max l₁ l₂ : ℕ) : ℤ) := by
  have h2 : max (k₁ : ℤ) (k₂ : ℤ) ≤ max (l₁ : ℤ) (l₂ : ℤ) := by omega
  rw [Work.Analysis.EndVar.lmax, max_eq_left h2]
  omega

/-- `lmaxR` on the sub-case `max k ≤ max l`. -/
lemma lmaxR_eq_of_max_le {l₁ l₂ k₁ k₂ : ℕ} (hk : max k₁ k₂ ≤ max l₁ l₂) :
    lmaxR l₁ l₂ k₁ k₂ = ((max l₁ l₂ : ℕ) : ℝ) := by
  rw [lmaxR, lmax_eq_of_max_le hk, Int.cast_natCast]

/-- `lmaxR` is `max l₁ l₂` (as a real number) on the sub-case `max k ≤ max l`. -/
lemma lmaxR_eq_max_cast {l₁ l₂ k₁ k₂ : ℕ} (hk : max k₁ k₂ ≤ max l₁ l₂) :
    lmaxR l₁ l₂ k₁ k₂ = max (l₁ : ℝ) (l₂ : ℝ) := by
  rw [lmaxR_eq_of_max_le hk, Nat.cast_max]

/-- `lcL` on the sub-case `max k ≤ max l`. -/
lemma lcL_eq_of_max_le {l₁ l₂ k₁ k₂ : ℕ} (hk : max k₁ k₂ ≤ max l₁ l₂) :
    lcL l₁ l₂ k₁ k₂ = max l₁ l₂ := max_eq_left hk

/-! ## Case A: absorption of the core's polynomial loss into the gain -/

/-- **Absorption of the polynomial loss of the `l`-gain core into the gain, on the sub-case
`max k ≤ max l` of the target.**  For `ρ > 0` and `4ρ(A+1) ≤ c > 0`,

  `lossWeight A ρ l₁ l₂ k₁ k₂ · 2^{-c·max(l₁,l₂)} ≤ C · lcWeight (c/2) l₁ l₂ k₁ k₂`. -/
lemma lossWeight_mul_le_lcWeight (A c ρ : ℝ) (hA : 0 ≤ A) (hc : 0 < c) (hρ : 0 < ρ)
    (hρc : 4 * ρ * (A + 1) ≤ c) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l₁ l₂ k₁ k₂ : ℕ), max k₁ k₂ ≤ max l₁ l₂ →
      lossWeight A ρ l₁ l₂ k₁ k₂ * (2 : ℝ) ^ (-(c * max (l₁ : ℝ) (l₂ : ℝ)))
        ≤ C * lcWeight (c / 2) l₁ l₂ k₁ k₂ := by
  obtain ⟨C₁, hC₁, hC₁'⟩ := Work.KMTAreas.A7.rpow_poly_le_const_exp A (c / 4) hA (by positivity)
  refine ⟨C₁, hC₁, fun l₁ l₂ k₁ k₂ hk => ?_⟩
  have hpq : lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) = ((max l₁ l₂ : ℕ) : ℤ) := lmax_eq_of_max_le hk
  set L : ℝ := max (l₁ : ℝ) (l₂ : ℝ) with hLdef
  have hL0 : 0 ≤ L := by rw [hLdef]; positivity
  have hLR : lmaxR l₁ l₂ k₁ k₂ = L := by
    rw [lmaxR_eq_of_max_le hk, hLdef, Nat.cast_max]
  -- the polynomial factor
  have hp : (1 + lmaxR l₁ l₂ k₁ k₂) ^ A ≤ C₁ * (2 : ℝ) ^ ((c / 4) * L) := by
    rw [hLR, hLdef]
    simpa only [Nat.cast_max] using hC₁' (max l₁ l₂)
  -- the loss exponent is dominated by `c/4`
  have hAρ : A * ρ ≤ c / 4 := by
    have h1 : A * ρ ≤ (A + 1) * ρ := by nlinarith [hA, hρ]
    have h2 : (A + 1) * ρ ≤ c / 4 := by nlinarith [hρc]
    linarith
  have hexp : (2 : ℝ) ^ (A * ρ * lmaxR l₁ l₂ k₁ k₂) ≤ (2 : ℝ) ^ ((c / 4) * L) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    rw [hLR, hLdef]
    exact mul_le_mul_of_nonneg_right hAρ (by positivity)
  -- the exponential factors combine
  have hmul : (2 : ℝ) ^ ((c / 4) * L) * (2 : ℝ) ^ ((c / 4) * L) * (2 : ℝ) ^ (-(c * L))
      = (2 : ℝ) ^ (-(c / 2) * L) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2), ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1
    ring
  have hlc : lcWeight (c / 2) l₁ l₂ k₁ k₂ = (2 : ℝ) ^ (-(c / 2) * L) := by
    rw [lcWeight, hpq, hLdef, Int.cast_natCast, Nat.cast_max]
    congr 1
    ring
  calc lossWeight A ρ l₁ l₂ k₁ k₂ * (2 : ℝ) ^ (-(c * max (l₁ : ℝ) (l₂ : ℝ)))
      = (1 + lmaxR l₁ l₂ k₁ k₂) ^ A * (2 : ℝ) ^ (A * ρ * lmaxR l₁ l₂ k₁ k₂)
          * (2 : ℝ) ^ (-(c * L)) := by
        rw [lossWeight, hLR, hLdef]
    _ ≤ (C₁ * (2 : ℝ) ^ ((c / 4) * L)) * (2 : ℝ) ^ ((c / 4) * L) * (2 : ℝ) ^ (-(c * L)) := by
        have h2 : (0 : ℝ) < (2 : ℝ) ^ ((c / 4) * L) := Real.rpow_pos_of_pos (by norm_num) _
        have h3 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(c * L)) := (Real.rpow_pos_of_pos (by norm_num) _).le
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul hp hexp (by positivity) (by positivity)) h3
    _ = C₁ * ((2 : ℝ) ^ ((c / 4) * L) * (2 : ℝ) ^ ((c / 4) * L) * (2 : ℝ) ^ (-(c * L))) := by
        ring
    _ = C₁ * lcWeight (c / 2) l₁ l₂ k₁ k₂ := by rw [hmul, hlc]

/-! ## The two bookkeeping steps of Case B -/

/-- **Weight pull-out for the variational norm.**  Multiplying a family pointwise by a *scalar*
weight family `w` whose `r`-variational norm is at most `ofReal C` multiplies the
`ℓ¹(ℤ; V^r)`-norm by at most `2C`. -/
lemma eLpNorm_variationalNorm_mul_le (r : ℝ≥0) (hr : 1 ≤ r) {w : ℕ → ℂ} {C : ℝ}
    (hw : variationalNorm r w ≤ ENNReal.ofReal C) (Y : ℕ → ℤ → ℂ) :
    eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => w n * Y n x)) 1 Measure.count
      ≤ ((2 : ENNReal) * ENNReal.ofReal C) *
          eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => Y n x)) 1 Measure.count := by
  have hstep : ∀ x : ℤ, variationalNorm r (fun n : ℕ => w n * Y n x)
      ≤ ((2 : ENNReal) * ENNReal.ofReal C) * variationalNorm r (fun n : ℕ => Y n x) := by
    intro x
    calc variationalNorm r (fun n : ℕ => w n * Y n x)
        ≤ 2 * (variationalNorm r w * variationalNorm r (fun n : ℕ => Y n x)) :=
          Work.KMTPlan.A6.variationalNorm_prod_le hr w _
      _ ≤ 2 * (ENNReal.ofReal C * variationalNorm r (fun n : ℕ => Y n x)) := by gcongr
      _ = ((2 : ENNReal) * ENNReal.ofReal C) * variationalNorm r (fun n : ℕ => Y n x) := by ring
  refine (eLpNorm_mono_enorm (hf := by pw_aesm) (f := fun x : ℤ => variationalNorm r (fun n : ℕ => w n * Y n x))
    (g := fun x : ℤ => ((2 : ENNReal) * ENNReal.ofReal C) *
      variationalNorm r (fun n : ℕ => Y n x))
    (fun x => by simpa only [enorm_eq_self] using hstep x)).trans ?_
  rw [Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal
    (c := (2 : ENNReal) * ENNReal.ofReal C)
    (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top) (by norm_num) (by norm_num)]

/-- **Minkowski for a weighted `t`-integral.**  The `r`-variational norm of the `t`-integral of a
weighted family is at most the `t`-integral of the variational norms of the weighted slices
(instance of `Work.KMTPlan.A6.varNorm_integral_le`). -/
lemma varNorm_weighted_integral_le (r : ℝ≥0) (hr : 1 ≤ r) (w : ℕ → ℝ → ℂ)
    (Y : ℝ → ℕ → ℤ → ℂ) (x : ℤ)
    (hint : ∀ n : ℕ, IntervalIntegrable (fun t : ℝ => w n t * Y t n x) volume (1 / 2) 1)
    (hmeas : ∀ n : ℕ, Measurable fun t : ℝ => w n t * Y t n x) :
    variationalNorm r (fun n : ℕ => ∫ t in (1 / 2 : ℝ)..1, w n t * Y t n x)
      ≤ ∫⁻ t in Set.uIoc (1 / 2 : ℝ) 1,
          variationalNorm r (fun n : ℕ => w n t * Y t n x) :=
  Work.KMTPlan.A6.varNorm_integral_le r hr (fun t n x => w n t * Y t n x) x hint hmeas

/-! ## Case A of the target -/

/-- **Case A of `LowModelGain`** (`max k ≤ max l`): the `l`-gain core `MdlCoreGain` alone gives
the target's estimate with the weight `lcWeight c = 2^{-c·L}`. -/
theorem mdlGain_of_core_smallK (P : ℤ[X]) (r : ℝ≥0) (C₀ : ℕ)
    (hcore : MdlCoreGain P r C₀ 0 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : ℝ≥0 → ℝ≥0,
      ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → Lacunary Λ a → (∀ n, 1 ≤ a n) → (k₁ = 0 ∨ k₂ = 0) →
        max k₁ k₂ ≤ max l₁ l₂ →
        eLpNorm (fun x : ℤ => variationalNorm r
            (fun n : ℕ => mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) 1 Measure.count
          ≤ (K Λ : ℝ≥0∞) * ENNReal.ofReal (lcWeight c l₁ l₂ k₁ k₂) *
              eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
  obtain ⟨c₀, hc₀, A, hA, ρ₀, hρ₀, hcore'⟩ := hcore
  refine ⟨c₀ / 2, by positivity, min ρ₀ (c₀ / (4 * (A + 1))), lt_min hρ₀ (by positivity), ?_⟩
  intro ρ hρ hρle
  have hρρ₀ : ρ ≤ ρ₀ := le_trans hρle (min_le_left _ _)
  have hρc : 4 * ρ * (A + 1) ≤ c₀ := by
    have h1 : ρ ≤ c₀ / (4 * (A + 1)) := le_trans hρle (min_le_right _ _)
    have h2 : (0:ℝ) < 4 * (A + 1) := by linarith
    rw [le_div_iff₀ h2] at h1
    linarith
  obtain ⟨C, hC1, hC⟩ := lossWeight_mul_le_lcWeight A c₀ ρ hA hc₀ hρ hρc
  obtain ⟨K₀, hK₀⟩ := hcore' ρ hρ hρρ₀
  have hC0 : (0:ℝ) ≤ C := le_trans zero_le_one hC1
  set CW : NNReal := ⟨C, hC0⟩ with hCWdef
  refine ⟨fun Λ => K₀ Λ * CW, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hQ hk
  have hb := hK₀ a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 (fun _ => by norm_num) (fun _ => by norm_num)
  simp only [mdlPartJ_zero_zero] at hb
  have hCWreal : (CW : ENNReal) = ENNReal.ofReal C :=
    (ENNReal.ofReal_coe_nnreal (p := CW)).symm
  have hstep : ENNReal.ofReal (lossWeight A ρ l₁ l₂ k₁ k₂
        * (2 : ℝ) ^ (-(c₀ * max (l₁ : ℝ) (l₂ : ℝ))))
      ≤ (CW : ENNReal) * ENNReal.ofReal (lcWeight (c₀ / 2) l₁ l₂ k₁ k₂) := by
    rw [hCWreal, ← ENNReal.ofReal_mul hC0]
    exact ENNReal.ofReal_le_ofReal (hC l₁ l₂ k₁ k₂ hk)
  calc eLpNorm (fun x : ℤ => variationalNorm r
        (fun n : ℕ => mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) 1 Measure.count
      ≤ (K₀ Λ : ENNReal) * ENNReal.ofReal (lossWeight A ρ l₁ l₂ k₁ k₂
            * (2 : ℝ) ^ (-(c₀ * max (l₁ : ℝ) (l₂ : ℝ))))
          * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := hb
    _ ≤ (K₀ Λ : ENNReal) * ((CW : ENNReal) * ENNReal.ofReal (lcWeight (c₀ / 2) l₁ l₂ k₁ k₂))
          * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
        gcongr
    _ = ((K₀ Λ * CW : NNReal) : ENNReal) * ENNReal.ofReal (lcWeight (c₀ / 2) l₁ l₂ k₁ k₂)
          * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
        rw [ENNReal.coe_mul]
        ring


/-! ## The pieces of the low case, and their gluing

`LowModelGain` is proved by splitting the low-case quadruples `(k₁ = 0 ∨ k₂ = 0)` into three
classes, on which the three independent pieces of the §6--§8 analysis give the gain `2^{-c·L}`
uniformly:

* `Q₁ = (k₁ = 0 ∨ k₂ = 0) ∧ max k ≤ max l` — the **large `l`** regime, where the arithmetic gain
  `2^{-c·max(l₁,l₂)}` of the paper's Theorem `model-est-2` (`MdlCoreGain`, hence `MdlSliceCoreGain`
  at `(j₁,j₂) = (0,0)`) already has the strength of the target weight `lcWeight c`; this is
  `mdlGain_of_core_smallK` (Case A);
* `Q₂ = k₂ = 0 ∧ max l < k₁` — the **`k`-decay on the `f`-side**, from the integration-by-parts
  identity (i) of §6 (`MdlDecayHighLow`), which produces the factor `2^{-k₁} = 2^{-L}`;
* `Q₃ = k₁ = 0 ∧ max l < k₂` — the **`k`-decay on the `g`-side**, from identity (ii)
  (`MdlDecayLowHigh`), which produces the factor `2^{-d·k₂} = 2^{-L}`.

The three classes cover the low case (for `max k > max l` the disjunction `k₁ = 0 ∨ k₂ = 0`
identifies the side carrying the `k`-decay), and the pieces are glued by taking the minimum of
the three rates, the minimum of the three thresholds and the sum of the three constants. -/

/-- **The common shape of the pieces of `LowModelGain`**: a bound

  `‖(mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)_n‖_{ℓ¹(ℤ;V^r)} ≤ K(Λ)·2^{-c·L}·‖f‖₂‖g‖₂`

for the quadruples `(l₁,l₂,k₁,k₂)` satisfying the class predicate `Q`.  The rate `c` and the
threshold `ρ₀` are independent of `ρ ≤ ρ₀`, the constant `K` may depend on `ρ` and `Λ`, exactly as
in `LowBound`. -/
def GainOn (P : ℤ[X]) (r : ℝ≥0) (C₀ : ℕ) (Q : ℕ → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : ℝ≥0 → ℝ≥0,
    ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
      1 < Λ → Lacunary Λ a → (∀ n, 1 ≤ a n) → Q l₁ l₂ k₁ k₂ →
      eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) 1 Measure.count
        ≤ (K Λ : ℝ≥0∞) * ENNReal.ofReal (lcWeight c l₁ l₂ k₁ k₂) *
            eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count

/-- **`LowModelGain` is the `GainOn` statement for the low-case quadruples.** -/
theorem lowModelGain_iff_gainOn (P : ℤ[X]) (r : ℝ≥0) (C₀ : ℕ) :
    LowModelGain P r C₀ ↔ GainOn P r C₀ (fun _ _ k₁ k₂ => k₁ = 0 ∨ k₂ = 0) := Iff.rfl

/-- **Gluing three pieces of `GainOn` into one.**  If the class `Q` is covered by `Q₁, Q₂, Q₃`, and
each `Qᵢ` carries a gain bound with rate `cᵢ` and threshold `ρᵢ`, then `Q` carries the gain bound
with rate `min (min c₁ c₂) c₃`, threshold `min (min ρ₁ ρ₂) ρ₃` and constant
`K₁ Λ + K₂ Λ + K₃ Λ`. -/
theorem gainOn_of_cover {P : ℤ[X]} {r : ℝ≥0} {C₀ : ℕ} {Q Q₁ Q₂ Q₃ : ℕ → ℕ → ℕ → ℕ → Prop}
    (h₁ : GainOn P r C₀ Q₁) (h₂ : GainOn P r C₀ Q₂) (h₃ : GainOn P r C₀ Q₃)
    (hcover : ∀ l₁ l₂ k₁ k₂, Q l₁ l₂ k₁ k₂ →
      Q₁ l₁ l₂ k₁ k₂ ∨ Q₂ l₁ l₂ k₁ k₂ ∨ Q₃ l₁ l₂ k₁ k₂) :
    GainOn P r C₀ Q := by
  obtain ⟨c₁, hc₁, ρ₁, hρ₁, h₁'⟩ := h₁
  obtain ⟨c₂, hc₂, ρ₂, hρ₂, h₂'⟩ := h₂
  obtain ⟨c₃, hc₃, ρ₃, hρ₃, h₃'⟩ := h₃
  refine ⟨min (min c₁ c₂) c₃, lt_min (lt_min hc₁ hc₂) hc₃, min (min ρ₁ ρ₂) ρ₃,
    lt_min (lt_min hρ₁ hρ₂) hρ₃, ?_⟩
  intro ρ hρ hρle
  have hρ₁' : ρ ≤ ρ₁ := le_trans hρle (le_trans (min_le_left _ _) (min_le_left _ _))
  have hρ₂' : ρ ≤ ρ₂ := le_trans hρle (le_trans (min_le_left _ _) (min_le_right _ _))
  have hρ₃' : ρ ≤ ρ₃ := le_trans hρle (min_le_right _ _)
  obtain ⟨K₁, hK₁⟩ := h₁' ρ hρ hρ₁'
  obtain ⟨K₂, hK₂⟩ := h₂' ρ hρ hρ₂'
  obtain ⟨K₃, hK₃⟩ := h₃' ρ hρ hρ₃'
  refine ⟨fun Λ => K₁ Λ + K₂ Λ + K₃ Λ, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hQ
  have hc₁' : min (min c₁ c₂) c₃ ≤ c₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hc₂' : min (min c₁ c₂) c₃ ≤ c₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hc₃' : min (min c₁ c₂) c₃ ≤ c₃ := min_le_right _ _
  rcases hcover l₁ l₂ k₁ k₂ hQ with hQ₁ | hQ₂ | hQ₃
  · refine (hK₁ a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hQ₁).trans ?_
    gcongr
    · exact le_self_add.trans le_self_add
    · exact lcWeight_le_of_le hc₁' l₁ l₂ k₁ k₂
  · refine (hK₂ a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hQ₂).trans ?_
    gcongr
    · exact (le_add_of_nonneg_left (by positivity)).trans le_self_add
    · exact lcWeight_le_of_le hc₂' l₁ l₂ k₁ k₂
  · refine (hK₃ a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hQ₃).trans ?_
    gcongr
    · exact le_add_of_nonneg_left (by positivity)
    · exact lcWeight_le_of_le hc₃' l₁ l₂ k₁ k₂

/-- **Case A in `GainOn` form**: the `l`-gain core `MdlCoreGain P r C₀ 0 0` alone gives the target
bound on the class `Q₁ = (k₁ = 0 ∨ k₂ = 0) ∧ max k ≤ max l`. -/
theorem gainOn_smallK (P : ℤ[X]) (r : ℝ≥0) (C₀ : ℕ) (hcore : MdlCoreGain P r C₀ 0 0) :
    GainOn P r C₀ (fun l₁ l₂ k₁ k₂ => (k₁ = 0 ∨ k₂ = 0) ∧ max k₁ k₂ ≤ max l₁ l₂) := by
  obtain ⟨c, hc, ρ₀, hρ₀, h⟩ := mdlGain_of_core_smallK P r C₀ hcore
  refine ⟨c, hc, ρ₀, hρ₀, fun ρ hρ hρle => ?_⟩
  obtain ⟨K, hK⟩ := h ρ hρ hρle
  exact ⟨K, fun a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hQ =>
    hK a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hQ.1 hQ.2⟩

/-- **The trichotomy of the low case.**  Every low-case quadruple `(k₁ = 0 ∨ k₂ = 0)` lies in
Case A (`max k ≤ max l`) or in one of the two branches where the integration-by-parts identity of
§6 supplies the `k`-decay (the positive scale being `k₁` resp. `k₂`). -/
theorem lowCase_trichotomy (l₁ l₂ k₁ k₂ : ℕ) (hQ : k₁ = 0 ∨ k₂ = 0) :
    ((k₁ = 0 ∨ k₂ = 0) ∧ max k₁ k₂ ≤ max l₁ l₂) ∨
      (k₂ = 0 ∧ max l₁ l₂ < k₁) ∨ (k₁ = 0 ∧ max l₁ l₂ < k₂) := by
  by_cases hle : max k₁ k₂ ≤ max l₁ l₂
  · exact Or.inl ⟨hQ, hle⟩
  · have hlt : max l₁ l₂ < max k₁ k₂ := not_le.mp hle
    rcases hQ with h0 | h0
    · exact Or.inr (Or.inr ⟨h0, by rwa [h0, max_eq_right (Nat.zero_le k₂)] at hlt⟩)
    · exact Or.inr (Or.inl ⟨h0, by rwa [h0, max_eq_left (Nat.zero_le k₁)] at hlt⟩)


/-- **The integrated `l`-gain core from the frozen-`t` slice core.**  The `t`-integration of the
slice estimate (`MdlCoreGain_of_sliceMeasInt`) only needs the interval-integrability of the single
time slices, which is `Work.KMTPlan.A6.MdlSliceIntervalIntegrable`. -/
theorem mdlCoreGain_zero_zero (P : ℤ[X]) (r : ℝ≥0) (hr : 1 ≤ r) (C₀ : ℕ)
    (h : MdlSliceCoreGain P r C₀ 0 0) : MdlCoreGain P r C₀ 0 0 :=
  MdlCoreGain_of_sliceMeasInt P r C₀ 0 0 hr h
    (fun ρ a l₁ l₂ k₁ k₂ f g n x hf hg hk₁ hk₂ =>
      MdlSliceIntervalIntegrable ρ P C₀ a f g l₁ l₂ k₁ k₂ 0 0 n x hf hg hk₁ hk₂)

/-- **The integrated `l`-gain core from the `ℓ²` case of the frozen-`t` slice core.**  Companion of
`mdlCoreGain_zero_zero` through the area's reduction `MdlSliceCoreGain_of_memLp`: proving the `ℓ²`
statement `MdlSliceCoreGainMemLp` suffices for the whole assembly. -/
theorem mdlCoreGain_zero_zero_of_memLp (P : ℤ[X]) (r : ℝ≥0) (hr : 1 ≤ r) (C₀ : ℕ)
    (h : MdlSliceCoreGainMemLp P r C₀ 0 0) : MdlCoreGain P r C₀ 0 0 :=
  mdlCoreGain_zero_zero P r hr C₀ (MdlSliceCoreGain_of_memLp P r hr C₀ 0 0 h)

/-- **The final reduction of `LowModelGain`**: the target follows from the Case A piece (the
`l`-gain core) and the two `k`-decay branches of the §6 integration-by-parts identity. -/
theorem lowModelGain_of_gainOn (P : ℤ[X]) (r : ℝ≥0) (C₀ : ℕ)
    (hA : GainOn P r C₀ (fun l₁ l₂ k₁ k₂ => (k₁ = 0 ∨ k₂ = 0) ∧ max k₁ k₂ ≤ max l₁ l₂))
    (hB₁ : GainOn P r C₀ (fun l₁ l₂ k₁ k₂ => k₂ = 0 ∧ max l₁ l₂ < k₁))
    (hB₂ : GainOn P r C₀ (fun l₁ l₂ k₁ k₂ => k₁ = 0 ∧ max l₁ l₂ < k₂)) :
    LowModelGain P r C₀ :=
  (lowModelGain_iff_gainOn P r C₀).mpr
    (gainOn_of_cover hA hB₁ hB₂ (fun l₁ l₂ k₁ k₂ hQ => lowCase_trichotomy l₁ l₂ k₁ k₂ hQ))


/-- **The `f`-side `k`-decay branch in the `GainOn` form.** -/
theorem gainOn_highLow (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : ℝ≥0) (hr : 2 < r)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (hA1 : Work.KMTContract.AreaA1)
    (hI : Work.KMTContract.ImprovKMT P) :
    GainOn P r C₀ (fun l₁ l₂ k₁ k₂ => k₂ = 0 ∧ max l₁ l₂ < k₁) := by
  obtain ⟨c, hc, ρ₀, hρ₀, h⟩ := MdlPartHighLowGainV2 P hd r hr C₀ hC₀ hA1 hI
  refine ⟨c, hc, ρ₀, hρ₀, fun ρ hρ hρle => ?_⟩
  obtain ⟨K, hK⟩ := h ρ hρ hρle
  refine ⟨K, fun a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hQ => ?_⟩
  obtain ⟨hk₂, hlt⟩ := hQ
  cases hk₂
  exact hK a Λ l₁ l₂ k₁ f g hΛ ha ha1 hlt

/-- **The `g`-side `k`-decay branch in the `GainOn` form.** -/
theorem gainOn_lowHigh (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : ℝ≥0) (hr : 2 < r)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (hA1 : Work.KMTContract.AreaA1)
    (hI : Work.KMTContract.ImprovKMT P) :
    GainOn P r C₀ (fun l₁ l₂ k₁ k₂ => k₁ = 0 ∧ max l₁ l₂ < k₂) := by
  obtain ⟨c, hc, ρ₀, hρ₀, h⟩ := MdlPartLowHighGain P hd r hr C₀ hC₀ hA1 hI
  refine ⟨c, hc, ρ₀, hρ₀, fun ρ hρ hρle => ?_⟩
  obtain ⟨K, hK⟩ := h ρ hρ hρle
  refine ⟨K, fun a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hQ => ?_⟩
  obtain ⟨hk₁, hlt⟩ := hQ
  cases hk₁
  exact hK a Λ l₁ l₂ k₂ f g hΛ ha ha1 hlt

/-! ## The target -/

theorem LowModelGainEstimate (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (hA1 : Work.KMTContract.AreaA1)
    (hI : Work.KMTContract.ImprovKMT P) :
    Work.KMTPlan.A6.LowModelGain P r C₀ := by
  have hr1 : (1 : ℝ≥0) ≤ r :=
    le_of_lt (lt_trans (by norm_num : (1 : ℝ≥0) < 2) hr)
  have hj0 : (0 : ℤ) ∈ ({-1, 0, 1} : Finset ℤ) := by decide
  have hcore : MdlCoreGain P r C₀ 0 0 :=
    mdlCoreGain_zero_zero P r hr1 C₀ (MdlSliceCoreGainBig P hd r hr C₀ hC₀ hA1 hI 0 0 hj0 hj0)
  exact lowModelGain_of_gainOn P r C₀ (gainOn_smallK P r C₀ hcore)
    (gainOn_highLow P hd r hr C₀ hC₀ hA1 hI) (gainOn_lowHigh P hd r hr C₀ hC₀ hA1 hI)

end

end Work.KMTPlan.A6
