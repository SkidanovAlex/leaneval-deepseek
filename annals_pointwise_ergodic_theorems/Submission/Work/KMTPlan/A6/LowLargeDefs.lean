/-
# The vocabulary and the assembly of `Work.KMTPlan.A6.lowLargeScaled`

This module holds the *definitions* of the large-scale low case of area A6 (Krause--Mirek--Tao,
Theorem `varp` at `(p₁,p₂,p) = (2,2,1)`) together with the proved assembly `lcLarge_of_inputs`:
the bridge to the A7 tuples, the three families of the decomposition, the two model inputs
`mdlF`/`mdlG` (the paper symbols `Π_{l,≤-u}f`, `Π_{l,≤-du}g`, i.e. exact arithmetic height and a
*narrow* continuous window), the common shape `LowBound` of the three interface estimates, and
the three `Prop`s `LowModApprox`, `LowModelGain`, `LowExceptional`.

The target theorem `Work.KMTPlan.A6.lowLargeScaled` lives in
`Submission/Work/KMTPlan/A6/lowLargeScaled.lean`, which imports this module.  Both the interface
`Prop`s and the assembly are used by the A6 (and A7) fleet, so they are kept in this low module
so that the interface proofs (which import *this* file) can be imported by the target file
without an import cycle.

See `NOTES_A6_lowLargeScaled.md` for the state of the three interface estimates, for the two
corrections to the model operator found in this session (exact arithmetic height, and a narrow
window instead of window `0`), and for the precise wiring recipe.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.LowDefs
import Submission.Work.KMTPlan.A6.Basic
import Submission.Work.KMTAreas.A7.ModelApproxAux
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems
open Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar
open Work.KMTContract

/-! ## The bridge to the A7 tuples -/

/-- The A6 clamp is the A7 clamp: `colLarge` (`LowDefs`) and `colTuple` (`A7/Large/Defs`) are
the same family, since `lcL` is *defined* as the maximum that occurs in `colTuple`. -/
theorem colLarge_eq_colTuple (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) :
    colLarge ρ P C₀ a f g l₁ l₂ k₁ k₂
      = Work.KMTAreas.A7.colTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ := rfl

/-! ## The three families of the decomposition -/

/-- **The model input of §6 on the first side: the exact-height shell with the narrow continuous
window `Π_{l,≤-u} f = piExact (kmtPj ρ) l (-(u : ℤ)) f`** (the paper symbol `F = Π_{l₁,≤-u} f`).
Two features are essential:

* the arithmetic height is *exact*: the gain `2^{-c·l}` comes from the arithmetic annihilation on
  the heights below `l`, which the height-`≤l` projection `kmtProj ρ l 0` does not provide, since
  `m_Ẑ(0,0) = 1` would then contribute a gain-free pointwise product;
* the window is *narrow* (`-u`, not `0`): the exact-height projection at window `0` has symbol
  `∑_{β ∈ (ℚ/ℤ)_l} periodize (etaCut kmtEta 0)(ξ-β)` with `periodize kmtEta ≥ 1` pointwise, hence
  symbol `≥ |(ℚ/ℤ)_l|`, which no gain can absorb.  The wide-window projection is used by the A7
  model tuple (where the loss case does not care), never here. -/
def mdlF (ρ : ℝ) (u l : ℕ) (f : ℤ → ℂ) : ℤ → ℂ :=
  piExact (kmtPj ρ) l (-(u : ℤ)) f

/-- **The model input of §6 on the second side**, with the `d`-fold rescaled narrow window
`Π_{l,≤-du} g = piExact (kmtPj ρ) l (-(d·u)) g` (the paper symbol `G = Π_{l₂,≤-du} g`). -/
def mdlG (ρ : ℝ) (P : ℤ[X]) (u l : ℕ) (g : ℤ → ℂ) : ℤ → ℂ :=
  piExact (kmtPj ρ) l (-((P.natDegree : ℤ) * (u : ℤ))) g

/-- **The §6 model operator applied to the exact-height shells.**  This is
`∫_{1/2}^1 B^{l₁,l₂,m_Ẑ}_{m_*}(T^{l₁}_{φ_{N,t}}F, T^{l₂}_{φ̃_{N,t}}G) dt` with
`F = mdlF ρ l₁ f`, `G = mdlF ρ l₂ g`, on the admissible large scales in the main regime.  It
differs from `Work.KMTAreas.A7.modelTuple` only in that the *inputs* are the exact-height shells
`piExact` instead of the height-`≤l` projections `kmtProj ρ l 0`. -/
def mdlPart (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) :
    ℕ → ℤ → ℂ :=
  fun n x =>
    if inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n))
        ∧ Work.KMTAreas.A7.splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < Nat.floor (a n)
        ∧ Work.KMTAreas.A7.mainRegime ρ k₁ k₂ (Nat.floor (a n)) then
      ∫ t in (1/2 : ℝ)..1,
        Work.KMTAreas.A7.Btwist ρ P l₁ l₂
          (Work.KMTAreas.A7.mStarF
            (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
          (Work.KMTAreas.A7.mStargF P.natDegree
            (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
          (Work.KMTAreas.A7.Tle ρ l₁
            (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t)
            (mdlF ρ (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₁ f))
          (Work.KMTAreas.A7.Tle ρ l₂
            (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t)
            (mdlG ρ P (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₂ g)) x
    else 0

/-- The single-scale mod-approximation error at the index `n` (`N = ⌊a n⌋`): the distance
between the concrete halved average of the §5 pieces (`mainPartTuple`) and the §6 model
operator (`mdlPart`). -/
def modApproxErr (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) :
    ℕ → ℤ → ℂ :=
  fun n x => Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
    - mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x

/-- The exceptional part of the columns: the admissible large scales which are not in the main
regime of the §6 functional calculus. -/
def excPart (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) :
    ℕ → ℤ → ℂ :=
  Work.KMTAreas.A7.exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂

/-! ## The common shape of the three inputs -/

/-- **The common shape of the three inputs.**  A family `Fam` obeys the low-case large-scale
estimate with the gain if there are `c > 0` and `ρ₀ > 0` such that for every `ρ` in `(0, ρ₀]`
there is `K : ℝ≥0 → ℝ≥0` with

  `‖ (Fam ρ a l₁ l₂ k₁ k₂ f g n x)_n ‖_{ℓ¹(ℤ; V^r)} ≤ K(Λ) 2^{-c L} ‖f‖₂‖g‖₂`

for every low-case quadruple `(l₁,l₂,k₁,k₂)` (`k₁ = 0` or `k₂ = 0`), every `Λ`-lacunary `a`
with `a n ≥ 1`, and all `f g : ℤ → ℂ`; here `L = max (max l₁ l₂) (max k₁ k₂)`. -/
def LowBound (P : ℤ[X]) (r : ℝ≥0) (C₀ : ℕ)
    (Fam : (ρ : ℝ) → (a : ℕ → ℝ≥0) → (l₁ l₂ k₁ k₂ : ℕ) →
      (f g : ℤ → ℂ) → ℕ → ℤ → ℂ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
    ∃ K : ℝ≥0 → ℝ≥0,
      ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        (k₁ = 0 ∨ k₂ = 0) →
        eLpNorm (fun x : ℤ => variationalNorm r
            (fun n : ℕ => Fam ρ a l₁ l₂ k₁ k₂ f g n x)) 1 Measure.count
          ≤ (K Λ : ℝ≥0∞) * ENNReal.ofReal (lcWeight c l₁ l₂ k₁ k₂) *
              eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count

/-- **The model approximation at `(2,2,1)` for the low case**, summed over the lacunary scales
of the large-scale regime: the variational norm of the mod-approximation error
`mainPartTuple − mdlPart` carries the gain `2^{-c L}`.  This is Krause--Mirek--Tao,
Proposition `mod-approx`, composed with the functional calculus `bn-ident` and Lemma
`iw-prop`; in the regime `N > splitCut ρ L` the factor `N⁻¹` of the proposition beats the weight
`modelWeight A ρ L`, which is why the large-scale split isolates exactly these scales. -/
def LowModApprox (P : ℤ[X]) (r : ℝ≥0) (C₀ : ℕ) : Prop :=
  LowBound P r C₀ (fun ρ a l₁ l₂ k₁ k₂ f g => modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂)

/-- **The large-scale model estimate at `(2,2,1)` with the exponential gain (the low case)**:
Krause--Mirek--Tao, Theorem `model-est-2` at `p₁ = p₂ = 2`, `p = 1` (estimate
`all-all-large-2`), composed with the integration-by-parts identity `integ-ident` and the `V^r`
bounds `weight-bound`.  Its proof uses the quantitative Shannon sampling theorem, the
arithmetic bilinear estimate `bile` (Theorem `bile`) and the vector-valued Lépingle
inequality.  The arithmetic gain is available only for the *exact-height* shells `mdlF`: the
lower arithmetic heights must be annihilated (the paper symbol carries the indicator
`Height(α) = 2^l`), which is why the input of `mdlPart` is `piExact` and not `kmtProj ρ l 0`. -/
def LowModelGain (P : ℤ[X]) (r : ℝ≥0) (C₀ : ℕ) : Prop :=
  LowBound P r C₀ (fun ρ a l₁ l₂ k₁ k₂ f g => mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂)

/-- **The exceptional part of the low case**: the admissible large scales `N` which are not in
the main regime `k + 2u ≤ Log N` of the §6 functional calculus.  Each such scale is a
single-scale estimate for the concrete halved average of the §5 pieces, so the minor-arc
estimate `improv` (Theorem `improv`) applies with the gain `2^{-c max(l,k)}`; the number of
scales is `O(1 + 2^{2ρK})` (`K = max k₁ k₂ ≤ L`), whose `r`-th root is absorbed by the
smallness condition `ρ ≤ ρ₀`. -/
def LowExceptional (P : ℤ[X]) (r : ℝ≥0) (C₀ : ℕ) : Prop :=
  LowBound P r C₀ (fun ρ a l₁ l₂ k₁ k₂ f g => excPart ρ P C₀ a f g l₁ l₂ k₁ k₂)


/-! ## The pointwise splitting of the columns -/

/-- The pointwise splitting of the columns into the model tuple, the mod-approximation error
and the exceptional part. -/
theorem colLarge_apply_eq_mdl_add_err_add_exc (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ n : ℕ) (x : ℤ) :
    colLarge ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
      = mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
        + (modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
           + excPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) := by
  have h := congrFun (congrFun
    (Work.KMTAreas.A7.colTuple_eq_sum ρ P C₀ a f g l₁ l₂ k₁ k₂) n) x
  rw [colLarge_eq_colTuple, h]
  simp only [mdlPart, modApproxErr, excPart, Pi.add_apply, Pi.sub_apply]
  ring

/-! ## The assembly -/

/-- **`LcLarge` from the three estimates of §6--§8.**  The assembly of the low-case large-scale
estimate: the pointwise identity `colLarge = modelTuple + (mainPartTuple − modelTuple) +
exceptionalPart`, the subadditivity of `variationalNorm` and of `eLpNorm`, and the arithmetic
of the three weights. -/
theorem lcLarge_of_inputs (P : ℤ[X]) (r : ℝ≥0) (hr : 2 < r) (C₀ : ℕ)
    (hMod : LowModApprox P r C₀) (hMdl : LowModelGain P r C₀) (hExc : LowExceptional P r C₀) :
    LcLarge P r C₀ := by
  intro _hC₀
  obtain ⟨c₁, hc₁, ρ₁, hρ₁, h₁⟩ := hMod
  obtain ⟨c₂, hc₂, ρ₂, hρ₂, h₂⟩ := hMdl
  obtain ⟨c₃, hc₃, ρ₃, hρ₃, h₃⟩ := hExc
  have hr1 : (1 : ℝ≥0) ≤ r := le_of_lt (lt_of_le_of_lt (by norm_num : (1 : ℝ≥0) ≤ 2) hr)
  refine ⟨min (min c₁ c₂) c₃, lt_min (lt_min hc₁ hc₂) hc₃, min (min ρ₁ ρ₂) ρ₃,
    lt_min (lt_min hρ₁ hρ₂) hρ₃, ?_⟩
  intro ρ hρ hρle
  have hρ₁ : ρ ≤ ρ₁ := le_trans hρle (le_trans (min_le_left _ _) (min_le_left _ _))
  have hρ₂ : ρ ≤ ρ₂ := le_trans hρle (le_trans (min_le_left _ _) (min_le_right _ _))
  have hρ₃ : ρ ≤ ρ₃ := le_trans hρle (min_le_right _ _)
  obtain ⟨K₁, hK₁⟩ := h₁ ρ hρ hρ₁
  obtain ⟨K₂, hK₂⟩ := h₂ ρ hρ hρ₂
  obtain ⟨K₃, hK₃⟩ := h₃ ρ hρ hρ₃
  refine ⟨fun Λ => (K₁ Λ + K₂ Λ + K₃ Λ) * 3, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hQ
  have e₁ := hK₁ a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hQ
  have e₂ := hK₂ a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hQ
  have e₃ := hK₃ a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hQ
  have hsplit : ∀ x : ℤ,
      variationalNorm r (fun n : ℕ => colLarge ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
        ≤ variationalNorm r (fun n : ℕ => mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
          + (variationalNorm r (fun n : ℕ => modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
            + variationalNorm r (fun n : ℕ => excPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) := by
    intro x
    have hfun : (fun n : ℕ => colLarge ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
        = fun n : ℕ => mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
            + (modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
               + excPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) :=
      funext fun n => colLarge_apply_eq_mdl_add_err_add_exc ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
    have heq := congrArg (fun u : ℕ → ℂ => variationalNorm r u) hfun
    calc variationalNorm r (fun n : ℕ => colLarge ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
        = variationalNorm r ((fun n : ℕ => mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
            + (fun n : ℕ => modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                + excPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) := heq
      _ ≤ variationalNorm r (fun n : ℕ => mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
            + variationalNorm r (fun n : ℕ => modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                + excPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) :=
          variationalNorm_add_le hr1 _ _
      _ ≤ variationalNorm r (fun n : ℕ => mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
            + (variationalNorm r (fun n : ℕ => modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
              + variationalNorm r (fun n : ℕ => excPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) :=
          add_le_add le_rfl (variationalNorm_add_le hr1 _ _)
  have hmono : eLpNorm (fun x : ℤ => variationalNorm r
        (fun n : ℕ => colLarge ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) 1 Measure.count
      ≤ eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
            + (variationalNorm r (fun n : ℕ => modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
              + variationalNorm r (fun n : ℕ => excPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)))
          1 Measure.count :=
    eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => by simpa only [enorm_eq_self] using hsplit x)
  have hsub₁ : eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
          + (variationalNorm r (fun n : ℕ => modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
            + variationalNorm r (fun n : ℕ => excPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)))
        1 Measure.count
      ≤ eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
          1 Measure.count
        + eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
            + variationalNorm r (fun n : ℕ => excPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
          1 Measure.count :=
    eLpNorm_add_le le_rfl
  have hsub₂ : eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
          + variationalNorm r (fun n : ℕ => excPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
        1 Measure.count
      ≤ eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
          1 Measure.count
        + eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => excPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
          1 Measure.count :=
    eLpNorm_add_le le_rfl
  have b₁ : eLpNorm (fun x : ℤ => variationalNorm r
        (fun n : ℕ => modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) 1 Measure.count
      ≤ (K₁ Λ : ℝ≥0∞) * ENNReal.ofReal (lcWeight (min (min c₁ c₂) c₃) l₁ l₂ k₁ k₂)
        * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
    refine e₁.trans ?_
    gcongr
    exact lcWeight_le_of_le (le_trans (min_le_left _ _) (min_le_left _ _)) l₁ l₂ k₁ k₂
  have b₂ : eLpNorm (fun x : ℤ => variationalNorm r
        (fun n : ℕ => mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) 1 Measure.count
      ≤ (K₂ Λ : ℝ≥0∞) * ENNReal.ofReal (lcWeight (min (min c₁ c₂) c₃) l₁ l₂ k₁ k₂)
        * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
    refine e₂.trans ?_
    gcongr
    exact lcWeight_le_of_le (le_trans (min_le_left _ _) (min_le_right _ _)) l₁ l₂ k₁ k₂
  have b₃ : eLpNorm (fun x : ℤ => variationalNorm r
        (fun n : ℕ => excPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) 1 Measure.count
      ≤ (K₃ Λ : ℝ≥0∞) * ENNReal.ofReal (lcWeight (min (min c₁ c₂) c₃) l₁ l₂ k₁ k₂)
        * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
    refine e₃.trans ?_
    gcongr
    exact lcWeight_le_of_le (min_le_right _ _) l₁ l₂ k₁ k₂
  set Wc : ℝ≥0∞ := ENNReal.ofReal (lcWeight (min (min c₁ c₂) c₃) l₁ l₂ k₁ k₂) with hWc
  set FF : ℝ≥0∞ := eLpNorm f 2 Measure.count with hFF
  set GG : ℝ≥0∞ := eLpNorm g 2 Measure.count with hGG
  have harith : (K₂ Λ : ℝ≥0∞) * Wc * FF * GG
      + ((K₁ Λ : ℝ≥0∞) * Wc * FF * GG + (K₃ Λ : ℝ≥0∞) * Wc * FF * GG)
      ≤ (((K₁ Λ + K₂ Λ + K₃ Λ) * 3 : ℝ≥0) : ℝ≥0∞) * Wc * FF * GG := by
    have hZ : (K₂ Λ : ℝ≥0∞) * Wc * FF * GG
        + ((K₁ Λ : ℝ≥0∞) * Wc * FF * GG + (K₃ Λ : ℝ≥0∞) * Wc * FF * GG)
        = ((K₁ Λ : ℝ≥0∞) + (K₂ Λ : ℝ≥0∞) + (K₃ Λ : ℝ≥0∞)) * (Wc * FF * GG) := by
      ring
    have hcoe : (((K₁ Λ + K₂ Λ + K₃ Λ) * 3 : ℝ≥0) : ℝ≥0∞)
        = ((K₁ Λ : ℝ≥0∞) + (K₂ Λ : ℝ≥0∞) + (K₃ Λ : ℝ≥0∞)) * 3 := by
      push_cast
      ring
    rw [hZ, hcoe]
    have hle : ((K₁ Λ : ℝ≥0∞) + (K₂ Λ : ℝ≥0∞) + (K₃ Λ : ℝ≥0∞))
        ≤ ((K₁ Λ : ℝ≥0∞) + (K₂ Λ : ℝ≥0∞) + (K₃ Λ : ℝ≥0∞)) * 3 := by
      have h3 : ((K₁ Λ : ℝ≥0∞) + (K₂ Λ : ℝ≥0∞) + (K₃ Λ : ℝ≥0∞)) * 3
          = ((K₁ Λ : ℝ≥0∞) + (K₂ Λ : ℝ≥0∞) + (K₃ Λ : ℝ≥0∞))
            + ((K₁ Λ : ℝ≥0∞) + (K₂ Λ : ℝ≥0∞) + (K₃ Λ : ℝ≥0∞)) * 2 := by ring
      rw [h3]
      exact le_self_add
    calc ((K₁ Λ : ℝ≥0∞) + (K₂ Λ : ℝ≥0∞) + (K₃ Λ : ℝ≥0∞)) * (Wc * FF * GG)
        = (Wc * FF * GG) * ((K₁ Λ : ℝ≥0∞) + (K₂ Λ : ℝ≥0∞) + (K₃ Λ : ℝ≥0∞)) := by ring
      _ ≤ (Wc * FF * GG) * (((K₁ Λ : ℝ≥0∞) + (K₂ Λ : ℝ≥0∞) + (K₃ Λ : ℝ≥0∞)) * 3) :=
          mul_le_mul_right hle (Wc * FF * GG)
      _ = (((K₁ Λ : ℝ≥0∞) + (K₂ Λ : ℝ≥0∞) + (K₃ Λ : ℝ≥0∞)) * 3) * Wc * FF * GG := by ring
  have hmain : eLpNorm (fun x : ℤ => variationalNorm r
        (fun n : ℕ => mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) 1 Measure.count
      + (eLpNorm (fun x : ℤ => variationalNorm r
            (fun n : ℕ => modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) 1 Measure.count
        + eLpNorm (fun x : ℤ => variationalNorm r
            (fun n : ℕ => excPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) 1 Measure.count)
      ≤ (K₂ Λ : ℝ≥0∞) * Wc * FF * GG
        + ((K₁ Λ : ℝ≥0∞) * Wc * FF * GG + (K₃ Λ : ℝ≥0∞) * Wc * FF * GG) := by
    refine add_le_add ?_ (add_le_add ?_ ?_)
    · simpa only [hWc, hFF, hGG] using b₂
    · simpa only [hWc, hFF, hGG] using b₁
    · simpa only [hWc, hFF, hGG] using b₃
  calc eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => colLarge ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) 1 Measure.count
      ≤ eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
            + (variationalNorm r (fun n : ℕ => modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
              + variationalNorm r (fun n : ℕ => excPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)))
          1 Measure.count := hmono
    _ ≤ eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
          1 Measure.count
        + eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
            + variationalNorm r (fun n : ℕ => excPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
          1 Measure.count := hsub₁
    _ ≤ eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
          1 Measure.count
        + (eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
            1 Measure.count
          + eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => excPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
            1 Measure.count) := add_le_add le_rfl hsub₂
    _ ≤ (K₂ Λ : ℝ≥0∞) * Wc * FF * GG
        + ((K₁ Λ : ℝ≥0∞) * Wc * FF * GG + (K₃ Λ : ℝ≥0∞) * Wc * FF * GG) := hmain
    _ ≤ (((K₁ Λ + K₂ Λ + K₃ Λ) * 3 : ℝ≥0) : ℝ≥0∞) * Wc * FF * GG := harith
    _ = (((K₁ Λ + K₂ Λ + K₃ Λ) * 3 : ℝ≥0) : ℝ≥0∞)
          * ENNReal.ofReal (lcWeight (min (min c₁ c₂) c₃) l₁ l₂ k₁ k₂)
          * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by rw [hWc, hFF, hGG]

