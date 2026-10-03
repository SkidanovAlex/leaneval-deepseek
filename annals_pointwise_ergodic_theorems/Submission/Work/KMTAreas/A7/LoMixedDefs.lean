/-
# The mixed case `l₁ = 0`, `l₂ ≥ 1` of `Work.KMTAreas.A7.ModelApproxLo`: the vocabulary

Objects and analytic inputs of the mixed case of the `l = 0` model approximation of Area A7
(Krause--Mirek--Tao, *Pointwise ergodic theorems for non-conventional bilinear polynomial
averages*, Ann. of Math. 195 (3) 2022, §5--§8).

## The model, and the repaired window

The concrete column of the mixed range is `mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂`, the halved
average `Ã_N(F^{0,0,k₁}_N f, G^{0,l₂,k₂}_N g)` on the guard `loGuard`.  The *exact-height* model
tuple `Large.Defs.modelTuple` **vanishes** there (`LoDefs.modelTuple_eq_zero_of_lo`: `Tex ρ 0 = 0`),
so the target is an estimate for the concrete column itself.  The paper's model at arithmetic
heights `(0,l₂)` is instead built from the correct height-`0` multiplier
`T^0_φ = T_{Proj(φ ⊗ 1_{(ℚ/ℤ)_0})} = Tle ρ 0 φ = Tm ρ 0 φ` (`diffFreqs ρ 0 = {0}`).

**The window matters.**  The workspace's `smallModelOp` uses the frozen window
`u = uScale ρ L = ⌊2^{2ρL}⌋`, i.e. the paper's free constant `C₂` pinned to `1`.  When `2^{2ρL}` is
small while `l₂` is large, that window is *wider* than the separation of the exact-height fibres
`diffFreqs ρ l₂` (`ρ = 1/6`, `l₂ = 3`: `u = 2`, radius `1/16`, while `diffFreqs ρ 3 ∋ 2/5, 3/7`
are `1/35` apart), and the model's arithmetic symbol picks up a cross-fibre term that does **not**
decay with `N`: the comparison is then `O(1)`, not `O(1/N)` (see `NOTES_A7_smallKernelMass_le.md`
§6, where the defect is invisible because there `N ≤ splitCut ρ L` is bounded, and
`NOTES_LoMixedLeft.md` §6).  The model used here therefore takes the paper's *free* constant `C₂`
to be large enough to separate the fibres:

  `loMixedU ρ d l₂ k₁ k₂ = max (uScale ρ L) (d·l₂ + 3)`,  `L = max (max 0 l₂) (max k₁ k₂)`,
  `d = P.natDegree`  (`l₂ + 3 ≤ 2·d·loMixedU`: the window is narrow relative to the separation).

Widening the window makes the band condition `m_* = 1` on the support of the bumps *harder*; it is
`loBandCond ρ P l₂ k₁ k₂ N : max k₁ k₂ + 1 + 2·loMixedU ≤ Log N`, and it is **not** implied by
`loGuard` (`NOTES_A7_ModelApprox.md` §2).  The scales on which it fails are bounded in number by
`≲ 2^{2ρL}`, which the weight `lossWeight c ρ …` (any `c ≥ 2`) absorbs: that is
`LoMixedOffBandStatement`.  The band-restricted §6 estimate and the off-band estimate together give
the §6 model-approximation error (`LoMixedErrStatement`) via the pointwise splitting
`mainPartTuple − loMixedTuple = (band part) + (off-band part)`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LoDefs
import Submission.Work.KMTAreas.A7.SmallModDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTContract Work.Analysis.EndVar Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

/-! ## The repaired window -/

/-- **The repaired auxiliary/window scale of the mixed model**: the paper's `u = ⌊C₂ 2^{2ρl}⌋`
with the free constant `C₂` large enough to separate the exact-height fibres of
`diffFreqs ρ l₂` (witness: `d·l₂ + 3`). -/
noncomputable def loMixedU (ρ : ℝ) (d l₂ k₁ k₂ : ℕ) : ℕ :=
  max (uScale ρ (max (max 0 l₂) (max k₁ k₂))) (d * l₂ + 3)

/-- The repaired window is at least the pinned one (`uScale ρ L`), so all `cw m_*` mass bounds
proved for the pinned window transfer to it. -/
theorem uScale_le_loMixedU (ρ : ℝ) (d l₂ k₁ k₂ : ℕ) :
    uScale ρ (max (max 0 l₂) (max k₁ k₂)) ≤ loMixedU ρ d l₂ k₁ k₂ := le_max_left _ _

/-- The repaired window is at least `d·l₂ + 3`. -/
theorem d_mul_add_le_loMixedU (ρ : ℝ) (d l₂ k₁ k₂ : ℕ) :
    d * l₂ + 3 ≤ loMixedU ρ d l₂ k₁ k₂ := le_max_right _ _

/-- **The repaired window separates the exact-height fibres**: `l₂ + 3 ≤ 2·d·u`, i.e.
`2^{-2du} ≤ 2^{-l₂-3}`, below the separation `≳ 2^{-l₂}` of `diffFreqs ρ l₂`. -/
theorem ltwo_add_three_le_two_mul_loMixedU (ρ : ℝ) (d l₂ k₁ k₂ : ℕ) (hd : 1 ≤ d) :
    l₂ + 3 ≤ 2 * d * loMixedU ρ d l₂ k₁ k₂ := by
  have h1 : l₂ + 3 ≤ d * l₂ + 3 := by
    have h : l₂ ≤ d * l₂ := Nat.le_mul_of_pos_left l₂ (by omega)
    omega
  have h2 : d * l₂ + 3 ≤ loMixedU ρ d l₂ k₁ k₂ := d_mul_add_le_loMixedU ρ d l₂ k₁ k₂
  have h3 : loMixedU ρ d l₂ k₁ k₂ ≤ 2 * d * loMixedU ρ d l₂ k₁ k₂ := by
    have h : loMixedU ρ d l₂ k₁ k₂ * (1 : ℕ) ≤ loMixedU ρ d l₂ k₁ k₂ * (2 * d) :=
      Nat.mul_le_mul_left _ (by omega)
    simpa [mul_comm, mul_assoc, mul_left_comm] using h
  exact le_trans h1 (le_trans h2 h3)

/-- **The band condition of the repaired mixed model**: `m_* = 1` on the support of the bumps, i.e.
`2^{k+1}/N ≤ 2^{-2u}` ⟺ `max k₁ k₂ + 1 + 2·loMixedU ≤ Log N`.  It is *not* a consequence of
`loGuard`; the scales where it fails are handled by `LoMixedOffBandStatement`. -/
def loBandCond (ρ : ℝ) (P : ℤ[X]) (l₂ k₁ k₂ : ℕ) (N : ℕ) : Prop :=
  max k₁ k₂ + 1 + 2 * loMixedU ρ P.natDegree l₂ k₁ k₂ ≤ (Work.Analysis.EndVar.logN N).toNat

instance loBandCondDecidable (ρ : ℝ) (P : ℤ[X]) (l₂ k₁ k₂ N : ℕ) :
    Decidable (loBandCond ρ P l₂ k₁ k₂ N) := by unfold loBandCond; infer_instance

/-! ## The model operator and tuple -/

/-- **The §6 model operator of the mixed range, with the repaired window**: the twisted bilinear
multiplier `B^{0,l₂,m_Ẑ}_{m_*}` (coefficient kernels `cw m_*` built from `loMixedU`) applied to the
two modulated pieces, the first at arithmetic height `0` (`Tm ρ 0 = Tle ρ 0`). -/
noncomputable def loMixedOp (ρ : ℝ) (P : ℤ[X]) (N l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ) : ℤ → ℂ :=
  fun x =>
    ∫ t in (1/2 : ℝ)..1,
      smallBtwist ρ P 0 l₂
        (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂))
        (mStargF P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂))
        (Tm ρ 0 (varphiNt N k₁ t) f)
        (Tm ρ l₂ (varphitildeNt P P.natDegree N k₂ t) g) x

/-- **The mixed model tuple of the large scales**: `loMixedOp` on the guard `loGuard`, and `0`
off it. -/
noncomputable def loMixedTuple (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → NNReal) (f g : ℤ → ℂ)
    (l₂ k₁ k₂ : ℕ) : ℕ → ℤ → ℂ :=
  fun n x =>
    if loGuard ρ C₀ a 0 l₂ k₁ k₂ n then loMixedOp ρ P (Nat.floor (a n)) l₂ k₁ k₂ f g x else 0

/-- Off the guard the mixed model tuple vanishes. -/
theorem loMixedTuple_eq_zero (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → NNReal) (f g : ℤ → ℂ)
    (l₂ k₁ k₂ n : ℕ) (h : ¬ loGuard ρ C₀ a 0 l₂ k₁ k₂ n) :
    loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n = 0 := by
  funext x
  simp only [loMixedTuple, if_neg h, Pi.zero_apply]

/-! ## The inputs -/

/-- **The band-restricted single-scale §6 estimate of the mixed range**: on the guard *and* on the
band (`loBandCond`, which makes `m_* = 1` on the support of the bumps), the model-approximation
error is `K(Λ)·2^{C·max(2^{ρL},L)}·⌊a n⌋⁻¹·‖f‖_{p₁}‖g‖_{p₂}` per scale (`L = max (max 0 l₂) (max k₁ k₂)`),
off that set it is `0`.  This is the mixed-range analogue of `SmallSingleScaleB` for the repaired
window. -/
def LoMixedSingleScaleStatement (P : ℤ[X]) (p₁ p₂ : ENNReal) : Prop :=
  ∀ (C₀ : ℕ), 1 ≤ C₀ → ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ C : ℝ, 0 ≤ C ∧ ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → 1 ≤ l₂ →
        ∀ n : ℕ,
          MeasureTheory.eLpNorm (fun x : ℤ =>
              if loGuard ρ C₀ a 0 l₂ k₁ k₂ n ∧ loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n)) then
                mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x
                  - loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x
              else 0)
            (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) * ENNReal.ofReal (smallScaleWeight C ρ 0 l₂ k₁ k₂)
              * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹)
              * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count

/-- **The band-restricted §6 model-approximation error, summed over the lacunary scales.**  The
conclusion of the lacunary summation
(`Work.KMTAreas.A7.loMixedBandErr_of_singleScale`) applied to `LoMixedSingleScaleStatement`. -/
def LoMixedBandErrStatement (P : ℤ[X]) (p₁ p₂ : ENNReal) : Prop :=
  ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r →
    ∃ c : ℝ, 0 ≤ c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → 1 ≤ l₂ →
          MeasureTheory.eLpNorm (fun x : ℤ =>
              PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                if loGuard ρ C₀ a 0 l₂ k₁ k₂ n ∧ loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n)) then
                  mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x
                    - loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x
                else 0))
            (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) * ENNReal.ofReal (lossWeight c ρ 0 l₂ k₁ k₂)
              * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count

/-- **The off-band part of the §6 model-approximation error of the mixed range**: on the guard but
*outside* the band, the error is only `O(1)` per scale, but the number of such admissible lacunary
scales is `≲ 2^{2ρL}` (`NOTES_A7_ModelApprox.md` §2), which the weight `lossWeight c ρ …` with
`c ≥ 2` absorbs.  Template: `Work.KMTAreas.A7.ExceptionalBound` (the same argument for the
large-scale exceptional scales). -/
def LoMixedOffBandStatement (P : ℤ[X]) (p₁ p₂ : ENNReal) : Prop :=
  ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r →
    ∃ c : ℝ, 0 ≤ c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → 1 ≤ l₂ →
          MeasureTheory.eLpNorm (fun x : ℤ =>
              PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                if loGuard ρ C₀ a 0 l₂ k₁ k₂ n ∧ ¬ loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n)) then
                  mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x
                    - loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x
                else 0))
            (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) * ENNReal.ofReal (lossWeight c ρ 0 l₂ k₁ k₂)
              * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count

/-- **The §6 model-approximation error of the mixed range, summed over the lacunary scales** (the
whole guard): the band part and the off-band part together. -/
def LoMixedErrStatement (P : ℤ[X]) (p₁ p₂ : ENNReal) : Prop :=
  ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r →
    ∃ c : ℝ, 0 ≤ c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → 1 ≤ l₂ →
          MeasureTheory.eLpNorm (fun x : ℤ =>
              PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x
                  - loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x))
            (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) * ENNReal.ofReal (lossWeight c ρ 0 l₂ k₁ k₂)
              * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count

/-- **The §8 bound for the mixed model tuple** (paper §5--§8, `(lin-1)`/`(lin-2)` at the arithmetic
heights `(0,l₂)`): `‖V^r (loMixedTuple)‖_{ℓ^p} ≤ K(Λ)·lossWeight c ρ 0 l₂ k₁ k₂·‖f‖_{p₁}‖g‖_{p₂}`.
At arithmetic height `0` the twisted bilinear multiplier factorizes exactly as a product of
one-variable convolutions, so this reduces to the two *linear* lacunary variational estimates. -/
def LoMixedModelStatement (P : ℤ[X]) (p₁ p₂ : ENNReal) : Prop :=
  ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r →
    ∃ c : ℝ, 0 ≤ c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → 1 ≤ l₂ →
          MeasureTheory.eLpNorm (fun x : ℤ =>
              PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x))
            (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) * ENNReal.ofReal (lossWeight c ρ 0 l₂ k₁ k₂)
              * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count

end

end Work.KMTAreas.A7
