/-
# The §7 (small-scale) objects of Area A7

This module fixes the small-scale counterparts of the large-scale vocabulary of
`Work.KMTAreas.A7.Large.Defs`, i.e. the objects of the paper's §7 (the regime `N ≤ splitCut ρ L`):

* `smallColTuple` — the family bounded by `VarpLossSmall`, i.e. the §5 columns `varpCol`
  restricted to the small scales `N ≤ splitCut ρ L`;
* `smallCond` — the condition under which the *main* small-scale tuples are nonzero: admissibility
  (`inIndexSet`), the small-scale cut (`N ≤ splitCut ρ L`) and the §6 main regime (`mainRegime`,
  i.e. `k + 2u ≤ Log N`, without which the functional calculus `bn-ident` is not available);
* `smallMainPart` — the concrete §5 columns `varpPiece` restricted to `smallCond`;
* `smallModelOp` / `smallModelTuple` — the §6 model operator
  `∫_{1/2}^1 B^{l₁,l₂,m_Ẑ}_{m_*}(T^{l₁}_{φ_{N,t}}·, T^{l₂}_{φ̃_{N,t}}·) dt`, exactly as in
  `Work.KMTAreas.A7.Large.Defs.modelTuple`: the kernel form of the twisted bilinear multiplier is
  regime-independent, only the *technique* used to bound it differs (Rademacher--Menshov for the
  small scales, Shannon sampling / the adelic model for the large ones);
* `smallExcPart` — the *exceptional* small scales, i.e. the columns which are admissible and small
  but **outside** the main regime.  Their parameters are bounded (`SmallExcSupport`), so they are
  estimated by the crude single-scale bound;
* `smallSplit` / `smallColTuple_eq_sum` — the pointwise splitting of the small-scale family into
  the model tuple, the model-approximation error and the exceptional part.

## Note on the arguments of the model operator

The model operator is applied to `f` and `g` **directly**, not to a background projection
`Π_{≤l,≤0} f`: the background at height `0` is *wide* (`periodize η ≥ 1` pointwise, and it is not a
partition of unity), so the off-diagonal arithmetic cross terms do not vanish and the composite
symbol is inflated by `≍ #(ℚ/ℤ)_{≤l}`, which no admissible loss can absorb.  The paper's own form
uses the *narrow* background `Π_{≤l,≤-u}` (`u = uScale ρ L`), on which the full-set and the
exact-height multipliers agree because `φ_{N,t}` is supported at frequency scale `2^{k}/N ≤ 2^{-2u}`;
writing the tuple in terms of `f, g` directly is the same thing, and it is what
`A7/Large/Defs.lean` does for the large scales.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.ModelApproxAux
import Submission.Work.KMTAreas.A7.ModelOps

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier
open Work.KMTContract
open Work.Analysis.EndVar

/-- The scale `L = max (max l₁ l₂) (max k₁ k₂)` of the small-scale cut. -/
def smallL (l₁ l₂ k₁ k₂ : ℕ) : ℕ := max (max l₁ l₂) (max k₁ k₂)

/-- **The small-scale column family**: the §5 columns restricted to the small scales
`N = ⌊a n⌋ ≤ splitCut ρ L`.  This is exactly the family whose `ℓ^p(ℤ;V^r)` norm is bounded by
`VarpLossSmall P p₁ p₂`. -/
noncomputable def smallColTuple (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) : ℕ → ℤ → ℂ :=
  fun n x =>
    if Nat.floor (a n) ≤ splitCut ρ (smallL l₁ l₂ k₁ k₂) then
      varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x
    else 0

theorem smallColTuple_apply (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ n : ℕ) (x : ℤ) :
    smallColTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x =
      if Nat.floor (a n) ≤ splitCut ρ (smallL l₁ l₂ k₁ k₂) then
        varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x
      else 0 := rfl

/-- **The small-scale condition**: the scale `N = ⌊a n⌋` is admissible, small
(`N ≤ splitCut ρ L`) and in the §6 main regime.  Both main small-scale tuples are defined by this
`if`-test, so this is the only case in which the §7 model approximation has content. -/
def smallCond (ρ : ℝ) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (n : ℕ) : Prop :=
  inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n)) ∧
    Nat.floor (a n) ≤ splitCut ρ (smallL l₁ l₂ k₁ k₂) ∧
    mainRegime ρ k₁ k₂ (Nat.floor (a n))

instance (ρ : ℝ) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ n : ℕ) :
    Decidable (smallCond ρ C₀ a l₁ l₂ k₁ k₂ n) := by
  unfold smallCond; infer_instance

/-- The main-regime part of the small-scale columns: the concrete §5 piece average on `smallCond`,
and zero elsewhere. -/
noncomputable def smallMainPart (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) : ℕ → ℤ → ℂ :=
  fun n x =>
    if smallCond ρ C₀ a l₁ l₂ k₁ k₂ n then
      varpPiece (kmtPj ρ) P P.natDegree (a n) f g l₁ l₂ k₁ k₂ x
    else 0

/-- **The arithmetic kernel of the twisted bilinear multiplier at exact arithmetic heights**:
the double Fourier coefficient `∑_{α₁,α₂} m_Ẑ(α₁,α₂)e(-j₁α₁)e(-j₂α₂)` of the arithmetic symbol
`(1_{(ℚ/ℤ)_{l₁}\(ℚ/ℤ)_{l₁-1}} ⊗ 1_{(ℚ/ℤ)_{l₂}\(ℚ/ℤ)_{l₂-1}})m_Ẑ`.

The contract's §5 pieces are the *exact arithmetic height* projections
`piExact (kmtPj ρ) l κ = kmtProj ρ l κ − kmtProj ρ (l-1) κ` (`Fpiece`, `Gpiece`), so the model
operator must be built from the exact-height frequency sets `diffFreqs ρ l` (this is the same
convention as `Work.KMTPlan.A6.arithKernelEx`).  Using the height-`≤ l` sets
(`Work.KMTAreas.A7.arithKernel`, `Btwist`) would add the lower-level pieces, which do not cancel
against the concrete column. -/
noncomputable def smallArithKernel (ρ : ℝ) (P : ℤ[X]) (q : ℕ) (l₁ l₂ : ℕ)
    (j₁ j₂ : ℤ) : ℂ :=
  ∑ α₁ ∈ diffFreqs ρ l₁, ∑ α₂ ∈ diffFreqs ρ l₂,
    mZ P q α₁ α₂ * fourier (T := 1) (-j₁) α₁ * fourier (T := 1) (-j₂) α₂

/-- **The twisted bilinear multiplier `B^{l₁,l₂,m_Ẑ}_{m₁⊗m₂}` of §6 at exact arithmetic
heights**, in the kernel form `∑_{j₁,j₂} K(j₁,j₂)h(x-j₁)k(x-j₂)`. -/
noncomputable def smallBtwist (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (h k : ℤ → ℂ) : ℤ → ℂ :=
  fun x => ∑' j₁ : ℤ, ∑' j₂ : ℤ,
    smallArithKernel ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ j₁ j₂ * cw m₁ j₁ * cw m₂ j₂
      * h (x - j₁) * k (x - j₂)

/-- **The §6 model operator** (with no regime test): the bilinear operator
`∫_{1/2}^1 B^{l₁,l₂,m_Ẑ}_{m_*}(T^{l₁}_{φ_{N,t}}·, T^{l₂}_{φ̃_{N,t}}·) dt` applied to `f` and `g`,
with the *exact-height* IW multipliers `Tm ρ l` (the same convention as the pieces `Fpiece`,
`Gpiece`) and the exact-height arithmetic symbol `smallArithKernel`.

The bumps are applied to `f`, `g` themselves, not to a background projection `Π_{≤l,≤0}`: the
paper's `F = Π_{≤l,≤-u}f` is *not* a bounded projection at the contract's bottom scale `u = 0`
(its symbol `∑_{β∈(ℚ/ℤ)_{≤l}}η` is `≥ 1` pointwise, so the operator norm is at least `2^l`), while
`T^l_φ(Π_{≤l,≤-u}f) = T^l_{φη_{≤-u}}f` and `φη_{≤-u} = φ` on the band `φ` lives in. -/
noncomputable def smallModelOp (ρ : ℝ) (P : ℤ[X]) (N l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ) : ℤ → ℂ :=
  fun x =>
    ∫ t in (1/2 : ℝ)..1,
      smallBtwist ρ P l₁ l₂
        (mStarF (uScale ρ (smallL l₁ l₂ k₁ k₂)))
        (mStargF P.natDegree (uScale ρ (smallL l₁ l₂ k₁ k₂)))
        (Tm ρ l₁ (varphiNt N k₁ t) f)
        (Tm ρ l₂ (varphitildeNt P P.natDegree N k₂ t) g) x

/-- **The small-scale model tuple of §6**: the model operator `smallModelOp` on `smallCond`, and
zero elsewhere.  It is the small-scale analogue of `Work.KMTAreas.A7.modelTuple`. -/
noncomputable def smallModelTuple (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) : ℕ → ℤ → ℂ :=
  fun n x =>
    if smallCond ρ C₀ a l₁ l₂ k₁ k₂ n then
      smallModelOp ρ P (Nat.floor (a n)) l₁ l₂ k₁ k₂ f g x
    else 0

theorem smallModelTuple_apply (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ n : ℕ) (x : ℤ) :
    smallModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x =
      (if smallCond ρ C₀ a l₁ l₂ k₁ k₂ n then
        smallModelOp ρ P (Nat.floor (a n)) l₁ l₂ k₁ k₂ f g x else 0) := rfl

/-- The exceptional part of the small-scale family: the columns which are admissible and small but
outside the §6 main regime.  By `SmallExcSupport` their parameters `l₁,l₂,k₁,k₂,N` are bounded by a
constant depending only on `C₀` (and `ρ ≤ 1/(8C₀)`), so that only finitely many lacunary scales
occur and the crude single-scale bound applies. -/
noncomputable def smallExcPart (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) : ℕ → ℤ → ℂ :=
  fun n x =>
    if inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n))
        ∧ Nat.floor (a n) ≤ splitCut ρ (smallL l₁ l₂ k₁ k₂)
        ∧ ¬ mainRegime ρ k₁ k₂ (Nat.floor (a n)) then
      varpPiece (kmtPj ρ) P P.natDegree (a n) f g l₁ l₂ k₁ k₂ x
    else 0

theorem smallExcPart_apply (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ n : ℕ) (x : ℤ) :
    smallExcPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x =
      (if inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n))
          ∧ Nat.floor (a n) ≤ splitCut ρ (smallL l₁ l₂ k₁ k₂)
          ∧ ¬ mainRegime ρ k₁ k₂ (Nat.floor (a n)) then
        varpPiece (kmtPj ρ) P P.natDegree (a n) f g l₁ l₂ k₁ k₂ x else 0) := rfl

/-- The predicate of the exceptional small scales, i.e. the guard of `smallExcPart`. -/
def smallExcPred (ρ : ℝ) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (n : ℕ) : Prop :=
  inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n)) ∧
    Nat.floor (a n) ≤ splitCut ρ (smallL l₁ l₂ k₁ k₂) ∧
    ¬ mainRegime ρ k₁ k₂ (Nat.floor (a n))

instance (ρ : ℝ) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ n : ℕ) :
    Decidable (smallExcPred ρ C₀ a l₁ l₂ k₁ k₂ n) := by
  unfold smallExcPred; infer_instance

theorem smallExcPart_eq_zero (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ n : ℕ) (h : ¬ smallExcPred ρ C₀ a l₁ l₂ k₁ k₂ n) :
    smallExcPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n = 0 := by
  simp only [smallExcPred] at h
  funext x
  rw [smallExcPart_apply, if_neg h]
  rfl

/-- **The pointwise splitting of the small-scale column family** into the model tuple, the
model-approximation error and the exceptional part. -/
theorem smallColTuple_eq_sum (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) :
    smallColTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ =
      fun n x => smallModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
        + ((smallMainPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
            - smallModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
          + smallExcPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) := by
  funext n x
  simp only [smallColTuple, smallModelTuple, smallMainPart, smallExcPart, smallCond,
    varpCol, Pi.sub_apply]
  by_cases hS : Nat.floor (a n) ≤ splitCut ρ (smallL l₁ l₂ k₁ k₂)
  <;> by_cases hI : inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n))
  <;> by_cases hM : mainRegime ρ k₁ k₂ (Nat.floor (a n))
  <;> simp only [hS, hI, hM, if_true, if_false, and_true, and_false, true_and, false_and,
      not_true_eq_false, not_false_eq_true]
  <;> ring

/-- The model-tuple-free form of the splitting: the small-scale columns are the sum of the
main part and the exceptional part.  (Obtained from `smallColTuple_eq_sum` by cancelling the model
operator; recorded because the crude estimates are phrased on `smallMainPart` and `smallExcPart`.) -/
theorem smallColTuple_eq_main_add_exc (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) :
    smallColTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ =
      fun n x => smallMainPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
        + smallExcPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x := by
  funext n x
  simp only [smallColTuple, smallMainPart, smallExcPart, smallCond, varpCol]
  by_cases hS : Nat.floor (a n) ≤ splitCut ρ (smallL l₁ l₂ k₁ k₂)
  <;> by_cases hI : inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n))
  <;> by_cases hM : mainRegime ρ k₁ k₂ (Nat.floor (a n))
  <;> simp only [hS, hI, hM, if_true, if_false, and_true, and_false, true_and, false_and,
      not_true_eq_false, not_false_eq_true]
  <;> ring

end

end Work.KMTAreas.A7
