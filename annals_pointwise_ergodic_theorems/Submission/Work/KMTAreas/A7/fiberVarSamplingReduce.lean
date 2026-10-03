/-
# The reduction of `fiberVarSampling` to the large-scale (`L > B(ρ)`) fibre estimate

## What this file does

The target `Work.KMTAreas.A7.fiberVarSampling` is, by `fiberVarSampling_of_core`, a consequence
of the analytic core `Work.KMTAreas.A7.fiberOpVarSamplingCoreTex`.  That core is *unconditional*
in the scale `L = max (max l₁ l₂) (max k₁ k₂)`: it has to handle both the *bounded-scale*
regime `L ≤ B(ρ)` (where the packet band may sit above the Farey gap of `(ℚ/ℤ)_{≤l₁}`) and the
*Farey/strict* regime `L > B(ρ)`.

This file performs the bookkeeping split, and isolates the analytic content in the *single*
statement `FiberVarSamplingLarge` (defined below, delegated as
`Submission/Work/KMTAreas/A7/fiberVarSamplingLarge.lean`):

* **Case 1, `L ≤ B(ρ)`** — `fiberOpVarNonFareyBounded` (proved, sorry-free) gives the estimate
  *per residue*, uniformly in `n₀`, with a constant depending on `ρ`, `p` and `B`; the
  `residueLp`-average is then converted into the per-residue `ℓ^p`-norms with the (proved)
  Tonelli identity `Work.KMTAreas.A7Hi.eLpNormResidueLpEq`.
* **Case 2, `L > B(ρ)`** — here `farey_and_strict_of_large_L` (proved) supplies *both*
  the quantitative Farey (Shannon) condition `8·2^{k₁}·arithQ ρ (max l₁ l₂) ≤ N` *and* the strict
  main-regime condition `k₁ + 2·uScale ρ L + 1 ≤ Log N`, and
  `exists_nonAliasing_uScale` (proved here) supplies the non-aliasing of the arithmetic
  frequencies at the packet scale.  The estimate in this regime is the delegated statement.

The main theorem is `fiberVarSampling_of_large`: it takes `FiberVarSamplingLarge` as a hypothesis
and produces the target.  The instance of `FiberVarSamplingLarge` itself is the delegated lemma.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.farey_and_strict_of_large_L
import Submission.Work.KMTAreas.A7.varphiNt_support_le
import Submission.Work.KMTAreas.A7.fiberVarSamplingCoreG
import Submission.Work.KMTAreas.A7Hi.eLpNormResidueLpEq

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.EndVar

/-! ## The fibre is a translate of a (modulated) Ionescu--Wainger convolution -/

/-- **The fibre is a translate of the Ionescu–Wainger convolution with the *modulated* bump**
`periodize m · e(-M·)`.  This is the algebraic reduction of the fibre estimate: composing with the
shift `x ↦ x - M` (an `ℓ^p`-isometry) turns `fiberOp ρ l m M` into the single Ionescu–Wainger
multiplier with symbol `iwSymbolSet (iwArithFreqsNew ρ l) (periodize m · e(-M·))`.

This identity (a specialisation of `Work.KMTAreas.A7.fiberOpP_eq_translate_iwConv`, itself
sorry-free) is what reduces the large-scale fibre estimate to a *uniform in `M`* Ionescu–Wainger
multiplier bound: the symbol `periodize m · e(-M·)` is a *modulation* of `periodize m`, so its
`L^q(ℝ)`-multiplier norm equals that of `periodize m`, and its support is that of `periodize m`;
KMT Theorem `2iw` therefore applies to *all* `M` simultaneously, and indeed its *proved*
`ℓ`-uniform form `Work.KMTAreas.iwEvenMultiplierGapUniform` (sorry-free, `Submission/Work/KMTAreas/
iwEvenMultiplierGapUniform.lean`) gives the even-exponent case with a constant `C·M` **independent
of the level `l`** (and of the modulation `M`).  The remaining gap in the fibre estimate is the
`V^r`-valued (rather than Hilbert-valued) form of that bound, which is KMT's vector-valued `2iw`. -/
theorem fiberOp_eq_translate_iwConv (ρ : ℝ) (l : ℕ) (m : ℝ → ℂ) (hm : Integrable m)
    (hint : ∀ α ∈ iwArithFreqsNew ρ l,
      Integrable (fun ξ : Work.Analysis.IonescuWainger.Circle => periodize m (ξ - α))
        Work.Analysis.IonescuWainger.circleMeasure)
    (M : ℤ) (v : ℤ → ℂ) :
    fiberOp ρ l m M v = fun x : ℤ => Work.Analysis.IWMultiplier.iwConv
        (iwArithFreqsNew ρ l)
        (fun η : Work.Analysis.IonescuWainger.Circle =>
          periodize m η * fourier (T := 1) (-M) η) v (x - M) := by
  have hX : (Polynomial.X : Polynomial ℤ).eval M = M := Polynomial.eval_X
  have hfe : fiberOpP ρ Polynomial.X l m M v = fiberOp ρ l m M v := by
    unfold fiberOpP fiberOp
    rw [hX]
  have h := fiberOpP_eq_translate_iwConv ρ Polynomial.X l m hm hint M v
  rw [hX] at h
  rw [hfe] at h
  exact h

/-! ## The support of the modulated bump in the strict main regime -/

/-- **In the strict main regime the modulated bump `varphiNt N k₁ t` is supported in the arc of
radius `2^{-2·U-1}`, i.e. inside the *plateau* of `mStarF U`.**  This is the hypothesis that makes
the fibre's window cut the identity on the input family (and hence turns the fibre into the
arithmetic rephasing). -/
theorem varphiNt_support_strict (N k₁ : ℕ) (t : ℝ) (U : ℕ)
    (h : k₁ + 2 * U + 1 ≤ (logN N).toNat) :
    ∀ ξ : ℝ, varphiNt N k₁ t ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1) := by
  have hlog : ((k₁ + 2 * U + 1 : ℕ) : ℤ) ≤ logN N := by
    have h0 : (0 : ℤ) ≤ logN N := logN_nonneg N
    have := h
    omega
  have hlogR : (k₁ : ℝ) + 2 * (U : ℝ) + 1 ≤ (logN N : ℝ) := by
    have h := hlog
    have h2 : ((k₁ + 2 * U + 1 : ℕ) : ℤ) = (k₁ : ℤ) + 2 * (U : ℤ) + 1 := by push_cast; ring
    rw [h2] at h
    exact_mod_cast h
  have hz : ((-(2 * (U : ℤ)) - 1 : ℤ) : ℝ) = -(2 * (U : ℝ)) - 1 := by push_cast; ring
  have htarget : (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1) = (2 : ℝ) ^ (-(2 * (U : ℝ)) - 1) := by
    rw [← Real.rpow_intCast 2 (-(2 * (U : ℤ)) - 1), hz]
  intro ξ hξ
  rw [htarget]
  rcases Nat.eq_zero_or_pos k₁ with hk | hk
  · -- `k₁ = 0`
    subst hk
    simp only [varphiNt, varphiN, if_true, Nat.cast_zero] at hξ
    obtain ⟨h1, _⟩ := mul_ne_zero_iff.mp hξ
    have h2 : ¬ ((1 : ℝ) ≤ |((2 : ℝ) ^ (logN N : ℝ)) * ξ|) := fun hc =>
      h1 (Work.KMTContract.kmtEta_zero hc)
    have h3 : |((2 : ℝ) ^ (logN N : ℝ)) * ξ| < 1 := lt_of_not_ge h2
    have hp : (0 : ℝ) < (2 : ℝ) ^ (logN N : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    rw [abs_mul, abs_of_pos hp] at h3
    have h4 : |ξ| ≤ ((2 : ℝ) ^ (logN N : ℝ))⁻¹ := by
      rw [inv_eq_one_div, le_div_iff₀ hp]
      nlinarith [h3, abs_nonneg ξ]
    have h5 : ((2 : ℝ) ^ (logN N : ℝ))⁻¹ ≤ (2 : ℝ) ^ (-(2 * (U : ℝ)) - 1) := by
      rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      linarith [hlogR]
    linarith
  · -- `k₁ ≥ 1`
    refine le_trans (varphiNt_support_le k₁ hk N t ξ hξ) ?_
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    linarith

/-! ## Non-aliasing at the packet scale, for large `L` -/

/-- **The Ionescu–Wainger arithmetic frequencies do not alias at the packet scale
`2^{-2·uScale ρ L}`, for `L` large.**  `exists_goodMajorArcs_nonAliasing` gives non-aliasing at
every scale `k ≤ -Cρ·2^{ρl}`; for `l ≤ L` and `L` large the packet scale
`k = -(2·uScale ρ L)` (with `2·uScale ρ L ≥ 2^{2ρL} - 2` growing doubly exponentially while
`Cρ·2^{ρL}` grows only exponentially) satisfies this. -/
theorem exists_nonAliasing_uScale (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ B : ℕ, ∀ (l L : ℕ), l ≤ L → B ≤ L →
      NonAliasing (-(2 * (uScale ρ L : ℤ))) (iwArithFreqs ρ l) := by
  obtain ⟨Cρ, hCρpos, hCρ⟩ := exists_goodMajorArcs_nonAliasing hρ
  refine ⟨⌈Real.logb 2 (2 * (Cρ + 1)) / ρ⌉₊ + 1, fun l L hl hBL => ?_⟩
  refine hCρ l (-(2 * (uScale ρ L : ℤ))) ?_
  rw [GoodMajorArcs]
  have hu : uScale ρ L = ⌊(2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋₊ := by
    simp only [uScale, scaleCount, Int.floor_toNat, Nat.cast_one, one_mul]
  have hα1 : (1 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l : ℝ)) := Real.one_le_rpow (by norm_num) (by positivity)
  have hαpos : (0 : ℝ) < (2 : ℝ) ^ (ρ * (l : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  -- `2 * (Cρ + 1) ≤ 2^{ρL}` for `L ≥ B`
  have hyLle : 2 * (Cρ + 1) ≤ (2 : ℝ) ^ (ρ * (L : ℝ)) := by
    have hceil : Real.logb 2 (2 * (Cρ + 1)) / ρ
        ≤ ((⌈Real.logb 2 (2 * (Cρ + 1)) / ρ⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have hLle : ((⌈Real.logb 2 (2 * (Cρ + 1)) / ρ⌉₊ : ℕ) : ℝ) ≤ (L : ℝ) := by
      have : ⌈Real.logb 2 (2 * (Cρ + 1)) / ρ⌉₊ ≤ L := by omega
      exact_mod_cast this
    have hmul : Real.logb 2 (2 * (Cρ + 1)) / ρ * ρ ≤ (L : ℝ) * ρ :=
      mul_le_mul_of_nonneg_right (le_trans hceil hLle) hρ.le
    have hlog : Real.logb 2 (2 * (Cρ + 1)) ≤ ρ * (L : ℝ) := by
      have hcancel : Real.logb 2 (2 * (Cρ + 1)) / ρ * ρ = Real.logb 2 (2 * (Cρ + 1)) :=
        div_mul_cancel₀ _ hρ.ne'
      rw [hcancel] at hmul
      linarith
    calc 2 * (Cρ + 1) = (2 : ℝ) ^ (Real.logb 2 (2 * (Cρ + 1))) :=
          (Real.rpow_logb (b := 2) (x := 2 * (Cρ + 1)) (by norm_num) (by norm_num)
            (by linarith [hCρpos])).symm
      _ ≤ (2 : ℝ) ^ (ρ * (L : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hlog
  -- `2^{ρl} * 2(Cρ+1) ≤ 2^{2ρL}`
  have hα2 : (2 : ℝ) ^ (ρ * (l : ℝ)) * (2 * (Cρ + 1))
      ≤ (2 : ℝ) ^ (2 * ρ * (L : ℝ)) := by
    have hsl : (2 : ℝ) ^ (ρ * (l : ℝ)) * (2 : ℝ) ^ (ρ * (L : ℝ))
        = (2 : ℝ) ^ (ρ * (l : ℝ) + ρ * (L : ℝ)) :=
      (Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _).symm
    have hexp : ρ * (l : ℝ) + ρ * (L : ℝ) ≤ 2 * ρ * (L : ℝ) := by
      have hlL : (l : ℝ) ≤ (L : ℝ) := by exact_mod_cast hl
      nlinarith [hρ.le]
    calc (2 : ℝ) ^ (ρ * (l : ℝ)) * (2 * (Cρ + 1))
        ≤ (2 : ℝ) ^ (ρ * (l : ℝ)) * (2 : ℝ) ^ (ρ * (L : ℝ)) :=
          mul_le_mul_of_nonneg_left hyLle (le_of_lt hαpos)
      _ = (2 : ℝ) ^ (ρ * (l : ℝ) + ρ * (L : ℝ)) := hsl
      _ ≤ (2 : ℝ) ^ (2 * ρ * (L : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hfloor : (2 : ℝ) ^ (2 * ρ * (L : ℝ)) - 1
      < ((⌊(2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋₊ : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one ((2 : ℝ) ^ (2 * ρ * (L : ℝ)))
    linarith
  have hfin : Cρ * (2 : ℝ) ^ (ρ * (l : ℝ))
      ≤ 2 * ((⌊(2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋₊ : ℕ) : ℝ) := by
    nlinarith [hα2, hα1, hαpos.le, hCρpos.le, hfloor,
      mul_pos hCρpos hαpos]
  have hcastL : ((-(2 * (uScale ρ L : ℤ)) : ℤ) : ℝ)
      = -(2 * ((uScale ρ L : ℕ) : ℝ)) := by push_cast; ring
  rw [hcastL, hu]
  have hgoal : Cρ * (2 : ℝ) ^ (ρ * (l : ℝ))
      ≤ 2 * ((⌊(2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋₊ : ℕ) : ℝ) := hfin
  calc -(2 * ((⌊(2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋₊ : ℕ) : ℝ))
      ≤ -(Cρ * (2 : ℝ) ^ (ρ * (l : ℝ))) := by linarith
    _ = -Cρ * (2 : ℝ) ^ (ρ * (l : ℝ)) := by ring

/-! ## The large-scale fibre estimate -/

/-- **The large-scale (Farey/strict) fibre estimate — the single remaining analytic input of
`fiberVarSampling`.**

For `ρ ∈ (0,1]`, `p ∈ (1,∞)` and `r > 2` there is a constant `C = C(ρ,p,r)` such that, for every
quadruple of scales `(l₁,l₂,k₁,k₂)` with `L := max (max l₁ l₂) (max k₁ k₂)`, every `t ∈ [1/2,1]`,
every `f`, every scale sequence `N` and every clipping predicate `S`, if

* the quantitative Farey (Shannon) condition `8·2^{k₁}·arithQ ρ (max l₁ l₂) ≤ N n` holds at every
  scale (so that the packet band `2^{k₁}/N n` sits *below* the Farey gap of `(ℚ/ℤ)_{≤l₁}`), and
* the strict main-regime condition `k₁ + 2·uScale ρ L + 1 ≤ Log (N n)` holds at every scale (so
  that the packet band sits inside the *plateau* of the bump `mStarF (uScale ρ L)`), and
* the arithmetic frequencies `(ℚ/ℤ)_{≤l₁}` do not alias at the packet scale
  (`NonAliasing (-(2·uScale ρ L)) (iwArithFreqs ρ l₁)`),

then the `ℓ^p(ℤ)`-norm of the `ℓ^p`-average over the residues `n₀ < arithQ ρ (max l₁ l₂)` of the
variational norms of the fibres `fiberOp ρ l₁ (mStarF (uScale ρ L)) n₀` applied to the columns
`if S n then Tex ρ l₁ (varphiNt (N n) k₁ t) f else 0` is bounded by `C` times the `ℓ^p(ℤ)`-norm
of the variational norms of the columns themselves. -/
def FiberVarSamplingLarge : Prop :=
  ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ (p : ENNReal), 1 < p → p < ⊤ → ∀ (r : NNReal), 2 < r →
    ∃ C : ℝ, 0 < C ∧
      ∀ (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ) (N : ℕ → ℕ) (S : ℕ → Prop) [DecidablePred S],
        t ∈ Set.Icc (1/2 : ℝ) 1 →
        (∀ n : ℕ, (2 : ℝ) ^ k₁ * (arithQ ρ (max l₁ l₂) : ℝ) * 8 ≤ (N n : ℝ)) →
        (∀ n : ℕ, k₁ + 2 * uScale ρ (max (max l₁ l₂) (max k₁ k₂)) + 1
            ≤ (logN (N n)).toNat) →
        NonAliasing (-(2 * (uScale ρ (max (max l₁ l₂) (max k₁ k₂)) : ℤ)))
          (iwArithFreqs ρ l₁) →
        MeasureTheory.eLpNorm (fun x : ℤ => residueLp p.toReal (arithQ ρ (max l₁ l₂))
            (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
              fiberOp ρ l₁ (mStarF (uScale ρ (max (max l₁ l₂) (max k₁ k₂)))) n₀
                (if S n then Tex ρ l₁ (varphiNt (N n) k₁ t) f else 0) y)) x)
          p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
              (if S n then Tex ρ l₁ (varphiNt (N n) k₁ t) f else 0) x))
          p MeasureTheory.Measure.count

/-! ## The reduction -/

/-- **`fiberVarSampling` follows from the large-scale estimate `FiberVarSamplingLarge`.**

The proof splits on whether `L ≤ B(ρ)`.  In the bounded case the (already proved) unconditional
per-residue Young bound `fiberOpVarNonFareyBounded` applies, and the residue average is converted
into the per-residue `ℓ^p`-norms by the Tonelli identity `eLpNormResidueLpEq`; in the remaining
case `farey_and_strict_of_large_L` and `exists_nonAliasing_uScale` supply the three hypotheses of
`FiberVarSamplingLarge`, whose `S`-clipped family is exactly `Hcl` (`S := core …`,
`N n := ⌊a n⌋` on the core and a large constant elsewhere). -/
theorem fiberVarSampling_of_large (hlarge : FiberVarSamplingLarge)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (r : NNReal) (hr : 2 < r) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∀ (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
      ∃ C : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
          t ∈ Set.Icc (1/2 : ℝ) 1 →
          MeasureTheory.eLpNorm (fun x : ℤ =>
              Work.KMTAreas.A7.residueLp p.toReal (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
                (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r
                  (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l₁
                    (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ
                      (max (max l₁ l₂) (max k₁ k₂)))) n₀
                    (Work.KMTAreas.A7.Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n) y)) x) p
              MeasureTheory.Measure.count
            ≤ (C Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                  (fun n : ℕ => Work.KMTAreas.A7.Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n x)) p
                  MeasureTheory.Measure.count := by
  refine ⟨4, by norm_num, 1, by norm_num, ?_⟩
  intro ρ hρ hρ1 p hp hptop
  obtain ⟨Bfas, hBfas⟩ := farey_and_strict_of_large_L ρ hρ hρ1
  obtain ⟨Bna, hBna⟩ := exists_nonAliasing_uScale ρ hρ hρ1
  obtain ⟨C₁, hC₁pos, hC₁⟩ :=
    fiberOpVarNonFareyBounded r hr ρ hρ hρ1 p hp hptop (fun _ => max Bfas Bna)
  obtain ⟨C₂, hC₂pos, hC₂⟩ := hlarge ρ hρ hρ1 p hp hptop r hr
  have hpne : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have hpt := ne_of_lt hptop
  have hppos : (0 : ℝ) < p.toReal := ENNReal.toReal_pos hpne hpt
  have hpposne : p.toReal ≠ 0 := ne_of_gt hppos
  have hpo : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal hpt
  refine ⟨fun _ => Real.toNNReal (max C₁ C₂ + 1), ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ t f _hΛ _hac _ha1 ht
  set L : ℕ := max (max l₁ l₂) (max k₁ k₂) with hLdef
  set q : ℕ := arithQ ρ (max l₁ l₂) with hqdef
  have hqpos : 0 < q := arithQ_pos ρ (max l₁ l₂)
  set B : ℕ := max Bfas Bna with hBdef
  set N₀ : ENNReal := MeasureTheory.eLpNorm (fun x : ℤ =>
      PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n x)) p MeasureTheory.Measure.count with hN₀
  -- the constant absorbs the loss and the two case constants
  have hconst : ENNReal.ofReal (max C₁ C₂ + 1)
      ≤ ((Real.toNNReal (max C₁ C₂ + 1) : NNReal) : ENNReal) *
          ENNReal.ofReal (lossWeight 4 ρ l₁ l₂ k₁ k₂) := by
    have h2 : ((Real.toNNReal (max C₁ C₂ + 1) : NNReal) : ENNReal)
        = ENNReal.ofReal (max C₁ C₂ + 1) := ENNReal.ofNNReal_toNNReal _
    rw [h2]
    have h3 : (1 : ENNReal) ≤ ENNReal.ofReal (lossWeight 4 ρ l₁ l₂ k₁ k₂) := by
      have hlr : (0 : ℝ) ≤ lmaxR l₁ l₂ k₁ k₂ := by
        rw [lmaxR]
        have h : (0 : ℤ) ≤ lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) := by rw [lmax]; omega
        exact_mod_cast h
      rw [ENNReal.one_le_ofReal, lossWeight]
      refine one_le_mul_of_one_le_of_one_le ?_ ?_
      · exact Real.one_le_rpow (by linarith) (by norm_num)
      · exact Real.one_le_rpow (by norm_num) (by positivity)
    calc ENNReal.ofReal (max C₁ C₂ + 1)
        = ENNReal.ofReal (max C₁ C₂ + 1) * 1 := (mul_one _).symm
      _ ≤ ENNReal.ofReal (max C₁ C₂ + 1) * ENNReal.ofReal (lossWeight 4 ρ l₁ l₂ k₁ k₂) :=
          mul_le_mul_of_nonneg_left h3 bot_le
  have hfinal : ∀ X : ENNReal, ENNReal.ofReal (max C₁ C₂ + 1) * X
      ≤ ((Real.toNNReal (max C₁ C₂ + 1) : NNReal) : ENNReal) *
          ENNReal.ofReal (lossWeight 4 ρ l₁ l₂ k₁ k₂) * X := by
    intro X
    exact mul_le_mul_of_nonneg_right hconst bot_le
  by_cases hcase : L ≤ B
  · -- **Case 1**: bounded scales; the unconditional per-residue Young bound applies.
    have hper : ∀ n₀ : ℤ, MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => fiberOp ρ l₁
            (mStarF (uScale ρ L)) n₀ (Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n) x)) p
            MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C₁ * N₀ := by
      intro n₀
      have h := hC₁ l₁ l₂ k₁ k₂ (by rw [← hLdef]; exact hcase) n₀
        (fun n => Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n)
      have e1 : uScale ρ (max (max l₁ l₂) (max k₁ k₂)) = uScale ρ L := by rw [hLdef]
      rw [e1] at h
      rw [hN₀]
      exact h
    -- the residue average, via the Tonelli identity
    set F : ℤ → ℕ → ENNReal := fun y n₀ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => fiberOp ρ l₁ (mStarF (uScale ρ L)) n₀
          (Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n) y) with hF
    have hkey := Work.KMTAreas.A7Hi.eLpNormResidueLpEq p.toReal hppos q F
    rw [hpo] at hkey
    have hLHS : MeasureTheory.eLpNorm (fun x : ℤ => residueLp p.toReal q F x) p
          MeasureTheory.Measure.count
        = ENNReal.rpow (ENNReal.rpow (q : ENNReal) (-1) *
            ∑ n₀ ∈ Finset.range q, (MeasureTheory.eLpNorm (fun y : ℤ => F y n₀) p
              MeasureTheory.Measure.count) ^ p.toReal) (1 / p.toReal) := hkey
    have hsum : (∑ n₀ ∈ Finset.range q, (MeasureTheory.eLpNorm (fun y : ℤ => F y n₀) p
            MeasureTheory.Measure.count) ^ p.toReal)
        ≤ (q : ENNReal) * (ENNReal.ofReal C₁ * N₀) ^ p.toReal := by
      calc (∑ n₀ ∈ Finset.range q, (MeasureTheory.eLpNorm (fun y : ℤ => F y n₀) p
              MeasureTheory.Measure.count) ^ p.toReal)
          ≤ ∑ _n₀ ∈ Finset.range q, (ENNReal.ofReal C₁ * N₀) ^ p.toReal :=
            Finset.sum_le_sum (fun n₀ _ => ENNReal.rpow_le_rpow (hper n₀) hppos.le)
        _ = (q : ENNReal) * (ENNReal.ofReal C₁ * N₀) ^ p.toReal := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hqE : (q : ENNReal) ≠ 0 := by exact_mod_cast hqpos.ne'
    have hqT : (q : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top q
    have hmain : ENNReal.rpow (ENNReal.rpow (q : ENNReal) (-1) *
          ∑ n₀ ∈ Finset.range q, (MeasureTheory.eLpNorm (fun y : ℤ => F y n₀) p
            MeasureTheory.Measure.count) ^ p.toReal) (1 / p.toReal)
        ≤ ENNReal.ofReal C₁ * N₀ := by
      have h2 : ENNReal.rpow (q : ENNReal) (-1) *
            (∑ n₀ ∈ Finset.range q, (MeasureTheory.eLpNorm (fun y : ℤ => F y n₀) p
              MeasureTheory.Measure.count) ^ p.toReal)
          ≤ (ENNReal.ofReal C₁ * N₀) ^ p.toReal := by
        have h1 : ENNReal.rpow (q : ENNReal) (-1) = (q : ENNReal)⁻¹ :=
          ENNReal.rpow_neg_one (q : ENNReal)
        refine le_trans (mul_le_mul_of_nonneg_left hsum bot_le) ?_
        rw [h1, ← mul_assoc, ENNReal.inv_mul_cancel hqE hqT, one_mul]
      refine le_trans (ENNReal.rpow_le_rpow h2 (by positivity)) ?_
      have h4 : ENNReal.rpow (ENNReal.rpow (ENNReal.ofReal C₁ * N₀) p.toReal) (1 / p.toReal)
          = ENNReal.ofReal C₁ * N₀ := by
        simpa [one_div, inv_inv] using
          ENNReal.rpow_inv_rpow (y := (p.toReal)⁻¹) (inv_ne_zero hpposne)
            (ENNReal.ofReal C₁ * N₀)
      exact le_of_eq h4
    calc MeasureTheory.eLpNorm (fun x : ℤ => residueLp p.toReal q (fun y n₀ =>
            PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => fiberOp ρ l₁
              (mStarF (uScale ρ L)) n₀ (Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n) y)) x)
          p MeasureTheory.Measure.count
        = MeasureTheory.eLpNorm (fun x : ℤ => residueLp p.toReal q F x) p
            MeasureTheory.Measure.count := rfl
      _ = ENNReal.rpow (ENNReal.rpow (q : ENNReal) (-1) *
            ∑ n₀ ∈ Finset.range q, (MeasureTheory.eLpNorm (fun y : ℤ => F y n₀) p
              MeasureTheory.Measure.count) ^ p.toReal) (1 / p.toReal) := hLHS
      _ ≤ ENNReal.ofReal C₁ * N₀ := hmain
      _ ≤ ENNReal.ofReal (max C₁ C₂ + 1) * N₀ :=
          mul_le_mul_of_nonneg_right
            (ENNReal.ofReal_le_ofReal (le_trans (le_max_left C₁ C₂) (le_add_of_nonneg_right zero_le_one)))
            bot_le
      _ ≤ (((Real.toNNReal (max C₁ C₂ + 1) : NNReal)) : ENNReal) *
            ENNReal.ofReal (lossWeight 4 ρ l₁ l₂ k₁ k₂) * N₀ := hfinal N₀
  · -- **Case 2**: `L > B(ρ)`; the Farey, strict and non-aliasing hypotheses all hold.
    have hcase' : ¬ (max (max l₁ l₂) (max k₁ k₂) ≤ B) := by rwa [hLdef] at hcase
    have hBlt : B < max (max l₁ l₂) (max k₁ k₂) := not_le.mp hcase'
    have hBfasL : Bfas < max (max l₁ l₂) (max k₁ k₂) := lt_of_le_of_lt (le_max_left _ _) hBlt
    have hBnaL : Bna < max (max l₁ l₂) (max k₁ k₂) := lt_of_le_of_lt (le_max_right _ _) hBlt
    have hl₁L : l₁ ≤ L := by rw [hLdef]; omega
    set HUGE : ℕ := 8 * 2 ^ k₁ * arithQ ρ (max l₁ l₂) + 2 ^ (k₁ + 2 * uScale ρ L + 1) + 1
      with hHUGE
    set N : ℕ → ℕ := fun n => if core ρ C₀ l₁ l₂ k₁ k₂ a n then Nat.floor (a n) else HUGE
      with hNdef
    have hNcore : ∀ n : ℕ, core ρ C₀ l₁ l₂ k₁ k₂ a n → N n = Nat.floor (a n) := by
      intro n hn
      rw [hNdef]
      simp only [hn, if_true]
    have hNnot : ∀ n : ℕ, ¬ core ρ C₀ l₁ l₂ k₁ k₂ a n → N n = HUGE := by
      intro n hn
      rw [hNdef]
      simp only [hn, if_false]
    have hfarey : ∀ n : ℕ, (2 : ℝ) ^ k₁ * (arithQ ρ (max l₁ l₂) : ℝ) * 8 ≤ (N n : ℝ) := by
      intro n
      by_cases hn : core ρ C₀ l₁ l₂ k₁ k₂ a n
      · rw [hNcore n hn]
        refine (hBfas l₁ l₂ k₁ k₂ (Nat.floor (a n)) (by
          have h := hn; simp only [core] at h; exact h.2.1) hBfasL).1
      · rw [hNnot n hn]
        have hle : 8 * 2 ^ k₁ * arithQ ρ (max l₁ l₂) ≤ HUGE := by
          rw [hHUGE]
          exact le_trans (Nat.le_add_right _ _) (Nat.le_succ _)
        calc (2 : ℝ) ^ k₁ * (arithQ ρ (max l₁ l₂) : ℝ) * 8
            = ((8 * 2 ^ k₁ * arithQ ρ (max l₁ l₂) : ℕ) : ℝ) := by push_cast; ring
          _ ≤ (HUGE : ℝ) := by exact_mod_cast hle
    have hstrict : ∀ n : ℕ, k₁ + 2 * uScale ρ L + 1 ≤ (logN (N n)).toNat := by
      intro n
      by_cases hn : core ρ C₀ l₁ l₂ k₁ k₂ a n
      · rw [hNcore n hn]
        refine (hBfas l₁ l₂ k₁ k₂ (Nat.floor (a n)) (by
          have h := hn; simp only [core] at h; exact h.2.1) hBfasL).2
      · rw [hNnot n hn, logN, Int.toNat_natCast]
        have hle : 2 ^ (k₁ + 2 * uScale ρ L + 1) ≤ HUGE := by
          rw [hHUGE]
          exact le_trans (Nat.le_add_left _ _) (Nat.le_succ _)
        exact le_trans (Nat.le_log_of_pow_le (by norm_num) hle)
          (Nat.log_mono_right (le_max_left _ _))
    have hna : NonAliasing (-(2 * (uScale ρ L : ℤ))) (iwArithFreqs ρ l₁) :=
      hBna l₁ L hl₁L (le_of_lt hBnaL)
    have hHclfun : Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f
        = (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n then
            Tex ρ l₁ (varphiNt (N n) k₁ t) f else 0) := by
      funext n
      by_cases hn : core ρ C₀ l₁ l₂ k₁ k₂ a n
      · simp only [Hcl, hn, if_true, hNcore n hn]
      · simp only [Hcl, hn, if_false]
    have hN₀' : N₀ = MeasureTheory.eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          (if core ρ C₀ l₁ l₂ k₁ k₂ a n then Tex ρ l₁ (varphiNt (N n) k₁ t) f
            else 0) x)) p MeasureTheory.Measure.count := by
      rw [hN₀]
      simp only [hHclfun]
    have h := hC₂ l₁ l₂ k₁ k₂ t f N (fun n => core ρ C₀ l₁ l₂ k₁ k₂ a n)
      ht hfarey hstrict hna
    have hu : uScale ρ (max (max l₁ l₂) (max k₁ k₂)) = uScale ρ L := by rw [hLdef]
    rw [hu] at h
    rw [← hN₀'] at h
    calc MeasureTheory.eLpNorm (fun x : ℤ => residueLp p.toReal q (fun y n₀ =>
            PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => fiberOp ρ l₁
              (mStarF (uScale ρ L)) n₀ (Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n) y)) x)
          p MeasureTheory.Measure.count
        = MeasureTheory.eLpNorm (fun x : ℤ => residueLp p.toReal (arithQ ρ (max l₁ l₂))
            (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => fiberOp ρ l₁
              (mStarF (uScale ρ L)) n₀ (Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n) y)) x)
          p MeasureTheory.Measure.count := rfl
      _ = MeasureTheory.eLpNorm (fun x : ℤ => residueLp p.toReal (arithQ ρ (max l₁ l₂))
            (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => fiberOp ρ l₁
              (mStarF (uScale ρ L)) n₀
                (if core ρ C₀ l₁ l₂ k₁ k₂ a n then Tex ρ l₁ (varphiNt (N n) k₁ t) f
                  else 0) y)) x) p MeasureTheory.Measure.count := by
          simp only [hHclfun]
      _ ≤ ENNReal.ofReal C₂ * N₀ := h
      _ ≤ ENNReal.ofReal (max C₁ C₂ + 1) * N₀ :=
          mul_le_mul_of_nonneg_right
            (ENNReal.ofReal_le_ofReal (le_trans (le_max_right C₁ C₂) (le_add_of_nonneg_right zero_le_one)))
            bot_le
      _ ≤ ((Real.toNNReal (max C₁ C₂ + 1) : NNReal) : ENNReal) *
            ENNReal.ofReal (lossWeight 4 ρ l₁ l₂ k₁ k₂) * N₀ := hfinal N₀
      _ = ((Real.toNNReal (max C₁ C₂ + 1) : NNReal) : ENNReal) *
            ENNReal.ofReal (lossWeight 4 ρ l₁ l₂ k₁ k₂) *
            MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n x)) p MeasureTheory.Measure.count := by
          rw [hN₀]

/-! ## The loss-weighted large-scale fibre estimate -/

/-- **The loss-weighted form of the large-scale fibre estimate.**  Identical to
`FiberVarSamplingLarge` except that the constant may carry the loss `lossWeight A ρ l₁ l₂ k₁ k₂`
(with `A` fixed, so that `lossWeight A ρ l₁ l₂ k₁ k₂ ≥ 1`).  This is the form that the *proved*
machinery of the chapter delivers (see the docstring of
`Submission/Work/KMTAreas/A7/fiberVarSamplingLarge.lean`), and it is all the target needs: the
target's right-hand side carries exactly `ENNReal.ofReal (lossWeight A ρ l₁ l₂ k₁ k₂)`. -/
def FiberVarSamplingLargeLoss : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧
    ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ (p : ENNReal), 1 < p → p < ⊤ → ∀ (r : NNReal), 2 < r →
      ∃ C : ℝ, 0 < C ∧
        ∀ (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ) (N : ℕ → ℕ) (S : ℕ → Prop) [DecidablePred S],
          t ∈ Set.Icc (1/2 : ℝ) 1 →
          (∀ n : ℕ, (2 : ℝ) ^ k₁ * (arithQ ρ (max l₁ l₂) : ℝ) * 8 ≤ (N n : ℝ)) →
          (∀ n : ℕ, k₁ + 2 * uScale ρ (max (max l₁ l₂) (max k₁ k₂)) + 1
              ≤ (logN (N n)).toNat) →
          NonAliasing (-(2 * (uScale ρ (max (max l₁ l₂) (max k₁ k₂)) : ℤ)))
            (iwArithFreqs ρ l₁) →
          MeasureTheory.eLpNorm (fun x : ℤ => residueLp p.toReal (arithQ ρ (max l₁ l₂))
              (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                fiberOp ρ l₁ (mStarF (uScale ρ (max (max l₁ l₂) (max k₁ k₂)))) n₀
                  (if S n then Tex ρ l₁ (varphiNt (N n) k₁ t) f else 0) y)) x)
            p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C * lossWeight A ρ l₁ l₂ k₁ k₂) *
              MeasureTheory.eLpNorm (fun x : ℤ =>
                PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                  (if S n then Tex ρ l₁ (varphiNt (N n) k₁ t) f else 0) x))
              p MeasureTheory.Measure.count

/-- `lossWeight` is monotone in its first (exponent) argument, for nonnegative exponents. -/
theorem lossWeight_mono_A {A₁ A₂ : ℝ} (hA₁ : 0 ≤ A₁) (h : A₁ ≤ A₂) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (l₁ l₂ k₁ k₂ : ℕ) :
    lossWeight A₁ ρ l₁ l₂ k₁ k₂ ≤ lossWeight A₂ ρ l₁ l₂ k₁ k₂ := by
  have hL : (0 : ℝ) ≤ lmaxR l₁ l₂ k₁ k₂ := by
    rw [lmaxR]
    have h0 : (0 : ℤ) ≤ lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) := by rw [lmax]; omega
    exact_mod_cast h0
  have h1 : (1 : ℝ) ≤ 1 + lmaxR l₁ l₂ k₁ k₂ := by linarith
  rw [lossWeight, lossWeight]
  refine mul_le_mul ?_ ?_ (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _)
  · exact Real.rpow_le_rpow_of_exponent_le h1 h
  · refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h hρ) hL

/-- `lossWeight` is nonnegative. -/
theorem lossWeight_nonneg (c ρ : ℝ) (l₁ l₂ k₁ k₂ : ℕ) :
    0 ≤ lossWeight c ρ l₁ l₂ k₁ k₂ := by
  have hL : (0 : ℝ) ≤ lmaxR l₁ l₂ k₁ k₂ := by
    rw [lmaxR]
    have h0 : (0 : ℤ) ≤ lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) := by rw [lmax]; omega
    exact_mod_cast h0
  rw [lossWeight]
  exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by norm_num) _)

theorem fiberVarSampling_of_largeLoss (hlarge : FiberVarSamplingLargeLoss)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (r : NNReal) (hr : 2 < r) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∀ (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
      ∃ C : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
          t ∈ Set.Icc (1/2 : ℝ) 1 →
          MeasureTheory.eLpNorm (fun x : ℤ =>
              Work.KMTAreas.A7.residueLp p.toReal (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
                (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r
                  (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l₁
                    (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ
                      (max (max l₁ l₂) (max k₁ k₂)))) n₀
                    (Work.KMTAreas.A7.Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n) y)) x) p
              MeasureTheory.Measure.count
            ≤ (C Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                  (fun n : ℕ => Work.KMTAreas.A7.Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n x)) p
                  MeasureTheory.Measure.count := by
  obtain ⟨A₂, hA₂, hCL⟩ := hlarge
  refine ⟨max 4 A₂, by linarith [le_max_left (4:ℝ) A₂], 1, by norm_num, ?_⟩
  intro ρ hρ hρ1 p hp hptop
  obtain ⟨Bfas, hBfas⟩ := farey_and_strict_of_large_L ρ hρ hρ1
  obtain ⟨Bna, hBna⟩ := exists_nonAliasing_uScale ρ hρ hρ1
  obtain ⟨C₁, hC₁pos, hC₁⟩ :=
    fiberOpVarNonFareyBounded r hr ρ hρ hρ1 p hp hptop (fun _ => max Bfas Bna)
  obtain ⟨C₂, hC₂pos, hC₂⟩ := hCL ρ hρ hρ1 p hp hptop r hr
  have hpne : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have hpt := ne_of_lt hptop
  have hppos : (0 : ℝ) < p.toReal := ENNReal.toReal_pos hpne hpt
  have hpposne : p.toReal ≠ 0 := ne_of_gt hppos
  have hpo : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal hpt
  refine ⟨fun _ => Real.toNNReal (max C₁ C₂ + 1), ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ t f _hΛ _hac _ha1 ht
  set L : ℕ := max (max l₁ l₂) (max k₁ k₂) with hLdef
  set q : ℕ := arithQ ρ (max l₁ l₂) with hqdef
  have hqpos : 0 < q := arithQ_pos ρ (max l₁ l₂)
  set B : ℕ := max Bfas Bna with hBdef
  set N₀ : ENNReal := MeasureTheory.eLpNorm (fun x : ℤ =>
      PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n x)) p MeasureTheory.Measure.count with hN₀
  -- the constant absorbs the loss and the two case constants
  have hconst : ENNReal.ofReal (max C₁ C₂ + 1)
      ≤ ((Real.toNNReal (max C₁ C₂ + 1) : NNReal) : ENNReal) *
          ENNReal.ofReal (lossWeight (max 4 A₂) ρ l₁ l₂ k₁ k₂) := by
    have h2 : ((Real.toNNReal (max C₁ C₂ + 1) : NNReal) : ENNReal)
        = ENNReal.ofReal (max C₁ C₂ + 1) := ENNReal.ofNNReal_toNNReal _
    rw [h2]
    have h3 : (1 : ENNReal) ≤ ENNReal.ofReal (lossWeight (max 4 A₂) ρ l₁ l₂ k₁ k₂) := by
      have hlr : (0 : ℝ) ≤ lmaxR l₁ l₂ k₁ k₂ := by
        rw [lmaxR]
        have h : (0 : ℤ) ≤ lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) := by rw [lmax]; omega
        exact_mod_cast h
      rw [ENNReal.one_le_ofReal, lossWeight]
      refine one_le_mul_of_one_le_of_one_le ?_ ?_
      · exact Real.one_le_rpow (by linarith) (by linarith [le_max_left (4:ℝ) A₂])
      · exact Real.one_le_rpow (by norm_num) (by positivity)
    calc ENNReal.ofReal (max C₁ C₂ + 1)
        = ENNReal.ofReal (max C₁ C₂ + 1) * 1 := (mul_one _).symm
      _ ≤ ENNReal.ofReal (max C₁ C₂ + 1) * ENNReal.ofReal (lossWeight (max 4 A₂) ρ l₁ l₂ k₁ k₂) :=
          mul_le_mul_of_nonneg_left h3 bot_le
  have hΛ : ((Real.toNNReal (max C₁ C₂ + 1) : NNReal) : ENNReal)
      = ENNReal.ofReal (max C₁ C₂ + 1) := ENNReal.ofNNReal_toNNReal _
  have hfinal : ∀ X : ENNReal, ENNReal.ofReal (max C₁ C₂ + 1) * X
      ≤ ((Real.toNNReal (max C₁ C₂ + 1) : NNReal) : ENNReal) *
          ENNReal.ofReal (lossWeight (max 4 A₂) ρ l₁ l₂ k₁ k₂) * X := by
    intro X
    exact mul_le_mul_of_nonneg_right hconst bot_le
  by_cases hcase : L ≤ B
  · -- **Case 1**: bounded scales; the unconditional per-residue Young bound applies.
    have hper : ∀ n₀ : ℤ, MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => fiberOp ρ l₁
            (mStarF (uScale ρ L)) n₀ (Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n) x)) p
            MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C₁ * N₀ := by
      intro n₀
      have h := hC₁ l₁ l₂ k₁ k₂ (by rw [← hLdef]; exact hcase) n₀
        (fun n => Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n)
      have e1 : uScale ρ (max (max l₁ l₂) (max k₁ k₂)) = uScale ρ L := by rw [hLdef]
      rw [e1] at h
      rw [hN₀]
      exact h
    -- the residue average, via the Tonelli identity
    set F : ℤ → ℕ → ENNReal := fun y n₀ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => fiberOp ρ l₁ (mStarF (uScale ρ L)) n₀
          (Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n) y) with hF
    have hkey := Work.KMTAreas.A7Hi.eLpNormResidueLpEq p.toReal hppos q F
    rw [hpo] at hkey
    have hLHS : MeasureTheory.eLpNorm (fun x : ℤ => residueLp p.toReal q F x) p
          MeasureTheory.Measure.count
        = ENNReal.rpow (ENNReal.rpow (q : ENNReal) (-1) *
            ∑ n₀ ∈ Finset.range q, (MeasureTheory.eLpNorm (fun y : ℤ => F y n₀) p
              MeasureTheory.Measure.count) ^ p.toReal) (1 / p.toReal) := hkey
    have hsum : (∑ n₀ ∈ Finset.range q, (MeasureTheory.eLpNorm (fun y : ℤ => F y n₀) p
            MeasureTheory.Measure.count) ^ p.toReal)
        ≤ (q : ENNReal) * (ENNReal.ofReal C₁ * N₀) ^ p.toReal := by
      calc (∑ n₀ ∈ Finset.range q, (MeasureTheory.eLpNorm (fun y : ℤ => F y n₀) p
              MeasureTheory.Measure.count) ^ p.toReal)
          ≤ ∑ _n₀ ∈ Finset.range q, (ENNReal.ofReal C₁ * N₀) ^ p.toReal :=
            Finset.sum_le_sum (fun n₀ _ => ENNReal.rpow_le_rpow (hper n₀) hppos.le)
        _ = (q : ENNReal) * (ENNReal.ofReal C₁ * N₀) ^ p.toReal := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hqE : (q : ENNReal) ≠ 0 := by exact_mod_cast hqpos.ne'
    have hqT : (q : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top q
    have hmain : ENNReal.rpow (ENNReal.rpow (q : ENNReal) (-1) *
          ∑ n₀ ∈ Finset.range q, (MeasureTheory.eLpNorm (fun y : ℤ => F y n₀) p
            MeasureTheory.Measure.count) ^ p.toReal) (1 / p.toReal)
        ≤ ENNReal.ofReal C₁ * N₀ := by
      have h2 : ENNReal.rpow (q : ENNReal) (-1) *
            (∑ n₀ ∈ Finset.range q, (MeasureTheory.eLpNorm (fun y : ℤ => F y n₀) p
              MeasureTheory.Measure.count) ^ p.toReal)
          ≤ (ENNReal.ofReal C₁ * N₀) ^ p.toReal := by
        have h1 : ENNReal.rpow (q : ENNReal) (-1) = (q : ENNReal)⁻¹ :=
          ENNReal.rpow_neg_one (q : ENNReal)
        refine le_trans (mul_le_mul_of_nonneg_left hsum bot_le) ?_
        rw [h1, ← mul_assoc, ENNReal.inv_mul_cancel hqE hqT, one_mul]
      refine le_trans (ENNReal.rpow_le_rpow h2 (by positivity)) ?_
      have h4 : ENNReal.rpow (ENNReal.rpow (ENNReal.ofReal C₁ * N₀) p.toReal) (1 / p.toReal)
          = ENNReal.ofReal C₁ * N₀ := by
        simpa [one_div, inv_inv] using
          ENNReal.rpow_inv_rpow (y := (p.toReal)⁻¹) (inv_ne_zero hpposne)
            (ENNReal.ofReal C₁ * N₀)
      exact le_of_eq h4
    calc MeasureTheory.eLpNorm (fun x : ℤ => residueLp p.toReal q (fun y n₀ =>
            PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => fiberOp ρ l₁
              (mStarF (uScale ρ L)) n₀ (Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n) y)) x)
          p MeasureTheory.Measure.count
        = MeasureTheory.eLpNorm (fun x : ℤ => residueLp p.toReal q F x) p
            MeasureTheory.Measure.count := rfl
      _ = ENNReal.rpow (ENNReal.rpow (q : ENNReal) (-1) *
            ∑ n₀ ∈ Finset.range q, (MeasureTheory.eLpNorm (fun y : ℤ => F y n₀) p
              MeasureTheory.Measure.count) ^ p.toReal) (1 / p.toReal) := hLHS
      _ ≤ ENNReal.ofReal C₁ * N₀ := hmain
      _ ≤ ENNReal.ofReal (max C₁ C₂ + 1) * N₀ :=
          mul_le_mul_of_nonneg_right
            (ENNReal.ofReal_le_ofReal (le_trans (le_max_left C₁ C₂) (le_add_of_nonneg_right zero_le_one)))
            bot_le
      _ ≤ (((Real.toNNReal (max C₁ C₂ + 1) : NNReal)) : ENNReal) *
            ENNReal.ofReal (lossWeight (max 4 A₂) ρ l₁ l₂ k₁ k₂) * N₀ := hfinal N₀
  · -- **Case 2**: `L > B(ρ)`; the Farey, strict and non-aliasing hypotheses all hold.
    have hcase' : ¬ (max (max l₁ l₂) (max k₁ k₂) ≤ B) := by rwa [hLdef] at hcase
    have hBlt : B < max (max l₁ l₂) (max k₁ k₂) := not_le.mp hcase'
    have hBfasL : Bfas < max (max l₁ l₂) (max k₁ k₂) := lt_of_le_of_lt (le_max_left _ _) hBlt
    have hBnaL : Bna < max (max l₁ l₂) (max k₁ k₂) := lt_of_le_of_lt (le_max_right _ _) hBlt
    have hl₁L : l₁ ≤ L := by rw [hLdef]; omega
    set HUGE : ℕ := 8 * 2 ^ k₁ * arithQ ρ (max l₁ l₂) + 2 ^ (k₁ + 2 * uScale ρ L + 1) + 1
      with hHUGE
    set N : ℕ → ℕ := fun n => if core ρ C₀ l₁ l₂ k₁ k₂ a n then Nat.floor (a n) else HUGE
      with hNdef
    have hNcore : ∀ n : ℕ, core ρ C₀ l₁ l₂ k₁ k₂ a n → N n = Nat.floor (a n) := by
      intro n hn
      rw [hNdef]
      simp only [hn, if_true]
    have hNnot : ∀ n : ℕ, ¬ core ρ C₀ l₁ l₂ k₁ k₂ a n → N n = HUGE := by
      intro n hn
      rw [hNdef]
      simp only [hn, if_false]
    have hfarey : ∀ n : ℕ, (2 : ℝ) ^ k₁ * (arithQ ρ (max l₁ l₂) : ℝ) * 8 ≤ (N n : ℝ) := by
      intro n
      by_cases hn : core ρ C₀ l₁ l₂ k₁ k₂ a n
      · rw [hNcore n hn]
        refine (hBfas l₁ l₂ k₁ k₂ (Nat.floor (a n)) (by
          have h := hn; simp only [core] at h; exact h.2.1) hBfasL).1
      · rw [hNnot n hn]
        have hle : 8 * 2 ^ k₁ * arithQ ρ (max l₁ l₂) ≤ HUGE := by
          rw [hHUGE]
          exact le_trans (Nat.le_add_right _ _) (Nat.le_succ _)
        calc (2 : ℝ) ^ k₁ * (arithQ ρ (max l₁ l₂) : ℝ) * 8
            = ((8 * 2 ^ k₁ * arithQ ρ (max l₁ l₂) : ℕ) : ℝ) := by push_cast; ring
          _ ≤ (HUGE : ℝ) := by exact_mod_cast hle
    have hstrict : ∀ n : ℕ, k₁ + 2 * uScale ρ L + 1 ≤ (logN (N n)).toNat := by
      intro n
      by_cases hn : core ρ C₀ l₁ l₂ k₁ k₂ a n
      · rw [hNcore n hn]
        refine (hBfas l₁ l₂ k₁ k₂ (Nat.floor (a n)) (by
          have h := hn; simp only [core] at h; exact h.2.1) hBfasL).2
      · rw [hNnot n hn, logN, Int.toNat_natCast]
        have hle : 2 ^ (k₁ + 2 * uScale ρ L + 1) ≤ HUGE := by
          rw [hHUGE]
          exact le_trans (Nat.le_add_left _ _) (Nat.le_succ _)
        exact le_trans (Nat.le_log_of_pow_le (by norm_num) hle)
          (Nat.log_mono_right (le_max_left _ _))
    have hna : NonAliasing (-(2 * (uScale ρ L : ℤ))) (iwArithFreqs ρ l₁) :=
      hBna l₁ L hl₁L (le_of_lt hBnaL)
    have hHclfun : Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f
        = (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n then
            Tex ρ l₁ (varphiNt (N n) k₁ t) f else 0) := by
      funext n
      by_cases hn : core ρ C₀ l₁ l₂ k₁ k₂ a n
      · simp only [Hcl, hn, if_true, hNcore n hn]
      · simp only [Hcl, hn, if_false]
    have hN₀' : N₀ = MeasureTheory.eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          (if core ρ C₀ l₁ l₂ k₁ k₂ a n then Tex ρ l₁ (varphiNt (N n) k₁ t) f
            else 0) x)) p MeasureTheory.Measure.count := by
      rw [hN₀]
      simp only [hHclfun]
    have h := hC₂ l₁ l₂ k₁ k₂ t f N (fun n => core ρ C₀ l₁ l₂ k₁ k₂ a n)
      ht hfarey hstrict hna
    have hu : uScale ρ (max (max l₁ l₂) (max k₁ k₂)) = uScale ρ L := by rw [hLdef]
    rw [hu] at h
    rw [← hN₀'] at h
    calc MeasureTheory.eLpNorm (fun x : ℤ => residueLp p.toReal q (fun y n₀ =>
            PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => fiberOp ρ l₁
              (mStarF (uScale ρ L)) n₀ (Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n) y)) x)
          p MeasureTheory.Measure.count
        = MeasureTheory.eLpNorm (fun x : ℤ => residueLp p.toReal (arithQ ρ (max l₁ l₂))
            (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => fiberOp ρ l₁
              (mStarF (uScale ρ L)) n₀ (Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n) y)) x)
          p MeasureTheory.Measure.count := rfl
      _ = MeasureTheory.eLpNorm (fun x : ℤ => residueLp p.toReal (arithQ ρ (max l₁ l₂))
            (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => fiberOp ρ l₁
              (mStarF (uScale ρ L)) n₀
                (if core ρ C₀ l₁ l₂ k₁ k₂ a n then Tex ρ l₁ (varphiNt (N n) k₁ t) f
                  else 0) y)) x) p MeasureTheory.Measure.count := by
          simp only [hHclfun]
      _ ≤ ENNReal.ofReal (C₂ * lossWeight A₂ ρ l₁ l₂ k₁ k₂) * N₀ := h
      _ ≤ ENNReal.ofReal ((max C₁ C₂ + 1) * lossWeight (max 4 A₂) ρ l₁ l₂ k₁ k₂) * N₀ := by
          refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
          exact mul_le_mul (by linarith [le_max_right C₁ C₂])
            (lossWeight_mono_A hA₂ (le_max_right 4 A₂) ρ hρ.le l₁ l₂ k₁ k₂)
            (lossWeight_nonneg A₂ ρ l₁ l₂ k₁ k₂) (by linarith [le_max_right C₁ C₂])
      _ = ENNReal.ofReal (max C₁ C₂ + 1) *
            ENNReal.ofReal (lossWeight (max 4 A₂) ρ l₁ l₂ k₁ k₂) * N₀ := by
          rw [ENNReal.ofReal_mul (by linarith [le_max_right C₁ C₂])]
      _ = ((Real.toNNReal (max C₁ C₂ + 1) : NNReal) : ENNReal) *
            ENNReal.ofReal (lossWeight (max 4 A₂) ρ l₁ l₂ k₁ k₂) * N₀ := by
          rw [hΛ]
      _ = ((Real.toNNReal (max C₁ C₂ + 1) : NNReal) : ENNReal) *
            ENNReal.ofReal (lossWeight (max 4 A₂) ρ l₁ l₂ k₁ k₂) *
            MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n x)) p MeasureTheory.Measure.count := by
          rw [hN₀]


end

end Work.KMTAreas.A7
