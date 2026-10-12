import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseFixB1.perBoxF_pieces
import Submission.Work.BoseFixB1.perBoxMF_of_fibre_zero
import Submission.Work.BoseFixB1.tBwordKinInd_nonneg
import Submission.Work.BoseFixB1.w1MassB_le_const_mul_chiMass_regime
import Submission.Work.BoseFixB1.w1MassB_nonneg
import Submission.Work.BoseFixB1S.SbPotHalvesB1Fix
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.Up.Core` — cycle-free copies of the proved per-box layers

The target `Work.BoseFixB1.perBoxFWeight_holds` is *upstream* of `perBoxF_localised`,
`perBoxF_cases`, `perBoxF_thick`, `perBoxMF_cases`, ... (they all import it), so their
**proved** contents cannot be imported into it.  This module is a namespace-renamed
(`Work.BoseFixB1` → `Work.BoseFixB1.Up`) verbatim copy of the parts needed by the
dichotomy `PerBoxF ⟸ gap branch + flat branch + thin case`, so that the target file can
import them.

Copied from `Submission/Work/BoseFixB1/perBoxFWeight_holds.lean`
(its own helper lemmas), `.../perBoxF_localised.lean` (the fibre/pair/count peels and the
gap payment) and `.../perBoxF_thick.lean` (§1–§5: the `F`-rows, the `sbPot` split, the
gap regime, the gap branch `perBoxF_of_gapPayment` and the dichotomy
`perBoxF_thick_of_flatBranch`).  Nothing here is new mathematics.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1.Up

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 0. The case-split shapes (copied from `perBoxF_cases.lean`) -/

/-- The thin/degenerate box: no pair inside the cutoff support meets `supp g₀`. -/
def IsThinBox (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∀ x y : EuclideanSpace ℝ (Fin 3),
    Submission.BoseGases.chiSmallB (paramsAt μ (a v)).M (sideAt μ (a v))
      (paramsAt μ (a v)).d u x ≠ 0 →
    Submission.BoseGases.chiSmallB (paramsAt μ (a v)).M (sideAt μ (a v))
      (paramsAt μ (a v)).d u y ≠ 0 →
    Submission.BoseGases.g0 v h (x - y) = 0


/-- **`PerBoxF` with a case hypothesis on `(μ, u)`**: `PerBoxF`'s body *verbatim*, with the extra
hypothesis `P μ u`. -/
def PerBoxFCase (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ)
    (P : ℝ → EuclideanSpace ℝ (Fin 3) → Prop) : Prop :=
  ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : EuclideanSpace ℝ (Fin 3)),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
        P μ u →
        c₁ * (w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u *
            (∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 *
              psiWeight 1 μ (nCountB (paramsAt μ (a v)).M (sideAt μ (a v))
                (paramsAt μ (a v)).d u x /
                chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u)))
          - (1 / 2) * μ ^ 2 * w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
              (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ)
          - C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
                + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
              * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u *
              normB v μ n (Φ : X n → ℝ)
            + μ * (a v) * normB v μ n (Φ : X n → ℝ))
        ≤ sbWord h μ u (Φ : X n → ℝ)

abbrev PerBoxFAll (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  PerBoxFCase v h R (fun _ _ => True)

abbrev PerBoxF_thin (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  PerBoxFCase v h R (fun μ u => IsThinBox v h μ u)

abbrev PerBoxF_thick (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  PerBoxFCase v h R (fun μ u => ¬ IsThinBox v h μ u)


theorem perBoxMFCase_conv3Small_nonneg (M : ℕ) (x : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ Submission.BoseGases.conv3Small M x := by
  rw [Submission.BoseGases.conv3Small]
  exact integral_nonneg fun y => mul_nonneg (Submission.BoseGases.chiSmall_nonneg M y)
    (Submission.BoseGases.chiSmall_nonneg M _)

theorem perBoxMFCase_convScaleSmall_nonneg (M : ℕ) (c : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ Submission.BoseGases.convScaleSmall M c x := by
  rw [Submission.BoseGases.convScaleSmall]
  exact perBoxMFCase_conv3Small_nonneg M _

theorem perBoxMFCase_chiSmallB_nonneg (M : ℕ) (ℓ d : ℝ) (u x : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ Submission.BoseGases.chiSmallB M ℓ d u x := by
  rw [Submission.BoseGases.chiSmallB]
  exact mul_nonneg (Submission.BoseGases.chiScale_nonneg ℓ x)
    (Submission.BoseGases.chiSmall_nonneg M _)

theorem perBoxMFCase_wSmallPair_nonneg {M : ℕ} {ℓ d : ℝ} {u x y : EuclideanSpace ℝ (Fin 3)}
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : 0 ≤ f) :
    0 ≤ Submission.BoseGases.wSmallPair M ℓ d u f x y := by
  rw [Submission.BoseGases.wSmallPair, Submission.BoseGases.wSmallScaled]
  refine mul_nonneg (mul_nonneg ?_ ?_) ?_
  · exact perBoxMFCase_chiSmallB_nonneg M ℓ d u x
  · exact div_nonneg (div_nonneg (hf _) (perBoxMFCase_convScaleSmall_nonneg M (ℓ * d) _))
      (Submission.BoseGases.convScale_nonneg ℓ _)
  · exact perBoxMFCase_chiSmallB_nonneg M ℓ d u y

theorem perBoxMFCase_nCountB_nonneg {M : ℕ} {ℓ d : ℝ} {u : EuclideanSpace ℝ (Fin 3)} {n : ℕ}
    (x : X n) : 0 ≤ nCountB M ℓ d u x := by
  simp only [nCountB]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

theorem perBoxMFCase_chiMass_nonneg (M : ℕ) (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ chiMass M ℓ d u := by
  simp only [chiMass]
  exact integral_nonneg fun x => sq_nonneg _

theorem perBoxFCase_psiWeight_nonneg {c μ t : ℝ} (hc : 0 ≤ c) (hμ : 0 < μ) (ht : 0 ≤ t) :
    0 ≤ psiWeight c μ t := by
  rw [Work.SmallBoxSliding.psiWeight]
  refine div_nonneg (mul_nonneg hc (sq_nonneg _)) ?_
  have : 0 ≤ t * μ⁻¹ := mul_nonneg ht (le_of_lt (inv_pos.mpr hμ))
  linarith

/-- **Sharpened fibre bound for the localised one-body kernel.**

With `X(x) := chiSupAbs · chiSmall M ((ℓd)⁻¹•x − u)` (the `ℓd`-scale factor of the
two-factor cutoff, times `chiSupAbs`), for `R₀ ≤ ℓd/16` and `R₀ ≤ ℓ·chiR0`,

    |∫_y w_{1,B(u)}(x,y) dy| ≤ K · (a v) · X(x)

with `K = 16π·chiSupAbs²·chiSmallDecay M / smallConvLower M` independent of `u`, `x`,
`ℓ`, `d`.  (The corpus's `exists_fibre_wSmall1Pair_le_T` carries the extra factor
`∫χ_{B(u)}`, unbounded in the dilute regime; the loss is avoided here by bounding the
second cutoff factor at the `y`-evaluation point by the constant
`chiSupAbs·chiSmallDecay M` and integrating only `g₀`.) -/
theorem wSmall1Pair_fibre_le_chiM {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u x : EuclideanSpace ℝ (Fin 3)) :
    |∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u x y| ≤
      (16 * π * Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay M / Work.SmallBoxSliding.smallConvLower M)
        * (_root_.BoseGases.a v)
        * (Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) := by
  have hSpos : 0 < Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.smallConvLower_pos M
  have hDnn : 0 ≤ Submission.BoseGases.chiSmallDecay M :=
    Submission.BoseGases.chiSmallDecay_nonneg M
  have hAnn : 0 ≤ Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u) :=
    mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
      (Submission.BoseGases.chiSmall_nonneg M _)
  -- the pointwise kernel bound of the corpus
  have hpt : ∀ y : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.wSmall1Pair h M ℓ d u x y| ≤
        (Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u))
          * (2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
              * |Submission.BoseGases.g0 v h (x - y)|)
          / Work.SmallBoxSliding.smallConvLower M :=
    fun y => Work.SmallBoxSliding.abs_wSmall1Pair_le (v := v) (R0 := R0) hv_supp hR0 h
      hM hℓ hd hR hRχ u x y
  -- the `y`-integral of `|g₀(x − ·)|`
  have hg0int : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR0 hv_supp h
  have hshift_int : MeasureTheory.Integrable
      (fun y : EuclideanSpace ℝ (Fin 3) => |Submission.BoseGases.g0 v h (x - y)|) := by
    have h' := hg0int.abs.comp_sub_left x
    simpa [Function.comp_def] using h'
  have hshift_nonneg : 0 ≤ᵐ[MeasureTheory.volume]
      (fun y : EuclideanSpace ℝ (Fin 3) => |Submission.BoseGases.g0 v h (x - y)|) :=
    Filter.Eventually.of_forall (fun y => abs_nonneg _)
  have hshift_eq : (∫ y in Submission.BoseGases.acube ℓ,
        |Submission.BoseGases.g0 v h (x - y)|)
      ≤ ∫ y : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.g0 v h (x - y)| :=
    setIntegral_le_integral hshift_int hshift_nonneg
  have hshift_val : (∫ y : EuclideanSpace ℝ (Fin 3),
        |Submission.BoseGases.g0 v h (x - y)|) = 8 * π * (_root_.BoseGases.a v) := by
    have hsub := Submission.BoseGases.integral_comp_sub_left
      (fun z : EuclideanSpace ℝ (Fin 3) => |Submission.BoseGases.g0 v h z|) x
    have habs : (∫ z : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.g0 v h z|)
        = ∫ z : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.g0 v h z := by
      refine integral_congr_ae ?_
      filter_upwards [Submission.BoseGases.g0_nonneg_ae (v := v) (R := R0) hR0 hv hvrad
        hv_supp h] with z hz
      exact abs_of_nonneg hz
    rw [hsub, habs, Submission.BoseGases.g0_integral hR0 hv_supp h]
  -- assemble
  set A : ℝ := Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u) with hA
  set B : ℝ := 2 * (Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M with hB
  have hBnn : 0 ≤ B := by
    rw [hB]
    exact div_nonneg (mul_nonneg (by norm_num)
      (mul_nonneg Submission.BoseGases.chiSupAbs_nonneg hDnn)) (le_of_lt hSpos)
  have hdom_int : MeasureTheory.IntegrableOn
      (fun y : EuclideanSpace ℝ (Fin 3) => A * (B * |Submission.BoseGases.g0 v h (x - y)|))
      (Submission.BoseGases.acube ℓ) := by
    have h' := (hshift_int.const_mul B).const_mul A
    simpa only [mul_assoc] using h'.integrableOn
  have h1 : |∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u x y|
      ≤ ∫ y in Submission.BoseGases.acube ℓ,
          A * (B * |Submission.BoseGases.g0 v h (x - y)|) := by
    have hnorm := norm_integral_le_integral_norm
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
        (Submission.BoseGases.acube ℓ))
      (f := fun y : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wSmall1Pair h M ℓ d u x y)
    rw [Real.norm_eq_abs] at hnorm
    refine le_trans hnorm ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y => abs_nonneg _))
      hdom_int ?_
    filter_upwards with y
    have hy := hpt y
    have hrew : A * (B * |Submission.BoseGases.g0 v h (x - y)|)
        = (Submission.BoseGases.chiSupAbs
              * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u))
            * (2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
                * |Submission.BoseGases.g0 v h (x - y)|)
            / Work.SmallBoxSliding.smallConvLower M := by
      rw [hA, hB]; ring
    rw [hrew]
    exact hy
  have h2 : (∫ y in Submission.BoseGases.acube ℓ,
        A * (B * |Submission.BoseGases.g0 v h (x - y)|))
      ≤ A * B * (8 * π * (_root_.BoseGases.a v)) := by
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    have hstep := mul_le_mul_of_nonneg_left (le_trans hshift_eq hshift_val.le)
      (mul_nonneg hAnn hBnn)
    simpa only [mul_assoc] using hstep
  have h3 : A * B * (8 * π * (_root_.BoseGases.a v))
      = (16 * π * Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay M / Work.SmallBoxSliding.smallConvLower M)
        * (_root_.BoseGases.a v) * A := by
    rw [hA, hB]; ring
  calc |∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u x y|
      ≤ ∫ y in Submission.BoseGases.acube ℓ,
          A * (B * |Submission.BoseGases.g0 v h (x - y)|) := h1
    _ ≤ A * B * (8 * π * (_root_.BoseGases.a v)) := h2
    _ = (16 * π * Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay M / Work.SmallBoxSliding.smallConvLower M)
        * (_root_.BoseGases.a v)
        * (Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) := h3

/-! ## The reduction of `PerBoxF` to the mean-field (density-square) form

**This is the whole reduction.**  Write (at FS's parameters `ℓ = sideAt μ (a v)`,
`d = (paramsAt μ (a v)).d`, `M = (paramsAt μ (a v)).M`, `u` in the good set)

* `W := w1MassB h M ℓ d u` (FS's per-box mass `∬w_{1,B(u)}`),
* `t(x) := nCountB M ℓ d u x / chiMass M ℓ d u` (the smooth local density, FS's
  `n(u)/|B(u)|`),
* `sbWord = sbKin + sbPot` (FS's `𝓗_{B(u)}(μ)` at the localised kernels).

Then, since `F(t) ≤ (t−μ)²` for `t ≥ 0` (`psiWeight_le_sq_sub`) and `W ≥ 0`
(`w1MassB_nonneg`), the `F`-weighted left-hand side of `PerBoxF` at `c₁ = 1/4` is
dominated by the **mean-field square** left-hand side of `PerBoxMF` below.  Hence
`PerBoxF` follows from `PerBoxMF`, which is the clean statement of the per-box
content FS's `thm:smallbox` has at the sliding box: *the localised word dominates
the mean-field square of the smooth local density minus the `½μ²` background, up
to the free error bracket*.  Proving `PerBoxMF` is the analytic content of
`perBoxFWeight_holds` (see `PERBOXF_ANALYSIS.md` §6 for the regime structure:
mean field at high density, the `ε_T`-gap at localised states, `≤ 0` at low
density). -/

/-- The `C`-bracket of `PerBoxF` — the per-box error term, isolated so that the
reduction below can be stated as one algebraic step. -/
noncomputable def perBoxErr (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ R : ℝ) (n : ℕ)
    (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
      + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
    * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u *
    normB v μ n (Φ : X n → ℝ)
  + μ * (a v) * normB v μ n (Φ : X n → ℝ)

/-- **`F(t) ≤ (t−μ)²`** for `t ≥ 0` (FS's weight is the square times
`μ/(t+μ) ≤ 1`). -/
lemma psiWeight_le_sq_sub {μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) :
    Work.SmallBoxSliding.psiWeight 1 μ t ≤ (t - μ) ^ 2 := by
  rw [Work.SmallBoxSliding.psiWeight, one_mul]
  have hden : 0 < 1 + t * μ⁻¹ := by
    have : 0 ≤ t * μ⁻¹ := mul_nonneg ht (le_of_lt (inv_pos.mpr hμ))
    linarith
  rw [div_le_iff₀ hden]
  have h1 : (1 : ℝ) ≤ 1 + t * μ⁻¹ := by
    have : 0 ≤ t * μ⁻¹ := mul_nonneg ht (le_of_lt (inv_pos.mpr hμ))
    linarith
  nlinarith [sq_nonneg (t - μ), h1]

/-- **`F(t) ≤ μ² + μt`** — the *linear* comparison of FS's weight. It is sharp at
`t = μ` only up to the defect `μ²` (`F(μ) = 0` exactly), which is why the *crude*
linear route cannot close `PerBoxF` (SESSION-3 FINDING): at the flat state of local
density `ρ` the exact weight `F(ρ) = μ²(ρ−μ)²/(ρ+μ)` must be used jointly with the
AM-GM identity `½(∬w₂)ρ² + ½μ²∬w₁ ≥ μρ∬w₁` (module docstring, SESSION FINDING). -/
lemma psiWeight_le_add_mul {μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) :
    Work.SmallBoxSliding.psiWeight 1 μ t ≤ μ ^ 2 + μ * t := by
  have hden : 0 < 1 + t * μ⁻¹ := by
    have : 0 ≤ t * μ⁻¹ := mul_nonneg ht (le_of_lt (inv_pos.mpr hμ))
    linarith
  rw [Work.SmallBoxSliding.psiWeight, one_mul, div_le_iff₀ hden]
  have hμ0 : μ ≠ 0 := ne_of_gt hμ
  have hkey : (μ ^ 2 + μ * t) * (1 + t * μ⁻¹) = (t + μ) ^ 2 := by
    field_simp
    ring
  rw [hkey]
  nlinarith [mul_nonneg hμ.le ht]

/-- **The exact value of FS's weight at a fixed density *ratio*** — the arithmetic step of every
per-box ledger, and the one that has been got wrong more than once in the chapter:
for `μ > 0` and `λ ≥ 0`,

    F(λμ) = μ²(λ−1)²/(λ+1) .

Consequences, recorded here so that they are machine-checked: `F` is **quadratic** in `μ` at
*every fixed* ratio `λ`, with `F(0) = μ²` and `F(μ) = 0`; hence the `F`-debit of `PerBoxF` at a
state of (smooth) density `λμ` is `c₁·M₁·m_k·μ²(λ−1)²/(λ+1)`, i.e. of the **same `μ²` order as the
background** `½μ²M₁m_k` and as the pair payment `½λ²μ²M₂m_k` — *not* of order `μ`.  In particular a
ledger that divides the debit by `M₁m_kμ²` must leave a *constant* `c₁(λ−1)²/(λ+1) + λ − ½` on the
left, and that constant is exactly what the pair term covers for `λ` in the mechanically relevant
range (`λ = 2`: `c₁/3 + 3/2 ≤ 2(1+ε)`, `ε = M₂/M₁ − 1 ≳ a v/(2R)`, `mfM2M1_key`).
See `FINDING_perBoxF_refutations_unsound.md` §1.1: dropping this `μ²` is what made the
correlation-hole family look like a refutation of the target. -/
lemma psiWeight_one_at_density_mul {μ r : ℝ} (hμ : 0 < μ) (hr : 0 ≤ r) :
    Work.SmallBoxSliding.psiWeight 1 μ (r * μ) = μ ^ 2 * (r - 1) ^ 2 / (r + 1) := by
  rw [Work.SmallBoxSliding.psiWeight, one_mul]
  have hμne : μ ≠ 0 := ne_of_gt hμ
  have hden : 1 + r * μ * μ⁻¹ = r + 1 := by
    rw [mul_assoc, mul_inv_cancel₀ hμne, mul_one, add_comm]
  have hnum : (r * μ - μ) ^ 2 = μ ^ 2 * (r - 1) ^ 2 := by ring
  rw [hnum, hden]

lemma nCountB_nonneg {M : ℕ} {ℓ d : ℝ} {u : EuclideanSpace ℝ (Fin 3)} {n : ℕ}
    (x : X n) : 0 ≤ nCountB M ℓ d u x := by
  simp only [nCountB]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

lemma chiMass_nonneg (M : ℕ) (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ chiMass M ℓ d u := by
  simp only [chiMass]
  exact integral_nonneg fun x => sq_nonneg _

/-- **The mean-field form of FS `thm:smallbox` at the sliding box** — `PerBoxF` with
`F(t)` replaced by the full square `(t−μ)²` and with `c₁ := 1/4`.

**WARNING (proved): this statement is FALSE** — see
`Submission/Work/BoseFixB1/FINDING_perBoxMF_square_false.md`: at a high local density
`t ≫ μ` the square is quadratic in the particle number while every payment available in
`sbWord` is at most linear (take the `n`-fold product of a narrow bump with a shell
potential `v`, `v(0) = 0`, so that the pair term vanishes identically).  The implication
`PerBoxMF ⟹ PerBoxF` (`perBoxFWeight_of_perBoxMF` below) is valid but *vacuous*; `PerBoxF`
must be proved with FS's own weight `F(t) = μ(t−μ)²/(t+μ)` (module docstring, SESSION
FINDING).  The definition is kept because it is the natural `∀μ`-form of the
`psiWeight_le_sq_sub` comparison and because the refutation is stated against it. -/
def PerBoxMF (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : EuclideanSpace ℝ (Fin 3)),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
        (1 / 4) * (w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u *
            (∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 *
              ((nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x /
                  chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) - μ) ^ 2))
          - (1 / 2) * μ ^ 2 * w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
              (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ)
          - C * perBoxErr v μ R n Φ u
        ≤ sbWord h μ u (Φ : X n → ℝ)

/-- **The reduction, at one admissible point**: `PerBoxMF` at `μ` implies
`PerBoxF v h R (1/4) C μ n Φ u`. -/
theorem perBoxF_of_perBoxMF_at {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {μ ε₀ C : ℝ} (hAdm : Work.BoseBoxFix.Adm v ε₀ μ) {n : ℕ}
    (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
    {u : EuclideanSpace ℝ (Fin 3)}
    (hMF : (1 / 4) * (w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u *
            (∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 *
              ((nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x /
                  chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) - μ) ^ 2))
          - (1 / 2) * μ ^ 2 * w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
              (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ)
          - C * perBoxErr v μ R n Φ u
        ≤ sbWord h μ u (Φ : X n → ℝ)) :
    PerBoxF v h R (1 / 4) C μ n Φ u := by
  have hℓ : 0 < sideAt μ (a v) := adm_ell_pos hAdm
  have hd : 0 < (paramsAt μ (a v)).d := adm_d_pos hAdm
  have hμ : 0 < μ := adm_mu_pos hAdm
  have hM1 : 1 ≤ (paramsAt μ (a v)).M := by
    rw [M_eq_mValue]; norm_num [Work.BoseBox.mValue]
  have hW : 0 ≤ w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u :=
    w1MassB_nonneg h hv hvrad hR hv_supp hℓ hd u
  -- continuity of the local density
  have hcB : Continuous (Submission.BoseGases.chiSmallB (paramsAt μ (a v)).M
      (sideAt μ (a v)) (paramsAt μ (a v)).d u) := by
    unfold Submission.BoseGases.chiSmallB
    exact (Submission.BoseGases.chiScale_continuous (sideAt μ (a v))).mul
      ((chiSmall_continuous hM1).comp (by fun_prop))
  have hcont_n : Continuous fun x : X n =>
      nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x := by
    simp only [nCountB]
    exact continuous_finsetSum _ fun i _ =>
      (hcB.comp (continuous_apply i)).pow 2
  have hcont_g : Continuous fun x : X n =>
      (Φ x) ^ 2 * ((nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x /
          chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) - μ) ^ 2 := by
    have h1 : Continuous (fun x : X n => (Φ x) ^ 2) := (Φ.contDiff.continuous).pow 2
    have hdiv : Continuous (fun x : X n =>
        nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x /
          chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) :=
      hcont_n.div_const _
    exact h1.mul ((hdiv.sub continuous_const).pow 2)
  have hK : IsCompact (abox n (sideAt μ (a v))) :=
    Work.UBBInputs9.B.abox_isCompact n (sideAt μ (a v))
  have hintg : MeasureTheory.IntegrableOn (fun x : X n =>
      (Φ x) ^ 2 * ((nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x /
          chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) - μ) ^ 2)
      (abox n (sideAt μ (a v))) :=
    ContinuousOn.integrableOn_compact hK hcont_g.continuousOn
  -- the pointwise domination of the `F`-weight by the square
  have hpt : (fun x : X n => (Φ x) ^ 2 * psiWeight 1 μ
        (nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x /
          chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u))
      ≤ (fun x : X n => (Φ x) ^ 2 *
          ((nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x /
            chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) - μ) ^ 2) := by
    intro x
    have ht0 : 0 ≤ nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x /
        chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u :=
      div_nonneg (nCountB_nonneg x) (chiMass_nonneg _ _ _ _)
    exact mul_le_mul_of_nonneg_left (psiWeight_le_sq_sub hμ ht0) (sq_nonneg _)
  have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (abox n (sideAt μ (a v)))]
      (fun x : X n => (Φ x) ^ 2 * psiWeight 1 μ
        (nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x /
          chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u)) :=
    Filter.Eventually.of_forall fun x => by
      refine mul_nonneg (sq_nonneg _) ?_
      rw [Work.SmallBoxSliding.psiWeight]
      refine div_nonneg (mul_nonneg zero_le_one (sq_nonneg _)) ?_
      have ht0 : 0 ≤ nCountB (paramsAt μ (a v)).M (sideAt μ (a v))
          (paramsAt μ (a v)).d u x / chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
          (paramsAt μ (a v)).d u :=
        div_nonneg (nCountB_nonneg x) (chiMass_nonneg _ _ _ _)
      have : 0 ≤ (nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x /
          chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) * μ⁻¹ :=
        mul_nonneg ht0 (le_of_lt (inv_pos.mpr hμ))
      linarith
  have hint : (∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 * psiWeight 1 μ
        (nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x /
          chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u))
      ≤ ∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 *
          ((nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x /
            chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) - μ) ^ 2 :=
    MeasureTheory.integral_mono_of_nonneg hnn hintg (Filter.Eventually.of_forall hpt)
  rw [PerBoxF]
  have hW14 : (0 : ℝ) ≤ (1 / 4) * w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
      (paramsAt μ (a v)).d u := mul_nonneg (by norm_num) hW
  have hstep : (1 / 4) * (w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u *
        (∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 * psiWeight 1 μ
          (nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x /
            chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u)))
      ≤ (1 / 4) * (w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u *
        (∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 *
          ((nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x /
            chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) - μ) ^ 2)) := by
    have h' := mul_le_mul_of_nonneg_left hint hW14
    linarith [h']
  simp only [perBoxErr] at hMF
  linarith [hstep, hMF]

/-- **The reduction, in the target's `∃`-shape**: `PerBoxMF` implies the
`perBoxFWeight_holds` conclusion (with `c₁ := 1/4`).  Valid but **vacuous**: the
hypothesis `PerBoxMF` is FALSE (see the module docstring and
`FINDING_perBoxMF_square_false.md`). -/
theorem perBoxFWeight_of_perBoxMF {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hMF : PerBoxMF v h R) :
    ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
          PerBoxF v h R c₁ C μ n Φ u := by
  obtain ⟨ε₀, C, hε, hC, hMF'⟩ := hMF
  exact ⟨ε₀, 1/4, C, hε, by norm_num, hC,
    fun μ hAdm n Φ u hu => perBoxF_of_perBoxMF_at h hv hvrad hR hv_supp hAdm Φ
      (hMF' μ hAdm n Φ u hu)⟩

/-! ## The `χ_B`-linear fibre bound (the payer of the chemical-potential term) -/

/-- **The `χ_B`-linear form of the fibre bound.**  Unlike `wSmall1Pair_fibre_le_chiM`
(which carries the `χ_M` factor, hence does *not* decay where the `ℓ`-scale factor
`chiScale ℓ` is small) this bound keeps the full cutoff value
`chiSmallB M ℓ d u x = chiScale ℓ x · chiSmall M ((ℓd)⁻¹•x − u)` at the evaluation point:

    |∫_y w_{1,B(u)}(x,y) dy| ≤ K · (a v) · chiSmallB M ℓ d u x ,

with `K` independent of `u, x, ℓ, d`.  This is the form the *small-local-density*
branch of `PerBoxMF` needs (there the fibre cost `μ·Σᵢ∫Φ²fibre(xᵢ)` must be bounded
by `μ·K(a v)·Σᵢχ_B(xᵢ)`), and it is strictly stronger than the `χ_M`-form because
`chiScale ℓ x ≤ chiSupAbs`.  Proof: the second cutoff factor is bounded by its sup and
the whole mass `∫g₀ = 8π(a v)` is paid inside the constant. -/
theorem wSmall1Pair_fibre_le_chiB {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u x : EuclideanSpace ℝ (Fin 3)) :
    |∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u x y| ≤
      (16 * π * Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay M / Work.SmallBoxSliding.smallConvLower M)
        * (_root_.BoseGases.a v)
        * (Submission.BoseGases.chiScale ℓ x
            * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) := by
  have hcpos : 0 < ℓ * d := mul_pos hℓ hd
  have hSpos : 0 < Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.smallConvLower_pos M
  have hDnn : 0 ≤ Submission.BoseGases.chiSmallDecay M :=
    Submission.BoseGases.chiSmallDecay_nonneg M
  have hsup_c : 0 ≤ Submission.BoseGases.chiSupAbs := Submission.BoseGases.chiSupAbs_nonneg
  have hsupp : ∀ z : EuclideanSpace ℝ (Fin 3),
      R0 ≤ ‖z‖ → Submission.BoseGases.g0 v h z = 0 :=
    fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h
  -- the middle factor: the renormalised kernel over the `ℓ`-denominator
  have hmid : ∀ y : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) (x - y)
          / Submission.BoseGases.convScale ℓ (x - y)| ≤
        2 * (|Submission.BoseGases.g0 v h (x - y)| / Work.SmallBoxSliding.smallConvLower M) := by
    intro y
    have hD2 : |Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h)
        (x - y)| ≤ |Submission.BoseGases.g0 v h (x - y)| /
          Work.SmallBoxSliding.smallConvLower M :=
      abs_wSmallScaled_le (M := M) (c := ℓ * d) (R := R0) hM hcpos
        hsupp hR (x - y)
    by_cases hnorm : ‖x - y‖ ≤ R0
    · have hinv : |(Submission.BoseGases.convScale ℓ (x - y))⁻¹| ≤ 2 :=
        Submission.BoseGases.abs_inv_convScale_le_two (ℓ := ℓ) (R := R0) hℓ hRχ hnorm
      rw [div_eq_mul_inv, abs_mul]
      calc |Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) (x - y)|
            * |(Submission.BoseGases.convScale ℓ (x - y))⁻¹|
          ≤ (|Submission.BoseGases.g0 v h (x - y)| /
              Work.SmallBoxSliding.smallConvLower M) * 2 :=
            mul_le_mul hD2 hinv (abs_nonneg _) (by positivity)
        _ = 2 * (|Submission.BoseGases.g0 v h (x - y)| /
              Work.SmallBoxSliding.smallConvLower M) := by ring
    · have hz0 : Submission.BoseGases.g0 v h (x - y) = 0 :=
        hsupp _ (le_of_lt (lt_of_not_ge hnorm))
      rw [hz0]
      simp [Submission.BoseGases.wSmallScaled, hz0]
  -- the second cutoff factor, bounded by its sup
  have hyB : ∀ y : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.chiSmallB M ℓ d u y| ≤
        Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M := by
    intro y
    refine le_trans (Work.SmallBoxSliding.abs_chiSmallB_le (M := M) (ℓ := ℓ) (d := d) hM u y) ?_
    have hb2 : Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u)
        ≤ Submission.BoseGases.chiSmallDecay M := by
      have hb' := Submission.BoseGases.chiSmall_decay_coord_le_decay hM ((ℓ * d)⁻¹ • y - u)
      rwa [abs_of_nonneg (Submission.BoseGases.chiSmall_nonneg M _)] at hb'
    exact mul_le_mul_of_nonneg_left hb2 hsup_c
  -- the pointwise kernel bound
  have hpt : ∀ y : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.wSmall1Pair h M ℓ d u x y| ≤
        (Submission.BoseGases.chiScale ℓ x
            * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u))
          * (2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
              * |Submission.BoseGases.g0 v h (x - y)|)
          / Work.SmallBoxSliding.smallConvLower M := by
    intro y
    have hxval : |Submission.BoseGases.chiSmallB M ℓ d u x| =
        Submission.BoseGases.chiScale ℓ x
          * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u) := by
      rw [Submission.BoseGases.chiSmallB,
        abs_of_nonneg (mul_nonneg (Submission.BoseGases.chiScale_nonneg ℓ x)
          (Submission.BoseGases.chiSmall_nonneg M _))]
    rw [Submission.BoseGases.wSmall1Pair, Submission.BoseGases.wSmallPair, abs_mul, abs_mul, hxval]
    have hmid' := hmid y
    have hyB' := hyB y
    have h1 : Submission.BoseGases.chiScale ℓ x
          * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)
          * |Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) (x - y)
              / Submission.BoseGases.convScale ℓ (x - y)|
          * |Submission.BoseGases.chiSmallB M ℓ d u y|
        ≤ (Submission.BoseGases.chiScale ℓ x
            * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u))
          * (2 * (|Submission.BoseGases.g0 v h (x - y)| /
              Work.SmallBoxSliding.smallConvLower M))
          * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left hmid' ?_) hyB'
        (abs_nonneg _) ?_
      · exact mul_nonneg (Submission.BoseGases.chiScale_nonneg ℓ x)
          (Submission.BoseGases.chiSmall_nonneg M _)
      · exact mul_nonneg (mul_nonneg (Submission.BoseGases.chiScale_nonneg ℓ x)
            (Submission.BoseGases.chiSmall_nonneg M _))
          (mul_nonneg (by norm_num) (div_nonneg (abs_nonneg _) (le_of_lt hSpos)))
    refine le_trans h1 (le_of_eq ?_)
    ring
  -- integrate
  have hg0int : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR0 hv_supp h
  have hshift_int : MeasureTheory.Integrable
      (fun y : EuclideanSpace ℝ (Fin 3) => |Submission.BoseGases.g0 v h (x - y)|) := by
    have h' := hg0int.abs.comp_sub_left x
    simpa [Function.comp_def] using h'
  have hshift_nonneg : 0 ≤ᵐ[MeasureTheory.volume]
      (fun y : EuclideanSpace ℝ (Fin 3) => |Submission.BoseGases.g0 v h (x - y)|) :=
    Filter.Eventually.of_forall (fun y => abs_nonneg _)
  have hshift_eq : (∫ y in Submission.BoseGases.acube ℓ,
        |Submission.BoseGases.g0 v h (x - y)|)
      ≤ ∫ y : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.g0 v h (x - y)| :=
    setIntegral_le_integral hshift_int hshift_nonneg
  have hshift_val : (∫ y : EuclideanSpace ℝ (Fin 3),
        |Submission.BoseGases.g0 v h (x - y)|) = 8 * π * (_root_.BoseGases.a v) := by
    have hsub := Submission.BoseGases.integral_comp_sub_left
      (fun z : EuclideanSpace ℝ (Fin 3) => |Submission.BoseGases.g0 v h z|) x
    have habs : (∫ z : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.g0 v h z|)
        = ∫ z : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.g0 v h z := by
      refine integral_congr_ae ?_
      filter_upwards [Submission.BoseGases.g0_nonneg_ae (v := v) (R := R0) hR0 hv hvrad
        hv_supp h] with z hz
      exact abs_of_nonneg hz
    rw [hsub, habs, Submission.BoseGases.g0_integral hR0 hv_supp h]
  set A : ℝ := Submission.BoseGases.chiScale ℓ x
      * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u) with hA
  set B : ℝ := 2 * (Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M with hB
  have hAnn : 0 ≤ A := by
    rw [hA]
    exact mul_nonneg (Submission.BoseGases.chiScale_nonneg ℓ x)
      (Submission.BoseGases.chiSmall_nonneg M _)
  have hBnn : 0 ≤ B := by
    rw [hB]
    exact div_nonneg (mul_nonneg (by norm_num)
      (mul_nonneg hsup_c hDnn)) (le_of_lt hSpos)
  have hdom_int : MeasureTheory.IntegrableOn
      (fun y : EuclideanSpace ℝ (Fin 3) => A * (B * |Submission.BoseGases.g0 v h (x - y)|))
      (Submission.BoseGases.acube ℓ) := by
    have h' := (hshift_int.const_mul B).const_mul A
    simpa only [mul_assoc] using h'.integrableOn
  have h1 : |∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u x y|
      ≤ ∫ y in Submission.BoseGases.acube ℓ,
          A * (B * |Submission.BoseGases.g0 v h (x - y)|) := by
    have hnorm := norm_integral_le_integral_norm
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
        (Submission.BoseGases.acube ℓ))
      (f := fun y : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wSmall1Pair h M ℓ d u x y)
    rw [Real.norm_eq_abs] at hnorm
    refine le_trans hnorm ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y => abs_nonneg _))
      hdom_int ?_
    filter_upwards with y
    have hy := hpt y
    have hrew : A * (B * |Submission.BoseGases.g0 v h (x - y)|)
        = (Submission.BoseGases.chiScale ℓ x
              * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u))
            * (2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
                * |Submission.BoseGases.g0 v h (x - y)|)
            / Work.SmallBoxSliding.smallConvLower M := by
      rw [hA, hB]; ring
    rw [hrew]
    exact hy
  have h2 : (∫ y in Submission.BoseGases.acube ℓ,
        A * (B * |Submission.BoseGases.g0 v h (x - y)|))
      ≤ A * B * (8 * π * (_root_.BoseGases.a v)) := by
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    have hstep := mul_le_mul_of_nonneg_left (le_trans hshift_eq hshift_val.le)
      (mul_nonneg hAnn hBnn)
    simpa only [mul_assoc] using hstep
  have h3 : A * B * (8 * π * (_root_.BoseGases.a v))
      = (16 * π * Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay M / Work.SmallBoxSliding.smallConvLower M)
        * (_root_.BoseGases.a v) * A := by
    rw [hA, hB]; ring
  calc |∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u x y|
      ≤ ∫ y in Submission.BoseGases.acube ℓ,
          A * (B * |Submission.BoseGases.g0 v h (x - y)|) := h1
    _ ≤ A * B * (8 * π * (_root_.BoseGases.a v)) := h2
    _ = (16 * π * Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay M / Work.SmallBoxSliding.smallConvLower M)
        * (_root_.BoseGases.a v)
        * (Submission.BoseGases.chiScale ℓ x
            * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) := h3

/-! ## Elementary facts about the localised objects

All proved here, no `sorry`; they are the parts of `PerBoxF` that need no analysis. -/

/-- **`0 ≤ sbKin`** — FS `eq:appTB`'s word is nonnegative (`0 ≤ ε_T`): both halves are
"nonnegative coefficient × integral of a square" (`Work.UBBInputs9.A.tBwordBInd_nonneg`). -/
theorem sbKin_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} {M : ℕ}
    {u : EuclideanSpace ℝ (Fin 3)} {n : ℕ} (Φ : X n → ℝ)
    (hℓ : 0 < sideAt μ (a v)) (hε : 0 ≤ (paramsAt μ (a v)).eT) :
    0 ≤ sbKin (v := v) μ M u Φ := by
  rw [sbKin]
  exact Work.UBBInputs9.A.tBwordBInd_nonneg hℓ hε u Φ

/-- **The localised two-body kernel is nonnegative** when the numerator is nonnegative at the
evaluated pair (both cutoff factors and both renormalisation denominators are nonnegative). -/
theorem wSmallPair_nonneg_of {M : ℕ} {ℓ d : ℝ} {u x y : EuclideanSpace ℝ (Fin 3)}
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : 0 ≤ f (x - y)) :
    0 ≤ Submission.BoseGases.wSmallPair M ℓ d u f x y := by
  simp only [Submission.BoseGases.wSmallPair, Submission.BoseGases.wSmallScaled]
  exact mul_nonneg
    (mul_nonneg (Work.SmallBoxSliding.chiSmallB_nonneg M ℓ d u x)
      (div_nonneg
        (div_nonneg hf (Work.SmallBoxSliding.convScaleSmall_nonneg M (ℓ * d) (x - y)))
        (Submission.BoseGases.convScale_nonneg ℓ (x - y))))
    (Work.SmallBoxSliding.chiSmallB_nonneg M ℓ d u y)

/-- **The fibre of the localised one-body kernel is nonnegative** (`∫_y w_{1,B(u)}(x,y) dy ≥ 0`):
the integrand is a.e. nonnegative (`g₀ ≥ 0` a.e., all other factors nonnegative). -/
theorem wSmall1Pair_fibre_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ} (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} {ℓ d : ℝ} (u x : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ ∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u x y := by
  refine integral_nonneg_of_ae ?_
  refine MeasureTheory.ae_restrict_of_ae ?_
  filter_upwards [Work.SmallBoxSliding.ae_g0_comp_sub hv hvrad hv_supp hR0 h x] with y hy
  exact wSmallPair_nonneg_of hy

/-- The smooth box cutoff is dominated by `chiSupAbs · chiSmallDecay M`. -/
theorem chiSmallB_le_sup {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ}
    (u z : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.chiSmallB M ℓ d u z
      ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M := by
  have hb2 : Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • z - u)
      ≤ Submission.BoseGases.chiSmallDecay M := by
    have hb' := Submission.BoseGases.chiSmall_decay_coord_le_decay hM ((ℓ * d)⁻¹ • z - u)
    rwa [abs_of_nonneg (Submission.BoseGases.chiSmall_nonneg M _)] at hb'
  calc Submission.BoseGases.chiSmallB M ℓ d u z
      ≤ |Submission.BoseGases.chiSmallB M ℓ d u z| := le_abs_self _
    _ ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • z - u) :=
        Work.SmallBoxSliding.abs_chiSmallB_le (M := M) (ℓ := ℓ) (d := d) hM u z
    _ ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M :=
        mul_le_mul_of_nonneg_left hb2 Submission.BoseGases.chiSupAbs_nonneg

/-- **The smooth box count is dominated by the particle number times a universal constant**:
`nCountB M ℓ d u x ≤ n · (chiSupAbs · chiSmallDecay M)²`. -/
theorem nCountB_le_n {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (u : EuclideanSpace ℝ (Fin 3))
    {n : ℕ} (x : X n) :
    nCountB M ℓ d u x ≤ (n : ℝ)
      * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2 := by
  have hnn : 0 ≤ Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmallDecay M :=
    mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
      (Submission.BoseGases.chiSmallDecay_nonneg M)
  rw [nCountB]
  calc ∑ i : Fin n, (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2
      ≤ ∑ _i : Fin n, (Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay M) ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 : Submission.BoseGases.chiSmallB M ℓ d u (x i) ≤
            Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M :=
          chiSmallB_le_sup hM u (x i)
        have h2 : 0 ≤ Submission.BoseGases.chiSmallB M ℓ d u (x i) :=
          Work.SmallBoxSliding.chiSmallB_nonneg M ℓ d u (x i)
        nlinarith [h1, h2, hnn]
    _ = (n : ℝ) * (Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay M) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ## SESSION-3 FINDING — the crude `F(t) ≤ μ(t+μ)` route is a DEAD END (do not repeat)

A first attempt of this session reduced the target to the *linear* crux

    (1/2)·(∬w_{1,B}/χ_{B}²)·μ·∫Φ²·nCountB  ≤  sbWord + C·perBoxErr        (linear crux, FALSE)

via `F(t) ≤ μ(t+μ)` (`perBoxF_pieces.psiWeight_le_mu_mul_add`) and the exact cancellation of
`½μ²W‖Φ‖²` at `c₁ = 1/2`.  **That crux is false**, and the reduction is therefore vacuous
(recorded here so that no one re-derives it): FS's weight `F(t) = μ(t−μ)²/(t+μ)` *vanishes* at
`t = μ`, so the linear bound loses `2μ²` exactly where the statement is tight.  At the
box-constant state with local density `ρ = μ` one has `sbWord ≈ ½W(ρ−μ)²‖Φ‖² − ½μ²W‖Φ‖² =
−½μ²W‖Φ‖²` (no surplus beyond the square) while `C·perBoxErr = o(μ²W‖Φ‖²)` at FS's parameters
(`Γ → 0`, `μV → ∞`), so the linear crux fails by `≈ Wμ²‖Φ‖²` for *every* fixed `C`.  The same
conclusion is recorded independently in
`Submission/Work/BoseFixB1/FINDING_perBoxF_ledger.md` §1b ("the crude `F(t) ≤ μ(t+μ)` route
does not close").

**The usable shapes** (machine-checked) are the *square* ones: `psiWeight_le_sq_sub`
(`F(t) ≤ (t−μ)²`, above) and `perBoxF_F_weight_le` (`c₁F(t) ≤ ¼(t−μ)²` for `c₁ ≤ 1/4`,
`perBoxF_pieces`).  Accordingly the residual of this file is (as before this session)
**`PerBoxMF`** (the mean-field square form), whose implication `PerBoxMF ⟹ perBoxFWeight_holds`
is the proved `perBoxF_of_perBoxMF_at` / `perBoxFWeight_of_perBoxMF` above.  The chapter's
critical path is therefore unchanged: `PerBoxMF` (FS `thm:smallbox` at the localised box),
whose fleet-side pieces are

* the localised `potsplit` (`Work.BoseFixB1.potsplit_localised_of_memLp`, proved),
* the localised `Q₀`-value and its `A₀`-main lower form
  (`Work.BoseFixB1.q0word_localised_value`, `q0word_ge_a0_main`),
* the `P/Q` peels (`Work.BoseFixB1.WB.peel_aP_g`, `WB.pq_split_meas`, proved),
* the `ε_T`-gap payment (`perBoxF_pieces.sbKin_ge_mu_av_cnPlus`, proved),
* the *cross-word* (`q₁..q₄`) Cauchy–Schwarz/pairing control (open),
* the count ↔ density passages and the assembly (open).
-/



open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 0. Small facts about FS's parameters -/

/-- `ε_T > 0` at an admissible point (it is `(μ(a v)³)^{23/1292}`). -/
theorem adm_eT_pos {v : EuclideanSpace ℝ (Fin 3) → ℝ} {ε₀ μ : ℝ}
    (h : Work.BoseBoxFix.Adm v ε₀ μ) : 0 < (paramsAt μ (a v)).eT := by
  have ht : 0 < μ * (a v) ^ 3 := mul_pos (adm_mu_pos h) (pow_pos (adm_a_pos h) 3)
  rw [paramsAt_eq_fsParams, fsParams]
  exact Real.rpow_pos_of_pos ht _

/-- The uniform bound `χ_{B(u)} ≤ Cs := chiSupAbs·chiSmallDecay M`. -/
lemma chiSmallB_le_Cs {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (u x : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.chiSmallB M ℓ d u x
      ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M := by
  have hb2 : Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)
      ≤ Submission.BoseGases.chiSmallDecay M := by
    have hb' := Submission.BoseGases.chiSmall_decay_coord_le_decay hM ((ℓ * d)⁻¹ • x - u)
    rwa [abs_of_nonneg (Submission.BoseGases.chiSmall_nonneg M _)] at hb'
  calc Submission.BoseGases.chiSmallB M ℓ d u x
      ≤ |Submission.BoseGases.chiSmallB M ℓ d u x| := le_abs_self _
    _ ≤ Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u) :=
        Work.SmallBoxSliding.abs_chiSmallB_le (M := M) (ℓ := ℓ) (d := d) hM u x
    _ ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M :=
        mul_le_mul_of_nonneg_left hb2 Submission.BoseGases.chiSupAbs_nonneg

/-- **The smooth count is at most `n·Cs²`**, `Cs := chiSupAbs·chiSmallDecay M`. -/
theorem nCountB_le_n_mul {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (u : EuclideanSpace ℝ (Fin 3))
    {n : ℕ} (x : X n) :
    nCountB M ℓ d u x
      ≤ (n : ℝ) * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2 := by
  have hCs0 : 0 ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M :=
    mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
      (Submission.BoseGases.chiSmallDecay_nonneg M)
  rw [nCountB]
  calc ∑ i : Fin n, (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2
      ≤ ∑ _i : Fin n, (Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay M) ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 := chiSmallB_le_Cs (M := M) hM (ℓ := ℓ) (d := d) u (x i)
        have h2 := Work.SmallBoxSliding.chiSmallB_nonneg M ℓ d u (x i)
        nlinarith [h1, h2, hCs0]
    _ = (n : ℝ) * (Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay M) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The linear count is at most `n·Cs`**. -/
theorem sum_chiSmallB_le_n_mul {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ}
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} (x : X n) :
    (∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i))
      ≤ (n : ℝ) * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) := by
  calc ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i)
      ≤ ∑ _i : Fin n, Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M :=
        Finset.sum_le_sum fun i _ => chiSmallB_le_Cs (M := M) hM (ℓ := ℓ) (d := d) u (x i)
    _ = (n : ℝ) * (Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay M) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ## 1. The counting functions -/

/-- The `n₊` of the sliding box: the excited count of the small box `dlBox ℓ d u`. -/
noncomputable def nPlus (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} (Φ : X n → ℝ) : ℝ :=
  Work.UBBInputs8.cnPlusBoxInd (sideAt μ (a v)) (dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u)
    (boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u) Φ

/-- The smooth count integral `∫Φ²·nCountB`. -/
noncomputable def scountB (M : ℕ) (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ}
    (Φ : X n → ℝ) : ℝ :=
  ∫ x in abox n ℓ, (Φ x) ^ 2 * nCountB M ℓ d u x

/-- The linear cutoff-count integral `∫Φ²·Σᵢχ_{B(u)}(xᵢ)`. -/
noncomputable def chiSum (M : ℕ) (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ}
    (Φ : X n → ℝ) : ℝ :=
  ∫ x in abox n ℓ, (Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i)

/-- The fibre integral `∫Φ²·Σᵢ∫_y w_{1,B(u)}(xᵢ,y)dy`. -/
noncomputable def fibSum {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (M : ℕ)
    (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} (Φ : X n → ℝ) : ℝ :=
  ∫ x in abox n ℓ, (Φ x) ^ 2 *
    ∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
      Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y

/-- The pair integral `∫Φ²·½Σ_{i≠j}w_{B(u)}(xᵢ,xⱼ)`. -/
noncomputable def pairSum (v : EuclideanSpace ℝ (Fin 3) → ℝ) (M : ℕ) (ℓ d : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} (Φ : X n → ℝ) : ℝ :=
  ∫ x in abox n ℓ, (Φ x) ^ 2 *
    ((1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n,
      Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2))

/-- The linear cutoff count is monotone in the state's square. -/
theorem chiSum_le {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ}
    {Φ : X n → ℝ} (hΦc : Continuous Φ) :
    chiSum M ℓ d u Φ
      ≤ (n : ℝ) * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
          * ∫ x in abox n ℓ, (Φ x) ^ 2 := by
  rw [chiSum]
  have hCs0 : 0 ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M :=
    mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
      (Submission.BoseGases.chiSmallDecay_nonneg M)
  have hcB : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chiSmallB M ℓ d u z) := by
    unfold Submission.BoseGases.chiSmallB
    exact (Submission.BoseGases.chiScale_continuous ℓ).mul
      ((chiSmall_continuous hM).comp (by fun_prop))
  have hcont1 : Continuous (fun x : X n => (Φ x) ^ 2 *
      ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i)) := by
    refine (hΦc.pow 2).mul ?_
    refine continuous_finsetSum _ fun i _ => ?_
    exact hcB.comp (continuous_apply i)
  have hcont2 : Continuous (fun x : X n =>
      (n : ℝ) * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
        * (Φ x) ^ 2) :=
    continuous_const.mul (hΦc.pow 2)
  have hmono : (∫ x in abox n ℓ, (Φ x) ^ 2 *
        ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i))
      ≤ ∫ x in abox n ℓ, ((n : ℝ) * (Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay M)) * (Φ x) ^ 2 := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => ?_) ?_ ?_
    · exact mul_nonneg (sq_nonneg _)
        (Finset.sum_nonneg fun i _ => Work.SmallBoxSliding.chiSmallB_nonneg M ℓ d u (x i))
    · exact ContinuousOn.integrableOn_compact (Work.UBBInputs9.B.abox_isCompact n ℓ)
        hcont2.continuousOn
    · exact Filter.Eventually.of_forall fun x => by
        have h1 := sum_chiSmallB_le_n_mul (M := M) hM (ℓ := ℓ) (d := d) u x
        have h2 : 0 ≤ (Φ x) ^ 2 := sq_nonneg _
        have h3 : (Φ x) ^ 2 * (∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i))
            ≤ (Φ x) ^ 2 * ((n : ℝ)
                * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)) :=
          mul_le_mul_of_nonneg_left h1 h2
        calc (Φ x) ^ 2 * (∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i))
            ≤ (Φ x) ^ 2 * ((n : ℝ)
                * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)) := h3
          _ = ((n : ℝ) * (Submission.BoseGases.chiSupAbs
                * Submission.BoseGases.chiSmallDecay M)) * (Φ x) ^ 2 := by ring
  rw [integral_const_mul] at hmono
  calc (∫ x in abox n ℓ, (Φ x) ^ 2 *
        ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i))
      ≤ ((n : ℝ) * (Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmallDecay M)) * (∫ x in abox n ℓ, (Φ x) ^ 2) := hmono
    _ = (n : ℝ) * (Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmallDecay M) * (∫ x in abox n ℓ, (Φ x) ^ 2) := by ring

/-- **The smooth-count integral is at most `n·Cs²·∫Φ²`.** -/
theorem scountB_le {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ}
    {Φ : X n → ℝ} (hΦc : Continuous Φ) :
    scountB M ℓ d u Φ
      ≤ (n : ℝ) * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2
          * ∫ x in abox n ℓ, (Φ x) ^ 2 := by
  rw [scountB]
  have hcB : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chiSmallB M ℓ d u z) := by
    unfold Submission.BoseGases.chiSmallB
    exact (Submission.BoseGases.chiScale_continuous ℓ).mul
      ((chiSmall_continuous hM).comp (by fun_prop))
  have hcont_n : Continuous (fun x : X n => nCountB M ℓ d u x) := by
    simp only [nCountB]
    exact continuous_finsetSum _ fun i _ => (hcB.comp (continuous_apply i)).pow 2
  have hcont2 : Continuous (fun x : X n =>
      (n : ℝ) * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2
        * (Φ x) ^ 2) := continuous_const.mul (hΦc.pow 2)
  have hmono : (∫ x in abox n ℓ, (Φ x) ^ 2 * nCountB M ℓ d u x)
      ≤ ∫ x in abox n ℓ, ((n : ℝ) * (Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay M) ^ 2) * (Φ x) ^ 2 := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => ?_) ?_ ?_
    · exact mul_nonneg (sq_nonneg _) (perBoxMFCase_nCountB_nonneg x)
    · exact ContinuousOn.integrableOn_compact (Work.UBBInputs9.B.abox_isCompact n ℓ)
        hcont2.continuousOn
    · exact Filter.Eventually.of_forall fun x => by
        have h : (Φ x) ^ 2 * nCountB M ℓ d u x
            ≤ (Φ x) ^ 2 * ((n : ℝ) * (Submission.BoseGases.chiSupAbs
                * Submission.BoseGases.chiSmallDecay M) ^ 2) :=
          mul_le_mul_of_nonneg_left
            (nCountB_le_n_mul (M := M) (ℓ := ℓ) (d := d) hM u x) (sq_nonneg (Φ x))
        calc (Φ x) ^ 2 * nCountB M ℓ d u x
            ≤ (Φ x) ^ 2 * ((n : ℝ) * (Submission.BoseGases.chiSupAbs
                * Submission.BoseGases.chiSmallDecay M) ^ 2) := h
          _ = (n : ℝ) * (Submission.BoseGases.chiSupAbs
                * Submission.BoseGases.chiSmallDecay M) ^ 2 * (Φ x) ^ 2 := by ring
  rw [integral_const_mul] at hmono
  calc (∫ x in abox n ℓ, (Φ x) ^ 2 * nCountB M ℓ d u x)
      ≤ ((n : ℝ) * (Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmallDecay M) ^ 2) * (∫ x in abox n ℓ, (Φ x) ^ 2) := hmono
    _ = (n : ℝ) * (Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmallDecay M) ^ 2
          * (∫ x in abox n ℓ, (Φ x) ^ 2) := by ring

/-- **The pair integral is nonnegative** for `0 ≤ v` (the localised pair kernel is pointwise
nonnegative, and `Φ² ≥ 0`). -/
theorem pairSum_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hv : 0 ≤ v) {M : ℕ} {ℓ d : ℝ}
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} (Φ : X n → ℝ) :
    0 ≤ pairSum v M ℓ d u Φ := by
  rw [pairSum]
  refine integral_nonneg fun x => ?_
  refine mul_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) ?_)
  refine Finset.sum_nonneg fun p _ => ?_
  exact perBoxMFCase_wSmallPair_nonneg (f := v)
    (M := M) (ℓ := ℓ) (d := d) (u := u) (x := x p.1) (y := x p.2) hv

/-- **The fibre integral is dominated by the linear cutoff integral** (FS's
`wSmall1Pair_fibre_le_chiB` pointwise, integrated; the pointwise nonnegativity of the fibre is
`perBoxFWeight_holds.wSmall1Pair_fibre_nonneg`). -/
theorem fibSum_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R0 : ℝ}
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hR0 : 0 < R0)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} {Φ : X n → ℝ} (hΦc : Continuous Φ) :
    fibSum h M ℓ d u Φ
      ≤ (16 * π * Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
          / Work.SmallBoxSliding.smallConvLower M) * (_root_.BoseGases.a v)
          * chiSum M ℓ d u Φ := by
  rw [fibSum, chiSum]
  have hcB : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chiSmallB M ℓ d u z) := by
    unfold Submission.BoseGases.chiSmallB
    exact (Submission.BoseGases.chiScale_continuous ℓ).mul
      ((chiSmall_continuous hM).comp (by fun_prop))
  have hcont2 : Continuous (fun x : X n =>
      (16 * π * Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
          / Work.SmallBoxSliding.smallConvLower M) * (_root_.BoseGases.a v)
        * ((Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i))) :=
    continuous_const.mul ((hΦc.pow 2).mul (continuous_finsetSum _ fun i _ =>
      hcB.comp (continuous_apply i)))
  have hmono : (∫ x in abox n ℓ, (Φ x) ^ 2 *
        ∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y)
      ≤ ∫ x in abox n ℓ,
          ((16 * π * Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
              / Work.SmallBoxSliding.smallConvLower M) * (_root_.BoseGases.a v))
            * ((Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i)) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => ?_) ?_ ?_
    · refine mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => ?_)
      exact wSmall1Pair_fibre_nonneg (v := v) (M := M) hR0 hv hvrad hv_supp h u (x i)
    · exact ContinuousOn.integrableOn_compact (Work.UBBInputs9.B.abox_isCompact n ℓ)
        hcont2.continuousOn
    · exact Filter.Eventually.of_forall fun x => by
        have hKav0 : 0 ≤ 16 * π * Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmallDecay M / Work.SmallBoxSliding.smallConvLower M := by
          refine div_nonneg (mul_nonneg (mul_nonneg (by positivity)
            Submission.BoseGases.chiSupAbs_nonneg)
            (Submission.BoseGases.chiSmallDecay_nonneg M)) ?_
          exact le_of_lt (Work.SmallBoxSliding.smallConvLower_pos M)
        have hfib : ∀ i : Fin n,
            ∫ y in Submission.BoseGases.acube ℓ,
                Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y
              ≤ (16 * π * Submission.BoseGases.chiSupAbs
                  * Submission.BoseGases.chiSmallDecay M
                  / Work.SmallBoxSliding.smallConvLower M) * (_root_.BoseGases.a v)
                  * Submission.BoseGases.chiSmallB M ℓ d u (x i) := by
          intro i
          refine le_trans (le_abs_self _) ?_
          exact wSmall1Pair_fibre_le_chiB (v := v) (R0 := R0) hv_supp hR0 hv hvrad h hM hℓ hd
            hR hRχ u (x i)
        have hsum : (∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
              Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y)
            ≤ (16 * π * Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
                / Work.SmallBoxSliding.smallConvLower M) * (_root_.BoseGases.a v)
                * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i) := by
          calc (∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
                Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y)
              ≤ ∑ i : Fin n, (16 * π * Submission.BoseGases.chiSupAbs
                    * Submission.BoseGases.chiSmallDecay M
                    / Work.SmallBoxSliding.smallConvLower M) * (_root_.BoseGases.a v)
                    * Submission.BoseGases.chiSmallB M ℓ d u (x i) :=
                Finset.sum_le_sum fun i _ => hfib i
            _ = (16 * π * Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
                  / Work.SmallBoxSliding.smallConvLower M) * (_root_.BoseGases.a v)
                  * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i) := by
                rw [Finset.mul_sum]
        calc (Φ x) ^ 2 * (∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
              Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y)
            ≤ (Φ x) ^ 2 * ((16 * π * Submission.BoseGases.chiSupAbs
                * Submission.BoseGases.chiSmallDecay M
                / Work.SmallBoxSliding.smallConvLower M) * (_root_.BoseGases.a v)
                * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i)) :=
              mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
          _ = ((16 * π * Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
                / Work.SmallBoxSliding.smallConvLower M) * (_root_.BoseGases.a v))
                * ((Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i)) := by
              ring
  rw [integral_const_mul] at hmono
  calc (∫ x in abox n ℓ, (Φ x) ^ 2 *
        ∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y)
      ≤ ((16 * π * Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
            / Work.SmallBoxSliding.smallConvLower M) * (_root_.BoseGases.a v))
          * (∫ x in abox n ℓ, (Φ x) ^ 2
              * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i)) := hmono
    _ = (16 * π * Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
          / Work.SmallBoxSliding.smallConvLower M) * (_root_.BoseGases.a v)
          * (∫ x in abox n ℓ, (Φ x) ^ 2
              * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i)) := by ring

/-! ## 3. The gap payment (FS `eq:appgapestimate`) -/

/-- `n₊ ≥ 0` (it is a sum of integrals of squares). -/
theorem nPlus_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} (Φ : X n → ℝ) :
    0 ≤ nPlus v μ u Φ := by
  rw [nPlus, Work.UBBInputs8.cnPlusBoxInd]
  exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _

/-- **The excited count of the small box is paid by the kinetic gap** at the coefficient
`eT/(2(1+π⁻²)(dℓ)²) = tbGapCoeff (dℓ) eT`, i.e. FS `eq:appgapestimate` in the sharp form in which
the whole gap coefficient is available (the nonnegativity of the spectral half is
`Work.BoseFixB1.tBwordKinInd_nonneg`). -/
theorem nPlus_gap_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} {M : ℕ}
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} (Φ : X n → ℝ) :
    (paramsAt μ (a v)).eT
        / (2 * (1 + (Real.pi ^ 2)⁻¹)
          * ((paramsAt μ (a v)).d * sideAt μ (a v)) ^ 2)
      * nPlus v μ u Φ ≤ sbKin (v := v) μ M u Φ := by
  have hker := tBwordKinInd_nonneg (a := sideAt μ (a v))
    (A := dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u)
    (volA := boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u)
    (χ := chiB (sideAt μ (a v)) (paramsAt μ (a v)).d u) (c := sbCut μ (a v)) Φ
  have hgap := sbKin_ge_gapPart (v := v) (μ := μ) (M := M) (u := u) Φ hker
  rw [nPlus]
  refine le_trans ?_ hgap
  refine mul_le_mul_of_nonneg_right ?_ (nPlus_nonneg (v := v) μ u Φ)
  -- the coefficient identity: eT/(2(1+π⁻²)(dℓ)²) = tbGapCoeff (dℓ) eT
  rw [Work.SmallBoxTBWord.tbGapCoeff, Work.SmallBoxTBWord.tbPiFactor]
  field_simp
  linarith




open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The `F`-weight integral bound -/

/-- **The `F`-weight is dominated by the smooth count plus the state mass**:
`∫Φ²F(nCountB/χ) ≤ μ(χ⁻¹·scountB + μ‖Φ‖²)`, the integral of the pointwise bound
`F(t) ≤ μ(t+μ)` (`perBoxF_pieces.psiWeight_le_mu_mul_add`). -/
theorem psiWeight_integral_le_thick {μ : ℝ} (hμ : 0 < μ) {M : ℕ} (hM : 1 ≤ M)
    {ℓ d : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
        Work.SmallBoxSliding.psiWeight 1 μ (nCountB M ℓ d u x / chiMass M ℓ d u))
      ≤ μ * ((chiMass M ℓ d u)⁻¹ * scountB M ℓ d u Φ
          + μ * ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) := by
  have hchi0 : 0 ≤ chiMass M ℓ d u := chiMass_nonneg M ℓ d u
  have hcB : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chiSmallB M ℓ d u z) := by
    unfold Submission.BoseGases.chiSmallB
    exact (Submission.BoseGases.chiScale_continuous ℓ).mul
      ((chiSmall_continuous hM).comp (by fun_prop))
  have hcont_num : Continuous (fun x : Submission.BoseGases.X n => nCountB M ℓ d u x) := by
    simp only [nCountB]
    exact continuous_finsetSum _ fun i _ => (hcB.comp (continuous_apply i)).pow 2
  have hInt1 : IntegrableOn (fun x : Submission.BoseGases.X n =>
      μ * ((Φ x) ^ 2 * (nCountB M ℓ d u x / chiMass M ℓ d u)))
      (Submission.BoseGases.abox n ℓ) :=
    ContinuousOn.integrableOn_compact (Work.UBBInputs9.B.abox_isCompact n ℓ)
      ((continuous_const.mul ((hΦc.pow 2).mul (hcont_num.div_const _))).continuousOn)
  have hInt2 : IntegrableOn (fun x : Submission.BoseGases.X n => μ ^ 2 * (Φ x) ^ 2)
      (Submission.BoseGases.abox n ℓ) :=
    ContinuousOn.integrableOn_compact (Work.UBBInputs9.B.abox_isCompact n ℓ)
      ((continuous_const.mul (hΦc.pow 2)).continuousOn)
  have hmono : (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
        Work.SmallBoxSliding.psiWeight 1 μ (nCountB M ℓ d u x / chiMass M ℓ d u))
      ≤ ∫ x in Submission.BoseGases.abox n ℓ,
          (μ * ((Φ x) ^ 2 * (nCountB M ℓ d u x / chiMass M ℓ d u)) + μ ^ 2 * (Φ x) ^ 2) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => ?_) (hInt1.add hInt2)
      (Filter.Eventually.of_forall fun x => ?_)
    · exact mul_nonneg (sq_nonneg _)
        (perBoxFCase_psiWeight_nonneg (by norm_num) hμ
          (div_nonneg (nCountB_nonneg x) hchi0))
    · have ht : 0 ≤ nCountB M ℓ d u x / chiMass M ℓ d u :=
        div_nonneg (nCountB_nonneg x) hchi0
      have hb := psiWeight_le_mu_mul_add (μ := μ) hμ ht
      have h2 : 0 ≤ (Φ x) ^ 2 := sq_nonneg _
      calc (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ (nCountB M ℓ d u x / chiMass M ℓ d u)
          ≤ (Φ x) ^ 2 * (μ * (nCountB M ℓ d u x / chiMass M ℓ d u + μ)) :=
            mul_le_mul_of_nonneg_left hb h2
        _ = μ * ((Φ x) ^ 2 * (nCountB M ℓ d u x / chiMass M ℓ d u)) + μ ^ 2 * (Φ x) ^ 2 := by
            ring
  calc (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
        Work.SmallBoxSliding.psiWeight 1 μ (nCountB M ℓ d u x / chiMass M ℓ d u))
      ≤ ∫ x in Submission.BoseGases.abox n ℓ,
          (μ * ((Φ x) ^ 2 * (nCountB M ℓ d u x / chiMass M ℓ d u)) + μ ^ 2 * (Φ x) ^ 2) := hmono
    _ = μ * (∫ x in Submission.BoseGases.abox n ℓ,
            (Φ x) ^ 2 * (nCountB M ℓ d u x / chiMass M ℓ d u))
          + μ ^ 2 * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) := by
          rw [integral_add hInt1 hInt2, integral_const_mul, integral_const_mul]
    _ = μ * ((chiMass M ℓ d u)⁻¹ * scountB M ℓ d u Φ
          + μ * ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) := by
          rw [scountB]
          have : (∫ x in Submission.BoseGases.abox n ℓ,
              (Φ x) ^ 2 * (nCountB M ℓ d u x / chiMass M ℓ d u))
              = (chiMass M ℓ d u)⁻¹ * (∫ x in Submission.BoseGases.abox n ℓ,
                  (Φ x) ^ 2 * nCountB M ℓ d u x) := by
            rw [← integral_const_mul]
            exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
          rw [this]; ring

/-- **The `F`-weight is superlinear below `μ`**: for `μ/3 ≤ t` one has `F(t) ≤ μ t`
(the *linear* regime `t ≳ μ` of FS's weight, the regime in which the pair term pays). -/
theorem psiWeight_le_mu_mul {μ t : ℝ} (hμ : 0 < μ) (ht : μ / 3 ≤ t) :
    Work.SmallBoxSliding.psiWeight 1 μ t ≤ μ * t := by
  rw [Work.SmallBoxSliding.psiWeight, one_mul]
  have hden : 0 < 1 + t * μ⁻¹ := by
    have : 0 ≤ t * μ⁻¹ := mul_nonneg (le_trans (div_nonneg hμ.le (by norm_num)) ht)
      (le_of_lt (inv_pos.mpr hμ))
    linarith
  rw [div_le_iff₀ hden]
  have h1 : 1 + t * μ⁻¹ = (t + μ) / μ := by field_simp; ring
  rw [h1]
  have h2 : μ * t * ((t + μ) / μ) = t * (t + μ) := by field_simp
  rw [h2]
  nlinarith [ht, hμ, sq_nonneg (t - μ)]

/-- **The `F`-weight is bounded by `μ²` below `3μ`**: for `t ≤ 3μ` one has `F(t) ≤ μ²`
(the *quadratic* regime `t ≲ μ` of FS's weight, where the `½μ²W` background pays). -/
theorem psiWeight_le_mu_sq {μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) (ht3 : t ≤ 3 * μ) :
    Work.SmallBoxSliding.psiWeight 1 μ t ≤ μ ^ 2 := by
  rw [Work.SmallBoxSliding.psiWeight, one_mul]
  have hden : 0 < 1 + t * μ⁻¹ := by
    have : 0 ≤ t * μ⁻¹ := mul_nonneg ht (le_of_lt (inv_pos.mpr hμ))
    linarith
  rw [div_le_iff₀ hden]
  have h1 : 1 + t * μ⁻¹ = (t + μ) / μ := by field_simp; ring
  rw [h1]
  have h2 : μ ^ 2 * ((t + μ) / μ) = μ * (t + μ) := by field_simp
  rw [h2]
  nlinarith [ht, ht3, hμ, sq_nonneg (t - μ)]

/-! ## 2. The split of the localised potential word -/

/-- **Integrability of the fibre half of `sbPot`**: the state-level fibre sum
`∫Φ²·Σᵢ w1Fibre ℓ (wSmall1Pair h M ℓ d u) (xᵢ)` is integrable over the box, from the per-slot
integrability `Work.BoseFixB1S.wSmall1Pair_slot_integrableOn` and
`MeasureTheory.integrable_finsetSum`. -/
theorem integrableOn_fibSumIntegrand {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R0 : ℝ} (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) {M : ℕ} (hM : 1 ≤ M)
    {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hR : R0 ≤ ℓ * d / 16)
    (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0) (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
        ∑ i : Fin n, Submission.BoseGases.w1Fibre ℓ
          (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
      (Submission.BoseGases.abox n ℓ) := by
  have h1 : ∀ i : Fin n, IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
      (∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y))
      (Submission.BoseGases.abox n ℓ) := fun i =>
    Work.BoseFixB1S.wSmall1Pair_slot_integrableOn (v := v) (R0 := R0)
      hv_supp hR0 hv hvrad h hM hℓ hd hR hRχ u Φ hΦc i
  have hfun : (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
        ∑ i : Fin n, Submission.BoseGases.w1Fibre ℓ
          (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
      = fun x : Submission.BoseGases.X n => ∑ i : Fin n, (Φ x) ^ 2 *
          (∫ y in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y) := by
    funext x
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Submission.BoseGases.w1Fibre]
  rw [hfun]
  exact integrable_finsetSum _ fun i _ => h1 i

/-- **Integrability of the pair half of `sbPot`**: the state-level pair sum
`∫Φ²·(½Σ_{p∈pairSet n} wSmallPair M ℓ d u v (x_{p.1}) (x_{p.2}))` is integrable over the box,
from the per-pair integrability `Work.BoseFixB1S.wSmallPair_pair_integrableOn`. -/
theorem integrableOn_pairSumIntegrand {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv1 : MeasureTheory.MemLp v 1) {M : ℕ} (hM : 1 ≤ M)
    {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hR : R0 ≤ ℓ * d / 16)
    (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0) (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
        ((1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n,
          Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2)))
      (Submission.BoseGases.abox n ℓ) := by
  have h2 := Work.BoseFixB1S.wSmallPair_pair_integrableOn (v := v) (R0 := R0)
    hv_supp hR0 hv1 hM hℓ hd hR hRχ u Φ hΦc
  have hfun : (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
        ((1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n,
          Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2)))
      = fun x : Submission.BoseGases.X n => ∑ p ∈ Submission.BoseGases.pairSet n,
          ((1 / 2) * ((Φ x) ^ 2 *
            Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2))) := by
    funext x
    rw [← mul_assoc, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hfun]
  exact integrable_finsetSum _ fun p hp => (h2 p hp).const_mul (1 / 2)

/-- **The split of the localised potential word** (`qLHSwordB`) into its chemical-potential loss
and its pair term, at *arbitrary* box parameters `(M, ℓ, d)`:

    `qLHSwordB h M ℓ d μ u Φ = −μ·fibSum h M ℓ d u Φ + pairSum v M ℓ d u Φ`,

i.e. the single box integral of `qLHSword` is the sum of the two state-level integrals.  The passage
is `MeasureTheory.integral_add` + `integral_const_mul`, which needs the integrability of both halves
(`integrableOn_fibSumIntegrand`, `integrableOn_pairSumIntegrand`). -/
theorem qLHSwordB_split {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (M : ℕ) (hM : 1 ≤ M) {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hR : R0 ≤ ℓ * d / 16)
    (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0) (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    Work.SmallBoxSliding.qLHSwordB h M ℓ d μ u Φ
      = - (μ * Work.BoseFixB1.Up.fibSum h M ℓ d u Φ)
        + Work.BoseFixB1.Up.pairSum v M ℓ d u Φ := by
  have hfib := integrableOn_fibSumIntegrand (v := v) (h := h) (R0 := R0) hv_supp hR0 hv hvrad hM
    hℓ hd hR hRχ u hΦc
  have hpair := integrableOn_pairSumIntegrand (v := v) (R0 := R0) hv_supp hR0 hv1 hM hℓ hd hR hRχ
    u hΦc
  have h1 : (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
        (-μ * (∑ i : Fin n, Submission.BoseGases.w1Fibre ℓ
            (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
          + (1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n,
              Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2)))
      = fun x : Submission.BoseGases.X n =>
          (-μ * ((Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.w1Fibre ℓ
              (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
            + (Φ x) ^ 2 * ((1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n,
                Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2))) := by
    funext x; ring
  calc Work.SmallBoxSliding.qLHSwordB h M ℓ d μ u Φ
      = ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
          (-μ * (∑ i : Fin n, Submission.BoseGases.w1Fibre ℓ
              (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
            + (1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n,
                Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2)) := by
        rw [Work.SmallBoxSliding.qLHSwordB, Submission.BoseGases.qLHSword]
    _ = ∫ x in Submission.BoseGases.abox n ℓ,
          (-μ * ((Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.w1Fibre ℓ
              (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
            + (Φ x) ^ 2 * ((1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n,
                Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2))) :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => congrFun h1 x)
    _ = (∫ x in Submission.BoseGases.abox n ℓ,
          -μ * ((Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.w1Fibre ℓ
              (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)))
        + ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
            ((1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n,
                Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2)) :=
        integral_add (hfib.const_mul (-μ)) hpair
    _ = - (μ * Work.BoseFixB1.Up.fibSum h M ℓ d u Φ)
        + Work.BoseFixB1.Up.pairSum v M ℓ d u Φ := by
        rw [integral_const_mul]
        simp only [Work.BoseFixB1.Up.fibSum, Work.BoseFixB1.Up.pairSum, Submission.BoseGases.w1Fibre]
        ring

/-- **The split of `sbPot` at FS's parameters** — the form consumed by the per-box assembly. -/
theorem sbPot_split {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hR : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    {ε₀ μ : ℝ} (hAdm : Work.BoseBoxFix.Adm v ε₀ μ) {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) (u : EuclideanSpace ℝ (Fin 3))
    (hR16 : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16)
    (hRχ : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0) :
    Work.BoseFixB1.sbPot h μ u Φ
      = - (μ * Work.BoseFixB1.Up.fibSum h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u Φ)
        + Work.BoseFixB1.Up.pairSum v (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u Φ :=
  qLHSwordB_split (v := v) (h := h) (R0 := R) hv_supp hR hv hvrad hv1 _
    (by rw [Work.BoseFixB1.M_eq_mValue]; norm_num [Work.BoseBox.mValue])
    (Work.BoseFixB1.adm_ell_pos hAdm) (Work.BoseFixB1.adm_d_pos hAdm) hR16 hRχ u hΦc

/-! ## 3. The regime arithmetic of the gap payment -/

/-- **The `ε_T`-gap regime is automatic for admissible `μ`.**  At FS's parameters the hypothesis
`2(1+π⁻²)(dℓ c' √(μ a v))² ≤ ε_T` of `perBoxF_pieces.sbKin_ge_mu_av_cnPlus` reads, in closed form,
`2(1+π⁻²)c'²·t^{13/1292} ≤ 1` with `t = μ(a v)³`, so it holds for all admissible `μ` once
`ε₀ ≤ (1/(2(1+π⁻²)c'²+1))^{1292/13}`. -/
theorem gapRegime_of_adm {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hav : 0 < _root_.BoseGases.a v)
    {c' : ℝ} (hc' : 0 ≤ c') :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      2 * (1 + (Real.pi ^ 2)⁻¹)
          * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
              * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * c'
              * Real.sqrt (μ * (_root_.BoseGases.a v))) ^ 2
        ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT := by
  set A : ℝ := _root_.BoseGases.a v with hA
  set B : ℝ := 1 / (2 * (1 + (Real.pi ^ 2)⁻¹) * c' ^ 2 + 1) with hB
  have hBpos : 0 < 2 * (1 + (Real.pi ^ 2)⁻¹) * c' ^ 2 + 1 := by
    have h1 : (0:ℝ) ≤ (1 + (Real.pi ^ 2)⁻¹) := by positivity
    nlinarith [sq_nonneg c']
  have hB0 : 0 < B := by rw [hB]; exact div_pos one_pos hBpos
  have hBkey : (2 * (1 + (Real.pi ^ 2)⁻¹) * c' ^ 2 + 1) * B = 1 := by
    rw [hB]; field_simp
  refine ⟨min 1 (B ^ (1292 / 13 : ℝ)), lt_min one_pos (Real.rpow_pos_of_pos hB0 _), ?_⟩
  intro μ hAdm
  have hμ : 0 < μ := hAdm.1
  have ht0 : 0 < μ * A ^ 3 := mul_pos hμ (pow_pos hav 3)
  have hε₀ : μ * A ^ 3 ≤ B ^ (1292 / 13 : ℝ) := le_trans hAdm.2.1 (min_le_right _ _)
  have hte : (μ * A ^ 3) ^ (13 / 1292 : ℝ) ≤ B := by
    have hb : (μ * A ^ 3) ^ (13 / 1292 : ℝ) ≤ (B ^ (1292 / 13 : ℝ)) ^ (13 / 1292 : ℝ) :=
      Real.rpow_le_rpow ht0.le hε₀ (by norm_num)
    rwa [← Real.rpow_mul hB0.le, show (1292:ℝ) / 13 * (13 / 1292) = 1 by norm_num,
      Real.rpow_one] at hb
  have hfinal : 2 * (1 + (Real.pi ^ 2)⁻¹) * c' ^ 2 * (μ * A ^ 3) ^ (13 / 1292 : ℝ) ≤ 1 := by
    have h1 : 2 * (1 + (Real.pi ^ 2)⁻¹) * c' ^ 2 * (μ * A ^ 3) ^ (13 / 1292 : ℝ)
        ≤ 2 * (1 + (Real.pi ^ 2)⁻¹) * c' ^ 2 * B :=
      mul_le_mul_of_nonneg_left hte (by positivity)
    have h2 : 2 * (1 + (Real.pi ^ 2)⁻¹) * c' ^ 2 * B
        ≤ (2 * (1 + (Real.pi ^ 2)⁻¹) * c' ^ 2 + 1) * B := by nlinarith [hB0.le]
    linarith [h1, h2, hBkey]
  -- the closed form of the squared bracket
  have hsq : ((Work.BoseBox.paramsAt μ A).d * Work.BoseBox.sideAt μ A * c'
        * Real.sqrt (μ * A)) ^ 2 = c' ^ 2 * Work.BoseBox.fsXp (μ * A ^ 3) 9 := by
    have hd_eq : (Work.BoseBox.paramsAt μ A).d = Work.BoseBox.fsXp (μ * A ^ 3) 6 := rfl
    have hside_eq : Work.BoseBox.sideAt μ A = A * Work.BoseBox.fsXp (μ * A ^ 3) (-163) :=
      Work.BoseFixB1.sideAt_eq_fsXp (A := A) (μ := μ) hav hμ
    have hsqr : Real.sqrt (μ * A) ^ 2 = μ * A := Real.sq_sqrt (mul_nonneg hμ.le hav.le)
    have h1 : Work.BoseBox.fsXp (μ * A ^ 3) 6 * Work.BoseBox.fsXp (μ * A ^ 3) (-163)
        = Work.BoseBox.fsXp (μ * A ^ 3) (-157) := by
      rw [Work.BoseBox.fsXp_mul ht0]; norm_num
    have h2 : Work.BoseBox.fsXp (μ * A ^ 3) (-157) * Work.BoseBox.fsXp (μ * A ^ 3) (-157)
        = Work.BoseBox.fsXp (μ * A ^ 3) (-314) := by
      rw [Work.BoseBox.fsXp_mul ht0]; norm_num
    have h3 : (μ * A ^ 3) * Work.BoseBox.fsXp (μ * A ^ 3) (-314)
        = Work.BoseBox.fsXp (μ * A ^ 3) 9 := by
      calc (μ * A ^ 3) * Work.BoseBox.fsXp (μ * A ^ 3) (-314)
          = (μ * A ^ 3) ^ (1:ℝ) * (μ * A ^ 3) ^ ((-314:ℝ) / 323) := by
              rw [Real.rpow_one]; rfl
        _ = (μ * A ^ 3) ^ ((1:ℝ) + (-314:ℝ) / 323) := (Real.rpow_add ht0 1 _).symm
        _ = (μ * A ^ 3) ^ ((9:ℝ) / 323) := by congr 1; norm_num
        _ = Work.BoseBox.fsXp (μ * A ^ 3) 9 := rfl
    rw [mul_pow, mul_pow, mul_pow, hd_eq, hside_eq, hsqr]
    calc Work.BoseBox.fsXp (μ * A ^ 3) 6 ^ 2 * (A * Work.BoseBox.fsXp (μ * A ^ 3) (-163)) ^ 2
          * c' ^ 2 * (μ * A)
        = c' ^ 2 * ((μ * A ^ 3) * (Work.BoseBox.fsXp (μ * A ^ 3) 6
            * Work.BoseBox.fsXp (μ * A ^ 3) (-163))
            * (Work.BoseBox.fsXp (μ * A ^ 3) 6 * Work.BoseBox.fsXp (μ * A ^ 3) (-163))) := by
          ring
      _ = c' ^ 2 * ((μ * A ^ 3) * (Work.BoseBox.fsXp (μ * A ^ 3) (-157)
            * Work.BoseBox.fsXp (μ * A ^ 3) (-157))) := by rw [h1]; ring
      _ = c' ^ 2 * ((μ * A ^ 3) * Work.BoseBox.fsXp (μ * A ^ 3) (-314)) := by rw [h2]
      _ = c' ^ 2 * Work.BoseBox.fsXp (μ * A ^ 3) 9 := by rw [h3]
  rw [hsq]
  have hsplit : Work.BoseBox.fsXp (μ * A ^ 3) 9
      = Work.BoseBox.fsXp (μ * A ^ 3) (23 / 4) * Work.BoseBox.fsXp (μ * A ^ 3) (13 / 4) := by
    rw [Work.BoseBox.fsXp_mul ht0]; norm_num
  rw [hsplit]
  have heTpos : 0 < Work.BoseBox.fsXp (μ * A ^ 3) (23 / 4) := Work.BoseBox.fsXp_pos ht0
  have hfs : Work.BoseBox.fsXp (μ * A ^ 3) (13 / 4) = (μ * A ^ 3) ^ (13 / 1292 : ℝ) := by
    rw [Work.BoseBox.fsXp]; norm_num
  rw [hfs]
  calc 2 * (1 + (Real.pi ^ 2)⁻¹) * (c' ^ 2
        * (Work.BoseBox.fsXp (μ * A ^ 3) (23 / 4) * (μ * A ^ 3) ^ (13 / 1292 : ℝ)))
      = (2 * (1 + (Real.pi ^ 2)⁻¹) * c' ^ 2 * (μ * A ^ 3) ^ (13 / 1292 : ℝ))
          * Work.BoseBox.fsXp (μ * A ^ 3) (23 / 4) := by ring
    _ ≤ 1 * Work.BoseBox.fsXp (μ * A ^ 3) (23 / 4) :=
        mul_le_mul_of_nonneg_right hfinal heTpos.le
    _ = Work.BoseBox.fsXp (μ * A ^ 3) (23 / 4) := one_mul _

/-! ## 4. The "gap pays" branch of `PerBoxF` -/

/-- **`PerBoxF` holds whenever the excited count is a fixed fraction of `n‖Φ‖²`.**

With the *explicit* constants `C_s = chiSupAbs·chiSmallDecay mValue`, `K_av` the fibre constant of
`perBoxF_localised.fibSum_le`, `c₀ = (1/4)C_W C_s² + K_av C_s`, `c'² = 10^{100}c₀ + 1` and
`γ = c₀/c'² ≤ 10^{-100}`, every admissible state satisfying `γ·n·‖Φ‖² ≤ n₊(B)` (the FS-faithful
excited count `cnPlusBoxInd` of the sliding box) obeys `PerBoxF` at `c₁ = 1/4`; the `ε₀` is small
enough that FS's `ε_T`-gap absorbs `c'²μ(a v)·n₊(B)`. -/
theorem perBoxF_of_gapPayment {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ C γ : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ 0 < γ ∧ γ ≤ (1 / 10 : ℝ) ^ (100 : ℕ) ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          γ * (n : ℝ) * normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
            ≤ Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Φ : Submission.BoseGases.X n → ℝ) →
          PerBoxF v h R (1 / 4) C μ n Φ u := by
  obtain ⟨ε₁, hε₁, hsplit⟩ :=
    Work.BoseFixB1S.SbPotHalvesB1Fix (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨ε₂, CW, hε₂, hCW0, hWle⟩ :=
    w1MassB_le_const_mul_chiMass_regime (v := v) h hv hvrad hR hv_supp
  obtain ⟨εr, hεr, hreg2⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  -- the explicit constants
  have hCs0 : 0 ≤ Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue :=
    mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
      (Submission.BoseGases.chiSmallDecay_nonneg _)
  have hKav0 : 0 ≤ 16 * π * Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue
      / Work.SmallBoxSliding.smallConvLower Work.BoseBox.mValue :=
    div_nonneg (mul_nonneg (mul_nonneg (by positivity)
      Submission.BoseGases.chiSupAbs_nonneg)
      (Submission.BoseGases.chiSmallDecay_nonneg _))
      (le_of_lt (Work.SmallBoxSliding.smallConvLower_pos _))
  set Cs : ℝ := Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue with hCs
  set Kav : ℝ := 16 * π * Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue
      / Work.SmallBoxSliding.smallConvLower Work.BoseBox.mValue with hKav
  set c₀ : ℝ := (1 / 4) * CW * Cs ^ 2 + Kav * Cs with hc₀
  have hc₀0 : 0 ≤ c₀ := by
    rw [hc₀]
    exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCW0) (sq_nonneg Cs))
      (mul_nonneg hKav0 hCs0)
  set csq : ℝ := (10 : ℝ) ^ (100 : ℕ) * (c₀ + 1) with hcsq
  have hcsq0 : 0 < csq := by
    rw [hcsq]
    have h1 : 0 < c₀ + 1 := by linarith
    positivity
  set c' : ℝ := Real.sqrt csq with hc'
  set γ : ℝ := (c₀ + 1) / csq with hγ
  have hc'0 : 0 ≤ c' := Real.sqrt_nonneg _
  have hc'2 : c' ^ 2 = csq := Real.sq_sqrt hcsq0.le
  have hγ0 : 0 < γ := by
    rw [hγ]
    exact div_pos (by linarith) hcsq0
  have hγeq : c' ^ 2 * γ = c₀ + 1 := by
    rw [hγ, hc'2]
    exact mul_div_cancel₀ (c₀ + 1) (ne_of_gt hcsq0)
  obtain ⟨ε₃, hε₃, hreg3⟩ := gapRegime_of_adm (v := v) hav (c' := c') hc'0
  have hγle : γ ≤ (1 / 10 : ℝ) ^ (100 : ℕ) := by
    have hne : c₀ + 1 ≠ 0 := by linarith
    have heq : (c₀ + 1) / ((10 : ℝ) ^ (100 : ℕ) * (c₀ + 1)) = (1 / 10 : ℝ) ^ (100 : ℕ) := by
      rw [div_eq_iff (by positivity : ((10 : ℝ) ^ (100 : ℕ) * (c₀ + 1)) ≠ 0)]
      rw [← mul_assoc, ← mul_pow]
      norm_num
    rw [hγ, hcsq, heq]
  refine ⟨min (min (min ε₁ ε₂) ε₃) (min εr 1), 1, γ,
    lt_min (lt_min (lt_min hε₁ hε₂) hε₃) (lt_min hεr one_pos), zero_le_one, hγ0, hγle, ?_⟩
  intro μ hAdm n Φ u hpay
  have hμ : 0 < μ := hAdm.1
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  -- the admissible thresholds
  have hAdm₁ : Work.BoseBoxFix.Adm v ε₁ μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
      (min_le_left _ _)))
  have hAdm₂ : Work.BoseBoxFix.Adm v ε₂ μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
      (min_le_right _ _)))
  have hAdm₃ : Work.BoseBoxFix.Adm v ε₃ μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_right _ _))
  have hAdmr : Work.BoseBoxFix.Adm v εr μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
  -- the parameter facts
  have hℓ0 : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd0 : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  have hM1 : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
    rw [Work.BoseFixB1.M_eq_mValue]; norm_num [Work.BoseBox.mValue]
  have hdil : μ * (_root_.BoseGases.a v) ^ 3 ≤ εr :=
    le_trans hAdm.2.1 (le_trans (min_le_right _ _) (min_le_left _ _))
  obtain ⟨hR16, hRχ'⟩ := hreg2 μ hμ hdil
  have hA0 : 0 ≤ _root_.BoseGases.a v := le_of_lt hav
  -- ### the ingredients
  have hF := psiWeight_integral_le_thick (μ := μ) hμ (M := (Work.BoseBox.paramsAt μ
    (_root_.BoseGases.a v)).M) (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) hM1 hℓ0 u hΦc
  have hsc := scountB_le (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
    (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) hM1 u hΦc
  have hWle' := hWle μ hAdm₂ u
  have hfib := fibSum_le (v := v) (h := h) hv hvrad hR hv_supp hM1 hℓ0 hd0 hR16 hRχ' u hΦc
  have hchi := chiSum_le (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
    (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) hM1 u hΦc
  have hpair0 := pairSum_nonneg (v := v) hv (M := (Work.BoseBox.paramsAt μ
    (_root_.BoseGases.a v)).M) (u := u) (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
    (Φ : Submission.BoseGases.X n → ℝ)
  have hW0 := w1MassB_nonneg (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
    (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) h hv hvrad hR hv_supp hℓ0 hd0 u
  have hN0 := normB_nonneg (v := v) (μ := μ) (n := n) (Φ : Submission.BoseGases.X n → ℝ)
  have hchi0 := chiMass_nonneg (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
  have hsplit' := sbPot_split (v := v) (h := h) (R := R) hv_supp hR hv hvrad hv1 hAdm hΦc u hR16 hRχ'
  have hsb : sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ)
      = sbKin (v := v) μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u
          (Φ : Submission.BoseGases.X n → ℝ)
        + (-(μ * fibSum h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Φ : Submission.BoseGases.X n → ℝ))
            + pairSum v (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Φ : Submission.BoseGases.X n → ℝ)) := by
    rw [sbWord, hsplit']
  have hgap := sbKin_ge_mu_av_cnPlus (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
    (u := u) (Φ := (Φ : Submission.BoseGases.X n → ℝ)) (c' := c')
    (by positivity) hμ.le hc'0 (mul_pos hd0 hℓ0) (Work.BoseFixB1.Up.adm_eT_pos hAdm)
    (hreg3 μ hAdm₃) (Work.BoseFixB1.tBwordKinInd_nonneg _)
  -- ### the arithmetic
  unfold PerBoxF
  simp only [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB] at hpay ⊢
  set N : ℝ := ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      (Φ x) ^ 2 with hN
  set χ : ℝ := chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u with hχ
  set W : ℝ := w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u with hW
  set Fterm : ℝ := ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ
        (nCountB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x
        / chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) with hFt
  set nps : ℝ := Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Φ : Submission.BoseGases.X n → ℝ) with hnps
  -- the two final bounds
  have hLHS : (1 / 4) * (W * Fterm) - (1 / 2) * μ ^ 2 * W * N
      - 1 * (μ ^ 2 * (_root_.BoseGases.a v)
            * ((R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
                  * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
              + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) * χ * N
          + μ * (_root_.BoseGases.a v) * N)
      ≤ (1 / 4) * CW * (_root_.BoseGases.a v) * μ * (n : ℝ) * Cs ^ 2 * N := by
    have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h4 : 0 ≤ χ⁻¹ := inv_nonneg.mpr hchi0
    have h5 : 0 ≤ μ * (χ⁻¹ * ((n : ℝ) * Cs ^ 2 * N) + μ * N) := by positivity
    -- the F-term, with the smooth count replaced by `n Cs² N`
    have h6 : Fterm ≤ μ * (χ⁻¹ * ((n : ℝ) * Cs ^ 2 * N) + μ * N) := by
      have hmid : χ⁻¹ * scountB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
            (Φ : Submission.BoseGases.X n → ℝ)
          ≤ χ⁻¹ * ((n : ℝ) * Cs ^ 2 * N) := mul_le_mul_of_nonneg_left hsc h4
      have hmid2 : χ⁻¹ * scountB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
            (Φ : Submission.BoseGases.X n → ℝ) + μ * N
          ≤ χ⁻¹ * ((n : ℝ) * Cs ^ 2 * N) + μ * N := by linarith
      exact le_trans hF (mul_le_mul_of_nonneg_left hmid2 hμ.le)
    have h7 : (1 / 4 : ℝ) * (W * Fterm)
        ≤ (1 / 4 : ℝ) * (W * (μ * (χ⁻¹ * ((n : ℝ) * Cs ^ 2 * N) + μ * N))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h6 hW0) (by norm_num)
    have h9 : (1 / 4 : ℝ) * (W * (μ * (χ⁻¹ * ((n : ℝ) * Cs ^ 2 * N) + μ * N)))
        = (1 / 4) * W * μ * (χ⁻¹ * ((n : ℝ) * Cs ^ 2 * N)) + (1 / 4) * W * μ ^ 2 * N := by
      ring
    have h10 : χ * χ⁻¹ ≤ 1 := by
      rcases eq_or_lt_of_le hchi0 with h | h
      · rw [← h, inv_zero, mul_zero]; norm_num
      · rw [mul_inv_cancel₀ (ne_of_gt h)]
    have h11 : W * χ⁻¹ ≤ CW * (_root_.BoseGases.a v) := by
      have h1 : W * χ⁻¹ ≤ (CW * (_root_.BoseGases.a v) * χ) * χ⁻¹ :=
        mul_le_mul_of_nonneg_right hWle' h4
      have h2 : (CW * (_root_.BoseGases.a v) * χ) * χ⁻¹
          = CW * (_root_.BoseGases.a v) * (χ * χ⁻¹) := by ring
      have h3 : CW * (_root_.BoseGases.a v) * (χ * χ⁻¹)
          ≤ CW * (_root_.BoseGases.a v) * 1 :=
        mul_le_mul_of_nonneg_left h10 (mul_nonneg hCW0 hA0)
      linarith [h1, h2, h3]
    have h12 : (1 / 4 : ℝ) * W * μ * (χ⁻¹ * ((n : ℝ) * Cs ^ 2 * N))
        ≤ (1 / 4) * CW * (_root_.BoseGases.a v) * μ * (n : ℝ) * Cs ^ 2 * N := by
      have hfac : (0:ℝ) ≤ (1/4) * μ * ((n : ℝ) * Cs^2 * N) := by positivity
      have h1 : (W * χ⁻¹) * ((1/4) * μ * ((n : ℝ) * Cs^2 * N))
          ≤ (CW * (_root_.BoseGases.a v)) * ((1/4) * μ * ((n : ℝ) * Cs^2 * N)) :=
        mul_le_mul_of_nonneg_right h11 hfac
      calc (1 / 4 : ℝ) * W * μ * (χ⁻¹ * ((n : ℝ) * Cs ^ 2 * N))
          = (W * χ⁻¹) * ((1/4) * μ * ((n : ℝ) * Cs^2 * N)) := by ring
        _ ≤ (CW * (_root_.BoseGases.a v)) * ((1/4) * μ * ((n : ℝ) * Cs^2 * N)) := h1
        _ = (1/4) * CW * (_root_.BoseGases.a v) * μ * (n : ℝ) * Cs ^ 2 * N := by ring
    have h13 : 0 ≤ (1 / 4 : ℝ) * W * μ ^ 2 * N := by positivity
    have h14 : 0 ≤ μ * (_root_.BoseGases.a v) * N := by positivity
    have h15 : 0 ≤ μ ^ 2 * (_root_.BoseGases.a v)
        * ((R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
          + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
            * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) * χ * N := by
      have hKB : (0:ℝ) ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB :=
        le_of_lt (Work.BoseFixB1.paramsAt_KB_pos hAdm)
      have h3 : (0:ℝ) ≤ (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) :=
        Real.rpow_nonneg (mul_nonneg hμ.le (pow_nonneg hA0 3)) _
      positivity
    linarith [h7, h9, h12, h13, h14, h15]
  have hRHS : c' ^ 2 * μ * (_root_.BoseGases.a v) * nps
      - μ * Kav * (_root_.BoseGases.a v) * (n : ℝ) * Cs * N
      ≤ sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
    rw [hsb]
    have h1 : μ * fibSum h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Φ : Submission.BoseGases.X n → ℝ)
        ≤ μ * (Kav * (_root_.BoseGases.a v) * chiSum
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
            (Φ : Submission.BoseGases.X n → ℝ)) :=
      mul_le_mul_of_nonneg_left hfib hμ.le
    have h2 : μ * (Kav * (_root_.BoseGases.a v) * chiSum
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
            (Φ : Submission.BoseGases.X n → ℝ))
        ≤ μ * (Kav * (_root_.BoseGases.a v) * ((n : ℝ) * Cs * N)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hchi (mul_nonneg hKav0 hA0)) hμ.le
    have h3 : μ * (Kav * (_root_.BoseGases.a v) * ((n : ℝ) * Cs * N))
        = μ * Kav * (_root_.BoseGases.a v) * (n : ℝ) * Cs * N := by ring
    linarith [h1, h2, h3, hgap, hpair0]
  have hkey : (1 / 4) * CW * (_root_.BoseGases.a v) * μ * (n : ℝ) * Cs ^ 2 * N
      ≤ c' ^ 2 * μ * (_root_.BoseGases.a v) * nps
        - μ * Kav * (_root_.BoseGases.a v) * (n : ℝ) * Cs * N := by
    have h1 : c' ^ 2 * μ * (_root_.BoseGases.a v) * nps
        ≥ μ * (_root_.BoseGases.a v) * ((n : ℝ) * N) * (c₀ + 1) := by
      have h2 : c' ^ 2 * μ * (_root_.BoseGases.a v) * (γ * (n : ℝ) * N)
          ≤ c' ^ 2 * μ * (_root_.BoseGases.a v) * nps :=
        mul_le_mul_of_nonneg_left hpay (by positivity)
      have h3 : c' ^ 2 * μ * (_root_.BoseGases.a v) * (γ * (n : ℝ) * N)
          = μ * (_root_.BoseGases.a v) * ((n : ℝ) * N) * (c' ^ 2 * γ) := by ring
      rw [hγeq] at h3
      linarith [h2, h3]
    have h2 : μ * (_root_.BoseGases.a v) * ((n : ℝ) * N) * (c₀ + 1)
        = (1 / 4) * CW * (_root_.BoseGases.a v) * μ * (n : ℝ) * Cs ^ 2 * N
          + μ * Kav * (_root_.BoseGases.a v) * (n : ℝ) * Cs * N
          + μ * (_root_.BoseGases.a v) * ((n : ℝ) * N) := by
      rw [hc₀]; ring
    have h3 : 0 ≤ μ * (_root_.BoseGases.a v) * ((n : ℝ) * N) := by positivity
    linarith [h1, h2, h3]
  calc (1 / 4) * (W * Fterm) - (1 / 2) * μ ^ 2 * W * N
      - 1 * (μ ^ 2 * (_root_.BoseGases.a v)
            * ((R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
                  * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
              + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) * χ * N
          + μ * (_root_.BoseGases.a v) * N)
      ≤ (1 / 4) * CW * (_root_.BoseGases.a v) * μ * (n : ℝ) * Cs ^ 2 * N := hLHS
    _ ≤ c' ^ 2 * μ * (_root_.BoseGases.a v) * nps
        - μ * Kav * (_root_.BoseGases.a v) * (n : ℝ) * Cs * N := hkey
    _ ≤ sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := hRHS

/-! ## 5. The reduction of the target to a single *flat-branch* atom -/

/-- **The thick case of the crux follows from the gap branch plus the flat branch.**

`perBoxF_of_gapPayment` (this file, PROVED) supplies the branch
`γ·n·‖Φ‖² ≤ n₊(B(u))` with an *explicit* threshold bound `γ ≤ 10^{-100}`; a statement of the
complementary branch — `n₊(B(u)) ≤ 10^{-100}·n·‖Φ‖²` implies `PerBoxF` — therefore completes the
dichotomy.  The parameter bookkeeping is `ε₀ = min`, `c₁ = min`, `C = max`, using the
monotonicity of `PerBoxF`'s left side in `c₁` (downwards) and `C` (upwards) (the `F`-term and the
error bracket are `≥ 0`). -/
theorem perBoxF_thick_of_flatBranch {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v)
    (hflat : ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
          ¬ IsThinBox v h μ u →
          Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Φ : Submission.BoseGases.X n → ℝ)
            ≤ (1 / 10 : ℝ) ^ (100 : ℕ) * (n : ℝ)
                * normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
          PerBoxF v h R c₁ C μ n Φ u) :
    PerBoxF_thick v h R := by
  obtain ⟨εg, Cg, γg, hεg, hCg, hγg, hγg100, hgap⟩ :=
    perBoxF_of_gapPayment (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εa, c₁a, Ca, hεa, hc₁a, hCa, hflat'⟩ := hflat
  refine ⟨min εg εa, min (1 / 4) c₁a, max Cg Ca, lt_min hεg hεa, lt_min (by norm_num) hc₁a,
    le_max_of_le_left hCg, ?_⟩
  intro μ hAdm n Φ u hu hthick
  have hAdm_g : Work.BoseBoxFix.Adm v εg μ := Adm.mono hAdm (min_le_left _ _)
  have hAdm_a : Work.BoseBoxFix.Adm v εa μ := Adm.mono hAdm (min_le_right _ _)
  have hμ : 0 < μ := hAdm.1
  have ha0 : 0 ≤ _root_.BoseGases.a v := le_of_lt hav
  -- the `F`-term and the error bracket of `PerBoxF` are nonnegative
  have hχ0 : 0 ≤ chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u := chiMass_nonneg _ _ _ _
  have hF0 : 0 ≤ ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      (Φ : Submission.BoseGases.X n → ℝ) x ^ 2 *
        Work.SmallBoxSliding.psiWeight 1 μ
          (nCountB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x /
            chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _)
      (perBoxFCase_psiWeight_nonneg (by norm_num) hμ
        (div_nonneg (nCountB_nonneg x) hχ0))
  have hW0 : 0 ≤ w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u :=
    w1MassB_nonneg (v := v) (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
      (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
      h hv hvrad hR hv_supp (adm_ell_pos hAdm_g) (adm_d_pos hAdm_g) u
  have herr0 : 0 ≤ μ ^ 2 * (_root_.BoseGases.a v) *
        ((R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
          + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
            * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) *
        chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u *
        normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
      + μ * (_root_.BoseGases.a v) * normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
    have hN0 : 0 ≤ normB v μ n (Φ : Submission.BoseGases.X n → ℝ) :=
      normB_nonneg (v := v) (μ := μ) (n := n) _
    have hKB : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB :=
      le_of_lt (paramsAt_KB_pos hAdm_g)
    have h3 : 0 ≤ (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) :=
      Real.rpow_nonneg (mul_nonneg hμ.le (pow_nonneg ha0 3)) _
    have hS : 0 ≤ (R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
        + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
          * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) :=
      add_nonneg (sq_nonneg _) (mul_nonneg (pow_nonneg hKB 3) h3)
    positivity
  by_cases hcase : γg * (n : ℝ) * normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
      ≤ Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
          (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
          (Φ : Submission.BoseGases.X n → ℝ)
  · have hp := hgap μ hAdm_g n Φ u hcase
    simp only [PerBoxF] at hp ⊢
    have h1 := mul_le_mul_of_nonneg_right (min_le_left (1 / 4) c₁a) (mul_nonneg hW0 hF0)
    have h2 := mul_le_mul_of_nonneg_right (le_max_left Cg Ca) herr0
    linarith
  · have hlt : Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
          (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
          (Φ : Submission.BoseGases.X n → ℝ)
        ≤ (1 / 10 : ℝ) ^ (100 : ℕ) * (n : ℝ)
            * normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
      have hN0 : 0 ≤ normB v μ n (Φ : Submission.BoseGases.X n → ℝ) :=
        normB_nonneg (v := v) (μ := μ) (n := n) _
      have hstep : γg * (n : ℝ) ≤ (1 / 10 : ℝ) ^ (100 : ℕ) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hγg100 (Nat.cast_nonneg n)
      have hstep2 : γg * (n : ℝ) * normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
          ≤ (1 / 10 : ℝ) ^ (100 : ℕ) * (n : ℝ)
              * normB v μ n (Φ : Submission.BoseGases.X n → ℝ) :=
        mul_le_mul_of_nonneg_right hstep hN0
      have hlt2 : Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            (Φ : Submission.BoseGases.X n → ℝ)
          < γg * (n : ℝ) * normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := not_le.mp hcase
      linarith
    have hp := hflat' μ hAdm_a n Φ u hu hthick hlt
    simp only [PerBoxF] at hp ⊢
    have h1 := mul_le_mul_of_nonneg_right (min_le_right (1 / 4) c₁a) (mul_nonneg hW0 hF0)
    have h2 := mul_le_mul_of_nonneg_right (le_max_right Cg Ca) herr0
    linarith


/-! ## The thin case (from `perBoxMF_of_thin_support`, upstream) -/

theorem perBoxF_thin_holds {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R : ℝ} (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) :
    PerBoxF_thin v h R := by
  refine ⟨1, 1 / 4, 0, one_pos, by norm_num, le_refl 0,
    fun μ hAdm n Φ u _hu hthin => ?_⟩
  have hμ : 0 < μ := adm_mu_pos hAdm
  have hM1 : 1 ≤ (paramsAt μ (a v)).M := by
    rw [M_eq_mValue]; norm_num [Work.BoseBox.mValue]
  have hℓ0 : 0 < sideAt μ (a v) := adm_ell_pos hAdm
  have hpair_nn : ∀ x y : EuclideanSpace ℝ (Fin 3),
      0 ≤ Submission.BoseGases.wSmallPair (paramsAt μ (a v)).M (sideAt μ (a v))
            (paramsAt μ (a v)).d u v x y := fun x y =>
    perBoxMFCase_wSmallPair_nonneg (M := (paramsAt μ (a v)).M) (ℓ := sideAt μ (a v))
      (d := (paramsAt μ (a v)).d) (u := u) (x := x) (y := y) hv
  have hkin : 0 ≤ sbKin (v := v) μ (paramsAt μ (a v)).M u Φ := by
    rw [sbKin]
    exact Work.UBBInputs9.A.tBwordBInd_nonneg hℓ0 (adm_eT_bounds hAdm).1 u (Φ : X n → ℝ)
  have key := perBoxMF_of_thin_support h hμ u (Φ : X n → ℝ) hM1 hℓ0 hthin hpair_nn hkin
  have key' : (1 / 4) * (w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u *
        (∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 *
          ((nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x /
              chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) - μ) ^ 2))
      - (1 / 2) * μ ^ 2 * w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
          (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ)
      - 0 * perBoxErr v μ R n Φ u
      ≤ sbWord h μ u (Φ : X n → ℝ) := by
    simpa using key
  exact perBoxF_of_perBoxMF_at h hv hvrad hR hv_supp hAdm Φ key'


theorem perBoxF_of_thin_thick {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R : ℝ} (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hthin : PerBoxF_thin v h R) (hthick : PerBoxF_thick v h R) : PerBoxFAll v h R := by
  obtain ⟨ε₁, c₁, C₁, hε₁, hc₁, hC₁, H₁⟩ := hthin
  obtain ⟨ε₂, c₂, C₂, hε₂, hc₂, hC₂, H₂⟩ := hthick
  refine ⟨min ε₁ ε₂, min c₁ c₂, max C₁ C₂, lt_min hε₁ hε₂, lt_min hc₁ hc₂,
    le_max_of_le_left hC₁, fun μ hAdm n Φ u hu _hP => ?_⟩
  have h₁ : Work.BoseBoxFix.Adm v ε₁ μ := Adm.mono (ε₀' := min ε₁ ε₂) (ε₀ := ε₁) hAdm
    (min_le_left _ _)
  have h₂ : Work.BoseBoxFix.Adm v ε₂ μ := Adm.mono (ε₀' := min ε₁ ε₂) (ε₀ := ε₂) hAdm
    (min_le_right _ _)
  have hμ : 0 < μ := adm_mu_pos h₁
  have hℓ : 0 < sideAt μ (a v) := adm_ell_pos h₁
  have hd : 0 < (paramsAt μ (a v)).d := adm_d_pos h₁
  have hΦnn : 0 ≤ ∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 *
      psiWeight 1 μ (nCountB (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u x /
        chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u) :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _)
      (perBoxFCase_psiWeight_nonneg (by norm_num) hμ
        (div_nonneg (nCountB_nonneg x) (chiMass_nonneg _ _ _ _)))
  have hW : 0 ≤ w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u :=
    w1MassB_nonneg h hv hvrad hR hv_supp hℓ hd u
  have hstep : min c₁ c₂ * (w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u *
        (∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 *
          psiWeight 1 μ (nCountB (paramsAt μ (a v)).M (sideAt μ (a v))
            (paramsAt μ (a v)).d u x /
            chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u)))
      ≤ c₁ * (w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u *
        (∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 *
          psiWeight 1 μ (nCountB (paramsAt μ (a v)).M (sideAt μ (a v))
            (paramsAt μ (a v)).d u x /
            chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u))) :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) (mul_nonneg hW hΦnn)
  have hstep₂ : min c₁ c₂ * (w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u *
        (∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 *
          psiWeight 1 μ (nCountB (paramsAt μ (a v)).M (sideAt μ (a v))
            (paramsAt μ (a v)).d u x /
            chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u)))
      ≤ c₂ * (w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u *
        (∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 *
          psiWeight 1 μ (nCountB (paramsAt μ (a v)).M (sideAt μ (a v))
            (paramsAt μ (a v)).d u x /
            chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u))) :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) (mul_nonneg hW hΦnn)
  have herr : 0 ≤ μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
        + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
      * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
      * normB v μ n (Φ : X n → ℝ) + μ * (a v) * normB v μ n (Φ : X n → ℝ) := by
    have ha : 0 ≤ a v := le_of_lt (adm_a_pos h₁)
    have hKB : 0 ≤ (paramsAt μ (a v)).KB := le_of_lt (paramsAt_KB_pos h₁)
    have hnb : 0 ≤ normB v μ n (Φ : X n → ℝ) := normB_nonneg _
    have hS : 0 ≤ (R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
        + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) :=
      add_nonneg (sq_nonneg _)
        (mul_nonneg (pow_nonneg hKB 3)
          (Real.rpow_nonneg (mul_nonneg (le_of_lt hμ) (pow_nonneg ha 3)) _))
    have hprod : 0 ≤ μ ^ 2 * (a v)
        * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
          + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
        * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
        * normB v μ n (Φ : X n → ℝ) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) ha) hS)
        (chiMass_nonneg _ _ _ _)) hnb
    have hlin : 0 ≤ μ * (a v) * normB v μ n (Φ : X n → ℝ) :=
      mul_nonneg (mul_nonneg (le_of_lt hμ) ha) hnb
    linarith [hprod, hlin]
  by_cases hthinμ : IsThinBox v h μ u
  · have key := H₁ μ h₁ n Φ u hu hthinμ
    unfold PerBoxF at key
    have hC : C₁ * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
          + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
        * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
        * normB v μ n (Φ : X n → ℝ)
      + μ * (a v) * normB v μ n (Φ : X n → ℝ))
        ≤ max C₁ C₂ * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
          + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
        * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
        * normB v μ n (Φ : X n → ℝ)
      + μ * (a v) * normB v μ n (Φ : X n → ℝ)) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) herr
    linarith [key, hstep, hC]
  · have key := H₂ μ h₂ n Φ u hu hthinμ
    unfold PerBoxF at key
    have hC : C₂ * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
          + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
        * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
        * normB v μ n (Φ : X n → ℝ)
      + μ * (a v) * normB v μ n (Φ : X n → ℝ))
        ≤ max C₁ C₂ * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
          + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
        * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
        * normB v μ n (Φ : X n → ℝ)
      + μ * (a v) * normB v μ n (Φ : X n → ℝ)) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) herr
    linarith [key, hstep₂, hC]

theorem perBoxF_of_thick {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hthick : PerBoxF_thick v h R) : PerBoxFAll v h R :=
  perBoxF_of_thin_thick hv hvrad hR hv_supp (perBoxF_thin_holds hv hvrad hR hv_supp) hthick

theorem perBoxFWeight_holds_of_all {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R : ℝ} (hA : PerBoxFAll v h R) :
    ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
          Work.BoseFixB1.PerBoxF v h R c₁ C μ n Φ u := by
  obtain ⟨ε₀, c₁, C, hε, hc, hC, H⟩ := hA
  exact ⟨ε₀, c₁, C, hε, hc, hC, fun μ hAdm n Φ u hu => H μ hAdm n Φ u hu trivial⟩

/-- **The target's conclusion from the flat-branch atom** (FS `thm:smallbox`'s condensed
branch, `Work.BoseFixB1.flatBranchAtom`): the proved gap branch plus the thin case plus this
atom give the target. -/
theorem perBoxFWeight_holds_of_flatAtom {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v) (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v)
    (hflat : ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
          ¬ IsThinBox v h μ u →
          Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Φ : Submission.BoseGases.X n → ℝ)
            ≤ (1 / 10 : ℝ) ^ (100 : ℕ) * (n : ℝ)
                * normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
          Work.BoseFixB1.PerBoxF v h R c₁ C μ n Φ u) :
    ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
          Work.BoseFixB1.PerBoxF v h R c₁ C μ n Φ u :=
  perBoxFWeight_holds_of_all (perBoxF_of_thick hv hvrad hR hv_supp
    (perBoxF_thick_of_flatBranch (v := v) h hv hv1 hvrad hR hv_supp hav hflat))

end Work.BoseFixB1.Up
