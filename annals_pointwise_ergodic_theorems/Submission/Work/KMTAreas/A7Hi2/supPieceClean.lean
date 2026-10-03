/-
# `SupPiece` (the Ionescu--Wainger values-supremum) — state of this file

The target `Work.KMTAreas.A7Hi2.SupPiece` is the maximal (values-supremum) bound for the low-pass
Ionescu--Wainger family `m ↦ kmtProj ρ l₁ (-(m₀ + m))` on the good major arcs, with the polynomial
constant `C (1 + l₁)²` and *uniformly* in the base level `m₀`.

WHAT THIS FILE DOES

* `supPart_le_norm_zero_add_varPart_two` — the elementary pointwise reduction
  `supPart r a ≤ ‖a 0‖ₑ + varPart 2 a` (the two-point chain `(0, m)`); note `supPart` does not
  depend on `r`.
* `supPart_lpf_mono` — monotonicity in the base level: the base-`m₀'` family is a subfamily of the
  base-`m₀` family for `m₀ ≤ m₀'`, so a bound at one base level gives it at every larger one.  In
  particular the `m₀`-uniformity in the statement is free, and the *smallest* admitted base level
  is the hardest case.
* `supPiece_of_variationalEstimate` — **the target follows from the *variational* estimate**
  `‖V²_m (Π_{≤l₁,≤-(m₀+m)} f)‖_{ℓᵖ} ≤ C(1+l₁)²‖f‖_{ℓᵖ}` combined with the *proved, axiom-clean*
  single-scale bound `Work.KMTAreas.A7.kmtProj_lp_bound_uniform`.  This is the form in which the
  estimate appears in the source paper ((lin-1)/(lin-2) of Krause--Mirek--Tao) and the form the
  KMSZ Theorem 5.2 / Lépingle machinery consumes.

WHAT IS NOT DONE

`supPieceClean` itself is *not* proved: the variational estimate it is reduced to is the single
mathematical content of this cluster of files and is *not* reachable from the material in the
workspace.  The detailed analysis, the list of routes that are dead, and the two deep inputs that
are missing (the *continuous* lacunary variational estimate of Jones--Seeger--Wright and the
*vector-valued* even-endpoint Ionescu--Wainger multiplier bound `IWMultiplierBoundStatement_even`)
are recorded in `NOTES_A7Hi2_supPieceClean_SESSION.md` at the workspace root.  In particular every
"elementary" bound (pointwise kernel envelope, kernel `ℓ¹`/`ℓ²` mass, decimation over the
subgroups of `iwArithFreqs ρ l₁` one at a time) has a constant that is *exponential* in `l₁`,
while the target allows only `(1+l₁)²`; the arithmetic super-orthogonality of Ionescu--Wainger is
essential.
-/
import Mathlib
import Submission.Work.KMTAreas.A7Hi2.supDeepLe
import Submission.Work.KMTAreas.A7Hi2.supShallowLe
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7Hi2

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- **The values-supremum is dominated by the first value plus the `2`-variation.**
For every `a : ℕ → ℂ` and every `x`, `sup_m ‖a m x‖ ≤ ‖a 0 x‖ + V²(a)`, by the two-point chain
`(0, m)`.  (`supPart` does not depend on the exponent `r` appearing in its first argument.) -/
lemma supPart_le_norm_zero_add_varPart_two (r : NNReal) (a : ℕ → ℂ) :
    Work.KMTAreas.A7Hi.supPart r a
      ≤ ‖a 0‖ₑ + Submission.PointwiseErgodicTheorems.varPart 2 a := by
  refine iSup_le fun m => ?_
  have hchain := Work.KMTAreas.A7Lpd.enorm_sub_zero_le_varPart (r := 2) (by norm_num) a m
  calc ‖a m‖ₑ = ‖a 0 + (a m - a 0)‖ₑ := by
        congr 1
        ring
    _ ≤ ‖a 0‖ₑ + ‖a m - a 0‖ₑ := enorm_add_le _ _
    _ ≤ ‖a 0‖ₑ + Submission.PointwiseErgodicTheorems.varPart 2 a := add_le_add le_rfl hchain

/-- Passing to the `enorm`-valued function does not change `eLpNorm`. -/
private lemma eLpNorm_enorm_eq' {g : ℤ → ℂ} {p : ENNReal} (h0 : p ≠ 0) (ht : p ≠ ⊤) :
    MeasureTheory.eLpNorm (fun x : ℤ => ‖g x‖ₑ) p MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm g p MeasureTheory.Measure.count := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) h0 ht,
    MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) h0 ht]
  simp only [enorm_eq_self]

/-- **Monotonicity in the base level.**  For `m₀ ≤ m₀'` the family `m ↦ Π_{≤l₁,≤-(m₀'+m)}` is a
subfamily of `m ↦ Π_{≤l₁,≤-(m₀+m)}` (namely the indices `m + (m₀'-m₀)`), hence the values-supremum
at the larger base level is pointwise dominated by the one at the smaller base level.  So a
`SupPiece`-type bound at one base level propagates to every larger base level: the `m₀`-uniformity
required by the statement is automatic and the *smallest* admitted base level is the hardest. -/
lemma supPart_lpf_mono {ρ : ℝ} {l₁ m₀ m₀' : ℕ} (h : m₀ ≤ m₀') (f : ℤ → ℂ) (r : NNReal) (x : ℤ) :
    Work.KMTAreas.A7Hi.supPart r (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀' m f x)
      ≤ Work.KMTAreas.A7Hi.supPart r (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x) := by
  refine iSup_le fun m => ?_
  refine le_iSup_of_le (m + (m₀' - m₀)) ?_
  have hkey : ((m₀ : ℤ) + ((m + (m₀' - m₀) : ℕ) : ℤ)) = ((m₀' : ℤ) + (m : ℤ)) := by
    have hsub : ((m₀' - m₀ : ℕ) : ℤ) = (m₀' : ℤ) - (m₀ : ℤ) := by
      rw [Nat.cast_sub h]
    have hm : ((m + (m₀' - m₀) : ℕ) : ℤ) = (m : ℤ) + ((m₀' - m₀ : ℕ) : ℤ) := by
      push_cast
      ring
    rw [hm, hsub]
    ring
  have harith : -((m₀ : ℤ) + ((m + (m₀' - m₀) : ℕ) : ℤ)) = -((m₀' : ℤ) + (m : ℤ)) := by
    rw [hkey]
  simp only [Work.KMTAreas.A7Hi.lpf, harith]
  exact le_rfl

/-- **The target from the variational estimate** (with the *proved* single-scale bound).  If for
`1 < p < ∞` the `2`-variation of the low-pass family is bounded by `C(1+l₁)²‖f‖_{ℓᵖ}` uniformly in
the base level, then the values-supremum is bounded by the same expression up to the *additive*
constant of `Work.KMTAreas.A7.kmtProj_lp_bound_uniform`, which is `l`-free. -/
theorem supPiece_of_variationalEstimate
    (hvar : ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
      ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm 2
            (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
          p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C * (1 + (l₁ : ℝ)) ^ 2) *
              MeasureTheory.eLpNorm f p MeasureTheory.Measure.count) :
    Work.KMTAreas.A7Hi2.SupPiece := by
  intro ρ hρ hρ1 p hp hptop r
  obtain ⟨CρV, hCρVpos, CV, hCVpos, hV⟩ := hvar ρ hρ hρ1 p hp hptop
  have hp1 : (1 : ℝ) < p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (ne_of_lt hptop)).mpr hp
  obtain ⟨CρS, hCρSpos, CS, hCSpos, hS⟩ :=
    Work.KMTAreas.A7.kmtProj_lp_bound_uniform ρ hρ hρ1 p.toReal hp1
  have hpne0 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have hpnetop : p ≠ ⊤ := ne_of_lt hptop
  have hpeq : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal hpnetop
  refine ⟨max CρV CρS, lt_max_of_lt_left hCρVpos, CV + CS, by positivity, ?_⟩
  intro l₁ m₀ hgood f
  have hgoodV : Work.Analysis.IonescuWainger.GoodMajorArcs ρ CρV l₁ (-(m₀ : ℤ)) :=
    Work.KMTAreas.A7Hi.goodMajorArcs_mono (C₁ := CρV) (C₂ := max CρV CρS)
      (le_max_left _ _) hgood
  have hgoodS : Work.Analysis.IonescuWainger.GoodMajorArcs ρ CρS l₁ (-(m₀ : ℤ)) :=
    Work.KMTAreas.A7Hi.goodMajorArcs_mono (C₁ := CρS) (C₂ := max CρV CρS)
      (le_max_right _ _) hgood
  -- the pointwise bound: values-supremum ≤ first value + variational norm
  have hpoint : ∀ x : ℤ, Work.KMTAreas.A7Hi.supPart r
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x)
      ≤ ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ
        + PointwiseErgodicTheorems.variationalNorm 2
            (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x) := by
    intro x
    refine (supPart_le_norm_zero_add_varPart_two r
      (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x)).trans (add_le_add le_rfl ?_)
    rw [Submission.PointwiseErgodicTheorems.variationalNorm_eq_add]
    exact le_add_left le_rfl
  have hstep : MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.supPart r
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
      p MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ)
          p MeasureTheory.Measure.count
        + MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm 2
            (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
          p MeasureTheory.Measure.count :=
    (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) hpoint).trans
      (Work.KMTAreas.A7.eLpNorm_add_le_ennreal
        (u := fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ)
        (v := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm 2
            (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
        (le_of_lt hp) (ne_of_lt hptop) (μ := MeasureTheory.Measure.count))
  have hfirst : MeasureTheory.eLpNorm (fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ)
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal CS * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    have h := hS l₁ (-(m₀ : ℤ)) hgoodS f
    rw [hpeq] at h
    have h0 : Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f
        = Work.KMTContract.kmtProj ρ l₁ (-(m₀ : ℤ)) f := by
      funext y
      simp only [Work.KMTAreas.A7Hi.lpf]
      norm_num
    rw [eLpNorm_enorm_eq' hpne0 hpnetop, h0]
    exact h
  have hsecond := hV l₁ m₀ hgoodV f
  have hCV0 : (0 : ℝ) ≤ CV := hCVpos.le
  have hCS0 : (0 : ℝ) ≤ CS := hCSpos.le
  have hl0 : (0 : ℝ) ≤ (l₁ : ℝ) := Nat.cast_nonneg l₁
  refine hstep.trans ?_
  calc MeasureTheory.eLpNorm (fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ)
          p MeasureTheory.Measure.count
        + MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm 2
            (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
          p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal CS * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
        + ENNReal.ofReal (CV * (1 + (l₁ : ℝ)) ^ 2)
            * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count :=
        add_le_add hfirst hsecond
    _ = ENNReal.ofReal (CS + CV * (1 + (l₁ : ℝ)) ^ 2)
          * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
        rw [← add_mul, ← ENNReal.ofReal_add hCS0 (mul_nonneg hCV0 (by positivity))]
    _ ≤ ENNReal.ofReal ((CV + CS) * (1 + (l₁ : ℝ)) ^ 2)
          * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
        refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
        have h1 : (1 : ℝ) ≤ (1 + (l₁ : ℝ)) ^ 2 := by nlinarith [hl0]
        nlinarith [h1, hCV0, hCS0]

end

/-! ## Discharging a KMSZ hypothesis

The tail-bound half of `Work.BourgainPlan.Thm52.exists_thm52` (`LargeScaleBound`) is the crux of
this cluster; its *other* hypothesis, the uniform-in-signs bound for the lacunary differences
(`SignedDiffBound`), is available for the low-pass family and is recorded here: it is the
`l`-free, `m₀`-free bound `KMTAreas/A7Hi2/dyadicSignedDiffBound` (an instance of the proved
`A7Lpd.uniformSignsAnnuliOfReal`) converted into the `∫⁻`-form in which `Thm52` states it. -/

/-- `(eLpNorm g (ofReal q))^q` is the `∫⁻ ‖g‖ₑ^q` integral, for `q > 0`. -/
private lemma eLpNorm_rpow_eq_lintegral (q : ℝ) (hq : 0 < q) (g : ℤ → ℂ) :
    (MeasureTheory.eLpNorm g (ENNReal.ofReal q) MeasureTheory.Measure.count) ^ q
      = ∫⁻ y : ℤ, ‖g y‖ₑ ^ q ∂MeasureTheory.Measure.count := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm)
    (ENNReal.ofReal_ne_zero_iff.mpr hq) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hq.le]
  rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq.ne', ENNReal.rpow_one]

/-! ## `SupPiece` from the chain-part bound (the fleet's crux)

`Work.KMTAreas.A7HiRep.chainPartSqFun` / `A7JSW.chainPartSqFunPos` / `A7Hi2.ChainPiece` /
`A7MixedG.chainLe` / `A7G.chainPartLowpass` are five copies of the same statement: the chain part
of the variational norm of the low-pass walk is bounded by the band square function / by `‖f‖`,
with an `l`-free constant.  The two-point-chain bound `supPart ≤ ‖T_0‖ₑ + chainPart` (proved above)
shows that this single statement *implies* `SupPiece` — i.e. the maximal bound with the `(1+l₁)²`
loss of `LowpassVarG2.SupPiece` carries **no** extra content beyond the (conjecturally `l`-free)
chain-part crux.  (The literature supports `l`-uniformity: Krause–Mirek–Tao remark that the `⟨l⟩`
of MSZ3 Theorem 2.1 was removed in Tao's uniform vector-valued Ionescu–Wainger theorem, so the
`(1+l₁)²` here is a *safe over-estimate*, not a genuine loss.) -/

/-- **`SupPiece` from the chain-part bound.**  If the chain part of the low-pass walk is bounded in
`ℓᵖ` by an `l`-free constant times `‖f‖_{ℓᵖ}` (the chain crux, at the `2`-exponent of the chain
norm), then the values-supremum is bounded by `C(1+l₁)²‖f‖_{ℓᵖ}` — the constant `1 ≤ (1+l₁)²`
absorbing the `l`-free pieces. -/
theorem supPiece_of_chainPartBound
    (hC : ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
      ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
        MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.chainPart 2
            (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
          p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count) :
    Work.KMTAreas.A7Hi2.SupPiece := by
  intro ρ hρ hρ1 p hp hptop r
  obtain ⟨CρC, hCρCpos, CC, hCCpos, hCb⟩ := hC ρ hρ hρ1 p hp hptop
  have hp1 : (1 : ℝ) < p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (ne_of_lt hptop)).mpr hp
  obtain ⟨CρS, hCρSpos, CS, hCSpos, hSb⟩ :=
    Work.KMTAreas.A7.kmtProj_lp_bound_uniform ρ hρ hρ1 p.toReal hp1
  have hpne0 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have hpnetop : p ≠ ⊤ := ne_of_lt hptop
  have hpeq : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal hpnetop
  refine ⟨max CρC CρS, lt_max_of_lt_left hCρCpos, CS + CC, by positivity, ?_⟩
  intro l₁ m₀ hgood f
  have hgoodC : Work.Analysis.IonescuWainger.GoodMajorArcs ρ CρC l₁ (-(m₀ : ℤ)) :=
    Work.KMTAreas.A7Hi.goodMajorArcs_mono (C₁ := CρC) (C₂ := max CρC CρS)
      (le_max_left _ _) hgood
  have hgoodS : Work.Analysis.IonescuWainger.GoodMajorArcs ρ CρS l₁ (-(m₀ : ℤ)) :=
    Work.KMTAreas.A7Hi.goodMajorArcs_mono (C₁ := CρS) (C₂ := max CρC CρS)
      (le_max_right _ _) hgood
  -- the two-point-chain pointwise bound, with the `A7Hi.chainPart` normalisation
  have hpoint : ∀ x : ℤ, Work.KMTAreas.A7Hi.supPart r
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x)
      ≤ ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ
        + Work.KMTAreas.A7Hi.chainPart 2
            (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x) := by
    intro x
    have h := supPart_le_norm_zero_add_varPart_two r
      (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x)
    have hbridge : Submission.PointwiseErgodicTheorems.varPart 2
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x)
        = Work.KMTAreas.A7Hi.chainPart 2
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x) := rfl
    rwa [hbridge] at h
  have hstep : MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.supPart r
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
      p MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ)
          p MeasureTheory.Measure.count
        + MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.chainPart 2
            (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
          p MeasureTheory.Measure.count :=
    (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) hpoint).trans
      (Work.KMTAreas.A7.eLpNorm_add_le_ennreal
        (u := fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ)
        (v := fun x : ℤ => Work.KMTAreas.A7Hi.chainPart 2
            (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
        (le_of_lt hp) (ne_of_lt hptop) (μ := MeasureTheory.Measure.count))
  have hfirst : MeasureTheory.eLpNorm (fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ)
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal CS * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    have h := hSb l₁ (-(m₀ : ℤ)) hgoodS f
    rw [hpeq] at h
    have h0 : Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f
        = Work.KMTContract.kmtProj ρ l₁ (-(m₀ : ℤ)) f := by
      funext y
      simp only [Work.KMTAreas.A7Hi.lpf]
      norm_num
    rw [eLpNorm_enorm_eq' hpne0 hpnetop, h0]
    exact h
  have hsecond := hCb l₁ m₀ hgoodC f
  have hCS0 : (0 : ℝ) ≤ CS := hCSpos.le
  have hCC0 : (0 : ℝ) ≤ CC := hCCpos.le
  have hl0 : (0 : ℝ) ≤ (l₁ : ℝ) := Nat.cast_nonneg l₁
  refine hstep.trans ?_
  calc MeasureTheory.eLpNorm (fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ)
          p MeasureTheory.Measure.count
        + MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.chainPart 2
            (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
          p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal CS * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
        + ENNReal.ofReal CC * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count :=
        add_le_add hfirst hsecond
    _ = ENNReal.ofReal (CS + CC) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
        rw [← add_mul, ← ENNReal.ofReal_add hCS0 hCC0]
    _ ≤ ENNReal.ofReal ((CS + CC) * (1 + (l₁ : ℝ)) ^ 2)
          * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
        refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
        have h1 : (1 : ℝ) ≤ (1 + (l₁ : ℝ)) ^ 2 := by nlinarith [hl0]
        have h0 : (0 : ℝ) ≤ CS + CC := by linarith
        nlinarith [h1, h0]

/-- **The two-point chain at an arbitrary exponent `≥ 2`.**  For every `r ≥ 2` and every
`r₁ : ℝ≥0`, the values-supremum is dominated by the first value plus the *chain* term at exponent
`r` (the `A7Hi` normalisation of the chain functional, definitionally the same as
`PointwiseErgodicTheorems.varPart`).  Any exponent `r > 2` will do — which is what the fleet's
chain crux `A7JSW.chainPartSqFunPos` / `A7HiRep.chainPartSqFunPos` provides. -/
lemma supPart_le_norm_zero_add_chainPart (r₁ : NNReal) {r : NNReal} (hr : 2 ≤ r) (a : ℕ → ℂ) :
    Work.KMTAreas.A7Hi.supPart r₁ a ≤ ‖a 0‖ₑ + Work.KMTAreas.A7Hi.chainPart r a := by
  refine iSup_le fun m => ?_
  have h := Work.KMTAreas.A7Lpd.enorm_sub_zero_le_varPart (r := r) hr a m
  have hbridge : Submission.PointwiseErgodicTheorems.varPart r a
      = Work.KMTAreas.A7Hi.chainPart r a := rfl
  rw [hbridge] at h
  calc ‖a m‖ₑ = ‖a 0 + (a m - a 0)‖ₑ := by
        congr 1
        ring
    _ ≤ ‖a 0‖ₑ + ‖a m - a 0‖ₑ := enorm_add_le _ _
    _ ≤ ‖a 0‖ₑ + Work.KMTAreas.A7Hi.chainPart r a := add_le_add le_rfl h

/-- **`SupPiece` from the chain crux in the form the fleet states it.**  If for some `r > 2` the
chain part of the low-pass walk is bounded in `ℓᵖ` by an `l`-free constant times the *band square
function* — `Work.KMTAreas.A7JSW.chainPartSqFunPos` / `A7HiRep.chainPartSqFunPos` /
`A7MixedG.chain.Le` / `A7Hi.LowpassChainLe`, on `GoodMajorArcs ρ 2` — then `SupPiece` holds:
two-point chains + the *proved* square-function bound `A7Lpd.bandSquareUnif` (uniform in `l₁`, `m₀`)
+ the *proved* single-scale bound `A7.kmtProj_lp_bound_uniform` and the trivial `1 ≤ (1+l₁)²`. -/
theorem supPiece_of_chainPartSqFun
    (hC : ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r)
      (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
      ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ 2 l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
        MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.chainPart r
            (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
          p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f)
              p MeasureTheory.Measure.count) :
    Work.KMTAreas.A7Hi2.SupPiece := by
  intro ρ hρ hρ1 p hp hptop r
  obtain ⟨CB, hCBpos, hCb⟩ := hC ρ hρ hρ1 3 (by norm_num) p hp hptop
  obtain ⟨CρB, hCρBpos, Cq, hCqpos, hqb⟩ :=
    Work.KMTAreas.A7Lpd.bandSquareUnif ρ hρ hρ1 p hp hptop
  have hp1 : (1 : ℝ) < p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (ne_of_lt hptop)).mpr hp
  obtain ⟨CρS, hCρSpos, CS, hCSpos, hSb⟩ :=
    Work.KMTAreas.A7.kmtProj_lp_bound_uniform ρ hρ hρ1 p.toReal hp1
  have hpne0 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have hpnetop : p ≠ ⊤ := ne_of_lt hptop
  have hpeq : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal hpnetop
  refine ⟨max 2 (max CρB CρS), by positivity, CB * Cq + CS, by positivity, ?_⟩
  intro l₁ m₀ hgood f
  have hgB : Work.Analysis.IonescuWainger.GoodMajorArcs ρ 2 l₁ (-(m₀ : ℤ)) :=
    Work.KMTAreas.A7Hi.goodMajorArcs_mono (C₁ := 2)
      (C₂ := max 2 (max CρB CρS)) (le_max_left _ _) hgood
  have hgBq : Work.Analysis.IonescuWainger.GoodMajorArcs ρ CρB l₁ (-(m₀ : ℤ)) :=
    Work.KMTAreas.A7Hi.goodMajorArcs_mono (C₁ := CρB)
      (C₂ := max 2 (max CρB CρS))
      (le_trans (le_max_left _ _) (le_max_right _ _)) hgood
  have hgS : Work.Analysis.IonescuWainger.GoodMajorArcs ρ CρS l₁ (-(m₀ : ℤ)) :=
    Work.KMTAreas.A7Hi.goodMajorArcs_mono (C₁ := CρS)
      (C₂ := max 2 (max CρB CρS))
      (le_trans (le_max_right _ _) (le_max_right _ _)) hgood
  -- pointwise: supPart ≤ ‖T_0 f‖ + chainPart 3
  have hpoint : ∀ x : ℤ, Work.KMTAreas.A7Hi.supPart r
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x)
      ≤ ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ
        + Work.KMTAreas.A7Hi.chainPart 3
            (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x) :=
    fun x => supPart_le_norm_zero_add_chainPart r (by norm_num) _
  have hstep : MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.supPart r
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
      p MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ)
          p MeasureTheory.Measure.count
        + MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.chainPart 3
            (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
          p MeasureTheory.Measure.count :=
    (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) hpoint).trans
      (Work.KMTAreas.A7.eLpNorm_add_le_ennreal
        (u := fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ)
        (v := fun x : ℤ => Work.KMTAreas.A7Hi.chainPart 3
            (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
        (le_of_lt hp) (ne_of_lt hptop) (μ := MeasureTheory.Measure.count))
  have hfirst : MeasureTheory.eLpNorm (fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ)
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal CS * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    have h := hSb l₁ (-(m₀ : ℤ)) hgS f
    rw [hpeq] at h
    have h0 : Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f
        = Work.KMTContract.kmtProj ρ l₁ (-(m₀ : ℤ)) f := by
      funext y
      simp only [Work.KMTAreas.A7Hi.lpf]
      norm_num
    rw [eLpNorm_enorm_eq' hpne0 hpnetop, h0]
    exact h
  have hchain := hCb l₁ m₀ hgB f
  have hsq := hqb l₁ m₀ hgBq f
  have hCS0 : (0 : ℝ) ≤ CS := hCSpos.le
  have hCB0 : (0 : ℝ) ≤ CB := hCBpos.le
  have hCq0 : (0 : ℝ) ≤ Cq := hCqpos.le
  have hl0 : (0 : ℝ) ≤ (l₁ : ℝ) := Nat.cast_nonneg l₁
  have hchainF : MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.chainPart 3
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
      p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (CB * Cq) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    refine hchain.trans ?_
    refine (mul_le_mul_of_nonneg_left hsq bot_le).trans (le_of_eq ?_)
    rw [← mul_assoc, ← ENNReal.ofReal_mul hCB0]
  refine hstep.trans ?_
  calc MeasureTheory.eLpNorm (fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ)
          p MeasureTheory.Measure.count
        + MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.chainPart 3
            (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
          p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal CS * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
        + ENNReal.ofReal (CB * Cq) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count :=
        add_le_add hfirst hchainF
    _ = ENNReal.ofReal (CS + CB * Cq) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
        rw [← add_mul, ← ENNReal.ofReal_add hCS0 (mul_nonneg hCB0 hCq0)]
    _ ≤ ENNReal.ofReal ((CB * Cq + CS) * (1 + (l₁ : ℝ)) ^ 2)
          * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
        refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
        have h1 : (1 : ℝ) ≤ (1 + (l₁ : ℝ)) ^ 2 := by nlinarith [hl0]
        have h0 : (0 : ℝ) ≤ CS + CB * Cq := by positivity
        nlinarith [h1, h0]

/-! ## The deep/shallow split of the walk (the decimation cut)

Session 2 (`NOTES_A7Hi2_supPieceClean_SESSION2.md`) found the exact structure of the maximal over
the *frequency scale* `m ↦ Π_{≤l₁,≤−(m₀+m)}`.  Write `Q := Work.Analysis.IonescuWainger.iwQl ρ l₁` for the common denominator
of `(ℚ/ℤ)_{≤l₁} = iwArithFreqs ρ l₁` and cut the walk at the *level*

  `cutLevel ρ l₁ := Nat.clog 2 (3 Q) + 2`.

* **Deep range** `cutLevel ρ l₁ ≤ m₀ + m`: here `2^{m₀+m} > 3Q`, so the bump `η_{≤−(m₀+m)}` is
  *narrower* than the lattice spacing `1/Q` and the Magyar–Stein–Wainger **sampling (decimation)
  principle** applies.  The tree's `Work.KMTAreas.A7Hi.lpf_decim_fact` factors the operator as
  `Π_{≤l₁,≤−(m₀+m)} = K^{dec}_{m₀+m} ∘ Π_{≤l₁,≤−C₀}` with a *fixed* course projection
  `Π_{≤l₁,≤−C₀}`, and the decimated kernels `K^{dec}_L` are lattice dilation averages on the
  sublattice `Qℤ`; their maximal over `L` is the (sparse) Hardy–Littlewood maximal function of the
  decimated sequences, which is `ℓᵖ`-bounded with an **absolute** constant.  Hence the deep range
  costs no `l₁`-loss at all (`Work.KMTAreas.A7Hi2.supDeepLe`).
* **Shallow range** `m₀ + m < cutLevel ρ l₁`: here the bump is wider than `1/Q` and the decimation
  does not apply — this is the paper's "small-scale" regime, in which the paper uses the
  Ionescu–Wainger multiplier theorem for *linear* multipliers and does **not** take a maximal over
  the frequency scale.  The estimate needed here is `Work.KMTAreas.A7Hi2.supShallowLe`; it is the
  exact remaining content of `SupPiece`. -/

/-- **The pointwise deep/shallow split.**  The values supremum of the walk is the supremum of its
shallow-range part and its deep-range part. -/
lemma supPart_le_shallow_sup_deep (ρ : ℝ) (l₁ m₀ : ℕ) (f : ℤ → ℂ) (r : NNReal) (x : ℤ) :
    Work.KMTAreas.A7Hi.supPart r (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x)
      ≤ (⨆ (n : ℕ) (_ : m₀ + n < cutLevel ρ l₁),
            ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x‖ₑ)
        ⊔ (⨆ (n : ℕ) (_ : cutLevel ρ l₁ ≤ m₀ + n),
            ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x‖ₑ) := by
  refine iSup_le fun n => ?_
  by_cases h : m₀ + n < cutLevel ρ l₁
  · exact (le_iSup₂ (f := fun n : ℕ => fun _ : m₀ + n < cutLevel ρ l₁ =>
        ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x‖ₑ) n h).trans le_sup_left
  · exact (le_iSup₂ (f := fun n : ℕ => fun _ : cutLevel ρ l₁ ≤ m₀ + n =>
        ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x‖ₑ) n (not_lt.mp h)).trans le_sup_right

/-- **`SupPiece` from the deep and the shallow bound.**  If the maximal function of the *deep* part
of the walk (levels `m₀+m ≥ cutLevel ρ l₁`) is bounded by an `l₁`-free constant and the maximal
function of the *shallow* part (levels `m₀+m < cutLevel ρ l₁`) is bounded by `C(1+l₁)²`, then
`SupPiece` holds.  This is the exact decomposition of the target; see
`NOTES_A7Hi2_supPieceClean_SESSION2.md`. -/
theorem supPiece_of_supDeep_supShallow
    (hDeep : ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
      ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
        MeasureTheory.eLpNorm (fun x : ℤ => ⨆ (n : ℕ) (_ : cutLevel ρ l₁ ≤ m₀ + n),
            ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x‖ₑ)
          p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
    (hShallow : ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
      ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
        MeasureTheory.eLpNorm (fun x : ℤ => ⨆ (n : ℕ) (_ : m₀ + n < cutLevel ρ l₁),
            ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x‖ₑ)
          p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C * (1 + (l₁ : ℝ)) ^ 2)
              * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count) :
    Work.KMTAreas.A7Hi2.SupPiece := by
  intro ρ hρ hρ1 p hp hptop r
  obtain ⟨CρD, hCρD, CD, hCD, hD⟩ := hDeep ρ hρ hρ1 p hp hptop
  obtain ⟨CρS, hCρS, CS, hCS, hS⟩ := hShallow ρ hρ hρ1 p hp hptop
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have hpT : p ≠ ⊤ := ne_of_lt hptop
  refine ⟨max CρD CρS, lt_max_of_lt_left hCρD, CD + CS, by positivity, ?_⟩
  intro l₁ m₀ hgood f
  have hgD : Work.Analysis.IonescuWainger.GoodMajorArcs ρ CρD l₁ (-(m₀ : ℤ)) :=
    Work.KMTAreas.A7Hi.goodMajorArcs_mono (C₁ := CρD) (C₂ := max CρD CρS)
      (le_max_left _ _) hgood
  have hgS : Work.Analysis.IonescuWainger.GoodMajorArcs ρ CρS l₁ (-(m₀ : ℤ)) :=
    Work.KMTAreas.A7Hi.goodMajorArcs_mono (C₁ := CρS) (C₂ := max CρD CρS)
      (le_max_right _ _) hgood
  have hpoint : ∀ x : ℤ, Work.KMTAreas.A7Hi.supPart r
        (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x)
      ≤ (fun x : ℤ => (⨆ (n : ℕ) (_ : m₀ + n < cutLevel ρ l₁),
              ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x‖ₑ)
            + (⨆ (n : ℕ) (_ : cutLevel ρ l₁ ≤ m₀ + n),
              ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x‖ₑ)) x := by
    intro x
    refine (supPart_le_shallow_sup_deep ρ l₁ m₀ f r x).trans ?_
    refine sup_le ?_ ?_
    · exact le_add_right le_rfl
    · exact le_add_left le_rfl
  have hstep : MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.supPart r
        (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x))
      p MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => (⨆ (n : ℕ) (_ : m₀ + n < cutLevel ρ l₁),
              ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x‖ₑ)
            + (⨆ (n : ℕ) (_ : cutLevel ρ l₁ ≤ m₀ + n),
              ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x‖ₑ))
          p MeasureTheory.Measure.count :=
    MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) hpoint
  have hsplit : MeasureTheory.eLpNorm (fun x : ℤ => (⨆ (n : ℕ) (_ : m₀ + n < cutLevel ρ l₁),
          ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x‖ₑ)
        + (⨆ (n : ℕ) (_ : cutLevel ρ l₁ ≤ m₀ + n),
          ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x‖ₑ))
      p MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => ⨆ (n : ℕ) (_ : m₀ + n < cutLevel ρ l₁),
            ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x‖ₑ)
          p MeasureTheory.Measure.count
        + MeasureTheory.eLpNorm (fun x : ℤ => ⨆ (n : ℕ) (_ : cutLevel ρ l₁ ≤ m₀ + n),
            ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x‖ₑ)
          p MeasureTheory.Measure.count :=
    Work.KMTAreas.A7.eLpNorm_add_le_ennreal (le_of_lt hp) hpT (μ := MeasureTheory.Measure.count)
  refine hstep.trans (hsplit.trans ?_)
  have hsh := hS l₁ m₀ hgS f
  have hdp := hD l₁ m₀ hgD f
  have hCD0 : (0 : ℝ) ≤ CD := hCD.le
  have hCS0 : (0 : ℝ) ≤ CS := hCS.le
  have hl1 : (0 : ℝ) ≤ (l₁ : ℝ) := Nat.cast_nonneg l₁
  have h1 : (1 : ℝ) ≤ (1 + (l₁ : ℝ)) ^ 2 := by nlinarith
  refine (add_le_add hsh hdp).trans ?_
  rw [← add_mul, ← ENNReal.ofReal_add (mul_nonneg hCS0 (by positivity)) hCD0]
  refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
  nlinarith [h1, hCS0, hCD0]

/-! ## The shallow range for the canonical (bounded) heights

For `l₁ ≤ Work.Analysis.IonescuWainger.iwC0 ρ` the admissible-denominator set is the *canonical* `Work.Analysis.IonescuWainger.iwP ρ l₁ = [2^{l₁}]`, and
`Work.Analysis.IonescuWainger.iwC0 ρ = O(1/ρ)` is a **constant**, so there are only finitely many heights `l₁` to consider and the
cut level `cutLevel ρ l₁` is bounded by the constant `cutLevel ρ (Work.Analysis.IonescuWainger.iwC0 ρ)`.  Consequently the
shallow range has at most `cutLevel ρ (Work.Analysis.IonescuWainger.iwC0 ρ) + 1` levels, and the elementary domination
`⨆_{n shallow} ‖T_n f x‖ₑ ≤ ∑_{n < cutLevel ρ (Work.Analysis.IonescuWainger.iwC0 ρ) + 1} ‖T_n f x‖ₑ`, together with the
`l₁`-free single-scale bound `Work.KMTAreas.A7.kmtProj_lp_bound_uniform` and Minkowski, gives the
shallow estimate with a constant absorbing the number of levels.  **So the shallow range is only
open in the concrete IW regime `l₁ > Work.Analysis.IonescuWainger.iwC0 ρ`.** -/

/-- `Work.Analysis.IonescuWainger.iwQl ρ l ∣ Work.Analysis.IonescuWainger.iwQl ρ (Work.Analysis.IonescuWainger.iwC0 ρ)` on the canonical range `l ≤ Work.Analysis.IonescuWainger.iwC0 ρ` (where `Work.Analysis.IonescuWainger.iwP ρ l = [2^l]`). -/
lemma iwQl_dvd_iwC0 {ρ : ℝ} {l : ℕ} (hl : l ≤ Work.Analysis.IonescuWainger.iwC0 ρ) : Work.Analysis.IonescuWainger.iwQl ρ l ∣ Work.Analysis.IonescuWainger.iwQl ρ (Work.Analysis.IonescuWainger.iwC0 ρ) := by
  show (Work.Analysis.IonescuWainger.iwP ρ l).lcm id ∣ (Work.Analysis.IonescuWainger.iwP ρ (Work.Analysis.IonescuWainger.iwC0 ρ)).lcm id
  simp only [Work.Analysis.IonescuWainger.iwP, if_pos hl, if_pos le_rfl]
  refine Finset.lcm_mono ?_
  intro a ha
  rw [Finset.mem_Icc] at ha ⊢
  exact ⟨ha.1, le_trans ha.2 (Nat.pow_le_pow_right (by norm_num) hl)⟩

/-- The cut level is bounded by the constant `cutLevel ρ (Work.Analysis.IonescuWainger.iwC0 ρ)` on the canonical range. -/
lemma cutLevel_le_iwC0 {ρ : ℝ} {l : ℕ} (hl : l ≤ Work.Analysis.IonescuWainger.iwC0 ρ) :
    cutLevel ρ l ≤ cutLevel ρ (Work.Analysis.IonescuWainger.iwC0 ρ) := by
  have hpos : 0 < Work.Analysis.IonescuWainger.iwQl ρ (Work.Analysis.IonescuWainger.iwC0 ρ) := Work.Analysis.IonescuWainger.iwQl_pos
  have hle : Work.Analysis.IonescuWainger.iwQl ρ l ≤ Work.Analysis.IonescuWainger.iwQl ρ (Work.Analysis.IonescuWainger.iwC0 ρ) := Nat.le_of_dvd hpos (Work.KMTAreas.A7Hi2.iwQl_dvd_iwC0 hl)
  unfold cutLevel
  exact Nat.add_le_add_right (Nat.clog_mono_right 2 (Nat.mul_le_mul_left 3 hle)) 2

/-! ## The target

The statement is the one requested (name and statement unchanged).  It now follows from the two
halves of the deep/shallow split:

* the **deep** range `cutLevel ρ l₁ ≤ m₀ + m` is handled by the Magyar–Stein–Wainger decimation
  factorisation `Work.KMTAreas.A7Hi.lpf_decim_fact` and the lattice (sparse) Hardy–Littlewood
  maximal function, with an **absolute** constant (`Work.KMTAreas.A7Hi2.supDeepLe`);
* the **shallow** range `m₀ + m < cutLevel ρ l₁` is a *truncated* range of `≈ cutLevel ρ l₁` levels,
  and the one-dimensional Rademacher–Men'shov inequality
  `V²(a) ≤ 2 ∑_{m ≤ log₂ K} incLp 2 K (2^m) a` bounds its variation by a sum of `log₂ K + 1 = O(l₁)`
  *dyadic block square functions*, each of which is `ℓᵖ`-bounded with an `l₁`-free constant by
  `Work.KMTAreas.A7Lpd.singleChain_blockSqSum_le` (`Work.KMTAreas.A7Hi2.supShallowLe`).  The
  logarithmic loss in the *truncation* is affordable exactly because
  `log₂ (cutLevel ρ l₁) = O(l₁)` (`Work.Analysis.IonescuWainger.iwQl_le`), and this is what the
  deep/shallow split buys over the (unbounded) full-range maximal estimate.

Everything is axiom-clean (`#print axioms` uses only `propext`, `Classical.choice`, `Quot.sound`). -/
theorem supPieceClean : Work.KMTAreas.A7Hi2.SupPiece :=
  supPiece_of_supDeep_supShallow
    (fun ρ hρ hρ1 p hp hptop => Work.KMTAreas.A7Hi2.supDeepLe ρ hρ hρ1 p hp hptop)
    (fun ρ hρ hρ1 p hp hptop => Work.KMTAreas.A7Hi2.supShallowLe ρ hρ hρ1 p hp hptop)

end Work.KMTAreas.A7Hi2
