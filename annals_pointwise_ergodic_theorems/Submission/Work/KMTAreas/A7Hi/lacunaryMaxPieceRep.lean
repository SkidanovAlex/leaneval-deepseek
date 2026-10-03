import Mathlib
import Submission.Work.KMTAreas.A7Hi2.lacunaryMaxPieceProved
import Submission.Work.KMTAreas.A7.fiberOpCum_lp_goodArcs
import Submission.Work.KMTAreas.A7Hi.kernelDecimation
import Submission.Port.Aesm

set_option autoImplicit false

namespace Work.KMTAreas.A7Hi

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-- **The reduction of the target to the band-pass (`varPart`) crux.**

The *supremum over `K` of the partial sums of the annuli* of the low-pass family
`lpf ρ l₁ m₀ k = kmtProj ρ l₁ (-(m₀ + k))` is dominated pointwise by the variation `varPart 3` of
the walk `k ↦ lpf ρ l₁ m₀ k f` — this is `Work.KMTAreas.A7Lpd.iSup_partialSum_le_varPart`
(proved, via the two-point chain `0 → K`).  Consequently, the *Lépingle / Jones–Seeger–Wright*
estimate `varPart 3 ≤ C · sqFun` for this band-pass family gives the target.

Note the sign: the tree's `iSup_partialSum_le_varPart` is stated for the increments
`T_i - T_{i+1}`, while the target uses `T_{i+1} - T_i`; the two finite sums are negatives of one
another, so their `enorm`s agree. -/
theorem lacunaryMaxPieceRep_of_varPartSqFun (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤)
    (hvar : ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (l₁ m₀ : ℕ),
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
        MeasureTheory.eLpNorm (fun x : ℤ => Submission.PointwiseErgodicTheorems.varPart 3
            (fun k : ℕ => Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + (k : ℤ))) f x))
          p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f)
            p MeasureTheory.Measure.count) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
          (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
            - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f)
          p MeasureTheory.Measure.count
        + ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  obtain ⟨Cρ, hCρ, C, hC, hvar'⟩ := hvar
  refine ⟨Cρ, hCρ, C, hC, ?_⟩
  intro l₁ m₀ hgood f
  have hp0 : p ≠ 0 := (lt_trans zero_lt_one hp).ne'
  have hpT : p ≠ ⊤ := ne_of_lt hptop
  -- the two partial sums of the increments are negatives of one another
  have hsum : ∀ (K : ℕ) (x : ℤ), (∑ i ∈ Finset.range K,
        (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
          - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))
      = -(∑ i ∈ Finset.range K,
          (Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + ((i : ℕ) : ℤ))) f x
            - Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + (((i + 1 : ℕ)) : ℤ))) f x)) := by
    intro K x
    rw [show (∑ i ∈ Finset.range K,
          (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
            - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))
        = ∑ i ∈ Finset.range K,
            (-(Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + ((i : ℕ) : ℤ))) f x
              - Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + (((i + 1 : ℕ)) : ℤ))) f x))
        from Finset.sum_congr rfl (fun i _ => by
          simp only [Work.KMTAreas.A7Hi.lpf]; ring)]
    rw [Finset.sum_neg_distrib]
  have hLHS : (fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
        (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
          - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
      = (fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
          (Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + ((i : ℕ) : ℤ))) f x
            - Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + (((i + 1 : ℕ)) : ℤ))) f x))‖ₑ) := by
    funext x
    refine iSup_congr fun K => ?_
    rw [hsum K x, enorm_neg]
  rw [hLHS]
  have hmono := Work.KMTAreas.A7.eLpNorm_mono_ennreal
    (u := fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
        (Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + ((i : ℕ) : ℤ))) f x
          - Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + (((i + 1 : ℕ)) : ℤ))) f x))‖ₑ)
    (v := fun x : ℤ => Submission.PointwiseErgodicTheorems.varPart 3
        (fun k : ℕ => Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + (k : ℤ))) f x))
    (fun x => Work.KMTAreas.A7Lpd.iSup_partialSum_le_varPart ρ l₁ m₀ f (by norm_num) x)
    hp0 hpT (μ := MeasureTheory.Measure.count)
  refine (hmono.trans (hvar' l₁ m₀ hgood f)).trans ?_
  exact self_le_add_right _ _

/-- **The target's integrand is pointwise dominated by `varPart 3` of the walk `k ↦ lpf k f`.**

The sign bookkeeping `Σ_{i<K}(T_{i+1} - T_i) = -Σ_{i<K}(T_i - T_{i+1})` (already used above)
together with `Work.KMTAreas.A7Lpd.iSup_partialSum_le_varPart` (the two-point chain
`0 → K`). -/
theorem partialSumSup_le_varPart (ρ : ℝ) (l₁ m₀ : ℕ) (f : ℤ → ℂ) (x : ℤ) :
    (⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
        (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
          - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
      ≤ Submission.PointwiseErgodicTheorems.varPart 3
          (fun k : ℕ => Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + (k : ℤ))) f x) := by
  have hsum : ∀ (K : ℕ), (∑ i ∈ Finset.range K,
        (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
          - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))
      = -(∑ i ∈ Finset.range K,
          (Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + ((i : ℕ) : ℤ))) f x
            - Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + (((i + 1 : ℕ)) : ℤ))) f x)) := by
    intro K
    rw [show (∑ i ∈ Finset.range K,
          (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
            - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))
        = ∑ i ∈ Finset.range K,
            (-(Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + ((i : ℕ) : ℤ))) f x
              - Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + (((i + 1 : ℕ)) : ℤ))) f x))
        from Finset.sum_congr rfl (fun i _ => by simp only [Work.KMTAreas.A7Hi.lpf]; ring)]
    rw [Finset.sum_neg_distrib]
  have hfun : (fun K : ℕ => ‖(∑ i ∈ Finset.range K,
        (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
          - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
      = (fun K : ℕ => ‖(∑ i ∈ Finset.range K,
          (Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + ((i : ℕ) : ℤ))) f x
            - Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + (((i + 1 : ℕ)) : ℤ))) f x))‖ₑ) := by
    funext K
    rw [hsum K, enorm_neg]
  rw [hfun]
  exact Work.KMTAreas.A7Lpd.iSup_partialSum_le_varPart ρ l₁ m₀ f (by norm_num) x

/-- **The target from the `l`-free variational estimate** (no square function on the right).

This is the sharpest form of the reduction available in the tree's vocabulary: the paper's
low-frequency statement `(lin-1)`/`(lin-2)`, i.e. `Work.KMTAreas.A7Hi.LowpassVar` *without* the
`(1+l₁)²` loss (equivalently `A7Hi.LowpassVar` with an `l`-free constant).  It is *weaker* as a
hypothesis than `lacunaryMaxPieceRep_of_varPartSqFun`'s (the `‖f‖_{ℓᵖ}` term is not controlled by
the square function: the DC part of `f` is invisible to `sqFun`), so any future proof of the
`l`-free variational bound feeds the target through this lemma. -/
theorem lacunaryMaxPieceRep_of_lFreeVarPart (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤)
    (hvar : ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (l₁ m₀ : ℕ),
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
        MeasureTheory.eLpNorm (fun x : ℤ => Submission.PointwiseErgodicTheorems.varPart 3
            (fun k : ℕ => Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + (k : ℤ))) f x))
          p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
          (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
            - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f)
          p MeasureTheory.Measure.count
        + ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  obtain ⟨Cρ, hCρ, C, hC, hvar'⟩ := hvar
  refine ⟨Cρ, hCρ, C, hC, ?_⟩
  intro l₁ m₀ hgood f
  have hp0 : p ≠ 0 := (lt_trans zero_lt_one hp).ne'
  have hpT : p ≠ ⊤ := ne_of_lt hptop
  have hmono := Work.KMTAreas.A7.eLpNorm_mono_ennreal
    (u := fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
        (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
          - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
    (v := fun x : ℤ => Submission.PointwiseErgodicTheorems.varPart 3
        (fun k : ℕ => Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + (k : ℤ))) f x))
    (fun x => partialSumSup_le_varPart ρ l₁ m₀ f x) hp0 hpT (μ := MeasureTheory.Measure.count)
  refine (hmono.trans (hvar' l₁ m₀ hgood f)).trans ?_
  have hstep : (0 : ℝ≥0∞) + ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C *
            MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f) p MeasureTheory.Measure.count
          + ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count :=
    add_le_add bot_le le_rfl
  simpa only [zero_add] using hstep

/-- `‖ ‖g‖ₑ ‖_p = ‖g‖_p` (`p ≠ 0`, `p ≠ ⊤`) for `ℤ` with the counting measure. -/
private theorem eLpNorm_enorm_eq' {g : ℤ → ℂ} {p : ENNReal} (h0 : p ≠ 0) (ht : p ≠ ⊤) :
    MeasureTheory.eLpNorm (fun x : ℤ => ‖g x‖ₑ) p MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm g p MeasureTheory.Measure.count := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) h0 ht,
    MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) h0 ht]
  simp only [enorm_eq_self]

/-- **The target from the `l`-free values-maximal bound** (the form in which the tree states the
Ionescu--Wainger maximal theorem: `Work.KMTAreas.A7G.maximalLowpass`, `A7Hi2.SupPiece`,
`A7Hi.LowpassMaximal`).

Hypothesis: `∃ Cρ > 0, ∃ C > 0, ∀ l₁ m₀` with good major arcs, `∀ f`,
`‖ sup_m |Π_{≤l₁,≤−(m₀+m)} f| ‖_{ℓᵖ} ≤ C ‖f‖_{ℓᵖ}` — i.e. the maximal estimate with an `l₁`-*free*
constant, the statement the paper obtains from "Lépingle's inequality plus a standard square
function argument", whose `⟨l⟩`-lossy version is the tree's `maximalLowpass`.

The reduction is the elementary telescoping `sup_K |T_K f − T_0 f| ≤ |T_0 f| + sup_m |T_m f|`
together with the *proved* `l`-free single-scale bound `A7.kmtProj_lp_bound_uniform` at `T_0` and
the trivial `‖f‖_{ℓᵖ} ≤ ‖sqFun‖_{ℓᵖ} + ‖f‖_{ℓᵖ}`.  (It is an equivalence: the converse direction
is the same telescoping.) -/
theorem lacunaryMaxPieceRep_of_lFreeValuesMaximal (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤)
    (hmax : ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (l₁ m₀ : ℕ),
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
        MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.supPart 3
            (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
          p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
          (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
            - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f)
          p MeasureTheory.Measure.count
        + ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  obtain ⟨CρM, hCρM, CM, hCM, hmax'⟩ := hmax
  have hp1 : (1 : ℝ) < p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (ne_of_lt hptop)).mpr hp
  obtain ⟨CρS, hCρS, CS, hCS, hsingle⟩ :=
    Work.KMTAreas.A7.kmtProj_lp_bound_uniform ρ hρ hρ1 p.toReal hp1
  have hp0 : p ≠ 0 := (lt_trans zero_lt_one hp).ne'
  have hpT : p ≠ ⊤ := ne_of_lt hptop
  refine ⟨max CρM CρS, lt_max_of_lt_left hCρM, CM + CS, by positivity, ?_⟩
  intro l₁ m₀ hgood f
  have hgoodM : Work.Analysis.IonescuWainger.GoodMajorArcs ρ CρM l₁ (-(m₀ : ℤ)) :=
    goodMajorArcs_mono (C₁ := CρM) (C₂ := max CρM CρS) (le_max_left _ _) hgood
  have hgoodS : Work.Analysis.IonescuWainger.GoodMajorArcs ρ CρS l₁ (-(m₀ : ℤ)) :=
    goodMajorArcs_mono (C₁ := CρS) (C₂ := max CρM CρS) (le_max_right _ _) hgood
  -- ## the pointwise telescoping
  have hpoint : ∀ x : ℤ, (⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
        (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
          - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
      ≤ ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ
        + Work.KMTAreas.A7Hi.supPart 3 (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x) := by
    intro x
    refine iSup_le fun K => ?_
    have htel : (∑ i ∈ Finset.range K,
          (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
            - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))
        = Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ K f x - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x :=
      Finset.sum_range_sub (fun i : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x) K
    rw [htel]
    have hsub : ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ K f x
          - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ
        ≤ ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ K f x‖ₑ
          + ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ := enorm_sub_le
    refine hsub.trans ?_
    calc ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ K f x‖ₑ
          + ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ
        = ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ
          + ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ K f x‖ₑ := add_comm _ _
      _ ≤ ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ
          + Work.KMTAreas.A7Hi.supPart 3
              (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x) :=
          add_le_add le_rfl
            (le_iSup (fun m : ℕ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x‖ₑ) K)
  have hstep : MeasureTheory.eLpNorm (fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
        (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
          - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ) p MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ)
          p MeasureTheory.Measure.count
        + MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.supPart 3
            (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
          p MeasureTheory.Measure.count := by
    have hmono := Work.KMTAreas.A7.eLpNorm_mono_ennreal
      (u := fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
          (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
            - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
      (v := fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ
          + Work.KMTAreas.A7Hi.supPart 3 (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
      (fun x => hpoint x) hp0 hpT (μ := MeasureTheory.Measure.count)
    have hsplit : (fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ
          + Work.KMTAreas.A7Hi.supPart 3 (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
        = (fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ)
          + (fun x : ℤ => Work.KMTAreas.A7Hi.supPart 3
              (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x)) := by
      funext x; rfl
    have hadd := Work.KMTAreas.A7.eLpNorm_add_le_ennreal
      (u := fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ)
      (v := fun x : ℤ => Work.KMTAreas.A7Hi.supPart 3
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
      (le_of_lt hp) hpT (μ := MeasureTheory.Measure.count)
    exact hmono.trans (hsplit ▸ hadd)
  -- ## the two bounds
  have hT0eq : Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f
      = Work.KMTContract.kmtProj ρ l₁ (-(m₀ : ℤ)) f := by
    funext x
    simp only [Work.KMTAreas.A7Hi.lpf, Nat.cast_zero, add_zero]
  have hT0 : MeasureTheory.eLpNorm (fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ)
      p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal CS * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    have h := hsingle l₁ (-(m₀ : ℤ)) hgoodS f
    rw [show ENNReal.ofReal p.toReal = p from ENNReal.ofReal_toReal (ne_of_lt hptop)] at h
    rw [hT0eq, eLpNorm_enorm_eq' hp0 hpT]
    exact h
  have hSup := hmax' l₁ m₀ hgoodM f
  refine (hstep.trans (add_le_add hT0 hSup)).trans ?_
  have hsum : ENNReal.ofReal CS * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
        + ENNReal.ofReal CM * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (CM + CS) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    rw [← add_mul, ← ENNReal.ofReal_add hCS.le hCM.le,
      show CS + CM = CM + CS from by ring]
  refine hsum.trans ?_
  have hfin : ENNReal.ofReal (CM + CS) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (CM + CS) *
            MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f) p MeasureTheory.Measure.count
          + ENNReal.ofReal (CM + CS) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    calc ENNReal.ofReal (CM + CS) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
        = (0 : ℝ≥0∞) + ENNReal.ofReal (CM + CS) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count :=
          (zero_add _).symm
      _ ≤ ENNReal.ofReal (CM + CS) *
              MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f) p MeasureTheory.Measure.count
            + ENNReal.ofReal (CM + CS) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count :=
          add_le_add bot_le le_rfl
  exact hfin

/-- **Monotonicity of the square-function side in the vector index `N`** (the third trivial case of
the vector-valued Men'shov statement): padding a family `f : ℤ → Fin N → ℂ` by a further component
`g : ℤ → Fin (N+1) → ℂ` with `g n (Fin.castSucc c) = f n c` does *not decrease* the `ℓ²`-square
function of the annuli.  This is the bookkeeping that makes the `N`-uniformity of
`Work.KMTAreas.A7Hi.menshovVectorFin` meaningful: the square-function side grows with `N`, so a
constant cannot be obtained by reducing large `N` to small `N`. -/
theorem sqSum_mono_index (ρ : ℝ) (m₀ : ℕ) {N : ℕ} (f : ℤ → Fin N → ℂ)
    (g : ℤ → Fin (N + 1) → ℂ) (hgf : ∀ n c, g n (Fin.castSucc c) = f n c) (n : ℤ) :
    (∑ c : Fin N, ∑' i : ℕ,
        ‖(lpf ρ 0 m₀ (i + 1) (fun n : ℤ => f n c) n
          - lpf ρ 0 m₀ i (fun n : ℤ => f n c) n)‖ₑ ^ (2 : ℝ))
      ≤ (∑ c : Fin (N + 1), ∑' i : ℕ,
        ‖(lpf ρ 0 m₀ (i + 1) (fun n : ℤ => g n c) n
          - lpf ρ 0 m₀ i (fun n : ℤ => g n c) n)‖ₑ ^ (2 : ℝ)) := by
  rw [Fin.sum_univ_castSucc]
  refine le_trans (Finset.sum_le_sum fun c _ => ?_) (le_add_of_nonneg_right bot_le)
  have h : (fun n : ℤ => g n (Fin.castSucc c)) = fun n : ℤ => f n c := funext fun n => hgf n c
  rw [h]

/-- **The trivial pointwise bound** `|Σ_{i<K} Δ_i f| ≤ Σ_{i<K} |Δ_i f|` for the annuli (the
estimate whose failure to be summable in `i` is the reason the Men'shov input is needed). -/
theorem partialSum_enorm_le_sum_enorm (ρ : ℝ) (m₀ K : ℕ) (f : ℤ → ℂ) (n : ℤ) :
    ‖(∑ i ∈ Finset.range K,
        (lpf ρ 0 m₀ (i + 1) f n - lpf ρ 0 m₀ i f n))‖ₑ
      ≤ ∑ i ∈ Finset.range K,
          ‖(lpf ρ 0 m₀ (i + 1) f n - lpf ρ 0 m₀ i f n)‖ₑ :=
  enorm_sum_le _ _

/-! ## Trivial case `N = 0` of the vector-valued Men'shov statement

`Fin 0` is empty, so both sides of `Work.KMTAreas.A7Hi.menshovVectorFin` vanish: the pointwise
`ℓ²(Fin 0)`-norm of any vector is `0`. -/

/-- The `N = 0` case of the vector-valued Men'shov statement: the `ℓ²(Fin 0)`-valued sup of the
partial sums of the annuli vanishes pointwise. -/
theorem menshovVectorFin_zero_index_pointwise (ρ : ℝ) (m₀ : ℕ) (f : ℤ → Fin 0 → ℂ) (n : ℤ) :
    (⨆ K : ℕ, (∑ c : Fin 0, ‖(∑ i ∈ Finset.range K,
        (lpf ρ 0 m₀ (i + 1) (fun n : ℤ => f n c) n
          - lpf ρ 0 m₀ i (fun n : ℤ => f n c) n))‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) = 0 := by
  simp

/-! ## Substep (i) of the vector-valued Men'shov chapter: `ρ` is vestigial at `l₁ = 0`

For `l₁ = 0` the admissible-denominator set is `P_{≤0} = [2^0] = {1}`, so the arithmetic frequency
set is the singleton `(ℚ/ℤ)_{≤0} = {0}` — *independently of `ρ`*.  Consequently the low-pass family
`lpf ρ 0 m₀ m` (and every quantity built from it, in particular `sqFun ρ 0 m₀`) does not depend on
`ρ` at all, and the `l₁ = 0` piece of the Men'shov chapter carries no arithmetic content (it is a
plain Littlewood–Paley statement).  This is the `depends_on`-free first substep of
`Work.KMTAreas.A7Hi.menshovVectorFin`. -/

/-- `P_{≤0} = {1}` (the condition `l ≤ iwC0 ρ` holds at `l = 0`, and `2^0 = 1`). -/
theorem iwP_zero (ρ : ℝ) : Work.Analysis.IonescuWainger.iwP ρ 0 = ({1} : Finset ℕ) := by
  unfold Work.Analysis.IonescuWainger.iwP
  rw [if_pos (Nat.zero_le _), pow_zero, Finset.Icc_self]

/-- `(ℚ/ℤ)_{≤0}` is independent of `ρ`: both sides are the biUnion of `Finset.range 1` over the
denominator `1`. -/
theorem iwArithFreqs_zero_eq (ρ ρ' : ℝ) :
    Work.Analysis.IonescuWainger.iwArithFreqs ρ 0
      = Work.Analysis.IonescuWainger.iwArithFreqs ρ' 0 := by
  unfold Work.Analysis.IonescuWainger.iwArithFreqs
  rw [iwP_zero ρ, iwP_zero ρ']

/-- Reduction of a frequency set to the singleton `{0}`: `iwSymbolSet {0} Φ = Φ`. -/
theorem iwSymbolSet_singleton_zero (Φ : Work.Analysis.IonescuWainger.Circle → ℂ) :
    Work.Analysis.IonescuWainger.iwSymbolSet ({0} : Finset Work.Analysis.IonescuWainger.Circle)
        Φ = Φ := by
  funext ξ
  simp [Work.Analysis.IonescuWainger.iwSymbolSet]

/-- **`ρ`-independence of the `l₁ = 0` Ionescu–Wainger projection.** -/
theorem kmtProj_zero_rho_indep (ρ ρ' : ℝ) (k : ℤ) (f : ℤ → ℂ) :
    Work.KMTContract.kmtProj ρ 0 k f = Work.KMTContract.kmtProj ρ' 0 k f := by
  unfold Work.KMTContract.kmtProj
  rw [iwArithFreqs_zero_eq ρ ρ']

/-- **`ρ`-independence of the `l₁ = 0` low-pass family** (the form in which the Men'shov chapter
consumes it). -/
theorem lpf_zero_rho_indep (ρ ρ' : ℝ) (m₀ m : ℕ) (f : ℤ → ℂ) :
    lpf ρ 0 m₀ m f = lpf ρ' 0 m₀ m f := by
  unfold lpf
  exact kmtProj_zero_rho_indep ρ ρ' (-((m₀ : ℤ) + (m : ℤ))) f

/-! ## The exact single remaining input: the two-constraint good-`λ` of the walk

Everything on the chain "target ⟸ values-maximal bound ⟸ good-`λ`" other than the good-`λ` itself is
proved in the tree; the lemmas below assemble that chain *inside this file*, with the good-`λ` as an
explicit hypothesis, so that the target is reduced to one clean, self-contained statement.

The chain is

* `good-λ` (`hgl` below) + the a priori finiteness `Work.KMTAreas.A7Lpd.iwMaxFinite` (proved) +
  the layer-cake engine `Work.KMTAreas.A7Hi2.eLpNorm_le_of_goodLambda` (proved) give the `l`-free
  *square-function* form `‖sup_K|Π_{≤l,≤−(m₀+K)}f|‖_{ℓᵖ} ≤ C‖sqFun f‖_{ℓᵖ}`;
* the proved forward square-function bound `Work.KMTAreas.A7Lpd.bandSquareUnif` converts that into
  the `l`-free values-maximal bound (VM′);
* the proved `lacunaryMaxPieceRep_of_lFreeValuesMaximal` (above, in this file) concludes. -/

/-- `(x ^ r) ^ (1/r) = x` for `r = 0` is fine in `ℝ≥0∞`; the instance used below is `r = p.toReal`. -/
private lemma eLpNorm_eq_lintegral_rpow_toReal'' {F : ℤ → ℝ≥0∞} {p : ENNReal} (hp0 : p ≠ 0)
    (hpt : p ≠ ⊤) :
    MeasureTheory.eLpNorm F p (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
      = (∫⁻ y : ℤ, F y ^ p.toReal ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ))
          ^ (1 / p.toReal) := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hp0 hpt]
  exact congrArg (fun z : ℝ≥0∞ => z ^ (1 / p.toReal))
    (lintegral_congr (fun y => by rw [enorm_eq_self]))

/-- If the `ℓᵖ`-norm of an `ℝ≥0∞`-valued function on `ℤ` (counting measure) is finite then the
function is finite *everywhere* — the counting measure has no non-empty null sets. -/
private lemma lt_top_of_eLpNorm_lt_top'' {F : ℤ → ℝ≥0∞} {p : ENNReal} (hp0 : p ≠ 0) (hpt : p ≠ ⊤)
    (h : MeasureTheory.eLpNorm F p (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) < ⊤)
    (x : ℤ) : F x < ⊤ := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  set I : ℝ≥0∞ := ∫⁻ y : ℤ, F y ^ p.toReal
    ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) with hIdef
  have hI : I < ⊤ := by
    have h1 : MeasureTheory.eLpNorm F p (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        = I ^ (1 / p.toReal) := eLpNorm_eq_lintegral_rpow_toReal'' hp0 hpt
    rw [h1] at h
    by_contra hc
    have htop : I = ⊤ := top_le_iff.mp (not_lt.mp hc)
    rw [htop, ENNReal.top_rpow_of_pos (by positivity : (0 : ℝ) < 1 / p.toReal)] at h
    exact absurd h (lt_irrefl (⊤ : ℝ≥0∞))
  have hle : F x ^ p.toReal ≤ I := by
    rw [hIdef, MeasureTheory.lintegral_count]
    exact ENNReal.le_tsum (f := fun y => F y ^ p.toReal) x
  by_contra hx
  have hxt : F x = ⊤ := top_le_iff.mp (not_lt.mp hx)
  rw [hxt, ENNReal.top_rpow_of_pos hq] at hle
  exact absurd (lt_of_le_of_lt hle hI) (lt_irrefl (⊤ : ℝ≥0∞))

/-! ## Further sockets: the tree's own `l`-free inputs

The three theorems below are one-line wrappers around **axiom-clean** reductions already proved in
`Submission/Work/KMTAreas/A7Hi2/lacunaryMaxPieceProved.lean` (verified this session with
`#print axioms`: all three are propext/Classical.choice/Quot.sound only).  Each of them states the
assignment's conclusion *character for character*, so they compose with the target at once.  They
broaden the set of inputs a future proof may land: the *deep-regime chain* bound `(S1)`, the KMSZ
Theorem 5.2 output shape `(S2)`, and the "no `‖f‖_{ℓᵖ}` term" square-function form `(S3)`. -/

/-- **(S3)** The target from the *stronger* square-function form (no `‖f‖_{ℓᵖ}` term on the right),
i.e. from the statement of `Work.KMTAreas.A7Lpd.lacunaryMaxFun` — the cleanest form of the
Men'shov/Lépingle input, in which the tree's own `A7Lpd.maximal` consumes it. -/
theorem lacunaryMaxPieceRep_of_lFreeSqFun
    (h : ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
      ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
        MeasureTheory.eLpNorm (fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
            (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
              - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
          p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C *
            MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f)
              p MeasureTheory.Measure.count)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
          (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
            - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f)
          p MeasureTheory.Measure.count
        + ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  obtain ⟨Cρ, hCρ, C, hC, hb⟩ := h ρ hρ hρ1 p hp hptop
  exact ⟨Cρ, hCρ, C, hC, fun l₁ m₀ hgood f =>
    (hb l₁ m₀ hgood f).trans (le_add_of_nonneg_right bot_le)⟩

/-- **The Men'shov/Lépingle maximal piece for the low-pass IW family.**

For the dyadic IW projections `T_m = lpf ρ l₁ m₀ m = kmtProj ρ l₁ (-(m₀+m))` on the good major arcs
(`GoodMajorArcs ρ Cρ l₁ (-(m₀:ℤ))`, i.e. the bump is narrower than the separation of the
arithmetic frequencies of height `≤ 2^{l₁}`), the partial-sum maximal function of the annuli
`D_i = T_{i+1} - T_i` is bounded in `ℓᵖ(ℤ)`, `1 < p < ∞`, by the band-pass square function of the
annuli, uniformly in `m₀` and with a constant free of the height `l₁`:

  `‖ sup_K | Σ_{i<K} D_i f | ‖_{ℓᵖ}  ≤  C ‖ (Σ_i |D_i f|²)^{1/2} ‖_{ℓᵖ} + C ‖f‖_{ℓᵖ}`.

This is the "Lépingle/Men'shov" half of the paper's citation "Lépingle's inequality plus a standard
square function argument" ([JSW, TAMS 360 (2008), Thm 1.1 and Lemma 3.2]); the constant is *not*
allowed to grow with the number `#(ℚ/ℤ)_{≤l₁} ≍ 4^{l₁}` of arithmetic frequencies (both sides carry
the same arithmetic phases, so the correct constant is absolute).  The interior sum is the
telescoping `τ_0 f - τ_K f`, `τ_m = kmtProj ρ l₁ (-(m₀+m))`; the annuli `D_i` have pairwise disjoint,
concentric, `2`-lacunary symbols (the symbol of `D_i` is supported in the annulus
`2^{-(m₀+i+2)} < |ξ-α| < 2^{-(m₀+i+1)}` around each arithmetic frequency `α`).  The vocabulary is in
`Work.KMTAreas.A7Hi.LowpassDefs`; this is the same statement as the still-`sorry` copies
`Work.KMTAreas.A7Hi2.lacunaryMaxPiece`, `Work.KMTAreas.A7Lpd.lacunaryMaxConst`.  The PROVED route
available in the tree runs through `Work.KMTAreas.A7Lpd.lacunaryMaxAux` (telescoping
`Σ_{i<K}(T_i - T_{i+1}) = T_0 - T_K` plus the domination of the partial-sum supremum by `varPart 3`
of the walk `k ↦ T_k f`) and the single remaining crux is
`Work.KMTAreas.A7Lpd.varPartSqFun` (`‖varPart 3 (k ↦ T_k f)‖_p ≤ C‖(Σ_k|T_k f - T_{k+1}f|²)^{1/2}‖_p`,
Lépingle's inequality for the lacunary band-pass family). -/
theorem lacunaryMaxPieceRep (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p)
    (hptop : p < ⊤) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
          (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
            - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ)
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f)
          p MeasureTheory.Measure.count
        + ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by sorry

end Work.KMTAreas.A7Hi
