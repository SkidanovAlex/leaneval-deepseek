import Mathlib
import Submission.Work.KMTAreas.A7Hi2.supPieceClean
import Submission.Work.KMTAreas.A7HiRep.supChainsInterchange
import Submission.Work.KMTAreas.A7LoPoly.lpfTailGeneral
import Submission.Work.KMTAreas.A7LoPoly.chainPartHeadLe
import Submission.Work.KMTAreas.A7LoPoly.chainPartTailLe
import Submission.Work.KMTAreas.A7LoPoly.VrBlockLp
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7LoPoly

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- **The dyadic core of the low-pass `(1+l)²`-loss variational estimate.**

For `0 < ρ ≤ 1`, `2 < r`, `1 < p < ∞` there are `Cρ > 0` and `C > 0` such that on the good major
arcs and for every `f : ℤ → ℂ`,

  `‖ V^r(n ↦ Π_{≤l,≤−(m₀+n)} f) ‖_{ℓᵖ} ≤ C (1+l)² ‖f‖_{ℓᵖ}`,

uniformly in the base level `m₀`.

The proof is the head/tail split of the variational norm at the level `n = 2^κ`:

* the **head** (`n < 2^κ`) is bounded through Rademacher--Men'shov plus the (PROVED, `l`-free)
  single-chain block square-function bound `Work.KMTAreas.A7Lpd.singleChain_blockSqSum_le`
  (`Work.A7LoPoly.VrBlockLp`), at the cost `log₂(2^κ)`;
* the **tail** (`n ≥ 2^κ`) is `varRhoFrom r (2^κ)`, bounded `l`-free by
  `Work.A7LoPoly.lpfTailGeneral`, with `κ + 1 ≤ Cκ (1+l)²`;
* the **values supremum** is `Work.KMTAreas.A7Hi2.SupPiece` (PROVED, `(1+l)²`).

Both pieces are `≤ C (1+l)² ‖f‖_{ℓᵖ}`, and `(1+l)² ≥ 1` absorbs the constants. -/
theorem lpfVarPolyLoss (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r)
    (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (l m₀ : ℕ), Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l m₀ n f x))
        p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (1 + (l : ℝ)) ^ 2) *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  classical
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have hpne : p ≠ ⊤ := ne_of_lt hptop
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) (le_of_lt hr)
  have hrR : (2 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hpR : (1 : ℝ) < p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hpne).mpr hp
  -- ### the three analytic inputs
  obtain ⟨CρS, hCρS, CS, hCS, hS⟩ :=
    Work.KMTAreas.A7Hi2.supPieceClean ρ hρ hρ1 p hp hptop r
  obtain ⟨CρB, hCρB, CB, hCB, hB⟩ :=
    VrBlockLp ρ hρ hρ1 (r : ℝ) (le_of_lt hrR) p hp hptop
  obtain ⟨CρT, hCρT, Cκ, hCκ, Bt, hBt, hTail⟩ :=
    lpfTailGeneral ρ hρ hρ1 (r : ℝ) hrR p.toReal hpR
  -- ### the good-arcs constant and the final constant
  refine ⟨max (max CρS CρB) CρT, lt_max_of_lt_left (lt_max_of_lt_left hCρS),
    5 * CS + 2 * CB * Cκ + 2 * Bt + 1, by positivity, ?_⟩
  intro l m₀ hgood f
  have hgS : Work.Analysis.IonescuWainger.GoodMajorArcs ρ CρS l (-(m₀ : ℤ)) :=
    Work.KMTAreas.A7Hi.goodMajorArcs_mono (le_trans (le_max_left CρS CρB)
      (le_max_left (max CρS CρB) CρT)) hgood
  have hgB : Work.Analysis.IonescuWainger.GoodMajorArcs ρ CρB l (-(m₀ : ℤ)) :=
    Work.KMTAreas.A7Hi.goodMajorArcs_mono (le_trans (le_max_right CρS CρB)
      (le_max_left (max CρS CρB) CρT)) hgood
  have hgT : Work.Analysis.IonescuWainger.GoodMajorArcs ρ CρT l (-(m₀ : ℤ)) :=
    Work.KMTAreas.A7Hi.goodMajorArcs_mono (le_max_right (max CρS CρB) CρT) hgood
  -- ### the tail threshold
  obtain ⟨κ, hκbudget, hκtail⟩ := hTail l m₀ hgT
  set M : ℕ := 2 ^ κ with hMdef
  have hM1 : 1 ≤ M := by rw [hMdef]; exact Nat.one_le_two_pow
  have hlog : (Nat.log2 M : ℝ) + 1 ≤ Cκ * (1 + (l : ℝ)) ^ 2 := by
    have h1 : Nat.log2 M = κ := by rw [hMdef]; exact Nat.log2_two_pow
    rw [h1]
    exact hκbudget
  have h5e : (ENNReal.ofReal 5 : ℝ≥0∞) = 5 := by norm_num
  have h2e : (ENNReal.ofReal 2 : ℝ≥0∞) = 2 := by norm_num
  -- ### the three pointwise pieces
  set S : ℤ → ℝ≥0∞ := fun x => Work.KMTAreas.A7Hi.supPart r
    (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l m₀ n f x) with hSdef
  set V : ℤ → ℝ≥0∞ := fun x => Work.Analysis.Variation.Vr (r : ℝ) M
    (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l m₀ n f x
      - Work.KMTAreas.A7Hi.lpf ρ l m₀ 0 f x) with hVdef
  set R : ℤ → ℝ≥0∞ := fun x => Work.BourgainPlan.Maximal.varRhoFrom (r : ℝ) M
    (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l m₀ n f x) with hRdef
  -- ### the pointwise decomposition of the variational norm
  have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l m₀ n f x)
      ≤ ENNReal.ofReal 5 * S x + (ENNReal.ofReal 2 * V x + ENNReal.ofReal 2 * R x) := by
    intro x
    set a : ℕ → ℂ := fun n => Work.KMTAreas.A7Hi.lpf ρ l m₀ n f x with hadef
    have hSa : Work.KMTAreas.A7Hi.supPart r a = S x := by rw [hSdef, hadef]
    have hVa : Work.Analysis.Variation.Vr (r : ℝ) M (fun n : ℕ => a n - a 0) = V x := by
      rw [hVdef, hadef]
    have hRa : Work.BourgainPlan.Maximal.varRhoFrom (r : ℝ) M a = R x := by
      rw [hRdef, hadef]
    have hsplit := Work.KMTAreas.A7HiRep.chainPartHeadTailSplit r hr1 M a
    have hH := chainPartHeadLe r hr1 M hM1 a
    have hTl := chainPartTailLe r hr1 M a
    have hchain : Work.KMTAreas.A7Hi.chainPart r a
        ≤ (2 : ℝ≥0∞) * S x + 2 * V x + (2 * S x + 2 * R x) := by
      have h := hsplit.trans (add_le_add hH hTl)
      rw [hSa, hVa, hRa] at h
      exact h
    calc PointwiseErgodicTheorems.variationalNorm r a
        = Work.KMTAreas.A7Hi.supPart r a + Work.KMTAreas.A7Hi.chainPart r a :=
          Work.KMTAreas.A7Hi.variationalNorm_eq_parts r a
      _ ≤ S x + ((2 : ℝ≥0∞) * S x + 2 * V x + (2 * S x + 2 * R x)) :=
          add_le_add (le_of_eq hSa) hchain
      _ = ENNReal.ofReal 5 * S x + (ENNReal.ofReal 2 * V x + ENNReal.ofReal 2 * R x) := by
          rw [h5e, h2e]; ring
  -- ### the `ℓᵖ` assembly
  have h1 : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l m₀ n f x)) p MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => ENNReal.ofReal 5 * S x
          + (ENNReal.ofReal 2 * V x + ENNReal.ofReal 2 * R x)) p MeasureTheory.Measure.count :=
    MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) hpt
  have h2 : MeasureTheory.eLpNorm (fun x : ℤ => ENNReal.ofReal 5 * S x
        + (ENNReal.ofReal 2 * V x + ENNReal.ofReal 2 * R x)) p MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => ENNReal.ofReal 5 * S x) p MeasureTheory.Measure.count
        + MeasureTheory.eLpNorm (fun x : ℤ =>
            ENNReal.ofReal 2 * V x + ENNReal.ofReal 2 * R x) p MeasureTheory.Measure.count :=
    Work.KMTAreas.A7.eLpNorm_add_le_ennreal (le_of_lt hp) hpne
      (u := fun x : ℤ => ENNReal.ofReal 5 * S x)
      (v := fun x : ℤ => ENNReal.ofReal 2 * V x + ENNReal.ofReal 2 * R x)
      (μ := MeasureTheory.Measure.count)
  have h3 : MeasureTheory.eLpNorm (fun x : ℤ =>
        ENNReal.ofReal 2 * V x + ENNReal.ofReal 2 * R x) p MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => ENNReal.ofReal 2 * V x) p MeasureTheory.Measure.count
        + MeasureTheory.eLpNorm (fun x : ℤ => ENNReal.ofReal 2 * R x) p
            MeasureTheory.Measure.count :=
    Work.KMTAreas.A7.eLpNorm_add_le_ennreal (le_of_lt hp) hpne
      (u := fun x : ℤ => ENNReal.ofReal 2 * V x)
      (v := fun x : ℤ => ENNReal.ofReal 2 * R x) (μ := MeasureTheory.Measure.count)
  have h4 : MeasureTheory.eLpNorm (fun x : ℤ => ENNReal.ofReal 5 * S x) p
        MeasureTheory.Measure.count
      = ENNReal.ofReal 5 * MeasureTheory.eLpNorm S p MeasureTheory.Measure.count :=
    Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal (c := ENNReal.ofReal 5)
      ENNReal.ofReal_ne_top hp0 hpne
  have h5 : MeasureTheory.eLpNorm (fun x : ℤ => ENNReal.ofReal 2 * V x) p
        MeasureTheory.Measure.count
      = ENNReal.ofReal 2 * MeasureTheory.eLpNorm V p MeasureTheory.Measure.count :=
    Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal (c := ENNReal.ofReal 2)
      ENNReal.ofReal_ne_top hp0 hpne
  have h6 : MeasureTheory.eLpNorm (fun x : ℤ => ENNReal.ofReal 2 * R x) p
        MeasureTheory.Measure.count
      = ENNReal.ofReal 2 * MeasureTheory.eLpNorm R p MeasureTheory.Measure.count :=
    Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal (c := ENNReal.ofReal 2)
      ENNReal.ofReal_ne_top hp0 hpne
  -- ### the three `ℓᵖ` bounds
  have hSbound : MeasureTheory.eLpNorm S p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (CS * (1 + (l : ℝ)) ^ 2) *
          MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    have h := hS l m₀ hgS f
    rw [hSdef]
    exact h
  have hVbound : MeasureTheory.eLpNorm V p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (CB * ((Nat.log2 M : ℝ) + 1)) *
          MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    have h := hB l m₀ M hM1 hgB f
    rw [hVdef]
    exact h
  have hRbound : MeasureTheory.eLpNorm R p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal Bt * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    have h := hκtail f
    rw [ENNReal.ofReal_toReal hpne] at h
    rw [hRdef, hMdef]
    exact h
  have hmulof : ∀ (c a : ℝ) (X : ℝ≥0∞), 0 ≤ c →
      ENNReal.ofReal c * (ENNReal.ofReal a * X) = ENNReal.ofReal (c * a) * X := by
    intro c a X hc
    rw [← mul_assoc, ← ENNReal.ofReal_mul hc]
  -- ### the constant bookkeeping
  have hCS0 : (0 : ℝ) ≤ CS := hCS.le
  have hCB0 : (0 : ℝ) ≤ CB := hCB.le
  have hBt0 : (0 : ℝ) ≤ Bt := hBt
  have hl0 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
  have hX1 : (1 : ℝ) ≤ (1 + (l : ℝ)) ^ 2 := by
    nlinarith [sq_nonneg (1 + (l : ℝ)), hl0]
  have hkey : 5 * (CS * (1 + (l : ℝ)) ^ 2) + (2 * (CB * ((Nat.log2 M : ℝ) + 1)) + 2 * Bt)
      ≤ (5 * CS + 2 * CB * Cκ + 2 * Bt + 1) * (1 + (l : ℝ)) ^ 2 := by
    have hstep1 : 2 * (CB * ((Nat.log2 M : ℝ) + 1)) ≤ 2 * (CB * (Cκ * (1 + (l : ℝ)) ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog hCB0)
        (by norm_num : (0 : ℝ) ≤ 2)
    have hstep2 : 2 * Bt ≤ 2 * (Bt * (1 + (l : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hBt0 hX1) (by norm_num : (0 : ℝ) ≤ 2)
    have hsum : 5 * (CS * (1 + (l : ℝ)) ^ 2)
          + (2 * (CB * (Cκ * (1 + (l : ℝ)) ^ 2)) + 2 * (Bt * (1 + (l : ℝ)) ^ 2))
        = (5 * CS + 2 * CB * Cκ + 2 * Bt) * (1 + (l : ℝ)) ^ 2 := by ring
    calc 5 * (CS * (1 + (l : ℝ)) ^ 2) + (2 * (CB * ((Nat.log2 M : ℝ) + 1)) + 2 * Bt)
        ≤ 5 * (CS * (1 + (l : ℝ)) ^ 2)
            + (2 * (CB * (Cκ * (1 + (l : ℝ)) ^ 2)) + 2 * (Bt * (1 + (l : ℝ)) ^ 2)) :=
          add_le_add le_rfl (add_le_add hstep1 hstep2)
      _ = (5 * CS + 2 * CB * Cκ + 2 * Bt) * (1 + (l : ℝ)) ^ 2 := hsum
      _ ≤ (5 * CS + 2 * CB * Cκ + 2 * Bt + 1) * (1 + (l : ℝ)) ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          linarith
  -- ### assembly
  calc MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l m₀ n f x)) p MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => ENNReal.ofReal 5 * S x
          + (ENNReal.ofReal 2 * V x + ENNReal.ofReal 2 * R x)) p MeasureTheory.Measure.count := h1
    _ ≤ MeasureTheory.eLpNorm (fun x : ℤ => ENNReal.ofReal 5 * S x) p MeasureTheory.Measure.count
          + MeasureTheory.eLpNorm (fun x : ℤ =>
              ENNReal.ofReal 2 * V x + ENNReal.ofReal 2 * R x) p
                MeasureTheory.Measure.count := h2
    _ ≤ MeasureTheory.eLpNorm (fun x : ℤ => ENNReal.ofReal 5 * S x) p MeasureTheory.Measure.count
          + (MeasureTheory.eLpNorm (fun x : ℤ => ENNReal.ofReal 2 * V x) p
                MeasureTheory.Measure.count
            + MeasureTheory.eLpNorm (fun x : ℤ => ENNReal.ofReal 2 * R x) p
                MeasureTheory.Measure.count) := add_le_add le_rfl h3
    _ = ENNReal.ofReal 5 * MeasureTheory.eLpNorm S p MeasureTheory.Measure.count
          + (ENNReal.ofReal 2 * MeasureTheory.eLpNorm V p MeasureTheory.Measure.count
            + ENNReal.ofReal 2 * MeasureTheory.eLpNorm R p MeasureTheory.Measure.count) := by
          rw [h4, h5, h6]
    _ ≤ ENNReal.ofReal 5 * (ENNReal.ofReal (CS * (1 + (l : ℝ)) ^ 2)
            * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
          + (ENNReal.ofReal 2 * (ENNReal.ofReal (CB * ((Nat.log2 M : ℝ) + 1))
              * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
            + ENNReal.ofReal 2 * (ENNReal.ofReal Bt
                * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)) :=
          add_le_add (mul_le_mul_of_nonneg_left hSbound bot_le)
            (add_le_add (mul_le_mul_of_nonneg_left hVbound bot_le)
              (mul_le_mul_of_nonneg_left hRbound bot_le))
    _ = ENNReal.ofReal (5 * (CS * (1 + (l : ℝ)) ^ 2)) *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
          + (ENNReal.ofReal (2 * (CB * ((Nat.log2 M : ℝ) + 1))) *
                MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
              + ENNReal.ofReal (2 * Bt) * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count) := by
          rw [hmulof 5 (CS * (1 + (l : ℝ)) ^ 2) (MeasureTheory.eLpNorm f p
                MeasureTheory.Measure.count) (by norm_num : (0 : ℝ) ≤ 5),
            hmulof 2 (CB * ((Nat.log2 M : ℝ) + 1)) (MeasureTheory.eLpNorm f p
                MeasureTheory.Measure.count) (by norm_num : (0 : ℝ) ≤ 2),
            hmulof 2 Bt (MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
                (by norm_num : (0 : ℝ) ≤ 2)]
    _ = ENNReal.ofReal (5 * (CS * (1 + (l : ℝ)) ^ 2)
            + (2 * (CB * ((Nat.log2 M : ℝ) + 1)) + 2 * Bt)) *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
          rw [← add_mul, ← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal ((5 * CS + 2 * CB * Cκ + 2 * Bt + 1) * (1 + (l : ℝ)) ^ 2)
          * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count :=
          mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hkey) bot_le

end

end Work.KMTAreas.A7LoPoly
