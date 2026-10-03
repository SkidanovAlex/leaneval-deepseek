/-
# The Ionescu--Wainger low-pass variational estimate with a polynomial loss in the arithmetic height

This module proves the paper's low-frequency case of `(lin-1)` for the *unmodulated* low-pass
Ionescu--Wainger walk — i.e. the estimate that the tree's canonical crux
`Work.KMTAreas.A7HiRep.chainPartSqFunPos` supplies `l₁`-freely — in the form with a *polynomial*
loss `(1+l₁)²` in the arithmetic height, which is all the consumers need: the target's weight
`Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂` is monotone in `(1+L)^A`, so a `(1+l₁)²` factor is
absorbed by `lossWeight 4`.

## The route (no `l₁`-free input)

The walk `m ↦ lpf ρ l₁ m₀ m f = kmtProj ρ l₁ (-(m₀+m)) f` is split at the **decimation cut**

  `cutLevel ρ l₁ = Nat.clog 2 (3 · iwQl ρ l₁) + 2`

(the level at which the IW bump becomes narrower than the common denominator of the arithmetic
frequencies, so that the Magyar--Stein--Wainger decimation factorisation applies):

* the **shallow** part (`m ≤ M`, `M := cutLevel ρ l₁ - m₀`, frozen at `M`): the
  Rademacher--Men'shov / dyadic block-square-function route, losing `log₂ (cutLevel ρ l₁) = O(l₁)`
  — taken as the hypothesis `hShallow` (see `Work.KMTPlan.A6.shallowChainLe`);
* the **deep** part (the walk shifted to the level `M`, i.e. `m ↦ lpf ρ l₁ m₀ (m+M) f`): the
  decimation factorisation turns it into a decimated dilation family of the *fixed* coarse
  projection `kmtProj ρ l₁ (-C₀) f`, whose variational norm is bounded by the `l₁`-free
  `Work.KMTAreas.A7Hi2.decimDilVarUnif` (JSW/Lépingle for lacunary dilation families) — with no
  loss in `l₁`; taken as the hypothesis `hDeep` (see `Work.KMTPlan.A6.deepChainLe`).

The two halves are glued with the subadditivity of the chain part
(`Work.KMTAreas.A7HiRep.chainPartSubAdd`) and the prefix-zero/tail comparison
(`Work.KMTAreas.A7HiRep.chainPart_prefixZero_tail`), and the values supremum is recovered from the
level-`0` value (`Work.KMTAreas.A7JSW.supPart_le_norm_add_chainPart`) together with the `l₁`-free
single-scale bound `Work.KMTAreas.A7.kmtProj_lp_bound_uniform`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7Hi2.cutLevel
import Submission.Work.KMTAreas.A7Hi2.chainPart_mono_comp
import Submission.Work.KMTAreas.A7HiRep.aliasingReduction
import Submission.Work.KMTAreas.A7.lacunaryIWProjLowpassVar
import Submission.Work.Analysis.Variation.Defs
import Submission.Work.KMTAreas.A7HiRep.chainPartSqFunLeTwo
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open Work.KMTAreas.A7Hi

noncomputable section

/-! ## The pointwise shallow/deep split of the chain part -/

/-- **Pointwise chain-part split of the IW walk at the decimation cut.**

Writing `M := cutLevel ρ l₁ - m₀`, the chain part of the walk is at most that of the walk frozen at
`M` plus that of the walk *shifted* to the level `M`.  (The second term is the prefix-zero/tail
comparison `Work.KMTAreas.A7HiRep.chainPart_prefixZero_tail`, which expresses the tail
`m ↦ b m − b (min m M)` by the shifted walk `m ↦ b (m + M)`.) -/
theorem chainPart_split_pointwise (ρ : ℝ) (l₁ m₀ : ℕ) (r : NNReal) (hr : 1 ≤ r)
    (f : ℤ → ℂ) (x : ℤ) :
    chainPart r (fun m : ℕ => lpf ρ l₁ m₀ m f x)
      ≤ chainPart r (fun m : ℕ =>
          lpf ρ l₁ m₀ (min m (Work.KMTAreas.A7Hi2.cutLevel ρ l₁ - m₀)) f x)
        + chainPart r (fun m : ℕ =>
            lpf ρ l₁ m₀ (m + (Work.KMTAreas.A7Hi2.cutLevel ρ l₁ - m₀)) f x) := by
  have hdecomp : (fun m : ℕ => lpf ρ l₁ m₀ m f x)
      = (fun m : ℕ => lpf ρ l₁ m₀ (min m (Work.KMTAreas.A7Hi2.cutLevel ρ l₁ - m₀)) f x)
        + (fun m : ℕ => lpf ρ l₁ m₀ m f x
            - lpf ρ l₁ m₀ (min m (Work.KMTAreas.A7Hi2.cutLevel ρ l₁ - m₀)) f x) := by
    funext m
    simp only [Pi.add_apply]
    ring
  rw [hdecomp]
  refine (Work.KMTAreas.A7HiRep.chainPartSubAdd r hr _ _).trans (add_le_add le_rfl ?_)
  exact Work.KMTAreas.A7HiRep.chainPart_prefixZero_tail r hr
    (Work.KMTAreas.A7Hi2.cutLevel ρ l₁ - m₀) (fun m : ℕ => lpf ρ l₁ m₀ m f x)

/-! ## The dyadic chain bound with a `(1+l₁)²` loss, from the two halves -/

/-- **The chain part of the IW low-pass walk is bounded with a `(1+l₁)²` loss**, given the shallow
bound (`(1+l₁)` loss) and the deep bound (`l₁`-free). -/
theorem chainLe_dyadic_of_parts (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r)
    (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤)
    (hShallow : ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ M : ℕ),
      M ≤ Work.KMTAreas.A7Hi2.cutLevel ρ l₁ →
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => chainPart r
          (fun m : ℕ => lpf ρ l₁ m₀ (min m M) f x))
        p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (1 + (l₁ : ℝ))) *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
    (hDeep : ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => chainPart r
          (fun n : ℕ => if Work.KMTAreas.A7Hi2.cutLevel ρ l₁ ≤ m₀ + n
            then lpf ρ l₁ m₀ n f x else 0))
        p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => chainPart r (fun m : ℕ => lpf ρ l₁ m₀ m f x))
        p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (1 + (l₁ : ℝ)) ^ 2) *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  obtain ⟨Cρs, hCρs, Cs, hCs, hs⟩ := hShallow
  obtain ⟨Cρd, hCρd, Cd, hCd, hd⟩ := hDeep
  refine ⟨max Cρs Cρd, lt_max_of_lt_left hCρs, Cs + Cd + 1, by positivity, ?_⟩
  intro l₁ m₀ hgood f
  have hgoods : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρs l₁ (-(m₀ : ℤ)) :=
    goodMajorArcs_mono (le_max_left _ _) hgood
  have hgoodd : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρd l₁ (-(m₀ : ℤ)) :=
    goodMajorArcs_mono (le_max_right _ _) hgood
  -- the shallow half
  have hshallow : MeasureTheory.eLpNorm (fun x : ℤ => chainPart r
        (fun m : ℕ => lpf ρ l₁ m₀ (min m (Work.KMTAreas.A7Hi2.cutLevel ρ l₁ - m₀)) f x))
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (Cs * (1 + (l₁ : ℝ))) * MeasureTheory.eLpNorm f p
          MeasureTheory.Measure.count :=
    hs l₁ m₀ (Work.KMTAreas.A7Hi2.cutLevel ρ l₁ - m₀) (Nat.sub_le _ _) hgoods f
  -- the deep half: the shifted walk is a monotone reindexing of the deep indicator family
  have hshift : MeasureTheory.eLpNorm (fun x : ℤ => chainPart r
        (fun m : ℕ => lpf ρ l₁ m₀ (m + (Work.KMTAreas.A7Hi2.cutLevel ρ l₁ - m₀)) f x))
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal Cd * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    refine (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => ?_)).trans (hd l₁ m₀ hgoodd f)
    have hle : ∀ m : ℕ, Work.KMTAreas.A7Hi2.cutLevel ρ l₁
        ≤ m₀ + (m + (Work.KMTAreas.A7Hi2.cutLevel ρ l₁ - m₀)) := by
      intro m
      rcases Nat.lt_or_ge m₀ (Work.KMTAreas.A7Hi2.cutLevel ρ l₁) with h | h
      · have h3 : (Work.KMTAreas.A7Hi2.cutLevel ρ l₁ - m₀) + m₀
            = Work.KMTAreas.A7Hi2.cutLevel ρ l₁ := Nat.sub_add_cancel h.le
        omega
      · have h3 : Work.KMTAreas.A7Hi2.cutLevel ρ l₁ - m₀ = 0 := by omega
        omega
    have hEq : (fun m : ℕ => lpf ρ l₁ m₀ (m + (Work.KMTAreas.A7Hi2.cutLevel ρ l₁ - m₀)) f x)
        = fun m : ℕ => (fun n : ℕ => if Work.KMTAreas.A7Hi2.cutLevel ρ l₁ ≤ m₀ + n
            then lpf ρ l₁ m₀ n f x else 0) (m + (Work.KMTAreas.A7Hi2.cutLevel ρ l₁ - m₀)) := by
      funext m
      simp only [if_pos (hle m)]
    rw [hEq]
    exact Work.KMTAreas.A7Hi2.chainPart_mono_comp r
      (fun n : ℕ => if Work.KMTAreas.A7Hi2.cutLevel ρ l₁ ≤ m₀ + n then lpf ρ l₁ m₀ n f x else 0)
      (fun m : ℕ => m + (Work.KMTAreas.A7Hi2.cutLevel ρ l₁ - m₀))
      (monotone_id.add_const _)
  -- assemble
  have hpt' : ∀ x : ℤ, ‖chainPart r (fun m : ℕ => lpf ρ l₁ m₀ m f x)‖ₑ
      ≤ ‖chainPart r (fun m : ℕ =>
            lpf ρ l₁ m₀ (min m (Work.KMTAreas.A7Hi2.cutLevel ρ l₁ - m₀)) f x)
          + chainPart r (fun m : ℕ =>
            lpf ρ l₁ m₀ (m + (Work.KMTAreas.A7Hi2.cutLevel ρ l₁ - m₀)) f x)‖ₑ := by
    intro x
    simpa only [enorm_eq_self] using chainPart_split_pointwise ρ l₁ m₀ r
      (le_trans (by norm_num : (1 : NNReal) ≤ 2) (le_of_lt hr)) f x
  refine (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) hpt').trans ?_
  refine (Work.KMTAreas.A7.eLpNorm_add_le_ennreal
    (u := fun x : ℤ => chainPart r
      (fun m : ℕ => lpf ρ l₁ m₀ (min m (Work.KMTAreas.A7Hi2.cutLevel ρ l₁ - m₀)) f x))
    (v := fun x : ℤ => chainPart r
      (fun m : ℕ => lpf ρ l₁ m₀ (m + (Work.KMTAreas.A7Hi2.cutLevel ρ l₁ - m₀)) f x))
    (q := p) (le_of_lt hp) (ne_of_lt hptop)
    (μ := MeasureTheory.Measure.count)).trans ?_
  refine (add_le_add hshallow hshift).trans ?_
  rw [← add_mul, ← ENNReal.ofReal_add (by positivity) hCd.le]
  refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
  have hl1 : (0 : ℝ) ≤ (l₁ : ℝ) := Nat.cast_nonneg _
  have h1 : (1 : ℝ) ≤ (1 + (l₁ : ℝ)) ^ 2 := by nlinarith
  have h2 : (1 : ℝ) + (l₁ : ℝ) ≤ (1 + (l₁ : ℝ)) ^ 2 := by nlinarith
  have hCs0 : (0 : ℝ) ≤ Cs := hCs.le
  have hCd0 : (0 : ℝ) ≤ Cd := hCd.le
  calc Cs * (1 + (l₁ : ℝ)) + Cd
      ≤ Cs * (1 + (l₁ : ℝ)) ^ 2 + Cd * (1 + (l₁ : ℝ)) ^ 2 := by
        have ha := mul_le_mul_of_nonneg_left h2 hCs0
        have hb := mul_le_mul_of_nonneg_left h1 hCd0
        linarith
    _ = (Cs + Cd) * (1 + (l₁ : ℝ)) ^ 2 := by ring
    _ ≤ (Cs + Cd + 1) * (1 + (l₁ : ℝ)) ^ 2 := by
        have h3 : (0 : ℝ) ≤ (1 + (l₁ : ℝ)) ^ 2 := by positivity
        nlinarith

/-! ## The dyadic variational estimate with a `(1+l₁)²` loss -/

/-- **The `r`-variational norm of the IW low-pass walk, with a `(1+l₁)²` loss.**

The values supremum is bounded by the level-`0` value plus the chain part
(`Work.KMTAreas.A7JSW.supPart_le_norm_add_chainPart`), the level-`0` value by the `l₁`-free
single-scale bound `Work.KMTAreas.A7.kmtProj_lp_bound_uniform`, and the chain part by `hChain`. -/
theorem dyadicVarLe_of_chain (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r)
    (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤)
    (hChain : ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => chainPart r (fun m : ℕ => lpf ρ l₁ m₀ m f x))
        p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (1 + (l₁ : ℝ)) ^ 2) *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun m : ℕ => lpf ρ l₁ m₀ m f x))
        p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (1 + (l₁ : ℝ)) ^ 2) *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  have hp0 : p ≠ 0 := (lt_trans zero_lt_one hp).ne'
  have hptop' : p ≠ ⊤ := ne_of_lt hptop
  have hpR : (1 : ℝ) < p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hptop').mpr hp
  have hpeq : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal hptop'
  obtain ⟨Cρc, hCρc, Cc, hCc, hc⟩ := hChain
  obtain ⟨CρS, hCρS, CS, hCS, hS⟩ := Work.KMTAreas.A7.kmtProj_lp_bound_uniform ρ hρ hρ1 p.toReal hpR
  refine ⟨max Cρc CρS, lt_max_of_lt_left hCρc, CS + 2 * Cc, by positivity, ?_⟩
  intro l₁ m₀ hgood f
  have hgoodc : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρc l₁ (-(m₀ : ℤ)) :=
    goodMajorArcs_mono (le_max_left _ _) hgood
  have hgoodS : Work.Analysis.IonescuWainger.GoodMajorArcs ρ CρS l₁ (-(m₀ : ℤ)) :=
    goodMajorArcs_mono (le_max_right _ _) hgood
  -- the level-`0` single-scale bound
  have hT0 : MeasureTheory.eLpNorm (fun x : ℤ => ‖lpf ρ l₁ m₀ 0 f x‖ₑ) p
        MeasureTheory.Measure.count
      ≤ ENNReal.ofReal CS * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    rw [Work.KMTAreas.A7JSW.eLpNorm_enorm_eq_aux hp0 hptop']
    have h := hS l₁ (-(m₀ : ℤ)) hgoodS f
    rw [hpeq] at h
    simpa only [Work.KMTAreas.A7Hi.lpf, Nat.cast_zero, add_zero] using h
  -- the chain term
  have hchain := hc l₁ m₀ hgoodc f
  -- pointwise: `V^r = supPart + chainPart ≤ (‖T_0 f‖ + chainPart) + chainPart`
  have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
        (fun m : ℕ => lpf ρ l₁ m₀ m f x)
      ≤ (‖lpf ρ l₁ m₀ 0 f x‖ₑ + chainPart r (fun m : ℕ => lpf ρ l₁ m₀ m f x))
        + chainPart r (fun m : ℕ => lpf ρ l₁ m₀ m f x) := by
    intro x
    have hsplit : PointwiseErgodicTheorems.variationalNorm r (fun m : ℕ => lpf ρ l₁ m₀ m f x)
        = supPart r (fun m : ℕ => lpf ρ l₁ m₀ m f x)
          + chainPart r (fun m : ℕ => lpf ρ l₁ m₀ m f x) :=
      variationalNorm_eq_parts r _
    rw [hsplit]
    exact add_le_add (Work.KMTAreas.A7JSW.supPart_le_norm_add_chainPart ρ l₁ m₀ 0 f x r
      (le_of_lt hr))
      le_rfl
  have hpt' : ∀ x : ℤ, ‖PointwiseErgodicTheorems.variationalNorm r
        (fun m : ℕ => lpf ρ l₁ m₀ m f x)‖ₑ
      ≤ ‖(‖lpf ρ l₁ m₀ 0 f x‖ₑ + chainPart r (fun m : ℕ => lpf ρ l₁ m₀ m f x))
        + chainPart r (fun m : ℕ => lpf ρ l₁ m₀ m f x)‖ₑ := by
    intro x
    simpa only [enorm_eq_self] using hpt x
  refine (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) hpt').trans ?_
  refine (Work.KMTAreas.A7.eLpNorm_add_le_ennreal
    (u := fun x : ℤ => ‖lpf ρ l₁ m₀ 0 f x‖ₑ + chainPart r (fun m : ℕ => lpf ρ l₁ m₀ m f x))
    (v := fun x : ℤ => chainPart r (fun m : ℕ => lpf ρ l₁ m₀ m f x))
    (q := p) (le_of_lt hp) hptop' (μ := MeasureTheory.Measure.count)).trans ?_
  refine (add_le_add ((Work.KMTAreas.A7.eLpNorm_add_le_ennreal
    (u := fun x : ℤ => ‖lpf ρ l₁ m₀ 0 f x‖ₑ)
    (v := fun x : ℤ => chainPart r (fun m : ℕ => lpf ρ l₁ m₀ m f x))
    (q := p) (le_of_lt hp) hptop' (μ := MeasureTheory.Measure.count)).trans
      (add_le_add hT0 hchain)) hchain).trans ?_
  have hcoef : ENNReal.ofReal CS + ENNReal.ofReal (Cc * (1 + (l₁ : ℝ)) ^ 2)
        + ENNReal.ofReal (Cc * (1 + (l₁ : ℝ)) ^ 2)
      ≤ ENNReal.ofReal ((CS + 2 * Cc) * (1 + (l₁ : ℝ)) ^ 2) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hl1 : (0 : ℝ) ≤ (l₁ : ℝ) := Nat.cast_nonneg _
    have h1 : (1 : ℝ) ≤ (1 + (l₁ : ℝ)) ^ 2 := by nlinarith
    have hCS0 : (0 : ℝ) ≤ CS := hCS.le
    have hCSg : CS ≤ CS * (1 + (l₁ : ℝ)) ^ 2 := le_mul_of_one_le_right hCS0 h1
    nlinarith [hCSg]
  calc (ENNReal.ofReal CS * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
          + ENNReal.ofReal (Cc * (1 + (l₁ : ℝ)) ^ 2) * MeasureTheory.eLpNorm f p
            MeasureTheory.Measure.count)
        + ENNReal.ofReal (Cc * (1 + (l₁ : ℝ)) ^ 2) * MeasureTheory.eLpNorm f p
          MeasureTheory.Measure.count
      = (ENNReal.ofReal CS + ENNReal.ofReal (Cc * (1 + (l₁ : ℝ)) ^ 2)
          + ENNReal.ofReal (Cc * (1 + (l₁ : ℝ)) ^ 2)) * MeasureTheory.eLpNorm f p
            MeasureTheory.Measure.count := by rw [← add_mul, ← add_mul]
    _ ≤ ENNReal.ofReal ((CS + 2 * Cc) * (1 + (l₁ : ℝ)) ^ 2) * MeasureTheory.eLpNorm f p
            MeasureTheory.Measure.count := mul_le_mul_left hcoef _

/-! ## The lacunary form: the `hLowpass` input of the A7 assembly -/

/-- **The lacunary low-pass variational estimate with a `(1+l₁)²` loss.**

The family `n ↦ Tle ρ l₁ (varphiN ⌊a n⌋ 0) f = kmtProj ρ l₁ (-(logN ⌊a n⌋)) f` is the monotone
reindexing of the *dyadic* family `m ↦ kmtProj ρ l₁ (-(m₀ + m)) f` (`m₀ := (-k).toNat`), and
reindexing by a monotone map does not increase the variational norm
(`Work.KMTAreas.A7.variationalNorm_comp_mono_le`).  This is the exact shape of the `hLowpass`
hypothesis of `Work.KMTAreas.A7.lacunaryBumpVarEstimate_assembly`, with the `l₁`-free crux
replaced by the lossy dyadic estimate `hDyadic`. -/
theorem lacLowpassVar_of_dyadic (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r)
    (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) (Λ : NNReal) (hΛ : 1 < Λ)
    (hDyadic : ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun m : ℕ => lpf ρ l₁ m₀ m f x))
        p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (1 + (l₁ : ℝ)) ^ 2) *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (k : ℤ) (l₁ : ℕ) (a : ℕ → NNReal)
        (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) (f : ℤ → ℂ),
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ k →
        (∀ n : ℕ, -(Work.Analysis.EndVar.logN (Nat.floor (a n))) ≤ k) →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l₁
              (Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0) f x))
          p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C * (1 + (l₁ : ℝ)) ^ 2) *
              MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  obtain ⟨Cρ, hCρ, C, hC, hd⟩ := hDyadic
  refine ⟨Cρ, hCρ, C, hC, ?_⟩
  intro k l₁ a ha ha1 f hgood hk
  -- ## `GoodMajorArcs` forces `k ≤ 0`
  have hk0 : k ≤ 0 := by
    have h2 : (0 : ℝ) < (2 : ℝ) ^ (ρ * (l₁ : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) (ρ * (l₁ : ℝ))
    have h4 : (k : ℝ) ≤ -Cρ * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) := hgood
    have h3 : (k : ℝ) ≤ 0 := by nlinarith
    exact_mod_cast h3
  -- ## `a` is monotone
  have hamono : Monotone a :=
    Work.KMTAreas.A7.lowpass_monotone_of_lacunary hΛ ha ha1
  -- ## the base level `m₀` of the dyadic family
  set m₀ : ℕ := (-k).toNat with hm₀def
  have hm₀ : ((m₀ : ℕ) : ℤ) = -k := by
    rw [hm₀def]
    exact Int.toNat_of_nonneg (by omega)
  have hgood' : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) := by
    rw [hm₀, neg_neg]
    exact hgood
  -- ## the monotone reindexing
  set σ : ℕ → ℕ := fun n => (Work.Analysis.EndVar.logN (Nat.floor (a n)) + k).toNat with hσdef
  have hσmono : Monotone σ := by
    intro n m hnm
    have h1 : Nat.floor (a n) ≤ Nat.floor (a m) := Nat.floor_mono (hamono hnm)
    have h2 : Work.Analysis.EndVar.logN (Nat.floor (a n))
        ≤ Work.Analysis.EndVar.logN (Nat.floor (a m)) :=
      Work.Analysis.EndVar.logN_mono h1
    have h3 : (0 : ℤ) ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)) + k := by
      have h := hk n; omega
    have h4 : (0 : ℤ) ≤ Work.Analysis.EndVar.logN (Nat.floor (a m)) + k := by
      have h := hk m; omega
    show (Work.Analysis.EndVar.logN (Nat.floor (a n)) + k).toNat
        ≤ (Work.Analysis.EndVar.logN (Nat.floor (a m)) + k).toNat
    have hx : (((Work.Analysis.EndVar.logN (Nat.floor (a n)) + k).toNat : ℕ) : ℤ)
        = Work.Analysis.EndVar.logN (Nat.floor (a n)) + k := Int.toNat_of_nonneg h3
    have hy : (((Work.Analysis.EndVar.logN (Nat.floor (a m)) + k).toNat : ℕ) : ℤ)
        = Work.Analysis.EndVar.logN (Nat.floor (a m)) + k := Int.toNat_of_nonneg h4
    have h5 : (((Work.Analysis.EndVar.logN (Nat.floor (a n)) + k).toNat : ℕ) : ℤ)
        ≤ (((Work.Analysis.EndVar.logN (Nat.floor (a m)) + k).toNat : ℕ) : ℤ) := by
      rw [hx, hy]; omega
    exact_mod_cast h5
  have hσcoe : ∀ n : ℕ, ((σ n : ℕ) : ℤ) = Work.Analysis.EndVar.logN (Nat.floor (a n)) + k := by
    intro n
    rw [hσdef]
    exact Int.toNat_of_nonneg (by have h := hk n; omega)
  have hreindex : ∀ x : ℤ,
      (fun n : ℕ => Work.KMTContract.kmtProj ρ l₁
          (-(Work.Analysis.EndVar.logN (Nat.floor (a n)))) f x)
        = fun n : ℕ =>
            (fun m : ℕ => Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + (m : ℤ))) f x) (σ n) := by
    intro x
    funext n
    have h1 : (-(Work.Analysis.EndVar.logN (Nat.floor (a n))) : ℤ)
        = -((m₀ : ℤ) + ((σ n : ℕ) : ℤ)) := by
      rw [hm₀, hσcoe n]
      ring
    rw [h1]
  -- ## assembly: the lacunary family is a monotone reindexing of the dyadic one
  calc MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l₁
            (Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0) f x))
        p MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTContract.kmtProj ρ l₁
            (-(Work.Analysis.EndVar.logN (Nat.floor (a n)))) f x))
        p MeasureTheory.Measure.count := by
        congr 1
        funext x
        simp only [Work.KMTAreas.A7.Tle_varphiN_zero]
    _ ≤ MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun m : ℕ => Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + (m : ℤ))) f x))
        p MeasureTheory.Measure.count := by
        refine MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => ?_)
        rw [hreindex x, enorm_eq_self, enorm_eq_self]
        exact Work.KMTAreas.A7.variationalNorm_comp_mono_le (r := r)
          (fun m : ℕ => Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + (m : ℤ))) f x) hσmono
    _ ≤ ENNReal.ofReal (C * (1 + (l₁ : ℝ)) ^ 2) *
          MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
        simpa only [Work.KMTAreas.A7Hi.lpf] using hd l₁ m₀ hgood' f

/-- **The `hLowpass` input of the A7 assembly, assembled from the shallow and the deep half.**

This is the exact shape expected by the first argument of
`Work.KMTAreas.A7.lacunaryBumpVarEstimate_assembly`: the lacunary low-pass variational estimate
with a `(1+l₁)²` loss, at every exponent `1 < p < ∞`, for every `Λ`-lacunary family of scales. -/
theorem lowpassVar_of_parts
    (hShallow : ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r)
      (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
      ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ M : ℕ),
        M ≤ Work.KMTAreas.A7Hi2.cutLevel ρ l₁ →
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
        MeasureTheory.eLpNorm (fun x : ℤ => chainPart r
            (fun m : ℕ => lpf ρ l₁ m₀ (min m M) f x))
          p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C * (1 + (l₁ : ℝ))) *
              MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
    (hDeep : ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r)
      (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
      ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
        MeasureTheory.eLpNorm (fun x : ℤ => chainPart r
            (fun n : ℕ => if Work.KMTAreas.A7Hi2.cutLevel ρ l₁ ≤ m₀ + n
              then lpf ρ l₁ m₀ n f x else 0))
          p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count) :
    ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r)
      (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) (Λ : NNReal) (hΛ : 1 < Λ),
      ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧
        ∀ (k : ℤ) (l₁ : ℕ) (a : ℕ → NNReal)
          (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) (f : ℤ → ℂ),
          Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ k →
          (∀ n : ℕ, -(Work.Analysis.EndVar.logN (Nat.floor (a n))) ≤ k) →
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l₁
                (Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0) f x))
            p MeasureTheory.Measure.count
            ≤ ENNReal.ofReal (C * (1 + (l₁ : ℝ)) ^ 2) *
                MeasureTheory.eLpNorm f p MeasureTheory.Measure.count :=
  fun ρ hρ hρ1 r hr p hp hptop Λ hΛ =>
    lacLowpassVar_of_dyadic ρ hρ hρ1 r hr p hp hptop Λ hΛ
      (dyadicVarLe_of_chain ρ hρ hρ1 r hr p hp hptop
        (chainLe_dyadic_of_parts ρ hρ hρ1 r hr p hp hptop
          (hShallow ρ hρ hρ1 r hr p hp hptop) (hDeep ρ hρ hρ1 r hr p hp hptop)))

end

end Work.KMTPlan.A6
