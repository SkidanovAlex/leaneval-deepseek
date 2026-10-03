/-
# The low-pass variational estimate on the *core* scales (no `l₁`-free crux needed)

This module records the observation that the A6 low-pass families live on the *core* scales
`N = ⌊a n⌋`, where the model demands `N > splitCut ρ L` — i.e. the scales are vastly larger than
the arithmetic lattice `iwQl ρ l₁`.  In that regime the *decimation* route of
`Work.KMTPlan.A6.lowpassVarFromDecim` (proved) supplies the `(1 + l₁)²`-lossy low-pass
variational estimate **unconditionally** — with no use of the `l₁`-free chain/square-function
crux (`Work.KMTAreas.A7Hi.LowpassChainLe`, `A7Hi2.ChainPiece`, `A7HiRep.chainPartSqFunLeTwo`,
`A7Hi2.MeanZeroVarFree`, …).

The object here is the `cruxShift`-shaped form of that statement
(`Work.KMTPlan.A6.MdlLpH.cruxShift`), in which the base level is a *parameter* `m` and the family
is the lacunary *shift* `n ↦ Tle ρ l₁ (varphiN ⌊a (n + m)⌋ 0) g` of the Ionescu–Wainger walk.
The only new hypothesis relative to `cruxShift` is the *largeness of the base scale*
`24 · iwQl ρ l₁ ≤ ⌊a m⌋`, which is precisely what the A6 core condition supplies (see
`Work.KMTPlan.A6.iwQl_mul_le_splitCut`).

This is the replacement of the crux in the Case-A/Case-B applications of
`Work.KMTPlan.A6.mdlLowpassCaseHigh_of_crux`: in both cases the base index of the shift is a
*core* index, so the largeness hypothesis holds there.

NOTE for the g-side (scaled levels `d · logN ⌊a n⌋`): the right shape there is the *walk* form
`Work.KMTPlan.A6.walkDecimVarBound` (proved: the deep walk `n ↦ lpf ρ l C₀ (1 + n) f` has an
`ℓ²(V^R)`-bound with an **`l`-free** constant) together with the monotone reindexing
`Work.KMTAreas.A7.variationalNorm_comp_mono_le`.  Beware the syntactic trap when the reindexed
levels are written as `σ n` while the walk is indexed by `1 + n`: the two are only equal by
`Nat.sub_add_cancel` (not definitionally), and a plain `rw` inside a `variationalNorm`-application
unfolds the `iSup` and fails — prove the *family* equality first and use the `le_of_eq … .trans`
form (`(congrArg (fun w => variationalNorm R w) hfun).le.trans hcomp`, where `hfun` is the
`funext`-ed family equality proved by `omega` on `1 + (σ n - 1) = σ n`).
-/
import Mathlib
import Submission.Work.KMTPlan.A6.lowpassVarFromDecim
import Submission.Work.KMTAreas.A7.lacunaryIWProjLowpassVar
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTAreas.A7

/-- `N / 2 ≤ 2 ^ (logN N).toNat`: the dyadic level `logN N` recovers the scale `N` up to the
factor `2` (`N < 2 ^ (logN N + 1)`). -/
lemma le_two_pow_logN_div (N : ℕ) :
    N / 2 ≤ 2 ^ (Work.Analysis.EndVar.logN N).toNat := by
  have h1 : Work.Analysis.EndVar.logN N = (Nat.log 2 (max N 2) : ℤ) := rfl
  have h2 : ((Work.Analysis.EndVar.logN N).toNat) = Nat.log 2 (max N 2) := by
    rw [h1]; exact Int.toNat_natCast _
  rw [h2]
  have h3 : max N 2 < 2 ^ (Nat.log 2 (max N 2) + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) _
  have h4 : N ≤ max N 2 := le_max_left _ _
  have h5 : 2 ^ (Nat.log 2 (max N 2) + 1) = 2 * 2 ^ (Nat.log 2 (max N 2)) := by
    rw [pow_succ]; ring
  omega

/-- **The low-pass variational estimate on the core scales, in the `cruxShift` shape.**

For `0 < ρ ≤ 1`, `2 < R`, `Λ > 1` there are `Cρ > 0` and `C > 0` such that for every `Λ`-lacunary
family `a : ℕ → ℝ≥0` with `a n ≥ 1`, every shift `m : ℕ`, every height `l₁ : ℕ` and every
`g : ℤ → ℂ`:

if the base level has *good major arcs*, `GoodMajorArcs ρ Cρ l₁ (-(logN ⌊a m⌋))`, and the base
*scale is large*, `24 · iwQl ρ l₁ ≤ ⌊a m⌋`, then the shifted lacunary walk
`n ↦ Tle ρ l₁ (varphiN ⌊a (n + m)⌋ 0) g` (which is the IW projection
`n ↦ kmtProj ρ l₁ (-(logN ⌊a (n + m)⌋)) g`) satisfies

  `‖ V^R_n (·) ‖_{ℓ²(ℤ)} ≤ C (1 + l₁)² ‖g‖_{ℓ²(ℤ)}`.

Proof: apply `Work.KMTPlan.A6.lowpassVarFromDecim` to the shifted lacunary family
`n ↦ a (n + m)`, whose scales are all `≥ ⌊a m⌋` and hence all in the decimation regime; the level
identity `Tle ρ l₁ (varphiN N 0) = kmtProj ρ l₁ (-(logN N))` (`Work.KMTAreas.A7.Tle_varphiN_zero`)
converts the walk to the projection family.  This is verbatim the proof of
`Work.KMTPlan.A6.MdlLpH.cruxShift`, with the `l₁`-free crux replaced by the decimation estimate and
the extra largeness hypothesis on the base scale. -/
theorem lowpassVarOnCore (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (R : NNReal) (hR : 2 < R)
    (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (m l₁ : ℕ) (a : ℕ → NNReal),
        PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) → ∀ g : ℤ → ℂ,
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁
            (-(Work.Analysis.EndVar.logN (Nat.floor (a m)))) →
        24 * Work.Analysis.IonescuWainger.iwQl ρ l₁ ≤ Nat.floor (a m) →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
            (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l₁
              (Work.KMTAreas.A7.varphiN (Nat.floor (a (n + m))) 0) g x))
          2 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (1 + (l₁ : ℝ)) ^ 2) *
            MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  obtain ⟨Cρ, hCρ, C, hC, hmain⟩ := lowpassVarFromDecim ρ hρ hρ1 R hR Λ hΛ
  refine ⟨Cρ, hCρ, C, hC, ?_⟩
  intro m l₁ a ha ha1 g hGMA hbig
  -- `a` is monotone, hence so is `n ↦ logN ⌊a n⌋`
  have hmonoA : Monotone a := Work.KMTAreas.A7.lowpass_monotone_of_lacunary hΛ ha ha1
  have hmonoFloor : Monotone fun n : ℕ => Nat.floor (a n) :=
    fun n m hnm => Nat.floor_mono (hmonoA hnm)
  -- the level `k = -logN ⌊a m⌋` dominates every level of the shifted family
  have hlev : ∀ n : ℕ, -(Work.Analysis.EndVar.logN (Nat.floor (a (n + m))))
      ≤ -(Work.Analysis.EndVar.logN (Nat.floor (a m))) := by
    intro n
    have hmn : m ≤ n + m := Nat.le_add_left m n
    have h3 : Work.Analysis.EndVar.logN (Nat.floor (a m))
        ≤ Work.Analysis.EndVar.logN (Nat.floor (a (n + m))) :=
      Work.Analysis.EndVar.logN_mono (Nat.floor_mono (hmonoA hmn))
    exact neg_le_neg h3
  -- the shifted family is `Λ`-lacunary with `a (n + m) ≥ 1`
  have hshift : PointwiseErgodicTheorems.Lacunary Λ (fun n : ℕ => a (n + m)) := by
    intro n
    change a (n + 1 + m) / a (n + m) > Λ
    rw [show n + 1 + m = n + m + 1 from by omega]
    exact ha (n + m)
  -- the shifted scales are all large: the base largeness propagates by monotonicity
  have hbig' : ∀ n : ℕ, 6 * Work.Analysis.IonescuWainger.iwQl ρ l₁
      ≤ 2 ^ (Work.Analysis.EndVar.logN (Nat.floor (a (n + m)))).toNat := by
    intro n
    have hle : Nat.floor (a m) ≤ Nat.floor (a (n + m)) := hmonoFloor (Nat.le_add_left m n)
    have hhalf := le_two_pow_logN_div (Nat.floor (a (n + m)))
    -- `12 * iwQl ≤ ⌊a m⌋ / 2 ≤ ⌊a (n+m)⌋ / 2 ≤ 2 ^ logN ⌊a (n+m)⌋`
    have h1 : 12 * Work.Analysis.IonescuWainger.iwQl ρ l₁ ≤ Nat.floor (a (n + m)) / 2 := by
      omega
    have h2 : 6 * Work.Analysis.IonescuWainger.iwQl ρ l₁
        ≤ 12 * Work.Analysis.IonescuWainger.iwQl ρ l₁ := by
      have hpos : 0 < Work.Analysis.IonescuWainger.iwQl ρ l₁ :=
        Work.Analysis.IonescuWainger.iwQl_pos
      omega
    exact le_trans h2 (le_trans h1 hhalf)
  simp only [Work.KMTAreas.A7.Tle_varphiN_zero]
  exact hmain (-(Work.Analysis.EndVar.logN (Nat.floor (a m)))) l₁ (fun n : ℕ => a (n + m))
    hshift (fun n => ha1 (n + m)) g hGMA hlev hbig'

/-- **The monotone reindexing of the deep walk keeps its unconditional variational bound**
(stated in the form the g-side needs; see the module docstring for the proof recipe and the
syntactic trap).  -/
theorem walkVarOfMonotoneReindex (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (R : NNReal) (hR : 2 < R) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (l C₀ : ℕ) (σ : ℕ → ℕ), Monotone σ → (∀ n : ℕ, 1 ≤ σ n) → ∀ f : ℤ → ℂ,
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l (-(C₀ : ℤ)) →
        3 * Work.Analysis.IonescuWainger.iwQl ρ l < 2 ^ C₀ →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l C₀ (σ n) f x))
          2 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
  obtain ⟨Cρ, hCρpos, C, hCpos, hwalk⟩ := walkDecimVarBound ρ hρ hρ1 R hR 2 (by norm_num)
  -- the exponent `ofReal 2` of `walkDecimVarBound` is the `ENNReal`-exponent `2`
  have hwalk' : ∀ (l C₀ : ℕ), Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l (-(C₀ : ℤ)) →
      3 * Work.Analysis.IonescuWainger.iwQl ρ l < 2 ^ C₀ → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l C₀ (1 + n) f x))
        2 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
    intro l C₀ hg hn f
    have h := hwalk l C₀ hg hn f
    rw [ENNReal.ofReal_ofNat 2] at h
    exact h
  refine ⟨Cρ, hCρpos, C, hCpos, ?_⟩
  intro l C₀ σ hσmono hσ1 f hgood hnarrow
  have hid : ∀ n : ℕ, 1 + (σ n - 1) = σ n := fun n => by
    have h1 := hσ1 n
    omega
  have hfun : ∀ x : ℤ, (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l C₀ (σ n) f x)
      = (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l C₀ (1 + (σ n - 1)) f x) := by
    intro x
    funext n
    rw [hid n]
  have hcomp : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l C₀ (1 + (σ n - 1)) f x)
      ≤ PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l C₀ (1 + n) f x) := by
    intro x
    exact Work.KMTAreas.A7.variationalNorm_comp_mono_le (r := R)
      (u := fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l C₀ (1 + n) f x)
      (φ := fun n : ℕ => σ n - 1) (by
        intro i j hij
        exact Nat.sub_le_sub_right (hσmono hij) 1)
  have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l C₀ (σ n) f x)
      ≤ PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l C₀ (1 + n) f x) := by
    intro x
    exact (congrArg (fun w : ℕ → ℂ => PointwiseErgodicTheorems.variationalNorm R w)
      (hfun x)).le.trans (hcomp x)
  refine (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => hpt x)).trans
    (hwalk' l C₀ hgood hnarrow f)

end

end Work.KMTPlan.A6
