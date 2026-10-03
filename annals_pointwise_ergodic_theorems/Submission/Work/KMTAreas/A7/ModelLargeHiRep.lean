/-
# The §8 large-scale estimate for the *repaired* §6 model tuple (`modelTupleRep`)

Krause--Mirek--Tao, *Pointwise ergodic theorems for non-conventional bilinear polynomial
averages*, Annals of Math. 195 (3) 2022, §8.

The target `Work.KMTAreas.A7.ModelLargeHiRep` is the model-tuple bound of §8 for the repaired
model `Work.KMTAreas.A7.modelTupleRep` of `Large/Defs.lean`: the twisted bilinear model whose
symbol has the band `uRep ρ l₁ l₂ k₁ k₂ = max (uScale ρ L) (max l₁ l₂ + 3)`
(`L = max (max l₁ l₂) (max k₁ k₂)`), i.e. the plateau `2^{-2·uRep}` is *narrower* than the
separation `2^{-2 max(l₁,l₂)}` of the exact-height arithmetic fibres, and which is additionally
guarded by the band condition `bandCond : k + 1 + 2·uRep ≤ Log N`.

The file follows the assembly of `Work.KMTAreas.A7.ModelLargeHi` (which does the same for the
unrepaired `modelTuple`), with `uScale ρ L` replaced by `uRep ρ l₁ l₂ k₁ k₂` and the two clipped
families `Hcl`, `Gcl` replaced by their band-clipped versions `HclRep`, `GclRep`:

* `modelTupleRep_variationalPointwise` (proved here) — the pointwise fibre factorisation
  (paper `form-1`): `BtwistExact` is the `n₀`-average of the products of the two fibres, so the
  variational norm of the model tuple is bounded by the `t`-integral of the `n₀`-average of the
  products of the fibre variational norms;
* `LinVarRep`, `LinVarGRep` (proved here) — the linear lacunary variational estimates (paper
  `(lin-1)`, `(lin-2)`) for the band-clipped families, derived from `A7Hi.LinVar` / `A7Hi.LinVarG`
  by the clipping lemma `variationalNorm_clip_of_upwardClosed`;
* `FiberVarSamplingRepBdd` (proved in `Submission/Work/KMTAreas/A7/FiberVarSamplingRepBdd.lean`)
  and `A7Rescue.fiberVarSamplingGRep_bdd` (proved in
  `Submission/Work/KMTAreas/A7Rescue/FiberVarSamplingGRep.lean`) — the fibre
  variational sampling estimates of §8, with `uRep` in place of `uScale ρ L` and with the clipped
  families.  These are the two analytic inputs of the assembly; they are the `uRep`-analogues of
  `A7Hi.FiberVarSampling` / `A7Hi.FiberVarSamplingG`.

The remaining obligations are therefore exactly the four analytic inputs listed above: the two
fibre estimates and the two low-pass pieces `A7Hi.lowpassNarrowVar` / `A7Hi2.lowpassVarG` that
`A7Hi.LinVar` / `A7Hi.LinVarG` (hence `LinVarRep` / `LinVarGRep`) still rest on.  See
`NOTES_A7_ModelLargeHiRep_SESSION.md` for the route of each.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.Hi.Pointwise
import Submission.Work.KMTAreas.A7.eLpNorm_lintegral_le
import Submission.Work.KMTAreas.A7.variationalNorm_clip_le
import Submission.Work.KMTAreas.A7Hi.LinVarG
import Submission.Work.KMTAreas.A7Hi.lowpassNarrowVarRep
import Submission.Work.KMTAreas.A7Rescue.FiberVarSamplingGRep
import Submission.Work.KMTAreas.A7.lacunaryBumpBadPartBound
import Submission.Work.KMTAreas.A7.lacunaryBumpLowpassClipBoundGen
import Submission.Work.KMTAreas.A7.FiberVarSamplingRepBdd
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.EndVar

/-- The `f`-side family of the repaired §6 model: the exact-height IW projection of `f` against
the modulated bump `φ_{N,t}` at the scale `N = ⌊a n⌋`, clipped both at the index set `core` and at
the band condition `bandCond` of the repaired model. -/
def HclRep (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ) :
    ℕ → ℤ → ℂ :=
  fun n => if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) then
    Tex ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f else 0

/-- The `g`-side family of the repaired §6 model. -/
def GclRep (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ)
    (g : ℤ → ℂ) : ℕ → ℤ → ℂ :=
  fun n => if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) then
    Tex ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g else 0

theorem HclRep_apply_of {ρ : ℝ} {C₀ : ℕ} {a : ℕ → NNReal} {l₁ l₂ k₁ k₂ n : ℕ} {t : ℝ}
    {f : ℤ → ℂ}
    (h : core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))) :
    HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f n
      = Tex ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f := by
  simp only [HclRep, if_pos h]

theorem GclRep_apply_of {ρ : ℝ} {P : ℤ[X]} {C₀ : ℕ} {a : ℕ → NNReal} {l₁ l₂ k₁ k₂ n : ℕ}
    {t : ℝ} {g : ℤ → ℂ}
    (h : core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))) :
    GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g n
      = Tex ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g := by
  simp only [GclRep, if_pos h]

/-- The band-clipped family is the `bandCond`-clipping of the `core`-clipped family `Hcl`. -/
theorem HclRep_eq_ite (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ)
    (f : ℤ → ℂ) (n : ℕ) :
    HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f n =
      if bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) then Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n else 0 := by
  by_cases hb : bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))
  · by_cases hc : core ρ C₀ l₁ l₂ k₁ k₂ a n
    · simp only [HclRep, Hcl, hb, hc, if_true, if_false, true_and, and_true]
    · simp only [HclRep, Hcl, hb, hc, if_true, if_false, true_and, and_true, false_and, and_false]
  · simp only [HclRep, Hcl, hb, if_true, if_false, true_and, and_true, false_and, and_false]

/-- The band-clipped family is the `bandCond`-clipping of the `core`-clipped family `Gcl`. -/
theorem GclRep_eq_ite (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ)
    (g : ℤ → ℂ) (n : ℕ) :
    GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g n =
      if bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) then Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t g n else 0 := by
  by_cases hb : bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))
  · by_cases hc : core ρ C₀ l₁ l₂ k₁ k₂ a n
    · simp only [GclRep, Gcl, hb, hc, if_true, if_false, true_and, and_true]
    · simp only [GclRep, Gcl, hb, hc, if_true, if_false, true_and, and_true, false_and, and_false]
  · simp only [GclRep, Gcl, hb, if_true, if_false, true_and, and_true, false_and, and_false]

/-- **The repaired model tuple is the `t`-integral of the twisted bilinear form at the exact
heights**, applied to the band-clipped families. -/
theorem modelTupleRep_eq_intervalIntegral (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → NNReal)
    (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) :
    modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ =
      fun n x => ∫ t in (1/2 : ℝ)..1,
        BtwistExact ρ P l₁ l₂ (mStarF (uRep ρ l₁ l₂ k₁ k₂))
          (mStargF P.natDegree (uRep ρ l₁ l₂ k₁ k₂))
          (HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f n) (GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g n) x := by
  funext n x
  have hguard : (inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n)) ∧
        splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < Nat.floor (a n) ∧
        mainRegime ρ k₁ k₂ (Nat.floor (a n)) ∧ bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)))
      ↔ core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) := by
    simp only [core]; tauto
  by_cases h : core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))
  · rw [modelTupleRep]
    simp only [if_pos (hguard.mpr h)]
    apply intervalIntegral.integral_congr
    intro t ht
    have hH : HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f n
        = Tex ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f := HclRep_apply_of h
    have hG : GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g n
        = Tex ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g := GclRep_apply_of h
    simp only [hH, hG]
  · rw [modelTupleRep]
    simp only [if_neg (fun hh => h (hguard.mp hh))]
    have hH : ∀ t : ℝ, HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f n = 0 := by
      intro t
      simp only [HclRep, if_neg h]
    have hzero : (fun t : ℝ => BtwistExact ρ P l₁ l₂ (mStarF (uRep ρ l₁ l₂ k₁ k₂))
        (mStargF P.natDegree (uRep ρ l₁ l₂ k₁ k₂))
        (HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f n) (GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g n) x)
        = fun _ : ℝ => (0 : ℂ) := by
      funext t
      rw [hH t]
      exact congrFun (Hi.BtwistExact_zero_left ρ P l₁ l₂ _ _
        (GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g n)) x
    rw [hzero]
    simp

/-! ## The pointwise fibre factorisation of the repaired model tuple -/

/-- **The pointwise variational estimate for the repaired model tuple.**  The right-hand side is
built from the fibres of the *same* exact-height frequency sets that `modelTupleRep` uses, and
with the *same* band `uRep`, so that it can be fed to the fibre sampling estimates.  This is the
`uRep`-analogue of `Work.KMTAreas.A7.Hi.modelTuple_variationalPointwiseHi`. -/
theorem modelTupleRep_variationalPointwise (ρ : ℝ) (hρ : 0 < ρ) (P : Polynomial ℤ)
    (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (r : NNReal) (hr : 2 < r) (f g : ℤ → ℂ)
    (hf : ∃ Cf : ℝ, ∀ y : ℤ, ‖f y‖ ≤ Cf) (hg : ∃ Cg : ℝ, ∀ y : ℤ, ‖g y‖ ≤ Cg) (n : ℕ) (x : ℤ) :
    PointwiseErgodicTheorems.variationalNorm r
        (fun m : ℕ => modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ m x) ≤
      ∫⁻ t in Set.Ioc (1/2 : ℝ) 1, (arithQ ρ (max l₁ l₂) : ENNReal)⁻¹ *
        ∑ n₀ ∈ Finset.range (arithQ ρ (max l₁ l₂)),
          PointwiseErgodicTheorems.variationalNorm r
            (fun m : ℕ => fiberOpSet (iwArithFreqsNew ρ l₁)
              (mStarF (uRep ρ l₁ l₂ k₁ k₂)) n₀
              (HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f m) x) *
          PointwiseErgodicTheorems.variationalNorm r
            (fun m : ℕ => fiberOpPSet P (iwArithFreqsNew ρ l₂)
              (mStargF P.natDegree (uRep ρ l₁ l₂ k₁ k₂)) n₀
              (GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g m) x) := by
  obtain ⟨Cf, hf'⟩ := hf
  obtain ⟨Cg, hg'⟩ := hg
  obtain ⟨hw₁, _, hw₁'⟩ := cw_etaCut_decay (-(2 * (uRep ρ l₁ l₂ k₁ k₂ : ℤ)))
  obtain ⟨hw₂, _, hw₂'⟩ :=
    cw_etaCut_decay (-((P.natDegree : ℤ) * 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℤ)))
  have hdec₁ : ∃ Cd : ℝ, ∀ j : ℤ, ‖cw (mStarF (uRep ρ l₁ l₂ k₁ k₂)) j‖
      ≤ Cd / (1 + |(j : ℝ)|) ^ 2 :=
    ⟨hw₁, fun j => by simpa only [mStarF] using hw₁' j⟩
  have hdec₂ : ∃ Cd : ℝ, ∀ j : ℤ,
      ‖cw (mStargF P.natDegree (uRep ρ l₁ l₂ k₁ k₂)) j‖
        ≤ Cd / (1 + |(j : ℝ)|) ^ 2 :=
    ⟨hw₂, fun j => by simpa only [mStargF] using hw₂' j⟩
  have hKern : ∃ K : ℝ, ∀ j₁ j₂ : ℤ, ‖arithKernelSet P (arithQ ρ (max l₁ l₂))
      (iwArithFreqsNew ρ l₁) (iwArithFreqsNew ρ l₂) j₁ j₂‖ ≤ K :=
    ⟨_, fun j₁ j₂ => norm_arithKernelSet_le P _ _ _ j₁ j₂⟩
  have hboundF : ∀ m : ℕ, ∃ C : ℝ, ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ y : ℤ,
      ‖HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f m y‖ ≤ C := by
    intro m
    obtain ⟨⟨hbm, hbm'⟩, _⟩ := iwConv_varphiNt_bounded_measurable (iwArithFreqsNew ρ l₁)
      (Nat.floor (a m)) k₁ f Cf hf'
    refine ⟨max hbm 0, fun t ht y => ?_⟩
    by_cases hc : core ρ C₀ l₁ l₂ k₁ k₂ a m ∧ bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a m))
    · rw [HclRep_apply_of hc]
      exact le_trans (hbm' t ht y) (le_max_left _ _)
    · simp only [HclRep, if_neg hc, Pi.zero_apply, norm_zero]
      exact le_max_right _ _
  have hboundG : ∀ m : ℕ, ∃ C : ℝ, ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ y : ℤ,
      ‖GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g m y‖ ≤ C := by
    intro m
    obtain ⟨⟨hbm, hbm'⟩, _⟩ := iwConv_varphitildeNt_bounded_measurable P (iwArithFreqsNew ρ l₂)
      (Nat.floor (a m)) k₂ g Cg hg'
    refine ⟨max hbm 0, fun t ht y => ?_⟩
    by_cases hc : core ρ C₀ l₁ l₂ k₁ k₂ a m ∧ bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a m))
    · rw [GclRep_apply_of hc]
      exact le_trans (hbm' t ht y) (le_max_left _ _)
    · simp only [GclRep, if_neg hc, Pi.zero_apply, norm_zero]
      exact le_max_right _ _
  have hmeasF : ∀ m : ℕ, ∀ y : ℤ,
      Measurable (fun t : ℝ => HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f m y) := by
    intro m y
    by_cases hc : core ρ C₀ l₁ l₂ k₁ k₂ a m ∧ bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a m))
    · have hfun : (fun t : ℝ => HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f m y)
          = fun t : ℝ => Tex ρ l₁ (varphiNt (Nat.floor (a m)) k₁ t) f y := by
        funext t; exact congrFun (HclRep_apply_of hc) y
      rw [hfun]
      exact (iwConv_varphiNt_bounded_measurable (iwArithFreqsNew ρ l₁)
        (Nat.floor (a m)) k₁ f Cf hf').2 y
    · have hfun : (fun t : ℝ => HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f m y) = fun _ : ℝ => 0 := by
        funext t
        simp only [HclRep, hc, if_false, Pi.zero_apply]
      rw [hfun]; exact measurable_const
  have hmeasG : ∀ m : ℕ, ∀ y : ℤ,
      Measurable (fun t : ℝ => GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g m y) := by
    intro m y
    by_cases hc : core ρ C₀ l₁ l₂ k₁ k₂ a m ∧ bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a m))
    · have hfun : (fun t : ℝ => GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g m y)
          = fun t : ℝ => Tex ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a m)) k₂ t) g y := by
        funext t; exact congrFun (GclRep_apply_of hc) y
      rw [hfun]
      exact (iwConv_varphitildeNt_bounded_measurable P (iwArithFreqsNew ρ l₂)
        (Nat.floor (a m)) k₂ g Cg hg').2 y
    · have hfun : (fun t : ℝ => GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g m y) = fun _ : ℝ => 0 := by
        funext t
        simp only [GclRep, hc, if_false, Pi.zero_apply]
      rw [hfun]; exact measurable_const
  have hZ : ∀ m : ℕ, Integrable (fun t : ℝ => BtwistExact ρ P l₁ l₂
      (mStarF (uRep ρ l₁ l₂ k₁ k₂))
      (mStargF P.natDegree (uRep ρ l₁ l₂ k₁ k₂))
      (HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f m) (GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g m) x)
      (volume.restrict (Set.Ioc (1/2 : ℝ) 1)) := by
    intro m
    obtain ⟨C, hC⟩ := exists_bound_BtwistSet_uniform ρ P l₁ l₂
      (iwArithFreqsNew ρ l₁) (iwArithFreqsNew ρ l₂)
      (mStarF (uRep ρ l₁ l₂ k₁ k₂))
      (mStargF P.natDegree (uRep ρ l₁ l₂ k₁ k₂))
      (fun t : ℝ => HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f m)
      (fun t : ℝ => GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g m)
      x hKern hdec₁ hdec₂ (hboundF m) (hboundG m)
    refine Integrable.of_bound ?_ C ?_
    · refine (Measurable.tsum (fun j₁ : ℤ => Measurable.tsum (fun j₂ : ℤ => ?_))).aestronglyMeasurable
      exact (measurable_const.mul (hmeasF m (x - j₁))).mul (hmeasG m (x - j₂))
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
      exact hC t (Set.Ioc_subset_Icc_self ht)
  have hdecomp : ∀ t ∈ Set.Ioc (1/2 : ℝ) 1, ∀ m : ℕ,
      BtwistExact ρ P l₁ l₂
        (mStarF (uRep ρ l₁ l₂ k₁ k₂))
        (mStargF P.natDegree (uRep ρ l₁ l₂ k₁ k₂))
        (HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f m) (GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g m) x
        = ((arithQ ρ (max l₁ l₂) : ℂ))⁻¹ *
            ∑ n₀ ∈ Finset.range (arithQ ρ (max l₁ l₂)),
              fiberOpSet (iwArithFreqsNew ρ l₁)
                (mStarF (uRep ρ l₁ l₂ k₁ k₂)) (n₀ : ℤ)
                (HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f m) x
              * fiberOpPSet P (iwArithFreqsNew ρ l₂)
                  (mStargF P.natDegree (uRep ρ l₁ l₂ k₁ k₂)) (n₀ : ℤ)
                  (GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g m) x := by
    intro t ht m
    have hF : ∃ C : ℝ, ∀ y : ℤ, ‖HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f m y‖ ≤ C :=
      ⟨Classical.choose (hboundF m), fun y => Classical.choose_spec (hboundF m) t
        (Set.Ioc_subset_Icc_self ht) y⟩
    have hG : ∃ C : ℝ, ∀ y : ℤ, ‖GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g m y‖ ≤ C :=
      ⟨Classical.choose (hboundG m), fun y => Classical.choose_spec (hboundG m) t
        (Set.Ioc_subset_Icc_self ht) y⟩
    have hC₁ : ∃ Ca : ℝ, ∀ y : ℤ, ‖arithCharSet (iwArithFreqsNew ρ l₁) y‖ ≤ Ca :=
      ⟨_, fun y => norm_arithCharSet_le _ y⟩
    have hC₂ : ∃ Ca : ℝ, ∀ y : ℤ, ‖arithCharSet (iwArithFreqsNew ρ l₂) y‖ ≤ Ca :=
      ⟨_, fun y => norm_arithCharSet_le _ y⟩
    have h := BtwistSet_eq_fiberSum ρ P l₁ l₂ (iwArithFreqsNew ρ l₁) (iwArithFreqsNew ρ l₂)
      (mStarF (uRep ρ l₁ l₂ k₁ k₂))
      (mStargF P.natDegree (uRep ρ l₁ l₂ k₁ k₂))
      (HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f m) (GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g m) x
      (fun n₀ => summable_fiberSet_family _ _ _ x hdec₁ hC₁ hF n₀)
      (fun n₀ => summable_fiberSet_family _ _ _ x hdec₂ hC₂ hG (P.eval n₀))
    simpa only [BtwistSet_iwArithFreqsNew] using h
  have hmod : (fun m : ℕ => modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ m x)
      = fun m : ℕ => ∫ t in (1/2 : ℝ)..1, BtwistExact ρ P l₁ l₂
          (mStarF (uRep ρ l₁ l₂ k₁ k₂))
          (mStargF P.natDegree (uRep ρ l₁ l₂ k₁ k₂))
          (HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f m) (GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g m) x := by
    funext m
    exact congrFun (congrFun (modelTupleRep_eq_intervalIntegral ρ P C₀ a f g l₁ l₂ k₁ k₂) m) x
  rw [hmod]
  exact Work.KMTAreas.A7Hi.VarNormIntegralFiber r hr (arithQ ρ (max l₁ l₂)) (arithQ_pos ρ _)
      (fun t m => BtwistExact ρ P l₁ l₂
        (mStarF (uRep ρ l₁ l₂ k₁ k₂))
        (mStargF P.natDegree (uRep ρ l₁ l₂ k₁ k₂))
        (HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f m) (GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g m) x)
      (fun t n₀ m => fiberOpSet (iwArithFreqsNew ρ l₁)
        (mStarF (uRep ρ l₁ l₂ k₁ k₂)) n₀
        (HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f m) x)
      (fun t n₀ m => fiberOpPSet P (iwArithFreqsNew ρ l₂)
        (mStargF P.natDegree (uRep ρ l₁ l₂ k₁ k₂)) n₀
        (GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g m) x)
      hZ hdecomp

/-! ## Clipping a family at a tail does not increase the variational norm by more than `2` -/

/-- The variational norm of the zero sequence vanishes (`1 ≤ r`). -/
theorem variationalNorm_zero' (r : NNReal) (hr : 1 ≤ r) :
    PointwiseErgodicTheorems.variationalNorm r (0 : ℕ → ℂ) = 0 := by
  have h := Submission.PointwiseErgodicTheorems.variationalNorm_smul (r := r) hr (0 : ℂ)
    (0 : ℕ → ℂ)
  simpa using h

/-- **Clipping a family at a tail** (an upward-closed predicate of the index) increases the
variational norm by at most a factor `2`.  The only new increment is the single jump `0 → u n₀`
at the boundary, paid for by the supremum part. -/
theorem variationalNorm_clip_of_tail (r : NNReal) (hr : 1 ≤ r) {P : ℕ → Prop} [DecidablePred P]
    (hP : ∀ n m : ℕ, n ≤ m → P n → P m) (u : ℕ → ℂ) :
    PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => if P n then u n else 0)
      ≤ 2 * PointwiseErgodicTheorems.variationalNorm r u := by
  by_cases hex : ∃ n, P n
  · have hspec : P (Nat.find hex) := Nat.find_spec hex
    have hiff : ∀ n : ℕ, P n ↔ Nat.find hex ≤ n := fun n =>
      ⟨fun h => Nat.find_min' hex h, fun h => hP (Nat.find hex) n h hspec⟩
    have hfun : (fun n : ℕ => if P n then u n else 0)
        = fun n : ℕ => if Nat.find hex ≤ n then u n else 0 := by
      funext n
      by_cases hp : P n
      · rw [if_pos hp, if_pos ((hiff n).mp hp)]
      · have hp' : ¬ (Nat.find hex ≤ n) := fun h => hp ((hiff n).mpr h)
        rw [if_neg hp, if_neg hp']
    rw [hfun]
    refine (variationalNorm_clip_le r hr u (Nat.find hex)).trans ?_
    have hshift := Work.KMTAreas.A7.variationalNorm_tail_le (r := r) (Nat.find hex) u
    calc PointwiseErgodicTheorems.variationalNorm r (fun j : ℕ => u (j + Nat.find hex))
          + PointwiseErgodicTheorems.variationalNorm r (fun j : ℕ => u (j + Nat.find hex))
        ≤ PointwiseErgodicTheorems.variationalNorm r u
          + PointwiseErgodicTheorems.variationalNorm r u := add_le_add hshift hshift
      _ = 2 * PointwiseErgodicTheorems.variationalNorm r u := by ring
  · push_neg at hex
    have hfun : (fun n : ℕ => if P n then u n else 0) = (0 : ℕ → ℂ) := by
      funext n
      simp only [hex n, if_false, Pi.zero_apply]
    rw [hfun, variationalNorm_zero' r hr]
    exact bot_le

/-! ## The linear lacunary variational estimates for the band-clipped families -/

/-- **`(lin-1)` for the band-clipped family** `HclRep`: the paper's linear lacunary variational
estimate, with the clipping at `bandCond` handled by `variationalNorm_clip_of_tail`. -/
theorem LinVarRep (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (r : NNReal) (hr : 2 < r) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∀ (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
      ∃ C : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
          t ∈ Set.Icc (1/2 : ℝ) 1 →
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f n x)) p MeasureTheory.Measure.count
            ≤ (C Λ : ENNReal) * ENNReal.ofReal (lossWeight A ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  -- the §8 assembly, with the *proved* low-pass piece `A7Hi.lowpassNarrowVarRep` in place of the
  -- stub `A7Hi.lowpassNarrowVar` used by `A7Hi.LinVar`
  obtain ⟨A, hA, ρ₀, hρ₀, H⟩ :
      ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∀ (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
        ∃ C : NNReal → NNReal,
          ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ),
            1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
            t ∈ Set.Icc (1/2 : ℝ) 1 →
            MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n x)) p MeasureTheory.Measure.count
              ≤ (C Λ : ENNReal) * ENNReal.ofReal (lossWeight A ρ l₁ l₂ k₁ k₂) *
                  MeasureTheory.eLpNorm f p MeasureTheory.Measure.count :=
    Work.KMTAreas.A7.lacunaryBumpVarEstimate_assembly
      (fun ρ hρ hρ1 r hr p hp hptop Λ hΛ =>
        Work.KMTAreas.A7Hi.lowpassNarrowVarRep ρ hρ hρ1 r hr p hp hptop Λ hΛ)
      (fun ρ hρ hρ1 C₀ Cρc Cρ hCρpos hCρc Λ hΛ r hr p hp hptop C hCpos =>
        Work.KMTAreas.A7.lacunaryBumpLowpassClipBoundGen ρ hρ hρ1 C₀ Cρc Cρ hCρpos hCρc
          Λ hΛ r hr p hp hptop C hCpos)
      (fun ρ hρ hρ1 C₀ hC₀ hρC Cρc hCρc Λ hΛ r hr p hp hptop =>
        Work.KMTAreas.A7.lacunaryBumpBadPartBound ρ hρ hρ1 C₀ hC₀ hρC Cρc hCρc Λ hΛ r hr p hp hptop)
      C₀ hC₀ r hr
  refine ⟨A, hA, ρ₀, hρ₀, ?_⟩
  intro ρ hρ hρle p hp hptop
  obtain ⟨C, hC⟩ := H ρ hρ hρle p hp hptop
  refine ⟨fun Λ => 2 * C Λ, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ t f hΛ ha ha1 ht
  -- the band condition, as a predicate of `n`, is a tail
  have hmono : Monotone (fun n : ℕ => Nat.floor (a n)) := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    have hdiv := ha n
    have ha0 : (0 : NNReal) < a n := lt_of_lt_of_le one_pos (ha1 n)
    have hlt : a n < a (n + 1) := by
      have hmul : Λ * a n < a (n + 1) := by
        have h := mul_lt_mul_of_pos_right hdiv ha0
        rwa [div_mul_cancel₀ _ (ne_of_gt ha0)] at h
      have hle : a n ≤ Λ * a n := by
        nth_rewrite 1 [← one_mul (a n)]
        exact mul_le_mul_of_nonneg_right (le_of_lt hΛ) (zero_le : (0 : NNReal) ≤ a n)
      exact lt_of_le_of_lt hle hmul
    have hle : a n ≤ a (n + 1) := le_of_lt hlt
    exact Nat.floor_mono hle
  have hP : ∀ n m : ℕ, n ≤ m →
      bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) → bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a m)) := by
    intro n m hnm hn
    have hlog : (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat
        ≤ (Work.Analysis.EndVar.logN (Nat.floor (a m))).toNat :=
      Int.toNat_le_toNat (Work.Analysis.EndVar.logN_mono (hmono hnm))
    exact ⟨le_trans hn.1 hlog, le_trans hn.2 hlog⟩
  have hpt : ∀ x : ℤ, ‖PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f n x)‖ₑ
      ≤ (2 : ENNReal) * ‖PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n x)‖ₑ := by
    intro x
    rw [enorm_eq_self, enorm_eq_self]
    have hfun : (fun n : ℕ => HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f n x)
        = fun n : ℕ => if bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) then
            Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n x else 0 := by
      funext n
      rw [HclRep_eq_ite]
      by_cases hb : bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))
      · simp only [hb, if_true]
      · simp only [hb, if_false, Pi.zero_apply]
    rw [hfun]
    exact variationalNorm_clip_of_tail r (le_trans (by norm_num) (le_of_lt hr)) hP
      (fun n : ℕ => Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n x)
  calc MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f n x)) p MeasureTheory.Measure.count
      ≤ (2 : NNReal) • MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n x)) p MeasureTheory.Measure.count :=
        eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' (hf := by pw_aesm) (Eventually.of_forall hpt) p
    _ = (2 : ENNReal) * MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n x)) p MeasureTheory.Measure.count := by
        rw [ENNReal.smul_def, smul_eq_mul]
        norm_num
    _ ≤ (2 : ENNReal) * ((C Λ : ENNReal) * ENNReal.ofReal (lossWeight A ρ l₁ l₂ k₁ k₂) *
          MeasureTheory.eLpNorm f p MeasureTheory.Measure.count) := by
        refine mul_le_mul_of_nonneg_left ?_ bot_le
        exact hC a Λ l₁ l₂ k₁ k₂ t f hΛ ha ha1 ht
    _ = ((2 * C Λ : NNReal) : ENNReal) * ENNReal.ofReal (lossWeight A ρ l₁ l₂ k₁ k₂) *
          MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
        push_cast
        ring

/-- **`(lin-2)` for the band-clipped family** `GclRep`: the `g`-side linear lacunary variational
estimate, with the clipping at `bandCond` handled by `variationalNorm_clip_of_tail`. -/
theorem LinVarGRep (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (r : NNReal) (hr : 2 < r) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∀ (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
      ∃ C : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
          t ∈ Set.Icc (1/2 : ℝ) 1 →
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g n x)) p MeasureTheory.Measure.count
            ≤ (C Λ : ENNReal) * ENNReal.ofReal (lossWeight A ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm g p MeasureTheory.Measure.count := by
  obtain ⟨A, hA, ρ₀, hρ₀, H⟩ := Work.KMTAreas.A7Hi.LinVarG P hdeg C₀ hC₀ r hr
  refine ⟨A, hA, ρ₀, hρ₀, ?_⟩
  intro ρ hρ hρle p hp hptop
  obtain ⟨C, hC⟩ := H ρ hρ hρle p hp hptop
  refine ⟨fun Λ => 2 * C Λ, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ t g hΛ ha ha1 ht
  have hmono : Monotone (fun n : ℕ => Nat.floor (a n)) := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    have hdiv := ha n
    have ha0 : (0 : NNReal) < a n := lt_of_lt_of_le one_pos (ha1 n)
    have hlt : a n < a (n + 1) := by
      have hmul : Λ * a n < a (n + 1) := by
        have h := mul_lt_mul_of_pos_right hdiv ha0
        rwa [div_mul_cancel₀ _ (ne_of_gt ha0)] at h
      have hle : a n ≤ Λ * a n := by
        nth_rewrite 1 [← one_mul (a n)]
        exact mul_le_mul_of_nonneg_right (le_of_lt hΛ) (zero_le : (0 : NNReal) ≤ a n)
      exact lt_of_le_of_lt hle hmul
    exact Nat.floor_mono (le_of_lt hlt)
  have hP : ∀ n m : ℕ, n ≤ m →
      bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) → bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a m)) := by
    intro n m hnm hn
    have hlog : (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat
        ≤ (Work.Analysis.EndVar.logN (Nat.floor (a m))).toNat :=
      Int.toNat_le_toNat (Work.Analysis.EndVar.logN_mono (hmono hnm))
    exact ⟨le_trans hn.1 hlog, le_trans hn.2 hlog⟩
  have hpt : ∀ x : ℤ, ‖PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g n x)‖ₑ
      ≤ (2 : ENNReal) * ‖PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t g n x)‖ₑ := by
    intro x
    rw [enorm_eq_self, enorm_eq_self]
    have hfun : (fun n : ℕ => GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g n x)
        = fun n : ℕ => if bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) then
            Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t g n x else 0 := by
      funext n
      rw [GclRep_eq_ite]
      by_cases hb : bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))
      · simp only [hb, if_true]
      · simp only [hb, if_false, Pi.zero_apply]
    rw [hfun]
    exact variationalNorm_clip_of_tail r (le_trans (by norm_num) (le_of_lt hr)) hP
      (fun n : ℕ => Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t g n x)
  calc MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g n x)) p MeasureTheory.Measure.count
      ≤ (2 : NNReal) • MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t g n x)) p MeasureTheory.Measure.count :=
        eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' (hf := by pw_aesm) (Eventually.of_forall hpt) p
    _ = (2 : ENNReal) * MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t g n x)) p MeasureTheory.Measure.count := by
        rw [ENNReal.smul_def, smul_eq_mul]
        norm_num
    _ ≤ (2 : ENNReal) * ((C Λ : ENNReal) * ENNReal.ofReal (lossWeight A ρ l₁ l₂ k₁ k₂) *
          MeasureTheory.eLpNorm g p MeasureTheory.Measure.count) := by
        refine mul_le_mul_of_nonneg_left ?_ bot_le
        exact hC a Λ l₁ l₂ k₁ k₂ t g hΛ ha ha1 ht
    _ = ((2 * C Λ : NNReal) : ENNReal) * ENNReal.ofReal (lossWeight A ρ l₁ l₂ k₁ k₂) *
          MeasureTheory.eLpNorm g p MeasureTheory.Measure.count := by
        push_cast
        ring

/-! ## The arithmetic of the loss weight -/

theorem lmaxR_nonneg_rhs (l₁ l₂ k₁ k₂ : ℕ) : 0 ≤ lmaxR l₁ l₂ k₁ k₂ := by
  rw [lmaxR]
  have : (0 : ℤ) ≤ lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) := by
    rw [Work.Analysis.EndVar.lmax]
    exact le_trans (Int.natCast_nonneg l₁)
      (le_trans (le_max_left _ _) (le_max_left _ _))
  exact_mod_cast this

theorem one_add_lmaxR_pos_rhs (l₁ l₂ k₁ k₂ : ℕ) : (0 : ℝ) < 1 + lmaxR l₁ l₂ k₁ k₂ := by
  have := lmaxR_nonneg_rhs l₁ l₂ k₁ k₂
  linarith

theorem lossWeight_mul_rhs (a b ρ : ℝ) (l₁ l₂ k₁ k₂ : ℕ) :
    lossWeight a ρ l₁ l₂ k₁ k₂ * lossWeight b ρ l₁ l₂ k₁ k₂
      = lossWeight (a + b) ρ l₁ l₂ k₁ k₂ := by
  have h1 := one_add_lmaxR_pos_rhs l₁ l₂ k₁ k₂
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hexp : a * ρ * lmaxR l₁ l₂ k₁ k₂ + b * ρ * lmaxR l₁ l₂ k₁ k₂
      = (a + b) * ρ * lmaxR l₁ l₂ k₁ k₂ := by ring
  rw [lossWeight, lossWeight, lossWeight, mul_mul_mul_comm, ← Real.rpow_add h1,
    ← Real.rpow_add h2, hexp]

theorem lossWeight_nonneg_rhs (c ρ : ℝ) (l₁ l₂ k₁ k₂ : ℕ) : 0 ≤ lossWeight c ρ l₁ l₂ k₁ k₂ := by
  rw [lossWeight]
  exact mul_nonneg (Real.rpow_nonneg (le_of_lt (one_add_lmaxR_pos_rhs l₁ l₂ k₁ k₂)) _)
    (Real.rpow_nonneg (by norm_num) _)

/-- The product of the four loss factors of the analytic inputs is at most one loss factor. -/
theorem ofReal_lossWeight_prod_le_rhs (A₁ A₂ A₃ A₄ ρ : ℝ) (l₁ l₂ k₁ k₂ : ℕ) :
    ENNReal.ofReal (lossWeight A₁ ρ l₁ l₂ k₁ k₂) *
        ENNReal.ofReal (lossWeight A₂ ρ l₁ l₂ k₁ k₂) *
        ENNReal.ofReal (lossWeight A₃ ρ l₁ l₂ k₁ k₂) *
        ENNReal.ofReal (lossWeight A₄ ρ l₁ l₂ k₁ k₂)
      ≤ ENNReal.ofReal (lossWeight (A₁ + A₂ + A₃ + A₄) ρ l₁ l₂ k₁ k₂) := by
  have h₁ := lossWeight_nonneg_rhs A₁ ρ l₁ l₂ k₁ k₂
  have h₂ := lossWeight_nonneg_rhs A₂ ρ l₁ l₂ k₁ k₂
  have h₃ := lossWeight_nonneg_rhs A₃ ρ l₁ l₂ k₁ k₂
  have h₄ := lossWeight_nonneg_rhs A₄ ρ l₁ l₂ k₁ k₂
  have h₅ : (0 : ℝ) ≤ lossWeight A₁ ρ l₁ l₂ k₁ k₂ * lossWeight A₂ ρ l₁ l₂ k₁ k₂ :=
    mul_nonneg h₁ h₂
  have h₆ : (0 : ℝ) ≤ lossWeight A₃ ρ l₁ l₂ k₁ k₂ * lossWeight A₄ ρ l₁ l₂ k₁ k₂ :=
    mul_nonneg h₃ h₄
  have hstep : ENNReal.ofReal (lossWeight A₁ ρ l₁ l₂ k₁ k₂) *
        ENNReal.ofReal (lossWeight A₂ ρ l₁ l₂ k₁ k₂) *
        ENNReal.ofReal (lossWeight A₃ ρ l₁ l₂ k₁ k₂) *
        ENNReal.ofReal (lossWeight A₄ ρ l₁ l₂ k₁ k₂)
      = (ENNReal.ofReal (lossWeight A₁ ρ l₁ l₂ k₁ k₂) *
          ENNReal.ofReal (lossWeight A₂ ρ l₁ l₂ k₁ k₂)) *
        (ENNReal.ofReal (lossWeight A₃ ρ l₁ l₂ k₁ k₂) *
          ENNReal.ofReal (lossWeight A₄ ρ l₁ l₂ k₁ k₂)) := by ring
  rw [hstep, ← ENNReal.ofReal_mul h₁, ← ENNReal.ofReal_mul h₃,
    ← ENNReal.ofReal_mul h₅]
  refine le_of_eq ?_
  congr 1
  rw [lossWeight_mul_rhs, lossWeight_mul_rhs, lossWeight_mul_rhs]
  ring

/-! ## The vanishing of the repaired model tuple for a vanishing input -/

theorem eq_zero_of_eLpNorm_count_eq_zero_rhs {p : ENNReal} (hp : p ≠ 0) {u : ℤ → ℂ}
    (h : MeasureTheory.eLpNorm u p (MeasureTheory.Measure.count : Measure ℤ) = 0) : u = 0 := by
  have hsm : AEStronglyMeasurable u (MeasureTheory.Measure.count : Measure ℤ) :=
    AEStronglyMeasurable.of_discrete
  have h0 : u =ᵐ[MeasureTheory.Measure.count] 0 := (eLpNorm_eq_zero_iff hp).mp h
  have hnull : MeasureTheory.Measure.count {m : ℤ | u m ≠ 0} = 0 := ae_iff.mp h0
  funext n
  by_contra hn
  have hne : MeasureTheory.Measure.count {m : ℤ | u m ≠ 0} ≠ 0 := by
    rw [MeasureTheory.Measure.count_ne_zero_iff]
    exact ⟨n, hn⟩
  exact hne hnull

/-- The exact-height multiplier of the zero function vanishes. -/
theorem Tex_zero_rhs (ρ : ℝ) (l : ℕ) (φ : ℝ → ℂ) :
    Tex ρ l φ (0 : ℤ → ℂ) = 0 := by
  funext n
  simp only [Tex, Work.Analysis.IWMultiplier.iwConv_apply, Pi.zero_apply, smul_zero, tsum_zero]

/-- The repaired model tuple vanishes when its first argument does. -/
theorem modelTupleRep_zero_left (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) :
    modelTupleRep ρ P C₀ a 0 g l₁ l₂ k₁ k₂ = 0 := by
  funext n x
  rw [modelTupleRep]
  split
  · simp only [Tex_zero_rhs]
    simp [BtwistExact]
  · rfl

/-- The repaired model tuple vanishes when its second argument does. -/
theorem modelTupleRep_zero_right (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (f : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) :
    modelTupleRep ρ P C₀ a f 0 l₁ l₂ k₁ k₂ = 0 := by
  funext n x
  rw [modelTupleRep]
  split
  · simp only [Tex_zero_rhs]
    simp [BtwistExact]
  · rfl

/-- The `V^r`-tuple of the repaired model vanishes when the first input vanishes pointwise. -/
theorem eLpNorm_modelTupleRep_eq_zero_left (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ)
    (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (r : NNReal) (q : ENNReal) (g : ℤ → ℂ) {f : ℤ → ℂ}
    (hr : 1 ≤ r) (hf : f = 0) :
    MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) q
      MeasureTheory.Measure.count = 0 := by
  subst hf
  have hseq : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => modelTupleRep ρ P C₀ a 0 g l₁ l₂ k₁ k₂ n x)) = fun _ : ℤ => 0 := by
    funext x
    have hzero : (fun n : ℕ => modelTupleRep ρ P C₀ a 0 g l₁ l₂ k₁ k₂ n x) = 0 := by
      funext n
      exact congrFun (congrFun (modelTupleRep_zero_left ρ P C₀ a g l₁ l₂ k₁ k₂) n) x
    rw [hzero, variationalNorm_zero' r hr]
  rw [hseq]
  simp

/-- The `V^r`-tuple of the repaired model vanishes when the second input vanishes pointwise. -/
theorem eLpNorm_modelTupleRep_eq_zero_right (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ)
    (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (r : NNReal) (q : ENNReal) (f : ℤ → ℂ) {g : ℤ → ℂ}
    (hr : 1 ≤ r) (hg : g = 0) :
    MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) q
      MeasureTheory.Measure.count = 0 := by
  subst hg
  have hseq : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => modelTupleRep ρ P C₀ a f 0 l₁ l₂ k₁ k₂ n x)) = fun _ : ℤ => 0 := by
    funext x
    have hzero : (fun n : ℕ => modelTupleRep ρ P C₀ a f 0 l₁ l₂ k₁ k₂ n x) = 0 := by
      funext n
      exact congrFun (congrFun (modelTupleRep_zero_right ρ P C₀ a f l₁ l₂ k₁ k₂) n) x
    rw [hzero, variationalNorm_zero' r hr]
  rw [hseq]
  simp

/-- The vanishing of the `V^r`-tuple of the repaired model when one input has vanishing `ℒ^p`
seminorm. -/
theorem eLpNorm_modelTupleRep_eq_zero (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ)
    (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (r : NNReal) (hr : 1 ≤ r) (p₁ p₂ : ENNReal)
    (hp₁ : p₁ ≠ 0) (hp₂ : p₂ ≠ 0) (f g : ℤ → ℂ)
    (h : MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count = 0 ∨
         MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count = 0) :
    MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
      (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count = 0 := by
  rcases h with hf | hg
  · exact eLpNorm_modelTupleRep_eq_zero_left ρ P C₀ a l₁ l₂ k₁ k₂ r _ g hr
      (eq_zero_of_eLpNorm_count_eq_zero_rhs hp₁ hf)
  · exact eLpNorm_modelTupleRep_eq_zero_right ρ P C₀ a l₁ l₂ k₁ k₂ r _ f hr
      (eq_zero_of_eLpNorm_count_eq_zero_rhs hp₂ hg)

theorem one_le_lossWeight_rhs {c ρ : ℝ} (hc : 0 ≤ c) (hρ : 0 ≤ ρ) (l₁ l₂ k₁ k₂ : ℕ) :
    1 ≤ lossWeight c ρ l₁ l₂ k₁ k₂ := by
  have hL := lmaxR_nonneg_rhs l₁ l₂ k₁ k₂
  have h1 : (1 : ℝ) ≤ (1 + lmaxR l₁ l₂ k₁ k₂) ^ c :=
    Real.one_le_rpow (by linarith) hc
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (c * ρ * lmaxR l₁ l₂ k₁ k₂) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  rw [lossWeight]
  exact one_le_mul_of_one_le_of_one_le h1 h2


/-! ## The fibre as the per-window phase rotation of the packet synthesis (paper `form-1`) -/

/-- The **window modulation** `M_α v = e(-αx)·v(x)`, in the circle-character form. -/
def winModR (α : Work.Analysis.IonescuWainger.Circle) (v : ℤ → ℂ) : ℤ → ℂ :=
  fun x => fourier (T := 1) (-x) α * v x

/-- The **window convolution** `T_m v = ∑_j (cw m j) v(·-j)`. -/
def winConvR (m : ℝ → ℂ) (v : ℤ → ℂ) : ℤ → ℂ :=
  fun x => ∑' j : ℤ, cw m j * v (x - j)

theorem norm_fourier_applyR (n : ℤ) (x : Work.Analysis.IonescuWainger.Circle) :
    ‖(fourier (T := 1) n) x‖ = 1 := by
  simp only [fourier_apply, Circle.norm_coe]

theorem fourier_neg_eq (n : ℤ) (x : Work.Analysis.IonescuWainger.Circle) :
    fourier (T := 1) (-n) (-x) = fourier (T := 1) n x := by
  rw [fourier_apply, fourier_apply]
  congr 1
  rw [neg_smul, smul_neg, neg_neg]

theorem fourier_neg_apply_mulR (x j : ℤ) (α : Work.Analysis.IonescuWainger.Circle) :
    fourier (T := 1) (-x) α * fourier (T := 1) (-(x - j)) (-α)
      = fourier (T := 1) (-j) α := by
  have h1 : fourier (T := 1) (-(x - j)) (-α) = fourier (T := 1) (x - j) α :=
    fourier_neg_eq (x - j) α
  rw [h1, ← fourier_add]
  rw [show -x + (x - j) = (-j : ℤ) from by ring]

theorem winModR_winConvR_apply (α : Work.Analysis.IonescuWainger.Circle) (m : ℝ → ℂ)
    (u : ℤ → ℂ) (x : ℤ) :
    winModR α (winConvR m (winModR (-α) u)) x
      = ∑' j : ℤ, fourier (T := 1) (-j) α * (cw m j * u (x - j)) := by
  rw [winModR, winConvR, ← tsum_mul_left]
  refine tsum_congr (fun j => ?_)
  rw [show winModR (-α) u (x - j) = fourier (T := 1) (-(x - j)) (-α) * u (x - j) from rfl]
  rw [← fourier_neg_apply_mulR x j α]
  ring

theorem fiberOp_eq_phaseRotation_windowCut (ρ : ℝ) (l : ℕ) (m : ℝ → ℂ) (n₀ : ℤ) (u : ℤ → ℂ)
    (x : ℤ) (hsum : Summable (fun j : ℤ => cw m j * u (x - j))) :
    fiberOp ρ l m n₀ u x
      = ∑ α ∈ iwArithFreqsNew ρ l, fourier (T := 1) n₀ α *
          winModR α (winConvR m (winModR (-α) u)) x := by
  set A := iwArithFreqsNew ρ l with hA
  have hsumα : ∀ α : Work.Analysis.IonescuWainger.Circle, Summable (fun j : ℤ =>
      fourier (T := 1) (-j) α * (cw m j * u (x - j))) := by
    intro α
    refine Summable.of_norm_bounded (hsum.norm) (fun j => ?_)
    rw [norm_mul, norm_fourier_applyR, one_mul]
  have hsumm : ∀ α : Work.Analysis.IonescuWainger.Circle, Summable (fun j : ℤ =>
      fourier (T := 1) n₀ α * (fourier (T := 1) (-j) α * (cw m j * u (x - j)))) :=
    fun α => Summable.mul_left _ (hsumα α)
  have hLHS : fiberOp ρ l m n₀ u x
      = ∑' j : ℤ, ∑ α ∈ A, fourier (T := 1) n₀ α
          * (fourier (T := 1) (-j) α * (cw m j * u (x - j))) := by
    rw [fiberOp]
    refine tsum_congr (fun j => ?_)
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [show fourier (T := 1) (n₀ - j) α = fourier (T := 1) n₀ α * fourier (T := 1) (-j) α from by
      rw [show (n₀ - j : ℤ) = n₀ + (-j) from rfl, fourier_add]]
    ring
  rw [hLHS, Summable.tsum_finsetSum (s := A) (fun α _ => hsumm α)]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [show winModR α (winConvR m (winModR (-α) u)) x
      = ∑' j : ℤ, fourier (T := 1) (-j) α * (cw m j * u (x - j)) from
    winModR_winConvR_apply α m u x, ← tsum_mul_left]

theorem ModelLargeHiRep (P : Polynomial ℤ) (p₁ p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂)
    (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1) :
    ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r →
      ∃ c : ℝ, 0 ≤ c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
          ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
            1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
            MeasureTheory.eLpNorm (fun x : ℤ =>
                PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                  Work.KMTAreas.A7.modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
              (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
            ≤ (K Λ : ENNReal) *
                ENNReal.ofReal (Work.KMTAreas.A7.lossWeight c ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
                MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
  intro C₀ r hC₀ hr
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) (le_of_lt hr)
  obtain ⟨A₁, hA₁, ρ₁, hρ₁, hlin₁⟩ := LinVarRep C₀ hC₀ r hr
  obtain ⟨A₂, hA₂, ρ₂, hρ₂, hsamp₁⟩ := FiberVarSamplingRepBdd r hr
  obtain ⟨A₃, hA₃, ρ₃, hρ₃, hlin₂⟩ := LinVarGRep P hdeg C₀ hC₀ r hr
  -- the `g`-side fibre estimate: the *bounded* (`A7Rescue`) form, proved
  obtain ⟨A₄, hA₄, ρ₄, hρ₄, hsamp₂⟩ := Work.KMTAreas.A7Rescue.fiberVarSamplingGRep_bdd P hdeg r hr
  refine ⟨A₁ + A₂ + A₃ + A₄, by positivity, min (min ρ₁ ρ₂) (min ρ₃ ρ₄),
    lt_min (lt_min hρ₁ hρ₂) (lt_min hρ₃ hρ₄), ?_⟩
  intro ρ hρ hρle
  have hρ₁' : ρ ≤ ρ₁ := le_trans hρle (le_trans (min_le_left _ _) (min_le_left _ _))
  have hρ₂' : ρ ≤ ρ₂ := le_trans hρle (le_trans (min_le_left _ _) (min_le_right _ _))
  have hρ₃' : ρ ≤ ρ₃ := le_trans hρle (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρ₄' : ρ ≤ ρ₄ := le_trans hρle (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨C₁, hC₁⟩ := hlin₁ ρ hρ hρ₁' p₁ hp₁ htp₁
  obtain ⟨C₂, hC₂pos, hC₂⟩ := hsamp₁ p₁ hp₁ htp₁ ρ hρ hρ₂'
  obtain ⟨C₃, hC₃⟩ := hlin₂ ρ hρ hρ₃' p₂ hp₂ htp₂
  obtain ⟨C₄, hC₄pos, hC₄⟩ := hsamp₂ p₂ hp₂ htp₂ ρ hρ hρ₄'
  refine ⟨fun Λ => max 1 (⌈C₂⌉₊ * (C₁ Λ) * ⌈C₄⌉₊ * (C₃ Λ)), ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1
  have hqe1 : 1 ≤ (p₁⁻¹ + p₂⁻¹)⁻¹ := ENNReal.one_le_inv.mpr hsum
  by_cases hf0 : MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count = 0
  · have hz := eLpNorm_modelTupleRep_eq_zero ρ P C₀ a l₁ l₂ k₁ k₂ r hr1 p₁ p₂
        (ne_of_gt (lt_trans zero_lt_one hp₁)) (ne_of_gt (lt_trans zero_lt_one hp₂)) f g
        (Or.inl hf0)
    rw [hz]
    exact bot_le
  by_cases hg0 : MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count = 0
  · have hz := eLpNorm_modelTupleRep_eq_zero ρ P C₀ a l₁ l₂ k₁ k₂ r hr1 p₁ p₂
        (ne_of_gt (lt_trans zero_lt_one hp₁)) (ne_of_gt (lt_trans zero_lt_one hp₂)) f g
        (Or.inr hg0)
    rw [hz]
    exact bot_le
  by_cases hfT : MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count = ⊤
  · have hK : ((max 1 (⌈C₂⌉₊ * (C₁ Λ) * ⌈C₄⌉₊ * (C₃ Λ)) : NNReal) : ENNReal) ≠ 0 := by
      rw [Ne, ENNReal.coe_eq_zero]
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    have hL : ENNReal.ofReal (lossWeight (A₁ + A₂ + A₃ + A₄) ρ l₁ l₂ k₁ k₂) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]
      exact lt_of_lt_of_le zero_lt_one
        (one_le_lossWeight_rhs (by positivity) hρ.le l₁ l₂ k₁ k₂)
    have htop : ((max 1 (⌈C₂⌉₊ * (C₁ Λ) * ⌈C₄⌉₊ * (C₃ Λ)) : NNReal) : ENNReal) *
          ENNReal.ofReal (lossWeight (A₁ + A₂ + A₃ + A₄) ρ l₁ l₂ k₁ k₂) *
          MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
          MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count = ⊤ := by
      rw [hfT, ENNReal.mul_top (mul_ne_zero hK hL), ENNReal.top_mul hg0]
    rw [htop]
    exact le_top
  by_cases hgT : MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count = ⊤
  · have hK : ((max 1 (⌈C₂⌉₊ * (C₁ Λ) * ⌈C₄⌉₊ * (C₃ Λ)) : NNReal) : ENNReal) ≠ 0 := by
      rw [Ne, ENNReal.coe_eq_zero]
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    have hL : ENNReal.ofReal (lossWeight (A₁ + A₂ + A₃ + A₄) ρ l₁ l₂ k₁ k₂) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]
      exact lt_of_lt_of_le zero_lt_one
        (one_le_lossWeight_rhs (by positivity) hρ.le l₁ l₂ k₁ k₂)
    have htop : ((max 1 (⌈C₂⌉₊ * (C₁ Λ) * ⌈C₄⌉₊ * (C₃ Λ)) : NNReal) : ENNReal) *
          ENNReal.ofReal (lossWeight (A₁ + A₂ + A₃ + A₄) ρ l₁ l₂ k₁ k₂) *
          MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
          MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count = ⊤ := by
      rw [hgT, ENNReal.mul_top (mul_ne_zero (mul_ne_zero hK hL) hf0)]
    rw [htop]
    exact le_top
  obtain ⟨Cf, hf⟩ := eLpNorm_finite_bounded p₁ (le_of_lt hp₁) f (lt_of_le_of_ne le_top hfT)
  obtain ⟨Cg, hg⟩ := eLpNorm_finite_bounded p₂ (le_of_lt hp₂) g (lt_of_le_of_ne le_top hgT)
  let F : ℝ → ℕ → ℤ → ℂ := fun t => HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f
  let G : ℝ → ℕ → ℤ → ℂ := fun t => GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g
  let U : ℝ → ℤ → ℕ → ENNReal := fun t x n₀ => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => fiberOp ρ l₁ (mStarF (uRep ρ l₁ l₂ k₁ k₂)) n₀ (F t n) x)
  let V : ℝ → ℤ → ℕ → ENNReal := fun t x n₀ => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => fiberOpP ρ P l₂ (mStargF P.natDegree (uRep ρ l₁ l₂ k₁ k₂)) n₀ (G t n) x)
  let Z : ℝ → ℤ → ENNReal := fun t x =>
      ((arithQ ρ (max l₁ l₂) : ℕ) : ENNReal)⁻¹ *
        ∑ n₀ ∈ Finset.range (arithQ ρ (max l₁ l₂)), U t x n₀ * V t x n₀
  have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
      ≤ ∫⁻ t in Set.Ioc (1/2 : ℝ) 1, Z t x := by
    intro x
    have h := modelTupleRep_variationalPointwise ρ hρ P C₀ a l₁ l₂ k₁ k₂ r hr f g
      ⟨Cf, hf⟩ ⟨Cg, hg⟩ 0 x
    simpa only [Z, U, V, F, G, fiberOp_eq_fiberOpSet_iwArithFreqsNew,
      fiberOpP_eq_fiberOpPSet_iwArithFreqsNew] using h
  have hmono : MeasureTheory.eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
        (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => ∫⁻ t in Set.Ioc (1/2 : ℝ) 1, Z t x)
        (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count :=
    MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => by simpa only [enorm_eq_self] using hpt x)
  have hZ : ∀ t ∈ Set.Ioc (1/2 : ℝ) 1,
      MeasureTheory.eLpNorm (fun x : ℤ => Z t x) (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
        ≤ ((⌈C₂⌉₊ * (C₁ Λ) * ⌈C₄⌉₊ * (C₃ Λ) : NNReal) : ENNReal) *
            ENNReal.ofReal (lossWeight (A₁ + A₂ + A₃ + A₄) ρ l₁ l₂ k₁ k₂) *
            MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
            MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
    intro t ht
    have htI : t ∈ Set.Icc (1/2 : ℝ) 1 := ⟨le_of_lt ht.1, ht.2⟩
    have hs1 := hC₂ a Λ hΛ ha ha1 l₁ l₂ k₁ k₂ t f
      (fun n => core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)))
      ⟨Cf, hf⟩ htI (fun n hn => hn.2.1) (fun n hn => hn.1.2.1)
    have hs2 := hC₄ a Λ hΛ ha ha1 l₁ l₂ k₁ k₂ t g Cg hg
      (fun n => core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)))
      htI (fun n hn => hn.2.2) (fun n hn => hn.1.2.1)
    have hs1' : MeasureTheory.eLpNorm (fun x : ℤ =>
          Work.KMTAreas.A7.residueLp p₁.toReal (arithQ ρ (max l₁ l₂)) (U t) x) p₁
          MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C₂ * lossWeight A₂ ρ l₁ l₂ k₁ k₂) *
            MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => F t n x)) p₁ MeasureTheory.Measure.count := by
      simpa only [U, F, HclRep] using hs1
    have hs2' : MeasureTheory.eLpNorm (fun x : ℤ =>
          Work.KMTAreas.A7.residueLp p₂.toReal (arithQ ρ (max l₁ l₂)) (V t) x) p₂
          MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C₄ * lossWeight A₄ ρ l₁ l₂ k₁ k₂) *
            MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => G t n x)) p₂ MeasureTheory.Measure.count := by
      simpa only [V, G, GclRep] using hs2
    have hl1 := hC₁ a Λ l₁ l₂ k₁ k₂ t f hΛ ha ha1 htI
    have hl2 := hC₃ a Λ l₁ l₂ k₁ k₂ t g hΛ ha ha1 htI
    have hhold := Work.KMTAreas.A7.residueLp_mul_le (arithQ ρ (max l₁ l₂)) p₁ p₂ hp₁ hp₂
      htp₁ htp₂ hsum (U t) (V t)
    refine hhold.trans ?_
    calc MeasureTheory.eLpNorm (fun x : ℤ =>
            Work.KMTAreas.A7.residueLp p₁.toReal (arithQ ρ (max l₁ l₂)) (U t) x) p₁
            MeasureTheory.Measure.count *
          MeasureTheory.eLpNorm (fun x : ℤ =>
            Work.KMTAreas.A7.residueLp p₂.toReal (arithQ ρ (max l₁ l₂)) (V t) x) p₂
            MeasureTheory.Measure.count
        ≤ (ENNReal.ofReal (C₂ * lossWeight A₂ ρ l₁ l₂ k₁ k₂) *
              MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => F t n x)) p₁ MeasureTheory.Measure.count) *
          (ENNReal.ofReal (C₄ * lossWeight A₄ ρ l₁ l₂ k₁ k₂) *
              MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => G t n x)) p₂ MeasureTheory.Measure.count) := by
          exact mul_le_mul hs1' hs2' bot_le bot_le
      _ ≤ (ENNReal.ofReal (C₂ * lossWeight A₂ ρ l₁ l₂ k₁ k₂) *
              ((C₁ Λ : ENNReal) * ENNReal.ofReal (lossWeight A₁ ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count)) *
          (ENNReal.ofReal (C₄ * lossWeight A₄ ρ l₁ l₂ k₁ k₂) *
              ((C₃ Λ : ENNReal) * ENNReal.ofReal (lossWeight A₃ ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count)) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left hl1 bot_le)
            (mul_le_mul_of_nonneg_left hl2 bot_le) bot_le bot_le
      _ ≤ ((⌈C₂⌉₊ * (C₁ Λ) * ⌈C₄⌉₊ * (C₃ Λ) : NNReal) : ENNReal) *
            ENNReal.ofReal (lossWeight (A₁ + A₂ + A₃ + A₄) ρ l₁ l₂ k₁ k₂) *
            MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
            MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
          have h2le : ENNReal.ofReal (C₂ * lossWeight A₂ ρ l₁ l₂ k₁ k₂)
              ≤ (⌈C₂⌉₊ : ENNReal) * ENNReal.ofReal (lossWeight A₂ ρ l₁ l₂ k₁ k₂) := by
            rw [ENNReal.ofReal_mul hC₂pos.le]
            refine mul_le_mul' ?_ le_rfl
            rw [← ENNReal.ofReal_natCast]
            exact ENNReal.ofReal_le_ofReal (Nat.le_ceil C₂)
          have h4le : ENNReal.ofReal (C₄ * lossWeight A₄ ρ l₁ l₂ k₁ k₂)
              ≤ (⌈C₄⌉₊ : ENNReal) * ENNReal.ofReal (lossWeight A₄ ρ l₁ l₂ k₁ k₂) := by
            rw [ENNReal.ofReal_mul hC₄pos.le]
            refine mul_le_mul' ?_ le_rfl
            rw [← ENNReal.ofReal_natCast]
            exact ENNReal.ofReal_le_ofReal (Nat.le_ceil C₄)
          have hK : ((⌈C₂⌉₊ * (C₁ Λ) * ⌈C₄⌉₊ * (C₃ Λ) : NNReal) : ENNReal)
              = (⌈C₂⌉₊ : ENNReal) * (C₁ Λ : ENNReal) * (⌈C₄⌉₊ : ENNReal) * (C₃ Λ : ENNReal) := by
            push_cast
            ring
          have hprod := ofReal_lossWeight_prod_le_rhs A₁ A₂ A₃ A₄ ρ l₁ l₂ k₁ k₂
          rw [hK]
          calc (ENNReal.ofReal (C₂ * lossWeight A₂ ρ l₁ l₂ k₁ k₂) *
                  ((C₁ Λ : ENNReal) * ENNReal.ofReal (lossWeight A₁ ρ l₁ l₂ k₁ k₂) *
                    MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count)) *
                (ENNReal.ofReal (C₄ * lossWeight A₄ ρ l₁ l₂ k₁ k₂) *
                  ((C₃ Λ : ENNReal) * ENNReal.ofReal (lossWeight A₃ ρ l₁ l₂ k₁ k₂) *
                    MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count))
              ≤ ((⌈C₂⌉₊ : ENNReal) * ENNReal.ofReal (lossWeight A₂ ρ l₁ l₂ k₁ k₂) *
                  ((C₁ Λ : ENNReal) * ENNReal.ofReal (lossWeight A₁ ρ l₁ l₂ k₁ k₂) *
                    MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count)) *
                ((⌈C₄⌉₊ : ENNReal) * ENNReal.ofReal (lossWeight A₄ ρ l₁ l₂ k₁ k₂) *
                  ((C₃ Λ : ENNReal) * ENNReal.ofReal (lossWeight A₃ ρ l₁ l₂ k₁ k₂) *
                    MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count)) := by gcongr
            _ = ((⌈C₂⌉₊ : ENNReal) * (C₁ Λ : ENNReal) * (⌈C₄⌉₊ : ENNReal) * (C₃ Λ : ENNReal)) *
                  (ENNReal.ofReal (lossWeight A₁ ρ l₁ l₂ k₁ k₂) *
                    ENNReal.ofReal (lossWeight A₂ ρ l₁ l₂ k₁ k₂) *
                    ENNReal.ofReal (lossWeight A₃ ρ l₁ l₂ k₁ k₂) *
                    ENNReal.ofReal (lossWeight A₄ ρ l₁ l₂ k₁ k₂)) *
                  MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
                  MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by ring
            _ ≤ ((⌈C₂⌉₊ : ENNReal) * (C₁ Λ : ENNReal) * (⌈C₄⌉₊ : ENNReal) * (C₃ Λ : ENNReal)) *
                  ENNReal.ofReal (lossWeight (A₁ + A₂ + A₃ + A₄) ρ l₁ l₂ k₁ k₂) *
                  MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
                  MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by gcongr
  have hlin : MeasureTheory.eLpNorm (fun x : ℤ => ∫⁻ t in Set.Ioc (1/2 : ℝ) 1, Z t x)
        (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
      ≤ ((⌈C₂⌉₊ * (C₁ Λ) * ⌈C₄⌉₊ * (C₃ Λ) : NNReal) : ENNReal) *
          ENNReal.ofReal (lossWeight (A₁ + A₂ + A₃ + A₄) ρ l₁ l₂ k₁ k₂) *
          MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
          MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count :=
    Work.KMTAreas.A7.eLpNorm_lintegral_le (p₁⁻¹ + p₂⁻¹)⁻¹ hqe1 Z _ hZ
  have hKle : ((⌈C₂⌉₊ * (C₁ Λ) * ⌈C₄⌉₊ * (C₃ Λ) : NNReal) : ENNReal)
      ≤ ((max 1 (⌈C₂⌉₊ * (C₁ Λ) * ⌈C₄⌉₊ * (C₃ Λ)) : NNReal) : ENNReal) := by
    rw [ENNReal.coe_le_coe]
    exact le_max_right _ _
  refine le_trans hmono (le_trans hlin ?_)
  calc ((⌈C₂⌉₊ * (C₁ Λ) * ⌈C₄⌉₊ * (C₃ Λ) : NNReal) : ENNReal) *
        ENNReal.ofReal (lossWeight (A₁ + A₂ + A₃ + A₄) ρ l₁ l₂ k₁ k₂) *
        MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
        MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count
      = ((⌈C₂⌉₊ * (C₁ Λ) * ⌈C₄⌉₊ * (C₃ Λ) : NNReal) : ENNReal) *
        (ENNReal.ofReal (lossWeight (A₁ + A₂ + A₃ + A₄) ρ l₁ l₂ k₁ k₂) *
          MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
          MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) := by ring
    _ ≤ ((max 1 (⌈C₂⌉₊ * (C₁ Λ) * ⌈C₄⌉₊ * (C₃ Λ)) : NNReal) : ENNReal) *
        (ENNReal.ofReal (lossWeight (A₁ + A₂ + A₃ + A₄) ρ l₁ l₂ k₁ k₂) *
          MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
          MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) :=
        mul_le_mul_of_nonneg_right hKle bot_le
    _ = ((max 1 (⌈C₂⌉₊ * (C₁ Λ) * ⌈C₄⌉₊ * (C₃ Λ)) : NNReal) : ENNReal) *
        ENNReal.ofReal (lossWeight (A₁ + A₂ + A₃ + A₄) ρ l₁ l₂ k₁ k₂) *
        MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
        MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by ring

end

end Work.KMTAreas.A7
