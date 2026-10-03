import Mathlib
import Submission.Work.KMTAreas.A7.IsLqMultiplierBound_star
import Submission.Work.KMTAreas.A7.IwLqGeneral
import Submission.Work.KMTAreas.A7.Tle_finsetSum_of_bounded
import Submission.Work.KMTAreas.A7.eLpNorm_finite_bounded
import Submission.Work.KMTAreas.A7.eLpNorm_iwConv_le_of_IWLqBoundScalar_of_bounded
import Submission.Work.KMTAreas.A7.varEst_of_uniformSigns_of_measurable
import Submission.Work.KMTAreas.iwEvenMultiplierGapUniform

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7

open MeasureTheory Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

noncomputable section

/-- **The variational estimate for a lacunary family of narrow Ionescu–Wainger bumps from a
multiplier bound at the two exponents `2` and `2k₀`.**  This is the form of
`Work.KMTAreas.A7.varEst_of_narrow_schwartz_symbols` that is actually *instantiable* in the
application: the uniform-in-signs hypothesis is required only at the `ℓ²` endpoint and at the even
endpoint `2k₀` (with `2k₀ ≥ max (p, p/(p-1))`), because those are exactly the exponents at which the
shifted Calderón–Zygmund / `IsLqMultiplierBound` input is available; the intermediate exponents are
reached by Riesz–Thorin and, for `p < 2`, by duality.

Concretely: for `0 < ρ ≤ 1`, `1 < p < ∞`, `2 < r`, `2 ≤ k₀`, `p.toReal ≤ 2k₀` and
`p.toReal/(p.toReal - 1) ≤ 2k₀` there are `Cρ > 0` and `K > 0` (`K` independent of `l, k, M, Φ`, and
appearing in the conclusion only multiplied by `(1 + l)`, so that the polynomial loss
`⟨l⟩` of the `ℓ²` endpoint can be absorbed into the caller's loss weight) such that: for every
narrowness height `k` with `2^k < 1/2` and `GoodMajorArcs ρ Cρ l k`, every family
`Φ : ℕ → 𝒮(ℝ,ℂ)` supported in the arc `ℝ_{≤k}`, every `M > 0` such that *every* finite signed sum
`ξ ↦ Σ_{n∈U} ω n · Φ n ξ` satisfies `IsLqMultiplierBound 2 · M` and
`IsLqMultiplierBound (ofReal 2k₀) · M`, and every `f : ℤ → ℂ`,

  `‖𝕍^r_n (Tle ρ l (Φ n) f)‖_{ℓᵖ} ≤ K (1 + l) M ‖f‖_{ℓᵖ}`.

Route (assembly of existing workspace results, the reviewers verified each ingredient):
* `IsLqMultiplierBound 2 Ψ M` plus `Work.KMTAreas.IsLqMultiplierBound_supNorm` gives the pointwise
  bound `‖Ψ‖ ≤ M`, and `Work.Analysis.IWMultiplier.IWMultiplierBoundScalar_q2` then gives
  `IWLqBound (iwArithFreqs ρ l) (periodize Ψ) 2 (angleBracket l * M)` — the `angleBracket l` is the
  only `l`-loss; `Work.Analysis.IWMultiplier.Q2Vector` (`IWLqBound_of_scalar_q2`) makes it
  vector-valued, which interpolation needs;
* `IsLqMultiplierBound (ofReal 2k₀) Ψ M` plus `Work.KMTAreas.IWMult_periodize` gives
  `IWMult k₀ (periodize Ψ) M`, and `Work.KMTAreas.A7.opArc_iwArithFreqs_endpoint` (which needs
  exactly `GoodMajorArcs ρ Cρ l k` and narrowness, and whose constant is independent of `l`) gives
  `IWLqBound (iwArithFreqs ρ l) (periodize Ψ) (ofReal 2k₀) (C M)`;
* Riesz–Thorin (`Work.Analysis.IWMultiplier.IWLqBound_interpolation`, or the packaged
  `Work.KMTAreas.A7.IWLqBound_interpolate_two`) between `2` and `ofReal 2k₀` gives the bound at `p`
  when `2 ≤ p.toReal`, and for `p.toReal < 2` one dualises the bound at `p.toReal/(p.toReal - 1)`
  for the *conjugate* symbol (`Work.Analysis.IWMultiplier.IWLqBound_of_dual`; the conjugate symbols
  are again signed sums of the conjugated `Φ n`, and `Work.KMTAreas.IsLqMultiplierBound_star`
  transfers the two continuous bounds — `star (star S) = S` closes the loop);
* `iwConv`-linearity in the symbol (`Work.KMTAreas.A7.iwConv_finsetSum_of_bounded`, for bounded `f`,
  extended to all `f` by `Work.KMTAreas.A7.eLpNorm_sum_clipped_le_of_bounded`) turns this into the
  uniform-in-signs bound for the family `T n = Tle ρ l (Φ n)`, and
  `Work.KMTAreas.A7.varEst_of_uniformSigns` (or its measurable-only variant
  `varEst_of_uniformSigns_of_measurable`) concludes. -/

/- **The argument actually formalised here.**  The even endpoint `2k₀` is supplied by
`Work.KMTAreas.iwEvenMultiplierGapUniform` (which needs the continuous multiplier bound only at
`2k₀`, and is already proved in the workspace), and the *lower* endpoint of the Riesz–Thorin
interpolation is taken to be the dual even exponent `(2k₀)' = 2k₀/(2k₀-1)`, reached from the same
even bound for the *conjugate* symbol by `Work.Analysis.IWMultiplier.IWLqBound_of_dual` (using
`Work.KMTAreas.A7.IsLqMultiplierBound_star` and `periodize_star`).  Since the hypotheses
`p.toReal ≤ 2k₀` and `p.toReal/(p.toReal-1) ≤ 2k₀` say exactly `(2k₀)' ≤ p.toReal ≤ 2k₀`, this
covers every exponent `p ∈ (1,∞)` without ever needing the `ℓ²` endpoint, and the two interpolation
endpoints carry the *same* constant `Ce * M`, which Riesz–Thorin returns unchanged. -/

theorem varEst_of_narrow_symbols_twoEndpoints (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal)
    (hr : 2 < r) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) (k₀ : ℕ) (hk₀ : 2 ≤ k₀)
    (hpmax : p.toReal ≤ 2 * (k₀ : ℝ)) (hpd : p.toReal / (p.toReal - 1) ≤ 2 * (k₀ : ℝ)) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ K : ℝ, 0 < K ∧
      ∀ (l : ℕ) (k : ℤ) (hCρ : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l k)
        (hk : (2 : ℝ) ^ k < 1 / 2) (M : NNReal) (hM : 0 < M) (Φ : ℕ → SchwartzMap ℝ ℂ)
        (hnarrow : ∀ n ξ, (Φ n : ℝ → ℂ) ξ ≠ 0 → ξ ∈ Work.Analysis.IonescuWainger.realArc k)
        (hMult : ∀ (U : Finset ℕ) (ω : ℕ → Bool),
          Work.Analysis.IWMultiplier.IsLqMultiplierBound 2
              (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * (Φ n : ℝ → ℂ) ξ) M ∧
            Work.Analysis.IWMultiplier.IsLqMultiplierBound (ENNReal.ofReal (2 * (k₀ : ℝ)))
              (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * (Φ n : ℝ → ℂ) ξ) M)
        (f : ℤ → ℂ),
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l (Φ n : ℝ → ℂ) f x))
              p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (K * (1 + (l : ℝ)) * M) *
              MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  -- ## The even-endpoint Ionescu–Wainger multiplier theorem
  obtain ⟨Cρg, hCρgpos, hgap⟩ := Work.KMTAreas.iwEvenMultiplierGapUniform ρ hρ hρ1
  obtain ⟨Ce, hCepos, hCe⟩ := hgap k₀ hk₀
  have hCenn : (0 : ℝ) ≤ (Ce : ℝ) := Ce.coe_nonneg
  have hCeposR : (0 : ℝ) < (Ce : ℝ) := by exact_mod_cast hCepos
  -- ## The exponent `q = p.toReal`, and the two elementary endpoints
  set q : ℝ := p.toReal with hqdef
  have hq1 : 1 < q := by
    rw [hqdef, ← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (ne_of_lt hptop)).mpr hp
  have hqpos : 0 < q := lt_trans zero_lt_one hq1
  have hpq : ENNReal.ofReal q = p := by
    rw [hqdef]; exact ENNReal.ofReal_toReal (ne_of_lt hptop)
  have hqmax : q ≤ 2 * (k₀ : ℝ) := by simpa only [hqdef] using hpmax
  have hqd : q / (q - 1) ≤ 2 * (k₀ : ℝ) := by simpa only [hqdef] using hpd
  obtain ⟨Ke, hKepos, hKe⟩ := varEst_of_uniformSigns_of_measurable q hq1 r hr
  refine ⟨Cρg, hCρgpos, Ke * (Ce : ℝ), mul_pos hKepos hCeposR, ?_⟩
  intro l k hCρ hk M hM Φ hnarrow hMult f
  have hCρg' : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρg l k := hCρ
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := M.coe_nonneg
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  -- ## Step 1: the per-sign-pattern `ℓ^q` bound for bounded input
  have hstep : ∀ (U : Finset ℕ) (ω : ℕ → Bool) (g : ℤ → ℂ),
      (∃ B : ℝ, ∀ m : ℤ, ‖g m‖ ≤ B) →
      MeasureTheory.eLpNorm (fun x : ℤ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
          Tle ρ l (Φ n : ℝ → ℂ) g x) (ENNReal.ofReal q) Measure.count
        ≤ ENNReal.ofReal ((Ce : ℝ) * (M : ℝ)) *
            MeasureTheory.eLpNorm g (ENNReal.ofReal q) Measure.count := by
    intro U ω g hgbdd
    obtain ⟨B, hB⟩ := hgbdd
    set Sfin : ℝ → ℂ := fun ξ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * (Φ n : ℝ → ℂ) ξ
      with hSfindef
    have hSnarrow : ∀ ξ : ℝ, Sfin ξ ≠ 0 → ξ ∈ realArc k := by
      intro ξ hξ
      by_contra hcon
      have hzero : ∀ n : ℕ, (Φ n : ℝ → ℂ) ξ = 0 := fun n => by
        by_contra hn
        exact hcon (hnarrow n ξ hn)
      have hSξ : Sfin ξ = ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * (Φ n : ℝ → ℂ) ξ := by
        rw [hSfindef]
      rw [hSξ, Finset.sum_eq_zero (fun n _ => by rw [hzero n, mul_zero])] at hξ
      exact hξ rfl
    have hScd : ContDiff ℝ (⊤ : ℕ∞) Sfin := by
      rw [hSfindef]
      exact ContDiff.sum (s := U)
        (f := fun n ξ => (if ω n then (1 : ℂ) else -1) * (Φ n : ℝ → ℂ) ξ)
        (fun n _ => contDiff_const.mul ((Φ n).smooth ⊤))
    have hScs : HasCompactSupport Sfin :=
      HasCompactSupport.of_support_subset_isCompact (K := realArc k) isCompact_Icc
        (fun ξ hξ => hSnarrow ξ hξ)
    let Ssch : SchwartzMap ℝ ℂ := hScs.toSchwartzMap hScd
    have hScoe : (Ssch : ℝ → ℂ) = Sfin := by
      funext x
      exact HasCompactSupport.toSchwartzMap_toFun hScs hScd x
    have hnarrowS : ∀ x : ℝ, (Ssch : ℝ → ℂ) x ≠ 0 → x ∈ realArc k := by
      intro x hx
      exact hSnarrow x (by rwa [hScoe] at hx)
    have hstarcoe : (starSchwartz Ssch : ℝ → ℂ) = fun x : ℝ => star (Sfin x) := by
      rw [starSchwartz_coe, hScoe]
    have hnarrowS' : ∀ x : ℝ, (starSchwartz Ssch : ℝ → ℂ) x ≠ 0 → x ∈ realArc k := by
      intro x hx
      have hx' : star (Sfin x) ≠ 0 := by rw [hstarcoe] at hx; exact hx
      exact hSnarrow x (star_ne_zero.mp hx')
    -- ### The multiplier bounds at the even endpoint, for the symbol and its conjugate
    have hMbig : Work.Analysis.IWMultiplier.IsLqMultiplierBound
        (ENNReal.ofReal (2 * (k₀ : ℝ))) Sfin M := by
      rw [hSfindef]
      exact (hMult U ω).2
    have hMbig' : Work.Analysis.IWMultiplier.IsLqMultiplierBound
        (ENNReal.ofReal (2 * (k₀ : ℝ))) (starSchwartz Ssch : ℝ → ℂ) M := by
      rw [hstarcoe]
      exact Work.KMTAreas.A7.IsLqMultiplierBound_star hMbig
    have h2k : ((2 * k₀ : ℕ) : ℝ≥0∞) = ENNReal.ofReal (2 * (k₀ : ℝ)) := by
      rw [← Work.KMTAreas.A7.ofReal_two_mul k₀]
      congr 1
      push_cast
      ring
    have hbig : Work.Analysis.IWMultiplier.IWLqBound (iwArithFreqs ρ l)
        (periodize (Ssch : ℝ → ℂ)) (ENNReal.ofReal (2 * (k₀ : ℝ))) (Ce * M) := by
      rw [← h2k]
      refine hCe l k hCρg' Ssch hnarrowS M ?_
      rw [h2k, hScoe]
      exact hMbig
    have hbig' : Work.Analysis.IWMultiplier.IWLqBound (iwArithFreqs ρ l)
        (periodize (starSchwartz Ssch : ℝ → ℂ)) (ENNReal.ofReal (2 * (k₀ : ℝ))) (Ce * M) := by
      rw [← h2k]
      refine hCe l k hCρg' (starSchwartz Ssch) hnarrowS' M ?_
      rw [h2k]
      exact hMbig'
    -- ### Duality: the bound at the conjugate endpoint `(2k₀)'`
    have hq2k : 1 < (ENNReal.ofReal (2 * (k₀ : ℝ))).toReal := by
      rw [ENNReal.toReal_ofReal (by positivity)]
      have h2 : (2 : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast hk₀
      linarith
    have hdual := Work.Analysis.IWMultiplier.IWLqBound_of_dual (iwArithFreqs ρ l)
      (periodize (starSchwartz Ssch : ℝ → ℂ)) hbig' hq2k
    have hsym : (fun ξ => star (periodize (starSchwartz Ssch : ℝ → ℂ) ξ))
        = periodize (Ssch : ℝ → ℂ) := by
      funext ξ
      rw [starSchwartz_coe]
      exact periodize_star (Ssch : ℝ → ℂ) ξ
    rw [hsym, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * (k₀ : ℝ))] at hdual
    -- ### Riesz–Thorin between `(2k₀)'` and `2k₀`
    have hk0R : (2 : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast hk₀
    have hKpos : 0 < 2 * (k₀ : ℝ) := by linarith
    have hKm1 : 0 < 2 * (k₀ : ℝ) - 1 := by linarith
    have hlowpos : 0 < (2 * (k₀ : ℝ)) / (2 * (k₀ : ℝ) - 1) := div_pos hKpos hKm1
    have hlowlt : (2 * (k₀ : ℝ)) / (2 * (k₀ : ℝ) - 1) < 2 * (k₀ : ℝ) := by
      rw [div_lt_iff₀ hKm1]; nlinarith
    have hqmp : 0 < q - 1 := by linarith
    have hstep2 : 2 * (k₀ : ℝ) ≤ q * (2 * (k₀ : ℝ) - 1) := by
      have h := (div_le_iff₀ hqmp).mp hqd
      nlinarith
    have hq₀p : (2 * (k₀ : ℝ)) / (2 * (k₀ : ℝ) - 1) ≤ q := (div_le_iff₀ hKm1).mpr hstep2
    set θ : ℝ := interpTheta ((2 * (k₀ : ℝ)) / (2 * (k₀ : ℝ) - 1)) (2 * (k₀ : ℝ)) q with hθdef
    obtain ⟨hθ0, hθ1, hθeq⟩ := interpTheta_mem (a := (2 * (k₀ : ℝ)) / (2 * (k₀ : ℝ) - 1))
      (b := 2 * (k₀ : ℝ)) (p := q) hlowpos hlowlt hq₀p hqmax
    rw [← hθdef] at hθeq
    have hInt : Work.Analysis.IWMultiplier.IWLqBound (iwArithFreqs ρ l)
        (periodize (Ssch : ℝ → ℂ)) (ENNReal.ofReal q)
        ((Ce * M) ^ (1 - θ) * (Ce * M) ^ θ) :=
      Work.Analysis.IWMultiplier.IWLqBound_interpolation (iwArithFreqs ρ l)
        (periodize (Ssch : ℝ → ℂ)) hdual hbig hθ0 hθ1
        (by rw [ENNReal.toReal_ofReal hlowpos.le, le_div_iff₀ hKm1]; linarith)
        (by rw [ENNReal.toReal_ofReal hKpos.le]; linarith)
        (by rw [ENNReal.toReal_ofReal hqpos.le, ENNReal.toReal_ofReal hlowpos.le,
              ENNReal.toReal_ofReal hKpos.le]; exact hθeq)
    have hCeMne : Ce * M ≠ 0 := mul_ne_zero (ne_of_gt hCepos) (ne_of_gt hM)
    have hconst : (Ce * M) ^ (1 - θ) * (Ce * M) ^ θ = Ce * M := by
      rw [← NNReal.rpow_add hCeMne, show 1 - θ + θ = 1 by ring, NNReal.rpow_one]
    have hIWq : Work.Analysis.IWMultiplier.IWLqBound (iwArithFreqs ρ l)
        (periodize (Ssch : ℝ → ℂ)) (ENNReal.ofReal q) (Ce * M) :=
      hInt.mono (le_of_eq hconst)
    have hScal : Work.Analysis.IWMultiplier.IWLqBoundScalar (iwArithFreqs ρ l) (periodize Sfin)
        (ENNReal.ofReal q) (Ce * M) := by
      have hper : periodize Sfin = periodize (Ssch : ℝ → ℂ) := by rw [hScoe]
      rw [hper]
      exact hIWq.scalar
    have hScd2 : ContDiff ℝ 2 Sfin := hScd.of_le (WithTop.coe_le_coe.mpr le_top)
    obtain ⟨S, hSnn, hS1, hS2⟩ :
        ∃ S : ℝ, 0 ≤ S ∧ (∫ y : ℝ, ‖Sfin y‖) ≤ S ∧
          (∫ y : ℝ, ‖iteratedDeriv 2 Sfin y‖) ≤ S :=
      ⟨max (∫ y : ℝ, ‖Sfin y‖) (∫ y : ℝ, ‖iteratedDeriv 2 Sfin y‖),
        le_trans (integral_nonneg (fun _ => norm_nonneg _)) (le_max_left _ _),
        le_max_left _ _, le_max_right _ _⟩
    have hker : Summable (fun j : ℤ =>
        ‖iwKernel (iwSymbolSet (iwArithFreqs ρ l) (periodize Sfin)) j‖) :=
      Summable.of_nonneg_of_le (fun j => norm_nonneg _)
        (fun j => iwKernel_decay_of_bump (iwArithFreqs ρ l) hScd2 hScs hSnn hS1 hS2 j)
        (summable_kmtKernWeight.mul_left _)
    have hbound := eLpNorm_iwConv_le_of_IWLqBoundScalar_of_bounded (A := iwArithFreqs ρ l)
      (Φ := periodize Sfin) hq1 hker hScal ⟨B, hB⟩
    rw [NNReal.coe_mul] at hbound
    have hlin := Tle_finsetSum_of_bounded ρ l k hk Φ hnarrow U ω hB
    calc MeasureTheory.eLpNorm (fun x : ℤ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
            Tle ρ l (Φ n : ℝ → ℂ) g x) (ENNReal.ofReal q) Measure.count
        = MeasureTheory.eLpNorm (Tle ρ l Sfin g) (ENNReal.ofReal q) Measure.count := by rw [hlin]
      _ = MeasureTheory.eLpNorm (iwConv (iwArithFreqs ρ l) (periodize Sfin) g)
            (ENNReal.ofReal q) Measure.count := rfl
      _ ≤ ENNReal.ofReal ((Ce : ℝ) * (M : ℝ)) *
            MeasureTheory.eLpNorm g (ENNReal.ofReal q) Measure.count := hbound
  -- ## Step 2: the uniform-in-signs bound in `lintegral` form
  have hT : ∀ (U : Finset ℕ) (ω : ℕ → Bool) (g : ℤ → ℂ),
      MeasureTheory.lintegral Measure.count (fun x : ℤ => ‖∑ n ∈ U,
          (if ω n then (1 : ℂ) else -1) * Tle ρ l (Φ n : ℝ → ℂ) g x‖ₑ ^ q)
        ≤ ENNReal.ofReal (((Ce : ℝ) * (M : ℝ)) ^ q) *
            MeasureTheory.lintegral Measure.count (fun x : ℤ => ‖g x‖ₑ ^ q) := by
    intro U ω g
    by_cases hfin : MeasureTheory.eLpNorm g (ENNReal.ofReal q) Measure.count = ⊤
    · have hlinf : MeasureTheory.lintegral Measure.count (fun x : ℤ => ‖g x‖ₑ ^ q) = ⊤ := by
        rw [Work.BourgainPlan.Maximal.lintegral_enorm_rpow_eq_eLpNorm_rpow g hqpos, hfin]
        exact ENNReal.top_rpow_of_pos hqpos
      rw [hlinf, ENNReal.mul_top]
      · exact le_top
      · refine ENNReal.ofReal_ne_zero_iff.mpr ?_
        exact Real.rpow_pos_of_pos (mul_pos hCeposR hMpos) q
    · have hlt : MeasureTheory.eLpNorm g (ENNReal.ofReal q) Measure.count < ⊤ :=
        lt_top_iff_ne_top.mpr hfin
      obtain ⟨B, hB⟩ := eLpNorm_finite_bounded (ENNReal.ofReal q)
        (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq1.le) g hlt
      have hb := hstep U ω g ⟨B, hB⟩
      rw [Work.BourgainPlan.Maximal.lintegral_enorm_rpow_eq_eLpNorm_rpow _ hqpos,
        Work.BourgainPlan.Maximal.lintegral_enorm_rpow_eq_eLpNorm_rpow g hqpos]
      calc (MeasureTheory.eLpNorm (fun x : ℤ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
              Tle ρ l (Φ n : ℝ → ℂ) g x) (ENNReal.ofReal q) Measure.count) ^ q
          ≤ (ENNReal.ofReal ((Ce : ℝ) * (M : ℝ)) *
              MeasureTheory.eLpNorm g (ENNReal.ofReal q) Measure.count) ^ q :=
            ENNReal.rpow_le_rpow hb hqpos.le
        _ = (ENNReal.ofReal ((Ce : ℝ) * (M : ℝ))) ^ q *
              (MeasureTheory.eLpNorm g (ENNReal.ofReal q) Measure.count) ^ q :=
            ENNReal.mul_rpow_of_nonneg _ _ hqpos.le
        _ = ENNReal.ofReal ((((Ce : ℝ) * (M : ℝ))) ^ q) *
              (MeasureTheory.eLpNorm g (ENNReal.ofReal q) Measure.count) ^ q := by
            rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hCenn hMnn) hqpos.le]
  -- ## Step 3: the variational estimate
  have hfin2 := hKe (fun n : ℕ => Tle ρ l (Φ n : ℝ → ℂ))
      (fun n g => (measurable_of_countable (Tle ρ l (Φ n : ℝ → ℂ) g)).aemeasurable)
      ((Ce : ℝ) * (M : ℝ)) (mul_nonneg hCenn hMnn) hT f
  rw [hpq] at hfin2
  refine hfin2.trans ?_
  refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
  have hl1 : (1 : ℝ) ≤ 1 + (l : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) l]
  have hKC : (0 : ℝ) ≤ Ke * (Ce : ℝ) := mul_nonneg hKepos.le hCenn
  have hMM : (M : ℝ) ≤ (1 + (l : ℝ)) * (M : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hl1 hMnn
    rwa [one_mul] at h
  calc Ke * ((Ce : ℝ) * (M : ℝ)) = Ke * (Ce : ℝ) * (M : ℝ) := by ring
    _ ≤ Ke * (Ce : ℝ) * ((1 + (l : ℝ)) * (M : ℝ)) :=
        mul_le_mul_of_nonneg_left hMM hKC
    _ = Ke * (Ce : ℝ) * (1 + (l : ℝ)) * (M : ℝ) := by ring

end

end Work.KMTAreas.A7
