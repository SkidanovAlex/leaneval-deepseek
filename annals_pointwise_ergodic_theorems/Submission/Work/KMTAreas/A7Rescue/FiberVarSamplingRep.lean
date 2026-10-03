import Mathlib
import Submission.Work.KMTAreas.A7.FiberVarSamplingRep
import Submission.Work.KMTAreas.A7.fiberVarSamplingLarge_columnBanded
import Submission.Work.KMTAreas.A7.MixedGSideAux
import Submission.Port.Aesm

/-!
# The fibre variational sampling estimate at the repaired window `uRep` (rescue)

This file works on `Work.KMTAreas.A7Rescue.FiberVarSamplingRep`, the `uRep`-analogue of the §8
fibre variational sampling estimate of Krause--Mirek--Tao.  The auxiliary results are stated in
the namespaces they belong to (`Work.KMTAreas.A7`), so that they can be fed into the existing
chapter.

## The pieces

* `Work.KMTAreas.A7.fibreVarSampling_quarter` — the band-limited fibre estimate with the
  **quarter** Shannon condition `W n * q ≤ 1/4` (the `1/8` sibling
  `A7.fibreVarSampling_of_bandLimited_sharp` is proved in the tree; the quarter version is what
  the repaired window needs, since the exact-height packet band `2^{k₁ - logN N}` is only known to
  satisfy `· q ≤ 1/4` under the Farey condition `8 · 2^{k₁} · arithQ ≤ N`).  The proof is the
  sibling's, with `PacketRotationResidueBoundLpGeTwo` replaced by the proved
  `PacketRotationResidueBoundQuarter`.
* `Work.KMTAreas.A7.fiberVarSamplingRep_unclipped_of_memLpTwo` — the target's inequality for
  input `f ∈ ℓ²` (then the columns are `ℓ²` and band-limited by the proved
  `A7.hasFreqSupport_Tex_of_memℓp`; the two scale regimes are handled by the proved bounded-scale
  estimate `A7.rep_smallL` and by `fibreVarSampling_quarter`).  Both new results are axiom-clean
  (`#print axioms` = `[propext, Classical.choice, Quot.sound]`).

## The remaining gap (the target's `sorry`), precisely

The reduction proved in this file (`FiberVarSamplingRep_of_residual`, session 2) says that the target
is *equivalent* to `FiberVarSamplingRepResidual r`, i.e. to the target's inequality under the extra
hypothesis that **every column** `n ↦ if S n then Tex ρ l₁ (varphiNt (N n) k₁ t) f else 0` is in
`ℓᵖ`: if some column is outside `ℓᵖ`, the right-hand side is `⊤`
(`eLpNorm_variationalNorm_eq_top_of_eLpNorm_eq_top`) and the inequality is trivial.

So the only remaining content is the **masked case**, i.e. the estimate for families all of whose
columns lie in `ℓᵖ` but which are not necessarily `ℓ²`.  This is a genuine restriction: for `p > 2`
the columns need not be in `ℓ²` even when the input is in `ℓᵖ` (witness: `f = ∑_k k^{-2/5} δ_{t_k}`
with the `t_k` far apart — the columns are sums of disjoint bumps, `∑|A_k|^p < ∞` but
`∑|A_k|² = ∞`; and the same witness defeats the natural `Young`-inequality argument, whose exponent
`1/r = 3/2 - 1/p` is not admissible for `p > 2`).  The proved crux
`A7Hi.PacketRotationResidueBoundQuarter` requires its *envelopes* to be in `ℓ²` and band-limited to a
single arc, so it does not apply verbatim.  See
`NOTES_A7Rescue_FiberVarSamplingRep_SESSION2.md` (§1 for the witness, §3 for the "separated spike"
observation showing that such data nevertheless satisfy the target, and §4 for the route).

The target's `ℓ²` case (`Memℓp f 2`) is *proved* as
`Work.KMTAreas.A7Rescue.fiberVarSamplingRepMemLpTwo` in the sibling file
`A7Rescue/fiberVarSamplingRepMemLpTwo.lean` (which imports this file, so its proof must be copied here
rather than imported back).  The unclipped form for `Memℓp f 2` is already proved *in this file* as
`Work.KMTAreas.A7.fiberVarSamplingRep_unclipped_of_memLpTwo`.

The remaining gap (the target's `sorry`), precisely
-- the masked case -- is unchanged from session 1; for the record, the earlier description follows.

The target is the same inequality for **arbitrary** `f`, and the `ℓ²` case above is *not* the only
case: for `f ∉ ℓ²` the `tsum`-realisation of `Tex` is *junk* at some points (Lean's `tsum` is `0`
there), and the stored column is a **masked** object

    w n = 1_{E n} · (honest convolution),  E n `d`-periodic, `d = arithQ ρ l₁`,

(SESSION11 §1 of the tree's notes), i.e. the fibre estimate must hold for the *masked* families
`1_{E n} v n` with `v n` honest band-`W` — this is the tree's recognised open (MASKED) statement,
whose `p = 2` half is provable from the orthogonality

    (1/d) Σ_{n₀<d} |T_{n₀} w (y)|² = Σ_{α ∈ A} |P_α w (y)|²,   A = iwArithFreqsNew ρ l₁,

(the characters `e(α n₀)`, `α ∈ A ⊆ (1/d)ℤ/ℤ`, are orthogonal mod `d`) together with
`Σ_α ‖P_α w‖²_{ℓ²} ≤ ‖w‖²_{ℓ²}` (the α-arcs of `mStarF U` are disjoint — `uRep_nonAliasing`), and
whose general-`p`/`Vʳ` half needs the multi-scale version of that orthogonality (Rubio de Francia's
square-function inequality for the *torsion-band* pieces).  Note that the target's `residueLp`
average is over `n₀ < q` with `q = arithQ ρ (max l₁ l₂)` a multiple of `d`, so the `q`-average is
`(d/q)^{1/p}` times the `d`-average — an extra gain which is what makes the no-Nyquist regime
(`2^{2U} < q`, the only regime where the quarter Shapiro condition `W q ≤ 1/4` is not available for
the *plateau* band) plausible.

**Route to the target from here** (the first step is now *done*; the second is the open input):
1. the `S`-clipping transport -- **PROVED** as
   `Work.KMTAreas.A7Rescue.fiberVarSamplingRepMemLpTwo` in
   `Submission/Work/KMTAreas/A7Rescue/fiberVarSamplingRepMemLpTwo.lean` (sorry-free,
   axiom-clean): the target's inequality for `f ∈ ℓ²`.  That file re-runs the assembly with
   `Work.KMTAreas.A7.fibreVarSampling_quarter`, exploiting that its radii `W n` are *free* (so the
   clip off `S` is handled by choosing the radii there), plus `A7.rep_smallL` for the bounded
   scales.  Its file imports this one, so this file must not import it back; a *downstream*
   assembly file can import both.
2. the masked case (the open input): the fibre estimate for `1_{E n} v n` with `E n` `d`-periodic
   and `v n` honest band-`W`.  Its `p = 2` half is provable from the `d`-torsion orthogonality
   `d⁻¹ Σ_{n₀<d} |T_{n₀} w (y)|² = Σ_{α ∈ A} |P_α w (y)|²` together with
   `Σ_α ‖P_α w‖²_{ℓ²} ≤ ‖w‖²_{ℓ²}` (the `mStarF U`-arcs are disjoint by `A7.uRep_nonAliasing`);
   the general-`p`/`Vʳ` half needs the *coherent* torsion-band packet-rotation bound, i.e. the
   crux for pieces that are the α-plateau projections of a common masked band-`W` family (their
   spectra are unions of `W`-narrow bits at the `d`-torsion points rather than a single arc, which
   is why the proved crux does not apply verbatim).  The target's fibre is exactly the weighted
   packet rotation `T_{n₀} w = Σ_{α ∈ A} e(α n₀) · P_α w` of those pieces, whose synthesis is `w`;
   and the `q`-residue average gains `(d/q)^{1/p}` over the `d`-average because the phases
   `e(α n₀)` are `d`-torsion.
-/

namespace Work.KMTAreas.A7

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems

noncomputable section

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-- **The band-limited fibre variational sampling estimate at the quarter Shannon threshold.**

Same statement as the proved `Work.KMTAreas.A7.fibreVarSampling_of_bandLimited_sharp`, with the
Shannon condition `W n * q ≤ 1/8` relaxed to `W n * q ≤ 1/4` (the threshold of the proved
packet-rotation crux `A7Hi.PacketRotationResidueBoundQuarter`).  The proof is the sibling's with
`PacketRotationResidueBoundLpGeTwo` replaced by `PacketRotationResidueBoundQuarter` and
`1/8 ↦ 1/4` in the packet band.

Both the range identity (`fiberOp_zero_eq_self_of_plateau`, whose hypothesis is
`W n + 2^{-2U} < ‖α - β‖`) and the band limitation of the window envelopes
(`windowEnvelopesHasFreqSupport_twoRadius`, hypothesis `2^{-2U} + W n < ‖α - β‖`) are fed by the
sharp separation `2 · 2^{-2U} ≤ ‖α - β‖` together with `W n ≤ 2^{-2U-1}`; the quarter crux is fed
by `W n ≤ 1/(4 q)`. -/
theorem fibreVarSampling_quarter (ρ : ℝ) (p : ℝ) (hp : 1 < p) (r : NNReal) (hr : 2 < r) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (l₁ U : ℕ) (hU : 1 ≤ U) (q : ℕ) (hq : 0 < q) (W : ℕ → ℝ) (w : ℕ → ℤ → ℂ),
        (∀ n : ℕ, 0 < W n) →
        (∀ n : ℕ, W n * (q : ℝ) ≤ 1 / 4) →
        (∀ n : ℕ, W n ≤ (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1)) →
        (∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁,
          ∀ β ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁, α ≠ β →
            2 * (2 : ℝ) ^ (-(2 * (U : ℤ))) ≤ ‖α - β‖) →
        (∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁, q • α = 0) →
        (∀ n : ℕ, ∃ hw : Memℓp (w n) 2,
          Work.BourgainPlan.IonescuWainger.HasFreqSupport (w n) hw
            (⋃ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁,
              Work.BourgainPlan.IonescuWainger.arcSet α (W n))) →
        MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp p q
            (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
              Work.KMTAreas.A7.fiberOp ρ l₁ (Work.KMTAreas.A7.mStarF U) (n₀ : ℤ) (w n) y)) x)
            (ENNReal.ofReal p) MeasureTheory.Measure.count
          ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (fun x : ℤ =>
              PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => w n x))
              (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.KMTAreas.A7Hi.PacketRotationResidueBoundQuarter p hp r hr
  refine ⟨max C₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro l₁ U hU q hq W w hWpos hWq hWle hsep htors hband
  have hqposR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  -- the square-summability and the band limitation of the input
  have hw2 : ∀ n : ℕ, Memℓp (w n) 2 := fun n => (hband n).choose
  have hwband : ∀ n : ℕ, Work.BourgainPlan.IonescuWainger.HasFreqSupport (w n) (hw2 n)
      (⋃ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁,
        Work.BourgainPlan.IonescuWainger.arcSet α (W n)) :=
    fun n => (hband n).choose_spec
  -- the convolution is absolutely summable
  have hsumm : ∀ (n : ℕ) (x : ℤ), Summable (fun j : ℤ =>
      Work.KMTAreas.A7.cw (mStarF U) j * w n (x - j)) :=
    fun n x => summable_cw_mul_of_memℓp
      ((Work.KMTAreas.A7Hi.summable_cw_mStarF U).norm) (hw2 n) x
  -- the range identity, at the sharp separation constant
  have hrange : ∀ n : ℕ, Work.KMTAreas.A7.fiberOp ρ l₁ (mStarF U) 0 (w n) = w n := by
    intro n
    refine fiberOp_zero_eq_self_of_plateau ρ l₁ (mStarF U)
      (W n) ((2 : ℝ) ^ (-(2 * (U : ℤ))))
      (kmt_integrable_mStarF U)
      ((Work.KMTAreas.A7Hi.summable_cw_mStarF U).norm) ?_
      (fun θ hθ => periodize_mStarF_mem_arcSet (U := U) hθ) ?_
      (w n) (hw2 n) (hwband n)
    · intro θ hθ
      exact (periodize_mStarF_one U hU).1 θ (arcSet_mono (hWle n) 0 hθ)
    · intro α hα β hβ hne
      have h4 := hsep α hα β hβ hne
      have h2 := hWle n
      have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(2 * (U : ℤ))) := zpow_pos (by norm_num) _
      have hsplit : (2 : ℝ) ^ (-(2 * (U : ℤ))) + (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1)
          = (3 / 2) * (2 : ℝ) ^ (-(2 * (U : ℤ))) := by
        rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
        ring
      nlinarith
  -- the packet-rotation bound for the window envelopes, at the quarter threshold
  have hδpos : (0 : ℝ) < 1 / (4 * (q : ℝ)) := by positivity
  have hdec : (1 / (4 * (q : ℝ))) * (q : ℝ) ≤ 1 / 4 := by
    have heq : (1 / (4 * (q : ℝ))) * (q : ℝ) = 1 / 4 := by
      have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqposR
      field_simp
    rw [heq]
  have hbd : ∀ (n : ℕ) (α : Circ), α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁ →
      ∃ hh : Memℓp (Work.KMTAreas.A7Hi.windowEnvelopes (mStarF U) (w n) α) 2,
        Work.BourgainPlan.IonescuWainger.HasFreqSupport
          (Work.KMTAreas.A7Hi.windowEnvelopes (mStarF U) (w n) α) hh
          (Work.BourgainPlan.IonescuWainger.arcSet 0 (1 / (4 * (q : ℝ)))) := by
    intro n α hα
    have hδin : W n ≤ 1 / (4 * (q : ℝ)) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (q : ℝ))]
      nlinarith [hWq n]
    have hsep2 : ∀ α' ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁,
        ∀ β ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁, α' ≠ β →
          (2 : ℝ) ^ (-(2 * (U : ℤ))) + W n < ‖α' - β‖ := by
      intro α' hα' β hβ hne
      have h4 := hsep α' hα' β hβ hne
      have h2 := hWle n
      have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(2 * (U : ℤ))) := zpow_pos (by norm_num) _
      have hsplit : (2 : ℝ) ^ (-(2 * (U : ℤ))) + (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1)
          = (3 / 2) * (2 : ℝ) ^ (-(2 * (U : ℤ))) := by
        rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
        ring
      nlinarith
    obtain ⟨hh, hsup⟩ := windowEnvelopesHasFreqSupport_twoRadius (mStarF U)
      (kmt_integrable_mStarF U) ((Work.KMTAreas.A7Hi.summable_cw_mStarF U).norm)
      ((2 : ℝ) ^ (-(2 * (U : ℤ)))) (1 / (4 * (q : ℝ))) (W n) hδin
      (fun θ hθ => periodize_mStarF_mem_arcSet (U := U) hθ)
      (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁) hsep2 (w n) (hw2 n) (hwband n) α hα
    have heq : Work.KMTAreas.A7Hi.windowEnvelopes (mStarF U) (w n) α
        = Work.KMTAreas.A7Rep.winConvRep (mStarF U)
            (Work.KMTAreas.A7Rep.winModRep (-α) (w n)) :=
      funext fun x => Work.KMTAreas.A7Hi.windowEnvelopes_eq (mStarF U) (w n) α x
    exact ⟨heq.symm ▸ hh,
      Work.BourgainPlan.IonescuWainger.hasFreqSupport_congr heq.symm hsup⟩
  have hcrux := hC₀ q hq (1 / (4 * (q : ℝ))) hδpos hdec
      (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁) htors
      (fun n α => Work.KMTAreas.A7Hi.windowEnvelopes (mStarF U) (w n) α) hbd
  -- enlarge the constant
  have hcrux' :
      MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp p q
          (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
            Work.KMTAreas.A7Hi.winRot (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁)
              (fun α => Work.KMTAreas.A7Hi.windowEnvelopes (mStarF U) (w n) α) (n₀ : ℤ) y)) x)
          (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (max C₀ 1) * MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
              Work.KMTAreas.A7Hi.winSynth (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁)
                (fun α => Work.KMTAreas.A7Hi.windowEnvelopes (mStarF U) (w n) α) x))
            (ENNReal.ofReal p) MeasureTheory.Measure.count :=
    hcrux.trans (mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal (le_max_left C₀ 1)) bot_le)
  exact Work.KMTAreas.A7Hi.fiberVarSampling_of_windowCrux ρ l₁ q hq htors U p r
    (max C₀ 1) w hsumm hrange hcrux'

/-! ## The `ℓ²` case of the unclipped estimate -/

/-- **The strict main regime dominates the exact-height packet band.**  If
`k + 1 + 2U ≤ Log N` then the packet band `2^{k - Log N}` is inside the plateau radius
`2^{-2U-1}` of `mStarF U`. -/
private lemma two_rpow_sub_logN_le (k U N : ℕ)
    (h : k + 1 + 2 * U ≤ (Work.Analysis.EndVar.logN N).toNat) :
    (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) ≤ (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1) := by
  rw [← Real.rpow_intCast (2 : ℝ) (-(2 * (U : ℤ)) - 1)]
  have hlog : ((Work.Analysis.EndVar.logN N).toNat : ℝ) = (Work.Analysis.EndVar.logN N : ℝ) := by
    rw [← Int.cast_natCast (R := ℝ),
      Int.toNat_of_nonneg (Work.Analysis.EndVar.logN_nonneg N)]
  have h3 : (k : ℝ) + 1 + 2 * (U : ℝ) ≤ (Work.Analysis.EndVar.logN N : ℝ) := by
    have h4 : (k : ℝ) + 1 + 2 * (U : ℝ) ≤ ((Work.Analysis.EndVar.logN N).toNat : ℝ) := by
      exact_mod_cast h
    rwa [hlog] at h4
  have hkey : ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))
      ≤ (((-(2 * (U : ℤ)) - 1 : ℤ)) : ℝ) := by
    have h5 : (((-(2 * (U : ℤ)) - 1 : ℤ)) : ℝ) = -(2 * (U : ℝ)) - 1 := by
      push_cast; ring
    rw [h5]; linarith
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hkey

/-- **The Farey (Shannon) condition dominates the exact-height packet band.**  If
`2^k · q · 8 ≤ N` then `2^{k - Log N} · q ≤ 1/4`. -/
private lemma two_rpow_sub_logN_mul_le (k N q : ℕ) (hN : 0 < N)
    (hF : (2 : ℝ) ^ k * (q : ℝ) * 8 ≤ (N : ℝ)) :
    (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) * (q : ℝ) ≤ 1 / 4 := by
  have hpow : (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ))
      = (2 : ℝ) ^ (Nat.log 2 (max N 2)) := by
    rw [Real.rpow_intCast, Work.Analysis.EndVar.logN, zpow_natCast]
  have hlt : N < 2 ^ (Nat.log 2 (max N 2) + 1) := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (max N 2)
    exact lt_of_le_of_lt (le_max_left N 2) h
  have hhalf : (N : ℝ) / 2 < (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ)) := by
    rw [hpow]
    have hc : ((2 : ℕ) ^ (Nat.log 2 (max N 2) + 1) : ℝ)
        = 2 * (2 : ℝ) ^ (Nat.log 2 (max N 2)) := by
      push_cast [pow_succ]
      ring
    have hltR : (N : ℝ) < 2 * (2 : ℝ) ^ (Nat.log 2 (max N 2)) := by
      calc (N : ℝ) < ((2 : ℕ) ^ (Nat.log 2 (max N 2) + 1) : ℝ) := by exact_mod_cast hlt
        _ = 2 * (2 : ℝ) ^ (Nat.log 2 (max N 2)) := hc
    linarith
  have hposN : (0 : ℝ) < N := by exact_mod_cast hN
  have hinv : (2 : ℝ) ^ (-(Work.Analysis.EndVar.logN N : ℝ)) ≤ 2 / (N : ℝ) := by
    rw [le_div_iff₀ hposN]
    calc (2 : ℝ) ^ (-(Work.Analysis.EndVar.logN N : ℝ)) * (N : ℝ)
        ≤ (2 : ℝ) ^ (-(Work.Analysis.EndVar.logN N : ℝ))
            * (2 * (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith [hhalf]
      _ = 2 * ((2 : ℝ) ^ (-(Work.Analysis.EndVar.logN N : ℝ))
            * (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ))) := by ring
      _ = 2 := by
          have h1 : (2 : ℝ) ^ (-(Work.Analysis.EndVar.logN N : ℝ))
              * (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ)) = 1 := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
              show -(Work.Analysis.EndVar.logN N : ℝ) + (Work.Analysis.EndVar.logN N : ℝ) = 0 by ring,
              Real.rpow_zero]
          rw [h1, mul_one]
  have hmain : (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) * (q : ℝ)
      = (2 : ℝ) ^ k * ((2 : ℝ) ^ (-(Work.Analysis.EndVar.logN N : ℝ)) * (q : ℝ)) := by
    rw [show (k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)
        = (k : ℝ) + (-(Work.Analysis.EndVar.logN N : ℝ)) by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
    ring
  rw [hmain]
  calc (2 : ℝ) ^ k * ((2 : ℝ) ^ (-(Work.Analysis.EndVar.logN N : ℝ)) * (q : ℝ))
      ≤ (2 : ℝ) ^ k * ((2 / (N : ℝ)) * (q : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right hinv (by positivity)
    _ = 2 * ((2 : ℝ) ^ k * (q : ℝ)) / (N : ℝ) := by ring
    _ ≤ 2 * ((N : ℝ) / 8) / (N : ℝ) := by
        have h8 : (2 : ℝ) ^ k * (q : ℝ) ≤ (N : ℝ) / 8 := by linarith
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left h8 (by norm_num : (0 : ℝ) ≤ 2)) hposN.le
    _ = 1 / 4 := by field_simp; ring

/-- **The `ℓ²` case of the (unclipped) fibre variational sampling estimate at the repaired
window.**  For `f ∈ ℓ²` the columns `Tex ρ l₁ (varphiNt (N n) k₁ t) f` are `ℓ²` and band-limited to
the exact-height packet arcs (`A7.hasFreqSupport_Tex_of_memℓp`), so the estimate follows from the
proved bounded-scale bound `A7.rep_smallL` and the proved quarter-threshold band-limited estimate
`A7.fibreVarSampling_quarter`; the quantitative inputs are the Farey condition (from
`splitCut ρ L < N n` and `lmax_le_of_not_farey`), the strict main regime (the target's own
hypothesis) and the automatic non-aliasing of `uRep` (`A7.uRep_nonAliasing`). -/
theorem fiberVarSamplingRep_unclipped_of_memLpTwo (r : NNReal) (hr : 2 < r) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤), ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ∃ C : ℝ, 0 < C ∧
        ∀ (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ) (N : ℕ → ℕ),
          Memℓp f 2 →
          t ∈ Set.Icc (1/2 : ℝ) 1 →
          (∀ n : ℕ, k₁ + 1 + 2 * Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂
              ≤ (Work.Analysis.EndVar.logN (N n)).toNat) →
          (∀ n : ℕ, Work.KMTAreas.A7.splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < N n) →
          MeasureTheory.eLpNorm (fun x : ℤ =>
              Work.KMTAreas.A7.residueLp p.toReal (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
                (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r
                  (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l₁
                    (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂)) n₀
                    (Work.KMTAreas.A7.Tex ρ l₁
                      (Work.KMTAreas.A7.varphiNt (N n) k₁ t) f) y)) x) p
              MeasureTheory.Measure.count
            ≤ ENNReal.ofReal (C * Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                  (fun n : ℕ => Work.KMTAreas.A7.Tex ρ l₁
                    (Work.KMTAreas.A7.varphiNt (N n) k₁ t) f x)) p
                  MeasureTheory.Measure.count := by
  refine ⟨0, le_refl 0, 1, one_pos, ?_⟩
  intro p hp hptop ρ hρ hρ1
  have hpt : p ≠ ⊤ := ne_of_lt hptop
  have hpR : (1 : ℝ) < p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hpt).mpr hp
  have hpe : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal hpt
  obtain ⟨Bfun, hBfun⟩ := Work.KMTAreas.A7.lmax_le_of_not_farey ρ hρ hρ1
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.KMTAreas.A7.rep_smallL r hr ρ hρ hρ1 p hp hptop
    (fun _ => Bfun ρ)
  obtain ⟨C₂, hC₂pos, hC₂⟩ := fibreVarSampling_quarter ρ p.toReal hpR r hr
  refine ⟨max C₁ (max C₂ 1), lt_max_of_lt_left hC₁pos, ?_⟩
  intro l₁ l₂ k₁ k₂ t f N hf2 ht hband hsplit
  by_cases hcase : max (max l₁ l₂) (max k₁ k₂) ≤ Bfun ρ
  · refine (hC₁ l₁ l₂ k₁ k₂ hcase (fun n =>
      Work.KMTAreas.A7.Tex ρ l₁ (Work.KMTAreas.A7.varphiNt (N n) k₁ t) f)).trans ?_
    refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
    rw [show Work.KMTAreas.A7.lossWeight 0 ρ l₁ l₂ k₁ k₂ = 1 by
      simp [Work.KMTAreas.A7.lossWeight], mul_one]
    exact le_max_left _ _
  · push_neg at hcase
    set U : ℕ := Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ with hUdef
    set q : ℕ := Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) with hqdef
    set W : ℕ → ℝ := fun n =>
      (2 : ℝ) ^ ((k₁ : ℝ) - (Work.Analysis.EndVar.logN (N n) : ℝ)) with hWdef
    have hU1 : 1 ≤ U := by
      rw [hUdef, Work.KMTAreas.A7.uRep]
      exact le_trans (by omega : 1 ≤ max l₁ l₂ + 3) (le_max_right _ _)
    have hqpos : 0 < q := by rw [hqdef]; exact Work.KMTAreas.A7.arithQ_pos ρ _
    have hNpos : ∀ n : ℕ, 0 < N n := by
      intro n
      have h1 := hsplit n
      have h2 : 0 < Work.KMTAreas.A7.splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) := by
        rw [Work.KMTAreas.A7.splitCut]; positivity
      omega
    have hfarey : ∀ n : ℕ,
        (2 : ℝ) ^ k₁ * (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) : ℝ) * 8 ≤ (N n : ℝ) := by
      intro n
      by_contra hnot
      have hsplit' : Work.KMTAreas.A7.splitCut ρ
          (max (max (max l₁ l₂) l₂) (max k₁ k₂)) < N n := by
        convert hsplit n using 2
        omega
      have hle := hBfun (max l₁ l₂) l₂ k₁ k₂ (N n) hsplit' hnot
      omega
    have hWpos : ∀ n : ℕ, 0 < W n := by
      intro n
      rw [hWdef]
      positivity
    have hWq : ∀ n : ℕ, W n * (q : ℝ) ≤ 1 / 4 := by
      intro n
      rw [hWdef, hqdef]
      exact two_rpow_sub_logN_mul_le k₁ (N n) (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
        (hNpos n) (hfarey n)
    have hWle : ∀ n : ℕ, W n ≤ (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1) := by
      intro n
      rw [hWdef, hUdef]
      exact two_rpow_sub_logN_le k₁ (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂) (N n) (hband n)
    have hsep : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁,
        ∀ β ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁, α ≠ β →
          2 * (2 : ℝ) ^ (-(2 * (U : ℤ))) ≤ ‖α - β‖ := by
      intro α hα β hβ hne
      rw [hUdef]
      by_cases hl : l₁ = 0
      · subst hl
        exfalso
        have h0 : Work.Analysis.IonescuWainger.iwArithFreqsNew ρ 0 = (∅ : Finset Circ) := by
          simp [Work.Analysis.IonescuWainger.iwArithFreqsNew]
        rw [h0] at hα
        exact absurd hα (Finset.notMem_empty α)
      · have hdf : Work.KMTAreas.A7.diffFreqs ρ l₁
            = Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁ :=
          Work.KMTAreas.A7.diffFreqs_eq_iwArithFreqsNew hl
        have hna := Work.KMTAreas.A7.uRep_nonAliasing ρ hρ hρ1 l₁ l₂ k₁ k₂ l₁
          (le_max_left l₁ l₂)
        have hsep' := Work.KMTAreas.A7Hi.nonAliasing_separation (k := 1 - 2 * ((Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ : ℤ))) hna
          (by rw [hdf]; exact hα) (by rw [hdf]; exact hβ) hne
        have h4 : (2 : ℝ) ^ ((1 - 2 * (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ : ℤ)) + 1)
            = 4 * (2 : ℝ) ^ (-(2 * (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ : ℤ))) := by
          rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one,
            show (1 - 2 * (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ : ℤ))
              = 1 + (-(2 * (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ : ℤ))) by ring,
            zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
          ring
        rw [h4] at hsep'
        have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(2 * (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ : ℤ))) :=
          zpow_pos (by norm_num) _
        linarith
    have htors : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁, q • α = 0 := by
      intro α hα
      rw [hqdef]
      exact Work.KMTAreas.A7.arithQ_nsmul_eq_zero
        (Work.Analysis.IonescuWainger.iwArithFreqs_mono hρ hρ1 (le_max_left l₁ l₂)
          (Work.KMTAreas.A7.mem_iwArithFreqsNew_le hα))
    have hbandsupp : ∀ n : ℕ,
        ∃ hw : Memℓp (Work.KMTAreas.A7.Tex ρ l₁
            (Work.KMTAreas.A7.varphiNt (N n) k₁ t) f) 2,
          Work.BourgainPlan.IonescuWainger.HasFreqSupport
            (Work.KMTAreas.A7.Tex ρ l₁ (Work.KMTAreas.A7.varphiNt (N n) k₁ t) f) hw
            (⋃ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁,
              Work.BourgainPlan.IonescuWainger.arcSet α (W n)) := by
      intro n
      rw [hWdef]
      exact Work.KMTAreas.A7Hi.tex_varphiNt_memLpTwo_freqSupport ρ hρ hρ1 l₁ k₁ (N n) t f hf2
    have hkey := hC₂ l₁ U hU1 q hqpos W
      (fun n => Work.KMTAreas.A7.Tex ρ l₁ (Work.KMTAreas.A7.varphiNt (N n) k₁ t) f)
      hWpos hWq hWle hsep htors hbandsupp
    rw [hpe] at hkey
    refine hkey.trans ?_
    refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
    rw [show Work.KMTAreas.A7.lossWeight 0 ρ l₁ l₂ k₁ k₂ = 1 by
      simp [Work.KMTAreas.A7.lossWeight], mul_one]
    exact le_trans (le_max_left C₂ 1) (le_max_right C₁ (max C₂ 1))

end

end Work.KMTAreas.A7

namespace Work.KMTAreas.A7Hi

/-!
### Status of the `p = 2` half of the masked case, and the exact gap to the target

* **PROVED here:** `maskedFiberSqSumIdentity` — the `d`-torsion square-sum identity, i.e. the
  single-scale `p = 2` *mechanism*: the `d`-residue average of the fibre square function is exactly
  the square function `Σ_{α} |envelope_α|²` of the coherent window pieces.

* **REVIEWED, NOT YET PROVED (queue saturated twice at each attempt):** the companion Bessel bound
  `Work.KMTAreas.A7Hi.windowEnvelopeL2Mass`,

      Σ_{α ∈ iwArithFreqsNew ρ l₁} Σ'_x ‖windowEnvelopes (mStarF U) u α x‖ₑ²  ≤  Σ'_x ‖u x‖ₑ² ,

  under the separation `2 · 2^{-2U} ≤ ‖α - β‖` (which `A7.uRep_nonAliasing` supplies).  The review
  confirmed the statement and its numerology: `supp (periodize (mStarF U))` has diameter exactly
  `2 · 2^{-2U}`, so at most one `α` contributes at each frequency and the constant is `1`; no
  kernel-mass input is needed.  **Where a direct proof must start:** `windowEnvelopes m u α
  = winConvRep m (winModRep (-α) u)` (`windowEnvelopes_eq`), and one has to pin the Fourier-shift
  convention of the modulation — the envelope's `ftLp` must come out as
  `periodize (mStarF U)(ξ - α) · 𝓕u(ξ)`, i.e. the *window* shifted and `𝓕u` unshifted, so that
  `Σ_α |periodize (mStarF U)(ξ - α)|² ≤ 1` applies; the relevant proved tools are
  `A7Rep.winConvRep_ftLp_ae`, `A7Rep.windowEnvelopes_eq` and the `hasFreqSupport_modSeq*` family of
  `Work.BourgainPlan.IonescuWainger`.  Getting the sign wrong makes the two shifts cancel and the
  disjointness unusable, so read those two lemmas before writing the estimate.

* **The Fourier-shift convention, pinned** (this is the piece `windowEnvelopeL2Mass` needs; read
  the three lemmas below *before* writing the estimate, the sign is the whole content):
  * `windowEnvelopes m u α = winConvRep m (winModRep (-α) u)` (`A7Rep.windowEnvelopes_eq`), with
    `winConvRep m v x = ∑'_j cw m j * v (x-j)` (the multiplier with symbol `periodize m`) and
    `winModRep θ v x = fourier (-x) θ * v x` (the modulation by `θ`);
  * `A7Hi.winConvRep_ftLp_ae m hm hΨ hv` produces `hw : Memℓp (winConvRep m v) 2` together with
    `ftLp (winConvRep m v) hw =ᵐ (fun ξ => periodize m ξ * ftLp v hv ξ)`;
  * `BourgainPlan.IonescuWainger.ftLp_modSeq ρ hρ θ : ftLp (modSeq ρ θ) = shiftLp θ (ftLp ρ)`
    (`opArc_arcShift.lean`): the modulation shifts the transform by `+θ`, and
    `winModRep (-α) u = modSeq u θ_α` with `θ_α = -α`, so `ftLp (winModRep (-α) u)` is `𝓕u (· + α)`.
  Hence `ftLp (envelope_α) =ᵐ m̃ · (𝓕u shifted by -α)`; after the change of variable `η ↦ η + α`
  inside each term,
  `Σ_α ‖envelope_α‖²_{ℓ²} = ∫⁻ (Σ_α ‖m̃ (η + θ_α)‖ₑ²) · ‖𝓕u η‖ₑ²` , and since `m̃ = periodize
  (mStarF U)` is supported in `arcSet 0 (2^{-2U})`, `m̃ (η + θ_α) ≠ 0` iff `η ∈ arcSet (-θ_α)
  (2^{-2U}) = arcSet α (2^{-2U})`: those are exactly the arcs `hsep` makes disjoint, so at most one
  `α` contributes at each `η` and, with `‖m̃‖ ≤ 1` (from support diameter `< 1/2` and
  `|mStarF U| ≤ 1`), the inner sum is `≤ 1`.  Chain: `tsum_norm_sq_eq_norm_ftLp` (Parseval,
  ℝ-valued) → the a.e. formula → the pointwise bound → Parseval again for `u`; the ℝ/`ℝ≥0∞`
  transfer uses `ENNReal.ofReal_tsum_of_nonneg`.  *Do not* take `θ_α = α`: then the arcs appear at
  `-α` and `hsep` has to be appealed to through `‖(-α)-(-β)‖ = ‖α-β‖` — harmless but avoidable.
* **The three bookkeeping lemmas of the Bessel estimate, and where the content actually is.**
  With the convention above fixed, the chain `Σ_α Σ'_x ‖envelope_α x‖²ₑ ≤ Σ'_x ‖u x‖²ₑ` is:
  1. `tsum_norm_sq_eq_norm_ftLp` (Parseval, `ℝ`-valued) for each `α`;
  2. `‖F‖²_{L²} = ∫⁻ ‖F ξ‖ₑ²` for the `L²`-element `ftLp (envelope_α)` (the `Lp`-norm formula);
  3. the a.e. formula `ftLp (envelope_α) =ᵐ m̃ · (𝓕u shifted by -α)` — `winConvRep_ftLp_ae` +
     `ftLp_modSeq` + `shiftLp` (and `shiftLp θ F = F(· - θ)`, so `θ_α = -α` gives `𝓕u(·+α)`);
  4. **the interchange over `α` is *not* new mathematics**: it is Mathlib's
     `MeasureTheory.lintegral_finset_sum` (finite sum of `ℝ≥0∞`-valued functions), and the
     per-term change of variable is the translation invariance of the Haar measure on
     `AddCircle 1` (`lintegral_add_left_eq_self`-type); together they turn `Σ_α ∫⁻ …(ξ+α)` into
     `∫⁻ (Σ_α …)(η)`;
  5. the pointwise bound `Σ_α ‖m̃ (η + θ_α)‖ₑ² ≤ 1` a.e. — the only genuinely new step, and it is
     *local*: `mStarF_plateau U` (proved) gives `mStarF U x = 0` for `2^{-2U} ≤ |x|`, and
     `periodize` is by definition the sum of the translates at `x_k = ξ₀ + k` with
     `ξ₀ ∈ [0,1)`; for `U ≥ 1` (`2^{-2U} < 1/2`) at most one of the `x_k` is nonzero, so
     `‖periodize (mStarF U) ξ‖ ≤ 1` from `Work.KMTContract.kmtEta_le_one`/`kmtEta_nonneg`
     (all of `mStarF U`'s values are the real number `kmtEta (2^{2U} x)` in `[0,1]`); combined with
     the separation `hsep` (at most one `α` per `η`) this is `≤ 1`;
  6. Parseval again for `u`, then `ENNReal.ofReal_tsum_of_nonneg` for the `ℝ ≥ 0∞` transfer.
  So the remaining work is *bookkeeping around named lemmas*, plus step 5 — two or three lemmas,
  no new analysis.
* **The target's `sorry` is NOT cleared by the two items above.**  Together they give the
  *single-scale* `p = 2` masked bound
  `1/d · Σ_{n₀<d} Σ'_y ‖T_{n₀}u(y)‖ₑ² ≤ Σ'_y ‖u(y)‖ₑ²`.  The target quantifies over arbitrary
  `S` and `N`, i.e. over *families* `n ↦ w n`, and there the left-hand side is the `ℓ²`-norm of
  `Vʳ_n (T_{n₀} w n)` — the identity above is an identity of *values* and says nothing about the
  `Vʳ`-oscillation in `n` (the `Vʳ` is nonlinear in the family).  The multi-scale step is the
  `Vʳ`-valued (torsion-band) packet-rotation bound, i.e. the chapter below; the identity and the
  Bessel bound are exactly the two inputs its proof consumes (the "square function" side).
-/

open MeasureTheory Finset
open scoped ENNReal BigOperators

/- **The `p = 2` half of the masked case: the single-scale `d`-torsion square-sum identity.**

For the exact-height frequency set `A = iwArithFreqsNew ρ l₁` killed by `d` (`d • α = 0`), any
`u ∈ ℓ²` and any `y`, the *fibres* at the residues `n₀ < d` and the *window envelopes* satisfy

    Σ_{n₀ < d} ‖fiberOp ρ l₁ (mStarF U) n₀ u (y)‖ₑ²
      = d · Σ_{α ∈ A} ‖windowEnvelopes (mStarF U) u α (y)‖ₑ² ,

i.e. the `d`-residue average of the fibre square function is exactly the square function of the
coherent window pieces.  This is the `p = 2` mechanism of the masked case: the characters
`n₀ ↦ e(n₀α)` are orthogonal on `ℤ/d` precisely because `d` kills `A` (this is
`A7Hi.ResidueSqSumIdentity` at `q := d`, multiplied by `d`, with the inner `tsum` rewritten to its
envelope by `A7Rep.tsum_fourier_neg_mul_eq_winModRep`; the two differ by the unit-modulus factor
`fourier y α`).  The companion *bound* on the right-hand side (Bessel, using the disjointness of
the `mStarF U`-arcs) is the separate lemma `A7Hi.windowEnvelopeL2Mass`.

Stated in the tree's `ℝ≥0∞`-valued convention; the `ℝ`-valued form follows by `ENNReal.toReal`.

theorem maskedFiberSqSumIdentity` lands *between* that theorem's docstring and the
theorem, which is a hard parse error (a docstring must be immediately followed by its own
declaration) — insert above the docstring instead; (ii) after `rw [A7.mStarF, etaCut]` the goal is
`‖kmtEta (x / 2 ^ (-(2 * ↑U)))‖ ≤ 1` (the coercion from `ℝ` to `ℂ` is on the *function*
`etaCut kmtEta k`, not on the value), and `Complex.norm_real` does not fire on that shape — use the
`EtaCutPositivity` lemma of route 1 rather than hand-rolling `Complex.norm_real` +
`Real.norm_eq_abs` + `kmtEta_le_one`.
-/

end Work.KMTAreas.A7Hi

namespace Work.KMTAreas.A7Rescue

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTAreas.A7

/-! ## The trivial case, and the reduction of the target to its "masked" case

The target's inequality is trivial whenever one of the columns
`n ↦ if S n then Tex ρ l₁ (varphiNt (N n) k₁ t) f else 0` is not in `ℓᵖ`: the *right-hand side* is
then `⊤`, because the variational norm dominates the values
(`A7.enorm_apply_le_variationalNorm`).  The two lemmas below make that precise; the `Prop`
`FiberVarSamplingRepResidual` isolates the remaining case (all columns in `ℓᵖ`), and
`FiberVarSamplingRep_of_residual` shows that the target follows from it.

The residual is a genuine restriction and not a rewording: for `p > 2` the columns need not be in
`ℓ²` even when the input is in `ℓᵖ` (witness `f = ∑_k k^{-2/5} δ_{t_k}`, `t_k` far apart: the columns
are sums of disjoint bumps, `∑|A_k|^p < ∞` but `∑|A_k|² = ∞`), so the proved crux
`A7Hi.PacketRotationResidueBoundQuarter` — whose hypothesis is that the *envelopes* are in `ℓ²` and
band-limited to a single arc — is not automatically available.  See
`NOTES_A7Rescue_FiberVarSamplingRep_SESSION2.md` for the details and for the "separated spike"
observation which shows that such data nevertheless satisfy the target. -/

/-- **If one column of a family has infinite `ℓᵖ`-norm, so has the variational norm of the
family.**  Immediate from the variational norm dominating the values. -/
theorem eLpNorm_variationalNorm_eq_top_of_eLpNorm_eq_top (r : NNReal) (u : ℕ → ℤ → ℂ) (N : ℕ)
    {p : ENNReal} (h : MeasureTheory.eLpNorm (u N) p MeasureTheory.Measure.count = ⊤) :
    MeasureTheory.eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u n x)) p
      MeasureTheory.Measure.count = ⊤ := by
  have hle : MeasureTheory.eLpNorm (fun x : ℤ => ‖u N x‖ₑ) p MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u n x)) p
        MeasureTheory.Measure.count :=
    MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) fun x =>
      Work.KMTAreas.A7.enorm_apply_le_variationalNorm (fun n : ℕ => u n x) N
  refine le_antisymm le_top ?_
  rw [← h, ← MeasureTheory.eLpNorm_enorm (hf := by pw_aesm)]
  exact hle

/-- **The "masked" residual of the target**: the target's inequality under the extra hypothesis that
every column `n ↦ if S n then Tex ρ l₁ (varphiNt (N n) k₁ t) f else 0` has finite `ℓᵖ`-norm (i.e. lies
in `ℓᵖ`, the counting measure being fixed).

By `eLpNorm_variationalNorm_eq_top_of_eLpNorm_eq_top` this is *equivalent* to the target
(`FiberVarSamplingRep_of_residual`), so it is the exact remaining content. -/
def FiberVarSamplingRepResidual (r : NNReal) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
    ∀ (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤), ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ) (N : ℕ → ℕ) (S : ℕ → Prop) [DecidablePred S],
        (∀ n : ℕ, MeasureTheory.eLpNorm (if S n then Work.KMTAreas.A7.Tex ρ l₁
            (Work.KMTAreas.A7.varphiNt (N n) k₁ t) f else 0) p MeasureTheory.Measure.count ≠ ⊤) →
        t ∈ Set.Icc (1/2 : ℝ) 1 →
        (∀ n : ℕ, S n → k₁ + 1 + 2 * Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂
            ≤ (Work.Analysis.EndVar.logN (N n)).toNat) →
        (∀ n : ℕ, S n → Work.KMTAreas.A7.splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < N n) →
        MeasureTheory.eLpNorm (fun x : ℤ =>
            Work.KMTAreas.A7.residueLp p.toReal (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
              (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l₁
                  (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂)) n₀
                  (if S n then Work.KMTAreas.A7.Tex ρ l₁
                    (Work.KMTAreas.A7.varphiNt (N n) k₁ t) f else 0) y)) x) p
            MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C * Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂) *
              MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => (if S n then Work.KMTAreas.A7.Tex ρ l₁
                  (Work.KMTAreas.A7.varphiNt (N n) k₁ t) f else 0) x)) p
                MeasureTheory.Measure.count

/-- **The target follows from its masked residual**: split the data according to whether all columns
lie in `ℓᵖ`.  In the negative case a column outside `ℓᵖ` makes the right-hand side `⊤`
(`eLpNorm_variationalNorm_eq_top_of_not_memLp`), so the inequality holds trivially; in the positive
case the residual applies verbatim. -/
theorem FiberVarSamplingRep_of_residual (r : NNReal) (hr : 2 < r)
    (hres : FiberVarSamplingRepResidual r) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ∃ C : ℝ, 0 < C ∧
        ∀ (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ) (N : ℕ → ℕ) (S : ℕ → Prop) [DecidablePred S],
          t ∈ Set.Icc (1/2 : ℝ) 1 →
          (∀ n : ℕ, S n → k₁ + 1 + 2 * Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂
              ≤ (Work.Analysis.EndVar.logN (N n)).toNat) →
          (∀ n : ℕ, S n → Work.KMTAreas.A7.splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < N n) →
          MeasureTheory.eLpNorm (fun x : ℤ =>
              Work.KMTAreas.A7.residueLp p.toReal (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
                (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r
                  (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l₁
                    (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂)) n₀
                    (if S n then Work.KMTAreas.A7.Tex ρ l₁
                      (Work.KMTAreas.A7.varphiNt (N n) k₁ t) f else 0) y)) x) p
              MeasureTheory.Measure.count
            ≤ ENNReal.ofReal (C * Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                  (fun n : ℕ => (if S n then Work.KMTAreas.A7.Tex ρ l₁
                    (Work.KMTAreas.A7.varphiNt (N n) k₁ t) f else 0) x)) p
                  MeasureTheory.Measure.count := by
  obtain ⟨A, hA, ρ₀, hρ₀, H⟩ := hres
  refine ⟨A, hA, ρ₀, hρ₀, ?_⟩
  intro p hp hptop ρ hρ hρ1
  obtain ⟨C, hC, HC⟩ := H p hp hptop ρ hρ hρ1
  refine ⟨C, hC, ?_⟩
  intro l₁ l₂ k₁ k₂ t f N S _ ht hband hsplit
  by_cases hcols : ∀ n : ℕ, MeasureTheory.eLpNorm (if S n then Work.KMTAreas.A7.Tex ρ l₁
      (Work.KMTAreas.A7.varphiNt (N n) k₁ t) f else 0) p MeasureTheory.Measure.count ≠ ⊤
  · exact HC l₁ l₂ k₁ k₂ t f N S hcols ht hband hsplit
  · obtain ⟨n, hn⟩ := not_forall.mp hcols
    have htop : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => (if S n then Work.KMTAreas.A7.Tex ρ l₁
          (Work.KMTAreas.A7.varphiNt (N n) k₁ t) f else 0) x)) p
        MeasureTheory.Measure.count = ⊤ :=
      eLpNorm_variationalNorm_eq_top_of_eLpNorm_eq_top r
        (fun n : ℕ => if S n then Work.KMTAreas.A7.Tex ρ l₁
          (Work.KMTAreas.A7.varphiNt (N n) k₁ t) f else 0) n (not_not.mp hn)
    have hne : ENNReal.ofReal (C * Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]
      have hLpos : 0 < Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂ :=
        lt_of_lt_of_le zero_lt_one
          (Work.KMTAreas.A7Hi.one_le_lossWeight_of_nonneg A ρ hA hρ.le l₁ l₂ k₁ k₂)
      exact mul_pos hC hLpos
    rw [htop, ENNReal.mul_top hne]
    exact le_top

/-- The target.  Its remaining content is exactly the residual `FiberVarSamplingRepResidual r`
(`FiberVarSamplingRep_of_residual`); see the module docstring and
`NOTES_A7Rescue_FiberVarSamplingRep_SESSION2.md`. -/
theorem FiberVarSamplingRep (r : NNReal) (hr : 2 < r) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ∃ C : ℝ, 0 < C ∧
        ∀ (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ) (N : ℕ → ℕ) (S : ℕ → Prop) [DecidablePred S],
          t ∈ Set.Icc (1/2 : ℝ) 1 →
          (∀ n : ℕ, S n → k₁ + 1 + 2 * Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂
              ≤ (Work.Analysis.EndVar.logN (N n)).toNat) →
          (∀ n : ℕ, S n → Work.KMTAreas.A7.splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < N n) →
          MeasureTheory.eLpNorm (fun x : ℤ =>
              Work.KMTAreas.A7.residueLp p.toReal (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
                (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r
                  (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l₁
                    (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂)) n₀
                    (if S n then Work.KMTAreas.A7.Tex ρ l₁
                      (Work.KMTAreas.A7.varphiNt (N n) k₁ t) f else 0) y)) x) p
              MeasureTheory.Measure.count
            ≤ ENNReal.ofReal (C * Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                  (fun n : ℕ => (if S n then Work.KMTAreas.A7.Tex ρ l₁
                    (Work.KMTAreas.A7.varphiNt (N n) k₁ t) f else 0) x)) p
                  MeasureTheory.Measure.count := by
  -- The `ℓ²` case (`hf2 : Memℓp f 2`) is the *proved* theorem
  -- `Work.KMTAreas.A7Rescue.fiberVarSamplingRepMemLpTwo` in `A7Rescue/fiberVarSamplingRepMemLpTwo.lean`
  -- (which imports this file, so it cannot be imported back — call it from a *downstream* file).
  -- The remaining case is the wild/masked one; see the module docstring and the notes file.
  sorry

end Work.KMTAreas.A7Rescue
