import Mathlib
import Submission.Work.KMTAreas.A7Rep.fiberOpVarNonFareyBoundedRep
import Submission.Work.KMTAreas.A7Rep.mStarF_eq_one_of_varphiN_ne
import Submission.Work.KMTAreas.A7Hi.PacketRotationResidueBoundQuarter
import Submission.Work.KMTAreas.A7.arithChar_eq_iwQ0_mul_KW
import Submission.Work.KMTAreas.A7.fibreVarSampling_of_bandLimited
import Submission.Work.KMTAreas.A7.uRep_nonAliasing

namespace Work.KMTAreas.A7

/-- **The bounded-scale regime of the target, with the residue average.**  If
`L := max (max l₁ l₂) (max k₁ k₂) ≤ B ρ` then the fibre estimate holds with a constant depending
only on `ρ` and `p` (no `lossWeight` needed, since `lossWeight A ... ≥ 1`), for *every* input
family `u`; the `ℓ^p`-average over the residues is converted into the per-residue bounds by Tonelli
(`eLpNorm_residueLp_le_of_single`). -/
theorem rep_smallL (r : NNReal) (hr : 2 < r) :
    ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ (p : ENNReal), 1 < p → p < ⊤ → ∀ (B : ℝ → ℕ),
      ∃ C : ℝ, 0 < C ∧
        ∀ (l₁ l₂ k₁ k₂ : ℕ), max (max l₁ l₂) (max k₁ k₂) ≤ B ρ →
        ∀ (u : ℕ → ℤ → ℂ),
          MeasureTheory.eLpNorm (fun x : ℤ =>
              Work.KMTAreas.A7.residueLp p.toReal (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
                (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r
                  (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l₁
                    (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂)) n₀ (u n) y)) x) p
              MeasureTheory.Measure.count
          ≤ ENNReal.ofReal C *
              MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => u n x)) p MeasureTheory.Measure.count := by
  intro ρ hρ hρ1 p hp hptop B
  obtain ⟨C, hCpos, hC⟩ :=
    Work.KMTAreas.A7Rep.fiberOpVarNonFareyBoundedRep r hr ρ hρ hρ1 p hp hptop B
  refine ⟨C, hCpos, ?_⟩
  intro l₁ l₂ k₁ k₂ hL u
  have hpne : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have hpt : p ≠ ⊤ := ne_of_lt hptop
  have hpR : (0 : ℝ) < p.toReal := ENNReal.toReal_pos hpne hpt
  have hqpos : 0 < Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) := Work.KMTAreas.A7.arithQ_pos ρ _
  have hofReal : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal hpt
  have hsingle : ∀ n₀ : ℕ, MeasureTheory.eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l₁
            (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂)) (n₀ : ℤ) (u n) x))
        (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u n x))
        (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count := by
    intro n₀
    have h := hC l₁ l₂ k₁ k₂ hL (n₀ : ℤ) u
    simpa only [hofReal] using h
  have hmain := Work.KMTAreas.A7.eLpNorm_residueLp_le_of_single hpR hqpos
    (A := fun x n₀ => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l₁
        (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂)) n₀ (u n) x))
    (B := ENNReal.ofReal C * MeasureTheory.eLpNorm (fun x : ℤ =>
      PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u n x))
      (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count) hsingle
  simpa only [hofReal] using hmain

/-
# `Work.KMTAreas.A7.FiberVarSamplingRep` — the f-side §8 fibre variational sampling estimate at
the repaired window `uRep`: STATUS and the EXACT remaining work (updated)

Target file: this file; theorem `Work.KMTAreas.A7.FiberVarSamplingRep` (statement verbatim).

**State.**  The target still carries its `sorry`, but it is *reduced by proved lemmas* to a single
`Prop` (`FiberVarSamplingRepLarge B r`), and the analytic core of §8 that this used to be blocked on
is now **PROVED in the tree**:

* `Work.KMTAreas.A7Hi.PacketRotationResidueBoundShift` (**proved**, 0 sorries) — the
  residue-averaged packet/window rotation bound: for `q > 0`, `δ > 0` with `δ·q ≤ 1/8`, a
  `q`-torsion frequency set `A`, envelopes `f n α` band-limited to `arcSet 0 δ` and in `ℓ²`, and
  **any** rotation family `M : ℕ → ℤ`,
  `‖residueLp p q (n₀ ↦ Vʳ_n(winRot A (f n) (M n₀)))‖_{ℓᵖ} ≤ C ‖Vʳ_n(winSynth A (f n))‖_{ℓᵖ}`.
  (Rubio de Francia's square-function inequality, formerly the blocker, is now proved:
  `Work.Analysis.RubioDeFrancia.square_function` has 0 sorries.)

## What is proved in / around this file (sorry-free)

* `rep_smallL` (below) — the whole **bounded-scale** regime `L ≤ B ρ`, with the residue average, for
  an *arbitrary* input family (Tonelli + `A7Rep.fiberOpVarNonFareyBoundedRep`).
* `FiberVarSamplingRep_of_large` (below) — the **gluing**: for *any* `B : ℝ → ℕ`,
  `FiberVarSamplingRepLarge B r → the target`.
* `A7Rep.texWideCutRep` — the **range identity**
  `fiberOp ρ l₁ (mStarF (uRep ρ l₁ l₂ k₁ k₂)) 0 (Tex ρ l₁ (varphiNt N k₁ t) f) = Tex ρ l₁ (varphiNt N k₁ t) f`
  for **bounded** `f` under the band condition.
* `A7Hi.fiberOp_eq_windowRotation` — the exact identity
  `fiberOp ρ l m M u x = Σ_α e(Mα)·e(-xα)·(Σ_j e((x-j)α)·cw m j·u(x-j))`, hence, writing
  `env α x := Σ_j e((x-j)α)·cw m j·u(x-j)`,
  `fiberOp ρ l m M u = winRot A (env) (-M)` and `winSynth A (env) = fiberOp ρ l m 0 u`.
* `A7Hi.fiberOp_windowSynthesis` + the `winConv`/`WindowEnvelopesHasFreqSupport*`/`winSynth` chain
  (all 0 sorries in `Submission/Work/KMTAreas/A7Hi/`) — the window decomposition
  `u n = Σ_α winMod α (winConv m' (winMod (-α) (u n)))` of the range of the wide cut, with the
  envelopes in `ℓ²` and band-limited (the `HasFreqSupport` bookkeeping).
* `A7Hi.mStarF_eq_one_of_varphiN_ne` (`A7Rep/…`), `A7.farey_and_strict_of_large_L`,
  `A7.uRep_nonAliasing` — the plateau / Farey / non-aliasing inputs of the large regime.

## The recipe that closes `FiberVarSamplingRepLarge B r` (and hence the target)

For `L > B ρ` (so `L` large) and `n ∈ S`:
1. `texWideCutRep` gives the range hypothesis `fiberOp ρ l₁ (mStarF U) 0 (u n) = u n`, where
   `u n := Tex ρ l₁ (varphiNt (N n) k₁ t) f`;
2. the window decomposition writes `u n = winSynth A (env n)` with `env n α ∈ ℓ²` band-limited to
   `arcSet 0 β_n`, `β_n := 2^{k₁}/N n` (and `env n α := 0` off `S`);
3. `fiberOp_eq_windowRotation` gives `fiberOp ρ l₁ (mStarF U) n₀ (u n) = winRot A (env n) (-n₀)`;
4. `farey_and_strict_of_large_L` gives `8·2^{k₁}·arithQ ρ (max l₁ l₂) ≤ N n` for `n ∈ S`, and the
   tree's sharp support estimate `varphiNt_support_mul_le` (`A7/fiberVarSamplingLargeLossAux.lean`)
   turns this into `|ξ|·q ≤ 1/4` for `ξ ∈ supp (varphiNt (N n) k₁ t)`: the envelopes are therefore
   band-limited to `arcSet 0 δ` with **`δ := 1/(4q)`** (note: NOT `1/(8q)` — the integer `logN` is
   a floor, so only the quarter radius is available; a delegation at `1/(8q)` was correctly
   refuted).  `δ·q ≤ 1/4` is exactly the hypothesis of the **proved**
   `Work.KMTAreas.A7Hi.PacketRotationResidueBoundQuarter` (the `1/4`-variant of the crux), applied
   with the rotation family `M n₀ := n₀`, the frequency set `A := iwArithFreqsNew ρ l₁` (which is
   `q`-torsion since `arithQ ρ (max l₁ l₂)` kills `(ℚ/ℤ)_{≤ max l₁ l₂}`);
5. the RHS of the crux is `‖Vʳ(u_·)‖` because `winSynth A (env ·) = fiberOp ρ l₁ m 0 (u ·) = u ·`.

**Rotation-index fine print.**  The bridge gives `fiberOp … M (Tex …) = winRot A env (-M)`, while
`PacketRotationResidueBoundQuarter` is stated with the rotation index `(n₀ : ℤ)` itself.  The two
agree after the reindexing `n₀ ↦ -n₀`, because `q • α = 0` for `α ∈ A` makes `e(-jα)` depend on `j`
only modulo `q`: for `n₀ < q` one has `winRot A env (-n₀) = winRot A env (q - n₀)`, and
`n₀ ↦ q - n₀` permutes `{0,…,q-1}` up to the periodicity `winRot A env q = winRot A env 0`; hence
the two `residueLp`-expressions are *equal* (a small `Finset.sum_range_reflect` + periodicity
argument).  Equivalently, a `1/4`-plus-arbitrary-shift variant of the crux (the analogue of
`PacketRotationResidueBoundShift` at the quarter radius, whose proof is the same verbatim) would
remove the need for the reindexing; it is not in the tree.

The envelope bridge (the `∃ env` with conjuncts (i) `Memℓp`+`HasFreqSupport` at the quarter radius,
(ii) `winSynth A env = Tex …`, (iii) `fiberOp … M (Tex …) = winRot A env (-M)` for all `M`) is
delegated as `Work.KMTAreas.A7Rep.texWindowEnvelopesQuarter`; its natural witness is
`env α := windowEnvelopes (mStarF U) (Tex ρ l₁ (varphiNt N k₁ t) f) α`, and the ingredients are
`winSynth_windowEnvelopes`, `winRot_windowEnvelopes`, `windowEnvelopesHasFreqSupport_twoRadius`,
`tex_varphiNt_memLpTwo_freqSupport`, `texWideCutRep`, `uRep_nonAliasing`.

## Two traps (both cost time; do not re-derive)

* **The quantitative Farey budget must be taken on the input band `β = 2^{k₁}/N`, never on the
  plateau `δ_0 = 2^{-2U-1}`.**  `q·δ_0 ≤ 1/8` is FALSE for `ρ < 1/2`, `k₁ = k₂ = 0`, `max l₁ l₂`
  large (`arithQ ρ l = e^{Θ(2^l)}` while `2^{2U} = 2^{2·2^{2ρl}}`).  Only `q·β ≤ 1/8` holds, and it
  is exactly the Farey condition of `farey_and_strict_of_large_L`.
* **Boundedness *and* `ℓ²`-honesty.**  `fiberOp_eq_windowRotation` needs `u n` *bounded*, and the
  cut identity is FALSE for arbitrary `f` (`NOTES_A7_fiberOpTex_eq_fiberOp_self_REFUTATION.md`).
  Moreover the crux `PacketRotationResidueBoundShift` *requires* its envelopes to be in `ℓ²`
  (`∃ hh : Memℓp (f n α) 2, HasFreqSupport …`), and a *bounded* `f` does **not** make
  `Tex ρ l₁ (varphiNt N k₁ t) f` lie in `ℓ²` (witness: `f x = e(xβ)`, `Tex` then has constant
  modulus and is not `ℓ²`; this refuted a first form of the envelope-bridge delegation).  Hence the
  large case needs the *honest* (`Memℓp f 2`) case plus the reduction from arbitrary `f`, exactly as
  for the `uScale` sibling: `A7/fiberVarSamplingLarge_tame.lean` (proved) uses a *tameness*
  hypothesis, and its consumer `A7/fibreVarSampling_of_honest.lean` (**proved**) performs the
  reduction from arbitrary `f` (in the non-honest regime the RHS `‖Vʳ(u_·)‖_{ℓᵖ}` is `⊤`, since the
  family is a non-`ℓᵖ` constant-modulus character-like sequence, so the inequality is trivial).  A
  Rep analogue of `fibreVarSampling_of_honest` is the last missing *reduction*; the *honest* large
  case is then the recipe above (with `texWindowEnvelopes` supplying the envelopes, hypotheses
  `Memℓp f 2` + bounded `f`).

## Simplifications of the remaining work (recorded late in the session)

* **`ℓᵖ ⊆ ℓ^∞`.**  For `0 < p < ∞` a square/`p`-summable sequence is bounded, so the *bounded*
  case of the estimate (the extra hypothesis `∃ B, ∀ x, ‖f x‖ ≤ B`) covers every `f ∈ ℓᵖ`; the tree
  proves the `uScale` bounded case as `Work.KMTAreas.A7.fiberVarSamplingLargeLoss_bdd` and its
  polished form `fiberVarSamplingLarge_tame`/`fibreVarSampling_of_honest`.  The paper's own setting
  has `ℓ^{p₁}` (hence bounded) input, so the target's quantification over *arbitrary* `f` is
  stronger than what the paper needs.
* **Non-`ℓᵖ` families give `⊤`.**  Since `Vʳ(u_·)(x) ≥ sup_n ‖u n x‖ₑ`, if for some `n` the function
  `u n` is not in `ℓᵖ` then the target's right-hand side is `⊤` and the inequality is trivial.  So
  the only content of the target is the case where every column `u n` lies in `ℓᵖ` — in particular
  (by the previous point) the bounded case.
* **The junk regime.**  For `f` bounded but with `Tex ρ l₁ (varphiNt N k₁ t) f ∉ ℓ²` (possible when
  `p ≠ 2`), the crux route above does *not* apply (it needs the envelopes in `ℓ²`), and the tree's
  own notes (`A7/fiberVarSamplingLarge.lean`, §21) record that the junk-robust Young/kernel route
  also fails (a `2^{l₁}`-loss).  A Rep analogue of the *proved* `uScale` bounded-case proof
  (`fiberVarSamplingLargeLoss_bdd`) is therefore the remaining mathematical input; the recipe above
  closes the `ℓ²`- (hence, by `ℓᵖ ⊆ ℓ^∞`, the `ℓᵖ`-) sub-case.

## THE CURRENT ROUTE TO THE TARGET (session end, aligned with the A7Rescue agent)

A parallel agent works the *same* target (as `Work.KMTAreas.A7Rescue.FiberVarSamplingRep`) in
`Submission/Work/KMTAreas/A7Rescue/`; that directory *imports this file* and uses the proved
`rep_smallL` here.  Its `FiberVarSamplingRep.lean` docstring ("The remaining gap …") is the most
up-to-date analysis of what is left; the essentials:

* **PROVED there** (sorry-free, axiom-clean):
  `Work.KMTAreas.A7.fibreVarSampling_quarter` — the band-limited fibre estimate with the *free*
  radii family `W` and the quarter Shannon condition `W n · q ≤ 1/4` (proved from the crux
  `A7Hi.PacketRotationResidueBoundQuarter`); and
  `Work.KMTAreas.A7Rescue.fiberVarSamplingRepMemLpTwo` — **the target's inequality for `f ∈ ℓ²`**
  (assembled from `rep_smallL` (this file) + `fibreVarSampling_quarter` + `lmax_le_of_not_farey`;
  the `S`-clipping is handled by choosing the free radii off `S`).
* **OPEN (the single remaining input): the MASKED case.**  For `f ∉ ℓ²` the `tsum`-realisation of
  `Tex` is junk (Lean's `tsum` is `0`) at some points, and the stored column is
  `w n = 1_{E n} · (honest band-`W n` convolution)` with `E n` `d`-periodic, `d = arithQ ρ l₁`.
  The fibre estimate must therefore hold for the *masked* families `1_{E n} v n` with `v n` honest
  and band-`W n`.  Its `p = 2` single-scale half follows from the `d`-torsion orthogonality
  `d⁻¹ Σ_{n₀<d} |T_{n₀} w (y)|² = Σ_{α ∈ A} |P_α w (y)|²` (`A = iwArithFreqsNew ρ l₁`) plus
  `Σ_α ‖P_α w‖²_{ℓ²} ≤ ‖w‖²_{ℓ²}` (the `mStarF U`-arcs are disjoint, `uRep_nonAliasing`); the
  general-`p`/`Vʳ` half needs the *coherent torsion-band packet-rotation bound* (the proved crux
  does not apply verbatim, because those pieces have spectra that are unions of `W`-narrow bits at
  the `d`-torsion points rather than a single arc).  The target's fibre is exactly the weighted
  packet rotation `T_{n₀} w = Σ_{α ∈ A} e(α n₀) · P_α w` with synthesis `w`, and the `q`-residue
  average gains `(d/q)^{1/p}` over the `d`-average since the phases are `d`-torsion.
* **Then** the target is `by_cases hf2 : Memℓp f 2` with the *proved* `fiberVarSamplingRepMemLpTwo`
  in the positive case and the masked case in the negative one (a downstream assembly file may
  import both `A7Rescue` files; note `A7Rescue/fiberVarSamplingRepMemLpTwo.lean` imports
  `A7Rescue/FiberVarSamplingRep.lean`, so the downstream file must not create a cycle).

## Proved siblings to mirror

* `Submission/Work/KMTAreas/A7/fiberVarSampling.lean` (**0 sorries**) — the `uScale` f-side target,
  proved from `A7.fiberVarSamplingLargeLoss` (proved) by `fiberVarSampling_of_core`.
* `Submission/Work/KMTAreas/A7/fiberVarSamplingLargeLoss.lean` / `_bdd.lean` / `_tame.lean` /
  `_growth.lean` (**0 sorries**) — the `uScale` large regime.
* `Submission/Work/KMTAreas/A7Hi/FiberVarSamplingG.lean` and `FiberVarSamplingGLarge.lean`
  (**0 sorries**) — the whole g-side `uScale` chain.
* `Submission/Work/KMTAreas/A7Rep/fiberVarSamplingGRepGlue.lean` +
  `fiberVarSamplingGRepSmallL.lean` (**0 sorries**) — the g-side *Rep* gluing and bounded-scale
  case (the exact analogue of `FiberVarSamplingRep_of_large` + `rep_smallL` here).
-/
/-- **The statement of the target, as a `Prop`** (the target itself is a `theorem`, so it cannot
be used in type position).  This is its statement, verbatim. -/
def FiberVarSamplingRepStatement (r : NNReal) : Prop :=
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
                    MeasureTheory.Measure.count

/-- **The large-scale case of the target** (`B ρ < L = max (max l₁ l₂) (max k₁ k₂)`): the target's
statement restricted to the scales above the threshold `B : ℝ → ℕ`.  This is the single remaining
mathematical input of the target -- equivalently, the residue-averaged form of
`Work.KMTAreas.A7Hi.FiberOpCutVarBound` / its `M = 0` core `FiberOpCutZeroVarBound`; see the module
docstring above for its precise shape and for its blocker
(`Work.Analysis.RubioDeFrancia.square_function`). -/
def FiberVarSamplingRepLarge (B : ℝ → ℕ) (r : NNReal) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
        ∀ (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
        ∃ C : ℝ, 0 < C ∧
          ∀ (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ) (N : ℕ → ℕ) (S : ℕ → Prop) [DecidablePred S],
  B ρ < max (max l₁ l₂) (max k₁ k₂) →
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
/-- **The gluing of the two regimes of the target.**  Given the large-scale case
`FiberVarSamplingRepLarge B r` for *any* threshold `B : ℝ → ℕ`, the target statement follows from
the proved bounded-scale estimate `rep_smallL` (which holds for every `B`, with a `ρ`-dependent but
`B`-uniform constant).  The construction mirrors the one used for the sibling g-side statement in
`Submission/Work/KMTAreas/A7Rep/fiberVarSamplingGRepGlue.lean`: take `A := A₂`, `ρ₀ := min 1 ρ₀₂`,
`C := max C₁ C₂`; the loss-free constant of the bounded-scale case is absorbed by
`lossWeight A₂ ρ · ≥ 1`. -/
theorem FiberVarSamplingRep_of_large (r : NNReal) (hr : 2 < r) (B : ℝ → ℕ)
    (hlarge : FiberVarSamplingRepLarge B r) : FiberVarSamplingRepStatement r := by
  obtain ⟨A₂, hA₂, ρ₂, hρ₂, H₂⟩ := hlarge
  refine ⟨A₂, hA₂, min 1 ρ₂, lt_min one_pos hρ₂, ?_⟩
  intro p hp hptop ρ hρ hρm
  have hρ1 : ρ ≤ 1 := le_trans hρm (min_le_left _ _)
  have hρ2 : ρ ≤ ρ₂ := le_trans hρm (min_le_right _ _)
  obtain ⟨C₁, hC₁, H₁⟩ := rep_smallL r hr ρ hρ hρ1 p hp hptop B
  obtain ⟨C₂, hC₂, H₂'⟩ := H₂ p hp hptop ρ hρ hρ2
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, ?_⟩
  intro l₁ l₂ k₁ k₂ t f N S _ ht hband hsplit
  have hLW1 : (1 : ℝ) ≤ Work.KMTAreas.A7.lossWeight A₂ ρ l₁ l₂ k₁ k₂ := by
    have h0 : Work.KMTAreas.A7.lossWeight 0 ρ l₁ l₂ k₁ k₂ = 1 := by
      simp [Work.KMTAreas.A7.lossWeight]
    have hm := Work.KMTAreas.A7.lossWeight_mono_A (le_refl (0 : ℝ)) hA₂ ρ hρ.le l₁ l₂ k₁ k₂
    rwa [h0] at hm
  by_cases hcase : max (max l₁ l₂) (max k₁ k₂) ≤ B ρ
  · have hb := H₁ l₁ l₂ k₁ k₂ hcase (fun n =>
      if S n then Work.KMTAreas.A7.Tex ρ l₁ (Work.KMTAreas.A7.varphiNt (N n) k₁ t) f else 0)
    have hstep : C₁ ≤ max C₁ C₂ * Work.KMTAreas.A7.lossWeight A₂ ρ l₁ l₂ k₁ k₂ := by
      nlinarith [hLW1, le_max_left C₁ C₂, le_of_lt hC₁]
    exact le_trans hb (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hstep) bot_le)
  · have hlt : B ρ < max (max l₁ l₂) (max k₁ k₂) := lt_of_not_ge hcase
    have hb := H₂' l₁ l₂ k₁ k₂ t f N S hlt ht hband hsplit
    have hstep : C₂ * Work.KMTAreas.A7.lossWeight A₂ ρ l₁ l₂ k₁ k₂
        ≤ max C₁ C₂ * Work.KMTAreas.A7.lossWeight A₂ ρ l₁ l₂ k₁ k₂ :=
      mul_le_mul_of_nonneg_right (le_max_right C₁ C₂)
        (Work.KMTAreas.A7.lossWeight_nonneg _ _ _ _ _ _)
    exact le_trans hb (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hstep) bot_le)

/-- The target.  (Its remaining input is `FiberVarSamplingRepLarge B r`; see the module docstring.)

**REFUTED (session 3) — see `NOTES_A7_FiberVarSamplingRep_SESSION3.md` at the workspace root.**
The statement is *false* for every `p ∈ (1,2)`: it quantifies over **arbitrary** `f : ℤ → ℂ`,
whereas the paper's §8 estimate is applied to `f ∈ ℓ^{p₁}` (hence bounded).  Indeed the fibre
`Tex ρ l₁ φ` has kernel `k_j = (∑_{α ∈ iwArithFreqsNew ρ l₁} e(-jα)) · cw φ j`, and the "inverse
filter" `f n := (1/2πi) ∮_{|λ|=R} K(λ)^{-1} λ^{n-1} dλ` (with `K(λ) = ∑_j k_j λ^{-j}`, `R` chosen
with `K ≠ 0` on `|λ| = R` — possible since the zero set of the non-zero analytic function `K` on
`ℂ^*` is countable) is an *exponentially growing* sequence with
`Σ_j k_j f (n-j) = (1/2πi) ∮_{|λ|=R} λ^{n-1} dλ = δ_{n,0}`, i.e. `Tex ρ l₁ φ f = δ₀` **exactly**
(no junk; the honest set is all of `ℤ`).  With `S = {1}` both sides are then computable: the fibre
of a spike is `χ_A(n₀-x)·cw (mStarF U) x` with `χ_A(z) = ∑_{α∈A} e(zα)`, so
`LHS = β·(⍱_{z<d}|χ_A(z)|^p)^{1/p}·‖cw (mStarF U)‖_{ℓ^p}` and `RHS = ofReal(C·lossWeight)·β`
(`β` cancels).  Numerics give `⍱_{z<d}|χ_A| ≈ 0.3·2^{l₁}` (exponential; exact for `l₁ ≤ 4`,
verified up to `l₁ = 13`), and `‖cw (mStarF U)‖_{ℓ^p} ≳ 2^{-2U(1-1/p)}`; hence with `p = 1+ε`,
`l₁ = ⌈1/ρ⌉`, the LHS is `2^{Θ(1/ρ)}` while the RHS is only
`C(1+l₁)^A 2^{Aρl₁} = 2^{O(A log(1/ρ))}` — contradiction as `ρ → 0`.  The repair is a growth
hypothesis on `f` (polynomial growth / `ℓ^{p₁}`), exactly as in the tree's proved branches
(`A7.fiberVarSamplingLarge_growth`, `A7.fiberVarSamplingLargeLoss_bdd`); with such a hypothesis
the spike construction is unavailable and the inequality is the sibling `_growth` theorem. -/
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
                  MeasureTheory.Measure.count := by sorry

end Work.KMTAreas.A7
