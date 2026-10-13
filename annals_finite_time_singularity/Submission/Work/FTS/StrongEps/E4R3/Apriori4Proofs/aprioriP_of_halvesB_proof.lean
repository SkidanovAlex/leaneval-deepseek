import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Defs
import Submission.Work.FTS.StrongEps.EpsE4Thr.AprioriSixthBound
import Submission.Work.FTS.StrongEps.StrongEpsP.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Apriori4Proofs/aprioriP_of_halvesB_proof.lean` — the leaf L-B, and the two hypotheses it
is missing

Status of this file (owner note, do read before re-pointing the task):

* the **target** `aprioriP_of_halvesB_proof` is left as installed (`sorry`): its statement is **not
  derivable from its hypotheses** — see §1 below;
* the **corrected** statement, with the two missing hypotheses made explicit, is proved here as
  `aprioriP_of_halvesB_strict` (sorry-free, standard axioms); it is the statement a producer should
  aim at, and `Apriori4.lean`'s call site can be adapted to it without changing any constant;
* the standalone real-analysis brick used by it is a `private` copy `sInf_crossing_aux` (so that
  this file is self-contained); the same lemma is proved publicly as
  `Work.FTS.StrongEps.E4R3.Apriori4Proofs.sInf_crossing` (`…/sInf_crossing.lean`), which is the
  name to use in a restated leaf;

## 1. Why the target statement is not provable as stated

Unfolding `EpsE4Thr/Reduction.AprioriP` and `E4R3/Apriori4Defs.{AprioriPSixthB,
AprioriPFourthB}`, for a fixed horizon `T'' ∈ (0,T]` and a regular `P₀`-solution `g` the two
hypotheses are exactly the two implications

* `h4` : `P(T'') ⟹ Q(T'')`,  `P(T'') := ∀τ∈[0,T''], Xn6 α (slice g τ) ≤ √(2E₁+1)`,
  `Q(T'') := ∀τ∈[0,T''], Xn α (slice (JfamP ρ ε g) τ) ≤ C₀α²`;
* `h6` : `Q(T'') ⟹ C(T'')`,  `C(T'') := ∀τ∈[0,T''], rawE6 α g τ ≤ E₁`.

Conversely `C(T'') ⟹ P(T'')`, because `HkSq α 6 = Xn6² ≤ IP6o = rawE6`
(`EpsE4Thr.HkSq_le_IP6`, the level-six loop) and `√E₁ ≤ √(2E₁+1)` (`hE₁`).  Hence at **every**
horizon the three interval statements are *equivalent*, and the only datum-level information
available is the `τ = 0` instance (`slice g 0 = g₀`): `Xn6 α g₀ ≤ √(2E₁+1)` and
`Xn α (Pz (Jeps ρ ε g₀)) ≤ C₀α²`, i.e. exactly the conclusion at `τ = 0`.  So `h6 ∧ h4` alone
force nothing beyond `P(T') ↔ Q(T')`, and both may fail: the standard maximal-interval argument
needs a *first interval* on which the bounds hold and a way to reach the supremum of the good set.

Concretely, the closing argument is the following (it is implemented in
`aprioriP_of_halvesB_strict`): let `S := {τ ∈ [0,T'] : √(2E₁+1) < Xn6 α (slice g τ)}` and
`s := sInf S`.  Then `s ∉ S`, `Xn6 α (slice g s) = √(2E₁+1)` and `Xn6 ≤ √(2E₁+1)` on `[0,s]`
(*provided* the map `τ ↦ Xn6 α (slice g τ)` is continuous at `s`); `h4` at horizon `s` then gives
`Q` on `[0,s]`, `h6` gives `rawE6 ≤ E₁` on `[0,s]`, so `Xn6 ≤ √E₁` on `[0,s]` — a **strict**
contradiction with `Xn6 α (slice g s) = √(2E₁+1) > √E₁`.  That contradiction also needs `s > 0`,
i.e. the datum must satisfy the **strict** inequality `Xn6 α g₀ < √(2E₁+1)`; with only `≤`, the
case `Xn6 α g₀ = √(2E₁+1)` together with an immediate crossing (`s = 0`) is consistent with `h4`
and `h6` (`h6` then forces that no solution has `Q` on any interval, `h4` that none has `P`; both
are vacuous and the conclusion still fails at the first crossing time).

Neither input is a consequence of the standing hypotheses:

* continuity of `τ ↦ Xn6 α (slice g τ)` is *not* derivable from `EpsRegP + IsEpsSolP` (per-slice
  `HkMem α 6` plus joint `C¹` allow the `ℋ⁶`-norms to jump while the values converge) — this is
  risk **R2** of `E4R3/Apriori4Leaves/RawE6Deriv.lean`, whose own statement carries the uniform
  bound `hbdd6 : ∃B, ∀τ∈[0,T], Xn6 α (slice g τ) ≤ B` as an explicit hypothesis, and it is
  recorded in `StrongEps/REPORT_LEAD_apriori4_decisions.md`, decision (1): “Per-slice honesty plus
  joint `C¹` does not even give continuity of `τ ↦ Xn6 (slice g τ)`”;
* the strict datum inequality is *not* implied by the non-strict one.  The same defect of
  `AprioriP`'s datum condition is already on file for the level-four half: `TransO`’s
  `AprioriFourthLevel.lean` says its barrier “is the one a producer should aim at … the current
  `AprioriPFourth` (which asks for the datum merely *in* the ball) is out of reach of this route”.

The corrected statement therefore adds

```
(hcont   : ∀ T' ∈ Set.Ioc 0 T, ∀ g, IsEpsSolP α ρ ε T' Φs E g₀ g → EpsRegP α ρ ε T' g →
             ContinuousOn (fun τ => Xn6 α (slice g τ)) (Icc 0 T'))
(hstrict : Xn6 α g₀ < √(2E₁+1))
```

and is proved below.  `hstrict` costs nothing at the intended call site (this is made formal by
`strict_datum_of_xn6_le` below): `Apriori4.lean` has `Xn6 α g₀ ≤ K·α²` with `α ≤ 1` from the datum
and `K ≤ √(2E₁+1)`, and the sixth chapter picks `E₁` with `K² ≤ E₁`, which gives
`Xn6 α g₀ ≤ K < √(2K²+1) ≤ √(2E₁+1)`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The first-crossing brick (private copy; the public one is `…/sInf_crossing.lean`) -/

/-- **First-crossing lemma.**  For `f` continuous on `[0,T]` with `f 0 < M` and `M < f τ` somewhere,
the first crossing time `s = sInf {τ ∈ [0,T] : M < f τ}` is positive, satisfies `f s = M`, and
`f ≤ M` already holds on `[0,s]`. -/
private theorem sInf_crossing_aux {f : ℝ → ℝ} {M T : ℝ} (hT : 0 < T)
    (hf : ContinuousOn f (Set.Icc 0 T)) (h0 : f 0 < M)
    (hU : ∃ τ ∈ Set.Icc 0 T, M < f τ) :
    0 < sInf {τ : ℝ | τ ∈ Set.Icc 0 T ∧ M < f τ} ∧
      sInf {τ : ℝ | τ ∈ Set.Icc 0 T ∧ M < f τ} ≤ T ∧
      f (sInf {τ : ℝ | τ ∈ Set.Icc 0 T ∧ M < f τ}) = M ∧
      ∀ τ ∈ Set.Icc 0 (sInf {τ : ℝ | τ ∈ Set.Icc 0 T ∧ M < f τ}), f τ ≤ M := by
  set S : Set ℝ := {τ : ℝ | τ ∈ Set.Icc 0 T ∧ M < f τ} with hSdef
  have hSne : S.Nonempty := hU
  have hSbd : BddBelow S := ⟨0, fun τ hτ => hτ.1.1⟩
  have hs0 : 0 ≤ sInf S := le_csInf hSne (fun τ hτ => hτ.1.1)
  have hsT : sInf S ≤ T := by
    obtain ⟨u, hu⟩ := hU
    exact le_trans (csInf_le hSbd (show u ∈ S from hu)) hu.1.2
  have hsmem : sInf S ∈ closure S := csInf_mem_closure hSne hSbd
  -- the infimum is a lower bound for `f`
  have hle : M ≤ f (sInf S) := by
    have hcl : IsClosed (Set.Icc 0 T ∩ f ⁻¹' Set.Ici M) :=
      hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hsub : S ⊆ Set.Icc 0 T ∩ f ⁻¹' Set.Ici M := fun x hx => ⟨hx.1, le_of_lt hx.2⟩
    exact (closure_minimal hsub hcl hsmem).2
  have hsIcc : sInf S ∈ Set.Icc 0 T := by
    have hcl : IsClosed (Set.Icc 0 T : Set ℝ) := isClosed_Icc
    exact closure_minimal (fun x hx => hx.1) hcl hsmem
  -- strict positivity: `0 ∉ S` because `f 0 < M`
  have hs_pos : 0 < sInf S := by
    have hne : sInf S ≠ 0 := by
      intro hzero
      have hM0 : M ≤ f 0 := by have := hle; rwa [hzero] at this
      exact absurd hM0 (not_le.mpr h0)
    exact lt_of_le_of_ne hs0 (Ne.symm hne)
  -- the infimum is an upper bound for `f`: otherwise continuity would produce a smaller crossing
  have hge : f (sInf S) ≤ M := by
    by_contra hcon
    rw [not_le] at hcon
    have hEv : ∀ᶠ τ in 𝓝[Set.Icc 0 T] (sInf S), M < f τ :=
      (hf (sInf S) hsIcc).tendsto.eventually_const_lt hcon
    have hEvSet : ({τ : ℝ | M < f τ} : Set ℝ) ∈ 𝓝[Set.Icc 0 T] (sInf S) := hEv
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhdsWithin_iff.mp hEvSet
    have hδ : 0 < min (ε / 2) (sInf S / 2) := lt_min (by linarith) (by linarith)
    set τ : ℝ := sInf S - min (ε / 2) (sInf S / 2) with hτdef
    have hτlt : τ < sInf S := by rw [hτdef]; linarith
    have hτd : dist τ (sInf S) < ε := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> rw [hτdef] <;>
        linarith [min_le_left (ε/2) (sInf S/2), min_le_right (ε/2) (sInf S/2), hε]
    have hτIcc : τ ∈ Set.Icc 0 T := by
      refine ⟨?_, ?_⟩
      · rw [hτdef]; linarith [min_le_right (ε / 2) (sInf S / 2)]
      · rw [hτdef]; linarith [hδ, min_le_left (ε / 2) (sInf S / 2)]
    have hMτ : M < f τ := hεsub ⟨by rw [Metric.mem_ball]; exact hτd, hτIcc⟩
    have : sInf S ≤ τ := csInf_le hSbd ⟨hτIcc, hMτ⟩
    linarith
  refine ⟨hs_pos, hsT, le_antisymm hge hle, ?_⟩
  intro τ hτ
  rcases lt_or_eq_of_le hτ.2 with hlt | heq
  · by_contra hcon
    rw [not_le] at hcon
    have hτS : τ ∈ S := ⟨⟨hτ.1, le_of_lt (lt_of_lt_of_le hlt hsT)⟩, hcon⟩
    have : sInf S ≤ τ := csInf_le hSbd hτS
    linarith
  · rw [heq]; exact hge

/-! ## The strict datum inequality is free at the intended call site -/

/-- **`hstrict` costs nothing along the route.**  The datum of `EpsE4R4Stmt`/`EpsE4R3` satisfies
`Xn6 α g₀ ≤ K·α² ≤ K` (with `α ≤ 1`, `0 ≤ K`), while the sixth chapter chooses `E₁` with `K² ≤ E₁`;
hence `Xn6 α g₀ ≤ K < √(2K²+1) ≤ √(2E₁+1)`: the strict inequality required by
`aprioriP_of_halvesB_strict` is automatic from the datum. -/
theorem strict_datum_of_xn6_le {α K E₁ : ℝ} {g₀ : Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hK : 0 ≤ K) (hE : K ^ 2 ≤ E₁)
    (hXn : Work.FTS.StrongGlobal.Xn6 α g₀ ≤ K * α ^ 2) :
    Work.FTS.StrongGlobal.Xn6 α g₀ < Real.sqrt (2 * E₁ + 1) := by
  have hα2 : α ^ 2 ≤ 1 := by nlinarith
  have h1 : Work.FTS.StrongGlobal.Xn6 α g₀ ≤ K := by
    calc Work.FTS.StrongGlobal.Xn6 α g₀ ≤ K * α ^ 2 := hXn
      _ ≤ K * 1 := mul_le_mul_of_nonneg_left hα2 hK
      _ = K := by ring
  have h2 : K < Real.sqrt (2 * K ^ 2 + 1) := by
    have hKs : K = Real.sqrt (K ^ 2) := (Real.sqrt_sq hK).symm
    rw [hKs]
    exact Real.sqrt_lt_sqrt (by positivity) (by nlinarith)
  have h3 : Real.sqrt (2 * K ^ 2 + 1) ≤ Real.sqrt (2 * E₁ + 1) :=
    Real.sqrt_le_sqrt (by linarith)
  linarith

/-! ## The corrected assembly -/

/-- **The maximal-interval assembly of the two halves**, with the two hypotheses the target
statement lacks (see the header): continuity in `τ` of the slices' `ℋ⁶`-size along the flow, and the
*strict* datum inequality `Xn6 α g₀ < √(2E₁+1)`.

The conclusion is `AprioriP` itself (whose datum condition is the weaker non-strict one), so this is
a drop-in strengthening of the requested statement; the proof is short:

* if `√(2E₁+1) < Xn6 α (slice g τ)` somewhere, the first-crossing brick gives `s` with
  `Xn6 α (slice g s) = √(2E₁+1)` and `Xn6 ≤ √(2E₁+1)` on `[0,s]`;
* `h4` at horizon `s` gives the ball on `[0,s]`, `h6` gives `rawE6 ≤ E₁` there, and the level-six
  loop `HkSq α 6 ≤ rawE6` turns that into `Xn6 ≤ √E₁` on `[0,s]` — contradicting `√E₁ < √(2E₁+1)`;
* so `Xn6 α (slice g τ) ≤ √(2E₁+1)` on `[0,T']`, and `h4` at horizon `T'` gives the ball. -/
theorem aprioriP_of_halvesB_strict {α ε T C₀ E₁ : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hE₁ : 0 ≤ E₁)
    (h6 : Work.FTS.StrongEps.EpsE4Thr.E4R4.AprioriPSixthB α ρ ε T Φs E g₀ C₀ E₁)
    (h4 : Work.FTS.StrongEps.EpsE4Thr.E4R4.AprioriPFourthB α ρ ε T Φs E g₀ C₀
      (Real.sqrt (2 * E₁ + 1)))
    (hcont : ∀ T' ∈ Set.Ioc 0 T, ∀ g : Fam,
      Work.FTS.StrongEps.IsEpsSolP α ρ ε T' Φs E g₀ g →
      Work.FTS.StrongEps.EpsRegP α ρ ε T' g →
      ContinuousOn (fun τ => Work.FTS.StrongGlobal.Xn6 α (slice g τ)) (Set.Icc 0 T'))
    (hstrict : Work.FTS.StrongGlobal.Xn6 α g₀ < Real.sqrt (2 * E₁ + 1)) :
    Work.FTS.StrongEps.EpsE4Thr.AprioriP α ρ ε T Φs E g₀ C₀ (Real.sqrt (2 * E₁ + 1)) := by
  intro _hM hsmall T' hT' hT'le g hsol hreg
  -- the slices' honesty, and the `ℋ⁶`-loop `HkSq α 6 ≤ rawE6`
  have hdat : ∀ τ ∈ Set.Icc 0 T', Work.FTS.StrongEps.EpsDatumP α ρ ε (slice g τ) := hreg.2
  -- the datum is strictly below the barrier
  have hslice0 : slice g 0 = g₀ := funext fun z => funext fun θ => hsol.1 z θ
  have hstrict0 : Work.FTS.StrongGlobal.Xn6 α (slice g 0) < Real.sqrt (2 * E₁ + 1) := by
    rw [hslice0]; exact hstrict
  -- the map whose first crossing is the barrier
  have hcontg : ContinuousOn (fun τ => Work.FTS.StrongGlobal.Xn6 α (slice g τ)) (Set.Icc 0 T') :=
    hcont T' ⟨hT', hT'le⟩ g hsol hreg
  have hP : ∀ τ ∈ Set.Icc 0 T',
      Work.FTS.StrongGlobal.Xn6 α (slice g τ) ≤ Real.sqrt (2 * E₁ + 1) := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨τ₀, hτ₀, hgt⟩ := hcon
    set s : ℝ := sInf {τ : ℝ | τ ∈ Set.Icc 0 T' ∧ Real.sqrt (2 * E₁ + 1)
      < Work.FTS.StrongGlobal.Xn6 α (slice g τ)} with hsdef
    have hsprop := sInf_crossing_aux (f := fun τ => Work.FTS.StrongGlobal.Xn6 α (slice g τ))
      (M := Real.sqrt (2 * E₁ + 1)) (T := T') hT' hcontg hstrict0 ⟨τ₀, hτ₀, hgt⟩
    rw [← hsdef] at hsprop
    obtain ⟨hspos, hsT', hsval, hsle⟩ := hsprop
    have hsT : s ≤ T := le_trans hsT' hT'le
    -- restrict the solution to the horizon `s`
    have hsolS : Work.FTS.StrongEps.IsEpsSolP α ρ ε s Φs E g₀ g :=
      Work.FTS.StrongEps.StrongEpsP.IsEpsSolP.mono hsol hsT'
    have hregS : Work.FTS.StrongEps.EpsRegP α ρ ε s g := hreg.mono hsT'
    -- `h4` at horizon `s`: the ball on `[0,s]`
    have hQ : ∀ τ ∈ Set.Icc 0 s,
        Work.FTS.Nonlin.Xn α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) ≤ C₀ * α ^ 2 :=
      h4 hsmall s hspos hsT g hsolS hregS hsle
    -- `h6` at horizon `s`: the raw energy bound on `[0,s]`
    have hraw : ∀ τ ∈ Set.Icc 0 s, Work.FTS.StrongEps.EpsE4Thr.E4R4.rawE6 α g τ ≤ E₁ :=
      h6 s hspos hsT g hsolS hregS hQ
    -- the level-six loop at `τ = s`
    have hloop : Work.Spaces.HkSq α 6 (slice g s)
        ≤ Work.FTS.StrongEps.EpsE4Thr.E4R4.rawE6 α g s := by
      have hd := hdat s ⟨hspos.le, hsT'⟩
      have h := Work.FTS.StrongEps.EpsE4Thr.HkSq_le_IP6 (α := α) ⟨hα, hα1⟩ hd.1 hd.2.1
      simpa only [Work.FTS.StrongEps.EpsE4Thr.E4R4.rawE6,
        Work.FTS.StrongEps.EpsE4Thr.E4R4.IP6o] using h
    have hsqrt : Work.FTS.StrongGlobal.Xn6 α (slice g s) ≤ Real.sqrt E₁ := by
      show Real.sqrt (Work.Spaces.HkSq α 6 (slice g s)) ≤ Real.sqrt E₁
      exact le_trans (Real.sqrt_le_sqrt hloop) (Real.sqrt_le_sqrt (hraw s ⟨hspos.le, le_rfl⟩))
    -- the strict margin `E₁ < 2E₁+1` gives the contradiction
    have hcontr : Real.sqrt (2 * E₁ + 1) ≤ Real.sqrt E₁ := by rw [← hsval]; exact hsqrt
    have h21 : 2 * E₁ + 1 ≤ E₁ := (Real.sqrt_le_sqrt_iff hE₁).mp hcontr
    linarith
  -- `h4` at the full horizon
  intro τ hτ
  exact ⟨hP τ hτ, h4 hsmall T' hT' hT'le g hsol hreg hP τ hτ⟩

/-! ## The requested statement

Left unproved: `aprioriP_of_halvesB_strict` above shows that it follows from the target's
hypotheses once the continuity input `hcont` and the strict datum inequality `hstrict` are added;
neither is available here (see the header of this file).  Nothing else is missing. -/

theorem aprioriP_of_halvesB_proof {α ε T C₀ E₁ : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g₀ : Work.FTS.Galerkin.Fn} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : 0 < α)
    (hα1 : α ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) (hE₁ : 0 ≤ E₁)
    (h6 : Work.FTS.StrongEps.EpsE4Thr.E4R4.AprioriPSixthB α ρ ε T Φs E g₀ C₀ E₁)
    (h4 : Work.FTS.StrongEps.EpsE4Thr.E4R4.AprioriPFourthB α ρ ε T Φs E g₀ C₀ (Real.sqrt (2 * E₁ + 1))) :
    Work.FTS.StrongEps.EpsE4Thr.AprioriP α ρ ε T Φs E g₀ C₀ (Real.sqrt (2 * E₁ + 1)) := by sorry

end Work.FTS.StrongEps.E4R3.Apriori4Proofs
