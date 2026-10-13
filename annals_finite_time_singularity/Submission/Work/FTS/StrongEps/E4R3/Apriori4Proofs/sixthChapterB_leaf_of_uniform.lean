import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Defs
import Submission.Work.FTS.StrongEps.E4R3.Sixth4

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Apriori4Proofs/sixthChapterB_leaf_of_uniform.lean` — H6 with the uniform `ℋ⁶` bound as a
hypothesis

**Verdict: the assigned statement is MIS-STATED (the missing hypothesis it carries is not the one
that the leaf actually lacks); it is not provable from its hypotheses.**  This file therefore
carries (a) the verbatim assigned statement, left as `sorry` and documented below, and (b) the
*sharpest repair* `sixthChapterB_of_uniformBound` (proved, `sorry`-free) together with the
Cauchy–Schwarz constant `exists_IP6o_cs_uniform` it uses.  The full analysis is in
`NOTES_sixthChapterB_leaf_of_uniform.md`.

## What the statement asks

`SixthChapterB Ce Cs C₀ ρ` demands, for every admissible datum `E4Data α' C₀ K Ce Cs ρ Φs E g₀`
(`α' ∈ (0,1]`, `K` the datum's `ℋ⁶`-size, `Ce/Cs` the two operator packages, plus `StarPkg6`) and
every horizon `T > 0`, a **single** constant `E₁ ≥ K²` and a threshold `ε₆ ∈ (0,1]` such that for
**every** `ε ∈ (0,ε₆]` and **every** regular `ε`-solution `g` whose projected mollified slices stay
in the `C₀α'²`-ball,

```
∀ τ ∈ Icc 0 T, rawE6 α' g τ ≤ E₁,      rawE6 α g τ = IP6o α (slice g τ) (slice g τ).
```

So `E₁` must be uniform in `ε` **and uniform over the whole solution family**.

The added hypothesis `hb` is the uniform-in-`τ` *value* bound of the raw slices,
`∃ B, ∀ τ ∈ Icc 0 T, Xn6 α (slice g τ) ≤ B` — literally the `hbdd6` of the S4 leaf
(`E4R3/Apriori4Leaves/RawE6Deriv.lean`, risk R2) and the `hb6` that repairs L-A
(`Apriori4Proofs/rawE6_ineq_proof.lean`, `rawE6_ineq_uniform_of_leaves`).  It is therefore the
hypothesis the *leaf-level* design prescribed.

## Why it does not suffice

**(1) `hb` is a per-`(ε, solution)` bound.**  Its witness `B` may depend on `ε`, on the horizon, on
the datum and on the solution `g` itself.  The conclusion needs one `E₁` for all `ε ∈ (0,ε₆]` and
all solutions.  The only available conversion of a *value* bound into a *pairing* bound is
Cauchy–Schwarz for `IP6o` (`exists_IP6o_cs_uniform` below, from the proved
`StrongPersist.IP6_cs_coeffs`),

```
rawE6 α g τ ≤ CC · Xn6 α (slice g τ)² ≤ CC · B²,
```

which keeps the dependence on `B = B(ε,g)`.  So the statement is *equivalent to* the assertion
that the family `{Xn6 α (slice g τ)}` is bounded uniformly in `ε` and in the solution — which is
exactly the chapter's mathematical content, not a consequence of the hypothesis as written.

**(2) The design's route to that content is broken at S4.**  The ε-uniformity of the intended
estimate comes from L-A — `rawE6_ineq_uniform_of_leaves` (proved), which uses `hb6` (which we have)
and produces **ε-uniform** `Λ, C₁` with

```
2 · IP6o α (epsRHSP … τ) (slice g τ) ≤ Λ (1 + rawE6 α g τ) + ε C₁ (1 + rawE6 α g τ)²
```

— followed by L-C (`gronwall_absorb`, proved).  Between them sits the level-six **energy identity
S4**,

```
ContinuousOn (rawE6 α g) (Icc 0 T) ∧
  ∀ τ ∈ Ioo 0 T, HasDerivAt (rawE6 α g) (2 · IP6o α (epsRHSP … τ) (slice g τ)) τ,
```

which is precisely what licenses the Grönwall comparison.  S4 is **not a consequence of
`IsEpsSolP + EpsRegP + hb`**, and the tree's own verdict (`rawE6_deriv` returned FALSE; see
`Apriori4Proofs/rawE6_deriv_proof.lean`, `rawE6_deriv_local_proof.lean`) records why:

* `EpsRegP` supplies *joint `C¹`* of `g` on the open quadrant and per-slice `SmoothOpen`; `C¹` does
  not give `∂_τ∂_θ = ∂_θ∂_τ`, so the a.e. **slot chain rule**
  `∂_τ (D_z^b D_θ^a (slice g ·))(p) = (D_z^b D_θ^a (epsRHSP … τ))(p)` (for slot words of length
  `≤ 6`) is not available.  The tree's producers of it (`EpsE4Thr.mixed_slice_deriv,
  mixed_slice_deriv_at`) take — as an explicit hypothesis — the *slot-level fake-time continuity of
  the scheme's right-hand side*, `∀ z θ ∈ Q0, ContinuousOn (fun s => mixed j i (epsRHSP … s) z θ)`;
  this is interface item (IV) (`hcontUAll`) of `EpsE4Thr.DiagCurveI_data_of_solution`, listed there
  as producible nowhere in the tree (`EpsLocalPStar.EpsRHSPLipX` gives only *weighted-`L²`*
  continuity in the fake time, not pointwise slot continuity; `hmeas` for the higher slots is
  similarly only obtainable from the slot continuity).  A machine-checked analysis of the
  consequences is in the S4 notes (groups (M1)–(M4)); the same conclusion was reached
  independently for the level-four siblings D1 (`energyDeriv_JfamP_ball`) and D2
  (`energyCont_JfamP_ball`), for F6 (`rawSlice_L12_zero`) and for L-B (`aprioriP_of_halvesB`).
* the **domination** for the differentiation (uniform bound of the level-six slots of the derivative
  family) is likewise not what a bound on the *slices* gives: by AM–GM the majorant splits into
  `HkIntegrand α 6 (slice g σ)` (bounded by `hb`) plus the same quantity for `epsRHSP … σ`, whose
  fake-time behaviour is the missing item above.
* equivalently: `hb` is exactly S4's `hbdd6`, and S4's prover established that `hbdd6` is *not* the
  missing hypothesis — so a leaf whose only added hypothesis is `hbdd6` inherits the same gap.

**(3) The alternative (norm propagation) route cannot be ε-uniform.**  The Volterra identity
`slice g τ − slice g 0 = ∫₀^τ epsRHSP α ρ ε Φs E g s ds` together with the `ℋ⁶`-valued Minkowski
inequality gives `N(τ) ≤ N(0) + ∫₀^τ ‖epsRHSP … s‖₆ ds`, and the semi-tame bound
(`epsWP_semitame`, `Apriori4Leaves/EpsWPSemitame.lean`) combined with the mollifier *gain*
`‖J_ε u‖₇ ≤ (Cg/ε)‖u‖₆` produces a **linear coefficient `Ct·Cg/ε`**.  The resulting Riccati
comparison blows up at a time `≍ ε/C'` and is genuinely `ε`-dependent, so it cannot produce a
threshold `ε₆` and a constant `E₁` valid for all `ε ≤ ε₆`.  (This is the analysis of
`NOTES_sixthChapterB_leaf_proof.md` §3b.)  The `ε`-uniform content of the chapter rests on the
*energy* formulation, i.e. on S4.

## The repair

The exact missing hypothesis, in the strongest usable form, is the ε- **and solution-uniform**
`ℋ⁶` bound: **one** `B` with `Xn6 α (slice g τ) ≤ B` for all admissible `(α, ε, T, Φs, E, g₀, g)`
and all `τ ∈ [0,T]`.  From it the conclusion is immediate by `exists_IP6o_cs_uniform` (proved
below): `E₁ := max (K²) (CC·B²)`, `ε₆ := 1`.  That is
`sixthChapterB_of_uniformBound` below, `sorry`-free.  (Equivalently one may carry the level-six
energy identity S4 — or, better, the pointwise slot continuity of `epsRHSP`, interface item (IV) —
and then the route L-A + L-C closes as prescribed by the two reviewers of this path; compare the
repaired siblings `rawE6_ineq_uniform_of_leaves`, `rawE6_deriv_of_diagData`,
`aprioriP_of_halvesB_strict`.)
-/

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs

open Work.FTS.Galerkin (Fn Fam slice)

/-! ## The assigned statement (verbatim, mis-stated: see the header) -/

theorem sixthChapterB_leaf_of_uniform {Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hρs : ∀ p : ℝ × ℝ, ρ (-p) = ρ p)
    (hb : ∀ {α ε T : ℝ} {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
      {g₀ : Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}, 0 < α → α ≤ 1 → 0 < ε → ε ≤ 1 → 0 < T →
      Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g → Work.FTS.StrongEps.EpsRegP α ρ ε T g →
      ∃ B : ℝ, ∀ τ ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α (Work.FTS.Galerkin.slice g τ) ≤ B) :
    ∃ C : ℝ, ∀ C₀ : ℝ, C ≤ C₀ → Work.FTS.StrongEps.EpsE4Thr.E4R4.SixthChapterB Ce Cs C₀ ρ := by sorry

/-! ## The Cauchy–Schwarz constant of the level-six pairing

`IP6o` is the concrete level-six pairing `IP6 1 … 1`; the proved `StrongPersist.IP6_cs_coeffs`
gives its Cauchy–Schwarz bound on the honest `ℋ⁶`-class (`HQo α 6`), with a single `α`-free
constant.  This is what converts the *value* bound `Xn6 α (slice g τ) ≤ B` into the raw-energy
bound `rawE6 α g τ ≤ CC·B²`. -/

/-- Cauchy–Schwarz for the concrete level-six pairing `IP6o` on the honest `ℋ⁶`-class. -/
theorem exists_IP6o_cs_uniform :
    ∃ CC : ℝ, 0 < CC ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ f g : Fn,
      Work.FTS.VocabO.HQo α 6 f → Work.FTS.VocabO.HQo α 6 g →
      |Work.FTS.StrongEps.EpsE4Thr.E4R4.IP6o α f g|
        ≤ CC * Work.FTS.StrongGlobal.Xn6 α f * Work.FTS.StrongGlobal.Xn6 α g := by
  obtain ⟨CC, hCC, h⟩ :=
    Work.FTS.StrongPersist.IP6_cs_coeffs 1 1 1 1 1 1 1 1 1 1 (1 : ℝ) one_pos
  exact ⟨CC, hCC, fun α hα f g hf hg => h α hα f g hf hg⟩

/-! ## The sharpest repair: one `ℋ⁶` bound for the whole family

The hypothesis below is the assigned `hb` with its existential *outside* the `∀`-block: a single
`B` valid for every admissible datum, every `ε ∈ (0,1]` and every solution.  This is exactly the
information that the conclusion needs and that `hb` does not supply; with it the conclusion follows
immediately, with `E₁ = max (K²) (CC·B²)` and `ε₆ = 1`. -/

/-- **The repair.**  If the level-six size of the raw slices is bounded by one number `B` uniformly
over all admissible data and all regular solutions, then `SixthChapterB` holds: `rawE6 α' g τ =
IP6o α' (slice g τ) (slice g τ) ≤ CC·(Xn6 α' (slice g τ))² ≤ CC·B²`. -/
theorem sixthChapterB_of_uniformBound {Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ}
    (hb : ∃ B : ℝ, ∀ {α ε T : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn} {g : Fam},
      0 < α → α ≤ 1 → 0 < ε → ε ≤ 1 → 0 < T →
      Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g → Work.FTS.StrongEps.EpsRegP α ρ ε T g →
      ∀ τ ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α (slice g τ) ≤ B) :
    ∃ C : ℝ, ∀ C₀ : ℝ, C ≤ C₀ →
      Work.FTS.StrongEps.EpsE4Thr.E4R4.SixthChapterB Ce Cs C₀ ρ := by
  obtain ⟨CC, hCCpos, hCS⟩ := exists_IP6o_cs_uniform
  obtain ⟨B, hB⟩ := hb
  refine ⟨0, fun C₀ _ => ?_⟩
  -- the chapter's datum threshold: `α := 1` (nothing in the conclusion needs a small `α` here)
  refine ⟨1, one_pos, le_rfl, ?_⟩
  intro α' hα' K Φs E g₀ hdat hstar6 T hT
  obtain ⟨hK0, -, -, -, -, -, -, -⟩ := hdat
  refine ⟨max (K ^ 2) (CC * B ^ 2), le_trans (sq_nonneg K) (le_max_left _ _),
    le_max_left _ _, 1, one_pos, le_rfl, ?_⟩
  intro ε hε T' hT' hle g hsol hreg hball τ hτ
  -- the uniform size bound of the slice, from the hypothesis
  have hbd : Work.FTS.StrongGlobal.Xn6 α' (slice g τ) ≤ B :=
    hB hα'.1 hα'.2 hε.1 hε.2 hT' hsol hreg τ hτ
  -- the slice is honest in `ℋ⁶` (per-slice datum of `EpsRegP`)
  have hd := hreg.2 τ hτ
  have hQo : Work.FTS.VocabO.HQo α' 6 (slice g τ) := ⟨hd.1, hd.2.1⟩
  have hcs := hCS α' hα' (slice g τ) (slice g τ) hQo hQo
  have hnn : 0 ≤ Work.FTS.StrongGlobal.Xn6 α' (slice g τ) :=
    Work.Spaces.HkNorm_nonneg α' 6 (slice g τ)
  have hBnn : 0 ≤ B := le_trans hnn hbd
  have hsq : Work.FTS.StrongGlobal.Xn6 α' (slice g τ) * Work.FTS.StrongGlobal.Xn6 α' (slice g τ)
      ≤ B * B := mul_le_mul hbd hbd hnn hBnn
  have hraw : Work.FTS.StrongEps.EpsE4Thr.E4R4.rawE6 α' g τ
      = Work.FTS.StrongEps.EpsE4Thr.E4R4.IP6o α' (slice g τ) (slice g τ) := rfl
  rw [hraw]
  refine le_trans (le_trans (le_abs_self _) hcs) ?_
  calc CC * Work.FTS.StrongGlobal.Xn6 α' (slice g τ) * Work.FTS.StrongGlobal.Xn6 α' (slice g τ)
      = CC * (Work.FTS.StrongGlobal.Xn6 α' (slice g τ)
          * Work.FTS.StrongGlobal.Xn6 α' (slice g τ)) := by ring
    _ ≤ CC * (B * B) := mul_le_mul_of_nonneg_left hsq hCCpos.le
    _ = CC * B ^ 2 := by ring
    _ ≤ max (K ^ 2) (CC * B ^ 2) := le_max_right _ _

end Work.FTS.StrongEps.E4R3.Apriori4Proofs
