import Mathlib
import Submission.OneManifold
import Submission.Commons.Analysis.Calculus.strictMonoOn_surj_Ioo_tendsto_right
import Submission.Commons.Analysis.Calculus.strictMonoOn_surj_Ioo_tendsto_top
import Submission.Commons.Topology.Homeomorph.open_interval_affine
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# S154–S155 — the ordered two-chart gluing core (the engine's atomic
step): facing end-overlap charts of a Hausdorff-type space glue to an
open interval

`OneManifold.lean` (S153) fixed the generic engine vocabulary; this
module is the gluing core ROADMAP S154/S155: two open-interval charts
whose overlap is the RIGHT end of one chart and the LEFT end of the
other (the *facing* configuration; only orientation-preserving
transitions are Hausdorff-compatible — ROADMAP S154) glue to an open
interval.  Charts are normalised to `(0,1)` (`OpenRealInterval 0 1`);
general chart intervals are reached by pre-normalising with the affine
homeo `Commons.Topology.Homeomorph.open_interval_affine` (L30).

1. **the transition coordinate** `T hu1 φ ψ hUend hv` — the U-chart
   coordinate of the overlap point `ψ v` (`v ∈ (0,u)`); with
   `T_mem` (values in `(s,1)`) and `T_range` (surjectivity onto
   `(s,1)`: the overlap `ψ((0,u)) = φ((s,1))` in coordinates);
2. **the real-function form** `Tfun` (0 off `(0,u)`; its `if`-condition
   is written `0 < v ∧ v < u` — the membership form does NOT match
   `dif_pos`), with `Tfun_eq`, `Tfun_range`, `Tfun_strictMonoOn`;
3. **the endpoint-limit** `T_endpoint_right` (S154 (P1)): under the
   orientation-preserving hypothesis `hinc`, `T v → 1` as `v → u⁻`
   (invoking the fleet fact
   `Commons.Analysis.Calculus.strictMonoOn_surj_Ioo_tendsto_right`,
   L31), plus the upper bound `T_lt_one`;
4. **the seam function** `Gfun` (S155): `Gfun v = T v` on `(0,u)`,
   `v + 1 − u` elsewhere — the V-side coordinate formula — with
   `G_at_u` (`G u = 1`) and **`G_continuousAt`** (continuous at `u`):
   left side controlled by `T_endpoint_right` + `T_lt_one`, right side
   affine.

S156/S157: the global map **`twoChartF hu1 φ ψ hUend hUV : X →
OpenRealInterval 0 (2 − u)`** (U-coordinate on `U`, ψ⁻¹-coordinate +
`1 − u` on `V∖U`) with value lemmas and **bijectivity**
(`twoChartF_surjective`/`injective`/`bijective`), and its **continuity**:
`Tfun_continuousOn (0,u)` (a), `Gfun_continuousOn` on `(0,u)`, `(u,1)`
and `(0,1)` (b), `twoChartF_comp_ψ_val` (`F(ψ t) = Gfun t`),
`twoChartF_continuousOn_U`/`_V`, the open-cover glue
`continuous_of_continuousOn_open_cover`, and **`twoChartF_continuous`**
(c)/(d).  NEXT: the continuous inverse (S157 (f): the inverse **`twoChartG hs0 hu φ ψ : OpenRealInterval 0
(2 − u) → X`** (piecewise: `y < 1 ↦ φ⟨y⟩`, `y ≥ 1 ↦ ψ⟨y − 1 + u⟩`)
with value lemmas `twoChartG_apply_lt_one`/`twoChartG_apply_ge_one`,
continuity on the two open pieces
`twoChartG_continuousOn_left`/`twoChartG_continuousOn_right`, and the
**seam identity `φ_eq_ψ_Sfun`** (an overlap point with U-coordinate
`y ∈ (s,1)` is `ψ⟨Sfun y⟩`) and the real-parameter seam convergence
lemmas **`twoChartG_left_converge`** (any neighbourhood `N` of `ψ⟨u⟩`
contains `φ⟨y⟩ = ψ⟨Sfun y⟩` eventually as `y → 1⁻`, via the `ψ`-pullback
metric ball + `Sfun_endpoint_top` + `Sfun_lt_u`) and
**`twoChartG_right_converge`** (`twoChartG⟨y⟩ = ψ⟨y − 1 + u⟩ → ψ⟨u⟩` as
`y → 1⁺`).  S157 (f) step 3 (done): **`twoChartG_continuousAt_seam`**
(ε-ball proof at `⟨1, ·⟩`: `δ := min δₗ (min δᵣ (1 − s))`; values with
`val < 1` are `φ⟨val⟩ ∈ N` by the left convergence (with `val > s` from
`ε ≤ 1 − s`), `val = 1` is `ψ⟨u⟩ ∈ N` by `mem_of_mem_nhds`, `val > 1`
by the right convergence; subtype distances reduced via the helper
`dist_subtype_val` (subtype distance is induced — `change`-free after
`Metric.mem_ball` + this rfl lemma)) and **`twoChartG_continuous`**
(three-piece pointwise: `lt_trichotomy` on the value; the two open
pieces via `ContinuousOn.continuousAt` at the open preimages
`val⁻¹(Iio 1)`/`val⁻¹(Ioi 1)`; the middle by
`twoChartG_continuousAt_seam`).  STEP 4 (done): the inverse identities
**`twoChartG_comp_twoChartF`** / **`twoChartF_comp_twoChartG`** and the
**two-chart gluing theorem `two_chart_glue_homeo`**: facing end-overlap
charts (open `U V`, `0 < s < 1`, `0 < u < 1`, overlap `(s,1)`/`(0,u)`
in coordinates, `hinc` orientation-preserving, `U ∪ V = univ`) glue to
`Nonempty (X ≃ₜ OpenRealInterval 0 (2 - u))` — `Homeomorph.mk` of the
`Equiv` of `twoChartF`/`twoChartG` with the two continuities.
(ROADMAP S154 (P2)/(P3) finish: the engine's atomic gluing step is
fully verified.)  S158: **`range_chain_union_interval`** (the
coordinate model: finite chains of overlapping real intervals have
interval unions), **`unionSubtypeHomeo`** (the generalized subset
reassociation), and **`single_junction_extension`** — the
chain-induction step: open `U V` of an ambient space with facing
terminal-overlap charts `η ψ` glue to
`Nonempty ({z : Y // z ∈ U ∪ V} ≃ₜ OpenRealInterval 0 (2 - u))`, via
`two_chart_glue_homeo` on the union-subtype with transported overlap
equivalences `hVend'`/`hUend'` and the (computational) `Tfun`
invariance under reassociation (`dsimp [T, η', ψ', reassocU, reassocV,
unionSubtypeHomeo]`).  S159: **`prefix_two_charts_interval`** — the
base+first-step of the chain induction: two open traces `T₀ T₁` with
facing terminal-overlap interval charts glue to
`Nonempty ({z : Y // z ∈ T₀ ∪ T₁} ≃ₜ OpenRealInterval 0 1)`
(`single_junction_extension` + the affine `norm01` back to `(0,1)`),
and the abstract **`chain_step`** — `T : ℕ → Set Y`, prefix-up-to-`k`
interval chart `κk`, new trace `T (k+1)` attaching along a facing
terminal overlap (`hVend`/`hUend`/`hinc` stated against `κk`):
`Nonempty (ORI 0 1 ≃ₜ {z : Y // z ∈ ⋃ j ∈ range (k+2), T j})` —
via `single_junction_extension` + `norm01` + the set-equality
reassociation `setEqSubtypeHomeo` and the union split
`union_range_succ`.  Everything here is verified (no axioms, no
`sorry`).

S160: the **finite-chain prefix interval theorem** — the induction
harness over the chain: `prefix_open` (each prefix union
`⋃ j ∈ range (k+1), T j` is open — finite union of open traces),
`prefix_zero_interval` (base: single trace `T 0` is the `(0+1)`-prefix),
`chain_step_open` (the abstract `chain_step` with `hUopen` derived from
per-trace openness), and **`finite_prefix_interval`** — given interval
charts `η j` of every trace and, at every level `k`, the facing
terminal-overlap data (`hdata`) stated against the current prefix
homeo `κk` (the overlap of `T (k+1)` with the prefix is the right end
`(s,1)` of `κk` and the left end `(0,u)` of `ηnew`, with the
`hinc` monotone transition), every prefix union
`⋃ j ∈ range (k+1), T j` is an open real interval chart
(`Nonempty (ORI 0 1 ≃ₜ {z : Y // z ∈ ⋃ j ∈ range (k+1), T j})`), by
transfinite-style induction: zero via `prefix_zero_interval`, succ via
`chain_step_open`.  This is the *chain-induction harness* of the
S147-T sweep: it reduces the sweep to (a) supplying the per-trace
interval charts `η`, and (b) proving `hdata` — the automatic
re-supply of facing terminal-overlap data as the prefix homeo
changes.  Where (b) wraps (the union covers the whole component / the
chain closes on itself), the interval model is replaced by the
compact circle side of the dichotomy (ROADMAP S152 analysis).

S161: the **interval-side growth atom and the wrap contradiction** —
`prefix_proper_growth` (if the new trace is an interval chart whose
overlap with the `k`-prefix is the left terminal interval `(0,u)`, `u < 1`,
then the new trace contains a point outside the prefix: every
facing-terminal chain step strictly grows the prefix union) and
`chain_data_fails_at_full_prefix` (the facing-terminal data with `u < 1`
cannot be supplied at a level whose prefix already equals the whole space
— the precise sense in which a compact/circle component is NOT chainable:
at the absorbing level the new trace must attach at both ends / wrap).
These are the two dichotomy markers the S147-T sweep reduces to on the
interval side: an infinite facing-terminal chain is the certificate of the
non-compact (interval) side, and its failure at full prefix is the wrap.
-/

open LeanEval.KnotTheory.Quadrisecant
open Set
open scoped Real Topology

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

variable {X : Type*} [TopologicalSpace X]

/-- `v ∈ (0,u)` embedded into `(0,1)` (needs `u ≤ 1`). -/
theorem emb01 {u : ℝ} (hu1 : u ≤ 1) {v : ℝ} (hv : v ∈ Set.Ioo (0 : ℝ) u) : v ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨hv.1, lt_of_lt_of_le hv.2 hu1⟩

/-- The U-chart coordinate of the point `ψ v` (transition; `v ∈ (0,u)`). -/
noncomputable def T {U V : Set X} {u : ℝ} (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    {v : ℝ} (hv : v ∈ Set.Ioo 0 u) : ℝ :=
  ((φ.symm ⟨(ψ ⟨v, emb01 hu1 hv⟩ : X), (hUend ⟨v, emb01 hu1 hv⟩).mpr hv⟩ : OpenRealInterval 0 1) : ℝ)

/-- `T` is monotone-or-antitone free; `T v ∈ (s,1)` and `T` ranges over all of `(s,1)`. -/
lemma T_mem {U V : Set X} {s u : ℝ} (hs : 0 < s) (hu : 0 < u) (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    {v : ℝ} (hv : v ∈ Set.Ioo 0 u) :
    T hu1 φ ψ hUend hv ∈ Set.Ioo s 1 := by
  dsimp [T]
  have hpV : ((ψ ⟨v, emb01 hu1 hv⟩) : X) ∈ V :=
    (ψ ⟨v, emb01 hu1 hv⟩ : {x : X // x ∈ V}).2
  have hpU : ((ψ ⟨v, emb01 hu1 hv⟩) : X) ∈ U :=
    (hUend ⟨v, emb01 hu1 hv⟩).mpr hv
  have hφφ : (φ (φ.symm ⟨(ψ ⟨v, emb01 hu1 hv⟩ : X), hpU⟩) : X) = (ψ ⟨v, emb01 hu1 hv⟩ : X) := by
    exact congrArg (fun z : {x : X // x ∈ U} => (z : X))
      (φ.apply_symm_apply ⟨(ψ ⟨v, emb01 hu1 hv⟩ : X), hpU⟩)
  exact (hVend (φ.symm ⟨(ψ ⟨v, emb01 hu1 hv⟩ : X), hpU⟩)).1 (by simpa [hφφ] using hpV)

/-- Surjectivity of the transition coordinate: every `y ∈ (s,1)` is the
U-coordinate of the overlap point `ψ v` for some `v ∈ (0,u)`; conversely
every such value lies in `(s,1)` (`T_mem`). -/
lemma T_range {U V : Set X} {s u : ℝ} (hs : 0 < s) (hu : 0 < u) (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u) :
    ∀ y : ℝ, y ∈ Set.Ioo s 1 ↔ ∃ v : ℝ, ∃ hv : v ∈ Set.Ioo 0 u, T hu1 φ ψ hUend hv = y := by
  intro y
  constructor
  · intro hy
    have hy01 : y ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_trans hs hy.1, hy.2⟩
    let p : X := (φ ⟨y, hy01⟩ : X)
    have hpU : p ∈ U := (φ ⟨y, hy01⟩ : {x : X // x ∈ U}).2
    have hpV : p ∈ V := (hVend ⟨y, hy01⟩).2 hy
    let w : OpenRealInterval 0 1 := ψ.symm ⟨p, hpV⟩
    have hwU : (w : ℝ) ∈ Set.Ioo (0 : ℝ) u := by
      have hψwU : ((ψ w : X) ∈ U) := by
        have heq : (ψ w : X) = p := by
          exact congrArg (fun z : {x : X // x ∈ V} => (z : X)) (ψ.apply_symm_apply ⟨p, hpV⟩)
        simpa [heq] using hpU
      exact (hUend w).1 hψwU
    refine ⟨(w : ℝ), hwU, ?_⟩
    dsimp [T]
    have hwψ : (⟨(w : ℝ), emb01 hu1 hwU⟩ : OpenRealInterval 0 1) = w := by
      apply Subtype.ext
      rfl
    have hp' : ((ψ ⟨(w : ℝ), emb01 hu1 hwU⟩ : X) ∈ U) := by
      simpa [hwψ] using (hUend w).mpr hwU
    have hψp : (ψ ⟨(w : ℝ), emb01 hu1 hwU⟩ : X) = p := by
      rw [hwψ]
      exact congrArg (fun z : {x : X // x ∈ V} => (z : X)) (ψ.apply_symm_apply ⟨p, hpV⟩)
    have harg : (⟨(ψ ⟨(w : ℝ), emb01 hu1 hwU⟩ : X), hp'⟩ : {x : X // x ∈ U}) = φ ⟨y, hy01⟩ := by
      apply Subtype.ext
      exact hψp
    calc
      ((φ.symm ⟨(ψ ⟨(w : ℝ), emb01 hu1 hwU⟩ : X), hp'⟩ : OpenRealInterval 0 1) : ℝ)
          = ((φ.symm (φ ⟨y, hy01⟩) : OpenRealInterval 0 1) : ℝ) := by
            exact congrArg (fun z : {x : X // x ∈ U} => ((φ.symm z : OpenRealInterval 0 1) : ℝ)) harg
      _ = ((⟨y, hy01⟩ : OpenRealInterval 0 1) : ℝ) := by
            rw [φ.symm_apply_apply]
  · intro hv_exists
    rcases hv_exists with ⟨v, hv, hvy⟩
    rw [← hvy]
    exact T_mem hs hu hu1 φ ψ hVend hUend hv

/-! ## Endpoint-limit of the transition (S154 (P1), via L31) -/

/-- The transition as a total real function (0 off its domain). -/
noncomputable def Tfun {U V : Set X} {u : ℝ} (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (v : ℝ) : ℝ :=
  if hv : 0 < v ∧ v < u then T hu1 φ ψ hUend ⟨hv.1, hv.2⟩ else 0

/-- `Tfun` agrees with `T` on the domain. -/
lemma Tfun_eq {U V : Set X} {u : ℝ} (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    {v : ℝ} (hv : v ∈ Set.Ioo 0 u) :
    Tfun hu1 φ ψ hUend v = T hu1 φ ψ hUend hv := by
  change (if hv : 0 < v ∧ v < u then T hu1 φ ψ hUend ⟨hv.1, hv.2⟩ else 0) = T hu1 φ ψ hUend hv
  rw [dif_pos ⟨hv.1, hv.2⟩]

/-- `Tfun '' (0,u) = (s,1)`: the real-function form of `T_range`. -/
lemma Tfun_range {U V : Set X} {s u : ℝ} (hs : 0 < s) (hu : 0 < u) (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u) :
    Tfun hu1 φ ψ hUend '' Set.Ioo 0 u = Set.Ioo s 1 := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨v, hv, hvy⟩
    have hTeq : T hu1 φ ψ hUend hv = y := by
      rw [← Tfun_eq hu1 φ ψ hUend hv]
      exact hvy
    exact (T_range hs hu hu1 φ ψ hVend hUend y).2 ⟨v, hv, hTeq⟩
  · intro hy
    rcases (T_range hs hu hu1 φ ψ hVend hUend y).1 hy with ⟨v, hv, hTeq⟩
    refine ⟨v, hv, ?_⟩
    rw [Tfun_eq hu1 φ ψ hUend hv]
    exact hTeq

/-- Strict monotonicity of the real transition function from the
`hinc` (orientation-preserving) hypothesis. -/
lemma Tfun_strictMonoOn {U V : Set X} {u : ℝ} (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hinc : ∀ ⦃v₁ v₂ : ℝ⦄, v₁ ∈ Set.Ioo 0 u → v₂ ∈ Set.Ioo 0 u → v₁ < v₂ →
        Tfun hu1 φ ψ hUend v₁ < Tfun hu1 φ ψ hUend v₂) :
    StrictMonoOn (Tfun hu1 φ ψ hUend) (Set.Ioo 0 u) := by
  intro v₁ hv₁ v₂ hv₂ hvlt
  exact hinc hv₁ hv₂ hvlt

/-- **Endpoint-limit of the transition (S154 (P1))**: under the
orientation-preserving hypothesis, the U-coordinate `T v` of the overlap
point `ψ v` approaches `1` as `v` approaches `u` from below.  (Invokes the
fleet fact `Commons.Analysis.Calculus.strictMonoOn_surj_Ioo_tendsto_right`
on the total function `Tfun`.) -/
lemma T_endpoint_right {U V : Set X} {s u : ℝ} (hs : 0 < s) (hu : 0 < u) (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hinc : ∀ ⦃v₁ v₂ : ℝ⦄, v₁ ∈ Set.Ioo 0 u → v₂ ∈ Set.Ioo 0 u → v₁ < v₂ →
        Tfun hu1 φ ψ hUend v₁ < Tfun hu1 φ ψ hUend v₂) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ v : ℝ, ∀ hv : v ∈ Set.Ioo 0 u, u - δ < v → 1 - ε < T hu1 φ ψ hUend hv := by
  intro ε hε
  rcases Commons.Analysis.Calculus.strictMonoOn_surj_Ioo_tendsto_right hu
      (Tfun_strictMonoOn hu1 φ ψ hUend hinc)
      (Tfun_range hs hu hu1 φ ψ hVend hUend) ε hε with ⟨δ, hδpos, hδ⟩
  refine ⟨δ, hδpos, ?_⟩
  intro v hv huδ
  have hvT : 1 - ε < Tfun hu1 φ ψ hUend v := hδ v hv huδ
  rw [← Tfun_eq hu1 φ ψ hUend hv]
  exact hvT

/-- Upper bound: `T v < 1` on the domain (values live in `(s,1)`). -/
lemma T_lt_one {U V : Set X} {s u : ℝ} (hs : 0 < s) (hu : 0 < u) (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    {v : ℝ} (hv : v ∈ Set.Ioo 0 u) :
    T hu1 φ ψ hUend hv < 1 := by
  exact (T_mem hs hu hu1 φ ψ hVend hUend hv).2

/-! ## The seam function `Gfun` and its continuity at `u` (S155) -/

/-- **The seam real function**: on the overlap coordinates `(0,u)` it is
the transition `T`; on the rest it is the affine `v + 1 − u` (the V-tail
formula).  At `v = u` the two formulas both give `1`. -/
noncomputable def Gfun {U V : Set X} {u : ℝ} (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (v : ℝ) : ℝ :=
  if hv : 0 < v ∧ v < u then T hu1 φ ψ hUend ⟨hv.1, hv.2⟩ else v + 1 - u

/-- The seam value: `G u = 1` (the affine branch at `v = u`). -/
lemma G_at_u {U V : Set X} {u : ℝ} (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u) :
    Gfun hu1 φ ψ hUend u = 1 := by
  dsimp [Gfun]
  have hnot : ¬ (0 < u ∧ u < u) := by intro h; linarith
  rw [dif_neg hnot]
  ring

/-- **Seam continuity (S155)**: `Gfun` is continuous at `u` with value
`1`.  Left side: the transition `T v` tends to `1` as `v → u⁻`
(`T_endpoint_right`, the lower bound) and stays below `1`
(`T_lt_one`); right side: `v + 1 − u` is linear, equal to `1` at `u`;
the ε-δ glue at `u` combines the two. -/
lemma G_continuousAt {U V : Set X} {s u : ℝ} (hs : 0 < s) (hu : 0 < u) (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hinc : ∀ ⦃v₁ v₂ : ℝ⦄, v₁ ∈ Set.Ioo 0 u → v₂ ∈ Set.Ioo 0 u → v₁ < v₂ →
        Tfun hu1 φ ψ hUend v₁ < Tfun hu1 φ ψ hUend v₂) :
    ContinuousAt (Gfun hu1 φ ψ hUend) u := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  rcases T_endpoint_right hs hu hu1 φ ψ hVend hUend hinc ε hε with ⟨δ₁, hδ₁pos, hδ₁⟩
  let δ := min δ₁ (min ε u)
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact lt_min hδ₁pos (lt_min hε hu)
  have hδ₁le : δ ≤ δ₁ := by
    dsimp [δ]
    exact min_le_left δ₁ (min ε u)
  have hδu : δ ≤ u := by
    dsimp [δ]
    exact le_trans (min_le_right δ₁ (min ε u)) (min_le_right ε u)
  have hδε : δ ≤ ε := by
    dsimp [δ]
    exact le_trans (min_le_right δ₁ (min ε u)) (min_le_left ε u)
  refine ⟨δ, hδpos, ?_⟩
  intro y hy
  have hy' : |y - u| < δ := by
    simpa [Real.dist_eq] using hy
  have hyu' : -(δ) < y - u := (abs_lt.mp hy').1
  have hGu : Gfun hu1 φ ψ hUend u = 1 := G_at_u hu1 φ ψ hUend
  by_cases hyu : u ≤ y
  · -- y ≥ u: affine branch
    have hnot : ¬ (0 < y ∧ y < u) := by intro h; linarith
    have hG : Gfun hu1 φ ψ hUend y = y + 1 - u := by
      dsimp [Gfun]
      rw [dif_neg hnot]
    rw [hG, hGu]
    have habs : |(y + 1 - u) - 1| < ε := by
      have hcalc : (y + 1 - u) - 1 = y - u := by ring
      rw [hcalc]
      exact lt_of_lt_of_le hy' hδε
    rw [Real.dist_eq]
    exact habs
  · -- y < u: transition branch (y ∈ (0,u) since |y−u| < δ ≤ u)
    have hylt : y < u := lt_of_not_ge hyu
    have hy0 : 0 < y := by
      have : y - u > -δ := hyu'
      have : y > u - δ := by linarith
      linarith [hδu]
    have hG : Gfun hu1 φ ψ hUend y = T hu1 φ ψ hUend ⟨hy0, hylt⟩ := by
      dsimp [Gfun]
      rw [dif_pos ⟨hy0, hylt⟩]
    have huδy : u - δ₁ < y := by
      have h1 : -δ < y - u := (abs_lt.mp hy').1
      have h2 : -δ₁ ≤ -δ := by linarith
      linarith
    have hlow : 1 - ε < T hu1 φ ψ hUend ⟨hy0, hylt⟩ := hδ₁ y ⟨hy0, hylt⟩ huδy
    have hup : T hu1 φ ψ hUend ⟨hy0, hylt⟩ < 1 + ε := by
      have hlt1 : T hu1 φ ψ hUend ⟨hy0, hylt⟩ < 1 := T_lt_one hs hu hu1 φ ψ hVend hUend ⟨hy0, hylt⟩
      linarith
    rw [hG, hGu]
    have habs : |(T hu1 φ ψ hUend ⟨hy0, hylt⟩) - 1| < ε := by
      rw [abs_lt]
      constructor <;> linarith
    rw [Real.dist_eq]
    exact habs

/-! ## The global map `twoChartF` and its bijectivity (S156) -/

/-- Outside `U`, a point lies in `V` (the two charts cover `X`). -/
theorem memV_of_not_memU {U V : Set X} (hUV : U ∪ V = univ) {x : X} (hxU : x ∉ U) : x ∈ V := by
  have hx : x ∈ (U ∪ V : Set X) := by simpa [hUV]
  exact hx.elim (fun h => (hxU h).elim) id

/-- **The global coordinate map** `F : X → OpenRealInterval 0 (2 − u)`:
the U-chart coordinate on `U`; on `V ∖ U` the V-chart coordinate shifted
by `1 − u` (so the free V-tail `(u,1)` maps onto `(1, 2−u)` and the seam
point `ψ(u)` maps to `1`). -/
noncomputable def twoChartF {U V : Set X} {u : ℝ} (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hUV : U ∪ V = univ) (x : X) : OpenRealInterval 0 (2 - u) := by
  classical
  by_cases hxU : x ∈ U
  · let c : OpenRealInterval 0 1 := φ.symm ⟨x, hxU⟩
    exact ⟨(c : ℝ), by
      have h1le : 1 ≤ 2 - u := by linarith
      exact ⟨c.2.1, lt_of_lt_of_le c.2.2 h1le⟩⟩
  · let v : OpenRealInterval 0 1 := ψ.symm ⟨x, memV_of_not_memU hUV hxU⟩
    exact ⟨(v : ℝ) + 1 - u, by
      have hvnot : ¬ (v : ℝ) ∈ Set.Ioo 0 u := by
        intro hvu
        have hψx : (ψ v : X) = x := by
          dsimp [v]
          exact congrArg (fun z : {x : X // x ∈ V} => (z : X))
            (ψ.apply_symm_apply ⟨x, memV_of_not_memU hUV hxU⟩)
        have hxU' : x ∈ U := by
          simpa [hψx] using ((hUend v).mpr hvu)
        exact hxU hxU'
      have hvu : u ≤ (v : ℝ) := by
        by_contra hvul
        have hvltu : (v : ℝ) < u := lt_of_not_ge hvul
        exact hvnot ⟨v.2.1, hvltu⟩
      constructor
      · have hge1 : 1 ≤ (v : ℝ) + 1 - u := by linarith
        exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hge1
      · have hlt : (v : ℝ) + 1 - u < 2 - u := by linarith [v.2.2]
        exact hlt⟩

/-- Value on `U`: the U-chart coordinate. -/
lemma twoChartF_val_memU {U V : Set X} {u : ℝ} (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hUV : U ∪ V = univ) {x : X} (hxU : x ∈ U) :
    ((twoChartF hu1 φ ψ hUend hUV x : OpenRealInterval 0 (2 - u)) : ℝ) =
      ((φ.symm ⟨x, hxU⟩ : OpenRealInterval 0 1) : ℝ) := by
  dsimp [twoChartF]
  rw [dif_pos hxU]

/-- Value outside `U` (on the free V-tail): the V-chart coordinate shifted. -/
lemma twoChartF_val_not_memU {U V : Set X} {u : ℝ} (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hUV : U ∪ V = univ) {x : X} (hxU : x ∉ U) :
    ((twoChartF hu1 φ ψ hUend hUV x : OpenRealInterval 0 (2 - u)) : ℝ) =
      ((ψ.symm ⟨x, memV_of_not_memU hUV hxU⟩ : OpenRealInterval 0 1) : ℝ) + 1 - u := by
  dsimp [twoChartF]
  rw [dif_neg hxU]

/-- The V-coordinate of a point outside `U` is at least `u` (it lies on
the free V-tail, not in the overlap `(0,u)`). -/
lemma coord_ge_u_of_not_memU {U V : Set X} {u : ℝ} (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hUV : U ∪ V = univ) {x : X} (hxU : x ∉ U) :
    u ≤ ((ψ.symm ⟨x, memV_of_not_memU hUV hxU⟩ : OpenRealInterval 0 1) : ℝ) := by
  let v : OpenRealInterval 0 1 := ψ.symm ⟨x, memV_of_not_memU hUV hxU⟩
  have hvnot : ¬ (v : ℝ) ∈ Set.Ioo 0 u := by
    intro hvu
    have hψx : (ψ v : X) = x := by
      dsimp [v]
      exact congrArg (fun z : {x : X // x ∈ V} => (z : X))
        (ψ.apply_symm_apply ⟨x, memV_of_not_memU hUV hxU⟩)
    have hxU' : x ∈ U := by
      simpa [hψx] using ((hUend v).mpr hvu)
    exact hxU hxU'
  by_contra hvul
  have hvltu : (v : ℝ) < u := lt_of_not_ge hvul
  exact hvnot ⟨v.2.1, hvltu⟩

/-- **Surjectivity of the global map.**  `y < 1`: preimage `φ⟨y⟩ ∈ U`;
`y ≥ 1`: preimage `ψ⟨y − 1 + u⟩` on the free V-tail. -/
lemma twoChartF_surjective {U V : Set X} {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hUV : U ∪ V = univ) : Function.Surjective (twoChartF hu1 φ ψ hUend hUV) := by
  intro y
  by_cases hy1 : (y : ℝ) < 1
  · let x : X := (φ ⟨(y : ℝ), ⟨y.2.1, hy1⟩⟩ : X)
    refine ⟨x, ?_⟩
    have hxU : x ∈ U := (φ ⟨(y : ℝ), ⟨y.2.1, hy1⟩⟩ : {x : X // x ∈ U}).2
    apply Subtype.ext
    rw [twoChartF_val_memU hu1 φ ψ hUend hUV hxU]
    have hφinv : (φ.symm (φ ⟨(y : ℝ), ⟨y.2.1, hy1⟩⟩) : OpenRealInterval 0 1) =
        ⟨(y : ℝ), ⟨y.2.1, hy1⟩⟩ :=
      φ.symm_apply_apply ⟨(y : ℝ), ⟨y.2.1, hy1⟩⟩
    have harg : (⟨x, hxU⟩ : {x : X // x ∈ U}) = φ ⟨(y : ℝ), ⟨y.2.1, hy1⟩⟩ := by
      apply Subtype.ext
      dsimp [x]
    calc
      ((φ.symm ⟨x, hxU⟩ : OpenRealInterval 0 1) : ℝ)
          = ((φ.symm (φ ⟨(y : ℝ), ⟨y.2.1, hy1⟩⟩) : OpenRealInterval 0 1) : ℝ) := by
            exact congrArg (fun z : {x : X // x ∈ U} => ((φ.symm z : OpenRealInterval 0 1) : ℝ)) harg
      _ = ((⟨(y : ℝ), ⟨y.2.1, hy1⟩⟩ : OpenRealInterval 0 1) : ℝ) := by
            simpa using congrArg (fun t : OpenRealInterval 0 1 => (t : ℝ)) hφinv
      _ = (y : ℝ) := rfl
  · have hyge : 1 ≤ (y : ℝ) := le_of_not_gt hy1
    let w : ℝ := (y : ℝ) - 1 + u
    have hw0 : 0 < w := by dsimp [w]; linarith [hyge, hu]
    have hw1 : w < 1 := by dsimp [w]; linarith [y.2.2]
    have hwnot : ¬ w ∈ Set.Ioo 0 u := by
      intro hw
      have hwltu : w < u := hw.2
      dsimp [w] at hwltu
      linarith
    let x : X := (ψ ⟨w, ⟨hw0, hw1⟩⟩ : X)
    refine ⟨x, ?_⟩
    have hxnotU : x ∉ U := by
      intro hxU
      exact hwnot ((hUend ⟨w, ⟨hw0, hw1⟩⟩).1 hxU)
    apply Subtype.ext
    have hψinv : (ψ.symm (ψ ⟨w, ⟨hw0, hw1⟩⟩) : OpenRealInterval 0 1) = ⟨w, ⟨hw0, hw1⟩⟩ :=
      ψ.symm_apply_apply ⟨w, ⟨hw0, hw1⟩⟩
    have hval : ((ψ.symm ⟨x, memV_of_not_memU hUV hxnotU⟩ : OpenRealInterval 0 1) : ℝ) = w := by
      -- ψ.symm of ψ⟨w⟩ with a different membership: apply_symm_apply on the exact element
      have hx : x = (ψ ⟨w, ⟨hw0, hw1⟩⟩ : X) := rfl
      have harg : (⟨x, memV_of_not_memU hUV hxnotU⟩ : {x : X // x ∈ V}) =
          ψ ⟨w, ⟨hw0, hw1⟩⟩ := by
        apply Subtype.ext
        exact hx
      calc
        ((ψ.symm ⟨x, memV_of_not_memU hUV hxnotU⟩ : OpenRealInterval 0 1) : ℝ)
            = ((ψ.symm (ψ ⟨w, ⟨hw0, hw1⟩⟩) : OpenRealInterval 0 1) : ℝ) := by
              exact congrArg (fun z : {x : X // x ∈ V} => ((ψ.symm z : OpenRealInterval 0 1) : ℝ)) harg
        _ = w := by
              simpa using congrArg (fun t : OpenRealInterval 0 1 => (t : ℝ)) hψinv
    calc
      ((twoChartF hu1 φ ψ hUend hUV x : OpenRealInterval 0 (2 - u)) : ℝ) = w + 1 - u := by
        rw [twoChartF_val_not_memU hu1 φ ψ hUend hUV hxnotU]
        rw [hval]
      _ = (y : ℝ) := by dsimp [w]; ring

/-- **Injectivity of the global map**: the two image regions `(0,1)`
(U-part) and `[1, 2−u)` (V-tail) are disjoint, and within each region the
chart coordinate map is injective. -/
lemma twoChartF_injective {U V : Set X} {u : ℝ} (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hUV : U ∪ V = univ) : Function.Injective (twoChartF hu1 φ ψ hUend hUV) := by
  intro x₁ x₂ hEq
  by_cases h1 : x₁ ∈ U
  · by_cases h2 : x₂ ∈ U
    · have hc₁ : ((twoChartF hu1 φ ψ hUend hUV x₁ : OpenRealInterval 0 (2 - u)) : ℝ) =
          ((φ.symm ⟨x₁, h1⟩ : OpenRealInterval 0 1) : ℝ) :=
        twoChartF_val_memU hu1 φ ψ hUend hUV h1
      have hc₂ : ((twoChartF hu1 φ ψ hUend hUV x₂ : OpenRealInterval 0 (2 - u)) : ℝ) =
          ((φ.symm ⟨x₂, h2⟩ : OpenRealInterval 0 1) : ℝ) :=
        twoChartF_val_memU hu1 φ ψ hUend hUV h2
      have hcoord : (φ.symm ⟨x₁, h1⟩ : OpenRealInterval 0 1) = φ.symm ⟨x₂, h2⟩ := by
        apply Subtype.ext
        have hval : ((φ.symm ⟨x₁, h1⟩ : OpenRealInterval 0 1) : ℝ) =
            ((φ.symm ⟨x₂, h2⟩ : OpenRealInterval 0 1) : ℝ) := by
          simpa [hc₁, hc₂] using congrArg (fun z : OpenRealInterval 0 (2 - u) => (z : ℝ)) hEq
        exact hval
      exact congrArg (fun z : {x : X // x ∈ U} => (z : X)) ((φ.symm.injective) hcoord)
    · have hval₁lt : ((twoChartF hu1 φ ψ hUend hUV x₁ : OpenRealInterval 0 (2 - u)) : ℝ) < 1 := by
        rw [twoChartF_val_memU hu1 φ ψ hUend hUV h1]
        exact (φ.symm ⟨x₁, h1⟩ : OpenRealInterval 0 1).2.2
      have hval₂ge : 1 ≤ ((twoChartF hu1 φ ψ hUend hUV x₂ : OpenRealInterval 0 (2 - u)) : ℝ) := by
        rw [twoChartF_val_not_memU hu1 φ ψ hUend hUV h2]
        have hgeu := coord_ge_u_of_not_memU hu1 φ ψ hUend hUV h2
        linarith
      have heqv : ((twoChartF hu1 φ ψ hUend hUV x₁ : OpenRealInterval 0 (2 - u)) : ℝ) =
          ((twoChartF hu1 φ ψ hUend hUV x₂ : OpenRealInterval 0 (2 - u)) : ℝ) :=
        congrArg (fun z : OpenRealInterval 0 (2 - u) => (z : ℝ)) hEq
      linarith
  · by_cases h2 : x₂ ∈ U
    · have hval₁ge : 1 ≤ ((twoChartF hu1 φ ψ hUend hUV x₁ : OpenRealInterval 0 (2 - u)) : ℝ) := by
        rw [twoChartF_val_not_memU hu1 φ ψ hUend hUV h1]
        have hgeu := coord_ge_u_of_not_memU hu1 φ ψ hUend hUV h1
        linarith
      have hval₂lt : ((twoChartF hu1 φ ψ hUend hUV x₂ : OpenRealInterval 0 (2 - u)) : ℝ) < 1 := by
        rw [twoChartF_val_memU hu1 φ ψ hUend hUV h2]
        exact (φ.symm ⟨x₂, h2⟩ : OpenRealInterval 0 1).2.2
      have heqv : ((twoChartF hu1 φ ψ hUend hUV x₁ : OpenRealInterval 0 (2 - u)) : ℝ) =
          ((twoChartF hu1 φ ψ hUend hUV x₂ : OpenRealInterval 0 (2 - u)) : ℝ) :=
        congrArg (fun z : OpenRealInterval 0 (2 - u) => (z : ℝ)) hEq
      linarith
    · have hc₁ : ((twoChartF hu1 φ ψ hUend hUV x₁ : OpenRealInterval 0 (2 - u)) : ℝ) =
          ((ψ.symm ⟨x₁, memV_of_not_memU hUV h1⟩ : OpenRealInterval 0 1) : ℝ) + 1 - u :=
        twoChartF_val_not_memU hu1 φ ψ hUend hUV h1
      have hc₂ : ((twoChartF hu1 φ ψ hUend hUV x₂ : OpenRealInterval 0 (2 - u)) : ℝ) =
          ((ψ.symm ⟨x₂, memV_of_not_memU hUV h2⟩ : OpenRealInterval 0 1) : ℝ) + 1 - u :=
        twoChartF_val_not_memU hu1 φ ψ hUend hUV h2
      have hcoord : (ψ.symm ⟨x₁, memV_of_not_memU hUV h1⟩ : OpenRealInterval 0 1) =
          ψ.symm ⟨x₂, memV_of_not_memU hUV h2⟩ := by
        apply Subtype.ext
        have hval : ((ψ.symm ⟨x₁, memV_of_not_memU hUV h1⟩ : OpenRealInterval 0 1) : ℝ) =
            ((ψ.symm ⟨x₂, memV_of_not_memU hUV h2⟩ : OpenRealInterval 0 1) : ℝ) := by
          have hvv : ((twoChartF hu1 φ ψ hUend hUV x₁ : OpenRealInterval 0 (2 - u)) : ℝ) =
              ((twoChartF hu1 φ ψ hUend hUV x₂ : OpenRealInterval 0 (2 - u)) : ℝ) :=
            congrArg (fun z : OpenRealInterval 0 (2 - u) => (z : ℝ)) hEq
          linarith
        exact hval
      exact congrArg (fun z : {x : X // x ∈ V} => (z : X)) ((ψ.symm.injective) hcoord)

/-- **Bijectivity of the global map.** -/
lemma twoChartF_bijective {U V : Set X} {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hUV : U ∪ V = univ) : Function.Bijective (twoChartF hu1 φ ψ hUend hUV) := by
  exact ⟨twoChartF_injective hu1 φ ψ hUend hUV, twoChartF_surjective hu hu1 φ ψ hUend hUV⟩

/-! ## Continuity of the transition function on its domain (S157 (a)) -/

/-- `Tfun` is continuous on its domain `(0,u)`: there it is the
coordinate composition `val ∘ φ.symm ∘ ψ ∘ emb`, continuous by the
chart homeos. -/
lemma Tfun_continuousOn {U V : Set X} {u : ℝ} (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u) :
    ContinuousOn (Tfun hu1 φ ψ hUend) (Set.Ioo 0 u) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let g : {x : ℝ // x ∈ Set.Ioo 0 u} → ℝ := fun v =>
    ((φ.symm ⟨(ψ ⟨(v : ℝ), emb01 hu1 v.2⟩ : X), (hUend ⟨(v : ℝ), emb01 hu1 v.2⟩).mpr v.2⟩
        : OpenRealInterval 0 1) : ℝ)
  have hg : Continuous g := by
    dsimp [g]
    have h1 : Continuous (fun v : {x : ℝ // x ∈ Set.Ioo 0 u} =>
        (⟨(v : ℝ), emb01 hu1 v.2⟩ : OpenRealInterval 0 1)) := by
      exact Continuous.subtype_mk continuous_subtype_val (fun v => emb01 hu1 v.2)
    have hψ : Continuous (fun v : {x : ℝ // x ∈ Set.Ioo 0 u} =>
        (ψ ⟨(v : ℝ), emb01 hu1 v.2⟩ : X)) := by
      exact continuous_subtype_val.comp (ψ.continuous.comp h1)
    have h2 : Continuous (fun v : {x : ℝ // x ∈ Set.Ioo 0 u} =>
        (⟨(ψ ⟨(v : ℝ), emb01 hu1 v.2⟩ : X), (hUend ⟨(v : ℝ), emb01 hu1 v.2⟩).mpr v.2⟩
          : {x : X // x ∈ U})) := by
      exact Continuous.subtype_mk hψ (fun v => (hUend ⟨(v : ℝ), emb01 hu1 v.2⟩).mpr v.2)
    have h3 : Continuous (fun v : {x : ℝ // x ∈ Set.Ioo 0 u} =>
        (φ.symm ⟨(ψ ⟨(v : ℝ), emb01 hu1 v.2⟩ : X), (hUend ⟨(v : ℝ), emb01 hu1 v.2⟩).mpr v.2⟩
          : OpenRealInterval 0 1)) := by
      exact φ.symm.continuous.comp h2
    exact continuous_subtype_val.comp h3
  have hcongr : (fun v : {x : ℝ // x ∈ Set.Ioo 0 u} => Tfun hu1 φ ψ hUend (v : ℝ)) = g := by
    funext v
    dsimp [g]
    rw [Tfun_eq hu1 φ ψ hUend v.2]
    dsimp [T]
  change Continuous (fun v : {x : ℝ // x ∈ Set.Ioo 0 u} => Tfun hu1 φ ψ hUend (v : ℝ))
  rw [hcongr]
  exact hg

/-! ## Continuity of the seam function on the unit interval (S157 (b)) -/

/-- `Gfun` equals the transition `T` on the overlap domain. -/
lemma Gfun_eq_Tfun {U V : Set X} {u : ℝ} (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    {v : ℝ} (hv : v ∈ Set.Ioo 0 u) :
    Gfun hu1 φ ψ hUend v = T hu1 φ ψ hUend hv := by
  dsimp [Gfun]
  rw [dif_pos ⟨hv.1, hv.2⟩]

/-- `Gfun` is continuous on the overlap domain `(0,u)` (it equals `Tfun`
there, continuous by (a)). -/
lemma Gfun_continuousOn_domain {U V : Set X} {u : ℝ} (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u) :
    ContinuousOn (Gfun hu1 φ ψ hUend) (Set.Ioo 0 u) := by
  apply ContinuousOn.congr (Tfun_continuousOn hu1 φ ψ hUend)
  intro v hv
  rw [Gfun_eq_Tfun hu1 φ ψ hUend hv, Tfun_eq hu1 φ ψ hUend hv]

/-- `Gfun` is continuous on the free V-tail `(u,1)` (it is the affine map
`v ↦ v + 1 − u` there). -/
lemma Gfun_continuousOn_tail {U V : Set X} {u : ℝ} (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u) :
    ContinuousOn (Gfun hu1 φ ψ hUend) (Set.Ioo u 1) := by
  have haff : ContinuousOn (fun v : ℝ => v + 1 - u) (Set.Ioo u 1) := by fun_prop
  apply ContinuousOn.congr haff
  intro v hv
  dsimp [Gfun]
  have hnot : ¬ (0 < v ∧ v < u) := by intro h; linarith [hv.1]
  rw [dif_neg hnot]

/-- `Gfun` is continuous on the whole unit interval `(0,1)`: the three
pieces `(0,u)` (domain), `{u}` (seam, by `G_continuousAt`) and `(u,1)`
(tail). -/
lemma Gfun_continuousOn_unit {U V : Set X} {s u : ℝ} (hs : 0 < s) (hu : 0 < u) (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hinc : ∀ ⦃v₁ v₂ : ℝ⦄, v₁ ∈ Set.Ioo 0 u → v₂ ∈ Set.Ioo 0 u → v₁ < v₂ →
        Tfun hu1 φ ψ hUend v₁ < Tfun hu1 φ ψ hUend v₂) :
    ContinuousOn (Gfun hu1 φ ψ hUend) (Set.Ioo 0 1) := by
  rw [IsOpen.continuousOn_iff isOpen_Ioo]
  intro v hv
  rcases lt_trichotomy v u with hlt | heq | hgt
  · exact ContinuousOn.continuousAt (Gfun_continuousOn_domain hu1 φ ψ hUend)
      (isOpen_Ioo.mem_nhds ⟨hv.1, hlt⟩)
  · subst heq
    exact G_continuousAt hs hu hu1 φ ψ hVend hUend hinc
  · exact ContinuousOn.continuousAt (Gfun_continuousOn_tail hu1 φ ψ hUend)
      (isOpen_Ioo.mem_nhds ⟨hgt, hv.2⟩)

/-! ## Continuity of the global map (S157 (c)/(d)) -/

/-- Along the V-chart, the global map reads as the seam function:
`F (ψ t) = Gfun (t : ℝ)` (as real values). -/
lemma twoChartF_comp_ψ_val {U V : Set X} {u : ℝ} (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hUV : U ∪ V = univ) {t : OpenRealInterval 0 1} :
    ((twoChartF hu1 φ ψ hUend hUV (ψ t : X) : OpenRealInterval 0 (2 - u)) : ℝ) =
      Gfun hu1 φ ψ hUend (t : ℝ) := by
  by_cases ht : (t : ℝ) < u
  · -- t ∈ (0,u): ψ t ∈ U; both sides are the U-coordinate of ψ t = T t
    have htmem : (t : ℝ) ∈ Set.Ioo 0 u := ⟨t.2.1, ht⟩
    have hψU : ((ψ t : X) ∈ U) := (hUend t).mpr htmem
    rw [twoChartF_val_memU hu1 φ ψ hUend hUV hψU]
    have hG : Gfun hu1 φ ψ hUend (t : ℝ) = T hu1 φ ψ hUend htmem := Gfun_eq_Tfun hu1 φ ψ hUend htmem
    rw [hG]
    dsimp [T]
  · -- t ≥ u: ψ t ∉ U; both sides are ψ⁻¹-coordinate of ψ t + 1 − u = t + 1 − u
    have htge : u ≤ (t : ℝ) := le_of_not_gt ht
    have hψnotU : ((ψ t : X) ∉ U) := by
      intro hU
      have htt : (t : ℝ) ∈ Set.Ioo 0 u := (hUend t).1 hU
      exact (not_lt_of_ge htge) htt.2
    rw [twoChartF_val_not_memU hu1 φ ψ hUend hUV hψnotU]
    have hψinv : ((ψ.symm ⟨(ψ t : X), memV_of_not_memU hUV hψnotU⟩ : OpenRealInterval 0 1) : ℝ) = (t : ℝ) := by
      have harg : (⟨(ψ t : X), memV_of_not_memU hUV hψnotU⟩ : {x : X // x ∈ V}) = ψ t := by
        apply Subtype.ext
        rfl
      calc
        ((ψ.symm ⟨(ψ t : X), memV_of_not_memU hUV hψnotU⟩ : OpenRealInterval 0 1) : ℝ)
            = ((ψ.symm (ψ t) : OpenRealInterval 0 1) : ℝ) := by
              exact congrArg (fun z : {x : X // x ∈ V} => ((ψ.symm z : OpenRealInterval 0 1) : ℝ)) harg
        _ = (t : ℝ) := by
              simpa using congrArg (fun z : OpenRealInterval 0 1 => (z : ℝ)) (ψ.symm_apply_apply t)
    rw [hψinv]
    dsimp [Gfun]
    have hnot : ¬ (0 < (t : ℝ) ∧ (t : ℝ) < u) := by intro h; linarith
    rw [dif_neg hnot]

/-- `F` is continuous on the open chart `U`: there it is the U-chart
coordinate (a chart homeo). -/
lemma twoChartF_continuousOn_U {U V : Set X} {u : ℝ} (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hUV : U ∪ V = univ) : ContinuousOn (twoChartF hu1 φ ψ hUend hUV) U := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun x : {x : X // x ∈ U} => twoChartF hu1 φ ψ hUend hUV (x : X))
  have hval : Continuous (fun x : {x : X // x ∈ U} =>
      ((twoChartF hu1 φ ψ hUend hUV (x : X) : OpenRealInterval 0 (2 - u)) : ℝ)) := by
    have hclean : Continuous (fun x : {x : X // x ∈ U} => ((φ.symm ⟨(x : X), x.2⟩ : OpenRealInterval 0 1) : ℝ)) := by
      exact continuous_subtype_val.comp φ.symm.continuous
    apply Continuous.congr hclean
    intro x
    rw [twoChartF_val_memU hu1 φ ψ hUend hUV x.2]
  exact Continuous.subtype_mk hval (fun x => (twoChartF hu1 φ ψ hUend hUV (x : X)).2)

/-- `F` is continuous on the open chart `V`: along `ψ` it reads as the
seam function `Gfun`, continuous on the unit interval by (b). -/
lemma twoChartF_continuousOn_V {U V : Set X} {s u : ℝ} (hs : 0 < s) (hu : 0 < u) (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hinc : ∀ ⦃v₁ v₂ : ℝ⦄, v₁ ∈ Set.Ioo 0 u → v₂ ∈ Set.Ioo 0 u → v₁ < v₂ →
        Tfun hu1 φ ψ hUend v₁ < Tfun hu1 φ ψ hUend v₂)
    (hUV : U ∪ V = univ) : ContinuousOn (twoChartF hu1 φ ψ hUend hUV) V := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun x : {x : X // x ∈ V} => twoChartF hu1 φ ψ hUend hUV (x : X))
  -- V ≃ (0,1) via ψ: pull back to the unit interval
  let g : OpenRealInterval 0 1 → OpenRealInterval 0 (2 - u) := fun t =>
    twoChartF hu1 φ ψ hUend hUV (ψ t : X)
  have hg : Continuous g := by
    dsimp [g]
    refine Continuous.subtype_mk ?_ (fun t => (twoChartF hu1 φ ψ hUend hUV (ψ t : X)).2)
    have hGcont : Continuous (fun t : OpenRealInterval 0 1 => Gfun hu1 φ ψ hUend (t : ℝ)) := by
      -- from Gfun_continuousOn_unit via the domRestrict direction
      have h1 := (Gfun_continuousOn_unit hs hu hu1 φ ψ hVend hUend hinc)
      rw [continuousOn_iff_continuous_domRestrict] at h1
      exact h1
    apply Continuous.congr hGcont
    intro t
    exact (twoChartF_comp_ψ_val hu1 φ ψ hUend hUV).symm
  -- V-restriction = g ∘ (the map back from V to the interval) ∘?
  -- for x : V: x = ψ(ψ⁻¹ x): twoChartF x = g (ψ⁻¹-based): express x ↦ F x = g (fun via ψ.symm)
  have hback : Continuous (fun x : {x : X // x ∈ V} =>
      (ψ.symm ⟨(x : X), x.2⟩ : OpenRealInterval 0 1)) := by
    exact ψ.symm.continuous
  -- F on V = g ∘ ψ⁻¹∘(embedding)? we need: (fun x : V => twoChartF .. (x : X)) = (g ∘ fun x : V => ψ.symm ⟨x, x.2⟩)
  have hEq : (fun x : {x : X // x ∈ V} => twoChartF hu1 φ ψ hUend hUV (x : X)) =
      (fun x : {x : X // x ∈ V} => g (ψ.symm ⟨(x : X), x.2⟩)) := by
    funext x
    dsimp [g]
    congr 1
    -- (ψ (ψ.symm ⟨x, x.2⟩) : X) = (x : X)
    have hψψ : (ψ (ψ.symm ⟨(x : X), x.2⟩) : X) = (x : X) := by
      exact congrArg (fun z : {x : X // x ∈ V} => (z : X)) (ψ.apply_symm_apply ⟨(x : X), x.2⟩)
    exact hψψ.symm
  rw [hEq]
  exact hg.comp hback

/-- Open-cover glue: continuous on two open sets covering the space. -/
lemma continuous_of_continuousOn_open_cover {X : Type*} [TopologicalSpace X]
    {Y : Type*} [TopologicalSpace Y] {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = univ) {f : X → Y} (hUc : ContinuousOn f U) (hVc : ContinuousOn f V) :
    Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hxU : x ∈ U
  · exact ContinuousOn.continuousAt hUc (hU.mem_nhds hxU)
  · exact ContinuousOn.continuousAt hVc (hV.mem_nhds (memV_of_not_memU hUV hxU))

/-- **Continuity of the global map** (S157 (d)): `twoChartF` is
continuous — on `U` the U-coordinate, on `V` the seam function pulled
back along `ψ`, glued by the open cover `U ∪ V = univ`. -/
lemma twoChartF_continuous {U V : Set X} {s u : ℝ} (hUopen : IsOpen U) (hVopen : IsOpen V)
    (hs : 0 < s) (hu : 0 < u) (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hinc : ∀ ⦃v₁ v₂ : ℝ⦄, v₁ ∈ Set.Ioo 0 u → v₂ ∈ Set.Ioo 0 u → v₁ < v₂ →
        Tfun hu1 φ ψ hUend v₁ < Tfun hu1 φ ψ hUend v₂)
    (hUV : U ∪ V = univ) : Continuous (twoChartF hu1 φ ψ hUend hUV) := by
  exact continuous_of_continuousOn_open_cover hUopen hVopen hUV
    (twoChartF_continuousOn_U hu1 φ ψ hUend hUV)
    (twoChartF_continuousOn_V hs hu hu1 φ ψ hVend hUend hinc hUV)

/-! ## The inverse transition `Sfun` and its endpoint limit (S157 (e)) -/

/-- `y ∈ (s,1)` embedded into `(0,1)` (needs `0 < s`). -/
theorem embS {s : ℝ} (hs0 : 0 < s) {y : ℝ} (hy : y ∈ Set.Ioo s 1) : y ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨lt_trans hs0 hy.1, hy.2⟩

/-- The V-chart coordinate of an overlap point with U-coordinate `y` (the
inverse transition; `y ∈ (s,1)`, value in `(0,u)`), as a total real
function (0 off its domain). -/
noncomputable def Sfun {U V : Set X} {s : ℝ} (hs0 : 0 < s)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (y : ℝ) : ℝ :=
  if hy : y ∈ Set.Ioo s 1 then
    ((ψ.symm ⟨(φ ⟨y, embS hs0 hy⟩ : X), (hVend ⟨y, embS hs0 hy⟩).mpr hy⟩
        : OpenRealInterval 0 1) : ℝ)
  else 0

/-- The overlap value of `Sfun` lies in `(0,u)`: V-coordinates of overlap
points lie in the V-overlap. -/
lemma Sfun_mem {U V : Set X} {s u : ℝ} (hs0 : 0 < s) (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    {y : ℝ} (hy : y ∈ Set.Ioo s 1) :
    Sfun hs0 φ ψ hVend y ∈ Set.Ioo 0 u := by
  dsimp [Sfun]
  have hφV : ((φ ⟨y, embS hs0 hy⟩ : X) ∈ V) := (hVend ⟨y, embS hs0 hy⟩).mpr hy
  let w : OpenRealInterval 0 1 := ψ.symm ⟨(φ ⟨y, embS hs0 hy⟩ : X), hφV⟩
  have hwU : (w : ℝ) ∈ Set.Ioo 0 u := by
    have hψwU : ((ψ w : X) ∈ U) := by
      have heq : (ψ w : X) = (φ ⟨y, embS hs0 hy⟩ : X) := by
        dsimp [w]
        exact congrArg (fun z : {x : X // x ∈ V} => (z : X))
          (ψ.apply_symm_apply ⟨(φ ⟨y, embS hs0 hy⟩ : X), hφV⟩)
      have hφU : ((φ ⟨y, embS hs0 hy⟩ : X) ∈ U) :=
        (φ ⟨y, embS hs0 hy⟩ : {x : X // x ∈ U}).2
      simpa [heq] using hφU
    exact (hUend w).1 hψwU
  rw [dif_pos hy]
  exact hwU

/-- `Tfun (Sfun y) = y` for overlap U-coordinates: the two transitions
are mutual inverses on the overlap. -/
lemma Tfun_of_Sfun {U V : Set X} {s u : ℝ} (hs0 : 0 < s) (hu : 0 < u) (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    {y : ℝ} (hy : y ∈ Set.Ioo s 1) :
    Tfun hu1 φ ψ hUend (Sfun hs0 φ ψ hVend y) = y := by
  -- Sfun y = w = V-coordinate of p := φ⟨y⟩; Tfun w = U-coordinate of ψ⟨w⟩ = p = y
  dsimp [Sfun]
  have hφV : ((φ ⟨y, embS hs0 hy⟩ : X) ∈ V) := (hVend ⟨y, embS hs0 hy⟩).mpr hy
  let p : X := (φ ⟨y, embS hs0 hy⟩ : X)
  let w : OpenRealInterval 0 1 := ψ.symm ⟨p, hφV⟩
  have hwU : (w : ℝ) ∈ Set.Ioo 0 u := by
    have hψwU : ((ψ w : X) ∈ U) := by
      have heq : (ψ w : X) = p := by
        dsimp [w]
        exact congrArg (fun z : {x : X // x ∈ V} => (z : X))
          (ψ.apply_symm_apply ⟨p, hφV⟩)
      have hφU : p ∈ U := (φ ⟨y, embS hs0 hy⟩ : {x : X // x ∈ U}).2
      simpa [heq] using hφU
    exact (hUend w).1 hψwU
  rw [dif_pos hy]
  change Tfun hu1 φ ψ hUend (w : ℝ) = y
  -- Tfun (w:ℝ) = T-coord(w) = U-coordinate of ψ⟨w⟩; ψ⟨w⟩ = p = φ⟨y⟩; U-coordinate = y
  have hψp : (ψ ⟨(w : ℝ), emb01 hu1 hwU⟩ : X) = p := by
    have hwψ : (⟨(w : ℝ), emb01 hu1 hwU⟩ : OpenRealInterval 0 1) = w := by
      apply Subtype.ext
      rfl
    rw [hwψ]
    dsimp [w]
    exact congrArg (fun z : {x : X // x ∈ V} => (z : X))
      (ψ.apply_symm_apply ⟨p, hφV⟩)
  have hφp : (φ ⟨y, embS hs0 hy⟩ : X) = p := rfl
  have hφarg : (⟨(ψ ⟨(w : ℝ), emb01 hu1 hwU⟩ : X),
      (hUend ⟨(w : ℝ), emb01 hu1 hwU⟩).mpr hwU⟩ : {x : X // x ∈ U}) = φ ⟨y, embS hs0 hy⟩ := by
    apply Subtype.ext
    exact hψp
  rw [Tfun_eq hu1 φ ψ hUend hwU]
  dsimp [T]
  calc
    ((φ.symm ⟨(ψ ⟨(w : ℝ), emb01 hu1 hwU⟩ : X),
        (hUend ⟨(w : ℝ), emb01 hu1 hwU⟩).mpr hwU⟩ : OpenRealInterval 0 1) : ℝ)
        = ((φ.symm (φ ⟨y, embS hs0 hy⟩) : OpenRealInterval 0 1) : ℝ) := by
          exact congrArg (fun z : {x : X // x ∈ U} => ((φ.symm z : OpenRealInterval 0 1) : ℝ)) hφarg
    _ = ((⟨y, embS hs0 hy⟩ : OpenRealInterval 0 1) : ℝ) := by
          simpa using congrArg (fun z : OpenRealInterval 0 1 => (z : ℝ))
            (φ.symm_apply_apply ⟨y, embS hs0 hy⟩)
    _ = y := rfl

/-- `Sfun (T v) = v` for overlap V-coordinates: the other direction of
the mutual-inverse identity. -/
lemma Sfun_of_Tfun {U V : Set X} {s u : ℝ} (hs0 : 0 < s) (hu : 0 < u) (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    {v : ℝ} (hv : v ∈ Set.Ioo 0 u) :
    Sfun hs0 φ ψ hVend (T hu1 φ ψ hUend hv) = v := by
  have hy : T hu1 φ ψ hUend hv ∈ Set.Ioo s 1 := T_mem hs0 hu hu1 φ ψ hVend hUend hv
  dsimp [Sfun]
  rw [dif_pos hy]
  -- y := T hv is the U-coordinate of ψ⟨v⟩: the point φ⟨y⟩ equals ψ⟨v⟩,
  -- hence its V-coordinate is v.
  let p : X := (φ ⟨(T hu1 φ ψ hUend hv), embS hs0 hy⟩ : X)
  have hφV : p ∈ V := (hVend ⟨(T hu1 φ ψ hUend hv), embS hs0 hy⟩).mpr hy
  have hpψ : p = (ψ ⟨v, emb01 hu1 hv⟩ : X) := by
    -- y = U-coordinate of ψ⟨v⟩: T hu1 φ ψ hUend hv = U-coord(ψ⟨v⟩): so φ⟨y⟩ = ψ⟨v⟩
    have hyeq : ((φ.symm ⟨(ψ ⟨v, emb01 hu1 hv⟩ : X), (hUend ⟨v, emb01 hu1 hv⟩).mpr hv⟩
        : OpenRealInterval 0 1) : ℝ) = T hu1 φ ψ hUend hv := rfl
    dsimp [p]
    -- φ applied to the ORI element ⟨T hv, embS⟩ equals ψ⟨v⟩:
    -- φ⟨U-coord⟩ of a point returns the point.
    have harg : (⟨(T hu1 φ ψ hUend hv), embS hs0 hy⟩ : OpenRealInterval 0 1) =
        φ.symm ⟨(ψ ⟨v, emb01 hu1 hv⟩ : X), (hUend ⟨v, emb01 hu1 hv⟩).mpr hv⟩ := by
      apply Subtype.ext
      exact hyeq
    calc
      (φ ⟨(T hu1 φ ψ hUend hv), embS hs0 hy⟩ : X)
          = (φ (φ.symm ⟨(ψ ⟨v, emb01 hu1 hv⟩ : X), (hUend ⟨v, emb01 hu1 hv⟩).mpr hv⟩) : X) := by
            exact congrArg (fun z : OpenRealInterval 0 1 => (φ z : X)) harg
      _ = (ψ ⟨v, emb01 hu1 hv⟩ : X) := by
            exact congrArg (fun z : {x : X // x ∈ U} => (z : X))
              (φ.apply_symm_apply ⟨(ψ ⟨v, emb01 hu1 hv⟩ : X), (hUend ⟨v, emb01 hu1 hv⟩).mpr hv⟩)
  have hφarg : (⟨p, hφV⟩ : {x : X // x ∈ V}) = ψ ⟨v, emb01 hu1 hv⟩ := by
    apply Subtype.ext
    exact hpψ
  calc
    ((ψ.symm ⟨p, hφV⟩ : OpenRealInterval 0 1) : ℝ)
        = ((ψ.symm (ψ ⟨v, emb01 hu1 hv⟩) : OpenRealInterval 0 1) : ℝ) := by
          exact congrArg (fun z : {x : X // x ∈ V} => ((ψ.symm z : OpenRealInterval 0 1) : ℝ)) hφarg
    _ = ((⟨v, emb01 hu1 hv⟩ : OpenRealInterval 0 1) : ℝ) := by
          simpa using congrArg (fun z : OpenRealInterval 0 1 => (z : ℝ))
            (ψ.symm_apply_apply ⟨v, emb01 hu1 hv⟩)
    _ = v := rfl

/-- Range of `Sfun`: the V-coordinates of overlap points cover `(0,u)`.
(One direction: values lie in `(0,u)` by `Sfun_mem`; the other: every
`w ∈ (0,u)` is the V-coordinate of `ψ⟨w⟩`, whose U-coordinate is
`T hu1 φ ψ hUend ⟨w.1, w.2⟩`.) -/
lemma Sfun_range {U V : Set X} {s u : ℝ} (hs0 : 0 < s) (hu : 0 < u) (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u) :
    Sfun hs0 φ ψ hVend '' Set.Ioo s 1 = Set.Ioo 0 u := by
  ext w
  constructor
  · intro hw
    rcases hw with ⟨y, hy, hwy⟩
    have hwm : Sfun hs0 φ ψ hVend y ∈ Set.Ioo 0 u := Sfun_mem hs0 hu1 φ ψ hVend hUend hy
    rwa [hwy] at hwm
  · intro hw
    exact ⟨T hu1 φ ψ hUend hw,
      T_mem hs0 hu hu1 φ ψ hVend hUend hw,
      Sfun_of_Tfun hs0 hu hu1 φ ψ hVend hUend hw⟩

/-- `Sfun` is strictly increasing on its domain `(s,1)`: it is the
inverse of the increasing `Tfun` (identity `Tfun (Sfun y) = y` + `hinc`). -/
lemma Sfun_strictMonoOn {U V : Set X} {s u : ℝ} (hs0 : 0 < s) (hu : 0 < u) (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hinc : ∀ ⦃v₁ v₂ : ℝ⦄, v₁ ∈ Set.Ioo 0 u → v₂ ∈ Set.Ioo 0 u → v₁ < v₂ →
        Tfun hu1 φ ψ hUend v₁ < Tfun hu1 φ ψ hUend v₂) :
    StrictMonoOn (Sfun hs0 φ ψ hVend) (Set.Ioo s 1) := by
  intro y₁ hy₁ y₂ hy₂ hylt
  have hTmono := Tfun_strictMonoOn hu1 φ ψ hUend hinc
  have h1 : Sfun hs0 φ ψ hVend y₁ ∈ Set.Ioo 0 u := Sfun_mem hs0 hu1 φ ψ hVend hUend hy₁
  have h2 : Sfun hs0 φ ψ hVend y₂ ∈ Set.Ioo 0 u := Sfun_mem hs0 hu1 φ ψ hVend hUend hy₂
  by_contra hnot
  have hle : Sfun hs0 φ ψ hVend y₂ ≤ Sfun hs0 φ ψ hVend y₁ := le_of_not_gt hnot
  rcases lt_or_eq_of_le hle with hlt | heq
  · have hTs : Tfun hu1 φ ψ hUend (Sfun hs0 φ ψ hVend y₂) <
        Tfun hu1 φ ψ hUend (Sfun hs0 φ ψ hVend y₁) := hTmono h2 h1 hlt
    have hTs1 : Tfun hu1 φ ψ hUend (Sfun hs0 φ ψ hVend y₂) = y₂ :=
      Tfun_of_Sfun hs0 hu hu1 φ ψ hVend hUend hy₂
    have hTs2 : Tfun hu1 φ ψ hUend (Sfun hs0 φ ψ hVend y₁) = y₁ :=
      Tfun_of_Sfun hs0 hu hu1 φ ψ hVend hUend hy₁
    rw [hTs1, hTs2] at hTs
    exact (not_lt_of_ge (le_of_lt hylt)) hTs
  · have hTeq : y₂ = y₁ := by
      calc
        y₂ = Tfun hu1 φ ψ hUend (Sfun hs0 φ ψ hVend y₂) :=
          (Tfun_of_Sfun hs0 hu hu1 φ ψ hVend hUend hy₂).symm
        _ = Tfun hu1 φ ψ hUend (Sfun hs0 φ ψ hVend y₁) := by rw [heq]
        _ = y₁ := Tfun_of_Sfun hs0 hu hu1 φ ψ hVend hUend hy₁
    exact (ne_of_lt hylt) hTeq.symm

/-- **Endpoint-limit of the inverse transition (S157 (e))**: as the
U-coordinate `y` of an overlap point approaches `1` from below, its
V-coordinate `Sfun y` approaches `u` (the top of the V-overlap).
Invokes the fleet mirror of L31
(`Commons.Analysis.Calculus.strictMonoOn_surj_Ioo_tendsto_top`) on the
strictly increasing surjection `Sfun`. -/
lemma Sfun_endpoint_top {U V : Set X} {s u : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hu : 0 < u) (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hinc : ∀ ⦃v₁ v₂ : ℝ⦄, v₁ ∈ Set.Ioo 0 u → v₂ ∈ Set.Ioo 0 u → v₁ < v₂ →
        Tfun hu1 φ ψ hUend v₁ < Tfun hu1 φ ψ hUend v₂) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ y : ℝ, y ∈ Set.Ioo s 1 → 1 - δ < y → u - ε < Sfun hs0 φ ψ hVend y := by
  exact Commons.Analysis.Calculus.strictMonoOn_surj_Ioo_tendsto_top hs1
    (Sfun_strictMonoOn hs0 hu hu1 φ ψ hVend hUend hinc)
    (Sfun_range hs0 hu hu1 φ ψ hVend hUend)

/-- Upper bound: `Sfun y < u` on its domain (values live in `(0,u)`). -/
lemma Sfun_lt_u {U V : Set X} {s u : ℝ} (hs0 : 0 < s) (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    {y : ℝ} (hy : y ∈ Set.Ioo s 1) :
    Sfun hs0 φ ψ hVend y < u := by
  exact (Sfun_mem hs0 hu1 φ ψ hVend hUend hy).2

/-! ## The inverse map `twoChartG` and its continuity (S157 (f)) -/

/-- **The inverse of the global map**: `y < 1` is the U-coordinate of a
point of `U` (`φ⟨y⟩`); `y ≥ 1` is the affine-shifted V-coordinate of a
point of the free V-tail (`ψ⟨y − 1 + u⟩`). -/
noncomputable def twoChartG {U V : Set X} {s u : ℝ} (hs0 : 0 < s) (hu : 0 < u)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (y : OpenRealInterval 0 (2 - u)) : X := by
  classical
  by_cases hy1 : (y : ℝ) < 1
  · exact (φ ⟨(y : ℝ), ⟨y.2.1, hy1⟩⟩ : X)
  · have hyge : 1 ≤ (y : ℝ) := le_of_not_gt hy1
    let w : ℝ := (y : ℝ) - 1 + u
    have hw0 : 0 < w := by dsimp [w]; linarith [hyge, hu]
    have hw1 : w < 1 := by dsimp [w]; linarith [y.2.2]
    exact (ψ ⟨w, ⟨hw0, hw1⟩⟩ : X)

/-- Value of `twoChartG` for `y < 1`: the U-chart point `φ⟨y⟩`. -/
lemma twoChartG_apply_lt_one {U V : Set X} {s u : ℝ} (hs0 : 0 < s) (hu : 0 < u)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    {y : OpenRealInterval 0 (2 - u)} (hy1 : (y : ℝ) < 1) :
    twoChartG hs0 hu φ ψ y = (φ ⟨(y : ℝ), ⟨y.2.1, hy1⟩⟩ : X) := by
  dsimp [twoChartG]
  rw [dif_pos hy1]

/-- Value of `twoChartG` for `y ≥ 1`: the V-tail point
`ψ⟨y − 1 + u⟩` (whose parameter lies in `[u,1)`). -/
lemma twoChartG_apply_ge_one {U V : Set X} {s u : ℝ} (hs0 : 0 < s) (hu : 0 < u)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    {y : OpenRealInterval 0 (2 - u)} (hy1 : ¬ (y : ℝ) < 1) :
    twoChartG hs0 hu φ ψ y = (ψ ⟨(y : ℝ) - 1 + u, ⟨by
      have hyge : 1 ≤ (y : ℝ) := le_of_not_gt hy1
      have hw0 : 0 < (y : ℝ) - 1 + u := by linarith [hyge, hu]
      exact hw0, by
      have hw1 : (y : ℝ) - 1 + u < 1 := by linarith [y.2.2]
      exact hw1⟩⟩ : X) := by
  dsimp [twoChartG]
  rw [dif_neg hy1]

/-- `twoChartG` is continuous on the open piece `{y | (y : ℝ) < 1}`:
there it is `φ` applied to the coordinate. -/
lemma twoChartG_continuousOn_left {U V : Set X} {s u : ℝ} (hs0 : 0 < s) (hu : 0 < u)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V}) :
    ContinuousOn (twoChartG hs0 hu φ ψ)
      {y : OpenRealInterval 0 (2 - u) | (y : ℝ) < 1} := by
  rw [continuousOn_iff_continuous_domRestrict]
  let A : Set (OpenRealInterval 0 (2 - u)) := {y | (y : ℝ) < 1}
  change Continuous (fun a : {y : OpenRealInterval 0 (2 - u) // y ∈ A} =>
    twoChartG hs0 hu φ ψ (a : OpenRealInterval 0 (2 - u)))
  have hf : Continuous (fun a : {y : OpenRealInterval 0 (2 - u) // y ∈ A} =>
      ((a : OpenRealInterval 0 (2 - u)) : ℝ)) := by
    fun_prop
  have hc : Continuous (fun a : {y : OpenRealInterval 0 (2 - u) // y ∈ A} =>
      (⟨((a : OpenRealInterval 0 (2 - u)) : ℝ),
        ⟨(a : OpenRealInterval 0 (2 - u)).2.1, a.2⟩⟩ : OpenRealInterval 0 1)) := by
    exact Continuous.subtype_mk hf
      (fun a => ⟨(a : OpenRealInterval 0 (2 - u)).2.1, a.2⟩)
  have hφX : Continuous (fun z : OpenRealInterval 0 1 => (φ z : X)) := by
    exact continuous_subtype_val.comp φ.continuous
  have hclean : Continuous (fun a : {y : OpenRealInterval 0 (2 - u) // y ∈ A} =>
      (φ ⟨((a : OpenRealInterval 0 (2 - u)) : ℝ),
        ⟨(a : OpenRealInterval 0 (2 - u)).2.1, a.2⟩⟩ : X)) :=
    hφX.comp hc
  apply Continuous.congr hclean
  intro a
  exact (twoChartG_apply_lt_one hs0 hu φ ψ a.2).symm

lemma twoChartG_continuousOn_right {U V : Set X} {s u : ℝ} (hs0 : 0 < s) (hu : 0 < u)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V}) :
    ContinuousOn (twoChartG hs0 hu φ ψ)
      {y : OpenRealInterval 0 (2 - u) | 1 < (y : ℝ)} := by
  rw [continuousOn_iff_continuous_domRestrict]
  let A : Set (OpenRealInterval 0 (2 - u)) := {y | 1 < (y : ℝ)}
  change Continuous (fun a : {y : OpenRealInterval 0 (2 - u) // y ∈ A} =>
    twoChartG hs0 hu φ ψ (a : OpenRealInterval 0 (2 - u)))
  have hc : Continuous (fun a : {y : OpenRealInterval 0 (2 - u) // y ∈ A} =>
      (⟨((a : OpenRealInterval 0 (2 - u)) : ℝ) - 1 + u,
          ⟨by
            have hyge : 1 ≤ ((a : OpenRealInterval 0 (2 - u)) : ℝ) := le_of_lt a.2
            have hw0 : 0 < ((a : OpenRealInterval 0 (2 - u)) : ℝ) - 1 + u := by linarith [hyge, hu]
            exact hw0, by
            have hw1 : ((a : OpenRealInterval 0 (2 - u)) : ℝ) - 1 + u < 1 := by
              linarith [(a : OpenRealInterval 0 (2 - u)).2.2]
            exact hw1⟩⟩ : OpenRealInterval 0 1)) := by
    apply Continuous.subtype_mk
    fun_prop
  have hψ : Continuous (fun a : {y : OpenRealInterval 0 (2 - u) // y ∈ A} =>
      (ψ ⟨((a : OpenRealInterval 0 (2 - u)) : ℝ) - 1 + u,
        ⟨by
          have hyge : 1 ≤ ((a : OpenRealInterval 0 (2 - u)) : ℝ) := le_of_lt a.2
          have hw0 : 0 < ((a : OpenRealInterval 0 (2 - u)) : ℝ) - 1 + u := by linarith [hyge, hu]
          exact hw0, by
          have hw1 : ((a : OpenRealInterval 0 (2 - u)) : ℝ) - 1 + u < 1 := by
            linarith [(a : OpenRealInterval 0 (2 - u)).2.2]
          exact hw1⟩⟩ : X)) := by
    exact continuous_subtype_val.comp (ψ.continuous.comp hc)
  apply Continuous.congr hψ
  intro a
  have hge : ¬ ((a : OpenRealInterval 0 (2 - u)) : ℝ) < 1 := not_lt_of_gt a.2
  rw [twoChartG_apply_ge_one hs0 hu φ ψ hge]

/-! ## The seam identity and continuity of `twoChartG` at `y = 1` -/

/-- **Seam identity**: an overlap point with U-coordinate `y ∈ (s,1)` is
`ψ⟨Sfun y⟩` (its V-coordinate is `Sfun y`). -/
lemma φ_eq_ψ_Sfun {U V : Set X} {s u : ℝ} (hs0 : 0 < s) (hu : 0 < u) (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    {y : ℝ} (hy : y ∈ Set.Ioo s 1) :
    (ψ ⟨Sfun hs0 φ ψ hVend y, emb01 hu1 (Sfun_mem hs0 hu1 φ ψ hVend hUend hy)⟩ : X)
      = (φ ⟨y, embS hs0 hy⟩ : X) := by
  let p : X := (φ ⟨y, embS hs0 hy⟩ : X)
  have hφV : p ∈ V := (hVend ⟨y, embS hs0 hy⟩).mpr hy
  let w : OpenRealInterval 0 1 := ψ.symm ⟨p, hφV⟩
  have hS : Sfun hs0 φ ψ hVend y = (w : ℝ) := by
    dsimp [Sfun, w]
    rw [dif_pos hy]
  have harg : (⟨Sfun hs0 φ ψ hVend y, emb01 hu1 (Sfun_mem hs0 hu1 φ ψ hVend hUend hy)⟩
      : OpenRealInterval 0 1) = w := by
    apply Subtype.ext
    exact hS
  calc
    (ψ ⟨Sfun hs0 φ ψ hVend y, emb01 hu1 (Sfun_mem hs0 hu1 φ ψ hVend hUend hy)⟩ : X)
        = (ψ w : X) := by
          exact congrArg (fun z : OpenRealInterval 0 1 => (ψ z : X)) harg
    _ = p := by
          dsimp [w]
          exact congrArg (fun z : {x : X // x ∈ V} => (z : X))
            (ψ.apply_symm_apply ⟨p, hφV⟩)
    _ = (φ ⟨y, embS hs0 hy⟩ : X) := rfl

/-! ## Seam convergence of `twoChartG` at `y = 1` (S157 (f) step 2) -/

/-- **Left convergence at the seam**: for any neighbourhood `N` of
`ψ⟨u⟩`, the left-hand values `φ⟨y⟩ = ψ⟨Sfun y⟩` (overlap U-coordinates
`y ∈ (s,1)` sufficiently close to `1` from below) lie in `N`.  Proof:
pull `N` back under the homeo `ψ` to a real neighbourhood of `u`
(metric ball of radius `η`); `Sfun_endpoint_top` + `Sfun_lt_u` give
`|Sfun y − u| < η` eventually; the seam identity `φ_eq_ψ_Sfun`
identifies `ψ⟨Sfun y⟩` with `φ⟨y⟩`. -/
lemma twoChartG_left_converge {U V : Set X} {s u : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hu : 0 < u) (hu1s : u < 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hinc : ∀ ⦃v₁ v₂ : ℝ⦄, v₁ ∈ Set.Ioo 0 u → v₂ ∈ Set.Ioo 0 u → v₁ < v₂ →
        Tfun (le_of_lt hu1s) φ ψ hUend v₁ < Tfun (le_of_lt hu1s) φ ψ hUend v₂) :
    ∀ N : Set X, N ∈ 𝓝 ((ψ ⟨u, ⟨hu, hu1s⟩⟩ : X)) →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ y : ℝ, ∀ hy : y ∈ Set.Ioo s 1, 1 - δ < y →
          ((φ ⟨y, embS hs0 hy⟩ : X) ∈ N) := by
  intro N hN
  let hu1 : u ≤ 1 := le_of_lt hu1s
  have hm : Continuous (fun t : OpenRealInterval 0 1 => (ψ t : X)) :=
    continuous_subtype_val.comp ψ.continuous
  have hpre : (fun t : OpenRealInterval 0 1 => (ψ t : X)) ⁻¹' N ∈ 𝓝 ⟨u, ⟨hu, hu1s⟩⟩ :=
    hm.continuousAt.preimage_mem_nhds hN
  rcases Metric.mem_nhds_iff.mp hpre with ⟨η, hηpos, hball⟩
  have hballN : ∀ t : OpenRealInterval 0 1,
      dist t ⟨u, ⟨hu, hu1s⟩⟩ < η → (ψ t : X) ∈ N := by
    intro t ht
    exact hball (by simpa [Metric.mem_ball] using ht)
  rcases Sfun_endpoint_top hs0 hs1 hu hu1 φ ψ hVend hUend hinc η hηpos with ⟨δ₁, hδ₁pos, hδ₁⟩
  let δ : ℝ := min δ₁ (1 - s)
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact lt_min hδ₁pos (sub_pos.mpr hs1)
  refine ⟨δ, hδpos, ?_⟩
  intro y hy hyδ
  have hyδ₁ : 1 - δ₁ < y := by
    have hδ₁le : δ ≤ δ₁ := by dsimp [δ]; exact min_le_left δ₁ (1 - s)
    linarith
  have hlow : u - η < Sfun hs0 φ ψ hVend y := hδ₁ y hy hyδ₁
  have hup : Sfun hs0 φ ψ hVend y < u := Sfun_lt_u hs0 hu1 φ ψ hVend hUend hy
  have hSnear : dist (⟨Sfun hs0 φ ψ hVend y, emb01 hu1 (Sfun_mem hs0 hu1 φ ψ hVend hUend hy)⟩
      : OpenRealInterval 0 1) (⟨u, ⟨hu, hu1s⟩⟩ : OpenRealInterval 0 1) < η := by
    have habs : |Sfun hs0 φ ψ hVend y - u| < η := by
      rw [abs_lt]
      constructor <;> linarith
    change dist (Sfun hs0 φ ψ hVend y) u < η
    rw [Real.dist_eq]
    exact habs
  have hψin : (ψ ⟨Sfun hs0 φ ψ hVend y, emb01 hu1 (Sfun_mem hs0 hu1 φ ψ hVend hUend hy)⟩ : X) ∈ N :=
    hballN (⟨Sfun hs0 φ ψ hVend y, emb01 hu1 (Sfun_mem hs0 hu1 φ ψ hVend hUend hy)⟩
      : OpenRealInterval 0 1) hSnear
  have hid := φ_eq_ψ_Sfun hs0 hu hu1 φ ψ hVend hUend hy
  rwa [hid] at hψin

/-- **Right convergence at the seam**: `twoChartG⟨y⟩ = ψ⟨y − 1 + u⟩ →
ψ⟨u⟩` as `y → 1⁺` (affine reparametrisation of the continuous `ψ`). -/
lemma twoChartG_right_converge {U V : Set X} {s u : ℝ} (hs0 : 0 < s)
    (hu : 0 < u) (hu1s : u < 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V}) :
    ∀ N : Set X, N ∈ 𝓝 ((ψ ⟨u, ⟨hu, hu1s⟩⟩ : X)) →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ y : OpenRealInterval 0 (2 - u), 1 < (y : ℝ) → (y : ℝ) - 1 < δ →
          (twoChartG hs0 hu φ ψ y ∈ N) := by
  intro N hN
  let hu1 : u ≤ 1 := le_of_lt hu1s
  have hm : Continuous (fun t : OpenRealInterval 0 1 => (ψ t : X)) :=
    continuous_subtype_val.comp ψ.continuous
  have hpre : (fun t : OpenRealInterval 0 1 => (ψ t : X)) ⁻¹' N ∈ 𝓝 ⟨u, ⟨hu, hu1s⟩⟩ :=
    hm.continuousAt.preimage_mem_nhds hN
  rcases Metric.mem_nhds_iff.mp hpre with ⟨η, hηpos, hball⟩
  have hballN : ∀ t : OpenRealInterval 0 1,
      dist t ⟨u, ⟨hu, hu1s⟩⟩ < η → (ψ t : X) ∈ N := by
    intro t ht
    exact hball (by simpa [Metric.mem_ball] using ht)
  refine ⟨η, hηpos, ?_⟩
  intro y hygt hyη
  have hge : ¬ (y : ℝ) < 1 := not_lt_of_gt hygt
  rw [twoChartG_apply_ge_one hs0 hu φ ψ hge]
  have hw0 : 0 < (y : ℝ) - 1 + u := by linarith [hu, hygt]
  have hw1 : (y : ℝ) - 1 + u < 1 := by linarith [y.2.2]
  have hnear : dist (⟨(y : ℝ) - 1 + u, ⟨hw0, hw1⟩⟩ : OpenRealInterval 0 1)
      (⟨u, ⟨hu, hu1s⟩⟩ : OpenRealInterval 0 1) < η := by
    have habs : |((y : ℝ) - 1 + u) - u| < η := by
      rw [abs_lt]
      constructor <;> linarith
    change dist ((y : ℝ) - 1 + u) u < η
    rw [Real.dist_eq]
    exact habs
  exact hballN (⟨(y : ℝ) - 1 + u, ⟨hw0, hw1⟩⟩ : OpenRealInterval 0 1) hnear

/-- Subtype distance is the induced distance on values. -/
lemma dist_subtype_val {α : Type*} [PseudoMetricSpace α] (p : α → Prop)
    (x y : {a : α // p a}) : dist x y = dist (x : α) (y : α) := rfl

/-! ## Seam continuity of `twoChartG` and the full continuity (S157 (f) step 3) -/

/-- Continuity of `twoChartG` at the seam point `⟨1, ·⟩`: left values
`φ⟨y⟩ = ψ⟨Sfun y⟩ → ψ⟨u⟩` (`twoChartG_left_converge`), right values
`ψ⟨y − 1 + u⟩ → ψ⟨u⟩` (`twoChartG_right_converge`). -/
lemma twoChartG_continuousAt_seam {U V : Set X} {s u : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hu : 0 < u) (hu1s : u < 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hinc : ∀ ⦃v₁ v₂ : ℝ⦄, v₁ ∈ Set.Ioo 0 u → v₂ ∈ Set.Ioo 0 u → v₁ < v₂ →
        Tfun (le_of_lt hu1s) φ ψ hUend v₁ < Tfun (le_of_lt hu1s) φ ψ hUend v₂)
    {hm : 1 ∈ Set.Ioo 0 (2 - u)} :
    ContinuousAt (twoChartG hs0 hu φ ψ) ⟨1, hm⟩ := by
  have hval0 : twoChartG hs0 hu φ ψ ⟨1, hm⟩ = (ψ ⟨u, ⟨hu, hu1s⟩⟩ : X) := by
    have hge : ¬ (1 : ℝ) < 1 := by norm_num
    rw [twoChartG_apply_ge_one hs0 hu φ ψ hge]
    congr 1
    apply Subtype.ext
    ring_nf
  rw [continuousAt_def]
  intro N hN
  have hN' : N ∈ 𝓝 ((ψ ⟨u, ⟨hu, hu1s⟩⟩ : X)) := by
    simpa [hval0] using hN
  rcases twoChartG_left_converge hs0 hs1 hu hu1s φ ψ hVend hUend hinc N hN' with ⟨δₗ, hδₗpos, hδₗ⟩
  rcases twoChartG_right_converge hs0 hu hu1s φ ψ N hN' with ⟨δᵣ, hδᵣpos, hδᵣ⟩
  let ε : ℝ := min δₗ (min δᵣ (1 - s))
  have hεpos : 0 < ε := by
    dsimp [ε]
    exact lt_min hδₗpos (lt_min hδᵣpos (sub_pos.mpr hs1))
  apply Metric.mem_nhds_iff.mpr
  refine ⟨ε, hεpos, ?_⟩
  intro z hz
  have hzabs : |(z : ℝ) - 1| < ε := by
    have hz1 : dist (z : ℝ) 1 < ε := by
      rw [Metric.mem_ball] at hz
      rw [dist_subtype_val] at hz
      simpa using hz
    rwa [Real.dist_eq] at hz1
  by_cases hzlt : (z : ℝ) < 1
  · have hval_gt_s : s < (z : ℝ) := by
      have h1 : 1 - ε < (z : ℝ) := by linarith [(abs_lt.mp hzabs).1]
      have hεs : ε ≤ 1 - s := by
        dsimp [ε]
        exact le_trans (min_le_right δₗ (min δᵣ (1 - s))) (min_le_right δᵣ (1 - s))
      linarith
    have hvalmem : (z : ℝ) ∈ Set.Ioo s 1 := ⟨hval_gt_s, hzlt⟩
    have hzδl : 1 - δₗ < (z : ℝ) := by
      have h1 : 1 - ε < (z : ℝ) := by linarith [(abs_lt.mp hzabs).1]
      have hεδl : ε ≤ δₗ := by
        dsimp [ε]
        exact min_le_left δₗ (min δᵣ (1 - s))
      linarith
    have hφin : (φ ⟨(z : ℝ), embS hs0 hvalmem⟩ : X) ∈ N := hδₗ (z : ℝ) hvalmem hzδl
    have hval2 : twoChartG hs0 hu φ ψ z = (φ ⟨(z : ℝ), embS hs0 hvalmem⟩ : X) := by
      rw [twoChartG_apply_lt_one hs0 hu φ ψ hzlt]
    rwa [← hval2] at hφin
  · by_cases hzeq : (z : ℝ) = 1
    · have hzdef : z = ⟨1, hm⟩ := by
        apply Subtype.ext
        exact hzeq
      rw [hzdef]
      change twoChartG hs0 hu φ ψ ⟨1, hm⟩ ∈ N
      rw [hval0]
      exact mem_of_mem_nhds hN'
    · have hgt1 : 1 < (z : ℝ) := lt_of_le_of_ne (le_of_not_gt hzlt) (by intro h; exact hzeq h.symm)
      have hzδr : (z : ℝ) - 1 < δᵣ := by
        have hεδr : ε ≤ δᵣ := by
          dsimp [ε]
          exact le_trans (min_le_right δₗ (min δᵣ (1 - s))) (min_le_left δᵣ (1 - s))
        linarith [(abs_lt.mp hzabs).2, hεδr]
      exact hδᵣ z hgt1 hzδr

/-- **`twoChartG` is continuous** (three pieces: the two open pieces and
the seam point, glued by the convergence lemmas). -/
lemma twoChartG_continuous {U V : Set X} {s u : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hu : 0 < u) (hu1s : u < 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hinc : ∀ ⦃v₁ v₂ : ℝ⦄, v₁ ∈ Set.Ioo 0 u → v₂ ∈ Set.Ioo 0 u → v₁ < v₂ →
        Tfun (le_of_lt hu1s) φ ψ hUend v₁ < Tfun (le_of_lt hu1s) φ ψ hUend v₂) :
    Continuous (twoChartG hs0 hu φ ψ) := by
  rw [continuous_iff_continuousAt]
  intro y
  rcases lt_trichotomy (y : ℝ) 1 with hlt | heq | hgt
  · exact ContinuousOn.continuousAt (twoChartG_continuousOn_left hs0 hu φ ψ)
      (by
        have hp : (fun z : OpenRealInterval 0 (2 - u) => (z : ℝ)) ⁻¹' (Set.Iio 1) ∈ 𝓝 y :=
          (continuous_subtype_val.continuousAt).preimage_mem_nhds (isOpen_Iio.mem_nhds hlt)
        simpa [Set.preimage, Set.Iio] using hp)
  · have hmem : 1 ∈ Set.Ioo 0 (2 - u) := by simpa [heq] using y.2
    have hydef : y = ⟨1, hmem⟩ := by
      apply Subtype.ext
      exact heq
    rw [hydef]
    exact twoChartG_continuousAt_seam hs0 hs1 hu hu1s φ ψ hVend hUend hinc (hm := hmem)
  · exact ContinuousOn.continuousAt (twoChartG_continuousOn_right hs0 hu φ ψ)
      (by
        have hp : (fun z : OpenRealInterval 0 (2 - u) => (z : ℝ)) ⁻¹' (Set.Ioi 1) ∈ 𝓝 y :=
          (continuous_subtype_val.continuousAt).preimage_mem_nhds (isOpen_Ioi.mem_nhds hgt)
        simpa [Set.preimage, Set.Ioi] using hp)

/-! ## The two-chart gluing theorem (S157 (f) step 4) -/

/-- `twoChartG` is the left inverse of `twoChartF`. -/
lemma twoChartG_comp_twoChartF {U V : Set X} {s u : ℝ} (hs0 : 0 < s) (hu : 0 < u)
    (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hUV : U ∪ V = univ) (x : X) :
    twoChartG hs0 hu φ ψ (twoChartF hu1 φ ψ hUend hUV x) = x := by
  by_cases hxU : x ∈ U
  · let Fx : OpenRealInterval 0 (2 - u) := twoChartF hu1 φ ψ hUend hUV x
    have hFx : (Fx : ℝ) < 1 := by
      dsimp [Fx]
      rw [twoChartF_val_memU hu1 φ ψ hUend hUV hxU]
      exact (φ.symm ⟨x, hxU⟩ : OpenRealInterval 0 1).2.2
    dsimp [twoChartG]
    rw [dif_pos hFx]
    have harg : (⟨(Fx : ℝ), ⟨Fx.2.1, hFx⟩⟩ : OpenRealInterval 0 1) = φ.symm ⟨x, hxU⟩ := by
      apply Subtype.ext
      dsimp [Fx]
      exact twoChartF_val_memU hu1 φ ψ hUend hUV hxU
    calc
      (φ ⟨(Fx : ℝ), ⟨Fx.2.1, hFx⟩⟩ : X)
          = (φ (φ.symm ⟨x, hxU⟩) : X) := by
            exact congrArg (fun z : OpenRealInterval 0 1 => (φ z : X)) harg
      _ = x := by
            exact congrArg (fun z : {x : X // x ∈ U} => (z : X)) (φ.apply_symm_apply ⟨x, hxU⟩)
  · let Fx : OpenRealInterval 0 (2 - u) := twoChartF hu1 φ ψ hUend hUV x
    have hge : ¬ (Fx : ℝ) < 1 := by
      dsimp [Fx]
      rw [twoChartF_val_not_memU hu1 φ ψ hUend hUV hxU]
      have hgeu := coord_ge_u_of_not_memU hu1 φ ψ hUend hUV hxU
      exact not_lt_of_ge (by linarith)
    dsimp [twoChartG]
    rw [dif_neg hge]
    have hw0 : 0 < (Fx : ℝ) - 1 + u := by
      have hv0 : 0 < ((ψ.symm ⟨x, memV_of_not_memU hUV hxU⟩ : OpenRealInterval 0 1) : ℝ) :=
        (ψ.symm ⟨x, memV_of_not_memU hUV hxU⟩ : OpenRealInterval 0 1).2.1
      dsimp [Fx]
      rw [twoChartF_val_not_memU hu1 φ ψ hUend hUV hxU]
      nlinarith
    have hw1 : (Fx : ℝ) - 1 + u < 1 := by
      have hv1 : ((ψ.symm ⟨x, memV_of_not_memU hUV hxU⟩ : OpenRealInterval 0 1) : ℝ) < 1 :=
        (ψ.symm ⟨x, memV_of_not_memU hUV hxU⟩ : OpenRealInterval 0 1).2.2
      dsimp [Fx]
      rw [twoChartF_val_not_memU hu1 φ ψ hUend hUV hxU]
      nlinarith
    have harg : (⟨(Fx : ℝ) - 1 + u, ⟨hw0, hw1⟩⟩ : OpenRealInterval 0 1) =
        ψ.symm ⟨x, memV_of_not_memU hUV hxU⟩ := by
      apply Subtype.ext
      dsimp [Fx]
      rw [twoChartF_val_not_memU hu1 φ ψ hUend hUV hxU]
      ring
    calc
      (ψ ⟨(Fx : ℝ) - 1 + u, ⟨hw0, hw1⟩⟩ : X)
          = (ψ (ψ.symm ⟨x, memV_of_not_memU hUV hxU⟩) : X) := by
            exact congrArg (fun z : OpenRealInterval 0 1 => (ψ z : X)) harg
      _ = x := by
            exact congrArg (fun z : {x : X // x ∈ V} => (z : X))
              (ψ.apply_symm_apply ⟨x, memV_of_not_memU hUV hxU⟩)

/-- `twoChartF` is the right inverse of `twoChartG`. -/
lemma twoChartF_comp_twoChartG {U V : Set X} {s u : ℝ} (hs0 : 0 < s) (hu : 0 < u)
    (hu1 : u ≤ 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hUV : U ∪ V = univ) (y : OpenRealInterval 0 (2 - u)) :
    twoChartF hu1 φ ψ hUend hUV (twoChartG hs0 hu φ ψ y) = y := by
  apply Subtype.ext
  by_cases hy1 : (y : ℝ) < 1
  · have hGy : twoChartG hs0 hu φ ψ y = (φ ⟨(y : ℝ), ⟨y.2.1, hy1⟩⟩ : X) :=
      twoChartG_apply_lt_one hs0 hu φ ψ hy1
    have hGU : twoChartG hs0 hu φ ψ y ∈ U := by
      rw [hGy]
      exact (φ ⟨(y : ℝ), ⟨y.2.1, hy1⟩⟩ : {x : X // x ∈ U}).2
    dsimp [twoChartF]
    rw [dif_pos hGU]
    have harg : (⟨twoChartG hs0 hu φ ψ y, hGU⟩ : {x : X // x ∈ U}) = φ ⟨(y : ℝ), ⟨y.2.1, hy1⟩⟩ := by
      apply Subtype.ext
      exact hGy
    calc
      ((φ.symm ⟨twoChartG hs0 hu φ ψ y, hGU⟩ : OpenRealInterval 0 1) : ℝ)
          = ((φ.symm (φ ⟨(y : ℝ), ⟨y.2.1, hy1⟩⟩) : OpenRealInterval 0 1) : ℝ) := by
            exact congrArg (fun z : {x : X // x ∈ U} => ((φ.symm z : OpenRealInterval 0 1) : ℝ)) harg
      _ = ((⟨(y : ℝ), ⟨y.2.1, hy1⟩⟩ : OpenRealInterval 0 1) : ℝ) := by
            simpa using congrArg (fun z : OpenRealInterval 0 1 => (z : ℝ))
              (φ.symm_apply_apply ⟨(y : ℝ), ⟨y.2.1, hy1⟩⟩)
      _ = (y : ℝ) := rfl
  · have hGy : twoChartG hs0 hu φ ψ y = (ψ ⟨(y : ℝ) - 1 + u, ⟨by
        have hge : 1 ≤ (y : ℝ) := le_of_not_gt hy1
        have hw0 : 0 < (y : ℝ) - 1 + u := by linarith [hge, hu]
        exact hw0, by
        have hw1 : (y : ℝ) - 1 + u < 1 := by linarith [y.2.2]
        exact hw1⟩⟩ : X) := twoChartG_apply_ge_one hs0 hu φ ψ hy1
    have hnotGU : twoChartG hs0 hu φ ψ y ∉ U := by
      rw [hGy]
      intro hU
      have hwu : (y : ℝ) - 1 + u ∈ Set.Ioo 0 u := by
        exact (hUend ⟨(y : ℝ) - 1 + u, ⟨by
          have hge : 1 ≤ (y : ℝ) := le_of_not_gt hy1
          have hw0 : 0 < (y : ℝ) - 1 + u := by linarith [hge, hu]
          exact hw0, by
          have hw1 : (y : ℝ) - 1 + u < 1 := by linarith [y.2.2]
          exact hw1⟩⟩).1 hU
      have hgeu : u ≤ (y : ℝ) - 1 + u := by linarith [le_of_not_gt hy1]
      exact (not_lt_of_ge hgeu) hwu.2
    dsimp [twoChartF]
    rw [dif_neg hnotGU]
    have harg : (⟨twoChartG hs0 hu φ ψ y, memV_of_not_memU hUV hnotGU⟩ : {x : X // x ∈ V}) =
        ψ ⟨(y : ℝ) - 1 + u, ⟨by
          have hge : 1 ≤ (y : ℝ) := le_of_not_gt hy1
          have hw0 : 0 < (y : ℝ) - 1 + u := by linarith [hge, hu]
          exact hw0, by
          have hw1 : (y : ℝ) - 1 + u < 1 := by linarith [y.2.2]
          exact hw1⟩⟩ := by
      apply Subtype.ext
      exact hGy
    calc
      ((ψ.symm ⟨twoChartG hs0 hu φ ψ y, memV_of_not_memU hUV hnotGU⟩ : OpenRealInterval 0 1) : ℝ) + 1 - u
          = ((ψ.symm (ψ ⟨(y : ℝ) - 1 + u, ⟨by
              have hge : 1 ≤ (y : ℝ) := le_of_not_gt hy1
              have hw0 : 0 < (y : ℝ) - 1 + u := by linarith [hge, hu]
              exact hw0, by
              have hw1 : (y : ℝ) - 1 + u < 1 := by linarith [y.2.2]
              exact hw1⟩⟩) : OpenRealInterval 0 1) : ℝ) + 1 - u := by
              exact congrArg (fun r : ℝ => r + 1 - u)
                (congrArg (fun z : {x : X // x ∈ V} => ((ψ.symm z : OpenRealInterval 0 1) : ℝ)) harg)
      _ = ((⟨(y : ℝ) - 1 + u, ⟨by
              have hge : 1 ≤ (y : ℝ) := le_of_not_gt hy1
              have hw0 : 0 < (y : ℝ) - 1 + u := by linarith [hge, hu]
              exact hw0, by
              have hw1 : (y : ℝ) - 1 + u < 1 := by linarith [y.2.2]
              exact hw1⟩⟩ : OpenRealInterval 0 1) : ℝ) + 1 - u := by
              simpa using congrArg (fun z : OpenRealInterval 0 1 => (z : ℝ))
                (ψ.symm_apply_apply ⟨(y : ℝ) - 1 + u, ⟨by
                  have hge : 1 ≤ (y : ℝ) := le_of_not_gt hy1
                  have hw0 : 0 < (y : ℝ) - 1 + u := by linarith [hge, hu]
                  exact hw0, by
                  have hw1 : (y : ℝ) - 1 + u < 1 := by linarith [y.2.2]
                  exact hw1⟩⟩)
      _ = (y : ℝ) := by ring_nf

/-- **The two-chart gluing theorem**: two open-interval charts of a space
whose overlap is the right end of one and the left end of the other
(facing, orientation-preserving) cover a space homeomorphic to an open
real interval.  `twoChartF` and `twoChartG` are mutual inverses
(`twoChartF_comp_twoChartG`, `twoChartG_comp_twoChartF`), both
continuous (`twoChartF_continuous`, `twoChartG_continuous`). -/
theorem two_chart_glue_homeo {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hUopen : IsOpen U) (hVopen : IsOpen V)
    {s u : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hu : 0 < u) (hu1s : u < 1)
    (φ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((φ t) : X) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hinc : ∀ ⦃v₁ v₂ : ℝ⦄, v₁ ∈ Set.Ioo 0 u → v₂ ∈ Set.Ioo 0 u → v₁ < v₂ →
        Tfun (le_of_lt hu1s) φ ψ hUend v₁ < Tfun (le_of_lt hu1s) φ ψ hUend v₂)
    (hUV : U ∪ V = univ) :
    Nonempty (X ≃ₜ OpenRealInterval 0 (2 - u)) := by
  let hu1 : u ≤ 1 := le_of_lt hu1s
  let F : X → OpenRealInterval 0 (2 - u) := twoChartF hu1 φ ψ hUend hUV
  let G : OpenRealInterval 0 (2 - u) → X := twoChartG hs0 hu φ ψ
  have hcF : Continuous F := by
    dsimp [F]
    exact twoChartF_continuous hUopen hVopen hs0 hu hu1 φ ψ hVend hUend hinc hUV
  have hcG : Continuous G := by
    dsimp [G]
    exact twoChartG_continuous hs0 hs1 hu hu1s φ ψ hVend hUend hinc
  let e : X ≃ OpenRealInterval 0 (2 - u) := ⟨F, G,
    (fun x => by
      dsimp [F, G]
      exact twoChartG_comp_twoChartF hs0 hu hu1 φ ψ hUend hUV x),
    (fun y => by
      dsimp [F, G]
      exact twoChartF_comp_twoChartG hs0 hu hu1 φ ψ hUend hUV y)⟩
  exact ⟨Homeomorph.mk e (by simpa [e] using hcF) (by simpa [e] using hcG)⟩

/-! ## Finite chains of real intervals (S158: coordinate model of the
sweep) -/

/-- A finite chain of open real intervals with consecutive overlaps has
an open-interval union: the coordinate model of the interval side of the
sweep (on `ℝ` there is no wrapping, so consecutive overlaps suffice). -/
theorem range_chain_union_interval (n : ℕ) (I : ℕ → Set ℝ)
    (hI : ∀ j, j < n + 1 → ∃ a b : ℝ, I j = Set.Ioo a b)
    (hchain : ∀ j, j < n → (I j ∩ I (j + 1)).Nonempty) :
    ∃ a b : ℝ, (⋃ j ∈ Finset.range (n + 1), I j) = Set.Ioo a b := by
  induction n with
  | zero =>
      rcases hI 0 (by omega) with ⟨a, b, hI0⟩
      refine ⟨a, b, ?_⟩
      simp [Finset.range_one, hI0]
  | succ n ih =>
      have hIn : ∀ j, j < n + 1 → ∃ a b : ℝ, I j = Set.Ioo a b := by
        intro j hj
        exact hI j (by omega)
      have hch : ∀ j, j < n → (I j ∩ I (j + 1)).Nonempty := by
        intro j hj
        exact hchain j (by omega)
      rcases ih hIn hch with ⟨lo, hi, hU⟩
      rcases hI (n + 1) (by omega) with ⟨a, b, hI1⟩
      have hmemIn : I n ⊆ (⋃ j ∈ Finset.range (n + 1), I j) := by
        intro x hx
        exact Set.mem_iUnion₂.mpr ⟨n, Finset.mem_range.mpr (by omega), hx⟩
      have hov : (Set.Ioo lo hi ∩ Set.Ioo a b).Nonempty := by
        rcases hchain n (by omega) with ⟨x, hx1, hx2⟩
        have hxU : x ∈ Set.Ioo lo hi := by
          rw [← hU]
          exact hmemIn hx1
        have hx2' : x ∈ Set.Ioo a b := by
          rwa [hI1] at hx2
        exact ⟨x, hxU, hx2'⟩
      rcases union_Ioo_of_overlap hov with ⟨l, h, hUunion⟩
      refine ⟨l, h, ?_⟩
      calc
        (⋃ j ∈ Finset.range (n + 2), I j)
            = (⋃ j ∈ Finset.range (n + 1), I j) ∪ I (n + 1) := by
              ext x
              constructor
              · intro hx
                rcases Set.mem_iUnion₂.mp hx with ⟨j, hj, hxj⟩
                have hjlt : j < n + 2 := Finset.mem_range.mp hj
                by_cases hjn : j < n + 1
                · exact Or.inl (Set.mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr hjn, hxj⟩)
                · have hj' : j = n + 1 := by omega
                  exact Or.inr (by simpa [hj'] using hxj)
              · intro hx
                rcases hx with hx1 | hx2
                · rcases Set.mem_iUnion₂.mp hx1 with ⟨j, hj, hxj⟩
                  have hjlt : j < n + 1 := Finset.mem_range.mp hj
                  exact Set.mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr (by omega), hxj⟩
                · exact Set.mem_iUnion₂.mpr ⟨n + 1, Finset.mem_range.mpr (by omega), hx2⟩
        _ = Set.Ioo l h := by
              rw [hU, hI1]
              exact hUunion

/-! ## The single-junction extension lemma (S158) -/

/-- **Subset reassociation homeo**: a subset `U ⊆ W` read as a subtype
of the ambient space and as a subtype of the `W`-subtype are the same
topological space (the identity on values).  (Generalises the
union-subtype reassociation: both chart reassociations of the
single-junction extension use one instance with `W := U ∪ V` and the
two inclusions `U ⊆ U∪V`, `V ⊆ U∪V`.) -/
noncomputable def unionSubtypeHomeo {Y : Type*} [TopologicalSpace Y] {U W : Set Y}
    (hsub : U ⊆ W) : {y : Y // y ∈ U} ≃ₜ
      {z : {x : Y // x ∈ W} // (z : Y) ∈ U} where
  toFun := fun y => ⟨⟨(y : Y), hsub y.2⟩, y.2⟩
  invFun := fun z => ⟨((z : {x : Y // x ∈ W}) : Y), z.2⟩
  left_inv := by intro y; rfl
  right_inv := by intro z; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-! ## The single-junction extension lemma (S158) -/

theorem single_junction_extension {Y : Type*} [TopologicalSpace Y] {U V : Set Y}
    (hUopen : IsOpen U) (hVopen : IsOpen V)
    {s u : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hu : 0 < u) (hu1s : u < 1)
    (η : OpenRealInterval 0 1 ≃ₜ {y : Y // y ∈ U})
    (ψ : OpenRealInterval 0 1 ≃ₜ {y : Y // y ∈ V})
    (hVend : ∀ t : OpenRealInterval 0 1, ((η t) : Y) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ψ t) : Y) ∈ U ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hinc : ∀ ⦃v₁ v₂ : ℝ⦄, v₁ ∈ Set.Ioo 0 u → v₂ ∈ Set.Ioo 0 u → v₁ < v₂ →
        Tfun (le_of_lt hu1s) η ψ hUend v₁ < Tfun (le_of_lt hu1s) η ψ hUend v₂) :
    Nonempty ({z : Y // z ∈ U ∪ V} ≃ₜ OpenRealInterval 0 (2 - u)) := by
  let hu1 : u ≤ 1 := le_of_lt hu1s
  let X := {z : Y // z ∈ U ∪ V}
  let U' : Set X := {z : X | (z : Y) ∈ U}
  let V' : Set X := {z : X | (z : Y) ∈ V}
  have hU'open : IsOpen U' := by
    dsimp [U']
    exact hUopen.preimage continuous_subtype_val
  have hV'open : IsOpen V' := by
    dsimp [V']
    exact hVopen.preimage continuous_subtype_val
  have hUV' : U' ∪ V' = univ := by
    ext z
    constructor
    · intro hz; exact trivial
    · intro hz
      rcases z.2 with hU | hV
      · exact Or.inl (by simpa [U'] using hU)
      · exact Or.inr (by simpa [V'] using hV)
  let reassocU : {y : Y // y ∈ U} ≃ₜ {z : {x : Y // x ∈ U ∪ V} // (z : Y) ∈ U} :=
    unionSubtypeHomeo (U := U) (W := U ∪ V) (by intro y hy; exact Or.inl hy)
  let reassocV : {y : Y // y ∈ V} ≃ₜ {z : {x : Y // x ∈ U ∪ V} // (z : Y) ∈ V} :=
    unionSubtypeHomeo (U := V) (W := U ∪ V) (by intro y hy; exact Or.inr hy)
  let η' : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U'} := η.trans reassocU
  let ψ' : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V'} := ψ.trans reassocV
  have hxU : ∀ t : OpenRealInterval 0 1,
      (((η' t : {x : X // x ∈ U'}) : X) : Y) = ((η t : {y : Y // y ∈ U}) : Y) := by
    intro t
    dsimp [η', reassocU]
    rfl
  have hxV : ∀ t : OpenRealInterval 0 1,
      (((ψ' t : {x : X // x ∈ V'}) : X) : Y) = ((ψ t : {y : Y // y ∈ V}) : Y) := by
    intro t
    dsimp [ψ', reassocV]
    rfl
  have hVend' : ∀ t : OpenRealInterval 0 1, ((η' t : {x : X // x ∈ U'}) : X) ∈ V' ↔
      (t : ℝ) ∈ Set.Ioo s 1 := by
    intro t
    constructor
    · intro ht
      have hval : (((η' t : {x : X // x ∈ U'}) : X) : Y) ∈ V := by
        simpa [V'] using ht
      have hyt : ((η t : {y : Y // y ∈ U}) : Y) ∈ V := by
        simpa [hxU t] using hval
      exact (hVend t).1 hyt
    · intro hyt
      have hval : (((η' t : {x : X // x ∈ U'}) : X) : Y) ∈ V := by
        simpa [hxU t] using ((hVend t).2 hyt)
      simpa [V'] using hval
  have hUend' : ∀ t : OpenRealInterval 0 1, ((ψ' t : {x : X // x ∈ V'}) : X) ∈ U' ↔
      (t : ℝ) ∈ Set.Ioo 0 u := by
    intro t
    constructor
    · intro ht
      have hval : (((ψ' t : {x : X // x ∈ V'}) : X) : Y) ∈ U := by
        simpa [U'] using ht
      have hyt : ((ψ t : {y : Y // y ∈ V}) : Y) ∈ U := by
        simpa [hxV t] using hval
      exact (hUend t).1 hyt
    · intro hyt
      have hval : (((ψ' t : {x : X // x ∈ V'}) : X) : Y) ∈ U := by
        simpa [hxV t] using ((hUend t).2 hyt)
      simpa [U'] using hval
  -- invariance of the transition coordinate under reassociation:
  have hTfun : ∀ {v : ℝ} (hv : v ∈ Set.Ioo 0 u),
      Tfun hu1 η' ψ' hUend' v = Tfun hu1 η ψ hUend v := by
    intro v hv
    rw [Tfun_eq hu1 η' ψ' hUend' hv, Tfun_eq hu1 η ψ hUend hv]
    dsimp [T, η', ψ', reassocU, reassocV, unionSubtypeHomeo]

  have hinc' : ∀ ⦃v₁ v₂ : ℝ⦄, v₁ ∈ Set.Ioo 0 u → v₂ ∈ Set.Ioo 0 u → v₁ < v₂ →
      Tfun (le_of_lt hu1s) η' ψ' hUend' v₁ < Tfun (le_of_lt hu1s) η' ψ' hUend' v₂ := by
    intro v₁ v₂ hv₁ hv₂ hvlt
    have h1 := hinc hv₁ hv₂ hvlt
    -- rewrite Tfun η' ψ' hUend' → Tfun η ψ hUend on both sides via hTfun
    rwa [hTfun hv₁, hTfun hv₂]
  exact two_chart_glue_homeo hU'open hV'open hs0 hs1 hu hu1s η' ψ' hVend' hUend' hinc' hUV'

/-! ## The prefix-union step (S159) -/

-- normalization: (0, 2-u) ≃ (0,1) via L30 (affine)
lemma norm01 {u : ℝ} (hu1s : u < 1) : Nonempty (OpenRealInterval 0 (2 - u) ≃ₜ OpenRealInterval 0 1) := by
  have hpos : 0 < 2 - u := by linarith
  exact Commons.Topology.Homeomorph.open_interval_affine hpos (by norm_num)

/-- **S159 base+first-step**: two open traces `T₀ T₁` of an ambient
space with interval charts `η₀ η₁` whose overlap is the facing terminal
pair (right end `(s,1)` of `T₀`, left end `(0,u)` of `T₁` in
coordinates, monotone transition) glue to a single interval chart of the
prefix union: `{z | z ∈ T₀ ∪ T₁} ≃ₜ OpenRealInterval 0 1`. -/
theorem prefix_two_charts_interval {Y : Type*} [TopologicalSpace Y]
    (T₀ T₁ : Set Y) (hT₀open : IsOpen T₀) (hT₁open : IsOpen T₁)
    {s u : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hu : 0 < u) (hu1s : u < 1)
    (η₀ : OpenRealInterval 0 1 ≃ₜ {y : Y // y ∈ T₀})
    (η₁ : OpenRealInterval 0 1 ≃ₜ {y : Y // y ∈ T₁})
    (hVend : ∀ t : OpenRealInterval 0 1, ((η₀ t) : Y) ∈ T₁ ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((η₁ t) : Y) ∈ T₀ ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hinc : ∀ ⦃v₁ v₂ : ℝ⦄, v₁ ∈ Set.Ioo 0 u → v₂ ∈ Set.Ioo 0 u → v₁ < v₂ →
        Tfun (le_of_lt hu1s) η₀ η₁ hUend v₁ < Tfun (le_of_lt hu1s) η₀ η₁ hUend v₂) :
    Nonempty ({z : Y // z ∈ T₀ ∪ T₁} ≃ₜ OpenRealInterval 0 1) := by
  rcases single_junction_extension (U := T₀) (V := T₁) hT₀open hT₁open hs0 hs1 hu hu1s
      η₀ η₁ hVend hUend hinc with ⟨hmid⟩
  rcases norm01 (u := u) hu1s with ⟨hnorm⟩
  exact ⟨hmid.trans hnorm⟩

/-! ## The abstract chain step (S159) -/

/-- Reassociation along a set equality. -/
noncomputable def setEqSubtypeHomeo {Y : Type*} [TopologicalSpace Y] {s t : Set Y} (h : s = t) :
    {z : Y // z ∈ s} ≃ₜ {z : Y // z ∈ t} where
  toFun := fun z => ⟨(z : Y), by rw [← h]; exact z.2⟩
  invFun := fun z => ⟨(z : Y), by rw [h]; exact z.2⟩
  left_inv := by intro z; rfl
  right_inv := by intro z; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- range (k+2) splits into range (k+1) and {k+1}. -/
lemma union_range_succ {Y : Type*} (T : ℕ → Set Y) (k : ℕ) :
    (⋃ j ∈ Finset.range (k + 2), T j) =
      (⋃ j ∈ Finset.range (k + 1), T j) ∪ T (k + 1) := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion₂.mp hx with ⟨j, hj, hxj⟩
    have hjlt : j < k + 2 := Finset.mem_range.mp hj
    by_cases hjn : j < k + 1
    · exact Or.inl (Set.mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr hjn, hxj⟩)
    · have hj' : j = k + 1 := by omega
      exact Or.inr (by simpa [hj'] using hxj)
  · intro hx
    rcases hx with hx1 | hx2
    · rcases Set.mem_iUnion₂.mp hx1 with ⟨j, hj, hxj⟩
      have hjlt : j < k + 1 := Finset.mem_range.mp hj
      exact Set.mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr (by omega), hxj⟩
    · exact Set.mem_iUnion₂.mpr ⟨k + 1, Finset.mem_range.mpr (by omega), hx2⟩

/-- **The abstract chain step (S159)**: the prefix union up to `k` is an
interval chart `κk`; the new trace `T (k+1)` attaches along a facing
terminal overlap (right end `(s,1)` of the prefix in `κk` coordinates,
left end `(0,u)` of the new chart, monotone transition).  Then the
prefix up to `k+1` is an interval chart. -/
theorem chain_step {Y : Type*} [TopologicalSpace Y] (T : ℕ → Set Y) (k : ℕ)
    (hUopen : IsOpen (⋃ j ∈ Finset.range (k + 1), T j))
    (hnewopen : IsOpen (T (k + 1)))
    {s u : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hu : 0 < u) (hu1s : u < 1)
    (κk : OpenRealInterval 0 1 ≃ₜ {z : Y // z ∈ ⋃ j ∈ Finset.range (k + 1), T j})
    (ηnew : OpenRealInterval 0 1 ≃ₜ {y : Y // y ∈ T (k + 1)})
    (hVend : ∀ t : OpenRealInterval 0 1, ((κk t) : Y) ∈ T (k + 1) ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ηnew t) : Y) ∈
        (⋃ j ∈ Finset.range (k + 1), T j) ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hinc : ∀ ⦃v₁ v₂ : ℝ⦄, v₁ ∈ Set.Ioo 0 u → v₂ ∈ Set.Ioo 0 u → v₁ < v₂ →
        Tfun (le_of_lt hu1s) κk ηnew hUend v₁ < Tfun (le_of_lt hu1s) κk ηnew hUend v₂) :
    Nonempty (OpenRealInterval 0 1 ≃ₜ {z : Y // z ∈ ⋃ j ∈ Finset.range (k + 2), T j}) := by
  let U : Set Y := ⋃ j ∈ Finset.range (k + 1), T j
  let V : Set Y := T (k + 1)
  rcases single_junction_extension (U := U) (V := V) hUopen hnewopen hs0 hs1 hu hu1s
      κk ηnew hVend hUend hinc with ⟨hmid⟩
  -- hmid : {z // z ∈ U ∪ V} ≃ₜ ORI 0 (2-u)
  have hnorm : Nonempty (OpenRealInterval 0 (2 - u) ≃ₜ OpenRealInterval 0 1) := by
    have hpos : 0 < 2 - u := by linarith
    exact Commons.Topology.Homeomorph.open_interval_affine hpos (by norm_num)
  rcases hnorm with ⟨hN⟩
  -- reassociate {z//z∈U∪V} to {z//z∈⋃range(k+2)} via the union-split equality
  have hsplit : (U ∪ V : Set Y) = (⋃ j ∈ Finset.range (k + 2), T j) := by
    dsimp [U, V]
    exact (union_range_succ T k).symm
  exact ⟨hN.symm.trans (hmid.symm.trans (setEqSubtypeHomeo hsplit))⟩

variable {Y : Type*} [TopologicalSpace Y]

/-- The prefix union `⋃ j ∈ range (k+1), T j` is open (finite union of
open traces). -/
lemma prefix_open (T : ℕ → Set Y) (hopen : ∀ j, IsOpen (T j)) (k : ℕ) :
    IsOpen (⋃ j ∈ Finset.range (k + 1), T j) := by
  induction k with
  | zero =>
      -- range 1 = {0}
      rw [show Finset.range (0 + 1) = {0} by simp]
      simp [hopen 0]
  | succ k ih =>
      rw [union_range_succ]
      exact ih.union (hopen (k + 1))

/-- Base case `k = 0`: the single trace `T 0` (chart `η 0`) is the
`(0+1)`-prefix interval. -/
theorem prefix_zero_interval (T : ℕ → Set Y)
    (η0 : OpenRealInterval 0 1 ≃ₜ {y : Y // y ∈ T 0}) :
    Nonempty (OpenRealInterval 0 1 ≃ₜ {z : Y // z ∈ ⋃ j ∈ Finset.range (0 + 1), T j}) := by
  have hsplit : (⋃ j ∈ Finset.range (0 + 1), T j) = T 0 := by
    simp [Finset.range_one]
  exact ⟨η0.trans (setEqSubtypeHomeo (hsplit.symm))⟩

/-- The chain step with prefix-openness derived from the per-trace
openness. -/
theorem chain_step_open (T : ℕ → Set Y) (k : ℕ) (hopen : ∀ j, IsOpen (T j))
    {s u : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hu : 0 < u) (hu1s : u < 1)
    (κk : OpenRealInterval 0 1 ≃ₜ {z : Y // z ∈ ⋃ j ∈ Finset.range (k + 1), T j})
    (ηnew : OpenRealInterval 0 1 ≃ₜ {y : Y // y ∈ T (k + 1)})
    (hVend : ∀ t : OpenRealInterval 0 1, ((κk t) : Y) ∈ T (k + 1) ↔ (t : ℝ) ∈ Set.Ioo s 1)
    (hUend : ∀ t : OpenRealInterval 0 1, ((ηnew t) : Y) ∈
        (⋃ j ∈ Finset.range (k + 1), T j) ↔ (t : ℝ) ∈ Set.Ioo 0 u)
    (hinc : ∀ ⦃v₁ v₂ : ℝ⦄, v₁ ∈ Set.Ioo 0 u → v₂ ∈ Set.Ioo 0 u → v₁ < v₂ →
        Tfun (le_of_lt hu1s) κk ηnew hUend v₁ < Tfun (le_of_lt hu1s) κk ηnew hUend v₂) :
    Nonempty (OpenRealInterval 0 1 ≃ₜ {z : Y // z ∈ ⋃ j ∈ Finset.range (k + 2), T j}) :=
  chain_step T k (prefix_open T hopen k) (hopen (k + 1)) hs0 hs1 hu hu1s κk ηnew hVend hUend hinc

/-- **The finite-chain interval theorem (S160)**: given interval charts
of every trace and, at each level, the facing terminal-overlap data
stated against the current prefix homeo, every prefix union
`⋃ j ∈ range (k+1), T j` is an open real interval chart. -/
theorem finite_prefix_interval (T : ℕ → Set Y) (hopen : ∀ j, IsOpen (T j))
    (η : ∀ j, OpenRealInterval 0 1 ≃ₜ {y : Y // y ∈ T j})
    (hdata : ∀ k : ℕ,
        ∀ κk : OpenRealInterval 0 1 ≃ₜ {z : Y // z ∈ ⋃ j ∈ Finset.range (k + 1), T j},
          ∃ s u : ℝ, ∃ hs0 : 0 < s, ∃ hs1 : s < 1, ∃ hu : 0 < u, ∃ hu1s : u < 1,
            ∃ ηnew : OpenRealInterval 0 1 ≃ₜ {y : Y // y ∈ T (k + 1)},
            ∃ hUend : (∀ t : OpenRealInterval 0 1, ((ηnew t) : Y) ∈
                  (⋃ j ∈ Finset.range (k + 1), T j) ↔ (t : ℝ) ∈ Set.Ioo 0 u),
              (∀ t : OpenRealInterval 0 1, ((κk t) : Y) ∈ T (k + 1) ↔ (t : ℝ) ∈ Set.Ioo s 1) ∧
              (∀ ⦃v₁ v₂ : ℝ⦄, v₁ ∈ Set.Ioo 0 u → v₂ ∈ Set.Ioo 0 u → v₁ < v₂ →
                  Tfun (u := u) (le_of_lt hu1s) κk ηnew hUend v₁ <
                  Tfun (u := u) (le_of_lt hu1s) κk ηnew hUend v₂)) :
    ∀ k : ℕ, Nonempty (OpenRealInterval 0 1 ≃ₜ
      {z : Y // z ∈ ⋃ j ∈ Finset.range (k + 1), T j}) := by
  intro k
  induction k with
  | zero =>
      exact prefix_zero_interval T (η 0)
  | succ k ih =>
      classical
      rcases ih with ⟨κk⟩
      rcases hdata k κk with ⟨s, u, hs0, hs1, hu, hu1s, ηnew, hU, hV, hinc⟩
      exact chain_step_open T k hopen hs0 hs1 hu hu1s κk ηnew hV hU hinc


/-- The interval-side growth atom (S161): if the new trace `T (k+1)` is
an interval chart whose overlap with the prefix
`⋃ j ∈ range (k+1), T j` is the LEFT terminal interval `(0,u)` of the
new chart with `u < 1`, then the new trace contains a point outside the
prefix — every facing-terminal chain step strictly grows the prefix
union.  This is the wrap/dichotomy marker: inside a compact ambient
(where some prefix already equals the whole space by open-cover
compactness) the facing-terminal chain data can never hold indefinitely,
so an infinite interval chain is the certificate of the NON-compact
(interval) side. -/
lemma prefix_proper_growth {Y : Type*} [TopologicalSpace Y] (T : ℕ → Set Y) (k : ℕ)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (ηnew : OpenRealInterval 0 1 ≃ₜ {y : Y // y ∈ T (k + 1)})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ηnew t) : Y) ∈
        (⋃ j ∈ Finset.range (k + 1), T j) ↔ (t : ℝ) ∈ Set.Ioo 0 u) :
    ∃ x : Y, x ∈ T (k + 1) ∧ x ∉ ⋃ j ∈ Finset.range (k + 1), T j := by
  let tv : ℝ := (1 + u) / 2
  have htv0 : 0 < tv := by dsimp [tv]; linarith
  have htv1 : tv < 1 := by dsimp [tv]; linarith
  have htvu : u < tv := by dsimp [tv]; linarith
  let z : {y : Y // y ∈ T (k + 1)} := ηnew ⟨tv, ⟨htv0, htv1⟩⟩
  refine ⟨(z : Y), ?mem, ?notin⟩
  · exact z.2
  · intro hx
    have htu : (tv : ℝ) ∈ Set.Ioo (0 : ℝ) u := (hUend ⟨tv, ⟨htv0, htv1⟩⟩).mp hx
    exact (not_lt_of_ge (le_of_lt htu.2)) htvu

/-- The compact wrap contradiction (S161): the facing-terminal chain
data (`hUend` with `u < 1`) cannot be supplied at a level `k` whose
prefix already covers the whole space — the prefix being full makes the
growth atom impossible (`prefix_proper_growth` finds a point of
`T (k+1)` outside the prefix, yet `T (k+1) ⊆ univ = prefix`).  This is
the precise sense in which a compact (circle) component is NOT
chainable: at the level where the prefixes absorb the space, the
facing-terminal assumption must fail — the new trace must attach at
both ends (wrap) instead. -/
lemma chain_data_fails_at_full_prefix {Y : Type*} [TopologicalSpace Y]
    (T : ℕ → Set Y) (k : ℕ)
    (hfull : (⋃ j ∈ Finset.range (k + 1), T j) = Set.univ)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (ηnew : OpenRealInterval 0 1 ≃ₜ {y : Y // y ∈ T (k + 1)})
    (hUend : ∀ t : OpenRealInterval 0 1, ((ηnew t) : Y) ∈
        (⋃ j ∈ Finset.range (k + 1), T j) ↔ (t : ℝ) ∈ Set.Ioo 0 u) : False := by
  rcases prefix_proper_growth T k hu0 hu1 ηnew hUend with ⟨x, _hxT, hxP⟩
  have hxP' : x ∈ ⋃ j ∈ Finset.range (k + 1), T j := by
    rw [hfull]
    trivial
  exact hxP hxP'

end LeanEval.KnotTheory.Quadrisecant
