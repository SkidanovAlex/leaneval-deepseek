import Mathlib
import ChallengeDeps
import Submission.TorusPathFollow

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

/-!
# Layer A (xvii) — path-following applications: parameters of zero-set
points, path lifts and their round trips

The chain machinery (`TorusPathFollow.lean`) transports *parameters* along
chains of charts; this module adds the **point side**: the
`ZeroSetPoint`-valued view in which a chart parametrises the zero set and a
path in `Z` is followed through charts.

1. **`chartParam c z hV`** — the parameter of a zero-set point `z` in the
   chart `c` (requires the point to lie in `c.V`): the inverse of the chart
   homeo.  Round-trips: `chartParam_spec` (`c.homeo` applied to the
   parameter recovers the point of `z`), `chartParam_point` (its torus
   value is `z`), `chartParam_lift` (`chartLift c (chartParam c z hV) =
   z`).
2. **path round trips** — for a continuous path `σ : ℝ → Z` (any interval,
   in particular a compact one) lying in the chart region(s), the lifted
   parameter path returns the original path:
   `chartLift_path_roundTrip` (single chart) and
   `chartChain_path_roundTrip` (a whole chain: for every `t`, the lift at
   the endpoint chart of the transported parameter of `σ t` equals `σ t`).
3. **`continuous_chartParam_path`** — the lifted parameter path is
   continuous (the chart homeo inverse is continuous and the point map is).
4. **junction consistency `chartParam_transition`** — the parameter of a
   zero-set point in chart `c₂` is exactly the transition-transport of its
   parameter in chart `c₁` (when the point lies in both neighbourhoods):
   the chart-boundary glue of path-following.

Everything here is elementary and verified (no axioms, no `sorry`).
-/

namespace LeanEval.KnotTheory.Quadrisecant

/-- The **parameter of a zero-set point in a chart**: `z : ZeroSetPoint r`
(a point of the trisecant zero set) whose torus value lies in `c.V` is sent
to the unique parameter of `c` describing it (`c.homeo.symm` applied to the
point). -/
noncomputable def chartParam {r : ℝ → Space} {p : KnotParamTriple}
    (c : ZeroSet1Chart r p) (z : ZeroSetPoint r) (hV : (z : KnotParamTriple) ∈ c.V) :
    ChartInterval c.lo c.hi :=
  c.homeo.symm ⟨(z : KnotParamTriple), ⟨z.2, hV⟩⟩

/-- The chart homeo applied to the parameter of `z` recovers the point of
`z` (with its zero-set membership and the `V`-membership). -/
lemma chartParam_spec {r : ℝ → Space} {p : KnotParamTriple}
    (c : ZeroSet1Chart r p) (z : ZeroSetPoint r) (hV : (z : KnotParamTriple) ∈ c.V) :
    c.homeo (chartParam c z hV) =
      ⟨(z : KnotParamTriple), ⟨z.2, hV⟩⟩ := by
  exact c.homeo.apply_symm_apply ⟨(z : KnotParamTriple), ⟨z.2, hV⟩⟩

/-- The torus value of the chart homeo at the parameter of `z` is the point
of `z`. -/
lemma chartParam_point {r : ℝ → Space} {p : KnotParamTriple}
    (c : ZeroSet1Chart r p) (z : ZeroSetPoint r) (hV : (z : KnotParamTriple) ∈ c.V) :
    (c.homeo (chartParam c z hV) : KnotParamTriple) = (z : KnotParamTriple) := by
  simpa using congrArg (fun w : {q0 : KnotParamTriple // q0 ∈ trisecantZeroSet r ∧ q0 ∈ c.V} =>
    (w : KnotParamTriple)) (chartParam_spec c z hV)

/-- The lift of the parameter of `z` is `z` itself (single-chart round
trip). -/
lemma chartParam_lift {r : ℝ → Space} {p : KnotParamTriple}
    (c : ZeroSet1Chart r p) (z : ZeroSetPoint r) (hV : (z : KnotParamTriple) ∈ c.V) :
    chartLift c (chartParam c z hV) = z := by
  apply Subtype.ext
  simpa [chartLift] using chartParam_point c z hV

/-- **Single-chart path round trip.**  For a continuous path `σ` in the
zero set whose every point lies in `c.V`, the lift of the lifted parameter
path is the original path (pointwise). -/
lemma chartLift_path_roundTrip {r : ℝ → Space} {p : KnotParamTriple}
    (c : ZeroSet1Chart r p) (σ : ℝ → ZeroSetPoint r)
    (hV : ∀ t : ℝ, (σ t : KnotParamTriple) ∈ c.V) :
    ∀ t : ℝ, chartLift c (chartParam c (σ t) (hV t)) = σ t := by
  intro t
  exact chartParam_lift c (σ t) (hV t)

/-- **Whole-chain path round trip.**  For a continuous path `σ` in the
zero set whose every point lies in every chart region of the chain (and in
`c.V`), the lift at the endpoint chart of the transported parameter of
`σ t` is `σ t` itself: following the point along the chain returns the
point. -/
lemma chartChain_path_roundTrip {r : ℝ → Space} {p : KnotParamTriple}
    (c : ZeroSet1Chart r p) (chain : ChartChain c) (σ : ℝ → ZeroSetPoint r)
    (hV₀ : ∀ t : ℝ, (σ t : KnotParamTriple) ∈ c.V)
    (hch : ∀ t : ℝ, (σ t : KnotParamTriple) ∈ chartChainVs c chain) :
    ∀ t : ℝ,
      chartLift (chartChainLast c chain).2
          (chartChainTransport c chain
            ⟨chartParam c (σ t) (hV₀ t),
              (by
                have hp := chartParam_point c (σ t) (hV₀ t)
                rw [hp]
                exact hch t)⟩) = σ t := by
  intro t
  rw [chartChain_lift c chain ⟨chartParam c (σ t) (hV₀ t),
    (by
      have hp := chartParam_point c (σ t) (hV₀ t)
      rw [hp]
      exact hch t)⟩]
  exact chartParam_lift c (σ t) (hV₀ t)

/-- **The lifted parameter path is continuous**: for a continuous path in
the zero set lying in `c.V`, the map `t ↦ chartParam c (σ t) (hV t)` is
continuous (the chart homeo inverse is continuous and the point-valued map
is).  The domain is an arbitrary topological space, so the statement applies
to real intervals and to compact subintervals alike. -/
lemma continuous_chartParam_path {r : ℝ → Space} {p : KnotParamTriple}
    (c : ZeroSet1Chart r p) {X : Type*} [TopologicalSpace X]
    {σ : X → ZeroSetPoint r} (hσ : Continuous σ)
    (hV : ∀ t : X, (σ t : KnotParamTriple) ∈ c.V) :
    Continuous (fun t : X => chartParam c (σ t) (hV t)) := by
  -- the point-valued map into the chart codomain is continuous (its value
  -- is the value of σ, which is continuous)
  have hpoint : Continuous (fun t : X =>
      (⟨(σ t : KnotParamTriple), ⟨(σ t).2, hV t⟩⟩ :
        {q0 : KnotParamTriple // q0 ∈ trisecantZeroSet r ∧ q0 ∈ c.V})) := by
    rw [continuous_def]
    intro U hUo
    rw [isOpen_induced_iff] at hUo
    rcases hUo with ⟨W, hWo, hUW⟩
    have hpre : (fun t : X =>
        (⟨(σ t : KnotParamTriple), ⟨(σ t).2, hV t⟩⟩ :
          {q0 : KnotParamTriple // q0 ∈ trisecantZeroSet r ∧ q0 ∈ c.V})) ⁻¹' U =
        (fun t : X => (σ t : KnotParamTriple)) ⁻¹' W := by
      ext t
      rw [← hUW]
      rfl
    rw [hpre]
    exact IsOpen.preimage (continuous_subtype_val.comp hσ) hWo
  -- the parameter is c.homeo.symm of the point
  change Continuous (fun t : X =>
      (c.homeo.symm (⟨(σ t : KnotParamTriple), ⟨(σ t).2, hV t⟩⟩ :
        {q0 : KnotParamTriple // q0 ∈ trisecantZeroSet r ∧ q0 ∈ c.V})))
  exact c.homeo.symm.continuous.comp hpoint

/-- **Junction consistency.**  When a zero-set point `z` lies in both
`c₁.V` and `c₂.V`, the parameter of `z` in `c₂` is exactly the
transition-transport of its parameter in `c₁`: crossing from chart `c₁` to
chart `c₂` at the shared point is consistent. -/
lemma chartParam_transition {r : ℝ → Space} {p₁ p₂ : KnotParamTriple}
    (c₁ : ZeroSet1Chart r p₁) (c₂ : ZeroSet1Chart r p₂) (z : ZeroSetPoint r)
    (h₁ : (z : KnotParamTriple) ∈ c₁.V) (h₂ : (z : KnotParamTriple) ∈ c₂.V) :
    ((chartTransitionHomeo c₁ c₂
        ⟨chartParam c₁ z h₁,
          (by
            have hp := chartParam_point c₁ z h₁
            rw [hp]
            exact h₂)⟩ : ChartTransitionDomain c₂ c₁) : ChartInterval c₂.lo c₂.hi) =
      chartParam c₂ z h₂ := by
  -- both parameters describe the point z: compare their chart-homeo images
  apply c₂.homeo.injective
  -- the transported parameter has chart image the point of z (transition
  -- preserves the point)
  have hp₁ := chartParam_point c₁ z h₁
  have htr : (c₂.homeo ((chartTransitionHomeo c₁ c₂
        ⟨chartParam c₁ z h₁,
          (by
            have hp := chartParam_point c₁ z h₁
            rw [hp]
            exact h₂)⟩ : ChartTransitionDomain c₂ c₁) : ChartInterval c₂.lo c₂.hi)).1 =
      (z : KnotParamTriple) := by
    have hq := chartTransition_preserves_point c₁ c₂
      ⟨chartParam c₁ z h₁,
        (by
          have hp := chartParam_point c₁ z h₁
          rw [hp]
          exact h₂)⟩
    -- hq : (c₂.homeo ((T …) : I₂)).1 = (c₁.homeo ⟨param₁, mem⟩.1).1
    -- the right-hand side is the point of z
    rw [hq]
    exact chartParam_point c₁ z h₁
  -- the image of the transported parameter is the point of z (as a chart
  -- point of c₂)
  have himg₁ : c₂.homeo ((chartTransitionHomeo c₁ c₂
        ⟨chartParam c₁ z h₁,
          (by
            have hp := chartParam_point c₁ z h₁
            rw [hp]
            exact h₂)⟩ : ChartTransitionDomain c₂ c₁) : ChartInterval c₂.lo c₂.hi) =
      ⟨(z : KnotParamTriple), ⟨z.2, h₂⟩⟩ := by
    apply Subtype.ext
    simpa using htr
  -- the image of the direct parameter is the same point
  have himg₂ : c₂.homeo (chartParam c₂ z h₂) = ⟨(z : KnotParamTriple), ⟨z.2, h₂⟩⟩ :=
    chartParam_spec c₂ z h₂
  simpa using himg₁.trans himg₂.symm

end LeanEval.KnotTheory.Quadrisecant

/-! ## 2. Path-following over a compact interval

A continuous path `σ` in the zero set on a compact interval `[a,b]`, all of
whose points lie in the chart regions of a chain from `c`, admits a
continuous parameter lift along the chain (`ChartChainLiftOnInterval`,
statement).  The **single-chart base case** is proved below
(`singleChart_pathLift`): within one chart the parameter lift is
`t ↦ chartParam c (σ t) …`, continuous by `continuous_chartParam_path`
and round-tripping by `chartParam_lift`.  The **one-step extension
agreement** (`chartParam_junction_agree`) records that at a junction time
`m` the parameter of `σ m` in the next chart is the transition-transport of
its parameter in the current chart — the local glue used when the chain is
grown one chart at a time (Lebesgue-number-style covering is the means of
building the chain; the base case and the junction are the two inductive
steps). -/

namespace LeanEval.KnotTheory.Quadrisecant

/-- A compact interval of real parameters, `[a,b]`. -/
abbrev CompactInterval (a b : ℝ) : Type := {t : ℝ // t ∈ Set.Icc a b}

/-- The chain-domain element describing the zero-set point `σ t` in the
first chart of the chain (the parameter together with the membership of the
point in all the chain's chart regions). -/
noncomputable def chainDomainParam {r : ℝ → Space} {p : KnotParamTriple}
    (c : ZeroSet1Chart r p) (chain : ChartChain c) {a b : ℝ}
    (σ : CompactInterval a b → ZeroSetPoint r) (t : CompactInterval a b)
    (hV₀ : (σ t : KnotParamTriple) ∈ c.V)
    (hch : (σ t : KnotParamTriple) ∈ chartChainVs c chain) :
    chartChainDomain c chain :=
  ⟨chartParam c (σ t) hV₀, by
    have hp := chartParam_point c (σ t) hV₀
    rw [hp]
    exact hch⟩

/-- **Compact-interval chain lift** (statement).  A continuous path
`σ : [a,b] → Z` whose points all lie in the first chart's neighbourhood and
in the chart regions of the whole chain has a continuous parameter lift
`τ : [a,b] → chartChainEnd c chain` that follows the composite transport
(τ t is the transported parameter of `σ t`) and whose lift at the endpoint
chart is the original path. -/
def ChartChainLiftOnInterval {r : ℝ → Space} {p : KnotParamTriple}
    (c : ZeroSet1Chart r p) (chain : ChartChain c) (a b : ℝ)
    (σ : CompactInterval a b → ZeroSetPoint r) (_hσ : Continuous σ)
    (hV₀ : ∀ t : CompactInterval a b, (σ t : KnotParamTriple) ∈ c.V)
    (hch : ∀ t : CompactInterval a b, (σ t : KnotParamTriple) ∈ chartChainVs c chain) :
    Prop :=
  ∃ τ : CompactInterval a b → chartChainEnd c chain,
    Continuous τ ∧
    ∀ t : CompactInterval a b,
      τ t = chartChainTransport c chain (chainDomainParam c chain σ t (hV₀ t) (hch t)) ∧
        chartLift (chartChainLast c chain).2 (τ t) = σ t

/-- **Single-chart base case.**  A continuous path in the zero set lying in
`c.V` lifts to a continuous parameter path in `c` whose lift is the
original path. -/
theorem singleChart_pathLift {r : ℝ → Space} {p : KnotParamTriple}
    (c : ZeroSet1Chart r p) (a b : ℝ) (σ : CompactInterval a b → ZeroSetPoint r)
    (hσ : Continuous σ) (hV : ∀ t : CompactInterval a b, (σ t : KnotParamTriple) ∈ c.V) :
    ∃ τ : CompactInterval a b → ChartInterval c.lo c.hi,
      Continuous τ ∧ ∀ t : CompactInterval a b, chartLift c (τ t) = σ t := by
  refine ⟨fun t => chartParam c (σ t) (hV t), ?_, ?_⟩
  · exact continuous_chartParam_path c hσ hV
  · intro t
    exact chartParam_lift c (σ t) (hV t)

/-- **The compact-interval chain lift holds for the trivial (single-chart)
chain**: the base case of the induction over the chain. -/
theorem ChartChainLiftOnInterval_nil {r : ℝ → Space} {p : KnotParamTriple}
    (c : ZeroSet1Chart r p) (a b : ℝ) (σ : CompactInterval a b → ZeroSetPoint r)
    (hσ : Continuous σ) (hV₀ : ∀ t : CompactInterval a b, (σ t : KnotParamTriple) ∈ c.V) :
    ChartChainLiftOnInterval c (ChartChain.nil c) a b σ hσ hV₀
      (fun t => Set.mem_univ (σ t : KnotParamTriple)) := by
  unfold ChartChainLiftOnInterval
  refine ⟨fun t => chartParam c (σ t) (hV₀ t), ?cont, ?props⟩
  · exact continuous_chartParam_path c hσ hV₀
  · intro t
    constructor
    · dsimp [chainDomainParam]
      rfl
    · exact chartParam_lift c (σ t) (hV₀ t)

/-- **One-step extension agreement (junction).**  At a junction time `m`
where the zero-set point `σ m` lies in both `c₁.V` and `c₂.V`, the
parameter of `σ m` in the next chart `c₂` is the transition-transport of
its parameter in the current chart `c₁`: the two parameter lifts agree at
the junction, so the chain can be grown one chart at a time. -/
theorem chartParam_junction_agree {r : ℝ → Space} {p₁ p₂ : KnotParamTriple}
    (c₁ : ZeroSet1Chart r p₁) (c₂ : ZeroSet1Chart r p₂) {a b : ℝ}
    (σ : CompactInterval a b → ZeroSetPoint r) (m : CompactInterval a b)
    (h₁ : (σ m : KnotParamTriple) ∈ c₁.V) (h₂ : (σ m : KnotParamTriple) ∈ c₂.V) :
    ((chartTransitionHomeo c₁ c₂
        ⟨chartParam c₁ (σ m) h₁,
          (by
            have hp := chartParam_point c₁ (σ m) h₁
            rw [hp]
            exact h₂)⟩ : ChartTransitionDomain c₂ c₁) : ChartInterval c₂.lo c₂.hi) =
      chartParam c₂ (σ m) h₂ :=
  chartParam_transition c₁ c₂ (σ m) h₁ h₂


/-! ## 3. The one-step extension (cons) of the compact-interval chain lift

`ChartChainLiftOnInterval_nil` (the base case) and the **cons step** proved
here complete the induction over the chain: a path lifting through the
chain `tail` from `c'` also lifts through the extended chain `cons c c'`
from `c`.  The lift is the *same* continuous map `τ'`; only the transport
equality changes: transporting the chain-domain parameter of `σ t` along
the extended chain is the tail transport of its single-transitioned
parameter, which by `chartParam_transition` is exactly the tail-chain
parameter of `σ t` (`chainDomainParam_cons_transport_eq`).  The two
auxiliary lemmas make the proof-irrelevant memberships flow through the
transition. -/

/-- The transition transport is insensitive to which membership proof of
the (same) point-in-`V` proposition is used. -/
lemma chartTransition_irrel_mem {r : ℝ → Space} {p₁ p₂ : KnotParamTriple}
    (c₁ : ZeroSet1Chart r p₁) (c₂ : ZeroSet1Chart r p₂)
    (u : ChartInterval c₁.lo c₁.hi) (h₁ h₂ : (c₁.homeo u).1 ∈ c₂.V) :
    ((chartTransitionHomeo c₁ c₂ ⟨u, h₁⟩ : ChartTransitionDomain c₂ c₁) : ChartInterval c₂.lo c₂.hi) =
      ((chartTransitionHomeo c₁ c₂ ⟨u, h₂⟩ : ChartTransitionDomain c₂ c₁) : ChartInterval c₂.lo c₂.hi) := by
  congr 1

/-- **Cons transport of the chain-domain parameter.**  Transporting the
chain-domain parameter of `σ t` along the extended chain `cons c c' tail`
gives the same tail-end parameter as transporting its parameter in `c'`
along `tail`: the single transition `c → c'` sends the parameter of `σ t`
in `c` to its parameter in `c'` (`chartParam_transition`). -/
lemma chainDomainParam_cons_transport_eq {r : ℝ → Space} {p₁ p₂ : KnotParamTriple}
    (c : ZeroSet1Chart r p₁) (c' : ZeroSet1Chart r p₂) (tail : ChartChain c')
    {a b : ℝ} (σ : CompactInterval a b → ZeroSetPoint r) (t : CompactInterval a b)
    (hV₀ : (σ t : KnotParamTriple) ∈ c.V)
    (h₁ : (σ t : KnotParamTriple) ∈ c'.V)
    (h₂ : (σ t : KnotParamTriple) ∈ chartChainVs c' tail) :
    chartChainTransport c (ChartChain.cons c c' tail)
        (chainDomainParam c (ChartChain.cons c c' tail) σ t hV₀ ⟨h₁, h₂⟩) =
      chartChainTransport c' tail (chainDomainParam c' tail σ t h₁ h₂) := by
  let z : chartChainDomain c (ChartChain.cons c c' tail) :=
    chainDomainParam c (ChartChain.cons c c' tail) σ t hV₀ ⟨h₁, h₂⟩
  change chartChainTransport c (ChartChain.cons c c' tail) z =
    chartChainTransport c' tail (chainDomainParam c' tail σ t h₁ h₂)
  let wd : chartChainDomain c' tail :=
    ⟨((chartTransitionHomeo c c' ⟨z.1, z.2.1⟩ : ChartTransitionDomain c' c) : ChartInterval c'.lo c'.hi), by
        have hq := chartTransition_preserves_point c c' ⟨z.1, z.2.1⟩
        rw [hq]
        exact z.2.2⟩
  have hdec : chartChainTransport c (ChartChain.cons c c' tail) z =
      chartChainTransport c' tail wd := chartChainTransport_cons c c' tail z
  -- the single-transition value equals the direct parameter of σ t in c'
  have hz1 : z.1 = chartParam c (σ t) hV₀ := by rfl
  have hw : (c.homeo (chartParam c (σ t) hV₀)).1 ∈ c'.V := hz1 ▸ z.2.1
  have htr := chartParam_transition c c' (σ t) hV₀ h₁
  have hstep : ((chartTransitionHomeo c c' ⟨z.1, z.2.1⟩ : ChartTransitionDomain c' c) : ChartInterval c'.lo c'.hi) =
      chartParam c' (σ t) h₁ := by
    calc
      ((chartTransitionHomeo c c' ⟨z.1, z.2.1⟩ : ChartTransitionDomain c' c) : ChartInterval c'.lo c'.hi)
          = ((chartTransitionHomeo c c' ⟨chartParam c (σ t) hV₀, hw⟩ : ChartTransitionDomain c' c) : ChartInterval c'.lo c'.hi) := by
              congr 1
      _ = ((chartTransitionHomeo c c' ⟨chartParam c (σ t) hV₀,
              (by have hp := chartParam_point c (σ t) hV₀; rw [hp]; exact h₁)⟩ : ChartTransitionDomain c' c) : ChartInterval c'.lo c'.hi) := by
              exact chartTransition_irrel_mem c c' (chartParam c (σ t) hV₀) hw
                (by have hp := chartParam_point c (σ t) hV₀; rw [hp]; exact h₁)
      _ = chartParam c' (σ t) h₁ := htr
  -- wd equals the tail chain-domain parameter of σ t
  have hwd : wd = chainDomainParam c' tail σ t h₁ h₂ := by
    apply Subtype.ext
    dsimp [wd, chainDomainParam]
    exact hstep
  exact hdec.trans (congrArg (chartChainTransport c' tail) hwd)

/-- **Compact-interval chain lift, one-step extension (cons).**  If the
path lifts through the tail chain `tail` from `c'` (whose first chart's
region contains every path point), then it also lifts through the extended
chain `cons c c' tail` from `c` — provided every path point also lies in
the region of the first chart `c` (the membership of the points in the
extended chain's corridor is `⟨h₁, h₂⟩`).  The lift is the same continuous
map `τ'`; the transport equality along the extended chain is the cons
transport lemma, and the endpoint chart of the extended chain is the
endpoint chart of the tail. -/
theorem ChartChainLiftOnInterval_cons {r : ℝ → Space} {p₁ p₂ : KnotParamTriple}
    (c : ZeroSet1Chart r p₁) (c' : ZeroSet1Chart r p₂) (tail : ChartChain c')
    (a b : ℝ) (σ : CompactInterval a b → ZeroSetPoint r) (hσ : Continuous σ)
    (hV₀ : ∀ t : CompactInterval a b, (σ t : KnotParamTriple) ∈ c.V)
    (h₁ : ∀ t : CompactInterval a b, (σ t : KnotParamTriple) ∈ c'.V)
    (h₂ : ∀ t : CompactInterval a b, (σ t : KnotParamTriple) ∈ chartChainVs c' tail)
    (hlift : ChartChainLiftOnInterval c' tail a b σ hσ h₁ h₂) :
    ChartChainLiftOnInterval c (ChartChain.cons c c' tail) a b σ hσ hV₀
      (fun t => ⟨h₁ t, h₂ t⟩) := by
  rcases hlift with ⟨τ', hτ', hprops⟩
  refine ⟨τ', hτ', ?_⟩
  intro t
  constructor
  · exact (hprops t).1.trans (chainDomainParam_cons_transport_eq c c' tail σ t (hV₀ t) (h₁ t) (h₂ t)).symm
  · change chartLift (chartChainLast c' tail).2 (τ' t) = σ t
    exact (hprops t).2


/-- **Compact-interval chain lift, full induction over a finite chain.**
A continuous path in the zero set over `[a,b]` whose points all lie in the
first chart's neighbourhood and in the chart regions of *every* chart of
the finite chain lifts to a continuous parameter path through the whole
chain: this is the inductive closure of the base case
(`ChartChainLiftOnInterval_nil`) and the one-step extension
(`ChartChainLiftOnInterval_cons`).  The induction is over the chain (whose
root chart changes at each `cons`), so the recursive hypothesis is applied
at the continuation chart `cnext` with the corridor memberships
`h₁ t := (hch t).1` (the point lies in the next chart's region) and
`h₂ t := (hch t).2` (it lies in the tail's corridor). -/
theorem ChartChainLiftOnInterval_chain {r : ℝ → Space} {p : KnotParamTriple}
    (c : ZeroSet1Chart r p) (chain : ChartChain c) (a b : ℝ)
    (σ : CompactInterval a b → ZeroSetPoint r) (hσ : Continuous σ)
    (hV₀ : ∀ t : CompactInterval a b, (σ t : KnotParamTriple) ∈ c.V)
    (hch : ∀ t : CompactInterval a b, (σ t : KnotParamTriple) ∈ chartChainVs c chain) :
    ChartChainLiftOnInterval c chain a b σ hσ hV₀ hch := by
  induction chain with
  | nil croot =>
      rcases ChartChainLiftOnInterval_nil croot a b σ hσ hV₀ with ⟨τ, hτ, hprops⟩
      refine ⟨τ, hτ, ?_⟩
      intro t
      constructor
      · exact (hprops t).1
      · exact (hprops t).2
  | cons croot cnext rest ih =>
      let h₁ : ∀ t : CompactInterval a b, (σ t : KnotParamTriple) ∈ cnext.V :=
        fun t => by simpa using (hch t).1
      let h₂ : ∀ t : CompactInterval a b, (σ t : KnotParamTriple) ∈ chartChainVs cnext rest :=
        fun t => by simpa using (hch t).2
      have hih : ChartChainLiftOnInterval cnext rest a b σ hσ h₁ h₂ := ih h₁ h₂
      exact ChartChainLiftOnInterval_cons croot cnext rest a b σ hσ hV₀ h₁ h₂ hih

end LeanEval.KnotTheory.Quadrisecant
