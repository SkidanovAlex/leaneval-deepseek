import Mathlib
import ChallengeDeps
import Submission.Torus1Chart

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

set_option maxHeartbeats 800000

/-!
# Layer A (xvi) — path-following along the trisecant zero set: chart chains

The zero set `Z = trisecantZeroSet r` of a general-position smooth knot is
covered by bundled 1-charts (`ZeroSet1Chart`, Layer A (xv)) whose
parametrisations agree on overlaps through the transition homeos
(`chartTransitionHomeo`, `chartLift_overlap`, S41–S42).  This module begins
the **global path-following** construction: moving a parameter along a
finite chain of overlapping charts.

1. **`ChartChain c`** — an inductive finite chain of bundled charts
   starting at `c`: `nil` is the trivial chain, `cons c' tail` steps to the
   chart `c'` and then follows `tail` from `c'`.
2. **`chartChainVs`** — the intersection of the neighbourhoods `V` of the
   charts of the chain (first chart excluded, since its own points already
   lie in its `V`); a parameter of the first chart is usable along the
   whole chain iff its zero-set point lies in every such `V`.
3. **`chartChainEnd` / `chartChainTransport`** — the endpoint type (the
   parameter interval of the last chart) and the **composite overlap
   transport**: given a parameter of the first chart whose point lies in
   every chart of the chain, transport it successively through the
   transition homeos to a parameter of the last chart describing the same
   zero-set point.
4. **two-step coherence** (`transport_twoStep_eq` and
   `chartLift_twoStep`): transporting through a middle chart and then on
   gives the same final parameter (and the same lift) as transporting
   directly — the local associativity/coherence on which the whole chain
   construction hangs.

Everything here is elementary and verified (no axioms, no `sorry`).
-/

namespace LeanEval.KnotTheory.Quadrisecant

/-! ## 1. Finite chart chains -/

/-- A **finite chain of bundled charts** starting at `c`: `nil` is the
trivial chain; `cons c' tail` continues from `c` to the chart `c'` and then
follows `tail` from `c'`.  (Consecutive charts need not overlap globally —
whether a parameter can travel the whole chain is a condition on the
parameter, expressed by `chartChainVs` below.) -/
inductive ChartChain {r : ℝ → Space} : {p : KnotParamTriple} → ZeroSet1Chart r p → Type
  | nil : {p : KnotParamTriple} → (c : ZeroSet1Chart r p) → ChartChain c
  | cons : {p p' : KnotParamTriple} → (c : ZeroSet1Chart r p) →
      (c' : ZeroSet1Chart r p') → ChartChain c' → ChartChain c

/-- The intersection of the neighbourhoods `V` of the charts of the chain
following the starting chart (the starting chart is excluded: the points of
its own parametrisation already lie in its `V`).  A point of the zero set
can be followed along the whole chain iff it lies in this set. -/
def chartChainVs {r : ℝ → Space} {p : KnotParamTriple} (c : ZeroSet1Chart r p) :
    ChartChain c → Set KnotParamTriple
  | .nil _ => Set.univ
  | .cons _ c' tail => {q : KnotParamTriple | q ∈ c'.V} ∩ chartChainVs c' tail

/-- The **last chart** of a chain from `c`: the endpoint chart of the chain
(`⟨p, c⟩` itself for the trivial chain). -/
noncomputable def chartChainLast {r : ℝ → Space} {p : KnotParamTriple}
    (c : ZeroSet1Chart r p) : ChartChain c → Sigma (fun q : KnotParamTriple => ZeroSet1Chart r q)
  | .nil _ => ⟨p, c⟩
  | .cons _ c' tail => chartChainLast c' tail

/-- The **endpoint type** of a chain from `c`: the parameter interval of
the last chart of the chain (`chartChainLast c chain`).  (An `abbrev` so
that the subspace typeclass instances on the endpoint interval reduce.) -/
noncomputable abbrev chartChainEnd {r : ℝ → Space} {p : KnotParamTriple}
    (c : ZeroSet1Chart r p) (chain : ChartChain c) : Type :=
  ChartInterval (chartChainLast c chain).2.lo (chartChainLast c chain).2.hi

/-- The **domain** of the composite transport along a chain from `c`: a
parameter of `c` whose zero-set point lies in the `V` of every chart of the
chain. -/
def chartChainDomain {r : ℝ → Space} {p : KnotParamTriple} (c : ZeroSet1Chart r p)
    (chain : ChartChain c) : Type :=
  {z : ChartInterval c.lo c.hi // (c.homeo z).1 ∈ chartChainVs c chain}

/-- **The composite overlap transport** along a chain: successively moving
a parameter through the transition homeos `chartTransitionHomeo` of each
consecutive pair of charts of the chain, ending with a parameter of the
last chart that describes the same zero-set point. -/
noncomputable def chartChainTransport {r : ℝ → Space} {p : KnotParamTriple}
    (c : ZeroSet1Chart r p) : ∀ (chain : ChartChain c),
    chartChainDomain c chain → chartChainEnd c chain
  | .nil _, z => z.1
  | .cons _ c' tail, z =>
      -- step from c to c' (the point of z lies in V_{c'} by z.2.1)
      let step : ChartTransitionDomain c' c := chartTransitionHomeo c c' ⟨z.1, z.2.1⟩
      -- continue along the tail: the point of step is the same as that of
      -- z (transition preserves the zero-set point), which lies in the
      -- remaining neighbourhoods by z.2.2
      let w : chartChainDomain c' tail :=
        ⟨step.1, by
          have hq := chartTransition_preserves_point c c' ⟨z.1, z.2.1⟩
          rw [hq]
          exact z.2.2⟩
      chartChainTransport c' tail w

end LeanEval.KnotTheory.Quadrisecant





/-! ## 2. Two-step coherence: transport through a middle chart equals
direct transport

The genuinely new local content of the chain construction: transporting a
parameter of chart `a` first to chart `b` and then on to chart `c` ends at
the **same parameter of `c`** as transporting directly `a → c`, whenever
the zero-set point lies in all three neighbourhoods.  Both transports are
"the parameter of `c` describing the given zero-set point", so equality is
forced by the bijectivity of the chart homeos; the proof records this
coherence at the level of the transition maps.  All chain-level statements
hang off this local associativity. -/

namespace LeanEval.KnotTheory.Quadrisecant

/-- The bundled transition homeo is (on values) the forward transition map
`chartTransitionTo`. -/
lemma chartTransitionHomeo_apply {r : ℝ → Space} {p₁ p₂ : KnotParamTriple}
    (a : ZeroSet1Chart r p₁) (c : ZeroSet1Chart r p₂) (x : ChartTransitionDomain a c) :
    (chartTransitionHomeo a c x : ChartTransitionDomain c a) = chartTransitionTo a c x := by
  rfl

/-- **Direct transport**: the parameter of `c` describing the same
zero-set point as the parameter `y` of `a` (whose point lies in `c.V`). -/
noncomputable def chartDirectParam {r : ℝ → Space} {p₁ p₂ : KnotParamTriple}
    (a : ZeroSet1Chart r p₁) (c : ZeroSet1Chart r p₂) (y : ChartTransitionDomain a c) :
    ChartInterval c.lo c.hi :=
  ((chartTransitionTo a c y) : ChartInterval c.lo c.hi)

/-- The direct parameter is `c.homeo.symm` applied to the zero-set point of
`y` (value unfolding of the direct transport). -/
lemma chartDirectParam_eq {r : ℝ → Space} {p₁ p₂ : KnotParamTriple}
    (a : ZeroSet1Chart r p₁) (c : ZeroSet1Chart r p₂) (u : ChartInterval a.lo a.hi)
    (hu : (a.homeo u).1 ∈ c.V) :
    chartDirectParam a c ⟨u, hu⟩ =
      (c.homeo.symm ⟨(a.homeo u).1, ⟨(a.homeo u).2.1, hu⟩⟩ : ChartInterval c.lo c.hi) := by
  dsimp [chartDirectParam]
  rw [chartTransitionTo_val a c ⟨u, hu⟩]

/-- After the first step of a two-step transport, the transported parameter
of `b` has its zero-set point in `c.V` (both describe the point of the
original parameter of `a`). -/
lemma chartTwoStep_mem {r : ℝ → Space} {p₁ p₂ p₃ : KnotParamTriple}
    (a : ZeroSet1Chart r p₁) (b : ZeroSet1Chart r p₂) (c : ZeroSet1Chart r p₃)
    (x : ChartTransitionDomain a b) (h : (a.homeo x.1).1 ∈ c.V) :
    (b.homeo (chartTransitionTo a b x).1).1 ∈ c.V := by
  have hq := chartTransition_preserves_point a b x
  have hq' : (b.homeo (chartTransitionTo a b x).1).1 = (a.homeo x.1).1 := by
    simpa [chartTransitionHomeo_apply a b x] using hq
  rw [hq']
  exact h

/-- **Two-step transport**: from `a` to the middle chart `b`, then from `b`
to `c`. -/
noncomputable def chartTwoStepParam {r : ℝ → Space} {p₁ p₂ p₃ : KnotParamTriple}
    (a : ZeroSet1Chart r p₁) (b : ZeroSet1Chart r p₂) (c : ZeroSet1Chart r p₃)
    (x : ChartTransitionDomain a b) (h : (a.homeo x.1).1 ∈ c.V) :
    ChartInterval c.lo c.hi :=
  chartDirectParam b c ⟨(chartTransitionTo a b x).1, chartTwoStep_mem a b c x h⟩

/-- The two-step parameter is `c.homeo.symm` applied to the zero-set point
of `x` (value unfolding of the two-step transport). -/
lemma chartTwoStepParam_eq {r : ℝ → Space} {p₁ p₂ p₃ : KnotParamTriple}
    (a : ZeroSet1Chart r p₁) (b : ZeroSet1Chart r p₂) (c : ZeroSet1Chart r p₃)
    (x : ChartTransitionDomain a b) (h : (a.homeo x.1).1 ∈ c.V) :
    chartTwoStepParam a b c x h =
      (c.homeo.symm ⟨(a.homeo x.1).1, ⟨(a.homeo x.1).2.1, h⟩⟩ : ChartInterval c.lo c.hi) := by
  dsimp [chartTwoStepParam]
  rw [chartDirectParam_eq b c (chartTransitionTo a b x).1 (chartTwoStep_mem a b c x h)]
  congr 1
  apply Subtype.ext
  have hq := chartTransition_preserves_point a b x
  have hq' : (b.homeo (chartTransitionTo a b x).1).1 = (a.homeo x.1).1 := by
    simpa [chartTransitionHomeo_apply a b x] using hq
  simpa using hq'

/-- **Two-step coherence (parameters).**  For a parameter `x` of `a` whose
zero-set point lies in both `b.V` and `c.V`, the two-step transport through
the middle chart `b` ends at the same parameter of `c` as the direct
transport `a → c`. -/
lemma transport_twoStep_eq {r : ℝ → Space} {p₁ p₂ p₃ : KnotParamTriple}
    (a : ZeroSet1Chart r p₁) (b : ZeroSet1Chart r p₂) (c : ZeroSet1Chart r p₃)
    (x : ChartTransitionDomain a b) (h : (a.homeo x.1).1 ∈ c.V) :
    chartTwoStepParam a b c x h = chartDirectParam a c ⟨x.1, h⟩ := by
  have h₂ := chartTwoStepParam_eq a b c x h
  have h₁ := chartDirectParam_eq a c x.1 h
  calc
    chartTwoStepParam a b c x h
        = (c.homeo.symm ⟨(a.homeo x.1).1, ⟨(a.homeo x.1).2.1, h⟩⟩ : ChartInterval c.lo c.hi) := h₂
    _ = chartDirectParam a c ⟨x.1, h⟩ := h₁.symm

/-- **Two-step coherence (lifts).**  The single-chart lift of the two-step
parameter equals the lift of the direct parameter: following a zero-set
point through a chain of charts does not change the point itself. -/
lemma chartLift_twoStep {r : ℝ → Space} {p₁ p₂ p₃ : KnotParamTriple}
    (a : ZeroSet1Chart r p₁) (b : ZeroSet1Chart r p₂) (c : ZeroSet1Chart r p₃)
    (x : ChartTransitionDomain a b) (h : (a.homeo x.1).1 ∈ c.V) :
    chartLift c (chartTwoStepParam a b c x h) = chartLift c (chartDirectParam a c ⟨x.1, h⟩) := by
  rw [transport_twoStep_eq a b c x h]

end LeanEval.KnotTheory.Quadrisecant

/-! ## 3. Chain-level lemmas: decomposition and whole-chain lift agreement

The composite transport along `cons b tail` is, by construction, the
transport along `tail` applied to the parameter obtained by the single
first transition `c → b` (the **decomposition lemma**
`chartChainTransport_cons`).  Following a parameter along an entire chain
never changes its zero-set point: the **whole-chain lift agreement**
`chartChain_lift_val` says that the point reached at the end of the chain
(defined recursively alongside the transport as `chartChainEndVal`) equals
the point of the original parameter.  The induction step mirrors the
two-step coherence of Section 2: decompose the chain into its first
transition and the tail, apply the induction hypothesis to the tail, and
use `chartTransition_preserves_point` for the first step. -/

/-- **Decomposition of the composite transport.**  Transporting along the
chain `cons b tail` is the transport along `tail` of the parameter obtained
by the single first transition `c → b` (whose point lies in every remaining
neighbourhood, since the whole chain is usable). -/
lemma chartChainTransport_cons {r : ℝ → Space} {p₀ p₁ : KnotParamTriple}
    (c : ZeroSet1Chart r p₀) (b : ZeroSet1Chart r p₁) (tail : ChartChain b)
    (z : chartChainDomain c (ChartChain.cons c b tail)) :
    chartChainTransport c (ChartChain.cons c b tail) z =
      chartChainTransport b tail
        ⟨((chartTransitionHomeo c b ⟨z.1, z.2.1⟩ : ChartTransitionDomain b c) :
            ChartInterval b.lo b.hi),
          by
            have hq := chartTransition_preserves_point c b ⟨z.1, z.2.1⟩
            rw [hq]
            exact z.2.2⟩ := by
  rfl

/-- The **point reached by following** the parameter along the whole chain:
the value of the current chart homeo at the transported parameter,
recursively along the chain (mirroring `chartChainTransport`). -/
noncomputable def chartChainEndVal {r : ℝ → Space} {p : KnotParamTriple}
    (c : ZeroSet1Chart r p) : ∀ (chain : ChartChain c),
    chartChainDomain c chain → KnotParamTriple
  | .nil _, z => (c.homeo z.1 : KnotParamTriple)
  | .cons _ b tail, z =>
      let step : ChartTransitionDomain b c := chartTransitionHomeo c b ⟨z.1, z.2.1⟩
      chartChainEndVal b tail
        ⟨step.1, by
          have hq := chartTransition_preserves_point c b ⟨z.1, z.2.1⟩
          rw [hq]
          exact z.2.2⟩

/-- **Whole-chain lift agreement.**  Following a parameter of `c` along an
entire chain ends at the same zero-set point: the point reached at the end
of the chain equals the point of the original parameter. -/
lemma chartChain_lift_val {r : ℝ → Space} {p : KnotParamTriple}
    (c : ZeroSet1Chart r p) :
    ∀ (chain : ChartChain c) (z : chartChainDomain c chain),
      chartChainEndVal c chain z = (c.homeo z.1).1
  | .nil _, z => by
      dsimp [chartChainEndVal]
  | .cons _ b tail, z => by
      -- decompose the end value recursion into the first transition and
      -- the tail
      have hdec : chartChainEndVal c (ChartChain.cons c b tail) z =
          chartChainEndVal b tail
            ⟨((chartTransitionHomeo c b ⟨z.1, z.2.1⟩ : ChartTransitionDomain b c) :
                ChartInterval b.lo b.hi),
              by
                have hq := chartTransition_preserves_point c b ⟨z.1, z.2.1⟩
                rw [hq]
                exact z.2.2⟩ := by
        rfl
      rw [hdec]
      have hrec : chartChainEndVal b tail
          ⟨((chartTransitionHomeo c b ⟨z.1, z.2.1⟩ : ChartTransitionDomain b c) :
              ChartInterval b.lo b.hi),
            (by
              have hq := chartTransition_preserves_point c b ⟨z.1, z.2.1⟩
              rw [hq]
              exact z.2.2 : (b.homeo ((chartTransitionHomeo c b ⟨z.1, z.2.1⟩ :
                  ChartTransitionDomain b c) : ChartInterval b.lo b.hi)).1 ∈
                chartChainVs b tail)⟩ =
          (c.homeo z.1).1 := by
        have hp := chartTransition_preserves_point c b ⟨z.1, z.2.1⟩
        have hIH := chartChain_lift_val b tail
          ⟨((chartTransitionHomeo c b ⟨z.1, z.2.1⟩ : ChartTransitionDomain b c) :
              ChartInterval b.lo b.hi),
            (by
              have hq := chartTransition_preserves_point c b ⟨z.1, z.2.1⟩
              rw [hq]
              exact z.2.2 : (b.homeo ((chartTransitionHomeo c b ⟨z.1, z.2.1⟩ :
                  ChartTransitionDomain b c) : ChartInterval b.lo b.hi)).1 ∈
                chartChainVs b tail)⟩
        -- hIH : chartChainEndVal b tail w = (b.homeo w.1).1
        calc
          chartChainEndVal b tail
              ⟨((chartTransitionHomeo c b ⟨z.1, z.2.1⟩ : ChartTransitionDomain b c) :
                  ChartInterval b.lo b.hi),
                (by
                  have hq := chartTransition_preserves_point c b ⟨z.1, z.2.1⟩
                  rw [hq]
                  exact z.2.2 : (b.homeo ((chartTransitionHomeo c b ⟨z.1, z.2.1⟩ :
                      ChartTransitionDomain b c) : ChartInterval b.lo b.hi)).1 ∈
                    chartChainVs b tail)⟩
              = (b.homeo ((chartTransitionHomeo c b ⟨z.1, z.2.1⟩ :
                    ChartTransitionDomain b c) : ChartInterval b.lo b.hi)).1 := hIH
          _ = (c.homeo z.1).1 := by
              simpa using hp
      exact hrec


/-- **The endpoint bridge.**  The value of the endpoint chart's homeo at
the transported parameter equals the endpoint value of the recursive
following (`chartChainEndVal`): the chain has a well-defined endpoint in
`KnotParamTriple` terms, and the two descriptions agree. -/
lemma chartChain_EndVal_eq_last {r : ℝ → Space} {p : KnotParamTriple}
    (c : ZeroSet1Chart r p) :
    ∀ (chain : ChartChain c) (z : chartChainDomain c chain),
      (((chartChainLast c chain).2).homeo (chartChainTransport c chain z) : KnotParamTriple) =
        chartChainEndVal c chain z
  | .nil _, z => by
      rfl
  | .cons _ b tail, z => by
      -- the transported element of the first step (its point lies in the
      -- remaining neighbourhoods by z.2.2 and the transition preservation)
      let wd : chartChainDomain b tail :=
        ⟨((chartTransitionHomeo c b ⟨z.1, z.2.1⟩ : ChartTransitionDomain b c) :
            ChartInterval b.lo b.hi),
          by
            have hq := chartTransition_preserves_point c b ⟨z.1, z.2.1⟩
            rw [hq]
            exact z.2.2⟩
      -- the transport along cons is the transport along the tail of wd
      have hdec : chartChainTransport c (ChartChain.cons c b tail) z =
          chartChainTransport b tail wd := by
        dsimp [wd]
        rfl
      -- the end value along cons is the end value along the tail of wd
      have hev : chartChainEndVal c (ChartChain.cons c b tail) z =
          chartChainEndVal b tail wd := by
        dsimp [wd]
        rfl
      -- the last chart of cons is the last chart of the tail
      dsimp [chartChainLast]
      rw [hdec, hev]
      exact chartChain_EndVal_eq_last b tail wd

/-- **Whole-chain lift agreement (chartLift form).**  The single-chart lift
at the endpoint chart of the transported parameter equals the lift of the
original parameter: a chain of charts transports a zero-set point to
itself. -/
lemma chartChain_lift {r : ℝ → Space} {p : KnotParamTriple}
    (c : ZeroSet1Chart r p) (chain : ChartChain c) (z : chartChainDomain c chain) :
    chartLift (chartChainLast c chain).2 (chartChainTransport c chain z) =
      chartLift c z.1 := by
  apply Subtype.ext
  simpa [chartLift] using
    (chartChain_EndVal_eq_last c chain z).trans (chartChain_lift_val c chain z)
