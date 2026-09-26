import Mathlib
import ChallengeDeps
import Submission.TorusAtlas
import Submission.TorusChartHomeo

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

/-!
# Layer A (xv) — bundled 1-dimensional charts of the trisecant zero set

`TorusChartHomeo.lean` (Layer A (xiv)) proved that the local curve of every
graph arc is in fact a **homeomorphism** from an open parameter interval
onto the trisecant zero set inside an open torus neighbourhood `V`
(`torus_chart_homeo_AB/AM/BM`).  `TorusAtlas.lean` (Layer A (xiii)) proved
the *cover*: every collinear off-diagonal torus triple of a
general-position smooth knot lies in some chart neighbourhood.

This module bundles the two into the **honest local 1-manifold statement**:

1. **`ZeroSet1Chart r p`** — a record carrying `V` (open, containing `p` in
   the zero set), an open parameter interval `(lo,hi)` with base `x₀`, and a
   homeomorphism `(lo,hi) ≃ₜ {q | q ∈ trisecantZeroSet r ∧ q ∈ V}` sending
   `x₀` to `p`.  This is exactly "the zero set is a 1-dimensional
   topological manifold at `p`": `p` has the chart neighbourhood
   `Z ∩ V` (open in `Z`) parametrised homeomorphically by an open interval
   of `ℝ`.
2. **per-witness constructors** `zeroSet1Chart_AB/AM/BM` (via the split
   instances + `RealGraphArc.exists_small_delta` +
   `torus_chart_homeo_*`);
3. **the cover theorem** `zeroSet1Chart_at_general_position`: under
   `TorusGeneralPosition r`, every `p ∈ trisecantZeroSet r` carries a
   `ZeroSet1Chart r p` (dispatch over the rank-two witness, exactly as in
   `zeroSetChart_at_general_position`).

The component/1-manifold analysis (connected components of the zero set,
path-following along charts) is the next gluing stage and will be stated on
top of these bundled charts.

Everything here is elementary and verified (no axioms, no `sorry`).
-/

namespace LeanEval.KnotTheory.Quadrisecant

/-- **A bundled 1-dimensional chart of the trisecant zero set at `p`**: an
open torus neighbourhood `V` with `p ∈ Z ∩ V`, an open interval
`(lo,hi) ∋ x₀`, and a homeomorphism of the interval onto `Z ∩ V` (subspace
of the torus) sending `x₀` to `p`.  In particular `Z ∩ V` is an open
neighbourhood of `p` in `Z` homeomorphic to an open interval — `Z` is
locally a 1-dimensional topological manifold at `p`. -/
structure ZeroSet1Chart (r : ℝ → Space) (p : KnotParamTriple) where
  V : Set KnotParamTriple
  V_open : IsOpen V
  p_zero : p ∈ trisecantZeroSet r
  p_mem : p ∈ V
  lo : ℝ
  hi : ℝ
  x₀ : ℝ
  x₀_mem : x₀ ∈ Set.Ioo lo hi
  homeo : {x : ℝ // x ∈ Set.Ioo lo hi} ≃ₜ
    {q : KnotParamTriple // q ∈ trisecantZeroSet r ∧ q ∈ V}
  base : (homeo ⟨x₀, x₀_mem⟩).1 = p

/-- **Chart, `(A,B)` witness**: a collinear off-diagonal triple with
independent `a`/`b` partials has a bundled 1-chart at
`torusQuotient (a,(b,m))`. -/
theorem zeroSet1Chart_AB {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ)
    (hΦ : collinearityValue r a b m = 0)
    (hZ : r a - r b ≠ 0) (hW0 : r a - r m ≠ 0) (hmb : r m - r b ≠ 0)
    (hLI : LinearIndependent ℝ ![collPartialA r a b m, collPartialB r a b m]) :
    Nonempty (ZeroSet1Chart r (torusQuotient (a, (b, m)))) := by
  rcases exists_realGraphArc_AB_splitting h a b m hΦ hZ hW0 hmb hLI with ⟨d, hB, hA, hu⟩
  rcases d.exists_small_delta with ⟨δ, hδpos, hδw, hL, hR⟩
  have hLm : d.a < m - δ := by
    rw [hu] at hL
    exact hL
  have hRm : m + δ < d.b := by
    rw [hu] at hR
    exact hR
  rcases torus_chart_homeo_AB h a b m hδpos hδw d hB hA hu hLm hRm with
    ⟨V, hVo, pZ, pV, e, hbase, htrace⟩
  exact ⟨⟨V, hVo, pZ, pV, m - δ, m + δ, m, by constructor <;> linarith, e, hbase⟩⟩

/-- **Chart, `(A,M)` witness**: mirror of `zeroSet1Chart_AB` for
independent `a`/`m` partials. -/
theorem zeroSet1Chart_AM {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ)
    (hΦ : collinearityValue r a b m = 0)
    (hZ : r a - r b ≠ 0) (hW0 : r a - r m ≠ 0) (hmb : r m - r b ≠ 0)
    (hLI : LinearIndependent ℝ ![collPartialA r a b m, collPartialM r a b m]) :
    Nonempty (ZeroSet1Chart r (torusQuotient (a, (b, m)))) := by
  rcases exists_realGraphArc_AM_splitting h a b m hΦ hZ hW0 hmb hLI with ⟨d, hB, hA, hu⟩
  rcases d.exists_small_delta with ⟨δ, hδpos, hδw, hL, hR⟩
  have hLb : d.a < b - δ := by
    rw [hu] at hL
    exact hL
  have hRb : b + δ < d.b := by
    rw [hu] at hR
    exact hR
  rcases torus_chart_homeo_AM h a b m hδpos hδw d hB hA hu hLb hRb with
    ⟨V, hVo, pZ, pV, e, hbase, htrace⟩
  exact ⟨⟨V, hVo, pZ, pV, b - δ, b + δ, b, by constructor <;> linarith, e, hbase⟩⟩

/-- **Chart, `(B,M)` witness**: mirror of `zeroSet1Chart_AB` for
independent `b`/`m` partials. -/
theorem zeroSet1Chart_BM {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ)
    (hΦ : collinearityValue r a b m = 0)
    (hZ : r a - r b ≠ 0) (hW0 : r a - r m ≠ 0) (hmb : r m - r b ≠ 0)
    (hLI : LinearIndependent ℝ ![collPartialB r a b m, collPartialM r a b m]) :
    Nonempty (ZeroSet1Chart r (torusQuotient (a, (b, m)))) := by
  rcases exists_realGraphArc_BM_splitting h a b m hΦ hZ hW0 hmb hLI with ⟨d, hB, hA, hu⟩
  rcases d.exists_small_delta with ⟨δ, hδpos, hδw, hL, hR⟩
  have hLa : d.a < a - δ := by
    rw [hu] at hL
    exact hL
  have hRa : a + δ < d.b := by
    rw [hu] at hR
    exact hR
  rcases torus_chart_homeo_BM h a b m hδpos hδw d hB hA hu hLa hRa with
    ⟨V, hVo, pZ, pV, e, hbase, htrace⟩
  exact ⟨⟨V, hVo, pZ, pV, a - δ, a + δ, a, by constructor <;> linarith, e, hbase⟩⟩

/-- **The local 1-manifold theorem for the trisecant zero set**: under the
torus general-position hypothesis, every collinear off-diagonal torus triple
carries a bundled 1-chart — the zero set is a 1-dimensional topological
manifold at every one of its (off-diagonal) points. -/
theorem zeroSet1Chart_at_general_position {r : ℝ → Space} (h : IsSmoothKnot r)
    (hgp : TorusGeneralPosition r) (p : KnotParamTriple)
    (hp : p ∈ trisecantZeroSet r) : Nonempty (ZeroSet1Chart r p) := by
  have hpZ : torusCollinearity r p = 0 := (mem_trisecantZeroSet_iff p).mp hp |>.1
  have hpOff : p ∈ TorusOffDiag r := (mem_trisecantZeroSet_iff p).mp hp |>.2
  rcases hgp p hpZ hpOff with ⟨a, b, m, ha, hb, hm, hpa, hpb, hpm, hGP⟩
  rcases hGP with ⟨hZa, hW0, hmb, hP⟩
  rcases hP with ⟨i, j, hij, hLIij⟩
  have hp_eq : torusQuotient (a, (b, m)) = p := by
    simp [torusQuotient, hpa, hpb, hpm]
  have hΦ : collinearityValue r a b m = 0 := by
    rw [← hp_eq] at hpZ
    rw [torusCollinearity_quotient h (a, (b, m))] at hpZ
    simpa [collinearityValue_eq, collinearityMap] using hpZ
  rw [← hp_eq]
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · exact zeroSet1Chart_AB h a b m hΦ hZa hW0 hmb
      (by simpa [collPartial_eq_A, collPartial_eq_B] using hLIij)
  · exact zeroSet1Chart_AM h a b m hΦ hZa hW0 hmb
      (by simpa [collPartial_eq_A, collPartial_eq_M] using hLIij)
  · exact zeroSet1Chart_AB h a b m hΦ hZa hW0 hmb
      (by
        have hsw := (linearIndependent_pair_swap_iff (collPartialA r a b m) (collPartialB r a b m)).mp ?_
        · simpa [collPartial_eq_A, collPartial_eq_B] using hsw
        · simpa [collPartial_eq_A, collPartial_eq_B] using hLIij)
  · exact False.elim (hij rfl)
  · exact zeroSet1Chart_BM h a b m hΦ hZa hW0 hmb
      (by simpa [collPartial_eq_B, collPartial_eq_M] using hLIij)
  · exact zeroSet1Chart_AM h a b m hΦ hZa hW0 hmb
      (by
        have hsw := (linearIndependent_pair_swap_iff (collPartialA r a b m) (collPartialM r a b m)).mp ?_
        · simpa [collPartial_eq_A, collPartial_eq_M] using hsw
        · simpa [collPartial_eq_A, collPartial_eq_M] using hLIij)
  · exact zeroSet1Chart_BM h a b m hΦ hZa hW0 hmb
      (by
        have hsw := (linearIndependent_pair_swap_iff (collPartialB r a b m) (collPartialM r a b m)).mp ?_
        · simpa [collPartial_eq_B, collPartial_eq_M] using hsw
        · simpa [collPartial_eq_B, collPartial_eq_M] using hLIij)
  · exact False.elim (hij rfl)

end LeanEval.KnotTheory.Quadrisecant


/-! ## 2. Transition maps between overlapping bundled charts

Two bundled charts at (possibly different) base points whose zero-set
neighbourhoods overlap parametrise the same portion of the trisecant zero
set from two sides.  The **transition lemma** below is the manifold-theoretic
compatibility statement: on the transition domains (the parameters of `c₁`
whose points lie in `c₂.V`, and symmetrically) the two parametrisations are
related by a **homeomorphism which preserves the zero-set point** — applying
`c₂.homeo` to the transported parameter gives the very same torus point as
`c₁.homeo` applied to the original parameter.

This is the glue with which path-following along `Z ∩ offdiag` will be
assembled: passing from one local chart to the next along a path of the zero
set is a homeomorphism of open parameter intervals.
-/

namespace LeanEval.KnotTheory.Quadrisecant

/-- The parameter interval of a bundled chart (an open interval of the
reals, as a subtype). -/
abbrev ChartInterval (lo hi : ℝ) : Type := {t : ℝ // t ∈ Set.Ioo lo hi}

/-- The **transition domain** of chart `c₁` into chart `c₂`: the parameters
of `c₁` whose zero-set points lie in the neighbourhood `V₂` of `c₂`. -/
abbrev ChartTransitionDomain {r : ℝ → Space} {p₁ p₂ : KnotParamTriple}
    (c₁ : ZeroSet1Chart r p₁) (c₂ : ZeroSet1Chart r p₂) : Type :=
  {x : ChartInterval c₁.lo c₁.hi // (c₁.homeo x).1 ∈ c₂.V}

/-- The **forward transition map** `c₁ → c₂`: a parameter `x` of `c₁` whose
point `q = (c₁.homeo x).1` lies in `V₂` is sent to the parameter of `c₂`
describing the same zero-set point `q`. -/
noncomputable def chartTransitionTo {r : ℝ → Space} {p₁ p₂ : KnotParamTriple}
    (c₁ : ZeroSet1Chart r p₁) (c₂ : ZeroSet1Chart r p₂)
    (x : ChartTransitionDomain c₁ c₂) : ChartTransitionDomain c₂ c₁ :=
  ⟨c₂.homeo.symm ⟨(c₁.homeo x.1).1, ⟨(c₁.homeo x.1).2.1, x.2⟩⟩, by
    have hz := c₂.homeo.apply_symm_apply
      ⟨(c₁.homeo x.1).1, ⟨(c₁.homeo x.1).2.1, x.2⟩⟩
    rw [hz]
    simpa using (c₁.homeo x.1).2.2⟩

/-- The **backward transition map** `c₂ → c₁` (the candidate inverse of
`chartTransitionTo`). -/
noncomputable def chartTransitionBack {r : ℝ → Space} {p₁ p₂ : KnotParamTriple}
    (c₁ : ZeroSet1Chart r p₁) (c₂ : ZeroSet1Chart r p₂)
    (y : ChartTransitionDomain c₂ c₁) : ChartTransitionDomain c₁ c₂ :=
  ⟨c₁.homeo.symm ⟨(c₂.homeo y.1).1, ⟨(c₂.homeo y.1).2.1, y.2⟩⟩, by
    have hz := c₁.homeo.apply_symm_apply
      ⟨(c₂.homeo y.1).1, ⟨(c₂.homeo y.1).2.1, y.2⟩⟩
    rw [hz]
    simpa using (c₂.homeo y.1).2.2⟩

/-- The value of the forward transition map (no proofs involved). -/
lemma chartTransitionTo_val {r : ℝ → Space} {p₁ p₂ : KnotParamTriple}
    (c₁ : ZeroSet1Chart r p₁) (c₂ : ZeroSet1Chart r p₂)
    (x : ChartTransitionDomain c₁ c₂) :
    (chartTransitionTo c₁ c₂ x).1 =
      c₂.homeo.symm ⟨(c₁.homeo x.1).1, ⟨(c₁.homeo x.1).2.1, x.2⟩⟩ := by
  dsimp [chartTransitionTo]

/-- The value of the backward transition map (no proofs involved). -/
lemma chartTransitionBack_val {r : ℝ → Space} {p₁ p₂ : KnotParamTriple}
    (c₁ : ZeroSet1Chart r p₁) (c₂ : ZeroSet1Chart r p₂)
    (y : ChartTransitionDomain c₂ c₁) :
    (chartTransitionBack c₁ c₂ y).1 =
      c₁.homeo.symm ⟨(c₂.homeo y.1).1, ⟨(c₂.homeo y.1).2.1, y.2⟩⟩ := by
  dsimp [chartTransitionBack]

/-- Forward and backward transition maps are mutually inverse (the left
half): going to chart `c₂` and back returns the original parameter. -/
lemma chartTransition_leftInverse {r : ℝ → Space} {p₁ p₂ : KnotParamTriple}
    (c₁ : ZeroSet1Chart r p₁) (c₂ : ZeroSet1Chart r p₂)
    (x : ChartTransitionDomain c₁ c₂) :
    chartTransitionBack c₁ c₂ (chartTransitionTo c₁ c₂ x) = x := by
  let q : KnotParamTriple := (c₁.homeo x.1).1
  have hqZ : q ∈ trisecantZeroSet r := (c₁.homeo x.1).2.1
  have hqV₁ : q ∈ c₁.V := (c₁.homeo x.1).2.2
  have hx1 : c₁.homeo x.1 = ⟨q, ⟨hqZ, hqV₁⟩⟩ := by
    apply Subtype.ext
    rfl
  apply Subtype.ext
  rw [chartTransitionBack_val]
  -- write x.1 as c₁.homeo.symm (c₁.homeo x.1) and expand c₁.homeo x.1
  rw [← c₁.homeo.symm_apply_apply x.1]
  rw [hx1]
  -- compare the two c₁.homeo.symm arguments: both describe the point q
  apply congrArg c₁.homeo.symm
  apply Subtype.ext
  -- values: c₂.homeo applied to the forward value is the point q
  have hz := c₂.homeo.apply_symm_apply
    ⟨(c₁.homeo x.1).1, ⟨(c₁.homeo x.1).2.1, x.2⟩⟩
  have hval : (c₂.homeo (chartTransitionTo c₁ c₂ x).1 : KnotParamTriple) =
      (c₁.homeo x.1).1 := by
    have h1 := congrArg (fun w : {q0 : KnotParamTriple //
        q0 ∈ trisecantZeroSet r ∧ q0 ∈ c₂.V} => (w : KnotParamTriple))
      (congrArg c₂.homeo (chartTransitionTo_val c₁ c₂ x))
    have h2 := congrArg (fun w : {q0 : KnotParamTriple //
        q0 ∈ trisecantZeroSet r ∧ q0 ∈ c₂.V} => (w : KnotParamTriple)) hz
    simpa using h1.trans h2
  simpa [q] using hval

/-- Forward transition with the roles of the two charts swapped is the
backward transition map (they compute the same value). -/
lemma chartTransitionBack_eq {r : ℝ → Space} {p₁ p₂ : KnotParamTriple}
    (c₁ : ZeroSet1Chart r p₁) (c₂ : ZeroSet1Chart r p₂)
    (y : ChartTransitionDomain c₂ c₁) :
    chartTransitionBack c₁ c₂ y = chartTransitionTo c₂ c₁ y := by
  unfold chartTransitionBack chartTransitionTo
  apply Subtype.ext
  rfl

/-- Forward and backward transition maps are mutually inverse (the right
half). -/
lemma chartTransition_rightInverse {r : ℝ → Space} {p₁ p₂ : KnotParamTriple}
    (c₁ : ZeroSet1Chart r p₁) (c₂ : ZeroSet1Chart r p₂)
    (y : ChartTransitionDomain c₂ c₁) :
    chartTransitionTo c₁ c₂ (chartTransitionBack c₁ c₂ y) = y := by
  calc
    chartTransitionTo c₁ c₂ (chartTransitionBack c₁ c₂ y)
        = chartTransitionTo c₁ c₂ (chartTransitionTo c₂ c₁ y) := by
          rw [chartTransitionBack_eq c₁ c₂ y]
    _ = chartTransitionBack c₂ c₁ (chartTransitionTo c₂ c₁ y) := by
          rw [chartTransitionBack_eq c₂ c₁ (chartTransitionTo c₂ c₁ y)]
    _ = y := chartTransition_leftInverse c₂ c₁ y

/-- The transition correspondence as an equivalence of the two domains. -/
noncomputable def chartTransitionEquiv {r : ℝ → Space} {p₁ p₂ : KnotParamTriple}
    (c₁ : ZeroSet1Chart r p₁) (c₂ : ZeroSet1Chart r p₂) :
    ChartTransitionDomain c₁ c₂ ≃ ChartTransitionDomain c₂ c₁ where
  toFun := chartTransitionTo c₁ c₂
  invFun := chartTransitionBack c₁ c₂
  left_inv := chartTransition_leftInverse c₁ c₂
  right_inv := chartTransition_rightInverse c₁ c₂

end LeanEval.KnotTheory.Quadrisecant

/-! The continuity of the transition maps and the bundled homeomorphism
(`chartTransitionHomeo`) and the transition lemma itself. -/

namespace LeanEval.KnotTheory.Quadrisecant

/-- The forward transition map is continuous: the value into `I₂` (and
thence into `ℝ`) is the composition of the chart homeomorphism `c₁.homeo`,
the point-valued map into `c₂`'s chart codomain, and `c₂.homeo.symm`, each
continuous. -/
lemma continuous_chartTransitionTo {r : ℝ → Space} {p₁ p₂ : KnotParamTriple}
    (c₁ : ZeroSet1Chart r p₁) (c₂ : ZeroSet1Chart r p₂) :
    Continuous (chartTransitionTo c₁ c₂) := by
  let Y₂ : Type := {q : KnotParamTriple // q ∈ trisecantZeroSet r ∧ q ∈ c₂.V}
  let X₁ : Type := ChartTransitionDomain c₁ c₂
  -- the point-valued map X₁ → Y₂ (val = the chart point of x)
  have hq : Continuous (fun x : X₁ => ((c₁.homeo x.1 : {q : KnotParamTriple //
      q ∈ trisecantZeroSet r ∧ q ∈ c₁.V}) : KnotParamTriple)) := by
    have hval₁ : Continuous (fun x : X₁ => (x.1 : ChartInterval c₁.lo c₁.hi)) :=
      continuous_subtype_val
    have hstep : Continuous (fun x : X₁ => (c₁.homeo (x.1 : ChartInterval c₁.lo c₁.hi))) :=
      c₁.homeo.continuous.comp hval₁
    exact (continuous_subtype_val.comp hstep)
  have ht : Continuous (fun x : X₁ =>
      (⟨(c₁.homeo x.1).1, ⟨(c₁.homeo x.1).2.1, x.2⟩⟩ : Y₂)) := by
    rw [continuous_def]
    intro U hUo
    rw [isOpen_induced_iff] at hUo
    rcases hUo with ⟨W, hWo, hUW⟩
    have hpre : (fun x : X₁ =>
        (⟨(c₁.homeo x.1).1, ⟨(c₁.homeo x.1).2.1, x.2⟩⟩ : Y₂)) ⁻¹' U =
        (fun x : X₁ => ((c₁.homeo x.1 : {q : KnotParamTriple //
            q ∈ trisecantZeroSet r ∧ q ∈ c₁.V}) : KnotParamTriple)) ⁻¹' W := by
      ext x
      rw [← hUW]
      rfl
    rw [hpre]
    exact IsOpen.preimage hq hWo
  -- the value into the real line is c₂.homeo.symm of that point
  have h2r : Continuous (fun w : Y₂ =>
      ((c₂.homeo.symm w : ChartInterval c₂.lo c₂.hi) : ℝ)) := by
    have hI : Continuous (fun u : ChartInterval c₂.lo c₂.hi => (u : ℝ)) :=
      continuous_subtype_val
    exact hI.comp c₂.homeo.symm.continuous
  have hmain : Continuous (fun x : X₁ =>
      ((c₂.homeo.symm (⟨(c₁.homeo x.1).1, ⟨(c₁.homeo x.1).2.1, x.2⟩⟩ : Y₂) :
        ChartInterval c₂.lo c₂.hi) : ℝ)) := h2r.comp ht
  -- reduce the target: X₂ is induced from I₂, which is induced from ℝ
  have hid₂ : Topology.IsInducing ((↑) : ChartTransitionDomain c₂ c₁ →
      ChartInterval c₂.lo c₂.hi) := Topology.IsInducing.subtypeVal
  have hid₂ℝ : Topology.IsInducing ((↑) : ChartInterval c₂.lo c₂.hi → ℝ) :=
    Topology.IsInducing.subtypeVal
  rw [hid₂.continuous_iff]
  rw [hid₂ℝ.continuous_iff]
  -- now the target is ℝ-valued; compare with hmain
  change Continuous (fun x : X₁ =>
      ((c₂.homeo.symm (⟨(c₁.homeo x.1).1, ⟨(c₁.homeo x.1).2.1, x.2⟩⟩ : Y₂) :
        ChartInterval c₂.lo c₂.hi) : ℝ))
  exact hmain

/-- The backward transition map is continuous (it is the forward transition
with the two charts swapped, which agrees with `chartTransitionBack`). -/
lemma continuous_chartTransitionBack {r : ℝ → Space} {p₁ p₂ : KnotParamTriple}
    (c₁ : ZeroSet1Chart r p₁) (c₂ : ZeroSet1Chart r p₂) :
    Continuous (chartTransitionBack c₁ c₂) := by
  -- chartTransitionBack c₁ c₂ = chartTransitionTo c₂ c₁ on values
  apply (continuous_iff_continuousAt).mpr
  intro y
  -- (fun y => chartTransitionBack c₁ c₂ y) agrees with (chartTransitionTo c₂ c₁)
  have hagree : chartTransitionBack c₁ c₂ = chartTransitionTo c₂ c₁ := by
    funext y
    exact chartTransitionBack_eq c₁ c₂ y
  rw [hagree]
  exact (continuous_chartTransitionTo c₂ c₁).continuousAt

/-- The transition correspondence of two overlapping bundled charts is a
**homeomorphism of open parameter domains** (the interval subtypes). -/
noncomputable def chartTransitionHomeo {r : ℝ → Space} {p₁ p₂ : KnotParamTriple}
    (c₁ : ZeroSet1Chart r p₁) (c₂ : ZeroSet1Chart r p₂) :
    ChartTransitionDomain c₁ c₂ ≃ₜ ChartTransitionDomain c₂ c₁ :=
  Homeomorph.mk (chartTransitionEquiv c₁ c₂) (continuous_chartTransitionTo c₁ c₂)
    (continuous_chartTransitionBack c₁ c₂)

/-- The transition homeomorphism **preserves the zero-set point**: applying
`c₂.homeo` to the transported parameter gives the same torus point as
`c₁.homeo` applied to the original parameter. -/
lemma chartTransition_preserves_point {r : ℝ → Space} {p₁ p₂ : KnotParamTriple}
    (c₁ : ZeroSet1Chart r p₁) (c₂ : ZeroSet1Chart r p₂)
    (x : ChartTransitionDomain c₁ c₂) :
    (c₂.homeo ((chartTransitionHomeo c₁ c₂ x : ChartTransitionDomain c₂ c₁) :
        ChartInterval c₂.lo c₂.hi)).1 = (c₁.homeo x.1).1 := by
  -- the transported parameter is chartTransitionTo of x
  have hval : ((chartTransitionHomeo c₁ c₂ x : ChartTransitionDomain c₂ c₁) :
      ChartInterval c₂.lo c₂.hi) =
      (chartTransitionTo c₁ c₂ x).1 := by
    rfl
  rw [hval]
  -- c₂.homeo applied to the forward value is the point q := (c₁.homeo x.1).1
  have hz := c₂.homeo.apply_symm_apply
    ⟨(c₁.homeo x.1).1, ⟨(c₁.homeo x.1).2.1, x.2⟩⟩
  have hvalq : (c₂.homeo (chartTransitionTo c₁ c₂ x).1 : KnotParamTriple) =
      (c₁.homeo x.1).1 := by
    have h1 := congrArg (fun w : {q0 : KnotParamTriple //
        q0 ∈ trisecantZeroSet r ∧ q0 ∈ c₂.V} => (w : KnotParamTriple))
      (congrArg c₂.homeo (chartTransitionTo_val c₁ c₂ x))
    have h2 := congrArg (fun w : {q0 : KnotParamTriple //
        q0 ∈ trisecantZeroSet r ∧ q0 ∈ c₂.V} => (w : KnotParamTriple)) hz
    simpa using h1.trans h2
  -- compare values of the two chart points
  simpa using hvalq

/-- **The transition lemma.**  Two bundled charts whose zero-set
neighbourhoods overlap are compatible: on the transition domains the change
of parameters is a homeomorphism (`chartTransitionHomeo`), and it preserves
the zero-set point (`chartTransition_preserves_point`). -/
theorem zeroSet1Chart_transition {r : ℝ → Space} {p₁ p₂ : KnotParamTriple}
    (c₁ : ZeroSet1Chart r p₁) (c₂ : ZeroSet1Chart r p₂) :
    ∃ h : ChartTransitionDomain c₁ c₂ ≃ₜ ChartTransitionDomain c₂ c₁,
      ∀ x : ChartTransitionDomain c₁ c₂,
        (c₂.homeo ((h x) : ChartInterval c₂.lo c₂.hi)).1 = (c₁.homeo x.1).1 := by
  refine ⟨chartTransitionHomeo c₁ c₂, ?_⟩
  intro x
  exact chartTransition_preserves_point c₁ c₂ x

/-! ## 3. Single-chart lifts and their overlap agreement

The global path-following construction moves along the trisecant zero set by
changing charts.  The elementary building block is the **single-chart
lift**: the chart homeomorphism `c.homeo` viewed as a map from the open
parameter interval `ChartInterval c.lo c.hi` into the zero set
(`chartLift c`).  The local coherence needed to glue the pieces is the
**overlap agreement**: for a parameter `x` in the transition domain of `c₁`
into `c₂` (its zero-set point lies in `c₂.V`), the lift of `c₁` at `x`
equals the lift of `c₂` at the parameter transported by
`chartTransitionHomeo c₁ c₂` — exactly the statement that the change of
charts preserves the zero-set point, restated at the level of the lifts.
-/

/-- Points of the trisecant zero set (collinear off-diagonal triples of the
parameter torus) — the type-level carrier of the path-following
construction. -/
abbrev ZeroSetPoint (r : ℝ → Space) : Type :=
  {q : KnotParamTriple // q ∈ trisecantZeroSet r}

/-- **The single-chart lift**: the chart homeomorphism `c.homeo` viewed as a
map from the open parameter interval into the trisecant zero set (the
neighbourhood membership is dropped; the zero-set membership is kept). -/
noncomputable def chartLift {r : ℝ → Space} {p : KnotParamTriple}
    (c : ZeroSet1Chart r p) (x : ChartInterval c.lo c.hi) : ZeroSetPoint r :=
  ⟨(c.homeo x).1, (c.homeo x).2.1⟩

/-- The value of the single-chart lift is the chart point. -/
lemma chartLift_val {r : ℝ → Space} {p : KnotParamTriple} (c : ZeroSet1Chart r p)
    (x : ChartInterval c.lo c.hi) :
    (chartLift c x : KnotParamTriple) = (c.homeo x).1 := by
  rfl

/-- The single-chart lift is continuous (the chart homeomorphism is
continuous and the zero-set membership is forgotten by the value map). -/
lemma continuous_chartLift {r : ℝ → Space} {p : KnotParamTriple}
    (c : ZeroSet1Chart r p) : Continuous (chartLift c) := by
  have hid : Topology.IsInducing ((↑) : ZeroSetPoint r → KnotParamTriple) :=
    Topology.IsInducing.subtypeVal
  rw [hid.continuous_iff]
  change Continuous (fun x : ChartInterval c.lo c.hi =>
      ((c.homeo x : {q0 : KnotParamTriple // q0 ∈ trisecantZeroSet r ∧ q0 ∈ c.V}) :
        KnotParamTriple))
  exact continuous_subtype_val.comp c.homeo.continuous

/-- **Overlap agreement of the single-chart lifts.**  When a parameter `x`
of `c₁` lies in the transition domain into `c₂` (its zero-set point lies in
`c₂.V`), the two charts describe the same zero-set point in compatible
coordinates: the lift of `c₁` at `x` equals the lift of `c₂` at the
parameter obtained by the transition homeomorphism. -/
lemma chartLift_overlap {r : ℝ → Space} {p₁ p₂ : KnotParamTriple}
    (c₁ : ZeroSet1Chart r p₁) (c₂ : ZeroSet1Chart r p₂)
    (x : ChartTransitionDomain c₁ c₂) :
    chartLift c₁ x.1 =
      chartLift c₂ ((chartTransitionHomeo c₁ c₂ x : ChartTransitionDomain c₂ c₁) :
        ChartInterval c₂.lo c₂.hi) := by
  apply Subtype.ext
  simpa [chartLift] using (chartTransition_preserves_point c₁ c₂ x).symm

end LeanEval.KnotTheory.Quadrisecant
