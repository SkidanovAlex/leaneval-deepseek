import Mathlib
import ChallengeDeps
import Submission.TorusGraphInstances
import Submission.TorusCharts

open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Real Topology

/-!
# Layer A (xii) — the torus-quotient lift of the `(A,B)` graph arc: an honest chart

The three instances (`TorusGraphInstances.lean`) give, at every
general-position collinear off-diagonal real triple, a `RealGraphArc`: the
local zero set is the graph `γ(x) = A(x, ψ(x))` over the *curve coordinate*
`x = (B q).1` (which for the `(A,B)` split is the third parameter, `m`).
This module lifts the `(A,B)` witness through the period quotient
`torusQuotient : ℝ³ → T³` to an **honest torus chart**: a *single* interval
parametrisation `x ↦ torusQuotient(γ(x))` that is

- **injective** over the whole interval — new, and now free: the graph
  coordinate `x` is an actual coordinate of the real triple (`γ(x)` has
  third coordinate `x` for the `splitAB` graph), so two torus-equal graph
  points force `x ≡ x′ (mod period)`, and on an interval of width `< period`
  that forces `x = x′` (`coe_injOn_Ioo`).  (This is the improvement over
  `TorusCharts.lean`, whose opaque curves were only injective on a
  sub-interval.)
- **covering an open torus neighbourhood** of the base point
  `p₀ = torusQuotient(a,(b,m))`: any collinear off-diagonal torus zero whose
  real lift has curve coordinate in the interval and lies in the
  `ψ`-covering neighbourhood `W` sits on the arc (the `RealGraphArc.cover`
  covering property, transported by the bridge
  `torusCollinearity_quotient` / `TorusOffDiag_quotient_iff`).

The theorem is stated for an arbitrary `d : RealGraphArc r` carrying the
`(A,B)` split identities (`d.B = unSplitAB`, `d.A = splitAB`,
`d.u = (m,(a,b))`); such `d` exists by
`exists_realGraphArc_AB_splitting` (the `Classical.choice`-based
`realGraphArc_AB` is opaque, so the lift is stated on the *splitting*
witness whose identities are available).  The interval conditions
(`d.a < m − δ`, `m + δ < d.b`, `0 < δ`, `2δ < period`) place the graph
inside the chart's parameter interval and make the quotient injective on it.
The same statement ports to the `(A,M)`/`(B,M)` witnesses with the matching
coordinate functional (second/first parameter) — the anticipated
per-witness edit.

Everything here is elementary and verified (no axioms, no `sorry`).
-/

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-- For the `(A,B)` split, the graph coordinate is the third parameter: the
graph point `γ(x)` has third coordinate `x`. -/
lemma RealGraphArc.g_coord3_AB {r : ℝ → Space} (d : RealGraphArc r)
    (hB : d.B = unSplitAB) (x : ℝ) :
    (d.g x).2.2 = x := by
  have h1 : (d.g x).2.2 = (unSplitAB (d.g x)).1 := by
    simp [unSplitAB]
  have h2 : (unSplitAB (d.g x)).1 = (d.B (d.g x)).1 := by
    rw [hB]
  rw [h1, h2]
  rw [d.g_B]

/-- **Quotient injectivity on the graph**: two torus-equal graph points with
parameter values in an interval of width `< period` must have equal
parameters (the parameter is a coordinate of the real triple, so congruence
modulo the period forces equality). -/
lemma injOn_torusQuotient_g_of_graphCoord {m δ : ℝ} (hδ : 2 * δ < period)
    {f : ℝ → RealParamTriple} (hf : ∀ x : ℝ, (f x).2.2 = x) :
    Set.InjOn (fun x : ℝ => torusQuotient (f x)) (Set.Ioo (m - δ) (m + δ)) := by
  intro x₁ hx₁ x₂ hx₂ hEq
  have hc := congrArg (fun t : KnotParamTriple => t.2.2) hEq
  have h1 : (torusQuotient (f x₁)).2.2 = ((f x₁).2.2 : KnotParam) := by
    simp [torusQuotient]
  have h2 : (torusQuotient (f x₂)).2.2 = ((f x₂).2.2 : KnotParam) := by
    simp [torusQuotient]
  have hc' : ((f x₁).2.2 : KnotParam) = ((f x₂).2.2 : KnotParam) := by
    rw [← h1, ← h2]
    exact hc
  rw [hf x₁, hf x₂] at hc'
  exact coe_injOn_Ioo (c := m) (η := δ) hδ hx₁ hx₂ hc'

/-- **The `(A,B)` torus chart**: a single interval parametrisation of the
torus trisecant zero set, injective on the whole interval, covering an open
torus neighbourhood of the base point `torusQuotient (a,(b,m))`.  `δ` is the
half-width of the parameter interval (must keep the graph inside `(d.a,d.b)`
and have width `< period`). -/
theorem torus_chart_lift_AB {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ)
    {δ : ℝ} (hδpos : 0 < δ) (hδw : 2 * δ < period)
    (d : RealGraphArc r) (hB : d.B = unSplitAB) (hA : d.A = splitAB)
    (hu : d.u = (m, (a, b)))
    (hL : d.a < m - δ) (hR : m + δ < d.b) :
    ∃ V : Set KnotParamTriple, IsOpen V ∧ torusQuotient (a, (b, m)) ∈ V ∧
      ∃ γ : ℝ → KnotParamTriple,
        ContinuousOn γ (Set.Ioo (m - δ) (m + δ)) ∧
          Set.InjOn γ (Set.Ioo (m - δ) (m + δ)) ∧ γ m = torusQuotient (a, (b, m)) ∧
          γ '' Set.Ioo (m - δ) (m + δ) ⊆ trisecantZeroSet r ∧
          γ '' Set.Ioo (m - δ) (m + δ) ⊆ V ∧
          (∀ q ∈ V, q ∈ trisecantZeroSet r → ∃ x ∈ Set.Ioo (m - δ) (m + δ), γ x = q) := by
  let γ : ℝ → KnotParamTriple := fun x => torusQuotient (d.g x)
  have hcoord : ∀ x : ℝ, (d.g x).2.2 = x := d.g_coord3_AB hB
  -- the real "curve window" U₀ = {q | (B q).1 ∈ (m−δ,m+δ)} ∩ B⁻¹'(W)
  let U₀ : Set RealParamTriple :=
    {q : RealParamTriple | (d.B q).1 ∈ Set.Ioo (m - δ) (m + δ)} ∩ (d.B ⁻¹' d.W)
  have hU₀o : IsOpen U₀ := by
    dsimp [U₀]
    have hBfst : Continuous (fun q : RealParamTriple => (d.B q).1) := Continuous.fst d.B_cont
    exact (isOpen_Ioo.preimage hBfst).inter (d.W_open.preimage d.B_cont)
  have hxIab : ∀ x : ℝ, x ∈ Set.Ioo (m - δ) (m + δ) → x ∈ Set.Ioo d.a d.b := by
    intro x hx
    constructor <;> linarith [hL, hR, hx.1, hx.2]
  have hu1 : d.u.1 = m := by rw [hu]
  -- the base graph point equals (a,(b,m))
  have hgm : d.g m = (a, (b, m)) := by
    rw [← hu1]
    have hgAu : d.g d.u.1 = d.A d.u := by
      unfold RealGraphArc.g
      congr 1
      ext <;> simp [d.ψu]
    rw [hgAu, hA, hu]
    simp [splitAB]
  -- the graph point at m lies in the curve window
  have hgmU₀ : d.g m ∈ U₀ := by
    dsimp [U₀]
    constructor
    · change (d.B (d.g m)).1 ∈ Set.Ioo (m - δ) (m + δ)
      rw [d.g_B]
      exact ⟨by linarith, by linarith⟩
    · change d.B (d.g m) ∈ d.W
      rw [d.g_B]
      have hm : m ∈ Set.Ioo d.a d.b := by
        rw [← hu1]
        exact ⟨d.center.1, d.center.2⟩
      exact d.ψ_graph_in_W m hm
  -- the torus neighbourhood V = π₃''U₀
  let V : Set KnotParamTriple := torusQuotient '' U₀
  have hVo : IsOpen V := by
    dsimp [V]
    exact isOpenMap_torusQuotient U₀ hU₀o
  have hVp : torusQuotient (a, (b, m)) ∈ V := by
    dsimp [V]
    exact ⟨d.g m, ⟨hgmU₀, congrArg torusQuotient hgm⟩⟩
  -- continuity of the parametrisation
  have hγc : ContinuousOn γ (Set.Ioo (m - δ) (m + δ)) := by
    dsimp [γ]
    have hg : ContinuousOn d.g (Set.Ioo (m - δ) (m + δ)) := d.continuousOn_g.mono hxIab
    exact continuous_torusQuotient.comp_continuousOn hg
  -- injectivity (the parameter is the third coordinate of the real triple)
  have hγinj : Set.InjOn γ (Set.Ioo (m - δ) (m + δ)) := by
    dsimp [γ]
    exact injOn_torusQuotient_g_of_graphCoord hδw hcoord
  -- base point value
  have hγm : γ m = torusQuotient (a, (b, m)) := by
    change torusQuotient (d.g m) = torusQuotient (a, (b, m))
    rw [hgm]
  -- values stay in the zero set
  have hγzero : ∀ x ∈ Set.Ioo (m - δ) (m + δ), γ x ∈ trisecantZeroSet r := by
    intro x hx
    have hg := d.g_good (hxIab x hx)
    dsimp [γ]
    rw [mem_trisecantZeroSet_iff]
    constructor
    · rw [torusCollinearity_quotient h (d.g x)]
      exact hg.1
    · exact (TorusOffDiag_quotient_iff h (d.g x)).mpr hg.2
  -- values stay in V
  have hγV : ∀ x ∈ Set.Ioo (m - δ) (m + δ), γ x ∈ V := by
    intro x hx
    dsimp [γ, V]
    refine ⟨d.g x, ⟨?_, rfl⟩⟩
    dsimp [U₀]
    constructor
    · change (d.B (d.g x)).1 ∈ Set.Ioo (m - δ) (m + δ)
      rw [d.g_B]
      exact hx
    · change d.B (d.g x) ∈ d.W
      rw [d.g_B]
      exact d.ψ_graph_in_W x (hxIab x hx)
  -- covering: every zero of V lies on the arc
  have hcover : ∀ q ∈ V, q ∈ trisecantZeroSet r →
      ∃ x ∈ Set.Ioo (m - δ) (m + δ), γ x = q := by
    intro q hqV hqZ
    rcases hqV with ⟨w, hwU, hwq⟩
    have hwX : (d.B w).1 ∈ Set.Ioo (m - δ) (m + δ) := hwU.1
    have hwW : d.B w ∈ d.W := hwU.2
    have hq0 : torusCollinearity r q = 0 := (mem_trisecantZeroSet_iff q).mp hqZ |>.1
    have hqOff : q ∈ TorusOffDiag r := (mem_trisecantZeroSet_iff q).mp hqZ |>.2
    have hwZ : collinearityMap r w = 0 := by
      rw [← hwq] at hq0
      rw [torusCollinearity_quotient h w] at hq0
      exact hq0
    have hwOff : w ∈ RealOffDiagonalTriples r := by
      rw [← hwq] at hqOff
      exact (TorusOffDiag_quotient_iff h w).mp hqOff
    have hψ := d.cover (d.B w) (hxIab (d.B w).1 hwX) hwW
      (by simpa [d.BA] using hwZ) (by simpa [d.BA] using hwOff)
    refine ⟨(d.B w).1, hwX, ?_⟩
    dsimp [γ]
    calc
      torusQuotient (d.g (d.B w).1)
          = torusQuotient (d.A ((d.B w).1, d.ψ (d.B w).1)) := by rfl
      _ = torusQuotient (d.A (d.B w)) := by rw [hψ]
      _ = torusQuotient w := by rw [d.BA w]
      _ = q := hwq
  have hγVset : γ '' Set.Ioo (m - δ) (m + δ) ⊆ V := by
    intro q hq
    rcases hq with ⟨x, hx, rfl⟩
    exact hγV x hx
  refine ⟨V, hVo, hVp, γ, hγc, hγinj, hγm, ?_, hγVset, hcover⟩
  · intro q hq
    rcases hq with ⟨x, hx, rfl⟩
    exact hγzero x hx

/-- For the `(A,M)` split, the graph coordinate is the second parameter:
the graph point `γ(x)` has second coordinate `x`. -/
lemma RealGraphArc.g_coord2_AM {r : ℝ → Space} (d : RealGraphArc r)
    (hB : d.B = unSplitAM) (x : ℝ) :
    (d.g x).2.1 = x := by
  have h1 : (d.g x).2.1 = (unSplitAM (d.g x)).1 := by
    simp [unSplitAM]
  have h2 : (unSplitAM (d.g x)).1 = (d.B (d.g x)).1 := by
    rw [hB]
  rw [h1, h2]
  rw [d.g_B]

/-- **Quotient injectivity on the graph (second-parameter variant)**: two
torus-equal graph points with parameter values in an interval of width
`< period` must have equal parameters (the parameter is the second
coordinate of the real triple). -/
lemma injOn_torusQuotient_g_of_graphCoord2 {m δ : ℝ} (hδ : 2 * δ < period)
    {f : ℝ → RealParamTriple} (hf : ∀ x : ℝ, (f x).2.1 = x) :
    Set.InjOn (fun x : ℝ => torusQuotient (f x)) (Set.Ioo (m - δ) (m + δ)) := by
  intro x₁ hx₁ x₂ hx₂ hEq
  have hc := congrArg (fun t : KnotParamTriple => t.2.1) hEq
  have h1 : (torusQuotient (f x₁)).2.1 = ((f x₁).2.1 : KnotParam) := by
    simp [torusQuotient]
  have h2 : (torusQuotient (f x₂)).2.1 = ((f x₂).2.1 : KnotParam) := by
    simp [torusQuotient]
  have hc' : ((f x₁).2.1 : KnotParam) = ((f x₂).2.1 : KnotParam) := by
    rw [← h1, ← h2]
    exact hc
  rw [hf x₁, hf x₂] at hc'
  exact coe_injOn_Ioo (c := m) (η := δ) hδ hx₁ hx₂ hc'

theorem torus_chart_lift_AM {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ)
    {δ : ℝ} (hδpos : 0 < δ) (hδw : 2 * δ < period)
    (d : RealGraphArc r) (hB : d.B = unSplitAM) (hA : d.A = splitAM)
    (hu : d.u = (b, (a, m)))
    (hL : d.a < b - δ) (hR : b + δ < d.b) :
    ∃ V : Set KnotParamTriple, IsOpen V ∧ torusQuotient (a, (b, m)) ∈ V ∧
      ∃ γ : ℝ → KnotParamTriple,
        ContinuousOn γ (Set.Ioo (b - δ) (b + δ)) ∧
          Set.InjOn γ (Set.Ioo (b - δ) (b + δ)) ∧ γ b = torusQuotient (a, (b, m)) ∧
          γ '' Set.Ioo (b - δ) (b + δ) ⊆ trisecantZeroSet r ∧
          γ '' Set.Ioo (b - δ) (b + δ) ⊆ V ∧
          (∀ q ∈ V, q ∈ trisecantZeroSet r → ∃ x ∈ Set.Ioo (b - δ) (b + δ), γ x = q) := by
  let γ : ℝ → KnotParamTriple := fun x => torusQuotient (d.g x)
  have hcoord : ∀ x : ℝ, (d.g x).2.1 = x := d.g_coord2_AM hB
  -- the real "curve window" U₀ = {q | (B q).1 ∈ (m−δ,m+δ)} ∩ B⁻¹'(W)
  let U₀ : Set RealParamTriple :=
    {q : RealParamTriple | (d.B q).1 ∈ Set.Ioo (b - δ) (b + δ)} ∩ (d.B ⁻¹' d.W)
  have hU₀o : IsOpen U₀ := by
    dsimp [U₀]
    have hBfst : Continuous (fun q : RealParamTriple => (d.B q).1) := Continuous.fst d.B_cont
    exact (isOpen_Ioo.preimage hBfst).inter (d.W_open.preimage d.B_cont)
  have hxIab : ∀ x : ℝ, x ∈ Set.Ioo (b - δ) (b + δ) → x ∈ Set.Ioo d.a d.b := by
    intro x hx
    constructor <;> linarith [hL, hR, hx.1, hx.2]
  have hu1 : d.u.1 = b := by rw [hu]
  -- the base graph point equals (a,(b,m))
  have hgm : d.g b = (a, (b, m)) := by
    rw [← hu1]
    have hgAu : d.g d.u.1 = d.A d.u := by
      unfold RealGraphArc.g
      congr 1
      ext <;> simp [d.ψu]
    rw [hgAu, hA, hu]
    simp [splitAM]
  -- the graph point at m lies in the curve window
  have hgmU₀ : d.g b ∈ U₀ := by
    dsimp [U₀]
    constructor
    · change (d.B (d.g b)).1 ∈ Set.Ioo (b - δ) (b + δ)
      rw [d.g_B]
      exact ⟨by linarith, by linarith⟩
    · change d.B (d.g b) ∈ d.W
      rw [d.g_B]
      have hb₀ : b ∈ Set.Ioo d.a d.b := by
        rw [← hu1]
        exact ⟨d.center.1, d.center.2⟩
      exact d.ψ_graph_in_W b hb₀
  -- the torus neighbourhood V = π₃''U₀
  let V : Set KnotParamTriple := torusQuotient '' U₀
  have hVo : IsOpen V := by
    dsimp [V]
    exact isOpenMap_torusQuotient U₀ hU₀o
  have hVp : torusQuotient (a, (b, m)) ∈ V := by
    dsimp [V]
    exact ⟨d.g b, ⟨hgmU₀, congrArg torusQuotient hgm⟩⟩
  -- continuity of the parametrisation
  have hγc : ContinuousOn γ (Set.Ioo (b - δ) (b + δ)) := by
    dsimp [γ]
    have hg : ContinuousOn d.g (Set.Ioo (b - δ) (b + δ)) := d.continuousOn_g.mono hxIab
    exact continuous_torusQuotient.comp_continuousOn hg
  -- injectivity (the parameter is the third coordinate of the real triple)
  have hγinj : Set.InjOn γ (Set.Ioo (b - δ) (b + δ)) := by
    dsimp [γ]
    exact injOn_torusQuotient_g_of_graphCoord2 hδw hcoord
  -- base point value
  have hγm : γ b = torusQuotient (a, (b, m)) := by
    change torusQuotient (d.g b) = torusQuotient (a, (b, m))
    rw [hgm]
  -- values stay in the zero set
  have hγzero : ∀ x ∈ Set.Ioo (b - δ) (b + δ), γ x ∈ trisecantZeroSet r := by
    intro x hx
    have hg := d.g_good (hxIab x hx)
    dsimp [γ]
    rw [mem_trisecantZeroSet_iff]
    constructor
    · rw [torusCollinearity_quotient h (d.g x)]
      exact hg.1
    · exact (TorusOffDiag_quotient_iff h (d.g x)).mpr hg.2
  -- values stay in V
  have hγV : ∀ x ∈ Set.Ioo (b - δ) (b + δ), γ x ∈ V := by
    intro x hx
    dsimp [γ, V]
    refine ⟨d.g x, ⟨?_, rfl⟩⟩
    dsimp [U₀]
    constructor
    · change (d.B (d.g x)).1 ∈ Set.Ioo (b - δ) (b + δ)
      rw [d.g_B]
      exact hx
    · change d.B (d.g x) ∈ d.W
      rw [d.g_B]
      exact d.ψ_graph_in_W x (hxIab x hx)
  -- covering: every zero of V lies on the arc
  have hcover : ∀ q ∈ V, q ∈ trisecantZeroSet r →
      ∃ x ∈ Set.Ioo (b - δ) (b + δ), γ x = q := by
    intro q hqV hqZ
    rcases hqV with ⟨w, hwU, hwq⟩
    have hwX : (d.B w).1 ∈ Set.Ioo (b - δ) (b + δ) := hwU.1
    have hwW : d.B w ∈ d.W := hwU.2
    have hq0 : torusCollinearity r q = 0 := (mem_trisecantZeroSet_iff q).mp hqZ |>.1
    have hqOff : q ∈ TorusOffDiag r := (mem_trisecantZeroSet_iff q).mp hqZ |>.2
    have hwZ : collinearityMap r w = 0 := by
      rw [← hwq] at hq0
      rw [torusCollinearity_quotient h w] at hq0
      exact hq0
    have hwOff : w ∈ RealOffDiagonalTriples r := by
      rw [← hwq] at hqOff
      exact (TorusOffDiag_quotient_iff h w).mp hqOff
    have hψ := d.cover (d.B w) (hxIab (d.B w).1 hwX) hwW
      (by simpa [d.BA] using hwZ) (by simpa [d.BA] using hwOff)
    refine ⟨(d.B w).1, hwX, ?_⟩
    dsimp [γ]
    calc
      torusQuotient (d.g (d.B w).1)
          = torusQuotient (d.A ((d.B w).1, d.ψ (d.B w).1)) := by rfl
      _ = torusQuotient (d.A (d.B w)) := by rw [hψ]
      _ = torusQuotient w := by rw [d.BA w]
      _ = q := hwq
  have hγVset : γ '' Set.Ioo (b - δ) (b + δ) ⊆ V := by
    intro q hq
    rcases hq with ⟨x, hx, rfl⟩
    exact hγV x hx
  refine ⟨V, hVo, hVp, γ, hγc, hγinj, hγm, ?_, hγVset, hcover⟩
  · intro q hq
    rcases hq with ⟨x, hx, rfl⟩
    exact hγzero x hx

/-- For the `(B,M)` split (identity), the graph coordinate is the first
parameter: the graph point `γ(x)` has first coordinate `x`. -/
lemma RealGraphArc.g_coord1_BM {r : ℝ → Space} (d : RealGraphArc r)
    (hB : d.B = unSplitBM) (x : ℝ) :
    (d.g x).1 = x := by
  have hBx : d.g x = (x, d.ψ x) := by
    have h := d.g_B x
    rw [hB] at h
    simpa [unSplitBM] using h
  rw [hBx]

/-- **Quotient injectivity on the graph (first-parameter variant)**: two
torus-equal graph points with parameter values in an interval of width
`< period` must have equal parameters (the parameter is the first coordinate
of the real triple). -/
lemma injOn_torusQuotient_g_of_graphCoord1 {m δ : ℝ} (hδ : 2 * δ < period)
    {f : ℝ → RealParamTriple} (hf : ∀ x : ℝ, (f x).1 = x) :
    Set.InjOn (fun x : ℝ => torusQuotient (f x)) (Set.Ioo (m - δ) (m + δ)) := by
  intro x₁ hx₁ x₂ hx₂ hEq
  have hc := congrArg (fun t : KnotParamTriple => t.1) hEq
  have h1 : (torusQuotient (f x₁)).1 = ((f x₁).1 : KnotParam) := by
    simp [torusQuotient]
  have h2 : (torusQuotient (f x₂)).1 = ((f x₂).1 : KnotParam) := by
    simp [torusQuotient]
  have hc' : ((f x₁).1 : KnotParam) = ((f x₂).1 : KnotParam) := by
    rw [← h1, ← h2]
    exact hc
  rw [hf x₁, hf x₂] at hc'
  exact coe_injOn_Ioo (c := m) (η := δ) hδ hx₁ hx₂ hc'

theorem torus_chart_lift_BM {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ)
    {δ : ℝ} (hδpos : 0 < δ) (hδw : 2 * δ < period)
    (d : RealGraphArc r) (hB : d.B = unSplitBM) (hA : d.A = splitBM)
    (hu : d.u = (a, (b, m)))
    (hL : d.a < a - δ) (hR : a + δ < d.b) :
    ∃ V : Set KnotParamTriple, IsOpen V ∧ torusQuotient (a, (b, m)) ∈ V ∧
      ∃ γ : ℝ → KnotParamTriple,
        ContinuousOn γ (Set.Ioo (a - δ) (a + δ)) ∧
          Set.InjOn γ (Set.Ioo (a - δ) (a + δ)) ∧ γ a = torusQuotient (a, (b, m)) ∧
          γ '' Set.Ioo (a - δ) (a + δ) ⊆ trisecantZeroSet r ∧
          γ '' Set.Ioo (a - δ) (a + δ) ⊆ V ∧
          (∀ q ∈ V, q ∈ trisecantZeroSet r → ∃ x ∈ Set.Ioo (a - δ) (a + δ), γ x = q) := by
  let γ : ℝ → KnotParamTriple := fun x => torusQuotient (d.g x)
  have hcoord : ∀ x : ℝ, (d.g x).1 = x := d.g_coord1_BM hB
  -- the real "curve window" U₀ = {q | (B q).1 ∈ (m−δ,m+δ)} ∩ B⁻¹'(W)
  let U₀ : Set RealParamTriple :=
    {q : RealParamTriple | (d.B q).1 ∈ Set.Ioo (a - δ) (a + δ)} ∩ (d.B ⁻¹' d.W)
  have hU₀o : IsOpen U₀ := by
    dsimp [U₀]
    have hBfst : Continuous (fun q : RealParamTriple => (d.B q).1) := Continuous.fst d.B_cont
    exact (isOpen_Ioo.preimage hBfst).inter (d.W_open.preimage d.B_cont)
  have hxIab : ∀ x : ℝ, x ∈ Set.Ioo (a - δ) (a + δ) → x ∈ Set.Ioo d.a d.b := by
    intro x hx
    constructor <;> linarith [hL, hR, hx.1, hx.2]
  have hu1 : d.u.1 = a := by rw [hu]
  -- the base graph point equals (a,(b,m))
  have hgm : d.g a = (a, (b, m)) := by
    rw [← hu1]
    have hgAu : d.g d.u.1 = d.A d.u := by
      unfold RealGraphArc.g
      congr 1
      ext <;> simp [d.ψu]
    rw [hgAu, hA, hu]
    simp [splitBM]
  -- the graph point at m lies in the curve window
  have hgmU₀ : d.g a ∈ U₀ := by
    dsimp [U₀]
    constructor
    · change (d.B (d.g a)).1 ∈ Set.Ioo (a - δ) (a + δ)
      rw [d.g_B]
      exact ⟨by linarith, by linarith⟩
    · change d.B (d.g a) ∈ d.W
      rw [d.g_B]
      have ha₀ : a ∈ Set.Ioo d.a d.b := by
        rw [← hu1]
        exact ⟨d.center.1, d.center.2⟩
      exact d.ψ_graph_in_W a ha₀
  -- the torus neighbourhood V = π₃''U₀
  let V : Set KnotParamTriple := torusQuotient '' U₀
  have hVo : IsOpen V := by
    dsimp [V]
    exact isOpenMap_torusQuotient U₀ hU₀o
  have hVp : torusQuotient (a, (b, m)) ∈ V := by
    dsimp [V]
    exact ⟨d.g a, ⟨hgmU₀, congrArg torusQuotient hgm⟩⟩
  -- continuity of the parametrisation
  have hγc : ContinuousOn γ (Set.Ioo (a - δ) (a + δ)) := by
    dsimp [γ]
    have hg : ContinuousOn d.g (Set.Ioo (a - δ) (a + δ)) := d.continuousOn_g.mono hxIab
    exact continuous_torusQuotient.comp_continuousOn hg
  -- injectivity (the parameter is the third coordinate of the real triple)
  have hγinj : Set.InjOn γ (Set.Ioo (a - δ) (a + δ)) := by
    dsimp [γ]
    exact injOn_torusQuotient_g_of_graphCoord1 hδw hcoord
  -- base point value
  have hγm : γ a = torusQuotient (a, (b, m)) := by
    change torusQuotient (d.g a) = torusQuotient (a, (b, m))
    rw [hgm]
  -- values stay in the zero set
  have hγzero : ∀ x ∈ Set.Ioo (a - δ) (a + δ), γ x ∈ trisecantZeroSet r := by
    intro x hx
    have hg := d.g_good (hxIab x hx)
    dsimp [γ]
    rw [mem_trisecantZeroSet_iff]
    constructor
    · rw [torusCollinearity_quotient h (d.g x)]
      exact hg.1
    · exact (TorusOffDiag_quotient_iff h (d.g x)).mpr hg.2
  -- values stay in V
  have hγV : ∀ x ∈ Set.Ioo (a - δ) (a + δ), γ x ∈ V := by
    intro x hx
    dsimp [γ, V]
    refine ⟨d.g x, ⟨?_, rfl⟩⟩
    dsimp [U₀]
    constructor
    · change (d.B (d.g x)).1 ∈ Set.Ioo (a - δ) (a + δ)
      rw [d.g_B]
      exact hx
    · change d.B (d.g x) ∈ d.W
      rw [d.g_B]
      exact d.ψ_graph_in_W x (hxIab x hx)
  -- covering: every zero of V lies on the arc
  have hcover : ∀ q ∈ V, q ∈ trisecantZeroSet r →
      ∃ x ∈ Set.Ioo (a - δ) (a + δ), γ x = q := by
    intro q hqV hqZ
    rcases hqV with ⟨w, hwU, hwq⟩
    have hwX : (d.B w).1 ∈ Set.Ioo (a - δ) (a + δ) := hwU.1
    have hwW : d.B w ∈ d.W := hwU.2
    have hq0 : torusCollinearity r q = 0 := (mem_trisecantZeroSet_iff q).mp hqZ |>.1
    have hqOff : q ∈ TorusOffDiag r := (mem_trisecantZeroSet_iff q).mp hqZ |>.2
    have hwZ : collinearityMap r w = 0 := by
      rw [← hwq] at hq0
      rw [torusCollinearity_quotient h w] at hq0
      exact hq0
    have hwOff : w ∈ RealOffDiagonalTriples r := by
      rw [← hwq] at hqOff
      exact (TorusOffDiag_quotient_iff h w).mp hqOff
    have hψ := d.cover (d.B w) (hxIab (d.B w).1 hwX) hwW
      (by simpa [d.BA] using hwZ) (by simpa [d.BA] using hwOff)
    refine ⟨(d.B w).1, hwX, ?_⟩
    dsimp [γ]
    calc
      torusQuotient (d.g (d.B w).1)
          = torusQuotient (d.A ((d.B w).1, d.ψ (d.B w).1)) := by rfl
      _ = torusQuotient (d.A (d.B w)) := by rw [hψ]
      _ = torusQuotient w := by rw [d.BA w]
      _ = q := hwq
  have hγVset : γ '' Set.Ioo (a - δ) (a + δ) ⊆ V := by
    intro q hq
    rcases hq with ⟨x, hx, rfl⟩
    exact hγV x hx
  refine ⟨V, hVo, hVp, γ, hγc, hγinj, hγm, ?_, hγVset, hcover⟩
  · intro q hq
    rcases hq with ⟨x, hx, rfl⟩
    exact hγzero x hx

end LeanEval.KnotTheory.Quadrisecant
