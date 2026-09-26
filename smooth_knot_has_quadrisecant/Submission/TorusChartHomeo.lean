import Mathlib
import ChallengeDeps
import Submission.TorusChartLift

open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Real Topology

/-!
# Layer A (xiv) — chart homeomorphisms: the trisecant zero set is covered
by honest 1-dimensional charts

`TorusAtlas.lean` (Layer A (xiii)) assembled, for each collinear
off-diagonal torus triple of a general-position smooth knot, a
`ZeroSetChart`: an injective continuous curve `γ(x) = torusQuotient (d.g x)`
over an open interval whose image is *exactly* the trisecant zero set inside
an open torus neighbourhood `V`.  The curve is injective, but that alone
does **not** make it a homeomorphism onto its image (a continuous injective
map from an open interval need not be open).  This module supplies the
missing half — the **open-map property** — from the graph-arc structure:

1. **`RealGraphArc.zeroSet_trace_open`** — the *open-trace identity*: for
   any parameter interval `J` inside `(a,b)` the curve images exactly
   the zero set sitting over `J`:
   `γ '' J = trisecantZeroSet r ∩ torusQuotient '' {w | (d.B w).1 ∈ J ∧ d.B w ∈ d.W}`.
   Forward: `d.g x` lies over `J` (`(B(γ x)).1 = x` by `g_B`, and
   `B(γ x) = (x,ψ x) ∈ W` by `ψ_graph_in_W`).  Backward: any zero `w` over
   `J` is collinear off-diagonal, so the graph-arc covering property
   (`RealGraphArc.cover`) gives `ψ((B w).1) = (B w).2`, i.e. the real point
   `A(B w) = w` is the graph point at parameter `(B w).1`.  Uniform in the
   chart — no per-witness case split.
2. **`torus_chart_homeo`** — assembled *homeo theorem*: for a graph arc and
   a parameter interval `(lo,hi) ⊆ (a,b)` on which the quotient curve is
   injective, the curve is a **homeomorphism from the open interval onto
   the zero set inside its chart neighbourhood `V`** (which is open).  The
   inverse continuity is obtained via `IsHomeomorph`: the curve is a
   continuous bijection onto `Z ∩ V` and the open-trace identity makes it
   an *open map* (image of an open `J ⊆ (lo,hi)` is the zero-set points
   over the open window `{w | (B w).1 ∈ J}`, open in `Z ∩ V`).

Together with the cover theorems of `TorusAtlas.lean` this gives the honest
local chart structure of the trisecant zero set: every point has a
neighbourhood inside `Z` homeomorphic to an open interval of `ℝ` — the
starting point of the component / 1-manifold analysis of Layer A.

Everything here is elementary and verified (no axioms, no `sorry`).
-/

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-- The real **curve window over an interval `J`**: points whose first split
coordinate lies in `J` and whose split data lie in the `ψ`-covering
neighbourhood `W`.  (For the `(A,B)` split the coordinate `(B w).1` is the
third parameter, for `(A,M)` the second and for `(B,M)` the first — the
definition is uniform.) -/
def chartWindow {r : ℝ → Space} (d : RealGraphArc r) (J : Set ℝ) : Set RealParamTriple :=
  {w : RealParamTriple | (d.B w).1 ∈ J ∧ d.B w ∈ d.W}

/-- The window over an open interval is open in the real parameter space
(`(B ·).1` and `B` are continuous, `W` is open). -/
lemma isOpen_chartWindow {r : ℝ → Space} (d : RealGraphArc r) {J : Set ℝ}
    (hJo : IsOpen J) : IsOpen (chartWindow d J) := by
  unfold chartWindow
  have hBfst : Continuous (fun w : RealParamTriple => (d.B w).1) := Continuous.fst d.B_cont
  exact hJo.preimage hBfst |>.inter (d.W_open.preimage d.B_cont)

/-- A graph point over `x ∈ (a,b)` is a zero of the *torus* collinearity
map and off-diagonal, i.e. lies in the trisecant zero set. -/
lemma RealGraphArc.torus_g_mem {r : ℝ → Space} (h : IsSmoothKnot r) (d : RealGraphArc r)
    {x : ℝ} (hx : x ∈ Set.Ioo d.a d.b) :
    torusQuotient (d.g x) ∈ trisecantZeroSet r := by
  rw [mem_trisecantZeroSet_iff]
  have hg := d.g_good hx
  constructor
  · rw [torusCollinearity_quotient h (d.g x)]
    exact hg.1
  · exact (TorusOffDiag_quotient_iff h (d.g x)).mpr hg.2

/-- A graph point over `x ∈ J` lies in the image of the window over `J`
(`(B (γ x)).1 = x` and `B (γ x) = (x, ψ x) ∈ W`). -/
lemma RealGraphArc.g_mem_chartWindow {r : ℝ → Space} (d : RealGraphArc r) {J : Set ℝ}
    {x : ℝ} (hxJ : x ∈ J) (hxab : x ∈ Set.Ioo d.a d.b) :
    d.g x ∈ chartWindow d J := by
  unfold chartWindow
  constructor
  · rw [d.g_B]
    exact hxJ
  · rw [d.g_B]
    exact d.ψ_graph_in_W x hxab

/-- **The open-trace identity.**  For an interval `J` inside the graph
parameter interval `(a,b)`, the curve images over `J` exactly the trisecant
zero set whose (real) points lie over `J`:
`γ '' J = trisecantZeroSet r ∩ torusQuotient '' (chartWindow d J)`. -/
theorem RealGraphArc.zeroSet_trace_open {r : ℝ → Space} (h : IsSmoothKnot r)
    (d : RealGraphArc r) {J : Set ℝ} (hJab : J ⊆ Set.Ioo d.a d.b) :
    (fun x : ℝ => torusQuotient (d.g x)) '' J =
      trisecantZeroSet r ∩ torusQuotient '' chartWindow d J := by
  ext q
  constructor
  · rintro ⟨x, hxJ, rfl⟩
    constructor
    · exact d.torus_g_mem h (hJab hxJ)
    · exact ⟨d.g x, d.g_mem_chartWindow hxJ (hJab hxJ), rfl⟩
  · rintro ⟨qZ, w, hw, rfl⟩
    rcases hw with ⟨hwJ, hwW⟩
    let x₀ : ℝ := (d.B w).1
    have hx₀J : x₀ ∈ J := hwJ
    have hx₀ab : x₀ ∈ Set.Ioo d.a d.b := hJab hx₀J
    refine ⟨x₀, hx₀J, ?_⟩
    -- q = π(w) is a collinear off-diagonal torus zero; the real point w is
    -- the same by the bridge lemmas.
    have hqZ : torusQuotient w ∈ trisecantZeroSet r := qZ
    have hq0 : torusCollinearity r (torusQuotient w) = 0 :=
      (mem_trisecantZeroSet_iff (torusQuotient w)).mp hqZ |>.1
    have hwZ : collinearityMap r w = 0 := by
      have hb := torusCollinearity_quotient h w
      rw [hb] at hq0
      exact hq0
    have hwOff : w ∈ RealOffDiagonalTriples r := by
      exact (TorusOffDiag_quotient_iff h w).mp ((mem_trisecantZeroSet_iff (torusQuotient w)).mp hqZ |>.2)
    have hψ : d.ψ x₀ = (d.B w).2 := by
      have hz1 : (d.B w).1 ∈ Set.Ioo d.a d.b := hx₀ab
      have hA0 : collinearityMap r (d.A (d.B w)) = 0 := by
        simpa [d.BA] using hwZ
      have hAOff : d.A (d.B w) ∈ RealOffDiagonalTriples r := by
        simpa [d.BA] using hwOff
      exact d.cover (d.B w) hz1 hwW hA0 hAOff
    -- the graph point at x₀ is the real point w
    have hg : d.g x₀ = w := by
      dsimp [x₀, RealGraphArc.g]
      rw [hψ]
      exact d.BA w
    change torusQuotient (d.g x₀) = torusQuotient w
    rw [hg]

/-! ## 2. The chart curve is a homeomorphism onto its zero-set trace -/

/-- **Chart homeo theorem (generic).**  Let `d` be a graph arc of the
trisecant zero set and `(lo,hi) ⊆ (a,b)` a parameter interval on which the
quotient curve `γ(x) = torusQuotient (d.g x)` is injective.  Then there is
an open torus neighbourhood `V` of the curve over `(lo,hi)` such that `γ`
is a **homeomorphism from the open interval onto `trisecantZeroSet r ∩ V`**
(subspace topology of the torus).  The inverse continuity is not automatic
from injectivity — it comes from the open-trace identity: over any open
sub-interval `J`, `γ '' J` is the zero set over the open window
`{w | (d.B w).1 ∈ J}`, open in `Z ∩ V`. -/
theorem torus_chart_homeo {r : ℝ → Space} (h : IsSmoothKnot r) (d : RealGraphArc r)
    {lo hi : ℝ} (hIab : Set.Ioo lo hi ⊆ Set.Ioo d.a d.b)
    (hγinj : Set.InjOn (fun x : ℝ => torusQuotient (d.g x)) (Set.Ioo lo hi)) :
    ∃ V : Set KnotParamTriple, IsOpen V ∧
      ∃ e : {x : ℝ // x ∈ Set.Ioo lo hi} ≃ₜ
          {q : KnotParamTriple // q ∈ trisecantZeroSet r ∧ q ∈ V},
        ∀ x : {x : ℝ // x ∈ Set.Ioo lo hi}, (e x).1 = torusQuotient (d.g x.1) := by
  let V : Set KnotParamTriple := torusQuotient '' chartWindow d (Set.Ioo lo hi)
  have hVo : IsOpen V := by
    dsimp [V]
    exact isOpenMap_torusQuotient (chartWindow d (Set.Ioo lo hi)) (isOpen_chartWindow d isOpen_Ioo)
  -- the full-interval trace: γ '' (lo,hi) = Z ∩ V
  have hfull : (fun x : ℝ => torusQuotient (d.g x)) '' Set.Ioo lo hi =
      trisecantZeroSet r ∩ V := by
    dsimp [V]
    exact d.zeroSet_trace_open h hIab
  let Y : Type := {q : KnotParamTriple // q ∈ trisecantZeroSet r ∧ q ∈ V}
  let f : {x : ℝ // x ∈ Set.Ioo lo hi} → Y := fun x =>
    ⟨torusQuotient (d.g x.1), ⟨d.torus_g_mem h (hIab x.2),
      ⟨d.g x.1, d.g_mem_chartWindow (J := Set.Ioo lo hi) x.2 (hIab x.2), rfl⟩⟩⟩
  -- continuity of the value map γ ∘ coe (the composition of continuous
  -- maps along the graph, which is continuous on (a,b) ⊇ (lo,hi))
  have hFcont : Continuous (fun x : {t : ℝ // t ∈ Set.Ioo lo hi} =>
      torusQuotient (d.g (x : ℝ))) := by
    rw [continuous_iff_continuousAt]
    intro x
    have hxab : (x : ℝ) ∈ Set.Ioo d.a d.b := hIab x.2
    have hcat : ContinuousAt d.g (x : ℝ) := d.continuousAt_g hxab
    have hval : ContinuousAt (fun y : {t : ℝ // t ∈ Set.Ioo lo hi} => (y : ℝ)) x :=
      continuous_subtype_val.continuousAt
    exact (continuous_torusQuotient.continuousAt).comp (hcat.comp hval)
  -- continuity of f: open sets of the subtype Y are pulled back from the
  -- ambient torus, and under f they pull back to preimages under the value
  -- map γ, which is continuous.
  have hfcont : Continuous f := by
    rw [continuous_def]
    intro U hUo
    rw [isOpen_induced_iff] at hUo
    rcases hUo with ⟨W, hWo, hUW⟩
    have hpre : f ⁻¹' U =
        (fun x : {t : ℝ // t ∈ Set.Ioo lo hi} => torusQuotient (d.g (x : ℝ))) ⁻¹' W := by
      ext x
      constructor
      · intro hx
        simpa [f, ← hUW] using hx
      · intro hx
        rw [← hUW]
        simpa [f] using hx
    rw [hpre]
    exact IsOpen.preimage hFcont hWo
  -- injectivity
  have hinj : Function.Injective f := by
    intro x₁ x₂ hEq
    have hEq' : torusQuotient (d.g x₁.1) = torusQuotient (d.g x₂.1) := by
      simpa [f] using congrArg (fun q : Y => (q : KnotParamTriple)) hEq
    apply Subtype.ext
    exact hγinj x₁.2 x₂.2 hEq'
  -- surjectivity: every zero of V lies on the curve (the full trace), and
  -- the curve point with that parameter maps to it.
  have hsurj : Function.Surjective f := by
    intro y
    have hy : (y : KnotParamTriple) ∈ (fun x : ℝ => torusQuotient (d.g x)) '' Set.Ioo lo hi := by
      rw [hfull]
      exact ⟨y.2.1, y.2.2⟩
    rcases hy with ⟨x₀, hx₀, hxq⟩
    refine ⟨⟨x₀, hx₀⟩, ?_⟩
    apply Subtype.ext
    simpa [f] using hxq
  -- openness: over an open U of the interval, the image is the set of zeros
  -- lying over the corresponding open window (open in Z ∩ V by the trace).
  have hfopen : IsOpenMap f := by
    intro U hUo
    -- open sets of the interval subtype are pulled back from ℝ
    rw [isOpen_induced_iff] at hUo
    rcases hUo with ⟨O, hOo, hUO⟩
    let J : Set ℝ := O ∩ Set.Ioo lo hi
    have hJo : IsOpen J := hOo.inter isOpen_Ioo
    have hJab : J ⊆ Set.Ioo d.a d.b := fun x hx => hIab hx.2
    have hUJ : U = {x : {t : ℝ // t ∈ Set.Ioo lo hi} | (x : ℝ) ∈ J} := by
      ext x
      constructor
      · intro hx
        rw [← hUO] at hx
        exact ⟨hx, x.2⟩
      · intro hxJ
        rw [← hUO]
        exact hxJ.1
    -- image of U under f = zeros over J
    have himg : f '' U = {y : Y | (y : KnotParamTriple) ∈
        (fun x : ℝ => torusQuotient (d.g x)) '' J} := by
      ext y
      constructor
      · rintro ⟨x, hxU, rfl⟩
        have hxJ : (x : ℝ) ∈ J := by
          rw [hUJ] at hxU
          exact hxU
        exact ⟨x.1, hxJ, rfl⟩
      · intro hyJ
        rcases hyJ with ⟨x₀, hx₀J, hxq₀⟩
        refine ⟨⟨x₀, hx₀J.2⟩, ?_, ?_⟩
        · rw [hUJ]
          exact hx₀J
        · apply Subtype.ext
          simpa [f] using hxq₀
    -- y ∈ Y has y.1 ∈ Z automatically, so membership over J is openness in Y
    have hZy : ∀ y : Y, (y : KnotParamTriple) ∈ trisecantZeroSet r := fun y => y.2.1
    have hW : IsOpen {y : Y | (y : KnotParamTriple) ∈
        torusQuotient '' chartWindow d J} := by
      have hWopen : IsOpen (torusQuotient '' chartWindow d J) :=
        isOpenMap_torusQuotient (chartWindow d J) (isOpen_chartWindow d hJo)
      -- preimage of an open torus set under the continuous value projection
      rw [isOpen_induced_iff]
      refine ⟨torusQuotient '' chartWindow d J, hWopen, ?_⟩
      ext y
      simp
    rw [himg]
    -- over Y (whose points lie in Z), membership in γ '' J reduces to
    -- membership in the open window image (the open-trace identity)
    have hmain : {y : Y | (y : KnotParamTriple) ∈
          (fun x : ℝ => torusQuotient (d.g x)) '' J} =
        {y : Y | (y : KnotParamTriple) ∈ torusQuotient '' chartWindow d J} := by
      ext y
      have ht := d.zeroSet_trace_open h (J := J) hJab
      constructor
      · intro hyγ
        have hyzw : (y : KnotParamTriple) ∈ trisecantZeroSet r ∩ torusQuotient '' chartWindow d J := by
          rw [← ht]
          exact hyγ
        exact hyzw.2
      · intro hyW
        rw [ht]
        exact ⟨hZy y, hyW⟩
    rw [hmain]
    exact hW
  -- assemble
  refine ⟨V, hVo, (Equiv.ofBijective f ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen hfcont hfopen, ?_⟩
  intro x
  rfl

/-! ## 3. The three witness instantiations -/

/-- **`(A,B)` chart homeo**: a collinear off-diagonal triple with independent
`a`/`b` partials yields a homeomorphism of `(m−δ,m+δ)` onto the trisecant
zero set inside an open torus neighbourhood `V` of the base point, tracing
`x ↦ torusQuotient (d.g x)` and sending `m` to `torusQuotient (a,(b,m))`. -/
theorem torus_chart_homeo_AB {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ)
    {δ : ℝ} (hδpos : 0 < δ) (hδw : 2 * δ < period)
    (d : RealGraphArc r) (hB : d.B = unSplitAB) (hA : d.A = splitAB)
    (hu : d.u = (m, (a, b))) (hL : d.a < m - δ) (hR : m + δ < d.b) :
    ∃ V : Set KnotParamTriple, IsOpen V ∧
      torusQuotient (a, (b, m)) ∈ trisecantZeroSet r ∧ torusQuotient (a, (b, m)) ∈ V ∧
      ∃ e : {x : ℝ // x ∈ Set.Ioo (m - δ) (m + δ)} ≃ₜ
          {q : KnotParamTriple // q ∈ trisecantZeroSet r ∧ q ∈ V},
        (e ⟨m, by constructor <;> linarith⟩).1 = torusQuotient (a, (b, m)) ∧
        ∀ x : {x : ℝ // x ∈ Set.Ioo (m - δ) (m + δ)}, (e x).1 = torusQuotient (d.g x.1) := by
  have hIab : Set.Ioo (m - δ) (m + δ) ⊆ Set.Ioo d.a d.b := by
    intro x hx
    constructor <;> linarith [hL, hR, hx.1, hx.2]
  have hγinj : Set.InjOn (fun x : ℝ => torusQuotient (d.g x)) (Set.Ioo (m - δ) (m + δ)) :=
    injOn_torusQuotient_g_of_graphCoord (m := m) (δ := δ) hδw (f := d.g)
      (fun x => d.g_coord3_AB hB x)
  rcases torus_chart_homeo h d (lo := m - δ) (hi := m + δ) hIab hγinj with ⟨V, hVo, e, htrace⟩
  have hu1 : d.u.1 = m := by rw [hu]
  have hm : m ∈ Set.Ioo (m - δ) (m + δ) := by constructor <;> linarith
  have hgm : d.g m = (a, (b, m)) := by
    rw [← hu1]
    have hgAu : d.g d.u.1 = d.A d.u := by
      unfold RealGraphArc.g
      congr 1
      ext <;> simp [d.ψu]
    rw [hgAu, hA, hu]
    simp [splitAB]
  have hval : (e ⟨m, hm⟩).1 = torusQuotient (d.g m) := htrace ⟨m, hm⟩
  refine ⟨V, hVo, ?_, ?_, e, ?_, htrace⟩
  · rw [← hgm, ← hval]
    exact (e ⟨m, hm⟩).2.1
  · rw [← hgm, ← hval]
    exact (e ⟨m, hm⟩).2.2
  · calc
      (e ⟨m, hm⟩).1 = torusQuotient (d.g m) := htrace ⟨m, hm⟩
      _ = torusQuotient (a, (b, m)) := by rw [hgm]

/-- **`(A,M)` chart homeo**: the mirror of `torus_chart_homeo_AB` for
independent `a`/`m` partials: the graph parameter is `b` (interval
`(b−δ,b+δ)`), the base point sent to `torusQuotient (a,(b,m))`. -/
theorem torus_chart_homeo_AM {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ)
    {δ : ℝ} (hδpos : 0 < δ) (hδw : 2 * δ < period)
    (d : RealGraphArc r) (hB : d.B = unSplitAM) (hA : d.A = splitAM)
    (hu : d.u = (b, (a, m))) (hL : d.a < b - δ) (hR : b + δ < d.b) :
    ∃ V : Set KnotParamTriple, IsOpen V ∧
      torusQuotient (a, (b, m)) ∈ trisecantZeroSet r ∧ torusQuotient (a, (b, m)) ∈ V ∧
      ∃ e : {x : ℝ // x ∈ Set.Ioo (b - δ) (b + δ)} ≃ₜ
          {q : KnotParamTriple // q ∈ trisecantZeroSet r ∧ q ∈ V},
        (e ⟨b, by constructor <;> linarith⟩).1 = torusQuotient (a, (b, m)) ∧
        ∀ x : {x : ℝ // x ∈ Set.Ioo (b - δ) (b + δ)}, (e x).1 = torusQuotient (d.g x.1) := by
  have hIab : Set.Ioo (b - δ) (b + δ) ⊆ Set.Ioo d.a d.b := by
    intro x hx
    constructor <;> linarith [hL, hR, hx.1, hx.2]
  have hγinj : Set.InjOn (fun x : ℝ => torusQuotient (d.g x)) (Set.Ioo (b - δ) (b + δ)) :=
    injOn_torusQuotient_g_of_graphCoord2 (m := b) (δ := δ) hδw (f := d.g)
      (fun x => d.g_coord2_AM hB x)
  rcases torus_chart_homeo h d (lo := b - δ) (hi := b + δ) hIab hγinj with ⟨V, hVo, e, htrace⟩
  have hu1 : d.u.1 = b := by rw [hu]
  have hb : b ∈ Set.Ioo (b - δ) (b + δ) := by constructor <;> linarith
  have hgm : d.g b = (a, (b, m)) := by
    rw [← hu1]
    have hgAu : d.g d.u.1 = d.A d.u := by
      unfold RealGraphArc.g
      congr 1
      ext <;> simp [d.ψu]
    rw [hgAu, hA, hu]
    simp [splitAM]
  have hval : (e ⟨b, hb⟩).1 = torusQuotient (d.g b) := htrace ⟨b, hb⟩
  refine ⟨V, hVo, ?_, ?_, e, ?_, htrace⟩
  · rw [← hgm, ← hval]
    exact (e ⟨b, hb⟩).2.1
  · rw [← hgm, ← hval]
    exact (e ⟨b, hb⟩).2.2
  · calc
      (e ⟨b, hb⟩).1 = torusQuotient (d.g b) := htrace ⟨b, hb⟩
      _ = torusQuotient (a, (b, m)) := by rw [hgm]

/-- **`(B,M)` chart homeo**: the mirror of `torus_chart_homeo_AB` for
independent `b`/`m` partials: the graph parameter is `a` (interval
`(a−δ,a+δ)`), the base point sent to `torusQuotient (a,(b,m))`. -/
theorem torus_chart_homeo_BM {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ)
    {δ : ℝ} (hδpos : 0 < δ) (hδw : 2 * δ < period)
    (d : RealGraphArc r) (hB : d.B = unSplitBM) (hA : d.A = splitBM)
    (hu : d.u = (a, (b, m))) (hL : d.a < a - δ) (hR : a + δ < d.b) :
    ∃ V : Set KnotParamTriple, IsOpen V ∧
      torusQuotient (a, (b, m)) ∈ trisecantZeroSet r ∧ torusQuotient (a, (b, m)) ∈ V ∧
      ∃ e : {x : ℝ // x ∈ Set.Ioo (a - δ) (a + δ)} ≃ₜ
          {q : KnotParamTriple // q ∈ trisecantZeroSet r ∧ q ∈ V},
        (e ⟨a, by constructor <;> linarith⟩).1 = torusQuotient (a, (b, m)) ∧
        ∀ x : {x : ℝ // x ∈ Set.Ioo (a - δ) (a + δ)}, (e x).1 = torusQuotient (d.g x.1) := by
  have hIab : Set.Ioo (a - δ) (a + δ) ⊆ Set.Ioo d.a d.b := by
    intro x hx
    constructor <;> linarith [hL, hR, hx.1, hx.2]
  have hγinj : Set.InjOn (fun x : ℝ => torusQuotient (d.g x)) (Set.Ioo (a - δ) (a + δ)) :=
    injOn_torusQuotient_g_of_graphCoord1 (m := a) (δ := δ) hδw (f := d.g)
      (fun x => d.g_coord1_BM hB x)
  rcases torus_chart_homeo h d (lo := a - δ) (hi := a + δ) hIab hγinj with ⟨V, hVo, e, htrace⟩
  have hu1 : d.u.1 = a := by rw [hu]
  have ha : a ∈ Set.Ioo (a - δ) (a + δ) := by constructor <;> linarith
  have hgm : d.g a = (a, (b, m)) := by
    rw [← hu1]
    have hgAu : d.g d.u.1 = d.A d.u := by
      unfold RealGraphArc.g
      congr 1
      ext <;> simp [d.ψu]
    rw [hgAu, hA, hu]
    simp [splitBM]
  have hval : (e ⟨a, ha⟩).1 = torusQuotient (d.g a) := htrace ⟨a, ha⟩
  refine ⟨V, hVo, ?_, ?_, e, ?_, htrace⟩
  · rw [← hgm, ← hval]
    exact (e ⟨a, ha⟩).2.1
  · rw [← hgm, ← hval]
    exact (e ⟨a, ha⟩).2.2
  · calc
      (e ⟨a, ha⟩).1 = torusQuotient (d.g a) := htrace ⟨a, ha⟩
      _ = torusQuotient (a, (b, m)) := by rw [hgm]

end LeanEval.KnotTheory.Quadrisecant
