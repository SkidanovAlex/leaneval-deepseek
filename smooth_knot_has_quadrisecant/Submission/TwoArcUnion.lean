import Mathlib
import Submission.FacingNormalization
import Submission.TwoChartGlue
import Submission.AmbientTwoArc
import Submission.RealIntervalShape
import Submission.OneManifold

open Set
open scoped Topology
open LeanEval.KnotTheory.Quadrisecant

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false

noncomputable section
namespace LeanEval.KnotTheory.Quadrisecant

/-!
# S182 — the ambient two-arc theorem (module Submission/TwoArcUnion.lean)

The four-pairing end assembly of the facing-normalization program
(ROADMAP S182; AmbientTwoArc four-step outline step (3)+(4)): in a
HAUSDORFF space, TWO OPEN ARCS with CONNECTED OVERLAP GLUE TO AN OPEN
INTERVAL.  Content (namespace LeanEval.KnotTheory.Quadrisecant;
sorry-free, warning-free):

1. **Containment detection from the overlap shapes**:
   `subset_of_coordShape_all` — if the `V`-part of the `U`-chart is the
   whole interval `(0,1)` (shape `(a,b)` with `a = 0`, `b = 1`) then
   `U ⊆ V`; `subset_of_coordShape_all_symm` — the mirror `V ⊆ U`;
2. **`endIff_of_shape`** — the overlap-shape read off as the terminal
   membership iff `(ψ t : X) ∈ U ↔ (t : ℝ) ∈ Ioo lo hi` (the engine's
   `hVend`/`hUend` data, from `coord_mem_iff_mem_coordRealSet`);
3. **`Tfun_eq_transitionHomeo_coord`** — the engine's real transition
   `Tfun` agrees pointwise with the `transitionHomeo` coordinate value on
   the overlap domain (via `transitionHomeo_coord` S169);
4. **`two_arc_union_straight_facing`** (from shape data + `Tfun`-monotone
   `hinc`) and **`two_arc_union_straight_facing_of_strictMono`** (same,
   driven by `StrictMono` of the transition coordinate map through (3));
5. **`reversedChart_symm_apply_val` / `reversedChart_symm_coord_val`** —
   the symm of a reversed chart is the reflected `φ.symm` (coordinate
   `1 −` value); **`two_arc_union_mirror_facing_of_strictMono`** — the
   MIRROR configuration (overlap `(0,b)` LEFT-terminal in `U`, `(c,1)`
   RIGHT-terminal in `V`) glues too: reverse BOTH chart orientations
   (`(1−b,1)` / `(0,1−c)`), the doubly-reversed transition stays strictly
   increasing (`t ↦ 1 − g(1−t)`, direct coordinate computation through
   `transitionHomeo_coord` + the symm value lemma), then (4) applies;
6. **`two_open_arcs_union_of_shapes_inc`** — THE four-pairing theorem
   under the increasing orientation: shapes `(a,b)`, `(c,d)` with
   `[T2Space X]` and `StrictMono` transition.  `TransitionIncreasing`
   (S179) + `ends_of_at_least_one_chart_of_increasing` (S178) give
   `(a = 0 ∨ c = 0) ∧ (b = 1 ∨ d = 1)`; the four corners are containment
   (`a=0,b=1` ⟹ `U ⊆ V`; `c=0,d=1` ⟹ `V ⊆ U`), straight gluing
   (`c=0,b=1`) and mirror gluing (`a=0,d=1`); degenerate sub-corners
   collapse into the containments;
7. **`two_open_arcs_union_is_openInterval`** — THE ambient two-arc
   theorem: `[T2Space X]`, open `U V` with interval charts `φ ψ`, overlap
   `U ∩ V` connected ⟹ `Nonempty ({x : X // x ∈ U ∪ V} ≃ₜ
   OpenRealInterval 0 1)`.  Orientation normalization: the transition
   monotone dichotomy (S165) — `StrictMono` applies (6) directly,
   `StrictAnti` reverses the `V`-chart (S181 `coordRealSet_reversedShape`
   + `transitionHomeo_reversedCoord`, the reversed transition
   `StrictMono` by the pointwise value identity) and applies (6) to the
   reversed pair.

This closes the gap recorded in ROADMAP S164/S177/S181: the consistent
orientation is always realisable (S181), the seam contradictions are
packaged (S178), and the end-covered lattice glues (this module) — the
union of two overlapping arcs of a Hausdorff space is an arc.  The
one-dimensional sweep (OneManifold / chain machinery) consumes this at
the two-trace base step.
-/
/-- If the `V`-part of the `U`-chart is the whole open interval `(0,1)`
then every point of `U` lies in `V` (`U ⊆ V`). -/
theorem subset_of_coordShape_all {X : Type*} [TopologicalSpace X] {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) {a b : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (ha0' : a = 0) (hb1' : b = 1) : U ⊆ V := by
  intro x hx
  let xu : {x : X // x ∈ U} := ⟨x, hx⟩
  let t : ORI 0 1 := φ.symm xu
  have htv : (φ t : X) = x := by
    dsimp [t, xu]
    exact congrArg (fun z : {x : X // x ∈ U} => (z : X)) (φ.apply_symm_apply ⟨x, hx⟩)
  have hiff := coord_mem_iff_mem_coordRealSet (φ := φ) (V := V) (r := (t : ℝ)) t.2
  have htV : (t : ℝ) ∈ coordRealSet φ V := by
    rw [hA, ha0', hb1']
    exact t.2
  have hφtV : (φ ⟨(t : ℝ), t.2⟩ : X) ∈ V := hiff.mpr htV
  have ht_eq : (⟨(t : ℝ), t.2⟩ : ORI 0 1) = t := by apply Subtype.ext; rfl
  have hφtV' : (φ t : X) ∈ V := by
    rwa [ht_eq] at hφtV
  rw [← htv]
  exact hφtV'

/-- The mirror: if the `U`-part of the `V`-chart is the whole interval then
`V ⊆ U`. -/
theorem subset_of_coordShape_all_symm {X : Type*} [TopologicalSpace X] {U V : Set X}
    (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V}) {c d : ℝ}
    (hB : coordRealSet ψ U = Set.Ioo c d) (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (hc0' : c = 0) (hd1' : d = 1) : V ⊆ U := by
  -- instantiate the previous lemma with U↔V, φ↔ψ, and the tested set V↔U
  have h := subset_of_coordShape_all (U := V) (V := U) ψ hB hc0 hcd hd1 hc0' hd1'
  simpa [inter_comm, Set.subset_def] using h


/-- The terminal-overlap membership iff, read off the overlap shape: for a
chart `ψ` of `V` whose `U`-part has shape `(lo,hi)`, `(ψ t : X) ∈ U` iff
`(t : ℝ) ∈ Ioo lo hi` (exactly the `hUend`/`hVend` data of the glue
engine). -/
theorem endIff_of_shape {X : Type*} [TopologicalSpace X] {V : Set X}
    (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V}) (U : Set X)
    {lo hi : ℝ} (hB : coordRealSet ψ U = Set.Ioo lo hi) :
    ∀ t : ORI 0 1, ((ψ t) : X) ∈ U ↔ (t : ℝ) ∈ Set.Ioo lo hi := by
  intro t
  have ht01 : (t : ℝ) ∈ Ioo (0 : ℝ) 1 := t.2
  have hiff := coord_mem_iff_mem_coordRealSet (U := V) (V := U) (φ := ψ) (r := (t : ℝ)) ht01
  constructor
  · intro hψtU
    have ht_eq : (⟨(t : ℝ), ht01⟩ : ORI 0 1) = t := by apply Subtype.ext; rfl
    have h' : (ψ ⟨(t : ℝ), ht01⟩ : X) ∈ U := by simpa [ht_eq] using hψtU
    have hin : (t : ℝ) ∈ coordRealSet ψ U := hiff.mp h'
    simpa [hB] using hin
  · intro ht
    have h' : (t : ℝ) ∈ coordRealSet ψ U := by simpa [hB] using ht
    have h'' : (ψ ⟨(t : ℝ), ht01⟩ : X) ∈ U := hiff.mpr h'
    have ht_eq : (⟨(t : ℝ), ht01⟩ : ORI 0 1) = t := by apply Subtype.ext; rfl
    simpa [ht_eq] using h''

/-- **S182 (straight-facing two-arc union)**: two open arcs `U V` whose
overlap is the right-terminal strip `(a,1)` of the `U`-chart and the
left-terminal strip `(0,d)` of the `V`-chart (monotone increasing
transition) glue to an open interval — the engine step
`prefix_two_charts_interval` (S159) driven by shape data. -/
theorem two_arc_union_straight_facing {X : Type*} [TopologicalSpace X]
    {U V : Set X} (hUopen : IsOpen U) (hVopen : IsOpen V)
    {a d : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1)
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    (hA : coordRealSet φ V = Set.Ioo a 1) (hB : coordRealSet ψ U = Set.Ioo 0 d)
    (hinc : ∀ ⦃v₁ v₂ : ℝ⦄, v₁ ∈ Set.Ioo 0 d → v₂ ∈ Set.Ioo 0 d → v₁ < v₂ →
        Tfun (le_of_lt hd1) φ ψ (endIff_of_shape ψ U hB) v₁ <
        Tfun (le_of_lt hd1) φ ψ (endIff_of_shape ψ U hB) v₂) :
    Nonempty ({x : X // x ∈ U ∪ V} ≃ₜ OpenRealInterval 0 1) := by
  exact prefix_two_charts_interval (Y := X) (T₀ := U) (T₁ := V) hUopen hVopen ha0 ha1 hd0 hd1
    φ ψ (endIff_of_shape φ V hA) (endIff_of_shape ψ U hB) hinc



/-- The engine's transition function `Tfun` agrees pointwise with the
coordinate value of `transitionHomeo` on the overlap domain `(0,d)`. -/
lemma Tfun_eq_transitionHomeo_coord {X : Type*} [TopologicalSpace X]
    {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a d : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1)
    (hA : coordRealSet φ V = Set.Ioo a 1) (hB : coordRealSet ψ U = Set.Ioo 0 d)
    {v : ℝ} (hv : v ∈ Set.Ioo 0 d) :
    Tfun (le_of_lt hd1) φ ψ (endIff_of_shape ψ U hB) v =
      ((transitionHomeo φ ψ hA hB (le_of_lt ha0) ha1 le_rfl
        le_rfl hd0 (le_of_lt hd1) ⟨v, hv⟩ : {x : ℝ // x ∈ Ioo a 1}) : ℝ) := by
  have hu1 : d ≤ 1 := le_of_lt hd1
  let hUend := endIff_of_shape ψ U hB
  rw [Tfun_eq hu1 φ ψ hUend hv]
  dsimp [T, hUend]
  -- v ∈ (0,1) needed
  have hv01 : v ∈ Ioo (0 : ℝ) 1 := ⟨hv.1, lt_trans hv.2 hd1⟩
  have hψU : (ψ ⟨v, hv01⟩ : X) ∈ U := (endIff_of_shape ψ U hB ⟨v, hv01⟩).mpr (by
    have hvv : v ∈ Ioo 0 d := hv
    simpa using hvv)
  have hg := transitionHomeo_coord φ ψ hA hB (le_of_lt ha0) ha1 le_rfl
    le_rfl hd0 (le_of_lt hd1) ⟨v, hv⟩ hv01 hψU
  -- hg : (transitionHomeo ... ⟨v,hv⟩ : ℝ) = (φ.symm ⟨(ψ ⟨v, hv01⟩ : X), hψU⟩ : ORI) : ℝ
  -- goal: ((φ.symm ⟨(ψ ⟨v, emb01 hu1 hv⟩ : X), (endIff hUend...).mpr hv⟩) : ORI) : ℝ = that RHS
  -- after dsimp [T], goal is: ((φ.symm (⟨(ψ ⟨v, emb01 hu1 hv⟩ : X), hmem⟩ : {x//x∈U})) : ORI) : ℝ = (hg RHS?)
  -- Actually goal after Tfun_eq + dsimp [T]: LHS = RHS from hg (orientation reversed).
  exact hg.symm



/-- **Straight-facing union from `StrictMono`**: with the overlap the
right-terminal strip `(a,1)` of the `U`-chart and the left-terminal strip
`(0,d)` of the `V`-chart and a strictly increasing transition coordinate
map, `U ∪ V` is an open interval.  (This is `two_arc_union_straight_facing`
driven by `StrictMono` through the pointwise identity
`Tfun_eq_transitionHomeo_coord`.) -/
lemma two_arc_union_straight_facing_of_strictMono {X : Type*} [TopologicalSpace X]
    {U V : Set X} (hUopen : IsOpen U) (hVopen : IsOpen V)
    {a d : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hd0 : 0 < d) (hd1 : d < 1)
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    (hA : coordRealSet φ V = Set.Ioo a 1) (hB : coordRealSet ψ U = Set.Ioo 0 d)
    (hmono : StrictMono (fun x : {x : ℝ // x ∈ Ioo 0 d} =>
        ((transitionHomeo φ ψ hA hB (le_of_lt ha0) ha1 le_rfl
          le_rfl hd0 (le_of_lt hd1) x : {x : ℝ // x ∈ Ioo a 1}) : ℝ))) :
    Nonempty ({x : X // x ∈ U ∪ V} ≃ₜ OpenRealInterval 0 1) := by
  refine two_arc_union_straight_facing hUopen hVopen ha0 ha1 hd0 hd1 φ ψ hA hB ?_
  intro v₁ v₂ hv₁ hv₂ hvlt
  rw [Tfun_eq_transitionHomeo_coord φ ψ ha0 ha1 hd0 hd1 hA hB hv₁,
      Tfun_eq_transitionHomeo_coord φ ψ ha0 ha1 hd0 hd1 hA hB hv₂]
  exact hmono (a := ⟨v₁, hv₁⟩) (b := ⟨v₂, hv₂⟩) hvlt



/-- **First-chart reversal value identity**: reversing the orientation of
the FIRST chart (`φ` ↦ `reversedChart φ`) reflects the transition values
about `1/2` — the new transition at `t` has coordinate `1 −` the old
coordinate, for `t` in the (unchanged) second-chart overlap `(c,d)`. -/
theorem transitionHomeo_firstReversedCoord {X : Type*} [TopologicalSpace X]
    {U V : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (t : {x : ℝ // x ∈ Ioo c d}) :
    ((transitionHomeo (reversedChart φ) ψ
        (coordRealSet_reversedShape φ V ha0 hab hb1 hA) hB
        (show 0 ≤ 1 - b by linarith) (show 1 - b < 1 - a by linarith)
        (show 1 - a ≤ 1 by linarith) hc0 hcd hd1 t : {x : ℝ // x ∈ Ioo (1 - b) (1 - a)}) : ℝ)
      = 1 - ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 t : {x : ℝ // x ∈ Ioo a b}) : ℝ) := by
  let φ' : ORI 0 1 ≃ₜ {x : X // x ∈ U} := reversedChart φ
  let hA' : coordRealSet φ' V = Set.Ioo (1 - b) (1 - a) :=
    coordRealSet_reversedShape φ V ha0 hab hb1 hA
  let hb'0 : 0 ≤ 1 - b := by linarith
  let hb'a : 1 - b < 1 - a := by linarith
  let ha'1 : 1 - a ≤ 1 := by linarith
  -- coordinates
  rcases t.2 with ⟨htc, htd⟩
  have ht01 : (t : ℝ) ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> linarith
  have hψU : (ψ ⟨(t : ℝ), ht01⟩ : X) ∈ U := by
    have hiff := coord_mem_iff_mem_coordRealSet (U := V) (V := U) (φ := ψ) (r := (t : ℝ)) ht01
    exact hiff.mpr (by simpa [hB] using t.2)
  have hL := transitionHomeo_coord φ' ψ hA' hB hb'0 hb'a ha'1 hc0 hcd hd1 t ht01 hψU
  have hR := transitionHomeo_coord φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 t ht01 hψU
  -- LHS = (φ'.symm ⟨(ψ⟨t⟩:X), hψU⟩ : ORI) : ℝ ; RHS-side: 1 - (φ.symm ⟨…⟩ : ORI) : ℝ
  -- φ' = φ ∘ refl, so φ'.symm z = refl (φ.symm z); value 1 - value
  have hφ' : ∀ z : {x : X // x ∈ U},
      ((φ'.symm z : ORI 0 1) : ℝ) = 1 - ((φ.symm z : ORI 0 1) : ℝ) := by
    intro z
    have hsymm : (φ'.symm z : ORI 0 1) = intervalReflection (0 : ℝ) 1 (φ.symm z) := by
      -- φ'.symm z is the unique point whose φ'-image is z; reflection∘φ.symm has image z
      apply (φ').injective
      have h1 : φ' (φ'.symm z) = z := φ'.apply_symm_apply z
      have h2 : φ' (intervalReflection (0 : ℝ) 1 (φ.symm z)) = z := by
        -- φ' = φ ∘ refl ; refl involutive
        have href : intervalReflection (0 : ℝ) 1 (intervalReflection (0 : ℝ) 1 (φ.symm z))
            = φ.symm z := intervalReflection_involutive (0 : ℝ) 1 (φ.symm z)
        dsimp [φ']
        dsimp [reversedChart]
        rw [href]
        -- (intervalReflection 0 1).trans φ applied to x is φ(refl x)?? compute:
        exact congrArg (fun w : {x : X // x ∈ U} => w) (φ.apply_symm_apply z)
      simpa [h1] using h2.symm ▸ h1
    rw [hsymm]
    rw [intervalReflection_apply]
    ring
  have hL' : ((transitionHomeo φ' ψ hA' hB hb'0 hb'a ha'1 hc0 hcd hd1 t : {x : ℝ // x ∈ Ioo (1-b) (1-a)}) : ℝ)
      = 1 - ((φ.symm ⟨(ψ ⟨(t : ℝ), ht01⟩ : X), hψU⟩ : ORI 0 1) : ℝ) := by
    rw [hL]
    dsimp [φ'] at hφ' ⊢
    rw [hφ']
  have hR' : ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 t : {x : ℝ // x ∈ Ioo a b}) : ℝ)
      = ((φ.symm ⟨(ψ ⟨(t : ℝ), ht01⟩ : X), hψU⟩ : ORI 0 1) : ℝ) := hR
  -- goal: (T(φ',ψ) t : ℝ) = 1 - (T(φ,ψ) t : ℝ)
  rw [hL', hR']





/-- **Symm of the reversed chart**: `(reversedChart φ).symm` is the
reflection of `φ.symm` (the reflection homeo is its own inverse). -/
theorem reversedChart_symm_apply_val {X : Type*} [TopologicalSpace X] {U : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (z : {x : X // x ∈ U}) :
    ((reversedChart φ).symm z : ORI 0 1) = intervalReflection (0 : ℝ) 1 (φ.symm z) := by
  let φ' : ORI 0 1 ≃ₜ {x : X // x ∈ U} := reversedChart φ
  have h1 : φ' (φ'.symm z) = z := φ'.apply_symm_apply z
  have h2 : φ' (intervalReflection (0 : ℝ) 1 (φ.symm z)) = z := by
    have href : intervalReflection (0 : ℝ) 1 (intervalReflection (0 : ℝ) 1 (φ.symm z))
        = φ.symm z := intervalReflection_involutive (0 : ℝ) 1 (φ.symm z)
    dsimp [φ']
    dsimp [reversedChart]
    rw [href]
    exact congrArg (fun w : {x : X // x ∈ U} => w) (φ.apply_symm_apply z)
  have h3 : φ'.symm z = intervalReflection (0 : ℝ) 1 (φ.symm z) :=
    (φ'.injective (by simpa [h1] using h2.symm ▸ h1))
  exact congrArg (fun w : ORI 0 1 => (w : ORI 0 1)) h3

/-- Coordinate value of the symm: `((reversedChart φ).symm z : ℝ) = 1 −
`((φ.symm z) : ℝ)`. -/
theorem reversedChart_symm_coord_val {X : Type*} [TopologicalSpace X] {U : Set X}
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (z : {x : X // x ∈ U}) :
    (((reversedChart φ).symm z : ORI 0 1) : ℝ) = 1 - ((φ.symm z : ORI 0 1) : ℝ) := by
  rw [reversedChart_symm_apply_val φ z]
  rw [intervalReflection_apply]
  ring

/-- **S182 (mirror-facing two-arc union)**: two open arcs whose overlap is
the LEFT-terminal strip `(0,b)` of the `U`-chart and the RIGHT-terminal
strip `(c,1)` of the `V`-chart (strictly increasing transition) glue to an
open interval.  Proof: reverse BOTH chart orientations — the overlap becomes
the straight-facing configuration (`(1−b,1)` right-terminal in the reversed
`U`-chart, `(0,1−c)` left-terminal in the reversed `V`-chart) of
`two_arc_union_straight_facing_of_strictMono`, and the doubly-reversed
transition is strictly increasing (`t ↦ 1 − g(1 − t)`). -/
lemma two_arc_union_mirror_facing_of_strictMono {X : Type*} [TopologicalSpace X]
    {U V : Set X} (hUopen : IsOpen U) (hVopen : IsOpen V)
    {b c : ℝ} (hb0 : 0 < b) (hb1 : b < 1) (hc0 : 0 < c) (hc1 : c < 1)
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    (hA : coordRealSet φ V = Set.Ioo 0 b) (hB : coordRealSet ψ U = Set.Ioo c 1)
    (hmono : StrictMono (fun x : {x : ℝ // x ∈ Ioo c 1} =>
        ((transitionHomeo φ ψ hA hB le_rfl hb0 (le_of_lt hb1) (le_of_lt hc0) hc1 le_rfl
           x : {x : ℝ // x ∈ Ioo 0 b}) : ℝ))) :
    Nonempty ({x : X // x ∈ U ∪ V} ≃ₜ OpenRealInterval 0 1) := by
  let φ' : ORI 0 1 ≃ₜ {x : X // x ∈ U} := reversedChart φ
  let ψ' : ORI 0 1 ≃ₜ {x : X // x ∈ V} := reversedChart ψ
  let hA' : coordRealSet φ' V = Set.Ioo (1 - b) 1 := by
    dsimp [φ']
    simpa using coordRealSet_reversedShape φ V (c := 0) (d := b)
      (show 0 ≤ 0 from le_rfl) hb0 (le_of_lt hb1) hA
  let hB' : coordRealSet ψ' U = Set.Ioo 0 (1 - c) := by
    dsimp [ψ']
    simpa using coordRealSet_reversedShape ψ U (c := c) (d := 1)
      (le_of_lt hc0) hc1 (show 1 ≤ 1 from le_rfl) hB
  have hval2 : ∀ t : {x : ℝ // x ∈ Ioo 0 (1 - c)},
      ((transitionHomeo φ' ψ' hA' hB'
          (show 0 ≤ 1 - b by linarith) (show 1 - b < 1 by linarith) le_rfl
          le_rfl (show 0 < 1 - c by linarith) (show 1 - c ≤ 1 by linarith)
          t : {x : ℝ // x ∈ Ioo (1 - b) 1}) : ℝ)
        = 1 - ((transitionHomeo φ ψ hA hB le_rfl hb0 (le_of_lt hb1) (le_of_lt hc0) hc1 le_rfl
            ⟨1 - (t : ℝ), (by rcases t.2 with ⟨ht0, htc⟩; constructor <;> linarith)⟩
              : {x : ℝ // x ∈ Ioo 0 b}) : ℝ) := by
    intro t
    rcases t.2 with ⟨ht0, htc⟩
    have ht01 : (t : ℝ) ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith
    have hs01 : 1 - (t : ℝ) ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith
    have hsc1 : 1 - (t : ℝ) ∈ Ioo c 1 := by constructor <;> linarith
    have hψ'U : (ψ' ⟨(t : ℝ), ht01⟩ : X) ∈ U := by
      have hiff := coord_mem_iff_mem_coordRealSet (U := V) (V := U) (φ := ψ') (r := (t : ℝ)) ht01
      exact hiff.mpr (by simpa [hB'] using t.2)
    have hψU : (ψ ⟨(1 - (t : ℝ)), hs01⟩ : X) ∈ U := by
      have hiff := coord_mem_iff_mem_coordRealSet (U := V) (V := U) (φ := ψ) (r := 1 - (t : ℝ)) hs01
      exact hiff.mpr (by simpa [hB] using hsc1)
    have hXval : (ψ' ⟨(t : ℝ), ht01⟩ : X) = (ψ ⟨(1 - (t : ℝ)), hs01⟩ : X) := by
      dsimp [ψ']
      calc
        ((reversedChart ψ ⟨(t : ℝ), ht01⟩ : {x : X // x ∈ V}) : X)
            = (ψ (intervalReflection (0 : ℝ) 1 ⟨(t : ℝ), ht01⟩) : X) :=
              reversedChart_apply_val ψ ⟨(t : ℝ), ht01⟩
        _ = (ψ ⟨(1 - (t : ℝ)), hs01⟩ : X) := by
              exact congrArg (fun w : ORI 0 1 => (ψ w : X)) (by
                apply Subtype.ext
                rw [intervalReflection_apply]
                ring)
    have hArg : (⟨(ψ' ⟨(t : ℝ), ht01⟩ : X), hψ'U⟩ : {x : X // x ∈ U}) =
        ⟨(ψ ⟨(1 - (t : ℝ)), hs01⟩ : X), hψU⟩ := by
      apply Subtype.ext
      exact hXval
    have hL := transitionHomeo_coord φ' ψ' hA' hB'
      (show 0 ≤ 1 - b by linarith) (show 1 - b < 1 by linarith) le_rfl
      le_rfl (show 0 < 1 - c by linarith) (show 1 - c ≤ 1 by linarith) t ht01 hψ'U
    have hR := transitionHomeo_coord φ ψ hA hB le_rfl hb0 (le_of_lt hb1) (le_of_lt hc0) hc1 le_rfl
      ⟨1 - (t : ℝ), hsc1⟩ hs01 hψU
    rw [hL, hR]
    dsimp [φ']
    rw [reversedChart_symm_coord_val φ ⟨(ψ' ⟨(t : ℝ), ht01⟩ : X), hψ'U⟩]
    exact congrArg (fun w : {x : X // x ∈ U} => (1 - ((φ.symm w : ORI 0 1) : ℝ))) hArg
  have hmono' : StrictMono (fun t : {x : ℝ // x ∈ Ioo 0 (1 - c)} =>
      ((transitionHomeo φ' ψ' hA' hB'
          (show 0 ≤ 1 - b by linarith) (show 1 - b < 1 by linarith) le_rfl
          le_rfl (show 0 < 1 - c by linarith) (show 1 - c ≤ 1 by linarith)
          t : {x : ℝ // x ∈ Ioo (1 - b) 1}) : ℝ)) := by
    intro t₁ t₂ hlt
    have hltv : (t₁ : ℝ) < (t₂ : ℝ) := hlt
    have h₁ := hval2 t₁
    have h₂ := hval2 t₂
    change ((transitionHomeo φ' ψ' hA' hB'
          (show 0 ≤ 1 - b by linarith) (show 1 - b < 1 by linarith) le_rfl
          le_rfl (show 0 < 1 - c by linarith) (show 1 - c ≤ 1 by linarith)
          t₁ : {x : ℝ // x ∈ Ioo (1 - b) 1}) : ℝ) <
        ((transitionHomeo φ' ψ' hA' hB'
          (show 0 ≤ 1 - b by linarith) (show 1 - b < 1 by linarith) le_rfl
          le_rfl (show 0 < 1 - c by linarith) (show 1 - c ≤ 1 by linarith)
          t₂ : {x : ℝ // x ∈ Ioo (1 - b) 1}) : ℝ)
    rw [h₁, h₂]
    have hrc : ((⟨1 - (t₂ : ℝ), (by rcases t₂.2 with ⟨ht0, htc⟩; constructor <;> linarith)⟩
        : {x : ℝ // x ∈ Ioo c 1}) : ℝ) <
        ((⟨1 - (t₁ : ℝ), (by rcases t₁.2 with ⟨ht0, htc⟩; constructor <;> linarith)⟩
        : {x : ℝ // x ∈ Ioo c 1}) : ℝ) := by
      change 1 - (t₂ : ℝ) < 1 - (t₁ : ℝ)
      linarith
    have hg := hmono (a := ⟨1 - (t₂ : ℝ), (by rcases t₂.2 with ⟨ht0, htc⟩; constructor <;> linarith)⟩)
      (b := ⟨1 - (t₁ : ℝ), (by rcases t₁.2 with ⟨ht0, htc⟩; constructor <;> linarith)⟩) hrc
    linarith
  exact two_arc_union_straight_facing_of_strictMono (X := X) hUopen hVopen
    (a := 1 - b) (d := 1 - c)
    (show 0 < 1 - b by linarith) (show 1 - b < 1 by linarith)
    (show 0 < 1 - c by linarith) (show 1 - c < 1 by linarith)
    φ' ψ' hA' hB' (by simpa [φ', ψ', hA', hB'] using hmono')



/-- **S182 (the two-arc union theorem — increasing orientation)**: two open
arcs `U V` of a Hausdorff ambient, whose overlap `U ∩ V` has the interval
shapes `(a,b)` in the `U`-chart and `(c,d)` in the `V`-chart, with a
strictly increasing transition coordinate map, glue to an open interval.
Proof (the four-pairing end assembly): under `[T2Space X]` the increasing
orientation forbids a strict seam pair at either overlap end
(`ends_of_at_least_one_chart_of_increasing`, S178), so each overlap end is
an end of at least one chart: `(a = 0 ∨ c = 0) ∧ (b = 1 ∨ d = 1)`.  The
four corners give containment (`a = 0 ∧ b = 1` ⟹ `U ⊆ V`;
`c = 0 ∧ d = 1` ⟹ `V ⊆ U`), the straight facing gluing
(`c = 0 ∧ b = 1`; `two_arc_union_straight_facing_of_strictMono`), and the
mirror facing gluing (`a = 0 ∧ d = 1`;
`two_arc_union_mirror_facing_of_strictMono`, reversing both chart
orientations); degenerate sub-corners collapse into the containments. -/
theorem two_open_arcs_union_of_shapes_inc {X : Type*} [TopologicalSpace X] [T2Space X]
    {U V : Set X} (hUopen : IsOpen U) (hVopen : IsOpen V)
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    {a b c d : ℝ}
    (hA : coordRealSet φ V = Set.Ioo a b) (hB : coordRealSet ψ U = Set.Ioo c d)
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hcd : c < d) (hd1 : d ≤ 1)
    (hmono : StrictMono (fun x : {x : ℝ // x ∈ Ioo c d} =>
        ((transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 x : {x : ℝ // x ∈ Ioo a b}) : ℝ))) :
    Nonempty ({x : X // x ∈ U ∪ V} ≃ₜ OpenRealInterval 0 1) := by
  classical
  have hinc := increasing_of_strictMono φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 hmono
  have hends := ends_of_at_least_one_chart_of_increasing φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 hinc
  have hlef : a = 0 ∨ c = 0 := by
    by_cases ha0s : a = 0
    · exact Or.inl ha0s
    · right
      have hapos : 0 < a := lt_of_le_of_ne ha0 (fun hz => ha0s hz.symm)
      have hnotc : ¬ 0 < c := fun hcpos => hends.1 ⟨hapos, hcpos⟩
      exact le_antisymm (le_of_not_gt hnotc) hc0
  have hrig : b = 1 ∨ d = 1 := by
    by_cases hb1s : b = 1
    · exact Or.inl hb1s
    · right
      have hblt : b < 1 := lt_of_le_of_ne hb1 hb1s
      have hnotd : ¬ d < 1 := fun hdlt => hends.2 ⟨hblt, hdlt⟩
      exact le_antisymm hd1 (le_of_not_gt hnotd)
  rcases hlef with ha0s | hc0s
  · rcases hrig with hb1s | hd1s
    · -- a = 0, b = 1 : U ⊆ V (containment)
      have hUV : U ⊆ V := subset_of_coordShape_all φ hA ha0 hab hb1 ha0s hb1s
      rcases two_arc_contained (U := V) (V := U) hUV ψ with ⟨hmid⟩
      exact ⟨(setEqSubtypeHomeoX (Set.union_comm U V)).trans hmid⟩
    · -- a = 0, d = 1 : mirror (degenerate corners collapse to containment)
      subst a
      subst d
      by_cases hb1eq : b = 1
      · have hUV : U ⊆ V := subset_of_coordShape_all φ hA ha0 hab hb1 rfl hb1eq
        rcases two_arc_contained (U := V) (V := U) hUV ψ with ⟨hmid⟩
        exact ⟨(setEqSubtypeHomeoX (Set.union_comm U V)).trans hmid⟩
      · have hblt : b < 1 := lt_of_le_of_ne hb1 hb1eq
        by_cases hc0eq : c = 0
        · have hVU : V ⊆ U := subset_of_coordShape_all_symm ψ hB hc0 hcd hd1 hc0eq rfl
          exact two_arc_contained hVU φ
        · have hcpos : 0 < c := lt_of_le_of_ne hc0 (fun hz => hc0eq hz.symm)
          exact two_arc_union_mirror_facing_of_strictMono (X := X) hUopen hVopen
            hab hblt hcpos hcd φ ψ hA hB hmono
  · rcases hrig with hb1s | hd1s
    · -- c = 0, b = 1 : straight (degenerate corners collapse to containment)
      subst b
      subst c
      by_cases ha0eq : a = 0
      · have hUV : U ⊆ V := subset_of_coordShape_all φ hA ha0 hab hb1 ha0eq rfl
        rcases two_arc_contained (U := V) (V := U) hUV ψ with ⟨hmid⟩
        exact ⟨(setEqSubtypeHomeoX (Set.union_comm U V)).trans hmid⟩
      · have hapos : 0 < a := lt_of_le_of_ne ha0 (fun hz => ha0eq hz.symm)
        by_cases hd1eq : d = 1
        · have hVU : V ⊆ U := subset_of_coordShape_all_symm ψ hB hc0 hcd hd1 rfl hd1eq
          exact two_arc_contained hVU φ
        · have hdlt : d < 1 := lt_of_le_of_ne hd1 hd1eq
          exact two_arc_union_straight_facing_of_strictMono (X := X) hUopen hVopen
            hapos hab hcd hdlt φ ψ hA hB hmono
    · -- c = 0, d = 1 : V ⊆ U (containment)
      have hVU : V ⊆ U := subset_of_coordShape_all_symm ψ hB hc0 hcd hd1 hc0s hd1s
      exact two_arc_contained hVU φ



/-- **S182 (the ambient two-arc theorem)**: in a Hausdorff space, two open
arcs `U V` (with interval charts `φ ψ`) whose overlap `U ∩ V` is connected
glue to a single open interval — `{x : X // x ∈ U ∪ V} ≃ₜ (0,1)`.  Proof:
classify the two overlap shapes `(a,b)`, `(c,d)`; take the transition
monotone dichotomy (S165): under `StrictMono` apply
`two_open_arcs_union_of_shapes_inc` directly, under `StrictAnti` reverse
the `V`-chart orientation (S181) — the reversed transition is `StrictMono`
(`transitionHomeo_reversedCoord` value identity) and the reversed pair has
shapes `(a,b)`, `(1−d,1−c)` (`coordRealSet_reversedShape`) — then apply
the same theorem to the reversed pair. -/
theorem two_open_arcs_union_is_openInterval {X : Type*} [TopologicalSpace X] [T2Space X]
    {U V : Set X} (hUopen : IsOpen U) (hVopen : IsOpen V)
    (φ : ORI 0 1 ≃ₜ {x : X // x ∈ U}) (ψ : ORI 0 1 ≃ₜ {x : X // x ∈ V})
    (hconn : ConnectedSpace {x : X // x ∈ U ∩ V}) :
    Nonempty ({x : X // x ∈ U ∪ V} ≃ₜ OpenRealInterval 0 1) := by
  -- V-side overlap connectedness
  have hconn' : ConnectedSpace {x : X // x ∈ V ∩ U} := by
    let e : {x : X // x ∈ V ∩ U} ≃ₜ {x : X // x ∈ U ∩ V} :=
      setEqSubtypeHomeoX (Set.inter_comm V U)
    exact (e.connectedSpace_iff).mpr hconn
  rcases overlap_coord_shape φ hVopen hconn with ⟨a, b, ha0, hab, hb1, hA⟩
  rcases overlap_coord_shape ψ hUopen hconn' with ⟨c, d, hc0, hcd, hd1, hB⟩
  let g : ({x : ℝ // x ∈ Ioo c d}) ≃ₜ ({x : ℝ // x ∈ Ioo a b}) :=
    transitionHomeo φ ψ hA hB ha0 hab hb1 hc0 hcd hd1
  rcases intervalHomeo_coord_strictMono_or_anti hab hcd g with hmono | hanti
  · exact two_open_arcs_union_of_shapes_inc hUopen hVopen φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 hmono
  · -- reverse the V-chart: the reversed transition is strictly increasing
    have hmono' : StrictMono (fun x : {x : ℝ // x ∈ Ioo (1 - d) (1 - c)} =>
        ((transitionHomeo φ (reversedChart ψ) hA
            (coordRealSet_reversedShape ψ U hc0 hcd hd1 hB) ha0 hab hb1
            (show 0 ≤ 1 - d by linarith) (show 1 - d < 1 - c by linarith)
            (show 1 - c ≤ 1 by linarith)
            x : {x : ℝ // x ∈ Ioo a b}) : ℝ)) := by
      intro x₁ x₂ hlt
      have hltv : (x₁ : ℝ) < (x₂ : ℝ) := hlt
      have h₁ := transitionHomeo_reversedCoord φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 x₁
      have h₂ := transitionHomeo_reversedCoord φ ψ hA hB ha0 hab hb1 hc0 hcd hd1 x₂
      change ((transitionHomeo φ (reversedChart ψ) hA
            (coordRealSet_reversedShape ψ U hc0 hcd hd1 hB) ha0 hab hb1
            (show 0 ≤ 1 - d by linarith) (show 1 - d < 1 - c by linarith)
            (show 1 - c ≤ 1 by linarith)
            x₁ : {x : ℝ // x ∈ Ioo a b}) : ℝ) <
        ((transitionHomeo φ (reversedChart ψ) hA
            (coordRealSet_reversedShape ψ U hc0 hcd hd1 hB) ha0 hab hb1
            (show 0 ≤ 1 - d by linarith) (show 1 - d < 1 - c by linarith)
            (show 1 - c ≤ 1 by linarith)
            x₂ : {x : ℝ // x ∈ Ioo a b}) : ℝ)
      rw [h₁, h₂]
      have hrc : ((reflectCoord c d x₂ : {x : ℝ // x ∈ Ioo c d}) : ℝ) <
          ((reflectCoord c d x₁ : {x : ℝ // x ∈ Ioo c d}) : ℝ) := by
        rw [reflectCoord_val, reflectCoord_val]
        linarith
      have hg := hanti (a := reflectCoord c d x₂) (b := reflectCoord c d x₁) hrc
      linarith
    exact two_open_arcs_union_of_shapes_inc hUopen hVopen φ (reversedChart ψ) hA
      (coordRealSet_reversedShape ψ U hc0 hcd hd1 hB) ha0 hab hb1
      (show 0 ≤ 1 - d by linarith) (show 1 - d < 1 - c by linarith)
      (show 1 - c ≤ 1 by linarith) hmono'


/-! ## S183 — the finite-chain union theorem (induction over the two-arc gluing)

The chain-level statement the S182 two-arc theorem feeds: a finite chain
of open arcs of a Hausdorff space whose every PREFIX meets the next trace
in a connected overlap glues to one open interval.  The induction carries
the explicit prefix homeomorphism (each step consumes the previous
prefix's interval chart).  (Successive-overlap-only hypotheses are NOT
sufficient — a wrapping trace can touch the prefix in two components;
prefix-overlap connectivity must come from the walk/O-chart geometry.)
-/

/-- **S183 (finite-chain union, induction statement)**: in a Hausdorff
space, a finite chain of open arcs — each trace `T k` (`k ≤ n`) open with
an interval chart, every prefix `P k := ⋃ j ∈ range (k+1), T j` meeting
the next trace `T (k+1)` in a CONNECTED (hence nonempty) overlap — glues
to a single open interval: the full prefix `P n` carries an interval
chart.  The induction carries the explicit homeomorphism (not merely
interval-ness), because the two-arc theorem's next step consumes the
prefix's interval chart as an input.

HYPOTHESES ARE PREFIX-OVERLAP (not merely successive-overlap): the
`(k ↦ k+1)` gluing applies the ambient two-arc theorem
(`two_open_arcs_union_is_openInterval`, S182) to the pair
`(P k, T (k+1))`, which requires `P k ∩ T (k+1)` connected.  NOTE
(honest): connectedness of the *successive* overlaps `T k ∩ T (k+1)`
alone does NOT suffice — a later trace may touch the interior of the
prefix in a second component (e.g. arcs of a circle wrapping past a
meridian), which disconnects `P k ∩ T (k+1)`; the walk/O-chart geometry
must supply prefix-overlap connectivity. -/
theorem finite_chain_union_interval {X : Type*} [TopologicalSpace X] [T2Space X]
    (T : ℕ → Set X) (n : ℕ)
    (hopen : ∀ k, k ≤ n → IsOpen (T k))
    (hchart : ∀ k, k ≤ n → Nonempty (ORI 0 1 ≃ₜ {x : X // x ∈ T k}))
    (hconn : ∀ k, k < n →
      ConnectedSpace {x : X // x ∈ (⋃ j ∈ Finset.range (k+1), T j) ∩ T (k+1)}) :
    Nonempty ({x : X // x ∈ ⋃ j ∈ Finset.range (n+1), T j} ≃ₜ OpenRealInterval 0 1) := by
  classical
  induction n with
  | zero =>
      have hset : (⋃ j ∈ Finset.range (1), T j) = T 0 := by
        ext x
        simp [Finset.range_one]
      rcases hchart 0 (by omega) with ⟨e⟩
      exact ⟨(setEqSubtypeHomeoX hset).trans e.symm⟩
  | succ n ih =>
      -- prefix-openness at level n (finite union of open traces, j ≤ n)
      have hpref_open : IsOpen (⋃ j ∈ Finset.range (n + 1), T j) := by
        -- induction on the trace count m, showing prefix m open for m ≤ n+1
        have hgo : ∀ m : ℕ, m ≤ n + 1 → IsOpen (⋃ j ∈ Finset.range (m + 1), T j) := by
          intro m
          induction m with
          | zero =>
              intro hm
              have hset0 : (⋃ j ∈ Finset.range (1), T j) = T 0 := by
                ext x
                simp [Finset.range_one]
              rw [hset0]
              exact hopen 0 (by omega)
          | succ m ih' =>
              intro hm
              rw [union_range_succ T m]
              exact (ih' (by omega)).union (hopen (m + 1) (by omega))
        exact hgo n (by omega)
      -- induction hypothesis: the prefix of the first n+1 traces is an arc
      have hP := ih (fun k hk => hopen k (by omega)) (fun k hk => hchart k (by omega))
        (fun k hk => hconn k (by omega))
      rcases hP with ⟨eP⟩
      rcases hchart (n + 1) (by omega) with ⟨eT⟩
      have hov : ConnectedSpace
          {x : X // x ∈ (⋃ j ∈ Finset.range (n+1), T j) ∩ T (n+1)} := hconn n (by omega)
      have htwo := two_open_arcs_union_is_openInterval
        (U := ⋃ j ∈ Finset.range (n+1), T j) (V := T (n+1))
        hpref_open (hopen (n + 1) (by omega)) eP.symm eT hov
      rcases htwo with ⟨eU⟩
      have hset : (⋃ j ∈ Finset.range (n + 2), T j) =
          (⋃ j ∈ Finset.range (n + 1), T j) ∪ T (n + 1) := union_range_succ T n
      have hfin : ({x : X // x ∈ ⋃ j ∈ Finset.range (n + 2), T j}) ≃ₜ
          ({x : X // x ∈ (⋃ j ∈ Finset.range (n+1), T j) ∪ T (n+1)}) :=
        setEqSubtypeHomeoX hset
      exact ⟨hfin.trans eU⟩
end LeanEval.KnotTheory.Quadrisecant
