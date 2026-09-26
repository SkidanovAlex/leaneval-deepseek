import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.Compact

open Set
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.deprecated false

noncomputable section

namespace Commons.Topology.OneManifold

namespace AttractsLeftEnd

/-- The open unit interval as a type. -/
abbrev ORI : Type := {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1}

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-- Chart coercion of an arc chart `e : ORI ≃ₜ {x : X // x ∈ P}` into `X`. -/
def chartVal {P : Set X} (e : ORI ≃ₜ {x : X // x ∈ P}) : ORI → X :=
  fun t => ((e t : {x : X // x ∈ P}) : X)

theorem chartVal_continuous {P : Set X} (e : ORI ≃ₜ {x : X // x ∈ P}) :
    Continuous (chartVal e) := by
  exact continuous_subtype_val.comp e.continuous

theorem chartVal_injective {P : Set X} (e : ORI ≃ₜ {x : X // x ∈ P}) :
    Function.Injective (chartVal e) := by
  intro t s h
  apply e.injective
  apply Subtype.ext
  exact h

theorem chartVal_range {P : Set X} (e : ORI ≃ₜ {x : X // x ∈ P}) :
    Set.range (chartVal e) = P := by
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    exact (e t).2
  · intro hy
    refine ⟨e.symm ⟨y, hy⟩, ?_⟩
    have h := congrArg (fun z : {x : X // x ∈ P} => (z : X)) (e.apply_symm_apply ⟨y, hy⟩)
    simpa [chartVal] using h

/-- Sub-arc over the open real interval `(lo,hi)`. -/
def sub {P : Set X} (e : ORI ≃ₜ {x : X // x ∈ P}) (lo hi : ℝ) : Set X :=
  chartVal e '' {t : ORI | (t : ℝ) ∈ Set.Ioo lo hi}

/-- Sub-arc over the closed real interval `[lo,hi]`. -/
def subClosed {P : Set X} (e : ORI ≃ₜ {x : X // x ∈ P}) (lo hi : ℝ) : Set X :=
  chartVal e '' {t : ORI | (t : ℝ) ∈ Set.Icc lo hi}

theorem mem_sub {P : Set X} (e : ORI ≃ₜ {x : X // x ∈ P}) {lo hi : ℝ} {x : X} :
    x ∈ sub e lo hi ↔ ∃ t : ORI, (t : ℝ) ∈ Set.Ioo lo hi ∧ chartVal e t = x := by
  rfl

theorem mem_subClosed {P : Set X} (e : ORI ≃ₜ {x : X // x ∈ P}) {lo hi : ℝ} {x : X} :
    x ∈ subClosed e lo hi ↔ ∃ t : ORI, (t : ℝ) ∈ Set.Icc lo hi ∧ chartVal e t = x := by
  rfl

theorem sub_subset_P {P : Set X} (e : ORI ≃ₜ {x : X // x ∈ P}) {lo hi : ℝ} :
    sub e lo hi ⊆ P := by
  intro x hx
  rw [mem_sub] at hx
  rcases hx with ⟨t, ht, rfl⟩
  exact (e t).2

theorem subClosed_subset_P {P : Set X} (e : ORI ≃ₜ {x : X // x ∈ P}) {lo hi : ℝ} :
    subClosed e lo hi ⊆ P := by
  intro x hx
  rw [mem_subClosed] at hx
  rcases hx with ⟨t, ht, rfl⟩
  exact (e t).2

theorem sub_mono {P : Set X} (e : ORI ≃ₜ {x : X // x ∈ P}) {lo lo' hi hi' : ℝ}
    (hlo : lo' ≤ lo) (hhi : hi ≤ hi') : sub e lo hi ⊆ sub e lo' hi' := by
  intro x hx
  rw [mem_sub] at hx ⊢
  rcases hx with ⟨t, ht, rfl⟩
  refine ⟨t, ⟨lt_of_le_of_lt hlo ht.1, lt_of_lt_of_le ht.2 hhi⟩, rfl⟩

/-- A closed-coordinate sub-arc is closed in X (compact image in a Hausdorff space). -/
theorem subClosed_isClosed {P : Set X} (e : ORI ≃ₜ {x : X // x ∈ P}) {a b : ℝ}
    (h0a : 0 < a) (hb1 : b < 1) : IsClosed (subClosed e a b) := by
  let C := {r : ℝ // r ∈ Set.Icc a b}
  haveI : CompactSpace C := by
    dsimp [C]
    exact isCompact_iff_compactSpace.mp (isCompact_Icc : IsCompact (Set.Icc a b : Set ℝ))
  have hmem : ∀ r : ℝ, r ∈ Set.Icc a b → r ∈ Set.Ioo (0 : ℝ) 1 := by
    intro r hr
    exact ⟨lt_of_lt_of_le h0a hr.1, lt_of_le_of_lt hr.2 hb1⟩
  let g : C → X := fun r => chartVal e ⟨(r : ℝ), hmem (r : ℝ) r.2⟩
  have hinner_cont : Continuous (fun r : C => (⟨(r : ℝ), hmem (r : ℝ) r.2⟩ : ORI)) :=
    Continuous.subtype_mk (f := fun r : C => (r : ℝ)) continuous_subtype_val
      (fun r => hmem (r : ℝ) r.2)
  have hg_cont : Continuous g := by
    dsimp [g]
    exact (chartVal_continuous e).comp hinner_cont
  have hg_compact : IsCompact (g '' Set.univ) := IsCompact.image isCompact_univ hg_cont
  have hEq : g '' Set.univ = subClosed e a b := by
    ext y
    constructor
    · rintro ⟨r, -, rfl⟩
      rw [mem_subClosed]
      refine ⟨⟨(r : ℝ), hmem (r : ℝ) r.2⟩, r.2, rfl⟩
    · intro hy
      rcases hy with ⟨s, hs, rfl⟩
      refine ⟨⟨(s : ℝ), hs⟩, trivial, ?_⟩
      dsimp [g]
  rw [← hEq]
  exact hg_compact.isClosed

/-- The value map from `ORI` to `ℝ`. -/
def val (t : ORI) : ℝ := (t : ℝ)

theorem val_injective : Function.Injective (val : ORI → ℝ) := by
  intro t s h
  apply Subtype.ext
  exact h

/-- The value map embeds `ORI` into `ℝ` (it is the subtype inclusion). -/
theorem val_isEmbedding : Topology.IsEmbedding (val : ORI → ℝ) := by
  change Topology.IsEmbedding (fun t : {r : ℝ // r ∈ Set.Ioo (0 : ℝ) 1} => (t : ℝ))
  exact Topology.IsEmbedding.subtypeVal (p := fun r : ℝ => r ∈ Set.Ioo (0 : ℝ) 1)

/-- The left half of the open unit interval below `c₀`. -/
def leftHalf (c₀ : ℝ) : Set ORI := {t : ORI | (t : ℝ) < c₀}

/-- The right half of the open unit interval above `c₀`. -/
def rightHalf (c₀ : ℝ) : Set ORI := {t : ORI | c₀ < (t : ℝ)}

/-- The left half of the open unit interval is homeomorphic to `(0,c₀)`. -/
theorem leftHalf_homeo (c₀ : ℝ) (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1) :
    Nonempty ({t : ORI // t ∈ leftHalf c₀} ≃ₜ {r : ℝ // r ∈ Set.Ioo (0 : ℝ) c₀}) := by
  refine ⟨{ toFun := fun t => ⟨(t : ORI).1, ⟨(t : ORI).2.1, t.2⟩⟩
            invFun := fun r => ⟨⟨(r : ℝ), ⟨r.2.1, lt_trans r.2.2 hc₀₁⟩⟩, r.2.2⟩
            left_inv := by
              intro t
              apply Subtype.ext
              rfl
            right_inv := by
              intro r
              apply Subtype.ext
              rfl }⟩

/-- The right half of the open unit interval is homeomorphic to `(c₀,1)`. -/
theorem rightHalf_homeo (c₀ : ℝ) (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1) :
    Nonempty ({t : ORI // t ∈ rightHalf c₀} ≃ₜ {r : ℝ // r ∈ Set.Ioo c₀ 1}) := by
  refine ⟨{ toFun := fun t => ⟨(t : ORI).1, ⟨t.2, (t : ORI).2.2⟩⟩
            invFun := fun r => ⟨⟨(r : ℝ), ⟨lt_of_lt_of_le hc₀₀ (le_of_lt r.2.1), r.2.2⟩⟩, r.2.1⟩
            left_inv := by
              intro t
              apply Subtype.ext
              rfl
            right_inv := by
              intro r
              apply Subtype.ext
              rfl }⟩

/-- The left half of the open unit interval is connected. -/
theorem isConnected_leftHalf (c₀ : ℝ) (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1) :
    IsConnected (leftHalf c₀) := by
  rcases leftHalf_homeo c₀ hc₀₀ hc₀₁ with ⟨h⟩
  have hc : ConnectedSpace {r : ℝ // r ∈ Set.Ioo (0 : ℝ) c₀} :=
    (isConnected_iff_connectedSpace.mp (isConnected_Ioo hc₀₀))
  have hc' : ConnectedSpace {t : ORI // t ∈ leftHalf c₀} :=
    (h.connectedSpace_iff).mpr hc
  exact isConnected_iff_connectedSpace.mpr hc'

/-- The right half of the open unit interval is connected. -/
theorem isConnected_rightHalf (c₀ : ℝ) (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1) :
    IsConnected (rightHalf c₀) := by
  rcases rightHalf_homeo c₀ hc₀₀ hc₀₁ with ⟨h⟩
  have hc : ConnectedSpace {r : ℝ // r ∈ Set.Ioo c₀ 1} :=
    (isConnected_iff_connectedSpace.mp (isConnected_Ioo hc₀₁))
  have hc' : ConnectedSpace {t : ORI // t ∈ rightHalf c₀} :=
    (h.connectedSpace_iff).mpr hc
  exact isConnected_iff_connectedSpace.mpr hc'

/-- The coordinate `c₀` lies in the closure of the left half of `ORI`. -/
theorem mem_closure_leftHalf (c₀ : ℝ) (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1) :
    (⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : ORI) ∈ closure (leftHalf c₀) := by
  rw [val_isEmbedding.closure_eq_preimage_closure_image (s := leftHalf c₀)]
  change c₀ ∈ closure (val '' leftHalf c₀)
  have hIm : val '' leftHalf c₀ = Set.Ioo (0 : ℝ) c₀ := by
    ext r
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨(t : ORI).2.1, ht⟩
    · intro hr
      refine ⟨⟨r, ⟨hr.1, lt_trans hr.2 hc₀₁⟩⟩, hr.2, rfl⟩
  rw [hIm]
  have hcl : closure (Set.Ioo (0 : ℝ) c₀) = Set.Icc (0 : ℝ) c₀ :=
    closure_Ioo (by positivity : (0 : ℝ) ≠ c₀)
  rw [hcl]
  exact ⟨le_of_lt hc₀₀, le_rfl⟩

/-- The coordinate `c₀` lies in the closure of the right half of `ORI`. -/
theorem mem_closure_rightHalf (c₀ : ℝ) (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1) :
    (⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : ORI) ∈ closure (rightHalf c₀) := by
  rw [val_isEmbedding.closure_eq_preimage_closure_image (s := rightHalf c₀)]
  change c₀ ∈ closure (val '' rightHalf c₀)
  have hIm : val '' rightHalf c₀ = Set.Ioo c₀ 1 := by
    ext r
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨ht, (t : ORI).2.2⟩
    · intro hr
      refine ⟨⟨r, ⟨lt_of_lt_of_le hc₀₀ (le_of_lt hr.1), hr.2⟩⟩, hr.1, rfl⟩
  rw [hIm]
  have hcl : closure (Set.Ioo c₀ 1) = Set.Icc c₀ 1 :=
    closure_Ioo (by linarith : c₀ ≠ (1 : ℝ))
  rw [hcl]
  exact ⟨le_rfl, le_of_lt hc₀₁⟩

/-- The chart-piece of a real coordinate set `D`: the image of the
coordinates of `D` under the arc chart `e`. -/
def chartPiece {P : Set X} (e : ORI ≃ₜ {x : X // x ∈ P}) (D : Set ℝ) : Set X :=
  chartVal e '' {t : ORI | (t : ℝ) ∈ D}

/-- The coordinate set (in the `e`-chart) of a set `S`: all real
coordinates `t` whose chart point `chartVal e t` lies in `S`. -/
def coords {P : Set X} (e : ORI ≃ₜ {x : X // x ∈ P}) (S : Set X) : Set ℝ :=
  val '' {t : ORI | chartVal e t ∈ S}

/-- A real coordinate set is bounded away from both ends `0` and `1`. -/
def BoundedAway (D : Set ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ D, y ∈ Set.Ioo δ (1 - δ)

/-- A coordinate set has points arbitrarily close to the left end `0`. -/
def EscapesLeft (D : Set ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ y ∈ D, y < δ

/-- A coordinate set has points arbitrarily close to the right end `1`. -/
def EscapesRight (D : Set ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ y ∈ D, 1 - δ < y

theorem mem_chartPiece {P : Set X} (e : ORI ≃ₜ {x : X // x ∈ P}) {D : Set ℝ} {x : X} :
    x ∈ chartPiece e D ↔ ∃ t : ORI, (t : ℝ) ∈ D ∧ chartVal e t = x := by
  simp [chartPiece]

theorem mem_coords {P : Set X} (e : ORI ≃ₜ {x : X // x ∈ P}) {S : Set X} {y : ℝ} :
    y ∈ coords e S ↔ ∃ t : ORI, chartVal e t ∈ S ∧ val t = y := by
  simp [coords]

theorem chartPiece_union {P : Set X} (e : ORI ≃ₜ {x : X // x ∈ P}) (D₁ D₂ : Set ℝ) :
    chartPiece e (D₁ ∪ D₂) = chartPiece e D₁ ∪ chartPiece e D₂ := by
  ext x
  constructor
  · intro hx
    rw [mem_chartPiece] at hx
    rcases hx with ⟨t, ht, rfl⟩
    rcases ht with ht₁ | ht₂
    · left
      rw [mem_chartPiece]
      exact ⟨t, ht₁, rfl⟩
    · right
      rw [mem_chartPiece]
      exact ⟨t, ht₂, rfl⟩
  · intro hx
    rcases hx with hx | hx
    · rw [mem_chartPiece] at hx
      rcases hx with ⟨t, ht, rfl⟩
      rw [mem_chartPiece]
      exact ⟨t, Or.inl ht, rfl⟩
    · rw [mem_chartPiece] at hx
      rcases hx with ⟨t, ht, rfl⟩
      rw [mem_chartPiece]
      exact ⟨t, Or.inr ht, rfl⟩

theorem coords_subset_Ioo {P : Set X} (e : ORI ≃ₜ {x : X // x ∈ P}) {S : Set X} :
    coords e S ⊆ Set.Ioo (0 : ℝ) 1 := by
  intro y hy
  rw [mem_coords] at hy
  rcases hy with ⟨t, htS, hty⟩
  rw [← hty]
  exact t.2

/-- `chartPiece` over the coordinates of `S` recovers `S` (when `S ⊆ P`). -/
theorem chartPiece_coords {P : Set X} (e : ORI ≃ₜ {x : X // x ∈ P}) {S : Set X}
    (hSP : S ⊆ P) : chartPiece e (coords e S) = S := by
  ext x
  constructor
  · intro hx
    rw [mem_chartPiece] at hx
    rcases hx with ⟨t, ht, htx⟩
    rw [mem_coords] at ht
    rcases ht with ⟨u, huS, htu⟩
    have hut : u = t := by
      apply val_injective
      simpa [val] using htu
    subst u
    rw [← htx]
    exact huS
  · intro hx
    have hxP : x ∈ P := hSP hx
    rw [← chartVal_range e] at hxP
    rcases hxP with ⟨t, rfl⟩
    rw [mem_chartPiece]
    refine ⟨t, ?_, rfl⟩
    rw [mem_coords]
    refine ⟨t, hx, rfl⟩

/-- `chartPiece` over the whole unit interval is all of `P`. -/
theorem chartPiece_Ioo_univ {P : Set X} (e : ORI ≃ₜ {x : X // x ∈ P}) :
    chartPiece e (Set.Ioo (0 : ℝ) 1) = P := by
  ext x
  constructor
  · intro hx
    rw [mem_chartPiece] at hx
    rcases hx with ⟨t, -, rfl⟩
    exact (e t).2
  · intro hx
    rw [← chartVal_range e] at hx
    rcases hx with ⟨t, rfl⟩
    rw [mem_chartPiece]
    exact ⟨t, t.2, rfl⟩

/-- Coordinates of a connected subset of an arc form an order-connected
set of reals. -/
theorem coords_ordConnected {P : Set X} (e : ORI ≃ₜ {x : X // x ∈ P}) {S : Set X}
    (hSP : S ⊆ P) (hconn : IsConnected S) : (coords e S).OrdConnected := by
  haveI : ConnectedSpace {x : X // x ∈ S} := isConnected_iff_connectedSpace.mp hconn
  let G : {x : X // x ∈ S} → ℝ := fun x => val (e.symm ⟨(x : X), hSP x.2⟩)
  have hGcont : Continuous G := by
    dsimp [G]
    exact continuous_subtype_val.comp (e.symm.continuous.comp (Continuous.subtype_mk
      (f := fun x : {x : X // x ∈ S} => (x : X)) continuous_subtype_val (fun x => hSP x.2)))
  have hIm : G '' Set.univ = coords e S := by
    ext y
    constructor
    · rintro ⟨x, -, hy⟩
      rw [mem_coords]
      refine ⟨e.symm ⟨(x : X), hSP x.2⟩, ?_, ?_⟩
      · have hrew : chartVal e (e.symm ⟨(x : X), hSP x.2⟩) = (x : X) := by
          simp [chartVal]
        simpa [hrew] using x.2
      · exact hy
    · intro hy
      rw [mem_coords] at hy
      rcases hy with ⟨t, htS, hty⟩
      refine ⟨⟨chartVal e t, htS⟩, trivial, ?_⟩
      dsimp [G]
      rw [← hty]
      congr 1
      apply e.injective
      apply Subtype.ext
      simp [chartVal]
  have hcon : IsConnected (coords e S) := by
    rw [← hIm]
    exact IsConnected.image isConnected_univ G hGcont.continuousOn
  exact (isPreconnected_iff_ordConnected.mp hcon.isPreconnected)

/-- Coordinates of disjoint subsets are disjoint. -/
theorem disjoint_coords {P : Set X} (e : ORI ≃ₜ {x : X // x ∈ P}) {S T : Set X}
    (hST : Disjoint S T) : Disjoint (coords e S) (coords e T) := by
  rw [Set.disjoint_left]
  intro y hyS hyT
  rw [mem_coords] at hyS hyT
  rcases hyS with ⟨t, htS, hty⟩
  rcases hyT with ⟨u, huT, htu⟩
  have htu' : u = t := val_injective (htu.trans hty.symm)
  subst u
  exact (Set.disjoint_left.mp hST) htS huT

/-- Coordinates equal to the whole interval force the set to be all of `P`. -/
theorem coords_eq_Ioo_of_eq {P : Set X} (e : ORI ≃ₜ {x : X // x ∈ P}) {S : Set X}
    (hSP : S ⊆ P) (h : coords e S = Set.Ioo (0 : ℝ) 1) : S = P := by
  calc
    S = chartPiece e (coords e S) := (chartPiece_coords e hSP).symm
    _ = chartPiece e (Set.Ioo (0 : ℝ) 1) := by rw [h]
    _ = P := chartPiece_Ioo_univ e

/-- **Bounded-away sets cannot contain `p` in their chart-closure**: if
`p ∉ P` but `p ∈ closure (chartPiece e D)` then the real coordinates `D`
are not bounded away from both ends (compact chart images of closed
coordinate intervals are closed in a Hausdorff space). -/
theorem not_boundedAway {P : Set X} (e : ORI ≃ₜ {x : X // x ∈ P}) {p : X}
    {D : Set ℝ} (hD01 : D ⊆ Set.Ioo (0 : ℝ) 1)
    (hp : p ∈ closure (chartPiece e D)) (hpP : p ∉ P) : ¬ BoundedAway D := by
  intro hb
  rcases hb with ⟨δ, hδ, hsub⟩
  have hcl : IsClosed (subClosed e δ (1 - δ)) := subClosed_isClosed e hδ (by linarith)
  have hinc : chartPiece e D ⊆ subClosed e δ (1 - δ) := by
    intro x hx
    rw [mem_chartPiece] at hx
    rcases hx with ⟨t, ht, rfl⟩
    rw [mem_subClosed]
    refine ⟨t, ⟨le_of_lt (hsub (t : ℝ) ht).1, le_of_lt (hsub (t : ℝ) ht).2⟩, rfl⟩
  have hsubcl : closure (chartPiece e D) ⊆ subClosed e δ (1 - δ) := by
    rw [← IsClosed.closure_eq hcl]
    exact closure_mono hinc
  exact hpP (subClosed_subset_P e (hsubcl hp))

/-- A set not bounded away from both ends must escape to the left or to
the right. -/
theorem escapes_left_or_right_of_not_boundedAway {D : Set ℝ}
    (hD01 : D ⊆ Set.Ioo (0 : ℝ) 1) (h : ¬ BoundedAway D) :
    EscapesLeft D ∨ EscapesRight D := by
  classical
  by_contra h'
  push_neg at h'
  rcases h' with ⟨hL, hR⟩
  rw [EscapesLeft] at hL
  rw [EscapesRight] at hR
  push_neg at hL hR
  rcases hL with ⟨δ₁, hδ₁, h₁⟩
  rcases hR with ⟨δ₂, hδ₂, h₂⟩
  let d : ℝ := min (δ₁ / 2) (δ₂ / 2)
  have hd₀ : 0 < d := by
    dsimp [d]
    positivity
  apply h
  refine ⟨d, hd₀, ?_⟩
  intro y hy
  have hδ₁y : δ₁ ≤ y := h₁ y hy
  have hyδ₂ : y ≤ 1 - δ₂ := h₂ y hy
  constructor
  · have hδ₁d : δ₁ / 2 < δ₁ := by linarith
    have hdδ₁ : d < δ₁ := lt_of_le_of_lt (by dsimp [d]; exact min_le_left _ _) hδ₁d
    exact lt_of_lt_of_le hdδ₁ hδ₁y
  · have hδ₂d : δ₂ / 2 < δ₂ := by linarith
    have hdδ₂ : d < δ₂ := lt_of_le_of_lt (by dsimp [d]; exact min_le_right _ _) hδ₂d
    have hlow : 1 - δ₂ < 1 - d := by linarith
    exact lt_of_le_of_lt hyδ₂ hlow

/-- An order-connected set with points arbitrarily close to `0` contains a
full initial segment `(0,x₀)` below any of its points. -/
theorem initial_segment_subset_of_escapesLeft {D : Set ℝ} (hord : D.OrdConnected)
    (hesc : EscapesLeft D) {x₀ : ℝ} (hx₀ : x₀ ∈ D) : Set.Ioo (0 : ℝ) x₀ ⊆ D := by
  intro y hy
  rcases hesc y hy.1 with ⟨z, hzD, hzy⟩
  exact hord.out hzD hx₀ ⟨le_of_lt hzy, le_of_lt hy.2⟩

/-- An order-connected set with points arbitrarily close to `1` contains a
full terminal segment `(x₀,1)` above any of its points. -/
theorem terminal_segment_subset_of_escapesRight {D : Set ℝ} (hord : D.OrdConnected)
    (hesc : EscapesRight D) {x₀ : ℝ} (hx₀ : x₀ ∈ D) : Set.Ioo x₀ 1 ⊆ D := by
  intro y hy
  have hy1 : y < 1 := hy.2
  rcases hesc (1 - y) (by linarith) with ⟨z, hzD, hzy⟩
  have hzy' : y < z := by nlinarith
  exact hord.out hx₀ hzD ⟨le_of_lt hy.1, le_of_lt hzy'⟩

/-- An order-connected subset of `(0,1)` escaping to both ends is the whole
interval. -/
theorem escapes_left_escapesRight_eq_Ioo {D : Set ℝ} (hD01 : D ⊆ Set.Ioo (0 : ℝ) 1)
    (hord : D.OrdConnected) (hL : EscapesLeft D) (hR : EscapesRight D) :
    D = Set.Ioo (0 : ℝ) 1 := by
  ext y
  constructor
  · intro hy
    exact hD01 hy
  · intro hy
    have hy1 : y < 1 := hy.2
    rcases hL y hy.1 with ⟨z, hzD, hzy⟩
    rcases hR (1 - y) (by linarith) with ⟨w, hwD, hwy⟩
    have hyw : y < w := by nlinarith
    exact hord.out hzD hwD ⟨le_of_lt hzy, le_of_lt hyw⟩

/-- Two disjoint order-connected subsets of `(0,1)` cannot both escape to
the right. -/
theorem not_both_escapesRight {D₁ D₂ : Set ℝ} (h01₁ : D₁ ⊆ Set.Ioo (0 : ℝ) 1)
    (h01₂ : D₂ ⊆ Set.Ioo (0 : ℝ) 1) (ho₁ : D₁.OrdConnected) (ho₂ : D₂.OrdConnected)
    (hdisj : Disjoint D₁ D₂) (h₁ : EscapesRight D₁) (h₂ : EscapesRight D₂) : False := by
  rcases h₁ 1 (by norm_num) with ⟨x₁, hx₁, _⟩
  rcases h₂ 1 (by norm_num) with ⟨x₂, hx₂, _⟩
  let u : ℝ := (max x₁ x₂ + 1) / 2
  have hx₁₁ : x₁ < 1 := (h01₁ hx₁).2
  have hx₂₁ : x₂ < 1 := (h01₂ hx₂).2
  have hmax : max x₁ x₂ < 1 := max_lt hx₁₁ hx₂₁
  have hu₀ : max x₁ x₂ < u := by dsimp [u]; linarith
  have hu₁ : u < 1 := by dsimp [u]; linarith
  have hu₁' : u ∈ Set.Ioo x₁ 1 := ⟨lt_of_le_of_lt (le_max_left x₁ x₂) hu₀, hu₁⟩
  have hu₂' : u ∈ Set.Ioo x₂ 1 := ⟨lt_of_le_of_lt (le_max_right x₁ x₂) hu₀, hu₁⟩
  have hu₁ : u ∈ D₁ := terminal_segment_subset_of_escapesRight ho₁ h₁ hx₁ hu₁'
  have hu₂ : u ∈ D₂ := terminal_segment_subset_of_escapesRight ho₂ h₂ hx₂ hu₂'
  exact (Set.disjoint_left.mp hdisj) hu₁ hu₂

/-- If `p` is in the closure of the image of one initial segment of the
chart, and `p ∉ P`, then `p` is in the closure of EVERY initial segment. -/
theorem attract_from_initial {P : Set X} (e : ORI ≃ₜ {x : X // x ∈ P}) {p : X} {β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hp : p ∈ closure (sub e 0 β)) (hpP : p ∉ P) :
    ∀ a : ℝ, 0 < a → a < 1 → p ∈ closure (sub e 0 a) := by
  intro a ha0 ha1
  by_cases hba : β ≤ a
  · exact closure_mono (sub_mono e (le_refl (0 : ℝ)) hba) hp
  · have hab : a < β := lt_of_not_ge hba
    by_contra hpa
    have hcl : IsClosed (subClosed e a β) := subClosed_isClosed e ha0 hβ1
    have hinc : sub e 0 β ⊆ sub e 0 a ∪ subClosed e a β := by
      intro x hx
      rw [mem_sub] at hx
      rcases hx with ⟨t, ht, rfl⟩
      by_cases hta : (t : ℝ) < a
      · left
        rw [mem_sub]
        exact ⟨t, ⟨ht.1, hta⟩, rfl⟩
      · right
        rw [mem_subClosed]
        exact ⟨t, ⟨le_of_not_gt hta, le_of_lt ht.2⟩, rfl⟩
    have hcov : closure (sub e 0 β) ⊆ closure (sub e 0 a) ∪ subClosed e a β := by
      calc
        closure (sub e 0 β) ⊆ closure (sub e 0 a ∪ subClosed e a β) := closure_mono hinc
        _ = closure (sub e 0 a) ∪ closure (subClosed e a β) := closure_union
        _ = closure (sub e 0 a) ∪ subClosed e a β := by rw [IsClosed.closure_eq hcl]
    have hp2 : p ∈ closure (sub e 0 a) ∪ subClosed e a β := hcov hp
    rcases hp2 with hp2 | hp2
    · exact hpa hp2
    · exact hpP (subClosed_subset_P e hp2)

/-- **Core attract lemma** (real-coordinate form): if the coordinate set `D`
of an arc-side is order-connected, not the whole interval, escapes to the
left and carries `p` in its chart-closure, then `p` attracts the left end
of the arc. -/
theorem attract_left_of_coords {P : Set X} (e : ORI ≃ₜ {x : X // x ∈ P}) {p : X}
    {D : Set ℝ} (hD01 : D ⊆ Set.Ioo (0 : ℝ) 1) (hord : D.OrdConnected)
    (hDne : D ≠ Set.Ioo (0 : ℝ) 1) (hescL : EscapesLeft D)
    (hp : p ∈ closure (chartPiece e D)) (hpP : p ∉ P) :
    ∀ a : ℝ, 0 < a → a < 1 → p ∈ closure (sub e 0 a) := by
  have hnotR : ¬ EscapesRight D := by
    intro hR
    apply hDne
    exact escapes_left_escapesRight_eq_Ioo hD01 hord hescL hR
  rcases hescL 1 (by norm_num) with ⟨x₀, hx₀D, hx₀lt1⟩
  have hx₀pos : 0 < x₀ := (hD01 hx₀D).1
  have hinit : Set.Ioo (0 : ℝ) x₀ ⊆ D := initial_segment_subset_of_escapesLeft hord hescL hx₀D
  have hx₀cl : p ∈ closure (sub e 0 x₀) := by
    let D₂ : Set ℝ := D ∩ Set.Ici x₀
    have hsplit : D = Set.Ioo (0 : ℝ) x₀ ∪ D₂ := by
      ext y
      constructor
      · intro hy
        by_cases hyx : y < x₀
        · left
          exact ⟨(hD01 hy).1, hyx⟩
        · right
          dsimp [D₂]
          exact ⟨hy, le_of_not_gt hyx⟩
      · intro hy
        rcases hy with hy | hy
        · exact hinit hy
        · exact hy.1
    have hpiece : chartPiece e D = sub e 0 x₀ ∪ chartPiece e D₂ := by
      rw [hsplit, chartPiece_union]
      rfl
    have hp2 : p ∈ closure (sub e 0 x₀) ∪ closure (chartPiece e D₂) := by
      have heq : closure (chartPiece e D) =
          closure (sub e 0 x₀) ∪ closure (chartPiece e D₂) := by
        rw [hpiece, closure_union]
      rw [← heq]
      exact hp
    by_contra hpnot
    have hp2' : p ∈ closure (chartPiece e D₂) := by
      rcases hp2 with hp2 | hp2
      · exact False.elim (hpnot hp2)
      · exact hp2
    have hD₂01 : D₂ ⊆ Set.Ioo (0 : ℝ) 1 := fun y hy => hD01 hy.1
    have hnb : ¬ BoundedAway D₂ := not_boundedAway e hD₂01 hp2' hpP
    have hEsc₂ : EscapesLeft D₂ ∨ EscapesRight D₂ :=
      escapes_left_or_right_of_not_boundedAway hD₂01 hnb
    have hnotL₂ : ¬ EscapesLeft D₂ := by
      intro hL₂
      rcases hL₂ (x₀ / 2) (by positivity) with ⟨y, hy, hyx⟩
      have hyx₀ : x₀ ≤ y := hy.2
      linarith
    have hR₂ : EscapesRight D₂ := hEsc₂.resolve_left hnotL₂
    have hRD : EscapesRight D := by
      intro δ hδ
      rcases hR₂ δ hδ with ⟨y, hy, hyδ⟩
      exact ⟨y, hy.1, hyδ⟩
    exact hnotR hRD
  intro a ha0 ha1
  exact attract_from_initial e hx₀pos hx₀lt1 hx₀cl hpP a ha0 ha1

/-- **Side-pair attract lemma**: two disjoint connected sides of `P`, each
with `p` in its closure, force `p` to attract the left end of the arc
charted by `e`. -/
theorem attract_of_side_pair {P : Set X} (e : ORI ≃ₜ {x : X // x ∈ P}) {p : X}
    (hpP : p ∉ P) {L R : Set X} (hLP : L ⊆ P) (hRP : R ⊆ P) (hLR : Disjoint L R)
    (hLconn : IsConnected L) (hRconn : IsConnected R)
    (hpL : p ∈ closure L) (hpR : p ∈ closure R) (hLneP : L ≠ P) (hRneP : R ≠ P) :
    ∀ a : ℝ, 0 < a → a < 1 → p ∈ closure (sub e 0 a) := by
  have hpL' : p ∈ closure (chartPiece e (coords e L)) := by
    rw [← chartPiece_coords e hLP] at hpL
    exact hpL
  have hpR' : p ∈ closure (chartPiece e (coords e R)) := by
    rw [← chartPiece_coords e hRP] at hpR
    exact hpR
  have hordL : (coords e L).OrdConnected := coords_ordConnected e hLP hLconn
  have hordR : (coords e R).OrdConnected := coords_ordConnected e hRP hRconn
  have hdisj : Disjoint (coords e L) (coords e R) := disjoint_coords e hLR
  have hneL : coords e L ≠ Set.Ioo (0 : ℝ) 1 := by
    intro h
    exact hLneP (coords_eq_Ioo_of_eq e hLP h)
  have hneR : coords e R ≠ Set.Ioo (0 : ℝ) 1 := by
    intro h
    exact hRneP (coords_eq_Ioo_of_eq e hRP h)
  have hbL : ¬ BoundedAway (coords e L) :=
    not_boundedAway e (coords_subset_Ioo (S := L) e) hpL' hpP
  have hbR : ¬ BoundedAway (coords e R) :=
    not_boundedAway e (coords_subset_Ioo (S := R) e) hpR' hpP
  have hEscL : EscapesLeft (coords e L) ∨ EscapesRight (coords e L) :=
    escapes_left_or_right_of_not_boundedAway (coords_subset_Ioo (S := L) e) hbL
  have hEscR : EscapesLeft (coords e R) ∨ EscapesRight (coords e R) :=
    escapes_left_or_right_of_not_boundedAway (coords_subset_Ioo (S := R) e) hbR
  intro a ha0 ha1
  by_cases hEL : EscapesLeft (coords e L)
  · exact attract_left_of_coords e (coords_subset_Ioo (S := L) e) hordL hneL hEL hpL' hpP a ha0 ha1
  · have hERL : EscapesRight (coords e L) := hEscL.resolve_left hEL
    have hnotER : ¬ EscapesRight (coords e R) := by
      intro hER
      exact not_both_escapesRight (coords_subset_Ioo (S := L) e) (coords_subset_Ioo (S := R) e)
        hordL hordR hdisj hERL hER
    have hELR : EscapesLeft (coords e R) := hEscR.resolve_right hnotER
    exact attract_left_of_coords e (coords_subset_Ioo (S := R) e) hordR hneR hELR hpR' hpP a ha0 ha1

end AttractsLeftEnd

open AttractsLeftEnd

/-- **Boundary point attracts the left end.**  If the open arcs `P` and `W`
(`e : ORI ≃ₜ ↑P`, `ψ : ORI ≃ₜ ↑W`) overlap exactly in `W` minus the single
point `p = ψ(c₀)` (`0 < c₀ < 1`), then `p` is in the closure of every
initial segment `e((0,a))` of `P` — i.e. `p` attracts the LEFT end of `P`. -/
theorem boundary_point_attracts_left_end {X : Type*} [TopologicalSpace X] [T2Space X]
    {P W : Set X} (e : ({t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1}) ≃ₜ {x : X // x ∈ P})
    (ψ : ({t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1}) ≃ₜ {x : X // x ∈ W})
    {c₀ : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hstruct : P ∩ W = W \ {((ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : {x : X // x ∈ W}) : X)}) :
    ∀ a : ℝ, 0 < a → a < 1 →
      ((ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : {x : X // x ∈ W}) : X) ∈ closure
        ((fun t : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} =>
          ((e t : {x : X // x ∈ P}) : X)) ''
          {t : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} | (t : ℝ) ∈ Set.Ioo (0 : ℝ) a}) := by
  let p : X := ((ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : {x : X // x ∈ W}) : X)
  change ∀ a : ℝ, 0 < a → a < 1 → p ∈ closure (sub e 0 a)
  let L : Set X := chartVal ψ '' leftHalf c₀
  let R : Set X := chartVal ψ '' rightHalf c₀
  have hpW : p ∈ W := by
    simpa [p] using (ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩).2
  have hpP : p ∉ P := by
    intro hp
    have h' : p ∈ P ∩ W := ⟨hp, hpW⟩
    have h'' : p ∈ W \ ({p} : Set X) := by
      rw [← hstruct]
      exact h'
    exact h''.2 rfl
  have hL_P : L ⊆ P := by
    intro x hx
    dsimp [L] at hx
    rw [Set.mem_image] at hx
    rcases hx with ⟨t, ht, rfl⟩
    have hxW : chartVal ψ t ∈ W := (ψ t).2
    have hxp : chartVal ψ t ≠ p := by
      intro heq
      have ht_eq : t = ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ := by
        apply ψ.injective
        apply Subtype.ext
        simpa [chartVal, p] using heq
      have hlt : (t : ℝ) < c₀ := by
        dsimp [leftHalf] at ht
        exact ht
      rw [ht_eq] at hlt
      exact (lt_irrefl c₀) hlt
    have hx' : chartVal ψ t ∈ W \ ({p} : Set X) := ⟨hxW, by
      intro hps
      exact hxp (by simpa using hps)⟩
    have hPW : chartVal ψ t ∈ P ∩ W := by
      rw [hstruct]
      exact hx'
    exact hPW.1
  have hR_P : R ⊆ P := by
    intro x hx
    dsimp [R] at hx
    rw [Set.mem_image] at hx
    rcases hx with ⟨t, ht, rfl⟩
    have hxW : chartVal ψ t ∈ W := (ψ t).2
    have hxp : chartVal ψ t ≠ p := by
      intro heq
      have ht_eq : t = ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ := by
        apply ψ.injective
        apply Subtype.ext
        simpa [chartVal, p] using heq
      have hgt : c₀ < (t : ℝ) := by
        dsimp [rightHalf] at ht
        exact ht
      rw [ht_eq] at hgt
      exact (lt_irrefl c₀) hgt
    have hx' : chartVal ψ t ∈ W \ ({p} : Set X) := ⟨hxW, by
      intro hps
      exact hxp (by simpa using hps)⟩
    have hPW : chartVal ψ t ∈ P ∩ W := by
      rw [hstruct]
      exact hx'
    exact hPW.1
  have hLR : Disjoint L R := by
    rw [Set.disjoint_left]
    intro x hxL hxR
    dsimp [L, R] at hxL hxR
    rw [Set.mem_image] at hxL hxR
    rcases hxL with ⟨t₁, ht₁, rfl⟩
    rcases hxR with ⟨t₂, ht₂, hxeq⟩
    have hsub : t₂ = t₁ := by
      exact chartVal_injective ψ hxeq
    rw [hsub] at ht₂
    have hlt : (t₁ : ℝ) < c₀ := by
      dsimp [leftHalf] at ht₁
      exact ht₁
    have hgt : c₀ < (t₁ : ℝ) := by
      dsimp [rightHalf] at ht₂
      exact ht₂
    linarith
  have hpL : p ∈ closure L := by
    have himg := image_closure_subset_closure_image (s := leftHalf c₀) (chartVal_continuous ψ)
    have hmem : p ∈ chartVal ψ '' closure (leftHalf c₀) := by
      rw [Set.mem_image]
      refine ⟨⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩, mem_closure_leftHalf c₀ hc₀₀ hc₀₁, ?_⟩
      rfl
    dsimp [L]
    exact himg hmem
  have hpR : p ∈ closure R := by
    have himg := image_closure_subset_closure_image (s := rightHalf c₀) (chartVal_continuous ψ)
    have hmem : p ∈ chartVal ψ '' closure (rightHalf c₀) := by
      rw [Set.mem_image]
      refine ⟨⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩, mem_closure_rightHalf c₀ hc₀₀ hc₀₁, ?_⟩
      rfl
    dsimp [R]
    exact himg hmem
  have hLc : IsConnected L := by
    dsimp [L]
    exact IsConnected.image (isConnected_leftHalf c₀ hc₀₀ hc₀₁) (chartVal ψ)
      (chartVal_continuous ψ).continuousOn
  have hRc : IsConnected R := by
    dsimp [R]
    exact IsConnected.image (isConnected_rightHalf c₀ hc₀₀ hc₀₁) (chartVal ψ)
      (chartVal_continuous ψ).continuousOn
  have hLnonempty : L.Nonempty := by
    refine ⟨chartVal ψ ⟨c₀ / 2, ⟨by positivity, by linarith⟩⟩, ?_⟩
    dsimp [L]
    rw [Set.mem_image]
    refine ⟨⟨c₀ / 2, ⟨by positivity, by linarith⟩⟩, ?_, rfl⟩
    change (c₀ / 2 : ℝ) < c₀
    linarith
  have hRnonempty : R.Nonempty := by
    refine ⟨chartVal ψ ⟨(c₀ + 1) / 2, ⟨by positivity, by linarith⟩⟩, ?_⟩
    dsimp [R]
    rw [Set.mem_image]
    refine ⟨⟨(c₀ + 1) / 2, ⟨by positivity, by linarith⟩⟩, ?_, rfl⟩
    change c₀ < (c₀ + 1) / 2
    linarith
  have hLneP : L ≠ P := by
    intro hL
    rcases hRnonempty with ⟨x, hxR⟩
    have hxL : x ∈ L := by
      rw [hL]
      exact hR_P hxR
    exact (Set.disjoint_left.mp hLR) hxL hxR
  have hRneP : R ≠ P := by
    intro hR
    rcases hLnonempty with ⟨x, hxL⟩
    have hxR : x ∈ R := by
      rw [hR]
      exact hL_P hxL
    exact (Set.disjoint_left.mp hLR) hxL hxR
  intro a ha0 ha1
  exact (attract_of_side_pair (P := P) e hpP hL_P hR_P hLR hLc hRc hpL hpR hLneP hRneP) a ha0 ha1

end Commons.Topology.OneManifold