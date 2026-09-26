import Mathlib
import Submission.Commons.Topology.OneManifold.arc_branch_left_dichotomy
import Submission.Commons.Topology.OneManifold.arc_branch_right_dichotomy

open Set
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

noncomputable section

namespace Commons.Topology.OneManifold

/-!
# boundary_point_attracts_right_end

Let `P` and `W` be two open arcs of a Hausdorff space `X` (charts `e` and
`ψ` from the open unit interval) whose overlap is all of `W` except one
point `z = ψ⟨c₀⟩`:

    P ∩ W = W ∖ {z}.

Then `z` lies in the closure of every right terminal segment of the
`P`-arc: for all `b ∈ (0,1)`, `z ∈ closure (e '' (b,1))`.

## Proof structure

1. `z ∉ P`, and every other `W`-point lies in `P`.  The two components
   `C₁ = ψ '' (0,c₀)` and `C₂ = ψ '' (c₀,1)` of `W ∖ {z}` are two disjoint
   open sub-arcs of `P`.
2. The `P`-coordinates of `C₁` (resp. `C₂`) are the image of the interval
   `(0,c₀)` (resp. `(c₀,1)`) under the continuous injective chart-coordinate
   map `k = e.symm ∘ ψ`.  The terminal sub-branches `ψ '' (u,c₀)` and
   `ψ '' (c₀,u)` have `z` in their closure (continuity of `ψ`).
3. The delegated dichotomy
   `Commons.Topology.OneManifold.arc_branch_left_dichotomy` (resp. `...right_...`)
   applied to each branch yields: either `z` is in the closure of every right
   terminal segment of `P` (and we are done), or the branch coordinate range
   contains a whole initial real segment `(0,δ)`.
4. Both branches cannot be of the latter kind: their coordinate ranges are
   disjoint (the branches are disjoint and `e` is injective) yet two ranges
   containing initial segments `(0,δ₁)`, `(0,δ₂)` intersect.  Hence some
   branch gives the right-end attraction.
-/

private abbrev ORI : Type := {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1}

section Setup

variable {X : Type*} [TopologicalSpace X]
variable {P W : Set X}

/-- The chart coercion of `e` into `X`. -/
private def E (e : ORI ≃ₜ {x : X // x ∈ P}) : ORI → X :=
  fun t => (e t : {x : X // x ∈ P}).1

/-- The chart coercion of `ψ` into `X`. -/
private def PS (ψ : ORI ≃ₜ {x : X // x ∈ W}) : ORI → X :=
  fun t => (ψ t : {x : X // x ∈ W}).1

/-- The puncture point `z := ψ⟨c₀⟩` of the structural identity. -/
private def zval (ψ : ORI ≃ₜ {x : X // x ∈ W}) {c₀ : ℝ}
    (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1) : X :=
  ((ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : {x : X // x ∈ W}) : X)

private theorem E_cont (e : ORI ≃ₜ {x : X // x ∈ P}) : Continuous (E e) := by
  change Continuous (fun t : ORI => ((e t : {x : X // x ∈ P}) : X))
  exact continuous_subtype_val.comp e.continuous

private theorem PS_cont (ψ : ORI ≃ₜ {x : X // x ∈ W}) : Continuous (PS ψ) := by
  change Continuous (fun t : ORI => ((ψ t : {x : X // x ∈ W}) : X))
  exact continuous_subtype_val.comp ψ.continuous

private theorem E_inj (e : ORI ≃ₜ {x : X // x ∈ P}) : Function.Injective (E e) := by
  intro t s h
  apply e.injective
  apply Subtype.ext
  exact h

private theorem PS_inj (ψ : ORI ≃ₜ {x : X // x ∈ W}) : Function.Injective (PS ψ) := by
  intro t s h
  apply ψ.injective
  apply Subtype.ext
  exact h

private theorem E_range (e : ORI ≃ₜ {x : X // x ∈ P}) : Set.range (E e) = P := by
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    exact (e t).2
  · intro hy
    refine ⟨e.symm ⟨y, hy⟩, ?_⟩
    have h := congrArg (fun z : {x : X // x ∈ P} => (z : X)) (e.apply_symm_apply ⟨y, hy⟩)
    simpa [E] using h

/-- With `P ∩ W = W ∖ {z}` the puncture point `z` is not in `P`. -/
private theorem z_notin_P (ψ : ORI ≃ₜ {x : X // x ∈ W}) {c₀ : ℝ}
    (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hstruct : P ∩ W = W \ {((ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : {x : X // x ∈ W}) : X)}) :
    zval ψ hc₀₀ hc₀₁ ∉ P := by
  intro hzP
  have hzW : zval ψ hc₀₀ hc₀₁ ∈ W := (ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩).2
  have hzPW : zval ψ hc₀₀ hc₀₁ ∈ P ∩ W := ⟨hzP, hzW⟩
  have hz' : zval ψ hc₀₀ hc₀₁ ∈ W \ {zval ψ hc₀₀ hc₀₁} := by
    rw [hstruct] at hzPW
    exact hzPW
  exact hz'.2 rfl

/-- Chart points of `W` other than the puncture are `P`-points. -/
private theorem psi_coord_in_P (ψ : ORI ≃ₜ {x : X // x ∈ W}) {c₀ : ℝ}
    (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hstruct : P ∩ W = W \ {((ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : {x : X // x ∈ W}) : X)}) :
    ∀ t : ORI, (t : ℝ) ≠ c₀ → (PS ψ t) ∈ P := by
  intro t ht
  have hval : (PS ψ t) ∈ W := (ψ t).2
  have hvalne : (PS ψ t) ≠ ((ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : {x : X // x ∈ W}) : X) := by
    intro h
    apply ht
    have hψt : (ψ t : {x : X // x ∈ W}) = ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ := by
      apply Subtype.ext
      exact h
    have htEq : t = ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ := ψ.injective hψt
    exact congrArg (fun q : ORI => (q : ℝ)) htEq
  have hzmem : (PS ψ t) ∈ W \ {((ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : {x : X // x ∈ W}) : X)} :=
    ⟨hval, hvalne⟩
  have hPW : (PS ψ t) ∈ P ∩ W := by
    rw [hstruct]
    exact hzmem
  exact hPW.1

/-- Continuous maps send closures of sets into closures of their images. -/
private theorem cont_image_closure {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : Y → Z) (hf : Continuous f) {A : Set Y} {y : Y} (hy : y ∈ closure A) :
    f y ∈ closure (f '' A) := by
  rw [mem_closure_iff]
  intro o ho ho_fy
  have hpre : IsOpen (f ⁻¹' o) := ho.preimage hf
  have hyo : y ∈ f ⁻¹' o := ho_fy
  have hne : ((f ⁻¹' o) ∩ A).Nonempty := (mem_closure_iff.mp hy) (f ⁻¹' o) hpre hyo
  rcases hne with ⟨a, hao, haA⟩
  exact ⟨f a, ⟨hao, mem_image_of_mem f haA⟩⟩

/-- `c₀` is in the closure (in `ORI`) of the left sub-interval `(u,c₀)`. -/
private theorem cpt_mem_closure_left {c₀ : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1) {u : ℝ}
    (hu0 : 0 < u) (huc : u < c₀) :
    (⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : ORI) ∈ closure
      ({t : ORI | u < (t : ℝ) ∧ (t : ℝ) < c₀} : Set ORI) := by
  let A : Set ORI := {t : ORI | u < (t : ℝ) ∧ (t : ℝ) < c₀}
  let val : ORI → ℝ := fun t => (t : ℝ)
  have hInd : Topology.IsInducing val := by
    simpa [val] using (Topology.IsInducing.subtypeVal : Topology.IsInducing
      (Subtype.val : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} → ℝ))
  have hclreal : c₀ ∈ closure (Set.Ioo u c₀ : Set ℝ) := by
    rw [closure_Ioo (ne_of_lt huc)]
    exact ⟨le_of_lt huc, le_rfl⟩
  have hvalA : val '' A = (Set.Ioo u c₀ : Set ℝ) := by
    ext r
    constructor
    · rintro ⟨t, htA, rfl⟩
      exact htA
    · intro hr
      have hr01 : r ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_trans hu0 hr.1, lt_trans hr.2 hc₀₁⟩
      refine ⟨⟨r, hr01⟩, ?_, rfl⟩
      exact hr
  have hc₀val : (⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : ORI) ∈ (val ⁻¹' closure (val '' A)) := by
    simpa [hvalA] using hclreal
  have h : (⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : ORI) ∈ closure A := by
    rw [Topology.IsInducing.closure_eq_preimage_closure_image hInd A]
    simpa [A] using hc₀val
  simpa [A] using h

/-- `c₀` is in the closure (in `ORI`) of the right sub-interval `(c₀,v)`. -/
private theorem cpt_mem_closure_right {c₀ : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1) {v : ℝ}
    (hcv : c₀ < v) (hv1 : v < 1) :
    (⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : ORI) ∈ closure
      ({t : ORI | c₀ < (t : ℝ) ∧ (t : ℝ) < v} : Set ORI) := by
  let A : Set ORI := {t : ORI | c₀ < (t : ℝ) ∧ (t : ℝ) < v}
  let val : ORI → ℝ := fun t => (t : ℝ)
  have hInd : Topology.IsInducing val := by
    simpa [val] using (Topology.IsInducing.subtypeVal : Topology.IsInducing
      (Subtype.val : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} → ℝ))
  have hclreal : c₀ ∈ closure (Set.Ioo c₀ v : Set ℝ) := by
    rw [closure_Ioo (ne_of_lt hcv)]
    exact ⟨le_rfl, le_of_lt hcv⟩
  have hvalA : val '' A = (Set.Ioo c₀ v : Set ℝ) := by
    ext r
    constructor
    · rintro ⟨t, htA, rfl⟩
      exact htA
    · intro hr
      have hr01 : r ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_trans hc₀₀ hr.1, lt_trans hr.2 hv1⟩
      refine ⟨⟨r, hr01⟩, ?_, rfl⟩
      exact hr
  have hc₀val : (⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : ORI) ∈ (val ⁻¹' closure (val '' A)) := by
    simpa [hvalA] using hclreal
  have h : (⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : ORI) ∈ closure A := by
    rw [Topology.IsInducing.closure_eq_preimage_closure_image hInd A]
    simpa [A] using hc₀val
  simpa [A] using h

/-- The puncture `z` lies in the closure of every left `ψ`-subarc `(u,c₀)`. -/
private theorem z_mem_closure_left_subarc (ψ : ORI ≃ₜ {x : X // x ∈ W})
    {c₀ : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1) {u : ℝ} (hu0 : 0 < u) (huc : u < c₀) :
    zval ψ hc₀₀ hc₀₁ ∈ closure (PS ψ '' {t : ORI | u < (t : ℝ) ∧ (t : ℝ) < c₀}) := by
  have hc : (⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : ORI) ∈ closure
      ({t : ORI | u < (t : ℝ) ∧ (t : ℝ) < c₀} : Set ORI) :=
    cpt_mem_closure_left hc₀₀ hc₀₁ hu0 huc
  have him := cont_image_closure (PS ψ) (PS_cont ψ) hc
  exact him

/-- The puncture `z` lies in the closure of every right `ψ`-subarc `(c₀,v)`. -/
private theorem z_mem_closure_right_subarc (ψ : ORI ≃ₜ {x : X // x ∈ W})
    {c₀ : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1) {v : ℝ} (hcv : c₀ < v) (hv1 : v < 1) :
    zval ψ hc₀₀ hc₀₁ ∈ closure (PS ψ '' {t : ORI | c₀ < (t : ℝ) ∧ (t : ℝ) < v}) := by
  have hc : (⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : ORI) ∈ closure
      ({t : ORI | c₀ < (t : ℝ) ∧ (t : ℝ) < v} : Set ORI) :=
    cpt_mem_closure_right hc₀₀ hc₀₁ hcv hv1
  have him := cont_image_closure (PS ψ) (PS_cont ψ) hc
  exact him

end Setup

section Branch

/-- The left branch coordinate domain `(0,c₀)`. -/
private abbrev DL (c₀ : ℝ) : Type := {s : ℝ // s ∈ Set.Ioo (0 : ℝ) c₀}

/-- The right branch coordinate domain `(c₀,1)`. -/
private abbrev DR (c₀ : ℝ) : Type := {s : ℝ // s ∈ Set.Ioo c₀ 1}

/-- Coordinate embedding of the left branch domain into `ORI`. -/
private def toORIL {c₀ : ℝ} (hc₀₁ : c₀ < 1) : DL c₀ → ORI :=
  fun s => ⟨(s : ℝ), ⟨s.2.1, lt_trans s.2.2 hc₀₁⟩⟩

/-- Coordinate embedding of the right branch domain into `ORI`. -/
private def toORIR {c₀ : ℝ} (hc₀₀ : 0 < c₀) : DR c₀ → ORI :=
  fun s => ⟨(s : ℝ), ⟨lt_trans hc₀₀ s.2.1, s.2.2⟩⟩

private theorem toORIL_cont {c₀ : ℝ} (hc₀₁ : c₀ < 1) : Continuous (toORIL hc₀₁) := by
  exact Continuous.subtype_mk continuous_subtype_val (fun s => ⟨s.2.1, lt_trans s.2.2 hc₀₁⟩)

private theorem toORIR_cont {c₀ : ℝ} (hc₀₀ : 0 < c₀) : Continuous (toORIR hc₀₀) := by
  exact Continuous.subtype_mk continuous_subtype_val (fun s => ⟨lt_trans hc₀₀ s.2.1, s.2.2⟩)

/-- The `e`-coordinate of a `ψ`-chart point `t ≠ c₀` (well-defined: the
point lies in `P`). -/
private def kcoord {X : Type*} [TopologicalSpace X] {P W : Set X}
    (e : ORI ≃ₜ {x : X // x ∈ P}) (ψ : ORI ≃ₜ {x : X // x ∈ W}) {c₀ : ℝ}
    (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hstruct : P ∩ W = W \ {((ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : {x : X // x ∈ W}) : X)})
    (t : ORI) (ht : (t : ℝ) ≠ c₀) : ORI :=
  e.symm ⟨PS ψ t, psi_coord_in_P ψ hc₀₀ hc₀₁ hstruct t ht⟩

/-- Applying `e` to the coordinate recovers the `ψ`-point. -/
private theorem E_kcoord {X : Type*} [TopologicalSpace X] {P W : Set X}
    (e : ORI ≃ₜ {x : X // x ∈ P}) (ψ : ORI ≃ₜ {x : X // x ∈ W}) {c₀ : ℝ}
    (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hstruct : P ∩ W = W \ {((ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : {x : X // x ∈ W}) : X)})
    (t : ORI) (ht : (t : ℝ) ≠ c₀) :
    E e (kcoord e ψ hc₀₀ hc₀₁ hstruct t ht) = PS ψ t := by
  unfold kcoord
  exact congrArg (fun q : {x : X // x ∈ P} => (q : X)) (e.apply_symm_apply ⟨PS ψ t, _⟩)

/-- The left branch coordinate function `fL : (0,c₀) → ORI`. -/
private def fL {X : Type*} [TopologicalSpace X] {P W : Set X}
    (e : ORI ≃ₜ {x : X // x ∈ P}) (ψ : ORI ≃ₜ {x : X // x ∈ W}) {c₀ : ℝ}
    (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hstruct : P ∩ W = W \ {((ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : {x : X // x ∈ W}) : X)}) :
    DL c₀ → ORI :=
  fun s => kcoord e ψ hc₀₀ hc₀₁ hstruct (toORIL hc₀₁ s) (by
    simpa [toORIL] using (ne_of_lt s.2.2))

/-- The right branch coordinate function `fR : (c₀,1) → ORI`. -/
private def fR {X : Type*} [TopologicalSpace X] {P W : Set X}
    (e : ORI ≃ₜ {x : X // x ∈ P}) (ψ : ORI ≃ₜ {x : X // x ∈ W}) {c₀ : ℝ}
    (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hstruct : P ∩ W = W \ {((ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : {x : X // x ∈ W}) : X)}) :
    DR c₀ → ORI :=
  fun s => kcoord e ψ hc₀₀ hc₀₁ hstruct (toORIR hc₀₀ s) (by
    simpa [toORIR] using (ne_of_lt s.2.1).symm)

/-- `E (fL s) = PS ψ (toORIL s)`. -/
private theorem E_fL {X : Type*} [TopologicalSpace X] {P W : Set X}
    (e : ORI ≃ₜ {x : X // x ∈ P}) (ψ : ORI ≃ₜ {x : X // x ∈ W}) {c₀ : ℝ}
    (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hstruct : P ∩ W = W \ {((ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : {x : X // x ∈ W}) : X)})
    (s : DL c₀) :
    E e (fL e ψ hc₀₀ hc₀₁ hstruct s) = PS ψ (toORIL hc₀₁ s) := by
  unfold fL
  exact E_kcoord e ψ hc₀₀ hc₀₁ hstruct (toORIL hc₀₁ s) (ne_of_lt s.2.2)

/-- `E (fR s) = PS ψ (toORIR s)`. -/
private theorem E_fR {X : Type*} [TopologicalSpace X] {P W : Set X}
    (e : ORI ≃ₜ {x : X // x ∈ P}) (ψ : ORI ≃ₜ {x : X // x ∈ W}) {c₀ : ℝ}
    (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hstruct : P ∩ W = W \ {((ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : {x : X // x ∈ W}) : X)})
    (s : DR c₀) :
    E e (fR e ψ hc₀₀ hc₀₁ hstruct s) = PS ψ (toORIR hc₀₀ s) := by
  unfold fR
  exact E_kcoord e ψ hc₀₀ hc₀₁ hstruct (toORIR hc₀₀ s) (by
    simpa [toORIR] using (ne_of_lt s.2.1).symm)

/-- `fL` is continuous. -/
private theorem fL_cont {X : Type*} [TopologicalSpace X] {P W : Set X}
    (e : ORI ≃ₜ {x : X // x ∈ P}) (ψ : ORI ≃ₜ {x : X // x ∈ W}) {c₀ : ℝ}
    (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hstruct : P ∩ W = W \ {((ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : {x : X // x ∈ W}) : X)}) :
    Continuous (fL e ψ hc₀₀ hc₀₁ hstruct) := by
  let g : DL c₀ → {x : X // x ∈ P} :=
    fun s => ⟨PS ψ (toORIL hc₀₁ s),
      psi_coord_in_P ψ hc₀₀ hc₀₁ hstruct (toORIL hc₀₁ s)
        (by simpa [toORIL] using (ne_of_lt s.2.2))⟩
  have hcont_PS_or : Continuous (fun s : DL c₀ => PS ψ (toORIL hc₀₁ s)) :=
    (PS_cont ψ).comp (toORIL_cont hc₀₁)
  have hg_cont : Continuous g := by
    dsimp [g]
    exact Continuous.subtype_mk hcont_PS_or (fun s =>
      psi_coord_in_P ψ hc₀₀ hc₀₁ hstruct (toORIL hc₀₁ s)
        (by simpa [toORIL] using (ne_of_lt s.2.2)))
  have hEq : fL e ψ hc₀₀ hc₀₁ hstruct = e.symm ∘ g := by
    funext s
    simp [fL, kcoord, g]
  rw [hEq]
  exact e.symm.continuous.comp hg_cont

/-- `fR` is continuous. -/
private theorem fR_cont {X : Type*} [TopologicalSpace X] {P W : Set X}
    (e : ORI ≃ₜ {x : X // x ∈ P}) (ψ : ORI ≃ₜ {x : X // x ∈ W}) {c₀ : ℝ}
    (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hstruct : P ∩ W = W \ {((ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : {x : X // x ∈ W}) : X)}) :
    Continuous (fR e ψ hc₀₀ hc₀₁ hstruct) := by
  let g : DR c₀ → {x : X // x ∈ P} :=
    fun s => ⟨PS ψ (toORIR hc₀₀ s),
      psi_coord_in_P ψ hc₀₀ hc₀₁ hstruct (toORIR hc₀₀ s)
        (by simpa [toORIR] using (ne_of_lt s.2.1).symm)⟩
  have hcont_PS_or : Continuous (fun s : DR c₀ => PS ψ (toORIR hc₀₀ s)) :=
    (PS_cont ψ).comp (toORIR_cont hc₀₀)
  have hg_cont : Continuous g := by
    dsimp [g]
    exact Continuous.subtype_mk hcont_PS_or (fun s =>
      psi_coord_in_P ψ hc₀₀ hc₀₁ hstruct (toORIR hc₀₀ s)
        (by simpa [toORIR] using (ne_of_lt s.2.1).symm))
  have hEq : fR e ψ hc₀₀ hc₀₁ hstruct = e.symm ∘ g := by
    funext s
    simp [fR, kcoord, g]
  rw [hEq]
  exact e.symm.continuous.comp hg_cont

/-- `fL` is injective. -/
private theorem fL_inj {X : Type*} [TopologicalSpace X] {P W : Set X}
    (e : ORI ≃ₜ {x : X // x ∈ P}) (ψ : ORI ≃ₜ {x : X // x ∈ W}) {c₀ : ℝ}
    (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hstruct : P ∩ W = W \ {((ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : {x : X // x ∈ W}) : X)}) :
    Function.Injective (fL e ψ hc₀₀ hc₀₁ hstruct) := by
  intro s t h
  have hE : E e (fL e ψ hc₀₀ hc₀₁ hstruct s) = E e (fL e ψ hc₀₀ hc₀₁ hstruct t) :=
    congrArg (E e) h
  rw [E_fL, E_fL] at hE
  have hOR : toORIL hc₀₁ s = toORIL hc₀₁ t := by
    apply ψ.injective
    apply Subtype.ext
    exact hE
  apply Subtype.ext
  have hval := congrArg (fun q : ORI => (q : ℝ)) hOR
  simpa [toORIL] using hval

/-- `fR` is injective. -/
private theorem fR_inj {X : Type*} [TopologicalSpace X] {P W : Set X}
    (e : ORI ≃ₜ {x : X // x ∈ P}) (ψ : ORI ≃ₜ {x : X // x ∈ W}) {c₀ : ℝ}
    (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hstruct : P ∩ W = W \ {((ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : {x : X // x ∈ W}) : X)}) :
    Function.Injective (fR e ψ hc₀₀ hc₀₁ hstruct) := by
  intro s t h
  have hE : E e (fR e ψ hc₀₀ hc₀₁ hstruct s) = E e (fR e ψ hc₀₀ hc₀₁ hstruct t) :=
    congrArg (E e) h
  rw [E_fR, E_fR] at hE
  have hOR : toORIR hc₀₀ s = toORIR hc₀₀ t := by
    apply ψ.injective
    apply Subtype.ext
    exact hE
  apply Subtype.ext
  have hval := congrArg (fun q : ORI => (q : ℝ)) hOR
  simpa [toORIR] using hval

/-- The left terminal sub-branches of `W` give the CoreL closure hypothesis. -/
private theorem toORIL_subarc {c₀ : ℝ} (hc₀₁ : c₀ < 1) {u : ℝ} (hu0 : 0 < u) (huc : u < c₀) :
    toORIL hc₀₁ '' {t : DL c₀ | u < (t : ℝ)} =
      {t : ORI | u < (t : ℝ) ∧ (t : ℝ) < c₀} := by
  ext q
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨by simpa [toORIL] using hs, by simpa [toORIL] using s.2.2⟩
  · intro hq
    refine ⟨⟨(q : ℝ), ⟨q.2.1, hq.2⟩⟩, ?_, ?_⟩
    · simpa using hq.1
    · apply Subtype.ext
      simp [toORIL]

/-- The right terminal sub-branches of `W` give the CoreR closure hypothesis. -/
private theorem toORIR_subarc {c₀ : ℝ} (hc₀₀ : 0 < c₀) {v : ℝ} (hcv : c₀ < v) (hv1 : v < 1) :
    toORIR hc₀₀ '' {t : DR c₀ | (t : ℝ) < v} =
      {t : ORI | c₀ < (t : ℝ) ∧ (t : ℝ) < v} := by
  ext q
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨by simpa [toORIR] using s.2.1, by simpa [toORIR] using hs⟩
  · intro hq
    refine ⟨⟨(q : ℝ), ⟨hq.1, q.2.2⟩⟩, ?_, ?_⟩
    · simpa using hq.2
    · apply Subtype.ext
      simp [toORIR]

/-- `E ∘ fL = PS ψ ∘ toORIL` (agreement of the two parametrisations). -/
private theorem comp_E_fL {X : Type*} [TopologicalSpace X] {P W : Set X}
    (e : ORI ≃ₜ {x : X // x ∈ P}) (ψ : ORI ≃ₜ {x : X // x ∈ W}) {c₀ : ℝ}
    (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hstruct : P ∩ W = W \ {((ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : {x : X // x ∈ W}) : X)}) :
    E e ∘ fL e ψ hc₀₀ hc₀₁ hstruct = PS ψ ∘ toORIL hc₀₁ := by
  funext s
  exact E_fL e ψ hc₀₀ hc₀₁ hstruct s

/-- `E ∘ fR = PS ψ ∘ toORIR` (agreement of the two parametrisations). -/
private theorem comp_E_fR {X : Type*} [TopologicalSpace X] {P W : Set X}
    (e : ORI ≃ₜ {x : X // x ∈ P}) (ψ : ORI ≃ₜ {x : X // x ∈ W}) {c₀ : ℝ}
    (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hstruct : P ∩ W = W \ {((ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : {x : X // x ∈ W}) : X)}) :
    E e ∘ fR e ψ hc₀₀ hc₀₁ hstruct = PS ψ ∘ toORIR hc₀₀ := by
  funext s
  exact E_fR e ψ hc₀₀ hc₀₁ hstruct s

/-- The left terminal sub-branches of `W` give the CoreL closure hypothesis. -/
private theorem z_mem_closure_left_coord {X : Type*} [TopologicalSpace X] {P W : Set X}
    (e : ORI ≃ₜ {x : X // x ∈ P}) (ψ : ORI ≃ₜ {x : X // x ∈ W}) {c₀ : ℝ}
    (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hstruct : P ∩ W = W \ {((ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : {x : X // x ∈ W}) : X)})
    (u : DL c₀) :
    zval ψ hc₀₀ hc₀₁ ∈ closure
      (E e '' (fL e ψ hc₀₀ hc₀₁ hstruct '' {t : DL c₀ | (u : ℝ) < (t : ℝ)})) := by
  have hEq : E e '' (fL e ψ hc₀₀ hc₀₁ hstruct '' {t : DL c₀ | (u : ℝ) < (t : ℝ)}) =
      PS ψ '' {t : ORI | (u : ℝ) < (t : ℝ) ∧ (t : ℝ) < c₀} := by
    calc
      E e '' (fL e ψ hc₀₀ hc₀₁ hstruct '' {t : DL c₀ | (u : ℝ) < (t : ℝ)})
          = (E e ∘ fL e ψ hc₀₀ hc₀₁ hstruct) '' {t : DL c₀ | (u : ℝ) < (t : ℝ)} := by
              rw [← Set.image_comp]
      _ = (PS ψ ∘ toORIL hc₀₁) '' {t : DL c₀ | (u : ℝ) < (t : ℝ)} := by
              rw [comp_E_fL e ψ hc₀₀ hc₀₁ hstruct]
      _ = PS ψ '' (toORIL hc₀₁ '' {t : DL c₀ | (u : ℝ) < (t : ℝ)}) := by
              rw [Set.image_comp]
      _ = PS ψ '' {t : ORI | (u : ℝ) < (t : ℝ) ∧ (t : ℝ) < c₀} := by
              rw [toORIL_subarc hc₀₁ u.2.1 u.2.2]
  rw [hEq]
  exact z_mem_closure_left_subarc ψ hc₀₀ hc₀₁ u.2.1 u.2.2

/-- The right terminal sub-branches of `W` give the CoreR closure hypothesis. -/
private theorem z_mem_closure_right_coord {X : Type*} [TopologicalSpace X] {P W : Set X}
    (e : ORI ≃ₜ {x : X // x ∈ P}) (ψ : ORI ≃ₜ {x : X // x ∈ W}) {c₀ : ℝ}
    (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hstruct : P ∩ W = W \ {((ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : {x : X // x ∈ W}) : X)})
    (u : DR c₀) :
    zval ψ hc₀₀ hc₀₁ ∈ closure
      (E e '' (fR e ψ hc₀₀ hc₀₁ hstruct '' {t : DR c₀ | (t : ℝ) < (u : ℝ)})) := by
  have hEq : E e '' (fR e ψ hc₀₀ hc₀₁ hstruct '' {t : DR c₀ | (t : ℝ) < (u : ℝ)}) =
      PS ψ '' {t : ORI | c₀ < (t : ℝ) ∧ (t : ℝ) < (u : ℝ)} := by
    calc
      E e '' (fR e ψ hc₀₀ hc₀₁ hstruct '' {t : DR c₀ | (t : ℝ) < (u : ℝ)})
          = (E e ∘ fR e ψ hc₀₀ hc₀₁ hstruct) '' {t : DR c₀ | (t : ℝ) < (u : ℝ)} := by
              rw [← Set.image_comp]
      _ = (PS ψ ∘ toORIR hc₀₀) '' {t : DR c₀ | (t : ℝ) < (u : ℝ)} := by
              rw [comp_E_fR e ψ hc₀₀ hc₀₁ hstruct]
      _ = PS ψ '' (toORIR hc₀₀ '' {t : DR c₀ | (t : ℝ) < (u : ℝ)}) := by
              rw [Set.image_comp]
      _ = PS ψ '' {t : ORI | c₀ < (t : ℝ) ∧ (t : ℝ) < (u : ℝ)} := by
              rw [toORIR_subarc hc₀₀ u.2.1 u.2.2]
  rw [hEq]
  exact z_mem_closure_right_subarc ψ hc₀₀ hc₀₁ u.2.1 u.2.2

/-- The two `ψ`-branches `(0,c₀)` and `(c₀,1)` are disjoint. -/
private theorem branches_disjoint {X : Type*} [TopologicalSpace X] {W : Set X}
    (ψ : ORI ≃ₜ {x : X // x ∈ W}) {c₀ : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1) :
    (PS ψ '' {t : ORI | (t : ℝ) < c₀}) ∩ (PS ψ '' {t : ORI | c₀ < (t : ℝ)}) = ∅ := by
  ext y
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, ⟨b, hb, hEq⟩⟩
    have ha' : (a : ℝ) < c₀ := by simpa using ha
    have hb' : c₀ < (b : ℝ) := by simpa using hb
    have hab : a = b := by
      apply ψ.injective
      apply Subtype.ext
      exact hEq.symm
    have : (a : ℝ) < (a : ℝ) := by
      simpa [hab] using (lt_trans ha' hb')
    exact False.elim ((lt_irrefl (a : ℝ)) this)
  · intro hy
    exact False.elim hy

/-- The coordinate ranges of the two branches are disjoint. -/
private theorem coord_ranges_disjoint {X : Type*} [TopologicalSpace X] {P W : Set X}
    (e : ORI ≃ₜ {x : X // x ∈ P}) (ψ : ORI ≃ₜ {x : X // x ∈ W}) {c₀ : ℝ}
    (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hstruct : P ∩ W = W \ {((ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : {x : X // x ∈ W}) : X)}) :
    ¬ ∃ t : ORI, (∃ s : DL c₀, fL e ψ hc₀₀ hc₀₁ hstruct s = t) ∧
                (∃ s' : DR c₀, fR e ψ hc₀₀ hc₀₁ hstruct s' = t) := by
  rintro ⟨t, htL, htR⟩
  rcases htL with ⟨sL, hL⟩
  rcases htR with ⟨sR, hR⟩
  have hmem1 : E e t ∈ PS ψ '' {t : ORI | (t : ℝ) < c₀} := by
    rw [← hL, E_fL]
    exact mem_image_of_mem (PS ψ) (by simpa [toORIL] using sL.2.2)
  have hmem2 : E e t ∈ PS ψ '' {t : ORI | c₀ < (t : ℝ)} := by
    rw [← hR, E_fR]
    exact mem_image_of_mem (PS ψ) (by simpa [toORIR] using sR.2.1)
  have hbad : E e t ∈ (∅ : Set X) := by
    rw [← branches_disjoint ψ hc₀₀ hc₀₁]
    exact ⟨hmem1, hmem2⟩
  exact hbad

/-- Two initial real segments `(0,δ₁)`, `(0,δ₂)` in the two disjoint branch
coordinate ranges contradict. -/
private theorem zero_ranges_contradiction {X : Type*} [TopologicalSpace X] {P W : Set X}
    (e : ORI ≃ₜ {x : X // x ∈ P}) (ψ : ORI ≃ₜ {x : X // x ∈ W}) {c₀ : ℝ}
    (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hstruct : P ∩ W = W \ {((ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : {x : X // x ∈ W}) : X)})
    {δ₁ : ℝ} (hδ₁ : 0 < δ₁)
    (h₁ : ∀ t : ℝ, 0 < t → t < δ₁ →
      ∃ s : DL c₀, (fL e ψ hc₀₀ hc₀₁ hstruct s : ℝ) = t)
    {δ₂ : ℝ} (hδ₂ : 0 < δ₂)
    (h₂ : ∀ t : ℝ, 0 < t → t < δ₂ →
      ∃ s : DR c₀, (fR e ψ hc₀₀ hc₀₁ hstruct s : ℝ) = t) : False := by
  let m : ℝ := min δ₁ δ₂
  let t₀ : ℝ := m / 2
  have hm : 0 < m := lt_min hδ₁ hδ₂
  have ht₀₀ : 0 < t₀ := by
    dsimp [t₀]
    linarith
  have ht₀₁ : t₀ < δ₁ := by
    dsimp [t₀]
    have hm2 : m ≤ δ₁ := min_le_left δ₁ δ₂
    have hhalf : m / 2 < m := by
      dsimp [m]
      linarith
    exact lt_of_lt_of_le hhalf hm2
  have ht₀₂ : t₀ < δ₂ := by
    dsimp [t₀]
    have hm2 : m ≤ δ₂ := min_le_right δ₁ δ₂
    have hhalf : m / 2 < m := by
      dsimp [m]
      linarith
    exact lt_of_lt_of_le hhalf hm2
  rcases h₁ t₀ ht₀₀ ht₀₁ with ⟨s₁, ht₁⟩
  rcases h₂ t₀ ht₀₀ ht₀₂ with ⟨s₂, ht₂⟩
  apply coord_ranges_disjoint e ψ hc₀₀ hc₀₁ hstruct
  refine ⟨fL e ψ hc₀₀ hc₀₁ hstruct s₁, ⟨s₁, rfl⟩, ?_⟩
  refine ⟨s₂, ?_⟩
  apply Subtype.ext
  calc
    (fR e ψ hc₀₀ hc₀₁ hstruct s₂ : ℝ) = t₀ := ht₂
    _ = (fL e ψ hc₀₀ hc₀₁ hstruct s₁ : ℝ) := ht₁.symm

/-- Rewriting the goal tail-set into the `b < t` form. -/
private theorem tail_coord_set (b : ℝ) :
    ({t : ORI | (t : ℝ) ∈ Set.Ioo b 1} : Set ORI) = {t : ORI | b < (t : ℝ)} := by
  ext t
  constructor
  · intro ht
    exact ht.1
  · intro ht
    exact ⟨ht, t.2.2⟩

end Branch

/--
The main theorem (right end of `P` is attracted by the puncture point).
-/
theorem boundary_point_attracts_right_end {X : Type*} [TopologicalSpace X] [T2Space X]
    {P W : Set X} (e : ({t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1}) ≃ₜ {x : X // x ∈ P})
    (ψ : ({t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1}) ≃ₜ {x : X // x ∈ W})
    {c₀ : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hstruct : P ∩ W = W \ {((ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : {x : X // x ∈ W}) : X)}) :
    ∀ b : ℝ, 0 < b → b < 1 →
      ((ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : {x : X // x ∈ W}) : X) ∈ closure
        ((fun t : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} =>
          ((e t : {x : X // x ∈ P}) : X)) ''
          {t : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} | (t : ℝ) ∈ Set.Ioo b 1}) := by
  classical
  intro b hb0 hb1
  have hz_out : zval ψ hc₀₀ hc₀₁ ∉ Set.range (E e) := by
    rw [E_range e]
    exact (z_notin_P ψ hc₀₀ hc₀₁ hstruct)
  -- left branch dichotomy
  have hdichL := arc_branch_left_dichotomy (a := E e) (ha_cont := E_cont e)
    (c₀ := c₀) (hc₀₀ := hc₀₀) (hc₀₁ := hc₀₁) (z := zval ψ hc₀₀ hc₀₁) (hz_out := hz_out)
    (f := fL e ψ hc₀₀ hc₀₁ hstruct) (hf_cont := fL_cont e ψ hc₀₀ hc₀₁ hstruct)
    (hf_inj := fL_inj e ψ hc₀₀ hc₀₁ hstruct)
    (hzcl := fun u => z_mem_closure_left_coord e ψ hc₀₀ hc₀₁ hstruct u)
  -- right branch dichotomy
  have hdichR := arc_branch_right_dichotomy (a := E e) (ha_cont := E_cont e)
    (c₀ := c₀) (hc₀₀ := hc₀₀) (hc₀₁ := hc₀₁) (z := zval ψ hc₀₀ hc₀₁) (hz_out := hz_out)
    (f := fR e ψ hc₀₀ hc₀₁ hstruct) (hf_cont := fR_cont e ψ hc₀₀ hc₀₁ hstruct)
    (hf_inj := fR_inj e ψ hc₀₀ hc₀₁ hstruct)
    (hzcl := fun u => z_mem_closure_right_coord e ψ hc₀₀ hc₀₁ hstruct u)
  rcases hdichL with hAttL | hZeroL
  · -- right-end attraction from the left branch
    rw [tail_coord_set b]
    have hfun : (fun t : ORI => ((e t : {x : X // x ∈ P}) : X)) = E e := by rfl
    rw [hfun]
    exact hAttL b hb0 hb1
  · rcases hdichR with hAttR | hZeroR
    · -- right-end attraction from the right branch
      rw [tail_coord_set b]
      have hfun : (fun t : ORI => ((e t : {x : X // x ∈ P}) : X)) = E e := by rfl
      rw [hfun]
      exact hAttR b hb0 hb1
    · -- both branches run to the 0-end: disjointness contradiction
      rcases hZeroL with ⟨δ₁, hδ₁₀, hzero₁⟩
      rcases hZeroR with ⟨δ₂, hδ₂₀, hzero₂⟩
      exact False.elim (zero_ranges_contradiction e ψ hc₀₀ hc₀₁ hstruct
        hδ₁₀ hzero₁ hδ₂₀ hzero₂)

end Commons.Topology.OneManifold
