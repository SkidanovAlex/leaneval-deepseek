/-
  WilE7 (`Work.WilE7.SheetDefs`): the vocabulary of the sheet assembly.

  `SheetSpace S C = S.X.set ∩ π⁻¹'C` is the *sheet domain*: the part of the stratum lying over the
  base set `C`.  Its total space, as a type, is `SheetE S C`, and the projection to the base is
  `SheetProj`.  The single real-analysis input of the sheet argument is `sheetLocalPatch`: at every
  point `v` of the sheet domain, the stratum is *locally the graph* of a continuous map `y` over an
  open neighbourhood `U` of the base point, and every point of the stratum in the open set `V` whose
  base lies in `U` is that graph point.  It is `Work.WilE7.stratGraph` (the implicit-function form
  of `Good` with `S.j = q`) combined with the ambient locality hypothesis `hloc`, plus continuity of
  the graph map (from `Work.WilE7.sheetDomain_open`).
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.stratGraph
import Submission.Work.WilE7.sheetDomain_open
import Submission.Work.WilE7.sheetDomain_closedIn
import Submission.Work.WilE7.isCell_localPreconnected
import Submission.Work.WilE7.cells
import Submission.Work.WilE7.sheetCount_le_fibre

set_option autoImplicit false
noncomputable section
open Classical Filter Topology

namespace Work.WilE7

open WilkiesDesign WilkiesDesign.E

/-! ## The sheet domain, its total space and its projection -/

/-- The sheet domain of the stratum `S` over the base set `C`: the points of `S.X.set` whose base
projection lies in `C`. -/
def SheetSpace {p q : ℕ} (S : Stratum p q) (C : Set (Fin p → ℝ)) : Set (Fin (p + q) → ℝ) :=
  S.X.set ∩ {w | projFirst p q w ∈ C}

theorem mem_SheetSpace {p q : ℕ} {S : Stratum p q} {C : Set (Fin p → ℝ)}
    {w : Fin (p + q) → ℝ} : w ∈ SheetSpace S C ↔ w ∈ S.X.set ∧ projFirst p q w ∈ C := Iff.rfl

/-- The total space of the sheet fibration, as a type. -/
abbrev SheetE {p q : ℕ} (S : Stratum p q) (C : Set (Fin p → ℝ)) : Type :=
  {w : Fin (p + q) → ℝ // w ∈ SheetSpace S C}

/-- The projection of the sheet space onto the base set. -/
def SheetProj {p q : ℕ} {S : Stratum p q} {C : Set (Fin p → ℝ)} (w : SheetE S C) : C :=
  ⟨projFirst p q w.1, w.2.2⟩

@[simp] theorem SheetProj_val {p q : ℕ} {S : Stratum p q} {C : Set (Fin p → ℝ)}
    (w : SheetE S C) : (SheetProj w).1 = projFirst p q w.1 := rfl

theorem SheetProj_continuous {p q : ℕ} {S : Stratum p q} {C : Set (Fin p → ℝ)} :
    Continuous (SheetProj (S := S) (C := C)) :=
  Continuous.subtype_mk (f := fun w : SheetE S C => projFirst p q w.1)
    (continuous_pi fun i => (continuous_apply (Fin.castAdd q i)).comp continuous_subtype_val)
    (fun x => x.2.2)

/-- The total space sits inside the stratum. -/
theorem sheetE_mem_stratum {p q : ℕ} {S : Stratum p q} {C : Set (Fin p → ℝ)}
    (w : SheetE S C) : w.1 ∈ S.X.set := w.2.1

/-- A point of the total space is the gluing of its two projections. -/
theorem sheetE_append_proj {p q : ℕ} {S : Stratum p q} {C : Set (Fin p → ℝ)}
    (w : SheetE S C) : Fin.append (projFirst p q w.1) (projSnd p q w.1) = w.1 := append_proj w.1

/-- The point of the total space over `x` with fibre coordinate `y`. -/
def sheetPoint {p q : ℕ} {S : Stratum p q} {C : Set (Fin p → ℝ)} (x : C) (y : Fin q → ℝ)
    (h : Fin.append x.1 y ∈ S.X.set) : SheetE S C :=
  ⟨Fin.append x.1 y, h, by show projFirst p q (Fin.append x.1 y) ∈ C; rw [projFirst_append]; exact x.2⟩

@[simp] theorem SheetProj_sheetPoint {p q : ℕ} {S : Stratum p q} {C : Set (Fin p → ℝ)}
    (x : C) (y : Fin q → ℝ) (h : Fin.append x.1 y ∈ S.X.set) :
    SheetProj (sheetPoint x y h) = x := by
  refine Subtype.ext ?_
  show projFirst p q (Fin.append x.1 y) = x.1
  rw [projFirst_append]

theorem sheetPoint_injective {p q : ℕ} {S : Stratum p q} {C : Set (Fin p → ℝ)} (x : C) :
    Function.Injective fun y : {y : Fin q → ℝ // Fin.append x.1 y ∈ S.X.set} =>
      sheetPoint x y.1 y.2 := by
  intro y y' hy
  have h : Fin.append x.1 y.1 = Fin.append x.1 y'.1 := congrArg Subtype.val hy
  have := congrFun h
  refine Subtype.ext (funext fun i => ?_)
  simpa using congrFun h (Fin.natAdd p i)


/-! ## Fibres of the sheet fibration -/

/-- `projSnd p q (Fin.append x v) = v`. -/
theorem projSnd_append {p q : ℕ} (x : Fin p → ℝ) (v : Fin q → ℝ) :
    projSnd p q (Fin.append x v) = v := by
  funext i
  simp [projSnd]

/-- The fibre of the stratum over `x` is the image of the total space's fibre over `x` under
`projSnd`. -/
theorem sheetFiber_image {p q : ℕ} {S : Stratum p q} {C : Set (Fin p → ℝ)} (x : C) :
    projSnd p q '' (SheetSpace S C ∩ {w | projFirst p q w = x.1}) = fiber S.X.set x.1 := by
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    show Fin.append x.1 (projSnd p q w) ∈ S.X.set
    rw [← hw.2, append_proj]
    exact hw.1.1
  · intro hy
    refine ⟨Fin.append x.1 y, ⟨⟨hy, ?_⟩, ?_⟩, ?_⟩
    · show projFirst p q (Fin.append x.1 y) ∈ C
      rw [projFirst_append]; exact x.2
    · show projFirst p q (Fin.append x.1 y) = x.1
      rw [projFirst_append]
    · show projSnd p q (Fin.append x.1 y) = y
      rw [projSnd_append]

/-- The image of the fibre of the total space over `x` under `Subtype.val`. -/
theorem sheetFiber_val_image {p q : ℕ} {S : Stratum p q} {C : Set (Fin p → ℝ)} (x : C) :
    Subtype.val '' (SheetProj (S := S) (C := C) ⁻¹' {x}) =
      SheetSpace S C ∩ {w | projFirst p q w = x.1} := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w.2, ?_⟩
    show projFirst p q w.1 = x.1
    have h : SheetProj (S := S) (C := C) w = x := hw
    rw [← SheetProj_val]
    exact congrArg Subtype.val h
  · rintro ⟨hvS, hvπ⟩
    have hvπ' : projFirst p q v = x.1 := hvπ
    have hvC : projFirst p q v ∈ C := hvπ' ▸ x.2
    refine ⟨⟨v, hvS.1, hvC⟩, ?_, rfl⟩
    refine Subtype.ext ?_
    show projFirst p q v = x.1
    exact hvπ'

/-- The fibre of the total space over a base point is finite, since the stratum's fibres are. -/
theorem sheetFiber_finite {p q : ℕ} {S : Stratum p q} {C : Set (Fin p → ℝ)}
    (hfin : ∀ x : Fin p → ℝ, (fiber S.X.set x).Finite) (x : C) :
    (SheetProj (S := S) (C := C) ⁻¹' {x}).Finite := by
  refine Set.Finite.of_finite_image (f := Subtype.val) ?_ Subtype.val_injective.injOn
  rw [sheetFiber_val_image]
  refine Set.Finite.of_finite_image (f := projSnd p q) ?_ ?_
  · rw [sheetFiber_image]; exact hfin x.1
  · intro a ha b hb hab
    rw [← append_proj a, ← append_proj b, ha.2, hb.2, hab]

/-! ## The local patch lemma -/

/-- **The local patch.** At a point `v` of the sheet domain, the stratum is locally the graph of a
continuous map `y` over an open neighbourhood `U` of the base point `π v`; the graph points over
`U ∩ C` lie in `S.X.set`, and *every* point of the stratum in the open set `V` over `U` is that
graph point.  (The last clause is the uniqueness of the implicit-function graph.) -/
theorem sheetLocalPatch {p q : ℕ} (S : Stratum p q) (hGood : S.Good) (hj : S.j = q)
    (C : Set (Fin p → ℝ))
    (hloc : ∀ z ∈ S.X.set, projFirst p q z ∈ C →
      ∀ᶠ z' in 𝓝 z, (∀ a : Fin S.j, eaEval S.X.c (S.h a) z' = 0) → z' ∈ S.X.set)
    (v : Fin (p + q) → ℝ) (hv : v ∈ S.X.set) (hvC : projFirst p q v ∈ C) :
    ∃ (U : Set (Fin p → ℝ)) (y : (Fin p → ℝ) → (Fin q → ℝ)) (V : Set (Fin (p + q) → ℝ)),
      IsOpen U ∧ projFirst p q v ∈ U ∧ IsOpen V ∧ v ∈ V ∧ ContinuousOn y U ∧
      y (projFirst p q v) = projSnd p q v ∧
      (∀ x ∈ U, Fin.append x (y x) ∈ V) ∧
      (∀ x ∈ U ∩ C, Fin.append x (y x) ∈ S.X.set) ∧
      (∀ w ∈ V, w ∈ S.X.set → projFirst p q w ∈ U → projSnd p q w = y (projFirst p q w)) := by
  obtain ⟨U₀, y, W, hU₀o, hxU₀, hWo, hvW, hy0, hycont, hysol, hyuniq⟩ :=
    stratGraph S hGood hj v hv
  obtain ⟨N, hNsub, hNopen, hvN⟩ := mem_nhds_iff.mp (hloc v hv hvC)
  let g : (Fin p → ℝ) → (Fin (p + q) → ℝ) := fun x => Fin.append x (y x)
  let U : Set (Fin p → ℝ) := (U₀ ∩ g ⁻¹' N) ∩ (U₀ ∩ g ⁻¹' W)
  have hgr : ContinuousOn g U₀ := continuousOn_append hycont
  have hUo : IsOpen U :=
    (hgr.isOpen_inter_preimage hU₀o hNopen).inter (hgr.isOpen_inter_preimage hU₀o hWo)
  have hgv : g (projFirst p q v) = v := by
    show Fin.append (projFirst p q v) (y (projFirst p q v)) = v
    rw [hy0, append_proj]
  have hxU : projFirst p q v ∈ U := by
    refine ⟨⟨hxU₀, ?_⟩, hxU₀, ?_⟩
    · show g (projFirst p q v) ∈ N
      rw [hgv]; exact hvN
    · show g (projFirst p q v) ∈ W
      rw [hgv]; exact hvW
  have hcont : ContinuousOn y U := hycont.mono (fun x hx => hx.1.1)
  have h1 : ∀ x ∈ U, g x ∈ W := fun x hx => hx.2.2
  have h2 : ∀ x ∈ U ∩ C, g x ∈ S.X.set := by
    intro x hx
    exact hNsub hx.1.1.2 (hysol x hx.1.1.1)
  have h3 : ∀ w ∈ W, w ∈ S.X.set → projFirst p q w ∈ U →
      projSnd p q w = y (projFirst p q w) :=
    fun w hw hwS hwU => hyuniq w hw hwS hwU.1.1
  refine ⟨U, y, W, hUo, hxU, hWo, hvW, ?_, hy0, ?_, ?_, h3⟩
  · show ContinuousOn y U; exact hcont
  · show ∀ x ∈ U, g x ∈ W; exact h1
  · show ∀ x ∈ U ∩ C, g x ∈ S.X.set; exact h2

end Work.WilE7
