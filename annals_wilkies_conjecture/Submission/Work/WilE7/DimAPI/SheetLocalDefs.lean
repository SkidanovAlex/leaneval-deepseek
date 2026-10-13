/-
  WilE7 / DimAPI (`Work.WilE7.DimAPI.SheetLocalDefs`): vocabulary for the sheet lemma
  `sheets_of_localGraph`.

  Given `X ⊆ ℝ^{p+q}` and a base set `C ⊆ ℝ^p`, the sheet space is the part of `X` lying over
  `C` (`SheetTot X C`), and the sheet projection `SheetP X C : SheetT X C → C` is the restriction
  of `projFirst p q`.  The lemma `sheets_of_localGraph` says that, under a local-graph hypothesis
  on `X` over `C`, the fibres of this projection are of constant cardinality `k` and are covered
  by `k` continuous sheets.

  The route: the local-graph hypothesis makes `SheetP X C` a local homeomorphism
  (`SheetP_isLocalHomeomorphOn`, delegated), the boundedness of `X` and the closedness of `X`
  over `C` inside `closure X` make it a closed map (`SheetP_isClosedMap`, delegated); Mathlib's
  `IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn` then makes it a covering map.  A cell is
  contractible (`Work.WilE7.isCellContractible`), so the fibres can be transported
  (`Work.WilE7.transportMap`) to the fibre over the base point of the contraction, which produces
  the global continuous sheets.

  This file contains the vocabulary together with the elementary point-set lemmas about it
  (fibre finiteness and fibre cardinality, the contraction on the subtype `C`, and the projection
  of `C` inside the total space), all proved without `sorry`.
-/
import Mathlib
import Submission.Work.WilE7.projFirst_fiberClosure
import Submission.Work.WilE7.sheetDomain_open
import Submission.Work.WilE7.isCellContractible

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
namespace Work.WilE7.DimAPI
open WilkiesDesign WilkiesDesign.E

/-! ## The sheet space and its projection -/

/-- The part of `X` lying over the base set `C`. -/
def SheetTot {p q : ℕ} (X : Set (Fin (p + q) → ℝ)) (C : Set (Fin p → ℝ)) :
    Set (Fin (p + q) → ℝ) :=
  X ∩ {z | projFirst p q z ∈ C}

theorem mem_SheetTot {p q : ℕ} {X : Set (Fin (p + q) → ℝ)} {C : Set (Fin p → ℝ)}
    {z : Fin (p + q) → ℝ} : z ∈ SheetTot X C ↔ z ∈ X ∧ projFirst p q z ∈ C := Iff.rfl

/-- The total space of the sheet projection over `C`. -/
abbrev SheetT {p q : ℕ} (X : Set (Fin (p + q) → ℝ)) (C : Set (Fin p → ℝ)) : Type :=
  {z : Fin (p + q) → ℝ // z ∈ SheetTot X C}

/-- The sheet projection, onto the base set `C`. -/
def SheetP {p q : ℕ} (X : Set (Fin (p + q) → ℝ)) (C : Set (Fin p → ℝ)) : SheetT X C → C :=
  fun w => ⟨projFirst p q w.1, w.2.2⟩

@[simp] theorem SheetP_val {p q : ℕ} {X : Set (Fin (p + q) → ℝ)} {C : Set (Fin p → ℝ)}
    (w : SheetT X C) : (SheetP X C w).1 = projFirst p q w.1 := rfl

theorem SheetT_mem_X {p q : ℕ} {X : Set (Fin (p + q) → ℝ)} {C : Set (Fin p → ℝ)}
    (w : SheetT X C) : w.1 ∈ X := w.2.1

theorem SheetT_mem_C {p q : ℕ} {X : Set (Fin (p + q) → ℝ)} {C : Set (Fin p → ℝ)}
    (w : SheetT X C) : projFirst p q w.1 ∈ C := w.2.2

/-- A point of the total space is the gluing of its two projections. -/
theorem SheetT_append_proj {p q : ℕ} {X : Set (Fin (p + q) → ℝ)} {C : Set (Fin p → ℝ)}
    (w : SheetT X C) : Fin.append (projFirst p q w.1) (projSnd p q w.1) = w.1 :=
  append_projFirst_projSnd w.1

/-- The projection is continuous. -/
theorem SheetP_continuous {p q : ℕ} (X : Set (Fin (p + q) → ℝ)) (C : Set (Fin p → ℝ)) :
    Continuous (SheetP X C) := by
  refine Continuous.subtype_mk ?_ (fun w => w.2.2)
  exact continuous_pi fun i => (continuous_apply (Fin.castAdd q i)).comp continuous_subtype_val

/-- The sheet projection is onto `C` as soon as `C` is contained in the projection of `X`. -/
theorem SheetP_surjective {p q : ℕ} {X : Set (Fin (p + q) → ℝ)} {C : Set (Fin p → ℝ)}
    (hCsub : C ⊆ projFirst p q '' X) : Function.Surjective (SheetP X C) := by
  intro x
  obtain ⟨z, hzX, hzπ⟩ := hCsub x.2
  exact ⟨⟨z, hzX, by show projFirst p q z ∈ C; rw [hzπ]; exact x.2⟩, Subtype.ext hzπ⟩

/-! ## The fibres of the sheet projection -/

/-- The map `w ↦ projSnd p q w.1` is injective on the fibre of the sheet projection over `x`. -/
theorem SheetP_fiber_injOn {p q : ℕ} (X : Set (Fin (p + q) → ℝ)) (C : Set (Fin p → ℝ))
    (x : C) : Set.InjOn (fun w : SheetT X C => projSnd p q w.1) ((SheetP X C) ⁻¹' {x}) := by
  intro w hw w' hw' h
  have h' : projSnd p q w.1 = projSnd p q w'.1 := h
  have hwπ : projFirst p q w.1 = x.1 := congrArg Subtype.val hw
  have hw'π : projFirst p q w'.1 = x.1 := congrArg Subtype.val hw'
  refine Subtype.ext ?_
  calc w.1 = Fin.append (projFirst p q w.1) (projSnd p q w.1) :=
        (append_projFirst_projSnd w.1).symm
    _ = Fin.append x.1 (projSnd p q w.1) := by rw [hwπ]
    _ = Fin.append x.1 (projSnd p q w'.1) := by rw [h']
    _ = Fin.append (projFirst p q w'.1) (projSnd p q w'.1) := by rw [hw'π]
    _ = w'.1 := append_projFirst_projSnd w'.1

/-- The fibre of the sheet projection over `x` is, through `projSnd`, the fibre of `X` over `x`. -/
theorem SheetP_fiber_image {p q : ℕ} (X : Set (Fin (p + q) → ℝ)) (C : Set (Fin p → ℝ))
    (x : C) :
    (fun w : SheetT X C => projSnd p q w.1) '' ((SheetP X C) ⁻¹' {x}) = fiber X x.1 := by
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    show Fin.append x.1 (projSnd p q w.1) ∈ X
    rw [← congrArg Subtype.val hw, SheetP_val, append_projFirst_projSnd]
    exact w.2.1
  · intro hy
    refine ⟨⟨Fin.append x.1 y, hy, ?_⟩, ?_, projSnd_append x.1 y⟩
    · show projFirst p q (Fin.append x.1 y) ∈ C
      rw [projFirst_append]; exact x.2
    · exact Subtype.ext (by rw [SheetP_val, projFirst_append])

/-- Finiteness of the fibres of `X` over `C` gives finiteness of the fibres of the projection. -/
theorem SheetP_fiber_finite {p q : ℕ} {X : Set (Fin (p + q) → ℝ)} {C : Set (Fin p → ℝ)}
    (hfin : ∀ x ∈ C, (fiber X x).Finite) (x : C) : ((SheetP X C) ⁻¹' {x}).Finite :=
  Set.Finite.of_finite_image (by rw [SheetP_fiber_image X C x]; exact hfin x.1 x.2)
    (SheetP_fiber_injOn X C x)

/-- The cardinality of the fibre of the projection over `x` is that of the fibre of `X`. -/
theorem SheetP_fiber_ncard {p q : ℕ} {X : Set (Fin (p + q) → ℝ)} {C : Set (Fin p → ℝ)}
    (x : C) : ((SheetP X C) ⁻¹' {x}).ncard = (fiber X x.1).ncard := by
  rw [← SheetP_fiber_image X C x]
  exact (SheetP_fiber_injOn X C x).ncard_image.symm

/-! ## A contraction on the subtype `C` -/

/-- A contraction of `C ⊆ ℝ^p` to a point of itself, as supplied by
`Work.WilE7.isCellContractible`, is the same thing as a map `C × ℝ → C` which is continuous on
`univ ×ˢ Icc 0 1`, is the constant `c₀` at `t = 0` and the identity at `t = 1`.  This is the form
in which the covering-space argument (`covering_sections`) consumes it. -/
theorem hasContraction_subtype {p : ℕ} {C : Set (Fin p → ℝ)} {c₀ : Fin p → ℝ} (hc₀ : c₀ ∈ C)
    {K : (Fin p → ℝ) × ℝ → (Fin p → ℝ)}
    (hKcont : ContinuousOn K (C ×ˢ Set.Icc (0 : ℝ) 1))
    (hK0 : ∀ x ∈ C, K (x, 0) = c₀) (hK1 : ∀ x ∈ C, K (x, 1) = x)
    (hKmem : ∀ x ∈ C, ∀ t ∈ Set.Icc (0 : ℝ) 1, K (x, t) ∈ C) :
    ∃ K' : C → unitInterval → C, Continuous (Function.uncurry K') ∧
      (∀ x : C, K' x 0 = ⟨c₀, hc₀⟩) ∧ (∀ x : C, K' x 1 = x) := by
  classical
  refine ⟨fun x t => ⟨K (x.1, (t : ℝ)), hKmem x.1 x.2 (t : ℝ) t.2⟩, ?_, ?_, ?_⟩
  · show Continuous fun q : C × unitInterval =>
      (⟨K (q.1.1, (q.2 : ℝ)), hKmem q.1.1 q.1.2 (q.2 : ℝ) q.2.2⟩ : C)
    have hpair : Continuous fun q : C × unitInterval => (q.1.1, (q.2 : ℝ)) :=
      (Continuous.comp continuous_subtype_val continuous_fst).prodMk
        (Continuous.comp continuous_subtype_val continuous_snd)
    have hK : Continuous fun q : C × unitInterval => K (q.1.1, (q.2 : ℝ)) := by
      have h : ContinuousOn (fun q : C × unitInterval => K (q.1.1, (q.2 : ℝ))) Set.univ :=
        hKcont.comp (s := Set.univ) hpair.continuousOn (fun q _ => ⟨q.1.2, q.2.2⟩)
      exact continuousOn_univ.mp h
    exact hK.subtype_mk fun q => hKmem q.1.1 q.1.2 (q.2 : ℝ) q.2.2
  · -- at `t = 0`
    intro x
    exact Subtype.ext (hK0 x.1 x.2)
  · -- at `t = 1`
    intro x
    exact Subtype.ext (hK1 x.1 x.2)

end Work.WilE7.DimAPI
