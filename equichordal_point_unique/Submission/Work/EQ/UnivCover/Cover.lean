import Submission.Work.EQ.UnivCover.Defs
import Submission.Work.EQ.UnivCover.Sheet
import Submission.Work.EQ.UnivCover.Topology

/-!
# The universal cover is a covering space

The projection `UC.proj : UC x₀ → X` is a covering map, with evenly covered neighbourhoods given by
the disc-like sets.
-/

set_option autoImplicit false
open _root_.Topology
open scoped Topology
open Work.EQ.UnivCover

namespace Work.EQ.UnivCover

variable {X : Type*} [TopologicalSpace X] {x₀ : X}

section Sect

/-- A chosen family of paths inside a disc-like set. -/
noncomputable abbrev discPath (V : Set X) (hV : IsDiscLike V) (a : X) (ha : a ∈ V) (b : X)
    (hb : b ∈ V) : Path a b :=
  (hV.path_connected ha hb).choose

theorem discPath_mem (V : Set X) (hV : IsDiscLike V) (a : X) (ha : a ∈ V) (b : X) (hb : b ∈ V) :
    ∀ t, discPath V hV a ha b hb t ∈ V :=
  (hV.path_connected ha hb).choose_spec

/-- The point of the sheet of `e` over `V` sitting over `y`. -/
noncomputable abbrev sectOf (V : Set X) (hV : IsDiscLike V) (e : UC x₀) (he : e.pt ∈ V)
    (y : X) (hy : y ∈ V) : UC x₀ :=
  ⟨y, e.cls.trans (Path.Homotopic.Quotient.mk (discPath V hV e.pt he y hy))⟩

@[simp] theorem sectOf_pt (V : Set X) (hV : IsDiscLike V) (e : UC x₀) (he : e.pt ∈ V)
    (y : X) (hy : y ∈ V) : (sectOf V hV e he y hy).pt = y := rfl

theorem sectOf_mem (V : Set X) (hV : IsDiscLike V) (e : UC x₀) (he : e.pt ∈ V)
    (y : X) (hy : y ∈ V) : sectOf V hV e he y hy ∈ UC.sheet e V :=
  ⟨hy, discPath V hV e.pt he y hy, discPath_mem V hV e.pt he y hy, rfl⟩

/-- **Coherence of the sections**: the point of the sheet of `e` over the smaller disc-like set `W`
sitting over `y'` lies in the sheet of the point over `y`. -/
theorem sectOf_mem_sheet (V W : Set X) (hV : IsDiscLike V) (hW : IsDiscLike W) (hWV : W ⊆ V)
    (e : UC x₀) (he : e.pt ∈ V) {y y' : X} (hy : y ∈ V) (hyW : y ∈ W) (hy' : y' ∈ W) :
    sectOf W hW (sectOf V hV e he y hy) hyW y' hy'
      ∈ UC.sheet (sectOf V hV e he y hy) W := by
  obtain ⟨η, hη⟩ := hW.path_connected hyW hy'
  have hclass : Path.Homotopic.Quotient.mk
        (discPath W hW (sectOf V hV e he y hy).pt hyW y' hy')
      = Path.Homotopic.Quotient.mk η :=
    mk_eq_mk_of_isDiscLike hW _ η (discPath_mem W hW _ hyW y' hy') hη
  refine ⟨hy', η, hη, ?_⟩
  show (sectOf V hV e he y hy).cls.trans (Path.Homotopic.Quotient.mk
      (discPath W hW (sectOf V hV e he y hy).pt hyW y' hy'))
    = (sectOf V hV e he y hy).cls.trans (Path.Homotopic.Quotient.mk η)
  rw [hclass]

/-- Restricting the section over `V` to a smaller disc-like set `W` agrees with the section of the
restricted point. -/
theorem sectOf_eq_sectOf (V W : Set X) (hV : IsDiscLike V) (hW : IsDiscLike W) (hWV : W ⊆ V)
    (e : UC x₀) (he : e.pt ∈ V) {y y' : X} (hy : y ∈ V) (hyW : y ∈ W) (hy' : y' ∈ W) :
    sectOf W hW (sectOf V hV e he y hy) hyW y' hy' = sectOf V hV e he y' (hWV hy') := by
  have h₁ : sectOf W hW (sectOf V hV e he y hy) hyW y' hy' ∈ UC.sheet e V :=
    UC_sheet_trans (sectOf_mem V hV e he y hy)
      (sectOf_mem_sheet V W hV hW hWV e he hy hyW hy') hWV
  have h₂ : sectOf V hV e he y' (hWV hy') ∈ UC.sheet e V := sectOf_mem V hV e he y' (hWV hy')
  exact (UC_sheet_unique hV).1 h₁ h₂ rfl

end Sect

section Discrete

/-- In a discrete codomain, continuity is fibrewise openness. -/
theorem continuous_of_discrete_codomain {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [DiscreteTopology β] {f : α → β} (h : ∀ b, IsOpen (f ⁻¹' {b})) : Continuous f := by
  rw [continuous_def]
  intro U _
  have hU : U = ⋃ b : β, ⋃ (_ : b ∈ U), ({b} : Set β) := by
    ext b; simp only [Set.mem_iUnion, Set.mem_singleton_iff]; exact ⟨fun hb => ⟨b, hb, rfl⟩,
      fun ⟨b', hb', h⟩ => h ▸ hb'⟩
  rw [hU]
  simp only [Set.preimage_iUnion]
  exact isOpen_iUnion fun b => isOpen_iUnion fun _ => h b

/-- The fibres of the projection are discrete. -/
theorem UC_discreteTopology_fiber (hB : HasDiscBasis X) (x : X) :
    DiscreteTopology (UC.proj (x₀ := x₀) ⁻¹' ({x} : Set X)) := by
  obtain ⟨V, hV, hxV, -⟩ := hB x Set.univ isOpen_univ (Set.mem_univ x)
  have hmem : ∀ e : UC.proj (x₀ := x₀) ⁻¹' ({x} : Set X), e.1.pt ∈ V := by
    intro e
    have he : UC.proj (x₀ := x₀) e.1 = x := Set.mem_singleton_iff.mp e.2
    show UC.proj (x₀ := x₀) e.1 ∈ V
    rw [he]
    exact hxV
  have hpt : ∀ e e' : UC.proj (x₀ := x₀) ⁻¹' ({x} : Set X), e.1.pt = e'.1.pt := by
    intro e e'
    have h₁ : UC.proj (x₀ := x₀) e.1 = x := Set.mem_singleton_iff.mp e.2
    have h₂ : UC.proj (x₀ := x₀) e'.1 = x := Set.mem_singleton_iff.mp e'.2
    show UC.proj (x₀ := x₀) e.1 = UC.proj (x₀ := x₀) e'.1
    rw [h₁, h₂]
  rw [discreteTopology_iff_isOpen_singleton]
  intro e
  rw [isOpen_induced_iff]
  refine ⟨UC.sheet e.1 V, UC_isOpen_sheet hB hV (hmem e), ?_⟩
  ext e'
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h
    have h1 : e'.1 ∈ UC.sheet e.1 V := h
    have h2 : e.1 ∈ UC.sheet e.1 V := UC.self_mem_sheet (hmem e)
    have h3 : e'.1.pt = e.1.pt := hpt e' e
    exact Subtype.ext ((UC_sheet_unique hV).1 h1 h2 h3)
  · intro h
    rw [h]
    exact UC.self_mem_sheet (hmem e)

end Discrete

section Covering

/-- **The universal cover is a covering space.** -/
theorem UC_isCoveringMap_proj [T2Space X] (hB : HasDiscBasis X) :
    IsCoveringMap (UC.proj (x₀ := x₀)) := by
  intro x
  obtain ⟨V, hV, hxV, -⟩ := hB x Set.univ isOpen_univ (Set.mem_univ x)
  haveI : DiscreteTopology (UC.proj (x₀ := x₀) ⁻¹' ({x} : Set X)) :=
    UC_discreteTopology_fiber hB x
  have hfibV : ∀ e : UC.proj (x₀ := x₀) ⁻¹' ({x} : Set X), e.1.pt ∈ V := by
    intro e
    have he : UC.proj (x₀ := x₀) e.1 = x := Set.mem_singleton_iff.mp e.2
    show UC.proj (x₀ := x₀) e.1 ∈ V
    rw [he]
    exact hxV
  have hfibeq : ∀ e₁ e₂ : UC.proj (x₀ := x₀) ⁻¹' ({x} : Set X), e₁.1.pt = e₂.1.pt := by
    intro e₁ e₂
    have h₁ : UC.proj (x₀ := x₀) e₁.1 = x := Set.mem_singleton_iff.mp e₁.2
    have h₂ : UC.proj (x₀ := x₀) e₂.1 = x := Set.mem_singleton_iff.mp e₂.2
    show UC.proj (x₀ := x₀) e₁.1 = UC.proj (x₀ := x₀) e₂.1
    rw [h₁, h₂]
  -- the index of a point over `V`
  have hIdx : ∀ e' : UC.proj (x₀ := x₀) ⁻¹' V,
      ∃ e : UC.proj (x₀ := x₀) ⁻¹' ({x} : Set X), e'.1 ∈ UC.sheet e.1 V := by
    intro e'
    obtain ⟨δ, hδ⟩ := hV.path_connected hxV e'.2
    refine ⟨⟨⟨x, e'.1.cls.trans (Path.Homotopic.Quotient.mk δ).symm⟩,
      Set.mem_singleton_iff.mpr rfl⟩, ?_⟩
    refine ⟨e'.2, δ, hδ, ?_⟩
    simp only [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
      Path.Homotopic.Quotient.trans_refl]
  let idx : UC.proj (x₀ := x₀) ⁻¹' V → UC.proj (x₀ := x₀) ⁻¹' ({x} : Set X) :=
    fun e' => (hIdx e').choose
  have idx_spec : ∀ e', e'.1 ∈ UC.sheet (idx e').1 V := fun e' => (hIdx e').choose_spec
  -- the two directions of the trivialisation
  let Hf : UC.proj (x₀ := x₀) ⁻¹' V → V × (UC.proj (x₀ := x₀) ⁻¹' ({x} : Set X)) :=
    fun e' => (⟨e'.1.pt, e'.2⟩, idx e')
  let Hg : V × (UC.proj (x₀ := x₀) ⁻¹' ({x} : Set X)) → UC.proj (x₀ := x₀) ⁻¹' V :=
    fun p => ⟨sectOf V hV p.2.1 (hfibV p.2) p.1.1 p.1.2, by
      show p.1.1 ∈ V
      exact p.1.2⟩
  have hHfHg : ∀ p, Hf (Hg p) = p := by
    rintro ⟨⟨y, hy⟩, e⟩
    have hidx : idx (Hg (⟨y, hy⟩, e)) = e :=
      Subtype.ext ((UC_sheet_unique hV).2 (idx_spec _)
        (sectOf_mem V hV e.1 (hfibV e) y hy) (hfibeq (idx (Hg (⟨y, hy⟩, e))) e))
    exact Prod.ext (Subtype.ext (sectOf_pt V hV e.1 (hfibV e) y hy)) hidx
  have hHgHf : ∀ e' : UC.proj (x₀ := x₀) ⁻¹' V, Hg (Hf e') = e' := by
    intro e'
    refine Subtype.ext ((UC_sheet_unique hV).1
      (sectOf_mem V hV (idx e').1 (hfibV (idx e')) e'.1.pt e'.2) (idx_spec e') rfl)
  have hHf_cont : Continuous Hf := by
    have h1 : Continuous fun e' : UC.proj (x₀ := x₀) ⁻¹' V => (⟨e'.1.pt, e'.2⟩ : V) :=
      Continuous.subtype_mk ((UC_continuous_proj hB).comp continuous_subtype_val) _
    have h2 : Continuous idx := by
      refine continuous_of_discrete_codomain fun b => ?_
      have hset : idx ⁻¹' {b} = Subtype.val ⁻¹' (UC.sheet b.1 V) := by
        ext e'
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        exact ⟨fun h => h ▸ idx_spec e', fun h => Subtype.ext ((UC_sheet_unique hV).2
          (idx_spec e') h (hfibeq (idx e') b))⟩
      rw [hset]
      exact continuous_subtype_val.isOpen_preimage _ (UC_isOpen_sheet hB hV (hfibV b))
    show Continuous fun e' : UC.proj (x₀ := x₀) ⁻¹' V => ((⟨e'.1.pt, e'.2⟩ : V), idx e')
    exact h1.prodMk h2
  have hHg_cont : Continuous Hg := by
    rw [(isTopologicalBasis_subtype (UC_isTopologicalBasis_basis (x₀ := x₀) hB) _).continuous_iff]
    rintro S ⟨S₀, hS₀, rfl⟩
    obtain ⟨e₀, V₀, hV₀, he₀V₀, rfl⟩ := hS₀
    rw [isOpen_iff_mem_nhds]
    rintro ⟨⟨y, hy⟩, e⟩ hp
    have hp' : sectOf V hV e.1 (hfibV e) y hy ∈ UC.sheet e₀ V₀ := hp
    obtain ⟨W, hW, hyW, hWVWV₀⟩ := hB y (V ∩ V₀) (hV.isOpen.inter hV₀.isOpen) ⟨hy, hp'.1⟩
    have hWV' : W ⊆ V := fun a ha => (hWVWV₀ ha).1
    have hbox : (Subtype.val ⁻¹' W) ×ˢ ({e} : Set (UC.proj (x₀ := x₀) ⁻¹' ({x} : Set X)))
        ∈ 𝓝 (⟨y, hy⟩, e) := by
      rw [nhds_prod_eq]
      exact Filter.prod_mem_prod ((hW.isOpen.preimage continuous_subtype_val).mem_nhds hyW)
        ((isOpen_discrete _).mem_nhds rfl)
    refine Filter.mem_of_superset hbox ?_
    rintro ⟨⟨y', hy'⟩, e'⟩ ⟨hy'W, he'⟩
    have he'e : e' = e := by simpa using he'
    rw [he'e]
    show Hg (⟨y', hy'⟩, e) ∈ Subtype.val ⁻¹' UC.sheet e₀ V₀
    rw [Set.mem_preimage]
    have hWV : W ⊆ V := fun a ha => (hWVWV₀ ha).1
    have hWV₀ : W ⊆ V₀ := fun a ha => (hWVWV₀ ha).2
    refine UC_sheet_trans hp' ?_ hWV₀
    show sectOf V hV e.1 (hfibV e) y' hy' ∈ UC.sheet (sectOf V hV e.1 (hfibV e) y hy) W
    rw [← sectOf_eq_sectOf V W hV hW hWV e.1 (hfibV e) hy hyW hy'W]
    exact sectOf_mem_sheet V W hV hW hWV e.1 (hfibV e) hy hyW hy'W
  refine ⟨UC_discreteTopology_fiber hB x, V, hxV, hV.isOpen,
    (UC_continuous_proj hB).isOpen_preimage V hV.isOpen, ?_, ?_⟩
  · exact Homeomorph.mk ⟨Hf, Hg, hHgHf, hHfHg⟩ hHf_cont hHg_cont
  · intro e'
    rfl

end Covering

end Work.EQ.UnivCover
