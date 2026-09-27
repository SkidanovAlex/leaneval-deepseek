import Submission.Work.OneDim.Defs
import Submission.Work.OneDim.local_diffeo_congr

/-!
# Existence of a maximal arc in a smooth 1-manifold

We define the extension order on parametrized arcs (via their graphs) and apply Zorn's lemma.
-/

open scoped Manifold Topology
open Set Function Filter

noncomputable section

namespace Work.OneDim

variable {C : Type*} [TopologicalSpace C] [ChartedSpace E1 C] [IsManifold I1 sm C]

/-- The standard linear equivalence `ℝ ≃L[ℝ] E1`. -/
def stdLE : ℝ ≃L[ℝ] E1 :=
  (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm.trans
    (EuclideanSpace.equiv (Fin 1) ℝ).symm

/-- A continuous linear equivalence, viewed as a partial diffeomorphism on all of the space. -/
def pdiffCLM (L : ℝ ≃L[ℝ] E1) : PartialDiffeomorph (modelWithCornersSelf ℝ ℝ) I1 ℝ E1 sm where
  toPartialEquiv := L.toLinearEquiv.toEquiv.toPartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := (L : ℝ →L[ℝ] E1).contMDiff.contMDiffOn
  contMDiffOn_invFun := (L.symm : E1 →L[ℝ] ℝ).contMDiff.contMDiffOn

/-- Translation in `E1`, as a partial diffeomorphism on all of the space. -/
def pdiffTranslation (c : E1) : PartialDiffeomorph I1 I1 E1 E1 sm where
  toPartialEquiv :=
    { toFun := fun x => c + x
      invFun := fun x => x - c
      source := univ
      target := univ
      map_source' := fun x _ => mem_univ _
      map_target' := fun x _ => mem_univ _
      left_inv' := fun x _ => by abel
      right_inv' := fun x _ => by abel }
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := (contMDiff_const.add contMDiff_id).contMDiffOn
  contMDiffOn_invFun := (contMDiff_id.sub contMDiff_const).contMDiffOn

/-- The chart at a point, as a partial diffeomorphism. -/
def pdiffChart (p : C) : PartialDiffeomorph I1 I1 C E1 sm where
  toPartialEquiv := (chartAt E1 p).toPartialEquiv
  open_source := (chartAt E1 p).open_source
  open_target := (chartAt E1 p).open_target
  contMDiffOn_toFun := contMDiffOn_chart (I := I1) (n := sm) (x := p)
  contMDiffOn_invFun := contMDiffOn_chart_symm (I := I1) (n := sm) (x := p)

/-- **Seed arcs exist**: the chart at `p`, transported to `ℝ` along a linear equivalence
`ℝ ≃L[ℝ] E1`, is an arc parametrization near `p`. -/
theorem isArcParam_seed (p : C) : ∃ s γ, IsArcParam p s γ := by
  let L : ℝ ≃L[ℝ] E1 := stdLE
  refine ⟨{t : ℝ | (chartAt E1 p) p + L t ∈ (chartAt E1 p).target},
    fun t => (chartAt E1 p).symm ((chartAt E1 p) p + L t), ?_, ?_, ?_, ?_, ?_⟩
  · exact (chartAt E1 p).open_target.preimage (continuous_const.add L.continuous)
  · simpa using (chartAt E1 p).map_source (mem_chart_source E1 p)
  · have h : (chartAt E1 p) p + L 0 = (chartAt E1 p) p := by simp
    change (chartAt E1 p).symm ((chartAt E1 p) p + L 0) = p
    rw [h]
    exact (chartAt E1 p).left_inv (mem_chart_source E1 p)
  · rintro t₁ ht₁ t₂ ht₂ heq
    have h1 : (chartAt E1 p) p + L t₁ = (chartAt E1 p) p + L t₂ := by
      have e1 := (chartAt E1 p).right_inv ht₁
      have e2 := (chartAt E1 p).right_inv ht₂
      have heq' : (chartAt E1 p).symm ((chartAt E1 p) p + L t₁)
          = (chartAt E1 p).symm ((chartAt E1 p) p + L t₂) := heq
      have e3 : (chartAt E1 p) ((chartAt E1 p).symm ((chartAt E1 p) p + L t₁))
          = (chartAt E1 p) ((chartAt E1 p).symm ((chartAt E1 p) p + L t₂)) := by
        rw [heq']
      rw [e1, e2] at e3
      exact e3
    exact L.injective (add_left_cancel h1)
  · intro t
    have hLloc : IsLocalDiffeomorphAt 𝓘(ℝ) I1 sm L t.1 :=
      PartialDiffeomorph.isLocalDiffeomorphAt (pdiffCLM L) (I := 𝓘(ℝ)) (J := I1) (n := sm)
        (x := t.1) (mem_univ _)
    have hTloc : IsLocalDiffeomorphAt I1 I1 sm (fun y : E1 => (chartAt E1 p) p + y) (L t.1) :=
      PartialDiffeomorph.isLocalDiffeomorphAt (pdiffTranslation ((chartAt E1 p) p))
        (I := I1) (J := I1) (n := sm) (x := L t.1) (mem_univ _)
    have hAloc : IsLocalDiffeomorphAt 𝓘(ℝ) I1 sm
        (fun u : ℝ => (chartAt E1 p) p + L u) t.1 :=
      IsLocalDiffeomorphAt.comp (I := 𝓘(ℝ)) (J := I1) (K := I1) (M := ℝ) (N := E1) (P := E1)
        (n := sm) (g := fun y : E1 => (chartAt E1 p) p + y) hLloc hTloc
    have hXloc : IsLocalDiffeomorphAt I1 I1 sm (chartAt E1 p).symm
        ((chartAt E1 p) p + L t.1) :=
      PartialDiffeomorph.isLocalDiffeomorphAt (pdiffChart p).symm (I := I1) (J := I1) (n := sm)
        (x := (chartAt E1 p) p + L t.1) t.2
    exact IsLocalDiffeomorphAt.comp (I := 𝓘(ℝ)) (J := I1) (K := I1) (M := ℝ) (N := E1) (P := C)
      (n := sm) (g := (chartAt E1 p).symm) hAloc hXloc

lemma eq_of_mem_arcGraphs {p : C} {G : Set (ℝ × C)} (hG : G ∈ arcGraphs p) {t : ℝ} {x y : C}
    (hx : (t, x) ∈ G) (hy : (t, y) ∈ G) : x = y := by
  obtain ⟨s, γ, -, rfl⟩ := hG
  simp only [arcGraph, mem_ofPred_eq] at hx hy
  rw [hx.2, hy.2]

/-- The canonical function attached to a graph. -/
def graphFun (G : Set (ℝ × C)) (p : C) : ℝ → C := by
  classical
  exact fun t => if h : ∃ x, (t, x) ∈ G then h.choose else p

lemma graphFun_spec {G : Set (ℝ × C)} {p : C}
    (huniq : ∀ {t : ℝ} {x y : C}, (t, x) ∈ G → (t, y) ∈ G → x = y)
    {t : ℝ} {x : C} (hx : (t, x) ∈ G) : graphFun G p t = x := by
  have h : ∃ x, (t, x) ∈ G := ⟨x, hx⟩
  simp only [graphFun, dif_pos h]
  exact huniq h.choose_spec hx

lemma mem_arcGraphs_of_eq {p : C} {s : Set ℝ} {γ : ℝ → C} (h : IsArcParam p s γ) :
    arcGraph s γ ∈ arcGraphs p := ⟨s, γ, h, rfl⟩

lemma arcGraph_subset_iff {s s' : Set ℝ} {γ γ' : ℝ → C} :
    arcGraph s γ ⊆ arcGraph s' γ' ↔ s ⊆ s' ∧ EqOn γ γ' s where
  mp h := ⟨fun t ht => (h (mem_arcGraph.mpr ht)).1,
    fun t ht => (h (mem_arcGraph.mpr ht)).2⟩
  mpr h := by
    intro q hq
    obtain ⟨hsub, heq⟩ := h
    simp only [arcGraph, mem_ofPred_eq] at hq ⊢
    exact ⟨hsub hq.1, by rw [hq.2, heq hq.1]⟩

lemma sUnion_mem_arcGraphs {p : C} {c : Set (Set (ℝ × C))} (hc : c ⊆ arcGraphs p)
    (hchain : IsChain (· ⊆ ·) c) (hne : c.Nonempty) : ⋃₀ c ∈ arcGraphs p := by
  obtain ⟨G₀, hG₀⟩ := hne
  set G : Set (ℝ × C) := ⋃₀ c with hGdef
  have huniq : ∀ {t : ℝ} {x y : C}, (t, x) ∈ G → (t, y) ∈ G → x = y := by
    intro t x y hx hy
    rw [hGdef, mem_sUnion] at hx hy
    obtain ⟨G₁, hG₁, hx₁⟩ := hx
    obtain ⟨G₂, hG₂, hy₂⟩ := hy
    rcases eq_or_ne G₁ G₂ with rfl | hne12
    · exact eq_of_mem_arcGraphs (hc hG₁) hx₁ hy₂
    · rcases hchain hG₁ hG₂ hne12 with h | h
      · exact eq_of_mem_arcGraphs (hc hG₂) (h hx₁) hy₂
      · exact eq_of_mem_arcGraphs (hc hG₁) hx₁ (h hy₂)
  have hdom : arcGraphDom G = ⋃₀ (arcGraphDom '' c) := by
    ext t
    simp only [mem_arcGraphDom, hGdef, mem_sUnion, mem_image]
    constructor
    · rintro ⟨x, G', hG', hx⟩
      exact ⟨arcGraphDom G', ⟨G', hG', rfl⟩, ⟨x, hx⟩⟩
    · rintro ⟨s', ⟨G', hG', rfl⟩, ⟨x, hx⟩⟩
      exact ⟨x, G', hG', hx⟩
  have hopen : IsOpen (arcGraphDom G) := by
    rw [hdom]
    refine isOpen_sUnion ?_
    rintro s ⟨G', hG', rfl⟩
    obtain ⟨s', γ', harc', rfl⟩ := hc hG'
    simpa [arcGraphDom_arcGraph] using harc'.isOpen
  have hzero : (0 : ℝ) ∈ arcGraphDom G := by
    obtain ⟨s', γ', harc', rfl⟩ := hc hG₀
    refine ⟨γ' 0, ?_⟩
    simpa [hGdef] using mem_sUnion.mpr ⟨arcGraph s' γ', hG₀, mem_arcGraph.mpr harc'.zero_mem⟩
  have hval : graphFun G p 0 = p := by
    obtain ⟨s', γ', harc', rfl⟩ := hc hG₀
    have hmem : (0, γ' 0) ∈ G := by
      simpa [hGdef] using mem_sUnion.mpr ⟨arcGraph s' γ', hG₀, mem_arcGraph.mpr harc'.zero_mem⟩
    exact (graphFun_spec huniq hmem).trans harc'.apply_zero
  have hgraph : G = arcGraph (arcGraphDom G) (graphFun G p) := by
    ext q
    constructor
    · intro hq
      exact ⟨⟨q.2, hq⟩, (graphFun_spec huniq hq).symm⟩
    · rintro ⟨⟨x, hx⟩, h2⟩
      have h3 : graphFun G p q.1 = x := graphFun_spec huniq hx
      have h4 : q.2 = x := by rw [h2, h3]
      have hqeq : q = (q.1, x) := Prod.ext rfl h4
      rw [hqeq]
      exact hx
  refine ⟨arcGraphDom G, graphFun G p, ?_, hgraph⟩
  refine ⟨hopen, hzero, hval, ?_, ?_⟩
  · rintro t₁ ht₁ t₂ ht₂ heq
    have h1 : graphFun G p t₁ = graphFun G p t₂ := heq
    obtain ⟨x₁, hx₁⟩ := mem_arcGraphDom.mp ht₁
    obtain ⟨x₂, hx₂⟩ := mem_arcGraphDom.mp ht₂
    have e1 : graphFun G p t₁ = x₁ := graphFun_spec huniq hx₁
    have e2 : graphFun G p t₂ = x₂ := graphFun_spec huniq hx₂
    have hxyeq : x₁ = x₂ := by rw [← e1, ← e2]; exact h1
    rw [hGdef, mem_sUnion] at hx₁ hx₂
    obtain ⟨G₁, hG₁, hx₁'⟩ := hx₁
    obtain ⟨G₂, hG₂, hx₂'⟩ := hx₂
    rcases eq_or_ne G₁ G₂ with rfl | hne12
    · obtain ⟨s', γ', harc', rfl⟩ := hc hG₁
      exact harc'.injOn hx₁'.1 hx₂'.1 (hx₁'.2.symm.trans (hxyeq.trans hx₂'.2))
    · rcases hchain hG₁ hG₂ hne12 with h | h
      · obtain ⟨s', γ', harc', rfl⟩ := hc hG₂
        exact harc'.injOn (h hx₁').1 hx₂'.1 ((h hx₁').2.symm.trans (hxyeq.trans hx₂'.2))
      · obtain ⟨s', γ', harc', rfl⟩ := hc hG₁
        exact harc'.injOn hx₁'.1 (h hx₂').1 (hx₁'.2.symm.trans (hxyeq.trans (h hx₂').2))
  · intro t
    have ht : t.1 ∈ arcGraphDom G := t.2
    have ht2 : t.1 ∈ ⋃₀ (arcGraphDom '' c) := by simpa only [hdom] using ht
    rw [mem_sUnion] at ht2
    obtain ⟨s', ⟨G', hG', hs'⟩, ht''⟩ := ht2
    rw [← hs'] at ht''
    obtain ⟨s'', γ', harc', rfl⟩ := hc hG'
    have hts : t.1 ∈ s'' := by simpa [arcGraphDom_arcGraph] using ht''
    have hloc : IsLocalDiffeomorphAt 𝓘(ℝ) I1 sm γ' t.1 := harc'.isLocalDiffeomorphOn ⟨t.1, hts⟩
    refine local_diffeo_congr ?_ hloc
    refine Filter.eventuallyEq_of_mem (harc'.isOpen.mem_nhds hts) ?_
    intro u hu
    have hmem : (u, γ' u) ∈ G := by
      simpa [hGdef] using mem_sUnion.mpr ⟨arcGraph s'' γ', hG', mem_arcGraph.mpr hu⟩
    exact (graphFun_spec huniq hmem).symm

theorem exists_maximal_arc_param (p : C) :
    ∃ s γ, IsArcParam p s γ ∧
      ∀ s' γ', IsArcParam p s' γ' → s ⊆ s' → EqOn γ γ' s → s' ⊆ s := by
  obtain ⟨s₀, γ₀, h₀⟩ := isArcParam_seed (C := C) p
  obtain ⟨m, -, hmS, hmax⟩ :=
    zorn_subset_nonempty (arcGraphs (C := C) p)
      (fun c hc hchain hne => ⟨⋃₀ c, sUnion_mem_arcGraphs hc hchain hne,
        fun s hs => subset_sUnion_of_mem hs⟩) (arcGraph s₀ γ₀) (mem_arcGraphs_of_eq h₀)
  obtain ⟨s, γ, harc, hm⟩ := hmS
  subst hm
  refine ⟨s, γ, harc, fun s' γ' harc' hsub heq => ?_⟩
  have h1 : arcGraph s γ ⊆ arcGraph s' γ' := arcGraph_subset_iff.mpr ⟨hsub, heq⟩
  have h2 := hmax (mem_arcGraphs_of_eq harc') h1
  intro t ht
  exact (h2 (mem_arcGraph.mpr ht)).1

end Work.OneDim
