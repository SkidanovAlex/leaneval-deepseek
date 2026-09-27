import Mathlib
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.Auxi.simplex_cover
import Submission.Work.Engulf.E4Aux.facets_cover_frontier

/-!
# `E4`'s assembly helpers: `Engulfs` algebra, the `q`-skeleton of a shelling order, and the
reduction of Lemma 7 Case 1 to the shelling loop.

These are the lemmas of `Submission/Work/Engulf/Chain/E4.lean` that the *loop* of `E4`
(`Work.Engulf.E4Aux.loop`, which cannot import `Chain.E4` itself) also needs.  They live here so
that both `Chain.E4` and `E4Aux.loop` can use them.  Namespace `Work.Engulf.Chain` is shared, so
no fully qualified name changes.
-/

namespace Work.Engulf.Chain

open Set Metric _root_.PL

universe u

/-! ### `Engulfs` is monotone in the engulfed set and in the budget -/

/-! ### `Engulfs` is monotone in the engulfed set and in the budget -/

theorem engulfs_mono_H {N : ℕ} {M : Type*} [MetricSpace M] {V X : Set M} {Γ : Cx N}
    {H H' L : Set (E N)} {f : E N → M} {ε : ℝ} (h : H ⊆ H')
    (he : Work.Engulf.Engulfs V X Γ H' L f ε) : Work.Engulf.Engulfs V X Γ H L f ε := by
  obtain ⟨g, hg, hL, hd, hh, hsup, heng⟩ := he
  refine ⟨g, hg, hL, hd, hh, hsup, ?_⟩
  rintro z (hz | ⟨y, hy, rfl⟩)
  · exact heng (Or.inl hz)
  · exact heng (Or.inr ⟨y, h hy, rfl⟩)

theorem engulfs_mono_eps {N : ℕ} {M : Type*} [MetricSpace M] {V X : Set M} {Γ : Cx N}
    {H L : Set (E N)} {f : E N → M} {ε ε' : ℝ} (h : ε ≤ ε')
    (he : Work.Engulf.Engulfs V X Γ H L f ε) : Work.Engulf.Engulfs V X Γ H L f ε' := by
  obtain ⟨g, hg, hL, hd, hh, hsup, heng⟩ := he
  exact ⟨g, hg, hL, fun x hx => lt_of_lt_of_le (hd x hx) h, hh, hsup, heng⟩

/-! ### Composition of two engulfing steps -/

theorem CSupp.trans_skel {M : Type*} [TopologicalSpace M] {h₁ h₂ : M ≃ₜ M}
    (h1 : PL.CSupp h₁ univ) (h2 : PL.CSupp h₂ univ) : PL.CSupp (h₁.trans h₂) univ := by
  obtain ⟨C₁, hC₁c, -, hC₁⟩ := h1
  obtain ⟨C₂, hC₂c, -, hC₂⟩ := h2
  refine ⟨C₁ ∪ h₁ ⁻¹' C₂, hC₁c.union ?_, Set.subset_univ _, ?_⟩
  · rwa [Homeomorph.isCompact_preimage]
  · intro x hx
    simp only [Set.mem_union, Set.mem_preimage, not_or] at hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [Homeomorph.trans_apply, hC₁ x hx1]
    exact hC₂ x (by rwa [hC₁ x hx1] at hx2)

/-- Two engulfing steps compose.  The second step is run in the image `h₁ '' V` of the
first, and the first homeomorphism is left pointwise fixed there. -/
theorem engulfs_comp {N : ℕ} {M : Type*} [MetricSpace M] {Γ : Cx N} {V : Set M}
    {X₁ X₂ : Set M} {H₁ H₂ L : Set (E N)} {f g₁ g₂ : E N → M} {ε₁ ε₂ : ℝ} {h₁ h₂ : M ≃ₜ M}
    (hg₂ : ContinuousOn g₂ Γ.space)
    (hL : EqOn g₂ f L)
    (hd1 : ∀ x ∈ Γ.space, dist (g₁ x) (f x) < ε₁)
    (hd2 : ∀ x ∈ Γ.space, dist (g₂ x) (g₁ x) < ε₂)
    (hs1 : PL.CSupp h₁ univ) (hs2 : PL.CSupp h₂ univ)
    (hfix : ∀ y ∈ h₁ '' V, h₂ y = y)
    (Heq : EqOn g₂ g₁ H₁)
    (he1 : X₁ ∪ g₁ '' H₁ ⊆ h₁ '' V)
    (he2 : X₂ ∪ g₂ '' H₂ ⊆ h₂ '' (h₁ '' V)) :
    Work.Engulf.Engulfs V X₂ Γ (H₁ ∪ H₂) L f (ε₁ + ε₂) := by
  refine ⟨g₂, hg₂, hL, fun x hx => ?_, ⟨h₁.trans h₂, ?csupp, ?eng⟩⟩
  case csupp =>
    obtain ⟨C₁, hC₁c, -, hC₁⟩ := hs1
    obtain ⟨C₂, hC₂c, -, hC₂⟩ := hs2
    refine ⟨C₁ ∪ h₁ ⁻¹' C₂, hC₁c.union ?_, Set.subset_univ _, ?_⟩
    · rwa [Homeomorph.isCompact_preimage]
    · intro x hx
      simp only [Set.mem_union, Set.mem_preimage, not_or] at hx
      obtain ⟨hx1, hx2⟩ := hx
      rw [Homeomorph.trans_apply, hC₁ x hx1]
      exact hC₂ x (by rwa [hC₁ x hx1] at hx2)
  case eng =>
    have himg : ⇑(h₁.trans h₂) '' V = ⇑h₂ '' (⇑h₁ '' V) := by rw [Set.image_image]; rfl
    rw [himg]
    rintro z (hz | hz)
    · exact he2 (Or.inl hz)
    · obtain ⟨y, hy, rfl⟩ := hz
      rcases hy with hy | hy
      · have hgy : g₁ y ∈ h₁ '' V := he1 (Or.inr ⟨y, hy, rfl⟩)
        rw [Heq hy]
        exact ⟨g₁ y, hgy, hfix (g₁ y) hgy⟩
      · exact he2 (Or.inr ⟨y, hy, rfl⟩)
  · calc dist (g₂ x) (f x) ≤ dist (g₂ x) (g₁ x) + dist (g₁ x) (f x) := dist_triangle _ _ _
      _ < ε₂ + ε₁ := add_lt_add (hd2 x hx) (hd1 x hx)
      _ = ε₁ + ε₂ := by ring

/-! ### Transfer of `Engulfs` along a subdivision -/

theorem engulfs_of_subdivides {N : ℕ} {M : Type*} [MetricSpace M] {V X : Set M} {Γ Γ' : Cx N}
    {H L : Set (E N)} {f : E N → M} {ε : ℝ} (h : PL.Subdivides Γ' Γ)
    (he : Work.Engulf.Engulfs V X Γ' H L f ε) : Work.Engulf.Engulfs V X Γ H L f ε := by
  obtain ⟨g, hg, hL, hd, hh, hsu, hen⟩ := he
  rw [h.1] at hg hd
  exact ⟨g, hg, hL, hd, hh, hsu, hen⟩

/-- The `τ₀`-side of a simplex is contained in the union of the facets of any full-dimensional
family covering it: `topOf τ₀ τ₁ ⊆ ⋃_{t ∈ ord} ⋃_{w ∈ t} simp (t.erase w)`.  (This is what allows
`E4`'s invariant, which only tracks the `q`-skeleton of the shelled simplices, to imply the
engulfing of `K ∪ topOf τ₀ τ₁`.) -/
theorem topOf_subset_skeleton {N : ℕ} {τ₀ τ₁ : Finset (E N)} (ord : List (Finset (E N)))
    (hne : (τ₀ ∪ τ₁).Nonempty) (hind : AffineIndependent ℝ (fun v : ↥(τ₀ ∪ τ₁) => (v : E N)))
    (hfin : ∀ t ∈ ord, AffineIndependent ℝ (fun v : ↥t => (v : E N)))
    (hsub : ∀ t ∈ ord, simp t ⊆ simp (τ₀ ∪ τ₁))
    (hcard : ∀ t ∈ ord, t.card = (τ₀ ∪ τ₁).card)
    (hcover : simp (τ₀ ∪ τ₁) ⊆ ⋃ t ∈ ord, simp t) :
    Work.Engulf.topOf τ₀ τ₁ ⊆ ⋃ t ∈ ord, ⋃ w ∈ t, simp (t.erase w) := by
  intro x hx
  simp only [Work.Engulf.topOf, Set.mem_iUnion, exists_prop] at hx
  obtain ⟨w, hw, hxw⟩ := hx
  exact Work.Engulf.E4Aux.facets_cover_frontier ord hne hind hfin hsub hcard hcover w
    (Finset.mem_union_left τ₁ hw) hxw

/-! ### Assembling `E4` from the shelling loop (Newman `§14`, step `(e)`) -/

/-- If `E4`'s loop has engulfed the `q`-skeleton of the shelled simplex inside the subdivision
`Γ₁` of `Γ`, and that skeleton contains `topOf τ₀ τ₁`, then it provides the engulfing for `Γ`
and `K ∪ topOf τ₀ τ₁`. -/
theorem engulfs_of_shell {N : ℕ} {M : Type*} [MetricSpace M] {V X : Set M} {Γ Γ₁ : Cx N}
    {K L : Set (E N)} {f : E N → M} {ε : ℝ} {τ₀ τ₁ : Finset (E N)}
    (hsub : PL.Subdivides Γ₁ Γ) (ord : List (Finset (E N)))
    (hcov : Work.Engulf.topOf τ₀ τ₁ ⊆ ⋃ i ∈ Finset.range ord.length,
      ⋃ (hi : i < ord.length), ⋃ w ∈ ord[i], simp (ord[i].erase w))
    (he : Work.Engulf.Engulfs V X Γ₁ (K ∪ ⋃ i ∈ Finset.range ord.length,
      ⋃ (hi : i < ord.length), ⋃ w ∈ ord[i], simp (ord[i].erase w)) L f ε) :
    Work.Engulf.Engulfs V X Γ (K ∪ Work.Engulf.topOf τ₀ τ₁) L f ε :=
  engulfs_of_subdivides hsub (engulfs_mono_H (fun x hx => by
    rcases hx with h | h
    · exact Or.inl h
    · exact Or.inr (hcov h)) he)

/-! ### The `q`-skeleton of the shelling order and the reduction of `E4` to the loop -/

/-- The union of the facets (the `q`-skeleton) of the simplices of a shelling order, in the
`⋃ j ∈ range ord.length` form used by `Work.Engulf.InnerInv`. -/
def Skel {N : ℕ} (ord : List (Finset (E N))) : Set (E N) :=
  ⋃ j ∈ Finset.range ord.length, ⋃ (hj : j < ord.length),
    ⋃ w ∈ ord[j], simp (ord[j].erase w)

theorem mem_Skel {N : ℕ} {ord : List (Finset (E N))} {x : E N} :
    x ∈ Skel ord ↔ ∃ j : Fin ord.length, ∃ w, w ∈ ord.get j ∧
      x ∈ simp ((ord.get j).erase w) := by
  constructor
  · intro hx
    simp only [Skel, Set.mem_iUnion, Finset.mem_range, exists_prop] at hx
    obtain ⟨j, hj, hj', w, hw, hx⟩ := hx
    exact ⟨⟨j, hj'⟩, w, hw, hx⟩
  · rintro ⟨j, w, hw, hx⟩
    simp only [Skel, Set.mem_iUnion, Finset.mem_range, exists_prop]
    exact ⟨j.1, j.2, j.2, w, hw, hx⟩

/-- The union over a list is the union over its indices. -/
theorem iUnion_list_eq_range {N : ℕ} (ord : List (Finset (E N))) :
    (⋃ t ∈ ord, ⋃ w ∈ t, simp (t.erase w)) = Skel ord := by
  ext x
  constructor
  · intro hx
    simp only [Set.mem_iUnion, exists_prop] at hx
    obtain ⟨t, ht, w, hw, hx⟩ := hx
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ht
    exact mem_Skel.mpr ⟨i, w, hw, hx⟩
  · intro hx
    obtain ⟨i, w, hw, hx⟩ := mem_Skel.mp hx
    exact Set.mem_iUnion₂.mpr ⟨ord.get i, List.get_mem _ _,
      Set.mem_iUnion₂.mpr ⟨w, hw, hx⟩⟩

/-- **`topOf ⊆ ` the `q`-skeleton of the shelling order** (contract `E4e`, step (e)): the
`τ₀`-side `topOf τ₀ τ₁` of the join `Δ = τ₀ ∪ τ₁` is contained in the union of the facets of the
simplices of any full-dimensional cover of `simp Δ` — in particular of the simplices of the
shelling order produced by `SubdivTools.shell`. -/
theorem topOf_subset_Skel {N : ℕ} {Γ₁ : Cx N} {τ₀ τ₁ : Finset (E N)}
    (ord : List (Finset (E N)))
    (hne : (τ₀ ∪ τ₁).Nonempty)
    (hind : AffineIndependent ℝ (fun v : ↥(τ₀ ∪ τ₁) => (v : E N)))
    (hfin : ∀ t ∈ ord, t ∈ Γ₁.faces)
    (hsub : ∀ t ∈ ord, simp t ⊆ simp (τ₀ ∪ τ₁))
    (hcard : ∀ t ∈ ord, t.card = (τ₀ ∪ τ₁).card)
    (hcover : simp (τ₀ ∪ τ₁) ⊆ ⋃ t ∈ ord, simp t) :
    Work.Engulf.topOf τ₀ τ₁ ⊆ Skel ord := by
  rw [← iUnion_list_eq_range]
  exact topOf_subset_skeleton ord hne hind (fun t ht => Γ₁.indep (hfin t ht)) hsub hcard hcover

/-- **Assembly of `E4` from the loop (Newman §14(e)).**  If the loop has engulfed the
`q`-skeleton `Skel ord` of the shelling order inside the subdivision `Γ₁` of `Γ`, and that
skeleton contains `topOf τ₀ τ₁`, then it provides the engulfing for `Γ` and `K ∪ topOf τ₀ τ₁`. -/
theorem engulfs_of_Skel {N : ℕ} {M : Type*} [MetricSpace M] {V X : Set M} {Γ Γ₁ : Cx N}
    {K L : Set (E N)} {f : E N → M} {ε : ℝ} {τ₀ τ₁ : Finset (E N)}
    (hsub : PL.Subdivides Γ₁ Γ) (ord : List (Finset (E N)))
    (hcov : Work.Engulf.topOf τ₀ τ₁ ⊆ Skel ord)
    (he : Work.Engulf.Engulfs V X Γ₁ (K ∪ Skel ord) L f ε) :
    Work.Engulf.Engulfs V X Γ (K ∪ Work.Engulf.topOf τ₀ τ₁) L f ε :=
  engulfs_of_shell hsub ord hcov he

/-- The `i`-th stage of the `q`-skeleton: `Skel` restricted to the first `i` simplices of the
shelling order.  This is what `Work.Engulf.InnerInv.eng` tracks. -/
def SkelTake {N : ℕ} (ord : List (Finset (E N))) (i : ℕ) : Set (E N) :=
  ⋃ j ∈ Finset.range i, ⋃ (hj : j < ord.length),
    ⋃ w ∈ ord[j], simp (ord[j].erase w)

theorem SkelTake_mono {N : ℕ} (ord : List (Finset (E N))) {i i' : ℕ} (h : i ≤ i') :
    SkelTake ord i ⊆ SkelTake ord i' := by
  intro x hx
  simp only [SkelTake, Set.mem_iUnion, Finset.mem_range, exists_prop] at hx ⊢
  obtain ⟨j, hj, hj', w, hw, hx⟩ := hx
  exact ⟨j, lt_of_lt_of_le hj h, hj', w, hw, hx⟩

theorem SkelTake_self {N : ℕ} (ord : List (Finset (E N))) :
    SkelTake ord ord.length = Skel ord := rfl

theorem SkelTake_succ {N : ℕ} (ord : List (Finset (E N))) {i : ℕ} (hi : i < ord.length) :
    SkelTake ord (i + 1) = SkelTake ord i ∪ ⋃ w ∈ ord[i], simp (ord[i].erase w) := by
  ext x
  simp only [SkelTake, Set.mem_iUnion, Finset.mem_range, Set.mem_union, exists_prop]
  constructor
  · rintro ⟨j, hj, hj', w, hw, hx⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hjlt | rfl
    · exact Or.inl ⟨j, hjlt, hj', w, hw, hx⟩
    · exact Or.inr ⟨w, hw, hx⟩
  · rintro (⟨j, hj, hj', w, hw, hx⟩ | ⟨w, hw, hx⟩)
    · exact ⟨j, Nat.lt_succ_of_lt hj, hj', w, hw, hx⟩
    · exact ⟨i, Nat.lt_succ_self i, hi, w, hw, hx⟩




/-! ### A fine face inside the shelled simplex lies in a shelled simplex -/

/-- **Every face of the subdivision inside `simp Δ` lies in a simplex of the shelling order.**
If `ord` is a cover of `simp Δ` by full-dimensional faces of `Γ₁` (as delivered by
`SubdivTools.shell`), then a face `s` of `Γ₁` with `simp s ⊆ simp Δ` is contained in one of the
`ord[i]`.  This is what lets the loop freeze the whole subcomplex of `Γ₁` over `simp Δ` while
keeping the prepared map affine there. -/
theorem exists_ord_of_simp_subset {N : ℕ} {Γ₁ : PL.Cx N} {Δ : Finset (PL.E N)}
    (ord : List (Finset (PL.E N))) {s : Finset (PL.E N)}
    (hne : Δ.Nonempty) (hind : AffineIndependent ℝ (fun v : ↥Δ => (v : PL.E N)))
    (hordmem : ∀ i (hi : i < ord.length), ord[i] ∈ Γ₁.faces)
    (hordcard : ∀ i (hi : i < ord.length), (ord[i]).card = Δ.card)
    (hordsub : ∀ i (hi : i < ord.length), PL.simp ord[i] ⊆ PL.simp Δ)
    (hcov : PL.simp Δ ⊆ ⋃ i ∈ Finset.range ord.length,
      ⋃ (hj : i < ord.length), PL.simp ord[i])
    (hs : s ∈ Γ₁.faces) (hsΔ : PL.simp s ⊆ PL.simp Δ) :
    ∃ i : Fin ord.length, PL.simp s ⊆ PL.simp (ord.get i) := by
  classical
  by_contra hcon
  push_neg at hcon
  set T : Finset (Finset (PL.E N)) := ord.toFinset.image (fun τ => s ∩ τ) with hT
  have hsub : ∀ t ∈ T, t ⊆ s := by
    intro t ht
    rw [hT] at ht
    obtain ⟨τ, _, rfl⟩ := Finset.mem_image.mp ht
    exact Finset.inter_subset_left
  have hcovT : PL.simp s ⊆ ⋃ t ∈ T, PL.simp t := by
    intro x hx
    have hxΔ : x ∈ PL.simp Δ := hsΔ hx
    obtain ⟨i, hi, h'⟩ := Set.mem_iUnion₂.mp (hcov hxΔ)
    obtain ⟨hi', hxi⟩ := Set.mem_iUnion.mp h'
    have hmemT : s ∩ ord[i] ∈ T := by
      rw [hT]
      exact Finset.mem_image.mpr ⟨ord[i], List.mem_toFinset.mpr (List.getElem_mem hi'), rfl⟩
    have hxsimp : x ∈ PL.simp (s ∩ ord[i]) := by
      rw [show PL.simp (s ∩ ord[i]) = PL.simp s ∩ PL.simp ord[i] from
        (Work.Engulf.simp_inter hs (hordmem i hi')).symm]
      exact ⟨hx, hxi⟩
    exact Set.mem_iUnion₂.mpr ⟨s ∩ ord[i], hmemT, hxsimp⟩
  have hsn : s.Nonempty := Γ₁.nonempty_of_mem_faces hs
  have hmem := Work.Engulf.Aux.simplex_cover s T hsn (Γ₁.indep hs) hsub hcovT
  rw [hT] at hmem
  obtain ⟨τ, hτ, hτs⟩ := Finset.mem_image.mp hmem
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hτ)
  have hle : s ⊆ ord.get i := by rw [hi, ← hτs]; exact Finset.inter_subset_right
  exact hcon i (PL.simp_mono hle)

/-- The subcomplex of `Γ₁` over `simp Δ`: the union of the faces of `Γ₁` inside `simp Δ`. -/
noncomputable def subOver {N : ℕ} (Γ : PL.Cx N) (Δ : Finset (PL.E N))
    (hΓ : Γ.faces.Finite) : Set (PL.E N) := by
  classical
  exact ⋃ s ∈ hΓ.toFinset.filter (fun s => PL.simp s ⊆ PL.simp Δ), PL.simp s

theorem subOver_subset {N : ℕ} (Γ : PL.Cx N) (Δ : Finset (PL.E N)) (hΓ : Γ.faces.Finite)
    {x : PL.E N} :
    x ∈ subOver Γ Δ hΓ ↔ ∃ s ∈ Γ.faces, PL.simp s ⊆ PL.simp Δ ∧ x ∈ PL.simp s := by
  classical
  rw [subOver]
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨s, hs, hxs⟩
    exact ⟨s, (Set.Finite.mem_toFinset hΓ).mp (Finset.mem_filter.mp hs).1,
      (Finset.mem_filter.mp hs).2, hxs⟩
  · rintro ⟨s, hs, hsΔ, hxs⟩
    exact ⟨s, Finset.mem_filter.mpr ⟨(Set.Finite.mem_toFinset hΓ).mpr hs, hsΔ⟩, hxs⟩

theorem isSubSp_subOver {N : ℕ} (Γ : PL.Cx N) (Δ : Finset (PL.E N)) (hΓ : Γ.faces.Finite) :
    Work.Engulf.IsSubSp Γ (subOver Γ Δ hΓ) := by
  classical
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨s, hs, _, hxs⟩ := (subOver_subset Γ Δ hΓ).mp hx
    exact Geometry.SimplicialComplex.convexHull_subset_space hs hxs
  · intro x hx
    obtain ⟨s, hs, hsΔ, hxs⟩ := (subOver_subset Γ Δ hΓ).mp hx
    exact ⟨s, hs, hxs, fun y hy => (subOver_subset Γ Δ hΓ).mpr ⟨s, hs, hsΔ, hy⟩⟩

theorem SkelTake_subset_subOver {N : ℕ} {Γ₁ : PL.Cx N} {Δ : Finset (PL.E N)}
    (hΓ₁ : Γ₁.faces.Finite) (ord : List (Finset (PL.E N))) (i : ℕ)
    (hordmem : ∀ j (hj : j < ord.length), ord[j] ∈ Γ₁.faces)
    (hordsub : ∀ j (hj : j < ord.length), PL.simp ord[j] ⊆ PL.simp Δ) :
    SkelTake ord i ⊆ subOver Γ₁ Δ hΓ₁ := by
  intro x hx
  simp only [SkelTake, Set.mem_iUnion, Finset.mem_range, exists_prop] at hx
  obtain ⟨j, hj, hj', w, hw, hxw⟩ := hx
  have hfaces : ord[j].erase w ∈ Γ₁.faces :=
    Γ₁.down_closed (hordmem j hj') (Finset.erase_subset w _) (by
      rw [Finset.nonempty_iff_ne_empty]
      intro h0
      rw [h0, PL.simp, Finset.coe_empty, convexHull_empty] at hxw
      exact hxw)
  exact (subOver_subset Γ₁ Δ hΓ₁).mpr ⟨ord[j].erase w, hfaces,
    (PL.simp_mono (Finset.erase_subset w _)).trans (hordsub j hj'), hxw⟩

/-- `Engulfs` is monotone in the frozen set `L`: a smaller frozen set is a stronger conclusion. -/
theorem engulfs_mono_L {N : ℕ} {M : Type*} [MetricSpace M] {V X : Set M} {Γ : PL.Cx N}
    {H L L' : Set (PL.E N)} {f : PL.E N → M} {ε : ℝ} (h : L' ⊆ L)
    (he : Work.Engulf.Engulfs V X Γ H L f ε) : Work.Engulf.Engulfs V X Γ H L' f ε := by
  obtain ⟨g, hg, hL, hd, hh, hsu, hen⟩ := he
  exact ⟨g, hg, fun x hx => hL (h hx), hd, hh, hsu, hen⟩

end Work.Engulf.Chain
