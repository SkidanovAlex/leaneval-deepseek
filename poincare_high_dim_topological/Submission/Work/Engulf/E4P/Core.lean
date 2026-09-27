import Mathlib
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.E4alt.Defs2
import Submission.Work.Engulf.E4alt.Defs3
import Submission.Work.Engulf.Auxi.face_subset_of_subset_union
import Submission.Work.Engulf.Auxi.SimplexCover
import Submission.Work.Engulf.Auxi.TameTransfer
import Submission.Work.Engulf.E4P.Defs
import Submission.Work.Engulf.E4P.Basic

/-!
# `Work.Engulf.E4P.Core` — the core region `coreSet`

Elementary geometry of `Work.Engulf.Alt.coreSet Γ₁ f ψ` (the union of the fine faces whose
`f`-image lies in the `5/8` cube), and the transfer of the smoothing chart `SCh` of the *coarse*
complex `Γ` to the *fine* complex `Γ₁` on the frozen set `L ∪ coreSet` (this is the base case
`chart` of the piece loop).

* `isSubSp_coreSet` : the core region is the space of a subcomplex of `Γ₁`;
* `coreSet_wit` : a face whose simplex lies in the core region has its `f`-image in the `5/8` cube
  (the `simplex_cover` argument);
* `core11_of_core` : hence `Core11` gives `g₁ '' coreSet ⊆ ψ '' closedCube (11/16)`;
* `dimLE_of_subdivides` : `DimLE` transfers to a refinement;
* `smoothChart_core` : `SmoothChart p X Γ₁ (L ∪ coreSet) g₁ ψ` from `SmoothChart p X Γ L f ψ`
  and the witnesses `NormData.carrier`, `NormData.wit`.
-/

open Set Metric PL

namespace Work.Engulf.E4P

/-! ## The core region is a subcomplex, and the carrier property for its faces -/

theorem isSubSp_coreSet {n N : ℕ} {M : Type*} [MetricSpace M] (Γ₁ : Cx N) (f : E N → M)
    (ψ : CubeChart n M) : IsSubSp Γ₁ (Work.Engulf.Alt.coreSet Γ₁ f ψ) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    simp only [Work.Engulf.Alt.coreSet, Set.mem_iUnion, exists_prop] at hx
    obtain ⟨s, hs, -, hxs⟩ := hx
    exact Geometry.SimplicialComplex.convexHull_subset_space hs hxs
  · intro x hx
    simp only [Work.Engulf.Alt.coreSet, Set.mem_iUnion, exists_prop] at hx
    obtain ⟨s, hs, hcond, hxs⟩ := hx
    refine ⟨s, hs, hxs, fun y hy => ?_⟩
    exact Set.mem_iUnion₂.mpr ⟨s, hs, Set.mem_iUnion.mpr ⟨hcond, hy⟩⟩

/-- A face of `Γ₁` whose simplex lies in the core region has its `f`-image in the `5/8` cube. -/
theorem coreSet_wit {n N : ℕ} {M : Type*} [MetricSpace M] {Γ₁ : Cx N}
    (hfin : Γ₁.faces.Finite) (f : E N → M) (ψ : CubeChart n M) {s : Finset (E N)}
    (hs : s ∈ Γ₁.faces) (h : simp s ⊆ Work.Engulf.Alt.coreSet Γ₁ f ψ) :
    f '' simp s ⊆ ψ.toFun '' closedCube (5 / 8 : ℝ) := by
  classical
  set T : Finset (Finset (E N)) := hfin.toFinset.filter
    (fun t => f '' simp t ⊆ ψ.toFun '' closedCube (5 / 8 : ℝ)) with hT
  have hTmem : ∀ t, t ∈ T ↔ t ∈ Γ₁.faces ∧ f '' simp t ⊆ ψ.toFun '' closedCube (5 / 8 : ℝ) := by
    intro t
    rw [hT, Finset.mem_filter, Set.Finite.mem_toFinset]
  have hcov : simp s ⊆ ⋃ t ∈ T, simp t := by
    intro x hx
    have hx' := h hx
    simp only [Work.Engulf.Alt.coreSet, Set.mem_iUnion, exists_prop] at hx'
    obtain ⟨t, ht, hcond, hxt⟩ := hx'
    exact Set.mem_iUnion₂.mpr ⟨t, (hTmem t).mpr ⟨ht, hcond⟩, hxt⟩
  obtain ⟨t, htT, hst⟩ :=
    Work.Engulf.simp_cover (K := Γ₁) (fun t ht => ((hTmem t).mp ht).1) hs hcov
  exact (Set.image_mono hst).trans ((hTmem t).mp htT).2

/-- `Core11` unwound: the `g₁`-image of the whole core region lies in the `11/16` cube. -/
theorem core11_of_core {n p q N : ℕ} {M : Type*} [MetricSpace M] {V X : Set M} {Γ : Cx N}
    {K L : Set (E N)} {f : E N → M} {τ₀ τ₁ : Finset (E N)} {ψ : CubeChart n M} {ε : ℝ}
    (ND : Work.Engulf.Alt.NormData n p q N M V X Γ K L f τ₀ τ₁ ψ ε)
    (hc11 : Work.Engulf.Alt.Core11 ND) :
    ∀ x ∈ Work.Engulf.Alt.coreSet ND.Γ₁ f ψ,
      ND.g₁ x ∈ ψ.toFun '' closedCube (11 / 16 : ℝ) := by
  intro x hx
  obtain ⟨s, hs, hxs, hsub⟩ := (isSubSp_coreSet ND.Γ₁ f ψ).2 x hx
  have h5 : f '' simp s ⊆ ψ.toFun '' closedCube (5 / 8 : ℝ) := coreSet_wit ND.hΓ₁ f ψ hs hsub
  exact hc11 x (Geometry.SimplicialComplex.convexHull_subset_space hs hxs) (h5 ⟨x, hxs, rfl⟩)

/-! ## `DimLE` and the smoothing chart on the fine complex -/

/-- `DimLE` transfers to a refinement. -/
theorem dimLE_of_subdivides {N p : ℕ} {Γ₁ Γ : Cx N} (h : Subdivides Γ₁ Γ)
    (hΓ : DimLE Γ (p + 1)) : DimLE Γ₁ (p + 1) := by
  intro s hs
  obtain ⟨t, ht, hst⟩ := h.2 s hs
  exact le_trans (card_le_of_convexHull_subset (Γ₁.indep hs) (Γ.indep ht) hst) (hΓ t ht)

/-- The smoothing chart of the coarse complex is a smoothing chart of the fine complex on the
frozen set `L ∪ coreSet`. -/
theorem smoothChart_core {n p q N : ℕ} {M : Type*} [MetricSpace M] {V X : Set M} {Γ : Cx N}
    {K L : Set (E N)} {f : E N → M} {τ₀ τ₁ : Finset (E N)} {ψ : CubeChart n M} {ε : ℝ}
    (ND : Work.Engulf.Alt.NormData n p q N M V X Γ K L f τ₀ τ₁ ψ ε)
    (hLsub : IsSubSp Γ L) (SCh : SmoothChart p X Γ L f ψ) :
    SmoothChart p X ND.Γ₁ (L ∪ Work.Engulf.Alt.coreSet ND.Γ₁ f ψ) ND.g₁ ψ := by
  refine ⟨SCh.1, ?_⟩
  intro s hs hsL y hy hyc
  have hLsp : IsSubSp ND.Γ₁ L := ND.subsp L hLsub
  have hCsp : IsSubSp ND.Γ₁ (Work.Engulf.Alt.coreSet ND.Γ₁ f ψ) := isSubSp_coreSet ND.Γ₁ f ψ
  rcases Work.Engulf.Aux.face_subset_of_subset_union ND.hΓ₁ hLsp hCsp hs hsL with h1 | h2
  · obtain ⟨t, ht, hst, htL⟩ := ND.carrier s hs h1
    have hyL : y ∈ L := h1 hy
    have hcube : f y ∈ ψ.toFun '' closedCube (3 / 4 : ℝ) := by
      rw [← ND.g₁frz hyL]; exact hyc
    obtain ⟨δ, hδ, hlin⟩ := SCh.2 t ht htL y (hst hy) hcube
    obtain ⟨A, hA⟩ := hlin
    refine ⟨δ, hδ, A, fun z hz => ⟨(hA z ⟨hst hz.1, hz.2⟩).1, ?_⟩⟩
    rw [ND.g₁frz (h1 hz.1), (hA z ⟨hst hz.1, hz.2⟩).2]
  · have hcore : f '' simp s ⊆ ψ.toFun '' closedCube (5 / 8 : ℝ) :=
      coreSet_wit ND.hΓ₁ f ψ hs h2
    obtain ⟨A, hAeq, hAopen⟩ := ND.wit s hs hcore
    exact ⟨1, one_pos, A, fun z hz => ⟨(hAopen z hz.1).1, hAeq hz.1⟩⟩

end Work.Engulf.E4P
