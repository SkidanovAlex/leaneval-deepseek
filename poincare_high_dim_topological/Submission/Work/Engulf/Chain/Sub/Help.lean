import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Basic
import Submission.Work.Cells.Connell.extOverDisc_of_homeomorph
import Submission.Work.Engulf.Chain.Sub.Basic
import Submission.Work.Engulf.Chain.Sub.Skel
import Submission.Work.Engulf.Chain.Sub.RelInt

/-!
# `Submission.Work.Engulf.Chain.Sub.Help`

Elementary helpers for the outer loop of `Work.Engulf.Chain.E5`: compactly supported
homeomorphisms, diameters of simplices in a fine complex, uniform continuity on `Γ.space`,
transport of `Amb` along a homeomorphism, and `IsSubSp` for the faces occurring in the loop.
-/

open Set Metric PL

set_option maxHeartbeats 1000000

namespace Work.Engulf.Chain

variable {N : ℕ} {M : Type*} [MetricSpace M]

/-! ## Compactly supported homeomorphisms -/

theorem CSupp.trans {h₁ h₂ : M ≃ₜ M} (h₁c : PL.CSupp h₁ univ) (h₂c : PL.CSupp h₂ univ) :
    PL.CSupp (h₁.trans h₂) univ := by
  obtain ⟨C₁, hC₁, -, hid₁⟩ := h₁c
  obtain ⟨C₂, hC₂, -, hid₂⟩ := h₂c
  refine ⟨C₁ ∪ h₁.symm '' C₂, hC₁.union (hC₂.image h₁.symm.continuous), subset_univ _, ?_⟩
  intro x hx
  have hx₁ : x ∉ C₁ := fun h => hx (mem_union_left _ h)
  have hx₂ : h₁ x ∉ C₂ := by
    intro h
    have hmem : x ∈ h₁.symm '' C₂ := ⟨h₁ x, h, by simp⟩
    exact hx (mem_union_right _ hmem)
  show h₂ (h₁ x) = x
  rw [hid₂ (h₁ x) hx₂, hid₁ x hx₁]

/-! ## Diameters of fine simplices -/

/-- A point of the simplex on `s` is within the vertex-diameter of any vertex of `s`. -/
theorem dist_le_of_mem_simp {s : Finset (PL.E N)} {c : ℝ} {v₀ : PL.E N} (hv₀ : v₀ ∈ s)
    (h : ∀ v ∈ s, ∀ w ∈ s, dist v w ≤ c) {x : PL.E N} (hx : x ∈ PL.simp s) : dist x v₀ ≤ c := by
  obtain ⟨a, ha0, ha1, ha2⟩ := mem_simp_iff.1 hx
  have hsum : (∑ v ∈ s, a v • (v - v₀)) = x - v₀ := by
    rw [← ha2]
    simp only [smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul, ha1, one_smul]
  calc dist x v₀ = ‖x - v₀‖ := dist_eq_norm x v₀
    _ = ‖∑ v ∈ s, a v • (v - v₀)‖ := by rw [hsum]
    _ ≤ ∑ v ∈ s, ‖a v • (v - v₀)‖ := norm_sum_le _ _
    _ = ∑ v ∈ s, a v * dist v v₀ := by
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ha0 v hv), dist_eq_norm]
    _ ≤ ∑ v ∈ s, a v * c :=
      Finset.sum_le_sum fun v hv => mul_le_mul_of_nonneg_left (h v hv v₀ hv₀) (ha0 v hv)
    _ = c := by rw [← Finset.sum_mul, ha1, one_mul]

/-- Uniform continuity of `f` on the space of a finite complex. -/
theorem exists_uniform_radius {Γ : PL.Cx N} (hfin : Γ.faces.Finite) {f : PL.E N → M}
    (hc : ContinuousOn f Γ.space) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ δ > 0, ∀ x ∈ Γ.space, ∀ y ∈ Γ.space, dist x y < δ → dist (f x) (f y) < ρ :=
  Metric.uniformContinuousOn_iff.1
    ((isCompact_space hfin).uniformContinuousOn_of_continuous hc) ρ hρ

/-! ## Transport of `Amb` along a homeomorphism -/

theorem extOverDisc_image (h : M ≃ₜ M) {V : Set M} {j : ℕ} (hV : PL.ExtOverDisc ↥V j) :
    PL.ExtOverDisc ↥(h '' V) j :=
  Work.Cells.Connell.extOverDisc_of_homeomorph (h.image V) hV

theorem amb_image {n p : ℕ} {V : Set M} (A : Work.Engulf.Amb n p M V) (h : M ≃ₜ M) :
    Work.Engulf.Amb n p M (h '' V) where
  hp := A.hp
  loc := A.loc
  connM := A.connM
  Vo := h.isOpenMap V A.Vo
  Vne := A.Vne.image h
  connV := fun j hj => extOverDisc_image h (A.connV j hj)

/-! ## Compactness of the remaining part of `H` -/

/-- If `X ∪ g '' K ⊆ V` then the part of `X ∪ g '' (K ∪ T)` outside `V` is a compact set of
`g '' T`; this is the `Cfg.cpt` hypothesis of the pushed configuration of the outer loop. -/
theorem isCompact_sdiff_of_engulfs {Γ₁ : PL.Cx N} (hfin : Γ₁.faces.Finite) {X : Set M}
    (hX : IsClosed X) {g : PL.E N → M} (hg : ContinuousOn g Γ₁.space) {K T : Set (PL.E N)}
    (hK : IsSubSp Γ₁ K) (hT : IsCompact T) (hTsp : T ⊆ Γ₁.space) {V : Set M}
    (hVo : IsOpen V) (hVK : X ∪ g '' K ⊆ V) : IsCompact ((X ∪ g '' (K ∪ T)) \ V) := by
  have hT' : IsCompact (g '' T) := hT.image_of_continuousOn (hg.mono hTsp)
  have hTK : g '' (K ∪ T) = g '' K ∪ g '' T := image_union _ _ _
  have hclosed : IsClosed (X ∪ g '' (K ∪ T)) := by
    rw [hTK]
    refine hX.union ?_
    exact (((isCompact_of_isSubSp hfin hK).image_of_continuousOn
      (hg.mono hK.subset_space)).union hT').isClosed
  refine hT'.of_isClosed_subset (hclosed.sdiff hVo) ?_
  intro x hx
  simp only [mem_diff] at hx
  obtain ⟨hxF, hxV⟩ := hx
  rw [hTK] at hxF
  rcases hxF with hx | hx
  · exact absurd (hVK (Or.inl hx)) hxV
  · rcases hx with hx | hx
    · exact absurd (hVK (Or.inr hx)) hxV
    · exact hx

/-! ## `IsSubSp` for the faces of the loop -/

theorem isSubSp_iUnion_erase {Γ : PL.Cx N} {σ : Finset (PL.E N)} (hσ : σ ∈ Γ.faces) :
    IsSubSp Γ (⋃ w ∈ σ, PL.simp (σ.erase w)) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.1 hx
    exact Geometry.SimplicialComplex.convexHull_subset_space
      (Γ.down_closed hσ (Finset.erase_subset w σ) (simp_nonempty_iff.1 ⟨x, hxw⟩)) hxw
  · intro x hx
    obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.1 hx
    have hne : (σ.erase w).Nonempty := by
      by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty] at hcon
      rw [hcon, simp_empty] at hxw
      exact hxw
    exact ⟨σ.erase w, Γ.down_closed hσ (Finset.erase_subset w σ) hne, hxw,
      fun y hy => Set.mem_iUnion₂.2 ⟨w, hw, hy⟩⟩

theorem isSubSp_iUnion_erase_of_subset {Γ : PL.Cx N} {σ τ : Finset (PL.E N)} (hσ : σ ∈ Γ.faces)
    (hτ : τ ⊆ σ) (hcard : 2 ≤ σ.card) : IsSubSp Γ (⋃ w ∈ τ, PL.simp (σ.erase w)) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.1 hx
    have hne : (σ.erase w).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hemp
      have h1 := Finset.card_erase_of_mem (hτ hw)
      rw [hemp, Finset.card_empty] at h1
      omega
    exact Geometry.SimplicialComplex.convexHull_subset_space
      (Γ.down_closed hσ (Finset.erase_subset w σ) hne) hxw
  · intro x hx
    obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.1 hx
    have hne : (σ.erase w).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hemp
      have h1 := Finset.card_erase_of_mem (hτ hw)
      rw [hemp, Finset.card_empty] at h1
      omega
    exact ⟨σ.erase w, Γ.down_closed hσ (Finset.erase_subset w σ) hne, hxw,
      fun y hy => Set.mem_iUnion₂.2 ⟨w, hw, hy⟩⟩

theorem isSubSp_skel {Γ : PL.Cx N} {ord : List (Finset (PL.E N))}
    (h : ∀ j (hj : j < ord.length), ord.get ⟨j, hj⟩ ∈ Γ.faces) (i : ℕ) :
    IsSubSp Γ (skel ord i) := by
  induction i with
  | zero => rw [skel_zero]; exact isSubSp_empty Γ
  | succ i ih =>
    rw [skel_succ]
    refine isSubSp_union ih ?_
    by_cases hi : i < ord.length
    · rw [List.getD_eq_get ord ∅ ⟨i, hi⟩]
      exact isSubSp_iUnion_erase (h i hi)
    · rw [List.getD_eq_default ord ∅ (by omega)]
      have h0 : (⋃ w ∈ (∅ : Finset (PL.E N)), PL.simp ((∅ : Finset (PL.E N)).erase w))
          = (∅ : Set (PL.E N)) := by ext x; simp
      rw [h0]
      exact isSubSp_empty Γ

/-- The facets of the first `i` top simplices, as a subcomplex. -/
theorem isSubSp_range_erase {Γ : PL.Cx N} {ord : List (Finset (PL.E N))}
    (h : ∀ j (hj : j < ord.length), ord.get ⟨j, hj⟩ ∈ Γ.faces) (i : ℕ) :
    IsSubSp Γ (⋃ j ∈ Finset.range i, ⋃ w ∈ ord.getD j ∅,
      PL.simp ((ord.getD j ∅).erase w)) := by
  induction i with
  | zero =>
    have h0 : (⋃ j ∈ Finset.range 0, ⋃ w ∈ ord.getD j ∅,
        PL.simp ((ord.getD j ∅).erase w)) = (∅ : Set (PL.E N)) := by
      ext x; simp
    rw [h0]
    exact isSubSp_empty Γ
  | succ i ih =>
    rw [iUnion_range_succ]
    refine isSubSp_union ?_ ih
    by_cases hi : i < ord.length
    · rw [List.getD_eq_get ord ∅ ⟨i, hi⟩]
      exact isSubSp_iUnion_erase (h i hi)
    · rw [List.getD_eq_default ord ∅ (by omega)]
      have h0 : (⋃ w ∈ (∅ : Finset (PL.E N)), PL.simp ((∅ : Finset (PL.E N)).erase w))
          = (∅ : Set (PL.E N)) := by ext x; simp
      rw [h0]
      exact isSubSp_empty Γ

end Work.Engulf.Chain
