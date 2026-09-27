import Mathlib
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.Auxi.SimplexCover
import Submission.Work.Engulf.Auxi.face_subset_of_subset_union
import Submission.Work.Engulf.E4Aux.facets_cover_frontier
import Submission.Work.PL.Generic.Hull
import Submission.Work.PL.Generic.GpPairs

/-!
# `Work.Engulf.Alt.Api`

Elementary API for the second, independent proof of Newman's Lemma 7 Case 1 (`E4alt`).
Most of the point-set/combinatorial content is *vendored* from modules of the area that are
already proved (`Submission.Work.Engulf.Chain.E4` is a concurrent attempt which does not build at
the time of writing, so its lemmas are copied here with attribution).
-/

open Set Metric PL

namespace Work.Engulf.Alt

universe u

variable {n p q : ℕ} {M : Type*} [MetricSpace M] {N : ℕ}

/-! ## `IsSubSp` is monotone in the complex -/

theorem space_mono {Γ Γ' : Cx N} (h : Γ.faces ⊆ Γ'.faces) : Γ.space ⊆ Γ'.space := by
  intro x hx
  rw [Geometry.SimplicialComplex.mem_space_iff] at hx ⊢
  obtain ⟨s, hs, hxs⟩ := hx
  exact ⟨s, h hs, hxs⟩

theorem isSubSp_mono {Γ Γ' : Cx N} (h : Γ.faces ⊆ Γ'.faces) {S : Set (E N)}
    (hS : IsSubSp Γ S) : IsSubSp Γ' S :=
  ⟨hS.1.trans (space_mono h), fun x hx => by
    obtain ⟨s, hs, hxs, hsub⟩ := hS.2 x hx
    exact ⟨s, h hs, hxs, hsub⟩⟩

theorem isSubSp_biUnion {Γ : Cx N} {ι : Type*} (u : Finset ι) (S : ι → Set (E N))
    (h : ∀ i ∈ u, IsSubSp Γ (S i)) : IsSubSp Γ (⋃ i ∈ u, S i) := by
  classical
  induction u using Finset.induction_on with
  | empty => simpa using isSubSp_empty Γ
  | insert a u ha ih =>
      have hsplit : (⋃ i ∈ insert a u, S i) = S a ∪ ⋃ i ∈ u, S i := by
        ext x; simp only [Set.mem_iUnion, Finset.mem_insert, exists_prop, Set.mem_union]
        constructor
        · rintro ⟨i, (rfl | hi), hx⟩
          exacts [Or.inl hx, Or.inr ⟨i, hi, hx⟩]
        · rintro (hx | ⟨i, hi, hx⟩)
          exacts [⟨a, Or.inl rfl, hx⟩, ⟨i, Or.inr hi, hx⟩]
      rw [hsplit]
      exact isSubSp_union (h a (Finset.mem_insert_self a u))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem isSubSp_iUnion_simp_erase {Γ : Cx N} {Δ : Finset (E N)} (hΔ : Δ ∈ Γ.faces)
    (T : Finset (E N)) : IsSubSp Γ (⋃ w ∈ T, simp (Δ.erase w)) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · simp only [Set.mem_iUnion, exists_prop] at hx
    obtain ⟨w, _, hxw⟩ := hx
    exact Geometry.SimplicialComplex.convexHull_subset_space hΔ
      (convexHull_mono (by intro y hy; exact Finset.mem_of_mem_erase hy) hxw)
  · simp only [Set.mem_iUnion, exists_prop] at hx
    obtain ⟨w, hw, hxw⟩ := hx
    have hne : (Δ.erase w).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      rw [h, simp_empty] at hxw
      exact hxw
    exact ⟨Δ.erase w, Γ.down_closed hΔ (Finset.erase_subset w Δ) hne, hxw,
      fun y hy => mem_iUnion₂.mpr ⟨w, hw, hy⟩⟩

theorem topOf_isSubSp {Γ : Cx N} {Δ τ₀ τ₁ : Finset (E N)} (hmem : Δ = τ₀ ∪ τ₁)
    (hΔ : Δ ∈ Γ.faces) : IsSubSp Γ (topOf τ₀ τ₁) := by
  subst hmem
  unfold topOf
  exact isSubSp_iUnion_simp_erase hΔ τ₀

theorem floorOf_isSubSp {Γ : Cx N} {Δ τ₀ τ₁ : Finset (E N)} (hmem : Δ = τ₀ ∪ τ₁)
    (hΔ : Δ ∈ Γ.faces) : IsSubSp Γ (floorOf τ₀ τ₁) := by
  subst hmem
  unfold floorOf
  exact isSubSp_iUnion_simp_erase hΔ τ₁

theorem topOf_subset_simp (τ₀ τ₁ : Finset (E N)) :
    topOf τ₀ τ₁ ⊆ simp (τ₀ ∪ τ₁) := by
  intro x hx
  simp only [topOf, Set.mem_iUnion, exists_prop] at hx
  obtain ⟨w, _, hxw⟩ := hx
  exact simp_mono (Finset.erase_subset w _) hxw

theorem floorOf_subset_simp (τ₀ τ₁ : Finset (E N)) :
    floorOf τ₀ τ₁ ⊆ simp (τ₀ ∪ τ₁) := by
  intro x hx
  simp only [floorOf, Set.mem_iUnion, exists_prop] at hx
  obtain ⟨w, _, hxw⟩ := hx
  exact simp_mono (Finset.erase_subset w _) hxw

@[simp] theorem mem_topOf {τ₀ τ₁ : Finset (E N)} {x : E N} :
    x ∈ topOf τ₀ τ₁ ↔ ∃ w ∈ τ₀, x ∈ simp ((τ₀ ∪ τ₁).erase w) := by
  simp [topOf]

@[simp] theorem mem_floorOf {τ₀ τ₁ : Finset (E N)} {x : E N} :
    x ∈ floorOf τ₀ τ₁ ↔ ∃ w ∈ τ₁, x ∈ simp ((τ₀ ∪ τ₁).erase w) := by
  simp [floorOf]

/-! ## `Engulfs` is monotone in the engulfed set and in the budget -/

theorem engulfs_mono_H {V X : Set M} {Γ : Cx N}
    {H H' L : Set (E N)} {f : E N → M} {ε : ℝ} (h : H ⊆ H')
    (he : Engulfs V X Γ H' L f ε) : Engulfs V X Γ H L f ε := by
  obtain ⟨g, hg, hL, hd, hh, hsup, heng⟩ := he
  refine ⟨g, hg, hL, hd, hh, hsup, ?_⟩
  rintro z (hz | ⟨y, hy, rfl⟩)
  · exact heng (Or.inl hz)
  · exact heng (Or.inr ⟨y, h hy, rfl⟩)

theorem engulfs_mono_V {V V' X : Set M} {Γ : Cx N}
    {H L : Set (E N)} {f : E N → M} {ε : ℝ} (h : V ⊆ V')
    (he : Engulfs V X Γ H L f ε) : Engulfs V' X Γ H L f ε := by
  obtain ⟨g, hg, hL, hd, hh, hsu, hen⟩ := he
  exact ⟨g, hg, hL, hd, hh, hsu, fun z hz => Set.image_mono h (hen hz)⟩

theorem engulfs_of_subdivides {Γ Γ' : Cx N}
    {V X : Set M} {H L : Set (E N)} {f : E N → M} {ε : ℝ} (h : Subdivides Γ' Γ)
    (he : Engulfs V X Γ' H L f ε) : Engulfs V X Γ H L f ε := by
  obtain ⟨g, hg, hL, hd, hh, hsu, hen⟩ := he
  rw [h.1] at hg hd
  exact ⟨g, hg, hL, hd, hh, hsu, hen⟩

/-! ## The `τ₀`-side of a simplex is inside the union of the facets of any
full-dimensional family covering it -/

theorem topOf_subset_skeleton {τ₀ τ₁ : Finset (E N)} (ord : List (Finset (E N)))
    (hne : (τ₀ ∪ τ₁).Nonempty) (hind : AffineIndependent ℝ (fun v : ↥(τ₀ ∪ τ₁) => (v : E N)))
    (hfin : ∀ t ∈ ord, AffineIndependent ℝ (fun v : ↥t => (v : E N)))
    (hsub : ∀ t ∈ ord, simp t ⊆ simp (τ₀ ∪ τ₁))
    (hcard : ∀ t ∈ ord, t.card = (τ₀ ∪ τ₁).card)
    (hcover : simp (τ₀ ∪ τ₁) ⊆ ⋃ t ∈ ord, simp t) :
    topOf τ₀ τ₁ ⊆ ⋃ t ∈ ord, ⋃ w ∈ t, simp (t.erase w) := by
  intro x hx
  rw [mem_topOf] at hx
  obtain ⟨w, hw, hxw⟩ := hx
  exact Work.Engulf.E4Aux.facets_cover_frontier ord hne hind hfin hsub hcard hcover w
    (Finset.mem_union_left τ₁ hw) hxw

/-! ## `hcol` for `GPaForm` -/

theorem hullOf_inter_subset {ι : Type*} [DecidableEq ι] (y : ι → E n)
    (σ lm fz : Finset ι)
    (hind : AffineIndependent ℝ (fun v : ↥((σ ∪ lm) ∩ fz) => y v)) :
    Work.PL.Generic.hullOf y (σ ∩ fz) ∩ Work.PL.Generic.hullOf y (lm ∩ fz) ⊆
      Work.PL.Generic.hullOf y (σ ∩ lm ∩ fz) := by
  classical
  intro x hx
  obtain ⟨hxσ, hxlm⟩ := hx
  obtain ⟨a, ha0, ha1, hax⟩ := (Work.PL.Generic.mem_hullOf y (σ ∩ fz) x).1 hxσ
  obtain ⟨b, hb0, hb1, hbx⟩ := (Work.PL.Generic.mem_hullOf y (lm ∩ fz) x).1 hxlm
  set π : Finset ι := (σ ∪ lm) ∩ fz with hπ
  have hsub_a : σ ∩ fz ⊆ π := by
    intro v hv
    exact Finset.mem_inter.mpr ⟨Finset.mem_union_left lm (Finset.mem_inter.mp hv).1,
      (Finset.mem_inter.mp hv).2⟩
  have hsub_b : lm ∩ fz ⊆ π := by
    intro v hv
    exact Finset.mem_inter.mpr ⟨Finset.mem_union_right σ (Finset.mem_inter.mp hv).1,
      (Finset.mem_inter.mp hv).2⟩
  set a' : ι → ℝ := fun v => if v ∈ σ ∩ fz then a v else 0 with ha'
  set b' : ι → ℝ := fun v => if v ∈ lm ∩ fz then b v else 0 with hb'
  have ha'_eq : ∀ v ∈ σ ∩ fz, a' v = a v := by
    intro v hv; simp only [ha']; exact if_pos hv
  have hb'_eq : ∀ v ∈ lm ∩ fz, b' v = b v := by
    intro v hv; simp only [hb']; exact if_pos hv
  have hsum_a : ∑ v ∈ π, a' v = 1 := by
    have h1 : ∑ v ∈ σ ∩ fz, a' v = ∑ v ∈ π, a' v :=
      Finset.sum_subset hsub_a (fun v _ hvn => by simp only [ha']; exact if_neg hvn)
    rw [← h1, Finset.sum_congr rfl ha'_eq, ha1]
  have hsum_b : ∑ v ∈ π, b' v = 1 := by
    have h1 : ∑ v ∈ lm ∩ fz, b' v = ∑ v ∈ π, b' v :=
      Finset.sum_subset hsub_b (fun v _ hvn => by simp only [hb']; exact if_neg hvn)
    rw [← h1, Finset.sum_congr rfl hb'_eq, hb1]
  have hsum_y_a : ∑ v ∈ π, a' v • y v = x := by
    have h1 : ∑ v ∈ σ ∩ fz, a' v • y v = ∑ v ∈ π, a' v • y v :=
      Finset.sum_subset hsub_a (fun v _ hvn => by
        simp only [ha']; rw [if_neg hvn, zero_smul])
    rw [← h1, Finset.sum_congr rfl (fun v hv => by rw [ha'_eq v hv]), hax]
  have hsum_y_b : ∑ v ∈ π, b' v • y v = x := by
    have h1 : ∑ v ∈ lm ∩ fz, b' v • y v = ∑ v ∈ π, b' v • y v :=
      Finset.sum_subset hsub_b (fun v _ hvn => by
        simp only [hb']; rw [if_neg hvn, zero_smul])
    rw [← h1, Finset.sum_congr rfl (fun v hv => by rw [hb'_eq v hv]), hbx]
  have heq := Work.PL.Generic.eq_of_sum_smul_eq_of_affineIndependent hind hsum_a hsum_b (by
    rw [hsum_y_a, hsum_y_b])
  have hsupp : ∀ v ∈ σ ∩ fz, v ∉ σ ∩ lm ∩ fz → a v = 0 := by
    intro v hv hvn
    by_contra hne
    have hbv : b' v = a v := by rw [← heq v (hsub_a hv), ha'_eq v hv]
    have hmemlm : v ∈ lm ∩ fz := by
      by_contra hcon
      have h0 : b' v = 0 := by simp only [hb']; exact if_neg hcon
      rw [h0] at hbv
      exact hne hbv.symm
    exact hvn (Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1,
      (Finset.mem_inter.mp hmemlm).1⟩, (Finset.mem_inter.mp hv).2⟩)
  have hsub3 : σ ∩ lm ∩ fz ⊆ σ ∩ fz := by
    intro v hv
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hv).1).1,
      (Finset.mem_inter.mp hv).2⟩
  refine (Work.PL.Generic.mem_hullOf y (σ ∩ lm ∩ fz) x).2
    ⟨fun v => if v ∈ σ ∩ lm ∩ fz then a v else 0, ?_, ?_, ?_⟩
  · intro v hv
    simp only [if_pos hv]
    exact ha0 v (hsub3 hv)
  · have h1 : ∑ v ∈ σ ∩ lm ∩ fz, (if v ∈ σ ∩ lm ∩ fz then a v else 0)
        = ∑ v ∈ σ ∩ fz, a v := by
      rw [Finset.sum_subset hsub3 (fun v _ hvn => if_neg hvn)]
      exact Finset.sum_congr rfl (fun v hv => by
        by_cases h : v ∈ σ ∩ lm ∩ fz
        · rw [if_pos h]
        · rw [if_neg h, hsupp v hv h])
    rw [h1, ha1]
  · have h1 : ∑ v ∈ σ ∩ lm ∩ fz, (if v ∈ σ ∩ lm ∩ fz then a v else 0) • y v
        = ∑ v ∈ σ ∩ fz, a v • y v := by
      rw [Finset.sum_subset hsub3 (fun v _ hvn => by rw [if_neg hvn, zero_smul])]
      exact Finset.sum_congr rfl (fun v hv => by
        by_cases h : v ∈ σ ∩ lm ∩ fz
        · rw [if_pos h]
        · rw [if_neg h, hsupp v hv h, zero_smul])
    rw [h1, hax]

/-! ## Chart API -/

variable {M₀ : Type*} [TopologicalSpace M₀]

theorem CubeChart.image_openCube_mono (ψ : CubeChart n M₀) {r r' : ℝ} (h : r ≤ r') :
    ψ.toFun '' openCube r ⊆ ψ.toFun '' openCube r' :=
  Set.image_mono (openCube_mono h)

theorem CubeChart.image_closedCube_subset_image_openCube (ψ : CubeChart n M₀)
    {r r' : ℝ} (h : r < r') :
    ψ.toFun '' closedCube r ⊆ ψ.toFun '' openCube r' :=
  Set.image_mono (closedCube_subset_openCube h)

theorem CubeChart.image_openCube_subset_image_closedCube (ψ : CubeChart n M₀) (r : ℝ) :
    ψ.toFun '' openCube r ⊆ ψ.toFun '' closedCube r :=
  Set.image_mono (openCube_subset_closedCube r)

theorem CubeChart.eq_of_image_eq (ψ : CubeChart n M₀) {x y : E n} (hx : x ∈ openCube 1)
    (hy : y ∈ openCube 1) (h : ψ.toFun x = ψ.toFun y) : x = y := by
  have h' : (openCube (n := n) 1).domRestrict ψ.toFun ⟨x, hx⟩
      = (openCube (n := n) 1).domRestrict ψ.toFun ⟨y, hy⟩ := h
  exact congrArg Subtype.val (ψ.emb.toIsEmbedding.injective h')

/-- A face of a subdivision has at most as many vertices as a coarser face containing its simplex
(the vertices of a face are affinely independent and lie in the affine span of the coarse face). -/
theorem card_le_of_simp_subset {N : ℕ} {Γ Γ' : Cx N} {s' : Finset (E N)} {s : Finset (E N)}
    (hs' : s' ∈ Γ'.faces) (hs : s ∈ Γ.faces) (hsub : simp s' ⊆ simp s) : s'.card ≤ s.card := by
  have hne' : s'.Nonempty := Γ'.nonempty_of_mem_faces hs'
  have hne : s.Nonempty := Γ.nonempty_of_mem_faces hs
  have hind' : AffineIndependent ℝ (fun v : ↥s' => (v : E N)) := Γ'.indep hs'
  have hind : AffineIndependent ℝ (fun v : ↥s => (v : E N)) := Γ.indep hs
  have hle : affineSpan ℝ (s' : Set (E N)) ≤ affineSpan ℝ (s : Set (E N)) := by
    rw [affineSpan_le]
    intro x hx
    exact convexHull_subset_affineSpan (𝕜 := ℝ) (s := (s : Set (E N)))
      (hsub (subset_convexHull ℝ (s' : Set (E N)) hx))
  have h1 : vectorSpan ℝ (s' : Set (E N)) ≤ vectorSpan ℝ (s : Set (E N)) := by
    rw [← direction_affineSpan, ← direction_affineSpan]
    exact AffineSubspace.direction_le hle
  have h2 : Module.finrank ℝ ↥(vectorSpan ℝ (s' : Set (E N)))
      ≤ Module.finrank ℝ ↥(vectorSpan ℝ (s : Set (E N))) := Submodule.finrank_mono h1
  have hc' : Fintype.card ↥s' = (s'.card - 1) + 1 := by
    rw [Fintype.card_coe]
    exact (Nat.sub_add_cancel (Finset.card_pos.mpr hne')).symm
  have hc : Fintype.card ↥s = (s.card - 1) + 1 := by
    rw [Fintype.card_coe]
    exact (Nat.sub_add_cancel (Finset.card_pos.mpr hne)).symm
  have hf' := hind'.finrank_vectorSpan (n := s'.card - 1) hc'
  have hf := hind.finrank_vectorSpan (n := s.card - 1) hc
  rw [Work.Engulf.E4Aux.range_subtype_val_coe] at hf' hf
  rw [hf', hf] at h2
  have h3 : s'.card - 1 ≤ s.card - 1 := h2
  have h4 : 0 < s'.card := Finset.card_pos.mpr hne'
  have h6 : 0 < s.card := Finset.card_pos.mpr hne
  omega

end Work.Engulf.Alt
