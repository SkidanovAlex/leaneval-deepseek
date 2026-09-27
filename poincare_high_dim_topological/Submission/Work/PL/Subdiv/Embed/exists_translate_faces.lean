import Mathlib
import Submission.Work.PL.Defs

namespace Work.PL.Subdiv.Embed

open Set Metric
open _root_.PL

noncomputable section

/-- The translation `x ↦ x + v` of `ℝᴺ`, as an affine map. -/
def trAff {N : ℕ} (v : E N) : E N →ᵃ[ℝ] E N where
  toFun := fun x => x + v
  linear := LinearMap.id
  map_vadd' := by intro p w; simp [add_assoc]

@[simp] lemma trAff_apply {N : ℕ} (v x : E N) : trAff v x = x + v := rfl

lemma trAff_injective {N : ℕ} (v : E N) : Function.Injective (trAff v) :=
  fun x y h => add_right_cancel (show x + v = y + v from h)

lemma trAff_image_convexHull {N : ℕ} (v : E N) (s : Finset (E N)) :
    trAff v '' convexHull ℝ (↑s : Set (E N))
      = convexHull ℝ (↑(s.image (fun x => x + v)) : Set (E N)) := by
  rw [AffineMap.image_convexHull, Finset.coe_image]
  rfl

lemma coe_image_inter {N : ℕ} (v : E N) (s t : Finset (E N)) :
    (↑(s.image (fun x => x + v)) ∩ ↑(t.image (fun x => x + v)) : Set (E N))
      = ↑((s ∩ t).image (fun x => x + v)) := by
  rw [← Finset.coe_inter, ← Finset.image_inter s t (add_left_injective v)]

lemma trAff_image_convexHull_inter {N : ℕ} (v : E N) (s t : Finset (E N)) :
    trAff v '' convexHull ℝ (↑s ∩ ↑t : Set (E N))
      = convexHull ℝ (↑(s.image (fun x => x + v)) ∩ ↑(t.image (fun x => x + v))
          : Set (E N)) := by
  rw [← Finset.coe_inter, trAff_image_convexHull v (s ∩ t), ← coe_image_inter v s t]

/-- The image of an affinely independent vertex set under `x ↦ x + v` is affinely independent. -/
lemma affineIndependent_image {N : ℕ} (v : E N) (s : Finset (E N))
    (hs : AffineIndependent ℝ ((↑) : s → E N)) :
    AffineIndependent ℝ ((↑) : ↑(s.image (fun x => x + v)) → E N) := by
  have hg : AffineIndependent ℝ (fun y : s => (y : E N) + v) :=
    AffineIndependent.map' hs (trAff v) (trAff_injective v)
  have hset : Set.range (fun y : s => (y : E N) + v)
      = (↑(s.image (fun x => x + v)) : Set (E N)) := by
    ext x
    simp only [Set.mem_range, Finset.mem_image, SetLike.mem_coe]
    constructor
    · rintro ⟨y, hyx⟩; exact ⟨y, y.2, hyx⟩
    · rintro ⟨a, ha, hax⟩; exact ⟨⟨a, ha⟩, hax⟩
  have hrange := AffineIndependent.range hg
  rw [hset] at hrange
  exact hrange

/-- The translate of a complex `L` by `v`. -/
def translateCx {N : ℕ} (L : PL.Cx N) (v : PL.E N) : PL.Cx N where
  faces := {t | ∃ s ∈ L.faces, t = s.image (fun x => x + v)}
  isRelLowerSet_faces := by
    rintro a ⟨s, hs, rfl⟩
    refine ⟨Finset.image_nonempty.mpr (L.nonempty_of_mem_faces hs), ?_⟩
    rintro b hb hbne
    obtain ⟨u, hus, hbu⟩ := Finset.subset_image_iff.mp hb
    exact ⟨u, L.down_closed hs hus (Finset.image_nonempty.mp (hbu.symm ▸ hbne)), hbu.symm⟩
  indep := by
    rintro t ⟨s, hs, rfl⟩
    exact affineIndependent_image v s (L.indep hs)
  inter_subset_convexHull := by
    rintro s t ⟨s₁, hs₁, rfl⟩ ⟨t₁, ht₁, rfl⟩
    rintro x ⟨hx1, hx2⟩
    rw [← trAff_image_convexHull v s₁] at hx1
    rw [← trAff_image_convexHull v t₁] at hx2
    obtain ⟨y₁, hy₁, hy1⟩ := hx1
    obtain ⟨y₂, hy₂, hy2⟩ := hx2
    have hyeq : y₁ = y₂ := trAff_injective v (by rw [hy1, hy2])
    have hmem : y₁ ∈ convexHull ℝ (↑s₁ ∩ ↑t₁ : Set (E N)) :=
      L.inter_subset_convexHull hs₁ ht₁ ⟨hy₁, hyeq.symm ▸ hy₂⟩
    have hxmem : x ∈ trAff v '' convexHull ℝ (↑s₁ ∩ ↑t₁ : Set (E N)) := ⟨y₁, hmem, hy1⟩
    rw [trAff_image_convexHull_inter v s₁ t₁] at hxmem
    exact hxmem

theorem translateCx_faces {N : ℕ} (L : PL.Cx N) (v : PL.E N) (t : Finset (E N)) :
    t ∈ (translateCx L v).faces ↔ ∃ s ∈ L.faces, t = s.image (fun x => x + v) :=
  Iff.rfl

theorem translateCx_space {N : ℕ} (L : PL.Cx N) (v : PL.E N) :
    (translateCx L v).space = (fun x => x + v) '' L.space := by
  ext x
  rw [Geometry.SimplicialComplex.mem_space_iff]
  constructor
  · rintro ⟨t, ht, hxt⟩
    obtain ⟨s, hs, rfl⟩ := ht
    rw [← trAff_image_convexHull v s] at hxt
    obtain ⟨y, hy, hyx⟩ := hxt
    exact ⟨y, Geometry.SimplicialComplex.convexHull_subset_space hs hy, hyx⟩
  · rintro ⟨y, hy, rfl⟩
    rw [Geometry.SimplicialComplex.mem_space_iff] at hy
    obtain ⟨s, hs, hys⟩ := hy
    refine ⟨s.image (fun x => x + v), ⟨s, hs, rfl⟩, ?_⟩
    rw [← trAff_image_convexHull v s]
    exact ⟨y, hys, rfl⟩

theorem exists_translate_faces {N : ℕ} (L : PL.Cx N) (v : PL.E N) :
    ∃ M : PL.Cx N,
      (∀ t, t ∈ M.faces ↔ ∃ s ∈ L.faces, t = s.image (fun x => x + v)) ∧
      M.space = (fun x => x + v) '' L.space :=
  ⟨translateCx L v, translateCx_faces L v, translateCx_space L v⟩

end

end Work.PL.Subdiv.Embed
