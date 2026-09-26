import Mathlib

namespace Work.Drive.Mono

open scoped Convex

/-- If `p` lies on the affine line `{x + r • v}` with parameter `u`, and `m₁`, `m₂` are two
points of that same line with parameters `s ≤ u ≤ t` and `s < t`, then `p` lies on the
segment `[m₁, m₂]`.  This is the final, purely affine step of
`eq_segment_of_convex_compact_interior_empty`. -/
private lemma mem_segment_of_param {v x m₁ m₂ p : EuclideanSpace ℝ (Fin 2)} {s t u : ℝ}
    (hm₁ : m₁ = s • v +ᵥ x) (hm₂ : m₂ = t • v +ᵥ x) (hp : p = u • v +ᵥ x)
    (hsu : s ≤ u) (hut : u ≤ t) (hst : s < t) :
    p ∈ segment ℝ m₁ m₂ := by
  have hts : t - s ≠ 0 := sub_ne_zero.mpr hst.ne'
  set θ : ℝ := (u - s) / (t - s) with hθ
  have hθmem : θ ∈ Set.Icc (0:ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hsu) (le_of_lt (sub_pos.mpr hst))
    · rw [div_le_one (sub_pos.mpr hst)]
      linarith
  have hdiff : m₂ - m₁ = (t - s) • v := by
    rw [hm₁, hm₂]; simp only [vadd_eq_add]; module
  have hθeq : θ * (t - s) = u - s := by
    rw [hθ]; exact div_mul_cancel₀ _ hts
  have hkey : m₁ + θ • (m₂ - m₁) = p := by
    rw [hdiff, hm₁, hp]
    simp only [vadd_eq_add]
    rw [smul_smul, hθeq]
    module
  rw [segment_eq_image']
  exact ⟨θ, hθmem, hkey⟩

/-- A convex, compact subset of `ℝ²` with empty interior — provided it has at least two
points — is a (nondegenerate) line segment.

The proof separates into two independent halves:
* `C` is collinear.  Since `interior C = ∅`, `Convex.interior_nonempty_iff_affineSpan_eq_top`
  forces `affineSpan ℝ C ≠ ⊤`, hence `vectorSpan ℝ C ≠ ⊤`, hence `finrank ℝ (vectorSpan ℝ C) ≤ 1`
  (the ambient space is two-dimensional), i.e. `Collinear ℝ C`.
* On the resulting line, `C` is parametrised by the numbers `r` with `r • v +ᵥ x ∈ C`; that
  parameter set is closed, convex and bounded, so it is a closed interval, whose endpoints give
  the two segment endpoints.  Concretely we minimise/maximise the affine parameter
  `p ↦ ⟪p - x, v⟫ / ‖v‖²` over the compact set `C`. -/
theorem eq_segment_of_convex_compact_interior_empty {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hCc : Convex ℝ C) (hCcl : IsCompact C) (hCint : interior C = ∅)
    {x y : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y) :
    ∃ m₁ m₂ : EuclideanSpace ℝ (Fin 2), m₁ ≠ m₂ ∧ C = segment ℝ m₁ m₂ := by
  -- Step 1: `C` is collinear.
  have hCne : C.Nonempty := ⟨x, hx⟩
  have hint : ¬ (interior C).Nonempty := Set.not_nonempty_iff_eq_empty.mpr hCint
  have hspan : affineSpan ℝ C ≠ ⊤ := fun h => hint ((hCc.interior_nonempty_iff_affineSpan_eq_top).2 h)
  have hvspan : vectorSpan ℝ C ≠ ⊤ := fun h =>
    hspan ((AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ
      (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) hCne).2 h)
  have hcol : Collinear ℝ C := by
    have hlt : vectorSpan ℝ C < (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin 2))) :=
      lt_of_le_of_ne le_top hvspan
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt
    rw [finrank_top, finrank_euclideanSpace, Fintype.card_fin] at h1
    exact (collinear_iff_finrank_le_one).2 (by omega)
  -- Step 2: parametrise `C` by a real line.
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem (k := ℝ) hx).1 hcol
  obtain ⟨ry, hry⟩ := hv y hy
  have hvne : v ≠ 0 := by
    intro hv0
    rw [hv0] at hry
    simp at hry
    exact hxy hry.symm
  have hry0 : ry ≠ 0 := by
    intro h0
    rw [h0] at hry
    simp at hry
    exact hxy hry.symm
  -- The affine parameter of a point of the line.
  set g : EuclideanSpace ℝ (Fin 2) → ℝ := fun p => (inner ℝ (p - x) v) / ‖v‖ ^ 2 with hg_def
  have hg_cont : Continuous g := by rw [hg_def]; fun_prop
  have hg_line : ∀ r : ℝ, g (r • v +ᵥ x) = r := by
    intro r
    have hv2 : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hvne)
    have h1 : (r • v +ᵥ x) - x = r • v := by rw [vadd_eq_add, add_sub_cancel_right]
    rw [hg_def]
    change (inner ℝ ((r • v +ᵥ x) - x) v) / ‖v‖ ^ 2 = r
    rw [h1, inner_smul_left, real_inner_self_eq_norm_sq]
    simp only [starRingEnd_apply, star_trivial]
    exact mul_div_cancel_right₀ r hv2
  have hgx : g x = 0 := by rw [hg_def]; simp
  have hgy : g y = ry := by rw [hry, hg_line ry]
  -- Extreme points of `C` in the direction of the line.
  obtain ⟨m₁, hm₁C, hm₁min⟩ := hCcl.exists_isMinOn hCne hg_cont.continuousOn
  obtain ⟨m₂, hm₂C, hm₂max⟩ := hCcl.exists_isMaxOn hCne hg_cont.continuousOn
  have hst : g m₁ < g m₂ := by
    rcases lt_or_gt_of_ne hry0 with hneg | hpos
    · have h1 : g m₁ ≤ ry := by rw [← hgy]; exact hm₁min hy
      have h2 : (0:ℝ) ≤ g m₂ := by rw [← hgx]; exact hm₂max hx
      linarith
    · have h1 : g m₁ ≤ 0 := by rw [← hgx]; exact hm₁min hx
      have h2 : ry ≤ g m₂ := by rw [← hgy]; exact hm₂max hy
      linarith
  have hmne : m₁ ≠ m₂ := by
    intro h
    rw [h] at hst
    exact lt_irrefl _ hst
  refine ⟨m₁, m₂, hmne, ?_⟩
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨r, hr⟩ := hv p hp
    have hgp : g p = r := by rw [hr, hg_line r]
    obtain ⟨r₁, hr₁⟩ := hv m₁ hm₁C
    obtain ⟨r₂, hr₂⟩ := hv m₂ hm₂C
    have hgm1 : g m₁ = r₁ := by rw [hr₁, hg_line r₁]
    have hgm2 : g m₂ = r₂ := by rw [hr₂, hg_line r₂]
    have hm₁' : m₁ = g m₁ • v +ᵥ x := by rw [hgm1]; exact hr₁
    have hm₂' : m₂ = g m₂ • v +ᵥ x := by rw [hgm2]; exact hr₂
    have hp' : p = g p • v +ᵥ x := by rw [hgp]; exact hr
    exact mem_segment_of_param hm₁' hm₂' hp' (hm₁min hp) (hm₂max hp) hst
  · exact hCc.segment_subset hm₁C hm₂C

end Work.Drive.Mono
