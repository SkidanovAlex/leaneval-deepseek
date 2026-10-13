import Mathlib
import Submission.Work.WilkiesH.Defs

/-!
# Monotonicity of the dimension bound `DimLE`

`WilkieDesign.DimLE X μ` says, o-minimally, that `dim X ≤ μ`: every projection of
`X` to `μ + 1` coordinates has empty interior.  We prove that this notion is
monotone in `μ`: `DimLE X μ → DimLE X μ'` for `μ ≤ μ'`.

The mathematical content is that the *coordinate projection*
`ℝ^{μ'+1} → ℝ^{μ+1}` (keep the first `μ+1` coordinates) is an **open map**: if a
set has nonempty interior then so does its projection.  Indeed, if `A ⊆ ℝ^{μ'+1}`
contains a box, the projection contains the box in the first `μ+1` coordinates,
and conversely every point of that smaller box is the projection of a point of the
larger box (fill the remaining coordinates with the fixed centre).

So: given `e' : Fin (μ'+1) ↪ Fin n`, precomposing with the coordinate inclusion
`Fin (μ+1) ↪ Fin (μ'+1)` turns the `μ'+1`-coordinate projection into the
`μ+1`-coordinate projection of `DimLE X μ`, which has empty interior; since the
coordinate projection is open, the larger projection has empty interior too.
-/

namespace Work.WilkiesH.Dim

/-- Coordinate projection (keeping the first `m` of `k` coordinates) is an open
map `ℝ^k → ℝ^m`.  Both spaces carry the product topology, so it suffices to check
that the image of a basic box is the corresponding box: given a box `Π_{a} u a`
around `y`, the projected box `Π_{i<m} u (castLE h i)` lies in the image (drop
the coordinates `≥ m`, and for the coordinates `< m` pick the corresponding
coordinate of the given point). -/
lemma restrict_isOpenMap_aux {m k : ℕ} (h : m ≤ k) :
    IsOpenMap (fun (y : Fin k → ℝ) => fun i : Fin m => y (Fin.castLE h i)) := by
  intro U hU
  rw [isOpen_pi_iff']
  intro z hz
  obtain ⟨y, hyU, rfl⟩ := hz
  rw [isOpen_pi_iff'] at hU
  obtain ⟨u, hu, hsub⟩ := hU y hyU
  -- project the box `Π u` around `y` to the box `Π_{i<m} u (castLE h i)`
  refine ⟨fun i => u (Fin.castLE h i),
    fun i => ⟨(hu (Fin.castLE h i)).1, (hu (Fin.castLE h i)).2⟩, ?_⟩
  intro z' hz'
  have hz'm : ∀ i, z' i ∈ u (Fin.castLE h i) := fun i => Set.mem_univ_pi.mp hz' i
  -- fill the coordinates `≥ m` with those of `y`
  refine ⟨fun k' => if hk : k'.val < m then z' ⟨k'.val, hk⟩ else y k', ?_, ?_⟩
  · apply hsub
    intro k' _
    dsimp only
    by_cases hk : k'.val < m
    · rw [dite_eq_left hk]
      have hh := hz'm ⟨k'.val, hk⟩
      simpa using hh
    · rw [dite_eq_right hk]
      exact (hu k').2
  · funext i
    dsimp only
    rw [dite_eq_left (show (Fin.castLE h i).val < m from by rw [Fin.castLE]; exact i.isLt)]
    congr 1

theorem dimLE_mono {n μ μ' : ℕ} {X : Set (Fin n → ℝ)} (h : WilkiesDesign.DimLE X μ) (hμ : μ ≤ μ') : WilkiesDesign.DimLE X μ' := by
  intro e'
  have hle : μ + 1 ≤ μ' + 1 := Nat.succ_le_succ hμ
  -- the sub-embedding `Fin (μ+1) ↪ Fin n` obtained by ignoring the extra coordinates
  let e : Fin (μ + 1) ↪ Fin n := ⟨fun i => e' (Fin.castLE hle i), fun a b hab =>
    Fin.castLE_injective hle (e'.injective hab)⟩
  have hh : interior ((fun x : Fin n → ℝ => x ∘ e) '' X) = ∅ := h e
  let A : Set (Fin (μ' + 1) → ℝ) := (fun x : Fin n → ℝ => x ∘ e') '' X
  let π : (Fin (μ' + 1) → ℝ) → (Fin (μ + 1) → ℝ) := fun y => fun i => y (Fin.castLE hle i)
  -- the `π`-image of `A` is the `μ+1`-coordinate projection of `X`
  have himg : π '' A = (fun x : Fin n → ℝ => x ∘ e) '' X := by
    ext w
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, hyw⟩
      refine ⟨x, hx, ?_⟩
      rw [← hyw]
      rfl
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x ∘ e', ⟨x, hx, rfl⟩, rfl⟩
  by_contra hne
  have hne' : (interior A).Nonempty := Set.nonempty_iff_ne_empty.mpr hne
  -- an open map sends sets with nonempty interior to sets with nonempty interior
  have hsub : π '' interior A ⊆ interior (π '' A) :=
    interior_maximal (Set.image_mono interior_subset)
      (restrict_isOpenMap_aux hle (interior A) isOpen_interior)
  have hempty : interior (π '' A) = ∅ := by rw [himg]; exact hh
  obtain ⟨z, hz⟩ := hne'.image π
  have hz2 : z ∈ interior (π '' A) := hsub hz
  rw [hempty] at hz2
  exact hz2

end Work.WilkiesH.Dim
