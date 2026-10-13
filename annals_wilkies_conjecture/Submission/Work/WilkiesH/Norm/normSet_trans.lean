import Mathlib
import Submission.Work.WilkiesH.Norm.Defs
import Submission.Work.WilkiesH.Basic
import Submission.Work.WilkiesH.Norm.isSemialgebraic_preimage_normMap
import Submission.Work.WilkiesH.Norm.continuousOn_normMap_normSet

/-!
# Normalisation does not create algebraic (positive-dimensional) parts

`X.trans = X \ X.alg` is the *transcendental* part of `X`, where `X.alg` is the union of all
connected infinite semialgebraic subsets of `X` (BNZ §6, see `ChallengeDeps.lean`).

The point of this file is that the normalisation `normMap σ` — which is *not* a homeomorphism of
`ℝⁿ`, since inversion is discontinuous at `0` — nevertheless transports the transcendental part
correctly *along the pieces*: a point of `T ∩ normPiece σ` with `T ⊆ X.trans` is mapped into
`(normSet σ X).trans`.

The three structural facts about `normMap σ` used are

* `normMap σ` is an **involution** of `ℝⁿ` (`normMap_normMap` below): each of the four coordinate
  maps `id`, `-id`, `·⁻¹`, `-·⁻¹` is its own inverse.  Consequently
  `normMap σ ⁻¹' Y = normMap σ '' Y`, and, importantly, if `normMap σ z ∈ normSet σ X` then
  `z ∈ X`: writing `normMap σ z = normMap σ w` with `w ∈ X ∩ normPiece σ`, applying the
  involution gives `z = w`.  (This is where the *four* shapes — as opposed to the two shapes
  "`|x| ≤ 1`" and "`|x| > 1`" — are used: the sign of a coordinate is recoverable from the
  normalised value only because the piece records it.)
* `Work.WilkiesH.Norm.isSemialgebraic_preimage_normMap` — `normMap σ` is semialgebraic, so it
  pulls semialgebraic sets back to semialgebraic sets;
* `Work.WilkiesH.Norm.continuousOn_normMap_normSet` — `normMap σ` is continuous on `normSet σ X`
  (on the image of a piece the "big" coordinates are non-zero, so inversion is continuous there).

Putting these together: if `y = normMap σ t` lay in `(normSet σ X).alg`, there would be a
connected infinite semialgebraic `Y ∋ y` inside `normSet σ X`; its preimage `Z = normMap σ ⁻¹' Y`
is then semialgebraic, infinite and connected, contains `t`, and is contained in `X` — so
`t ∈ X.alg`, contradicting `t ∈ X.trans`.

## Main result

* `normSet_trans` — `normMap σ '' (T ∩ normPiece σ) ⊆ (normSet σ X).trans` for `T ⊆ X.trans`.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkiesH.Norm

open WilkiesConjecture

/-! ## `normMap σ` is an involution of `ℝⁿ` -/

private theorem shapeMap_shapeMap (s : NormShape) (t : ℝ) : shapeMap s (shapeMap s t) = t := by
  cases s <;> simp [shapeMap, inv_inv]

/-- Each coordinate map is its own inverse, hence so is `normMap σ`. -/
private theorem normMap_normMap {n : ℕ} (σ : Fin n → NormShape) (x : Fin n → ℝ) :
    normMap σ (normMap σ x) = x := by
  funext i
  simp [normMap, shapeMap_shapeMap]

/-- Preimages under the involutive map `normMap σ` are images. -/
private theorem normMap_preimage_eq_image {n : ℕ} (σ : Fin n → NormShape)
    (Y : Set (Fin n → ℝ)) : (normMap σ) ⁻¹' Y = normMap σ '' Y := by
  ext z
  constructor
  · intro hz
    exact ⟨normMap σ z, hz, normMap_normMap σ z⟩
  · rintro ⟨y, hy, rfl⟩
    show normMap σ (normMap σ y) ∈ Y
    rw [normMap_normMap]
    exact hy

/-! ## The main lemma -/

/-- **Normalisation respects the transcendental part.**  If `T ⊆ X.trans`, then the normalised
image of the piece of `T` lying in `normPiece σ` is contained in the transcendental part of the
normalised `X`. -/
theorem normSet_trans {n : ℕ} {σ : Fin n → NormShape} {X T : Set (Fin n → ℝ)}
    (hT : T ⊆ X.trans) :
    normMap σ '' (T ∩ normPiece σ) ⊆ (normSet σ X).trans := by
  rintro y ⟨t, ⟨htT, htPiece⟩, rfl⟩
  have htT' : t ∈ X ∧ t ∉ X.alg := WilkiesH.mem_trans_iff.mp (hT htT)
  refine ⟨⟨t, ⟨htT'.1, htPiece⟩, rfl⟩, ?_⟩
  intro hmem
  -- a connected infinite semialgebraic `Y ∋ normMap σ t` inside `normSet σ X`
  obtain ⟨Y, hYsub, hYsem, hYinf, hYcon, hYmem⟩ := WilkiesH.mem_alg_iff.mp hmem
  -- its preimage is a witness inside `X`
  have hZsub : (normMap σ) ⁻¹' Y ⊆ X := by
    intro z hz
    obtain ⟨w, ⟨hwX, _⟩, hwe⟩ := hYsub hz
    have hzw : z = w := by
      rw [← normMap_normMap σ z, ← hwe, normMap_normMap σ w]
    rw [hzw]
    exact hwX
  have hZsem : IsSemialgebraic ((normMap σ) ⁻¹' Y) :=
    isSemialgebraic_preimage_normMap σ hYsem
  have hZcon : IsConnected ((normMap σ) ⁻¹' Y) := by
    rw [normMap_preimage_eq_image]
    exact hYcon.image _ ((continuousOn_normMap_normSet σ X).mono hYsub)
  have hZinf : ((normMap σ) ⁻¹' Y).Infinite := by
    rw [normMap_preimage_eq_image]
    refine hYinf.image ?_
    intro a _ b _ hab
    calc a = normMap σ (normMap σ a) := (normMap_normMap σ a).symm
      _ = normMap σ (normMap σ b) := by rw [hab]
      _ = b := normMap_normMap σ b
  exact htT'.2 (WilkiesH.subset_alg_of_semialg hZsub hZsem hZinf hZcon hYmem)

end Work.WilkiesH.Norm
