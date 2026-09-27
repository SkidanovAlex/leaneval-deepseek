import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.Engulf.Tools

/-!
# `Work.Engulf.E4P.Basic` — elementary lemmas for the piece loop

* `card_le_of_convexHull_subset` : if the convex hull of an affinely independent finite vertex set
  `s` is contained in the convex hull of an affinely independent `t`, then `s.card ≤ t.card`
  (the `DimLE` transfer of `dimLE_of_subdivides` uses it for the faces of a refinement).
-/

open Set Metric PL

namespace Work.Engulf.E4P

/-- The convex hulls of two affinely independent finite vertex sets: containment forces the
cardinality bound.  (Proof by the dimension of the affine span.) -/
theorem card_le_of_convexHull_subset {N : ℕ} {s t : Finset (E N)}
    (hs : AffineIndependent ℝ (fun v : ↥s => (v : E N)))
    (ht : AffineIndependent ℝ (fun v : ↥t => (v : E N)))
    (h : convexHull ℝ (s : Set (E N)) ⊆ convexHull ℝ (t : Set (E N))) :
    s.card ≤ t.card := by
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · simp
  have htne : t.Nonempty := by
    obtain ⟨x, hx⟩ := hsne
    have h1 : (convexHull ℝ (t : Set (E N))).Nonempty :=
      ⟨x, h (subset_convexHull ℝ (s : Set (E N)) hx)⟩
    have h2 : (t : Set (E N)).Nonempty := (convexHull_nonempty_iff (𝕜 := ℝ)).mp h1
    rwa [Finset.coe_nonempty] at h2
  have hranges : Set.range (fun v : ↥s => (v : E N)) = (s : Set (E N)) := by
    ext x; constructor
    · rintro ⟨v, rfl⟩; exact v.2
    · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
  have hranget : Set.range (fun v : ↥t => (v : E N)) = (t : Set (E N)) := by
    ext x; constructor
    · rintro ⟨v, rfl⟩; exact v.2
    · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
  have hle : affineSpan ℝ ((s : Set (E N))) ≤ affineSpan ℝ ((t : Set (E N))) := by
    refine affineSpan_le.mpr ?_
    intro x hx
    exact convexHull_subset_affineSpan (t : Set (E N))
      (h (subset_convexHull ℝ (s : Set (E N)) hx))
  have hdir : (affineSpan ℝ ((s : Set (E N)))).direction ≤
      (affineSpan ℝ ((t : Set (E N)))).direction :=
    AffineSubspace.direction_le hle
  rw [direction_affineSpan, direction_affineSpan] at hdir
  have hfin : Module.finrank ℝ (vectorSpan ℝ ((s : Set (E N)))) ≤
      Module.finrank ℝ (vectorSpan ℝ ((t : Set (E N)))) :=
    Submodule.finrank_mono hdir
  have h1 : Module.finrank ℝ (vectorSpan ℝ ((s : Set (E N)))) + 1 = s.card := by
    haveI : Nonempty ↥s := ⟨⟨hsne.choose, hsne.choose_spec⟩⟩
    have h2 := hs.finrank_vectorSpan_add_one (k := ℝ)
    rw [hranges, Fintype.card_coe] at h2
    exact h2
  have h2 : Module.finrank ℝ (vectorSpan ℝ ((t : Set (E N)))) + 1 = t.card := by
    haveI : Nonempty ↥t := ⟨⟨htne.choose, htne.choose_spec⟩⟩
    have h3 := ht.finrank_vectorSpan_add_one (k := ℝ)
    rw [hranget, Fintype.card_coe] at h3
    exact h3
  omega

/-- An affine equivalence `E n ≃ᵃ ℝ Pr a q` can only exist if `q + 1 ≤ n` (the two spaces have
the same dimension, `n = a + q + 1` with `a = n - q - 1`).  Used to discharge the dimension
condition of `exists_pieces_list` in `piecesEngulfG`, where only `Φ` is given. -/
theorem q_add_one_le_of_affineEquiv {n q a : ℕ} (T : E n ≃ᵃ[ℝ] Pr a q) : q + 1 ≤ n := by
  have hbij : Function.Bijective (T : E n →ᵃ[ℝ] Pr a q) := ⟨T.injective, T.surjective⟩
  have hlin : Function.Bijective (T : E n →ᵃ[ℝ] Pr a q).linear :=
    (AffineMap.linear_bijective_iff (T : E n →ᵃ[ℝ] Pr a q)).mpr hbij
  let e : E n ≃ₗ[ℝ] Pr a q := LinearEquiv.ofBijective _ hlin
  have hf : Module.finrank ℝ (E n) = Module.finrank ℝ (Pr a q) := e.finrank_eq
  rw [finrank_euclideanSpace, Module.finrank_prod, finrank_euclideanSpace, Module.finrank_prod,
    finrank_euclideanSpace, Module.finrank_self] at hf
  simp only [Fintype.card_fin] at hf
  omega

end Work.Engulf.E4P
