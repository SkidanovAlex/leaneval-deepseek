import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.Engulf.Auxi.exists_far_placement
import Submission.Work.Engulf.Auxi.exists_cx_adjunction

namespace Work.Engulf.Aux

/-- **`exists_far_piece`** (contract §8, aux Hx5): a simplex of `ℝᵐ` with at most `N` vertices can be placed in `ℝᴺ` as a new face `Δ'` of a complex `Γ' ⊇ Γ`, far away from the compact `Γ.space`, together with an affine map `A : ℝᴺ →ᵃ[ℝ] ℝᵐ` taking `PL.simp Δ'` onto `PL.simp Δ`.  Used by `E1` and `E4` to add the frozen dominating pieces one at a time.  Suggested proof: take `Δ'` the translate of a set of `Δ.card ≤ N` standard-basis-like points far outside the bounded `Γ.space` (`Metric.isBounded_iff_subset_ball`), `A` the affine map determined by the vertex correspondence on an affine basis, and `Γ' := Geometry.SimplicialComplex.ofErase (Γ.faces ∪ {t | t ⊆ Δ'})`; the complex axioms use `PL.simp Δ' ∩ Γ.space = ∅`. -/
theorem exists_far_piece {N m : ℕ} (Γ : PL.Cx N) (hfin : Γ.faces.Finite) (Δ : Finset (PL.E m))
    (hne : Δ.Nonempty) (hind : AffineIndependent ℝ (fun v : ↥Δ => (v : PL.E m)))
    (hcard : Δ.card ≤ N) :
    ∃ (Γ' : PL.Cx N) (Δ' : Finset (PL.E N)) (A : PL.E N →ᵃ[ℝ] PL.E m),
      Γ'.faces.Finite ∧ Γ.faces ⊆ Γ'.faces ∧ Δ' ∈ Γ'.faces ∧
      (∀ t ∈ Γ'.faces, t ∈ Γ.faces ∨ t ⊆ Δ') ∧
      Γ'.space = Γ.space ∪ PL.simp Δ' ∧ PL.simp Δ' ∩ Γ.space = ∅ ∧
      Δ'.card = Δ.card ∧ A '' (Δ' : Set (PL.E N)) = (Δ : Set (PL.E m)) ∧
      A '' PL.simp Δ' = PL.simp Δ := by
  classical
  -- The space of a finite complex is compact, so it misses a sufficiently far translate.
  have hK : IsCompact Γ.space := by
    rw [Geometry.SimplicialComplex.space]
    exact hfin.isCompact_biUnion fun s _ => (s.finite_toSet).isCompact_convexHull ℝ
  -- Place a far copy `Δ'` of `Δ` in `ℝᴺ`, with an affine map `A` recovering `Δ`.
  obtain ⟨Δ', A, hΔ'ne, hΔ'card, hΔ'aff, hAimg, hAsimp, hdisj⟩ :=
    exists_far_placement Γ hK Δ hne hind hcard
  -- Glue `Δ'` onto `Γ`: the faces are the faces of `Γ` together with the subsets of `Δ'`.
  obtain ⟨Γ', hfin', hsub, hmem, hfaces, hspace⟩ :=
    exists_cx_adjunction Γ hfin Δ' hΔ'aff hΔ'ne hdisj
  exact ⟨Γ', Δ', A, hfin', hsub, hmem, hfaces, hspace, hdisj, hΔ'card, hAimg, hAsimp⟩

end Work.Engulf.Aux
