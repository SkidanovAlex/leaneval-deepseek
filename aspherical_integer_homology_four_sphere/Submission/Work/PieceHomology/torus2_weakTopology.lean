import Mathlib
import Submission.Work.PieceHomology.Torus2Chi

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PieceHomology

/-- The characteristic maps of the two triangles of the standard `Δ`-structure of the `2`-torus,
glued along the disjoint union of the two standard `2`-simplices, give a continuous surjection
onto the torus; since the domain is compact and the torus Hausdorff, the topology of the torus is
its weak topology: a subset whose preimage under every characteristic map is open is open. -/
theorem torus2_weakTopology (s : Set (Fin 2 → AddCircle (1 : ℝ)))
    (h : ∀ (k : ℕ) (σ : Fin (Work.PieceHomology.torus2Card k)),
      IsOpen ((Work.PieceHomology.torus2ChiCls k σ) ⁻¹' s))
    (hcover : ∀ x : Fin 2 → AddCircle (1 : ℝ),
      ∃ σ : Fin 2, ∃ w : Convexity.StdSimplex ℝ (Fin 3), Work.PieceHomology.chiT σ w = x) :
    IsOpen s := by
  -- The two triangle charts, glued along the disjoint union of the two `2`-simplices.
  let Φ : Convexity.StdSimplex ℝ (Fin 3) ⊕ Convexity.StdSimplex ℝ (Fin 3) →
      (Fin 2 → AddCircle (1 : ℝ)) := Sum.elim chiT0 chiT1
  have hcont : Continuous Φ := Continuous.sumElim chiT0.continuous chiT1.continuous
  -- The two closed triangles cover the torus.
  have hsurj : Function.Surjective Φ := by
    intro x
    obtain ⟨σ, w, hw⟩ := hcover x
    fin_cases σ
    · exact ⟨Sum.inl w, by simpa [Φ] using hw⟩
    · exact ⟨Sum.inr w, by simpa [Φ] using hw⟩
  -- Openness of the preimage of `s` under the two charts is precisely the hypothesis `h`.
  have hopen : IsOpen (Φ ⁻¹' s) := by
    have e0 : Sum.inl ⁻¹' (Φ ⁻¹' s) = (torus2ChiCls 2 (0 : Fin 2)) ⁻¹' s := by
      ext a; simp [Φ]
    have e1 : Sum.inr ⁻¹' (Φ ⁻¹' s) = (torus2ChiCls 2 (1 : Fin 2)) ⁻¹' s := by
      ext a; simp [Φ]
    rw [isOpen_sum_iff, e0, e1]
    exact ⟨h 2 (0 : Fin 2), h 2 (1 : Fin 2)⟩
  -- A continuous surjection from a compact space to a Hausdorff space is a quotient map, hence the
  -- topology of the torus is the weak topology of the two charts.
  have hq : Topology.IsQuotientMap Φ :=
    Topology.IsQuotientMap.of_surjective_continuous hsurj hcont
  exact (Topology.isCoinducing_iff.mp hq.isCoinducing s).mp hopen

end Work.PieceHomology
