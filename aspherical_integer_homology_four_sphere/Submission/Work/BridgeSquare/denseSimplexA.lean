import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.BridgeSquare

/-- The set of points of the standard `2`-simplex whose barycentric coordinate at the vertex `1`
is positive is dense in the simplex.  The simplex `Convexity.StdSimplex ℝ (Fin 2)` is homeomorphic
to the unit interval via its coordinate at `1`, and `(0,1]` is dense in `[0,1]`. -/
theorem denseSimplexA : Dense {w : Convexity.StdSimplex ℝ (Fin 2) | 0 < w.weights 1} := by
  -- d = 1 instance: `(0,1]` is dense in `[0,1] = unitInterval`.
  have hD : Dense {x : Set.Icc (0 : ℝ) 1 | 0 < (x : ℝ)} := by
    rw [dense_iff_closure_eq]
    have hsub : Topology.IsInducing (Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ) :=
      Topology.IsEmbedding.subtypeVal.isInducing
    rw [hsub.closure_eq_preimage_closure_image]
    have himg : (Subtype.val '' {x : Set.Icc (0 : ℝ) 1 | 0 < (x : ℝ)}) = Set.Ioc (0 : ℝ) 1 := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨hx, x.2.2⟩
      · rintro ⟨hy1, hy2⟩
        exact ⟨⟨y, ⟨le_of_lt hy1, hy2⟩⟩, hy1, rfl⟩
    rw [himg, closure_Ioc (by norm_num : (0 : ℝ) ≠ 1)]
    exact Set.eq_univ_of_forall (fun x => x.2)
  -- transfer along the homeomorphism `StdSimplex ℝ (Fin 2) ≃ₜ unitInterval`.
  have hD2 :
      Dense (Convexity.StdSimplex.homeomorphI ⁻¹'
        {x : Set.Icc (0 : ℝ) 1 | 0 < (x : ℝ)}) :=
    Dense.preimage hD (Convexity.StdSimplex.homeomorphI.isOpenMap)
  rwa [show Convexity.StdSimplex.homeomorphI ⁻¹'
        {x : Set.Icc (0 : ℝ) 1 | 0 < (x : ℝ)}
        = {w : Convexity.StdSimplex ℝ (Fin 2) | 0 < w.weights 1} from ?_] at hD2
  ext w
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [Convexity.StdSimplex.homeomorphI_apply_coe]

end Work.BridgeSquare
