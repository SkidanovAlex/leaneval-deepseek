import Mathlib
import Submission.Work.RatHurewicz.PairFibre

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `pairShiftHom` is an isomorphism

The curried map `pairShiftHom i a₀ m : π_{m+2}(X, i a₀) →* π_{m+1}(F)` (the loop space shift
composed with the identification of the loop space `ΩX` with the fibre `F` of the projection
`homotopyFibreFst i a₀`, see `Submission/Work/RatHurewicz/PairFibre.lean`) is an isomorphism: it is
the composite of the multiplicative equivalence `stepMulEquiv m` with the map induced by the
continuous map `fibrePsi i a₀`, whose two-sided inverse is `fibrePhi i a₀`.

The proof is the standard one: `fibrePhi_fibrePsi` and `fibrePsi_fibrePhi` say that the two
composites are the identity functions, so by `πmap_comp_apply`, `πmap_congr`, `πmap_id_apply` the
induced maps on homotopy groups are mutually inverse up to the transport `homotopyGroupCast` along
the corresponding base point equalities.
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.RatHurewicz

open Work.StemsB

noncomputable section

variable {X : Type} [TopologicalSpace X] {A : Type} [TopologicalSpace A]

/-- **The map induced by `fibrePsi` on homotopy groups is a bijection.** -/
theorem fibrePsi_πmap_bijective (i : C(A, X)) (a₀ : A) (m : ℕ) :
    Function.Bijective (πmap (fibrePsi i a₀) m (Path.refl (i a₀))) := by
  have hcomp₁ : (fibrePhi i a₀).comp (fibrePsi i a₀) = ContinuousMap.id (Path (i a₀) (i a₀)) := by
    apply ContinuousMap.ext
    intro γ
    exact fibrePhi_fibrePsi i a₀ γ
  have hcomp₂ : (fibrePsi i a₀).comp (fibrePhi i a₀) = ContinuousMap.id (fibreOf i a₀) := by
    apply ContinuousMap.ext
    intro e
    exact fibrePsi_fibrePhi i a₀ e
  -- the two composites are the identity, up to transports
  have key₁ : ∀ a : HomotopyGroup (Fin (m + 1)) (Path (i a₀) (i a₀)) (Path.refl (i a₀)),
      homotopyGroupCast
          (congrArg (fun k : C(Path (i a₀) (i a₀), Path (i a₀) (i a₀)) => k (Path.refl (i a₀)))
            hcomp₁) m
        (πmap (fibrePhi i a₀) m (fibrePsi i a₀ (Path.refl (i a₀)))
          (πmap (fibrePsi i a₀) m (Path.refl (i a₀)) a)) = a := by
    intro a
    rw [← πmap_comp_apply]
    exact (πmap_congr hcomp₁ m (Path.refl (i a₀)) a).trans
      (πmap_id_apply m (Path.refl (i a₀)) a)
  have key₂ : ∀ z : HomotopyGroup (Fin (m + 1)) (fibreOf i a₀)
        (fibrePsi i a₀ (Path.refl (i a₀))),
      homotopyGroupCast
          (congrArg (fun k : C(fibreOf i a₀, fibreOf i a₀) =>
            k (fibrePsi i a₀ (Path.refl (i a₀)))) hcomp₂) m
        (πmap ((fibrePsi i a₀).comp (fibrePhi i a₀)) m (fibrePsi i a₀ (Path.refl (i a₀)))
          z) = z := by
    intro z
    exact (πmap_congr hcomp₂ m (fibrePsi i a₀ (Path.refl (i a₀))) z).trans
      (πmap_id_apply m (fibrePsi i a₀ (Path.refl (i a₀))) z)
  refine ⟨?_, ?_⟩
  · -- injectivity
    intro a b hab
    have h3 := congrArg (fun t => homotopyGroupCast
      (congrArg (fun k : C(Path (i a₀) (i a₀), Path (i a₀) (i a₀)) => k (Path.refl (i a₀)))
        hcomp₁) m
      (πmap (fibrePhi i a₀) m (fibrePsi i a₀ (Path.refl (i a₀))) t)) hab
    exact (key₁ a).symm.trans (h3.trans (key₁ b))
  · -- surjectivity
    intro z
    refine ⟨homotopyGroupCast (fibrePhi_fibrePsi i a₀ (Path.refl (i a₀))) m
      (πmap (fibrePhi i a₀) m (fibrePsi i a₀ (Path.refl (i a₀))) z), ?_⟩
    -- the two base point equalities `fibrePhi (fibrePsi refl) = refl` are the same proposition
    have hcast : congrArg (fibrePsi i a₀) (fibrePhi_fibrePsi i a₀ (Path.refl (i a₀)))
        = congrArg (fun k : C(fibreOf i a₀, fibreOf i a₀) =>
            k (fibrePsi i a₀ (Path.refl (i a₀)))) hcomp₂ := Subsingleton.elim _ _
    rw [πmap_homotopyGroupCast]
    rw [← πmap_comp_apply]
    rw [homotopyGroupCast_congr
      (congrArg (fibrePsi i a₀) (fibrePhi_fibrePsi i a₀ (Path.refl (i a₀))))
      (congrArg (fun k : C(fibreOf i a₀, fibreOf i a₀) =>
        k (fibrePsi i a₀ (Path.refl (i a₀)))) hcomp₂) m]
    exact key₂ z

/-- **`pairShiftHom` is a bijection.** -/
theorem pairShiftHom_bijective (i : C(A, X)) (a₀ : A) (m : ℕ) :
    Function.Bijective (pairShiftHom i a₀ m) := by
  show Function.Bijective
    ((πmap (fibrePsi i a₀) m (Path.refl (i a₀))).comp (stepMulEquiv m).toMonoidHom)
  exact (fibrePsi_πmap_bijective i a₀ m).comp (stepMulEquiv m).bijective

end

end Work.RatHurewicz
