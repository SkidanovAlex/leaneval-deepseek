import Mathlib
import Submission.Work.RatHurewicz.PairFibre
import Submission.Work.StemsB.ConnectingMap

/-!
# The connecting map of the homotopy fibre projection is `i_*`

The connecting map `fibreDMap i a₀ m : π_{m+2}(A, a₀) →* π_{m+1}(F)` of the Serre fibration
`homotopyFibreFst i a₀ : E → A` (with fibre `F = fibreOf i a₀ ≅ ΩX`) is the composite of the map
`π_{m+2}(A, a₀) → π_{m+2}(X, i a₀)` induced by `i` with the curried loop-space shift
`pairShiftHom i a₀ m : π_{m+2}(X, i a₀) →* π_{m+1}(F)`.

Both sides are monoid homomorphisms out of `π_{m+2}(A,a₀)`, so it suffices to check them on the
class `⟦f⟧` of a based cube `f : Ω^(m+2) A a₀`:

* on the left, `dFun_mk` expresses the connecting map as the class of the top face of the chosen
  lift `dLift` (`Work.StemsB.ConnectingMap`), and the explicit lift `pairLift i a₀ f`
  (`Submission/Work/RatHurewicz/PairFibre.lean`) satisfies the same hypotheses, so
  `Work.StemsB.liftUniqueness` shows that its top face is homotopic to `dLift`'s;
* on the right, `pairShiftHom_comp_apply_mk` expresses the value as the class of the curried cube
  `genLoopMap (fibrePsi i a₀) (m+1) (Faux (m+1) (genLoopMap i (m+2) f))`, which
  `genLoopMap_fibrePsi_Faux_eq` identifies with the top face of `pairLift i a₀ f`.
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.RatHurewicz

open Work.StemsB

noncomputable section

variable {X : Type} [TopologicalSpace X] {A : Type} [TopologicalSpace A]

/-- **The connecting map of the fibration `homotopyFibreFst i a₀` is `i_*` after the loop-space
shift.** -/
theorem fibreDMap_eq_pairShiftHom (i : C(A, X)) (a₀ : A) (m : ℕ) :
    fibreDMap i a₀ m = (pairShiftHom i a₀ m).comp (πmap i (m + 1) a₀) := by
  apply MonoidHom.ext
  intro x
  refine Quotient.inductionOn x (fun f => ?_)
  -- the right hand side, on the representative `f`: the curried cube
  have hR : pairShiftHom i a₀ m (πmap i (m + 1) a₀ ⟦f⟧)
      = (⟦topFaceG (m + 1)
            (cubeReindex (p := homotopyFibreFst i a₀) (e₀ := homotopyFibreBasepoint i a₀) f)
            (cubeReindex_one _) (pairLift i a₀ f) (pairLift_spec_lift i a₀ f)
            (pairLift_spec_bdry i a₀ f)⟧ :
          HomotopyGroup (Fin (m + 1)) (fibreOf i a₀) (fibreOfPt i a₀)) := by
    rw [pairShiftHom_comp_apply_mk i a₀ m f, genLoopMap_fibrePsi_Faux_eq i a₀ m f]
  -- the left hand side, on the representative `f`: the top face of the canonical lift
  have hL : (dFun (homotopyFibreFst i a₀) (homotopyFibreBasepoint i a₀) (fibreHrel i a₀) m) ⟦f⟧
      = (⟦dGenLoop (homotopyFibreFst i a₀) (homotopyFibreBasepoint i a₀) (fibreHrel i a₀) f⟧ :
          HomotopyGroup (Fin (m + 1)) (fibreOf i a₀) (fibreOfPt i a₀)) :=
    dFun_mk (homotopyFibreFst i a₀) (homotopyFibreBasepoint i a₀) (fibreHrel i a₀) f
  -- the two top faces are homotopic, by uniqueness of lifts
  have htop : (⟦dGenLoop (homotopyFibreFst i a₀) (homotopyFibreBasepoint i a₀) (fibreHrel i a₀) f⟧ :
        HomotopyGroup (Fin (m + 1)) (fibreOf i a₀) (fibreOfPt i a₀))
      = (⟦topFaceG (m + 1)
            (cubeReindex (p := homotopyFibreFst i a₀) (e₀ := homotopyFibreBasepoint i a₀) f)
            (cubeReindex_one _) (pairLift i a₀ f) (pairLift_spec_lift i a₀ f)
            (pairLift_spec_bdry i a₀ f)⟧ :
          HomotopyGroup (Fin (m + 1)) (fibreOf i a₀) (fibreOfPt i a₀)) :=
    Quotient.sound
      (liftUniqueness (p := homotopyFibreFst i a₀) (e₀ := homotopyFibreBasepoint i a₀)
        (fibreHrel i a₀) (m + 1)
        (cubeReindex (p := homotopyFibreFst i a₀) (e₀ := homotopyFibreBasepoint i a₀) f)
        (cubeReindex_zero _) (cubeReindex_one _)
        (dLift (homotopyFibreFst i a₀) (homotopyFibreBasepoint i a₀) (fibreHrel i a₀) f)
        (pairLift i a₀ f)
        (dLift_spec (homotopyFibreFst i a₀) (homotopyFibreBasepoint i a₀) (fibreHrel i a₀) f).1
        (pairLift_spec_lift i a₀ f)
        (dLift_spec (homotopyFibreFst i a₀) (homotopyFibreBasepoint i a₀) (fibreHrel i a₀) f).2.1
        (pairLift_spec_zero i a₀ f)
        (dLift_spec (homotopyFibreFst i a₀) (homotopyFibreBasepoint i a₀) (fibreHrel i a₀) f).2.2
        (pairLift_spec_bdry i a₀ f))
  exact Eq.trans hL (Eq.trans htop hR.symm)

end

end Work.RatHurewicz
