import Mathlib
import Submission.Work.Mostow.geomFiniteThickThinDefs
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.thinTubeDefs
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.levYcFormula
import Submission.Work.Mostow.hptOf_yc
import Submission.Work.Mostow.hptOfLevelYc
import Submission.Work.Mostow.hptOf_level
import Submission.Work.Mostow.cuspCocompactAllLevels
import Submission.Work.Mostow.cuspCocompactAtLevel
import Submission.Work.Mostow.Margulis.exists_boost_near
import Submission.Work.Mostow.horoballComplementBoundedAux
import Submission.Work.Mostow.cuspCocompactParFixed
import Submission.Work.Mostow.busemannLimitAlongSequence
import Submission.Work.Mostow.dirFarOfLargeLev
import Submission.Work.Mostow.dirichletGapASelf

namespace Work.Mostow

theorem horoballComplementBounded (n : ℕ) (hn : 3 ≤ n) (hA : Submission.Mostow.POActionProp n) (hI : Submission.Mostow.HypIsometryProp n) (hBb : ∀ m, Submission.Mostow.BieberbachProp m) (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) (hΓ : Submission.Mostow.HypLattice Γ) (ht : Submission.Mostow.E n → ℝ) (heq : Work.Mostow.IsEquivHeight Γ (Work.Mostow.parFixed Γ) ht) : ∃ R : ℝ, ∀ z : Submission.Mostow.E n, z ∈ Work.Mostow.Dirichlet Γ → (∀ ξ ∈ Work.Mostow.parFixed Γ, ht ξ ≤ Submission.Mostow.busemann ξ z) → Submission.Mostow.hdist (0 : Submission.Mostow.E n) z ≤ R := by
  refine horoballComplementBounded_aux n (by omega) hA hI hBb Γ hΓ ht heq ?_ ?_ ?_ ?_
  · exact hlInput_of_gapA n (by omega) hA hI hBb Γ hΓ (gapA_allSelf n (by omega) Γ hΓ)
  · intro ξ hξ hvan
    obtain ⟨K, hKc, hK⟩ := cuspCocompactParFixed n (by omega) hA hI hBb Γ hΓ hvan ξ hξ 0
    refine ⟨K, hKc, fun u hu => ?_⟩
    have hbus0 : Submission.Mostow.busemann ξ u = 0 := by
      have hb : Submission.Mostow.busemann ξ u = Real.log (Work.Mostow.lev ξ u) := rfl
      rw [hb, hu, Real.log_one]
    obtain ⟨γ, hγbd, hγK⟩ := hK u hbus0
    exact ⟨γ, hγbd, hγK⟩
  · intro z ζ hζ hnorm hdir w
    exact busemannLimitAlongSequence n hI z ζ hζ hnorm hdir w
  · intro ξ hξ C hC
    exact dirFarOfLargeLev n hI ξ hξ C hC

end Work.Mostow
