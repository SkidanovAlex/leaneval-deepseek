import Mathlib
import Submission.Mostow.GapADefs
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.geomFiniteComplement
import Submission.Work.Mostow.horoballComplementBounded
import Submission.Work.Mostow.HL_of_escapeShort
import Submission.Work.Mostow.orbitFree_stab_busemann
import Submission.Work.Mostow.classifyProp
import Submission.Work.Mostow.geomFiniteParabolicClass
import Submission.Work.Mostow.geomFiniteStabHorosphere
import Submission.Work.Mostow.geomFiniteCuspCocompact
import Submission.Work.Mostow.cuspHoroballsPairwise
import Submission.Work.Mostow.busemannLimitAlongSequence
import Submission.Work.Mostow.dirFarOfLargeLev

/-!
# Area C1 (geomFinite) — final wiring through the lead's HL and GAP-A

This file assembles `Work.Mostow.geomFinite` from

* the cusp horoballs `cuspHoroballsPairwise` (equivariance + pairwise disjointness),
* the complement boundedness `horoballComplementBounded_aux`, fed with the lead's HL
  `HL_of_escapeShort` (whose non-locally-provable input is the `GapA` hypothesis `hesc`),
* the four chapters handled by `geomFinite_of_pieces`.

`GapA Γ` is the "escape ⇒ short infinite-order element" statement (GAP-A); for lattices in
`PO(n,1)`, `n ≥ 3`, it is supplied by the lead's chain (`gapA_three`, Kazhdan–Margulis + strata).
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}


/-- Boundedness of the Dirichlet part of the complement of the cusp horoballs, using the lead's
`HL_of_escapeShort` for HL and GAP-A for its non-local input. -/
theorem hdir_of_gapA (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (hBb : ∀ m, BieberbachProp m) (Γ : Subgroup (PO n 1)) (hΓ : HypLattice Γ)
    (ht : E n → ℝ) (heq : IsEquivHeight Γ (parFixed Γ) ht)
    (hM : MargulisCuspProp n) (hL : MargulisLoxProp n) (hPS : PairStabProp n) (hC : ClassifyProp n)
    (hesc : GapAProp Γ) :
    ∃ R : ℝ, ∀ z : E n, z ∈ Dirichlet Γ →
      (∀ ξ ∈ parFixed Γ, ht ξ ≤ busemann ξ z) → hdist (0 : E n) z ≤ R := by
  refine horoballComplementBounded_aux n (by omega) hA hI hBb Γ hΓ ht heq ?_ ?_ ?_ ?_
  · -- HL, from the lead's `HL_of_escapeShort`
    intro ζ hζ s hfree
    refine HL_of_escapeShort n hn hA hI hM hL hPS hC ?_ Γ hΓ.1 ?_ hesc ζ hζ s hfree ?_
    · intro g hg
      exact ⟨(geomFiniteParabolicClass n (by omega) hA hI g hg).1,
        (geomFiniteParabolicClass n (by omega) hA hI g hg).2.1⟩
    · intro ξ hξS hpar γ hγ
      have h := geomFiniteStabHorosphere n (by omega) hA hI Γ hΓ.1 ξ ⟨hξS, hpar⟩ γ hγ
      rw [bCocy, hγ] at h
      exact h
    · intro γ hγ
      exact orbitFree_stab_busemann n (by omega) hA hI Γ 0 ζ hζ s hfree γ hγ
  · -- cocompactness of the cusp stabiliser on the horosphere at level `1`
    intro ξ hξ hvan
    obtain ⟨K, hKc, hK⟩ :=
      geomFiniteCuspCocompact n (by omega) hA hI hBb Γ hΓ ξ hξ hvan 0
    refine ⟨K, hKc, fun u hu => ?_⟩
    have hbus0 : busemann ξ u = 0 := by
      have hb : busemann ξ u = Real.log (lev ξ u) := rfl
      rw [hb, hu, Real.log_one]
    obtain ⟨γ, hγbd, hγK⟩ := hK u hbus0
    exact ⟨γ, hγbd, hγK⟩
  · intro z ζ hζ hnorm hdir w
    exact busemannLimitAlongSequence n hI z ζ hζ hnorm hdir w
  · intro ξ hξ C hC
    exact dirFarOfLargeLev n hI ξ hξ C hC

/-- **Final assembly.**  Assuming GAP-A for every lattice, `GeomFiniteProp n` holds. -/
theorem geomFinite_of_gapA (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (hBb : ∀ m, BieberbachProp m)
    (hM : MargulisCuspProp n) (hL : MargulisLoxProp n) (hPS : PairStabProp n) (hC : ClassifyProp n)
    (hesc : ∀ (Γ : Subgroup (PO n 1)), HypLattice Γ → GapAProp Γ) :
    GeomFiniteProp n := by
  refine geomFinite_of_pieces n hn hA hI
    (fun g hg => (geomFiniteParabolicClass n (by omega) hA hI g hg).1)
    (fun Γ hd ξ hξ γ hγ => geomFiniteStabHorosphere n (by omega) hA hI Γ hd ξ hξ γ hγ)
    ?_
    (fun Γ hΓ ξ hξ hvan => geomFiniteCuspCocompact n (by omega) hA hI hBb Γ hΓ ξ hξ hvan)
  intro Γ hΓ hvan
  obtain ⟨ht, heq, hdisj⟩ := cuspHoroballsPairwise n (by omega) hA hI hBb Γ hΓ hvan
  refine hasCuspHoroballs_of hA hI Γ hΓ.1 ht heq hdisj ?_
  obtain ⟨R, hR⟩ := hdir_of_gapA n hn hA hI hBb Γ hΓ ht heq hM hL hPS hC (hesc Γ hΓ)
  refine ⟨R, fun z hz hout => hR z hz (fun ξ hξ => ?_)⟩
  have h := hout ξ hξ
  simp only [horoball, Set.mem_ofPred_eq, not_lt] at h
  exact h

end

end Work.Mostow

#print axioms Work.Mostow.geomFinite_of_gapA
#print axioms Work.Mostow.hdir_of_gapA
