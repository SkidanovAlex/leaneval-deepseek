import Mathlib
import Submission.Work.LandLeaves.TypeGeometry
import Submission.Work.LandLeaves.Defs
import Submission.Work.LandLeaves.ccBet_angDouble_of_typeSet_short
import Submission.Work.ELTop.All
import Submission.Work.ELTop.landsN_iff_landsAt
import Submission.Work.ELRig.Sides
import Submission.Work.TopJordan.Main

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Definitions and elementary lemmas for `ccBet_angDouble_of_typeSet_v2`

Vocabulary for the geometric core of the long-arc case of the cyclic order preservation.
-/

namespace Work.LandLeaves

open Classical
open scoped Topology
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

noncomputable section


/-! ## Bridging the Böttcher data (local copy, independent of the in-flight `ccBet_angDouble_geom`) -/

/-- The dynamical Nakane data attached to an arbitrary Böttcher coordinate `φ`. -/
theorem elDynPhi_eq_v2 {c : ℂ} {φ : ℂ → ℂ} (hφ : Work.ParamRays.IsDynBottcher c φ) :
    Work.EL.dynPhi c φ = Work.ParamRays.dynPhi c := by
  have hex : Work.ParamRays.DynBottcherExists c := ⟨φ, hφ⟩
  funext z
  by_cases hz : z ∈ Work.EL.K c
  · simp [Work.EL.dynPhi, Work.ParamRays.dynPhi, hz, Work.EL.K]
  · rw [Work.EL.dynPhi_of_notMem hz, Work.ParamRays.dynPhi_of_not_mem hz]
    exact (Work.ParamRays.dynPhiOf_eq_of_isDynBottcher hex hφ (by
      rw [Work.ParamRays.escaping_iff_not_bounded]
      exact fun hb => hz hb)).symm

/-- The dynamical Nakane data at a Böttcher coordinate. -/
noncomputable def dynBNakane {c : ℂ} {φ : ℂ → ℂ} (hφ : Work.ParamRays.IsDynBottcher c φ) :
    Work.EL.DynB c φ :=
  Eq.mp (congrArg (fun ψ : ℂ → ℂ => Work.Top.NakaneData (Work.EL.K c) ψ)
      (elDynPhi_eq_v2 hφ).symm)
    (Work.SeedDyn.dynB (Work.LandLeaves.dynBottcherOnlyOnMandelbar c ⟨φ, hφ⟩))

/-- `landsAt` from a `rayAccum` singleton at a specific Böttcher coordinate. -/
theorem landsAt_of_rayAccum {c : ℂ} {φ : ℂ → ℂ} (hφ : Work.ParamRays.IsDynBottcher c φ)
    {θ : ℝ} {y : ℂ} (h : Work.Landing.rayAccum c φ θ = {y}) :
    Work.Landing.landsAt c θ y := ⟨φ, hφ, h⟩


variable {c : ℂ} {φ : ℂ → ℂ} {y : ℂ}

/-- The co-landing pair at `y` of two angles whose dynamic rays both land at `y`. -/
def mkPair (hN : Work.EL.DynB c φ) {u v : ℝ} (hu : Work.EL.LandsN hN u y)
    (hv : Work.EL.LandsN hN v y) : Work.EL.CoPair hN where
  toRawPair := ⟨u, v, y⟩
  lands_a := hu
  lands_b := hv

@[simp] theorem mkPair_a (hN : Work.EL.DynB c φ) {u v : ℝ} (hu : Work.EL.LandsN hN u y)
    (hv : Work.EL.LandsN hN v y) : (mkPair hN hu hv).a = u := rfl

@[simp] theorem mkPair_b (hN : Work.EL.DynB c φ) {u v : ℝ} (hu : Work.EL.LandsN hN u y)
    (hv : Work.EL.LandsN hN v y) : (mkPair hN hu hv).b = v := rfl

/-- `ccBet a b x` is the same relation as `Work.EL.InArc x a b`. -/
theorem InArc_iff_ccBet {a b x : ℝ} : Work.EL.InArc x a b ↔ ccBet a b x := by
  simp only [Work.EL.InArc, Work.EL.arcLen, ccBet]

/-- `ccBet` is invariant under adding an integer to the *first* angle together with the arc
endpoint.  Specifically `ccBet v (u+1) w ↔ ccBet v u w`. -/
theorem ccBet_shift_end {u v w : ℝ} : ccBet v (u + 1) w ↔ ccBet v u w := by
  unfold ccBet
  rw [show u + 1 - v = (u - v) + ((1 : ℤ) : ℝ) by push_cast; ring, Int.fract_add_intCast]

/-- **Forward angle-side equivalence.** -/
theorem paramRay_subset_pairSide_of_ccBet (hN : Work.EL.DynB c φ) {u v w : ℝ}
    (hu : Work.EL.LandsN hN u y) (hv : Work.EL.LandsN hN v y)
    (hab : u < v) (hb1 : v < u + 1) (h : ccBet u v w) :
    Work.EL.paramRay hN w ⊆ Work.EL.pairSide (mkPair hN hu hv) :=
  Work.ELTop.paramRay_subset_pairSide_of_InArc hN (mkPair hN hu hv) hab hb1
    (InArc_iff_ccBet.mpr h)

/-- The near-arc form of the forward equivalence. -/
theorem paramRay_subset_pairSideNear_of_ccBet (hN : Work.EL.DynB c φ) {u v w : ℝ}
    (hu : Work.EL.LandsN hN u y) (hv : Work.EL.LandsN hN v y)
    (hab : u < v) (hb1 : v < u + 1) (h : ccBet v u w) :
    Work.EL.paramRay hN w ⊆ Work.EL.pairSideNear (mkPair hN hu hv) :=
  Work.ELTop.paramRay_subset_pairSideNear_of_InArc hN (mkPair hN hu hv) hab hb1
    (by rw [InArc_iff_ccBet]; exact (ccBet_shift_end).mpr h)

/-! ## Fractional-part arithmetic -/

theorem fract_sub_fract_of_le {w u v : ℝ} (h : Int.fract (v - u) ≤ Int.fract (w - u)) :
    Int.fract (w - v) = Int.fract (w - u) - Int.fract (v - u) := by
  have hw : w - u = Int.fract (w - u) + (⌊w - u⌋ : ℝ) := by
    have := Int.fract_add_floor (w - u); linarith
  have hv : v - u = Int.fract (v - u) + (⌊v - u⌋ : ℝ) := by
    have := Int.fract_add_floor (v - u); linarith
  have key : w - v = (Int.fract (w - u) - Int.fract (v - u)) + ((⌊w - u⌋ - ⌊v - u⌋ : ℤ) : ℝ) := by
    push_cast; linarith
  have h1 : 0 ≤ Int.fract (w - u) - Int.fract (v - u) := by linarith
  have h2 : Int.fract (w - u) - Int.fract (v - u) < 1 := by
    linarith [Int.fract_lt_one (w - u), Int.fract_nonneg (v - u)]
  rw [key, Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨h1, h2⟩]

theorem fract_sub_fract_of_lt {w u v : ℝ} (h : Int.fract (w - u) < Int.fract (v - u)) :
    Int.fract (w - v) = Int.fract (w - u) - Int.fract (v - u) + 1 := by
  have hw : w - u = Int.fract (w - u) + (⌊w - u⌋ : ℝ) := by
    have := Int.fract_add_floor (w - u); linarith
  have hv : v - u = Int.fract (v - u) + (⌊v - u⌋ : ℝ) := by
    have := Int.fract_add_floor (v - u); linarith
  have key : w - v = (Int.fract (w - u) - Int.fract (v - u) + 1)
      + ((⌊w - u⌋ - ⌊v - u⌋ - 1 : ℤ) : ℝ) := by
    push_cast; linarith
  have h1 : 0 ≤ Int.fract (w - u) - Int.fract (v - u) + 1 := by
    linarith [Int.fract_nonneg (w - u), Int.fract_lt_one (v - u)]
  have h2 : Int.fract (w - u) - Int.fract (v - u) + 1 < 1 := by linarith
  rw [key, Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨h1, h2⟩]

theorem fract_neg_eq {x : ℝ} (h0 : Int.fract x ≠ 0) : Int.fract (-x) = 1 - Int.fract x := by
  have hpos : 0 < Int.fract x := lt_of_le_of_ne (Int.fract_nonneg x) (Ne.symm h0)
  have hkey : -x = (1 - Int.fract x) + (((0 : ℤ) - ⌊x⌋ - 1 : ℤ) : ℝ) := by
    have := Int.fract_add_floor x; push_cast; linarith
  have h1 : 0 ≤ 1 - Int.fract x := by linarith [Int.fract_lt_one x]
  have h2 : 1 - Int.fract x < 1 := by linarith [Int.fract_nonneg x]
  rw [hkey, Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨h1, h2⟩]

/-- **Polarity of cyclic betweenness.** -/
theorem ccBet_or_ccBet_swap {u v w : ℝ} (huv : Int.fract (v - u) ≠ 0)
    (hwu : Int.fract (w - u) ≠ 0) (hwv : Int.fract (w - v) ≠ 0) :
    ccBet u v w ∨ ccBet v u w := by
  unfold ccBet
  rcases lt_trichotomy (Int.fract (w - u)) (Int.fract (v - u)) with h | h | h
  · exact Or.inl ⟨lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hwu), h⟩
  · exfalso
    have : Int.fract (w - v) = 0 := by
      rw [fract_sub_fract_of_le (le_of_eq h.symm), h, sub_self]
    exact hwv this
  · refine Or.inr ⟨?_, ?_⟩
    · rw [fract_sub_fract_of_le h.le]
      linarith [Int.fract_nonneg (w - u)]
    · rw [fract_sub_fract_of_le h.le, show u - v = -(v - u) by ring, fract_neg_eq huv]
      linarith [Int.fract_lt_one (w - u)]

/-- **Backward angle-side equivalence.**  A ray contained in the far side of the pair `(u,v)`
has its angle in the open counterclockwise arc `(u,v)` (the two sides are disjoint). -/
theorem ccBet_of_paramRay_subset_pairSide (hN : Work.EL.DynB c φ) (hJ : Work.Top.JordanForm)
    {u v w : ℝ} (hu : Work.EL.LandsN hN u y) (hv : Work.EL.LandsN hN v y)
    (hw : Work.EL.LandsN hN w y) (hab : u < v) (hb1 : v < u + 1)
    (hnd : Int.fract (w - u) ≠ 0) (hnd' : Int.fract (w - v) ≠ 0) (hnd'' : Int.fract (v - u) ≠ 0)
    (h : Work.EL.paramRay hN w ⊆ Work.EL.pairSide (mkPair hN hu hv)) : ccBet u v w := by
  rcases ccBet_or_ccBet_swap hnd'' hnd hnd' with h' | h'
  · exact h'
  · exfalso
    have hnear : Work.EL.paramRay hN w ⊆ Work.EL.pairSideNear (mkPair hN hu hv) :=
      paramRay_subset_pairSideNear_of_ccBet hN hu hv hab hb1 h'
    have hdis := Work.ELTop.pairSide_disjoint hN hJ (mkPair hN hu hv) hab hb1
    have hpt : Work.EL.rayPt hN w 2 ∈ Work.EL.paramRay hN w :=
      Work.EL.rayPt_mem_paramRay hN (by norm_num)
    exact Set.disjoint_left.mp hdis (h hpt) (hnear hpt)

end

end Work.LandLeaves
