import Mathlib
import Submission.Work.GATE2.Inputs
import Submission.Work.ELTop.mem_polyRegion_iff_of_notMem_K
import Submission.Work.ELTop.RigInput

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

namespace Work.GATE2.EXL

/-- A point off the filled Julia set which lies in the near side of a co-landing pair `P`
(with `P.a < P.b`) is the ray point of an angle in the near arc `(P.b, P.a + 1)`.

If the two angles of `P` are congruent modulo `ℤ` then the pair is degenerate: the reference
point of the near side lies on the pair curve, so the near side is empty and there is nothing to
prove.  Otherwise we normalise the second angle to `Q.b = P.b - ⌊P.b - P.a⌋ ∈ (P.a, P.a + 1)`;
the pair curve and both sides are invariant.  Writing `z = rayPt θ t` with `θ` the external angle
of `z` (`rayPt_extAngle_exp_pot`), the angle `θ` is congruent to neither `Q.a` nor `Q.b` (else `z`
would lie on the pair curve), so by `InArc_or_InArc_near` it lies in the far arc `(Q.a, Q.b)` or
in the near arc `(Q.b, Q.a + 1)`.  The first alternative puts `z` in the far side
(`paramRay_subset_pairSide_of_InArc`), contradicting the disjointness of the two sides. -/
theorem nearArc_of_mem_pairSideNear {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (P : Work.EL.CoPair hN) (hab : P.a < P.b) {z : ℂ} (hz : z ∉ Work.EL.K c)
    (hP : z ∈ Work.EL.pairSideNear P) :
    ∃ θ t : ℝ, 1 < t ∧ z = Work.EL.rayPt hN θ t ∧ Work.EL.InArc θ P.b (P.a + 1) := by
  classical
  by_cases hnd : Work.EL.arcLen P.a P.b = 0
  · -- degenerate pair: the near side is empty
    exfalso
    rw [Work.EL.arcLen] at hnd
    obtain ⟨j, hj⟩ := Int.fract_eq_zero_iff.mp hnd
    have hf' : Int.fract (P.a - P.b) = 0 := by
      rw [Int.fract_eq_zero_iff]
      exact ⟨-j, by push_cast; linarith⟩
    have harc' : Work.EL.arcLen P.b P.a = 0 := by
      rw [Work.EL.arcLen]; exact hf'
    have href : Work.EL.rayPt hN (P.b + Work.EL.arcLen P.b P.a / 2) 2
        = Work.EL.rayPt hN P.b 2 := by
      rw [harc']; norm_num
    have hmem : Work.EL.rayPt hN P.b 2 ∈ Work.EL.pairCurve P :=
      (Work.EL.mem_pairCurve_iff P _).mpr
        (Or.inr (Or.inr (Work.EL.rayPt_mem_paramRay hN (by norm_num))))
    have hemp : Work.EL.pairSideNear P = ∅ := by
      rw [show Work.EL.pairSideNear P = connectedComponentIn (Work.EL.pairCurve P)ᶜ
          (Work.EL.rayPt hN (P.b + Work.EL.arcLen P.b P.a / 2) 2) from rfl]
      rw [href]
      exact connectedComponentIn_eq_empty (by simpa using hmem)
    rw [hemp] at hP
    exact hP
  · -- non-degenerate pair: normalise the second angle
    set m : ℤ := ⌊P.b - P.a⌋ with hm_def
    let Q : Work.EL.CoPair hN :=
      { toRawPair := ⟨P.a, P.b - (m : ℝ), P.y⟩
        lands_a := P.lands_a
        lands_b := by
          have h := Work.ELTop.LandsN_add_int hN P.lands_b (-m)
          rwa [show P.b + ((-m : ℤ) : ℝ) = P.b - (m : ℝ) from by push_cast; ring] at h }
    have hQa : Q.a = P.a := rfl
    have hQb : Q.b = P.b - (m : ℝ) := rfl
    have hm : (⌊P.b - P.a⌋ : ℝ) = (m : ℝ) := rfl
    have hfpos : 0 < Int.fract (P.b - P.a) := by
      have h0 := Int.fract_nonneg (P.b - P.a)
      rcases lt_or_eq_of_le h0 with h | h
      · exact h
      · exact absurd h.symm hnd
    have hfloor : Int.fract (P.b - P.a) + (⌊P.b - P.a⌋ : ℝ) = P.b - P.a :=
      Int.fract_add_floor (P.b - P.a)
    have hQab : Q.a < Q.b := by
      show P.a < P.b - (m : ℝ)
      linarith [hfpos, hfloor, hm]
    have hQb1 : Q.b < Q.a + 1 := by
      show P.b - (m : ℝ) < P.a + 1
      have h := Int.fract_lt_one (P.b - P.a)
      linarith [h, hfloor, hm]
    -- the pair curve and the near side are invariant under the normalisation
    have hrawcurve : Work.EL.RawPair.curve hN Q.toRawPair
        = Work.EL.RawPair.curve hN P.toRawPair := by
      rw [show Q.toRawPair = (⟨P.a, P.b - (m : ℝ), P.y⟩ : Work.EL.RawPair) from rfl,
        show P.toRawPair = (⟨P.a, P.b, P.y⟩ : Work.EL.RawPair) from rfl]
      simp only [Work.EL.RawPair.curve, Work.ELTop.paramRay_sub_natCast hN P.b m]
    have harcQ' : Work.EL.arcLen Q.b Q.a = Work.EL.arcLen P.b P.a := by
      show Int.fract (Q.a - Q.b) = Int.fract (P.a - P.b)
      have h1 : Q.a - Q.b = (P.a - P.b) + (m : ℝ) := by rw [hQa, hQb]; ring
      rw [h1, Int.fract_add_intCast]
    have href' : Work.EL.rayPt hN (Q.b + Work.EL.arcLen Q.b Q.a / 2) 2
        = Work.EL.rayPt hN (P.b + Work.EL.arcLen P.b P.a / 2) 2 := by
      have harg : Q.b + Work.EL.arcLen Q.b Q.a / 2
          = (P.b + Work.EL.arcLen P.b P.a / 2) + ((-m : ℤ) : ℝ) := by
        rw [hQb, harcQ']; push_cast; ring
      rw [harg, Work.ELTop.rayPt_add_int hN (P.b + Work.EL.arcLen P.b P.a / 2) 2 (-m)]
    have hnear : Work.EL.pairSideNear Q = Work.EL.pairSideNear P := by
      show connectedComponentIn (Work.EL.RawPair.curve hN Q.toRawPair)ᶜ
          (Work.EL.rayPt hN (Q.b + Work.EL.arcLen Q.b Q.a / 2) 2)
        = connectedComponentIn (Work.EL.RawPair.curve hN P.toRawPair)ᶜ
          (Work.EL.rayPt hN (P.b + Work.EL.arcLen P.b P.a / 2) 2)
      rw [hrawcurve, href']
    have hPQ : z ∈ Work.EL.pairSideNear Q := by rw [hnear]; exact hP
    have hzQ : z ∉ Work.EL.pairCurve Q :=
      connectedComponentIn_subset (Work.EL.pairCurve Q)ᶜ
        (Work.EL.rayPt hN (Q.b + Work.EL.arcLen Q.b Q.a / 2) 2)
        (show z ∈ connectedComponentIn (Work.EL.pairCurve Q)ᶜ
            (Work.EL.rayPt hN (Q.b + Work.EL.arcLen Q.b Q.a / 2) 2) from hPQ)
    have hJ : Work.Top.JordanForm := Work.TopJordan.jordanForm
    have hdisj : Disjoint (Work.EL.pairSide Q) (Work.EL.pairSideNear Q) :=
      Work.ELTop.pairSide_disjoint hN hJ Q hQab hQb1
    -- the external angle and level of `z`
    set θ : ℝ := Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z with hθdef
    set t : ℝ := Real.exp (Work.EL.pot hN z) with htdef
    have ht : 1 < t := by
      rw [htdef]; exact Work.ELTop.one_lt_exp_pot hN hz
    have hzt : z = Work.EL.rayPt hN θ t := by
      rw [hθdef, htdef]; exact (Work.ELTop.rayPt_extAngle_exp_pot hN hz).symm
    -- `θ` is congruent to neither endpoint of the normalised pair
    have h1 : ∀ k : ℤ, θ ≠ Q.a + (k : ℝ) := by
      intro k hk
      have hmem : z ∈ Work.EL.paramRay hN Q.a := by
        have hz' : z = Work.EL.rayPt hN Q.a t := by
          rw [hzt, hk, Work.ELTop.rayPt_add_int hN Q.a t k]
        rw [hz']; exact Work.EL.rayPt_mem_paramRay hN ht
      exact hzQ ((Work.EL.mem_pairCurve_iff Q z).mpr (Or.inl hmem))
    have h2 : ∀ k : ℤ, θ ≠ Q.b + (k : ℝ) := by
      intro k hk
      have hmem : z ∈ Work.EL.paramRay hN Q.b := by
        have hz' : z = Work.EL.rayPt hN Q.b t := by
          rw [hzt, hk, Work.ELTop.rayPt_add_int hN Q.b t k]
        rw [hz']; exact Work.EL.rayPt_mem_paramRay hN ht
      exact hzQ ((Work.EL.mem_pairCurve_iff Q z).mpr (Or.inr (Or.inr hmem)))
    have hinarc : Work.EL.InArc θ P.b (P.a + 1) := by
      rcases Work.ELTop.InArc_or_InArc_near hQab hQb1 h1 h2 with hfar | hnearc
      · exfalso
        have hsub := Work.ELTop.paramRay_subset_pairSide_of_InArc hN Q hQab hQb1 hfar
        have hmem : z ∈ Work.EL.pairSide Q := by
          rw [hzt]; exact hsub (Work.EL.rayPt_mem_paramRay hN ht)
        exact (Set.disjoint_left.mp hdisj) hmem hPQ
      · rw [hQa, hQb] at hnearc
        rw [Work.EL.InArc, Work.EL.arcLen] at hnearc
        rw [Work.EL.InArc, Work.EL.arcLen]
        have e1 : θ - (P.b - (m : ℝ)) = (θ - P.b) + (m : ℝ) := by ring
        have e2 : (P.a + 1) - (P.b - (m : ℝ)) = ((P.a + 1) - P.b) + (m : ℝ) := by ring
        rw [e1, Int.fract_add_intCast, e2, Int.fract_add_intCast] at hnearc
        exact hnearc
    exact ⟨θ, t, ht, hzt, hinarc⟩

end Work.GATE2.EXL
