import Mathlib
import Submission.Work.ELTop.paramRay_subset_pairSide
import Submission.Work.ELTop.paramRay_subset_pairSideNear
import Submission.Work.ELTop.RigInput
import Submission.Work.ELRig.Defs
import Submission.Work.ELTop.pairSide_subset_pairSideNear

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.SeedSimple2.Rotation

/-- `InArc` depends on the *left* endpoint of the arc only modulo `ℤ`. -/
theorem InArc_add_left_endpoint_int (x a b : ℝ) (m : ℤ) :
    Work.EL.InArc x (a + (m : ℝ)) b ↔ Work.EL.InArc x a b := by
  unfold Work.EL.InArc Work.EL.arcLen
  have h1 : Int.fract (x - (a + (m : ℝ))) = Int.fract (x - a) := by
    rw [show x - (a + (m : ℝ)) = (x - a) - (m : ℝ) by ring, Int.fract_sub_intCast]
  have h2 : Int.fract (b - (a + (m : ℝ))) = Int.fract (b - a) := by
    rw [show b - (a + (m : ℝ)) = (b - a) - (m : ℝ) by ring, Int.fract_sub_intCast]
  rw [h1, h2]

/-- **A ray which meets the far side of a pair has its angle in the far arc of the pair.**

Given a co-landing pair `P` with its two-sidedness (`PairSides hN P`), a point `z` of the
parameter ray of angle `x` which lies in the far side `pairSide P` can only be there if the
angle `x` lies in the far arc `(P.a, P.b)`: rays of angles in the complementary arc lie in the
near side, and rays of the two boundary angles lie on the pair curve itself.

The angular dichotomy is `Work.ELTop.InArc_or_InArc_near_aux` applied after normalizing
`P.b` to the representative `P.a + arcLen P.a P.b ∈ (P.a, P.a + 1)`; the degenerate case
`arcLen P.a P.b = 0` is impossible because then the far side is empty. -/
theorem pairSide_imp_InArc {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (P : Work.EL.CoPair hN)
    (hPa : P.a = Work.EL.alpha1) (hPb : P.b = Work.EL.alpha2)
    (hside : Work.EL.PairSides hN P) {x : ℝ} {z : ℂ} (hz : z ∈ Work.EL.paramRay hN x)
    (hzp : z ∈ Work.EL.pairSide P) : Work.EL.InArc x Work.EL.alpha1 Work.EL.alpha2 := by
  rw [← hPa, ← hPb]
  rcases eq_or_lt_of_le (Work.EL.arcLen_nonneg P.a P.b) with hdeg | hpos
  · -- degenerate arc: the reference point of the far side lies on the pair curve
    have hrefC : Work.EL.rayPt hN (P.a + Work.EL.arcLen P.a P.b / 2) 2 ∈ Work.EL.pairCurve P := by
      rw [← hdeg]
      simp only [zero_div, add_zero]
      exact (Work.EL.mem_pairCurve_iff P _).mpr
        (Or.inl (Work.EL.rayPt_mem_paramRay hN (by norm_num)))
    have hempty : Work.EL.pairSide P = ∅ := by
      have h1 : Work.EL.rayPt hN (P.a + Work.EL.arcLen P.a P.b / 2) 2
          ∉ (Work.EL.RawPair.curve hN P.toRawPair)ᶜ := by
        rw [Set.mem_compl_iff]
        exact fun h => h hrefC
      exact connectedComponentIn_eq_empty h1
    rw [hempty] at hzp
    exact absurd hzp (Set.notMem_empty z)
  · -- nondegenerate arc: normalize the right endpoint modulo `1`
    obtain ⟨k, hk⟩ : ∃ k : ℤ, P.b - (k : ℝ) = P.a + Work.EL.arcLen P.a P.b := by
      refine ⟨⌊P.b - P.a⌋, ?_⟩
      have hff := Int.floor_add_fract (P.b - P.a)
      simp only [Work.EL.arcLen]
      linarith
    set b' : ℝ := P.b - (k : ℝ) with hb'def
    have hb'cast : b' = P.b + ((-k : ℤ) : ℝ) := by
      rw [hb'def]; push_cast; ring
    have hlt : P.a < b' := by
      rw [hb'def]
      linarith [hk, hpos]
    have hlt1 : b' < P.a + 1 := by
      rw [hb'def]
      linarith [hk, Work.EL.arcLen_lt_one P.a P.b]
    have hparam_b' : Work.EL.paramRay hN b' = Work.EL.paramRay hN P.b := by
      rw [hb'cast]
      exact Work.ELTop.paramRay_add_int hN P.b (-k)
    -- the far side misses the pair curve
    have hz_notcurve : z ∉ Work.EL.pairCurve P := by
      intro hzc
      have hzc' : z ∈ Work.EL.RawPair.curve hN P.toRawPair := hzc
      exact (connectedComponentIn_subset (Work.EL.RawPair.curve hN P.toRawPair)ᶜ _
        hzp) hzc'
    -- the same membership, read with the unfolded name of the parameter ray
    have hzT : z ∈ Work.Top.NakaneData.paramRay hN x := hz
    by_cases hxa : ∃ j : ℤ, x = P.a + (j : ℝ)
    · -- the angle of `z` is congruent to `P.a`: the ray is part of the pair curve
      obtain ⟨j, hj⟩ := hxa
      have hz' : z ∈ Work.Top.NakaneData.paramRay hN P.a := by
        rw [hj] at hzT
        rwa [Work.ELTop.paramRay_add_int hN P.a j] at hzT
      exact absurd ((Work.EL.mem_pairCurve_iff P z).mpr (Or.inl hz')) hz_notcurve
    · by_cases hxb : ∃ j : ℤ, x = b' + (j : ℝ)
      · -- the angle of `z` is congruent to `P.b`
        obtain ⟨j, hj⟩ := hxb
        have hpx : Work.Top.NakaneData.paramRay hN x = Work.Top.NakaneData.paramRay hN P.b := by
          rw [hj]
          exact (Work.ELTop.paramRay_add_int hN b' j).trans hparam_b'
        have hz' : z ∈ Work.Top.NakaneData.paramRay hN P.b := by rwa [hpx] at hzT
        exact absurd ((Work.EL.mem_pairCurve_iff P z).mpr (Or.inr (Or.inr hz'))) hz_notcurve
      · -- the angle lies in one of the two open arcs of the pair
        have hne_a : ∀ j : ℤ, x ≠ P.a + (j : ℝ) := not_exists.mp hxa
        have hne_b : ∀ j : ℤ, x ≠ b' + (j : ℝ) := not_exists.mp hxb
        rcases Work.ELTop.InArc_or_InArc_near_aux hlt hlt1 hne_a hne_b with hfar | hnear
        · have hfar' : Work.EL.InArc x P.a (P.b + ((-k : ℤ) : ℝ)) := by
            rw [← hb'cast]; exact hfar
          exact (Work.ELTop.InArc_right_add_int x P.a P.b (-k)).mp hfar'
        · -- the angle lies in the complementary arc: the ray is in the near side
          have hnear'' : Work.EL.InArc x (P.b + ((-k : ℤ) : ℝ)) (P.a + 1) := by
            rw [← hb'cast]; exact hnear
          have hnear' : Work.EL.InArc x P.b (P.a + 1) :=
            (InArc_add_left_endpoint_int x P.b (P.a + 1) (-k)).mp hnear''
          exact absurd (hside.paramRay_near x hnear' hz)
            (Set.disjoint_left.mp hside.disjoint hzp)

end Work.SeedSimple2.Rotation
