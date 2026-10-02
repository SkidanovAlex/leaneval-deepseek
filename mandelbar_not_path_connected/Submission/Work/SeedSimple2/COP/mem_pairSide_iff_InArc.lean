import Mathlib
import Submission.Work.SeedSimple2.Defs
import Submission.Work.ELTop.pairSides_decomposition
import Submission.Work.ELTop.paramRay_subset_pairSide
import Submission.Work.ELTop.paramRay_subset_pairSideNear
import Submission.Work.ELTop.pairSide_subset_pairSideNear

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedSimple2.COP

/-- `Work.EL.InArc` depends on the *left* endpoint of the arc only modulo `ℤ`: the angles `a`
and `a + m` represent the same point of the circle. -/
theorem inArc_add_left_endpoint_int (x a b : ℝ) (m : ℤ) :
    Work.EL.InArc x (a + (m : ℝ)) b ↔ Work.EL.InArc x a b := by
  unfold Work.EL.InArc Work.EL.arcLen
  have h1 : Int.fract (x - (a + (m : ℝ))) = Int.fract (x - a) := by
    rw [show x - (a + (m : ℝ)) = (x - a) - (m : ℝ) by ring, Int.fract_sub_intCast]
  have h2 : Int.fract (b - (a + (m : ℝ))) = Int.fract (b - a) := by
    rw [show b - (a + (m : ℝ)) = (b - a) - (m : ℝ) by ring, Int.fract_sub_intCast]
  rw [h1, h2]

/-- **The side of a pair is read off the angle** (general form of `Work.SeedSimple2.Rotation.pairSide_imp_InArc`, which is the special case `P.a = α₁`, `P.b = α₂`): for a two-sided co-landing pair `P` and a point `z` of the ray of an angle `θ` which is not congruent to `P.a` or `P.b` modulo `1`, `z` lies in the far side of `P` exactly when `θ` lies in the far arc of `P`.

Proof: `←` is `hside.paramRay_far`;  `→` is the argument of `Work.SeedSimple2.Rotation.pairSide_imp_InArc` (normalize `P.b` to `P.a + arcLen P.a P.b ∈ (P.a, P.a+1)` using `Int.floor_add_fract`, apply `Work.ELTop.InArc_or_InArc_near_aux` and `hside.paramRay_near`, contradicting `hside.disjoint`). -/
theorem mem_pairSide_iff_InArc {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (P : Work.EL.CoPair hN) (hside : Work.EL.PairSides hN P)
    (hab : ∀ k : ℤ, P.b ≠ P.a + k)
    {θ : ℝ} (hθa : ∀ k : ℤ, θ ≠ P.a + k) (hθb : ∀ k : ℤ, θ ≠ P.b + k) {z : ℂ}
    (hz : z ∈ Work.EL.paramRay hN θ) :
    (z ∈ Work.EL.pairSide P ↔ Work.EL.InArc θ P.a P.b) := by
  refine ⟨?_, fun h => hside.paramRay_far θ h hz⟩
  intro hzp
  -- the arc of the pair is nondegenerate
  have hpos : 0 < Work.EL.arcLen P.a P.b := by
    rcases lt_or_eq_of_le (Work.EL.arcLen_nonneg P.a P.b) with h | h
    · exact h
    · exfalso
      have hf : Int.fract (P.b - P.a) = 0 := by
        rw [Work.EL.arcLen] at h
        exact h.symm
      obtain ⟨j, hj⟩ := Set.mem_range.mp (Int.fract_eq_zero_iff.mp hf)
      exact hab j (by linarith)
  -- normalize the right endpoint of the pair modulo `1`
  obtain ⟨k, hk⟩ : ∃ k : ℤ, P.b - (k : ℝ) = P.a + Work.EL.arcLen P.a P.b := by
    refine ⟨⌊P.b - P.a⌋, ?_⟩
    have hff := Int.floor_add_fract (P.b - P.a)
    simp only [Work.EL.arcLen]
    linarith
  set b' : ℝ := P.b - (k : ℝ) with hb'def
  have hb'cast : b' = P.b + ((-k : ℤ) : ℝ) := by rw [hb'def]; push_cast; ring
  have hlt : P.a < b' := by rw [hb'def]; linarith [hk, hpos]
  have hlt1 : b' < P.a + 1 := by
    rw [hb'def]; linarith [hk, Work.EL.arcLen_lt_one P.a P.b]
  -- the angle `θ` is congruent modulo `ℤ` to neither endpoint of the normalized arc either
  have hθb' : ∀ j : ℤ, θ ≠ b' + (j : ℝ) := by
    intro j hj
    refine hθb (j - k) ?_
    rw [hb'def] at hj
    push_cast at hj ⊢
    linarith
  rcases Work.ELTop.InArc_or_InArc_near_aux hlt hlt1 hθa hθb' with hfar | hnear
  · -- the angle lies in the far arc: undo the normalization of `P.b`
    rw [hb'cast] at hfar
    exact (Work.ELTop.InArc_right_add_int θ P.a P.b (-k)).mp hfar
  · -- the angle lies in the complementary arc: the ray is in the near side, contradiction
    have hnear' : Work.EL.InArc θ P.b (P.a + 1) := by
      have h := hnear
      rw [hb'cast] at h
      exact (inArc_add_left_endpoint_int θ P.b (P.a + 1) (-k)).mp h
    exact absurd (hside.paramRay_near θ hnear' hz)
      (Set.disjoint_left.mp hside.disjoint hzp)

end Work.SeedSimple2.COP
