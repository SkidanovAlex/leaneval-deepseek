import Mathlib
import Submission.Work.ELAssembly.Defs
import Submission.Work.ELTop.paramRay_disjoint
import Submission.Work.ELTop.landsN_mem_K
import Submission.Work.ELTop.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

open Classical Filter Set
open scoped Topology

/-! ## Two rays which meet have angles differing by an integer

The curve of a co-landing pair `P` is the union of the two parametrized rays of `P.a` and `P.b`
with the landing point `P.y`.  Two such curves can therefore meet only in two ways: in a common
point of two rays, or in a landing point.  The first case is controlled by
`Work.ELTop.paramRay_disjoint`: the rays `R(θ)` and `R(θ')` meet only when `θ' = θ + k` for some
`k : ℤ` (the angle of a ray is defined modulo `ℤ`), and then the two landing *statements* force
the two landing points to agree, since then the two landing maps are the same function.
The second case is controlled by the fact that a landing point of a ray lies in the filled Julia
set `K c` (`Work.ELTop.landsN_mem_K`), while the rays themselves lie entirely in the complement
of `K c` (`Work.EL.paramRay_subset_compl`). -/

/-- **If two parametrized rays meet, their angles differ by an integer.**  This is the
contrapositive form of `Work.ELTop.paramRay_disjoint`. -/
theorem exists_int_angle_eq_of_mem_paramRay_inter {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    {θ θ' : ℝ} {z : ℂ} (h : z ∈ Work.EL.paramRay hN θ) (h' : z ∈ Work.EL.paramRay hN θ') :
    ∃ k : ℤ, θ' = θ + k := by
  by_contra hcon
  push Not at hcon
  exact Set.disjoint_left.mp (Work.ELTop.paramRay_disjoint hN hcon) h h'

/-- **Two rays which land and which meet land at the same point.**  If `R(θ)` lands at `y` and
`R(θ')` lands at `y'` and the two rays share a point `z`, then `y' = y`: the angles differ by an
integer `k`, and the point maps `t ↦ rayPt hN θ t` and `t ↦ rayPt hN θ' t` agree by the
`1`-periodicity of the rays (`Work.ELTop.rayPt_add_int`), so their limits coincide. -/
theorem eq_landing_of_mem_paramRay_inter {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    {θ θ' : ℝ} {y y' : ℂ} (hθ : Work.EL.LandsN hN θ y) (hθ' : Work.EL.LandsN hN θ' y')
    {z : ℂ} (h : z ∈ Work.EL.paramRay hN θ) (h' : z ∈ Work.EL.paramRay hN θ') : y' = y := by
  obtain ⟨k, hk⟩ := exists_int_angle_eq_of_mem_paramRay_inter hN h h'
  have hfun : (fun t : ℝ => Work.EL.rayPt hN θ' t) = (fun t : ℝ => Work.EL.rayPt hN θ t) := by
    funext t
    rw [hk]
    exact Work.ELTop.rayPt_add_int hN θ t k
  refine tendsto_nhds_unique ?_ hθ
  rw [← hfun]
  exact hθ'

/-- **The curve of the `α`-pair is disjoint from the curve of every co-landing pair whose landing
point is not `z₁`.**  Writing `P := alphaPairOf d` for the pair of the two root-portrait rays of
`d`, the curve of `P` is `R(α₁) ∪ {z₁} ∪ R(α₂)`, and that of `R` is
`R(R.a) ∪ {R.y} ∪ R(R.b)`.  A point `z` of both curves either lies in `K c`, in which case the
rays (which are contained in `K cᶜ`) are excluded and `z = z₁ = R.y`, contradicting the
hypothesis; or it lies outside `K c`, in which case it is a common point of one of the two
`α`-rays and one of the two `R`-rays, and `eq_landing_of_mem_paramRay_inter` forces
`R.y = z₁` again. -/
theorem pairCurve_disjoint_alpha {c : ℂ} (d : Work.EL.RootParabolic c)
    (R : Work.EL.CoPair d.hN) (hy : R.y ≠ d.z₁) :
    Disjoint (Work.EL.pairCurve (Work.ELAssembly.alphaPairOf d)) (Work.EL.pairCurve R) := by
  rw [Set.disjoint_iff]
  rintro z ⟨hz1, hz2⟩
  have h1 := (Work.EL.mem_pairCurve_iff (alphaPairOf d) z).mp hz1
  have h2 := (Work.EL.mem_pairCurve_iff R z).mp hz2
  -- the two root rays land at `z₁`
  have hz1lands : Work.EL.LandsN d.hN Work.EL.alpha1 d.z₁ :=
    (Work.ELTop.landsN_iff_landsAt d.hN d.bottcher Work.EL.alpha1 d.z₁).mpr d.rays.1
  have hz2lands : Work.EL.LandsN d.hN Work.EL.alpha2 d.z₁ :=
    (Work.ELTop.landsN_iff_landsAt d.hN d.bottcher Work.EL.alpha2 d.z₁).mpr d.rays.2
  have hK1 : d.z₁ ∈ Work.EL.K c := Work.ELTop.landsN_mem_K d.hN hz1lands
  have hKR : R.y ∈ Work.EL.K c := Work.ELTop.landsN_mem_K d.hN R.lands_a
  by_cases hK : z ∈ Work.EL.K c
  · -- a common point inside `K c` is the landing point of each pair
    have hz1' : z = d.z₁ := by
      rcases h1 with h | h | h
      · exact absurd hK ((Work.EL.paramRay_subset_compl d.hN Work.EL.alpha1) h)
      · exact h
      · exact absurd hK ((Work.EL.paramRay_subset_compl d.hN Work.EL.alpha2) h)
    have hz2' : z = R.y := by
      rcases h2 with h | h | h
      · exact absurd hK ((Work.EL.paramRay_subset_compl d.hN R.a) h)
      · exact h
      · exact absurd hK ((Work.EL.paramRay_subset_compl d.hN R.b) h)
    exact hy (hz2'.symm.trans hz1')
  · -- a common point outside `K c` is a common point of two rays
    have hne1 : z ≠ d.z₁ := fun h => hK (h ▸ hK1)
    have hneR : z ≠ R.y := fun h => hK (h ▸ hKR)
    have hzα : z ∈ Work.EL.paramRay d.hN Work.EL.alpha1 ∨
        z ∈ Work.EL.paramRay d.hN Work.EL.alpha2 := by
      rcases h1 with h | h | h
      · exact Or.inl h
      · exact absurd h hne1
      · exact Or.inr h
    have hzR : z ∈ Work.EL.paramRay d.hN R.a ∨ z ∈ Work.EL.paramRay d.hN R.b := by
      rcases h2 with h | h | h
      · exact Or.inl h
      · exact absurd h hneR
      · exact Or.inr h
    have key : R.y = d.z₁ := by
      rcases hzα with ha | ha <;> rcases hzR with hb | hb
      · exact eq_landing_of_mem_paramRay_inter d.hN hz1lands R.lands_a ha hb
      · exact eq_landing_of_mem_paramRay_inter d.hN hz1lands R.lands_b ha hb
      · exact eq_landing_of_mem_paramRay_inter d.hN hz2lands R.lands_a ha hb
      · exact eq_landing_of_mem_paramRay_inter d.hN hz2lands R.lands_b ha hb
    exact hy key

end Work.ELAssembly
