import Mathlib
import Submission.Work.KT.Fund.AssemblyDefs
import Submission.Work.KT.Fund.Geom
import Submission.Work.KT.Fund.Disc
import Submission.Work.KT.homotopy_inv
import Submission.Work.KT.k0_rep
import Submission.Work.KT.Fund.Basic

namespace Work.KT.ExtGen

open Work.KT

noncomputable section

/-- The section `X → X × S¹`, `x ↦ (x, 1)`, of the projection `X × S¹ → X`. -/
def secSph (X : Type) [TopologicalSpace X] : C(X, X × Sph ℂ) :=
  ⟨fun x => (x, ⟨1, mem_sphere_zero_iff_norm.mpr (by norm_num)⟩), by fun_prop⟩

/-- **`r` factors through the upper disc restriction.**  With `r = K0.mapA (pullAlg (bp X))` the
restriction to the base point `pt = up 0`, and `ev0 = K0.mapA (pullAlg (zeroX X))` evaluation at the
centre of the disc, one has `r = ev0 ∘ K0.map (Fund.pullUp X)`: the composite
`X → X × D → X × S²` of the zero section with the upper-hemisphere chart is `bp X`. -/
lemma r_eq_ev0_comp_pullUp (X : Type) [TopologicalSpace X] :
    ∀ z : K0 C(X × S2, ℂ), Fund.r X z = Fund.ev0 X (K0.map (Fund.pullUp X) z) := by
  have h : (pullAlg (Fund.bp X)).toRingHom
      = (pullAlg (Fund.zeroX X)).toRingHom.comp (Fund.pullUp X) := by
    refine RingHom.ext fun g => ContinuousMap.ext fun x => ?_
    simp only [RingHom.comp_apply, pullAlg, Fund.bp, Fund.pt, Fund.zeroX]
    rfl
  intro z
  change K0.map (pullAlg (Fund.bp X)).toRingHom z
    = K0.map (pullAlg (Fund.zeroX X)).toRingHom (K0.map (Fund.pullUp X) z)
  rw [h, K0.map_comp_apply]

/-- **Triviality of the kernel of the boundary restriction.**  A class on `X × D` whose restriction
to the boundary circle `X × S¹` vanishes is already zero: all classes on the disc come from `X`
(`Fund.sD_ev0`), and on those the boundary restriction is the pull-back along the projection
`X × S¹ → X`, which is split by the section `x ↦ (x, 1)`. -/
lemma bdryRestrict_map_eq_zero (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (w : K0 C(X × Ball ℂ, ℂ)) (hw : K0.map (Fund.bdryRestrict X) w = 0) : w = 0 := by
  -- every class on the disc is the pull-back of a class on `X`
  obtain ⟨a, ha⟩ : ∃ a, Fund.sD X a = w := ⟨Fund.ev0 X w, Fund.sD_ev0 X w⟩
  rw [← ha] at hw ⊢
  -- `bdryRestrict ∘ projX^* = fst^*`, and `fst` has the section `x ↦ (x, 1)`
  have hcomp : (Fund.bdryRestrict X).comp (pullAlg (Fund.projX X)).toRingHom
      = (pullAlg (ContinuousMap.fst : C(X × Sph ℂ, X))).toRingHom := by
    refine RingHom.ext fun g => ContinuousMap.ext fun p => ?_
    simp [pullAlg, Fund.projX, Fund.bdryRestrict_apply]
  have hsec : ((pullAlg (secSph X)).toRingHom).comp
      ((pullAlg (ContinuousMap.fst : C(X × Sph ℂ, X))).toRingHom)
      = RingHom.id (C(X, ℂ)) := by
    refine RingHom.ext fun g => ContinuousMap.ext fun x => ?_
    simp [pullAlg, secSph]
  have hfst : K0.map (pullAlg (ContinuousMap.fst : C(X × Sph ℂ, X))).toRingHom a = 0 := by
    have h := hw
    change K0.map (Fund.bdryRestrict X)
      (K0.map (pullAlg (Fund.projX X)).toRingHom a) = 0 at h
    rw [← K0.map_comp_apply (pullAlg (Fund.projX X)).toRingHom (Fund.bdryRestrict X) a,
      hcomp] at h
    exact h
  have hbig : K0.map (pullAlg (secSph X)).toRingHom
      (K0.map (pullAlg (ContinuousMap.fst : C(X × Sph ℂ, X))).toRingHom a) = a := by
    rw [← K0.map_comp_apply (pullAlg (ContinuousMap.fst : C(X × Sph ℂ, X))).toRingHom
      (pullAlg (secSph X)).toRingHom a, hsec, K0.map_id_apply]
  have ha0 : a = 0 := by
    rw [← hbig, hfst, map_zero]
  rw [ha0, map_zero]

/-- **Base-point independence of the two disc restrictions (upper/lower hemisphere).**  With
`r = K0.mapA (pullAlg (bp X))`, `bp X = ⟨fun x => (x, up 0)⟩` (the fibre over the north pole
`up 0 = mk3 0 1` of `S² = Sph (EuclideanSpace ℝ (Fin 3))`), and `Fund.pullDn X` the restriction to
the *lower* hemisphere: every class killed by `r` is also killed by `pullDn` (in fact
`ker r = ker (K0.map (Fund.pullDn X))`).

Route: `r = ev0 ∘ K0.map (Fund.pullUp X)` where `ev0 = K0.mapA (pullAlg (Fund.zeroX X))` is
evaluation at the centre `0` of the disc (`Fund.pullUp`, `Fund.zeroX`, `Fund.pullAlg_comp`,
`K0.map_comp`), so `r z = 0` gives `K0.map (Fund.pullUp X) z = 0` by `Fund.sD_ev0`
(`sD (ev0 x) = x`).  Two independent routes from there:

* (`bdryRestrict`) `Fund.bdryRestrict_pullUp_eq_pullDn` gives
  `bdryRestrict (pullUp z) = bdryRestrict (pullDn z)`, so it suffices that
  `Fund.bdryRestrict X : K0 C(X × Ball ℂ) → K0 C(X × Sph ℂ)` is *injective*.  That follows from
  `Fund.sD_bijective` (so `sD` surjects), `bdryRestrict ∘ sD` = pull-back along the projection
  `X × S¹ → X` and the injectivity of the latter (it has the section `x ↦ (x, 1)`); pick whichever
  of `ev0_sD`/`sD_ev0` bookkeeping is convenient.
* (homotopy) `bp` and the south-pole section `bp' X = ⟨fun x => (x, dn 0)⟩` are joined by the
  sections `x ↦ (x, γ t)` with `γ t = mk3 (Real.sin (π t)) (Real.cos (π t))` (on the sphere since
  `sin² + cos² = 1`, continuous, `γ 0 = up 0`, `γ 1 = dn 0`).  For an idempotent representative `P`
  of `z` (`Work.KT.k0_rep`) the family `t ↦ P ∘ (x ↦ (x, γ t))` is a continuous path of idempotents
  over `C(X, ℂ)`, so `Work.KT.homotopy_inv` (with `𝔄 = C(X, ℂ)`, `R = ⊤`) gives
  `K0.map (pullAlg (bp X)) z = K0.map (pullAlg (bp' X)) z`; and `pullDn z = sD (ev0' (pullDn z))`
  with `ev0' = K0.mapA (pullAlg (bp' X))` finishes it. -/
theorem ker_r_subset_ker_pullDn (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    ∀ z : K0 C(X × S2, ℂ), Work.KT.Fund.r X z = 0 →
      K0.map (Work.KT.Fund.pullDn X) z = 0 := by
  intro z hz
  -- `r` factors through the upper-disc restriction, so `r z = 0` kills the upper-disc class
  have h1 := r_eq_ev0_comp_pullUp X z
  have hpu : K0.map (Fund.pullUp X) z = 0 := by
    have h2 : Fund.sD X (Fund.ev0 X (K0.map (Fund.pullUp X) z)) = 0 := by
      rw [← h1, hz, map_zero]
    rwa [Fund.sD_ev0 X (K0.map (Fund.pullUp X) z)] at h2
  -- the two disc restrictions agree on the circle, and the boundary restriction is injective
  have hcomp2 : (Fund.bdryRestrict X).comp (Fund.pullUp X)
      = (Fund.bdryRestrict X).comp (Fund.pullDn X) :=
    RingHom.ext fun g => Fund.bdryRestrict_pullUp_eq_pullDn X g
  have hb : K0.map (Fund.bdryRestrict X) (K0.map (Fund.pullUp X) z)
      = K0.map (Fund.bdryRestrict X) (K0.map (Fund.pullDn X) z) := by
    rw [← K0.map_comp_apply (Fund.pullUp X) (Fund.bdryRestrict X) z,
      ← K0.map_comp_apply (Fund.pullDn X) (Fund.bdryRestrict X) z, hcomp2]
  exact bdryRestrict_map_eq_zero X _
    (by rw [← hb, hpu, map_zero])

end

end Work.KT.ExtGen
