import Mathlib
import Submission.Work.GroupChunk.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option linter.style.haveILetI false

namespace Work.GroupChunk

open CategoryTheory AlgebraicGeometry
open scoped MonoidalCategory
open scoped Work.GCBasics
open Work.GCBasics

universe u

/-- **The value of a RESID map is computed by any lift of its argument.**

Let `σ : X ⤏ Y` be a rational map of `K`-schemes with `X` reduced and `Y` separated over `K`,
let `p` be a point of `X` whose closed point lands in `dom σ`, and let `q` be a point of `dom σ`
lifting `p` (i.e. `q ≫ σ.domain.ι = p`).  Then the underlying point of the value `σ(p)` is the
image of the underlying point of `q` under the partial map `σ.toPartialMap.hom`.

This is the computation lurking in `Work.GroupChunk.value`: the value is built from the
canonical choice of a lift of `p` through `dom σ`, and that lift is unique. -/
theorem value_left {K : Type u} [Field K] {X Y : Sch K} (hred : IsReduced X.left)
    (hsep : IsSeparated Y.hom)
    (σ : X.left ⤏ Y.left) (hσ : σ.IsOver (Spec (CommRingCat.of K)))
    {F : Type u} [Field F] [Algebra K F] (p : FPt X F)
    (hp : RPt.LandsIn p σ.domain)
    (q : FPt (Opens.toOver σ.toPartialMap.domain) F)
    (hq : q ≫ Opens.ιOver σ.toPartialMap.domain = p) :
    (value hred hsep σ hσ p hp).left (IsLocalRing.closedPoint F) =
      (σ.toPartialMap).hom (q.left (IsLocalRing.closedPoint F)) := by
  rw [value]
  simp only [Over.homMk_left]
  have hspec := Classical.choose_spec
    (RPt.factor_of_closed_landsIn (K := K) σ.toPartialMap.domain p hp)
  have hq0 : Classical.choose
      (RPt.factor_of_closed_landsIn (K := K) σ.toPartialMap.domain p hp) = q :=
    (hspec.2 q hq).symm
  rw [hq0]
  exact Scheme.Hom.comp_apply _ _ _

/-- **The chart `V` is contained in the transition domain `W i i`.**

On the chart, `ℓ = 1` everywhere, so the RESID map `σ i i` (whose VALUE is
`divOf σ(x) + E_i ∼ divOf x + E_i`) is defined at every point of `V` and its value is a point
`y` with `ℓ(divOf y) = 1`; since `divOf y ∼ divOf x`, the uniqueness of the effective
representative of a divisor with `ℓ = 1` forces `divOf y = divOf x`, hence `y = x` by
injectivity of `divOf` on symmetric powers.  Thus `σ i i` restricts to the identity on `V` and
`V ⊆ dom σ_ii ∩ σ_ii⁻¹V = W i i`. -/
theorem le_W_self {K : Type u} [Field K] {C : CurveBasics.Curve K}
    {P0 : 𝟙_ (Sch K) ⟶ C.toOver} [SpecLin.DivBase C]
    [D : Input C P0] (i : D.Idx) : D.V ≤ W i i := by
  intro x hx
  rw [W]
  have hxV : RPt.LandsIn (resPt (D.Sym D.g) x) D.V :=
    (resPt_landsIn_iff (D.Sym D.g) x D.V).mpr hx
  obtain ⟨pV, hpV, -⟩ := FPt.factor_of_landsIn D.V (resPt (D.Sym D.g) x) hxV
  have hell : ell C (D.divOf D.g (resPt (D.Sym D.g) x)) = 1 := by
    have h := D.ell_eq_one_of_landsIn pV
    rwa [hpV] at h
  have hdom : x ∈ (σ i i).domain := by
    refine σ_mem_domain i i x ?_
    simpa only [add_sub_cancel_right] using hell
  have hpdom : RPt.LandsIn (resPt (D.Sym D.g) x) (σ i i).domain :=
    (resPt_landsIn_iff (D.Sym D.g) x (σ i i).domain).mpr hdom
  have hval := σ_value i i (resPt (D.Sym D.g) x) hpdom
  have hlin : LinEquiv C (D.divOf D.g (σVal i i (resPt (D.Sym D.g) x) hpdom))
      (D.divOf D.g (resPt (D.Sym D.g) x)) :=
    (LinEquiv.add_iff _ _ _).mp hval
  have heff : (D.divOf D.g (resPt (D.Sym D.g) x)).IsEffective :=
    (D.symGeom D.g).divOf_isEffective _
  have heff' : (D.divOf D.g (σVal i i (resPt (D.Sym D.g) x) hpdom)).IsEffective :=
    (D.symGeom D.g).divOf_isEffective _
  have hdiv_eq : D.divOf D.g (resPt (D.Sym D.g) x) =
      D.divOf D.g (σVal i i (resPt (D.Sym D.g) x) hpdom) :=
    linEquiv_eq_of_ell_eq_one heff hell heff' (LinEquiv.symm hlin)
  have heqp : (resPt (D.Sym D.g) x) = σVal i i (resPt (D.Sym D.g) x) hpdom :=
    (D.symGeom D.g).divOf_injective _ _ hdiv_eq
  obtain ⟨y, hy, -⟩ := FPt.factor_of_landsIn (σPM i i).domain (resPt (D.Sym D.g) x) hpdom
  have hpt2 : (σVal i i (resPt (D.Sym D.g) x) hpdom).left (IsLocalRing.closedPoint _) =
      (σPM i i).hom (y.left (IsLocalRing.closedPoint _)) :=
    value_left (inferInstance : IsReduced (D.Sym D.g).left)
      (by haveI := D.isProper_Sym D.g; exact inferInstance) (σ i i) (σ_isOver i i)
      (resPt (D.Sym D.g) x) hpdom y hy
  have hpt1 : (σVal i i (resPt (D.Sym D.g) x) hpdom).left (IsLocalRing.closedPoint _) = x := by
    rw [← heqp]
    exact resPt_apply (D.Sym D.g) x _
  have hhom : (σPM i i).hom (y.left (IsLocalRing.closedPoint _)) = x := by
    rw [← hpt2, hpt1]
  change x ∈ ⇑((σPM i i).domain.ι) '' (((σPM i i).hom ⁻¹ᵁ D.V) : Set _)
  refine ⟨y.left (IsLocalRing.closedPoint _), ?_, ?_⟩
  · refine (Scheme.Hom.mem_preimage (f := (σPM i i).hom) (U := D.V)
      (x := y.left (IsLocalRing.closedPoint _))).mpr ?_
    rw [hhom]
    exact hx
  · have h2 : ((Over.Hom.left y) ≫ (σPM i i).domain.ι) = (resPt (D.Sym D.g) x).left := by
      have h := congrArg Over.Hom.left hy
      simpa only [Over.comp_left, Opens.ιOver_left] using h
    calc (σPM i i).domain.ι ((Over.Hom.left y) (IsLocalRing.closedPoint _))
        = (((Over.Hom.left y) ≫ (σPM i i).domain.ι) (IsLocalRing.closedPoint _)) :=
          (Scheme.Hom.comp_apply _ _ _).symm
      _ = ((resPt (D.Sym D.g) x).left (IsLocalRing.closedPoint _)) :=
          congrArg (fun f => f (IsLocalRing.closedPoint _)) h2
      _ = x := resPt_apply (D.Sym D.g) x _

theorem U_self {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : 𝟙_ (Work.GCBasics.Sch K) ⟶ C.toOver} [Work.SpecLin.DivBase C]
    [D : Work.GroupChunk.Input C P0] (i : D.Idx) :
    Work.GroupChunk.U i i = ⊤ := by
  have hle : D.V ≤ W i i := le_W_self i
  have htop : D.V.ι ⁻¹ᵁ W i i = ⊤ := by
    apply TopologicalSpace.Opens.ext
    rw [TopologicalSpace.Opens.coe_top, Set.eq_univ_iff_forall]
    intro y
    show D.V.ι y ∈ W i i
    exact hle (Set.mem_of_mem_of_subset (Set.mem_range_self y)
      (le_of_eq (Scheme.Opens.range_ι D.V)))
  rw [U]
  exact htop

end Work.GroupChunk
