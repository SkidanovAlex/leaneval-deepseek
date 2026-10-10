import Mathlib
import Submission.Work.Twist.Defs
import Submission.Work.Twist.away_chart_mvPolynomial
import Submission.Work.Twist.exists_chart_away_X_zero_compat
import Submission.Work.Twist.ringHom_smooth_fromZeroRingHom_X_iff

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Twist

open CategoryTheory AlgebraicGeometry
open Work.Twist

set_option linter.style.haveILetI false

noncomputable section

/-!
# Smoothness of the projective model `ℙⁿ_𝕜`

`ℙⁿ_𝕜 = Proj 𝕜[X₀,…,Xₙ]` is smooth over `Spec 𝕜`.  This is one of the three conjuncts of
`ProjectiveModelGap 𝕜 n` (`Submission/Work/PointlessIndexFive/Model.lean`), and at `n = 1` it is
one of the three facts the pinned Mathlib is missing for a smooth projective curve.

The proof covers `Proj 𝕜[X₀,…,Xₙ]` by the charts `D₊(X_i)`, on each of which the structure
morphism is `Spec.map` of the ring homomorphism
`fromZeroRingHom 𝒜 (Submonoid.powers (X i)) : ↥(𝒜 0) →+* A⁰_{X_i}` (`Proj.awayι_toSpecZero`).
`Smooth` is Zariski-local on the source, so it suffices to show that each of those ring
homomorphisms is smooth.

For that, composing with a chart isomorphism `A⁰_{X_i} ≃+* 𝕜[y₁,…,yₙ]` turns the structure map
into the structure map `𝕜 → 𝕜[y₁,…,yₙ]`, which is (standard) smooth.  The chart isomorphism for
the standard chart `X₀`, together with the compatibility between it and the structure maps, is
`Work.Twist.exists_chart_away_X_zero_compat`; the transport from the chart `X₀` to an arbitrary
chart `X_i` (by the coordinate transposition `X₀ ↔ X_i`) is
`Work.Twist.ringHom_smooth_fromZeroRingHom_X_iff`.
-/

/-- The variable `X i` of the standard graded polynomial ring `𝕜[X₀,…,Xₙ]` is homogeneous of
degree one. -/
lemma X_mem_stdGrading (𝕜 : Type) [CommRing 𝕜] (n : ℕ) (i : Fin (n + 1)) :
    MvPolynomial.X i ∈ stdGrading 𝕜 n 1 :=
  MvPolynomial.isHomogeneous_X _ _

/-- `RingHom.Smooth` is invariant under post-composition with a ring isomorphism: if `e.comp f` is
smooth for a ring isomorphism `e`, then so is `f`. -/
lemma smooth_of_comp_ringEquiv {R S S' : Type} [CommRing R] [CommRing S] [CommRing S']
    (f : R →+* S) (e : S ≃+* S') (h : (e.toRingHom.comp f).Smooth) : f.Smooth := by
  have h1 : e.symm.toRingHom.Smooth := RingHom.Smooth.of_bijective e.symm.bijective
  have h2 : (e.symm.toRingHom.comp (e.toRingHom.comp f)).Smooth := RingHom.Smooth.comp h h1
  rwa [← RingHom.comp_assoc, RingEquiv.symm_toRingHom_comp_toRingHom, RingHom.id_comp] at h2

/-- **The chart ring `A⁰_{X_i}` of `ℙⁿ` is smooth over the constants.**  Composing the structure
map with the chart isomorphism `A⁰_{X_0} ≃+* 𝕜[y₁,…,yₙ]` of `Work.Twist.chartPsi` (and using
`Work.Twist.exists_chart_away_X_zero_compat` for the compatibility with the structure maps) turns
it into the structure map `𝕜 → 𝕜[y₁,…,yₙ]` composed with the isomorphism between the constants
`↥(stdGrading 𝕜 n 0)` and `𝕜`; the polynomial ring is (standard) smooth over the field `𝕜`, and
`RingHom.Smooth` is stable under composition and under ring isomorphisms.  The chart `X_i` is
reduced to the chart `X₀` by `Work.Twist.ringHom_smooth_fromZeroRingHom_X_iff`. -/
theorem ringHom_smooth_fromZeroRingHom_X (𝕜 : Type) [Field 𝕜] (n : ℕ) (i : Fin (n + 1)) :
    RingHom.Smooth (HomogeneousLocalization.fromZeroRingHom (stdGrading 𝕜 n)
        (Submonoid.powers (MvPolynomial.X i))) := by
  rw [ringHom_smooth_fromZeroRingHom_X_iff 𝕜 n i]
  obtain ⟨e, he⟩ := exists_chart_away_X_zero_compat 𝕜 n
  have hcomp : e.toRingHom.comp (HomogeneousLocalization.fromZeroRingHom (stdGrading 𝕜 n)
      (Submonoid.powers (MvPolynomial.X (0 : Fin (n + 1)))))
      = (algebraMap 𝕜 (MvPolynomial (Fin n) 𝕜)).comp
          (Work.PointlessIndexFive.zeroComponentEquiv 𝕜 n).toRingHom := by
    apply RingHom.ext
    intro c
    change e (HomogeneousLocalization.fromZeroRingHom (stdGrading 𝕜 n)
        (Submonoid.powers (MvPolynomial.X (0 : Fin (n + 1)))) c)
      = (algebraMap 𝕜 (MvPolynomial (Fin n) 𝕜)) (Work.PointlessIndexFive.zeroComponentEquiv 𝕜 n c)
    rw [he c, MvPolynomial.algebraMap_eq]
  have hp : (algebraMap 𝕜 (MvPolynomial (Fin n) 𝕜)).Smooth :=
    (RingHom.isStandardSmooth_algebraMap.mpr
      (Algebra.IsStandardSmooth.mvPolynomial (R := 𝕜) (Fin n))).smooth
  have hz : ((Work.PointlessIndexFive.zeroComponentEquiv 𝕜 n).toRingHom).Smooth :=
    RingHom.Smooth.of_bijective (Work.PointlessIndexFive.zeroComponentEquiv 𝕜 n).bijective
  exact smooth_of_comp_ringEquiv _ e (by rw [hcomp]; exact RingHom.Smooth.comp hz hp)

/-- The variables generate `𝕜[X₀,…,Xₙ]` over the ring of constants `↥(stdGrading 𝕜 n 0)`, so that
the charts `D₊(X_i)` cover `Proj 𝕜[X₀,…,Xₙ]` (`Proj.iSup_basicOpen_eq_top'`). -/
theorem adjoin_range_X_stdGrading_eq_top (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    Algebra.adjoin (↥(stdGrading 𝕜 n 0))
      (Set.range (fun i : Fin (n + 1) =>
        (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) 𝕜))) = ⊤ := by
  rw [eq_top_iff]
  intro p _
  let S : Set (MvPolynomial (Fin (n + 1)) 𝕜) :=
    Set.range (fun i : Fin (n + 1) => (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) 𝕜))
  change p ∈ (Algebra.adjoin (↥(stdGrading 𝕜 n 0)) S : Set (MvPolynomial (Fin (n + 1)) 𝕜))
  have key : ∀ x ∈ Algebra.adjoin 𝕜 S,
      x ∈ (Algebra.adjoin (↥(stdGrading 𝕜 n 0)) S : Set (MvPolynomial (Fin (n + 1)) 𝕜)) := by
    intro x hx
    refine Algebra.adjoin_induction (p := fun x _ =>
      x ∈ (Algebra.adjoin (↥(stdGrading 𝕜 n 0)) S : Set (MvPolynomial (Fin (n + 1)) 𝕜)))
      ?_ ?_ ?_ ?_ hx
    · intro x hx
      exact Algebra.subset_adjoin hx
    · intro r
      have hC : algebraMap 𝕜 (MvPolynomial (Fin (n + 1)) 𝕜) r
          = algebraMap (↥(stdGrading 𝕜 n 0)) (MvPolynomial (Fin (n + 1)) 𝕜)
              ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C _ r⟩ := by
        rw [MvPolynomial.algebraMap_eq]; rfl
      rw [hC]
      exact Subalgebra.algebraMap_mem _ _
    · intro x y _ _ hpx hpy
      exact add_mem hpx hpy
    · intro x y _ _ hpx hpy
      exact mul_mem hpx hpy
  exact key p (by rw [MvPolynomial.adjoin_range_X]; trivial)

/-- **`ℙⁿ_𝕜` is smooth over `Spec (𝒜 0)`**: `Proj.toSpecZero` is smooth for the standard graded
polynomial ring.  The charts `D₊(X_i)` cover `Proj 𝕜[X₀,…,Xₙ]`
(`Proj.iSup_basicOpen_eq_top'`, using `adjoin_range_X_stdGrading_eq_top`), and on the chart
`D₊(X_i)` the structure morphism is `Spec.map` of `fromZeroRingHom 𝒜 (Submonoid.powers (X i))`
(`Proj.awayι_toSpecZero`), which is smooth (`ringHom_smooth_fromZeroRingHom_X`). -/
theorem smooth_projToSpecZero (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    Smooth (Proj.toSpecZero (stdGrading 𝕜 n)) := by
  haveI : IsZariskiLocalAtSource @Smooth :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth) (Q := RingHom.Smooth)
  haveI : MorphismProperty.RespectsIso @Smooth := by
    rw [HasRingHomProperty.eq_affineLocally (P := @Smooth) (Q := RingHom.Smooth)]
    exact affineLocally_respectsIso (P := RingHom.Smooth) RingHom.Smooth.respectsIso
  have hcover : ⨆ i : Fin (n + 1), Proj.basicOpen (stdGrading 𝕜 n)
      (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) 𝕜) = ⊤ :=
    Proj.iSup_basicOpen_eq_top' (stdGrading 𝕜 n)
      (fun i : Fin (n + 1) => (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) 𝕜))
      (fun i => ⟨1, X_mem_stdGrading 𝕜 n i⟩) (adjoin_range_X_stdGrading_eq_top 𝕜 n)
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @Smooth)
    (fun i : Fin (n + 1) => Proj.basicOpen (stdGrading 𝕜 n) (MvPolynomial.X i)) hcover]
  intro i
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @Smooth)
      (Proj.basicOpenIsoSpec (stdGrading 𝕜 n) (MvPolynomial.X i)
        (X_mem_stdGrading 𝕜 n i) (by norm_num)).inv,
    ← Category.assoc, Proj.basicOpenIsoSpec_inv_ι, Proj.awayι_toSpecZero,
    HasRingHomProperty.Spec_iff (P := @Smooth)]
  simpa using ringHom_smooth_fromZeroRingHom_X 𝕜 n i

/-- **`ℙⁿ_𝕜` is smooth over `Spec 𝕜`.**  This is one of the three conjuncts of
`ProjectiveModelGap 𝕜 n` (`Submission/Work/PointlessIndexFive/Model.lean`); by
`curveModel_projectiveSpace_one` the three conjuncts at `n = 1` are exactly what is missing for a
`CurveModel 𝕜`.

Route: `Smooth` is a `HasRingHomProperty @Smooth RingHom.Smooth`, hence Zariski-local on the source;
the charts `D₊(X_i)` cover `ℙⁿ` (`Proj.iSup_basicOpen_eq_top`), each chart is
`Spec (Away 𝒜 X_i)` (`Proj.basicOpenIsoSpec`), and `Away 𝒜 X_i ≅ 𝕜[y₁,…,yₙ]` as rings
(`Twist.away_chart_mvPolynomial`, with the explicit map `Twist.chartPsi` and the dehomogenisation
`Twist.chartDhom`), which is smooth over the constants: composing with the ring isomorphism
`chartPsi` turns `fromZeroRingHom 𝒜 (Submonoid.powers (X i))` into the structure map of
`MvPolynomial (Fin n) 𝕜` (`𝒜 0 ≅ 𝕜 → 𝕜[y₁,…,yₙ]`, via `Work.PointlessIndexFive.zeroComponentEquiv`
and `Algebra.IsStandardSmooth.mvPolynomial`), and `RingHom.Smooth` transports along ring
isomorphisms and is stable under composition.  Finally `projectiveSpaceToSpec 𝕜 n` is
`Proj.toSpecZero 𝒜` composed with `Spec.map` of the ring isomorphism `𝒜 0 ≅ 𝕜`, and `Smooth` is
stable under composition. -/
theorem smooth_projectiveSpaceToSpec (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    Smooth (Work.PointlessIndexFive.projectiveSpaceToSpec 𝕜 n) := by
  haveI : Smooth (Proj.toSpecZero (stdGrading 𝕜 n)) := smooth_projToSpecZero 𝕜 n
  haveI : Smooth (Spec.map ((Work.PointlessIndexFive.zeroComponentEquiv 𝕜 n).toCommRingCatIso.inv)) :=
    inferInstance
  show Smooth (Proj.toSpecZero (stdGrading 𝕜 n) ≫
    Spec.map ((Work.PointlessIndexFive.zeroComponentEquiv 𝕜 n).toCommRingCatIso.inv))
  infer_instance

end

end Work.Twist

