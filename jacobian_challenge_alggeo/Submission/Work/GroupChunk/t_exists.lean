import Mathlib
import Submission.Work.GroupChunk.sigmaOnW_value
import Submission.Work.GroupChunk.landsIn_U_iff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.GroupChunk

open CategoryTheory AlgebraicGeometry
open scoped MonoidalCategory
open scoped Work.GCBasics

universe u

noncomputable section

open Work.GCBasics

namespace TExistsAux

variable {K : Type u} [Field K] {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver}
  [SpecLin.DivBase C] [D : Input C P0]

/-- The inclusion `U i j ↪ W i j` followed by the inclusion `W i j ↪ Sym^g C` is `Uι i j`. -/
theorem UToW_ιOver (i j : D.Idx) :
    UToW i j ≫ Opens.ιOver (W i j) = Uι i j := by
  apply Over.OverMorphism.ext
  show IsOpenImmersion.lift (W i j).ι (Uι i j).left _ ≫ (W i j).ι = (Uι i j).left
  rw [IsOpenImmersion.lift_fac]

/-- `σVal i j` only depends on the point at which it is evaluated (the lift of a point of the
domain of a rational map used in `value` is unique). -/
theorem σVal_congr (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    {x y : FPt (D.Sym D.g) F} (hxy : x = y)
    (hx : RPt.LandsIn x (σ i j).domain) (hy : RPt.LandsIn y (σ i j).domain) :
    σVal i j x hx = σVal i j y hy := by
  apply Over.OverMorphism.ext
  obtain ⟨q, hq, -⟩ := RPt.factor_of_closed_landsIn ((σ i j).domain) x hx
  have h1 := value_left_eq (hred := inferInstance) (hsep := inferInstance)
    (σ i j) (σ_isOver i j) x hx q hq
  have h2 := value_left_eq (hred := inferInstance) (hsep := inferInstance)
    (σ i j) (σ_isOver i j) y hy q (by rw [← hxy]; exact hq)
  exact h1.trans h2.symm

/-- The open `W i j` is the image of the preimage of `V` under the partial map of `σ i j`, so
`σOnW i j` maps `W i j` into `V`. -/
theorem range_σOnW_le_V (i j : D.Idx) : Set.range (σOnW i j).left ⊆ ↑D.V := by
  have hpre : (Scheme.homOfLE (D.Sym D.g).left (W_le_domain i j)
      ≫ (σPM i j).hom) ⁻¹ᵁ D.V = ⊤ := by
    have hS : (σPM i j).hom ⁻¹ᵁ D.V = (σPM i j).domain.ι ⁻¹ᵁ W i j := by
      unfold W
      exact (Scheme.Hom.preimage_image_eq (σPM i j).domain.ι _).symm
    rw [Scheme.Hom.comp_preimage, hS, ← Scheme.Hom.comp_preimage, Scheme.homOfLE_ι,
      Scheme.Opens.ι_preimage_self]
  rintro z ⟨w, rfl⟩
  have h1 : w ∈ (Scheme.homOfLE (D.Sym D.g).left (W_le_domain i j)
      ≫ (σPM i j).hom) ⁻¹ᵁ D.V := by
    rw [hpre]; exact trivial
  rw [Scheme.Hom.mem_preimage] at h1
  exact h1

/-- The value of `σ i j` on `W i j` lies in the chart `V`. -/
theorem landsIn_σOnW (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (p : FPt (Opens.toOver (W i j)) F) : RPt.LandsIn (p ≫ σOnW i j) D.V := by
  have h : (p ≫ σOnW i j).left (IsLocalRing.closedPoint F) =
      (σOnW i j).left (p.left (IsLocalRing.closedPoint F)) :=
    Scheme.Hom.comp_apply _ _ _
  show (p ≫ σOnW i j).left (IsLocalRing.closedPoint F) ∈ (D.V : Set (D.Sym D.g).left)
  rw [h]
  exact range_σOnW_le_V i j ⟨p.left (IsLocalRing.closedPoint F), rfl⟩

/-- **`tHom i j` computes the value of `σ i j`**: on the transition domain `U i j` the
morphism `tHom i j` agrees with `σVal i j`. -/
theorem tHom_eq_σVal (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (q : FPt (Opens.toOver (U i j)) F)
    (hq : RPt.LandsIn (q ≫ Uι i j) (σ i j).domain) :
    q ≫ tHom i j = σVal i j (q ≫ Uι i j) hq := by
  have hpt : (q ≫ UToW i j) ≫ Opens.ιOver (W i j) = q ≫ Uι i j := by
    rw [Category.assoc, UToW_ιOver i j]
  have hq' : RPt.LandsIn ((q ≫ UToW i j) ≫ Opens.ιOver (W i j)) (σ i j).domain :=
    hpt.symm ▸ hq
  have h1 : q ≫ tHom i j = (q ≫ UToW i j) ≫ σOnW i j := by
    rw [tHom, Category.assoc]
  have h2 := sigmaOnW_value i j (q ≫ UToW i j) hq'
  have h3 := σVal_congr i j hpt hq' hq
  exact h1.trans (h2.trans h3)

/-- The image of `tHom i j` lies in the chart `V`. -/
theorem tHom_landsIn_V (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (q : FPt (Opens.toOver (U i j)) F) : RPt.LandsIn (q ≫ tHom i j) D.V := by
  have h1 : q ≫ tHom i j = (q ≫ UToW i j) ≫ σOnW i j := by
    rw [tHom, Category.assoc]
  show (q ≫ tHom i j).left (IsLocalRing.closedPoint F) ∈ (D.V : Set (D.Sym D.g).left)
  rw [h1]
  exact landsIn_σOnW i j (q ≫ UToW i j)

/-- The image of `Uι i j` lies in the chart `V`. -/
theorem range_Uι_le_V (i j : D.Idx) : Set.range (Uι i j).left ⊆ ↑D.V := by
  have key : Set.range (Uι i j).left ⊆ Set.range (D.V.ι) := by
    rintro z ⟨w, rfl⟩
    exact ⟨(U i j).ι w, by
      rw [Uι, Over.comp_left, Opens.ιOver_left, Opens.ιOver_left, Scheme.Hom.comp_apply]⟩
  rwa [Scheme.Opens.range_ι] at key

/-- **`tHom i j` preserves the divisor class**: the class of the value of `σ i j` with respect
to the centre `E j` is the class of the original point with respect to `E i`. -/
theorem tHom_picOf (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (q : FPt (Opens.toOver (U i j)) F) :
    D.picOf j (q ≫ tHom i j) = D.picOf i (q ≫ Uι i j) := by
  have hx : RPt.LandsIn (q ≫ Uι i j) (W i j) :=
    range_Uι_le_W i j ⟨q.left (IsLocalRing.closedPoint F), rfl⟩
  have hq : RPt.LandsIn (q ≫ Uι i j) (σ i j).domain := W_le_domain i j hx
  rw [tHom_eq_σVal i j q hq]
  have hL : LinEquiv C ((D.symGeom D.g).divOf (σVal i j (q ≫ Uι i j) hq) + bcKF F (D.EDiv i))
      ((D.symGeom D.g).divOf (q ≫ Uι i j) + bcKF F (D.EDiv j)) :=
    σ_value i j (q ≫ Uι i j) hq
  have h2 : LinEquiv C ((D.symGeom D.g).divOf (σVal i j (q ≫ Uι i j) hq) - bcKF F (D.EDiv j))
      ((D.symGeom D.g).divOf (q ≫ Uι i j) - bcKF F (D.EDiv i)) := by
    have h3 := hL.add (-(bcKF F (D.EDiv i)) - bcKF F (D.EDiv j))
    have e1 : (D.symGeom D.g).divOf (σVal i j (q ≫ Uι i j) hq) + bcKF F (D.EDiv i)
        + (-(bcKF F (D.EDiv i)) - bcKF F (D.EDiv j))
        = (D.symGeom D.g).divOf (σVal i j (q ≫ Uι i j) hq) - bcKF F (D.EDiv j) := by abel
    have e2 : (D.symGeom D.g).divOf (q ≫ Uι i j) + bcKF F (D.EDiv j)
        + (-(bcKF F (D.EDiv i)) - bcKF F (D.EDiv j))
        = (D.symGeom D.g).divOf (q ≫ Uι i j) - bcKF F (D.EDiv i) := by abel
    rw [e1, e2] at h3
    exact h3
  rw [Input.picOf_def, Input.picOf_def]
  exact (Pic0.mk_eq_iff _ _).mpr (by simpa only [Input.EF_divOf] using h2)

/-- The image of `tHom i j` lies in `W j i`. -/
theorem tHom_landsIn_W (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (q : FPt (Opens.toOver (U i j)) F) : RPt.LandsIn (q ≫ tHom i j) (W j i) := by
  have hV := tHom_landsIn_V i j q
  obtain ⟨p, hp, -⟩ := FPt.factor_of_landsIn D.V (q ≫ tHom i j) hV
  have hIC : D.InChart i (D.picOf j (p ≫ Opens.ιOver D.V)) := by
    refine ⟨q ≫ Uι i j, ?_, ?_⟩
    · have h3 : (q ≫ Uι i j).left (IsLocalRing.closedPoint F) =
          (Uι i j).left (q.left (IsLocalRing.closedPoint F)) := Scheme.Hom.comp_apply _ _ _
      show (q ≫ Uι i j).left (IsLocalRing.closedPoint F) ∈ (D.V : Set (D.Sym D.g).left)
      rw [h3]
      exact range_Uι_le_V i j ⟨q.left (IsLocalRing.closedPoint F), rfl⟩
    · rw [hp]
      exact (tHom_picOf i j q).symm
  have hU : RPt.LandsIn p (U j i) := (landsIn_U_iff j i p).mpr hIC
  have h1 : D.V.ι (p.left (IsLocalRing.closedPoint F)) ∈ (W j i : Set (D.Sym D.g).left) :=
    (Scheme.Hom.mem_preimage (f := D.V.ι) (U := W j i)).mp hU
  have h2 : (p ≫ Opens.ιOver D.V).left (IsLocalRing.closedPoint F) =
      D.V.ι (p.left (IsLocalRing.closedPoint F)) :=
    Scheme.Hom.comp_apply _ _ _
  have h4 : (p ≫ Opens.ιOver D.V).left (IsLocalRing.closedPoint F) ∈ (W j i : Set _) := by
    rw [h2]; exact h1
  show (q ≫ tHom i j).left (IsLocalRing.closedPoint F) ∈ (W j i : Set (D.Sym D.g).left)
  rw [← hp]
  exact h4

/-- The range of `tHom i j` is contained in `U j i` (as an open of the chart `V`). -/
theorem range_tHom_le (i j : D.Idx) : Set.range (tHom i j).left ⊆ Set.range (Uι j i).left := by
  have hUj : Set.range (Uι j i).left = ↑(D.V ⊓ W j i) := by
    rw [Uι, Over.comp_left, Opens.ιOver_left, Opens.ιOver_left]
    rw [show ⇑((U j i).ι ≫ D.V.ι) = ⇑(D.V.ι) ∘ ⇑((U j i).ι) from
      funext fun w => Scheme.Hom.comp_apply _ _ _]
    rw [Set.range_comp, Scheme.Opens.range_ι, ← Scheme.Hom.coe_image (f := D.V.ι)]
    unfold U
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  rw [hUj]
  rintro z ⟨w, rfl⟩
  have hres : RPt.LandsIn ((resPt (Opens.toOver (U i j)) w) ≫ tHom i j) (D.V ⊓ W j i) := by
    show ((resPt (Opens.toOver (U i j)) w) ≫ tHom i j).left
      (IsLocalRing.closedPoint (resField (Opens.toOver (U i j)) w)) ∈ ↑(D.V ⊓ W j i)
    exact ⟨tHom_landsIn_V i j _, tHom_landsIn_W i j _⟩
  rw [RPt.landsIn_preimage] at hres
  rw [resPt_landsIn_iff] at hres
  rwa [Scheme.Hom.mem_preimage] at hres

end TExistsAux

/-- **Existence of the transition morphism.**  The transition `t i j : U i j ⟶ U j i` is the
restriction of `σ i j` to `U i j`: it computes the value of `σ i j` and it preserves the
divisor class. -/
theorem t_exists {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : 𝟙_ (Work.GCBasics.Sch K) ⟶ C.toOver} [Work.SpecLin.DivBase C]
    [D : Work.GroupChunk.Input C P0] (i j : D.Idx) :
    ∃ t : Work.GCBasics.Opens.toOver (Work.GroupChunk.U i j) ⟶
        Work.GCBasics.Opens.toOver (Work.GroupChunk.U j i),
      (∀ {F : Type u} [Field F] [Algebra K F]
          (p : Work.GCBasics.FPt (Work.GCBasics.Opens.toOver (Work.GroupChunk.U i j)) F)
          (hp : Work.GCBasics.RPt.LandsIn (p ≫ Work.GroupChunk.Uι i j)
            (Work.GroupChunk.σ i j).domain),
          p ≫ t ≫ Work.GroupChunk.Uι j i = Work.GroupChunk.σVal i j _ hp)
      ∧ (∀ {F : Type u} [Field F] [Algebra K F]
          (p : Work.GCBasics.FPt (Work.GCBasics.Opens.toOver (Work.GroupChunk.U i j)) F),
          D.picOf j (p ≫ t ≫ Work.GroupChunk.Uι j i) = D.picOf i (p ≫ Work.GroupChunk.Uι i j)) := by
  have hrange : Set.range (tHom i j).left ⊆ Set.range (Uι j i).left :=
    TExistsAux.range_tHom_le i j
  haveI hι : IsOpenImmersion (Uι j i).left := by
    rw [Uι, Over.comp_left, Opens.ιOver_left, Opens.ιOver_left]
    infer_instance
  let t : Opens.toOver (U i j) ⟶ Opens.toOver (U j i) :=
    Over.homMk (IsOpenImmersion.lift (Uι j i).left (tHom i j).left hrange) (by
      rw [← Over.w (Uι j i), ← Category.assoc, IsOpenImmersion.lift_fac,
        Over.w (tHom i j)])
  have ht : t ≫ Uι j i = tHom i j := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left]
    exact IsOpenImmersion.lift_fac (Uι j i).left (tHom i j).left hrange
  refine ⟨t, ?_, ?_⟩
  · intro F _ _ p hp
    rw [ht]
    exact TExistsAux.tHom_eq_σVal i j p hp
  · intro F _ _ p
    rw [ht]
    exact TExistsAux.tHom_picOf i j p

end

end Work.GroupChunk
