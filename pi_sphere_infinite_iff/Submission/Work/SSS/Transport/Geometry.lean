import Mathlib
import Submission.Work.SSS.Transport.SquareSetup
import Submission.Work.SSS.Transport.inclChains_naturality

/-!
# The corner comparison of the fibre transports along the edges of a homotopy square

This file compares the fibre transport of a Serre fibration along a path with the transport computed
through the corner fibres of the square pullback along a homotopy square.  The main inputs are
`Work.SSS.Transport.inclChains_naturality` (naturality of the inclusion of relative chains), the
contraction of the square to a corner (`Work.SSS.sqContr`) and the homotopy invariance of the slice
maps `e ↦ (e, (t, s₀))` (`Work.SSS.homologyMap_sideMap_eq`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.SSS

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

def cornerIso (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (G : C(unitInterval × unitInterval, B)) (c : unitInterval × unitInterval) (j : ℕ) :
    (Work.PiS.HZ ↥(sqCorner p G c) j) ≅ (Work.PiS.HZ (Work.StemsB.Pullback p G) j) :=
  sqCornerInclIso p hp G c j

def fibreCornerIso (p : C(E, B)) (G : C(unitInterval × unitInterval, B))
    (c : unitInterval × unitInterval) {b : B} (h : G c = b) (j : ℕ) :
    (Work.PiS.HZ (Work.StemsB.fibre p b) j) ≅ (Work.PiS.HZ ↥(sqCorner p G c) j) :=
  HZHomeoIso (fibreCornerHomeo p G c b h) j

theorem iso_cancel_iso {C : Type*} [Category C] {A B D C₁ C₂ E : C}
    (i₀ : A ≅ D) (i₁ : B ≅ D) (h₀ : A ≅ C₁) (h₁ : B ≅ C₂) (k₀ : C₁ ≅ E) (k₁ : C₂ ≅ E)
    (j : D ⟶ E) (e₀ : i₀.hom ≫ j = h₀.hom ≫ k₀.hom) (e₁ : i₁.hom ≫ j = h₁.hom ≫ k₁.hom) :
    i₀ ≪≫ i₁.symm = h₀ ≪≫ k₀ ≪≫ k₁.symm ≪≫ h₁.symm :=
  Iso.ext (iso_cancel i₀ i₁ h₀ h₁ k₀ k₁ j e₀ e₁)

theorem pullbackTransportIso_sq (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (G : C(unitInterval × unitInterval, B)) (t₀ : unitInterval) (γ : C(unitInterval, B))
    (hγ : ∀ s, G (t₀, s) = γ s) (j : ℕ) :
    pullbackTransportIso p hp γ j =
      HZHomeoIso (sliceFibreHomeo p G t₀ γ hγ 0) j ≪≫
        cornerIso p hp G (t₀, 0) j ≪≫ (cornerIso p hp G (t₀, 1) j).symm ≪≫
        (HZHomeoIso (sliceFibreHomeo p G t₀ γ hγ 1) j).symm := by
  have hn := Work.SSS.Transport.inclChains_naturality (X := TopCat.of (Work.StemsB.Pullback p γ))
    (A := edgeFibre p γ 0) (Y := TopCat.of (Work.StemsB.Pullback p G))
    (B := sqCorner p G (t₀, 0)) (f := TopCat.ofHom (sliceEmb p G t₀ γ hγ))
    (g := (sliceFibreHomeo p G t₀ γ hγ 0 : C(↥(edgeFibre p γ 0), ↥(sqCorner p G (t₀, 0)))))
    (fun a => rfl)
  have hn' : HomologicalComplex.homologyMap
        (Work.Cohomology.inclChains (TopCat.of (Work.StemsB.Pullback p γ)) (edgeFibre p γ 0)) j ≫
      HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (TopCat.of (Work.StemsB.Pullback p γ))
          (TopCat.of (Work.StemsB.Pullback p G)) (TopCat.ofHom (sliceEmb p G t₀ γ hγ))) j =
      HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (TopCat.of ↥(edgeFibre p γ 0))
          (TopCat.of ↥(sqCorner p G (t₀, 0)))
          (TopCat.ofHom (sliceFibreHomeo p G t₀ γ hγ 0))) j ≫
      HomologicalComplex.homologyMap
        (Work.Cohomology.inclChains (TopCat.of (Work.StemsB.Pullback p G))
          (sqCorner p G (t₀, 0))) j := by
    have h := congrArg (fun φ => HomologicalComplex.homologyMap φ j) hn
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
    exact h
  have hn1 := Work.SSS.Transport.inclChains_naturality (X := TopCat.of (Work.StemsB.Pullback p γ))
    (A := edgeFibre p γ 1) (Y := TopCat.of (Work.StemsB.Pullback p G))
    (B := sqCorner p G (t₀, 1)) (f := TopCat.ofHom (sliceEmb p G t₀ γ hγ))
    (g := (sliceFibreHomeo p G t₀ γ hγ 1 : C(↥(edgeFibre p γ 1), ↥(sqCorner p G (t₀, 1)))))
    (fun a => rfl)
  have hn1' : HomologicalComplex.homologyMap
        (Work.Cohomology.inclChains (TopCat.of (Work.StemsB.Pullback p γ)) (edgeFibre p γ 1)) j ≫
      HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (TopCat.of (Work.StemsB.Pullback p γ))
          (TopCat.of (Work.StemsB.Pullback p G)) (TopCat.ofHom (sliceEmb p G t₀ γ hγ))) j =
      HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (TopCat.of ↥(edgeFibre p γ 1))
          (TopCat.of ↥(sqCorner p G (t₀, 1)))
          (TopCat.ofHom (sliceFibreHomeo p G t₀ γ hγ 1))) j ≫
      HomologicalComplex.homologyMap
        (Work.Cohomology.inclChains (TopCat.of (Work.StemsB.Pullback p G))
          (sqCorner p G (t₀, 1))) j := by
    have h := congrArg (fun φ => HomologicalComplex.homologyMap φ j) hn1
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
    exact h
  rw [pullbackTransportIso_eq p hp γ j]
  refine iso_cancel_iso (edgeInclIso p hp γ 0 j) (edgeInclIso p hp γ 1 j)
    (HZHomeoIso (sliceFibreHomeo p G t₀ γ hγ 0) j)
    (HZHomeoIso (sliceFibreHomeo p G t₀ γ hγ 1) j)
    (cornerIso p hp G (t₀, 0) j) (cornerIso p hp G (t₀, 1) j)
    (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of (Work.StemsB.Pullback p γ))
        (TopCat.of (Work.StemsB.Pullback p G)) (TopCat.ofHom (sliceEmb p G t₀ γ hγ))) j) ?_ ?_
  · rw [edgeInclIso, cornerIso, sqCornerInclIso, HZHomeoIso_hom, asIso_hom, asIso_hom]
    exact hn'
  · rw [edgeInclIso, cornerIso, sqCornerInclIso, HZHomeoIso_hom, asIso_hom, asIso_hom]
    exact hn1'

theorem fibreCornerIso_comp_cornerIso (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (G : C(unitInterval × unitInterval, B)) (t s₀ : unitInterval) {b : B}
    (hb : G (t, s₀) = b) (hside : ∀ u, G (u, s₀) = b) (j : ℕ) :
    (fibreCornerIso p G (t, s₀) hb j ≪≫ cornerIso p hp G (t, s₀) j).hom =
      HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (TopCat.of (Work.StemsB.fibre p b))
          (TopCat.of (Work.StemsB.Pullback p G)) (TopCat.ofHom (sideMap p G s₀ hside t))) j := by
  rw [Iso.trans_hom, fibreCornerIso, cornerIso, sqCornerInclIso, HZHomeoIso_hom, asIso_hom,
    Work.Cohomology.inclChains, chain_homologyMap_comp]
  congr 1

theorem pullbackFibreHomeo_symm_trans_sliceFibreHomeo (p : C(E, B))
    (G : C(unitInterval × unitInterval, B)) (t₀ s₀ : unitInterval) (γ : C(unitInterval, B))
    (hγ : ∀ s, G (t₀, s) = γ s) (b : B) (hb : γ s₀ = b) (j : ℕ) :
    (HZHomeoIso (pullbackFibreHomeo p γ s₀) j).symm ≪≫
        HZHomeoIso (sliceFibreHomeo p G t₀ γ hγ s₀) j =
      (HZHomeoIso (homeoFibreEq p hb.symm) j).symm ≪≫
        fibreCornerIso p G (t₀, s₀) ((hγ s₀).trans hb) j := by
  have hA := congrArg (fun e => HZHomeoIso e j)
    (homeoFibreEq_trans_sliceFibreHomeo p G t₀ s₀ γ hγ b hb ((hγ s₀).trans hb))
  rw [HZHomeoIso_trans, HZHomeoIso_trans, ← HZHomeoIso_symm] at hA
  simp only [Iso.trans_assoc] at hA
  calc (HZHomeoIso (pullbackFibreHomeo p γ s₀) j).symm ≪≫
        HZHomeoIso (sliceFibreHomeo p G t₀ γ hγ s₀) j
      = (HZHomeoIso (homeoFibreEq p hb.symm) j).symm ≪≫
          (HZHomeoIso (homeoFibreEq p hb.symm) j ≪≫
            (HZHomeoIso (pullbackFibreHomeo p γ s₀) j).symm ≪≫
            HZHomeoIso (sliceFibreHomeo p G t₀ γ hγ s₀) j) := by
        simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]
    _ = (HZHomeoIso (homeoFibreEq p hb.symm) j).symm ≪≫
          fibreCornerIso p G (t₀, s₀) ((hγ s₀).trans hb) j := by
        rw [hA]
        simp only [fibreCornerIso]

theorem sliceFibreHomeo_symm_trans_pullbackFibreHomeo (p : C(E, B))
    (G : C(unitInterval × unitInterval, B)) (t₀ s₀ : unitInterval) (γ : C(unitInterval, B))
    (hγ : ∀ s, G (t₀, s) = γ s) (b : B) (hb : γ s₀ = b) (j : ℕ) :
    (HZHomeoIso (sliceFibreHomeo p G t₀ γ hγ s₀) j).symm ≪≫
        HZHomeoIso (pullbackFibreHomeo p γ s₀) j =
      (fibreCornerIso p G (t₀, s₀) ((hγ s₀).trans hb) j).symm ≪≫
        (HZHomeoIso (homeoFibreEq p hb) j).symm := by
  have hB := congrArg (fun e => HZHomeoIso e j)
    (sliceFibreHomeo_symm_trans_homeoFibreEq p G t₀ s₀ γ hγ b hb ((hγ s₀).trans hb))
  rw [HZHomeoIso_trans, HZHomeoIso_trans, ← HZHomeoIso_symm] at hB
  simp only [Iso.trans_assoc] at hB
  calc (HZHomeoIso (sliceFibreHomeo p G t₀ γ hγ s₀) j).symm ≪≫
        HZHomeoIso (pullbackFibreHomeo p γ s₀) j
      = ((HZHomeoIso (sliceFibreHomeo p G t₀ γ hγ s₀) j).symm ≪≫
            HZHomeoIso (pullbackFibreHomeo p γ s₀) j ≪≫
            HZHomeoIso (homeoFibreEq p hb) j) ≪≫
          (HZHomeoIso (homeoFibreEq p hb) j).symm := by
        simp only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]
    _ = (fibreCornerIso p G (t₀, s₀) ((hγ s₀).trans hb) j).symm ≪≫
          (HZHomeoIso (homeoFibreEq p hb) j).symm := by
        rw [hB, ← HZHomeoIso_symm]
        rfl

/-! ## The corner comparison along the two horizontal edges of the square -/

/-- **The transport along the two horizontal edges of a homotopy square agree.**  The corner
inclusions of the square pullback give two isomorphisms between the homology of the corner fibres,
one along the bottom edge and one along the top edge; they agree once the corner fibres are
identified with the fibres of `p` over the endpoints of the homotopy. -/
theorem square_corner_identity (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (G : C(unitInterval × unitInterval, B)) {b b' : B}
    (h00 : G (0, 0) = b) (h10 : G (1, 0) = b) (h01 : G (0, 1) = b') (h11 : G (1, 1) = b')
    (hleft : ∀ u, G (u, 0) = b) (hright : ∀ u, G (u, 1) = b') (j : ℕ) :
    fibreCornerIso p G (0, 0) h00 j ≪≫ cornerIso p hp G (0, 0) j ≪≫
        (cornerIso p hp G (0, 1) j).symm ≪≫ (fibreCornerIso p G (0, 1) h01 j).symm =
      fibreCornerIso p G (1, 0) h10 j ≪≫ cornerIso p hp G (1, 0) j ≪≫
        (cornerIso p hp G (1, 1) j).symm ≪≫ (fibreCornerIso p G (1, 1) h11 j).symm := by
  have hVL : fibreCornerIso p G (0, 0) h00 j ≪≫ cornerIso p hp G (0, 0) j =
      fibreCornerIso p G (1, 0) h10 j ≪≫ cornerIso p hp G (1, 0) j := by
    refine Iso.ext ?_
    rw [fibreCornerIso_comp_cornerIso p hp G 0 0 h00 hleft j,
      fibreCornerIso_comp_cornerIso p hp G 1 0 h10 hleft j]
    exact homologyMap_sideMap_eq p G 0 hleft j
  have hVR : fibreCornerIso p G (0, 1) h01 j ≪≫ cornerIso p hp G (0, 1) j =
      fibreCornerIso p G (1, 1) h11 j ≪≫ cornerIso p hp G (1, 1) j := by
    refine Iso.ext ?_
    rw [fibreCornerIso_comp_cornerIso p hp G 0 1 h01 hright j,
      fibreCornerIso_comp_cornerIso p hp G 1 1 h11 hright j]
    exact homologyMap_sideMap_eq p G 1 hright j
  have hVR' : (cornerIso p hp G (0, 1) j).symm ≪≫ (fibreCornerIso p G (0, 1) h01 j).symm =
      (cornerIso p hp G (1, 1) j).symm ≪≫ (fibreCornerIso p G (1, 1) h11 j).symm := by
    rw [← Iso.trans_symm, ← Iso.trans_symm, hVR]
  calc fibreCornerIso p G (0, 0) h00 j ≪≫ cornerIso p hp G (0, 0) j ≪≫
        (cornerIso p hp G (0, 1) j).symm ≪≫ (fibreCornerIso p G (0, 1) h01 j).symm
      = fibreCornerIso p G (0, 0) h00 j ≪≫ cornerIso p hp G (0, 0) j ≪≫
          ((cornerIso p hp G (1, 1) j).symm ≪≫ (fibreCornerIso p G (1, 1) h11 j).symm) := by
        rw [hVR']
    _ = (fibreCornerIso p G (0, 0) h00 j ≪≫ cornerIso p hp G (0, 0) j) ≪≫
          (cornerIso p hp G (1, 1) j).symm ≪≫ (fibreCornerIso p G (1, 1) h11 j).symm := by
        simp only [Iso.trans_assoc]
    _ = (fibreCornerIso p G (1, 0) h10 j ≪≫ cornerIso p hp G (1, 0) j) ≪≫
          (cornerIso p hp G (1, 1) j).symm ≪≫ (fibreCornerIso p G (1, 1) h11 j).symm := by
        rw [hVL]
    _ = fibreCornerIso p G (1, 0) h10 j ≪≫ cornerIso p hp G (1, 0) j ≪≫
          (cornerIso p hp G (1, 1) j).symm ≪≫ (fibreCornerIso p G (1, 1) h11 j).symm := by
        simp only [Iso.trans_assoc]

/-! ## The core of the transport along an edge -/

/-- **The core of the transport along a path, expressed through the corners of the square.**  The
composite of the inverse of `pullbackFibreHomeo`, the transport of the pullback and
`pullbackFibreHomeo` — the "core" of the fibre transport, between the fibres over the endpoints of
the path — is the composite of the corner isomorphisms of the square pullback along a homotopy whose
`t₀`-slice is the path, with the endpoint corrections supplied by `homeoFibreEq`. -/
theorem edgeCore_eq (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (G : C(unitInterval × unitInterval, B)) (t₀ : unitInterval) (γ : C(unitInterval, B))
    (hγ : ∀ s, G (t₀, s) = γ s) (b b' : B) (hs : γ 0 = b) (ht : γ 1 = b')
    (h0 : G (t₀, 0) = b) (h1 : G (t₀, 1) = b') (j : ℕ) :
    (HZHomeoIso (pullbackFibreHomeo p γ 0) j).symm ≪≫ pullbackTransportIso p hp γ j ≪≫
        HZHomeoIso (pullbackFibreHomeo p γ 1) j =
      (HZHomeoIso (homeoFibreEq p hs.symm) j).symm ≪≫
        fibreCornerIso p G (t₀, 0) h0 j ≪≫ cornerIso p hp G (t₀, 0) j ≪≫
        (cornerIso p hp G (t₀, 1) j).symm ≪≫
        (fibreCornerIso p G (t₀, 1) h1 j).symm ≪≫
        (HZHomeoIso (homeoFibreEq p ht) j).symm := by
  rw [show fibreCornerIso p G (t₀, 0) h0 j = fibreCornerIso p G (t₀, 0) ((hγ 0).trans hs) j
      from rfl,
    show fibreCornerIso p G (t₀, 1) h1 j = fibreCornerIso p G (t₀, 1) ((hγ 1).trans ht) j
      from rfl]
  calc (HZHomeoIso (pullbackFibreHomeo p γ 0) j).symm ≪≫ pullbackTransportIso p hp γ j ≪≫
        HZHomeoIso (pullbackFibreHomeo p γ 1) j
      = (HZHomeoIso (pullbackFibreHomeo p γ 0) j).symm ≪≫
          ((HZHomeoIso (sliceFibreHomeo p G t₀ γ hγ 0) j ≪≫ cornerIso p hp G (t₀, 0) j ≪≫
            (cornerIso p hp G (t₀, 1) j).symm ≪≫
            (HZHomeoIso (sliceFibreHomeo p G t₀ γ hγ 1) j).symm) ≪≫
          HZHomeoIso (pullbackFibreHomeo p γ 1) j) := by
        rw [pullbackTransportIso_sq p hp G t₀ γ hγ j]
    _ = ((HZHomeoIso (pullbackFibreHomeo p γ 0) j).symm ≪≫
          HZHomeoIso (sliceFibreHomeo p G t₀ γ hγ 0) j) ≪≫ cornerIso p hp G (t₀, 0) j ≪≫
          (cornerIso p hp G (t₀, 1) j).symm ≪≫
          ((HZHomeoIso (sliceFibreHomeo p G t₀ γ hγ 1) j).symm ≪≫
            HZHomeoIso (pullbackFibreHomeo p γ 1) j) := by
        simp only [Iso.trans_assoc]
    _ = ((HZHomeoIso (homeoFibreEq p hs.symm) j).symm ≪≫
          fibreCornerIso p G (t₀, 0) ((hγ 0).trans hs) j) ≪≫ cornerIso p hp G (t₀, 0) j ≪≫
          (cornerIso p hp G (t₀, 1) j).symm ≪≫
          ((fibreCornerIso p G (t₀, 1) ((hγ 1).trans ht) j).symm ≪≫
            (HZHomeoIso (homeoFibreEq p ht) j).symm) := by
        rw [pullbackFibreHomeo_symm_trans_sliceFibreHomeo p G t₀ 0 γ hγ b hs j,
          sliceFibreHomeo_symm_trans_pullbackFibreHomeo p G t₀ 1 γ hγ b' ht j]
    _ = (HZHomeoIso (homeoFibreEq p hs.symm) j).symm ≪≫
          fibreCornerIso p G (t₀, 0) ((hγ 0).trans hs) j ≪≫ cornerIso p hp G (t₀, 0) j ≪≫
          (cornerIso p hp G (t₀, 1) j).symm ≪≫
          (fibreCornerIso p G (t₀, 1) ((hγ 1).trans ht) j).symm ≪≫
          (HZHomeoIso (homeoFibreEq p ht) j).symm := by
        simp only [Iso.trans_assoc]


/-- The conjugated form of `Work.SSS.edgeCore_eq`, with a further factor on the right. -/
theorem edgeCore_eq_conj (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (G : C(unitInterval × unitInterval, B)) (t₀ : unitInterval) (γ : C(unitInterval, B))
    (hγ : ∀ s, G (t₀, s) = γ s) (b b' : B) (hs : γ 0 = b) (ht : γ 1 = b')
    (h0 : G (t₀, 0) = b) (h1 : G (t₀, 1) = b') (j : ℕ) {W : Type} [TopologicalSpace W]
    (B : Work.PiS.HZ (Work.StemsB.fibre p (γ 1)) j ≅ Work.PiS.HZ W j) :
    (HZHomeoIso (pullbackFibreHomeo p γ 0) j).symm ≪≫ pullbackTransportIso p hp γ j ≪≫
        HZHomeoIso (pullbackFibreHomeo p γ 1) j ≪≫ B =
      (HZHomeoIso (homeoFibreEq p hs.symm) j).symm ≪≫
        fibreCornerIso p G (t₀, 0) h0 j ≪≫ cornerIso p hp G (t₀, 0) j ≪≫
        (cornerIso p hp G (t₀, 1) j).symm ≪≫
        (fibreCornerIso p G (t₀, 1) h1 j).symm ≪≫
        (HZHomeoIso (homeoFibreEq p ht) j).symm ≪≫ B :=
  congrArg (fun e => e ≪≫ B) (edgeCore_eq p hp G t₀ γ hγ b b' hs ht h0 h1 j)


end
end Work.SSS
