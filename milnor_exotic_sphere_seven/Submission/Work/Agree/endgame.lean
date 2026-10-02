import Mathlib
import Submission.Work.Agree.crux
import Submission.Work.Agree.cLine
import Submission.Work.Agree.nonemptyThomClassClutchBundle
import Submission.Work.Agree.eulerClassIso
import Submission.Work.Agree.clutchShift
import Submission.Work.Transgression.Conclusion

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-! # AREA AGREE: the endgame — all remaining bricks as explicit hypotheses

Everything AGREE still owes is now reduced to four statements, each owned by a subproject or a
delegated lemma, and this file records the assembly:

1. `Work.Agree.EulerClutch` — the transgression brick (subproject `Submission/Work/Transgression/`):
   the Euler class of a clutched rank-`4` real bundle over `S⁴` is `±(a+b) · τ`.
2. `Work.Agree.ECIso` (delegated as `Work.Agree.eulerClassIso`) — a Thom class transports along a
   bundle isomorphism with the *same* Euler class (different model fibres allowed); this is the
   general real-bundle analogue of `Work.Thom.thomClassRank_eulerClass_iso`.
3. the degree-`2` Whitney formula for sums of two rank-`2` complex bundles over `S⁴`
   (subproject `Submission/Work/Whitney/`).
4. `Work.Agree.ComplexificationShift` (`Work.Agree.clutchShift`) — `ℂ(L^aR^b) ≅ ℂ(L^{a-b})`.

The chain proved here is

    (1) + (2) + (3)  ⟹  Work.Agree.BottHopf
    (4)              ⟹  Work.Agree.Crux          (via `crux_of_bottHopf_shift`)

and `agreeAll` is then `agreeAll_of_crux_geom` applied to `Crux` and the proved geometry
(`geomSplitting geometryB`).
-/

open scoped Manifold ContDiff Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.Agree

open Work.TangentClasses

noncomputable section

/-- **The Thom-class transport lemma**, as an explicit hypothesis: along a `BundleIso` of real
bundles (model fibres may differ) every Thom class has a transported Thom class with the *same*
Euler class.  Delegated as `Work.Agree.eulerClassIso`
(`Submission/Work/Agree/eulerClassIso.lean`). -/
def ECIso : Prop :=
  ∀ {B : Type} [TopologicalSpace B] {F F' : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] {ι ι' : Type} {n : ℕ}
    (Z : RealBundle B F ι) (Z' : RealBundle B F' ι') (e : Work.Thom.BundleIso Z Z')
    (T : Work.Thom.ThomClass Z n),
    ∃ T' : Work.Thom.ThomClass Z' n, T'.eulerClass = T.eulerClass

/-- **The rank-`2` Chern class of `V_a = cLine a` from the Euler-class brick.**

`c₂(V_a)` is, by `Work.Thom.chernClass_succ_top'`, the Euler class of the canonical Thom class of
the realification of `V_a`; transporting along `realification_cLine_iso_clutchBundle` turns that into
the Euler class of a Thom class of `L^a = clutchBundle a 0`, to which `EulerClutch` applies and
yields `± a · τ`; injectivity of `π^*` (`injective_HMap_discProj`) removes the pullback. -/
theorem cLineChern_of_eulerClutch (hiso : ECIso) (hE : EulerClutch) (a : ℤ) (G : H 4 S4)
    (hG : (HMap discProj 4).hom G = Work.Milnor.tauD) :
    Work.Thom.chernClass 2 2 (cLine a) = a • G ∨
    Work.Thom.chernClass 2 2 (cLine a) = -(a • G) := by
  obtain ⟨e⟩ := realification_cLine_iso_clutchBundle a
  obtain ⟨T', hT'⟩ := hiso (Work.Thom.realification (cLine a)) (clutchBundle a 0) e
    (Work.Thom.thomClassRank 2 (by norm_num) (cLine a))
  have hkey : Work.Thom.chernClass 2 2 (cLine a) = T'.eulerClass := by
    rw [Work.Thom.chernClass_succ_top' (cLine a), ← hT']
  have hbrick := hE a 0 T'
  have hx : (HMap discProj 4).hom (Work.Thom.chernClass 2 2 (cLine a))
        = (HMap discProj 4).hom (a • G) ∨
      (HMap discProj 4).hom (Work.Thom.chernClass 2 2 (cLine a))
        = (HMap discProj 4).hom (-(a • G)) := by
    rw [hkey]
    rcases hbrick with hb | hb
    · left
      rw [hb, show (a + 0 : ℤ) = a from by ring, map_zsmul, hG]
    · right
      rw [hb, show (a + 0 : ℤ) = a from by ring, map_neg, map_zsmul, hG]
  rcases hx with hx | hx
  · exact Or.inl (injective_HMap_discProj 4 hx)
  · exact Or.inr (injective_HMap_discProj 4 hx)

/-- **`BottHopf` from the four bricks** (here: the Euler brick, the transport lemma and the
degree-`2` Whitney formula — the shift is not needed for this step). -/
theorem bottHopf_of_bricks_all (hiso : ECIso) (hE : EulerClutch)
    (hW : ∀ (U V : VectorBundleCore ℂ S4 (EuclideanSpace ℂ (Fin 2)) Bool),
      Work.Thom.chernClass 4 2 (Whitney.whitneySum U V)
        = Work.Thom.chernClass 2 2 U + Work.Thom.chernClass 2 2 V) :
    BottHopf :=
  bottHopf_of_bricks hW (fun a G hG => cLineChern_of_eulerClutch hiso hE a G hG)

/-- **`Crux` from all four bricks**: the Bott normalisation (`EulerClutch` + `ECIso` + Whitney) and
the shift isomorphism `ℂ(L^aR^b) ≅ ℂ(L^{a-b})`. -/
theorem crux_of_all_bricks (hiso : ECIso) (hE : EulerClutch)
    (hW : ∀ (U V : VectorBundleCore ℂ S4 (EuclideanSpace ℂ (Fin 2)) Bool),
      Work.Thom.chernClass 4 2 (Whitney.whitneySum U V)
        = Work.Thom.chernClass 2 2 U + Work.Thom.chernClass 2 2 V)
    (hs : ComplexificationShift) : Crux :=
  crux_of_bottHopf_shift (bottHopf_of_bricks_all hiso hE hW) hs

/-- **The Thom-class transport lemma, proved** (`Submission/Work/Agree/eulerClassIso.lean`). -/
theorem eCIso : ECIso := fun Z Z' e T => Work.Agree.eulerClassIso Z Z' e T

/-- **`BottHopf` from the three remaining bricks** (`EulerClutch` from the TRANSGRESSION
subproject, the degree-`2` Whitney formula from the WHITNEY subproject; the transport lemma is now
proved). -/
theorem bottHopf_of_three_bricks (hE : EulerClutch)
    (hW : ∀ (U V : VectorBundleCore ℂ S4 (EuclideanSpace ℂ (Fin 2)) Bool),
      Work.Thom.chernClass 4 2 (Whitney.whitneySum U V)
        = Work.Thom.chernClass 2 2 U + Work.Thom.chernClass 2 2 V) :
    BottHopf :=
  bottHopf_of_bricks_all eCIso hE hW

/-- **`Crux` from the three remaining bricks** (the two subproject deliverables and the shift
isomorphism `ℂ(L^aR^b) ≅ ℂ(L^{a-b})`). -/
theorem crux_of_three_bricks (hE : EulerClutch)
    (hW : ∀ (U V : VectorBundleCore ℂ S4 (EuclideanSpace ℂ (Fin 2)) Bool),
      Work.Thom.chernClass 4 2 (Whitney.whitneySum U V)
        = Work.Thom.chernClass 2 2 U + Work.Thom.chernClass 2 2 V)
    (hs : ComplexificationShift) : Crux :=
  crux_of_all_bricks eCIso hE hW hs

/-- **The shift isomorphism, proved** (`Submission/Work/Agree/clutchShift.lean`). -/
theorem complexificationShift : ComplexificationShift := fun a b => Work.Agree.clutchShift a b

/-- **`Crux` from the two subproject deliverables and nothing else**: `EulerClutch`
(TRANSGRESSION) and the degree-`2` Whitney formula (WHITNEY).  Every other brick of AREA AGREE is
proved: the geometry (`geomSplitting geometryB`), the Thom-class transport (`eulerClassIso`), and
the shift isomorphism (`clutchShift`). -/
theorem crux_of_two_bricks (hE : EulerClutch)
    (hW : ∀ (U V : VectorBundleCore ℂ S4 (EuclideanSpace ℂ (Fin 2)) Bool),
      Work.Thom.chernClass 4 2 (Whitney.whitneySum U V)
        = Work.Thom.chernClass 2 2 U + Work.Thom.chernClass 2 2 V) :
    Crux :=
  crux_of_three_bricks hE hW complexificationShift

/-- **`Crux` from the WHITNEY brick alone.**  The transgression deliverable
`Work.Transgression.EulerClutch : Work.Agree.EulerClutch` is now available
(`Submission/Work/Transgression/Conclusion.lean`), so with the geometry, the transport lemma
`eulerClassIso` and the shift isomorphism `clutchShift` all proved, the *only* remaining input of
AREA AGREE is the degree-`2` Whitney formula for rank-`2` complex bundles over `S⁴` (summands of
the rank-`4` complex bundle `ℂ(L^a) = V_a ⊕ V_a`). -/
theorem crux_of_whitney
    (hW : ∀ (U V : VectorBundleCore ℂ S4 (EuclideanSpace ℂ (Fin 2)) Bool),
      Work.Thom.chernClass 4 2 (Whitney.whitneySum U V)
        = Work.Thom.chernClass 2 2 U + Work.Thom.chernClass 2 2 V) :
    Crux :=
  crux_of_two_bricks Work.Transgression.EulerClutch hW

/-! ## The rank-2 shift route: `BottHopf` **without** the Whitney formula -/

/-- **The rank-2 shift**, as an explicit hypothesis (delegated as `Work.Agree.shiftToRankTwo`):
the quaternionic line `L^a` has `ℂ(L^a) ≅ W ⊕ ε¹ ⊕ ε¹` for a rank-`2` complex bundle `W` whose
realification is `L^{2a} = clutchBundle (2a) 0`.

This *bypasses* the Whitney-sum formula: with it, `c₂(ℂ(L^a)) = c₂(W)` by stability
(`Work.Thom.chernClass_sumEps_sumEps`) and `c₂(W) = e(W_ℝ) = e(L^{2a}) = ±2a` by
`Work.Thom.chernClass_succ_top'` and the Euler brick.  The witness is expected to be `cLine (2a)`
(whose realification is `L^{2a}` by `Work.Agree.realification_cLine_iso_clutchBundle`). -/
def RankTwoShift : Prop :=
  ∀ a : ℤ, ∃ W : VectorBundleCore ℂ S4 (EuclideanSpace ℂ (Fin 2)) Bool,
      Nonempty (Work.Thom.BundleIso (Work.Thom.realification W) (clutchBundle (2 * a) 0)) ∧
      Nonempty (Work.Thom.BundleIso (Work.Thom.complexificationCore (clutchBundle a 0))
        (Work.Thom.sumEps Bool (Work.Thom.sumEps Bool W)))

/-- **`c₂` of a rank-`2` complex bundle whose realification is `L^m`.**  `c₂(W) = e(W_ℝ)` by
`chernClass_succ_top'`; transporting the canonical Thom class along `realification W ≅ L^m`
(`eCIso`) and applying the transgression deliverable `Work.Transgression.EulerClutch` gives
`± m · τ`, and injectivity of `π^*` removes the pullback. -/
theorem chern_of_realification_iso (m : ℤ)
    (W : VectorBundleCore ℂ S4 (EuclideanSpace ℂ (Fin 2)) Bool)
    (h : Nonempty (Work.Thom.BundleIso (Work.Thom.realification W) (clutchBundle m 0)))
    (G : H 4 S4) (hG : (HMap discProj 4).hom G = Work.Milnor.tauD) :
    Work.Thom.chernClass 2 2 W = m • G ∨ Work.Thom.chernClass 2 2 W = -(m • G) := by
  obtain ⟨e⟩ := h
  obtain ⟨T, hT⟩ := eCIso (Work.Thom.realification W) (clutchBundle m 0) e
    (Work.Thom.thomClassRank 2 (by norm_num) W)
  have hkey : Work.Thom.chernClass 2 2 W = T.eulerClass := by
    rw [Work.Thom.chernClass_succ_top' W, ← hT]
  have hb := Work.Transgression.EulerClutch m 0 T
  have hx : (HMap discProj 4).hom (Work.Thom.chernClass 2 2 W)
        = (HMap discProj 4).hom (m • G) ∨
      (HMap discProj 4).hom (Work.Thom.chernClass 2 2 W)
        = (HMap discProj 4).hom (-(m • G)) := by
    rw [hkey]
    rcases hb with hb | hb
    · left
      rw [hb, show (m + 0 : ℤ) = m from by ring, map_zsmul, hG]
    · right
      rw [hb, show (m + 0 : ℤ) = m from by ring, map_neg, map_zsmul, hG]
  rcases hx with hx | hx
  · exact Or.inl (injective_HMap_discProj 4 hx)
  · exact Or.inr (injective_HMap_discProj 4 hx)

/-- **`BottHopf` from the rank-2 shift alone** (no Whitney formula): stability
`c_j(W ⊕ ε¹ ⊕ ε¹) = c_j(W)` plus `c₂(W) = ±m·G` for `W_ℝ = L^m`. -/
theorem bottHopf_of_rankTwoShift (hs : RankTwoShift) : BottHopf := by
  intro a G hG
  obtain ⟨W, h1, h2⟩ := hs a
  obtain ⟨e2⟩ := h2
  have hiso : Work.Thom.chernClass 4 2 (Work.Thom.complexificationCore (clutchBundle a 0))
      = Work.Thom.chernClass 4 2 (Work.Thom.sumEps Bool (Work.Thom.sumEps Bool W)) :=
    Work.Thom.chernClass_BundleIso (j := 2)
      (Work.Thom.complexificationCore (clutchBundle a 0))
      (Work.Thom.sumEps Bool (Work.Thom.sumEps Bool W)) e2
  have hstab : Work.Thom.chernClass 4 2 (Work.Thom.sumEps Bool (Work.Thom.sumEps Bool W))
      = Work.Thom.chernClass 2 2 W :=
    Work.Thom.chernClass_sumEps_sumEps W 2
  rcases chern_of_realification_iso (2 * a) W h1 G hG with h | h
  · left
    rw [hiso, hstab, h]
  · right
    rw [hiso, hstab, h]

/-- **`Crux` from the rank-2 shift and the (proved) shift isomorphism**, with no Whitney formula. -/
theorem crux_of_rankTwoShift (hs : RankTwoShift) : Crux :=
  crux_of_bottHopf_shift (bottHopf_of_rankTwoShift hs) complexificationShift

/-- **The hypothesis form `RankTwoShift` from the fixed-witness iso** (delegated as
`Work.Agree.shiftToRankTwo`, path `Agree/shiftToRankTwo`) together with the already-proved
`Work.Agree.realification_cLine_iso_clutchBundle`.  This is the glue that closes `agreeAll`: once
`shiftToRankTwo` lands, `RankTwoShift` is `rankTwoShift_of_cLine shiftToRankTwo`. -/
theorem rankTwoShift_of_cLine
    (h : ∀ a : ℤ, Nonempty (Work.Thom.BundleIso
      (Work.Thom.complexificationCore (clutchBundle a 0))
      (Work.Thom.sumEps Bool (Work.Thom.sumEps Bool (cLine (2 * a)))))) :
    RankTwoShift :=
  fun a => ⟨cLine (2 * a), realification_cLine_iso_clutchBundle (2 * a), h a⟩

end

end Work.Agree
