import Mathlib
import Submission.Work.ThomBordism.Tower.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Naturality of the cochain-level Thom map `psiAbs`

`Work.ThomBordism.Tower.psiAbs_natural`: the restriction of `psiAbs Z n U τ W' hW' m a` from the
piece `W'` to a smaller piece `W ⊆ W'` is `psiAbs` of the restricted base cochain:
`rcResLM (preimage h) (psiAbs W' hW' m a) = psiAbs W hW m (baseRes h m a)`.

Both sides are, on the nose, the cup product of the pullback of the base cochain with the
restricted Thom representative, and the restriction `rcResLM` is (the transpose of) the inclusion
of the pieces of the total space `Z.proj ⁻¹' W ↪ Z.proj ⁻¹' W'`.  So the statement is the
naturality `Work.Cohomology.cupNatural` of the Alexander–Whitney cup product, together with the
two bookkeeping identities

* `pullAbs_baseRes` — the pullback of a base cochain is compatible with the restriction:
  `incl^* (pullAbs a) = pullAbs (baseRes a)`;
* `rcResLM_tauRepAt` — the representative of `τ` on the smaller piece is the restriction of the
  representative on the larger one.

The helper `dualChainMap_f_comp` is the pointwise composition formula for the pullback of cochains
(what makes `pullAbs_baseRes` a formal computation on the projections `pieceProj`), and the helper
`dualChainMap_pdIncl_cup` is the naturality of the cup product in the `dualChainMap` presentation
used throughout this file (it is `cupNatural` up to the definitional identity
`cochainPullbackHom = LinearMap.dualMap`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits
open Work.TangentClasses Work.Cohomology

namespace Work.ThomBordism.Tower

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-! ## Two general facts about the pullback of cochains -/

/-- **The pointwise composition formula for the pullback of cochains.**  Pulling a cochain back
along `f ≫ g` is pulling it back along `g` and then along `f`. -/
theorem dualChainMap_f_comp {X Y Zc : TopCat} (f : X ⟶ Y) (g : Y ⟶ Zc) (n : ℕ)
    (a : ↑((Work.Cohomology.singularCochainComplex ℤ Zc).X n)) :
    (ModuleCat.Hom.hom ((Work.Cohomology.dualChainMap ℤ X Zc (f ≫ g)).f n)) a
      = (ModuleCat.Hom.hom ((Work.Cohomology.dualChainMap ℤ X Y f).f n))
          ((ModuleCat.Hom.hom ((Work.Cohomology.dualChainMap ℤ Y Zc g).f n)) a) := by
  rw [Work.Cohomology.dualChainMap_comp, HomologicalComplex.comp_f]
  rw [ModuleCat.hom_comp, LinearMap.comp_apply]

/-- **Naturality of the Alexander–Whitney cup product**, in the `dualChainMap` presentation: for
`S ⊆ T` subsets of a space `X` and cochains `α`, `β` on `T`, the pullback along the inclusion of
`cup α β` is the cup of the pullbacks.  This is `Work.Cohomology.cupNatural` for the simplicial map
`TopCat.toSSet.map (pdIncl T S h)`, up to the definitional identity `cochainPullbackHom = dualMap`
(and the definitional identity between `singularCochainComplex` and `chainComplex`). -/
theorem dualChainMap_pdIncl_cup {X : Type} [TopologicalSpace X] {S T : Set X} (h : S ⊆ T)
    {n m : ℕ}
    (α : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj (TopCat.of T)) n)
    (β : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj (TopCat.of T)) m) :
    (ModuleCat.Hom.hom ((Work.Cohomology.dualChainMap ℤ (TopCat.of S) (TopCat.of T)
        (Work.Cohomology.pdIncl (M := TopCat.of X) T S h)).f (n + m)))
      (Work.Cohomology.cup ℤ (TopCat.toSSet.obj (TopCat.of T)) α β)
    = Work.Cohomology.cup ℤ (TopCat.toSSet.obj (TopCat.of S))
        ((ModuleCat.Hom.hom ((Work.Cohomology.dualChainMap ℤ (TopCat.of S) (TopCat.of T)
          (Work.Cohomology.pdIncl (M := TopCat.of X) T S h)).f n)) α)
        ((ModuleCat.Hom.hom ((Work.Cohomology.dualChainMap ℤ (TopCat.of S) (TopCat.of T)
          (Work.Cohomology.pdIncl (M := TopCat.of X) T S h)).f m)) β) :=
  (Work.Cohomology.cupNatural ℤ
    (TopCat.toSSet.map (Work.Cohomology.pdIncl (M := TopCat.of X) T S h)) α β).symm

/-- A relative cochain of a piece, regarded as an absolute cochain of the piece of the total space
(the two are definitionally the same type).  This is only a notational device: it lets the
pullbacks of the absolute cochain complex be applied to the relative representatives without
fighting the coercion of the subtype. -/
abbrev cohV (Z : RealBundle B F ι) (W : Set B) (n : ℕ) (x : TotC Z W n) :
    Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj (TopCat.of (Z.proj ⁻¹' W))) n := x.1

/-! ## The two bookkeeping identities -/

/-- **The pullback of a base cochain is compatible with the restriction.**  For `W ⊆ W'` the
pullback of the base cochain `a` to the piece of the total space over `W'`, restricted to the
smaller piece over `W`, is the pullback of the restricted base cochain `baseRes h a`.  This is
`dualChainMap_f_comp` applied to the two factorisations
`pieceProj W' ∘ incl = pdIncl h ∘ pieceProj W` of the projection. -/
theorem pullAbs_baseRes (Z : RealBundle B F ι) {W W' : Set B}
    (h : W ⊆ W') (m : ℕ) (a : BaseC W' m) :
    (ModuleCat.Hom.hom ((Work.Cohomology.dualChainMap ℤ (TopCat.of (Z.proj ⁻¹' W))
      (TopCat.of (Z.proj ⁻¹' W')) (Work.Cohomology.pdIncl (M := TopCat.of Z.TotalSpace)
        (Z.proj ⁻¹' W') (Z.proj ⁻¹' W) (Set.preimage_mono h))).f m))
      ((pullAbs Z W' m) a)
    = (pullAbs Z W m) ((baseRes h m) a) := by
  have hcomp : Work.Cohomology.pdIncl (M := TopCat.of Z.TotalSpace) (Z.proj ⁻¹' W')
        (Z.proj ⁻¹' W) (Set.preimage_mono h) ≫ TopCat.ofHom (Work.Thom.pieceProj Z W')
      = TopCat.ofHom (Work.Thom.pieceProj Z W)
        ≫ Work.Cohomology.pdIncl (M := TopCat.of B) W' W h := by
    apply TopCat.ext
    intro y
    rfl
  rw [pullAbs, baseRes, pullAbs]
  rw [← dualChainMap_f_comp (f := Work.Cohomology.pdIncl (M := TopCat.of Z.TotalSpace)
        (Z.proj ⁻¹' W') (Z.proj ⁻¹' W) (Set.preimage_mono h))
        (g := TopCat.ofHom (Work.Thom.pieceProj Z W')) m a]
  rw [hcomp]
  exact dualChainMap_f_comp (f := TopCat.ofHom (Work.Thom.pieceProj Z W))
    (g := Work.Cohomology.pdIncl (M := TopCat.of B) W' W h) m a

/-- **The representative of `τ` restricts to the representative on the smaller piece.**  This is
immediate from the definition `tauRepAt τ W hW = rcResLM (preimage_mono hW) (tauRep τ)` and the
functoriality `rcResLM_comp` of the restrictions. -/
theorem rcResLM_tauRepAt (Z : RealBundle B F ι) (n : ℕ) (U : Set B)
    (τ : Work.Thom.PieceCoh Z U n) {W W' : Set B} (h : W ⊆ W') (hW : W ⊆ U) (hW' : W' ⊆ U) :
    rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) n
        (tauRepAt Z n U τ W' hW')
      = tauRepAt Z n U τ W hW := by
  rw [tauRepAt, tauRepAt]
  rw [← LinearMap.comp_apply, rcResLM_comp]

/-! ## The target -/

theorem psiAbs_natural {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type} (Z : Work.TangentClasses.RealBundle B F ι) (n : ℕ) (U : Set B)
    (τ : Work.Thom.PieceCoh Z U n) {W W' : Set B} (h : W ⊆ W') (hW : W ⊆ U) (hW' : W' ⊆ U)
    (m : ℕ) (a : Work.ThomBordism.BaseC W' m) :
    Work.Cohomology.rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) (m + n)
        (Work.ThomBordism.psiAbs Z n U τ W' hW' m a)
      = Work.ThomBordism.psiAbs Z n U τ W hW m (Work.ThomBordism.baseRes h m a) := by
  apply Subtype.ext
  simp only [psiAbs, Work.Cohomology.rcResLM_coe, Subtype.coe_mk]
  have hx : (ModuleCat.Hom.hom ((Work.Cohomology.dualChainMap ℤ (TopCat.of (Z.proj ⁻¹' W))
      (TopCat.of (Z.proj ⁻¹' W')) (Work.Cohomology.pdIncl (M := TopCat.of Z.TotalSpace)
        (Z.proj ⁻¹' W') (Z.proj ⁻¹' W) (Set.preimage_mono h))).f m))
      ((pullAbs Z W' m) a)
      = (pullAbs Z W m) ((baseRes h m) a) :=
    pullAbs_baseRes Z h m a
  have hy : (ModuleCat.Hom.hom ((Work.Cohomology.dualChainMap ℤ (TopCat.of (Z.proj ⁻¹' W))
      (TopCat.of (Z.proj ⁻¹' W')) (Work.Cohomology.pdIncl (M := TopCat.of Z.TotalSpace)
        (Z.proj ⁻¹' W') (Z.proj ⁻¹' W) (Set.preimage_mono h))).f n))
      ↑(tauRepAt Z n U τ W' hW')
      = ↑(tauRepAt Z n U τ W hW) := by
    have hc := congrArg Subtype.val (rcResLM_tauRepAt Z n U τ h hW hW')
    simpa only [Work.Cohomology.rcResLM_coe] using hc
  have hcup : (ModuleCat.Hom.hom ((Work.Cohomology.dualChainMap ℤ (TopCat.of (Z.proj ⁻¹' W))
      (TopCat.of (Z.proj ⁻¹' W')) (Work.Cohomology.pdIncl (M := TopCat.of Z.TotalSpace)
        (Z.proj ⁻¹' W') (Z.proj ⁻¹' W) (Set.preimage_mono h))).f (m + n)))
      (Work.Cohomology.cup ℤ (TopCat.toSSet.obj (TopCat.of (Z.proj ⁻¹' W')))
        ((pullAbs Z W' m) a) (cohV Z W' n (tauRepAt Z n U τ W' hW')))
      = Work.Cohomology.cup ℤ (TopCat.toSSet.obj (TopCat.of (Z.proj ⁻¹' W)))
          ((ModuleCat.Hom.hom ((Work.Cohomology.dualChainMap ℤ (TopCat.of (Z.proj ⁻¹' W))
            (TopCat.of (Z.proj ⁻¹' W')) (Work.Cohomology.pdIncl (M := TopCat.of Z.TotalSpace)
              (Z.proj ⁻¹' W') (Z.proj ⁻¹' W) (Set.preimage_mono h))).f m))
            ((pullAbs Z W' m) a))
          ((ModuleCat.Hom.hom ((Work.Cohomology.dualChainMap ℤ (TopCat.of (Z.proj ⁻¹' W))
            (TopCat.of (Z.proj ⁻¹' W')) (Work.Cohomology.pdIncl (M := TopCat.of Z.TotalSpace)
              (Z.proj ⁻¹' W') (Z.proj ⁻¹' W) (Set.preimage_mono h))).f n))
            (cohV Z W' n (tauRepAt Z n U τ W' hW'))) :=
    dualChainMap_pdIncl_cup (X := Z.TotalSpace) (Set.preimage_mono h)
      ((pullAbs Z W' m) a) (cohV Z W' n (tauRepAt Z n U τ W' hW'))
  exact hcup.trans (by rw [hx, hy])

end

end Work.ThomBordism.Tower
