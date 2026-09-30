import Mathlib
import Submission.Work.Space.Split
import Submission.Work.Space.Split.retrAB_homotopyEquiv
import Submission.Work.Space.Split.retrB_homotopyEquiv

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function
open scoped Topology unitInterval

namespace Work.Space.Split

/-! ### The two homotopy equivalences, built from the natural retractions

The proof of compatibility is the statement that the two composites are *equal* (not merely
homotopic) for the two *natural* retractions: on the annulus `1/4 < ‖p‖∞ < 1` a point with
coordinates `(v, (p, t))` is sent to `(v, t)` both by "project `B` to its core `T_v`" and by
"normalise the annulus point to the boundary `∂[-1,1]²` and then forget the boundary coordinate".

We therefore first name the two homotopy equivalences: `eABCompat` from the annulus `A ∩ B` to the
glued boundary `⊔_v ∂[-1,1]² × T_v`, and `eBCompat` from the collar `B` to the cores `⊔_v T_v`. -/

/-- The homotopy equivalence `⊔_v T_v ≃ₕ ⊔_v T_v`-part of `B ≃ₕ ⊔_v T_v`: the collar retracts
onto its cores by `RetrB.collarProj`, with inverse `RetrB.collarCore` and the straight line
homotopy `RetrB.collarScale`. -/
def collarHE (a : Assembly) :
    ContinuousMap.HomotopyEquiv (RetrB.Collar a) (Σ v : Cusp, a.Torus v) :=
  ContinuousMap.HomotopyEquiv.mk
    ⟨RetrB.collarProj a, RetrB.continuous_collarProj a⟩
    ⟨RetrB.collarCore a, RetrB.continuous_collarCore a⟩
    ⟨ContinuousMap.Homotopy.mk
      (⟨RetrB.collarScale a, RetrB.continuous_collarScale a⟩ :
        ContinuousMap (↥unitInterval × RetrB.Collar a) (RetrB.Collar a))
      (fun q => RetrB.collarScale_zero a q)
      (fun q => RetrB.collarScale_one a q)⟩
    (by
      have h : ((⟨RetrB.collarProj a, RetrB.continuous_collarProj a⟩ :
          ContinuousMap (RetrB.Collar a) (Σ v : Cusp, a.Torus v)).comp
        (⟨RetrB.collarCore a, RetrB.continuous_collarCore a⟩ :
          ContinuousMap (Σ v : Cusp, a.Torus v) (RetrB.Collar a)))
        = ContinuousMap.id (Σ v : Cusp, a.Torus v) :=
        ContinuousMap.ext fun w => RetrB.collarProj_collarCore a w
      rw [h])

/-- **`B ≃ₕ ⊔_v T_v`**, through the homeomorphism `B ≅ {‖p‖∞ < 1}` of the collar and the
retraction `p ↦ 0` of the collar onto the cores. -/
def eBCompat (a : Assembly) :
    ContinuousMap.HomotopyEquiv {z : a.Mhat // z ∈ a.Bset} (Σ v : Cusp, a.Torus v) :=
  ((RetrB.collarHomeo a).symm.toHomotopyEquiv).trans (collarHE a)

/-- **`A ∩ B ≃ₕ ⊔_v ∂[-1,1]² × T_v`**, through the homeomorphism `A ∩ B ≅ {1/4 < ‖p‖∞ < 1}` of
the annulus, the identification of the annulus with `Σ_v AnnPt × T_v`, and the radial rescaling
`p ↦ p/‖p‖∞` of the annulus onto the boundary of the square. -/
def eABCompat (a : Assembly) :
    ContinuousMap.HomotopyEquiv {z : a.Mhat // z ∈ a.Aset ∧ z ∈ a.Bset}
      (Σ v : Cusp, {p : SquarePt // sqNorm p = 1} × a.Torus v) :=
  ((homeoAnnXSrc a).symm.toHomotopyEquiv).trans
    ((homeoAnnXAnnSig a).toHomotopyEquiv.trans (heAnnBdry a))

/-- The membership criterion of the annulus `{1/4 < ‖p‖∞ < 1}`. -/
theorem mem_annulus_iff (Torus : Cusp → Type*) (q : Filling Torus) :
    q ∈ annulus Torus ↔ 1/4 < sqNorm q.2.1 ∧ sqNorm q.2.1 < 1 := Iff.rfl

/-- **The two composites agree.**  Both send the point of `A ∩ B` lying over `⟨v, (p, t)⟩` in the
annulus (`1/4 < ‖p‖∞ < 1`) to `⟨v, t⟩`: `eBCompat` by collapsing the collar to the core, `eABCompat`
by rescaling to the boundary and forgetting the boundary coordinate. -/
theorem eBCompat_comp_inclAB_B_eq (a : Assembly) :
    (eBCompat a).toFun.comp (Assembly.inclAB_B a)
      = (Assembly.projBdry a).comp (eABCompat a).toFun := by
  refine ContinuousMap.ext fun z => ?_
  obtain ⟨x, rfl⟩ := (phiAnnSrc_bijective a).2 z
  obtain ⟨⟨v, p, t⟩, hx⟩ := x
  have hx' : 1/4 < sqNorm p ∧ sqNorm p < 1 := (mem_annulus_iff a.Torus _).mp hx
  simp only [ContinuousMap.comp_apply]
  -- the collar point of the filling pieces underlying `z`
  have hmem : (⟨v, (p, t)⟩ : a.Y) ∈ innerCore a.Torus := hx'.2
  have hL : (eBCompat a).toFun (Assembly.inclAB_B a (phiAnnSrc a ⟨⟨v, (p, t)⟩, hx⟩))
      = (⟨v, t⟩ : Σ w : Cusp, a.Torus w) := by
    have hsymm : (RetrB.collarHomeo a).symm (RetrB.incCollar a (⟨⟨v, (p, t)⟩, hmem⟩ : RetrB.Collar a))
        = (⟨⟨v, (p, t)⟩, hmem⟩ : RetrB.Collar a) :=
      Homeomorph.symm_apply_apply (RetrB.collarHomeo a) (⟨⟨v, (p, t)⟩, hmem⟩ : RetrB.Collar a)
    change RetrB.collarProj a ((RetrB.collarHomeo a).symm
      (RetrB.incCollar a (⟨⟨v, (p, t)⟩, hmem⟩ : RetrB.Collar a)))
      = (⟨v, t⟩ : Σ w : Cusp, a.Torus w)
    rw [hsymm]
    rfl
  have hR : (Assembly.projBdry a) ((eABCompat a).toFun (phiAnnSrc a ⟨⟨v, (p, t)⟩, hx⟩))
      = (⟨v, t⟩ : Σ w : Cusp, a.Torus w) := by
    have hsx : (homeoAnnXSrc a).symm (phiAnnSrc a ⟨⟨v, (p, t)⟩, hx⟩)
        = (⟨⟨v, (p, t)⟩, hx⟩ : AnnX a) :=
      Homeomorph.symm_apply_apply (homeoAnnXSrc a) (⟨⟨v, (p, t)⟩, hx⟩ : AnnX a)
    change Assembly.projBdry a (annToBdry a ((homeoAnnXAnnSig a)
      ((homeoAnnXSrc a).symm (phiAnnSrc a ⟨⟨v, (p, t)⟩, hx⟩))))
      = (⟨v, t⟩ : Σ w : Cusp, a.Torus w)
    rw [hsx]
    have hAnn : (homeoAnnXAnnSig a) (⟨⟨v, (p, t)⟩, hx⟩ : AnnX a)
        = (⟨v, (⟨p, hx'⟩, t)⟩ : AnnSig a) := by
      have hInv : (homeoAnnXAnnSig a).symm (⟨v, (⟨p, hx'⟩, t)⟩ : AnnSig a)
          = (⟨⟨v, (p, t)⟩, hx⟩ : AnnX a) := rfl
      have h := Homeomorph.apply_symm_apply (homeoAnnXAnnSig a) (⟨v, (⟨p, hx'⟩, t)⟩ : AnnSig a)
      rwa [hInv] at h
    rw [hAnn]
    rfl
  rw [hL, hR]

/-! **The Mayer--Vietoris compatibility of `A ∩ B` with `B`.**

There are homotopy equivalences `eAB : A ∩ B ≃ₕ ⊔_v (∂[-1,1]² × T_v)` and
`eB : B ≃ₕ ⊔_v T_v` such that the inclusion `A ∩ B ↪ B` followed by `eB` is homotopic to
`projBdry ∘ eAB`, where `projBdry : ⊔_v (∂[-1,1]² × T_v) → ⊔_v T_v` forgets the boundary
coordinate.  This is the statement that `(A ∩ B ↪ B)` is the product projection onto `T_v`
(blueprint §3), and it is what identifies the Mayer--Vietoris maps on homology.

Hint: with the *natural* retractions the two sides are equal, not merely homotopic: on a filling
point `⟨v, (p, t)⟩` with `1/4 < sqNorm p < 1`, `eB (inclAB_B z)` is `⟨v, t⟩` (the collar retracts
`p ↦ 0`) and `projBdry (eAB z)` is `⟨v, t⟩` as well (the annulus retracts `p ↦ p/sqNorm p`, whose
`T_v` coordinate is again `t`).  It is therefore enough to build the two maps explicitly on the
annulus (see `Work.Space.Split.retrAB_homotopyEquiv` for the same construction) and use
`ContinuousMap.Homotopic.refl`. -/
theorem retrAB_compat (a : Assembly) :
    ∃ (eAB : ContinuousMap.HomotopyEquiv {z : a.Mhat // z ∈ a.Aset ∧ z ∈ a.Bset}
            (Σ v : Cusp, {p : SquarePt // sqNorm p = 1} × a.Torus v))
      (eB : ContinuousMap.HomotopyEquiv {z : a.Mhat // z ∈ a.Bset} (Σ v : Cusp, a.Torus v)),
      (eB.toFun.comp (Assembly.inclAB_B a)).Homotopic ((Assembly.projBdry a).comp eAB.toFun) := by
  refine ⟨eABCompat a, eBCompat a, ?_⟩
  simpa only [eBCompat_comp_inclAB_B_eq a] using
    ContinuousMap.Homotopic.refl ((Assembly.projBdry a).comp (eABCompat a).toFun)

end Work.Space.Split

