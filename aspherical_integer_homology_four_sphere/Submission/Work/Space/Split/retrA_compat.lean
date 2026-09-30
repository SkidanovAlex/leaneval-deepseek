import Mathlib
import Submission.Work.Space.Split
import Submission.Work.Space.Split.retrA_homotopyEquiv
import Submission.Work.Space.Split.retrAB_homotopyEquiv

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function Filter
open scoped Topology unitInterval

namespace Work.Space.Split

/-! ### The two explicit homotopy equivalences

The compatibility statement is proved with the *natural* retractions: `eA` is the retraction
`r : A → M̄` of `Work.Space.Split.retrARetract` (with inverse the inclusion `i : M̄ → A`), and
`eAB` is the radial rescaling of the annulus `A ∩ B = {1/4 < ‖p‖∞ < 1}` onto the glued boundary
`⊔_v ∂[-1,1]² × T_v` of `Work.Space.Split.retrAB_homotopyEquiv`, transported to the subtype
`{q : a.Y // q ∈ a.boundarySet}`.  With these two choices the two composites `A ∩ B → M̄` are
*equal*, and the homotopy is the constant one. -/

/-- **`A ≃ₕ M̄`**, as the explicit homotopy equivalence whose forward map is the retraction
`a.r`, with inverse the inclusion `a.i` and homotopy `a.HCM`.  This is the homotopy equivalence
behind `Work.Space.Split.retrA_homotopyEquiv`, named here so that its underlying map is
available for computation. -/
def eACompat (a : Assembly) :
    ContinuousMap.HomotopyEquiv {z : a.Mhat // z ∈ a.Aset} a.Mbar :=
  { toFun := a.r
    invFun := a.i
    left_inv := ⟨{ toContinuousMap := a.HCM
                   map_zero_left := fun z => a.gfun_zero z
                   map_one_left := fun z => a.gfun_one z }⟩
    right_inv := by rw [a.r_comp_i] }

/-- The canonical homeomorphism between the glued boundary `{q : a.Y // q ∈ a.boundarySet}` of the
filling pieces and `⊔_v ∂[-1,1]² × T_v = BdrySig a`. -/
def homeoBdrySubSig (a : Assembly) :
    {q : a.Y // q ∈ a.boundarySet} ≃ₜ BdrySig a :=
  (subtypeSigmaHomeomorph (fun (i : Cusp) (w : SquarePt × a.Torus i) => sqNorm w.1 = 1)).trans
    (sigmaCongrRightHomeomorph (fun _ =>
      subtypeProdHomeomorph (fun p : SquarePt => sqNorm p = 1)))

/-- **`A ∩ B ≃ₕ ⊔_v ∂[-1,1]² × T_v`**: the annulus of the filling pieces is identified with
`Σ_v AnnPt × T_v` and then rescaled radially onto the boundary of the square, whose boundary
subtype is `{q : a.Y // q ∈ a.boundarySet}`. -/
def eABACompat (a : Assembly) :
    ContinuousMap.HomotopyEquiv {z : a.Mhat // z ∈ a.Aset ∧ z ∈ a.Bset}
      {q : a.Y // q ∈ a.boundarySet} :=
  ((homeoAnnXSrc a).symm.toHomotopyEquiv).trans
    (((homeoAnnXAnnSig a).toHomotopyEquiv).trans
      ((heAnnBdry a).trans (homeoBdrySubSig a).symm.toHomotopyEquiv))

/-- The radial collapse `p ↦ p/‖p‖∞` of the annulus, in the two forms needed here: the boundary
point of the square produced by `dirPt` has the same underlying point as `radPt p`. -/
theorem dirPt_fst_eq_radPt (p : SquarePt) (hp : 1/4 < sqNorm p) (hlt : sqNorm p < 1) :
    (dirPt ⟨p, hp, hlt⟩).1 = radPt p hp := by
  apply Subtype.ext
  show (sqNorm p)⁻¹ • (p : E2) = rayVal 0 p
  rw [rayVal, rayCoef_zero]

/-- **The retraction of `A` on the annulus.**  On a point of `A ∩ B` lying over the annulus point
`⟨v, (p, t)⟩`, the retraction `r : A → M̄` collapses the shell point radially to the boundary of
the square and then applies the gluing `a.glue.symm`. -/
theorem r_inclAB_A_phiAnnSrc (a : Assembly) (v : Cusp) (p : SquarePt) (hp : 1/4 < sqNorm p)
    (_hlt : sqNorm p < 1) (t : a.Torus v)
    (hx : (⟨v, (p, t)⟩ : a.Y) ∈ annulus a.Torus) :
    a.r (Assembly.inclAB_A a (phiAnnSrc a ⟨⟨v, (p, t)⟩, hx⟩))
      = (a.glue.symm (a.radShell ⟨v, (⟨p, hp⟩, t)⟩)).1 := by
  have hqA : Assembly.inclAB_A a (phiAnnSrc a ⟨⟨v, (p, t)⟩, hx⟩)
      = a.qA (Sum.inr (⟨v, (⟨p, hp⟩, t)⟩ : Assembly.ShellY a)) := Subtype.ext rfl
  rw [hqA]
  have h1 : a.r (a.qA (Sum.inr (⟨v, (⟨p, hp⟩, t)⟩ : Assembly.ShellY a)))
      = a.gFun (Sum.inr (⟨v, (⟨p, hp⟩, t)⟩ : Assembly.ShellY a)) := by
    simpa [Work.Space.Assembly.qACM, Work.Space.Assembly.gCM] using
      a.r_qA (Sum.inr (⟨v, (⟨p, hp⟩, t)⟩ : Assembly.ShellY a))
  rw [h1]
  rfl

/-- **The homotopy equivalence `A ∩ B ≃ₕ ⊔_v ∂[-1,1]² × T_v` on the annulus.**  On a point of
`A ∩ B` lying over the annulus point `⟨v, (p, t)⟩`, `eABACompat` rescales radially to the
boundary of the square `p ↦ p/‖p‖∞`, i.e. it produces the same boundary point as `a.radShell`. -/
theorem eABACompat_radShell (a : Assembly) (v : Cusp) (p : SquarePt) (hp : 1/4 < sqNorm p)
    (hlt : sqNorm p < 1) (t : a.Torus v)
    (hx : (⟨v, (p, t)⟩ : a.Y) ∈ annulus a.Torus) :
    eABACompat a (phiAnnSrc a ⟨⟨v, (p, t)⟩, hx⟩) = a.radShell ⟨v, (⟨p, hp⟩, t)⟩ := by
  have hsx : (homeoAnnXSrc a).symm (phiAnnSrc a ⟨⟨v, (p, t)⟩, hx⟩)
      = (⟨⟨v, (p, t)⟩, hx⟩ : AnnX a) :=
    Homeomorph.symm_apply_apply (homeoAnnXSrc a) (⟨⟨v, (p, t)⟩, hx⟩ : AnnX a)
  change (homeoBdrySubSig a).symm (annToBdry a ((homeoAnnXAnnSig a)
    ((homeoAnnXSrc a).symm (phiAnnSrc a ⟨⟨v, (p, t)⟩, hx⟩)))) = _
  rw [hsx]
  have hAnn : (homeoAnnXAnnSig a) (⟨⟨v, (p, t)⟩, hx⟩ : AnnX a)
      = (⟨v, (⟨p, hp, hlt⟩, t)⟩ : AnnSig a) := by
    have hInv : (homeoAnnXAnnSig a).symm (⟨v, (⟨p, hp, hlt⟩, t)⟩ : AnnSig a)
        = (⟨⟨v, (p, t)⟩, hx⟩ : AnnX a) := rfl
    have h :=
      Homeomorph.apply_symm_apply (homeoAnnXAnnSig a) (⟨v, (⟨p, hp, hlt⟩, t)⟩ : AnnSig a)
    rwa [hInv] at h
  rw [hAnn]
  have hann : annToBdry a (⟨v, (⟨p, hp, hlt⟩, t)⟩ : AnnSig a)
      = (⟨v, (dirPt ⟨p, hp, hlt⟩, t)⟩ : BdrySig a) := rfl
  rw [hann]
  rw [show (homeoBdrySubSig a).symm (⟨v, (dirPt ⟨p, hp, hlt⟩, t)⟩ : BdrySig a)
      = ⟨⟨v, ((dirPt ⟨p, hp, hlt⟩).1, t)⟩, (dirPt ⟨p, hp, hlt⟩).2⟩ from rfl]
  refine Subtype.ext ?_
  show (⟨v, ((dirPt ⟨p, hp, hlt⟩).1, t)⟩ : a.Y) = ⟨v, (radPt p hp, t)⟩
  rw [dirPt_fst_eq_radPt p hp hlt]

/-- **The two composites `A ∩ B → M̄` agree.**  Both send the point of `A ∩ B` lying over the
annulus point `⟨v, (p, t)⟩` to the point of `M̄` obtained by gluing the radially rescaled
boundary point `p/‖p‖∞` of the `v`-th filling piece: on the left the retraction `a.r` collapses
the shell point in the same way, on the right `tauBdry` is the inverse of the gluing. -/
theorem eACompat_comp_inclAB_A_eq (a : Assembly) :
    (eACompat a).toFun.comp (Assembly.inclAB_A a)
      = (Assembly.tauBdry a).comp (eABACompat a).toFun := by
  refine ContinuousMap.ext fun z => ?_
  obtain ⟨x, rfl⟩ := (phiAnnSrc_bijective a).2 z
  obtain ⟨⟨v, p, t⟩, hx⟩ := x
  have hx' : 1/4 < sqNorm p ∧ sqNorm p < 1 := hx
  simp only [ContinuousMap.comp_apply]
  change a.r (Assembly.inclAB_A a (phiAnnSrc a ⟨⟨v, (p, t)⟩, hx⟩))
      = Assembly.tauBdry a ((eABACompat a).toFun (phiAnnSrc a ⟨⟨v, (p, t)⟩, hx⟩))
  rw [r_inclAB_A_phiAnnSrc a v p hx'.1 hx'.2 t hx,
    eABACompat_radShell a v p hx'.1 hx'.2 t hx]
  rfl

/-! **The Mayer--Vietoris compatibility of `A ∩ B` with `A`.**

There are homotopy equivalences `eA : A ≃ₕ M̄` and `eAB : A ∩ B ≃ₕ ⊔_v (∂[-1,1]² × T_v)`
(the boundary `{q : a.Y // q ∈ a.boundarySet}` of the filling pieces, which is canonically
`⊔_v ∂[-1,1]² × T_v`) such that the inclusion `A ∩ B ↪ A` followed by `eA` is homotopic to
`(tauBdry) ∘ eAB`, where `tauBdry` is the cusp parametrisation `τ` (the inverse of the gluing
homeomorphism `a.glue`, restricted to the boundary).

This is the `h_v` half of blueprint §3 ("`(A ∩ B ↪ A)` corresponds under the retractions to `h_v`"),
and with `Work.Space.Split.retrAB_compat` it is what identifies the Mayer--Vietoris maps.

Hint: with the natural retractions both sides are the same map: on an annulus point `p` with
`1/4 < sqNorm p < 1`, the left-hand side retracts radially to `p/sqNorm p` and then applies the
gluing, and the right-hand side applies the annulus retraction `p ↦ p/sqNorm p` followed by
`tauBdry`.  The same construction as in `Submission/Work/Space/Split/retrA_homotopyEquiv.lean`
and `.../retrAB_homotopyEquiv.lean` applies. -/
theorem retrA_compat (a : Assembly) :
    ∃ (eA : ContinuousMap.HomotopyEquiv {z : a.Mhat // z ∈ a.Aset} a.Mbar)
      (eAB : ContinuousMap.HomotopyEquiv {z : a.Mhat // z ∈ a.Aset ∧ z ∈ a.Bset}
        {q : a.Y // q ∈ a.boundarySet}),
      (eA.toFun.comp (Assembly.inclAB_A a)).Homotopic ((Assembly.tauBdry a).comp eAB.toFun) := by
  exact ⟨eACompat a, eABACompat a,
    by rw [eACompat_comp_inclAB_A_eq a]⟩

end Work.Space.Split

end
