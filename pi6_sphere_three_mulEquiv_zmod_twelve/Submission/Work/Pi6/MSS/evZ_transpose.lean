import Mathlib
import Submission.Work.Pi6.MSS.e2FinalDefs
import Submission.Work.Pi6.MSS.evZ_d_transpose_vanishing
import Submission.Work.Pi6.MSS.d1elt_lift
import Submission.Work.Pi6.MSS.d1elt_class
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The transposed differential of the first page of the Serre filtration

Let `p : E → B`, `W = Wc 𝕜 p` the Serre cochain filtration of `p`, `𝕜` a field,
`x ∈ Z_1^s C^{s+q}` a `1`-cycle of the filtration and `y = xcast (δx) ∈ Z_1^{s+1} C^{(s+1)+q}` its
transposed coboundary.  For a cycle `w` of the `(s+1)`-st graded piece
`Kg (s+1) = C(A_{s+2})/C(A_{s+1})`, represented (through `e2Hb`) by its class in
`Z_{s+1+q} ⧸ B_{s+1+q}`, the two evaluations

* `⟨δx, w⟩` (the cohomological side, `evZ` at filtration degree `s+1`), and
* `⟨x, d¹[w]⟩` (the homological side, `evS` of the connecting map `d¹ = kF ≫ jF` at filtration
  degree `s`),

agree.

## The proof

* `d1elt_lift` produces a chain `v` of `F_s = C(A_{s+1})` whose image in `F_{s+1} = C(A_{s+2})` is
  the boundary `∂(grSecX_{s+1} w)` of a lift of `w`, together with its cycle conditions.
* `d1elt_class` computes the class `d1elt w` of the transposed differential as the class of the
  cycle `Kgπ_s v`.
* The remaining comparison is the chain level identity
  `⟨x, grSecX_s (Kgπ_s v)⟩ = ⟨x, ∂(grSecX_{s+1} w)⟩ = ⟨δx, grSecX_{s+1} w⟩`: the two lifts of the
  cycle `Kgπ_s v` differ by an element of `ker (Kgπ s)`, which `x ∈ F^s` annihilates
  (`ker_Kgπ_inclL_eq_zero`), while the second equality is the transposed coboundary
  `Wc_d_apply_applied` (with the degree transport `hy`).
-/

namespace Work.Pi6.MSS

theorem evZ_transpose (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (s q : ℕ)
    (x : ↥(pZ 𝕜 (Wc 𝕜 p) 1 s (s + q)))
    (y : ↥(pZ 𝕜 (Wc 𝕜 p) 1 (s + 1) ((s + 1) + q)))
    (hy : (y : (Wc 𝕜 p).C.X ((s + 1) + q))
      = (Wc 𝕜 p).xcast (show (s + q) + 1 = (s + 1) + q by omega)
          ((Wc 𝕜 p).d (s + q) (x : (Wc 𝕜 p).C.X (s + q))))
    (w : ↥(Work.StemsB.fdZ 𝕜 (Kg 𝕜 p (s + 1)) ((s + 1) + q))) :
    evZ 𝕜 p (s + 1) ((s + 1) + q) (hannSerre 𝕜 p) y
        ((Work.StemsB.fdH 𝕜 (Kg 𝕜 p (s + 1)) ((s + 1) + q)).mkQ w)
      = evS 𝕜 p s (s + q) (hannSerre 𝕜 p)
          (Submodule.mkQ ((pDen 𝕜 (Wc 𝕜 p) 1 s (s + q)).comap
            (pZ 𝕜 (Wc 𝕜 p) 1 s (s + q)).subtype) x)
          (d1elt 𝕜 p s q w) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option maxHeartbeats 1600000 in
  obtain ⟨v, hv, _hvcyc, hb⟩ := d1elt_lift 𝕜 E B p s q w
  have hdc := d1elt_class 𝕜 E B p s q w v hv hb
  -- the cohomological side, on representatives
  rw [evZ_apply 𝕜 p (s + 1) ((s + 1) + q) (hannSerre 𝕜 p) y w]
  -- the homological side: `evS` on a representative is `evZ`, and `d1elt` is the class of `Kgπ v`
  have hevS : evS 𝕜 p s (s + q) (hannSerre 𝕜 p)
      (Submodule.mkQ ((pDen 𝕜 (Wc 𝕜 p) 1 s (s + q)).comap
        (pZ 𝕜 (Wc 𝕜 p) 1 s (s + q)).subtype) x)
      = evZ 𝕜 p s (s + q) (hannSerre 𝕜 p) x := by
    rw [evS]
    exact Submodule.liftQ_apply _ _ _
  rw [hevS, hdc]
  rw [evZ_apply 𝕜 p s (s + q) (hannSerre 𝕜 p) x
        ⟨(ModuleCat.Hom.hom ((Kgπ 𝕜 p s).f (s + q))) v, hb⟩]
  -- evaluation of `δx` on the lift of `w`: move the degree transport `hy` inside
  rw [hy]
  rw [evZdtv_xcast_cochainFun 𝕜 p]
  rw [← Wc_d_apply_applied 𝕜 p (s + q)
        (x : (Wc 𝕜 p).C.X (s + q))]
  have hA : Work.SSSR.castElem (Work.SSSR.sChains 𝕜 (Work.SSS.sSing E))
        (show (s + 1) + q = (s + q) + 1 by omega)
        ((ModuleCat.Hom.hom ((inclL 𝕜 p (s + 2)).f ((s + 1) + q)))
          (grSecX 𝕜 p (s + 1) ((s + 1) + q)
            (w : (Kg 𝕜 p (s + 1)).X ((s + 1) + q))))
      = (ModuleCat.Hom.hom ((inclL 𝕜 p (s + 2)).f ((s + q) + 1)))
          (Work.SSSR.castElem (Cc 𝕜 p (s + 2))
            (show (s + 1) + q = (s + q) + 1 by omega)
            (grSecX 𝕜 p (s + 1) ((s + 1) + q)
              (w : (Kg 𝕜 p (s + 1)).X ((s + 1) + q)))) :=
    evZdtv_castElem_map (inclL 𝕜 p (s + 2))
      (show (s + 1) + q = (s + q) + 1 by omega)
      (grSecX 𝕜 p (s + 1) ((s + 1) + q)
        (w : (Kg 𝕜 p (s + 1)).X ((s + 1) + q)))
  rw [hA]
  have hB : (ModuleCat.Hom.hom
        ((Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).d ((s + q) + 1) (s + q)))
        ((ModuleCat.Hom.hom ((inclL 𝕜 p (s + 2)).f ((s + q) + 1)))
          (Work.SSSR.castElem (Cc 𝕜 p (s + 2))
            (show (s + 1) + q = (s + q) + 1 by omega)
            (grSecX 𝕜 p (s + 1) ((s + 1) + q)
              (w : (Kg 𝕜 p (s + 1)).X ((s + 1) + q)))))
      = (ModuleCat.Hom.hom ((inclL 𝕜 p (s + 2)).f (s + q)))
          ((ModuleCat.Hom.hom ((Cc 𝕜 p (s + 2)).d ((s + q) + 1) (s + q)))
            (Work.SSSR.castElem (Cc 𝕜 p (s + 2))
              (show (s + 1) + q = (s + q) + 1 by omega)
              (grSecX 𝕜 p (s + 1) ((s + 1) + q)
                (w : (Kg 𝕜 p (s + 1)).X ((s + 1) + q))))) :=
    e2pd_inclL_d 𝕜 p (s + 2) ((s + q) + 1)
      (Work.SSSR.castElem (Cc 𝕜 p (s + 2))
        (show (s + 1) + q = (s + q) + 1 by omega)
        (grSecX 𝕜 p (s + 1) ((s + 1) + q)
          (w : (Kg 𝕜 p (s + 1)).X ((s + 1) + q))))
  rw [hB]
  have hC : (ModuleCat.Hom.hom ((Cc 𝕜 p (s + 2)).d ((s + q) + 1) (s + q)))
        (Work.SSSR.castElem (Cc 𝕜 p (s + 2))
          (show (s + 1) + q = (s + q) + 1 by omega)
          (grSecX 𝕜 p (s + 1) ((s + 1) + q)
            (w : (Kg 𝕜 p (s + 1)).X ((s + 1) + q))))
      = (ModuleCat.Hom.hom ((Cc 𝕜 p (s + 2)).d ((s + 1) + q) (s + q)))
          (grSecX 𝕜 p (s + 1) ((s + 1) + q)
            (w : (Kg 𝕜 p (s + 1)).X ((s + 1) + q))) :=
    evZdtv_d_castElem_left (show (s + 1) + q = (s + q) + 1 by omega)
      (show (ComplexShape.down ℕ).Rel ((s + 1) + q) (s + q) by
        rw [ComplexShape.down_Rel]; omega)
      (grSecX 𝕜 p (s + 1) ((s + 1) + q)
        (w : (Kg 𝕜 p (s + 1)).X ((s + 1) + q)))
  rw [hC]
  -- `∂(grSecX w) = incF v`, and `inclL` is compatible with `incF`
  rw [← hv, inclL_comp_apply 𝕜 p s (s + q) v]
  -- the two lifts of the cycle `Kgπ v` differ by an element of `ker (Kgπ s)`
  have hker : (ModuleCat.Hom.hom ((Kgπ 𝕜 p s).f (s + q)))
      (grSecX 𝕜 p s (s + q) ((ModuleCat.Hom.hom ((Kgπ 𝕜 p s).f (s + q))) v) - v) = 0 := by
    rw [map_sub, Kgπ_grSecX_apply, sub_self]
  have hzero := ker_Kgπ_inclL_eq_zero 𝕜 p s (s + q) (hannSerre 𝕜 p)
    (cochainFun 𝕜 p (s + q) (x : (Wc 𝕜 p).C.X (s + q))) x.2.1
    (grSecX 𝕜 p s (s + q) ((ModuleCat.Hom.hom ((Kgπ 𝕜 p s).f (s + q))) v) - v) hker
  have hsub : cochainFun 𝕜 p (s + q) (x : (Wc 𝕜 p).C.X (s + q))
        (((inclL 𝕜 p (s + 1)).f (s + q)).hom
          (grSecX 𝕜 p s (s + q) ((ModuleCat.Hom.hom ((Kgπ 𝕜 p s).f (s + q))) v)))
      = cochainFun 𝕜 p (s + q) (x : (Wc 𝕜 p).C.X (s + q))
          (((inclL 𝕜 p (s + 1)).f (s + q)).hom v) := by
    have hsplit : ((inclL 𝕜 p (s + 1)).f (s + q)).hom
          (grSecX 𝕜 p s (s + q) ((ModuleCat.Hom.hom ((Kgπ 𝕜 p s).f (s + q))) v) - v)
        = ((inclL 𝕜 p (s + 1)).f (s + q)).hom
            (grSecX 𝕜 p s (s + q) ((ModuleCat.Hom.hom ((Kgπ 𝕜 p s).f (s + q))) v))
          - ((inclL 𝕜 p (s + 1)).f (s + q)).hom v :=
      map_sub _ _ _
    rw [hsplit, map_sub] at hzero
    exact sub_eq_zero.mp hzero
  exact hsub.symm

end Work.Pi6.MSS
