import Mathlib
import Submission.Work.Pi6.MSS.e2Bar
import Submission.Work.Pi6.MSS.evZ_transpose
import Submission.Work.Pi6.MSS.pagesData
import Submission.Work.Pi6.MSS.evSaux
import Submission.Work.Pi6.MSS.d1elt_class
import Submission.Work.Pi6.MSS.d1elt_lift
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The `E_2`-pairing vanishes on the image of `d¹`

Let `p : E → B` and `W = Wc 𝕜 p` the Serre cochain filtration of `p` over a field `𝕜`.  The pairing
on representatives

`e2L0 x v = evZ x (e2Hb v)`  (`v` a `d¹`-cycle of `E¹_{s,q}`, `x ∈ Z_2^s`)

descends to the `E_2`-term in the second variable: for every `u ∈ E¹_{s+1,q}` the value on
`d¹ u ∈ Z¹_{s,q} ⊆ E¹_{s,q}` vanishes.  Equivalently, `e2L0 x` lands in the annihilator of
`im d¹ ⊆ ker d¹`, i.e. in the image of `(E²_{s,q})^*` (cf. `Submission/Work/Pi6/MSS/e2Bar.lean`).

The proof is the transposition of the first differential.  Write `u = e1elt w` for a cycle `w` of
the graded piece `gr_{s+1}` (possible because `fdZ → fdZ ⧸ fdH` is surjective, `e2Hb` being an
isomorphism), so that `e2Hb (d¹ u) = d1elt w`.  Then

* `evZ x (d1elt w) = evS x (d¹ w)` (`evS` is the descent of `evZ` to the first page), and
* `evS x (d¹ w) = evZ y (mkQ w)` for `y = xcast (δx)`, which is `Work.Pi6.MSS.evZ_transpose`,

and `evZ y (mkQ w) = 0` because `y ∈ F^{s+2}` is the coboundary of the page-two cycle `x ∈ Z_2^s`
and the cycle representative `grSecX_{s+1} w` lies in the chains of `A_{s+2}`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.MSS

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **The pairing `e2L0` on representatives**, unfolded: it is the evaluation `evZ` of the `Z_1^s`
cycle underlying `x` on the `Z_{s+q} ⧸ B_{s+q}`-class of the `d¹`-cycle `v`. -/
lemma e2L0_evZ_apply (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (s q : ℕ)
    (x : ↥(pZ 𝕜 (Wc 𝕜 p) 2 s (s + q))) (v : ↥(e2KerD 𝕜 p s q)) :
    e2L0 𝕜 E B p s q x v =
      (evZ 𝕜 p s (s + q) (hannSerre 𝕜 p))
        ⟨(x : (Wc 𝕜 p).C.X (s + q)), pZ_two_le_one 𝕜 p s (s + q) x.2⟩
        ((e2Hb 𝕜 (Kg 𝕜 p s) (s + q)).hom.hom
          (v : (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).X s)) := by
  rw [e2L0]
  simp only [LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
  congr 1

theorem e2L0_imd (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (s q : ℕ) (x : ↥(Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 2 s (s + q)))
    (u : (Work.SSSR.E1Complex 𝕜 (Work.Pi6.MSS.e1cFilt 𝕜 p) q).X (s + 1)) :
    Work.Pi6.MSS.e2L0 𝕜 E B p s q x (Work.Pi6.MSS.e2dIm 𝕜 E B p s q u) = 0 := by
  -- a cycle of the graded piece `gr_{s+1}` representing the `E¹`-class `u`
  obtain ⟨w, hw⟩ : ∃ w : ↥(Work.StemsB.fdZ 𝕜 (Kg 𝕜 p (s + 1)) ((s + 1) + q)),
      e1elt 𝕜 p (s + 1) q w = u := by
    obtain ⟨w, hw⟩ := Submodule.mkQ_surjective
      (Work.StemsB.fdH 𝕜 (Kg 𝕜 p (s + 1)) ((s + 1) + q))
      ((e2Hb 𝕜 (Kg 𝕜 p (s + 1)) ((s + 1) + q)).hom.hom u)
    exact ⟨w, by rw [e1elt, hw]; exact CategoryTheory.Iso.hom_inv_id_apply _ u⟩
  rw [e2L0_evZ_apply]
  -- `e2dIm u` is the `d¹`-differential applied to `u`
  have hd : ((e2dIm 𝕜 E B p s q u : ↥(e2KerD 𝕜 p s q)) :
      (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).X s)
      = (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).d (s + 1) s u := rfl
  rw [hd, ← hw]
  -- now the goal is `evZ x (d1elt w) = 0`
  change (evZ 𝕜 p s (s + q) (hannSerre 𝕜 p)
      ⟨(x : (Wc 𝕜 p).C.X (s + q)), pZ_two_le_one 𝕜 p s (s + q) x.2⟩)
      (d1elt 𝕜 p s q w) = 0
  -- the transposed coboundary `y = xcast (δx)` is a `Z_1^{s+1}`-cycle
  have hxδ : (Wc 𝕜 p).d (s + q) (x : (Wc 𝕜 p).C.X (s + q))
      ∈ pZ 𝕜 (Wc 𝕜 p) 1 (s + 1) ((s + q) + 1) := by
    refine (mem_pZ_one (Wc 𝕜 p) (s + 1) ((s + q) + 1) _).mpr ⟨?_, ?_⟩
    · exact pd_F_mono_of_le (W := Wc 𝕜 p) (show s + 1 ≤ s + 2 by omega) x.2.2
    · rw [pd_d_comp_d_apply (𝕜 := 𝕜) (W := Wc 𝕜 p) (s + q) (x : (Wc 𝕜 p).C.X (s + q))]
      exact Submodule.zero_mem _
  have hdeg : (s + q) + 1 = (s + 1) + q := by omega
  let y : ↥(pZ 𝕜 (Wc 𝕜 p) 1 (s + 1) ((s + 1) + q)) :=
    ⟨(Wc 𝕜 p).xcast hdeg ((Wc 𝕜 p).d (s + q) (x : (Wc 𝕜 p).C.X (s + q))),
      pd_pZ_xcast (𝕜 := 𝕜) (W := Wc 𝕜 p) (r := 1) (a := s + 1) (b := s + 1)
        (m := (s + q) + 1) (k := (s + 1) + q) (rfl : s + 1 = s + 1) hdeg hxδ⟩
  have hyF : (y : (Wc 𝕜 p).C.X ((s + 1) + q)) ∈ (Wc 𝕜 p).F (s + 2) ((s + 1) + q) := by
    show (Wc 𝕜 p).xcast hdeg ((Wc 𝕜 p).d (s + q) (x : (Wc 𝕜 p).C.X (s + q)))
      ∈ (Wc 𝕜 p).F (s + 2) ((s + 1) + q)
    exact (pd_xcast_mem_iff (W := Wc 𝕜 p) (t := s + 2) hdeg _).mpr x.2.2
  have hy : (y : (Wc 𝕜 p).C.X ((s + 1) + q))
      = (Wc 𝕜 p).xcast (show (s + q) + 1 = (s + 1) + q by omega)
          ((Wc 𝕜 p).d (s + q) (x : (Wc 𝕜 p).C.X (s + q))) :=
    pd_xcast_congr (W := Wc 𝕜 p) hdeg _ _
  -- `evZ` on the first page is `evS` on the cohomology class
  have hevS : evS 𝕜 p s (s + q) (hannSerre 𝕜 p)
      (Submodule.mkQ ((pDen 𝕜 (Wc 𝕜 p) 1 s (s + q)).comap
        (pZ 𝕜 (Wc 𝕜 p) 1 s (s + q)).subtype)
        ⟨(x : (Wc 𝕜 p).C.X (s + q)), pZ_two_le_one 𝕜 p s (s + q) x.2⟩)
      = evZ 𝕜 p s (s + q) (hannSerre 𝕜 p)
        ⟨(x : (Wc 𝕜 p).C.X (s + q)), pZ_two_le_one 𝕜 p s (s + q) x.2⟩ := by
    rw [evS]
    exact Submodule.liftQ_apply _ _ _
  rw [← hevS]
  -- transposition
  rw [← evZ_transpose 𝕜 E B p s q
      ⟨(x : (Wc 𝕜 p).C.X (s + q)), pZ_two_le_one 𝕜 p s (s + q) x.2⟩ y hy w]
  -- and `y ∈ F^{s+2}` kills the chains of `A_{s+2}`
  rw [evZ_apply 𝕜 p (s + 1) ((s + 1) + q) (hannSerre 𝕜 p) y w]
  exact ((mem_F_iff 𝕜 p (s + 2) ((s + 1) + q) (hannSerre 𝕜 p)
    (y : (Wc 𝕜 p).C.X ((s + 1) + q))).mp hyF)
    (grSecX 𝕜 p (s + 1) ((s + 1) + q) (w : (Kg 𝕜 p (s + 1)).X ((s + 1) + q)))

end

end Work.Pi6.MSS
