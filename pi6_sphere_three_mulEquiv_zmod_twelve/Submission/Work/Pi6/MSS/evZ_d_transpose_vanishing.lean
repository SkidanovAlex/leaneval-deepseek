import Mathlib
import Submission.Work.Pi6.MSS.E1Map
import Submission.Work.Pi6.MSS.e2Pairing_descent
import Submission.Work.SSSR.chainCondition_gen
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The transposed `d_1`-differential vanishes on representatives of `E_1`-cycles

Let `p : E → B`, `W = Wc 𝕜 p` the Serre cochain filtration of `p`, `x ∈ Z_1^s C^{s+q}` and
`y ∈ Z_1^{s+1} C^{(s+1)+q} = xcast (δx)` its transposed coboundary.  If `W ∈ Z_∞(gr_{s+1} C_*(E))`
is a cycle whose lift `grSecX_{s+1} W` has a boundary which decomposes as
`∂(grSecX_{s+1} W) = Y + ∂Z` with `Y` a chain of `A_s` and `Z` a chain of `A_{s+1}`, then the
evaluation `evZ y (mkQ W)` of the transposed differential of `y` on `W` vanishes.

The proof transports `y = xcast (δx)` to the degree of `δx` (so that the transposed differential
formula `cochainFun (δx) v = cochainFun x (∂v)` applies), moves the degree transport past the
inclusion `inclL`, and then splits the boundary of `grSecX_{s+1} W`: the `A_s`-part is killed
because `x ∈ F^s`, and the `∂Z`-part is killed because `δx ∈ F^{s+1}`.
-/

set_option autoImplicit false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- Degree transport on the level of elements is independent of the chosen proof of the degree
equality. -/
lemma evZdtv_castElem_congr {R : Type} [CommRing R] {K : ChainComplex (ModuleCat R) ℕ}
    {i j : ℕ} (h h' : i = j) (x : K.X i) :
    Work.SSSR.castElem K h x = Work.SSSR.castElem K h' x := by
  cases h
  cases h'
  rfl

/-- The degree transport `eqToHom` in `ModuleCat` is the element level transport `castElem`. -/
lemma evZdtv_castElem_eqToHom {R : Type} [CommRing R] {K : ChainComplex (ModuleCat R) ℕ}
    {i j : ℕ} (h : i = j) (x : K.X i) :
    (ModuleCat.Hom.hom (CategoryTheory.eqToHom (congrArg (fun n => K.X n) h))) x
      = Work.SSSR.castElem K h x := by
  cases h
  rfl

/-- Degree transport is natural for chain maps. -/
lemma evZdtv_castElem_map {R : Type} [CommRing R] {K L : ChainComplex (ModuleCat R) ℕ}
    (φ : K ⟶ L) {i j : ℕ} (h : i = j) (x : K.X i) :
    Work.SSSR.castElem L h ((φ.f i) x) = (φ.f j) (Work.SSSR.castElem K h x) := by
  cases h
  rfl

/-- The differential only depends on the source degree up to the degree transport. -/
lemma evZdtv_d_castElem_left {R : Type} [CommRing R] {K : ChainComplex (ModuleCat R) ℕ}
    {i i' j : ℕ} (h : i = i') (hji : (ComplexShape.down ℕ).Rel i j) (x : K.X i) :
    (ModuleCat.Hom.hom (K.d i' j)) (Work.SSSR.castElem K h x)
      = (ModuleCat.Hom.hom (K.d i j)) x := by
  have hji' : (ComplexShape.down ℕ).Rel i' j := h ▸ hji
  have h0 := HomologicalComplex.eqToHom_comp_d K hji hji'
  have h2 := congrArg (fun (f : K.X i ⟶ K.X j) => ModuleCat.Hom.hom f x) h0
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  rw [← h2, evZdtv_castElem_eqToHom ((ComplexShape.down ℕ).prev_eq hji hji') x]

/-- The evaluation against a degree transported functional. -/
lemma evZdtv_xcast_cochainFun (𝕜 : Type) [Field 𝕜] (p : C(E, B)) {a b : ℕ} (h : a = b)
    (φ : (Work.Pi6.MSS.Wc 𝕜 p).C.X a) (V : (Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).X b) :
    Work.Pi6.MSS.cochainFun 𝕜 p b ((Work.Pi6.MSS.Wc 𝕜 p).xcast h φ) V
      = Work.Pi6.MSS.cochainFun 𝕜 p a φ
          (Work.SSSR.castElem (Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)) h.symm V) := by
  subst h
  rfl

theorem evZ_d_transpose_vanishing (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (s q : ℕ)
    (hann : ∀ s n, Work.Pi6.MSS.coFilt 𝕜 (Work.Pi6.MSS.sF p) s n =
      Work.Pi6.MSS.compAnn 𝕜 (Work.StemsB.serreSubcomplex (Work.Pi6.MSS.sF p) s) n)
    (x : ↥(Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 1 s (s+q)))
    (y : ↥(Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 1 (s+1) ((s+1)+q)))
    (hy : (y : (Work.Pi6.MSS.Wc 𝕜 p).C.X ((s+1)+q))
      = (Work.Pi6.MSS.Wc 𝕜 p).xcast (show (s+q)+1 = (s+1)+q by omega)
          ((Work.Pi6.MSS.Wc 𝕜 p).d (s+q) (x : (Work.Pi6.MSS.Wc 𝕜 p).C.X (s+q))))
    (W : ↥(Work.StemsB.fdZ 𝕜 (Work.Pi6.MSS.Kg 𝕜 p (s+1)) ((s+1)+q)))
    (hW : ∃ Y : ↥((Work.Pi6.MSS.Cc 𝕜 p s).X (s+q)),
      ∃ Z : ↥((Work.Pi6.MSS.Cc 𝕜 p (s+1)).X (s+q+1)),
        (Work.Pi6.MSS.inclL 𝕜 p (s+2)).f (s+q)
            (((Work.Pi6.MSS.Cc 𝕜 p (s+2)).d ((s+1)+q) (s+q)).hom
              (Work.Pi6.MSS.grSecX 𝕜 p (s+1) ((s+1)+q) W.1))
          = (Work.Pi6.MSS.inclL 𝕜 p s).f (s+q) Y
            + (Work.Pi6.MSS.inclL 𝕜 p (s+1)).f (s+q)
                (((Work.Pi6.MSS.Cc 𝕜 p (s+1)).d (s+q+1) (s+q)).hom Z)) :
    Work.Pi6.MSS.evZ 𝕜 p (s+1) ((s+1)+q) hann y
      ((Work.StemsB.fdH 𝕜 (Work.Pi6.MSS.Kg 𝕜 p (s+1)) ((s+1)+q)).mkQ W) = 0 := by
  rw [Work.Pi6.MSS.evZ_apply]
  rw [hy]
  rw [evZdtv_xcast_cochainFun 𝕜 p]
  rw [← Work.Pi6.MSS.Wc_d_apply_applied 𝕜 p (s+q)]
  -- move the degree transport past the inclusion `C_*(A_{s+2}) ⟶ C_*(E)`
  have hA : Work.SSSR.castElem (Work.SSSR.sChains 𝕜 (Work.SSS.sSing E))
        (show (s+1)+q = (s+q)+1 by omega)
        ((ModuleCat.Hom.hom ((Work.Pi6.MSS.inclL 𝕜 p (s+2)).f ((s+1)+q)))
          (Work.Pi6.MSS.grSecX 𝕜 p (s+1) ((s+1)+q) W.1))
      = (ModuleCat.Hom.hom ((Work.Pi6.MSS.inclL 𝕜 p (s+2)).f (s+q+1)))
          (Work.SSSR.castElem (Work.Pi6.MSS.Cc 𝕜 p (s+2))
            (show (s+1)+q = (s+q)+1 by omega)
            (Work.Pi6.MSS.grSecX 𝕜 p (s+1) ((s+1)+q) W.1)) :=
    evZdtv_castElem_map (Work.Pi6.MSS.inclL 𝕜 p (s+2))
      (show (s+1)+q = (s+q)+1 by omega) (Work.Pi6.MSS.grSecX 𝕜 p (s+1) ((s+1)+q) W.1)
  rw [hA]
  -- the inclusion commutes with the differential
  have hB : (ModuleCat.Hom.hom ((Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).d (s+q+1) (s+q)))
        ((ModuleCat.Hom.hom ((Work.Pi6.MSS.inclL 𝕜 p (s+2)).f (s+q+1)))
          (Work.SSSR.castElem (Work.Pi6.MSS.Cc 𝕜 p (s+2))
            (show (s+1)+q = (s+q)+1 by omega)
            (Work.Pi6.MSS.grSecX 𝕜 p (s+1) ((s+1)+q) W.1)))
      = (ModuleCat.Hom.hom ((Work.Pi6.MSS.inclL 𝕜 p (s+2)).f (s+q)))
          ((ModuleCat.Hom.hom ((Work.Pi6.MSS.Cc 𝕜 p (s+2)).d (s+q+1) (s+q)))
            (Work.SSSR.castElem (Work.Pi6.MSS.Cc 𝕜 p (s+2))
              (show (s+1)+q = (s+q)+1 by omega)
              (Work.Pi6.MSS.grSecX 𝕜 p (s+1) ((s+1)+q) W.1))) :=
    Work.Pi6.MSS.e2pd_inclL_d 𝕜 p (s+2) (s+q+1)
      (Work.SSSR.castElem (Work.Pi6.MSS.Cc 𝕜 p (s+2))
        (show (s+1)+q = (s+q)+1 by omega)
        (Work.Pi6.MSS.grSecX 𝕜 p (s+1) ((s+1)+q) W.1))
  rw [hB]
  -- the differential only depends on the source degree up to the degree transport
  have hC : (ModuleCat.Hom.hom ((Work.Pi6.MSS.Cc 𝕜 p (s+2)).d (s+q+1) (s+q)))
        (Work.SSSR.castElem (Work.Pi6.MSS.Cc 𝕜 p (s+2))
          (show (s+1)+q = (s+q)+1 by omega)
          (Work.Pi6.MSS.grSecX 𝕜 p (s+1) ((s+1)+q) W.1))
      = (ModuleCat.Hom.hom ((Work.Pi6.MSS.Cc 𝕜 p (s+2)).d ((s+1)+q) (s+q)))
          (Work.Pi6.MSS.grSecX 𝕜 p (s+1) ((s+1)+q) W.1) :=
    evZdtv_d_castElem_left (show (s+1)+q = (s+q)+1 by omega)
      (show (ComplexShape.down ℕ).Rel ((s+1)+q) (s+q) by
        rw [ComplexShape.down_Rel]; omega)
      (Work.Pi6.MSS.grSecX 𝕜 p (s+1) ((s+1)+q) W.1)
  rw [hC]
  -- split the boundary of the lift of `W`
  obtain ⟨Y, Z, hYZ⟩ := hW
  rw [hYZ, map_add]
  have hxF : (x : (Work.Pi6.MSS.Wc 𝕜 p).C.X (s+q)) ∈ (Work.Pi6.MSS.Wc 𝕜 p).F s (s+q) :=
    ((Work.Pi6.MSS.mem_pZ_one (Work.Pi6.MSS.Wc 𝕜 p) s (s+q) x.1).mp x.2).1
  have hdxF : (Work.Pi6.MSS.Wc 𝕜 p).d (s+q) (x : (Work.Pi6.MSS.Wc 𝕜 p).C.X (s+q))
      ∈ (Work.Pi6.MSS.Wc 𝕜 p).F (s+1) (s+q+1) :=
    ((Work.Pi6.MSS.mem_pZ_one (Work.Pi6.MSS.Wc 𝕜 p) s (s+q) x.1).mp x.2).2
  -- the `A_s`-part is killed by `x ∈ F^s`
  have hY0 : (Work.Pi6.MSS.cochainFun 𝕜 p (s+q) (x : (Work.Pi6.MSS.Wc 𝕜 p).C.X (s+q)))
      ((ModuleCat.Hom.hom ((Work.Pi6.MSS.inclL 𝕜 p s).f (s+q))) Y) = 0 :=
    ((Work.Pi6.MSS.mem_F_iff 𝕜 p s (s+q) hann)
      (x : (Work.Pi6.MSS.Wc 𝕜 p).C.X (s+q))).mp hxF Y
  -- the `∂Z`-part is killed because `δx ∈ F^{s+1}` and integrates by parts
  have hZ0 : (Work.Pi6.MSS.cochainFun 𝕜 p (s+q) (x : (Work.Pi6.MSS.Wc 𝕜 p).C.X (s+q)))
      ((ModuleCat.Hom.hom ((Work.Pi6.MSS.inclL 𝕜 p (s+1)).f (s+q)))
        ((ModuleCat.Hom.hom ((Work.Pi6.MSS.Cc 𝕜 p (s+1)).d (s+q+1) (s+q))) Z)) = 0 := by
    have hZ' : (ModuleCat.Hom.hom ((Work.Pi6.MSS.inclL 𝕜 p (s+1)).f (s+q)))
        ((ModuleCat.Hom.hom ((Work.Pi6.MSS.Cc 𝕜 p (s+1)).d (s+q+1) (s+q))) Z)
        = (ModuleCat.Hom.hom ((Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).d (s+q+1) (s+q)))
            ((ModuleCat.Hom.hom ((Work.Pi6.MSS.inclL 𝕜 p (s+1)).f (s+q+1))) Z) :=
      (Work.Pi6.MSS.e2pd_inclL_d 𝕜 p (s+1) (s+q+1) Z).symm
    rw [hZ', Work.Pi6.MSS.Wc_d_apply_applied 𝕜 p (s+q)]
    exact ((Work.Pi6.MSS.mem_F_iff 𝕜 p (s+1) (s+q+1) hann)
      ((Work.Pi6.MSS.Wc 𝕜 p).d (s+q) (x : (Work.Pi6.MSS.Wc 𝕜 p).C.X (s+q)))).mp hdxF Z
  rw [hY0, hZ0, zero_add]

end Work.Pi6.MSS
