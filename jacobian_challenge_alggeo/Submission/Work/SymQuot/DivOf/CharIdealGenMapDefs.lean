/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Evaluations at the lifted points, for the hub lemma C1 (`charIdealGen_map_eq`)

Let `C` be a curve over a field `K`, `F''/K` a field extension, and `x : Fin n → C(F'')` a
family of `F''`-points of `C`.  Each `x m` determines

* a closed point `ptPlace (x m)` of the base-changed curve `C_{F''}` (in an affine chart
  `W ⊆ C_{F''}` containing it), and
* an *evaluation map* `ptEval x W hmem m : Γ(C_{F''}, W) →+* F''`, the pullback of regular
  functions along the section `ptLeft (x m) : Spec F'' ⟶ C_{F''}`, read in `F''` through
  `Γ(Spec F'') ≅ F''`.

The place ideal of `ptPlace (x m)` is the kernel of this evaluation
(`mem_placeIdeal_iff_ptEval_eq_zero`), and the evaluation of a pulled-back section `secAlpha b`
is the value `valAtLift` of `b` at `x m` (`ptEval_secAlpha_eq_valAtLift`).
-/
import Mathlib
import Submission.Work.SymQuot.DivOf.C1Defs
import Submission.Work.SymQuot.DivOf.mem_placeIdeal_valAt_sub
import Submission.Work.SymQuot.DivOf.ptPlace_mem_bcOpens
import Submission.Work.SymQuot.DivOf.secAlpha_sub_mem_placeIdeal
import Submission.Work.SymQuot.DivOf.lift_mem_V
import Submission.Work.SymQuot.DivOf.genGenerator_map_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.SymQuot.DivOf

open Work.CurveBasics

variable {K : Type u} [Field K] {C : Curve K} {n : ℕ}

/-- The condition that the lift `Π_m x_m : Spec F'' ⟶ Cⁿ` of a point of `Symⁿ C` lands in the
open `d.openOf = Vⁿ ⊆ Cⁿ` of a chart `d`. -/
abbrev LandsInChartF {F : Type u} [Field F] [Algebra K F]
    {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F} (d : ChartPt C n p)
    {F'' : Type u} [Field F''] [Algebra K F''] (x : Fin n → Work.SpecLin.CurveFPt C F'') : Prop :=
  (⊤ : (Work.SpecLin.specOf (K := K) F'').left.Opens) ≤
    ((Limits.Pi.lift x : Work.SpecLin.specOf (K := K) F'' ⟶
      Work.SymQuot.prod C.toOver n)).left ⁻¹ᵁ d.openOf

section PtEval

variable {F'' : Type u} [Field F''] [Algebra K F'']

/-- The evaluation of a section of `Γ(C_{F''}, W)` at the `F''`-point `x m`: the pullback along
the section `ptLeft (x m) : Spec F'' ⟶ C_{F''}`, read in `F''` through `Γ(Spec F'') ≅ F''`.

The inclusion hypothesis `hσ` is explicit, so that this map can be compared with the composite
appearing in the existing lemmas `eval_sectionsAlgebraMap` and
`eval_secAlpha_eq_GammaSpecIso_apply`. -/
noncomputable def ptEvalHσ (x : Fin n → Work.SpecLin.CurveFPt C F'') (W : C.left.Opens)
    (m : Fin n) (hσ : ⊤ ≤ (Work.SpecLin.ptLeft (x m)) ⁻¹ᵁ C.bcOpens F'' W) :
    Γ((C.baseChange F'').left, C.bcOpens F'' W) →+* F'' :=
  ((Work.SpecLin.ptLeft (x m)).appLE (C.bcOpens F'' W) ⊤ hσ ≫
    (Scheme.ΓSpecIso (CommRingCat.of F'')).hom).hom

/-- The inclusion `⊤ ≤ ptLeft (x m) ⁻¹ᵁ W` coming from the fact that the (unique) point of
`Spec F''` lies in `W`. -/
theorem ptEvalHmem (x : Fin n → Work.SpecLin.CurveFPt C F'') (W : C.left.Opens)
    (hmem : ∀ m, (Work.SpecLin.ptPlace (x m)).point ∈ C.bcOpens F'' W) (m : Fin n) :
    ⊤ ≤ (Work.SpecLin.ptLeft (x m)) ⁻¹ᵁ C.bcOpens F'' W := by
  intro y _
  rw [show y = IsLocalRing.closedPoint F'' from Subsingleton.elim _ _]
  exact hmem m

/-- The evaluation of a section of `Γ(C_{F''}, W)` at the `F''`-point `x m`. -/
noncomputable def ptEval (x : Fin n → Work.SpecLin.CurveFPt C F'') (W : C.left.Opens)
    (hmem : ∀ m, (Work.SpecLin.ptPlace (x m)).point ∈ C.bcOpens F'' W) (m : Fin n) :
    Γ((C.baseChange F'').left, C.bcOpens F'' W) →+* F'' :=
  ptEvalHσ x W m (ptEvalHmem x W hmem m)

/-- `ptEval` does not depend on the proof of the inclusion of opens. -/
theorem ptEval_eq_ptEvalHσ (x : Fin n → Work.SpecLin.CurveFPt C F'') (W : C.left.Opens)
    (hmem : ∀ m, (Work.SpecLin.ptPlace (x m)).point ∈ C.bcOpens F'' W) (m : Fin n)
    (hσ : ⊤ ≤ (Work.SpecLin.ptLeft (x m)) ⁻¹ᵁ C.bcOpens F'' W)
    (a : Γ((C.baseChange F'').left, C.bcOpens F'' W)) :
    ptEval x W hmem m a = ptEvalHσ x W m hσ a := by
  have h : ptEvalHσ x W m (ptEvalHmem x W hmem m) = ptEvalHσ x W m hσ := by
    unfold ptEvalHσ
    rw [Work.SymQuot.appLE_congr_le (Work.SpecLin.ptLeft (x m))
      (ptEvalHmem x W hmem m) hσ]
  rw [ptEval, h]

/-- The evaluation of a constant section. -/
theorem ptEval_secConst (x : Fin n → Work.SpecLin.CurveFPt C F'') (W : C.left.Opens)
    (hmem : ∀ m, (Work.SpecLin.ptPlace (x m)).point ∈ C.bcOpens F'' W) (m : Fin n) (c : F'') :
    ptEval x W hmem m (secConst C F'' W c) = c := by
  rw [ptEval_eq_ptEvalHσ (hσ := ptEvalHmem x W hmem m)]
  exact eval_sectionsAlgebraMap (C.bcOpens F'' W) (Work.SpecLin.ptLeft (x m))
    (ptEvalHmem x W hmem m) (Work.SpecLin.Points.ptLeft_comp_hom (x m)) c

/-- The evaluation of a pulled-back section `secAlpha b` at `x m`. -/
theorem ptEval_secAlpha (x : Fin n → Work.SpecLin.CurveFPt C F'') (W : C.left.Opens)
    (hmem : ∀ m, (Work.SpecLin.ptPlace (x m)).point ∈ C.bcOpens F'' W) (m : Fin n)
    (b : C.left.presheaf.obj (Opposite.op W))
    (hsle : ⊤ ≤ Over.Hom.left (x m) ⁻¹ᵁ W) :
    ptEval x W hmem m (secAlpha C F'' W b) =
      (Scheme.ΓSpecIso (CommRingCat.of F'')).hom.hom
        ((Scheme.Hom.appLE (Over.Hom.left (x m)) W ⊤ hsle).hom b) := by
  rw [ptEval_eq_ptEvalHσ (hσ := ptEvalHmem x W hmem m)]
  exact eval_secAlpha_eq_GammaSpecIso_apply W (x m) hsle (ptEvalHmem x W hmem m) b

/-- The place ideal of `ptPlace (x m)` is the kernel of the evaluation at `x m`. -/
theorem mem_placeIdeal_iff_ptEval_eq_zero (x : Fin n → Work.SpecLin.CurveFPt C F'') {W : C.left.Opens}
    (hW : IsAffineOpen W) (hmem : ∀ m, (Work.SpecLin.ptPlace (x m)).point ∈ C.bcOpens F'' W)
    (m : Fin n) (a : Γ((C.baseChange F'').left, C.bcOpens F'' W)) :
    a ∈ placeIdeal (C.baseChange F'') (C.bcOpens F'' W) (Work.SpecLin.ptPlace (x m)) (hmem m) ↔
      ptEval x W hmem m a = 0 := by
  classical
  haveI hUne : Nonempty (C.bcOpens F'' W) := ⟨⟨(Work.SpecLin.ptPlace (x m)).point, hmem m⟩⟩
  have hσ := ptEvalHmem x W hmem m
  have hpt_eq : (⟨(Work.SpecLin.ptPlace (x m)).point, hmem m⟩ : C.bcOpens F'' W) =
      ⟨(Work.SpecLin.ptLeft (x m)) (IsLocalRing.closedPoint F''), hσ trivial⟩ :=
    Subtype.ext rfl
  rw [placeIdeal_eq_primeIdealOf (BaseChange.isAffineOpen_bcOpens F'' W hW)
      (Work.SpecLin.ptPlace (x m)) (hmem m), hpt_eq,
    mem_primeIdealOf_iff_appLE_GammaSpecIso_eq_zero]
  rfl

end PtEval

section Chart

variable {F : Type u} [Field F] [Algebra K F] [NeZero n] [Work.SymQuot.CurveAffineCover C]
  {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F}
variable {F'' : Type u} [Field F''] [Algebra K F'']
variable (d : ChartPt C n p) (x : Fin n → Work.SpecLin.CurveFPt C F'')

/-- **The `m`-th point of a lift lands in the chart open `V`.** -/
theorem hsle_of_landsInChart (h : LandsInChartF d x) (m : Fin n) :
    ⊤ ≤ Over.Hom.left (x m) ⁻¹ᵁ d.V := by
  intro z _
  have hfac : Over.Hom.left (Limits.Pi.lift x) ≫
      Over.Hom.left (Work.SymQuot.proj C.toOver n m) = Over.Hom.left (x m) := by
    simpa only [Over.comp_left] using congrArg Over.Hom.left (Limits.Pi.lift_comp_π x m)
  have hz : (Limits.Pi.lift x).left z ∈ d.openOf := h trivial
  have hz' : (Work.SymQuot.proj C.toOver n m).left ((Limits.Pi.lift x).left z) ∈ d.V :=
    Work.SymQuot.mem_piOpen.mp hz m
  have hcomp : (Work.SymQuot.proj C.toOver n m).left ((Limits.Pi.lift x).left z) = (x m).left z := by
    rw [← hfac, Scheme.Hom.comp_apply]
    rfl
  rwa [hcomp] at hz'

/-- **The chart open `V` is nonempty** as soon as a lift lands in the chart. -/
theorem nonempty_chart_of_landsInChart (h : LandsInChartF d x) : Nonempty ↥d.V := by
  obtain ⟨m⟩ := (inferInstance : Nonempty (Fin n))
  exact ⟨⟨(x m).left (IsLocalRing.closedPoint F''), hsle_of_landsInChart d x h m trivial⟩⟩

/-- **The evaluation of `secAlpha b` at `x m` is `valAtLift`.** -/
theorem ptEval_secAlpha_eq_valAtLift (h : LandsInChartF d x)
    (hmem : ∀ m, (Work.SpecLin.ptPlace (x m)).point ∈ C.bcOpens F'' d.V) (m : Fin n)
    (b : C.left.presheaf.obj (Opposite.op d.V)) :
    ptEval x d.V hmem m (secAlpha C F'' d.V b) = valAtLift d x h m b :=
  (ptEval_secAlpha x d.V hmem m b (hsle_of_landsInChart d x h m)).trans
    (valAtLift_eq_GammaSpecIso_apply d x h m (hsle_of_landsInChart d x h m) b).symm

end Chart

end Work.SymQuot.DivOf

namespace Work.SymQuot.DivOf

open Work.CurveBasics

/-- **The coefficients of an element of `Ideal.map MvPolynomial.C I` lie in `I`.** -/
theorem eval₂Hom_mem_of_mem_map_C {R : Type*} [CommRing R] {σ : Type*} (I : Ideal R)
    (f : σ → R) {h : MvPolynomial σ R}
    (hh : h ∈ Ideal.map (MvPolynomial.C : R →+* MvPolynomial σ R) I) :
    MvPolynomial.eval₂Hom (RingHom.id R) f h ∈ I := by
  have hle : Ideal.map (MvPolynomial.C : R →+* MvPolynomial σ R) I ≤
      Ideal.comap (MvPolynomial.eval₂Hom (RingHom.id R) f) I := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    show MvPolynomial.eval₂Hom (RingHom.id R) f (MvPolynomial.C r) ∈ I
    rw [MvPolynomial.eval₂Hom_C]
    exact hr
  exact hle hh

/-- **The evaluation of the mapped generic generator.**

For a family `b : Fin r → Γ(C,V)` of chart sections, a field element `f i` for each `i` and the
substitution `X_i ↦ secConst (f i)`, the image under `bcSec` of the generic Cayley–Hamilton
element `genGenerator` evaluates to `∏_m (Σ_i f_i b_i - (Σ_i f_i b_i)(x_m))`: the value at the
`m`-th lifted point of the `F''`-combination `Σ_i f_i b_i` of the `b_i`. -/
theorem eval₂Hom_map_genGenerator {K : Type u} [Field K] {C : Curve K} {n : ℕ} [NeZero n]
    [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F} (d : ChartPt C n p)
    {F'' : Type u} [Field F''] [Algebra K F''] [Algebra F F''] [IsScalarTower K F F'']
    (x : Fin n → Work.SpecLin.CurveFPt C F'')
    (hx : Work.SymQuot.Sym.powMap C n x =
      Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K F F'') p)
    {r : ℕ} (b : Fin r → Γ(C.left, d.V)) (f : Fin r → F'') :
    MvPolynomial.eval₂Hom (RingHom.id Γ((C.baseChange F'').left, C.bcOpens F'' d.V))
        (fun i => secConst C F'' d.V (f i))
        (MvPolynomial.map (bcSec (C := C) F F'' d.V) (d.genGenerator (K := K) b)) =
      ∏ m, ((∑ i, secConst C F'' d.V (f i) * secAlpha C F'' d.V (b i)) -
        secConst C F'' d.V
          (∑ i, f i * valAtLift d x (lift_mem_V d x hx) m (b i))) := by
  rw [genGenerator_map_eq d x hx b, map_prod]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [map_sum]
  rw [Finset.sum_congr rfl (fun i _ => by
    rw [map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', RingHom.id_apply])]
  rw [Finset.sum_congr rfl (fun i _ => sub_mul _ _ _), Finset.sum_sub_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← map_mul]
    ring

end Work.SymQuot.DivOf

namespace Work.SymQuot.DivOf

open Work.CurveBasics

section Hmem

variable {K : Type u} [Field K] {C : Curve K} {n : ℕ} {F'' : Type u} [Field F''] [Algebra K F'']

/-- If the `m`-th lifted point lies in the base-changed open `W_F`, then the `F''`-point `x m`
itself lands in `W`. -/
theorem hsle_of_hmem (x : Fin n → Work.SpecLin.CurveFPt C F'') (W : C.left.Opens) (m : Fin n)
    (hmem : (Work.SpecLin.ptPlace (x m)).point ∈ C.bcOpens F'' W) :
    ⊤ ≤ Over.Hom.left (x m) ⁻¹ᵁ W := by
  haveI : Subsingleton ↥(Over.left (Work.SpecLin.specOf (K := K) F'')) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of F'')))
  intro z _
  rw [show z = IsLocalRing.closedPoint F'' from Subsingleton.elim _ _]
  have h : (C.baseChangeFst F'') (Work.SpecLin.ptToPoint (x m)) ∈ W := hmem
  have hproj : (C.baseChangeFst F'') (Work.SpecLin.ptToPoint (x m)) =
      (x m).left (IsLocalRing.closedPoint F'') :=
    congrArg (fun (f : Spec (CommRingCat.of F'') ⟶ C.left) =>
      f (IsLocalRing.closedPoint F'')) (Work.SpecLin.ptLeft_fst (x m))
  rwa [hproj] at h

/-- A base-changed open containing a lifted point is nonempty, so its preimage in `C` is too. -/
theorem nonempty_chart_of_hmem (x : Fin n → Work.SpecLin.CurveFPt C F'') (W : C.left.Opens)
    (m : Fin n) (hmem : (Work.SpecLin.ptPlace (x m)).point ∈ C.bcOpens F'' W) :
    Nonempty W :=
  ⟨(C.baseChangeFst F'') (Work.SpecLin.ptToPoint (x m)), hmem⟩

end Hmem

end Work.SymQuot.DivOf

namespace Work.SymQuot.DivOf

open Work.CurveBasics

section PlaceIdealCongr

variable {F : Type u} [Field F] {C : Curve F}

/-- The place ideal depends on the place only (the proof of membership in the open is
irrelevant). -/
theorem placeIdeal_eq_of_place_eq {V : C.left.Opens} {z z' : C.Place} (h : z = z')
    (hz : z.point ∈ V) (hz' : z'.point ∈ V) :
    placeIdeal C V z hz = placeIdeal C V z' hz' := by
  subst h
  rfl

/-- Membership in the place ideal transports along an equality of places. -/
theorem mem_placeIdeal_of_place_eq {V : C.left.Opens} {z z' : C.Place} (h : z = z')
    (hz : z.point ∈ V) (hz' : z'.point ∈ V) {a : Γ(C.left, V)}
    (ha : a ∈ placeIdeal C V z hz) :
    a ∈ placeIdeal C V z' hz' := by
  subst h
  exact ha

end PlaceIdealCongr

end Work.SymQuot.DivOf
