import Mathlib
import Submission.Work.Whitney.TCMDefs
import Submission.Work.Whitney.Mpun_eq_of_fibrewise
import Submission.Work.Whitney.tcmRelCup_natural
import Submission.Work.Whitney.tcmRelCup_unit_right
import Submission.Work.Whitney.tcmModelMul_of_point
import Submission.Work.Thom.thomClass_of_finite_cover

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The model product formula `Work.Whitney.tcmModelMul`

**The statement** (`Submission/Work/Whitney/_tcm/REDUCTION.md` §2, item 2): the relative–relative cup
of the two pulled-back model Thom classes is the model class of the sum,

  `tcmRelCup (pr₁^* Mpun p) (pr₂^* Mpun q) = tcmF^* (Mpun (p+q))`,

an equality in `H^{p+q}(B × (ℝ^p × ℝ^q), A ∪ C)` with `A = {first ≠ 0}`, `C = {second ≠ 0}`.
It is *choice-free* (it mentions only `Mpun`, `tcmRelCup`, `relCohMap`), it is the mathematical heart
of the top-class multiplicativity (the "cross product of the two generators is the generator"), and
it is needed both by the chart bookkeeping and by the cure's use.

**Route** (see `_tcm/REDUCTION.md`): the boundary cases `p = 0` / `q = 0` (the unit law of the
relative–relative cup together with `Mpun 0`), the *reduction to a point* — the punctured model class
is detected by its restrictions to the fibres (`Work.Whitney.Mpun_eq_of_fibrewise`, transported along
the homeomorphism of pairs `tcmF`), the fibre restriction of the cup being computed by naturality
(`Work.Whitney.tcmRelCup_natural`, `Work.Thom.Mpun_natural`) — and the *point case* (the sign
calibration, through the suspension recursion `Work.Thom.Mn = step (Mn ·)` and the transgression
square `Work.Thom.suspensionStep_cup`).

This file is work in progress: the statements below are the interface; the proofs are being built.
-/

namespace Work.Whitney

open Work.Thom
open Work.Cohomology
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

variable {B : Type} [TopologicalSpace B]

/-- For `p = 0` the first closed set is empty (the first fibre coordinate lives in `ℝ^0`). -/
theorem tcmA_zero (q : ℕ) : tcmA B 0 q = (∅ : Set (tcmX B 0 q)) := by
  ext x
  exact ⟨fun hx => hx (Subsingleton.elim x.2.1 0), fun hx => hx.elim⟩

/-- For `q = 0` the second closed set is empty. -/
theorem tcmC_zero (p : ℕ) : tcmC B p 0 = (∅ : Set (tcmX B p 0)) := by
  ext x
  exact ⟨fun hx => hx (Subsingleton.elim x.2.2 0), fun hx => hx.elim⟩

/-- For `q = 0` the union `A ∪ C` is the complement of the zero section of `B × ℝ^p` (identified
with `B × (ℝ^p × ℝ^0)`). -/
theorem tcmA_union_tcmC_zero (p : ℕ) :
    tcmA B p 0 ∪ tcmC B p 0 = {x : tcmX B p 0 | x.2 ≠ 0} := by
  ext x
  constructor
  · rintro (hx | hx)
    · intro h
      exact hx (congrArg Prod.fst h)
    · intro h
      exact hx (congrArg Prod.snd h)
  · intro hx
    left
    intro h
    exact hx (Prod.ext h (Subsingleton.elim _ _))

/-- **The pair condition of `tcmF`**: the closed set `A ∪ C` is exactly the preimage of the punctured
part under the identification `tcmF` — this is what makes `tcmF` a map of pairs and hence an
isomorphism on the relative groups (the input of the reduction to a point). -/
theorem tcmF_preimage_punct (p q : ℕ) :
    (tcmF B p q) ⁻¹' Punct B (p + q) = tcmA B p q ∪ tcmC B p q := by
  ext x
  simp only [Set.mem_preimage, tcmF, ContinuousMap.coe_mk, Punct, tcmA, tcmC, Set.mem_union,
    Set.mem_setOf_eq]
  constructor
  · intro hx
    by_contra h
    push_neg at h
    have h0 : x.2 = 0 := Prod.ext h.1 h.2
    rw [h0] at hx
    exact hx (map_zero (tcmSumLin p q))
  · rintro (h1 | h2)
    · intro h0
      have h0' : x.2 = 0 :=
        (tcmSumLin p q).injective (h0.trans (map_zero (tcmSumLin p q)).symm)
      exact h1 (congrArg Prod.fst h0')
    · intro h0
      have h0' : x.2 = 0 :=
        (tcmSumLin p q).injective (h0.trans (map_zero (tcmSumLin p q)).symm)
      exact h2 (congrArg Prod.snd h0')

/-- **`tcmF` is a homeomorphism**: it is the product of the identity on the base with the linear
homeomorphism `tcmSumLin : ℝ^p × ℝ^q ≃L[ℝ] ℝ^{p+q}`. -/
noncomputable def tcmFHomeo (p q : ℕ) :
    tcmX B p q ≃ₜ (B × EuclideanSpace ℝ (Fin (p + q))) where
  toFun := tcmF B p q
  invFun y := (y.1, (tcmSumLin p q).symm y.2)
  left_inv x := by
    show (x.1, (tcmSumLin p q).symm (tcmSumLin p q x.2)) = x
    rw [(tcmSumLin p q).symm_apply_apply]
  right_inv y := by
    show (y.1, tcmSumLin p q ((tcmSumLin p q).symm y.2)) = y
    rw [(tcmSumLin p q).apply_symm_apply]
  continuous_toFun := (tcmF B p q).continuous
  continuous_invFun := continuous_fst.prodMk
    ((tcmSumLin p q).symm.continuous.comp continuous_snd)

/-- The pair condition of `tcmF`, in the form a map of pairs needs:
`x ∈ A ∪ C ↔ tcmF x ∈ Punct`. -/
theorem tcmF_pair (p q : ℕ) (x : tcmX B p q) :
    x ∈ tcmA B p q ∪ tcmC B p q ↔ (tcmFHomeo p q) x ∈ Punct B (p + q) := by
  have h := tcmF_preimage_punct (B := B) p q
  show x ∈ tcmA B p q ∪ tcmC B p q ↔ (tcmF B p q) x ∈ Punct B (p + q)
  rw [← h]
  exact Iff.rfl

/-- **`tcmF` induces an isomorphism on relative cohomology** — the relative class of
`(tcmX, A ∪ C)` is determined by, and determines, its image in `H^n(B × ℝ^{p+q}, Punct B (p+q))`.
This is the transport along which the reduction to a point is performed. -/
theorem bijective_relCohMap_tcmF (p q n : ℕ) :
    Function.Bijective ((relCohMap (tcmF B p q) (tcmA B p q ∪ tcmC B p q)
      (Punct B (p + q)) (tcmF_mem B p q) ℤ n).hom) := by
  rw [relCohMap_hcongrA (tcmF B p q) (tcmA B p q ∪ tcmC B p q) (Punct B (p + q))
    (tcmF_mem B p q) (fun x hx => (tcmF_pair p q x).mp hx) ℤ n]
  exact bijective_relCohMap_of_homeomorphA (tcmA B p q ∪ tcmC B p q) (Punct B (p + q))
    (tcmFHomeo p q) (tcmF_pair p q) ℤ n

/-! ## The boundary corner: the two ingredients

The cases `p = 0` / `q = 0` of `tcmModelMul` reduce to (i) the characterisation of `Mpun 0` as the
*unit* class of `H^0` and (ii) the unit law of the relative–relative cup: cupping with a degree-zero
class whose absolute image is `1`, over a closed set `C` contained in `A`, is the identity on
`H^m(X,A)`.  (The remaining bookkeeping in the corner is that `tcmC B p 0 = ∅` is a *set equality*,
so a class of `H^m(X, A ∪ tcmC B p 0)` has to be transported along `A ∪ ∅ = A` — see
`_tcm/REDUCTION.md`.) -/

/-- **`Mpun 0` is the unit class**: the model class of rank `0` is the class of `H^0` whose absolute
image is `1` (it is `Mn 0`, whose characterising equation `Work.Thom.Mn_zero_spec` says exactly
this, and for `Punct B 0 = Sph B 0 = ∅` the two restriction maps agree). -/
theorem relToAbs_Mpun_zero (B : Type) [TopologicalSpace B] :
    (relToAbs ℤ (Punct B 0) 0).hom (Mpun 0 B)
      = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of (B × EuclideanSpace ℝ (Fin 0)))) := by
  have hnat := relCohMap_relToAbs (ContinuousMap.id (B × EuclideanSpace ℝ (Fin 0)))
    (Sph B 0) (Punct B 0) (mem_Sph_punct B 0) ℤ 0
  have h := congrArg (fun φ => φ (Mpun 0 B)) hnat
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  simp only [CohMap_id, ModuleCat.hom_id, LinearMap.id_apply] at h
  rw [Mpun_spec 0 B] at h
  simpa [Work.Thom.oneSphZero] using h.symm.trans (Mn_zero_spec B)

-- The unit law of the relative--relative cup, `Work.Whitney.tcmRelCup_unit_right`, is proved in
-- `Submission/Work/Whitney/tcmRelCup_unit_right.lean` (with its auxiliary modules
-- `Work.Whitney.Unit.Pre` / `Work.Whitney.Unit.Lemmas`) and imported above; it is the second
-- ingredient of the boundary corner below.

/-! ## The `Y = ∅` corner of the point case

`Subsingleton Y` allows the empty base.  The point case there is vacuous (both sides lie in the
relative cohomology of an empty space, which is a subsingleton), so the point case for
`[Subsingleton Y]` follows from its `[Nonempty Y]` instance.  This is the refinement the two
reviewers of `Whitney/tcmModelMul_point_subsingleton` suggested, and it lets the point case be
proved with `[Nonempty Y]`. -/

/-- **The relative cohomology of an empty space is a subsingleton**: there are no simplices, so the
complex is trivial. -/
theorem subsingleton_relCoh_of_isEmpty {X : Type} [TopologicalSpace X] [IsEmpty X]
    (A : Set X) (n : ℕ) : Subsingleton (RelCoh ℤ n X A) := by
  haveI : IsEmpty ↥(TopCat.of X) := ‹IsEmpty X›
  haveI : IsEmpty ↥A := ⟨fun a => isEmptyElim (a : X)⟩
  haveI : IsIso (Work.Cohomology.relIncl ℤ (TopCat.of X) A) :=
    Work.Cohomology.isIso_relIncl_of_isEmpty _ _
  have h0 : IsZero ((Work.Cohomology.singularCochainComplex ℤ (TopCat.of X)).homology n) :=
    Work.Cohomology.isZero_homology_of_isZero_X_cochain n
      (Work.Cohomology.isZero_singularCochainComplex_of_isEmpty (TopCat.of X) n)
  exact ModuleCat.subsingleton_of_isZero
    (IsZero.of_iso h0 (asIso (HomologicalComplex.homologyMap (Work.Cohomology.relIncl ℤ
      (TopCat.of X) A) n)))

/-! ## THE POINT CASE AND THE MODEL PRODUCT FORMULA: NOT STATED HERE -- SEE THE WARNING

**WARNING (do not reprove the unsigned statement; it is FALSE).**  The two statements this module
used to carry,

* `tcmModelMul_point_subsingleton` (the point case), and
* `tcmModelMul` (the general model product formula
  `tcmRelCup (pr1^* Mpun p) (pr2^* Mpun q) = tcmF^*(Mpun (p+q))`),

are **false as written**, off by the Koszul sign `(-1)^{p*q}`:

  `tcmRelCup (pr1^* Mpun p) (pr2^* Mpun q) = ((-1 : Z) ^ (p * q)) • tcmF^*(Mpun (p+q))`.

The corrected statements, with the sign, are in

* `Submission/Work/Whitney/tcmModelMul_point_signed.lean` (`Work.Whitney.tcmModelMul_point_signed`),
* `Submission/Work/Whitney/tcmModelMul_signed_of_point.lean`
  (`Work.Whitney.tcmModelMul_signed_of_point`, the reduction to the point case),
* `Submission/Work/Whitney/tcmModelMul_signed.lean` (`Work.Whitney.tcmModelMul_signed`),

and the **even** instance `p = 2*m1`, `q = 2*m2` -- the one the top-class theorem needs -- is
*sign-free* (`(-1)^{4*m1*m2} = 1`): `Work.Whitney.tcmModelMul_even`.

Why the sign is there, and why the corrected statement is the true one:

* the *proved* unit law `Work.Whitney.tcmRelCup_unit_right` gives the value `+1` for `q = 0`, so the
  ratio `eps(p,q)` of the two sides of the model formula satisfies `eps(p,0) = 1`;
* the *proved* graded Leibniz rule `Work.Thom.suspensionStep_cup'`
  (`delta (x cup z) = (-1)^{|x|} • (x cup delta z)`) together with the recursion
  `Mpun (n+1) = Pstep n (Mpun n)` (`Work.Thom.Mpun_spec`, `Work.Thom.step`) forces the recursion
  `eps(p,q+1) = (-1)^p * eps(p,q)`, hence `eps(p,q) = (-1)^{p*q}`;
* the explicit computation at `(p,q) = (1,1)` over a point gives `-1`
  (`Submission/Work/Whitney/_cupSign/NOTES.md`, `Submission/Work/Whitney/_o/NOTES_sign_11.md`),
  i.e. `eps(1,1) = -1`, in agreement with the pattern.

The sign is an artefact of the workspace's *orientation convention* for the cap map inside
`Work.Thom.step` (`capMap n w = (w, sqrt (1 - ‖w‖^2))` traverses the upper hemisphere clockwise),
not of the mathematics: for the even ranks `2m` of realified complex bundles the model class is the
classical one up to the multiplicative sign `eps(2m) = (-1)^m`, which is why the top Chern class
identity of `Work.Whitney.chernClass_whitneySum_top` is unaffected by it.

The rest of this module is unaffected and remains valid: the homeomorphism `tcmFHomeo`, the pair
condition `tcmF_preimage_punct` / `tcmF_pair`, the relative-cohomology transport
`bijective_relCohMap_tcmF`, the unit computation `relToAbs_Mpun_zero`, the boundary facts
`tcmA_zero`, `tcmC_zero`, `tcmA_union_tcmC_zero`, and the empty-space triviality
`subsingleton_relCoh_of_isEmpty`.
-/

end

end Work.Whitney
