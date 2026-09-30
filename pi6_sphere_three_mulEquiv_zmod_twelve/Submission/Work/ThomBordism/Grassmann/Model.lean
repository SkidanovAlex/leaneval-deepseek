import Submission.Work.ThomBordism.Grassmann.Grassmannian
import Submission.Work.ThomBordism.Grassmann.GrassmannianTopology
import Submission.Work.ThomBordism.Grassmann.Oriented
import Submission.Work.ThomBordism.Grassmann.Linear
import Submission.Work.ThomBordism.Grassmann.Coord
import Submission.Work.Thom.ThomClass
import Submission.Work.Thom.manifoldP1
import Submission.Work.SignatureBordism.Rationalisation


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The universal model: the Thom space of the tautological bundle, and the cohomology statements

This module collects the **model** that the rest of the project uses, on top of the geometric
definitions of `Submission/Work/ThomBordism/Grassmann/Grassmannian.lean`:

* `G̃r_k(ℝ^{k+m}) = Work.ThomBordism.Grassmann.OG k m`, a compact Hausdorff space, with the
  tautological oriented rank-`k` bundle `Work.ThomBordism.Grassmann.tautologicalBundle k m` (the
  orientation-consistent gluing data of `Submission/Work/ThomBordism/Grassmann/Oriented.lean`,
  a `VectorBundleCore` over the finite cover `ChartIdx k m` with fibre `EuclideanSpace ℝ (Fin k)`);
* the **Thom space** `T = Th(γ) = Work.ThomBordism.Grassmann.TautologicalThomSpace k m` with its
  basepoint `thomBasepoint`, and (proved) a **Thom class** `tautologicalThomClass k m` together with
  the Thom isomorphism `tautologicalThomEquiv k m n`;
* the Pontryagin classes `p₁(γ)`, `p₂(γ)` (as `Work.Thom.pontryaginClass` of the tautological
  bundle) and the rational cohomology classes `p1Rat`, `p2Rat`, `p1SqRat`;
* the **statements** the project needs, as `Prop`s: the low-degree rational cohomology of `G`
  (`LowDegreeCohomology`), the rational cohomology of the Thom pair in the stable range
  (`ThomPairCohomology`, *proved* to follow from the former: `thomPairCohomology_of_lowDegree`), and
  the `(k-1)`-connectivity of the Thom space in the form used by
  `Submission/Work/Drive/RationalHurewicz.lean` (`ThomSpaceConnected`).  Item 1 of the chapter —
  the Thom class — is a *theorem* (`hasTautologicalThomClass`), so the model is
  `UniversalModel k m` as soon as the two remaining classical inputs are available
  (`universalModel_of`).  See `README.md` for the exact status of every statement and for the
  sibling bridge `Submission/Work/ThomBordism/Grassmann/ThomTarget.lean`.
-/

namespace Work.ThomBordism.Grassmann

open scoped Topology TensorProduct
open CategoryTheory

noncomputable section

variable {k m : ℕ}

/-- The singular simplicial set of a topological space, in the form used by the cohomology chapter. -/
abbrev sset (X : Type) [TopologicalSpace X] : SSet := TopCat.toSSet.obj (TopCat.of X)

/-! ## The Thom space of the tautological bundle -/

/-- **The Thom space `T = Th(γ)`** of the tautological oriented rank-`k` bundle over
`G̃r_k(ℝ^{k+m})`.

**Model choice (metric-free).**  `T` is the *one-point compactification* of the total space of `γ`
(`OnePoint`, Mathlib).  For a rank-`k` oriented bundle over a **compact** base — and `OG k m` is
compact, `instCompactSpaceOG` — this *is* the Thom space `D(γ)/S(γ)`, but no metric on the fibres is
needed to say so.  This matters: the disc-bundle model `Work.Thom.ThomSpace` defines `D(γ)` by the
*fibre norm in the chart `indexAt`*, which is chart-dependent unless the gluing data are
`Work.Thom.IsEuclidean`, and the tautological bundle's transitions (`A_T A_S⁻¹`, gauged by the sign
matrix) are **not** orthogonal.  For the metric-free model the pair `(γ.TotalSpace, zeroComplement)`
used by `Work.Thom.ThomClass`/`OpenThom` — which this chapter's Thom class is about — is exactly
right, and the comparison with the cohomology of `T` is
`H̃^n(T) ≅ H^n(T, {∞}) ≅ H^n(T, E∖0 ∪ {∞}) ≅ H^n(E, E∖0)` (fibrewise scaling `v ↦ t⁻¹v` deforms
`E∖0 ∪ {∞}` to `∞`).  Consumers that map *into* `T` (the collapse map of the tubular-neighbourhood
chapter) should use this model. -/
abbrev TautologicalThomSpace (k m : ℕ) : Type := OnePoint (tautologicalBundle k m).TotalSpace

/-- **The basepoint of the Thom space**: the point at infinity of the one-point compactification
(which is the image of the whole "sphere at infinity" under the collapse). -/
def thomBasepoint (k m : ℕ) : TautologicalThomSpace k m := OnePoint.infty

/-- **The Thom isomorphism theorem for the universal oriented bundle**: the tautological bundle
over the oriented Grassmannian carries a Thom class `U ∈ H^k(D γ, S γ; ℤ)` making the Thom map
`x ↦ π^*(x) ⌣ U` an isomorphism in every degree.  This is the orientability-plus-excision input;
everything else in this chapter is stated relative to a `U`. -/
def HasTautologicalThomClass (k m : ℕ) : Prop :=
  Nonempty (Work.Thom.ThomClass (tautologicalBundle k m) k)

/-! ## The Pontryagin classes of the tautological bundle -/

/-- `p₁(γ)`, the first Pontryagin class of the tautological bundle, as an integral class
`H⁴(G;ℤ)`. -/
def p1 (k m : ℕ) : (Work.Cohomology.cochainC ℤ (sset (OG k m))).homology 4 :=
  Work.Thom.pontryaginClass 1 (tautologicalBundle k m)

/-- `p₂(γ)`, the second Pontryagin class of the tautological bundle, as an integral class
`H⁸(G;ℤ)`. -/
def p2 (k m : ℕ) : (Work.Cohomology.cochainC ℤ (sset (OG k m))).homology 8 :=
  Work.Thom.pontryaginClass 2 (tautologicalBundle k m)

/-- `p₁(γ)²`, the square of the first Pontryagin class, in `H⁸(G;ℤ)`. -/
def p1Sq (k m : ℕ) : (Work.Cohomology.cochainC ℤ (sset (OG k m))).homology 8 :=
  Work.Cohomology.cupH' ℤ (sset (OG k m)) 4 4 (p1 k m) (p1 k m)

/-- The rationalised first Pontryagin class `1 ⊗ p₁(γ) ∈ H⁴(G;ℚ)`. -/
def p1Rat (k m : ℕ) : Work.SignatureBordism.ratCohomology 4 (sset (OG k m)) := (1 : ℚ) ⊗ₜ[ℤ] p1 k m

/-- The rationalised second Pontryagin class `1 ⊗ p₂(γ) ∈ H⁸(G;ℚ)`. -/
def p2Rat (k m : ℕ) : Work.SignatureBordism.ratCohomology 8 (sset (OG k m)) := (1 : ℚ) ⊗ₜ[ℤ] p2 k m

/-- The rationalised square `1 ⊗ p₁(γ)² ∈ H⁸(G;ℚ)`. -/
def p1SqRat (k m : ℕ) : Work.SignatureBordism.ratCohomology 8 (sset (OG k m)) := (1 : ℚ) ⊗ₜ[ℤ] p1Sq k m

/-! ## The statements -/

/-- The low degrees in which the rational cohomology of the oriented Grassmannian (with `k, m ≥ 10`)
vanishes: 1, 2, 3, 5, 6, 7. -/
def lowDegrees : Finset ℕ := {1, 2, 3, 5, 6, 7}

/-- **The rational cohomology of the oriented Grassmannian in low degrees.**

The statement is conditioned on `k ≥ 10` and `m ≥ 10` (outside that range the low-degree
computation is genuinely different: for `k = 1`, `G̃r_1(ℝ^{1+m}) = ℝP^m` has `H^4 = 0` and `p1(γ)` is
torsion, so the statement below is false without the hypotheses).

For `k ≥ 10` and `m ≥ 10`: `H^j(G;Q) = 0` for `j ∈ {1,2,3,5,6,7}`, `H^4(G;Q) = Q · p1(γ)`, and
`H^8(G;Q) = Q · p1(γ)^2 ⊕ Q · p2(γ)`, where `p1`, `p2` are the Pontryagin classes of the
tautological bundle.

The classical proof is by induction on `k` and `m` using the Gysin sequences of the sphere bundles
`S(γ_k) → G̃r_k` (`Work.Thom.GysinSequence`), or by Schubert cells; the linear independence of
`p1(γ)^2` and `p2(γ)` is checked by pulling back along classifying maps to `ℂP⁴`. -/
def LowDegreeCohomology (k m : ℕ) : Prop :=
  10 ≤ k → 10 ≤ m →
    (∀ j ∈ lowDegrees,
        Subsingleton (Work.SignatureBordism.ratCohomology j (sset (OG k m)))) ∧
      (Function.Bijective fun a : ℚ => a • p1Rat k m) ∧
      (Function.Bijective fun p : ℚ × ℚ => p.1 • p1SqRat k m + p.2 • p2Rat k m)

/-- The class `c ⌣ U` of the Thom pair of the tautological bundle, rationalised: the Thom map
`x ↦ π^*(x) ⌣ U` applied to a class `c` of `G`. -/
noncomputable def thomCupU (k m n : ℕ)
    (c : (Work.Cohomology.cochainC ℤ (sset (OG k m))).homology n)
    (U : Work.Thom.ThomClass (tautologicalBundle k m) k) :
    ℚ ⊗[ℤ] Work.Thom.OpenThom (tautologicalBundle k m) (n + k) :=
  (1 : ℚ) ⊗ₜ[ℤ] (Work.Thom.thomMap (tautologicalBundle k m) k U.τ n c)

/-- The map `(a,b) ↦ a · (p1(γ)^2 ⌣ U) + b · (p2(γ) ⌣ U)`. -/
noncomputable def thomBasisMap (k m : ℕ)
    (U : Work.Thom.ThomClass (tautologicalBundle k m) k) :
    ℚ × ℚ → ℚ ⊗[ℤ] Work.Thom.OpenThom (tautologicalBundle k m) (8 + k) :=
  fun p => p.1 • thomCupU k m 8 (p1Sq k m) U + p.2 • thomCupU k m 8 (p2 k m) U

/-- **The rational cohomology of the Thom pair of the tautological bundle.**

Again conditioned on `k ≥ 10` and `m ≥ 10` (see `LowDegreeCohomology`).

Given a Thom class `U` of the tautological bundle (so the Thom isomorphism of
`Work.Thom.ThomClass.isThom` holds by definition), the rational relative cohomology
`H^{k+j}(D γ, S γ; Q)` vanishes for `j ∈ {1,2,3,5,6,7}` and in degree `k+8` the classes
`p1(γ)^2 ⌣ U` and `p2(γ) ⌣ U` form a basis.

By the Thom isomorphism this is equivalent to `LowDegreeCohomology`. -/
def ThomPairCohomology (k m : ℕ) : Prop :=
  10 ≤ k → 10 ≤ m →
    ∀ U : Work.Thom.ThomClass (tautologicalBundle k m) k,
      (∀ j ∈ lowDegrees,
          Subsingleton (ℚ ⊗[ℤ] Work.Thom.OpenThom (tautologicalBundle k m) (k + j))) ∧
        Function.Bijective (fun a : ℚ => a • thomCupU k m 4 (p1 k m) U) ∧
        Function.Bijective (thomBasisMap k m U)

/-- **The `(k-1)`-connectivity of the Thom space of the tautological bundle.**

Every `π_i(T, x_0)` with `i < k` is trivial, where `T = Th(γ)` is the Thom space of the
tautological bundle and `x_0` its basepoint.  This is the form required by
`Submission/Work/Drive/RationalHurewicz.lean` (`Work.Drive.RationalHurewiczStable`).

The proof is the classical one: `D(γ) → G` is a `k`-disc bundle and `S(γ) → G` a
`(k-1)`-sphere bundle, so `π_i(D γ, S γ) = 0` for `i ≤ k-1`, and `T = D γ / S γ` is the cofibre. -/
def ThomSpaceConnected (k m : ℕ) : Prop :=
  ∀ i : ℕ, i < k →
    Subsingleton (HomotopyGroup (Fin i) (TautologicalThomSpace k m) (thomBasepoint k m))

/-! ## What is *proved* about the model

The vanishing of the relative cohomology of the Thom pair **below the rank** is available in the
workspace for every real vector bundle of rank `n` (`Work.Thom.subsingleton_OpenThom_of_lt_rank`),
and hence holds for the tautological bundle.  This is the cohomological shadow of the
`(k-1)`-connectivity of the Thom space and, combined with the Thom isomorphism, gives the vanishing
half of `ThomPairCohomology` in the stable range. -/

/-- **The relative cohomology of the Thom pair of the tautological bundle vanishes below the
rank.**

This is *proved* in the workspace for every real vector bundle of rank `n` in
`Submission/Work/Thom/subsingleton_OpenThom_of_lt_rank.lean`
(`Work.Thom.subsingleton_OpenThom_of_lt_rank`, valid for **any** gluing data, in particular for
`tautologicalBundle k m`); it cannot be *stated* in this module because that file belongs to an
import island that clashes with `Work.Thom.ThomClass` (see the README).  It is the cohomological

set_option synthInstance.maxHeartbeats 400000
shadow of the `(k-1)`-connectivity of the Thom space and, combined with the Thom isomorphism, gives
the vanishing half of `ThomPairCohomology` in the stable range. -/
def OpenThomVanishesBelowRank (k m : ℕ) : Prop :=
  ∀ j : ℕ, j < k → Subsingleton (Work.Thom.OpenThom (tautologicalBundle k m) j)

/-- **The low-degree datum** of the oriented Grassmannian, extracted from
`LowDegreeCohomology`. -/
theorem subsingleton_ratCohomology_of_lowDegree (h : LowDegreeCohomology k m)
    (hk : 10 ≤ k) (hm : 10 ≤ m) {j : ℕ} (hj : j ∈ lowDegrees) :
    Subsingleton (Work.SignatureBordism.ratCohomology j (sset (OG k m))) :=
  (h hk hm).1 j hj

/-- **The Thom isomorphism, rationalised: the vanishing half of `ThomPairCohomology`.**

If the rational cohomology of `G` vanishes in degree `j`, then so does the rational relative
cohomology of the Thom pair `(D γ, S γ)` in degree `k + j`: by definition of a Thom class
(`Work.Thom.ThomClass.isThom`) the Thom map `x ↦ π^*(x) ⌣ U` is a `ℤ`-linear *isomorphism*
`H^j(G;ℤ) ≅ H^{k+j}(D γ, S γ;ℤ)`, and tensoring an isomorphism with `ℚ` is an isomorphism.

This is the proof of the "hence, by the Thom isomorphism" half of `ThomPairCohomology`; the
statement about the *basis* `p₁² ⌣ U, p₂ ⌣ U` is not reduced here (it would require the
`ℤ`-freeness of the relative cohomology of the Thom pair, i.e. that it has no torsion). -/
theorem subsingleton_tensor_openThom_of_lowDegree
    (U : Work.Thom.ThomClass (tautologicalBundle k m) k) {j : ℕ}
    (h : Subsingleton (Work.SignatureBordism.ratCohomology j (sset (OG k m)))) :
    Subsingleton (ℚ ⊗[ℤ] Work.Thom.OpenThom (tautologicalBundle k m) (k + j)) := by
  have h1 : Subsingleton (ℚ ⊗[ℤ] Work.Thom.OpenThom (tautologicalBundle k m) (j + k)) := by
    have e : ℚ ⊗[ℤ] (Work.Thom.Coh ℤ j (OG k m)) ≃ₗ[ℤ]
        ℚ ⊗[ℤ] Work.Thom.OpenThom (tautologicalBundle k m) (j + k) :=
      TensorProduct.congr (LinearEquiv.refl ℤ ℚ) (U.thomEquiv j)
    haveI : Subsingleton (ℚ ⊗[ℤ] (Work.Thom.Coh ℤ j (OG k m))) := h
    refine Subsingleton.intro (fun a b => ?_)
    obtain ⟨x, rfl⟩ := e.surjective a
    obtain ⟨y, rfl⟩ := e.surjective b
    rw [Subsingleton.elim x y]
  rwa [show k + j = j + k from Nat.add_comm k j]

/-- **The vanishing half of `ThomPairCohomology` follows from the low-degree cohomology of `G`.**

This is the form in which the cohomological half of Thom's theorem is consumed: the
low-degree rational cohomology of the oriented Grassmannian, transported along the Thom
isomorphism of the universal Thom class. -/
theorem thomPairCohomology_vanishing_of_lowDegree (h : LowDegreeCohomology k m)
    (hk : 10 ≤ k) (hm : 10 ≤ m) (U : Work.Thom.ThomClass (tautologicalBundle k m) k) :
    ∀ j ∈ lowDegrees,
      Subsingleton (ℚ ⊗[ℤ] Work.Thom.OpenThom (tautologicalBundle k m) (k + j)) :=
  fun j hj => subsingleton_tensor_openThom_of_lowDegree U
    (subsingleton_ratCohomology_of_lowDegree h hk hm hj)

/-- The basepoint is irrelevant for the connectivity statement when the Thom space is connected, but
the statement for `k = 0` is vacuous in any case. -/
theorem thomSpaceConnected_zero (m : ℕ) : ThomSpaceConnected 0 m := fun i hi => absurd hi (Nat.not_lt_zero i)

/-- **The universal model**, as a single `Prop`. -/
def UniversalModel (k m : ℕ) : Prop :=
  HasTautologicalThomClass k m ∧ LowDegreeCohomology k m ∧ ThomPairCohomology k m ∧
    ThomSpaceConnected k m




/-- **The Thom isomorphism theorem for the tautological oriented bundle, proved.**

The tautological oriented bundle over `G̃r_k(ℝ^{k+m})` carries an integral Thom class: for `k ≥ 1`
this is `Oriented.nonempty_thomClass_tautologicalBundleO` (the orientation-consistent gluing data
has positive transition determinants, so `Work.Thom.thomClass_of_oriented_fintype` applies), and for
`k = 0` a rank-zero bundle carries a Thom class for trivial reasons.  Hence
`HasTautologicalThomClass` is a *theorem*, and `UniversalModel` is reduced to the two cohomological
statements and the connectivity: item 1 of the chapter is now a theorem in *all* degrees. -/
theorem hasTautologicalThomClass (k m : ℕ) : HasTautologicalThomClass k m := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    exact nonempty_thomClass_zero_of_subsingleton (tautologicalBundle 0 m)
  · exact nonempty_thomClass_tautologicalBundleO hk

/-- **A chosen Thom class `U` of the tautological oriented bundle** — the Thom isomorphism theorem
`hasTautologicalThomClass`, extracted.  Every statement about the universal bundle is stated
relative to a Thom class anyway, and this is the canonical one. -/
noncomputable def tautologicalThomClass (k m : ℕ) :
    Work.Thom.ThomClass (tautologicalBundle k m) k :=
  Classical.choice (hasTautologicalThomClass k m)

/-- **The Thom isomorphism of the tautological bundle**, in the form used throughout: cupping with
the Thom class, `H^n(G;ℤ) ≃ H^{n+k}(D γ, S γ;ℤ)`. -/
noncomputable def tautologicalThomEquiv (k m n : ℕ) :
    Work.Thom.Coh ℤ n (OG k m) ≃ₗ[ℤ]
      Work.Thom.OpenThom (tautologicalBundle k m) (n + k) :=
  (tautologicalThomClass k m).thomEquiv n

/-! ## The basis half of `ThomPairCohomology`: the Thom isomorphism in degree `8`

The Thom isomorphism is `x ↦ π^*(x) ⌣ U`.  Rationalised, it is a `ℤ`-linear equivalence

`thomRatEquiv : ℚ ⊗ H⁸(G;ℤ) ≃ ℚ ⊗ H^{k+8}(D γ, S γ;ℤ)`,

and the map `thomBasisMap` of the Thom pair is its composite with
`Φ : (a,b) ↦ a · p₁(γ)² + b · p₂(γ)`.  Hence the *basis* statement for the Thom pair is
*equivalent* to the basis statement for `G`, and no freeness hypothesis on the relative cohomology
is needed: this is the "hence, by the Thom isomorphism" clause of the deliverable, reduced to the
low-degree cohomology of the Grassmannian.
-/

/-- **The `ℚ`-scalar action on `ℚ ⊗[ℤ] M` on a pure tensor with `1` in the first factor.** -/
theorem ratTensor_smul_one_tmul {M : Type*} [AddCommGroup M] (q : ℚ) (x : M) :
    (q ⊗ₜ[ℤ] x : ℚ ⊗[ℤ] M) = q • ((1 : ℚ) ⊗ₜ[ℤ] x) := by
  rw [TensorProduct.smul_tmul']
  simp

/-- **The rationalised Thom isomorphism in degree `n`**, as a `ℤ`-linear equivalence
`ℚ ⊗ H^n(G;ℤ) ≃ ℚ ⊗ H^{n+k}(D γ, S γ;ℤ)`. -/
noncomputable def thomRatEquiv (k m n : ℕ) (U : Work.Thom.ThomClass (tautologicalBundle k m) k) :
    ℚ ⊗[ℤ] (Work.Cohomology.cochainC ℤ (sset (OG k m))).homology n ≃ₗ[ℤ]
      ℚ ⊗[ℤ] Work.Thom.OpenThom (tautologicalBundle k m) (n + k) :=
  TensorProduct.congr (LinearEquiv.refl ℤ ℚ) (U.thomEquiv n)

/-- `thomRatEquiv` on a pure tensor. -/
theorem thomRatEquiv_tmul (k m n : ℕ) (U : Work.Thom.ThomClass (tautologicalBundle k m) k)
    (q : ℚ) (x : (Work.Cohomology.cochainC ℤ (sset (OG k m))).homology n) :
    thomRatEquiv k m n U (q ⊗ₜ[ℤ] x) = q ⊗ₜ[ℤ] (U.thomEquiv n x) := by
  rw [thomRatEquiv, TensorProduct.congr_tmul]
  rfl


/-- **`thomRatEquiv` is `ℚ`-linear** (it is defined as a `ℤ`-linear equivalence, but both sides are
`ℚ`-modules and on pure tensors it is `q ⊗ x ↦ q ⊗ (U.thomEquiv x)`). -/
theorem thomRatEquiv_smul (k m n : ℕ) (U : Work.Thom.ThomClass (tautologicalBundle k m) k) (q : ℚ)
    (z : ℚ ⊗[ℤ] (Work.Cohomology.cochainC ℤ (sset (OG k m))).homology n) :
    thomRatEquiv k m n U (q • z) = q • thomRatEquiv k m n U z := by
  rw [thomRatEquiv]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
      rw [TensorProduct.smul_tmul', TensorProduct.congr_tmul, TensorProduct.congr_tmul]
      rfl
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- **The degree-`4` part of `ThomPairCohomology`: `a ↦ a · (p₁(γ) ⌣ U)` is the Thom isomorphism
applied to `a ↦ a · p₁(γ)`.** -/
theorem thomDegree4_eq (k m : ℕ) (U : Work.Thom.ThomClass (tautologicalBundle k m) k) (a : ℚ) :
    a • thomCupU k m 4 (p1 k m) U = thomRatEquiv k m 4 U (a • p1Rat k m) := by
  have h1 : thomRatEquiv k m 4 U (p1Rat k m) = thomCupU k m 4 (p1 k m) U := by
    rw [p1Rat, thomCupU, thomRatEquiv_tmul, Work.Thom.ThomClass.thomEquiv_apply]
  rw [← h1, ← thomRatEquiv_smul]

/-- **The degree-`4` half of `ThomPairCohomology`, from the degree-`4` half of
`LowDegreeCohomology`.** -/
theorem bijective_thomDegree4_of_lowDegree (k m : ℕ)
    (U : Work.Thom.ThomClass (tautologicalBundle k m) k)
    (hb : Function.Bijective fun a : ℚ => a • p1Rat k m) :
    Function.Bijective (fun a : ℚ => a • thomCupU k m 4 (p1 k m) U) := by
  have hEq : (fun a : ℚ => a • thomCupU k m 4 (p1 k m) U)
      = fun a : ℚ => thomRatEquiv k m 4 U (a • p1Rat k m) :=
    funext (thomDegree4_eq k m U)
  rw [hEq]
  exact (thomRatEquiv k m 4 U).bijective.comp hb

/-- **`thomBasisMap` is the Thom isomorphism applied to `Φ`**, i.e. the Thom map carries the
low-degree cohomology of `G` (spanned by `p₁²` and `p₂`) onto the degree-`(k+8)` cohomology of the
Thom pair. -/
theorem thomBasisMap_eq (k m : ℕ) (U : Work.Thom.ThomClass (tautologicalBundle k m) k)
    (p : ℚ × ℚ) :
    thomBasisMap k m U p = thomRatEquiv k m 8 U (p.1 • p1SqRat k m + p.2 • p2Rat k m) := by
  have h1 : thomRatEquiv k m 8 U (p1SqRat k m) = thomCupU k m 8 (p1Sq k m) U := by
    rw [p1SqRat, thomCupU, thomRatEquiv_tmul, Work.Thom.ThomClass.thomEquiv_apply]
  have h2 : thomRatEquiv k m 8 U (p2Rat k m) = thomCupU k m 8 (p2 k m) U := by
    rw [p2Rat, thomCupU, thomRatEquiv_tmul, Work.Thom.ThomClass.thomEquiv_apply]
  rw [thomBasisMap, map_add, thomRatEquiv_smul, thomRatEquiv_smul, h1, h2]

/-- **The basis half of `ThomPairCohomology` in degree `8`, from the basis half of
`LowDegreeCohomology`.** -/
theorem bijective_thomBasisMap_of_lowDegree (k m : ℕ)
    (U : Work.Thom.ThomClass (tautologicalBundle k m) k)
    (hb : Function.Bijective fun p : ℚ × ℚ => p.1 • p1SqRat k m + p.2 • p2Rat k m) :
    Function.Bijective (thomBasisMap k m U) := by
  have hEq : thomBasisMap k m U
      = fun p : ℚ × ℚ => thomRatEquiv k m 8 U (p.1 • p1SqRat k m + p.2 • p2Rat k m) :=
    funext (thomBasisMap_eq k m U)
  rw [hEq]
  exact (thomRatEquiv k m 8 U).bijective.comp hb

/-- **`ThomPairCohomology` follows from `LowDegreeCohomology`** (all three parts): the low-degree
cohomology of the oriented Grassmannian transported along the Thom isomorphism of the tautological
bundle.  This is the cohomological half of Thom's theorem in the form the project consumes:
`H^{k+j}(D γ,S γ;ℚ) = 0` for `j ∈ {1,2,3,5,6,7}`, `H^{k+4}(D γ,S γ;ℚ) = ℚ·(p₁(γ) ⌣ U)` and
`H^{k+8}(D γ,S γ;ℚ) = ℚ·(p₁(γ)² ⌣ U) ⊕ ℚ·(p₂(γ) ⌣ U)`. -/
theorem thomPairCohomology_of_lowDegree (h : LowDegreeCohomology k m) (hk : 10 ≤ k) (hm : 10 ≤ m) :
    ThomPairCohomology k m := by
  intro _ _ U
  exact ⟨thomPairCohomology_vanishing_of_lowDegree h hk hm U,
    bijective_thomDegree4_of_lowDegree k m U (h hk hm).2.1,
    bijective_thomBasisMap_of_lowDegree k m U (h hk hm).2.2⟩

/-- **The universal model from the two cohomological statements and the connectivity**: item 1
(`HasTautologicalThomClass`) is a theorem (`hasTautologicalThomClass`), item 2 in its two forms is
`LowDegreeCohomology`/`ThomPairCohomology` (the second following from the first,
`thomPairCohomology_of_lowDegree`), and item 3 is `ThomSpaceConnected`. -/
theorem universalModel_of (h : LowDegreeCohomology k m) (hk : 10 ≤ k) (hm : 10 ≤ m)
    (hconn : ThomSpaceConnected k m) : UniversalModel k m :=
  ⟨hasTautologicalThomClass k m, h, thomPairCohomology_of_lowDegree h hk hm, hconn⟩

end

end Work.ThomBordism.Grassmann