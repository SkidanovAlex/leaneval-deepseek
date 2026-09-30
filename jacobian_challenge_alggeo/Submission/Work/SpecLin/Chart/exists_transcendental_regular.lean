import Mathlib
import Submission.Work.SpecLin.Chart.Regular
import Submission.Work.CurveBasics.All
import Submission.Work.CurveBasics.exists_separating_element
import Submission.Work.SpecLin.Chart.ordAt_aeval_nonneg
import Submission.Work.SpecLin.Chart.ordAt_aeval_neg

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option linter.style.haveILetI false

namespace Work.SpecLin.Chart

open CategoryTheory Limits AlgebraicGeometry
open Work.CurveBasics
open Polynomial

/-! ## The `K`-algebra structure on the local ring of a curve at a point

Mathlib does not register the `K`-algebra structure on the stalk `𝒪_{C,z}` of a curve `C` over `K`.
It is the composite `K ⟶ Γ(Spec K) ⟶ Γ(C, ⊤) ⟶ 𝒪_{C,z}` of the structure morphism and the
germ map at `z`.  With this structure the structure map `𝒪_{C,z} → κ(z)` to the residue field is
`K`-linear, which is what relates evaluation at a place to polynomial evaluation. -/

private noncomputable instance instAlgebraStalk {K : Type*} [Field K] (C : Curve K) (z : C.left) :
    Algebra K (C.left.presheaf.stalk z) :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ C.hom.appTop ≫
    C.left.presheaf.germ (⊤ : C.left.Opens) z (show z ∈ (⊤ : C.left.Opens) from trivial)).hom.toAlgebra

/-- The canonical map `K → κ(z)` coincides with the composite `K → 𝒪_{C,z} → κ(z)`. -/
private theorem residue_algebraMap {K : Type*} [Field K] (C : Curve K) (Q : C.Place) (c : K) :
    C.left.residue Q.point (algebraMap K (C.left.presheaf.stalk Q.point) c)
      = algebraMap K (C.left.residueField Q.point) c := by
  have hz : Q.point ∈ (⊤ : C.left.Opens) := show _ ∈ _ from trivial
  have h1 : algebraMap K (C.left.presheaf.stalk Q.point) c =
      C.left.presheaf.germ (⊤ : C.left.Opens) Q.point hz
        (C.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c)) := by
    rw [RingHom.algebraMap_toAlgebra]; rfl
  rw [h1]
  change C.left.Γevaluation Q.point (C.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c)) = _
  rw [RingHom.algebraMap_toAlgebra]
  rw [← Scheme.Γevaluation_naturality_apply (f := C.hom) Q.point]
  rfl

/-- Evaluation at a place, as a `K`-algebra homomorphism on the local ring. -/
private noncomputable def residueAlg {K : Type*} [Field K] (C : Curve K) (Q : C.Place) :
    C.left.presheaf.stalk Q.point →ₐ[K] C.left.residueField Q.point where
  toRingHom := (C.left.residue Q.point).hom
  commutes' := residue_algebraMap C Q

/-- The scalar tower `K ⟶ 𝒪_{C,z} ⟶ K(C)`. -/
private theorem instScalarTower {K : Type*} [Field K] (C : Curve K) (z : C.left) :
    IsScalarTower K (C.left.presheaf.stalk z) C.functionField := by
  refine IsScalarTower.of_algebraMap_eq fun c => ?_
  have h1 : algebraMap K (C.left.presheaf.stalk z) c =
      C.left.presheaf.germ (⊤ : C.left.Opens) z (show z ∈ (⊤ : C.left.Opens) from trivial)
        (C.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c)) := by
    rw [RingHom.algebraMap_toAlgebra]; rfl
  rw [h1]
  rw [Scheme.algebraMap_germ_eq_germToFunctionField]
  rfl

/-- **A polynomial vanishing at a place where `x₀` is regular.**

If `x₀` is regular at `Q`, then some nonzero polynomial in `x₀` vanishes at `Q`: the value of
`x₀` at `Q` is an element of the finite-dimensional `K`-algebra `κ(Q)`, hence algebraic. -/
private theorem exists_poly_pos_ord {K : Type*} [Field K] (C : Curve K) (Q : C.Place)
    {x₀ : C.functionField} (hx₀ : Transcendental K x₀) (hQ : 0 ≤ C.ordAt x₀ Q) :
    ∃ p : Polynomial K, p ≠ 0 ∧ 0 < C.ordAt (aeval x₀ p) Q := by
  letI hκ := Curve.Place.instAlgebraResidueField C Q.point
  letI := instAlgebraStalk C Q.point
  haveI hST := instScalarTower C Q.point
  haveI hdvr : IsDiscreteValuationRing (C.left.presheaf.stalk Q.point) :=
    Curve.Place.instIsDiscreteValuationRing Q
  obtain ⟨a₀, ha₀⟩ := (BaseChange.mem_range_algebraMap_stalk_iff C Q x₀).mpr hQ
  have hdeg : Q.degree = Module.finrank K (C.left.residueField Q.point) := Place.degree_eq_finrank Q
  haveI hfin : Module.Finite K (C.left.residueField Q.point) := by
    by_contra h
    have h0 : Module.finrank K (C.left.residueField Q.point) = 0 := Module.finrank_of_not_finite h
    exact absurd (by rw [hdeg, h0] : Q.degree = 0) (ne_of_gt (Place.residueDegree_pos Q))
  haveI halg : Algebra.IsAlgebraic K (C.left.residueField Q.point) :=
    Algebra.IsAlgebraic.of_finite K _
  obtain ⟨p, hp, hp0⟩ := Algebra.IsAlgebraic.isAlgebraic (R := K) (residueAlg C Q a₀)
  refine ⟨p, hp, ?_⟩
  have h1 : residueAlg C Q (aeval a₀ p) = 0 := by
    rw [← Polynomial.aeval_algHom_apply (residueAlg C Q) a₀ p]
    exact hp0
  have hmem : aeval a₀ p ∈ IsLocalRing.maximalIdeal (C.left.presheaf.stalk Q.point) := by
    have := IsLocalRing.residue_eq_zero_iff (aeval a₀ p)
    exact this.mp h1
  have haeval : aeval x₀ p
      = algebraMap (C.left.presheaf.stalk Q.point) C.functionField (aeval a₀ p) := by
    rw [← ha₀]
    exact Polynomial.aeval_algebraMap_apply C.functionField a₀ p
  have hbne : aeval a₀ p ≠ 0 := by
    intro hb
    have : aeval x₀ p = 0 := by rw [haeval, hb, map_zero]
    exact absurd (transcendental_iff.mp hx₀ p this) hp
  rw [haeval]
  rw [show C.ordAt (algebraMap (C.left.presheaf.stalk Q.point) C.functionField (aeval a₀ p)) Q
      = -(Q.valuation (algebraMap (C.left.presheaf.stalk Q.point) C.functionField (aeval a₀ p))).log
      from Curve.Place.ord_eq_neg_log_valuation C Q _]
  have hv : Q.valuation (algebraMap (C.left.presheaf.stalk Q.point) C.functionField (aeval a₀ p)) < 1 := by
    exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem
      (IsDiscreteValuationRing.maximalIdeal (C.left.presheaf.stalk Q.point)) (aeval a₀ p)).mpr hmem
  have hne : Q.valuation (algebraMap (C.left.presheaf.stalk Q.point) C.functionField (aeval a₀ p)) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact fun h => hbne (IsFractionRing.injective (C.left.presheaf.stalk Q.point) C.functionField
      (by simpa using h))
  have : (Q.valuation (algebraMap (C.left.presheaf.stalk Q.point) C.functionField (aeval a₀ p))).log < 0 := by
    rw [WithZero.log_lt_iff_lt_exp hne, WithZero.exp_zero]
    exact hv
  linarith

/-! ## Elementary properties of the order of vanishing -/

private lemma ordAt_neg {K : Type*} [Field K] (C : Curve K) (Q : C.Place) (f : C.functionField) :
    C.ordAt (-f) Q = C.ordAt f Q := by
  change Scheme.ord (-f) Q.point = Scheme.ord f Q.point
  rcases eq_or_ne f 0 with hf | hf
  · rw [hf, neg_zero]
  · rw [show -f = (-1 : C.functionField) * f by ring,
      Scheme.ord_mul (x := Q.point) (by norm_num : (-1 : C.functionField) ≠ 0) hf]
    have h1 : Scheme.ord (-1 : C.functionField) Q.point = 0 := by
      change C.ordAt (-1 : C.functionField) Q = 0
      have h0 := Order.ordAt_algebraMap_eq_zero C (-1 : K) Q
      have h2 : algebraMap K C.functionField (-1 : K) = (-1 : C.functionField) := by
        rw [map_neg, map_one]
      rwa [h2] at h0
    rw [h1, zero_add]

private lemma ordAt_one {K : Type*} [Field K] (C : Curve K) (Q : C.Place) :
    C.ordAt (1 : C.functionField) Q = 0 := by
  change Scheme.ord (1 : C.functionField) Q.point = 0
  have := Order.ordAt_algebraMap_eq_zero C (1 : K) Q
  rwa [map_one] at this

/-- The order of a sum is the smaller of the two orders when these differ. -/
private lemma ordAt_add_of_lt {K : Type*} [Field K] (C : Curve K) (Q : C.Place)
    {f g : C.functionField} (h : C.ordAt f Q < C.ordAt g Q) (hf : f ≠ 0) :
    C.ordAt (f + g) Q = C.ordAt f Q := by
  change Scheme.ord (f + g) Q.point = Scheme.ord f Q.point
  change Scheme.ord f Q.point < Scheme.ord g Q.point at h
  haveI : IsDiscreteValuationRing (C.left.presheaf.stalk Q.point) :=
    Curve.Place.instIsDiscreteValuationRing Q
  have hfgn : f + g ≠ 0 := by
    intro hc
    have hgf : g = -f := by linear_combination hc
    have hneg : Scheme.ord (-f) Q.point = Scheme.ord f Q.point := ordAt_neg C Q f
    rw [hgf, hneg] at h
    exact lt_irrefl _ h
  have h1 : Scheme.ord f Q.point ≤ Scheme.ord (f + g) Q.point := by
    have := Scheme.ord_add (x := Q.point) hfgn
    rwa [min_eq_left h.le] at this
  have h2 : Scheme.ord (f + g) Q.point ≤ Scheme.ord f Q.point := by
    have hne : (f + g) + (-g) ≠ 0 := by simpa using hf
    have hold := Scheme.ord_add (x := Q.point) hne
    rw [add_neg_cancel_right] at hold
    have hneg : Scheme.ord (-g) Q.point = Scheme.ord g Q.point := ordAt_neg C Q g
    rw [hneg] at hold
    by_contra hgt
    rw [not_le] at hgt
    exact absurd (lt_of_lt_of_le (lt_min hgt h) hold) (lt_irrefl _)
  exact le_antisymm h2 h1

private lemma ordAt_inv {K : Type*} [Field K] (C : Curve K) (Q : C.Place) {f : C.functionField}
    (hf : f ≠ 0) : C.ordAt f⁻¹ Q = -C.ordAt f Q := by
  have h1 : C.ordAt (f * f⁻¹) Q = C.ordAt f Q + C.ordAt f⁻¹ Q :=
    Scheme.ord_mul hf (inv_ne_zero hf)
  rw [mul_inv_cancel₀ hf, ordAt_one] at h1
  linarith

private lemma ordAt_prod {K : Type*} [Field K] (C : Curve K) (Q : C.Place) {ι : Type*}
    (s : Finset ι) (g : ι → C.functionField) (hg : ∀ i ∈ s, g i ≠ 0) :
    C.ordAt (∏ i ∈ s, g i) Q = ∑ i ∈ s, C.ordAt (g i) Q := by
  classical
  induction s using Finset.induction with
  | empty => simp [ordAt_one]
  | insert a s ha ih =>
      have hga : g a ≠ 0 := hg a (Finset.mem_insert_self a s)
      have hgs : ∏ i ∈ s, g i ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun i hi => hg i (Finset.mem_insert_of_mem hi))
      have key : C.ordAt (g a * ∏ i ∈ s, g i) Q
          = C.ordAt (g a) Q + C.ordAt (∏ i ∈ s, g i) Q := by
        change Scheme.ord (g a * ∏ i ∈ s, g i) Q.point
          = Scheme.ord (g a) Q.point + Scheme.ord (∏ i ∈ s, g i) Q.point
        exact Scheme.ord_mul (x := Q.point) hga hgs
      rw [Finset.prod_insert ha, Finset.sum_insert ha, key]
      rw [ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))]

/-! ## Transcendentality -/

/-- A nonconstant polynomial in a transcendental element is transcendental. -/
private lemma transcendental_aeval {K : Type*} [Field K] (C : Curve K)
    {x₀ : C.functionField} (hx₀ : Transcendental K x₀) {g : Polynomial K} (hg : g ≠ 0)
    (hgd : g.natDegree ≠ 0) : Transcendental K (aeval x₀ g) :=
  (transcendental_aeval_iff).mpr
    ⟨hx₀, Polynomial.transcendental g hgd
      (mem_nonZeroDivisors_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hg))⟩

/-- Adding a constant to a transcendental element keeps it transcendental. -/
private lemma transcendental_add_one {K : Type*} [Field K] (C : Curve K) {y : C.functionField}
    (hy : Transcendental K y) : Transcendental K (y + 1) := by
  have h : Transcendental K (aeval y (Polynomial.X + Polynomial.C (1 : K))) :=
    (transcendental_aeval_iff).mpr
      ⟨hy, Polynomial.transcendental _
        (by rw [Polynomial.natDegree_X_add_C]; exact one_ne_zero)
        (by rw [Polynomial.leadingCoeff_X_add_C]
            exact mem_nonZeroDivisors_iff_ne_zero.mpr one_ne_zero)⟩
  simpa using h

/-- The inverse of a transcendental element is transcendental. -/
private lemma transcendental_inv {K : Type*} [Field K] (C : Curve K) {y : C.functionField}
    (hy : Transcendental K y) : Transcendental K y⁻¹ :=
  fun halg => hy ((IsAlgebraic.inv_iff (K := C.functionField)).mp halg)

/-- **A transcendental function regular on a prescribed finite set of points.**

For a finite set `S` of points of a curve `C` there is a rational function `x : K(C)`,
transcendental over `K`, which is regular at every point of `S` (i.e. `S` is contained in
`Work.SpecLin.Chart.regularOpens C x`).  Only the closed points of `S` matter (the generic
point lies in every nonempty open and every rational function is regular there).

Suggested route (no Riemann-Roch needed).

Take a separating element `x₀ : K(C)` (`Work.CurveBasics.exists_separating_element`: `x₀` is
transcendental and `K(C)/K(x₀)` is finite).  Let `S' = {Q : C.Place | Q.point ∈ S}` be the
places over `S` at which `x₀` is regular (`0 ≤ C.ordAt x₀ Q`); this set is finite.

If `S'` is empty then `x := x₀⁻¹` is transcendental and, at every `Q` with `Q.point ∈ S`,
`x₀` has a pole so `C.ordAt x₀⁻¹ Q > 0 ≥ 0` is regular.

Otherwise let `I ⊆ K[X]` be the ideal of polynomials `h` with `0 < C.ordAt (aeval x₀ h) Q`
for **all** `Q ∈ S'`.  This is an ideal of the polynomial ring (for `g, g' ∈ I` use the
ultrametric inequality `ord (a+b) ≥ min (ord a) (ord b)`; for the `K[X]`-action use that
`x₀` is regular at each `Q ∈ S'`, so `ord (h(x₀)) Q ≥ 0`).  Its nonvanishing is the
mathematical content: `I = ker (K[X] → ∏_{Q ∈ S'} κ(Q))` where the `Q`-th component is
`h ↦ (h(x₀))(Q) ∈ κ(Q)`, an ideal whose target is finite dimensional over `K` (each residue
field `κ(Q)` is finite over `K`: `Work.CurveBasics.Place.degree_eq_finrank` together with
`Work.CurveBasics.Place.residueDegree_pos`; `K[X]` is infinite dimensional over `K`), so `I`
contains a nonzero element by dimension reasons.  (Equivalently, each `κ(Q)` contains the
image of `K[x₀] ≅ K[X]`, so the kernel must be nonzero since `trdeg_K κ(Q) = 0 < 1`.)

Pick `0 ≠ j ∈ I` (necessarily nonconstant, since `I` contains only polynomials vanishing at
the places of `S'`, and `S' ≠ ∅`), and set `x := (j(x₀) + 1)⁻¹ = (aeval x₀ j + 1)⁻¹`.

- `x` is transcendental: `j(x₀)` is transcendental (a nonconstant polynomial evaluated at the
  transcendental `x₀`), hence so is `x` (inverse of a rational function, or use that
  `j(x₀) + 1` is transcendental).
- `x` is regular on `S`: for `Q ∈ S'`, `j(x₀)` vanishes at `Q` (order `> 0`), so
  `j(x₀) + 1` equals `1` at `Q` and `C.ordAt (j(x₀)+1) Q = 0`, hence `C.ordAt x Q = 0 ≥ 0`;
  for a place `Q` over `S` at which `x₀` has a pole, `j(x₀) + 1` (as a nonconstant
  polynomial in `x₀`) again has a pole, so `x` has a zero, i.e. `C.ordAt x Q > 0`; the
  generic point of `S` is in every nonempty open, so `S ⊆ regularOpens C x`. -/
theorem exists_transcendental_regular {K : Type*} [Field K] (C : Work.CurveBasics.Curve K)
    (S : Set C.left) (hS : S.Finite) :
    ∃ x : C.functionField, Transcendental K x ∧
      S ⊆ (Work.SpecLin.Chart.regularOpens C x : Set C.left) := by
  classical
  obtain ⟨x₀, hx₀, -⟩ := Work.CurveBasics.exists_separating_element C
  have hx₀_ne : x₀ ≠ 0 := hx₀.ne_zero
  -- the places of `S` at which `x₀` is regular
  let S' : Set C.Place := {Q | Q.point ∈ S ∧ 0 ≤ C.ordAt x₀ Q}
  have hS'fin : S'.Finite :=
    (hS.preimage (f := fun Q : C.Place => Q.point)
      (fun a _ b _ h => Subtype.ext h)).subset (fun Q hQ => hQ.1)
  let T : Finset C.Place := hS'fin.toFinset
  have hT : ∀ Q : C.Place, Q ∈ T ↔ Q.point ∈ S ∧ 0 ≤ C.ordAt x₀ Q :=
    fun Q => hS'fin.mem_toFinset
  -- a polynomial vanishing at every place of `S'`
  let f : C.Place → Polynomial K := fun Q =>
    if h : Q ∈ T then (exists_poly_pos_ord C Q hx₀ ((hT Q).mp h).2).choose else 0
  have hf : ∀ Q ∈ T, f Q ≠ 0 ∧ 0 < C.ordAt (aeval x₀ (f Q)) Q := by
    intro Q hQ
    have := (exists_poly_pos_ord C Q hx₀ ((hT Q).mp hQ).2).choose_spec
    simpa only [f, dite_eq_left hQ] using this
  -- multiply by `X` so that `j` is visibly nonconstant
  set j : Polynomial K := Polynomial.X * ∏ Q ∈ T, f Q with hjdef
  have hj₀ : (∏ Q ∈ T, f Q) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun Q hQ => (hf Q hQ).1)
  have hj : j ≠ 0 := by
    rw [hjdef]; exact mul_ne_zero Polynomial.X_ne_zero hj₀
  have hjd : j.natDegree ≠ 0 := by
    rw [hjdef, natDegree_mul Polynomial.X_ne_zero hj₀, natDegree_X]
    omega
  have haevalY : aeval x₀ (∏ Q ∈ T, f Q) ≠ 0 :=
    fun h => hj₀ ((transcendental_iff.mp hx₀) _ h)
  have htrans : Transcendental K (aeval x₀ j + 1) :=
    transcendental_add_one C (transcendental_aeval C hx₀ hj hjd)
  refine ⟨(aeval x₀ j + 1)⁻¹, transcendental_inv C htrans, ?_⟩
  intro z hz
  refine (mem_regularOpens C ((aeval x₀ j + 1)⁻¹)).mpr ?_
  intro Q hQ
  rw [ordAt_inv C Q htrans.ne_zero]
  by_cases hcase : 0 ≤ C.ordAt x₀ Q
  · -- `x₀` is regular at `Q`: `j(x₀)` vanishes there and `j(x₀) + 1` is a unit
    have hQT : Q ∈ T := (hT Q).mpr ⟨by rw [hQ]; exact hz, hcase⟩
    have hmul : C.ordAt (aeval x₀ j) Q
        = C.ordAt x₀ Q + C.ordAt (aeval x₀ (∏ Q' ∈ T, f Q')) Q := by
      rw [hjdef, map_mul, aeval_X]
      exact Scheme.ord_mul (x := Q.point) hx₀_ne haevalY
    have hsum : C.ordAt (aeval x₀ (∏ Q' ∈ T, f Q')) Q
        = ∑ Q' ∈ T, C.ordAt (aeval x₀ (f Q')) Q := by
      rw [map_prod]
      exact ordAt_prod C Q T (fun Q' => aeval x₀ (f Q'))
        (fun Q' hQ' h => (hf Q' hQ').1 ((transcendental_iff.mp hx₀) _ h))
    have hpos : 0 < C.ordAt (aeval x₀ j) Q := by
      have hbdd : C.ordAt (aeval x₀ (f Q)) Q
          ≤ ∑ Q' ∈ T, C.ordAt (aeval x₀ (f Q')) Q :=
        Finset.single_le_sum (fun Q' _ => ordAt_aeval_nonneg C Q hcase (f Q')) hQT
      rw [hmul, hsum]
      linarith [(hf Q hQT).2, hcase]
    have hzero : C.ordAt (aeval x₀ j + 1) Q = 0 := by
      rw [add_comm]
      rw [ordAt_add_of_lt C Q (f := (1 : C.functionField)) (g := aeval x₀ j)
        (by rw [ordAt_one]; exact hpos) one_ne_zero, ordAt_one]
    rw [hzero]
    norm_num
  · -- `x₀` has a pole at `Q`: so does `j(x₀) + 1`, hence `x` has a zero there
    have hneg : C.ordAt x₀ Q < 0 := not_le.mp hcase
    have hnegf : C.ordAt (aeval x₀ j) Q < 0 := ordAt_aeval_neg C Q hneg hj hjd
    have hfne : aeval x₀ j ≠ 0 := by
      intro h
      rw [h] at hnegf
      change Scheme.ord (0 : C.functionField) Q.point < 0 at hnegf
      simp at hnegf
    have hlt : C.ordAt (aeval x₀ j + 1) Q < 0 := by
      have h1' : C.ordAt (aeval x₀ j) Q < C.ordAt (1 : C.functionField) Q := by
        rw [ordAt_one]; exact hnegf
      rw [ordAt_add_of_lt C Q h1' hfne]
      exact hnegf
    linarith

end Work.SpecLin.Chart
