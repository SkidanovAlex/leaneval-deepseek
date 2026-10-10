import Mathlib
import Submission.Work.MotV.H1Data
import Submission.Work.MotV.Machinery
import Submission.Work.MotV.ordPlaceCommon
import Submission.Work.MotC2.Negation
import Submission.Work.MotC2.Classification
import Submission.Work.MotC2.AffPlaceSetup
import Submission.Work.MotC2.IsRatPlaceMap
import Submission.Work.MotV.map_negAlgEquiv_affPlaceAt
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV

/-! ## Helpers for `ordSumNeg`

The two facts below are the only new inputs: the quadratic `quad E c` (whose roots are the
`y`-coordinates of the fibre of `x = c`) is invariant under the negation `d ↦ negY E c d`, and the
places of the fibre `x = c` are exactly the `affPlaceAt E c d` with `d` a root of `quad E c`.

They live in a private namespace because this module is imported by `Submission/Work/MotV/fibreNorm`
(and hence by `sumA`), so the plain names are already used downstream. -/
namespace OrdSumNegAux

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

/-! ### Transporting the order of vanishing along an isomorphism of discrete valuation rings -/

section Transport

variable {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]

/-- A ring isomorphism between discrete valuation rings preserves the additive valuation. -/
lemma addVal_ringEquiv (e : R ≃+* S) (x : R) :
    IsDiscreteValuationRing.addVal S (e x) = IsDiscreteValuationRing.addVal R x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, IsDiscreteValuationRing.addVal_zero, IsDiscreteValuationRing.addVal_zero]
  · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
    have hirr : Irreducible (e ϖ) := by
      have h := (MulEquiv.irreducible_iff e.toMulEquiv).mpr hϖ
      simpa using h
    rw [IsDiscreteValuationRing.addVal_def ((u : R) * ϖ ^ n) u hϖ n rfl,
      IsDiscreteValuationRing.addVal_def (e ((u : R) * ϖ ^ n))
        ((Units.map (e : R →* S)) u) hirr n (by
          simp only [map_mul, map_pow, Units.coe_map]
          rfl)]

/-- `avNat` (the `ℕ`-valued order on a discrete valuation ring) is preserved by ring
isomorphisms. -/
lemma avNat_ringEquiv (e : R ≃+* S) (x : R) : avNat (e x) = avNat x := by
  rw [avNat_def, avNat_def, addVal_ringEquiv e x]

end Transport

variable {N : Type*} [Field N]

/-- The order of vanishing at a rational place is invariant under an automorphism of the function
field, the place being transported along the automorphism. -/
lemma ordOfPlace_map_aux (E : WeierstrassCurve N)
    (τ : MotC2.Func E ≃ₐ[N] MotC2.Func E) (S : Subalgebra N (MotC2.Func E))
    (hS : MotC2.IsRatPlace E S) (hS' : MotC2.IsRatPlace E (Subalgebra.map τ.toAlgHom S))
    (f : MotC2.Func E) :
    ordOfPlace E (Subalgebra.map τ.toAlgHom S) hS' (τ f) = ordOfPlace E S hS f := by
  classical
  haveI : IsDiscreteValuationRing ↥S := hS.1.choose
  haveI : IsDiscreteValuationRing ↥(S.map τ.toAlgHom) := hS'.1.choose
  let e : ↥S ≃+* ↥(S.map τ.toAlgHom) :=
    (Subalgebra.equivMapOfInjective S τ.toAlgHom τ.injective).toRingEquiv
  have hval : ∀ x : ↥S,
      ((e x : ↥(S.map τ.toAlgHom)) : MotC2.Func E) = τ (x : MotC2.Func E) := fun x => rfl
  have hmem : ∀ x : MotC2.Func E, x ∈ S ↔ τ x ∈ S.map τ.toAlgHom := by
    intro x
    constructor
    · intro hx
      exact Subalgebra.mem_map.mpr ⟨x, hx, rfl⟩
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subalgebra.mem_map.mp hx
      rwa [τ.injective hyx] at hy
  have havNat : ∀ x : ↥S, avNat (e x) = avNat x := fun x => avNat_ringEquiv e x
  rw [ordOfPlace_eq_ordPlace E (S.map τ.toAlgHom) hS' (τ f),
    ordOfPlace_eq_ordPlace E S hS f]
  by_cases hf : f ∈ S
  · have hτf : τ f ∈ S.map τ.toAlgHom := (hmem f).mp hf
    rw [ordPlace_eq_of_mem E (S.map τ.toAlgHom) hS' (τ f) hτf,
      ordPlace_eq_of_mem E S hS f hf]
    have hx : (⟨τ f, hτf⟩ : ↥(S.map τ.toAlgHom)) = e ⟨f, hf⟩ := Subtype.ext (hval ⟨f, hf⟩)
    rw [hx, havNat]
  · have hτf : τ f ∉ S.map τ.toAlgHom := fun h => hf ((hmem f).mpr h)
    rw [ordPlace_eq_of_notMem E (S.map τ.toAlgHom) hS' (τ f) hτf,
      ordPlace_eq_of_notMem E S hS f hf]
    have hx : (⟨(τ f)⁻¹, inv_mem_of_notMem hS' hτf⟩ : ↥(S.map τ.toAlgHom))
        = e ⟨f⁻¹, inv_mem_of_notMem hS hf⟩ := by
      refine Subtype.ext ?_
      rw [hval]
      exact (map_inv₀ τ.toAlgHom f).symm
    rw [hx, havNat]

/-- Evaluation of `quad E c` at `d`. -/
lemma quad_eval_eq (E : WeierstrassCurve N) (c d : N) :
    (quad E c).eval d = d ^ 2 + (E.a₁ * c + E.a₃) * d -
      (c ^ 3 + E.a₂ * c ^ 2 + E.a₄ * c + E.a₆) := by
  simp only [quad, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]

/-- The roots of `quad E c` are the `y`-coordinates of the affine points of `E` above `x = c`. -/
lemma quad_eval_eq_zero_iff (E : WeierstrassCurve N) (c d : N) :
    (quad E c).eval d = 0 ↔ Equation E c d := by
  rw [quad_eval_eq, equation_iff]
  constructor <;> intro h <;> linear_combination h

/-- `quad E c` is a nonzero (indeed monic) quadratic. -/
lemma quad_ne_zero (E : WeierstrassCurve N) (c : N) : quad E c ≠ 0 := by
  have hdeg : (Polynomial.C (E.a₁ * c + E.a₃) * Polynomial.X -
      Polynomial.C (c ^ 3 + E.a₂ * c ^ 2 + E.a₄ * c + E.a₆)).degree < (2 : WithBot ℕ) := by
    rw [sub_eq_add_neg, ← Polynomial.C_neg]
    refine lt_of_le_of_lt Polynomial.degree_linear_le ?_
    norm_num
  have hmonic : (quad E c).Monic := by
    rw [quad, add_sub_assoc]
    exact Polynomial.monic_X_pow_add hdeg
  exact hmonic.ne_zero

/-- The negation conjugates the quadratic `quad E c` over the fibre `x = c`: the `y`-coordinate
`negY E c d = -d - a₁c - a₃` of `-(c,d)` is a root of `quad E c` exactly when `d` is. -/
lemma quad_eval_negY (E : WeierstrassCurve N) (c d : N) :
    (quad E c).eval (WeierstrassCurve.Affine.negY E c d) = (quad E c).eval d := by
  simp only [quad, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, WeierstrassCurve.Affine.negY]
  first | refl_ring1 | ring

/-- The rational places of the fibre of `x = c` are the affine places `affPlaceAt E c d` with
`d` a root of `quad E c`. -/
lemma mem_fibrePlaces_iff (E : WeierstrassCurve N) [E.IsElliptic] (c : N) (Q : Place N E) :
    Q ∈ fibrePlaces E c ↔
      ∃ d : N, (quad E c).eval d = 0 ∧ Q.1 = MotC2.affPlaceAt E c d := by
  classical
  have hquad := quad_ne_zero E c
  rw [fibrePlaces]
  simp only [Finset.mem_biUnion, Multiset.mem_toFinset]
  constructor
  · rintro ⟨d, hd, hQ⟩
    have hd0 : (quad E c).eval d = 0 := (Polynomial.mem_roots' (p := quad E c)).mp hd |>.2
    rw [dif_pos ((quad_eval_eq_zero_iff E c d).mp hd0), Finset.mem_singleton] at hQ
    exact ⟨d, hd0, by rw [hQ]⟩
  · rintro ⟨d, hd, hQ⟩
    refine ⟨d, (Polynomial.mem_roots' (p := quad E c)).mpr ⟨hquad, ?_⟩, ?_⟩
    · exact Polynomial.IsRoot.def.mpr hd
    · rw [dif_pos ((quad_eval_eq_zero_iff E c d).mp hd), Finset.mem_singleton]
      exact Subtype.ext hQ

end OrdSumNegAux

-- imports: Mathlib, Submission.Work.MotV.H1Data, Submission.Work.MotV.Machinery, Submission.Work.MotC2.Negation, Submission.Work.MotC2.Classification, Submission.Work.MotC2.AffPlaceSetup, Submission.Work.MotC2.IsRatPlaceMap
/-- The negation `[-1]` of the elliptic curve permutes the points of the fibre of `x = c`, so it does
not change the sum of the orders of a function over that fibre.

Route.  (1) For any rational place `S` and any `N`-algebra automorphism `τ` of `N(E)` one has
`ordOfPlace E (S.map τ) (τ f) = ordOfPlace E S f`: transport `IsRatPlace` along `τ`
(`MotC2.IsRatPlaceMap`, or a direct instance), then compare the `IsDiscreteValuationRing.addVal`s
of the ring isomorphism `Subalgebra.equivMapOfInjective` using
`IsDiscreteValuationRing.addVal_le_iff_dvd` (divisibility is preserved) and the fact that
`IsDiscreteValuationRing` is a `Prop` (so the value does not depend on the proof of `IsRatPlace`).
(2) `τ := MotC2.negAlgEquiv E` fixes `genX` (`MotC2.negAlgEquiv_genX`) and maps `affPlaceAt E c d`
onto `affPlaceAt E c (-d - a₁c - a₃)`: on the coordinate ring the negation sends `x - c` to `x - c`
and `y - d` to the negative of `y - (-d - a₁c - a₃)` modulo `(x - c)`
(`MotC2.negCoordAlgEquiv_coordX`, `MotC2.negCoordAlgEquiv_coordY`,
`AffPlaceSetup.affPlaceAt_maximalIdeal_eq`); conclude with `AffPlaceSetup.affPlaceAt_mem_iff` and
`MotC2.DVRMaximal` (or directly with the maximal-ideal description).
(3) `d ↦ -d - a₁c - a₃` is an involution of `(quad E c).roots.toFinset`, because
`(quad E c).eval (-d - a₁c - a₃) = (quad E c).eval d` (`Polynomial.mem_roots`, `Polynomial.IsRoot`,
`Multiset.mem_toFinset`; expand the substitution, it conjugates the quadratic).
(4) Rewrite `ordSum` on both sides as a sum over `(quad E c).roots.toFinset` (unfold
`fibrePlaces E c`; see `MotV/ordSumPoly` for this enumeration), reindex the sum along the involution
of (3) (`Finset.sum_bij` or `Finset.sum_equiv`) and apply (1) at the corresponding places. -/
theorem ordSumNeg {N : Type*} [Field N] [IsAlgClosed N] [DecidableEq N]
    (E : WeierstrassCurve N) [E.IsElliptic] (H : Work.MotV.H1Data N E)
    (f : Work.MotC2.Func E) (c : N) :
    Work.MotV.ordSum E (Work.MotV.fibrePlaces E c) (Work.MotC2.negAlgEquiv E f)
      = Work.MotV.ordSum E (Work.MotV.fibrePlaces E c) f := by
  classical
  -- the negation is an involution of `N(E)`
  have hcomp : (MotC2.negAlgEquiv E).toAlgHom.comp (MotC2.negAlgEquiv E).toAlgHom
      = AlgHom.id N (MotC2.Func E) := by
    apply AlgHom.ext
    intro x
    have h := AlgEquiv.congr_fun (MotC2.negAlgEquiv_mul_self E) x
    simpa [AlgEquiv.mul_apply] using h
  -- the induced map on the rational places
  let σ : Place N E → Place N E := fun Q =>
    ⟨Q.1.map (MotC2.negAlgEquiv E).toAlgHom,
      MotC2.IsRatPlaceMap N E (MotC2.negAlgEquiv E) Q.1 Q.2⟩
  have hσ_val : ∀ Q : Place N E,
      (σ Q).1 = (Q.1).map (MotC2.negAlgEquiv E).toAlgHom := fun Q => rfl
  -- `σ` permutes the places of the fibre `x = c`
  have hσF : ∀ Q ∈ fibrePlaces E c, σ Q ∈ fibrePlaces E c := by
    intro Q hQ
    rw [OrdSumNegAux.mem_fibrePlaces_iff] at hQ ⊢
    obtain ⟨d, hd, hQd⟩ := hQ
    refine ⟨WeierstrassCurve.Affine.negY E c d, ?_, ?_⟩
    · rw [OrdSumNegAux.quad_eval_negY]; exact hd
    · rw [hσ_val, hQd]; exact map_negAlgEquiv_affPlaceAt E c d
  -- `σ` is an involution
  have hσσ : ∀ Q : Place N E, σ (σ Q) = Q := by
    intro Q
    refine Subtype.ext ?_
    show ((σ Q).1).map (MotC2.negAlgEquiv E).toAlgHom = Q.1
    rw [hσ_val, Subalgebra.map_map, hcomp, Subalgebra.map_id]
  have himage : (fibrePlaces E c).image σ = fibrePlaces E c := by
    refine Finset.Subset.antisymm ?_ ?_
    · exact Finset.image_subset_iff.mpr hσF
    · intro Q hQ
      exact Finset.mem_image.mpr ⟨σ Q, hσF Q hQ, hσσ Q⟩
  have hσinj : Set.InjOn σ ↑(fibrePlaces E c) := by
    intro a _ b _ hab
    have h1 : (σ a).1 = (σ b).1 := congrArg Subtype.val hab
    rw [hσ_val, hσ_val] at h1
    exact Subtype.ext (Subalgebra.map_injective
      (f := (MotC2.negAlgEquiv E).toAlgHom)
      (fun x y h => (MotC2.negAlgEquiv E).injective h) h1)
  -- the order at the place `σ Q` of the negated function is the order at `Q` of the function
  have hord : ∀ Q : Place N E,
      ordP E (σ Q) (MotC2.negAlgEquiv E f) = ordP E Q f :=
    fun Q => OrdSumNegAux.ordOfPlace_map_aux E (MotC2.negAlgEquiv E) Q.1 Q.2 ((σ Q).2) f
  have key1 : ∑ Q ∈ fibrePlaces E c, ordP E Q (MotC2.negAlgEquiv E f)
      = ∑ Q ∈ (fibrePlaces E c).image σ, ordP E Q (MotC2.negAlgEquiv E f) := by rw [himage]
  have key2 : ∑ Q ∈ (fibrePlaces E c).image σ, ordP E Q (MotC2.negAlgEquiv E f)
      = ∑ Q ∈ fibrePlaces E c, ordP E (σ Q) (MotC2.negAlgEquiv E f) :=
    Finset.sum_image (f := fun Q => ordP E Q (MotC2.negAlgEquiv E f)) (s := fibrePlaces E c)
      (g := σ) hσinj
  have key3 : ∑ Q ∈ fibrePlaces E c, ordP E (σ Q) (MotC2.negAlgEquiv E f)
      = ∑ Q ∈ fibrePlaces E c, ordP E Q f :=
    Finset.sum_congr rfl fun Q _ => hord Q
  simp only [ordSum]
  exact key1.trans (key2.trans key3)

end Work.MotV
