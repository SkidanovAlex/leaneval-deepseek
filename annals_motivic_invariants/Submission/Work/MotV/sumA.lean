import Mathlib
import Submission.Work.MotV.H1Data
import Submission.Work.MotV.Machinery
import Submission.Work.MotC2.Negation
import Submission.Work.MotC2.AffPlace
import Submission.Work.MotC2.AffPlaceSetup
import Submission.Work.MotV.ordPlaceCommon
import Submission.Work.MotV.normEqNeg
import Submission.Work.MotV.affOrd_eq_zero_of_notMem
import Submission.Work.MotV.map_negAlgEquiv_affPlaceAt
import Submission.Work.MotC2.IsRatPlaceMap
import Submission.Work.MotV.ordSumPoly
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero
namespace Work.MotV

noncomputable section

variable {N : Type*} [Field N]

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

lemma quad_eval_eq (E : WeierstrassCurve N) (c d : N) :
    (quad E c).eval d = d ^ 2 + (E.a₁ * c + E.a₃) * d -
      (c ^ 3 + E.a₂ * c ^ 2 + E.a₄ * c + E.a₆) := by
  simp only [quad, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]

lemma quad_eval_eq_zero_iff (E : WeierstrassCurve N) (c d : N) :
    (quad E c).eval d = 0 ↔ Equation E c d := by
  rw [quad_eval_eq, equation_iff]
  constructor <;> intro h <;> linear_combination h

lemma mem_fibrePlaces_iff (E : WeierstrassCurve N) [E.IsElliptic] (c : N) (Q : Place N E) :
    Q ∈ fibrePlaces E c ↔ ∃ d : N, (quad E c).eval d = 0 ∧ Q.1 = MotC2.affPlaceAt E c d := by
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

lemma algebraMap_XClass (E : WeierstrassCurve N) (c : N) :
    algebraMap (CoordinateRing E) (MotC2.Func E) (CoordinateRing.XClass E c)
      = MotC2.genX E - algebraMap N (MotC2.Func E) c := by
  rw [MotC2.XClass_eq_coordX_sub, map_sub]
  rfl

lemma ordOfPlace_algebraMap_eq_zero (E : WeierstrassCurve N) [E.IsElliptic] (H : H1Data N E)
    (S : Subalgebra N (MotC2.Func E)) (hS : MotC2.IsRatPlace E S) (c : N) :
    ordOfPlace E S hS (algebraMap N (MotC2.Func E) c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [map_zero]
    haveI : IsDiscreteValuationRing ↥S := hS.1.choose
    rw [ordOfPlace_eq_ordPlace E S hS, ordPlace_zero E S hS]
  · have hne : algebraMap N (MotC2.Func E) c ≠ 0 := fun h =>
      hc ((FaithfulSMul.algebraMap_injective N (MotC2.Func E)) (by rw [h, map_zero]))
    have h1 : (0 : ℤ) ≤ ordOfPlace E S hS (algebraMap N (MotC2.Func E) c) :=
      (H.ord_nonneg S hS _).mpr (Subalgebra.algebraMap_mem S c)
    have h2 : (0 : ℤ) ≤ ordOfPlace E S hS (algebraMap N (MotC2.Func E) c⁻¹) :=
      (H.ord_nonneg S hS _).mpr (Subalgebra.algebraMap_mem S c⁻¹)
    have h3 : ordOfPlace E S hS (algebraMap N (MotC2.Func E) c⁻¹)
        = - ordOfPlace E S hS (algebraMap N (MotC2.Func E) c) := by
      rw [map_inv₀ (algebraMap N (MotC2.Func E)) c]
      exact H.ord_inv S hS _ hne
    linarith

lemma algebraMap_neg_one_ne_zero (E : WeierstrassCurve N) :
    algebraMap N (MotC2.Func E) (-1) ≠ 0 := by
  intro h
  have h' : (-1 : N) = 0 := (FaithfulSMul.algebraMap_injective N (MotC2.Func E))
    (by rw [h, map_zero])
  exact neg_ne_zero.mpr one_ne_zero h'

lemma ordP_neg (E : WeierstrassCurve N) [E.IsElliptic] (H : H1Data N E) (Q : Place N E)
    (f : MotC2.Func E) : ordP E Q (-f) = ordP E Q f := by
  by_cases hf : f = 0
  · rw [hf, neg_zero]
  · have hneg : -(f) = algebraMap N (MotC2.Func E) (-1) * f := by
      rw [map_neg, map_one, neg_one_mul]
    simp only [ordP]
    rw [hneg, H.ord_mul Q.1 Q.2 _ _ (algebraMap_neg_one_ne_zero E) hf,
      ordOfPlace_algebraMap_eq_zero E H Q.1 Q.2 (-1), zero_add]

lemma one_le_ord_XClass_of_mem_fibrePlaces (E : WeierstrassCurve N) [E.IsElliptic]
    (H : H1Data N E) (c : N) (Q : Place N E) (hQ : Q ∈ fibrePlaces E c) :
    1 ≤ ordP E Q (algebraMap (CoordinateRing E) (MotC2.Func E) (CoordinateRing.XClass E c)) := by
  rw [mem_fibrePlaces_iff] at hQ
  obtain ⟨d, hd, hQd⟩ := hQ
  have hns : Nonsingular E c d := (equation_iff_nonsingular).mp ((quad_eval_eq_zero_iff E c d).mp hd)
  have hQ' : Q = ⟨MotC2.affPlaceAt E c d, (MotC2.AffPlace N E c d hns).1⟩ := Subtype.ext hQd
  have hle : (1 : ℤ) ≤ ordOfPlace E (MotC2.affPlaceAt E c d) (MotC2.AffPlace N E c d hns).1
      (MotC2.genX E - algebraMap N (MotC2.Func E) c) := by
    by_cases hw : 2 * d + E.a₁ * c + E.a₃ = 0
    · exact (H.aff_eq c d hns hw).1 ▸ (by norm_num : (1 : ℤ) ≤ 2)
    · exact (H.aff_ne c d hns hw).1 ▸ (by norm_num : (1 : ℤ) ≤ 1)
  rw [hQ']
  simpa only [ordP, algebraMap_XClass] using hle

lemma disjoint_fibrePlaces (E : WeierstrassCurve N) [E.IsElliptic] (H : H1Data N E)
    {c c' : N} (hcc : c ≠ c') : Disjoint (fibrePlaces E c) (fibrePlaces E c') := by
  classical
  rw [Finset.disjoint_left]
  intro Q hQ hQ'
  have h1 := one_le_ord_XClass_of_mem_fibrePlaces E H c Q hQ
  have h2 := one_le_ord_XClass_of_mem_fibrePlaces E H c' Q hQ'
  simp only [ordP] at h1 h2
  have hne : algebraMap N (MotC2.Func E) (c' - c) ≠ 0 := by
    intro h
    have h' : c' - c = 0 := (FaithfulSMul.algebraMap_injective N (MotC2.Func E))
      (by rw [h, map_zero])
    exact (sub_ne_zero.mpr (Ne.symm hcc)) h'
  have hne' : algebraMap (CoordinateRing E) (MotC2.Func E) (CoordinateRing.XClass E c') ≠ 0 :=
    fun h => CoordinateRing.XClass_ne_zero (W' := E) c'
      (IsFractionRing.injective (CoordinateRing E) (MotC2.Func E) (by simpa using h))
  have hdiff : algebraMap (CoordinateRing E) (MotC2.Func E) (CoordinateRing.XClass E c) +
      -(algebraMap (CoordinateRing E) (MotC2.Func E) (CoordinateRing.XClass E c'))
      = algebraMap N (MotC2.Func E) (c' - c) := by
    rw [algebraMap_XClass, algebraMap_XClass, map_sub]
    first | refl_ring1 | ring
  have hultra := H.ord_add Q.1 Q.2
    (algebraMap (CoordinateRing E) (MotC2.Func E) (CoordinateRing.XClass E c))
    (-(algebraMap (CoordinateRing E) (MotC2.Func E) (CoordinateRing.XClass E c')))
    (by rw [hdiff]; exact hne)
  have hneg : ordOfPlace E Q.1 Q.2
      (-(algebraMap (CoordinateRing E) (MotC2.Func E) (CoordinateRing.XClass E c'))) =
      ordOfPlace E Q.1 Q.2
        (algebraMap (CoordinateRing E) (MotC2.Func E) (CoordinateRing.XClass E c')) := by
    have := ordP_neg E H Q (algebraMap (CoordinateRing E) (MotC2.Func E) (CoordinateRing.XClass E c'))
    simpa only [ordP] using this
  rw [hdiff, hneg, ordOfPlace_algebraMap_eq_zero E H Q.1 Q.2 (c' - c)] at hultra
  have hmin : (1 : ℤ) ≤ min
      (ordOfPlace E Q.1 Q.2 (algebraMap (CoordinateRing E) (MotC2.Func E)
        (CoordinateRing.XClass E c)))
      (ordOfPlace E Q.1 Q.2 (algebraMap (CoordinateRing E) (MotC2.Func E)
        (CoordinateRing.XClass E c'))) := le_min h1 h2
  linarith

lemma notMem_fibrePlaces_infPlace (E : WeierstrassCurve N) [E.IsElliptic] (H : H1Data N E)
    (c : N) : (⟨MotC2.infPlace E, H.infRat⟩ : Place N E) ∉ fibrePlaces E c := by
  intro h
  rw [mem_fibrePlaces_iff] at h
  obtain ⟨d, hd, hQd⟩ := h
  have hsub : MotC2.infPlace E = MotC2.affPlaceAt E c d := hQd
  have hx : MotC2.genX E ∈ MotC2.infPlace E := by
    rw [hsub]
    exact MotC2.algebraMap_mem_affPlaceAt E c d (MotC2.coordX E)
  have hnn : (0 : ℤ) ≤ ordOfPlace E (MotC2.infPlace E) H.infRat (MotC2.genX E) :=
    (H.ord_nonneg (MotC2.infPlace E) H.infRat _).mpr hx
  have := H.inf_local.1
  linarith

/-- `ptsOf` is the point at infinity together with the union of the fibres over the roots. -/
lemma ptsOf_eq_insert (E : WeierstrassCurve N) [DecidableEq N] [DecidableEq (Place N E)]
    [E.IsElliptic] (H : H1Data N E) (p : Polynomial N) :
    ptsOf E H.infRat p = insert (⟨MotC2.infPlace E, H.infRat⟩ : Place N E)
      (p.roots.toFinset.biUnion (fun c => fibrePlaces E c)) := by
  ext Q
  rw [ptsOf]
  simp only [Finset.mem_insert, Finset.mem_biUnion, Multiset.mem_toFinset]

lemma ordSum_ptsOf (E : WeierstrassCurve N) [DecidableEq N] [E.IsElliptic] (H : H1Data N E)
    (p : Polynomial N) (f : MotC2.Func E) :
    ordSum E (ptsOf E H.infRat p) f = ordOfPlace E (MotC2.infPlace E) H.infRat f
      + ∑ c ∈ p.roots.toFinset, ordSum E (fibrePlaces E c) f := by
  classical
  have hnot : (⟨MotC2.infPlace E, H.infRat⟩ : Place N E) ∉
      p.roots.toFinset.biUnion (fun c => fibrePlaces E c) := by
    rw [Finset.mem_biUnion]
    rintro ⟨c, -, hc⟩
    exact notMem_fibrePlaces_infPlace E H c hc
  have hdisj : (↑p.roots.toFinset : Set N).PairwiseDisjoint (fun c => fibrePlaces E c) :=
    fun c _ c' _ hcc => disjoint_fibrePlaces E H hcc
  rw [ptsOf_eq_insert E H p]
  simp only [ordSum]
  rw [Finset.sum_insert (f := fun Q => ordP E Q f) hnot]
  rw [Finset.sum_biUnion (f := fun Q => ordP E Q f) hdisj]
  rfl


/-! ## The order sums over the fibres of `x = c` -/

/-! ## The per-fibre order sum of a coordinate-ring element

The fibre of `x : E → ℙ¹` over `c` has degree two, so the sum of the orders of a function over the
fibre is the multiplicity of `c` as a root of its norm.  For a coordinate-ring element this follows
from the two inputs below together with the norm identity `algA (norm a) = algA a · σ (algA a)` and
the invariance of the fibre sums under the negation `σ`. -/

/-- The order sums over a finite set of places are additive. -/
lemma ordSum_mul_local (E : WeierstrassCurve N) [E.IsElliptic] (H : H1Data N E)
    (S : Finset (Place N E))
    (f g : MotC2.Func E) (hf : f ≠ 0) (hg : g ≠ 0) :
    ordSum E S (f * g) = ordSum E S f + ordSum E S g := by
  rw [ordSum, ordSum, ordSum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun Q _ => by
    simp only [ordP]
    exact H.ord_mul Q.1 Q.2 _ _ hf hg

/-- The value of the fibre sums for polynomials in `x` (the fibre of `x = c` has degree two). -/
lemma ordSumPoly_local (E : WeierstrassCurve N) [IsAlgClosed N] [DecidableEq N] [E.IsElliptic]
    (H : H1Data N E) (h : Polynomial N) (hh : h ≠ 0) (c : N) :
    ordSum E (fibrePlaces E c) (algebraMap (Polynomial N) (MotC2.Func E) h)
      = 2 * ((h.roots.count c : ℕ) : ℤ) := by
  exact ordSumPoly E H h hh c

lemma DVR_addVal_ringEquiv_le {R₁ R₂ : Type*} [CommRing R₁] [IsDomain R₁]
    [IsDiscreteValuationRing R₁] [CommRing R₂] [IsDomain R₂] [IsDiscreteValuationRing R₂]
    (e : R₁ ≃+* R₂) (x : R₁) :
    IsDiscreteValuationRing.addVal R₂ (e x) ≤ IsDiscreteValuationRing.addVal R₁ x := by
  by_cases hx : x = 0
  · subst hx
    rw [map_zero, IsDiscreteValuationRing.addVal_zero, IsDiscreteValuationRing.addVal_zero]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_prime R₁
  have hϖi : Irreducible ϖ := hϖ.irreducible
  have hϖ'i : Irreducible (e ϖ) := hϖi.map e
  set n : ℕ := avNat x with hn
  have hcoe : ((n : ℕ) : ℕ∞) = IsDiscreteValuationRing.addVal R₁ x := coe_avNat hx
  have hdvd : x ∣ ϖ ^ n := by
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, Irreducible.addVal_pow hϖi]
    rw [← hcoe]
  have hdvd' : e x ∣ e (ϖ ^ n) := (e : R₁ →+* R₂).map_dvd hdvd
  rw [map_pow] at hdvd'
  have h2 : IsDiscreteValuationRing.addVal R₂ (e x) ≤ (n : ℕ∞) := by
    rw [← Irreducible.addVal_pow hϖ'i, IsDiscreteValuationRing.addVal_le_iff_dvd]
    exact hdvd'
  rw [← hcoe]
  exact h2

/-- A ring isomorphism of discrete valuation rings transports the additive valuation. -/

lemma DVR_addVal_ringEquiv {R₁ R₂ : Type*} [CommRing R₁] [IsDomain R₁]
    [IsDiscreteValuationRing R₁] [CommRing R₂] [IsDomain R₂] [IsDiscreteValuationRing R₂]
    (e : R₁ ≃+* R₂) (x : R₁) :
    IsDiscreteValuationRing.addVal R₂ (e x) = IsDiscreteValuationRing.addVal R₁ x :=
  le_antisymm (DVR_addVal_ringEquiv_le e x)
    (by
      have h := DVR_addVal_ringEquiv_le e.symm (e x)
      rwa [show e.symm (e x) = x from e.symm_apply_apply x] at h)

/-- The order at a rational place is transported by `N`-algebra automorphisms of the function
field: `ordOfPlace (S.map τ) (τ f) = ordOfPlace S f`. -/

theorem ordOfPlace_map' (E : WeierstrassCurve N) (τ : MotC2.Func E ≃ₐ[N] MotC2.Func E)
    (S : Subalgebra N (MotC2.Func E)) (hS : MotC2.IsRatPlace E S)
    (hS' : MotC2.IsRatPlace E (Subalgebra.map τ.toAlgHom S)) (f : MotC2.Func E) :
    ordOfPlace E (Subalgebra.map τ.toAlgHom S) hS' (τ f) = ordOfPlace E S hS f := by
  haveI hSd : IsDiscreteValuationRing ↥S := hS.1.choose
  haveI hS'd : IsDiscreteValuationRing ↥(Subalgebra.map τ.toAlgHom S) := hS'.1.choose
  set e : ↥S ≃+* ↥(Subalgebra.map τ.toAlgHom S) :=
    (Subalgebra.equivMapOfInjective S τ.toAlgHom τ.injective).toRingEquiv with he
  have he_apply : ∀ (x : MotC2.Func E) (hx : x ∈ S),
      e ⟨x, hx⟩ = ⟨τ x, Subalgebra.mem_map.mpr ⟨x, hx, rfl⟩⟩ := by
    intro x hx
    apply Subtype.ext
    rfl
  have hmem : τ f ∈ Subalgebra.map τ.toAlgHom S ↔ f ∈ S := by
    constructor
    · intro h
      obtain ⟨x, hx, hxy⟩ := Subalgebra.mem_map.mp h
      rw [τ.injective hxy] at hx
      exact hx
    · intro hf
      exact Subalgebra.mem_map.mpr ⟨f, hf, rfl⟩
  by_cases hf : f ∈ S
  · have hτf : τ f ∈ Subalgebra.map τ.toAlgHom S := hmem.mpr hf
    have h1 : ordOfPlace E S hS f =
        ((WithTop.untopD 0 ((IsDiscreteValuationRing.addVal ↥S) ⟨f, hf⟩) : ℕ) : ℤ) := by
      unfold ordOfPlace
      rw [dite_eq_left hf]
    have h2 : ordOfPlace E (Subalgebra.map τ.toAlgHom S) hS' (τ f) =
        ((WithTop.untopD 0 ((IsDiscreteValuationRing.addVal ↥(Subalgebra.map τ.toAlgHom S))
          ⟨τ f, hτf⟩) : ℕ) : ℤ) := by
      unfold ordOfPlace
      rw [dite_eq_left hτf]
    have he_f : e ⟨f, hf⟩ = ⟨τ f, hτf⟩ := by
      have h := he_apply f hf
      rw [h]
    have hkey : (WithTop.untopD 0 ((IsDiscreteValuationRing.addVal ↥S) ⟨f, hf⟩) : ℕ) =
        (WithTop.untopD 0 ((IsDiscreteValuationRing.addVal ↥(Subalgebra.map τ.toAlgHom S))
          ⟨τ f, hτf⟩) : ℕ) :=
      congrArg (fun v : ℕ∞ => v.untopD 0)
        (by rw [← he_f, DVR_addVal_ringEquiv e ⟨f, hf⟩])
    rw [h1, h2, hkey]
  · have hτf : τ f ∉ Subalgebra.map τ.toAlgHom S := fun h => hf (hmem.mp h)
    have hfinv : f⁻¹ ∈ S := (MotC2.mem_or_inv_mem_of_isRatPlace hS f).resolve_left hf
    have h1 : ordOfPlace E S hS f =
        -(((WithTop.untopD 0 ((IsDiscreteValuationRing.addVal ↥S) ⟨f⁻¹, hfinv⟩) : ℕ)) : ℤ) := by
      unfold ordOfPlace
      rw [dite_eq_right hf]
    have hτfinv : (τ f)⁻¹ ∈ Subalgebra.map τ.toAlgHom S := by
      have h : τ (f⁻¹) ∈ Subalgebra.map τ.toAlgHom S :=
        Subalgebra.mem_map.mpr ⟨f⁻¹, hfinv, rfl⟩
      rwa [map_inv₀ τ f] at h
    have h2 : ordOfPlace E (Subalgebra.map τ.toAlgHom S) hS' (τ f) =
        -(((WithTop.untopD 0 ((IsDiscreteValuationRing.addVal ↥(Subalgebra.map τ.toAlgHom S))
          ⟨(τ f)⁻¹, hτfinv⟩) : ℕ)) : ℤ) := by
      unfold ordOfPlace
      rw [dite_eq_right hτf]
    have he_finv : e ⟨f⁻¹, hfinv⟩ = ⟨(τ f)⁻¹, hτfinv⟩ := by
      have h := he_apply f⁻¹ hfinv
      rw [h]
      exact Subtype.ext (map_inv₀ τ f)
    have hadd : IsDiscreteValuationRing.addVal ↥(Subalgebra.map τ.toAlgHom S)
        ⟨(τ f)⁻¹, hτfinv⟩ = IsDiscreteValuationRing.addVal ↥S ⟨f⁻¹, hfinv⟩ := by
      calc IsDiscreteValuationRing.addVal ↥(Subalgebra.map τ.toAlgHom S) ⟨(τ f)⁻¹, hτfinv⟩
          = IsDiscreteValuationRing.addVal ↥(Subalgebra.map τ.toAlgHom S)
              (e ⟨f⁻¹, hfinv⟩) := by rw [he_finv]
        _ = IsDiscreteValuationRing.addVal ↥S ⟨f⁻¹, hfinv⟩ :=
              DVR_addVal_ringEquiv e ⟨f⁻¹, hfinv⟩
    have hkey : (WithTop.untopD 0 ((IsDiscreteValuationRing.addVal
        ↥(Subalgebra.map τ.toAlgHom S)) ⟨(τ f)⁻¹, hτfinv⟩) : ℕ) =
        (WithTop.untopD 0 ((IsDiscreteValuationRing.addVal ↥S) ⟨f⁻¹, hfinv⟩) : ℕ) :=
      congrArg (fun v : ℕ∞ => v.untopD 0) hadd
    rw [h1, h2, hkey]



lemma quad_eval_negY (E : WeierstrassCurve N) (c d : N) (hd : (quad E c).eval d = 0) :
    (quad E c).eval (negY E c d) = 0 := by
  rw [quad_eval_eq] at hd ⊢
  simp only [negY]
  linear_combination (norm := first | refl_ring1 | ring1) hd


lemma negAlgEquiv_apply_apply (E : WeierstrassCurve N) (x : MotC2.Func E) :
    (MotC2.negAlgEquiv E).toAlgHom ((MotC2.negAlgEquiv E).toAlgHom x) = x := by
  have h2 := congrArg (fun e : MotC2.Func E ≃ₐ[N] MotC2.Func E => e x)
    (MotC2.negAlgEquiv_mul_self E)
  rw [AlgEquiv.mul_apply, AlgEquiv.one_apply] at h2
  exact h2

/-- The negation is an involution on the subalgebras of the function field. -/

lemma map_map_negAlgEquiv (E : WeierstrassCurve N) (S : Subalgebra N (MotC2.Func E)) :
    Subalgebra.map (MotC2.negAlgEquiv E).toAlgHom
        (Subalgebra.map (MotC2.negAlgEquiv E).toAlgHom S) = S := by
  ext x
  simp only [Subalgebra.mem_map]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, hy⟩
    rw [negAlgEquiv_apply_apply] at hy
    rw [← hy]
    exact hz
  · intro hx
    exact ⟨MotC2.negAlgEquiv E x, ⟨x, hx, rfl⟩, negAlgEquiv_apply_apply E x⟩

/-- A `Place`-level version of `Subalgebra.map` under the negation. -/

def negPlace (E : WeierstrassCurve N) (Q : Place N E) : Place N E :=
  ⟨Subalgebra.map (MotC2.negAlgEquiv E).toAlgHom Q.1,
    MotC2.IsRatPlaceMap N E (MotC2.negAlgEquiv E) Q.1 Q.2⟩

/-- The place-level negation is an involution. -/

lemma negPlace_invol (E : WeierstrassCurve N) (Q : Place N E) : negPlace E (negPlace E Q) = Q := by
  apply Subtype.ext
  simp only [negPlace]
  exact map_map_negAlgEquiv E Q.1

/-- The negation permutes the fibre of `x = c`. -/

lemma negPlace_mem_fibrePlaces (E : WeierstrassCurve N) [E.IsElliptic] (c : N) (Q : Place N E)
    (hQ : Q ∈ fibrePlaces E c) : negPlace E Q ∈ fibrePlaces E c := by
  rw [mem_fibrePlaces_iff] at hQ ⊢
  obtain ⟨d, hd, hQd⟩ := hQ
  refine ⟨negY E c d, quad_eval_negY E c d hd, ?_⟩
  show Subalgebra.map (MotC2.negAlgEquiv E).toAlgHom Q.1 = MotC2.affPlaceAt E c (negY E c d)
  rw [hQd]
  exact map_negAlgEquiv_affPlaceAt E c d

/-- The order of `s f` at `Q` is the order of `f` at `s Q`. -/

lemma ordOfPlace_congr (E : WeierstrassCurve N) (S : Subalgebra N (MotC2.Func E))
    (h1 h2 : MotC2.IsRatPlace E S) (f : MotC2.Func E) :
    ordOfPlace E S h1 f = ordOfPlace E S h2 f := by
  rw [Subsingleton.elim h1 h2]

/-- The order at a place depends only on the subalgebra. -/

lemma ordOfPlace_subalgebra_congr (E : WeierstrassCurve N)
    {S T : Subalgebra N (MotC2.Func E)} (h : S = T)
    (hS : MotC2.IsRatPlace E S) (hT : MotC2.IsRatPlace E T) (f : MotC2.Func E) :
    ordOfPlace E T hT f = ordOfPlace E S hS f := by
  subst h
  exact ordOfPlace_congr E S hT hS f


lemma ordP_negPlace (E : WeierstrassCurve N) (Q : Place N E) (f : MotC2.Func E) :
    ordP E (negPlace E Q) f = ordP E Q (MotC2.negAlgEquiv E f) := by
  have hm : Subalgebra.map (MotC2.negAlgEquiv E).toAlgHom (negPlace E Q).1 = Q.1 := by
    simp only [negPlace]
    exact map_map_negAlgEquiv E Q.1
  have h := (ordOfPlace_map' E (MotC2.negAlgEquiv E) (negPlace E Q).1 (negPlace E Q).2
    (hm.symm ▸ Q.2) f).symm
  rw [← ordOfPlace_subalgebra_congr E hm (hm.symm ▸ Q.2) Q.2 (MotC2.negAlgEquiv E f)] at h
  simp only [ordP]
  exact h


/-- The negation permutes the fibre of `x = c`, so it preserves the fibre order sums. -/
theorem ordSumNeg_local (E : WeierstrassCurve N) [E.IsElliptic] (c : N)
    (f : MotC2.Func E) :
    ordSum E (fibrePlaces E c) (MotC2.negAlgEquiv E f) = ordSum E (fibrePlaces E c) f := by
  classical
  rw [ordSum, ordSum]
  refine Finset.sum_bij' (fun Q _ => negPlace E Q) (fun Q _ => negPlace E Q) ?_ ?_ ?_ ?_ ?_
  · intro Q hQ
    exact negPlace_mem_fibrePlaces E c Q hQ
  · intro Q hQ
    exact negPlace_mem_fibrePlaces E c Q hQ
  · intro Q hQ
    exact negPlace_invol E Q
  · intro Q hQ
    exact negPlace_invol E Q
  · intro Q hQ
    exact (ordP_negPlace E Q f).symm

/-- The per-fibre order sum of a coordinate-ring element is the multiplicity of `c` as a root of
its norm. -/
lemma fibreSum_eq_rootsCount (E : WeierstrassCurve N) [IsAlgClosed N] [DecidableEq N]
    [E.IsElliptic] (H : H1Data N E) (a : CoordinateRing E) (ha : a ≠ 0) (c : N) :
    ordSum E (fibrePlaces E c) (algebraMap (CoordinateRing E) (MotC2.Func E) a)
      = (((Algebra.norm (Polynomial N) a).roots.count c : ℕ) : ℤ) := by
  classical
  haveI : Module.Finite (Polynomial N) (CoordinateRing E) :=
    Module.Finite.of_basis (CoordinateRing.basis E)
  set σ := MotC2.negAlgEquiv E with hσ
  have hf0 : algebraMap (CoordinateRing E) (MotC2.Func E) a ≠ 0 := fun h =>
    ha (IsFractionRing.injective (CoordinateRing E) (MotC2.Func E) (by simpa using h))
  have hσ0 : σ (algebraMap (CoordinateRing E) (MotC2.Func E) a) ≠ 0 := fun h =>
    hf0 (σ.injective (by rw [h, map_zero]))
  have hmain : ordSum E (fibrePlaces E c) (algebraMap (CoordinateRing E) (MotC2.Func E) a) +
      ordSum E (fibrePlaces E c) (σ (algebraMap (CoordinateRing E) (MotC2.Func E) a))
      = 2 * (((Algebra.norm (Polynomial N) a).roots.count c : ℕ) : ℤ) := by
    rw [← ordSum_mul_local E H (fibrePlaces E c)
      (algebraMap (CoordinateRing E) (MotC2.Func E) a)
      (σ (algebraMap (CoordinateRing E) (MotC2.Func E) a)) hf0 hσ0,
      ← normEqNeg E a]
    exact ordSumPoly_local E H (Algebra.norm (Polynomial N) a)
      (Algebra.norm_ne_zero_iff.mpr ha) c
  have h2 : (2 : ℤ) * ordSum E (fibrePlaces E c)
      (algebraMap (CoordinateRing E) (MotC2.Func E) a)
      = 2 * (((Algebra.norm (Polynomial N) a).roots.count c : ℕ) : ℤ) := by
    rw [← hmain, ordSumNeg_local E c (algebraMap (CoordinateRing E) (MotC2.Func E) a)]
    first | refl_ring1 | ring
  linarith [h2]

/-- The number of roots (with multiplicity) of a nonzero polynomial over an algebraically closed
field is its degree. -/
lemma roots_count_sum (E : WeierstrassCurve N) [IsAlgClosed N] [DecidableEq N]
    (p : Polynomial N) (hp : p ≠ 0) :
    ∑ c ∈ p.roots.toFinset, ((p.roots.count c : ℕ) : ℤ) = (p.natDegree : ℤ) := by
  have h1 : ∑ c ∈ p.roots.toFinset, p.roots.count c = p.roots.card :=
    Multiset.toFinset_sum_count_eq p.roots
  have h2 : p.roots.card = p.natDegree := (IsAlgClosed.splits p).natDegree_eq_card_roots.symm
  rw [← h2, ← h1]
  push_cast
  rfl

/-- **The sum of the orders of a coordinate-ring element over the places above the roots of its
norm is zero.** -/
theorem sumA {N : Type*} [Field N] [IsAlgClosed N] (E : WeierstrassCurve N) [E.IsElliptic]
    (H : Work.MotV.H1Data N E)
    (hInf : ∀ (a : WeierstrassCurve.Affine.CoordinateRing E), a ≠ 0 →
      Work.MotV.ordOfPlace E (Work.MotC2.infPlace E) H.infRat
          (algebraMap (WeierstrassCurve.Affine.CoordinateRing E) (Work.MotC2.Func E) a)
        = - ((Algebra.norm (Polynomial N) a).natDegree : ℤ))
    (a : WeierstrassCurve.Affine.CoordinateRing E) (ha : a ≠ 0) :
    Work.MotV.ordSum E (Work.MotV.ptsOf E H.infRat (Algebra.norm (Polynomial N) a))
      (algebraMap (WeierstrassCurve.Affine.CoordinateRing E) (Work.MotC2.Func E) a) = 0 := by
  classical
  haveI : Module.Finite (Polynomial N) (CoordinateRing E) :=
    Module.Finite.of_basis (CoordinateRing.basis E)
  set p : Polynomial N := Algebra.norm (Polynomial N) a with hp
  have hp0 : p ≠ 0 := by
    rw [hp, Algebra.norm_ne_zero_iff]
    exact ha
  have h1 : ordOfPlace E (MotC2.infPlace E) H.infRat
      (algebraMap (CoordinateRing E) (MotC2.Func E) a) = -(p.natDegree : ℤ) := by
    rw [hInf a ha, ← hp]
  have h2 : ∑ c ∈ p.roots.toFinset,
      ordSum E (fibrePlaces E c) (algebraMap (CoordinateRing E) (MotC2.Func E) a)
      = (p.natDegree : ℤ) := by
    have hfib : ∀ c ∈ p.roots.toFinset, ordSum E (fibrePlaces E c)
        (algebraMap (CoordinateRing E) (MotC2.Func E) a)
        = ((p.roots.count c : ℕ) : ℤ) := by
      intro c _
      rw [hp]
      exact fibreSum_eq_rootsCount E H a ha c
    rw [Finset.sum_congr rfl hfib, roots_count_sum E p hp0]
  rw [ordSum_ptsOf E H (Algebra.norm (Polynomial N) a) _, ← hp, h1, h2]
  first | refl_ring1 | ring

end

end Work.MotV
