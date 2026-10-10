import Mathlib
import Submission.Work.MotV.H1Data
import Submission.Work.MotV.Machinery
import Submission.Work.MotV.ordPlaceCommon
import Submission.Work.MotV.ordBasic
import Submission.Work.MotC2.Relations
import Submission.Work.MotC2.AffPlace
import Submission.Work.MotC2.AffPlaceSetup
import Submission.Work.MotC2.Classification
import Submission.Work.MotC2.TranslationDefs
import Submission.Work.MotC2.NeTwoSetup
import Submission.Work.MotC2.algebraMap_smul_eq_aeval
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV

noncomputable section

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

variable {N : Type*} [Field N]

namespace OrdFibre

/-- The value of `quad E c` at `d`, in expanded form. -/
lemma quad_eval_eq (E : WeierstrassCurve N) (c d : N) :
    (quad E c).eval d =
      d ^ 2 + (E.a₁ * c + E.a₃) * d - (c ^ 3 + E.a₂ * c ^ 2 + E.a₄ * c + E.a₆) := by
  simp only [quad, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]

/-- `d` is a root of `quad E c` exactly when `(c, d)` is a point of `E`. -/
lemma quad_eval_eq_zero_iff (E : WeierstrassCurve N) (c d : N) :
    (quad E c).eval d = 0 ↔ Equation E c d := by
  rw [quad_eval_eq, equation_iff]
  constructor <;> intro h <;> linear_combination h

/-- `quad E c` has degree two. -/
lemma natDegree_quad (E : WeierstrassCurve N) (c : N) : (quad E c).natDegree = 2 := by
  have h : quad E c = C (1 : N) * X ^ 2 + C (E.a₁ * c + E.a₃) * X +
      C (-(c ^ 3 + E.a₂ * c ^ 2 + E.a₄ * c + E.a₆)) := by
    rw [quad, C_1, one_mul, sub_eq_add_neg, ← map_neg]
  rw [h]
  exact natDegree_quadratic one_ne_zero

/-- `quad E c` is nonzero. -/
lemma quad_ne_zero (E : WeierstrassCurve N) (c : N) : quad E c ≠ 0 := by
  intro h
  have := natDegree_quad E c
  rw [h] at this
  simp at this

/-- For a root `d` of `quad E c` the point `(c, d)` is nonsingular. -/
lemma nonsingular_of_quad_eval (E : WeierstrassCurve N) [E.IsElliptic] {c d : N}
    (hd : (quad E c).eval d = 0) : Nonsingular E c d :=
  (equation_iff_nonsingular).mp ((quad_eval_eq_zero_iff E c d).mp hd)

/-- The rational place of the point `(c, d)` of the fibre of `x = c`; the point at infinity when
`d` is not a root of `quad E c`. -/
def rootPlaceOf (E : WeierstrassCurve N) [E.IsElliptic] (c d : N) : Place N E := by
  classical
  exact if hd : (quad E c).eval d = 0 then
    ⟨MotC2.affPlaceAt E c d, (MotC2.AffPlace N E c d (nonsingular_of_quad_eval E hd)).1⟩
  else ⟨MotC2.infPlace E, MotC2.isRatPlace_infPlace E⟩

/-- The defining property of `rootPlaceOf` at a root. -/
lemma rootPlaceOf_of_eval (E : WeierstrassCurve N) [E.IsElliptic] {c d : N}
    (hd : (quad E c).eval d = 0) :
    rootPlaceOf E c d
      = ⟨MotC2.affPlaceAt E c d, (MotC2.AffPlace N E c d (nonsingular_of_quad_eval E hd)).1⟩ := by
  rw [rootPlaceOf, dif_pos hd]

/-- The evaluation of `quad E c` at a member of its root multiset is zero. -/
lemma eval_eq_zero_of_mem (E : WeierstrassCurve N) {c d : N}
    (hd : d ∈ (quad E c).roots) : (quad E c).eval d = 0 := by
  have h := (Polynomial.mem_roots' (p := quad E c)).mp hd
  exact Polynomial.IsRoot.def.mp h.2

/-- The root multiplicities of `quad E c` sum to `2`. -/
lemma sum_roots_count [IsAlgClosed N] [DecidableEq N] (E : WeierstrassCurve N) (c : N) :
    ∑ d ∈ (quad E c).roots.toFinset, (((quad E c).roots.count d : ℕ) : ℤ) = 2 := by
  have h1 : ∑ d ∈ (quad E c).roots.toFinset, (quad E c).roots.count d = 2 := by
    rw [Multiset.toFinset_sum_count_eq (quad E c).roots,
      ← (IsAlgClosed.splits (quad E c)).natDegree_eq_card_roots, natDegree_quad]
  have hcast : (((∑ d ∈ (quad E c).roots.toFinset, (quad E c).roots.count d : ℕ)) : ℤ) =
      ∑ d ∈ (quad E c).roots.toFinset, (((quad E c).roots.count d : ℕ) : ℤ) := by
    push_cast
    rfl
  rw [← hcast, h1]
  norm_num

/-! ## Membership of the fibre, and the elementary local bricks -/

/-- Membership in the fibre of `x = c`. -/
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

/-- `genX E - c` lies in every affine place of the fibre of `x = c`. -/
lemma genX_sub_mem (E : WeierstrassCurve N) (c a b : N) :
    MotC2.genX E - algebraMap N (MotC2.Func E) c ∈ MotC2.affPlaceAt E a b := by
  have h : MotC2.genX E - algebraMap N (MotC2.Func E) c =
      algebraMap (MotC2.Coord E) (MotC2.Func E) (CoordinateRing.XClass E c) := by
    rw [MotC2.XClass_eq_coordX_sub, map_sub,
      IsScalarTower.algebraMap_apply N (MotC2.Coord E) (MotC2.Func E)]
    rfl
  rw [h]
  exact MotC2.algebraMap_mem_affPlaceAt E a b _

/-- `genY E - b'` lies in every affine place of the point `(a, b)`. -/
lemma genY_sub_mem (E : WeierstrassCurve N) (a b b' : N) :
    MotC2.genY E - algebraMap N (MotC2.Func E) b' ∈ MotC2.affPlaceAt E a b := by
  have h : MotC2.genY E - algebraMap N (MotC2.Func E) b' =
      algebraMap (MotC2.Coord E) (MotC2.Func E) (CoordinateRing.YClass E (Polynomial.C b')) := by
    rw [MotC2.YClass_eq_coordY_sub, map_sub,
      IsScalarTower.algebraMap_apply N (MotC2.Coord E) (MotC2.Func E)]
    rfl
  rw [h]
  exact MotC2.algebraMap_mem_affPlaceAt E a b _

/-- The image of `YClass b'` in the function field is `y - b'`. -/
lemma YClass_eq_genY_sub (E : WeierstrassCurve N) (b' : N) :
    algebraMap (MotC2.Coord E) (MotC2.Func E) (CoordinateRing.YClass E (Polynomial.C b')) =
      MotC2.genY E - algebraMap N (MotC2.Func E) b' := by
  rw [MotC2.YClass_eq_coordY_sub, map_sub,
    IsScalarTower.algebraMap_apply N (MotC2.Coord E) (MotC2.Func E)]
  rfl

/-- A polynomial in `genX` lies in every subalgebra containing `genX`. -/
lemma aeval_genX_mem (E : WeierstrassCurve N) {S : Subalgebra N (MotC2.Func E)}
    (hx : MotC2.genX E ∈ S) (q : Polynomial N) : Polynomial.aeval (MotC2.genX E) q ∈ S := by
  have hle : Algebra.adjoin N ({MotC2.genX E} : Set (MotC2.Func E)) ≤ S :=
    Algebra.adjoin_le_iff.mpr (by rintro x (rfl : x = MotC2.genX E); exact hx)
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hle
  exact hle (AlgHom.mem_range_self _ q)

/-- The order of `0` at a rational place is `0`. -/
lemma ordP_zero (E : WeierstrassCurve N) (Q : Place N E) : ordP E Q (0 : MotC2.Func E) = 0 := by
  haveI : IsDiscreteValuationRing ↥Q.1 := Q.2.1.choose
  show ordOfPlace E Q.1 Q.2 (0 : MotC2.Func E) = 0
  rw [ordOfPlace_eq_ordPlace E Q.1 Q.2]
  exact ordPlace_zero E Q.1 Q.2

/-- Units of a subalgebra of a field, described in the ambient field. -/
lemma isUnit_subtype_iff (E : WeierstrassCurve N) {S : Subalgebra N (MotC2.Func E)}
    (f : MotC2.Func E) (hf : f ∈ S) :
    IsUnit (⟨f, hf⟩ : ↥S) ↔ ∃ g : MotC2.Func E, g ∈ S ∧ f * g = 1 := by
  constructor
  · rintro ⟨u, hu⟩
    have h1 : (u : ↥S) * ((u⁻¹ : (↥S)ˣ) : ↥S) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h2 : ((u : (↥S)ˣ) : ↥S) * (((u⁻¹ : (↥S)ˣ) : ↥S)) = 1 := h1
    refine ⟨(((u⁻¹ : (↥S)ˣ) : ↥S) : MotC2.Func E), ((u⁻¹ : (↥S)ˣ) : ↥S).2, ?_⟩
    have h3 := congrArg (fun z : ↥S => (z : MotC2.Func E)) h2
    rw [show (u : ↥S) = ⟨f, hf⟩ from hu] at h3
    exact h3
  · rintro ⟨g, hg, hfg⟩
    haveI : IsDedekindFiniteMonoid ↥S :=
      { mul_eq_one_symm := fun h => by rw [mul_comm, h] }
    exact ⟨Units.mkOfMulEqOne ⟨f, hf⟩ ⟨g, hg⟩ (Subtype.ext hfg), rfl⟩

/-- Two distinct roots of `quad E c` give distinct places. -/
lemma affPlaceAt_inj_of_eval (E : WeierstrassCurve N) [E.IsElliptic] {c d d' : N}
    (hd : (quad E c).eval d = 0) (hd' : (quad E c).eval d' = 0)
    (h : MotC2.affPlaceAt E c d = MotC2.affPlaceAt E c d') : d = d' := by
  classical
  by_contra hne
  have hns := nonsingular_of_quad_eval E hd
  have hns' := nonsingular_of_quad_eval E hd'
  haveI : MotC2.IsNonsingularPoint E c d := ⟨hns⟩
  haveI : MotC2.IsNonsingularPoint E c d' := ⟨hns'⟩
  -- `y - d'` is not a unit of the place of `(c, d')`
  have hmem' : MotC2.genY E - algebraMap N (MotC2.Func E) d' ∈ MotC2.affPlaceAt E c d' :=
    genY_sub_mem E c d' d'
  have hsub_eq : (algebraMap (MotC2.Coord E) ↥(MotC2.affPlaceAt E c d')
      (CoordinateRing.YClass E (Polynomial.C d')) : ↥(MotC2.affPlaceAt E c d')) =
      ⟨MotC2.genY E - algebraMap N (MotC2.Func E) d', hmem'⟩ := by
    apply Subtype.ext
    rw [MotC2.affPlaceAt_algebraMap_val]
    exact YClass_eq_genY_sub E d'
  have hnonunit' : ¬ IsUnit
      (⟨MotC2.genY E - algebraMap N (MotC2.Func E) d', hmem'⟩ :
        ↥(MotC2.affPlaceAt E c d')) := by
    intro hu
    exact ((IsLocalRing.notMem_maximalIdeal).mpr hu)
      (hsub_eq ▸ MotC2.affPlaceAt_YClass_mem_maximalIdeal E c d')
  -- transport it to the place of `(c, d)`
  have hmem : MotC2.genY E - algebraMap N (MotC2.Func E) d' ∈ MotC2.affPlaceAt E c d :=
    genY_sub_mem E c d d'
  have hnonunit : ¬ IsUnit
      (⟨MotC2.genY E - algebraMap N (MotC2.Func E) d', hmem⟩ : ↥(MotC2.affPlaceAt E c d)) := by
    intro hu
    rw [isUnit_subtype_iff E] at hu
    obtain ⟨g, hg, hfg⟩ := hu
    exact hnonunit' ((isUnit_subtype_iff E _ hmem').mpr ⟨g, h ▸ hg, hfg⟩)
  -- both `y - d` and `y - d'` lie in the maximal ideal of the place of `(c, d)`
  have hmemd : MotC2.genY E - algebraMap N (MotC2.Func E) d ∈ MotC2.affPlaceAt E c d :=
    genY_sub_mem E c d d
  have hMd : (⟨MotC2.genY E - algebraMap N (MotC2.Func E) d, hmemd⟩ :
      ↥(MotC2.affPlaceAt E c d)) ∈
      IsLocalRing.maximalIdeal ↥(MotC2.affPlaceAt E c d) := by
    have hsub_eq_d : (algebraMap (MotC2.Coord E) ↥(MotC2.affPlaceAt E c d)
        (CoordinateRing.YClass E (Polynomial.C d)) : ↥(MotC2.affPlaceAt E c d)) =
        ⟨MotC2.genY E - algebraMap N (MotC2.Func E) d, hmemd⟩ := by
      apply Subtype.ext
      rw [MotC2.affPlaceAt_algebraMap_val]
      exact YClass_eq_genY_sub E d
    rw [← hsub_eq_d]
    exact MotC2.affPlaceAt_YClass_mem_maximalIdeal E c d
  have hM' : (⟨MotC2.genY E - algebraMap N (MotC2.Func E) d', hmem⟩ :
      ↥(MotC2.affPlaceAt E c d)) ∈
      IsLocalRing.maximalIdeal ↥(MotC2.affPlaceAt E c d) := by
    by_contra hx
    exact hnonunit ((IsLocalRing.notMem_maximalIdeal).mp hx)
  -- hence the nonzero constant `d' - d` lies in the maximal ideal: contradiction
  have hdiff : (⟨MotC2.genY E - algebraMap N (MotC2.Func E) d, hmemd⟩ :
        ↥(MotC2.affPlaceAt E c d)) - ⟨MotC2.genY E - algebraMap N (MotC2.Func E) d', hmem⟩ =
      algebraMap N ↥(MotC2.affPlaceAt E c d) (d' - d) := by
    apply Subtype.ext
    change (MotC2.genY E - algebraMap N (MotC2.Func E) d) -
        (MotC2.genY E - algebraMap N (MotC2.Func E) d') = algebraMap N (MotC2.Func E) (d' - d)
    rw [map_sub]
    first | refl_ring1 | ring
  have hne' : d' - d ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  exact ((IsLocalRing.notMem_maximalIdeal).mpr
      (MotC2.isUnit_algebraMap_affPlaceAt_of_ne_zero E c d hne'))
    (hdiff ▸ sub_mem hMd hM')

/-! ## The two local computations -/

/-- The order of `h(genX)` at a place of the fibre of `x = c` is the multiplicity of `c` as a root of
`h` times the order of `x - c` there. -/
lemma ordP_algebraMap_eq_zero_of_eval_ne_zero (E : WeierstrassCurve N) [E.IsElliptic]
    (H : H1Data N E) (c : N) (p : Polynomial N) (hp : p.eval c ≠ 0) (d : N)
    (hd : (quad E c).eval d = 0) :
    ordP E (rootPlaceOf E c d) (algebraMap (Polynomial N) (MotC2.Func E) p) = 0 := by
  classical
  have hns := nonsingular_of_quad_eval E hd
  haveI : MotC2.IsNonsingularPoint E c d := ⟨hns⟩
  have hS : MotC2.IsRatPlace E (MotC2.affPlaceAt E c d) := (MotC2.AffPlace N E c d hns).1
  -- `p = p(c) + (X - c) * q`
  have hroot : (p - Polynomial.C (p.eval c)).IsRoot c := by
    rw [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_C, sub_self]
  obtain ⟨q, hq⟩ : ∃ q, p - Polynomial.C (p.eval c) = (Polynomial.X - Polynomial.C c) * q :=
    ⟨(p - Polynomial.C (p.eval c)) /ₘ (Polynomial.X - Polynomial.C c),
      ((Polynomial.mul_divByMonic_eq_iff_isRoot).mpr hroot).symm⟩
  have hpq : p = Polynomial.C (p.eval c) + (Polynomial.X - Polynomial.C c) * q := by
    rw [← hq]; ring
  have hF : algebraMap (Polynomial N) (MotC2.Func E) p =
      algebraMap N (MotC2.Func E) (p.eval c) +
        (MotC2.genX E - algebraMap N (MotC2.Func E) c) *
          Polynomial.aeval (MotC2.genX E) q := by
    conv_lhs => rw [hpq]
    rw [map_add, map_mul,
      MotC2.algebraMap_polynomial_eq_aeval_genX E (Polynomial.C (p.eval c)),
      MotC2.algebraMap_polynomial_eq_aeval_genX E (Polynomial.X - Polynomial.C c),
      MotC2.algebraMap_polynomial_eq_aeval_genX E q]
    simp only [Polynomial.aeval_sub, Polynomial.aeval_X, Polynomial.aeval_C]
  -- the order of the two summands
  have hxS : MotC2.genX E - algebraMap N (MotC2.Func E) c ∈ MotC2.affPlaceAt E c d :=
    genX_sub_mem E c c d
  have hxord : 1 ≤ ordOfPlace E (MotC2.affPlaceAt E c d) hS
      (MotC2.genX E - algebraMap N (MotC2.Func E) c) := by
    by_cases hw : 2 * d + E.a₁ * c + E.a₃ = 0
    · exact (H.aff_eq c d hns hw).1 ▸ (by norm_num : (1 : ℤ) ≤ 2)
    · exact (H.aff_ne c d hns hw).1 ▸ (by norm_num : (1 : ℤ) ≤ 1)
  have hxne : MotC2.genX E - algebraMap N (MotC2.Func E) c ≠ 0 := by
    intro h0
    rw [h0] at hxord
    have hzero : ordOfPlace E (MotC2.affPlaceAt E c d) hS (0 : MotC2.Func E) = 0 := by
      haveI : IsDiscreteValuationRing ↥(MotC2.affPlaceAt E c d) := hS.1.choose
      rw [ordOfPlace_eq_ordPlace E _ hS]
      exact ordPlace_zero E _ hS
    rw [hzero] at hxord
    exact absurd hxord (by norm_num)
  have hqS : Polynomial.aeval (MotC2.genX E) q ∈ MotC2.affPlaceAt E c d :=
    aeval_genX_mem E (MotC2.algebraMap_mem_affPlaceAt E c d (MotC2.coordX E)) q
  have hqord : 0 ≤ ordOfPlace E (MotC2.affPlaceAt E c d) hS
      (Polynomial.aeval (MotC2.genX E) q) :=
    (H.ord_nonneg _ hS _).mpr hqS
  have hu0 : algebraMap N (MotC2.Func E) (p.eval c) ≠ 0 := fun h0 =>
    hp ((FaithfulSMul.algebraMap_injective N (MotC2.Func E)) (by rw [h0, map_zero]))
  have huord : ordOfPlace E (MotC2.affPlaceAt E c d) hS
      (algebraMap N (MotC2.Func E) (p.eval c)) = 0 :=
    ordOfPlace_const E H _ hS (p.eval c) hp
  -- conclude
  rw [rootPlaceOf_of_eval E hd]
  show ordOfPlace E (MotC2.affPlaceAt E c d)
    (MotC2.AffPlace N E c d (nonsingular_of_quad_eval E hd)).1
    (algebraMap (Polynomial N) (MotC2.Func E) p) = 0
  by_cases hF0 : algebraMap (Polynomial N) (MotC2.Func E) p = 0
  · have hzero : ordOfPlace E (MotC2.affPlaceAt E c d) hS (0 : MotC2.Func E) = 0 := by
      haveI : IsDiscreteValuationRing ↥(MotC2.affPlaceAt E c d) := hS.1.choose
      rw [ordOfPlace_eq_ordPlace E _ hS]
      exact ordPlace_zero E _ hS
    rw [hF0]
    exact hzero
  · rw [hF]
    by_cases hv0 : (MotC2.genX E - algebraMap N (MotC2.Func E) c) *
        Polynomial.aeval (MotC2.genX E) q = 0
    · rw [hv0, add_zero, huord]
    · have hvord : 1 ≤ ordOfPlace E (MotC2.affPlaceAt E c d) hS
          ((MotC2.genX E - algebraMap N (MotC2.Func E) c) *
            Polynomial.aeval (MotC2.genX E) q) := by
        have hq0 : Polynomial.aeval (MotC2.genX E) q ≠ 0 := fun h0 => hv0 (by rw [h0, mul_zero])
        rw [H.ord_mul _ hS _ _ hxne hq0]
        linarith
      have hsum0 : algebraMap N (MotC2.Func E) (p.eval c) +
          (MotC2.genX E - algebraMap N (MotC2.Func E) c) *
            Polynomial.aeval (MotC2.genX E) q ≠ 0 := by
        rw [← hF]; exact hF0
      rw [ordOfPlace_add_eq_of_lt E H _ hS _ _ hu0 hv0 hsum0 (by rw [huord]; linarith)]
      exact huord

/-- The ramification index of the map `x` at the point `(c, d)` is the multiplicity of `d` as a root
of `quad E c`. -/
lemma ordP_genX_sub_eq (E : WeierstrassCurve N) [E.IsElliptic] (H : H1Data N E)
    (c d : N) (hd : (quad E c).eval d = 0) :
    ordP E (rootPlaceOf E c d) (MotC2.genX E - algebraMap N (MotC2.Func E) c)
      = ((Polynomial.rootMultiplicity d (quad E c) : ℕ) : ℤ) := by
  classical
  have hns := nonsingular_of_quad_eval E hd
  haveI : MotC2.IsNonsingularPoint E c d := ⟨hns⟩
  -- (A) the order of `x - c`
  have hA : ordP E (rootPlaceOf E c d) (MotC2.genX E - algebraMap N (MotC2.Func E) c)
      = 1 + (if 2 * d + E.a₁ * c + E.a₃ = 0 then 1 else 0) := by
    rw [rootPlaceOf_of_eval E hd]
    by_cases hw : 2 * d + E.a₁ * c + E.a₃ = 0
    · rw [if_pos hw]
      exact (H.aff_eq c d hns hw).1.trans (by norm_num : (2 : ℤ) = 1 + 1)
    · rw [if_neg hw]
      exact (H.aff_ne c d hns hw).1.trans (by norm_num : (1 : ℤ) = 1 + 0)
  -- (B) the multiplicity of `d` as a root of `quad E c`
  have hB : ((Polynomial.rootMultiplicity d (quad E c) : ℕ) : ℤ)
      = 1 + (if 2 * d + E.a₁ * c + E.a₃ = 0 then 1 else 0) := by
    have hconst : c ^ 3 + E.a₂ * c ^ 2 + E.a₄ * c + E.a₆ =
        d ^ 2 + (E.a₁ * c + E.a₃) * d := by
      have h0 := hd
      rw [quad_eval_eq] at h0
      exact (sub_eq_zero.mp h0).symm
    have hfac : quad E c =
        (Polynomial.X - Polynomial.C d) *
          (Polynomial.X + Polynomial.C (d + (E.a₁ * c + E.a₃))) := by
      rw [quad, hconst]
      simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow]
      first | refl_ring1 | ring
    have hprod0 : (Polynomial.X - Polynomial.C d) *
        (Polynomial.X + Polynomial.C (d + (E.a₁ * c + E.a₃))) ≠ 0 := by
      rw [← hfac]; exact (quad_ne_zero E c)
    have hmul : Polynomial.rootMultiplicity d (quad E c) =
        Polynomial.rootMultiplicity d (Polynomial.X - Polynomial.C d) +
          Polynomial.rootMultiplicity d
            (Polynomial.X + Polynomial.C (d + (E.a₁ * c + E.a₃))) := by
      conv_lhs => rw [hfac]
      exact Polynomial.rootMultiplicity_mul hprod0
    have h2 : Polynomial.rootMultiplicity d
        (Polynomial.X + Polynomial.C (d + (E.a₁ * c + E.a₃))) =
        if d = -(d + (E.a₁ * c + E.a₃)) then 1 else 0 := by
      have heq : Polynomial.X + Polynomial.C (d + (E.a₁ * c + E.a₃)) =
          Polynomial.X - Polynomial.C (-(d + (E.a₁ * c + E.a₃))) := by
        rw [Polynomial.C_neg, sub_neg_eq_add]
      rw [heq, Polynomial.rootMultiplicity_X_sub_C]
    rw [hmul, Polynomial.rootMultiplicity_X_sub_C_self, h2]
    have hiff : d = -(d + (E.a₁ * c + E.a₃)) ↔ 2 * d + E.a₁ * c + E.a₃ = 0 := by
      constructor <;> intro hh <;> linear_combination hh
    by_cases hw : 2 * d + E.a₁ * c + E.a₃ = 0
    · rw [if_pos (hiff.mpr hw), if_pos hw]
      norm_num
    · rw [if_neg (fun hh => hw (hiff.mp hh)), if_neg hw]
      norm_num
  rw [hA, hB]

/-- The order of `h(genX)` at a place of the fibre is the multiplicity of `c` as a root of `h` times
the order of `x - c` there. -/
lemma ordP_algebraMap_eq [DecidableEq N] (E : WeierstrassCurve N) [E.IsElliptic] (H : H1Data N E)
    (h : Polynomial N) (hh : h ≠ 0) (c d : N) (hd : (quad E c).eval d = 0) :
    ordP E (rootPlaceOf E c d) (algebraMap (Polynomial N) (MotC2.Func E) h)
      = ((h.roots.count c : ℕ) : ℤ) *
        ordP E (rootPlaceOf E c d) (MotC2.genX E - algebraMap N (MotC2.Func E) c) := by
  classical
  obtain ⟨g, hg, hgdvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd h hh c
  have hgeval : g.eval c ≠ 0 := fun h0 =>
    hgdvd (Polynomial.dvd_iff_isRoot.mpr (Polynomial.IsRoot.def.mpr h0))
  have hg0 : g ≠ 0 := fun h0 => hh (by rw [hg, h0, mul_zero])
  have hinj : Function.Injective (algebraMap (Polynomial N) (MotC2.Func E)) :=
    MotC2.algebraMap_poly_func_injective E
  have hgmap : algebraMap (Polynomial N) (MotC2.Func E) g ≠ 0 := fun h0 =>
    hg0 (hinj (by rw [h0, map_zero]))
  have hxne : MotC2.genX E - algebraMap N (MotC2.Func E) c ≠ 0 := by
    intro h0
    have h1 : algebraMap (Polynomial N) (MotC2.Func E) (Polynomial.X - Polynomial.C c) = 0 := by
      rw [MotC2.algebraMap_polynomial_eq_aeval_genX E, Polynomial.aeval_sub, Polynomial.aeval_X,
        Polynomial.aeval_C]
      exact h0
    exact (Polynomial.monic_X_sub_C c).ne_zero (hinj (by rw [h1, map_zero]))
  have hmap : algebraMap (Polynomial N) (MotC2.Func E) h =
      (MotC2.genX E - algebraMap N (MotC2.Func E) c) ^ h.rootMultiplicity c *
        algebraMap (Polynomial N) (MotC2.Func E) g := by
    conv_lhs => rw [hg]
    rw [map_mul, map_pow]
    congr 1
    rw [MotC2.algebraMap_polynomial_eq_aeval_genX E (Polynomial.X - Polynomial.C c),
      Polynomial.aeval_sub, Polynomial.aeval_X, Polynomial.aeval_C]
  have h1 : ordP E (rootPlaceOf E c d) (algebraMap (Polynomial N) (MotC2.Func E) h) =
      ordP E (rootPlaceOf E c d)
          ((MotC2.genX E - algebraMap N (MotC2.Func E) c) ^ h.rootMultiplicity c) +
        ordP E (rootPlaceOf E c d) (algebraMap (Polynomial N) (MotC2.Func E) g) := by
    rw [hmap]
    exact H.ord_mul _ _ _ _ (pow_ne_zero _ hxne) hgmap
  have h2 : ordP E (rootPlaceOf E c d)
        ((MotC2.genX E - algebraMap N (MotC2.Func E) c) ^ h.rootMultiplicity c) =
      (h.rootMultiplicity c : ℤ) *
        ordP E (rootPlaceOf E c d) (MotC2.genX E - algebraMap N (MotC2.Func E) c) := by
    simp only [ordP]
    exact ordOfPlace_pow E H (rootPlaceOf E c d).1 (rootPlaceOf E c d).2
      (MotC2.genX E - algebraMap N (MotC2.Func E) c) hxne _
  have h3 : ordP E (rootPlaceOf E c d) (algebraMap (Polynomial N) (MotC2.Func E) g) = 0 :=
    ordP_algebraMap_eq_zero_of_eval_ne_zero E H c g hgeval d hd
  rw [h1, h2, h3, ← Polynomial.count_roots h]
  first | refl_ring1 | ring

/-- The sum over the fibre of `x = c` is the sum over the roots of `quad E c`. -/
lemma sum_fibrePlaces_eq [DecidableEq N] (E : WeierstrassCurve N) [E.IsElliptic] (c : N)
    (f : MotC2.Func E) :
    ordSum E (fibrePlaces E c) f =
      ∑ d ∈ (quad E c).roots.toFinset, ordP E (rootPlaceOf E c d) f := by
  classical
  rw [ordSum]
  symm
  refine Finset.sum_bij (fun d _ => rootPlaceOf E c d) ?_ ?_ ?_ ?_
  · intro d hd
    rw [mem_fibrePlaces_iff]
    refine ⟨d, eval_eq_zero_of_mem E (Multiset.mem_toFinset.mp hd), ?_⟩
    rw [rootPlaceOf_of_eval E (eval_eq_zero_of_mem E (Multiset.mem_toFinset.mp hd))]
  · intro d₁ hd₁ d₂ hd₂ heq
    have h1 : (rootPlaceOf E c d₁).1 = (rootPlaceOf E c d₂).1 := congrArg Subtype.val heq
    rw [rootPlaceOf_of_eval E (eval_eq_zero_of_mem E (Multiset.mem_toFinset.mp hd₁)),
      rootPlaceOf_of_eval E (eval_eq_zero_of_mem E (Multiset.mem_toFinset.mp hd₂))] at h1
    exact affPlaceAt_inj_of_eval E (eval_eq_zero_of_mem E (Multiset.mem_toFinset.mp hd₁))
      (eval_eq_zero_of_mem E (Multiset.mem_toFinset.mp hd₂)) h1
  · intro Q hQ
    obtain ⟨d, hd, hQd⟩ := (mem_fibrePlaces_iff E c Q).mp hQ
    refine ⟨d, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots' (p := quad E c)).mpr
      ⟨quad_ne_zero E c, Polynomial.IsRoot.def.mpr hd⟩), ?_⟩
    rw [rootPlaceOf_of_eval E hd]
    exact Subtype.ext hQd.symm
  · intro d _
    rfl

end OrdFibre

-- imports: Mathlib, Submission.Work.MotV.H1Data, Submission.Work.MotV.Machinery, Submission.Work.MotV.ordPlaceCommon, Submission.Work.MotV.affLocal, Submission.Work.MotC2.Relations, Submission.Work.MotC2.AffPlace, Submission.Work.MotC2.AffPlaceSetup
/-- The sum of the orders of a polynomial in `x` over the fibre of `x = c` is twice the multiplicity
of `c` as a root of that polynomial (the fibre of `x : E → ℙ¹` over any point has degree `2`).

Route.  (0) For `d ∈ (quad E c).roots.toFinset` the equation `Equation E c d` holds (the
evaluation of `quad E c` at `d` is exactly the Weierstrass equation at `(c,d)`), so `(c,d)` is
nonsingular (`MotC2.nonsingular_of_equation`).
(1) Unfold `fibrePlaces E c`: it is `Finset.biUnion ((quad E c).roots.toFinset) f` where the
`by_cases` always takes the branch `{⟨affPlaceAt E c d, _⟩}`, hence equals
`((quad E c).roots.toFinset).image (fun d => ⟨MotC2.affPlaceAt E c d, _⟩)`; that map is injective on
the roots because `y - d` and `y - d'` both lie in the maximal ideal of the common place
(`AffPlaceSetup.affPlaceAt_YClass_mem_maximalIdeal`), so the nonzero constant `d' - d`, being a unit
(`AffPlaceSetup.isUnit_algebraMap_affPlaceAt_of_ne_zero`), would lie in it.  Use
`Finset.sum_image`.
(2) At each place of the fibre, `h(genX) = (genX - c)^m · h₁(genX)` with `m = h.roots.count c`
(`Polynomial.count_roots`, `Polynomial.rootMultiplicity`, `Polynomial.pow_rootMultiplicity_dvd`) and
`h₁.eval c ≠ 0`.  As `h₁(X) - C (h₁.eval c)` is divisible by `X - C c`
(`Polynomial.dvd_iff_isRoot`), `h₁(genX)` is a nonzero constant plus a multiple of `genX - c`, hence
a unit of the local ring: its order is `0`.  With `H.ord_mul` this gives
`ord (h(genX)) = m * ord (genX - c)`.
(3) For a root `d` of `quad E c`, `e d := ord_{(c,d)}(genX - c)` is `1` if
`2*d + a₁*c + a₃ ≠ 0` and `2` otherwise (`H.aff_ne`, `H.aff_eq`), and in fact
`e d = (quad E c).roots.count d`: if `2d + a₁c + a₃ = 0` then, since `d` is a root,
`quad E c = (X - C d)^2` (compare coefficients: `(X-d)^2 = X^2 - 2dX + d^2` and
`W = d² + s d = -d²`), so the multiplicity is `2`; conversely multiplicity `2` forces
`quad E c = (X - C d)^2` and hence `s = -2d`.  Then
`∑ d ∈ (quad E c).roots.toFinset, e d = ∑ d ∈ (quad E c).roots.toFinset, (quad E c).roots.count d
 = (quad E c).roots.card = 2` (`Multiset.toFinset_sum_count_eq`, and `roots.card = natDegree` for a
split quadratic over the algebraically closed `N`). -/
theorem ordSumPoly {N : Type*} [Field N] [IsAlgClosed N] [DecidableEq N]
    (E : WeierstrassCurve N) [E.IsElliptic] (H : Work.MotV.H1Data N E)
    (h : Polynomial N) (hh : h ≠ 0) (c : N) :
    Work.MotV.ordSum E (Work.MotV.fibrePlaces E c)
        (algebraMap (Polynomial N) (Work.MotC2.Func E) h)
      = 2 * (((h.roots.count c : ℕ)) : ℤ) := by
  classical
  rw [OrdFibre.sum_fibrePlaces_eq E c (algebraMap (Polynomial N) (MotC2.Func E) h)]
  have hstep : ∑ d ∈ (quad E c).roots.toFinset,
        ordP E (OrdFibre.rootPlaceOf E c d) (algebraMap (Polynomial N) (MotC2.Func E) h) =
      ∑ d ∈ (quad E c).roots.toFinset, ((h.roots.count c : ℕ) : ℤ) *
        ordP E (OrdFibre.rootPlaceOf E c d) (MotC2.genX E - algebraMap N (MotC2.Func E) c) :=
    Finset.sum_congr rfl fun d hd => OrdFibre.ordP_algebraMap_eq E H h hh c d
      (OrdFibre.eval_eq_zero_of_mem E (Multiset.mem_toFinset.mp hd))
  rw [hstep, ← Finset.mul_sum]
  have hsum2 : ∑ d ∈ (quad E c).roots.toFinset,
        ordP E (OrdFibre.rootPlaceOf E c d) (MotC2.genX E - algebraMap N (MotC2.Func E) c) = 2 := by
    have hstep2 : ∑ d ∈ (quad E c).roots.toFinset,
          ordP E (OrdFibre.rootPlaceOf E c d) (MotC2.genX E - algebraMap N (MotC2.Func E) c) =
        ∑ d ∈ (quad E c).roots.toFinset,
          ((Polynomial.rootMultiplicity d (quad E c) : ℕ) : ℤ) :=
      Finset.sum_congr rfl fun d hd => OrdFibre.ordP_genX_sub_eq E H c d
        (OrdFibre.eval_eq_zero_of_mem E (Multiset.mem_toFinset.mp hd))
    have hstep3 : ∑ d ∈ (quad E c).roots.toFinset,
          ((Polynomial.rootMultiplicity d (quad E c) : ℕ) : ℤ) =
        ∑ d ∈ (quad E c).roots.toFinset, (((quad E c).roots.count d : ℕ) : ℤ) :=
      Finset.sum_congr rfl fun d _ => by rw [← Polynomial.count_roots (quad E c)]
    rw [hstep2, hstep3]
    exact OrdFibre.sum_roots_count E c
  rw [hsum2]
  first | refl_ring1 | ring

end

end Work.MotV
