import Mathlib
import Submission.Work.MotV.H1Data
import Submission.Work.MotV.Machinery
import Submission.Work.MotV.derivCount
import Submission.Work.MotV.supportAff
import Submission.Work.MotC2.Classification
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV

open WeierstrassCurve WeierstrassCurve.Affine
open Work.MotC2
open scoped WithZero

noncomputable section

variable {N : Type*} [Field N]

/-! ## Auxiliary lemmas for the final ("value") step of `derivMain` -/

/-- Constants have non-negative order at every rational place. -/
lemma le_ordOfPlace_const (E : WeierstrassCurve N) [E.IsElliptic] (H : H1Data N E)
    (S : Subalgebra N (Func E)) (hS : MotC2.IsRatPlace E S) (c : N) :
    (0 : ℤ) ≤ ordOfPlace E S hS (algebraMap N (Func E) c) :=
  (H.ord_nonneg S hS _).mpr (Subalgebra.algebraMap_mem S c)

/-- **The value of a function at the point at infinity.**  If `f` is regular at the point at
infinity, then either `f` is a constant, or `f - c` has positive order there for the residue
`c` of `f`. -/
lemma exists_const_or_ord_pos (E : WeierstrassCurve N) [E.IsElliptic] (H : H1Data N E)
    (f : Func E) (hf : f ∈ MotC2.infPlace E) :
    ∃ c : N, algebraMap N (Func E) c = f ∨
      (f - algebraMap N (Func E) c ≠ 0 ∧
        0 < ordOfPlace E (MotC2.infPlace E) H.infRat (f - algebraMap N (Func E) c)) := by
  haveI : IsDiscreteValuationRing ↥(MotC2.infPlace E) := H.infRat.1.choose
  have hres : Function.Bijective (fun c : N =>
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(MotC2.infPlace E))
        (algebraMap N ↥(MotC2.infPlace E) c)) := H.infRat.1.choose_spec
  obtain ⟨c, hc⟩ := hres.2 (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(MotC2.infPlace E))
    (⟨f, hf⟩ : ↥(MotC2.infPlace E)))
  refine ⟨c, ?_⟩
  by_cases hfeq : algebraMap N (Func E) c = f
  · exact Or.inl hfeq
  · refine Or.inr ?_
    have hgmem : f - algebraMap N (Func E) c ∈ MotC2.infPlace E :=
      Subalgebra.sub_mem _ hf (Subalgebra.algebraMap_mem _ c)
    have hgm : (⟨f - algebraMap N (Func E) c, hgmem⟩ : ↥(MotC2.infPlace E))
        ∈ IsLocalRing.maximalIdeal ↥(MotC2.infPlace E) := by
      have h := Ideal.Quotient.eq.mp hc.symm
      have heq : (⟨f, hf⟩ : ↥(MotC2.infPlace E)) -
          ⟨algebraMap N ↥(MotC2.infPlace E) c, Subalgebra.algebraMap_mem _ c⟩ =
          ⟨f - algebraMap N (Func E) c, hgmem⟩ := Subtype.ext rfl
      rwa [heq] at h
    have hne : f - algebraMap N (Func E) c ≠ 0 :=
      sub_ne_zero.mpr (fun h => hfeq h.symm)
    have hinv_not : (f - algebraMap N (Func E) c)⁻¹ ∉ MotC2.infPlace E := by
      intro hinv
      have hprod : (⟨f - algebraMap N (Func E) c, hgmem⟩ : ↥(MotC2.infPlace E)) *
          ⟨(f - algebraMap N (Func E) c)⁻¹, hinv⟩ ∈
          IsLocalRing.maximalIdeal ↥(MotC2.infPlace E) :=
        Ideal.mul_mem_right _ _ hgm
      have heq : (⟨f - algebraMap N (Func E) c, hgmem⟩ : ↥(MotC2.infPlace E)) *
          ⟨(f - algebraMap N (Func E) c)⁻¹, hinv⟩ = 1 := by
        ext
        simp only [Subalgebra.coe_mul, Subalgebra.coe_one]
        exact mul_inv_cancel₀ hne
      rw [heq] at hprod
      exact (IsLocalRing.notMem_maximalIdeal.mpr isUnit_one) hprod
    have hord0 : ordOfPlace E (MotC2.infPlace E) H.infRat (f - algebraMap N (Func E) c) ≠ 0 := by
      intro h0
      have hinv_ord : ordOfPlace E (MotC2.infPlace E) H.infRat
          (f - algebraMap N (Func E) c)⁻¹ = 0 := by
        rw [H.ord_inv (MotC2.infPlace E) H.infRat _ hne, h0, neg_zero]
      exact hinv_not ((H.ord_nonneg (MotC2.infPlace E) H.infRat _).mp
        (le_of_eq hinv_ord.symm))
    have hordge : 0 ≤ ordOfPlace E (MotC2.infPlace E) H.infRat (f - algebraMap N (Func E) c) :=
      (H.ord_nonneg (MotC2.infPlace E) H.infRat _).mpr hgmem
    exact ⟨hne, by omega⟩

/-- The quadratic `quad E a` is non-zero (its leading coefficient is `1`). -/
lemma quad_ne_zero (E : WeierstrassCurve N) (a : N) : quad E a ≠ 0 := by
  intro h
  have hc := congrArg (fun p : Polynomial N => p.coeff 2) h
  simp only [quad, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow_self,
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C] at hc
  norm_num at hc

/-- A point `(a,b)` of the curve is a root of the quadratic `quad E a`. -/
lemma isRoot_quad_of_equation (E : WeierstrassCurve N) {a b : N} (h : Equation E a b) :
    (quad E a).IsRoot b := by
  have hq : Polynomial.eval b (quad E a) =
      b ^ 2 + (E.a₁ * a + E.a₃) * b - (a ^ 3 + E.a₂ * a ^ 2 + E.a₄ * a + E.a₆) := by
    simp only [quad, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  rw [Polynomial.IsRoot.def, hq]
  linear_combination (norm := first | refl_ring1 | ring1) (equation_iff (W := E) a b).mp h

/-- The place of a rational affine point belongs to the fibre of `x` over its `x`-coordinate. -/
lemma mem_fibrePlaces (E : WeierstrassCurve N) [E.IsElliptic] (a b : N) (h : Equation E a b)
    (hS : MotC2.IsRatPlace E (MotC2.affPlaceAt E a b)) :
    (⟨MotC2.affPlaceAt E a b, hS⟩ : Place N E) ∈ fibrePlaces E a := by
  classical
  unfold fibrePlaces
  rw [Finset.mem_biUnion]
  refine ⟨b, ?_, ?_⟩
  · rw [Multiset.mem_toFinset, Polynomial.mem_roots (quad_ne_zero E a)]
    exact isRoot_quad_of_equation E h
  · rw [dif_pos h]
    exact Finset.mem_singleton.mpr (Subtype.ext rfl)

/-- The order at a place is unchanged when the place is written with a different proof. -/
lemma ordP_congr (E : WeierstrassCurve N) {Q Q' : Place N E} (h : Q.1 = Q'.1) (f : Func E) :
    ordP E Q f = ordP E Q' f := by
  obtain ⟨S, hS⟩ := Q
  obtain ⟨S', hS'⟩ := Q'
  simp only at h
  subst h
  show ordOfPlace E S hS f = ordOfPlace E S hS' f
  rw [Subsingleton.elim hS hS']

/-- `supportAff` with an arbitrary proof that the affine place is rational. -/
lemma supportAff' (E : WeierstrassCurve N) [E.IsElliptic] (H : H1Data N E)
    (γ : CoordinateRing E) (hγ : γ ≠ 0) (a b : N) (h : Nonsingular E a b)
    (hS : MotC2.IsRatPlace E (MotC2.affPlaceAt E a b)) :
    0 ≤ ordOfPlace E (MotC2.affPlaceAt E a b) hS (algebraMap (CoordinateRing E) (Func E) γ) ∧
      (0 < ordOfPlace E (MotC2.affPlaceAt E a b) hS (algebraMap (CoordinateRing E) (Func E) γ) →
        (Algebra.norm (Polynomial N) γ).IsRoot a) :=
  Subsingleton.elim (MotC2.AffPlace N E a b h).1 hS ▸ supportAff E H γ hγ a b h

/-- **The support of an element of the coordinate ring.**  If `γ ∈ N[E]` is non-zero, then at
every rational place where `algebraMap γ` is not a unit the place is either the point at
infinity or lies above a root of the norm of `γ`. -/
lemma suppAlg (E : WeierstrassCurve N) [E.IsElliptic] (H : H1Data N E) [DecidableEq N]
    (γ : CoordinateRing E) (hγ : γ ≠ 0) :
    ∀ Q : Place N E, ordP E Q (algebraMap (CoordinateRing E) (Func E) γ) ≠ 0 →
      Q.1 = MotC2.infPlace E ∨
        ∃ a ∈ (Algebra.norm (Polynomial N) γ).roots.toFinset, Q ∈ fibrePlaces E a := by
  classical
  haveI : Module.Finite (Polynomial N) (CoordinateRing E) :=
    Module.Finite.of_basis (CoordinateRing.basis E)
  intro Q hQ
  by_cases hQinf : Q.1 = MotC2.infPlace E
  · exact Or.inl hQinf
  · rcases Classification N E Q.1 Q.2 with h | ⟨a, b, hns, hS⟩
    · exact absurd h hQinf
    · refine Or.inr ?_
      -- transport the order to the place equipped with the `AffPlace` proof
      let Q' : Place N E := ⟨MotC2.affPlaceAt E a b, (MotC2.AffPlace N E a b hns).1⟩
      have hord : ordP E Q (algebraMap (CoordinateRing E) (Func E) γ) =
          ordP E Q' (algebraMap (CoordinateRing E) (Func E) γ) := ordP_congr E hS _
      have hpos : 0 < ordP E Q' (algebraMap (CoordinateRing E) (Func E) γ) := by
        have h1 : 0 ≤ ordP E Q' (algebraMap (CoordinateRing E) (Func E) γ) :=
          (supportAff' E H γ hγ a b hns (MotC2.AffPlace N E a b hns).1).1
        rw [← hord] at h1
        omega
      have hroot : (Algebra.norm (Polynomial N) γ).IsRoot a :=
        (supportAff' E H γ hγ a b hns (MotC2.AffPlace N E a b hns).1).2 hpos
      refine ⟨a, ?_, ?_⟩
      · rw [Multiset.mem_toFinset, Polynomial.mem_roots (Algebra.norm_ne_zero_iff.mpr hγ)]
        exact hroot
      · have hQeq : Q = Q' := Subtype.ext hS
        rw [hQeq]
        exact mem_fibrePlaces E a b ((equation_iff_nonsingular (W := E)).mpr hns)
          (MotC2.AffPlace N E a b hns).1

theorem derivMain {N : Type*} [Field N] [IsAlgClosed N] (E : WeierstrassCurve N) [E.IsElliptic]
    (H : Work.MotV.H1Data N E)
    (D : Derivation N (Work.MotC2.Func E) (Work.MotC2.Func E))
    (hDx : D (Work.MotC2.genX E) = 2 * Work.MotC2.genY E +
        algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genX E +
        algebraMap N (Work.MotC2.Func E) E.a₃)
    (hDy : D (Work.MotC2.genY E) = 3 * (Work.MotC2.genX E) ^ 2 +
        2 * algebraMap N (Work.MotC2.Func E) E.a₂ * Work.MotC2.genX E +
        algebraMap N (Work.MotC2.Func E) E.a₄ -
        algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genY E)
    (hb1 : ∀ (S : Subalgebra N (Work.MotC2.Func E)) (hS : Work.MotC2.IsRatPlace E S)
      (f : Work.MotC2.Func E),
      Work.MotV.ordOfPlace E S hS f - 1 ≤ Work.MotV.ordOfPlace E S hS (D f))
    (hb2 : ∀ (S : Subalgebra N (Work.MotC2.Func E)) (hS : Work.MotC2.IsRatPlace E S)
      (f : Work.MotC2.Func E),
      Work.MotV.ordOfPlace E S hS f = 0 → 0 ≤ Work.MotV.ordOfPlace E S hS (D f))
    (hDeg : ∀ (f : Work.MotC2.Func E), f ≠ 0 → ∀ S : Finset (Work.MotV.Place N E),
      (∀ Q : Work.MotV.Place N E, Work.MotV.ordP E Q f ≠ 0 → Q ∈ S) →
        Work.MotV.ordSum E S f = 0)
    (r : Work.MotC2.Func E) (hDr : D r ≠ 0) (S : Finset (Work.MotV.Place N E))
    (hS : ∀ Q : Work.MotV.Place N E, Q ∉ S → Work.MotV.ordP E Q r = 0 ∧
      Work.MotV.ordP E Q (r - 1) = 0 ∧ Work.MotV.ordP E Q (D r) = 0)
    (hdiv : ∀ Q ∈ S, 5 ∣ Work.MotV.ordP E Q (r * (r - 1))) :
    ∃ c : N, algebraMap N (Work.MotC2.Func E) c = r := by
  classical
  -- the Hurwitz count: `r` is a unit at every rational place
  have hcount : ∀ Q : Place N E, ordP E Q r = 0 :=
    derivCount E H D hb1 hb2 hDeg r hDr S hS hdiv
  have hreg : ∀ Q : Place N E, 0 ≤ ordP E Q r := fun Q => le_of_eq (hcount Q).symm
  have hr_mem : r ∈ MotC2.infPlace E :=
    (H.ord_nonneg (MotC2.infPlace E) H.infRat r).mp (hreg ⟨MotC2.infPlace E, H.infRat⟩)
  obtain ⟨c, hc | hc⟩ := exists_const_or_ord_pos E H r hr_mem
  · exact ⟨c, hc⟩
  · -- otherwise `r - c` is regular everywhere with a zero at infinity, contradicting that the
    -- degree of the divisor of a function is zero
    exfalso
    have hg0 : r - algebraMap N (Func E) c ≠ 0 := hc.1
    have hcpos : 0 < ordOfPlace E (MotC2.infPlace E) H.infRat (r - algebraMap N (Func E) c) :=
      hc.2
    have hg_reg : ∀ Q : Place N E, 0 ≤ ordP E Q (r - algebraMap N (Func E) c) := by
      intro Q
      have hsum_eq : r + (-(algebraMap N (Func E) c)) = r - algebraMap N (Func E) c := by ring
      have h1 := H.ord_add Q.1 Q.2 r (-(algebraMap N (Func E) c)) (by rw [hsum_eq]; exact hg0)
      rw [hsum_eq] at h1
      have h3 : (0 : ℤ) ≤ ordOfPlace E Q.1 Q.2 r := hreg Q
      have h2 : (0 : ℤ) ≤ ordOfPlace E Q.1 Q.2 (-(algebraMap N (Func E) c)) := by
        rw [← map_neg (algebraMap N (Func E)) c]
        exact le_ordOfPlace_const E H Q.1 Q.2 (-c)
      exact le_trans (le_min h3 h2) h1
    -- write `r = α / β` and `r - c = (α - cβ) / β`
    obtain ⟨α, β, hβmem, hαβ⟩ := IsFractionRing.div_surjective (CoordinateRing E) r
    have hβ0 : β ≠ 0 := fun h => (mem_nonZeroDivisors_iff_ne_zero.mp hβmem) h
    let γ₁ : CoordinateRing E := α - algebraMap N (CoordinateRing E) c * β
    let γ₂ : CoordinateRing E := β
    have hγ₂0 : γ₂ ≠ 0 := hβ0
    have haβ : algebraMap (CoordinateRing E) (Func E) β ≠ 0 :=
      fun h => hβ0 (IsFractionRing.injective (CoordinateRing E) (Func E) (by rw [h, map_zero]))
    have haγ₂ : algebraMap (CoordinateRing E) (Func E) γ₂ ≠ 0 := haβ
    have hγ₁0 : γ₁ ≠ 0 := by
      intro h
      have hr_eq : r = algebraMap N (Func E) c := by
        have hαeq : α = algebraMap N (CoordinateRing E) c * β := by
          change α - algebraMap N (CoordinateRing E) c * β = 0 at h
          exact sub_eq_zero.mp h
        rw [← hαβ, hαeq, map_mul,
          IsScalarTower.algebraMap_apply N (CoordinateRing E) (Func E)]
        field_simp
      exact hg0 (by rw [hr_eq]; ring)
    have haγ₁ : algebraMap (CoordinateRing E) (Func E) γ₁ ≠ 0 :=
      fun h => hγ₁0 (IsFractionRing.injective (CoordinateRing E) (Func E) (by rw [h, map_zero]))
    have hsplit : r - algebraMap N (Func E) c =
        algebraMap (CoordinateRing E) (Func E) γ₁ *
          (algebraMap (CoordinateRing E) (Func E) γ₂)⁻¹ := by
      have hγ₁' : algebraMap (CoordinateRing E) (Func E) γ₁ =
          algebraMap (CoordinateRing E) (Func E) α -
            algebraMap N (Func E) c * algebraMap (CoordinateRing E) (Func E) β := by
        simp only [γ₁, map_sub, map_mul,
          IsScalarTower.algebraMap_apply N (CoordinateRing E) (Func E)]
      rw [← hαβ, hγ₁']
      dsimp only [γ₂]
      rw [div_eq_mul_inv, sub_mul, mul_assoc, mul_inv_cancel₀ haβ, mul_one]
    -- the support of `r - c` is contained in a finite set
    have hsupp : ∀ Q : Place N E, ordP E Q (r - algebraMap N (Func E) c) ≠ 0 →
        Q ∈ insert ⟨MotC2.infPlace E, H.infRat⟩
          ((((Algebra.norm (Polynomial N) γ₁).roots.toFinset).biUnion
              fun a => fibrePlaces E a) ∪
            (((Algebra.norm (Polynomial N) γ₂).roots.toFinset).biUnion
              fun a => fibrePlaces E a)) := by
      intro Q hQ
      have hval : ordP E Q (r - algebraMap N (Func E) c) =
          ordOfPlace E Q.1 Q.2 (algebraMap (CoordinateRing E) (Func E) γ₁) -
            ordOfPlace E Q.1 Q.2 (algebraMap (CoordinateRing E) (Func E) γ₂) := by
        simp only [ordP]
        rw [hsplit, H.ord_mul Q.1 Q.2 _ _ haγ₁ (inv_ne_zero haγ₂),
          H.ord_inv Q.1 Q.2 _ haγ₂]
        first | refl_ring1 | ring
      have hzero : ordOfPlace E Q.1 Q.2 (algebraMap (CoordinateRing E) (Func E) γ₁) ≠ 0 ∨
          ordOfPlace E Q.1 Q.2 (algebraMap (CoordinateRing E) (Func E) γ₂) ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hQ (by rw [hval, hcon.1, hcon.2, sub_zero])
      have hsupp₁ := suppAlg E H γ₁ hγ₁0 Q
      have hsupp₂ := suppAlg E H γ₂ hγ₂0 Q
      rw [Finset.mem_insert]
      rcases hzero with h1 | h2
      · rcases hsupp₁ h1 with hinf | ⟨a, ha, hQa⟩
        · exact Or.inl (Subtype.ext hinf)
        · exact Or.inr (Finset.mem_union.mpr (Or.inl (Finset.mem_biUnion.mpr ⟨a, ha, hQa⟩)))
      · rcases hsupp₂ h2 with hinf | ⟨a, ha, hQa⟩
        · exact Or.inl (Subtype.ext hinf)
        · exact Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨a, ha, hQa⟩)))
    -- the sum of the orders of `r - c` over that finite set is zero, and all terms are
    -- non-negative
    have hsum := hDeg (r - algebraMap N (Func E) c) hg0 _ hsupp
    rw [ordSum] at hsum
    have hall : ∀ Q ∈ insert ⟨MotC2.infPlace E, H.infRat⟩
        ((((Algebra.norm (Polynomial N) γ₁).roots.toFinset).biUnion
            fun a => fibrePlaces E a) ∪
          (((Algebra.norm (Polynomial N) γ₂).roots.toFinset).biUnion
            fun a => fibrePlaces E a)),
        ordP E Q (r - algebraMap N (Func E) c) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun Q _ => hg_reg Q)).mp hsum
    have hzero_inf : ordP E ⟨MotC2.infPlace E, H.infRat⟩ (r - algebraMap N (Func E) c) = 0 :=
      hall _ (Finset.mem_insert_self _ _)
    exact (ne_of_gt hcpos) hzero_inf

end

end Work.MotV
