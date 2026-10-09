import Mathlib
import Submission.NK.Chebotarev.ExistsSqrtInCyclotomic
import Submission.NK.Chebotarev.CyclotomicModelOfCyclotomic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The quadratic case of Kronecker–Weber

A quadratic Galois extension `L/ℚ` is of the form `ℚ(√d)` for a non-square rational `d`, and every
rational has a square root in a cyclotomic field (`NK.Chebotarev.ExistsSqrtInCyclotomic`); hence
`L` is a `CyclotomicModel` at some level `n`.

The two algebraic inputs proved here are

* `NK.Chebotarev.minpoly_eq_X_sq_sub_C`: if `y ^ 2 = algebraMap K E d` with `d` a non-square in
  `K`, then the minimal polynomial of `y` over `K` is `X ^ 2 - C d`;
* `NK.Chebotarev.poly_eq_X_sq_add_C_mul_X_add_C`: a monic quadratic polynomial over `ℚ` has the
  form `X ^ 2 + C b * X + C c`.

Together with the primitive element computation of `L = ℚ(√d)`, they give the theorem.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped IntermediateField
open Polynomial

namespace NK.Chebotarev

universe u

/-- A monic polynomial over `ℚ` whose `natDegree` is `2` has the form `X ^ 2 + b * X + c`. -/
lemma poly_eq_X_sq_add_C_mul_X_add_C (p : ℚ[X]) (hm : p.Monic) (h2 : p.natDegree = 2) :
    p = X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
  conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow p]
  rw [h2, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  have hc2 : p.coeff 2 = 1 := by rw [← h2]; exact hm.coeff_natDegree
  rw [hc2]
  simp only [map_one, one_mul, pow_zero, mul_one, pow_one, zero_add]
  ring

/-- **The minimal polynomial of a square root.**  If `y ^ 2 = d` and `d` is not a square in `K`,
then `minpoly K y = X ^ 2 - C d`. -/
lemma minpoly_eq_X_sq_sub_C {K E : Type*} [Field K] [Field E] [Algebra K E] (d : K) (y : E)
    (hd : ∀ a : K, a ^ 2 ≠ d) (hy : y ^ 2 = algebraMap K E d) :
    minpoly K y = X ^ 2 - C d := by
  have hirr : Irreducible (X ^ 2 - C d : K[X]) :=
    (X_pow_sub_C_irreducible_iff_of_prime (K := K) (p := 2) (by norm_num) (a := d)).mpr hd
  have hmonic : (X ^ 2 - C d : K[X]).Monic := Polynomial.monic_X_pow_sub_C d (by norm_num)
  have hroot : Polynomial.aeval y (X ^ 2 - C d : K[X]) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hy, sub_self]
  exact (minpoly.eq_of_irreducible_of_monic hirr hroot hmonic).symm

theorem KroneckerWeberQuadratic {L : Type u} [Field L] [NumberField L] [IsGalois ℚ L]
    (h : Module.finrank ℚ L = 2) :
    ∃ (n : ℕ) (_ : 0 < n), Nonempty (NK.Chebotarev.CyclotomicModel.{u} L n) := by
  -- ## Step 1: `L` contains an element which is not rational
  have hxex : ∃ x : L, x ∉ Set.range (algebraMap ℚ L) := by
    have hbot_top : (⊥ : IntermediateField ℚ L) ≠ ⊤ := by
      intro hc
      have h1 : Module.finrank ℚ (⊥ : IntermediateField ℚ L) = 1 :=
        IntermediateField.finrank_bot
      rw [hc, IntermediateField.finrank_top', h] at h1
      norm_num at h1
    by_contra hcon
    have hcon' : ∀ z : L, z ∈ Set.range (algebraMap ℚ L) := by
      intro z; by_contra hz; exact hcon ⟨z, hz⟩
    exact hbot_top (top_le_iff.mp fun z _ => by
      rw [IntermediateField.mem_bot]; exact hcon' z)
  obtain ⟨x, hx⟩ := hxex
  have hxint : IsIntegral ℚ x := IsIntegral.of_finite ℚ x
  haveI : IsSimpleOrder (IntermediateField ℚ L) :=
    IntermediateField.isSimpleOrder_of_finrank_prime ℚ L (by rw [h]; norm_num)
  have hne_bot : (ℚ⟮x⟯ : IntermediateField ℚ L) ≠ ⊥ := by
    intro hb
    apply hx
    rw [← IntermediateField.mem_bot, ← hb]
    exact IntermediateField.mem_adjoin_simple_self ℚ x
  have htop_x : (ℚ⟮x⟯ : IntermediateField ℚ L) = ⊤ := by
    rcases eq_bot_or_eq_top (ℚ⟮x⟯ : IntermediateField ℚ L) with hb | ht
    · exact absurd hb hne_bot
    · exact ht
  have hfinx : Module.finrank ℚ ↥(ℚ⟮x⟯ : IntermediateField ℚ L) = 2 := by
    rw [htop_x, IntermediateField.finrank_top', h]
  -- ## Step 2: `L = ℚ(√d)` for a non-square rational `d`
  have hpdeg : (minpoly ℚ x).natDegree = 2 := by
    rw [← IntermediateField.adjoin.finrank hxint, hfinx]
  have hpmonic : (minpoly ℚ x).Monic := minpoly.monic hxint
  have hpform : minpoly ℚ x =
      X ^ 2 + C ((minpoly ℚ x).coeff 1) * X + C ((minpoly ℚ x).coeff 0) :=
    poly_eq_X_sq_add_C_mul_X_add_C (minpoly ℚ x) hpmonic hpdeg
  set b : ℚ := (minpoly ℚ x).coeff 1 with hb
  set c : ℚ := (minpoly ℚ x).coeff 0 with hc
  have hxroot : x ^ 2 + algebraMap ℚ L b * x + algebraMap ℚ L c = 0 := by
    have hh := minpoly.aeval ℚ x
    rw [hpform] at hh
    simpa [hb, hc] using hh
  set d : ℚ := b ^ 2 - 4 * c with hd
  set y : L := 2 * x + algebraMap ℚ L b with hy
  have hynotmem : y ∉ Set.range (algebraMap ℚ L) := by
    rintro ⟨a, ha⟩
    apply hx
    have ha' : algebraMap ℚ L a = 2 * x + algebraMap ℚ L b := ha.trans hy
    refine ⟨(a - b) / 2, ?_⟩
    have h2 : (2 : L) * x = algebraMap ℚ L (a - b) := by
      rw [map_sub, ha']
      ring
    have h2ne : (2 : L) ≠ 0 := by norm_num
    rw [map_div₀, map_ofNat, div_eq_iff h2ne, ← h2]
    ring
  have hy2 : y ^ 2 = algebraMap ℚ L d := by
    rw [hy, hd, map_sub, map_pow, map_mul]
    have h4 : algebraMap ℚ L (4 : ℚ) = (4 : L) := by norm_num
    rw [h4]
    linear_combination (norm := ring_nf) 4 * hxroot
  have hdne : ∀ a : ℚ, a ^ 2 ≠ d := by
    intro a ha
    apply hynotmem
    have hsq : y ^ 2 = (algebraMap ℚ L a) ^ 2 := by rw [hy2, ← ha]; push_cast; ring
    have hprod : (y - algebraMap ℚ L a) * (y + algebraMap ℚ L a) = 0 := by
      have hh : (y - algebraMap ℚ L a) * (y + algebraMap ℚ L a)
          = y ^ 2 - (algebraMap ℚ L a) ^ 2 := by ring
      rw [hh, hsq, sub_self]
    rcases mul_eq_zero.mp hprod with hh | hh
    · exact ⟨a, (sub_eq_zero.mp hh).symm⟩
    · exact ⟨-a, by rw [map_neg]; exact (add_eq_zero_iff_eq_neg.mp hh).symm⟩
  -- ## Step 3: embed `√d` in a cyclotomic field
  obtain ⟨S⟩ := NK.Chebotarev.ExistsSqrtInCyclotomic.{u} d
  -- put the canonical `ℚ`-algebra structure on `S.F`, so that the instances match those of
  -- `CyclotomicModel`
  letI hCanF : Algebra ℚ S.F :=
    @DivisionRing.toRatAlgebra S.F S.fieldF.toDivisionRing S.numberFieldF.to_charZero
  have hA : S.algebraF = hCanF := Subsingleton.elim _ _
  have hxsq : S.x ^ 2 = algebraMap ℚ S.F d := hA ▸ S.x_sq
  have hz_int : IsIntegral ℚ S.x := IsIntegral.of_finite ℚ S.x
  have hminz : minpoly ℚ S.x = X ^ 2 - C d := minpoly_eq_X_sq_sub_C d S.x hdne hxsq
  let E : IntermediateField ℚ S.F := ℚ⟮S.x⟯
  have hfinE : Module.finrank ℚ ↥E = 2 := by
    rw [show (E : IntermediateField ℚ S.F) = ℚ⟮S.x⟯ from rfl]
    rw [IntermediateField.adjoin.finrank hz_int, hminz, Polynomial.natDegree_X_pow_sub_C]
  haveI : Algebra.IsQuadraticExtension ℚ ↥E := ⟨hfinE⟩
  haveI galE : IsGalois ℚ ↥E := Algebra.IsQuadraticExtension.isGalois ℚ _
  -- ## Step 4: the isomorphism `L ≃ₐ[ℚ] E`
  have hy_int : IsIntegral ℚ y := IsIntegral.of_finite ℚ y
  have hminy : minpoly ℚ y = X ^ 2 - C d := minpoly_eq_X_sq_sub_C d y hdne hy2
  have htop_y : (ℚ⟮y⟯ : IntermediateField ℚ L) = ⊤ := by
    rcases eq_bot_or_eq_top (ℚ⟮y⟯ : IntermediateField ℚ L) with hb2 | ht
    · exfalso
      apply hynotmem
      rw [← IntermediateField.mem_bot, ← hb2]
      exact IntermediateField.mem_adjoin_simple_self ℚ y
    · exact ht
  have e1 := (IntermediateField.adjoinRootEquivAdjoin ℚ hy_int).symm.trans
      (AdjoinRoot.algEquivOfEq ℚ (minpoly ℚ y) (X ^ 2 - C d) hminy)
  have e2 := (IntermediateField.adjoinRootEquivAdjoin ℚ hz_int).symm.trans
      (AdjoinRoot.algEquivOfEq ℚ (minpoly ℚ S.x) (X ^ 2 - C d) hminz)
  have eiso := (IntermediateField.topEquiv (F := ℚ) (E := L)).symm |>.trans
      ((IntermediateField.equivOfEq htop_y.symm).trans (e1.trans e2.symm))
  -- ## Step 5: build the model
  have hcyc : IsCyclotomicExtension {S.n} ℚ S.F := hA ▸ S.cycloF
  let model : NK.Chebotarev.CyclotomicModel.{u} L S.n :=
    { F := S.F, fieldF := S.fieldF, numberFieldF := S.numberFieldF,
      cyclotomicF := hcyc, E := E, galoisE := galE, equiv := eiso }
  exact ⟨S.n, S.hn, Nonempty.intro model⟩

end NK.Chebotarev
