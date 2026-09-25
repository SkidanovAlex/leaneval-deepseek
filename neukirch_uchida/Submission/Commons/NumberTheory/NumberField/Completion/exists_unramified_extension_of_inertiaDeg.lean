import Mathlib
import Submission.Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
import Submission.Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
import Submission.Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_le_finrank
import Submission.Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.FieldTheory.Polynomial.exists_monic_irreducible_of_natDegree
import Submission.Commons.LinearAlgebra.FiniteDimensional.natDegree_minpoly_le_finrank
import Submission.Commons.RingTheory.Polynomial.exists_monic_lift_of_surjective

open scoped NumberField IntermediateField
open Polynomial
open IsDedekindDomain.HeightOneSpectrum

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

namespace Commons.NumberTheory.NumberField.Completion

/-!
# Gap A: an unramified extension of prescribed inertia degree at a place

Given a number field `L`, a finite place `q` of `𝓞 L` and `n ≥ 1`, we build a finite extension
`L' / L` together with a place `q'` over `q` such that `e(q'|q) = 1`, `f(q'|q) = n` and
`[L' : L] = n`.  Equivalently `L'_{q'} / L_q` is the unramified extension of degree `n`.

## Construction

* `𝔽 := 𝓞 L ⧸ q` is a finite field;
* choose `g ∈ 𝔽[X]` monic irreducible of degree `n`
  (`Commons.FieldTheory.Polynomial.exists_monic_irreducible_of_natDegree`);
* lift the coefficients of `g` to `𝓞 L`, obtaining a monic `f ∈ (𝓞 L)[X]` with `f mod q = g`
  (`Commons.RingTheory.Polynomial.exists_monic_lift_of_surjective`);
* let `θ` be a root of `f` in an algebraic closure of `L` and put `L' := L⟮θ⟯`; this is a number
  field with `[L' : L] = deg (minpoly L θ) ≤ n`;
* choose `q'` over `q` (`Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver`);
  then `f(q'|q) ≥ n` because the reduction `θ̄` is a root of the irreducible `g`
  (`natDegree_le_inertiaDeg_of_aeval_eq_zero`), while
  `e(q'|q) · f(q'|q) = [L'_{q'} : L_q] ≤ [L' : L] ≤ n`
  (`finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg`,
  `finrank_adicCompletion_le_finrank`); hence `e = 1` and `f = n`.
-/

/-- Variant of `natDegree_minpoly_le_finrank` with a `Module.Finite` hypothesis (which avoids an
expensive instance search when the base is a residue ring). -/
theorem natDegree_minpoly_le_finrank_of_moduleFinite {F E : Type*} [Field F] [Field E]
    [Algebra F E] [Module.Finite F E] (y : E) :
    (minpoly F y).natDegree ≤ Module.finrank F E := by
  haveI : FiniteDimensional F E := ‹Module.Finite F E›
  exact Commons.LinearAlgebra.FiniteDimensional.natDegree_minpoly_le_finrank y

/-- **The residue-field degree bound.**  Let `p ⊆ R` and `q ⊆ S` be maximal ideals of commutative
rings with `q` lying over `p`, let `f ∈ R[X]` be a monic polynomial whose reduction `g` modulo `p`
is irreducible, and let `θ ∈ S` be a root of `f`.  Then `deg g ≤ [S/q : R/p]`, the inertia degree
of `q` over `R`.

Equivalently: `[S/q : R/p]` is at least the degree of the irreducible polynomial `g`, since the
image of `θ` in `S/q` has `minpoly` equal to `g`. -/
theorem natDegree_le_inertiaDeg_of_aeval_eq_zero
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsMaximal] (q : Ideal S) [q.IsMaximal] [q.LiesOver p]
    (f : Polynomial R) (g : Polynomial (R ⧸ p)) (hgmonic : g.Monic) (hgirr : Irreducible g)
    (hmap : f.map (Ideal.Quotient.mk p) = g)
    (θ : S) (hθ : Polynomial.aeval θ f = 0)
    [Finite (S ⧸ q)] :
    g.natDegree ≤ q.inertiaDeg R := by
  classical
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  letI : Field (S ⧸ q) := Ideal.Quotient.field q
  let y : S ⧸ q := Ideal.Quotient.mk q θ
  have hy : Polynomial.aeval y g = 0 := by
    have key : Polynomial.aeval y g =
        (Ideal.Quotient.mk q) (Polynomial.eval₂ (algebraMap R S) θ f) := by
      rw [Polynomial.aeval_def, ← hmap, Polynomial.eval₂_map]
      have hcomp : (algebraMap (R ⧸ p) (S ⧸ q)).comp (Ideal.Quotient.mk p) =
          (Ideal.Quotient.mk q).comp (algebraMap R S) := by
        ext r
        rw [RingHom.comp_apply, RingHom.comp_apply,
          Ideal.Quotient.algebraMap_mk_of_liesOver]
      rw [hcomp, ← Polynomial.eval₂_map (algebraMap R S) (Ideal.Quotient.mk q) θ]
      rw [Polynomial.eval₂_hom, ← Polynomial.eval_map]
    rw [key, ← Polynomial.aeval_def, hθ, map_zero]
  have hmin : g = minpoly (R ⧸ p) y :=
    minpoly.eq_of_irreducible_of_monic (A := R ⧸ p) (B := S ⧸ q) (x := y) (p := g)
      hgirr hy hgmonic
  rw [hmin]
  haveI : Module.Finite (R ⧸ p) (S ⧸ q) := Module.Finite.of_finite
  have h1 : (minpoly (R ⧸ p) y).natDegree ≤ Module.finrank (R ⧸ p) (S ⧸ q) :=
    natDegree_minpoly_le_finrank_of_moduleFinite y
  have h2 : Module.finrank (R ⧸ p) (S ⧸ q) = q.inertiaDeg R :=
    (Ideal.inertiaDeg_eq_of_isMaximal p q).symm
  omega

/-- **Gap A: the unramified extension of prescribed degree at a place.**

For a number field `L`, a finite place `q` of `𝓞 L` and `n ≥ 1`, there is a finite extension
`L' / L` together with a place `q'` over `q` such that the local extension `L'_{q'} / L_q` is
**unramified of degree `n`**: `e(q'|q) = 1`, `f(q'|q) = n` and in fact `[L' : L] = n`. -/
theorem exists_unramified_extension_of_inertiaDeg {L : Type} [Field L] [NumberField L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) (n : ℕ) (hn : 0 < n) :
    ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L')
      (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L')),
      q'.asIdeal.LiesOver q.asIdeal ∧
      q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers L) = 1 ∧
      q'.asIdeal.inertiaDeg (NumberField.RingOfIntegers L) = n ∧
      Module.finrank L L' = n := by
  classical
  let R := 𝓞 L
  haveI hfinq : Finite (R ⧸ q.asIdeal) := finite_quotient_heightOneSpectrum q
  letI : Field (R ⧸ q.asIdeal) := Ideal.Quotient.field q.asIdeal
  haveI : Fintype (R ⧸ q.asIdeal) := Fintype.ofFinite _
  obtain ⟨g, hgmonic, hgirr, hgdeg⟩ :=
    Commons.FieldTheory.Polynomial.exists_monic_irreducible_of_natDegree (F := R ⧸ q.asIdeal) n hn
  obtain ⟨f, hfmonic, hfdeg, hfmap⟩ :=
    Commons.RingTheory.Polynomial.exists_monic_lift_of_surjective
      (Ideal.Quotient.mk q.asIdeal) Ideal.Quotient.mk_surjective g hgmonic
  have hfndeg : f.natDegree = n := hfdeg.trans hgdeg
  let Ω := AlgebraicClosure L
  let φ : R →+* Ω := algebraMap R Ω
  have hφlead : φ f.leadingCoeff ≠ 0 := by
    rw [hfmonic.leadingCoeff, map_one]; exact one_ne_zero
  have hfdeg' : (f.map φ).degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree (hfmonic.map φ).ne_zero,
      Polynomial.natDegree_map_of_leadingCoeff_ne_zero φ hφlead, hfndeg]
    exact_mod_cast hn.ne'
  obtain ⟨θ, hθ⟩ := IsAlgClosed.exists_root (f.map φ) hfdeg'
  have hθ0 : f.eval₂ φ θ = 0 := by rw [← Polynomial.eval_map φ θ]; exact hθ
  have hintR : IsIntegral R θ :=
    ⟨f, hfmonic, by simpa only [Polynomial.aeval_def, φ] using hθ0⟩
  let Lst : IntermediateField L Ω := L⟮θ⟯
  have hmem : θ ∈ Lst := IntermediateField.mem_adjoin_simple_self L θ
  have hcompRL : (algebraMap L Ω).comp (algebraMap R L) = algebraMap R Ω := by
    ext x; exact IsScalarTower.algebraMap_apply R L Ω x
  have hL0 : Polynomial.aeval θ (f.map (algebraMap R L)) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcompRL]
    simpa only [φ] using hθ0
  have hintL : IsIntegral L θ := ⟨f.map (algebraMap R L), hfmonic.map _, hL0⟩
  haveI hfd : FiniteDimensional L Lst := IntermediateField.adjoin.finiteDimensional hintL
  haveI hnum : NumberField Lst := numberField_of_intermediateField (K := L) (K' := Ω) Lst
  obtain ⟨q', hq'⟩ := exists_heightOneSpectrum_liesOver (K := L) (L := Lst) q
  haveI hfinq' : Finite (𝓞 ↥Lst ⧸ q'.asIdeal) := finite_quotient_heightOneSpectrum q'
  have hcast : (algebraMap ↥Lst Ω) (⟨θ, hmem⟩ : ↥Lst) = θ := rfl
  -- ## the polynomial relation for `θ`
  have hA : Polynomial.aeval (⟨θ, hmem⟩ : ↥Lst) (f.map (algebraMap R L)) = 0 := by
    have h1 := Polynomial.map_aeval_eq_aeval_map (R := L) (S := ↥Lst) (T := Ω) (U := Ω)
      (φ := algebraMap L Ω) (ψ := algebraMap ↥Lst Ω) (by ext x; rfl)
      (f.map (algebraMap R L)) ⟨θ, hmem⟩
    have h2 : (algebraMap ↥Lst Ω)
        (Polynomial.aeval (⟨θ, hmem⟩ : ↥Lst) (f.map (algebraMap R L))) = 0 := by
      rw [h1, hcast]
      have h3 : (f.map (algebraMap R L)).map (algebraMap L Ω) = f.map (algebraMap R Ω) := by
        rw [Polynomial.map_map, hcompRL]
      rw [h3, Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id]
      exact hθ
    exact (algebraMap ↥Lst Ω).injective (by rw [h2, map_zero])
  have hA1 : Polynomial.aeval (⟨θ, hmem⟩ : ↥Lst) f = 0 := by
    rw [Polynomial.aeval_def,
      show algebraMap R ↥Lst = (algebraMap L ↥Lst).comp (algebraMap R L) from rfl,
      ← Polynomial.eval₂_map]
    exact hA
  have hIntA : IsIntegral (𝓞 L) (⟨θ, hmem⟩ : ↥Lst) := ⟨f, hfmonic, hA1⟩
  have hintZΩ : IsIntegral ℤ θ := isIntegral_trans (R := ℤ) (A := 𝓞 L) θ hintR
  have hintZ : IsIntegral ℤ (⟨θ, hmem⟩ : ↥Lst) :=
    IsIntegral.tower_bot (R := ℤ) (A := ↥Lst) (B := Ω) (algebraMap ↥Lst Ω).injective
      (by rw [hcast]; exact hintZΩ)
  let θ' : 𝓞 ↥Lst := ⟨⟨θ, hmem⟩, hintZ⟩
  have hθ'map : algebraMap (𝓞 ↥Lst) ↥Lst θ' = ⟨θ, hmem⟩ := rfl
  have hθ'aeval : Polynomial.aeval θ' f = 0 := by
    apply NumberField.RingOfIntegers.coe_injective (K := ↥Lst)
    rw [map_zero]
    have h5 := Polynomial.map_aeval_eq_aeval_map (R := R) (S := 𝓞 ↥Lst) (T := ↥Lst) (U := ↥Lst)
      (φ := algebraMap R ↥Lst) (ψ := algebraMap (𝓞 ↥Lst) ↥Lst)
      (by ext x; rfl) f θ'
    rw [h5, hθ'map]
    have h6 : f.map (algebraMap R ↥Lst) = (f.map (algebraMap R L)).map (algebraMap L ↥Lst) := by
      rw [Polynomial.map_map]
      congr 1
    rw [h6, ← Polynomial.aeval_eq_aeval_map (R := L) (S := ↥Lst) (T := ↥Lst)
      (φ := algebraMap L ↥Lst) (by ext x; rfl) (f.map (algebraMap R L)) ⟨θ, hmem⟩]
    exact hA
  -- ## the residue-field bound `n ≤ f`
  have hres : n ≤ q'.asIdeal.inertiaDeg R := by
    rw [← hgdeg]
    exact natDegree_le_inertiaDeg_of_aeval_eq_zero (R := R) (S := 𝓞 ↥Lst)
      q.asIdeal q'.asIdeal f g hgmonic hgirr hfmap θ' hθ'aeval
  -- ## the upper bound `[L' : L] ≤ n`
  have hLst_le : Module.finrank L ↥Lst ≤ n := by
    have hmin_dvd : minpoly L θ ∣ f.map (algebraMap R L) := minpoly.dvd L θ hL0
    have hne : f.map (algebraMap R L) ≠ 0 := (hfmonic.map _).ne_zero
    have h1 : (minpoly L θ).natDegree ≤ (f.map (algebraMap R L)).natDegree :=
      Polynomial.natDegree_le_of_dvd hmin_dvd hne
    have h2 : (f.map (algebraMap R L)).natDegree = n := by
      rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero]
      · exact hfndeg
      · rw [hfmonic.leadingCoeff, map_one]; exact one_ne_zero
    rw [IntermediateField.adjoin.finrank (K := L) hintL]
    omega
  -- ## the numerical conclusion
  letI : Algebra (q.adicCompletion L) (q'.adicCompletion ↥Lst) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q q' hq')
  have hcompl_le : Module.finrank (q.adicCompletion L) (q'.adicCompletion ↥Lst) ≤
      Module.finrank L ↥Lst :=
    finrank_adicCompletion_le_finrank (K := L) (L := ↥Lst) q q' hq'
  have hfin_le : Module.finrank (q.adicCompletion L) (q'.adicCompletion ↥Lst) ≤ n :=
    hcompl_le.trans hLst_le
  have hmul := finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg (K := L) (L := ↥Lst) q q' hq'
  have hepos : 0 < q'.asIdeal.ramificationIdx R := by
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx q.asIdeal q'.asIdeal q.ne_bot]
    exact Nat.pos_of_ne_zero
      (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver q'.asIdeal q.ne_bot)
  have hfqpos : 0 < q'.asIdeal.inertiaDeg R := lt_of_lt_of_le hn hres
  have h1 : q'.asIdeal.ramificationIdx R * q'.asIdeal.inertiaDeg R ≤ n := by
    rw [hmul]; exact hfin_le
  have he1 : q'.asIdeal.ramificationIdx R = 1 := by
    have hle : q'.asIdeal.ramificationIdx R ≤ 1 :=
      Nat.le_of_mul_le_mul_right (le_trans h1 (by rw [one_mul]; exact hres)) hfqpos
    omega
  have hfq : q'.asIdeal.inertiaDeg R = n := by
    have := h1
    rw [he1, one_mul] at this
    omega
  have hfrank : Module.finrank L ↥Lst = n := by
    have h2 : Module.finrank (q.adicCompletion L) (q'.adicCompletion ↥Lst) = n := by
      rw [← hmul, he1, one_mul, hfq]
    omega
  exact ⟨Lst, inferInstance, inferInstance, inferInstance, q', hq', he1, hfq, hfrank⟩

end Commons.NumberTheory.NumberField.Completion
