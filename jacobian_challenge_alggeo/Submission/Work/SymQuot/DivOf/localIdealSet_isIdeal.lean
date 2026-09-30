import Mathlib
import Submission.Work.SymQuot.DivOf.ChartPt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical
open TensorProduct
open scoped TensorProduct

universe u

namespace Work.SymQuot.DivOf

noncomputable section

/-- **Extension of a ring hom into a field to the tensor product.**

Let `R ⊆ S` be a ring extension (`Algebra R S`), `φ : R →+* F` a ring hom into a field `F`, and
`P` a prime ideal of `S` lying over `ker φ`.  Then there exist a field `L`, a ring hom `Ψ : S →+* L`
and a ring hom `σ : F →+* L` such that `Ψ` restricts to `σ ∘ φ` on `R`.

The field `L` is a residue field of `(S ⧸ P) ⊗[R ⧸ ker φ] F`, which is nontrivial because
`S ⧸ P` and `F` are domains over the domain `R ⧸ ker φ`. -/
theorem exists_field_hom_extension
    {R S F : Type u} [CommRing R] [CommRing S] [Algebra R S] [Field F] (φ : R →+* F)
    (P : Ideal S) (hP : P.IsPrime) (hcomap : Ideal.under R P = RingHom.ker φ) :
    ∃ (L : Type u) (_ : Field L) (Ψ : S →+* L) (σ : F →+* L),
      Ψ.comp (algebraMap R S) = σ.comp φ := by
  haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  let k := R ⧸ RingHom.ker φ
  haveI : IsDomain k := Ideal.Quotient.isDomain (RingHom.ker φ)
  haveI : IsDomain (S ⧸ P) := Ideal.Quotient.isDomain P
  let ρ : k →+* S ⧸ P := Ideal.Quotient.lift (RingHom.ker φ)
      ((Ideal.Quotient.mk P).comp (algebraMap R S))
      (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (by
        have h1 : a ∈ Ideal.under R P := hcomap.symm ▸ ha
        rw [Ideal.under_def] at h1
        exact Ideal.mem_comap.mp h1))
  let σF : k →+* F := Ideal.Quotient.lift (RingHom.ker φ) φ (fun a ha => ha)
  have hρ : Function.Injective ρ := by
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hx' : Ideal.Quotient.mk P (algebraMap R S a) = 0 := hx
    rw [Ideal.Quotient.eq_zero_iff_mem] at hx'
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr]
    rw [← hcomap, Ideal.under_def]
    exact Ideal.mem_comap.mpr hx'
  have hσF : Function.Injective σF := by
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hx' : φ a = 0 := hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (RingHom.mem_ker.mpr hx')
  letI : Algebra k (S ⧸ P) := ρ.toAlgebra
  letI : Algebra k F := σF.toAlgebra
  haveI hnontriv : Nontrivial ((S ⧸ P) ⊗[k] F) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k (S ⧸ P) F hρ hσF
  obtain ⟨m, hm⟩ := Ideal.exists_maximal ((S ⧸ P) ⊗[k] F)
  haveI : m.IsMaximal := hm
  letI : Field ((S ⧸ P) ⊗[k] F ⧸ m) := Ideal.Quotient.field m
  refine ⟨((S ⧸ P) ⊗[k] F) ⧸ m, inferInstance,
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeLeftRingHom.comp (Ideal.Quotient.mk P)),
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight : F →ₐ[k] _).toRingHom, ?_⟩
  ext x
  have h1 : (Ideal.Quotient.mk P) (algebraMap R S x) = ρ (Ideal.Quotient.mk (RingHom.ker φ) x) :=
    (Ideal.Quotient.lift_mk (RingHom.ker φ) ((Ideal.Quotient.mk P).comp (algebraMap R S)) _).symm
  have h2 : φ x = σF (Ideal.Quotient.mk (RingHom.ker φ) x) :=
    (Ideal.Quotient.lift_mk (RingHom.ker φ) φ _).symm
  simp only [RingHom.comp_apply]
  rw [h1, h2]
  exact congrArg (Ideal.Quotient.mk m)
    (congrArg (fun f : k →+* (S ⧸ P) ⊗[k] F => f (Ideal.Quotient.mk (RingHom.ker φ) x))
      Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap)

section Helpers

variable {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {n : ℕ} [NeZero n] [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F}

/-- The `n`-fold coordinate pullbacks are the roots of the characteristic polynomial; in
particular it has degree at most `n`. -/
theorem natDegree_charpoly_le (d : ChartPt C n p) (b : Γ(C.left, d.V)) :
    (charpoly C n d.V b).natDegree ≤ n := by
  rw [charpoly]
  calc (∏ m : Fin n, (Polynomial.X - Polynomial.C (coordPullbackAt C n d.V m b))).natDegree
      ≤ ∑ m : Fin n, (Polynomial.X - Polynomial.C (coordPullbackAt C n d.V m b)).natDegree :=
        Polynomial.natDegree_prod_le Finset.univ _
    _ ≤ ∑ _m : Fin n, (1 : ℕ) := by
        apply Finset.sum_le_sum
        intro m _
        exact Polynomial.natDegree_X_sub_C_le _
    _ = n := by simp

/-- **Evaluating the characteristic polynomial through a ring hom.**

For a ring hom `Ψ : Γ(Cⁿ,Vⁿ) →+* L` and `σ : F →+* L` compatible on the chart ring `A`, the
characteristic polynomial `χ_b` evaluated through `σ` is the evaluation of the characteristic
polynomial of `b` through `Ψ`.  This is the algebraic heart of the ideal property. -/
theorem charpolyValue_map_eq (d : ChartPt C n p) {L : Type u} [Field L]
    (Ψ : Γ((prod C.toOver n).left, d.openOf) →+* L) (σ : F →+* L)
    (h : Ψ.comp (Subring.subtype d.chartRingOf) = σ.comp d.φ) (b : Γ(C.left, d.V)) :
    Polynomial.map σ (d.charpolyValue b) = Polynomial.map Ψ (charpoly C n d.V b) := by
  have hdeg : (charpoly C n d.V b).natDegree < n + 1 :=
    lt_of_le_of_lt (natDegree_charpoly_le d b) (Nat.lt_succ_self n)
  have hsum : charpoly C n d.V b =
      ∑ i ∈ Finset.range (n + 1),
        Polynomial.C ((charpoly C n d.V b).coeff i) * Polynomial.X ^ i :=
    Polynomial.as_sum_range_C_mul_X_pow' _ hdeg
  rw [ChartPt.charpolyValue_def, Polynomial.map_sum]
  conv_rhs => rw [hsum, Polynomial.map_sum]
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
  refine Finset.sum_congr rfl fun i _ => ?_
  have key : σ (d.φ ⟨(charpoly C n d.V b).coeff i,
      charpoly_coeff_mem_chartInvariants C n d.V (symPiOpen_invariant C n d.V) b i⟩)
      = Ψ ((charpoly C n d.V b).coeff i) := by
    have hk := congrArg (fun f : ↥d.chartRingOf →+* L => f ⟨(charpoly C n d.V b).coeff i,
      charpoly_coeff_mem_chartInvariants C n d.V (symPiOpen_invariant C n d.V) b i⟩) h
    simpa using hk.symm
  rw [key]

/-- **The characteristic polynomial of `b` factors through a ring hom as a product of linear
factors.** -/
theorem map_charpoly_eq_prod (d : ChartPt C n p) {L : Type u} [Field L]
    (Ψ : Γ((prod C.toOver n).left, d.openOf) →+* L) (b : Γ(C.left, d.V)) :
    Polynomial.map Ψ (charpoly C n d.V b) =
      ∏ m : Fin n, (Polynomial.X - Polynomial.C (Ψ (coordPullbackAt C n d.V m b))) := by
  rw [charpoly, Polynomial.map_prod]
  exact Finset.prod_congr rfl fun m _ => by
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]

end Helpers

/-- **The local ideal set is an ideal.** -/
theorem localIdealSet_isIdeal {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {n : ℕ} [NeZero n] [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F} (d : Work.SymQuot.DivOf.ChartPt C n p) :
    ∃ J : Ideal (C.left.presheaf.obj (Opposite.op d.V)),
      (J : Set (C.left.presheaf.obj (Opposite.op d.V))) = d.localIdealSet := by
  -- produce a prime of `Γ(Cⁿ,Vⁿ)` lying over the kernel of the chart point
  haveI : (RingHom.ker d.φ).IsPrime := RingHom.ker_isPrime d.φ
  obtain ⟨P, -, hPprime, hPover⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (R := ↥d.chartRingOf)
      (RingHom.ker d.φ) (⊥ : Ideal Γ((prod C.toOver n).left, d.openOf))
      (by
        rw [Ideal.under_def, Ideal.comap_bot_of_injective _ Subtype.val_injective]
        exact bot_le)
  obtain ⟨L, hL, Ψ, σ, hcompat⟩ := exists_field_hom_extension d.φ P hPprime hPover
  letI : Field L := hL
  have hcompat' : Ψ.comp (Subring.subtype d.chartRingOf) = σ.comp d.φ := hcompat
  refine ⟨⨅ m : Fin n, RingHom.ker (Ψ.comp (coordPullbackAt C n d.V m)), ?_⟩
  ext b
  change b ∈ (⨅ m : Fin n, RingHom.ker (Ψ.comp (coordPullbackAt C n d.V m))) ↔
    b ∈ d.localIdealSet
  rw [Ideal.mem_iInf, ChartPt.mem_localIdealSet]
  simp only [RingHom.mem_ker, RingHom.comp_apply]
  have hmap := map_charpoly_eq_prod d Ψ b
  constructor
  · -- if all values vanish then `χ_b = Tⁿ`
    intro h0
    have hprod : Polynomial.map Ψ (charpoly C n d.V b) = Polynomial.X ^ n := by
      rw [hmap]
      simp only [h0, Polynomial.C_0, sub_zero]
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have h2 : Polynomial.map σ (d.charpolyValue b) = Polynomial.X ^ n := by
      rw [charpolyValue_map_eq d Ψ σ hcompat' b, hprod]
    have h3 : Polynomial.map σ (Polynomial.X ^ n) = Polynomial.X ^ n := by
      rw [Polynomial.map_pow, Polynomial.map_X]
    exact Polynomial.map_injective σ (RingHom.injective σ) (h2.trans h3.symm)
  · -- if `χ_b = Tⁿ` then all values vanish
    intro hb
    have hprod : Polynomial.map Ψ (charpoly C n d.V b) = Polynomial.X ^ n := by
      rw [← charpolyValue_map_eq d Ψ σ hcompat' b, hb, Polynomial.map_pow, Polynomial.map_X]
    have hprod' : ∏ m : Fin n,
        (Polynomial.X - Polynomial.C (Ψ (coordPullbackAt C n d.V m b))) = Polynomial.X ^ n := by
      rw [← hmap, hprod]
    intro m
    have hm := congrArg (Polynomial.eval (Ψ (coordPullbackAt C n d.V m b))) hprod'
    simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_pow] at hm
    have hz : ∏ m' : Fin n,
        (Ψ (coordPullbackAt C n d.V m b) - Ψ (coordPullbackAt C n d.V m' b)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ m) (by simp)
    rw [hz] at hm
    exact (pow_eq_zero_iff (NeZero.ne n)).mp hm.symm

end

end Work.SymQuot.DivOf
