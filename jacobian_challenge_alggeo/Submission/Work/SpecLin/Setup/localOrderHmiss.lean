import Mathlib
import Submission.Work.SpecLin.Alt.chartMap
import Submission.Work.CurveBasics.Basic.isDomain_tensor_sections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option linter.style.haveILetI false

namespace Work.SpecLin.Setup

universe u

open scoped TensorProduct

/-- `R → A ⊗[K] R` is injective for a nontrivial `K`-algebra `A` over a field `K`: a `K`-linear
functional on `A` normalised at `1` retracts `A ⊗[K] R` onto `R`. -/
private lemma chartTensor_includeRight_injective {K : Type u} [Field K] {A : Type u}
    [CommRing A] [Algebra K A] [Nontrivial A] {R : Type u} [CommRing R] [Algebra K R] :
    Function.Injective
      (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R)) := by
  haveI : Module.Free K A := Module.Free.of_divisionRing K A
  intro r r' hrr
  obtain ⟨π, hπ⟩ := Module.Projective.exists_dual_eq_one K (V := A) (x := (1 : A)) one_ne_zero
  let Φ : A ⊗[K] R →ₗ[K] R :=
    (TensorProduct.lid K R).toLinearMap.comp (TensorProduct.map π (LinearMap.id : R →ₗ[K] R))
  have hΦ : ∀ r : R, Φ ((1 : A) ⊗ₜ[K] r) = r := by
    intro r
    simp [Φ, TensorProduct.map_tmul, TensorProduct.lid_tmul, hπ]
  rw [Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.includeRight_apply] at hrr
  rw [← hΦ r, hrr, hΦ r']

/-- **The vertical primes of the relative chart are prime ideals.**  For a curve chart
`A = Γ(C,W)` over `K` and a prime ideal `q` of the valuation ring `R` which is a `K`-algebra, the
ideal `q·(A ⊗[K] R)` is prime: its quotient is `A ⊗[K] (R ⧸ q)`, which is a domain because
`A ⊗[K] L` is a domain for *every* field extension `L/K` (geometric integrality of `C`, i.e.
`Work.CurveBasics.Curve.isDomain_tensor_sections`) and because
`A ⊗[K] (R ⧸ q) ↪ A ⊗[K] Frac (R ⧸ q)` (`Work.SpecLin.Chart.isDomain_tensorProduct_fractionRing`).

The identification of the quotient with the tensor product is
`Algebra.TensorProduct.tensorQuotientEquiv` (the same isomorphism as in
`Work.SpecLin.Core.chartFibreQuotEquiv`, there for the maximal ideal). -/
private lemma isPrime_map_includeRight {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W]
    (q : Ideal R) (hq : q.IsPrime) :
    (q.map (Algebra.TensorProduct.includeRight (R := K)
      (A := C.left.presheaf.obj (Opposite.op W)) (B := R))).IsPrime := by
  haveI : IsDomain (R ⧸ q) := (Ideal.Quotient.isDomain_iff_prime q).mpr hq
  haveI hfrac : IsDomain ((C.left.presheaf.obj (Opposite.op W)) ⊗[K] (R ⧸ q)) :=
    Work.SpecLin.Chart.isDomain_tensorProduct_fractionRing
      (Work.CurveBasics.Curve.isDomain_tensor_sections C hW (FractionRing (R ⧸ q)))
  have hiso := Algebra.TensorProduct.tensorQuotientEquiv (R := K) (S := K) (T := R)
    (A := C.left.presheaf.obj (Opposite.op W)) q
  haveI : IsDomain (((C.left.presheaf.obj (Opposite.op W)) ⊗[K] R) ⧸
      (q.map (Algebra.TensorProduct.includeRight (R := K)
        (A := C.left.presheaf.obj (Opposite.op W)) (B := R)))) :=
    Function.Injective.isDomain hiso.symm hiso.symm.injective
  exact (Ideal.Quotient.isDomain_iff_prime _).mp ‹IsDomain _›

/-- **A height-one prime of the relative chart which is not contained in the fibre prime meets the
image of `R ∖ {0}` trivially.**

Let `R` be a valuation ring which is a `K`-algebra and `B = Γ(C,W) ⊗[K] R` the coordinate ring of
the relative chart of a nonempty affine chart of a curve `C/K` (a domain), with fibre prime
`P = 𝔪_R·B` (the prime of the generic point of the special fibre).  Then a prime `p ⊆ B` of height
one with `p ⊄ P` contains no nonzero element of the image of `R`: such a `p` lies over the generic
point of `Spec R`, i.e. it is a point of the generic fibre `C_F` (`F = Frac R`).

Indeed, if `ι r ∈ p` with `r ≠ 0` (`ι = includeRight`, injective), then the prime `q = p ∩ R`
contains `r`, so `Q = q·B` is a *nonzero* prime ideal contained in `p` (it is a prime because
`B ⧸ Q ≅ Γ(C,W) ⊗[K] (R ⧸ q)` is a domain).  If `Q ⊊ p` then `Q` would be a nonzero prime
strictly below `p`, forcing `p.height ≥ 2`; hence `p = Q`, and `q ⊆ 𝔪_R` gives `p ⊆ 𝔪_R·B = P`,
contradicting the hypothesis `p ⊄ P`. -/
theorem localOrderHmiss {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W]
    [IsDomain (Work.SpecLin.Core.chartTensor R W)]
    (p : Ideal (Work.SpecLin.Core.chartTensor R W)) (hp : p.IsPrime) (hp1 : p.height = 1)
    (hpP : ¬ (p ≤ Work.SpecLin.Core.chartFibrePrime R W)) :
    ∀ r : R, r ≠ 0 →
      Algebra.TensorProduct.includeRight (R := K)
        (A := C.left.presheaf.obj (Opposite.op W)) (B := R) r ∉ p := by
  intro r hr hmem
  -- Abbreviate `ι : R → B`, the structure map of the relative chart.
  let ι : R →+* Work.SpecLin.Core.chartTensor R W :=
    Algebra.TensorProduct.includeRight (R := K) (A := C.left.presheaf.obj (Opposite.op W)) (B := R)
  have hinj : Function.Injective ι := chartTensor_includeRight_injective
  have hιr : ι r ≠ 0 := fun h0 => hr (hinj (by rw [h0, map_zero]))
  -- The contraction `q = p ∩ R` and the ideal `Q = q·B ⊆ p` generated by it.
  set q : Ideal R := p.comap ι with hqdef
  have hqprime : q.IsPrime := by
    haveI : p.IsPrime := hp
    exact Ideal.IsPrime.comap ι
  have hrq : r ∈ q := hmem
  have hqle : q ≤ IsLocalRing.maximalIdeal R :=
    IsLocalRing.le_maximalIdeal hqprime.ne_top
  have hQprime : (q.map ι).IsPrime := isPrime_map_includeRight R W hW q hqprime
  have hQle : q.map ι ≤ p := by
    rw [Ideal.map_le_iff_le_comap]
  have hQne : q.map ι ≠ ⊥ := by
    intro h0
    have hmem' : ι r ∈ q.map ι := Ideal.mem_map_of_mem ι hrq
    rw [h0] at hmem'
    exact hιr (by simpa using hmem')
  -- `p` has height one, so the nonzero prime `Q ≤ p` cannot be strictly smaller than `p`.
  have hp_le : p.height ≤ ((1 : ℕ) : ℕ∞) := by
    rw [hp1]
    exact le_of_eq (Nat.cast_one).symm
  have hQeq : q.map ι = p := by
    rcases lt_or_eq_of_le hQle with hlt | heq
    · exfalso
      haveI : p.IsPrime := hp
      have hQh : (q.map ι).height < ((1 : ℕ) : ℕ∞) :=
        (Ideal.height_le_iff.mp hp_le) (q.map ι) hQprime hlt
      have hzero : (q.map ι).height = 0 := by
        by_contra h
        have h1 : ((1 : ℕ) : ℕ∞) ≤ (q.map ι).height := by
          rw [Nat.cast_one]
          exact Order.one_le_iff_ne_zero.mpr h
        exact not_le.mpr hQh h1
      exact hQne (Ideal.height_eq_zero_iff_eq_bot.mp hzero)
    · exact heq
  -- Hence `p = q·B ⊆ 𝔪_R·B`, contradicting `hpP`.
  exact hpP (hQeq ▸ Ideal.map_mono hqle)

end Work.SpecLin.Setup
