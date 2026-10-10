/-
# The plane model of the residual curve `Z = V(radical (ZI a b h))`

**Deliverable.** `Work.MotK.TGen.ZPlaneModel`: the residual curve of the Klein-twist chart
`x₀ = zC/zA` is birational to the plane curve `V(ZElim2 a b h)`,

```
Frac (K[X₀,X₁,X₂]/√(ZI a b h)) ≅ Frac (K[X₁,X₂]/(ZElim2 a b h)).
```

**Structure of the proof.**  The elimination homomorphism
`zPsi : K[X₀,X₁,X₂] →ₐ[K] Frac (K[X₁,X₂]/(ZElim2))` substitutes `X₀ ↦ zC/zA`, `X₁ ↦ x₁`,
`X₂ ↦ x₂` (the graph of the chart map over the plane curve `V(g)`, `g = zg = ZElim`).  Then

* `√(ZI) ≤ ker zPsi` (`ZI_le_ker_zPsi` plus primality of the kernel of an algebra map into a
  domain — this is the `hker_ge` step below), and
* `ker zPsi ≤ √(ZI)`: every polynomial vanishing on the graph of the rational map vanishes on the
  whole residual curve `Z` (the finitely many extra points of `Z` are limits of the graph).  This
  geometric input is `Work.MotK.TGen.ker_zPsi_le_radical_aux`, proved in the companion module.

Hence `ker zPsi = √(ZI)` is prime, `Φ := lift zPsi` is an injective `K`-algebra map out of
`A := K[X₀,X₁,X₂]/√(ZI)`, and `IsFractionRing.liftAlgHom` extends it to the fraction fields; the
extension is bijective because `Phi` is injective and the target `ZF = Frac (K[X₁,X₂]/(ZElim2))` is
generated over `Φ(A)` by the two elements `x₁` and `x₂ ∈ Φ(A)` — concretely every element of `ZF`
is a quotient of elements of `Φ(A)`.

The *definitions* (`zA`, `zC`, `zB`, `zg`, `ZD`, `ZF`, `zPsi`, …) and the small lemmas about them
now live in `Submission/Work/MotK/TGen/ZPlaneDefs.lean` (module
`Submission.Work.MotK.TGen.ZPlaneDefs`), so that this module can import the geometric input
`ker_zPsi_le_radical_aux`, which is *about* those definitions.  Nothing else changed: `zPsi` and
friends keep their fully qualified names `Work.MotK.TGen.…`.
-/
import Mathlib
import Submission.Work.MotK.TGen.ZPlaneDefs
import Submission.Work.MotK.TGen.ker_zPsi_le_radical_aux

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

set_option maxHeartbeats 4000000

namespace Work.MotK.TGen

open MvPolynomial

theorem ZPlaneModel (K : Type) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) (hirr : Irreducible (Work.MotK.TwCensus.ZElim2 a b h)) : Nonempty (FractionRing (MvPolynomial (Fin 3) K ⧸ Ideal.radical (Work.MotK.TwCensus.ZI a b h)) ≃ₐ[K] FractionRing (MvPolynomial (Fin 2) K ⧸ Ideal.span {Work.MotK.TwCensus.ZElim2 a b h})) := by
  classical
  have hne : Work.MotK.TwCensus.ZElim2 a b h ≠ 0 := by
    intro hzero
    have hc : MvPolynomial.constantCoeff (Work.MotK.TwCensus.ZElim2 a b h) = 0 := by
      rw [hzero, map_zero]
    rw [Work.MotK.TwCensus.ZElim2] at hc
    simp only [map_add, map_sub, map_mul, map_pow, MvPolynomial.constantCoeff_C,
      MvPolynomial.constantCoeff_X] at hc
    exact (mul_ne_zero (pow_ne_zero 6 ha) (pow_ne_zero 2 hb)) (by simpa using hc)
  haveI hprime : (Ideal.span {Work.MotK.TwCensus.ZElim2 a b h}).IsPrime :=
    (Ideal.span_singleton_prime hne).mpr (UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr)
  haveI hD : IsDomain (ZD K a b h) := Ideal.Quotient.isDomain _
  have hker_le : RingHom.ker (zPsi K a b h) ≤ Ideal.radical (Work.MotK.TwCensus.ZI a b h) :=
    ker_zPsi_le_radical_aux K a b h ha hb hh
  have hker_ge : Ideal.radical (Work.MotK.TwCensus.ZI a b h) ≤ RingHom.ker (zPsi K a b h) := by
    intro x hx
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hx
    exact (RingHom.ker_isPrime (zPsi K a b h)).mem_of_pow_mem n
      (ZI_le_ker_zPsi K a b h ha hb hh hn)
  have hker : RingHom.ker (zPsi K a b h) = Ideal.radical (Work.MotK.TwCensus.ZI a b h) :=
    le_antisymm hker_le hker_ge
  have hpr : (Ideal.radical (Work.MotK.TwCensus.ZI a b h)).IsPrime :=
    hker ▸ RingHom.ker_isPrime (zPsi K a b h)
  haveI := hpr
  refine ⟨?_⟩
  let R := MvPolynomial (Fin 3) K ⧸ Ideal.radical (Work.MotK.TwCensus.ZI a b h)
  haveI : IsDomain R := Ideal.Quotient.isDomain _
  let Φ : R →ₐ[K] ZF K a b h :=
    Ideal.Quotient.liftₐ _ (zPsi K a b h) (fun x hx => by
      have h1 : x ∈ RingHom.ker (zPsi K a b h) := hker.symm ▸ hx
      exact (RingHom.mem_ker (f := zPsi K a b h)).mp h1)
  have hΦmk : ∀ f : MvPolynomial (Fin 3) K, Φ (Ideal.Quotient.mk _ f) = zPsi K a b h f := by
    intro f
    change (Ideal.Quotient.lift (Ideal.radical (Work.MotK.TwCensus.ZI a b h))
      (↑(zPsi K a b h) : MvPolynomial (Fin 3) K →+* ZF K a b h) _)
        (Ideal.Quotient.mk _ f) = (zPsi K a b h) f
    rfl
  have hΦinj : Function.Injective Φ := by
    intro x y hxy
    obtain ⟨fx, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨fy, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [hΦmk, hΦmk] at hxy
    have hmem : fx - fy ∈ Ideal.radical (Work.MotK.TwCensus.ZI a b h) := by
      rw [← hker, RingHom.mem_ker, map_sub, hxy, sub_self]
    rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hmem
  let e : FractionRing R →ₐ[K] ZF K a b h :=
    IsFractionRing.liftAlgHom (R := K) (A := R) (K := FractionRing R) (L := ZF K a b h)
      (g := Φ) hΦinj
  have he_apply : ∀ x : R, e (algebraMap R (FractionRing R) x) = Φ x := fun x =>
    IsFractionRing.lift_algebraMap hΦinj x
  have hinj_e : Function.Injective ⇑e := by
    intro x y hxy
    have hmem : x - y ∈ RingHom.ker e := by
      rw [RingHom.mem_ker, map_sub, hxy, sub_self]
    have hbot : RingHom.ker e = ⊥ := by
      rcases Ideal.eq_bot_or_top (RingHom.ker e) with h' | h'
      · exact h'
      · exfalso
        have h1 : (1 : FractionRing R) ∈ RingHom.ker e := by rw [h']; trivial
        exact one_ne_zero (by rw [← map_one e]; exact RingHom.mem_ker.mp h1)
    rw [hbot] at hmem
    exact sub_eq_zero.mp hmem
  have hsurj_e : Function.Surjective ⇑e := by
    intro z
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors (ZD K a b h)) z
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨q, hq⟩ := Ideal.Quotient.mk_surjective (s : ZD K a b h)
    have hsq : algebraMap (ZD K a b h) (ZF K a b h) (s : ZD K a b h) ≠ 0 := by
      intro h0
      have hs0 : (s : ZD K a b h) = 0 :=
        IsFractionRing.injective (ZD K a b h) (ZF K a b h) (by rw [h0, map_zero])
      exact one_ne_zero ((mem_nonZeroDivisors_iff.mp s.2).1 (1 : ZD K a b h)
        (by rw [hs0, zero_mul]))
    refine ⟨algebraMap R (FractionRing R) (Ideal.Quotient.mk _ (MvPolynomial.rename zEmb p))
      * (algebraMap R (FractionRing R) (Ideal.Quotient.mk _ (MvPolynomial.rename zEmb q)))⁻¹, ?_⟩
    have hY1 : e (algebraMap R (FractionRing R) (Ideal.Quotient.mk _ (MvPolynomial.rename zEmb p)))
        = algebraMap (ZD K a b h) (ZF K a b h) x := by
      rw [he_apply, hΦmk, zPsi_rename, hp]
    have hY2 : e (algebraMap R (FractionRing R) (Ideal.Quotient.mk _ (MvPolynomial.rename zEmb q)))
        = algebraMap (ZD K a b h) (ZF K a b h) (s : ZD K a b h) := by
      rw [he_apply, hΦmk, zPsi_rename, hq]
    have hY2ne : e (algebraMap R (FractionRing R) (Ideal.Quotient.mk _ (MvPolynomial.rename zEmb q)))
        ≠ 0 := by
      rw [hY2]; exact hsq
    have hY2ne' : algebraMap R (FractionRing R)
        (Ideal.Quotient.mk _ (MvPolynomial.rename zEmb q)) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hY2ne
      exact hY2ne rfl
    have key : e (algebraMap R (FractionRing R) (Ideal.Quotient.mk _ (MvPolynomial.rename zEmb p))
          * (algebraMap R (FractionRing R) (Ideal.Quotient.mk _ (MvPolynomial.rename zEmb q)))⁻¹)
        * e (algebraMap R (FractionRing R) (Ideal.Quotient.mk _ (MvPolynomial.rename zEmb q)))
        = z * e (algebraMap R (FractionRing R)
            (Ideal.Quotient.mk _ (MvPolynomial.rename zEmb q))) := by
      rw [← map_mul, mul_assoc, inv_mul_cancel₀ hY2ne', mul_one, hY1, hY2, ← hs]
    exact mul_right_cancel₀ hY2ne key
  refine AlgEquiv.ofBijective e ?_
  exact ⟨hinj_e, hsurj_e⟩

end Work.MotK.TGen
