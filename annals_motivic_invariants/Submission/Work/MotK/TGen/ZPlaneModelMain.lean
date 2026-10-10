import Mathlib
import Submission.Work.MotK.TGen.ZPlaneModel
import Submission.Work.MotK.TGen.ZRingIsDomainAll

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

/-!
# The plane-model reduction of the residual curve, after the primality of `radical (ZI)`

The main theorem `Work.MotK.TGen.ZPlaneModel` (the reduction of the residual curve
`Z = V(radical (ZI a b h))` to the plane model `V(ZElim2 a b h)`) needs the *geometric input*
`RingHom.ker (zPsi) ≤ radical (ZI)`, which used to be the hole
`Work.MotK.TGen.ker_zPsi_le_radical` of `ZPlaneModel.lean`.  It is proved here from the
saturation computation of `Work.MotK.TGen.ZRingIsDomainAll`:

* `zJ := (zF1, zB) ⊆ ZI` (`zF1_mem_ZI`, `zB_mem_ZI`);
* `ZI ⊆ ker (zPsi)` (`ZI_le_ker_zPsi`), so `zJ ⊆ ker (zPsi)`;
* `ker (zPsi) ⊆ zJ`: this is `ker_zPsi_eq_saturation` (clearing denominators by `zA`), plus the
  saturation step `zA_mul_mem_zJ`;
* hence `ker (zPsi) = zJ ⊆ ZI ⊆ radical (ZI)`.

The statements are copied verbatim from `ZPlaneModel.lean` so that the consumer
(`Work.MotK.TGen.ZTwistDiv`) is unchanged.
-/

set_option maxHeartbeats 4000000

namespace Work.MotK.TGen

open MvPolynomial

variable {K : Type} [Field K]

/-- `zJ = (zF1, zB) ⊆ ZI`. -/
theorem zJ_le_ZI_aux (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    zJ K a b h ≤ Work.MotK.TwCensus.ZI a b h := by
  rw [zJ, Ideal.span_le]
  intro x hx
  rcases hx with rfl | rfl
  · exact zF1_mem_ZI (K := K) a b h ha hb
  · exact zB_mem_ZI (K := K) a b h hb

/-- `ker (zPsi) ⊆ zJ`: the saturation step. -/
theorem ker_zPsi_le_zJ (K : Type) [Field K] (a b h : K) [IsDomain (ZD K a b h)]
    (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    RingHom.ker (zPsi K a b h) ≤ zJ K a b h := by
  intro f hf
  obtain ⟨N, hN⟩ := (ker_zPsi_eq_saturation K a b h ha hb hh f).mp hf
  have hsub : Ideal.span ({zg K a b h, zB K a b h} : Set (MvPolynomial (Fin 3) K))
      ≤ zJ K a b h := by
    rw [zJ, Ideal.span_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact zg_mem_zJ K a b h hb hh
    · exact Ideal.subset_span (by simp)
  have hsat : ∀ n (g : MvPolynomial (Fin 3) K),
      (zA K a b h) ^ n * g ∈ zJ K a b h → g ∈ zJ K a b h := by
    intro n
    induction n with
    | zero => intro g hg; simpa using hg
    | succ m ih =>
        intro g hg
        rw [pow_succ, mul_assoc] at hg
        exact zA_mul_mem_zJ K a b h ha hb hh g (ih _ hg)
  exact hsat N f (hsub hN)

/-- **The geometric input.**  Every polynomial vanishing on the graph of the rational map
`(v,w) ↦ (C₁/A₁, v, w)` over the curve `V(g)` vanishes on the whole residual curve `Z = V(ZI)`:
the finitely many extra points of `Z` (those with `A₁ = 0`) are limits of the graph along the
branches of `V(g)`.  Consequently `ker Ψ = radical (ZI)`. -/
theorem ker_zPsi_le_radical (K : Type) [Field K] (a b h : K) [IsDomain (ZD K a b h)]
    (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    RingHom.ker (zPsi K a b h) ≤ Ideal.radical (Work.MotK.TwCensus.ZI a b h) :=
  le_trans (ker_zPsi_le_zJ K a b h ha hb hh)
    (le_trans (zJ_le_ZI_aux a b h ha hb) Ideal.le_radical)

/-- NOTE (2026-10-05).  The canonical declaration of the plane-model reduction is
`Work.MotK.TGen.ZPlaneModel` in `Submission/Work/MotK/TGen/ZPlaneModel.lean`; it is available to
`Work.MotK.TGen.ZTwistDiv` through the import of this module.  The theorem below is the same
statement proved along the *saturation* route `zJ = (zF1, zB)` of `ZRingIsDomainAll`; it is kept
(renamed) for the record. -/
theorem ZPlaneModel_of_zJ (K : Type) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) (hirr : Irreducible (Work.MotK.TwCensus.ZElim2 a b h)) : Nonempty (FractionRing (MvPolynomial (Fin 3) K ⧸ Ideal.radical (Work.MotK.TwCensus.ZI a b h)) ≃ₐ[K] FractionRing (MvPolynomial (Fin 2) K ⧸ Ideal.span {Work.MotK.TwCensus.ZElim2 a b h})) := by
  classical
  have hne : Work.MotK.TwCensus.ZElim2 a b h ≠ 0 := by
    intro hzero
    have hc : MvPolynomial.constantCoeff (Work.MotK.TwCensus.ZElim2 a b h) = 0 := by
      rw [hzero, map_zero]
    rw [Work.MotK.TwCensus.ZElim2] at hc
    simp only [map_add, map_sub, map_mul, map_pow, MvPolynomial.constantCoeff_C,
      MvPolynomial.constantCoeff_X] at hc
    exact (mul_ne_zero (pow_ne_zero 6 ha) (pow_ne_zero 2 hb)) (by simpa using hc)
  have hprime : (Ideal.span {Work.MotK.TwCensus.ZElim2 a b h}).IsPrime :=
    (Ideal.span_singleton_prime hne).mpr (UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr)
  haveI hD : IsDomain (ZD K a b h) := Ideal.Quotient.isDomain _
  have hker_le : RingHom.ker (zPsi K a b h) ≤ Ideal.radical (Work.MotK.TwCensus.ZI a b h) :=
    ker_zPsi_le_radical K a b h ha hb hh
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
