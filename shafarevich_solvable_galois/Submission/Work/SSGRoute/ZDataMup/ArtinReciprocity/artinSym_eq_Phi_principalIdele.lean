import Mathlib
import Submission.Work.SSGRoute.ZDataMup.unitIdele_mem_normImage
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.localFactor_unramified_eq_frob_zpow
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.localImageAt_ofInfinite_mem_localNormSubgroup_of_pos
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField nonZeroDivisors

set_option linter.style.haveILetI false

namespace Work.SSGRoute.ZDataMup.ArtinReciprocity

/-- **The glued Artin map computes the Artin symbol of a congruent principal ideal.**

Let `Φ : 𝕀_K →* Gal(L/K)` kill the idèle norms and be Frobenius-normalised at every unramified
prime.  Let `m` be an admissible modulus, `b ≡ 1 mod m` at the ramified primes dividing `(m)`
(`hcong`), and `b` totally positive (`hpos`).  Then `Φ` computes the Artin symbol of the principal
ideal `(b)`:

  `Φ (principalIdele K b) = artinSym ((b))`.

The idea: write `(b) = ∏_Q Q ^ v_Q(b)` and factor the principal idèle as
`principalIdele K b = c · z` with `c = ∏_Q ideleOfPrime Q ^ v_Q(b)` and `z := c⁻¹ ·
principalIdele K b`.  The "unit part" `z` is an idèle norm (`unitIdele_mem_normImage`), hence
killed by `Φ`, so `Φ (principalIdele K b) = Φ c`.  Every prime `Q` occurring in `(b)` is
unramified (a ramified `Q | (m)` would make `b` a local unit, forcing `Q ∤ (b)`), so `hF` computes
each factor `Φ (ideleOfPrime Q) = frobAtPrime Q`, and the product is exactly `artinSym ((b))`. -/
theorem artinSym_eq_Phi_principalIdele
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (m : ℕ)
    (hAdm : NK.CFTLib.ArtinReciprocityIdeal.IsAdmissible K L m)
    (Φ : NK.GlobalCFT.Idele K →* (L ≃ₐ[K] L))
    (hN : ∀ y : NK.GlobalCFT.Idele L, Φ (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1)
    (hF : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
      Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q)
    (hram : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∉ Q.asIdeal →
      Ideal.ramificationIdxIn Q.asIdeal (NumberField.RingOfIntegers L) = 1)
    (b : Kˣ)
    (hcong : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∈ Q.asIdeal →
      Ideal.ramificationIdxIn Q.asIdeal (NumberField.RingOfIntegers L) ≠ 1 →
      Valued.v (algebraMap K (Q.adicCompletion K) ((b : Kˣ) : K) - 1)
        ≤ Valued.v ((m : ℕ) : Q.adicCompletion K))
    (hpos : ∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal),
      0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
            (algebraMap K w.Completion ((b : Kˣ) : K))) :
    Φ (NK.GlobalCFT.Idele.principalIdele K b)
      = NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
          ((b : Kˣ) : K)) := by
  classical
  letI : CommMonoid (L ≃ₐ[K] L) := NK.CFTLib.Arl.galCommMonoid hcomm
  set A : FractionalIdeal (𝓞 K)⁰ K :=
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((b : Kˣ) : K) with hA
  set c : NK.GlobalCFT.Idele K :=
    ∏ Q ∈ (NK.CFTLib.Arl.exps A).support,
      (NK.HeckeL.ideleOfPrime K Q) ^ (NK.CFTLib.Arl.exps A Q) with hc
  set z : NK.GlobalCFT.Idele K := c⁻¹ * NK.GlobalCFT.Idele.principalIdele K b with hz
  have hsplit : NK.GlobalCFT.Idele.principalIdele K b = c * z := by
    rw [hz, hc]; group
  -- the "unit part" is an idèle norm
  have hzmem : z ∈ NK.GlobalCFT.Idele.normImage K L := by
    rw [hz, hc]
    exact Work.SSGRoute.ZDataMup.unitIdele_mem_normImage (K := K) (L := L) m hAdm hram b hcong hpos
  -- hence `Φ (principalIdele b) = Φ c`
  have hΦ : Φ (NK.GlobalCFT.Idele.principalIdele K b) = Φ c := by
    rw [hsplit, map_mul]
    obtain ⟨y, hy⟩ := NK.GlobalCFT.Idele.mem_normImage.mp hzmem
    rw [show z = NK.GlobalCFT.Idele.normIdeleHom K L y from
        NK.GlobalCFT.Idele.ext fun v => hy v, hN y, mul_one]
  -- every prime occurring in `(b)` is unramified: if `Q` were ramified then `(m) ∈ Q` by `hram`
  -- and `hcong` would force `b_Q ≡ 1 mod Q ^ v_Q(m)`, i.e. `Q ∤ (b)`
  have hunrOfMem : ∀ Q ∈ (NK.CFTLib.Arl.exps A).support,
      NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q := by
    intro Q hQ
    have hcount : FractionalIdeal.count K Q A ≠ 0 := by
      rw [← NK.CFTLib.Arl.exps_apply]
      exact Finsupp.mem_support_iff.mp hQ
    by_contra hnot
    have hne : Ideal.ramificationIdxIn Q.asIdeal (𝓞 L) ≠ 1 :=
      fun h1 => hnot
        (Work.SSGRoute.ZDataMup.isUnramifiedIn_of_ramificationIdxIn_eq_one (K := K) (L := L) Q h1)
    have hmem : (m : 𝓞 K) ∈ Q.asIdeal := by
      by_contra h
      exact hne (hram Q h)
    have hval : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (((NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite Q) b :
            (Q.adicCompletion K)ˣ) : Q.adicCompletion K) - 1) < 1 :=
      lt_of_le_of_lt (hcong Q hmem hne) (NK.CFTLib.Arl.val_natCast_lt_one (K := K) Q m hmem)
    have hunit : NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite Q) b ∈
        NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite Q) :=
      (NK.GlobalCFT.Place.mem_localUnits_ofFinite_iff_valued_eq_one).mpr (by
        have h := Valuation.map_add_eq_of_lt_left
          (v := Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)))
          (x := (1 : Q.adicCompletion K))
          (y := ((NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofFinite Q) b :
            (Q.adicCompletion K)ˣ) : Q.adicCompletion K) - 1) (by rw [map_one]; exact hval)
        rw [map_one, add_sub_cancel] at h
        exact h)
    exact hcount ((Work.SSGRoute.ZDataMup.count_eq_zero_iff_localUnit (K := K) Q b).mpr hunit)
  -- `Φ c` is the Frobenius product over the support of `exps A`, which is `artinSym A` by the
  -- definitional unfolding of `NK.CFTLib.Arl.artinSym` as a `Finsupp.prod` over `exps A`
  have hartinSym : NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm A =
      ∏ Q ∈ (NK.CFTLib.Arl.exps A).support,
        (NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) ^ (NK.CFTLib.Arl.exps A Q) := by
    unfold NK.CFTLib.Arl.artinSym
    exact Finsupp.prod_of_support_subset (NK.CFTLib.Arl.exps A) (subset_refl _)
      (fun Q e => (NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) ^ e) (fun i _ => zpow_zero _)
  rw [hΦ]
  rw [hc, map_prod]
  have hstep : ∀ Q ∈ (NK.CFTLib.Arl.exps A).support,
      Φ ((NK.HeckeL.ideleOfPrime K Q) ^ (NK.CFTLib.Arl.exps A Q)) =
        (NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) ^ (NK.CFTLib.Arl.exps A Q) := by
    intro Q hQ
    rw [map_zpow, hF Q (hunrOfMem Q hQ)]
  rw [Finset.prod_congr rfl hstep]
  exact hartinSym.symm.trans
    (congrArg (NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm) hA)

end Work.SSGRoute.ZDataMup.ArtinReciprocity
